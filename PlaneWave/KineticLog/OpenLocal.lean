import PlaneWave.KineticLog.OpenFree

/-!
# Logarithmic kinetic bound, part 25: the spatial localisation of the kinetic energy

The free-space step of `prop:free-kinetic-log`: for `f ∈ L²(ℝ^{3η})` with weak first and second
derivatives, the cutoff `χ` of `prop:free-dyn` (`χ = 1` on `B^one`, `∂χ = 0` off a shell
`S ⊆ (B^one)ᶜ`) and wavefunction leakage `∫_{(B^one)ᶜ} |f|² ≤ ε²`,

  `|(1/(2m_p)) Σ_c ‖∂_{p,c} f‖² - ⟨φ, T_p φ⟩_torus| ≤ (3/2)(1 + 4D₁ + D₁²) N ε`,

`φ = T(χ f)` the transplant, `N` a bound for `‖f‖`, `‖∂f‖`, `‖∂²f‖`. No small exterior gradient is
used; the only small exterior quantity is the wavefunction norm.

* `kco`, `dirD_liftTest`: coordinate derivatives of the lifted Fourier tests;
* **`coeff_cut_grad`**: the Fourier coefficients of the transplanted derivative,
  `(T(∂_a(χ f)))^(q) = i k_a(q) (T(χ f))^(q)` (compact support in the cell: no boundary terms);
* **`regKin_expect_cut`**: transplantation preserves the kinetic energy of particle `p`,
  `⟨T(χf), T_p T(χf)⟩ = (1/(2m_p)) Σ_c ‖∂_{p,c}(χ f)‖²`;
* `norm_sq_cutL2_add`: the transplant is isometric on functions supported in the cell;
* **`free_loc_coord`**, **`free_torus_kin`**: the localisation estimate (graph pairing through
  integration by parts, `inner_ibp`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter MeasureTheory Set PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FreeBoundary
  FSNormal

namespace KineticLog

attribute [local instance] FreeBoundary.unitAddCircleMeasureSpaceFB15
  FreeBoundary.unitAddCircleProbabilityMeasureFB15 FreeBoundary.molecularTorusFiniteMeasureFB15

variable {eta : ℕ}

/-! ## Coordinate derivatives of the lifted Fourier tests -/

/-- The physical momentum `k_a(q) = (2π/L) q_a` of a Fourier index along the coordinate `a`. -/
noncomputable def kco (L : ℝ) (q : FourierConfig eta Lattice3) (a : Fin eta × Fin 3) : ℝ :=
  2 * Real.pi / L * (q a.1 a.2 : ℝ)

lemma liftTest_apply (L : ℝ) (s : Finset (FourierConfig eta Lattice3))
    (c : FourierConfig eta Lattice3 → ℂ) (r : Rcfg eta) :
    liftTest L s c r = ∑ p ∈ s, c p * UnitAddTorus.mFourier (molecularFourierIndexEquiv eta p)
      (torusRealQuotient (Fin eta × Fin 3) (L⁻¹ • r)) := by
  unfold liftTest torusRealLift
  rw [molecularPositionFourierTest_apply]

lemma liftTest_single (L : ℝ) (q : FourierConfig eta Lattice3)
    (c : FourierConfig eta Lattice3 → ℂ) (r : Rcfg eta) :
    liftTest L {q} c r = c q * liftTest L {q} (fun _ => 1) r := by
  rw [liftTest_apply, liftTest_apply, Finset.sum_singleton, Finset.sum_singleton, one_mul]

lemma liftTest_hasDerivAt_line (L : ℝ) (s : Finset (FourierConfig eta Lattice3))
    (c : FourierConfig eta Lattice3 → ℂ) (r : Rcfg eta) (a : Fin eta × Fin 3) :
    HasDerivAt (fun t : ℝ => liftTest L s c (r + t • Pi.single a 1))
      (liftTest L s (fun p => c p * ((kco L p a : ℂ) * Complex.I)) r) 0 := by
  have heq : (fun t : ℝ => liftTest L s c (r + t • Pi.single a 1)) =
      fun t => molecularPositionFourierTest eta s c
        (torusCoordinateLine (torusRealQuotient (Fin eta × Fin 3) (L⁻¹ • r)) a (L⁻¹ * t)) := by
    funext t
    show molecularPositionFourierTest eta s c
        (torusRealQuotient (Fin eta × Fin 3) (L⁻¹ • (r + t • Pi.single a 1))) = _
    rw [← torusRealQuotient_coordinateLine, smul_add, smul_smul]
    congr
    exact Subsingleton.elim _ _
  rw [heq]
  have h1 : HasDerivAt (fun r' : ℝ => molecularPositionFourierTest eta s c
        (torusCoordinateLine (torusRealQuotient (Fin eta × Fin 3) (L⁻¹ • r)) a r'))
      (molecularPositionFourierTest eta s
        (fun p => c p * (2 * (Real.pi : ℂ) * Complex.I * (p a.1 a.2 : ℂ)))
        (torusCoordinateLine (torusRealQuotient (Fin eta × Fin 3) (L⁻¹ • r)) a (L⁻¹ * 0)))
      ((fun t : ℝ => L⁻¹ * t) 0) :=
    molecularPositionFourierTest_hasDerivAt_coordinateLine eta s c
      (torusRealQuotient (Fin eta × Fin 3) (L⁻¹ • r)) a (L⁻¹ * 0)
  have h2 : HasDerivAt (fun t : ℝ => L⁻¹ * t) L⁻¹ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul L⁻¹
  have h3 := HasDerivAt.scomp 0 h1 h2
  refine h3.congr_deriv ?_
  rw [mul_zero, torusCoordinateLine_zero, liftTest_apply, molecularPositionFourierTest_apply,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold kco
  rw [Complex.real_smul]
  push_cast
  field_simp

/-- `∂_a Φ̃ = Φ̃'` with the coefficients multiplied by `i k_a`. -/
lemma dirD_liftTest (L : ℝ) (s : Finset (FourierConfig eta Lattice3))
    (c : FourierConfig eta Lattice3 → ℂ) (a : Fin eta × Fin 3) (r : Rcfg eta) :
    dirD a (liftTest L s c) r = liftTest L s (fun p => c p * ((kco L p a : ℂ) * Complex.I)) r := by
  have hd : DifferentiableAt ℝ (liftTest L s c) (r + (0 : ℝ) • Pi.single a 1) :=
    ((contDiff_liftTest L s c 1).differentiable (by norm_num)) _
  have h1 := hasDerivAt_line hd.hasFDerivAt
  have h2 := liftTest_hasDerivAt_line L s c r a
  have h3 := h1.unique h2
  rw [zero_smul, add_zero] at h3
  exact h3

/-! ## The Fourier coefficients of transplanted derivatives -/

lemma coeff_eq_inner (q : FourierConfig eta Lattice3) (F : MolecularPositionL2 eta) :
    (molecularPositionSynthesis eta).symm F q =
      ⟪(ContinuousMap.toLp 2 volume ℂ) (molecularPositionFourierTest eta {q} (fun _ => 1)),
        F⟫_ℂ := by
  rw [molecularPositionFourierTest_inner, Finset.sum_singleton, map_one, one_mul]

/-- **The Fourier coefficients of the transplanted derivative**: for `f` with weak gradient `g`,
`(T(∂_aχ f) + T(χ g_a))^(q) = i k_a(q) (T(χ f))^(q)`. -/
theorem coeff_cut_grad {L : ℝ} (hL : 0 < L) (X : Cutoff eta L) {f : FreeL2 eta}
    {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad f g) (a : Fin eta × Fin 3)
    (q : FourierConfig eta Lattice3) :
    (molecularPositionSynthesis eta).symm ((X.d1W a).cutL2 hL f + X.chiW.cutL2 hL (g a)) q =
      ((kco L q a : ℂ) * Complex.I) *
        (molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL f) q := by
  have hΨd : ∀ r, dirD a (liftTest L {q} (fun _ => (1 : ℂ))) r =
      ((kco L q a : ℂ) * Complex.I) * liftTest L {q} (fun _ => (1 : ℂ)) r := fun r => by
    rw [dirD_liftTest, liftTest_single, one_mul]
  have hibp := ibp_weight hg (X.smooth.of_le (by norm_num)) (X.hasCompactSupport hL)
    (contDiff_liftTest L {q} (fun _ => (1 : ℂ)) 1) a
  simp_rw [hΨd] at hibp
  have e : ∫ r, conj (((kco L q a : ℂ) * Complex.I) * liftTest L {q} (fun _ => (1 : ℂ)) r) *
      ((X.χ r : ℂ) * f r) =
      -((kco L q a : ℂ) * Complex.I) *
        ∫ r, conj (liftTest L {q} (fun _ => (1 : ℂ)) r) * ((X.χ r : ℂ) * f r) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [e] at hibp
  rw [coeff_eq_inner, coeff_eq_inner, inner_add_right, inner_test_cutL2 hL, inner_test_cutL2 hL,
    inner_test_cutL2 hL]
  simp only [Cutoff.chiW, Cutoff.d1W]
  linear_combination ((tScale eta L : ℂ))⁻¹ * hibp

/-- **The transplant is isometric on functions supported in the cell**:
`‖T(w₁ f₁) + T(w₂ f₂)‖² = ∫ |w₁ f₁ + w₂ f₂|²`. -/
lemma norm_sq_cutL2_add {L : ℝ} (hL : 0 < L) (W₁ W₂ : BoxWeight eta L) (f₁ f₂ : FreeL2 eta) :
    ‖W₁.cutL2 hL f₁ + W₂.cutL2 hL f₂‖ ^ 2 = ∫ r, ‖W₁.w r * f₁ r + W₂.w r * f₂ r‖ ^ 2 := by
  have hae : (fun x => ‖((W₁.cutL2 hL f₁ + W₂.cutL2 hL f₂ : MolecularPositionL2 eta) :
      MolecularPositionTorus eta → ℂ) x‖ ^ 2) =ᵐ[volume]
      fun x => L ^ Fintype.card (Fin eta × Fin 3) * ‖W₁.w (cellCoord L x) * f₁ (cellCoord L x) +
        W₂.w (cellCoord L x) * f₂ (cellCoord L x)‖ ^ 2 := by
    filter_upwards [Lp.coeFn_add (W₁.cutL2 hL f₁) (W₂.cutL2 hL f₂), W₁.cutL2_ae hL f₁,
      W₂.cutL2_ae hL f₂] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    simp only [BoxWeight.cutFun]
    rw [← mul_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (tScale_pos hL),
      mul_pow, tScale_sq hL]
  have hs : ∀ r, (fun r => L ^ Fintype.card (Fin eta × Fin 3) *
      ‖W₁.w r * f₁ r + W₂.w r * f₂ r‖ ^ 2) r ≠ 0 → ∀ a, |r a| ≤ L / 4 := by
    intro r hr
    by_cases h1 : W₁.w r = 0
    · by_cases h2 : W₂.w r = 0
      · exact absurd (by simp [h1, h2]) hr
      · exact W₂.supp r h2
    · exact W₁.supp r h1
  rw [norm_sq_L2_eq, integral_congr_ae hae, integral_comp_cellCoord hL _ hs, smul_eq_mul,
    integral_const_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-! ## The kinetic energy of a transplanted state -/

section TransplantKin

variable {ν : Type} [Fintype ν]

omit [Fintype ν] in
/-- **Transplantation preserves the kinetic energy of particle `p`**:
`⟨T(χf), T_p T(χf)⟩ = (1/(2 m_p)) Σ_c ‖T(∂_{p,c}(χ f))‖²`. -/
theorem regKin_expect_cut (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (X : Cutoff eta L)
    {f : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad f g) (p : Fin eta) :
    (regKin sys (gF L) p).expect ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL f)) =
      1 / (2 * sys.mass p) *
        ∑ c : Fin 3, ‖(X.d1W (p, c)).cutL2 hL f + X.chiW.cutL2 hL (g (p, c))‖ ^ 2 := by
  set x := (molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL f) with hx
  set G : Fin 3 → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 := fun c =>
    (molecularPositionSynthesis eta).symm ((X.d1W (p, c)).cutL2 hL f + X.chiW.cutL2 hL (g (p, c)))
    with hG
  have hGq : ∀ c q, ‖G c q‖ ^ 2 = kco L q (p, c) ^ 2 * ‖x q‖ ^ 2 := by
    intro c q
    simp only [hG]
    rw [coeff_cut_grad hL X hg (p, c) q, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, mul_pow, Real.norm_eq_abs, sq_abs]
  have hnorm : ∀ c, ‖(X.d1W (p, c)).cutL2 hL f + X.chiW.cutL2 hL (g (p, c))‖ ^ 2 =
      ∑' q, ‖G c q‖ ^ 2 := by
    intro c
    rw [← l2_norm_sq]
    simp only [hG, LinearIsometryEquiv.norm_map]
  simp_rw [hnorm]
  rw [← Summable.tsum_finsetSum (fun c _ => l2_summable_sq (G c)), ← tsum_mul_left]
  unfold KinMult.expect
  refine tsum_congr fun q => ?_
  simp_rw [hGq]
  change regSymbol sys (gF L) p q * ‖x q‖ ^ 2 = _
  unfold regSymbol latticeNormSq kco gF
  rw [Fin.sum_univ_three]
  have := sys.mass_pos p
  field_simp

end TransplantKin

/-! ## The free-space localisation -/

section FreeLoc

variable {L : ℝ} (X : Cutoff eta L)

/-- The cutoff `χ` as a real weight on `ℝ^{3η}`. -/
noncomputable def chiR : RWeight eta where
  w := X.χ
  meas := X.smooth.continuous.measurable
  B := 1
  bound := fun r => by rw [abs_of_nonneg (X.nonneg r)]; exact X.le_one r

/-- `∂_a χ` as a real weight on `ℝ^{3η}`. -/
noncomputable def d1R (a : Fin eta × Fin 3) : RWeight eta where
  w := dirD a X.χ
  meas := (continuous_dirD X.smooth (by norm_num) a).measurable
  B := X.D1
  bound := fun r => X.d1 r a

/-- The transplant of `∂_a (χ f)` has the norm of `∂_a(χ f)` in free space. -/
lemma norm_cut_grad_eq (hL : 0 < L) (f : FreeL2 eta) (g : FreeL2 eta) (a : Fin eta × Fin 3) :
    ‖(X.d1W a).cutL2 hL f + X.chiW.cutL2 hL g‖ = ‖(d1R X a).mul f + (chiR X).mul g‖ := by
  have h1 := norm_sq_cutL2_add hL (X.d1W a) X.chiW f g
  have h2 : ‖(d1R X a).mul f + (chiR X).mul g‖ ^ 2 =
      ∫ r, ‖(X.d1W a).w r * f r + X.chiW.w r * g r‖ ^ 2 := by
    refine norm_sq_eq_of_ae ?_
    filter_upwards [Lp.coeFn_add ((d1R X a).mul f) ((chiR X).mul g), (d1R X a).mul_ae f,
      (chiR X).mul_ae g] with r e1 e2 e3
    rw [e1, Pi.add_apply, e2, e3]
    rfl
  rw [← h2] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

variable {X}

/-- **The localisation of one coordinate**: for `f` with weak gradient `g` and weak second
derivatives `g2`, and wavefunction leakage `‖1_{(B^one)ᶜ} f‖ ≤ ε`,
`|‖∂_a f‖² - ‖∂_a(χ f)‖²| ≤ ε (‖∂_a² f‖ + 4 D₁ ‖∂_a f‖ + D₁² ‖f‖)`. -/
theorem free_loc_coord {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S)
    (hBm : MeasurableSet Bone) (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0) {f : FreeL2 eta}
    {g : Fin eta × Fin 3 → FreeL2 eta} {g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad f g) (hg2 : ∀ b, HasWeakGrad (g b) (g2 b)) {ε : ℝ} (hε : 0 ≤ ε)
    (h0 : ∫ r in Boneᶜ, ‖f r‖ ^ 2 ≤ ε ^ 2) (a : Fin eta × Fin 3) :
    |‖g a‖ ^ 2 - ‖(d1R X a).mul f + (chiR X).mul (g a)‖ ^ 2| ≤
      ε * (‖g2 a a‖ + 4 * X.D1 * ‖g a‖ + X.D1 ^ 2 * ‖f‖) := by
  set χW := chiR X with hχW
  set dW := d1R X with hdW
  have hD1 : 0 ≤ X.D1 := (abs_nonneg _).trans (X.d1 0 a)
  have hχ1 : ContDiff ℝ 1 χW.w := X.smooth.of_le (by norm_num)
  have hdWw : ∀ b, (dW b).w = dirD b χW.w := fun b => rfl
  -- the weak gradients of `χ g_a` and `χ² g_a`
  have k1 := hasWeakGrad_mul (hg2 a) χW hχ1 dW hdWw
  have k2 := hasWeakGrad_mul k1 χW hχ1 dW hdWw
  have k3 := HasWeakGrad.sub (hg2 a) k2
  have hibp := inner_ibp hg k3 a
  -- the leakage norms
  have hS0 : ∫ r in S, ‖f r‖ ^ 2 ≤ ε ^ 2 :=
    le_trans (setIntegral_mono_set (integrable_sq_L2 f).integrableOn
      (ae_of_all _ fun r => by positivity) hSB.eventuallyLE) h0
  have hU0 : ‖f - χW.mul (χW.mul f)‖ ≤ ε := by
    have h := norm_le_of_ae_mul_supp (F := f - χW.mul (χW.mul f)) (f := f)
      (c := fun r => ((1 - X.χ r ^ 2 : ℝ) : ℂ)) ?_ hBm.compl (fun r hr => ?_) (B := 1)
      (fun r => ?_) hε h0
    · simpa using h
    · filter_upwards [Lp.coeFn_sub f (χW.mul (χW.mul f)), χW.mul_ae (χW.mul f), χW.mul_ae f]
        with r e1 e2 e3
      rw [e1, Pi.sub_apply, e2, e3]
      simp only [hχW, chiR]
      push_cast
      ring
    · have hr' : r ∈ Bone := by simpa using hr
      rw [hχB r hr']
      norm_num
    · rw [Complex.norm_real, Real.norm_eq_abs]
      have e1 := X.nonneg r
      have e2 := X.le_one r
      rw [abs_le]
      constructor <;> nlinarith
  have hB : ‖(dW a).mul f‖ ≤ X.D1 * ε :=
    (dW a).norm_mul_le_of_supp hSm (fun r hr => hdS r hr a) f hε hS0
  have hU1 : ‖χW.mul ((dW a).mul f)‖ ≤ X.D1 * ε := by
    refine (χW.norm_mul_le _).trans ?_
    have : χW.B = 1 := rfl
    rw [this, one_mul]
    exact hB
  have hU2 : ‖(dW a).mul (χW.mul f)‖ ≤ X.D1 * ε := by
    refine norm_le_of_ae_mul_supp (f := f) (c := fun r => ((dirD a X.χ r * X.χ r : ℝ) : ℂ)) ?_ hSm
      (fun r hr => by rw [hdS r hr a, zero_mul, Complex.ofReal_zero]) (fun r => ?_) hε hS0
    · filter_upwards [(dW a).mul_ae (χW.mul f), χW.mul_ae f] with r e1 e2
      rw [e1, e2]
      simp only [hdW, hχW, d1R, chiR]
      push_cast
      ring
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (X.nonneg r)]
      calc |dirD a X.χ r| * X.χ r ≤ X.D1 * 1 :=
            mul_le_mul (X.d1 r a) (X.le_one r) (X.nonneg r) hD1
        _ = X.D1 := mul_one _
  have hA : ‖χW.mul (g a)‖ ≤ ‖g a‖ := by
    refine (χW.norm_mul_le _).trans ?_
    have : χW.B = 1 := rfl
    rw [this, one_mul]
  have hBf : ‖(dW a).mul f‖ ≤ X.D1 * ‖f‖ := (dW a).norm_mul_le f
  -- the identity `‖g_a‖² - ‖χ g_a‖² = re(-⟪g2_aa, f - χ²f⟫ + ⟪g_a, U₁⟫ + ⟪g_a, U₂⟫)`
  have t1 : ⟪(dW a).mul (χW.mul (g a)), f⟫_ℂ = ⟪g a, χW.mul ((dW a).mul f)⟫_ℂ := by
    rw [(dW a).inner_mul_left, χW.inner_mul_left]
  have t2 : ⟪χW.mul ((dW a).mul (g a) + χW.mul (g2 a a)), f⟫_ℂ =
      ⟪g a, (dW a).mul (χW.mul f)⟫_ℂ + ⟪g2 a a, χW.mul (χW.mul f)⟫_ℂ := by
    rw [χW.inner_mul_left, inner_add_left, (dW a).inner_mul_left, χW.inner_mul_left]
  have t3 : ⟪g2 a a - ((dW a).mul (χW.mul (g a)) +
      χW.mul ((dW a).mul (g a) + χW.mul (g2 a a))), f⟫_ℂ = ⟪g2 a a, f⟫_ℂ -
      (⟪(dW a).mul (χW.mul (g a)), f⟫_ℂ + ⟪χW.mul ((dW a).mul (g a) + χW.mul (g2 a a)), f⟫_ℂ) := by
    rw [inner_sub_left, inner_add_left]
  have t4 : ⟪g2 a a, f - χW.mul (χW.mul f)⟫_ℂ = ⟪g2 a a, f⟫_ℂ -
      ⟪g2 a a, χW.mul (χW.mul f)⟫_ℂ := inner_sub_right _ _ _
  have hc : ⟪g a - χW.mul (χW.mul (g a)), g a⟫_ℂ =
      -⟪g2 a a, f - χW.mul (χW.mul f)⟫_ℂ + ⟪g a, χW.mul ((dW a).mul f)⟫_ℂ +
        ⟪g a, (dW a).mul (χW.mul f)⟫_ℂ := by
    rw [hibp, t3, t1, t2, t4]
    ring
  have e1 : RCLike.re ⟪g a - χW.mul (χW.mul (g a)), g a⟫_ℂ =
      ‖g a‖ ^ 2 - ‖χW.mul (g a)‖ ^ 2 := by
    rw [inner_sub_left, χW.inner_mul_left, map_sub, inner_self_eq_norm_sq, inner_self_eq_norm_sq]
  have hnorm1 : |‖g a‖ ^ 2 - ‖χW.mul (g a)‖ ^ 2| ≤ ε * ‖g2 a a‖ + 2 * (X.D1 * ε) * ‖g a‖ := by
    rw [← e1, hc]
    refine (RCLike.abs_re_le_norm _).trans ?_
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_neg]
    have t5 : ‖⟪g2 a a, f - χW.mul (χW.mul f)⟫_ℂ‖ ≤ ‖g2 a a‖ * ε :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hU0 (norm_nonneg _))
    have t6 : ‖⟪g a, χW.mul ((dW a).mul f)⟫_ℂ‖ ≤ ‖g a‖ * (X.D1 * ε) :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hU1 (norm_nonneg _))
    have t7 : ‖⟪g a, (dW a).mul (χW.mul f)⟫_ℂ‖ ≤ ‖g a‖ * (X.D1 * ε) :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hU2 (norm_nonneg _))
    linarith
  -- add the gradient of the cutoff
  have hsq : ‖(dW a).mul f + χW.mul (g a)‖ ^ 2 = ‖(dW a).mul f‖ ^ 2 +
      2 * RCLike.re ⟪(dW a).mul f, χW.mul (g a)⟫_ℂ + ‖χW.mul (g a)‖ ^ 2 := norm_add_sq _ _
  have hre : |RCLike.re ⟪(dW a).mul f, χW.mul (g a)⟫_ℂ| ≤ X.D1 * ε * ‖g a‖ := by
    refine (RCLike.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    exact mul_le_mul hB hA (norm_nonneg _) (by positivity)
  have hB2 : ‖(dW a).mul f‖ ^ 2 ≤ X.D1 ^ 2 * ε * ‖f‖ := by
    have e := mul_le_mul hB hBf (norm_nonneg _) (by positivity)
    nlinarith [norm_nonneg ((dW a).mul f)]
  rw [hsq]
  have hre' := abs_le.mp hre
  have hn1 := abs_le.mp hnorm1
  rw [abs_le]
  constructor <;> nlinarith [norm_nonneg (g a), norm_nonneg f, norm_nonneg (g2 a a),
    sq_nonneg ‖(dW a).mul f‖]

end FreeLoc

/-! ## The localisation of the kinetic energy of one particle -/

section FreeTorus

variable {ν : Type} [Fintype ν]

omit [Fintype ν] in
/-- **The free-space kinetic energy against the transplanted one**: with `N` a bound for `‖f‖`,
`‖∂f‖` and `‖∂²f‖`, and wavefunction leakage `ε`,
`|(1/(2m_p)) Σ_c ‖∂_{p,c} f‖² - ⟨T(χf), T_p T(χf)⟩| ≤ (3/2)(1 + 4D₁ + D₁²) N ε`. -/
theorem free_torus_kin (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (X : Cutoff eta L)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ) (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    {f : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta}
    {g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad f g) (hg2 : ∀ b, HasWeakGrad (g b) (g2 b)) {ε : ℝ} (hε : 0 ≤ ε)
    (h0 : ∫ r in Boneᶜ, ‖f r‖ ^ 2 ≤ ε ^ 2) {N : ℝ} (hN0 : ‖f‖ ≤ N) (hN1 : ∀ a, ‖g a‖ ≤ N)
    (hN2 : ∀ a b, ‖g2 a b‖ ≤ N) (p : Fin eta) :
    |freeKinQ sys p g -
        (regKin sys (gF L) p).expect ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 hL f))| ≤
      3 / 2 * (1 + 4 * X.D1 + X.D1 ^ 2) * N * ε := by
  have hD1 : 0 ≤ X.D1 := (abs_nonneg _).trans (X.d1 0 (p, 0))
  have hN : 0 ≤ N := (norm_nonneg _).trans hN0
  have hm := sys.mass_pos p
  have hm1 := sys.one_le_mass p
  rw [regKin_expect_cut sys hL X hg p]
  unfold freeKinQ
  have hc : ∀ c : Fin 3, |‖g (p, c)‖ ^ 2 - ‖(X.d1W (p, c)).cutL2 hL f +
      X.chiW.cutL2 hL (g (p, c))‖ ^ 2| ≤ (1 + 4 * X.D1 + X.D1 ^ 2) * N * ε := by
    intro c
    rw [norm_cut_grad_eq X hL f (g (p, c)) (p, c)]
    refine (free_loc_coord hSm hBm hχB hSB hdS hg hg2 hε h0 (p, c)).trans ?_
    have e1 := hN2 (p, c) (p, c)
    have e2 := hN1 (p, c)
    have e3 : 4 * X.D1 * ‖g (p, c)‖ ≤ 4 * X.D1 * N := mul_le_mul_of_nonneg_left e2 (by positivity)
    have e4 : X.D1 ^ 2 * ‖f‖ ≤ X.D1 ^ 2 * N := mul_le_mul_of_nonneg_left hN0 (by positivity)
    have e5 : ε * (‖g2 (p, c) (p, c)‖ + 4 * X.D1 * ‖g (p, c)‖ + X.D1 ^ 2 * ‖f‖) ≤
        ε * ((1 + 4 * X.D1 + X.D1 ^ 2) * N) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hε
    linarith
  have hsum : |∑ c : Fin 3, (‖g (p, c)‖ ^ 2 - ‖(X.d1W (p, c)).cutL2 hL f +
      X.chiW.cutL2 hL (g (p, c))‖ ^ 2)| ≤ 3 * ((1 + 4 * X.D1 + X.D1 ^ 2) * N * ε) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun c _ => hc c).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
  have hinv : 1 / (2 * sys.mass p) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h0' : 0 ≤ (1 + 4 * X.D1 + X.D1 ^ 2) * N * ε := by positivity
  calc 1 / (2 * sys.mass p) * |∑ c : Fin 3, (‖g (p, c)‖ ^ 2 - ‖(X.d1W (p, c)).cutL2 hL f +
        X.chiW.cutL2 hL (g (p, c))‖ ^ 2)|
      ≤ 1 / 2 * (3 * ((1 + 4 * X.D1 + X.D1 ^ 2) * N * ε)) :=
        mul_le_mul hinv hsum (abs_nonneg _) (by norm_num)
    _ = 3 / 2 * (1 + 4 * X.D1 + X.D1 ^ 2) * N * ε := by ring

end FreeTorus

end KineticLog
