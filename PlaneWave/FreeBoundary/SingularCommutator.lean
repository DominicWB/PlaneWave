import PlaneWave.FreeBoundary.MassWeightedCutoff

/-!
# The cut initial state in `D(H_L²)`, part 3: the singular commutator

The non-Born–Oppenheimer interaction `V = Σ_{i<j} q_i q_j / |x_i - x_j|` (no clamped nuclei) and
its regularisation `V_ε = Σ_{i<j} q_i q_j (|x_i - x_j|² + ε²)^{-1/2}`. For a cutoff with the
mass-weighted cancellation (`DomCutoff`), the singular part of the double commutator,
`W = -Σ_a m_a⁻¹ ∂_aχ ∂_aV = Σ_{i<j} q_i q_j ⟨∇_iχ/m_i - ∇_jχ/m_j, x_i - x_j⟩ / |x_i - x_j|³`,
is a bounded multiple of the inverse distances: `|W| ≤ Σ_{i<j} |q_i q_j| C / |x_i - x_j|`.

* `pinv`, `pairPot`, `pinvε`, `pairPotε`: the inverse distances, the interaction and their
  regularisations;
* `hasFDerivAt_pinvε`, `dirD_pinvε`: the derivative of the regularised inverse distance;
* `sum_massGrad_inner`: `Σ_a m_{a}⁻¹ ∂_aχ ⟨y, ∂_a y⟩ = ⟨∇_iχ/m_i - ∇_jχ/m_j, y⟩`,
  `y = x_i - x_j`;
* `commWε`, `sum_dirD_pairPotε`: the regularised singular weight `W_ε`;
* `pairL2`, `hasL2PointwisePotential_pairL2`: `V u = Σ_{i<j} q_i q_j Y_{ij}` for the Hardy
  functions `Y_{ij} = u/|x_i - x_j|` in `L²`;
* `commBeta`, `DomCutoff.abs_commBeta_le`: `W = Σ_{i<j} β_{ij}/|x_i - x_j|` with
  `|β_{ij}| ≤ |q_i q_j| C`;
* **`singular_identity`**: the weak form of the singular term of `[V, [K, χ]] u`, from `V_ε` by
  dominated convergence (`tendsto_integral_pairPotε`, `tendsto_integral_commWε`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15

variable {eta : ℕ}

/-! ## Pair coordinates -/

section Pairs

/-- The position of particle `i` as a continuous linear map of the configuration. -/
noncomputable def particleCLM (i : Fin eta) : Rcfg eta →L[ℝ] E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun c => ContinuousLinearMap.proj (i, c))

lemma particleCLM_apply (i : Fin eta) (r : Rcfg eta) : particleCLM i r = particle r i := rfl

/-- The relative position `x_i - x_j` of a pair. -/
noncomputable def pairY (p : FiniteElectronPair eta) : Rcfg eta →L[ℝ] E3 :=
  particleCLM p.1.1 - particleCLM p.1.2

lemma pairY_apply (p : FiniteElectronPair eta) (r : Rcfg eta) :
    pairY p r = particle r p.1.1 - particle r p.1.2 := rfl

lemma particle_single (k i : Fin eta) (c : Fin 3) :
    particle (Pi.single (k, c) (1 : ℝ) : Rcfg eta) i =
      if k = i then EuclideanSpace.single c 1 else 0 := by
  ext d
  by_cases hk : k = i
  · subst hk
    by_cases hd : d = c
    · subst hd
      simp [particle]
    · simp [particle, hd]
  · simp [particle, hk]

/-- `⟨y, ∂_{(k,c)} y⟩ = (δ_{k i} - δ_{k j}) y_c` for `y = x_i - x_j`. -/
lemma inner_pairY_single (p : FiniteElectronPair eta) (r : Rcfg eta) (k : Fin eta) (c : Fin 3) :
    ⟪pairY p r, pairY p (Pi.single (k, c) 1)⟫_ℝ =
      (if k = p.1.1 then pairY p r c else 0) - (if k = p.1.2 then pairY p r c else 0) := by
  rw [pairY_apply (r := Pi.single (k, c) 1), particle_single, particle_single, inner_sub_right]
  congr 1
  · split_ifs <;> simp [EuclideanSpace.inner_single_right]
  · split_ifs <;> simp [EuclideanSpace.inner_single_right]

end Pairs

/-! ## The interaction and its regularisation -/

section Potential

/-- The inverse distance `|x_i - x_j|⁻¹` (`0` at coalescence). -/
noncomputable def pinv (p : FiniteElectronPair eta) (r : Rcfg eta) : ℝ := ‖pairY p r‖⁻¹

/-- The interaction `Σ_{i<j} q_i q_j / |x_i - x_j|`. -/
noncomputable def pairPot (q : Fin eta → ℝ) (r : Rcfg eta) : ℝ :=
  ∑ p : FiniteElectronPair eta, q p.1.1 * q p.1.2 * pinv p r

/-- The regularised inverse distance `(|x_i - x_j|² + ε²)^{-1/2}`. -/
noncomputable def pinvε (ε : ℝ) (p : FiniteElectronPair eta) (r : Rcfg eta) : ℝ :=
  (Real.sqrt (‖pairY p r‖ ^ 2 + ε ^ 2))⁻¹

/-- The regularised interaction. -/
noncomputable def pairPotε (q : Fin eta → ℝ) (ε : ℝ) (r : Rcfg eta) : ℝ :=
  ∑ p : FiniteElectronPair eta, q p.1.1 * q p.1.2 * pinvε ε p r

variable {ν : Type} [Fintype ν]

/-- Without clamped nuclei the free-space interaction is the pair interaction. -/
lemma freePot_eq_pairPot [IsEmpty ν] (sys : CoulombSystem eta ν) (P : ν → E3) (r : Rcfg eta) :
    freePot sys P r = pairPot sys.charge r := by
  unfold freePot potInf pairPot pinv
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [one_div, pairY_apply]

lemma sq_add_pos {ε : ℝ} (hε : 0 < ε) (y : E3) : 0 < ‖y‖ ^ 2 + ε ^ 2 := by positivity

lemma pinvε_pos {ε : ℝ} (hε : 0 < ε) (p : FiniteElectronPair eta) (r : Rcfg eta) :
    0 < pinvε ε p r :=
  inv_pos.mpr (Real.sqrt_pos.mpr (sq_add_pos hε _))

lemma pinvε_le_pinv (ε : ℝ) (p : FiniteElectronPair eta) {r : Rcfg eta}
    (hr : pairY p r ≠ 0) : pinvε ε p r ≤ pinv p r := by
  unfold pinvε pinv
  have hy : 0 < ‖pairY p r‖ := norm_pos_iff.mpr hr
  refine inv_anti₀ hy ?_
  calc ‖pairY p r‖ = Real.sqrt (‖pairY p r‖ ^ 2) := (Real.sqrt_sq hy.le).symm
    _ ≤ Real.sqrt (‖pairY p r‖ ^ 2 + ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

lemma tendsto_pinvε (p : FiniteElectronPair eta) {r : Rcfg eta} (hr : pairY p r ≠ 0) :
    Tendsto (fun n : ℕ => pinvε (1 / ((n : ℝ) + 1)) p r) atTop (𝓝 (pinv p r)) := by
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hy : 0 < ‖pairY p r‖ := norm_pos_iff.mpr hr
  have h1 : Tendsto (fun n : ℕ => ‖pairY p r‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) atTop
      (𝓝 (‖pairY p r‖ ^ 2 + 0 ^ 2)) := tendsto_const_nhds.add (hε.pow 2)
  have h2 := (Real.continuous_sqrt.tendsto _).comp h1
  have h3 : Real.sqrt (‖pairY p r‖ ^ 2 + 0 ^ 2) = ‖pairY p r‖ := by
    rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hy.le]
  rw [h3] at h2
  exact h2.inv₀ hy.ne'

/-! ### The derivative of the regularised inverse distance -/

lemma hasFDerivAt_pinvε {ε : ℝ} (hε : 0 < ε) (p : FiniteElectronPair eta) (r : Rcfg eta) :
    HasFDerivAt (pinvε ε p)
      (-((‖pairY p r‖ ^ 2 + ε ^ 2) * Real.sqrt (‖pairY p r‖ ^ 2 + ε ^ 2))⁻¹ •
        (innerSL ℝ (pairY p r)).comp (pairY p)) r := by
  set s := ‖pairY p r‖ ^ 2 + ε ^ 2 with hs
  have hs0 : 0 < s := sq_add_pos hε _
  have h1 : HasFDerivAt (fun x => ‖pairY p x‖ ^ 2 + ε ^ 2)
      (2 • (innerSL ℝ (pairY p r)).comp (pairY p)) r :=
    ((pairY p).hasFDerivAt.norm_sq).add_const _
  have h2 := h1.sqrt hs0.ne'
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have h3 := (hasDerivAt_inv hsq.ne').comp_hasFDerivAt r h2
  unfold pinvε
  refine h3.congr_fderiv ?_
  ext v
  simp only [FunLike.coe_smul, ContinuousLinearMap.coe_comp, Pi.smul_apply,
    Function.comp_apply, innerSL_apply_apply, smul_eq_mul]
  rw [Real.sq_sqrt hs0.le]
  field_simp
  ring

/-- `∂_a (|y|² + ε²)^{-1/2} = -⟨y, ∂_a y⟩ / ((|y|² + ε²)^{3/2})`, `y = x_i - x_j`. -/
lemma dirD_pinvε {ε : ℝ} (hε : 0 < ε) (p : FiniteElectronPair eta) (a : Fin eta × Fin 3)
    (r : Rcfg eta) :
    dirD a (pinvε ε p) r =
      -⟪pairY p r, pairY p (Pi.single a 1)⟫_ℝ /
        ((‖pairY p r‖ ^ 2 + ε ^ 2) * Real.sqrt (‖pairY p r‖ ^ 2 + ε ^ 2)) := by
  unfold dirD
  rw [(hasFDerivAt_pinvε hε p r).fderiv]
  simp only [FunLike.coe_smul, ContinuousLinearMap.coe_comp, Pi.smul_apply,
    Function.comp_apply, innerSL_apply_apply, smul_eq_mul]
  ring

lemma contDiff_pinvε {ε : ℝ} (hε : 0 < ε) (p : FiniteElectronPair eta) (n : ℕ) :
    ContDiff ℝ n (pinvε ε p) := by
  unfold pinvε
  have h1 : ContDiff ℝ n (fun x : Rcfg eta => ‖pairY p x‖ ^ 2 + ε ^ 2) :=
    (contDiff_norm_sq ℝ).comp (pairY p).contDiff |>.add contDiff_const
  have h2 := h1.sqrt fun x => (sq_add_pos hε _).ne'
  exact h2.inv fun x => (Real.sqrt_pos.mpr (sq_add_pos hε _)).ne'

lemma contDiff_pairPotε (q : Fin eta → ℝ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ContDiff ℝ n (pairPotε q ε) := by
  unfold pairPotε
  exact ContDiff.sum fun p _ => contDiff_const.mul (contDiff_pinvε hε p n)

lemma pairPotε_tendsto (q : Fin eta → ℝ) {r : Rcfg eta}
    (hr : ∀ p : FiniteElectronPair eta, pairY p r ≠ 0) :
    Tendsto (fun n : ℕ => pairPotε q (1 / ((n : ℝ) + 1)) r) atTop (𝓝 (pairPot q r)) := by
  unfold pairPotε pairPot
  exact tendsto_finsetSum _ fun p _ => (tendsto_pinvε p (hr p)).const_mul _

lemma abs_pairPotε_le (q : Fin eta → ℝ) {ε : ℝ} (hε : 0 < ε) {r : Rcfg eta}
    (hr : ∀ p : FiniteElectronPair eta, pairY p r ≠ 0) :
    |pairPotε q ε r| ≤ ∑ p : FiniteElectronPair eta, |q p.1.1 * q p.1.2| * pinv p r := by
  unfold pairPotε
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul, abs_of_pos (pinvε_pos hε p r)]
  exact mul_le_mul_of_nonneg_left (pinvε_le_pinv ε p (hr p)) (abs_nonneg _)

end Potential

/-! ## The mass-weighted combination -/

section Combination

/-- `Σ_a m_a⁻¹ ∂_aχ ⟨y, ∂_a y⟩ = ⟨∇_iχ/m_i - ∇_jχ/m_j, y⟩` for `y = x_i - x_j`. -/
lemma sum_massGrad_inner (m : Fin eta → ℝ) (χ : Rcfg eta → ℝ) (p : FiniteElectronPair eta)
    (r : Rcfg eta) :
    ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * dirD a χ r * ⟪pairY p r, pairY p (Pi.single a 1)⟫_ℝ =
      ⟪massGrad m χ p.1.1 r - massGrad m χ p.1.2 r, pairY p r⟫_ℝ := by
  rw [Fintype.sum_prod_type]
  simp_rw [inner_pairY_single, mul_sub, Finset.sum_sub_distrib]
  rw [inner_sub_left, PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial, massGrad_apply]
  congr 1
  · rw [Finset.sum_comm]
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_ite_eq' Finset.univ p.1.1
      (fun k => (m k)⁻¹ * dirD (k, c) χ r * pairY p r c)]
    simp only [Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun c _ => by ring
  · rw [Finset.sum_comm]
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_ite_eq' Finset.univ p.1.2
      (fun k => (m k)⁻¹ * dirD (k, c) χ r * pairY p r c)]
    simp only [Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun c _ => by ring

/-- The regularised singular weight
`W_ε = Σ_{i<j} q_i q_j ⟨∇_iχ/m_i - ∇_jχ/m_j, y⟩ / ((|y|² + ε²)^{3/2})`. -/
noncomputable def commWε (m q : Fin eta → ℝ) (χ : Rcfg eta → ℝ) (ε : ℝ) (r : Rcfg eta) : ℝ :=
  ∑ p : FiniteElectronPair eta, q p.1.1 * q p.1.2 *
    (⟪massGrad m χ p.1.1 r - massGrad m χ p.1.2 r, pairY p r⟫_ℝ /
      ((‖pairY p r‖ ^ 2 + ε ^ 2) * Real.sqrt (‖pairY p r‖ ^ 2 + ε ^ 2)))

/-- **The singular combination**: `-Σ_a m_a⁻¹ ∂_aχ ∂_aV_ε = W_ε`. -/
lemma sum_dirD_pairPotε (m q : Fin eta → ℝ) (χ : Rcfg eta → ℝ) {ε : ℝ} (hε : 0 < ε)
    (r : Rcfg eta) :
    ∑ a : Fin eta × Fin 3, (-(m a.1)⁻¹) * dirD a χ r * dirD a (pairPotε q ε) r =
      commWε m q χ ε r := by
  have hd : ∀ p ∈ (Finset.univ : Finset (FiniteElectronPair eta)),
      DifferentiableAt ℝ (fun x => q p.1.1 * q p.1.2 * pinvε ε p x) r := fun p _ =>
    (((contDiff_pinvε hε p 1).differentiable (by norm_num)) r).const_mul _
  have hdV : ∀ a, dirD a (pairPotε q ε) r =
      ∑ p : FiniteElectronPair eta, q p.1.1 * q p.1.2 * dirD a (pinvε ε p) r := by
    intro a
    have e : pairPotε q ε = fun x => ∑ p : FiniteElectronPair eta, q p.1.1 * q p.1.2 *
        pinvε ε p x := rfl
    rw [e, dirD_sum_fun _ hd a]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold dirD
    rw [fderiv_const_mul (((contDiff_pinvε hε p 1).differentiable (by norm_num)) r)]
    rfl
  simp_rw [hdV, dirD_pinvε hε, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold commWε
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← sum_massGrad_inner m χ p r, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **The bound of the regularised weight** under the mass-weighted cancellation:
`|W_ε| ≤ Σ_{i<j} |q_i q_j| C / |x_i - x_j|`. -/
lemma abs_commWε_le {L : ℝ} {m : Fin eta → ℝ} (X : DomCutoff eta L m) (q : Fin eta → ℝ)
    {ε : ℝ} (hε : 0 < ε) {r : Rcfg eta} (hr : ∀ p : FiniteElectronPair eta, pairY p r ≠ 0) :
    |commWε m q X.χ ε r| ≤ ∑ p : FiniteElectronPair eta, |q p.1.1 * q p.1.2| * X.C * pinv p r := by
  unfold commWε
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  have hy : 0 < ‖pairY p r‖ := norm_pos_iff.mpr (hr p)
  set y := ‖pairY p r‖ with hydef
  set s := y ^ 2 + ε ^ 2 with hsdef
  have hs : 0 < s := by positivity
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hys : y ≤ Real.sqrt s := by
    calc y = Real.sqrt (y ^ 2) := (Real.sqrt_sq hy.le).symm
      _ ≤ Real.sqrt s := Real.sqrt_le_sqrt (by nlinarith)
  have hcan := X.abs_inner_cancel_le r p.1.1 p.1.2
  rw [← pairY_apply] at hcan
  rw [abs_mul, abs_div, abs_of_pos (mul_pos hs hsq), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [div_le_iff₀ (mul_pos hs hsq)]
  unfold pinv
  rw [← hydef]
  calc |⟪massGrad m X.χ p.1.1 r - massGrad m X.χ p.1.2 r, pairY p r⟫_ℝ| ≤ X.C * y ^ 2 := hcan
    _ ≤ X.C * y⁻¹ * (s * Real.sqrt s) := by
        have hC := X.C_nonneg
        have h1 : y ^ 2 ≤ y⁻¹ * (s * Real.sqrt s) := by
          rw [le_inv_mul_iff₀ hy]
          have : y ^ 3 ≤ s * Real.sqrt s := by
            have h2 : y ^ 2 ≤ s := by nlinarith
            calc y ^ 3 = y ^ 2 * y := by ring
              _ ≤ s * Real.sqrt s := mul_le_mul h2 hys hy.le hs.le
          nlinarith
        calc X.C * y ^ 2 ≤ X.C * (y⁻¹ * (s * Real.sqrt s)) := mul_le_mul_of_nonneg_left h1 hC
          _ = X.C * y⁻¹ * (s * Real.sqrt s) := by ring

end Combination

/-! ## Coalescences are null -/

section Null

lemma pinv_nonneg (p : FiniteElectronPair eta) (r : Rcfg eta) : 0 ≤ pinv p r :=
  inv_nonneg.mpr (norm_nonneg _)

lemma volume_pairY_zero (p : FiniteElectronPair eta) :
    volume {r : Rcfg eta | pairY p r = 0} = 0 := by
  have hij : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  let ℓ : Rcfg eta →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin eta × Fin 3 => ℝ) (p.1.1, (0 : Fin 3)) -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin eta × Fin 3 => ℝ) (p.1.2, (0 : Fin 3))
  have hsub : {r : Rcfg eta | pairY p r = 0} ⊆ (LinearMap.ker ℓ : Set (Rcfg eta)) := by
    intro r hr
    have h0 : (pairY p r) 0 = 0 := by
      rw [show pairY p r = 0 from hr]
      rfl
    rw [pairY_apply] at h0
    show ℓ r = 0
    simpa [ℓ, particle] using h0
  have hne : LinearMap.ker ℓ ≠ ⊤ := by
    intro h
    have hmem : (Pi.single (p.1.1, (0 : Fin 3)) (1 : ℝ) : Rcfg eta) ∈ LinearMap.ker ℓ := by
      rw [h]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker] at hmem
    have hne' : (p.1.2, (0 : Fin 3)) ≠ (p.1.1, 0) := fun h => hij (Prod.mk.inj h).1.symm
    simp [ℓ, hne'] at hmem
  exact measure_mono_null hsub (Measure.addHaar_submodule volume _ hne)

/-- Almost every configuration has no coalescence. -/
lemma ae_pairY_ne : ∀ᵐ r : Rcfg eta, ∀ p : FiniteElectronPair eta, pairY p r ≠ 0 := by
  rw [ae_all_iff]
  intro p
  exact (measure_eq_zero_iff_ae_notMem.mp (volume_pairY_zero p)).mono fun r hr => hr

end Null

/-! ## The square-integrable Coulomb images -/

section Images

/-- `Σ_{i<j} q_i q_j F_{ij}`, for the Hardy functions `F_{ij} = f / |x_i - x_j|` of `f`: the
`L²` image `V f`. -/
noncomputable def pairL2 (q : Fin eta → ℝ) (F : FiniteElectronPair eta → FreeL2 eta) :
    FreeL2 eta :=
  ∑ p : FiniteElectronPair eta, ((q p.1.1 * q p.1.2 : ℝ) : ℂ) • F p

lemma pairL2_ae (q : Fin eta → ℝ) {f : FreeL2 eta} {F : FiniteElectronPair eta → FreeL2 eta}
    (hF : ∀ p, ∀ᵐ r, F p r = (pinv p r : ℂ) * f r) :
    ∀ᵐ r, pairL2 q F r = (pairPot q r : ℂ) * f r := by
  have hs := Lp.coeFn_finsetSum (Finset.univ : Finset (FiniteElectronPair eta))
    (fun p => ((q p.1.1 * q p.1.2 : ℝ) : ℂ) • F p)
  have hall : ∀ᵐ r, ∀ p : FiniteElectronPair eta, F p r = (pinv p r : ℂ) * f r :=
    ae_all_iff.mpr hF
  have hsm : ∀ᵐ r, ∀ p : FiniteElectronPair eta,
      (((q p.1.1 * q p.1.2 : ℝ) : ℂ) • F p) r = ((q p.1.1 * q p.1.2 : ℝ) : ℂ) * F p r :=
    ae_all_iff.mpr fun p => (Lp.coeFn_smul _ (F p)).mono fun r hr => by rw [hr]; rfl
  filter_upwards [hs, hall, hsm] with r h1 h2 h3
  unfold pairL2
  rw [h1, Finset.sum_apply]
  simp only [h3, h2]
  unfold pairPot
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- `V f = pairL2` is the pointwise Coulomb image (no clamped nuclei). -/
lemma hasL2PointwisePotential_pairL2 {ν : Type} [Fintype ν] [IsEmpty ν]
    (sys : CoulombSystem eta ν) (P : ν → E3) {f : FreeL2 eta}
    {F : FiniteElectronPair eta → FreeL2 eta} (hF : ∀ p, ∀ᵐ r, F p r = (pinv p r : ℂ) * f r) :
    HasL2PointwisePotential volume (fun r => (freePot sys P r : ℂ)) f (pairL2 sys.charge F) := by
  filter_upwards [pairL2_ae sys.charge hF] with r hr
  rw [hr, freePot_eq_pairPot]

lemma integrable_indicator_norm_mul {K : Set (Rcfg eta)} (hK : IsCompact K)
    {Ψ : Rcfg eta → ℂ} (hΨ : Continuous Ψ) (f : FreeL2 eta) :
    Integrable (K.indicator fun r => ‖Ψ r‖ * ‖f r‖) := by
  have hf : IntegrableOn (fun r => ‖f r‖) K :=
    ((Lp.memLp f).norm.locallyIntegrable (by norm_num)).integrableOn_isCompact hK
  exact (hf.continuousOn_mul hΨ.norm.continuousOn hK).integrable_indicator hK.measurableSet

/-- **Convergence of the regularised Coulomb terms**: for `ω` continuous of compact support and
`f` with Hardy functions `F`, `∫ ω V_ε f → ∫ ω V f`. -/
lemma tendsto_integral_pairPotε (q : Fin eta → ℝ) {ω : Rcfg eta → ℂ} (hω : Continuous ω)
    (hωc : HasCompactSupport ω) {f : FreeL2 eta} {F : FiniteElectronPair eta → FreeL2 eta}
    (hF : ∀ p, ∀ᵐ r, F p r = (pinv p r : ℂ) * f r) :
    Tendsto (fun n : ℕ => ∫ r, ω r * ((pairPotε q (1 / ((n : ℝ) + 1)) r : ℂ) * f r)) atTop
      (𝓝 (∫ r, ω r * pairL2 q F r)) := by
  have hall : ∀ᵐ r, ∀ p : FiniteElectronPair eta, F p r = (pinv p r : ℂ) * f r :=
    ae_all_iff.mpr hF
  have hpl := pairL2_ae q hF
  refine tendsto_integral_of_dominated_convergence
    (fun r => ∑ p : FiniteElectronPair eta, |q p.1.1 * q p.1.2| * ‖ω r * F p r‖) ?_ ?_ ?_ ?_
  · intro n
    have hc : Continuous fun r => (pairPotε q (1 / ((n : ℝ) + 1)) r : ℂ) :=
      Complex.continuous_ofReal.comp (contDiff_pairPotε q (by positivity) 0).continuous
    exact hω.aestronglyMeasurable.mul (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  · exact integrable_finsetSum _ fun p _ =>
      ((integrable_cont_mul_L2 hω hωc (F p)).norm).const_mul _
  · intro n
    filter_upwards [ae_pairY_ne, hall] with r hr hFr
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖ω r‖ * (|pairPotε q (1 / ((n : ℝ) + 1)) r| * ‖f r‖)
        ≤ ‖ω r‖ * ((∑ p : FiniteElectronPair eta, |q p.1.1 * q p.1.2| * pinv p r) * ‖f r‖) := by
          gcongr
          exact abs_pairPotε_le q (by positivity) hr
      _ = ∑ p : FiniteElectronPair eta, |q p.1.1 * q p.1.2| * ‖ω r * F p r‖ := by
          rw [Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hFr p, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (pinv_nonneg p r)]
          ring
  · filter_upwards [ae_pairY_ne, hpl] with r hr hpr
    rw [hpr]
    have h2 : Tendsto (fun n : ℕ => ((pairPotε q (1 / ((n : ℝ) + 1)) r : ℝ) : ℂ)) atTop
        (𝓝 (pairPot q r : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (pairPotε_tendsto q hr)
    exact (h2.mul_const (f r)).const_mul (ω r)

end Images

/-! ## The singular weight -/

section Weight

/-- The singular weight `β_{ij} = q_i q_j ⟨∇_iχ/m_i - ∇_jχ/m_j, y⟩ / |y|²`, `y = x_i - x_j`: the
singular part of the double commutator is `W = Σ_{i<j} β_{ij} / |x_i - x_j|`. -/
noncomputable def commBeta (m q : Fin eta → ℝ) (χ : Rcfg eta → ℝ) (p : FiniteElectronPair eta)
    (r : Rcfg eta) : ℝ :=
  q p.1.1 * q p.1.2 *
    (⟪massGrad m χ p.1.1 r - massGrad m χ p.1.2 r, pairY p r⟫_ℝ / ‖pairY p r‖ ^ 2)

lemma dirD_eq_zero_of_notMem {χ : Rcfg eta → ℝ} {r : Rcfg eta} (hr : r ∉ tsupport χ)
    (a : Fin eta × Fin 3) : dirD a χ r = 0 := by
  by_contra h
  exact hr (mem_tsupport_of_dirD_ne h)

lemma massGrad_eq_zero_of_notMem (m : Fin eta → ℝ) {χ : Rcfg eta → ℝ} {r : Rcfg eta}
    (hr : r ∉ tsupport χ) (i : Fin eta) : massGrad m χ i r = 0 := by
  ext c
  rw [massGrad_apply, dirD_eq_zero_of_notMem hr]
  simp

lemma commWε_eq_zero_of_notMem (m q : Fin eta → ℝ) {χ : Rcfg eta → ℝ} (ε : ℝ)
    {r : Rcfg eta} (hr : r ∉ tsupport χ) : commWε m q χ ε r = 0 := by
  unfold commWε
  simp [massGrad_eq_zero_of_notMem m hr]

lemma commBeta_eq_zero_of_notMem (m q : Fin eta → ℝ) {χ : Rcfg eta → ℝ}
    (p : FiniteElectronPair eta) {r : Rcfg eta} (hr : r ∉ tsupport χ) :
    commBeta m q χ p r = 0 := by
  unfold commBeta
  simp [massGrad_eq_zero_of_notMem m hr]

lemma DomCutoff.abs_commBeta_le {L : ℝ} {m : Fin eta → ℝ} (X : DomCutoff eta L m) (q : Fin eta → ℝ)
    (p : FiniteElectronPair eta) (r : Rcfg eta) :
    |commBeta m q X.χ p r| ≤ |q p.1.1 * q p.1.2| * X.C := by
  unfold commBeta
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rcases eq_or_ne (pairY p r) 0 with h0 | h0
  · rw [h0]
    simp [X.C_nonneg]
  · have hy : 0 < ‖pairY p r‖ ^ 2 := by positivity
    have hcan := X.abs_inner_cancel_le r p.1.1 p.1.2
    rw [← pairY_apply] at hcan
    rw [abs_div, abs_of_pos hy, div_le_iff₀ hy]
    exact hcan

lemma DomCutoff.continuous_massGrad {L : ℝ} {m : Fin eta → ℝ} (X : DomCutoff eta L m)
    (i : Fin eta) : Continuous (massGrad m X.χ i) := by
  unfold massGrad
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun c =>
    continuous_const.mul (continuous_dirD X.smooth (by norm_num) (i, c)))

lemma DomCutoff.measurable_commBeta {L : ℝ} {m : Fin eta → ℝ} (X : DomCutoff eta L m)
    (q : Fin eta → ℝ) (p : FiniteElectronPair eta) : Measurable (commBeta m q X.χ p) := by
  unfold commBeta
  have h1 : Continuous fun r =>
      ⟪massGrad m X.χ p.1.1 r - massGrad m X.χ p.1.2 r, pairY p r⟫_ℝ :=
    ((X.continuous_massGrad _).sub (X.continuous_massGrad _)).inner (pairY p).continuous
  have h2 : Continuous fun r => ‖pairY p r‖ ^ 2 := ((pairY p).continuous.norm).pow 2
  exact measurable_const.mul (h1.measurable.div h2.measurable)

lemma tendsto_commWε (m q : Fin eta → ℝ) (χ : Rcfg eta → ℝ) {r : Rcfg eta}
    (hr : ∀ p : FiniteElectronPair eta, pairY p r ≠ 0) :
    Tendsto (fun n : ℕ => commWε m q χ (1 / ((n : ℝ) + 1)) r) atTop
      (𝓝 (∑ p : FiniteElectronPair eta, commBeta m q χ p r * pinv p r)) := by
  unfold commWε
  refine tendsto_finsetSum _ fun p _ => ?_
  have hy : 0 < ‖pairY p r‖ := norm_pos_iff.mpr (hr p)
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun n : ℕ => ‖pairY p r‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2) atTop
      (𝓝 (‖pairY p r‖ ^ 2 + 0 ^ 2)) := tendsto_const_nhds.add (hε.pow 2)
  rw [zero_pow two_ne_zero, add_zero] at h1
  have h2 := (Real.continuous_sqrt.tendsto _).comp h1
  rw [Real.sqrt_sq hy.le] at h2
  have h3 := h1.mul h2
  have h4 := (tendsto_const_nhds (x := q p.1.1 * q p.1.2 *
    ⟪massGrad m χ p.1.1 r - massGrad m χ p.1.2 r, pairY p r⟫_ℝ)).div h3 (by positivity)
  have e : commBeta m q χ p r * pinv p r = q p.1.1 * q p.1.2 *
      ⟪massGrad m χ p.1.1 r - massGrad m χ p.1.2 r, pairY p r⟫_ℝ /
        (‖pairY p r‖ ^ 2 * ‖pairY p r‖) := by
    unfold commBeta pinv
    field_simp
  rw [e]
  refine h4.congr fun n => ?_
  simp only [Function.comp_apply, Pi.div_apply]
  ring

/-- **Convergence of the singular term**: `∫ Ψ W_ε u → Σ_{i<j} ∫ Ψ β_{ij} F_{ij}`,
`F_{ij} = u / |x_i - x_j|`. -/
lemma tendsto_integral_commWε {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m)
    (q : Fin eta → ℝ) {Ψ : Rcfg eta → ℂ} (hΨ : Continuous Ψ) {u : FreeL2 eta}
    {Y : FiniteElectronPair eta → FreeL2 eta} (hY : ∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * u r) :
    Tendsto (fun n : ℕ => ∫ r, Ψ r * ((commWε m q X.χ (1 / ((n : ℝ) + 1)) r : ℂ) * u r)) atTop
      (𝓝 (∑ p : FiniteElectronPair eta, ∫ r, Ψ r * ((commBeta m q X.χ p r : ℂ) * Y p r))) := by
  have hK : IsCompact (tsupport X.χ) := X.hasCompactSupport hL
  have hall : ∀ᵐ r, ∀ p : FiniteElectronPair eta, Y p r = (pinv p r : ℂ) * u r :=
    ae_all_iff.mpr hY
  have hbint : ∀ p : FiniteElectronPair eta,
      Integrable fun r => Ψ r * ((commBeta m q X.χ p r : ℂ) * Y p r) := by
    intro p
    have hmeas : AEStronglyMeasurable (fun r => Ψ r * ((commBeta m q X.χ p r : ℂ) * Y p r)) :=
      hΨ.aestronglyMeasurable.mul ((Complex.continuous_ofReal.measurable.comp
        (X.measurable_commBeta q p)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable (Y p)))
    refine ((integrable_indicator_norm_mul hK hΨ (Y p)).const_mul
      (|q p.1.1 * q p.1.2| * X.C)).mono' hmeas (ae_of_all _ fun r => ?_)
    by_cases hr : r ∈ tsupport X.χ
    · rw [indicator_of_mem hr, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := X.abs_commBeta_le q p r
      calc ‖Ψ r‖ * (|commBeta m q X.χ p r| * ‖Y p r‖)
          ≤ ‖Ψ r‖ * (|q p.1.1 * q p.1.2| * X.C * ‖Y p r‖) := by gcongr
        _ = |q p.1.1 * q p.1.2| * X.C * (‖Ψ r‖ * ‖Y p r‖) := by ring
    · rw [indicator_of_notMem hr, commBeta_eq_zero_of_notMem m q p hr]
      simp
  have hlim : ∫ r, Ψ r * (((∑ p : FiniteElectronPair eta, commBeta m q X.χ p r * pinv p r : ℝ)
      : ℂ) * u r) = ∑ p : FiniteElectronPair eta,
        ∫ r, Ψ r * ((commBeta m q X.χ p r : ℂ) * Y p r) := by
    rw [← integral_finsetSum _ fun p _ => hbint p]
    refine integral_congr_ae ?_
    filter_upwards [hall] with r hr
    push_cast
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hr p]
    ring
  rw [← hlim]
  refine tendsto_integral_of_dominated_convergence
    (fun r => ∑ p : FiniteElectronPair eta, |q p.1.1 * q p.1.2| * X.C *
      (tsupport X.χ).indicator (fun r => ‖Ψ r‖ * ‖Y p r‖) r) ?_ ?_ ?_ ?_
  · intro n
    have hc : Continuous fun r => (commWε m q X.χ (1 / ((n : ℝ) + 1)) r : ℂ) := by
      refine Complex.continuous_ofReal.comp ?_
      unfold commWε
      refine continuous_finsetSum _ fun p _ => continuous_const.mul ?_
      have h1 : Continuous fun r =>
          ⟪massGrad m X.χ p.1.1 r - massGrad m X.χ p.1.2 r, pairY p r⟫_ℝ :=
        ((X.continuous_massGrad _).sub (X.continuous_massGrad _)).inner (pairY p).continuous
      have h2 : Continuous fun r => ‖pairY p r‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2 :=
        ((pairY p).continuous.norm.pow 2).add continuous_const
      refine h1.div (h2.mul h2.sqrt) fun r => ?_
      have hs : 0 < ‖pairY p r‖ ^ 2 + (1 / ((n : ℝ) + 1)) ^ 2 := sq_add_pos (by positivity) _
      exact (mul_pos hs (Real.sqrt_pos.mpr hs)).ne'
    exact hΨ.aestronglyMeasurable.mul (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  · exact integrable_finsetSum _ fun p _ =>
      (integrable_indicator_norm_mul hK hΨ (Y p)).const_mul _
  · intro n
    filter_upwards [ae_pairY_ne, hall] with r hr hYr
    by_cases hrK : r ∈ tsupport X.χ
    · simp only [indicator_of_mem hrK]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hW := abs_commWε_le X q (ε := 1 / ((n : ℝ) + 1)) (by positivity) hr
      calc ‖Ψ r‖ * (|commWε m q X.χ (1 / ((n : ℝ) + 1)) r| * ‖u r‖)
          ≤ ‖Ψ r‖ * ((∑ p : FiniteElectronPair eta, |q p.1.1 * q p.1.2| * X.C * pinv p r) *
              ‖u r‖) := by gcongr
        _ = ∑ p : FiniteElectronPair eta, |q p.1.1 * q p.1.2| * X.C * (‖Ψ r‖ * ‖Y p r‖) := by
            rw [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hYr p, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (pinv_nonneg p r)]
            ring
    · simp only [indicator_of_notMem hrK, mul_zero, Finset.sum_const_zero]
      rw [commWε_eq_zero_of_notMem m q _ hrK]
      simp
  · filter_upwards [ae_pairY_ne] with r hr
    have h2 := (Complex.continuous_ofReal.tendsto _).comp (tendsto_commWε m q X.χ hr)
    exact (h2.mul_const (u r)).const_mul (Ψ r)

end Weight

/-! ## The singular identity -/

section Identity

lemma dirD_mul_real {f g : Rcfg eta → ℝ} {x : Rcfg eta} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (a : Fin eta × Fin 3) :
    dirD a (fun y => f y * g y) x = dirD a f x * g x + f x * dirD a g x := by
  unfold dirD
  rw [fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

variable {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m) (q : Fin eta → ℝ)
include hL

/-- The regularised identity for one coordinate `a`, from the weak gradient tested with
`∂_aχ V_ε Ψ`. -/
lemma regularised_identity_one {ε : ℝ} (hε : 0 < ε) {u : FreeL2 eta}
    {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad u g) {Ψ : Rcfg eta → ℂ}
    (hΨ : ContDiff ℝ 1 Ψ) (a : Fin eta × Fin 3) :
    (∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r * pairPotε q ε r : ℝ) : ℂ) * u r)) +
        ∫ r, conj (dirD a Ψ r) * (((dirD a X.χ r * pairPotε q ε r : ℝ) : ℂ) * u r) =
      -(∫ r, conj (Ψ r) * (((dirD a X.χ r * pairPotε q ε r : ℝ) : ℂ) * g a r)) -
        ∫ r, conj (Ψ r) * (((dirD a X.χ r * dirD a (pairPotε q ε) r : ℝ) : ℂ) * u r) := by
  have hV1 : ContDiff ℝ 1 (pairPotε q ε) := contDiff_pairPotε q hε 1
  have hχ1 : ContDiff ℝ 1 (dirD a X.χ) := (X.c1 a).of_le (by norm_num)
  have hζ : ContDiff ℝ 1 (fun r => dirD a X.χ r * pairPotε q ε r) := hχ1.mul hV1
  have hcsχ : HasCompactSupport (dirD a X.χ) := X.hcs_of_sub hL (X.ts1 a)
  have hcs2 : HasCompactSupport (dirD a (dirD a X.χ)) := X.hcs_of_sub hL (X.ts2 a a)
  have hζc : HasCompactSupport (fun r => dirD a X.χ r * pairPotε q ε r) := hcsχ.mul_right
  have hibp := ibp_weight hg hζ hζc hΨ a
  have hdζ : ∀ r, dirD a (fun r => dirD a X.χ r * pairPotε q ε r) r =
      dirD a (dirD a X.χ) r * pairPotε q ε r + dirD a X.χ r * dirD a (pairPotε q ε) r :=
    fun r => dirD_mul_real ((hχ1.differentiable (by norm_num)) r)
      ((hV1.differentiable (by norm_num)) r) a
  have hΨc : Continuous Ψ := hΨ.continuous
  have hVc : Continuous (pairPotε q ε) := hV1.continuous
  have hdVc : Continuous (dirD a (pairPotε q ε)) := continuous_dirD hV1 (by norm_num) a
  have hc2 : Continuous (dirD a (dirD a X.χ)) := continuous_dirD (X.c1 a) (by norm_num) a
  have hI1 : Integrable fun r =>
      conj (Ψ r) * (((dirD a (dirD a X.χ) r * pairPotε q ε r : ℝ) : ℂ) * u r) :=
    integrable_conj_mul_weight hΨc (hc2.mul hVc) hcs2.mul_right u
  have hI2 : Integrable fun r =>
      conj (Ψ r) * (((dirD a X.χ r * dirD a (pairPotε q ε) r : ℝ) : ℂ) * u r) :=
    integrable_conj_mul_weight hΨc (hχ1.continuous.mul hdVc) hcsχ.mul_right u
  have hsplit : ∫ r, conj (Ψ r) * (((dirD a (fun r => dirD a X.χ r * pairPotε q ε r) r : ℝ) :
      ℂ) * u r) = (∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r * pairPotε q ε r : ℝ) : ℂ) * u r)) +
        ∫ r, conj (Ψ r) * (((dirD a X.χ r * dirD a (pairPotε q ε) r : ℝ) : ℂ) * u r) := by
    rw [← integral_add hI1 hI2]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [hdζ]
    push_cast
    ring
  rw [hsplit] at hibp
  linear_combination hibp

/-- **The regularised identity**: with `w_a = -m_a⁻¹`,
`Σ_a w_a (∫ conj(Ψ) ∂_a²χ V_ε u + ∫ conj(∂_aΨ) ∂_aχ V_ε u)
  = -Σ_a w_a ∫ conj(Ψ) ∂_aχ V_ε g_a - ∫ conj(Ψ) W_ε u`. -/
lemma regularised_identity {ε : ℝ} (hε : 0 < ε) {u : FreeL2 eta}
    {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad u g) {Ψ : Rcfg eta → ℂ}
    (hΨ : ContDiff ℝ 1 Ψ) :
    ∑ a : Fin eta × Fin 3, ((-(m a.1)⁻¹ : ℝ) : ℂ) *
        ((∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r * pairPotε q ε r : ℝ) : ℂ) * u r)) +
          ∫ r, conj (dirD a Ψ r) * (((dirD a X.χ r * pairPotε q ε r : ℝ) : ℂ) * u r)) =
      -(∑ a : Fin eta × Fin 3, ((-(m a.1)⁻¹ : ℝ) : ℂ) *
          ∫ r, conj (Ψ r) * (((dirD a X.χ r * pairPotε q ε r : ℝ) : ℂ) * g a r)) -
        ∫ r, conj (Ψ r) * ((commWε m q X.χ ε r : ℂ) * u r) := by
  simp_rw [regularised_identity_one hL X q hε hg hΨ]
  have hV1 : ContDiff ℝ 1 (pairPotε q ε) := contDiff_pairPotε q hε 1
  have hI : ∀ a : Fin eta × Fin 3, Integrable fun r => ((-(m a.1)⁻¹ : ℝ) : ℂ) *
      (conj (Ψ r) * (((dirD a X.χ r * dirD a (pairPotε q ε) r : ℝ) : ℂ) * u r)) := by
    intro a
    refine (integrable_conj_mul_weight hΨ.continuous
      (((X.c1 a).of_le (by norm_num) : ContDiff ℝ 1 (dirD a X.χ)).continuous.mul
        (continuous_dirD hV1 (by norm_num) a))
      (X.hcs_of_sub hL (X.ts1 a)).mul_right u).const_mul _
  have hW : ∫ r, conj (Ψ r) * ((commWε m q X.χ ε r : ℂ) * u r) =
      ∑ a : Fin eta × Fin 3, ((-(m a.1)⁻¹ : ℝ) : ℂ) *
        ∫ r, conj (Ψ r) * (((dirD a X.χ r * dirD a (pairPotε q ε) r : ℝ) : ℂ) * u r) := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun a _ => hI a]
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only
    rw [← sum_dirD_pairPotε m q X.χ hε r]
    push_cast
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hW, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **The singular identity** (non-Born–Oppenheimer, mass-weighted cancellation): for `u` with
weak gradient `g`, Hardy functions `Y_{ij} = u/|x_i - x_j|`, `Z_{ij,a} = g_a/|x_i - x_j|`, and
`Ψ ∈ C¹`, with `w_a = -m_a⁻¹`,
`Σ_a w_a (∫ conj(Ψ) ∂_a²χ V u + ∫ conj(∂_aΨ) ∂_aχ V u)
  = -Σ_a w_a ∫ conj(Ψ) ∂_aχ V g_a - Σ_{i<j} ∫ conj(Ψ) β_{ij} Y_{ij}`,
where `V u = pairL2 q Y` and `V g_a = pairL2 q Z_{·,a}`: the distributional derivative
`Σ_a w_a ∂_aχ ∂_a(V u)` is `Σ_a w_a ∂_aχ V g_a + W u` with `W u = Σ β_{ij} Y_{ij} ∈ L²`. -/
theorem singular_identity {u : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad u g) {Y : FiniteElectronPair eta → FreeL2 eta}
    (hY : ∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * u r)
    {Z : FiniteElectronPair eta → Fin eta × Fin 3 → FreeL2 eta}
    (hZ : ∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * g a r) {Ψ : Rcfg eta → ℂ}
    (hΨ : ContDiff ℝ 1 Ψ) :
    ∑ a : Fin eta × Fin 3, ((-(m a.1)⁻¹ : ℝ) : ℂ) *
        ((∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r : ℝ) : ℂ) * pairL2 q Y r)) +
          ∫ r, conj (dirD a Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) * pairL2 q Y r)) =
      -(∑ a : Fin eta × Fin 3, ((-(m a.1)⁻¹ : ℝ) : ℂ) *
          ∫ r, conj (Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) * pairL2 q (fun p => Z p a) r)) -
        ∑ p : FiniteElectronPair eta, ∫ r, conj (Ψ r) * ((commBeta m q X.χ p r : ℂ) * Y p r) := by
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
  -- the limits of the four kinds of terms
  have T1 : ∀ a, Tendsto (fun n : ℕ => ∫ r, conj (Ψ r) *
      (((dirD a (dirD a X.χ) r * pairPotε q (1 / ((n : ℝ) + 1)) r : ℝ) : ℂ) * u r)) atTop
      (𝓝 (∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r : ℝ) : ℂ) * pairL2 q Y r))) := by
    intro a
    have h := tendsto_integral_pairPotε q (hcΨ.mul (hc2 a)) (hcs2 a).mul_left (f := u) hY
    have e : (∫ r, conj (Ψ r) * (((dirD a (dirD a X.χ) r : ℝ) : ℂ) * pairL2 q Y r)) =
        ∫ r, ((fun r => conj (Ψ r)) * fun r => ((dirD a (dirD a X.χ) r : ℝ) : ℂ)) r *
          pairL2 q Y r :=
      integral_congr_ae (ae_of_all _ fun r => by simp only [Pi.mul_apply]; ring)
    rw [e]
    refine h.congr fun n => integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [Pi.mul_apply]
    push_cast
    ring
  have T2 : ∀ a, Tendsto (fun n : ℕ => ∫ r, conj (dirD a Ψ r) *
      (((dirD a X.χ r * pairPotε q (1 / ((n : ℝ) + 1)) r : ℝ) : ℂ) * u r)) atTop
      (𝓝 (∫ r, conj (dirD a Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) * pairL2 q Y r))) := by
    intro a
    have h := tendsto_integral_pairPotε q ((hdΨ a).mul (hc1 a)) (hcs1 a).mul_left (f := u) hY
    have e : (∫ r, conj (dirD a Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) * pairL2 q Y r)) =
        ∫ r, ((fun r => conj (dirD a Ψ r)) * fun r => ((dirD a X.χ r : ℝ) : ℂ)) r *
          pairL2 q Y r :=
      integral_congr_ae (ae_of_all _ fun r => by simp only [Pi.mul_apply]; ring)
    rw [e]
    refine h.congr fun n => integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [Pi.mul_apply]
    push_cast
    ring
  have T3 : ∀ a, Tendsto (fun n : ℕ => ∫ r, conj (Ψ r) *
      (((dirD a X.χ r * pairPotε q (1 / ((n : ℝ) + 1)) r : ℝ) : ℂ) * g a r)) atTop
      (𝓝 (∫ r, conj (Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) * pairL2 q (fun p => Z p a) r))) := by
    intro a
    have h := tendsto_integral_pairPotε q (hcΨ.mul (hc1 a)) (hcs1 a).mul_left (f := g a)
      (F := fun p => Z p a) (fun p => hZ p a)
    have e : (∫ r, conj (Ψ r) * (((dirD a X.χ r : ℝ) : ℂ) * pairL2 q (fun p => Z p a) r)) =
        ∫ r, ((fun r => conj (Ψ r)) * fun r => ((dirD a X.χ r : ℝ) : ℂ)) r *
          pairL2 q (fun p => Z p a) r :=
      integral_congr_ae (ae_of_all _ fun r => by simp only [Pi.mul_apply]; ring)
    rw [e]
    refine h.congr fun n => integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [Pi.mul_apply]
    push_cast
    ring
  have T4 := tendsto_integral_commWε hL X q hcΨ hY
  have hLHS := tendsto_finsetSum (Finset.univ : Finset (Fin eta × Fin 3))
    fun a _ => ((T1 a).add (T2 a)).const_mul (((-(m a.1)⁻¹ : ℝ) : ℂ))
  have hRHS := (tendsto_finsetSum (Finset.univ : Finset (Fin eta × Fin 3))
    fun a _ => (T3 a).const_mul (((-(m a.1)⁻¹ : ℝ) : ℂ))).neg.sub T4
  refine tendsto_nhds_unique hLHS (hRHS.congr fun n => ?_)
  exact (regularised_identity hL X q (by positivity) hg hΨ).symm

end Identity

end FreeBoundary
