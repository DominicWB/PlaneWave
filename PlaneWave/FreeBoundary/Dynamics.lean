import PlaneWave.FreeBoundary.LowerBound

/-!
# `prop:free-dyn`: the free-space step of the free-boundary dynamics

`prop:free-dyn` compares the exact free-space evolution `ψ_∞(t)` with the torus evolution of the
cut-off, transplanted initial state. This file proves the free-space step of its proof for any
propagator `U` of the `g_L` Hamiltonian `H_L` (zero mode removed) of `PlaneWave.FreeBoundary.PositionPotential`–`PlaneWave.FreeBoundary.CompletedHamiltonian`:

* `HasFreeHamiltonian`, `HasWeakGrad`: the free-space Hamiltonian relation `H_∞ f = h` (Coulomb
  potential pointwise, kinetic energy weakly against `C²` tests of compact support) and the weak
  gradient, on `L²(ℝ^{3η})`;
* `HasGLHamiltonian`: the torus Hamiltonian relation of `H_L`, in the form of the release's
  `HasCoulombHamiltonian`;
* `BoxWeight.cutL2`: the normalised weighted transplant `f ↦ (x ↦ L^{3η/2} (w f)(L · rep(x)))`, a
  bounded operator `L²(ℝ^{3η}) → L²(T)`; for a cutoff `X`, `X.chiW.cutL2 hL f` is `T(χ f)`;
* `transplant_hasGLHamiltonian`: for `H_∞ f = h` with weak gradient `g` and a `C²` cutoff `χ`
  supported in the retained region, `H_L T(χ f) = T(χ h) - C₀ T(χ f) + T([K, χ] f)`, `C₀` the
  zero-mode shift and `[K, χ] f = -(1/2) Σ_a m_a⁻¹ (∂_a²χ f + 2 ∂_aχ ∂_a f)` the commutator (the
  manuscript's `-[χ_B, T_tot] f`);
* `duhamel_phase`: Duhamel's estimate for the propagator of a Hamiltonian relation;
* **`free_dyn_torus`** (`prop:free-dyn`, free-space step): under (H_leak),
  `‖1_{outside B^one} ψ_∞(s)‖ ≤ ε` and `‖1_S ∇ψ_∞(s)‖ ≤ ε` for `0 ≤ s ≤ t`,
  `‖φ(t) - e^{-iC₀t} U(t) φ(0)‖ ≤ C ε t` with `φ(s) = T(χ ψ_∞(s))` and `C = 3η (D₁ + D₂/2)`
  (`D₁`, `D₂` bounds of every `∂_aχ`, `∂_a²χ`; masses `m_a ≥ 1`, as in every `CoulombSystem`), and
  for every measurable multiplier `0 ≤ χ_o ≤ 1` whose torus version `G = χ_o ∘ cell` is continuous
  `|⟨ψ_∞(t), χ_o ψ_∞(t)⟩ - ⟨U(t)φ(0), χ_o U(t)φ(0)⟩| ≤ ε² + (‖ψ_∞(t)‖ + ‖ψ_∞(0)‖) C ε t`.

The remaining step of `prop:free-dyn`, the grid dynamics of the `g_L` kernel
(`thm:grid-dyn-sharp` for `g_L`), is not part of this file.
-/

set_option autoImplicit false

open MeasureTheory Filter Set PlaneWaveCertificate Asymptotics
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15
  molecularTorusFiniteMeasureFB15

/-! ## Duhamel's estimate -/

section Duhamel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The derivative of `s ↦ U(-s) φ(s)` for a strongly continuous family of isometries. -/
lemma hasDerivAt_neg_apply (U : ℝ → E ≃ₗᵢ[ℂ] E) (hUcont : ∀ x, Continuous fun t => U t x)
    {φ : ℝ → E} {φ' : E} {s₀ : ℝ} (hφ : HasDerivAt φ φ' s₀) {d : E}
    (hd : HasDerivAt (fun τ => U τ (φ s₀)) d (-s₀)) :
    HasDerivAt (fun s => U (-s) (φ s)) (U (-s₀) φ' - d) s₀ := by
  have h3 : HasDerivAt (fun s => U (-s) (φ s₀)) (-d) s₀ := by
    have h := hd.scomp s₀ (hasDerivAt_neg s₀)
    simpa [Function.comp_def] using h
  rw [hasDerivAt_iff_isLittleO] at hφ h3 ⊢
  have hcont : Tendsto (fun x : ℝ => U (-x) φ' - U (-s₀) φ') (𝓝 s₀) (𝓝 0) := by
    have hc : Continuous fun x : ℝ => U (-x) φ' := (hUcont φ').comp continuous_neg
    simpa using (hc.tendsto s₀).sub_const (U (-s₀) φ')
  have h2 : (fun x : ℝ => (x - s₀) • (U (-x) φ' - U (-s₀) φ')) =o[𝓝 s₀] fun x => x - s₀ := by
    have h := (isBigO_refl (fun x : ℝ => x - s₀) (𝓝 s₀)).smul_isLittleO
      ((isLittleO_one_iff (F := ℝ)).mpr hcont)
    simpa using h
  have h1 : (fun x : ℝ => U (-x) (φ x - φ s₀ - (x - s₀) • φ')) =o[𝓝 s₀] fun x => x - s₀ := by
    refine IsLittleO.of_norm_left ?_
    simpa only [LinearIsometryEquiv.norm_map] using hφ.norm_left
  refine ((h1.add h2).add h3).congr_left fun x => ?_
  have hsm : U (-x) ((x - s₀) • φ') = (x - s₀) • U (-x) φ' :=
    (U (-x)).toLinearEquiv.toLinearMap.map_smul_of_tower (x - s₀) φ'
  simp only [map_sub, hsm]
  module

/-- **Duhamel's estimate.** Let `U` be a strongly continuous group of isometries with generator
relation `Rel` (`U'(t) f = -i U(t) h` whenever `Rel f h`, i.e. `h = H f`), and let `φ` solve
`i φ' = ζ + c φ + r` with `Rel (φ s) (ζ s)` and a real constant `c`. Then
`‖φ(t) - e^{-ict} U(t) φ(0)‖ ≤ t · sup_{[0,t]} ‖r‖`. -/
theorem duhamel_phase (Rel : E → E → Prop) (U : ℝ → E ≃ₗᵢ[ℂ] E) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUadd : ∀ s t ψ, U (s + t) ψ = U s (U t ψ)) (hUcont : ∀ ψ, Continuous fun t => U t ψ)
    (hUderiv : ∀ t f h, Rel f h → HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    {φ ζ r : ℝ → E} (c : ℝ) (hrel : ∀ s, Rel (φ s) (ζ s))
    (hφ : ∀ s, HasDerivAt φ (-(Complex.I • (ζ s + (c : ℂ) • φ s + r s))) s)
    {t M : ℝ} (ht : 0 ≤ t) (hr : ∀ s ∈ Icc 0 t, ‖r s‖ ≤ M) :
    ‖φ t - Complex.exp (-(Complex.I * c * t)) • U t (φ 0)‖ ≤ M * t := by
  obtain ⟨w, hw⟩ : ∃ w : ℝ → E,
      w = fun s : ℝ => Complex.exp (Complex.I * c * (s : ℂ)) • U (-s) (φ s) := ⟨_, rfl⟩
  have hderiv : ∀ s : ℝ, HasDerivAt w
      (Complex.exp (Complex.I * c * (s : ℂ)) • (-(Complex.I • U (-s) (r s)))) s := by
    intro s
    rw [hw]
    have h1 := hasDerivAt_neg_apply U hUcont (hφ s) (hUderiv (-s) (φ s) (ζ s) (hrel s))
    have he : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * c * s))
        (Complex.exp (Complex.I * c * s) * (Complex.I * c)) s := by
      have h := ((hasDerivAt_id s).ofReal_comp.const_mul (Complex.I * c)).cexp
      simpa using h
    have h2 := he.smul h1
    convert h2 using 1
    · rfl
    · simp only [map_neg, map_add, map_smul]
      module
  have hbound : ‖w t - w 0‖ ≤ M * (t - 0) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f := w)
      (fun s _ => (hderiv s).hasDerivWithinAt) (fun s hs => ?_) t ⟨ht, le_rfl⟩
    rw [norm_smul, norm_neg, norm_smul, Complex.norm_I, one_mul, LinearIsometryEquiv.norm_map,
      Complex.norm_exp]
    simpa using hr s (Ico_subset_Icc_self hs)
  have hw0 : w 0 = φ 0 := by
    rw [hw]
    simp [hU0]
  have hwt : w t = Complex.exp (Complex.I * c * t) • U (-t) (φ t) := by rw [hw]
  have hUt : U t (U (-t) (φ t)) = φ t := by rw [← hUadd, add_neg_cancel, hU0]
  have key : φ t - Complex.exp (-(Complex.I * c * t)) • U t (φ 0) =
      Complex.exp (-(Complex.I * c * t)) • U t (w t - w 0) := by
    rw [map_sub, hw0, smul_sub, hwt]
    simp only [map_smul, hUt, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
      one_smul]
  rw [key, norm_smul, LinearIsometryEquiv.norm_map, Complex.norm_exp]
  simpa using hbound

end Duhamel

variable {eta : ℕ}

/-! ## Transplanting `L²` functions -/

/-- Free-space `L²` on the configuration space `ℝ^{3η}`. -/
abbrev FreeL2 (eta : ℕ) := Lp ℂ 2 (volume : Measure (Rcfg eta))

lemma cellCoord_box (L : ℝ) (y : Rcfg eta)
    (hy : ∀ i, y i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i) ((fun _ => (-1 / 2 : ℝ)) i + 1)) :
    cellCoord L (fun i => (y i : UnitAddCircle)) = L • y := by
  funext a
  unfold cellCoord
  rw [equivIoc_coe_rep1, rep1_of_mem (hy a)]
  rfl

/-- The cell coordinates are quasi-measure-preserving. -/
lemma qmp_cellCoord {L : ℝ} (hL : L ≠ 0) :
    Measure.QuasiMeasurePreserving (cellCoord (eta := eta) L) volume volume := by
  have h1 := (UnitAddTorus.measurePreserving_equivPiIoc
    (fun _ : Fin eta × Fin 3 => (-1 / 2 : ℝ))).quasiMeasurePreserving
  have hmp := measurePreserving_subtype_coe (μa := (volume : Measure (Rcfg eta)))
    (box_measurable (eta := eta))
  have h2 : Measure.QuasiMeasurePreserving
      (Subtype.val : {x : Rcfg eta | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
        ((fun _ => (-1 / 2 : ℝ)) i + 1)} → Rcfg eta)
      (Measure.comap Subtype.val volume) volume :=
    ⟨hmp.measurable, by
      rw [hmp.map_eq]
      exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self⟩
  have h3 : Measure.QuasiMeasurePreserving (fun y : Rcfg eta => L • y) volume volume :=
    Measure.quasiMeasurePreserving_smul volume hL
  exact (h3.comp h2).comp h1

lemma zero_of_not_box {F : Type*} [NormedAddCommGroup F] {L : ℝ} (hL : 0 < L)
    {g : Rcfg eta → F} (hs : ∀ r, g r ≠ 0 → ∀ a, |r a| ≤ L / 4) (y : Rcfg eta)
    (hy : y ∉ {x : Rcfg eta | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
      ((fun _ => (-1 / 2 : ℝ)) i + 1)}) :
    g (L • y) = 0 := by
  by_contra hne
  apply hy
  intro a
  have hb := abs_le_quarter hL (hs _ hne a)
  obtain ⟨h1, h2⟩ := abs_le.mp hb
  constructor <;> linarith

/-- **The integral over the torus of a function of the cell coordinates**:
`∫_T g(cell x) dx = L^{-3η} ∫ g` for `g` supported in the quarter box. -/
theorem integral_comp_cellCoord {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {L : ℝ}
    (hL : 0 < L) (g : Rcfg eta → F) (hs : ∀ r, g r ≠ 0 → ∀ a, |r a| ≤ L / 4) :
    ∫ x : MolecularPositionTorus eta, g (cellCoord L x) =
      ((L ^ Fintype.card (Fin eta × Fin 3))⁻¹ : ℝ) • ∫ r, g r := by
  rw [UnitAddTorus.integral_preimage _ (fun _ => -1 / 2)]
  rw [setIntegral_congr_fun box_measurable (fun y hy => by rw [cellCoord_box L y hy])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => zero_of_not_box hL hs y hy),
    Measure.integral_comp_smul volume g L, Module.finrank_fintype_fun_eq_card,
    abs_of_pos (by positivity)]

/-- Integrability transfers to the torus. -/
theorem integrable_comp_cellCoord {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : ℝ} (hL : 0 < L) {g : Rcfg eta → F} (hint : Integrable g) :
    Integrable (fun x : MolecularPositionTorus eta => g (cellCoord L x)) := by
  have hmp := (UnitAddTorus.measurePreserving_equivPiIoc
    (fun _ : Fin eta × Fin 3 => (-1 / 2 : ℝ))).symm
  have h3 : Integrable (fun y : Rcfg eta => g (L • y)) :=
    (integrable_comp_smul_iff volume g hL.ne').mpr hint
  have h2 := h3.integrableOn (s := {x : Rcfg eta | ∀ i, x i ∈ Ioc ((fun _ => (-1 / 2 : ℝ)) i)
    ((fun _ => (-1 / 2 : ℝ)) i + 1)})
  rw [integrableOn_iff_comap_subtypeVal box_measurable] at h2
  refine (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mp
    (h2.congr (ae_of_all _ fun y => ?_))
  simp only [Function.comp_apply, UnitAddTorus.coe_symm_measurableEquivPiIoc_apply]
  rw [cellCoord_box L y.1 y.2]

lemma norm_sq_L2_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} (F : Lp ℂ 2 μ) :
    ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂μ := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def]
  have hc : ∀ x, inner ℂ (F x) (F x) = ((‖F x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  simp_rw [hc]
  rw [integral_complex_ofReal, RCLike.re_to_complex, Complex.ofReal_re]

lemma lift_cellCoord {L : ℝ} (hL : L ≠ 0) (Φ : MolecularPositionTorus eta → ℂ)
    (x : MolecularPositionTorus eta) : torusRealLift Φ (L⁻¹ • cellCoord L x) = Φ x := by
  unfold torusRealLift
  rw [quot_cellCoord hL]

/-- The scale `L^{3η/2}` of the normalised transplant. -/
def tScale (eta : ℕ) (L : ℝ) : ℝ := Real.sqrt (L ^ Fintype.card (Fin eta × Fin 3))

lemma tScale_sq {L : ℝ} (hL : 0 < L) :
    tScale eta L ^ 2 = L ^ Fintype.card (Fin eta × Fin 3) :=
  Real.sq_sqrt (by positivity)

lemma tScale_pos {L : ℝ} (hL : 0 < L) : 0 < tScale eta L :=
  Real.sqrt_pos.mpr (by positivity)

/-! ## Weighted transplants -/

/-- A bounded measurable weight on `ℝ^{3η}` supported in the quarter box `[-L/4, L/4]^{3η}`. -/
structure BoxWeight (eta : ℕ) (L : ℝ) where
  /-- The weight. -/
  w : Rcfg eta → ℂ
  meas : Measurable w
  /-- A bound for the weight. -/
  B : ℝ
  bound : ∀ r, ‖w r‖ ≤ B
  supp : ∀ r, w r ≠ 0 → ∀ a, |r a| ≤ L / 4

namespace BoxWeight

variable {L : ℝ}

lemma B_nonneg (W : BoxWeight eta L) : 0 ≤ W.B := (norm_nonneg _).trans (W.bound 0)

lemma supp_of {F : Type*} [NormedAddCommGroup F] (W : BoxWeight eta L) {g : Rcfg eta → F}
    (hg : ∀ r, W.w r = 0 → g r = 0) : ∀ r, g r ≠ 0 → ∀ a, |r a| ≤ L / 4 :=
  fun r hr => W.supp r fun h => hr (hg r h)

/-- The normalised weighted transplant `x ↦ L^{3η/2} w(r) f(r)`, `r = cell(x)`. -/
def cutFun (W : BoxWeight eta L) (f : Rcfg eta → ℂ) (x : MolecularPositionTorus eta) : ℂ :=
  (tScale eta L : ℂ) * (W.w (cellCoord L x) * f (cellCoord L x))

lemma norm_sq_cutFun (hL : 0 < L) (W : BoxWeight eta L) (f : Rcfg eta → ℂ)
    (x : MolecularPositionTorus eta) :
    ‖W.cutFun f x‖ ^ 2 = L ^ Fintype.card (Fin eta × Fin 3) *
      (‖W.w (cellCoord L x)‖ ^ 2 * ‖f (cellCoord L x)‖ ^ 2) := by
  unfold cutFun
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (tScale_pos hL), mul_pow, mul_pow, tScale_sq hL]

lemma integrable_weight_sq (W : BoxWeight eta L) (f : FreeL2 eta) :
    Integrable (fun r => ‖W.w r‖ ^ 2 * ‖f r‖ ^ 2) := by
  have hf2 : Integrable (fun r => ‖f r‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  refine hf2.bdd_mul (c := W.B ^ 2) (W.meas.norm.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun r => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (W.bound r) 2

lemma memLp_cutFun (hL : 0 < L) (W : BoxWeight eta L) (f : FreeL2 eta) :
    MemLp (W.cutFun f) 2 volume := by
  have hmeas : AEStronglyMeasurable (W.cutFun f) volume :=
    aestronglyMeasurable_const.mul ((W.meas.comp (measurable_cellCoord L)).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving (qmp_cellCoord hL.ne')))
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  have hG := (W.integrable_weight_sq f).const_mul (L ^ Fintype.card (Fin eta × Fin 3))
  refine (integrable_comp_cellCoord hL hG).congr
    (ae_of_all _ fun x => ?_)
  simp only
  rw [norm_sq_cutFun hL]

lemma norm_sq_toLp_cutFun (hL : 0 < L) (W : BoxWeight eta L) (f : FreeL2 eta) :
    ‖(W.memLp_cutFun hL f).toLp _‖ ^ 2 = ∫ r, ‖W.w r‖ ^ 2 * ‖f r‖ ^ 2 := by
  have hae : (fun x => ‖((W.memLp_cutFun hL f).toLp _ : MolecularPositionTorus eta → ℂ) x‖ ^ 2)
      =ᵐ[volume] fun x => ‖W.cutFun f x‖ ^ 2 := by
    filter_upwards [MemLp.coeFn_toLp (W.memLp_cutFun hL f)] with x hx
    rw [hx]
  rw [norm_sq_L2_eq, integral_congr_ae hae]
  simp_rw [norm_sq_cutFun hL]
  rw [integral_comp_cellCoord hL (fun r => L ^ Fintype.card (Fin eta × Fin 3) *
      (‖W.w r‖ ^ 2 * ‖f r‖ ^ 2)) (W.supp_of fun r h => by simp [h]),
    smul_eq_mul, integral_const_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

lemma integral_weight_sq_le (W : BoxWeight eta L) (f : FreeL2 eta) :
    ∫ r, ‖W.w r‖ ^ 2 * ‖f r‖ ^ 2 ≤ W.B ^ 2 * ‖f‖ ^ 2 := by
  have hf2 : Integrable (fun r => ‖f r‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  rw [norm_sq_L2_eq f, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun r => by positivity) (hf2.const_mul _)
    (ae_of_all _ fun r => ?_)
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (W.bound r) 2)
    (by positivity)

/-- **The weighted transplant** `f ↦ L^{3η/2} T(w f)`, a bounded operator
`L²(ℝ^{3η}) → L²(T)` of norm at most `sup |w|`. -/
def cutL2 (hL : 0 < L) (W : BoxWeight eta L) : FreeL2 eta →L[ℂ] MolecularPositionL2 eta :=
  LinearMap.mkContinuous
    { toFun := fun f => (W.memLp_cutFun hL f).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (W.memLp_cutFun hL (f + g)),
          MemLp.coeFn_toLp (W.memLp_cutFun hL f), MemLp.coeFn_toLp (W.memLp_cutFun hL g),
          Lp.coeFn_add ((W.memLp_cutFun hL f).toLp _) ((W.memLp_cutFun hL g).toLp _),
          (qmp_cellCoord hL.ne').ae (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
        rw [h4, Pi.add_apply, h1, h2, h3]
        simp only [cutFun, h5, Pi.add_apply]
        ring
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (W.memLp_cutFun hL (c • f)),
          MemLp.coeFn_toLp (W.memLp_cutFun hL f),
          Lp.coeFn_smul c ((W.memLp_cutFun hL f).toLp _),
          (qmp_cellCoord hL.ne').ae (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h3, Pi.smul_apply, h1, h2]
        simp only [cutFun, h4, Pi.smul_apply, smul_eq_mul]
        ring }
    W.B (fun f => by
      change ‖MemLp.toLp (W.cutFun f) (W.memLp_cutFun hL f)‖ ≤ W.B * ‖f‖
      have h1 := W.norm_sq_toLp_cutFun hL f
      have h2 := W.integral_weight_sq_le f
      have h3 : ‖MemLp.toLp (W.cutFun f) (W.memLp_cutFun hL f)‖ ^ 2 ≤ (W.B * ‖f‖) ^ 2 := by
        rw [mul_pow]
        linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _)
        (mul_nonneg W.B_nonneg (norm_nonneg _)) two_ne_zero).mp h3)

lemma cutL2_ae (hL : 0 < L) (W : BoxWeight eta L) (f : FreeL2 eta) :
    (W.cutL2 hL f : MolecularPositionTorus eta → ℂ) =ᵐ[volume] W.cutFun f :=
  MemLp.coeFn_toLp (W.memLp_cutFun hL f)

lemma norm_sq_cutL2 (hL : 0 < L) (W : BoxWeight eta L) (f : FreeL2 eta) :
    ‖W.cutL2 hL f‖ ^ 2 = ∫ r, ‖W.w r‖ ^ 2 * ‖f r‖ ^ 2 :=
  W.norm_sq_toLp_cutFun hL f

lemma norm_cutL2_le (hL : 0 < L) (W : BoxWeight eta L) (f : FreeL2 eta) :
    ‖W.cutL2 hL f‖ ≤ W.B * ‖f‖ := by
  have h3 : ‖W.cutL2 hL f‖ ^ 2 ≤ (W.B * ‖f‖) ^ 2 := by
    rw [mul_pow, W.norm_sq_cutL2 hL f]
    exact W.integral_weight_sq_le f
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg W.B_nonneg (norm_nonneg _)) two_ne_zero).mp h3

/-- A weight vanishing off `S` sees only the `L²` mass of `f` on `S`. -/
lemma norm_cutL2_le_of_supp (hL : 0 < L) (W : BoxWeight eta L) {S : Set (Rcfg eta)}
    (hS : MeasurableSet S) (hW : ∀ r, r ∉ S → W.w r = 0) (f : FreeL2 eta) {e : ℝ}
    (he : 0 ≤ e) (hfe : ∫ r in S, ‖f r‖ ^ 2 ≤ e ^ 2) : ‖W.cutL2 hL f‖ ≤ W.B * e := by
  have hf2 : Integrable (fun r => ‖f r‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have h1 : ∫ r, ‖W.w r‖ ^ 2 * ‖f r‖ ^ 2 ≤ W.B ^ 2 * e ^ 2 := by
    calc ∫ r, ‖W.w r‖ ^ 2 * ‖f r‖ ^ 2
        ≤ ∫ r, S.indicator (fun r => W.B ^ 2 * ‖f r‖ ^ 2) r := by
          refine integral_mono_of_nonneg (ae_of_all _ fun r => by positivity)
            ((hf2.const_mul _).indicator hS) (ae_of_all _ fun r => ?_)
          by_cases hr : r ∈ S
          · rw [indicator_of_mem hr]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (W.bound r) 2)
              (by positivity)
          · rw [indicator_of_notMem hr]
            simp [hW r hr]
      _ = W.B ^ 2 * ∫ r in S, ‖f r‖ ^ 2 := by
          rw [integral_indicator hS, integral_const_mul]
      _ ≤ W.B ^ 2 * e ^ 2 := mul_le_mul_of_nonneg_left hfe (by positivity)
  have h3 : ‖W.cutL2 hL f‖ ^ 2 ≤ (W.B * e) ^ 2 := by
    rw [mul_pow, W.norm_sq_cutL2 hL f]
    exact h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg W.B_nonneg he) two_ne_zero).mp h3

/-- **Inner products with torus tests**: `⟨Φ, L^{3η/2} T(w f)⟩ = L^{-3η/2} ∫ conj(Φ̃) w f`,
`Φ̃(r) = Φ(r/L)` the periodic lift. -/
lemma inner_cutL2 (hL : 0 < L) (W : BoxWeight eta L) (Φ : C(MolecularPositionTorus eta, ℂ))
    (f : FreeL2 eta) :
    inner ℂ ((ContinuousMap.toLp 2 volume ℂ) Φ) (W.cutL2 hL f) =
      ((tScale eta L : ℂ))⁻¹ * ∫ r, conj (torusRealLift Φ (L⁻¹ • r)) * (W.w r * f r) := by
  obtain ⟨G, hG⟩ : ∃ G : Rcfg eta → ℂ,
      G = fun r => conj (torusRealLift Φ (L⁻¹ • r)) * (W.w r * f r) := ⟨_, rfl⟩
  rw [MeasureTheory.L2.inner_def]
  have hae : (fun x => inner ℂ (((ContinuousMap.toLp 2 volume ℂ) Φ :
      MolecularPositionTorus eta → ℂ) x) ((W.cutL2 hL f : MolecularPositionTorus eta → ℂ) x))
      =ᵐ[volume] fun x => (tScale eta L : ℂ) * G (cellCoord L x) := by
    filter_upwards [Φ.coeFn_toLp (p := 2) (𝕜 := ℂ)
      (volume : Measure (MolecularPositionTorus eta)), W.cutL2_ae hL f] with x h1 h2
    rw [RCLike.inner_apply, h1, h2, hG]
    simp only [cutFun, lift_cellCoord hL.ne']
    ring
  have hGs : ∀ r, G r ≠ 0 → ∀ a, |r a| ≤ L / 4 :=
    W.supp_of fun r h => by rw [hG]; simp [h]
  rw [integral_congr_ae hae, integral_const_mul, integral_comp_cellCoord hL G hGs, hG,
    Complex.real_smul]
  have hs := tScale_sq (eta := eta) hL
  have hpos := (tScale_pos (eta := eta) hL).ne'
  rw [← hs]
  push_cast
  field_simp

end BoxWeight

/-! ## The free-space and torus Hamiltonian relations -/

section Relations

variable {ν : Type} [Fintype ν]

/-- **The weak gradient**: `g a` is the distributional derivative `∂_a f` of `f ∈ L²(ℝ^{3η})`,
tested against `C¹` functions of compact support. -/
def HasWeakGrad (f : FreeL2 eta) (g : Fin eta × Fin 3 → FreeL2 eta) : Prop :=
  ∀ φ : Rcfg eta → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ a,
    ∫ r, conj (φ r) * g a r = -∫ r, conj (dirD a φ r) * f r

/-- **The weak free-space kinetic equation** `K f = k`, `K = -(1/2) Σ_a m_a⁻¹ ∂_a²`, tested
against `C²` functions of compact support. -/
def HasFreeWeakKinetic (m : Fin eta → ℝ) (f k : FreeL2 eta) : Prop :=
  ∀ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ → HasCompactSupport φ →
    ∫ r, conj (φ r) * k r = ∫ r, conj (freeKinetic m φ r) * f r

/-- **The free-space Hamiltonian relation** `H_∞ f = h`: the Coulomb term `V_∞ f` is in `L²` and
`h - V_∞ f` is the weak kinetic image of `f`. -/
def HasFreeHamiltonian (sys : CoulombSystem eta ν) (P : ν → E3) (f h : FreeL2 eta) : Prop :=
  ∃ v : FreeL2 eta, HasL2PointwisePotential volume (fun r => (freePot sys P r : ℂ)) f v ∧
    HasFreeWeakKinetic sys.mass f (h - v)

/-- **The torus Hamiltonian relation** `H_L f = h` of the `g_L` Hamiltonian (zero mode removed),
in the form of the release's `HasCoulombHamiltonian`. -/
def HasGLHamiltonian (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (f h : MolecularPositionL2 eta) : Prop :=
  ∃ v : MolecularPositionL2 eta, HasL2PointwisePotential volume (gLFourierPotential sys L θ) f v ∧
    HasCoulombContDiffWeakKinetic sys L f (h - v)

end Relations

/-! ## The kinetic energy of periodic lifts and of products -/

section Kinetic

variable {ν : Type} [Fintype ν]

omit [Fintype ν] in
/-- The free-space kinetic expression of the periodic lift `Φ̃(r) = Φ(r/L)` of a `C²` torus
function is the lift of its torus kinetic energy. -/
lemma freeKinetic_lift (sys : CoulombSystem eta ν) {L : ℝ} (hL : L ≠ 0)
    (Φ : C(MolecularPositionTorus eta, ℂ)) (hΦ : ContDiff ℝ 2 (torusRealLift Φ)) (r : Rcfg eta) :
    freeKinetic sys.mass (fun r => torusRealLift Φ (L⁻¹ • r)) r =
      torusRealLift (coulombPositionContDiffKinetic sys L Φ hΦ) (L⁻¹ • r) := by
  have hR : torusRealLift (coulombPositionContDiffKinetic sys L Φ hΦ) (L⁻¹ • r) =
      coulombPositionClassicalKinetic sys L Φ (torusRealQuotient _ (L⁻¹ • r)) := by
    unfold torusRealLift
    rw [coulombPositionContDiffKinetic_eq_classicalKinetic]
  rw [hR]
  have hline : ∀ a : Fin eta × Fin 3,
      deriv (deriv (fun s : ℝ => torusRealLift Φ (L⁻¹ • (r + s • Pi.single a 1)))) 0 =
      ((L⁻¹ ^ 2 : ℝ) : ℂ) * deriv (deriv (fun t : ℝ =>
        (Φ : MolecularPositionTorus eta → ℂ)
          (torusCoordinateLine (torusRealQuotient _ (L⁻¹ • r)) a t))) 0 := by
    intro a
    have heq : (fun s : ℝ => torusRealLift Φ (L⁻¹ • (r + s • Pi.single a 1))) =
        fun s => (fun t : ℝ => (Φ : MolecularPositionTorus eta → ℂ)
          (torusCoordinateLine (torusRealQuotient _ (L⁻¹ • r)) a t)) (L⁻¹ * s) := by
      funext s
      show (Φ : MolecularPositionTorus eta → ℂ)
          (torusRealQuotient _ (L⁻¹ • (r + s • Pi.single a 1))) =
        (Φ : MolecularPositionTorus eta → ℂ)
          (torusCoordinateLine (torusRealQuotient _ (L⁻¹ • r)) a (L⁻¹ * s))
      rw [← torusRealQuotient_coordinateLine, smul_add, smul_smul]
      congr
      exact Subsingleton.elim _ _
    rw [heq]
    exact deriv2_comp_mul_left (fun t : ℝ => (Φ : MolecularPositionTorus eta → ℂ)
      (torusCoordinateLine (torusRealQuotient _ (L⁻¹ • r)) a t)) L⁻¹
  simp only [freeKinetic, coulombPositionClassicalKinetic]
  simp_rw [hline]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  push_cast
  field_simp

end Kinetic

lemma dirD_fun_add {F G : Rcfg eta → ℂ} {x : Rcfg eta} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) (a : Fin eta × Fin 3) :
    dirD a (fun y => F y + G y) x = dirD a F x + dirD a G x := by
  unfold dirD
  have h : fderiv ℝ (fun y => F y + G y) x = fderiv ℝ F x + fderiv ℝ G x :=
    (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv
  rw [h]
  rfl

lemma differentiable_ofReal_mul {χ : Rcfg eta → ℝ} {φ : Rcfg eta → ℂ}
    (hχ : Differentiable ℝ χ) (hφ : Differentiable ℝ φ) :
    Differentiable ℝ (fun y => (χ y : ℂ) * φ y) :=
  (Complex.ofRealCLM.differentiable.comp hχ).mul hφ

/-- **The kinetic energy of a product with a real cutoff**:
`K(χ φ) = χ K φ + (-1/2) Σ_a m_a⁻¹ (2 ∂_a(∂_aχ φ) - ∂_a²χ φ)`. -/
lemma freeKinetic_ofReal_mul (m : Fin eta → ℝ) {χ : Rcfg eta → ℝ} {φ : Rcfg eta → ℂ}
    (hχ : ContDiff ℝ 2 χ) (hφ : ContDiff ℝ 2 φ) (r : Rcfg eta) :
    freeKinetic m (fun y => (χ y : ℂ) * φ y) r = (χ r : ℂ) * freeKinetic m φ r +
      (-(1 / 2 : ℂ)) * ∑ a : Fin eta × Fin 3, ((m a.1 : ℂ))⁻¹ *
        (2 * dirD a (fun y => ((dirD a χ y : ℝ) : ℂ) * φ y) r - ((dirD a (dirD a χ) r : ℝ) : ℂ) * φ r) := by
  rw [freeKinetic_eq m (contDiff_ofReal_mul hχ hφ), freeKinetic_eq m hφ]
  have hχd : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hχ1 : ∀ a, Differentiable ℝ (dirD a χ) :=
    fun a => (contDiff_dirD hχ a).differentiable (by norm_num)
  have hφ1 : ∀ a, Differentiable ℝ (dirD a φ) :=
    fun a => (contDiff_dirD hφ a).differentiable (by norm_num)
  have key : ∀ a, dirD a (dirD a (fun y => (χ y : ℂ) * φ y)) r =
      (χ r : ℂ) * dirD a (dirD a φ) r +
        (2 * dirD a (fun y => ((dirD a χ y : ℝ) : ℂ) * φ y) r - ((dirD a (dirD a χ) r : ℝ) : ℂ) * φ r) := by
    intro a
    have h1 : dirD a (fun y => (χ y : ℂ) * φ y) =
        fun y => ((dirD a χ y : ℝ) : ℂ) * φ y + (χ y : ℂ) * dirD a φ y := by
      funext y
      exact dirD_ofReal_mul (hχd y) (hφd y) a
    have hA : DifferentiableAt ℝ (fun y => ((dirD a χ y : ℝ) : ℂ) * φ y) r :=
      differentiable_ofReal_mul (hχ1 a) hφd r
    have hB : DifferentiableAt ℝ (fun y => (χ y : ℂ) * dirD a φ y) r :=
      differentiable_ofReal_mul hχd (hφ1 a) r
    rw [h1, dirD_fun_add hA hB, dirD_ofReal_mul (hχd r) (hφ1 a r) a,
      dirD_ofReal_mul (hχ1 a r) (hφd r) a]
    ring
  simp_rw [key]
  have hsum : ∑ a : Fin eta × Fin 3, ((m a.1 : ℂ))⁻¹ * ((χ r : ℂ) * dirD a (dirD a φ) r +
      (2 * dirD a (fun y => ((dirD a χ y : ℝ) : ℂ) * φ y) r - ((dirD a (dirD a χ) r : ℝ) : ℂ) * φ r)) =
      (χ r : ℂ) * ∑ a : Fin eta × Fin 3, ((m a.1 : ℂ))⁻¹ * dirD a (dirD a φ) r +
      ∑ a : Fin eta × Fin 3, ((m a.1 : ℂ))⁻¹ *
        (2 * dirD a (fun y => ((dirD a χ y : ℝ) : ℂ) * φ y) r - ((dirD a (dirD a χ) r : ℝ) : ℂ) * φ r) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hsum]
  ring

/-! ## The weak commutator identity -/

lemma integrable_cont_mul_L2 {c : Rcfg eta → ℂ} (hc : Continuous c) (hcs : HasCompactSupport c)
    (f : FreeL2 eta) : Integrable (fun r => c r * f r) :=
  (hc.memLp_of_hasCompactSupport (p := 2) (μ := volume) hcs).integrable_mul (Lp.memLp f)

lemma hasCompactSupport_ofReal {χ : Rcfg eta → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (fun r => (χ r : ℂ)) :=
  hχc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)

/-- **The weak commutator identity.** For a `C²` cutoff `χ` of compact support, a `C²` function
`Φ̃`, and `f ∈ L²` with weak kinetic image `k` and weak gradient `g`,
`∫ conj(Φ̃) χ k + Σ_a (-1/2) m_a⁻¹ (∫ conj(Φ̃) ∂_a²χ f + 2 ∫ conj(Φ̃) ∂_aχ g_a)
  = ∫ conj(K Φ̃) χ f`. -/
lemma weak_comm_identity (m : Fin eta → ℝ) {χ : Rcfg eta → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) {Φ : Rcfg eta → ℂ} (hΦ : ContDiff ℝ 2 Φ)
    {f k : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta}
    (hK : HasFreeWeakKinetic m f k) (hg : HasWeakGrad f g) :
    (∫ r, conj (Φ r) * ((χ r : ℂ) * k r)) +
      ∑ a : Fin eta × Fin 3, (-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹ *
        ((∫ r, conj (Φ r) * (((dirD a (dirD a χ) r : ℝ) : ℂ) * f r)) +
          2 * ∫ r, conj (Φ r) * (((dirD a χ r : ℝ) : ℂ) * g a r)) =
      ∫ r, conj (freeKinetic m Φ r) * ((χ r : ℂ) * f r) := by
  -- the two kinds of test functions
  have hφ₁ : ContDiff ℝ 2 (fun y => (χ y : ℂ) * Φ y) := contDiff_ofReal_mul hχ hΦ
  have hφ₁c : HasCompactSupport (fun y => (χ y : ℂ) * Φ y) :=
    (hasCompactSupport_ofReal hχc).mul_right
  have hd1 : ∀ a, ContDiff ℝ 1 (dirD a χ) := fun a => contDiff_dirD hχ a
  have hd1c : ∀ a, HasCompactSupport (dirD a χ) := fun a => hasCompactSupport_dirD hχc a
  have hφ₂ : ∀ a, ContDiff ℝ 1 (fun y => ((dirD a χ y : ℝ) : ℂ) * Φ y) :=
    fun a => (Complex.ofRealCLM.contDiff.comp (hd1 a)).mul (hΦ.of_le (by norm_num))
  have hφ₂c : ∀ a, HasCompactSupport (fun y => ((dirD a χ y : ℝ) : ℂ) * Φ y) :=
    fun a => (hasCompactSupport_ofReal (hd1c a)).mul_right
  have hW1 := hK _ hφ₁ hφ₁c
  have hW2 := fun a => hg _ (hφ₂ a) (hφ₂c a) a
  -- continuity facts
  have hΦc : Continuous Φ := hΦ.continuous
  have hKc : Continuous (freeKinetic m Φ) := by
    have h : freeKinetic m Φ = fun r => (-(1 / 2 : ℂ)) * ∑ a : Fin eta × Fin 3,
        ((m a.1 : ℂ))⁻¹ * dirD a (dirD a Φ) r := funext fun r => freeKinetic_eq m hΦ r
    rw [h]
    exact continuous_const.mul (continuous_finsetSum _ fun a _ => continuous_const.mul
      (continuous_dirD (contDiff_dirD hΦ a) (by norm_num) a))
  have hχcont : Continuous fun r => (χ r : ℂ) := Complex.continuous_ofReal.comp hχ.continuous
  have hd2c : ∀ a, Continuous fun r => ((dirD a (dirD a χ) r : ℝ) : ℂ) :=
    fun a => Complex.continuous_ofReal.comp (continuous_dirD (hd1 a) (by norm_num) a)
  have hd2cs : ∀ a, HasCompactSupport fun r => ((dirD a (dirD a χ) r : ℝ) : ℂ) :=
    fun a => hasCompactSupport_ofReal (hasCompactSupport_dirD (hd1c a) a)
  -- integrability of the pieces
  have hI1 : Integrable (fun r => conj (freeKinetic m Φ r) * ((χ r : ℂ) * f r)) := by
    have h := integrable_cont_mul_L2 ((Complex.continuous_conj.comp hKc).mul hχcont)
      (hasCompactSupport_ofReal hχc).mul_left f
    refine h.congr (ae_of_all _ fun r => ?_)
    simp only [Function.comp_apply, Pi.mul_apply]
    ring
  have hI2 : ∀ a, Integrable
      (fun r => conj (dirD a (fun y => ((dirD a χ y : ℝ) : ℂ) * Φ y) r) * f r) :=
    fun a => integrable_cont_mul_L2
      (Complex.continuous_conj.comp (continuous_dirD (hφ₂ a) (by norm_num) a))
      ((hasCompactSupport_dirD (hφ₂c a) a).comp_left (g := conj) (by simp)) f
  have hI3 : ∀ a, Integrable
      (fun r => conj (Φ r) * (((dirD a (dirD a χ) r : ℝ) : ℂ) * f r)) := by
    intro a
    have h := integrable_cont_mul_L2 ((Complex.continuous_conj.comp hΦc).mul (hd2c a))
      (hd2cs a).mul_left f
    refine h.congr (ae_of_all _ fun r => ?_)
    simp only [Function.comp_apply, Pi.mul_apply]
    ring
  have hI4 : ∀ a : Fin eta × Fin 3, Integrable (fun r => (-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹ *
      (2 * (conj (dirD a (fun y => ((dirD a χ y : ℝ) : ℂ) * Φ y) r) * f r) -
        conj (Φ r) * (((dirD a (dirD a χ) r : ℝ) : ℂ) * f r))) :=
    fun a => (((hI2 a).const_mul 2).sub (hI3 a)).const_mul _
  have hI5 : Integrable (fun r => ∑ a : Fin eta × Fin 3, (-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹ *
      (2 * (conj (dirD a (fun y => ((dirD a χ y : ℝ) : ℂ) * Φ y) r) * f r) -
        conj (Φ r) * (((dirD a (dirD a χ) r : ℝ) : ℂ) * f r))) :=
    integrable_finsetSum _ fun a _ => hI4 a
  -- the left side of the kinetic test, pointwise
  have hL1 : ∫ r, conj ((χ r : ℂ) * Φ r) * k r = ∫ r, conj (Φ r) * ((χ r : ℂ) * k r) := by
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [map_mul, Complex.conj_ofReal]
    ring
  -- the right side of the kinetic test, pointwise
  have hpt : ∀ r, conj (freeKinetic m (fun y => (χ y : ℂ) * Φ y) r) * f r =
      conj (freeKinetic m Φ r) * ((χ r : ℂ) * f r) +
        ∑ a : Fin eta × Fin 3, (-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹ *
          (2 * (conj (dirD a (fun y => ((dirD a χ y : ℝ) : ℂ) * Φ y) r) * f r) -
            conj (Φ r) * (((dirD a (dirD a χ) r : ℝ) : ℂ) * f r)) := by
    intro r
    rw [freeKinetic_ofReal_mul m hχ hΦ r]
    simp only [map_add, map_mul, map_sub, map_sum, map_neg, Complex.conj_ofReal, map_inv₀,
      map_div₀, map_one, map_ofNat]
    rw [add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun a _ => by ring
  have hR1 : ∫ r, conj (freeKinetic m (fun y => (χ y : ℂ) * Φ y) r) * f r =
      (∫ r, conj (freeKinetic m Φ r) * ((χ r : ℂ) * f r)) +
        ∑ a : Fin eta × Fin 3, (-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹ *
          (2 * (∫ r, conj (dirD a (fun y => ((dirD a χ y : ℝ) : ℂ) * Φ y) r) * f r) -
            ∫ r, conj (Φ r) * (((dirD a (dirD a χ) r : ℝ) : ℂ) * f r)) := by
    simp_rw [hpt]
    rw [integral_add hI1 hI5, integral_finsetSum _ fun a _ => hI4 a]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_const_mul, integral_sub ((hI2 a).const_mul 2) (hI3 a), integral_const_mul]
  -- the gradient tests
  have hG : ∀ a, ∫ r, conj (dirD a (fun y => ((dirD a χ y : ℝ) : ℂ) * Φ y) r) * f r =
      -∫ r, conj (Φ r) * (((dirD a χ r : ℝ) : ℂ) * g a r) := by
    intro a
    rw [neg_eq_iff_eq_neg.mp (hW2 a).symm]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun r => ?_)
    simp only [map_mul, Complex.conj_ofReal]
    ring
  rw [← hL1, hW1, hR1]
  simp_rw [hG]
  rw [add_assoc, ← Finset.sum_add_distrib]
  have h0 : ∀ a : Fin eta × Fin 3,
      (-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹ *
          (2 * -(∫ r, conj (Φ r) * (((dirD a χ r : ℝ) : ℂ) * g a r)) -
            ∫ r, conj (Φ r) * (((dirD a (dirD a χ) r : ℝ) : ℂ) * f r)) +
        (-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹ *
          ((∫ r, conj (Φ r) * (((dirD a (dirD a χ) r : ℝ) : ℂ) * f r)) +
            2 * ∫ r, conj (Φ r) * (((dirD a χ r : ℝ) : ℂ) * g a r)) = 0 := fun a => by ring
  simp only [h0, Finset.sum_const_zero, add_zero]

/-! ## The cutoff and its transplants -/

lemma box_of_tsupport {L : ℝ} {χ : Rcfg eta → ℝ} (hbox : ∀ r, χ r ≠ 0 → ∀ a, |r a| ≤ L / 4) :
    ∀ r ∈ tsupport χ, ∀ a, |r a| ≤ L / 4 := by
  have hcl : IsClosed {r : Rcfg eta | ∀ a, |r a| ≤ L / 4} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun a =>
      isClosed_le (continuous_abs.comp (continuous_apply a)) continuous_const
  exact fun r hr => closure_minimal (fun y hy => hbox y hy) hcl hr

lemma mem_tsupport_of_dirD_ne {χ : Rcfg eta → ℝ} {r : Rcfg eta} {a : Fin eta × Fin 3}
    (h : dirD a χ r ≠ 0) : r ∈ tsupport χ := by
  apply support_fderiv_subset (𝕜 := ℝ)
  rw [Function.mem_support]
  intro h0
  apply h
  unfold dirD
  rw [h0]
  rfl

lemma tsupport_dirD_subset {χ : Rcfg eta → ℝ} (a : Fin eta × Fin 3) :
    tsupport (dirD a χ) ⊆ tsupport χ :=
  closure_minimal (fun _ hy => mem_tsupport_of_dirD_ne hy) (isClosed_tsupport χ)

/-- A `C²` cutoff `0 ≤ χ ≤ 1` supported in the quarter box, with bounds `D₁`, `D₂` for its first
and second coordinate derivatives `∂_aχ`, `∂_a²χ`. -/
structure Cutoff (eta : ℕ) (L : ℝ) where
  /-- The cutoff function. -/
  χ : Rcfg eta → ℝ
  smooth : ContDiff ℝ 2 χ
  nonneg : ∀ r, 0 ≤ χ r
  le_one : ∀ r, χ r ≤ 1
  box : ∀ r, χ r ≠ 0 → ∀ a, |r a| ≤ L / 4
  /-- The bound for the first derivatives. -/
  D1 : ℝ
  /-- The bound for the second derivatives. -/
  D2 : ℝ
  d1 : ∀ r a, |dirD a χ r| ≤ D1
  d2 : ∀ r a, |dirD a (dirD a χ) r| ≤ D2

namespace Cutoff

variable {L : ℝ}

lemma hasCompactSupport (X : Cutoff eta L) (hL : 0 < L) : HasCompactSupport X.χ := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Rcfg eta) (L / 4)) fun r hr => ?_
  by_contra hne
  apply hr
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
  intro a
  rw [Real.norm_eq_abs]
  exact X.box r hne a

/-- The cutoff as a weight. -/
def chiW (X : Cutoff eta L) : BoxWeight eta L where
  w := fun r => (X.χ r : ℂ)
  meas := (Complex.continuous_ofReal.comp X.smooth.continuous).measurable
  B := 1
  bound := fun r => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (X.nonneg r)]
    exact X.le_one r
  supp := fun r hr => X.box r fun h => hr (by rw [h, Complex.ofReal_zero])

/-- The first derivative `∂_aχ` as a weight. -/
def d1W (X : Cutoff eta L) (a : Fin eta × Fin 3) : BoxWeight eta L where
  w := fun r => ((dirD a X.χ r : ℝ) : ℂ)
  meas := (Complex.continuous_ofReal.comp (continuous_dirD X.smooth (by norm_num) a)).measurable
  B := X.D1
  bound := fun r => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact X.d1 r a
  supp := fun r hr => box_of_tsupport X.box r
    (mem_tsupport_of_dirD_ne fun h => hr (by rw [h, Complex.ofReal_zero]))

/-- The second derivative `∂_a²χ` as a weight. -/
def d2W (X : Cutoff eta L) (a : Fin eta × Fin 3) : BoxWeight eta L where
  w := fun r => ((dirD a (dirD a X.χ) r : ℝ) : ℂ)
  meas := (Complex.continuous_ofReal.comp
    (continuous_dirD (contDiff_dirD X.smooth a) (by norm_num) a)).measurable
  B := X.D2
  bound := fun r => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact X.d2 r a
  supp := fun r hr => box_of_tsupport X.box r (tsupport_dirD_subset a
    (mem_tsupport_of_dirD_ne fun h => hr (by rw [h, Complex.ofReal_zero])))

/-- **The transplanted commutator**
`T([K, χ] f) = Σ_a (-1/2) m_a⁻¹ (T(∂_a²χ f) + 2 T(∂_aχ g_a))` (`g` the weak gradient of `f`). -/
def commT (X : Cutoff eta L) (hL : 0 < L) (m : Fin eta → ℝ) (f : FreeL2 eta)
    (g : Fin eta × Fin 3 → FreeL2 eta) : MolecularPositionL2 eta :=
  ∑ a : Fin eta × Fin 3, ((-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹) •
    ((X.d2W a).cutL2 hL f + (2 : ℂ) • (X.d1W a).cutL2 hL (g a))

/-- The commutator constant `3η (D₁ + D₂/2)`. -/
def commConst (X : Cutoff eta L) : ℝ := Fintype.card (Fin eta × Fin 3) * (X.D1 + X.D2 / 2)

/-- **The commutator bound**: if `∂χ`, `∂²χ` vanish off `S ⊆ (B^one)ᶜ`, `‖1_{(B^one)ᶜ} f‖ ≤ ε`
and `‖1_S ∇f‖ ≤ ε`, then `‖T([K, χ] f)‖ ≤ 3η (D₁ + D₂/2) ε` (masses `≥ 1`). -/
lemma norm_commT_le (X : Cutoff eta L) (hL : 0 < L) {m : Fin eta → ℝ} (hm : ∀ i, 1 ≤ m i)
    {S Bone : Set (Rcfg eta)} (hSm : MeasurableSet S) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    (f : FreeL2 eta) (g : Fin eta × Fin 3 → FreeL2 eta) {ε : ℝ} (hε : 0 ≤ ε)
    (h0 : ∫ r in Boneᶜ, ‖f r‖ ^ 2 ≤ ε ^ 2) (h1 : ∫ r in S, ∑ a, ‖g a r‖ ^ 2 ≤ ε ^ 2) :
    ‖X.commT hL m f g‖ ≤ X.commConst * ε := by
  have hf2 : Integrable (fun r => ‖f r‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hg2 : ∀ a, Integrable (fun r => ‖g a r‖ ^ 2) := fun a =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (g a))).mp (Lp.memLp (g a))
  have hS0 : ∫ r in S, ‖f r‖ ^ 2 ≤ ε ^ 2 :=
    le_trans (setIntegral_mono_set hf2.integrableOn (ae_of_all _ fun r => by positivity)
      hSB.eventuallyLE) h0
  have hS1 : ∀ a, ∫ r in S, ‖g a r‖ ^ 2 ≤ ε ^ 2 := by
    intro a
    refine le_trans (integral_mono_of_nonneg (ae_of_all _ fun r => by positivity)
      (integrable_finsetSum _ fun b _ => hg2 b).integrableOn (ae_of_all _ fun r => ?_)) h1
    exact Finset.single_le_sum (f := fun b => ‖g b r‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ a)
  have hT2 : ∀ a, ‖(X.d2W a).cutL2 hL f‖ ≤ X.D2 * ε := fun a =>
    (X.d2W a).norm_cutL2_le_of_supp hL hSm (fun r hr => by simp [d2W, hd2S r hr a]) f hε hS0
  have hT1 : ∀ a, ‖(X.d1W a).cutL2 hL (g a)‖ ≤ X.D1 * ε := fun a =>
    (X.d1W a).norm_cutL2_le_of_supp hL hSm (fun r hr => by simp [d1W, hdS r hr a]) (g a) hε
      (hS1 a)
  have hc : ∀ a : Fin eta × Fin 3, ‖(-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹‖ ≤ 1 / 2 := by
    intro a
    have hm0 : 0 < m a.1 := lt_of_lt_of_le one_pos (hm a.1)
    rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h2]
    have h3 : (m a.1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hm a.1)
    nlinarith
  unfold commT commConst
  calc ‖∑ a : Fin eta × Fin 3, ((-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹) •
        ((X.d2W a).cutL2 hL f + (2 : ℂ) • (X.d1W a).cutL2 hL (g a))‖
      ≤ ∑ a : Fin eta × Fin 3, ‖((-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹) •
        ((X.d2W a).cutL2 hL f + (2 : ℂ) • (X.d1W a).cutL2 hL (g a))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin eta × Fin 3, 1 / 2 * (X.D2 * ε + 2 * (X.D1 * ε)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_smul]
        have hv : ‖(X.d2W a).cutL2 hL f + (2 : ℂ) • (X.d1W a).cutL2 hL (g a)‖ ≤
            X.D2 * ε + 2 * (X.D1 * ε) := by
          refine (norm_add_le _ _).trans (add_le_add (hT2 a) ?_)
          rw [norm_smul]
          have h2 : ‖(2 : ℂ)‖ = 2 := by simp
          rw [h2]
          exact mul_le_mul_of_nonneg_left (hT1 a) (by norm_num)
        exact mul_le_mul (hc a) hv (norm_nonneg _) (by norm_num)
    _ = (Fintype.card (Fin eta × Fin 3) : ℝ) * (X.D1 + X.D2 / 2) * ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Cutoff

/-! ## The zero-mode shift is real -/

lemma ghat_zero_eq {R : ℝ} {θ : ℝ → ℝ} (hθ : Profile R θ) (L : ℝ) :
    ghat L θ (fun _ => 0) =
      (((4 * Real.pi * ∫ r in (0 : ℝ)..R, r * θ r) / L ^ 3 : ℝ) : ℂ) := by
  have hk : kvec L (fun _ => 0) = 0 := by
    unfold kvec
    ext i
    simp
  unfold ghat
  rw [hk, gFT_zero hθ]
  push_cast
  ring

lemma zeroModeShift_re_eq {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {R : ℝ}
    {θ : ℝ → ℝ} (hθ : Profile R θ) (L : ℝ) :
    (((zeroModeShift sys L θ).re : ℝ) : ℂ) = zeroModeShift sys L θ := by
  have h : zeroModeShift sys L θ =
      ((∑ pair : FiniteElectronPair eta, sys.charge pair.1.1 * sys.charge pair.1.2 *
          ((4 * Real.pi * ∫ r in (0 : ℝ)..R, r * θ r) / L ^ 3) +
        ∑ i : Fin eta, sys.charge i * ∑ ell : ν, sys.nuclei.charge ell *
          ((4 * Real.pi * ∫ r in (0 : ℝ)..R, r * θ r) / L ^ 3) : ℝ) : ℂ) := by
    unfold zeroModeShift
    rw [ghat_zero_eq hθ L]
    push_cast
    rfl
  rw [h, Complex.ofReal_re]

/-! ## The transplanted Hamiltonian relation -/

section Transplant

variable {ν : Type} [Fintype ν]

/-- **The Hamiltonian relation of a cut-off transplant.** If `H_∞ f = h` with weak gradient `g`,
and the cutoff `χ` is supported in the retained region, then on the torus
`H_L T(χ f) = T(χ h) - C₀ T(χ f) + T([K, χ] f)` (`T` the normalised transplant, `C₀` the
zero-mode shift): on the support of `χ` the `g_L` interaction is the free one minus `C₀`, and
the kinetic energies differ by the commutator. -/
theorem transplant_hasGLHamiltonian (sys : CoulombSystem eta ν) {L R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {f h : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta}
    (hH : HasFreeHamiltonian sys P f h) (hg : HasWeakGrad f g) :
    HasGLHamiltonian sys L θ (X.chiW.cutL2 hL f)
      (X.chiW.cutL2 hL h - zeroModeShift sys L θ • X.chiW.cutL2 hL f +
        X.commT hL sys.mass f g) := by
  obtain ⟨v, hv, hK⟩ := hH
  refine ⟨X.chiW.cutL2 hL v - zeroModeShift sys L θ • X.chiW.cutL2 hL f, ?_, ?_⟩
  · -- the potential: on the support of `χ` the `g_L` interaction is `V_∞ - C₀`
    filter_upwards [Lp.coeFn_sub (X.chiW.cutL2 hL v) (zeroModeShift sys L θ • X.chiW.cutL2 hL f),
      Lp.coeFn_smul (zeroModeShift sys L θ) (X.chiW.cutL2 hL f),
      X.chiW.cutL2_ae hL v, X.chiW.cutL2_ae hL f, (qmp_cellCoord hL.ne').ae hv]
      with x h1 h2 h3 h4 h5
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
    simp only [BoxWeight.cutFun, Cutoff.chiW]
    rw [h5]
    by_cases h0 : X.χ (cellCoord L x) = 0
    · simp [h0]
    · rw [gLFourierPotential_eq_freePot sys hL hR0 hρ hone P hP hpos x (hret _ h0)]
      ring
  · -- the kinetic energy: the weak commutator identity, transplanted
    have hζ : X.chiW.cutL2 hL h - zeroModeShift sys L θ • X.chiW.cutL2 hL f +
        X.commT hL sys.mass f g -
        (X.chiW.cutL2 hL v - zeroModeShift sys L θ • X.chiW.cutL2 hL f) =
        X.chiW.cutL2 hL (h - v) + X.commT hL sys.mass f g := by
      rw [map_sub]
      abel
    rw [hζ]
    intro Φ hΦ
    have hΦ' : ContDiff ℝ 2 (fun r => torusRealLift Φ (L⁻¹ • r)) :=
      hΦ.comp (contDiff_const_smul L⁻¹)
    have hid := weak_comm_identity sys.mass X.smooth (X.hasCompactSupport hL) hΦ' hK hg
    beta_reduce at hid
    simp only [Cutoff.commT, inner_add_right, inner_sum, inner_smul_right,
      BoxWeight.inner_cutL2]
    simp_rw [← freeKinetic_lift sys hL.ne' Φ hΦ]
    simp only [Cutoff.chiW, Cutoff.d1W, Cutoff.d2W]
    rw [← hid, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ => by ring

end Transplant

/-! ## Observables -/

/-- **Multiplier observables**: for `G = χ_o ∘ cell`,
`⟨T(w f), G T(w f)⟩ = ∫ χ_o |w|² |f|²`. -/
lemma BoxWeight.inner_cutL2_mulCLM {L : ℝ} (hL : 0 < L) (W : BoxWeight eta L)
    {χo : Rcfg eta → ℝ} (G : C(MolecularPositionTorus eta, ℂ))
    (hG : ∀ x, G x = (χo (cellCoord L x) : ℂ)) (f : FreeL2 eta) :
    inner ℂ (W.cutL2 hL f) (PlaneWaveDynamics.mulCLM G (W.cutL2 hL f)) =
      ((∫ r, χo r * (‖W.w r‖ ^ 2 * ‖f r‖ ^ 2) : ℝ) : ℂ) := by
  obtain ⟨g, hg⟩ : ∃ g : Rcfg eta → ℝ, g = fun r =>
      L ^ Fintype.card (Fin eta × Fin 3) * (χo r * (‖W.w r‖ ^ 2 * ‖f r‖ ^ 2)) := ⟨_, rfl⟩
  rw [MeasureTheory.L2.inner_def]
  have hae : (fun x => inner ℂ ((W.cutL2 hL f : MolecularPositionTorus eta → ℂ) x)
      ((PlaneWaveDynamics.mulCLM G (W.cutL2 hL f) : MolecularPositionTorus eta → ℂ) x))
      =ᵐ[volume] fun x => ((g (cellCoord L x) : ℝ) : ℂ) := by
    filter_upwards [W.cutL2_ae hL f, PlaneWaveDynamics.mulCLM_ae G (W.cutL2 hL f)] with x h1 h2
    rw [RCLike.inner_apply, h2, h1, hG, hg]
    have hz := W.norm_sq_cutFun hL f x
    calc (χo (cellCoord L x) : ℂ) * W.cutFun f x * conj (W.cutFun f x)
        = (χo (cellCoord L x) : ℂ) * (conj (W.cutFun f x) * W.cutFun f x) := by ring
      _ = (χo (cellCoord L x) : ℂ) * ((‖W.cutFun f x‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.conj_mul']
          push_cast
          ring
      _ = _ := by
          rw [hz]
          push_cast
          ring
  have hgs : ∀ r, g r ≠ 0 → ∀ a, |r a| ≤ L / 4 :=
    W.supp_of fun r h => by rw [hg]; simp [h]
  rw [integral_congr_ae hae, integral_complex_ofReal, integral_comp_cellCoord hL g hgs, hg,
    smul_eq_mul, integral_const_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-! ## `prop:free-dyn`, the free-space step -/

section Main

variable {ν : Type} [Fintype ν]

/-- **`prop:free-dyn`, the free-space step.** Let `ψ_∞` solve the free-space Schrödinger
equation `i ψ' = H_∞ ψ` (`HasFreeHamiltonian`, with weak gradients `∇ψ_∞(s)`), let `χ` be a `C²`
cutoff, `χ = 1` on `B^one`, supported in the retained region, whose derivatives (bounded by
`D₁`, `D₂`) vanish off a shell `S ⊆ (B^one)ᶜ`, and let `U` be any propagator of the `g_L`
Hamiltonian `H_L` (zero mode removed). Under (H_leak) on `[0, t]`,
`∫_{(B^one)ᶜ} |ψ_∞(s)|² ≤ ε²` and `∫_S |∇ψ_∞(s)|² ≤ ε²`, the transplant `φ(s) = T(χ ψ_∞(s))`
satisfies

* `‖φ(t) - e^{-iC₀t} U(t) φ(0)‖ ≤ C ε t`, `C = 3η (D₁ + D₂/2)` (masses `≥ 1`), `C₀` the zero-mode
  shift (so `e^{-iC₀t} U(t)` is the torus evolution with the zero mode included);
* for every measurable multiplier `0 ≤ χ_o ≤ 1` whose torus version `G = χ_o ∘ cell` is continuous,
  `|⟨ψ_∞(t), χ_o ψ_∞(t)⟩ - ⟨U(t)φ(0), G U(t)φ(0)⟩| ≤ ε² + (‖ψ_∞(t)‖ + ‖ψ_∞(0)‖) C ε t`. -/
theorem free_dyn_torus (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hθ : Profile R θ) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta)
    (hU0 : ∀ ψ, U 0 ψ = ψ) (hUadd : ∀ s t ψ, U (s + t) ψ = U s (U t ψ))
    (hUcont : ∀ ψ, Continuous fun t => U t ψ)
    (hUderiv : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {χo : Rcfg eta → ℝ} (hχo0 : ∀ r, 0 ≤ χo r) (hχo1 : ∀ r, χo r ≤ 1) (hχom : Measurable χo)
    (G : C(MolecularPositionTorus eta, ℂ)) (hG : ∀ x, G x = (χo (cellCoord L x) : ℂ)) :
    ‖X.chiW.cutL2 hL (ψ t) - Complex.exp (-(Complex.I * (zeroModeShift sys L θ).re * t)) •
        U t (X.chiW.cutL2 hL (ψ 0))‖ ≤ X.commConst * ε * t ∧
      ‖((∫ r, χo r * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - inner ℂ (U t (X.chiW.cutL2 hL (ψ 0)))
          (PlaneWaveDynamics.mulCLM G (U t (X.chiW.cutL2 hL (ψ 0))))‖ ≤
        ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.commConst * ε * t) := by
  have hC₀ := zeroModeShift_re_eq sys hθ L
  -- Duhamel
  have hrel : ∀ s, HasGLHamiltonian sys L θ (X.chiW.cutL2 hL (ψ s))
      (X.chiW.cutL2 hL (H s) - zeroModeShift sys L θ • X.chiW.cutL2 hL (ψ s) +
        X.commT hL sys.mass (ψ s) (grad s)) := fun s =>
    transplant_hasGLHamiltonian sys hL hR0 hρ hone P hP hpos X hret (hHam s) (hgrad s)
  have hderiv : ∀ s, HasDerivAt (fun s => X.chiW.cutL2 hL (ψ s))
      (-(Complex.I • ((X.chiW.cutL2 hL (H s) - zeroModeShift sys L θ • X.chiW.cutL2 hL (ψ s) +
        X.commT hL sys.mass (ψ s) (grad s)) +
        (((zeroModeShift sys L θ).re : ℝ) : ℂ) • X.chiW.cutL2 hL (ψ s) +
        -X.commT hL sys.mass (ψ s) (grad s)))) s := by
    intro s
    have h : HasDerivAt (fun s => X.chiW.cutL2 hL (ψ s))
        (X.chiW.cutL2 hL (-(Complex.I • H s))) s :=
      ((X.chiW.cutL2 hL).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hψd s)
    convert h using 1
    rw [hC₀, map_neg, map_smul]
    module
  have hbound : ∀ s ∈ Icc 0 t, ‖-X.commT hL sys.mass (ψ s) (grad s)‖ ≤ X.commConst * ε :=
    fun s hs => by
      rw [norm_neg]
      exact X.norm_commT_le hL sys.one_le_mass hSm hSB hdS hd2S (ψ s) (grad s) hε
        (hleak0 s hs) (hleak1 s hs)
  have hD := duhamel_phase (HasGLHamiltonian sys L θ) U hU0 hUadd hUcont hUderiv
    (φ := fun s => X.chiW.cutL2 hL (ψ s))
    (ζ := fun s => X.chiW.cutL2 hL (H s) - zeroModeShift sys L θ • X.chiW.cutL2 hL (ψ s) +
      X.commT hL sys.mass (ψ s) (grad s))
    (r := fun s => -X.commT hL sys.mass (ψ s) (grad s))
    (zeroModeShift sys L θ).re hrel hderiv ht hbound
  refine ⟨hD, ?_⟩
  -- the observable
  set Xt := X.chiW.cutL2 hL (ψ t) with hXt
  set Z := U t (X.chiW.cutL2 hL (ψ 0)) with hZ
  set e := Complex.exp (-(Complex.I * (zeroModeShift sys L θ).re * t)) with he
  set Gop := PlaneWaveDynamics.mulCLM G with hGop
  have he1 : ‖e‖ = 1 := by
    rw [he, Complex.norm_exp]
    simp
  have hG1 : ‖G‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr fun x => by
    rw [hG x, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχo0 _)]
    exact hχo1 _
  have hGv : ∀ v, ‖Gop v‖ ≤ ‖v‖ := fun v =>
    (Gop.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg _)
      ((PlaneWaveDynamics.norm_mulCLM_le G).trans hG1))
  have hB : X.chiW.B = 1 := rfl
  have hXn : ‖Xt‖ ≤ ‖ψ t‖ := by
    have h := X.chiW.norm_cutL2_le hL (ψ t)
    rw [hB, one_mul] at h
    exact h
  have hZn : ‖Z‖ ≤ ‖ψ 0‖ := by
    rw [hZ, LinearIsometryEquiv.norm_map]
    have h := X.chiW.norm_cutL2_le hL (ψ 0)
    rw [hB, one_mul] at h
    exact h
  have hYn : ‖e • Z‖ ≤ ‖ψ 0‖ := by
    rw [norm_smul, he1, one_mul]
    exact hZn
  -- the free-space observable against the cut-off one
  have hobs := X.chiW.inner_cutL2_mulCLM hL G hG (ψ t)
  have hw2 : ∀ r, ‖X.chiW.w r‖ ^ 2 = X.χ r ^ 2 := fun r => by
    simp [Cutoff.chiW, Complex.norm_real, sq_abs]
  simp only [hw2] at hobs
  have hf2 : Integrable (fun r => ‖ψ t r‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (ψ t))).mp (Lp.memLp (ψ t))
  have hχm : Measurable X.χ := X.smooth.continuous.measurable
  have hI1 : Integrable (fun r => χo r * ‖ψ t r‖ ^ 2) :=
    hf2.bdd_mul (c := 1) hχom.aestronglyMeasurable (ae_of_all _ fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχo0 r)]
      exact hχo1 r)
  have hI2 : Integrable (fun r => χo r * (X.χ r ^ 2 * ‖ψ t r‖ ^ 2)) := by
    have h := hf2.bdd_mul (c := 1) (hχom.mul (hχm.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun r => by
        simp only [Pi.mul_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχo0 r) (sq_nonneg _))]
        have h1 : X.χ r ^ 2 ≤ 1 := by
          have := X.le_one r
          have := X.nonneg r
          nlinarith
        nlinarith [hχo0 r, hχo1 r, sq_nonneg (X.χ r)])
    refine h.congr (ae_of_all _ fun r => ?_)
    simp only [Pi.mul_apply]
    ring
  have hfree : |(∫ r, χo r * ‖ψ t r‖ ^ 2) - ∫ r, χo r * (X.χ r ^ 2 * ‖ψ t r‖ ^ 2)| ≤ ε ^ 2 := by
    rw [← integral_sub hI1 hI2]
    have hpt0 : ∀ r, 0 ≤ χo r * ‖ψ t r‖ ^ 2 - χo r * (X.χ r ^ 2 * ‖ψ t r‖ ^ 2) := fun r => by
      have h1 : X.χ r ^ 2 ≤ 1 := by
        have := X.le_one r
        have := X.nonneg r
        nlinarith
      have h2 : 0 ≤ χo r * ‖ψ t r‖ ^ 2 * (1 - X.χ r ^ 2) :=
        mul_nonneg (mul_nonneg (hχo0 r) (sq_nonneg _)) (by linarith)
      nlinarith
    rw [abs_of_nonneg (integral_nonneg hpt0)]
    calc ∫ r, (χo r * ‖ψ t r‖ ^ 2 - χo r * (X.χ r ^ 2 * ‖ψ t r‖ ^ 2))
        ≤ ∫ r, Boneᶜ.indicator (fun r => ‖ψ t r‖ ^ 2) r := by
          refine integral_mono_of_nonneg (ae_of_all _ hpt0) (hf2.indicator hBm.compl)
            (ae_of_all _ fun r => ?_)
          by_cases hr : r ∈ Bone
          · rw [indicator_of_notMem (fun h : r ∈ Boneᶜ => h hr)]
            simp [hχB r hr]
          · rw [indicator_of_mem hr]
            have h1 := hχo1 r
            have h2 : 0 ≤ X.χ r ^ 2 * ‖ψ t r‖ ^ 2 := by positivity
            nlinarith [hχo0 r, sq_nonneg (‖ψ t r‖)]
      _ = ∫ r in Boneᶜ, ‖ψ t r‖ ^ 2 := integral_indicator hBm.compl
      _ ≤ ε ^ 2 := hleak0 t ⟨ht, le_rfl⟩
  -- the cut-off observable against the torus evolution
  have hY : inner ℂ (e • Z) (Gop (e • Z)) = inner ℂ Z (Gop Z) := by
    rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', he1]
    simp
  have hdiff : ‖inner ℂ Xt (Gop Xt) - inner ℂ (e • Z) (Gop (e • Z))‖ ≤
      ‖Xt - e • Z‖ * (‖Xt‖ + ‖e • Z‖) := by
    have h : inner ℂ Xt (Gop Xt) - inner ℂ (e • Z) (Gop (e • Z)) =
        inner ℂ (Xt - e • Z) (Gop Xt) + inner ℂ (e • Z) (Gop (Xt - e • Z)) := by
      rw [inner_sub_left, map_sub, inner_sub_right]
      ring
    rw [h]
    calc ‖inner ℂ (Xt - e • Z) (Gop Xt) + inner ℂ (e • Z) (Gop (Xt - e • Z))‖
        ≤ ‖inner ℂ (Xt - e • Z) (Gop Xt)‖ + ‖inner ℂ (e • Z) (Gop (Xt - e • Z))‖ :=
          norm_add_le _ _
      _ ≤ ‖Xt - e • Z‖ * ‖Gop Xt‖ + ‖e • Z‖ * ‖Gop (Xt - e • Z)‖ :=
          add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖Xt - e • Z‖ * ‖Xt‖ + ‖e • Z‖ * ‖Xt - e • Z‖ :=
          add_le_add (mul_le_mul_of_nonneg_left (hGv _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hGv _) (norm_nonneg _))
      _ = ‖Xt - e • Z‖ * (‖Xt‖ + ‖e • Z‖) := by ring
  rw [← hY]
  calc ‖((∫ r, χo r * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - inner ℂ (e • Z) (Gop (e • Z))‖
      = ‖(((∫ r, χo r * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - inner ℂ Xt (Gop Xt)) +
          (inner ℂ Xt (Gop Xt) - inner ℂ (e • Z) (Gop (e • Z)))‖ := by ring_nf
    _ ≤ ‖((∫ r, χo r * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - inner ℂ Xt (Gop Xt)‖ +
          ‖inner ℂ Xt (Gop Xt) - inner ℂ (e • Z) (Gop (e • Z))‖ := norm_add_le _ _
    _ ≤ ε ^ 2 + ‖Xt - e • Z‖ * (‖Xt‖ + ‖e • Z‖) := by
        refine add_le_add ?_ hdiff
        rw [hobs, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact hfree
    _ ≤ ε ^ 2 + (X.commConst * ε * t) * (‖ψ t‖ + ‖ψ 0‖) := by
        have hC : 0 ≤ X.commConst * ε * t := le_trans (norm_nonneg _) hD
        exact add_le_add le_rfl (mul_le_mul hD (add_le_add hXn hYn) (by positivity) hC)
    _ = ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.commConst * ε * t) := by ring

end Main

end

end FreeBoundary
