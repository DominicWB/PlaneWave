import PlaneWave.FreeBoundary.TorusIMS

/-!
# `app:free`, part 15: the lower bound of `prop:free` under assumption (A)

The reverse transplant: a torus state supported in the retained region is carried to free space,
and the energy identities of `PlaneWave.FreeBoundary.Transplant` hold with equality. With IMS localisation on the torus
(`PlaneWave.FreeBoundary.TorusIMS`) this gives the lower bound of the text, under the finite-volume localisation
assumption (A) in the form of `C²` approximants of the torus ground state.

* `cellFun`, `contDiff_liftR_cell`, `tDR_cell`: a `C²` function on `ℝ^{3η}` that is constant
  outside the cube `[-L/4, L/4]^{3η}` descends to the torus, with coordinate derivatives `L ∂_a f`;
* `TorusLocPair`, `stdTorusLocPair`: the localisation pair `cos/sin(locPhase)` on the torus;
* `revT`: the reverse transplant (a smooth bump times the periodic lift);
* `transplant_torusEnergy`: `torusEnergy(Tφ) = L^{-3η}(E(φ) - C₀ ‖φ‖²)`;
* **`free_lower_torus`**: `E_∞ ≤ E_L + C₀ + Mτ/(2(1 - τ))` when the torus ground energy is
  approached by normalised `C²` sector states with mass `≤ τ` outside the inner region.
-/

set_option autoImplicit false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

local instance unitAddCircleMeasureSpaceFB15 : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

local instance unitAddCircleProbabilityMeasureFB15 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  instIsProbabilityMeasureUnitAddCircleVolume

local instance molecularTorusFiniteMeasureFB15 {eta : ℕ} :
    IsFiniteMeasure (volume : Measure (MolecularPositionTorus eta)) := by
  infer_instance

variable {eta : ℕ}

/-! ## Functions of the cell coordinates -/

lemma cellCoord_quot (L : ℝ) (y : Rcfg eta) :
    cellCoord L (torusRealQuotient _ y) = fun a => L * rep1 (y a) := by
  funext a
  unfold cellCoord torusRealQuotient
  rw [equivIoc_coe_rep1]

lemma sq_le_cfgSq (r : Rcfg eta) (a : Fin eta × Fin 3) : r a ^ 2 ≤ cfgSq r :=
  Finset.single_le_sum (f := fun b => r b ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)

/-- `f` is constant (`= f₀`) outside the cube `[-L/4, L/4]^{3η}`. -/
def ConstOutside (L : ℝ) (f : Rcfg eta → ℝ) (f0 : ℝ) : Prop :=
  ∀ r, f r ≠ f0 → ∀ a, |r a| ≤ L / 4

lemma supp4_of_constOutside {L : ℝ} {f : Rcfg eta → ℝ} {f0 : ℝ} (hf : ConstOutside L f f0) :
    Supp4 L (fun r => ((f r - f0 : ℝ) : ℂ)) := by
  intro r hr
  apply hf r
  intro h
  apply hr
  change ((f r - f0 : ℝ) : ℂ) = 0
  rw [h, sub_self, Complex.ofReal_zero]

/-- The torus function `x ↦ f(L · rep(x))`. -/
def cellFun (L : ℝ) (f : Rcfg eta → ℝ) (x : MolecularPositionTorus eta) : ℝ := f (cellCoord L x)

lemma liftR_cellFun (L : ℝ) (f : Rcfg eta → ℝ) (f0 : ℝ) (y : Rcfg eta) :
    liftR (cellFun L f) y = f0 + (perLift L (fun r => ((f r - f0 : ℝ) : ℂ)) y).re := by
  unfold liftR cellFun perLift
  rw [cellCoord_quot, Complex.ofReal_re]
  ring

lemma contDiff_liftR_cell {L : ℝ} (hL : 0 < L) {f : Rcfg eta → ℝ} {f0 : ℝ}
    (hf2 : ContDiff ℝ 2 f) (hf : ConstOutside L f f0) : ContDiff ℝ 2 (liftR (cellFun L f)) := by
  have hC : ContDiff ℝ 2 (fun r => ((f r - f0 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hf2.sub contDiff_const)
  have h := contDiff_perLift hL (supp4_of_constOutside hf) hC
  rw [show liftR (cellFun L f) = fun y => f0 + (perLift L (fun r => ((f r - f0 : ℝ) : ℂ)) y).re
    from funext (liftR_cellFun L f f0)]
  exact contDiff_const.add (Complex.reCLM.contDiff.comp h)

lemma liftR_cell_eventuallyEq {L : ℝ} (hL : 0 < L) {f : Rcfg eta → ℝ} {f0 : ℝ}
    (hf : ConstOutside L f f0) (y : Rcfg eta) :
    liftR (cellFun L f) =ᶠ[𝓝 y] fun y' => f (fun a => L * (y' a - ⌈y a - 1 / 2⌉)) := by
  filter_upwards [perLift_eventuallyEq hL (supp4_of_constOutside hf) y] with y' hy'
  rw [liftR_cellFun L f f0, hy', Complex.ofReal_re]
  ring

/-- The coordinate derivatives of `x ↦ f(L · rep(x))` are `L ∂_a f`. -/
lemma tDR_cell {L : ℝ} (hL : 0 < L) {f : Rcfg eta → ℝ} {f0 : ℝ} (hf2 : ContDiff ℝ 2 f)
    (hf : ConstOutside L f f0) (a : Fin eta × Fin 3) (x : MolecularPositionTorus eta) :
    tDR a (cellFun L f) x = L * dirD a f (cellCoord L x) := by
  obtain ⟨y, rfl⟩ := torusRealQuotient_surjective _ x
  rw [tDR_quot ((contDiff_liftR_cell hL hf2 hf).differentiable (by norm_num))]
  set n : Rcfg eta := fun b => ((⌈y b - 1 / 2⌉ : ℤ) : ℝ) with hn
  have hA : HasFDerivAt (fun y' : Rcfg eta => L • y' - L • n)
      (L • ContinuousLinearMap.id ℝ (Rcfg eta)) y :=
    ((hasFDerivAt_id y).const_smul L).sub_const (L • n)
  have hpt : (L • y - L • n) = cellCoord L (torusRealQuotient _ y) := by
    rw [cellCoord_quot]
    funext b
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rep1, hn]
    ring
  have hfd : HasFDerivAt f (fderiv ℝ f (L • y - L • n)) (L • y - L • n) :=
    ((hf2.differentiable (by norm_num)) _).hasFDerivAt
  have hcomp := hfd.comp y hA
  have hfun : (fun y' : Rcfg eta => f (fun a => L * (y' a - ⌈y a - 1 / 2⌉))) =
      f ∘ fun y' : Rcfg eta => L • y' - L • n := by
    funext y'
    simp only [Function.comp_apply]
    congr 1
    funext b
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hn]
    ring
  unfold dirD
  rw [(liftR_cell_eventuallyEq hL hf y).fderiv_eq, hfun, hcomp.fderiv, ← hpt]
  simp

/-! ## Localisation pairs on the torus -/

/-- A localisation pair `c² + e² = 1` on the torus: `c` vanishes outside the retained region
(in cell coordinates) and equals `1` on the inner region `S`; both are exchange-invariant; the
physical gradient bound `Σ_a ((∂_a c)² + (∂_a e)²) ≤ M L²` (torus coordinates), vanishing on
`S`. -/
structure TorusLocPair (eta : ℕ) (L R0 ρ : ℝ) (S : Set (MolecularPositionTorus eta)) (M : ℝ) where
  c : MolecularPositionTorus eta → ℝ
  e : MolecularPositionTorus eta → ℝ
  c_smooth : ContDiff ℝ 2 (liftR c)
  e_smooth : ContDiff ℝ 2 (liftR e)
  sq_add : ∀ x, c x ^ 2 + e x ^ 2 = 1
  c_swap : ∀ i j x, c (molecularPositionSwap i j x) = c x
  e_swap : ∀ i j x, e (molecularPositionSwap i j x) = e x
  c_supp : ∀ x, c x ≠ 0 → ∀ i, ‖particle (cellCoord L x) i‖ ≤ retainedRadius L R0 ρ
  c_one : ∀ x ∈ S, c x = 1
  grad_bound : ∀ x, ∑ a, (tDR a c x ^ 2 + tDR a e x ^ 2) ≤ M * L ^ 2
  grad_zero : ∀ x ∈ S, ∀ a, tDR a c x = 0 ∧ tDR a e x = 0

section Std

variable {L R0 ρ R1 : ℝ}

lemma locPhase_eq_of_ge (hR1 : 0 < R1) (h12 : R1 < retainedRadius L R0 ρ) {r : Rcfg eta}
    (hr : retainedRadius L R0 ρ ^ 2 ≤ cfgSq r) : locPhase L R0 ρ R1 r = Real.pi / 2 := by
  have hW : 0 < retainedRadius L R0 ρ ^ 2 - R1 ^ 2 := by nlinarith
  have h1 : 1 ≤ (cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) := by
    rw [le_div_iff₀ hW]
    linarith
  unfold locPhase
  rw [Real.smoothTransition.one_of_one_le h1, mul_one]

lemma abs_lt_of_phase (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hR1 : 0 < R1)
    (h12 : R1 < retainedRadius L R0 ρ) {r : Rcfg eta}
    (hr : locPhase L R0 ρ R1 r ≠ Real.pi / 2) (a : Fin eta × Fin 3) : |r a| ≤ L / 4 := by
  have hlt : cfgSq r < retainedRadius L R0 ρ ^ 2 := by
    by_contra hge
    push Not at hge
    exact hr (locPhase_eq_of_ge hR1 h12 hge)
  have hRL : 0 < retainedRadius L R0 ρ := lt_trans hR1 h12
  have h1 : r a ^ 2 < retainedRadius L R0 ρ ^ 2 := lt_of_le_of_lt (sq_le_cfgSq r a) hlt
  have h2 : |r a| < retainedRadius L R0 ρ := abs_lt_of_sq_lt_sq h1 hRL.le
  have h3 : retainedRadius L R0 ρ ≤ L / 4 := by
    unfold retainedRadius
    linarith
  linarith

lemma constOutside_cos (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hR1 : 0 < R1)
    (h12 : R1 < retainedRadius L R0 ρ) :
    ConstOutside L (fun r : Rcfg eta => Real.cos (locPhase L R0 ρ R1 r)) 0 := by
  intro r hr a
  refine abs_lt_of_phase hR0 hρ hR1 h12 (fun h => hr ?_) a
  simp only [h, Real.cos_pi_div_two]

lemma constOutside_sin (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hR1 : 0 < R1)
    (h12 : R1 < retainedRadius L R0 ρ) :
    ConstOutside L (fun r : Rcfg eta => Real.sin (locPhase L R0 ρ R1 r)) 1 := by
  intro r hr a
  refine abs_lt_of_phase hR0 hρ hR1 h12 (fun h => hr ?_) a
  simp only [h, Real.sin_pi_div_two]

lemma contDiff_cosPhase :
    ContDiff ℝ 2 (fun r : Rcfg eta => Real.cos (locPhase L R0 ρ R1 r)) :=
  Real.contDiff_cos.comp contDiff_locPhase

lemma contDiff_sinPhase :
    ContDiff ℝ 2 (fun r : Rcfg eta => Real.sin (locPhase L R0 ρ R1 r)) :=
  Real.contDiff_sin.comp contDiff_locPhase

lemma measurable_cellCoord (L : ℝ) : Measurable (cellCoord (eta := eta) L) := by
  unfold cellCoord
  refine measurable_pi_lambda _ fun a => measurable_const.mul ?_
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc 1 (-1 / 2)).measurable.comp (measurable_pi_apply a))

lemma measurableSet_inner (L R1 : ℝ) :
    MeasurableSet {x : MolecularPositionTorus eta | cfgSq (cellCoord L x) < R1 ^ 2} :=
  measurableSet_lt (contDiff_cfgSq.continuous.measurable.comp (measurable_cellCoord L))
    measurable_const

/-- **The localisation pair on the torus**, `c = cos(locPhase(L·rep))`, `e = sin(…)`. -/
def stdTorusLocPair (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hR1 : 0 < R1)
    (h12 : R1 < retainedRadius L R0 ρ) :
    TorusLocPair eta L R0 ρ {x | cfgSq (cellCoord L x) < R1 ^ 2} (locConst L R0 ρ R1) where
  c := cellFun L (fun r => Real.cos (locPhase L R0 ρ R1 r))
  e := cellFun L (fun r => Real.sin (locPhase L R0 ρ R1 r))
  c_smooth := contDiff_liftR_cell hL contDiff_cosPhase (constOutside_cos hR0 hρ hR1 h12)
  e_smooth := contDiff_liftR_cell hL contDiff_sinPhase (constOutside_sin hR0 hρ hR1 h12)
  sq_add := fun x => Real.cos_sq_add_sin_sq _
  c_swap := fun i j x => by
    unfold cellFun
    exact (stdLocPair (eta := eta) hR1 h12).χ_swap i j (cellCoord L x)
  e_swap := fun i j x => by
    unfold cellFun
    exact (stdLocPair (eta := eta) hR1 h12).η_swap i j (cellCoord L x)
  c_supp := fun x hx i => (stdLocPair (eta := eta) hR1 h12).χ_supp (cellCoord L x) hx i
  c_one := fun x hx => (stdLocPair (eta := eta) hR1 h12).χ_one (cellCoord L x) hx
  grad_bound := fun x => by
    rw [show (∑ a : Fin eta × Fin 3, (tDR a (cellFun L (fun r => Real.cos (locPhase L R0 ρ R1 r))) x ^ 2 +
        tDR a (cellFun L (fun r => Real.sin (locPhase L R0 ρ R1 r))) x ^ 2)) =
        L ^ 2 * ∑ a : Fin eta × Fin 3,
          (dirD a (fun r => Real.cos (locPhase L R0 ρ R1 r)) (cellCoord L x) ^ 2 +
            dirD a (fun r => Real.sin (locPhase L R0 ρ R1 r)) (cellCoord L x) ^ 2) by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [tDR_cell hL contDiff_cosPhase (constOutside_cos hR0 hρ hR1 h12),
        tDR_cell hL contDiff_sinPhase (constOutside_sin hR0 hρ hR1 h12)]
      ring]
    have h := (stdLocPair (eta := eta) hR1 h12).grad_bound (cellCoord L x)
    have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
    calc L ^ 2 * _ ≤ L ^ 2 * locConst L R0 ρ R1 := mul_le_mul_of_nonneg_left h hL2
      _ = locConst L R0 ρ R1 * L ^ 2 := mul_comm _ _
  grad_zero := fun x hx a => by
    have h := (stdLocPair (eta := eta) hR1 h12).grad_zero (cellCoord L x) hx a
    constructor
    · rw [tDR_cell hL contDiff_cosPhase (constOutside_cos hR0 hρ hR1 h12)]
      have h1 : dirD a (fun r => Real.cos (locPhase L R0 ρ R1 r)) (cellCoord L x) = 0 := h.1
      rw [h1, mul_zero]
    · rw [tDR_cell hL contDiff_sinPhase (constOutside_sin hR0 hρ hR1 h12)]
      have h2 : dirD a (fun r => Real.sin (locPhase L R0 ρ R1 r)) (cellCoord L x) = 0 := h.2
      rw [h2, mul_zero]

end Std

/-! ## The reverse transplant -/

/-- The cutoff profile `β(t) = T((L²/9 - t²)/(7L²/144))`: `1` for `|t| ≤ L/4`, `0` for
`|t| ≥ L/3`. -/
def betaCut (L t : ℝ) : ℝ := Real.smoothTransition ((L ^ 2 / 9 - t ^ 2) / (7 * L ^ 2 / 144))

/-- The bump `b(r) = Π_a β(r_a)`. -/
def bumpL (L : ℝ) (r : Rcfg eta) : ℝ := ∏ a, betaCut L (r a)

lemma contDiff_betaCut (L : ℝ) : ContDiff ℝ 2 (betaCut L) :=
  (Real.smoothTransition.contDiff (n := 2)).comp
    ((contDiff_const.sub (contDiff_id.pow 2)).div_const _)

lemma contDiff_bumpL (L : ℝ) : ContDiff ℝ 2 (bumpL (eta := eta) L) := by
  unfold bumpL
  exact contDiff_prod fun a _ => (contDiff_betaCut L).comp (contDiff_apply ℝ ℝ a)

lemma betaCut_one {L t : ℝ} (hL : 0 < L) (ht : |t| ≤ L / 4) : betaCut L t = 1 := by
  unfold betaCut
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by positivity)]
  have h : t ^ 2 ≤ (L / 4) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  nlinarith

lemma betaCut_zero {L t : ℝ} (hL : 0 < L) (ht : L / 3 ≤ |t|) : betaCut L t = 0 := by
  unfold betaCut
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have h : (L / 3) ^ 2 ≤ t ^ 2 := by
    have h' := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ L / 3) ht 2
    rwa [sq_abs] at h'
  nlinarith

lemma bumpL_one {L : ℝ} (hL : 0 < L) {r : Rcfg eta} (hr : ∀ a, |r a| ≤ L / 4) :
    bumpL L r = 1 :=
  Finset.prod_eq_one fun a _ => betaCut_one hL (hr a)

lemma abs_lt_of_bumpL_ne {L : ℝ} (hL : 0 < L) {r : Rcfg eta} (hr : bumpL L r ≠ 0)
    (a : Fin eta × Fin 3) : |r a| < L / 3 := by
  by_contra h
  push Not at h
  exact hr (Finset.prod_eq_zero (Finset.mem_univ a) (betaCut_zero hL h))

lemma bumpL_freeSwap (L : ℝ) (i j : Fin eta) (r : Rcfg eta) :
    bumpL L (freeSwap i j r) = bumpL L r := by
  unfold bumpL freeSwap
  exact Equiv.prod_comp ((Equiv.swap i j).prodCongr (Equiv.refl (Fin 3)))
    (fun a => betaCut L (r a))

/-- **The reverse transplant** of a torus function: the bump times the periodic lift
`r ↦ w(r/L)`. -/
def revT (L : ℝ) (w : MolecularPositionTorus eta → ℂ) (r : Rcfg eta) : ℂ :=
  (bumpL L r : ℂ) * torusRealLift w (L⁻¹ • r)

lemma quot_cellCoord {L : ℝ} (hL : L ≠ 0) (x : MolecularPositionTorus eta) :
    torusRealQuotient _ (L⁻¹ • cellCoord L x) = x := by
  funext a
  unfold torusRealQuotient cellCoord
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hL, one_mul, AddCircle.coe_equivIoc]

lemma cellCoord_quot_small {L : ℝ} (hL : 0 < L) {r : Rcfg eta} (hr : ∀ a, |r a| < L / 2) :
    cellCoord L (torusRealQuotient _ (L⁻¹ • r)) = r := by
  rw [cellCoord_quot]
  funext a
  have h := hr a
  have hm : (L⁻¹ • r) a ∈ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
    simp only [Pi.smul_apply, smul_eq_mul]
    obtain ⟨h1, h2⟩ := abs_lt.mp h
    constructor
    · rw [lt_inv_mul_iff₀ hL]
      linarith
    · rw [inv_mul_le_iff₀ hL]
      linarith
  rw [rep1_of_mem hm]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- A torus function supported in the retained region (cell coordinates). -/
def TorusRetained (L R0 ρ : ℝ) (w : MolecularPositionTorus eta → ℂ) : Prop :=
  ∀ x, w x ≠ 0 → ∀ i, ‖particle (cellCoord L x) i‖ ≤ retainedRadius L R0 ρ

lemma transplantFun_revT {L R0 ρ : ℝ} (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    {w : MolecularPositionTorus eta → ℂ} (hw : TorusRetained L R0 ρ w) :
    transplantFun L (revT L w) = w := by
  funext x
  rw [transplantFun_eq]
  unfold revT
  rw [show torusRealLift w (L⁻¹ • cellCoord L x) = w x by
    unfold torusRealLift
    rw [quot_cellCoord hL.ne']]
  by_cases h0 : w x = 0
  · rw [h0, mul_zero]
  · have hb : bumpL L (cellCoord L x) = 1 := by
      apply bumpL_one hL
      intro a
      have h1 := hw x h0 a.1
      have h2 := abs_coord_le_norm (particle (cellCoord L x) a.1) a.2
      have h3 : retainedRadius L R0 ρ ≤ L / 4 := by
        unfold retainedRadius
        linarith
      have h4 : (particle (cellCoord L x) a.1) a.2 = cellCoord L x a := rfl
      rw [h4] at h2
      linarith
    rw [hb, Complex.ofReal_one, one_mul]

lemma suppRet_revT {L R0 ρ : ℝ} (hL : 0 < L) {w : MolecularPositionTorus eta → ℂ}
    (hw : TorusRetained L R0 ρ w) : SuppRet L R0 ρ (revT L w) := by
  intro r hr i
  have hb : bumpL L r ≠ 0 := by
    intro h
    apply hr
    unfold revT
    rw [h, Complex.ofReal_zero, zero_mul]
  have hw0 : w (torusRealQuotient _ (L⁻¹ • r)) ≠ 0 := by
    intro h
    apply hr
    unfold revT torusRealLift
    rw [h, mul_zero]
  have hsmall : ∀ a, |r a| < L / 2 := fun a => by
    have := abs_lt_of_bumpL_ne hL hb a
    linarith
  have h := hw _ hw0 i
  rwa [cellCoord_quot_small hL hsmall] at h

lemma contDiff_revT {L : ℝ} {w : MolecularPositionTorus eta → ℂ}
    (hw : ContDiff ℝ 2 (torusRealLift w)) : ContDiff ℝ 2 (revT L w) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_bumpL L)).mul (hw.comp (contDiff_const_smul L⁻¹))

lemma hasCompactSupport_revT {L : ℝ} (hL : 0 < L) (w : MolecularPositionTorus eta → ℂ) :
    HasCompactSupport (revT L w) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Rcfg eta) (L / 3)) fun r hr => ?_
  by_contra hne
  apply hr
  have hb : bumpL L r ≠ 0 := by
    intro h
    apply hne
    unfold revT
    rw [h, Complex.ofReal_zero, zero_mul]
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
  intro a
  rw [Real.norm_eq_abs]
  exact (abs_lt_of_bumpL_ne hL hb a).le

lemma isFreeSector_revT {L : ℝ} {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ}
    {w : MolecularPositionTorus eta → ℂ}
    (hS : ∀ i j : Fin eta, i ≠ j → lab i = lab j →
      ∀ x, w (molecularPositionSwap i j x) = sgn i * w x) :
    IsFreeSector sgn lab (revT L w) := by
  intro i j hij hlab r
  unfold revT
  rw [bumpL_freeSwap]
  have h : torusRealLift w (L⁻¹ • freeSwap i j r) =
      w (molecularPositionSwap i j (torusRealQuotient _ (L⁻¹ • r))) := rfl
  rw [h, hS i j hij hlab]
  unfold torusRealLift
  ring

/-! ## The energy identity of the transplant -/

lemma norm_sq_toLp_eq (w : C(MolecularPositionTorus eta, ℂ)) :
    ‖(ContinuousMap.toLp 2 volume ℂ) w‖ ^ 2 = ∫ x, ‖w x‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), ContinuousMap.inner_toLp]
  have hc : ∀ x, w x * conj (w x) = ((‖w x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [hc]
  rw [integral_complex_ofReal, RCLike.re_to_complex, Complex.ofReal_re]

section System

variable {ν : Type} [Fintype ν]

lemma re_inner_pot (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    (w : C(MolecularPositionTorus eta, ℂ)) {p : MolecularPositionL2 eta}
    (hp : HasL2PointwisePotential volume (gLFourierPotential sys L θ)
      ((ContinuousMap.toLp 2 volume ℂ) w) p) :
    (inner ℂ ((ContinuousMap.toLp 2 volume ℂ) w) p).re =
      ∫ x, (gLFourierPotential sys L θ x).re * ‖w x‖ ^ 2 := by
  have hcT := w.coeFn_toLp (p := 2) (𝕜 := ℂ) (volume : Measure (MolecularPositionTorus eta))
  have hae : (fun x => inner ℂ (((ContinuousMap.toLp 2 volume ℂ) w) x) (p x))
      =ᵐ[volume] fun x => gLFourierPotential sys L θ x * w x * conj (w x) := by
    filter_upwards [hp, hcT] with x h1 h2
    rw [RCLike.inner_apply, h1, h2]
  have hint : Integrable (fun x => gLFourierPotential sys L θ x * w x * conj (w x)) :=
    (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) _ _).congr hae
  rw [MeasureTheory.L2.inner_def, integral_congr_ae hae]
  rw [← RCLike.re_to_complex, ← integral_re hint]
  congr 1
  funext x
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, RCLike.re_to_complex]
  exact Complex.re_mul_ofReal _ _

lemma re_integral_pot_split (sys : CoulombSystem eta ν) (P : ν → E3) (C0 : ℂ)
    {φ : Rcfg eta → ℂ} (hV : Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2))
    (hN : Integrable (fun r => ‖φ r‖ ^ 2)) :
    (∫ r, ((freePot sys P r : ℂ) - C0) * φ r * conj (φ r)).re =
      (∫ r, freePot sys P r * ‖φ r‖ ^ 2) - C0.re * ∫ r, ‖φ r‖ ^ 2 := by
  have hpt : ∀ r, ((freePot sys P r : ℂ) - C0) * φ r * conj (φ r) =
      ((freePot sys P r * ‖φ r‖ ^ 2 : ℝ) : ℂ) - C0 * ((‖φ r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  simp_rw [hpt]
  have hV' : Integrable (fun r => ((freePot sys P r * ‖φ r‖ ^ 2 : ℝ) : ℂ)) := hV.ofReal
  have hN' : Integrable (fun r => C0 * ((‖φ r‖ ^ 2 : ℝ) : ℂ)) :=
    (hN.ofReal : Integrable (fun r => ((‖φ r‖ ^ 2 : ℝ) : ℂ))).const_mul C0
  rw [integral_sub hV' hN', integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, Complex.sub_re, Complex.ofReal_re,
    Complex.re_mul_ofReal]

/-- **The energy identity of the transplant**: for a `C²` free-space state supported in the
retained region, `torusEnergy(Tφ) = L^{-3η}(E(φ) - C₀ ‖φ‖²)` and `‖Tφ‖² = L^{-3η} ‖φ‖²`; the
Coulomb term of `φ` is integrable. -/
theorem transplant_torusEnergy (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hθ : Profile R θ) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {φ : Rcfg eta → ℂ} (h2 : ContDiff ℝ 2 φ) (hsupp : SuppRet L R0 ρ φ) :
    torusEnergy sys L θ (transplant hL φ (hsupp.supp4 hR0 hρ) h2)
        (contDiff_transplant_lift hL _ h2) =
      (L ^ Fintype.card (Fin eta × Fin 3))⁻¹ *
        (freeEnergy sys P φ - (zeroModeShift sys L θ).re * ∫ r, ‖φ r‖ ^ 2) ∧
    (∫ x, ‖transplant hL φ (hsupp.supp4 hR0 hρ) h2 x‖ ^ 2) =
      (L ^ Fintype.card (Fin eta × Fin 3))⁻¹ * ∫ r, ‖φ r‖ ^ 2 ∧
    Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) := by
  obtain ⟨p, hp, hinner, hint⟩ := transplant_potential sys hL hθ hR0 hρ hone P hP hpos h2 hsupp
  have hs4 : Supp4 L φ := hsupp.supp4 hR0 hρ
  have hint2 := integrable_mul_conj hL hs4 h2
  have hc2 : ∀ r, φ r * conj (φ r) = ((‖φ r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint2' : Integrable (fun r => ((‖φ r‖ ^ 2 : ℝ) : ℂ)) :=
    hint2.congr (ae_of_all _ fun r => hc2 r)
  have hpt : ∀ r, ((freePot sys P r : ℂ) - zeroModeShift sys L θ) * φ r * conj (φ r) =
      ((freePot sys P r * ‖φ r‖ ^ 2 : ℝ) : ℂ) -
        zeroModeShift sys L θ * ((‖φ r‖ ^ 2 : ℝ) : ℂ) := by
    intro r
    rw [mul_assoc, hc2]
    push_cast
    ring
  have hint3 : Integrable (fun r => ((freePot sys P r * ‖φ r‖ ^ 2 : ℝ) : ℂ)) := by
    have hfun : (fun r => ((freePot sys P r * ‖φ r‖ ^ 2 : ℝ) : ℂ)) = fun r =>
        ((freePot sys P r : ℂ) - zeroModeShift sys L θ) * φ r * conj (φ r) +
          zeroModeShift sys L θ * ((‖φ r‖ ^ 2 : ℝ) : ℂ) := by
      funext r
      rw [hpt]
      ring
    rw [hfun]
    exact hint.add (hint2'.const_mul _)
  have hreal : Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) := by
    refine hint3.re.congr (ae_of_all _ fun r => ?_)
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
  have hNreal : Integrable (fun r => ‖φ r‖ ^ 2) := by
    refine hint2'.re.congr (ae_of_all _ fun r => ?_)
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine ⟨?_, ?_, hreal⟩
  · unfold torusEnergy
    rw [← ContinuousMap.inner_toLp, inner_kinetic_transplant sys hL hs4 h2,
      ← re_inner_pot sys L θ _ hp, hinner, Complex.smul_re, Complex.smul_re, smul_eq_mul,
      smul_eq_mul, re_integral_pot_split sys P _ hreal hNreal]
    unfold freeEnergy
    ring
  · rw [← norm_sq_toLp_eq, norm_sq_toLp_transplant hL hs4 h2]

/-! ## The lower bound -/

lemma torusEnergy_congr (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
    {w₁ w₂ : C(MolecularPositionTorus eta, ℂ)} (h : w₁ = w₂)
    (h₁ : ContDiff ℝ 2 (torusRealLift w₁)) (h₂ : ContDiff ℝ 2 (torusRealLift w₂)) :
    torusEnergy sys L θ w₁ h₁ = torusEnergy sys L θ w₂ h₂ := by
  subst h
  rfl

/-- **`prop:free`, lower bound, under the finite-volume localisation assumption (A).** Let `E_L`
be the torus ground energy of the sector (zero mode removed), `C` a localisation pair on the
torus with inner region `S` and gradient constant `M`. If `E_∞` bounds the free-space form below
on the `C²` sector states of compact support, and for every `ε > 0` a normalised `C²` torus state
of the sector has `g_L` energy `≤ E_L + ε` and mass `≤ τ < 1` outside `S` (assumption (A) for
`C²` approximants of the torus ground state), then `E_∞ ≤ E_L + C₀ + Mτ/(2(1 - τ))`. -/
theorem free_lower_torus (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} {L R R0 ρ : ℝ}
    {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {E : ℝ} (hE : IsGLTorusGroundEnergy sys lab L θ E)
    {S : Set (MolecularPositionTorus eta)} (hSm : MeasurableSet S) {M : ℝ}
    (C : TorusLocPair eta L R0 ρ S M) {Einf τ : ℝ} (hτ : τ < 1)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (hA : ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy sys L θ u hu ≤ E + ε ∧
      ∫ x in Sᶜ, ‖u x‖ ^ 2 ≤ τ) :
    Einf ≤ E + (zeroModeShift sys L θ).re + M * τ / (2 * (1 - τ)) := by
  refine le_of_forall_pos_le_add fun ε' hε' => ?_
  have hd : 0 < 1 - τ := by linarith
  obtain ⟨u, hu, hsec, hN, hen, htail⟩ := hA (ε' * (1 - τ)) (by positivity)
  have hc := C.c_smooth
  have he := C.e_smooth
  have h1 := C.sq_add
  have hims := torusEnergy_ims sys hL hθ hc he h1 hu
  set w := cutT C.c (continuous_of_liftR hc.continuous) u with hw_def
  set we := cutT C.e (continuous_of_liftR he.continuous) u with hwe_def
  have hwl : ContDiff ℝ 2 (torusRealLift w) := contDiff_lift_ofReal_mul hc hu
  have hwel : ContDiff ℝ 2 (torusRealLift we) := contDiff_lift_ofReal_mul he hu
  have hwx : ∀ x, w x = (C.c x : ℂ) * u x := fun x => rfl
  have hwex : ∀ x, we x = (C.e x : ℂ) * u x := fun x => rfl
  -- the two masses
  have hiw : Integrable (fun x => ‖w x‖ ^ 2) :=
    integrable_of_continuous_torus (w.continuous.norm.pow 2)
  have hiwe : Integrable (fun x => ‖we x‖ ^ 2) :=
    integrable_of_continuous_torus (we.continuous.norm.pow 2)
  have hsum : (∫ x, ‖w x‖ ^ 2) + (∫ x, ‖we x‖ ^ 2) = 1 := by
    calc (∫ x, ‖w x‖ ^ 2) + (∫ x, ‖we x‖ ^ 2) = ∫ x, (‖w x‖ ^ 2 + ‖we x‖ ^ 2) :=
          (integral_add hiw hiwe).symm
      _ = ∫ x, ‖u x‖ ^ 2 := by
          congr 1
          funext x
          rw [hwx, hwex, norm_ofReal_mul_sq, norm_ofReal_mul_sq]
          linear_combination ‖u x‖ ^ 2 * h1 x
      _ = 1 := hN
  have hu2 : Integrable (fun x => ‖u x‖ ^ 2) :=
    integrable_of_continuous_torus (u.continuous.norm.pow 2)
  have hτ0 : 0 ≤ τ :=
    le_trans (setIntegral_nonneg_of_ae (ae_of_all _ fun x => by positivity)) htail
  have hNw : 1 - τ ≤ ∫ x, ‖w x‖ ^ 2 := by
    have hS1 : (∫ x in S, ‖u x‖ ^ 2) + (∫ x in Sᶜ, ‖u x‖ ^ 2) = 1 :=
      (integral_add_compl hSm hu2).trans hN
    have hS2 : ∫ x in S, ‖u x‖ ^ 2 ≤ ∫ x, ‖w x‖ ^ 2 := by
      have heq : ∫ x in S, ‖u x‖ ^ 2 = ∫ x in S, ‖w x‖ ^ 2 := by
        refine setIntegral_congr_fun hSm fun x hx => ?_
        rw [hwx, norm_ofReal_mul_sq, C.c_one x hx]
        ring
      rw [heq]
      exact setIntegral_le_integral hiw (ae_of_all _ fun x => by positivity)
    linarith
  have hNwpos : 0 < ∫ x, ‖w x‖ ^ 2 := lt_of_lt_of_le hd hNw
  -- the localisation error
  have hL2 : 0 < L ^ 2 := by positivity
  have hM0 : 0 ≤ M := by
    have h := C.grad_bound (fun _ => 0)
    have h0 : 0 ≤ ∑ a : Fin eta × Fin 3, (tDR a C.c (fun _ => 0) ^ 2 +
        tDR a C.e (fun _ => 0) ^ 2) := Finset.sum_nonneg fun a _ => by positivity
    nlinarith
  have hG : (1 / (2 * L ^ 2)) * ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ *
      ∫ x, (tDR a C.c x ^ 2 + tDR a C.e x ^ 2) * ‖u x‖ ^ 2 ≤ M * τ / 2 := by
    have hint : ∀ a : Fin eta × Fin 3, Integrable
        (fun x => (tDR a C.c x ^ 2 + tDR a C.e x ^ 2) * ‖u x‖ ^ 2) := fun a =>
      integrable_of_continuous_torus ((((continuous_tDR (hc.of_le (by norm_num)) a).pow 2).add
        ((continuous_tDR (he.of_le (by norm_num)) a).pow 2)).mul (u.continuous.norm.pow 2))
    have hstep1 : ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ *
        ∫ x, (tDR a C.c x ^ 2 + tDR a C.e x ^ 2) * ‖u x‖ ^ 2 ≤
        ∫ x, (∑ a : Fin eta × Fin 3, (tDR a C.c x ^ 2 + tDR a C.e x ^ 2)) * ‖u x‖ ^ 2 := by
      rw [show (fun x => (∑ a : Fin eta × Fin 3, (tDR a C.c x ^ 2 + tDR a C.e x ^ 2)) *
          ‖u x‖ ^ 2) = fun x => ∑ a : Fin eta × Fin 3,
            (tDR a C.c x ^ 2 + tDR a C.e x ^ 2) * ‖u x‖ ^ 2 from
          funext fun x => Finset.sum_mul _ _ _, integral_finsetSum _ (fun a _ => hint a)]
      refine Finset.sum_le_sum fun a _ => ?_
      have hI : 0 ≤ ∫ x, (tDR a C.c x ^ 2 + tDR a C.e x ^ 2) * ‖u x‖ ^ 2 :=
        integral_nonneg fun x => by positivity
      have hm : (sys.mass a.1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (sys.one_le_mass a.1)
      nlinarith
    have hstep2 : ∫ x, (∑ a : Fin eta × Fin 3, (tDR a C.c x ^ 2 + tDR a C.e x ^ 2)) *
        ‖u x‖ ^ 2 ≤ ∫ x, Sᶜ.indicator (fun y => M * L ^ 2 * ‖u y‖ ^ 2) x := by
      refine integral_mono (by
          have h := integrable_finsetSum (s := Finset.univ) (fun a _ => hint a)
          refine h.congr (ae_of_all _ fun x => ?_)
          simp only
          rw [Finset.sum_mul])
        ((hu2.const_mul (M * L ^ 2)).indicator hSm.compl) fun x => ?_
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_notMem (by simpa using hx)]
        have h0 : ∑ a : Fin eta × Fin 3, (tDR a C.c x ^ 2 + tDR a C.e x ^ 2) = 0 :=
          Finset.sum_eq_zero fun a _ => by
            rw [(C.grad_zero x hx a).1, (C.grad_zero x hx a).2]
            ring
        rw [h0, zero_mul]
      · rw [Set.indicator_of_mem (by simpa using hx)]
        exact mul_le_mul_of_nonneg_right (C.grad_bound x) (by positivity)
    have hstep3 : ∫ x, Sᶜ.indicator (fun y => M * L ^ 2 * ‖u y‖ ^ 2) x ≤ M * L ^ 2 * τ := by
      rw [integral_indicator hSm.compl, integral_const_mul]
      exact mul_le_mul_of_nonneg_left htail (by positivity)
    have h4 : (1 / (2 * L ^ 2)) * (M * L ^ 2 * τ) = M * τ / 2 := by
      field_simp
    have h5 : 0 ≤ 1 / (2 * L ^ 2) := by positivity
    calc (1 / (2 * L ^ 2)) * ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ *
          ∫ x, (tDR a C.c x ^ 2 + tDR a C.e x ^ 2) * ‖u x‖ ^ 2
        ≤ (1 / (2 * L ^ 2)) * (M * L ^ 2 * τ) :=
          mul_le_mul_of_nonneg_left (hstep1.trans (hstep2.trans hstep3)) h5
      _ = M * τ / 2 := h4
  -- the outer part is bounded below by `E_L`
  have hwe_sec : ∀ i j : Fin eta, i ≠ j → lab i = lab j →
      ∀ x, we (molecularPositionSwap i j x) = sys.sign i * we x := by
    intro i j hij hlab x
    rw [hwex, hwex, C.e_swap, hsec i j hij hlab]
    ring
  have hvar := torus_variational sys hL hθ hR hE we hwel hwe_sec
  -- the inner part
  have key : torusEnergy sys L θ w hwl ≤
      E * (∫ x, ‖w x‖ ^ 2) + (ε' * (1 - τ) + M * τ / 2) := by
    have hNwe : ∫ x, ‖we x‖ ^ 2 = 1 - ∫ x, ‖w x‖ ^ 2 := by linarith
    rw [hNwe] at hvar
    linarith [hims, hG, hen, hvar]
  -- the reverse transplant
  have hwret : TorusRetained L R0 ρ w := fun x hx i => C.c_supp x (fun h0 => hx (by
    rw [hwx, h0, Complex.ofReal_zero, zero_mul])) i
  have hw_sec : ∀ i j : Fin eta, i ≠ j → lab i = lab j →
      ∀ x, w (molecularPositionSwap i j x) = sys.sign i * w x := by
    intro i j hij hlab x
    rw [hwx, hwx, C.c_swap, hsec i j hij hlab]
    ring
  have hφ2 : ContDiff ℝ 2 (revT L w) := contDiff_revT hwl
  have hφsupp : SuppRet L R0 ρ (revT L w) := suppRet_revT hL hwret
  obtain ⟨hEid, hNid, hVint⟩ :=
    transplant_torusEnergy sys hL hθ hR0 hρ hone P hP hpos hφ2 hφsupp
  have hT : transplant hL (revT L w) (hφsupp.supp4 hR0 hρ) hφ2 = w :=
    ContinuousMap.ext fun x => congrFun (transplantFun_revT hL hR0 hρ hwret) x
  rw [torusEnergy_congr sys L θ hT _ hwl] at hEid
  have hNid' : ∫ x, ‖w x‖ ^ 2 =
      (L ^ Fintype.card (Fin eta × Fin 3))⁻¹ * ∫ r, ‖revT L w r‖ ^ 2 := by
    rw [← hNid, hT]
  have hlowφ := hlow (revT L w) hφ2 (hasCompactSupport_revT hL w) (isFreeSector_revT hw_sec)
    hVint
  -- the arithmetic
  set c : ℝ := (L ^ Fintype.card (Fin eta × Fin 3))⁻¹ with hc_def
  have hc0 : 0 < c := by positivity
  set Nφ := ∫ r, ‖revT L w r‖ ^ 2 with hNφ
  set Nw := ∫ x, ‖w x‖ ^ 2 with hNw_def
  set C0 := (zeroModeShift sys L θ).re with hC0
  set X := ε' * (1 - τ) + M * τ / 2 with hX
  have hA1 : Einf * Nw ≤ (E + C0) * Nw + X := by
    have h5 : c * (Einf * Nφ) ≤ c * freeEnergy sys P (revT L w) :=
      mul_le_mul_of_nonneg_left hlowφ hc0.le
    rw [hNid'] at key ⊢
    nlinarith [h5, hEid, key]
  have hX0 : 0 ≤ X := by positivity
  have h8 : Einf - E - C0 ≤ X / Nw := by
    rw [le_div_iff₀ hNwpos]
    linarith
  have h9 : X / Nw ≤ X / (1 - τ) := div_le_div_of_nonneg_left hX0 hd hNw
  have h10 : X / (1 - τ) = M * τ / (2 * (1 - τ)) + ε' := by
    rw [hX]
    field_simp
    ring
  linarith

/-- The torus ground energy is unique. -/
lemma IsGLTorusGroundEnergy.unique {sys : CoulombSystem eta ν} {lab : Fin eta → ℕ} {L : ℝ}
    {θ : ℝ → ℝ} {E₁ E₂ : ℝ} (h₁ : IsGLTorusGroundEnergy sys lab L θ E₁)
    (h₂ : IsGLTorusGroundEnergy sys lab L θ E₂) : E₁ = E₂ := by
  have key : ∀ {A B : ℝ}, IsGLTorusGroundEnergy sys lab L θ A →
      IsGLTorusGroundEnergy sys lab L θ B → B ≤ A := by
    intro A B hA hB
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, u, hu, hn, hlt⟩ := hA.2 ε hε
    have h := hB.1 n u hu
    rw [hn, one_pow, mul_one] at h
    linarith
  exact le_antisymm (key h₂ h₁) (key h₁ h₂)

/-- **`prop:free`, the two-sided bound** (eq:free-energy). Under the free-space hypotheses
(`E_∞` bounds the form below on the `C²` sector states of compact support; the infimum is
approached by normalised such states with mass `≤ τ` outside `|r| < R_L - w`) and assumption (A)
(the torus ground energy `E_L` is approached by normalised `C²` torus states of the sector with
mass `≤ τ_A` outside the same region), with `δ = π² B²/w² · max(τ/(2(1-τ)), τ_A/(2(1-τ_A)))`:
`|E_L + C₀ - E_∞| ≤ δ`, and the grid energies satisfy `|E_{N,L} + C₀ - E_∞| ≤ δ + C K^{-3}`. -/
theorem free_grid_two_sided (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (hw : 0 < w) (hwL : w < retainedRadius L R0 ρ)
    {EL : ℝ} (hEL : IsGLTorusGroundEnergy sys lab L θ EL)
    {Einf τ τA : ℝ} (hτ : τ < 1) (hτA : τA < 1)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (happrox : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | cfgSq r < (retainedRadius L R0 ρ - w) ^ 2}ᶜ, ‖φ r‖ ^ 2 ≤ τ)
    (hA : ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy sys L θ u hu ≤ EL + ε ∧
      ∫ x in {x | cfgSq (cellCoord L x) < (retainedRadius L R0 ρ - w) ^ 2}ᶜ, ‖u x‖ ^ 2 ≤ τA) :
    |EL + (zeroModeShift sys L θ).re - Einf| ≤
        Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) ∧
      ∀ m : ℕ, PlaneWaveGridG.gLGridThreshold sys L (tv R θ) EL ≤ m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) +
              PlaneWaveGridG.gLGridErrorConstant sys L (tv R θ) EL /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  have hR1 : 0 < retainedRadius L R0 ρ - w := by linarith
  have h12 : retainedRadius L R0 ρ - w < retainedRadius L R0 ρ := by linarith
  set K0 := Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 with hK0
  have hK0nn : 0 ≤ K0 := by positivity
  set δ := K0 * max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) with hδ
  have hτA0 : 0 ≤ τA := by
    obtain ⟨u, -, -, -, -, ht⟩ := hA 1 one_pos
    exact le_trans (setIntegral_nonneg_of_ae (ae_of_all _ fun x => by positivity)) ht
  -- upper bound
  have hup := free_upper_agmon sys hL hθ hR hR0 hρ hone P hP hpos hEL hw hwL hτ hlow happrox
  have hup' : EL + (zeroModeShift sys L θ).re ≤ Einf + δ := by
    have h1 : K0 * τ / (2 * (1 - τ)) = K0 * (τ / (2 * (1 - τ))) := by ring
    have h2 : K0 * (τ / (2 * (1 - τ))) ≤ δ :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hK0nn
    linarith
  -- lower bound
  have hlowb := free_lower_torus sys hL hθ hR hR0 hρ hone P hP hpos hEL
    (measurableSet_inner L (retainedRadius L R0 ρ - w)) (stdTorusLocPair hL hR0 hρ hR1 h12)
    hτA hlow hA
  have hM := locConst_le (L := L) (R0 := R0) (ρ := ρ) (R1 := retainedRadius L R0 ρ - w) hw rfl
    hwL.le
  have hlow' : Einf ≤ EL + (zeroModeShift sys L θ).re + δ := by
    have hdA : 0 < 2 * (1 - τA) := by linarith
    have h1 : locConst L R0 ρ (retainedRadius L R0 ρ - w) * τA / (2 * (1 - τA)) ≤
        K0 * (τA / (2 * (1 - τA))) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hM (div_nonneg hτA0 hdA.le)
    have h2 : K0 * (τA / (2 * (1 - τA))) ≤ δ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hK0nn
    linarith
  have habs : |EL + (zeroModeShift sys L θ).re - Einf| ≤ δ := by
    rw [abs_le]
    constructor <;> linarith
  refine ⟨habs, fun m hm => ?_⟩
  obtain ⟨E, hE, hgrid⟩ := PlaneWaveGridG.gLSectorGridError sys lab hlab hL hθ
  have hEE : E = EL := hE.unique hEL
  subst hEE
  obtain ⟨Eg, hEg, herr⟩ := hgrid m hm
  refine ⟨Eg, hEg, ?_⟩
  have h3 : |Eg + (zeroModeShift sys L θ).re - Einf| ≤
      |Eg - E| + |E + (zeroModeShift sys L θ).re - Einf| := by
    have := abs_add_le (Eg - E) (E + (zeroModeShift sys L θ).re - Einf)
    rw [show Eg - E + (E + (zeroModeShift sys L θ).re - Einf) =
      Eg + (zeroModeShift sys L θ).re - Einf by ring] at this
    exact this
  linarith

lemma half_ratio_le {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1 / 2) : τ / (2 * (1 - τ)) ≤ τ := by
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **eq:free-energy in exponential form.** With the Agmon decay of the free ground state
(mass `≤ A e^{-2α d}` outside `|r| < d`, `d = R_L - w`) and assumption (A) (mass `≤ A' e^{-2β d}`),
both at most `1/2`:
`|E_L + C₀ - E_∞| ≤ C' e^{-γ L}` and `|E_{N,L} + C₀ - E_∞| ≤ C' e^{-γ L} + C K^{-3}`, with
`γ = min(α, β)/2` and `C' = π² B²/w² · max(A, A') · e^{2 max(α, β)(R₀ + ρ + w)}`. -/
theorem free_grid_exponential (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (hw : 0 < w) (hwL : w < retainedRadius L R0 ρ)
    {EL : ℝ} (hEL : IsGLTorusGroundEnergy sys lab L θ EL)
    {Einf A α A' β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsmall : A * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))) ≤ 1 / 2)
    (hsmall' : A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w))) ≤ 1 / 2)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (happrox : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | cfgSq r < (retainedRadius L R0 ρ - w) ^ 2}ᶜ, ‖φ r‖ ^ 2 ≤
        A * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))))
    (hA : ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy sys L θ u hu ≤ EL + ε ∧
      ∫ x in {x | cfgSq (cellCoord L x) < (retainedRadius L R0 ρ - w) ^ 2}ᶜ, ‖u x‖ ^ 2 ≤
        A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w)))) :
    |EL + (zeroModeShift sys L θ).re - Einf| ≤
        Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
          Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) ∧
      ∀ m : ℕ, PlaneWaveGridG.gLGridThreshold sys L (tv R θ) EL ≤ m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
              Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) +
              PlaneWaveGridG.gLGridErrorConstant sys L (tv R θ) EL /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  set d := retainedRadius L R0 ρ - w with hd
  have hd0 : 0 < d := by linarith
  set τ := A * Real.exp (-(2 * α * d)) with hτ_def
  set τA := A' * Real.exp (-(2 * β * d)) with hτA_def
  have hτ0 : 0 ≤ τ := by
    obtain ⟨φ, -, -, -, -, -, -, ht⟩ := happrox 1 one_pos
    exact le_trans (setIntegral_nonneg_of_ae (ae_of_all _ fun r => by positivity)) ht
  have hτA0 : 0 ≤ τA := by
    obtain ⟨u, -, -, -, -, ht⟩ := hA 1 one_pos
    exact le_trans (setIntegral_nonneg_of_ae (ae_of_all _ fun x => by positivity)) ht
  obtain ⟨h1, h2⟩ := free_grid_two_sided sys lab hlab hL hθ hR hR0 hρ hone P hP hpos hw hwL hEL
    (by linarith : τ < 1) (by linarith : τA < 1) hlow happrox hA
  -- the exponential bound for `max(τ/(2(1-τ)), τA/(2(1-τA)))`
  have hA0 : 0 ≤ A := by
    by_contra h
    push Not at h
    have : A * Real.exp (-(2 * α * d)) < 0 := mul_neg_of_neg_of_pos h (Real.exp_pos _)
    linarith
  have hA'0 : 0 ≤ A' := by
    by_contra h
    push Not at h
    have : A' * Real.exp (-(2 * β * d)) < 0 := mul_neg_of_neg_of_pos h (Real.exp_pos _)
    linarith
  have hexp : ∀ γ' : ℝ, min α β ≤ γ' → Real.exp (-(2 * γ' * d)) ≤
      Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) := by
    intro γ' hγ'
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hdL : d = L / 4 - R0 - ρ - w := by rw [hd]; unfold retainedRadius; ring
    have hm1 : min α β ≤ max α β := min_le_max
    have hm0 : 0 ≤ min α β := le_min hα hβ
    have hRw : 0 ≤ R0 + ρ + w := by linarith
    rw [hdL]
    nlinarith [mul_le_mul_of_nonneg_right hγ' hd0.le, mul_le_mul_of_nonneg_right hm1 hRw]
  have hbound : max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) ≤
      max A A' * (Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2))) := by
    apply max_le
    · calc τ / (2 * (1 - τ)) ≤ τ := half_ratio_le hτ0 hsmall
        _ = A * Real.exp (-(2 * α * d)) := rfl
        _ ≤ max A A' * (Real.exp (2 * max α β * (R0 + ρ + w)) *
              Real.exp (-(min α β * L / 2))) :=
          mul_le_mul (le_max_left _ _) (hexp α (min_le_left _ _)) (Real.exp_pos _).le
            (le_trans hA0 (le_max_left _ _))
    · calc τA / (2 * (1 - τA)) ≤ τA := half_ratio_le hτA0 hsmall'
        _ = A' * Real.exp (-(2 * β * d)) := rfl
        _ ≤ max A A' * (Real.exp (2 * max α β * (R0 + ρ + w)) *
              Real.exp (-(min α β * L / 2))) :=
          mul_le_mul (le_max_right _ _) (hexp β (min_le_right _ _)) (Real.exp_pos _).le
            (le_trans hA0 (le_max_left _ _))
  have hK0 : 0 ≤ Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 := by positivity
  have hfin := mul_le_mul_of_nonneg_left hbound hK0
  have heq : Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * (max A A' *
      (Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)))) =
      Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
        Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) := by ring
  rw [heq] at hfin
  refine ⟨h1.trans hfin, fun m hm => ?_⟩
  obtain ⟨Eg, hEg, herr⟩ := h2 m hm
  exact ⟨Eg, hEg, by linarith⟩

end System

end

end FreeBoundary
