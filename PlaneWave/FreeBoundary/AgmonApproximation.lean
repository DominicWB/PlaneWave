import PlaneWave.FreeBoundary.FormApproximation

/-!
# Free-space regularity, part 8: approximate ground states from an eigenfunction

The upper bound of `prop:free` takes normalised `C²` states of compact support of the sector with
energy `≤ E_∞ + ε` and small mass outside the retained region. The manuscript assumes instead a
ground state `ψ_∞` with Agmon decay. If `H_∞ ψ_∞ = E_∞ ψ_∞`, `‖ψ_∞‖ = 1`, then
`E_∞ = (1/2) Σ_a m_a⁻¹ ‖∂_a ψ_∞‖² + ∫ V_∞ |ψ_∞|²`, and the normalised approximants `φ_n/‖φ_n‖` of
`PlaneWave.FreeBoundary.FormApproximation` converge in the form norm, so their energies tend to
`E_∞` and their masses outside any set to that of `ψ_∞`. With `Σ_i ∫ e^{2α|x_i|} |ψ_∞|² ≤ A`, the
mass of `ψ_∞` outside `{every |x_i| < R}` is at most `A e^{-2αR}`.

* `eigen_energy`: the energy identity for an eigenfunction;
* `freeEnergy_smul`, `setIntegral_sq_tendsto`: scaling and convergence of masses;
* **`approx_ground`**: approximate ground states with mass `≤ τ` on a set where `ψ_∞` has mass
  `< τ`;
* **`approx_ground_agmon`**: with Agmon decay, mass `≤ 2 max(A, 1) e^{-2αR}` outside
  `{every |x_i| < R}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology ENNReal
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Energy

/-- **The energy of an eigenfunction**: `H_∞ ψ = E ψ`, `‖ψ‖ = 1` give
`E = (1/2) Σ_a m_a⁻¹ ‖g_a‖² + ∫ V_∞ |ψ|²`. -/
theorem eigen_energy (sys : CoulombSystem eta ν) (P : ν → E3) {ψ : FreeL2 eta} {E : ℝ}
    (hH : HasFreeHamiltonian sys P ψ ((E : ℂ) • ψ)) (hn : ‖ψ‖ = 1)
    {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad ψ g) :
    E = (1 / 2) * ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ * ‖g a‖ ^ 2 +
      ∫ r, freePot sys P r * ‖ψ r‖ ^ 2 := by
  obtain ⟨v, hv, hK⟩ := hH
  have e1 := inner_weak_kinetic hK hg
  have e2 : ⟪ψ, v⟫_ℂ = ((∫ x, freePot sys P x * ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_L2_eq, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hv] with x hx
    rw [hx, ← mul_assoc, mul_comm (conj (ψ x)), mul_assoc, Complex.conj_mul']
    push_cast
    ring
  have e3 : ⟪ψ, (E : ℂ) • ψ⟫_ℂ = (E : ℂ) := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hn]
    simp
  have e4 : (E : ℂ) = (((1 / 2) * ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ * ‖g a‖ ^ 2 : ℝ) : ℂ) +
      ((∫ x, freePot sys P x * ‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← e3, ← e1, ← e2, ← inner_add_right, sub_add_cancel]
  exact_mod_cast e4

section Generic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma integrable_sq_Lp (f : Lp ℂ 2 μ) : Integrable (fun x => ‖f x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

lemma integral_norm_mul_le (a b : Lp ℂ 2 μ) : ∫ x, ‖a x‖ * ‖b x‖ ∂μ ≤ ‖a‖ * ‖b‖ := by
  have h := sq_integral_mul_le (μ := μ) (fun x => norm_nonneg (a x))
    (fun x => norm_nonneg (b x)) ((Lp.memLp a).norm.integrable_mul (Lp.memLp b).norm)
    (integrable_sq_Lp a) (integrable_sq_Lp b)
  rw [← norm_sq_L2_eq a, ← norm_sq_L2_eq b, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (integral_nonneg fun x => mul_nonneg (norm_nonneg _)
    (norm_nonneg _)) (by positivity) two_ne_zero).mp h

/-- The mass on a set depends continuously on `f ∈ L²`. -/
lemma setIntegral_sq_sub_le (T : Set α) (a b : Lp ℂ 2 μ) :
    |(∫ x in T, ‖a x‖ ^ 2 ∂μ) - ∫ x in T, ‖b x‖ ^ 2 ∂μ| ≤ ‖a - b‖ * (‖a‖ + ‖b‖) := by
  have ia := (integrable_sq_Lp a).integrableOn (s := T)
  have ib := (integrable_sq_Lp b).integrableOn (s := T)
  have hd : (⇑(a - b) : α → ℂ) =ᵐ[μ] fun x => a x - b x := Lp.coeFn_sub a b
  have hpt : ∀ x, |‖a x‖ ^ 2 - ‖b x‖ ^ 2| ≤ ‖a x - b x‖ * ‖a x‖ + ‖a x - b x‖ * ‖b x‖ := by
    intro x
    have h1 : |‖a x‖ - ‖b x‖| ≤ ‖a x - b x‖ := abs_norm_sub_norm_le _ _
    have e : ‖a x‖ ^ 2 - ‖b x‖ ^ 2 = (‖a x‖ - ‖b x‖) * (‖a x‖ + ‖b x‖) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖a x‖ + ‖b x‖)]
    have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ ‖a x‖ + ‖b x‖)
    linarith
  have j1 : Integrable (fun x => ‖(a - b) x‖ * ‖a x‖) μ :=
    (Lp.memLp (a - b)).norm.integrable_mul (Lp.memLp a).norm
  have j2 : Integrable (fun x => ‖(a - b) x‖ * ‖b x‖) μ :=
    (Lp.memLp (a - b)).norm.integrable_mul (Lp.memLp b).norm
  have j1' : Integrable (fun x => ‖a x - b x‖ * ‖a x‖) μ :=
    j1.congr (hd.mono fun x hx => by simp only [hx])
  have j2' : Integrable (fun x => ‖a x - b x‖ * ‖b x‖) μ :=
    j2.congr (hd.mono fun x hx => by simp only [hx])
  calc |(∫ x in T, ‖a x‖ ^ 2 ∂μ) - ∫ x in T, ‖b x‖ ^ 2 ∂μ|
      = |∫ x in T, (‖a x‖ ^ 2 - ‖b x‖ ^ 2) ∂μ| := by rw [integral_sub ia ib]
    _ ≤ ∫ x in T, |‖a x‖ ^ 2 - ‖b x‖ ^ 2| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, |‖a x‖ ^ 2 - ‖b x‖ ^ 2| ∂μ :=
        setIntegral_le_integral ((integrable_sq_Lp a).sub (integrable_sq_Lp b)).abs
          (ae_of_all _ fun x => abs_nonneg _)
    _ ≤ ∫ x, (‖a x - b x‖ * ‖a x‖ + ‖a x - b x‖ * ‖b x‖) ∂μ :=
        integral_mono ((integrable_sq_Lp a).sub (integrable_sq_Lp b)).abs (j1'.add j2') hpt
    _ = (∫ x, ‖(a - b) x‖ * ‖a x‖ ∂μ) + ∫ x, ‖(a - b) x‖ * ‖b x‖ ∂μ := by
        rw [integral_add j1' j2']
        congr 1
        · exact integral_congr_ae (hd.mono fun x hx => by simp only [hx])
        · exact integral_congr_ae (hd.mono fun x hx => by simp only [hx])
    _ ≤ ‖a - b‖ * ‖a‖ + ‖a - b‖ * ‖b‖ :=
        add_le_add (integral_norm_mul_le _ _) (integral_norm_mul_le _ _)
    _ = ‖a - b‖ * (‖a‖ + ‖b‖) := by ring

lemma setIntegral_sq_tendsto (T : Set α) {f : ℕ → Lp ℂ 2 μ} {f₀ : Lp ℂ 2 μ}
    (hf : Tendsto f atTop (𝓝 f₀)) :
    Tendsto (fun n => ∫ x in T, ‖f n x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x in T, ‖f₀ x‖ ^ 2 ∂μ)) := by
  have hb : Tendsto (fun n => ‖f n - f₀‖ * (‖f n‖ + ‖f₀‖)) atTop (𝓝 (0 * (‖f₀‖ + ‖f₀‖))) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hf).mul (hf.norm.add tendsto_const_nhds)
  rw [zero_mul] at hb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
  rw [Real.norm_eq_abs]
  exact setIntegral_sq_sub_le T (f n) f₀

end Generic

/-- Scaling: `E(c u) = c² E(u)` for a `C²` function of compact support. -/
lemma freeEnergy_smul (sys : CoulombSystem eta ν) (P : ν → E3) {u : Rcfg eta → ℂ}
    (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) (c : ℝ) :
    freeEnergy sys P (fun r => (c : ℂ) * u r) = c ^ 2 * freeEnergy sys P u := by
  have hcu : ContDiff ℝ 2 (fun r => (c : ℂ) * u r) := contDiff_const.mul hu
  have hccs : HasCompactSupport (fun r => (c : ℂ) * u r) := hcs.mul_left
  rw [freeEnergy_eq sys P hcu hccs, freeEnergy_eq sys P hu hcs]
  have hd : ∀ a x, dirD a (fun r => (c : ℂ) * u r) x = (c : ℂ) * dirD a u x := fun a x =>
    dirD_const_mul ((hu.differentiable two_ne_zero) x) (c : ℂ) a
  have hn : ∀ z : ℂ, ‖(c : ℂ) * z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := fun z => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  unfold gradForm
  simp_rw [hd, hn, integral_const_mul]
  have hp : ∫ r, freePot sys P r * (c ^ 2 * ‖u r‖ ^ 2) =
      c ^ 2 * ∫ r, freePot sys P r * ‖u r‖ ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext r
    ring
  rw [hp]
  have hs : ∀ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ * (c ^ 2 * ∫ x, ‖dirD a u x‖ ^ 2) =
      c ^ 2 * ((sys.mass a.1)⁻¹ * ∫ x, ‖dirD a u x‖ ^ 2) := fun a => by ring
  simp_rw [hs]
  rw [← Finset.mul_sum]
  ring

end Energy

/-! ## Approximate ground states -/

section Approx

/-- **Approximate ground states from an eigenfunction**: if `H_∞ ψ = E ψ`, `‖ψ‖ = 1`, `ψ` is in
the sector and has mass `< τ` on `T`, then for every `ε > 0` there is a normalised `C²` state of
compact support of the sector with energy `≤ E + ε` and mass `≤ τ` on `T`. -/
theorem approx_ground (sys : CoulombSystem eta ν) (P : ν → E3) (lab : Fin eta → ℕ)
    {ψ : FreeL2 eta} {E : ℝ} (hH : HasFreeHamiltonian sys P ψ ((E : ℂ) • ψ)) (hn : ‖ψ‖ = 1)
    (hS : ∀ i j : Fin eta, i ≠ j → lab i = lab j → ∀ᵐ r, ψ (freeSwap i j r) = sys.sign i * ψ r)
    (T : Set (Rcfg eta)) {τ : ℝ} (hτ : ∫ r in T, ‖ψ r‖ ^ 2 < τ) :
    ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ E + ε ∧ ∫ r in T, ‖φ r‖ ^ 2 ≤ τ := by
  intro ε hε
  have hH' := hH
  obtain ⟨v, hv, hK⟩ := hH'
  obtain ⟨g, -, hg, -⟩ := weak_kinetic_regularity (fun i => sys.mass_pos i) hK
  obtain ⟨hf, hgr⟩ := apprN_tendsto ψ hg
  have hE := eigen_energy sys P hH hn hg
  -- the energies of the approximants
  have hEn : ∀ n, freeEnergy sys P (apprN ψ n) =
      (1 / 2) * ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ * ‖apprGrad ψ n a‖ ^ 2 +
        ∫ r, freePot sys P r * ‖apprL2 ψ n r‖ ^ 2 := by
    intro n
    rw [freeEnergy_eq sys P (contDiff_apprN ψ n) (hasCompactSupport_apprN ψ n)]
    unfold gradForm
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [apprGrad, norm_sq_eq_of_ae (memLp_dirD_apprN ψ n a).coeFn_toLp]
    · refine integral_congr_ae ?_
      filter_upwards [(memLp_apprN ψ n).coeFn_toLp] with r hr
      rw [apprL2, hr]
  have hEt : Tendsto (fun n => freeEnergy sys P (apprN ψ n)) atTop (𝓝 E) := by
    simp_rw [hEn]
    rw [hE]
    refine Tendsto.add (Tendsto.const_mul _ (tendsto_finsetSum _ fun a _ =>
      Tendsto.const_mul _ (((hgr a).norm).pow 2))) ?_
    exact tendsto_integral_freePot sys P (hasWeakGrad_apprL2 ψ) hg hf hgr
  have hNt : Tendsto (fun n => ‖apprL2 ψ n‖ ^ 2) atTop (𝓝 1) := by
    have := (hf.norm).pow 2
    rwa [hn, one_pow] at this
  have hTt : Tendsto (fun n => ∫ r in T, ‖apprN ψ n r‖ ^ 2) atTop (𝓝 (∫ r in T, ‖ψ r‖ ^ 2)) := by
    have h := setIntegral_sq_tendsto T hf
    refine h.congr fun n => ?_
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (memLp_apprN ψ n).coeFn_toLp] with r hr
    rw [apprL2, hr]
  -- the normalised quantities
  have hq1 := hEt.div hNt one_ne_zero
  have hq2 := hTt.div hNt one_ne_zero
  rw [div_one] at hq1 hq2
  have ev1 : ∀ᶠ n in atTop, freeEnergy sys P (apprN ψ n) / ‖apprL2 ψ n‖ ^ 2 < E + ε :=
    hq1.eventually (gt_mem_nhds (by linarith))
  have ev2 : ∀ᶠ n in atTop, (∫ r in T, ‖apprN ψ n r‖ ^ 2) / ‖apprL2 ψ n‖ ^ 2 < τ :=
    hq2.eventually (gt_mem_nhds hτ)
  have ev3 : ∀ᶠ n in atTop, (1 : ℝ) / 2 < ‖apprL2 ψ n‖ ^ 2 :=
    hNt.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨n, h1, h2, h3⟩ := (ev1.and (ev2.and ev3)).exists
  set N := ‖apprL2 ψ n‖ with hNdef
  have hN : 0 < N := by
    by_contra hc
    have : N = 0 := le_antisymm (not_lt.mp hc) (norm_nonneg _)
    rw [this] at h3
    norm_num at h3
  have hN2 : N ^ 2 = ∫ r, ‖apprN ψ n r‖ ^ 2 := by
    rw [hNdef, apprL2, norm_sq_eq_of_ae (memLp_apprN ψ n).coeFn_toLp]
  set c : ℝ := N⁻¹ with hc
  have hc2 : c ^ 2 * N ^ 2 = 1 := by
    rw [hc, inv_pow]
    field_simp
  have hnorm : ∀ z : ℂ, ‖(c : ℂ) * z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := fun z => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  refine ⟨fun r => (c : ℂ) * apprN ψ n r, contDiff_const.mul (contDiff_apprN ψ n),
    (hasCompactSupport_apprN ψ n).mul_left, fun i j hij hl r => ?_, ?_, ?_, ?_, ?_⟩
  · simp only
    rw [apprN_freeSwap ψ (hS i j hij hl) n r]
    ring
  · have hi := (freePot_integral sys P (hasWeakGrad_apprL2 ψ n)).1
    have hi' : Integrable fun r => freePot sys P r * ‖apprN ψ n r‖ ^ 2 :=
      hi.congr (by
        filter_upwards [(memLp_apprN ψ n).coeFn_toLp] with r hr
        rw [apprL2, hr])
    refine (hi'.const_mul (c ^ 2)).congr (ae_of_all _ fun r => ?_)
    simp only
    rw [hnorm]
    ring
  · simp_rw [hnorm]
    rw [integral_const_mul, ← hN2, hc2]
  · rw [freeEnergy_smul sys P (contDiff_apprN ψ n) (hasCompactSupport_apprN ψ n)]
    have e : c ^ 2 * freeEnergy sys P (apprN ψ n) =
        freeEnergy sys P (apprN ψ n) / ‖apprL2 ψ n‖ ^ 2 := by
      rw [hc, inv_pow, ← hNdef]
      ring
    rw [e]
    exact h1.le
  · simp_rw [hnorm]
    rw [integral_const_mul]
    have e : c ^ 2 * ∫ r in T, ‖apprN ψ n r‖ ^ 2 =
        (∫ r in T, ‖apprN ψ n r‖ ^ 2) / ‖apprL2 ψ n‖ ^ 2 := by
      rw [hc, inv_pow, ← hNdef]
      ring
    rw [e]
    exact h2.le

/-- **Approximate ground states with Agmon decay**: if moreover
`Σ_i ∫ e^{2α|x_i|} |ψ|² ≤ A`, the approximate ground states can be chosen with mass
`≤ 2 max(A, 1) e^{-2αR}` outside `{every |x_i| < R}`. -/
theorem approx_ground_agmon (sys : CoulombSystem eta ν) (P : ν → E3) (lab : Fin eta → ℕ)
    {ψ : FreeL2 eta} {E : ℝ} (hH : HasFreeHamiltonian sys P ψ ((E : ℂ) • ψ)) (hn : ‖ψ‖ = 1)
    (hS : ∀ i j : Fin eta, i ≠ j → lab i = lab j → ∀ᵐ r, ψ (freeSwap i j r) = sys.sign i * ψ r)
    {α A : ℝ} (hα : 0 ≤ α)
    (hAi : ∀ i, Integrable fun r => Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2)
    (hA : ∑ i, ∫ r, Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2 ≤ A) (R : ℝ) :
    ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ E + ε ∧
      ∫ r in {r | ∀ i, ‖particle r i‖ < R}ᶜ, ‖φ r‖ ^ 2 ≤
        2 * max A 1 * Real.exp (-(2 * α * R)) := by
  set T := {r : Rcfg eta | ∀ i, ‖particle r i‖ < R}ᶜ with hTdef
  have hS0 : Integrable fun r => ∑ i, Real.exp (-(2 * α * R)) *
      (Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2) :=
    integrable_finsetSum _ fun i _ => (hAi i).const_mul _
  have htail : ∫ r in T, ‖ψ r‖ ^ 2 ≤ Real.exp (-(2 * α * R)) * A := by
    calc ∫ r in T, ‖ψ r‖ ^ 2
        ≤ ∫ r in T, ∑ i, Real.exp (-(2 * α * R)) *
            (Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2) := by
          refine setIntegral_mono_on (integrable_sq_L2 ψ).integrableOn hS0.integrableOn
            (by
              have hm : MeasurableSet {r : Rcfg eta | ∀ i, ‖particle r i‖ < R} := by
                rw [Set.setOf_forall]
                exact MeasurableSet.iInter fun i =>
                  measurableSet_lt (continuous_norm_particle i).measurable measurable_const
              exact hm.compl) fun r hr => ?_
          simp only [hTdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt] at hr
          obtain ⟨i, hi⟩ := hr
          have h1 : 1 ≤ Real.exp (-(2 * α * R)) * Real.exp (2 * α * ‖particle r i‖) := by
            rw [← Real.exp_add]
            apply Real.one_le_exp
            nlinarith
          have h2 : ‖ψ r‖ ^ 2 ≤ Real.exp (-(2 * α * R)) *
              (Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2) := by
            nlinarith [sq_nonneg ‖ψ r‖]
          refine h2.trans (Finset.single_le_sum (f := fun j => Real.exp (-(2 * α * R)) *
            (Real.exp (2 * α * ‖particle r j‖) * ‖ψ r‖ ^ 2)) (fun j _ => by positivity)
            (Finset.mem_univ i))
      _ ≤ ∫ r, ∑ i, Real.exp (-(2 * α * R)) *
            (Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2) :=
          setIntegral_le_integral hS0 (ae_of_all _ fun r =>
            Finset.sum_nonneg fun i _ => by positivity)
      _ = Real.exp (-(2 * α * R)) *
            ∑ i, ∫ r, Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2 := by
          rw [integral_finsetSum _ fun i _ => (hAi i).const_mul _, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul]
      _ ≤ Real.exp (-(2 * α * R)) * A := mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le
  have hlt : ∫ r in T, ‖ψ r‖ ^ 2 < 2 * max A 1 * Real.exp (-(2 * α * R)) := by
    have he := Real.exp_pos (-(2 * α * R))
    have hm : A ≤ max A 1 := le_max_left _ _
    have hm1 : 1 ≤ max A 1 := le_max_right _ _
    nlinarith
  exact approx_ground sys P lab hH hn hS T hlt

end Approx

end FreeBoundary
