import PlaneWave.FreeBoundary.FreeDynamicsEndpoint
import PlaneWave.FreeBoundary.FreeDynamicsBOUniform
import PlaneWave.FreeBoundary.SpinFreeDynamicsEndpoint
import PlaneWave.KineticLog.OpenVbar

/-!
# `prop:free-dyn` for a uniform bound on the profile variation

`prop:free-dyn` assumes only a uniform bound `V_θ ≤ V̄` on the total variation of the
range-truncation profiles. The endpoints of `PlaneWave.FreeBoundary.FreeDynamicsEndpoint`,
`FreeDynamicsBO`, `FreeDynamicsBOUniform` and `SpinFreeDynamicsEndpoint` have constants
`freeDynConst sys V_θ …`, `freeDynConstNBO`, `freeDynConstBO`, `freeDynConstSpinNBO`,
`freeDynConstSpinBO`, and the uniform forms fix `V_θ = V`. The profile enters these constants
only through the grid constants `(A₁, A₂, A₃) = gridConstsSharp_gLU sys V_θ …`, which are built from
the `L`-free constants `relBU`, `gLtailMU`, `gLzU`, `gLAU`, `gridFlowConstU` and `sigmaU` by sums,
products, powers and square roots with nonnegative coefficients. Each of these is increasing in
`V`, hence

* `gridConstsSharp_gLU_mono_V`: `A_i(V_θ) ≤ A_i(V̄)` componentwise, and `freeDynConst_mono`,
  `freeDynConstNBO_mono`, `freeDynConstBO_mono`, `freeDynConstSpinNBO_mono`,
  `freeDynConstSpinBO_mono`: every constant is increasing in `V`.

The thresholds (`m ≥ 8`, `K ≥ 8`, `L ≥ L₀`) do not depend on the profile. The endpoints hold with
the constants at `V̄`, for every profile with `V_θ ≤ V̄`:

* `free_dyn_endpoint_vbar` (any system, (H_dom) assumed), `free_dyn_nbo_endpoint_vbar`,
  `free_dyn_grid_bo_vbar` (compatible cutoffs, the domain condition proved);
* `free_dyn_uniform_vbar`, `free_dyn_nbo_uniform_vbar`, `free_dyn_bo_uniform_vbar` (the explicit
  cutoffs, one constant for every `L ≥ L₀`);
* `free_dyn_nbo_spin_endpoint_vbar`, `free_dyn_bo_spin_endpoint_vbar`,
  `free_dyn_nbo_spin_uniform_vbar`, `free_dyn_bo_spin_uniform_vbar` (internal spin).

The grid kernel class keeps the majorant `(1 + V_θ) ŵ` of the actual profile (eq:rangecut).

The intermediate statements, not in the form of the manuscript (`free_dyn_grid_gL`,
`free_dyn_grid_gLU_schwartz_cell`, `free_dyn_grid_nbo`, `free_dyn_grid_nbo_reg`,
`free_dyn_grid_nbo_cell`, `free_dyn_grid_spin`), keep their constants written with
`gridConstsSharp_gLU sys V_θ …`; `gridConstsSharp_gLU_mono_V` bounds them by their values at `V̄`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLref gLzU gLzU_nonneg gLAU)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The grid constants are increasing in `V` -/

section Mono

/-- `flow2` is increasing in all of its arguments but the first. -/
lemma flow2_mono' {g cJ cH sc X Y S cJ' cH' sc' X' Y' S' : ℝ} (hcJ : 0 ≤ cJ) (hcH : 0 ≤ cH)
    (hsc : 0 ≤ sc) (hY : 0 ≤ Y) (hS : 0 ≤ S) (ecJ : cJ ≤ cJ') (ecH : cH ≤ cH') (esc : sc ≤ sc')
    (eX : X ≤ X') (eY : Y ≤ Y') (eS : S ≤ S') :
    flow2 g cJ cH sc X Y S ≤ flow2 g cJ' cH' sc' X' Y' S' := by
  unfold flow2
  have : 0 ≤ cJ' := hcJ.trans ecJ
  have : 0 ≤ cH' := hcH.trans ecH
  have : 0 ≤ sc' := hsc.trans esc
  have : 0 ≤ Y' := hY.trans eY
  have : 0 ≤ S' := hS.trans eS
  gcongr

variable (sys : CoulombSystem eta ν) {V V' Hunit : ℝ}

lemma sigmaU_mono (hV : 0 ≤ V) (hVV : V ≤ V') : sigmaU sys V ≤ sigmaU sys V' := by
  unfold sigmaU
  have := KineticLog.gLAU_mono sys hV hVV
  have := KineticLog.gLzU_mono sys hVV
  gcongr

/-- `gLtailMU` is increasing in `V` and in `M ≥ 0`. -/
lemma gLtailMU_mono' (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) {M M' : ℝ} (hM : 0 ≤ M)
    (hMM : M ≤ M') : gLtailMU sys V Hunit M ≤ gLtailMU sys V' Hunit M' := by
  unfold gLtailMU
  have := sys.couplingWeight_nonneg
  have : 0 ≤ PlaneWaveGridG.ctailU Hunit := by
    unfold PlaneWaveGridG.ctailU PlaneWaveGridG.tBU
    positivity
  have : 0 ≤ 1 + V := by linarith
  have : 0 ≤ 1 + V' := by linarith
  gcongr

/-- **`Φ_U` is increasing in `V`.** -/
lemma gridPhiU_mono_V (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit)
    {Cχ D2 D4 s0 hu hs hv : ℝ} (hCχ : 0 ≤ Cχ) (hD2 : 0 ≤ D2) (h0 : 0 ≤ s0) (h1 : 0 ≤ hu)
    (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    gridPhiU sys V Hunit Cχ D2 D4 s0 hu hs hv ≤ gridPhiU sys V' Hunit Cχ D2 D4 s0 hu hs hv := by
  have hV' := hV.trans hVV
  have hM := sys.one_le_maxMass
  have hb := relBU_nonneg sys hV hH
  have hb' := relBU_nonneg sys hV' hH
  have hbb := KineticLog.relBU_mono sys hV hVV hH
  have hcJ := gridFlowConstU_nonneg sys hV
  have hcJ' := gridFlowConstU_nonneg sys hV'
  have hcJJ := KineticLog.gridFlowConstU_mono sys hV hVV
  have hA := KineticLog.gLAU_nonneg' sys hV
  have hA' := KineticLog.gLAU_nonneg' sys hV'
  have hAA := KineticLog.gLAU_mono sys hV hVV
  have hσ := sigmaU_nonneg sys hV
  have hσ' := sigmaU_nonneg sys hV'
  have hσσ := sigmaU_mono sys hV hVV
  have hcw := sys.couplingWeight_nonneg
  have hct : 0 ≤ PlaneWaveGridG.ctailU Hunit := by
    unfold PlaneWaveGridG.ctailU PlaneWaveGridG.tBU
    positivity
  have : 0 ≤ 1 + V := by linarith
  have : 0 ≤ 1 + V' := by linarith
  have : (0 : ℝ) ≤ eta := Nat.cast_nonneg _
  simp only [gridPhiU, gLtailMU, flow2]
  gcongr

/-- The facts behind `gridConstsSharp_gLU_mono_V`: the `L`-free constants at `V ≤ V'`. -/
private lemma consts_facts (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    0 ≤ relBU sys V Hunit ∧ 0 ≤ relBU sys V' Hunit ∧ relBU sys V Hunit ≤ relBU sys V' Hunit ∧
    0 ≤ gridFlowConstU sys V ∧ 0 ≤ gridFlowConstU sys V' ∧
    gridFlowConstU sys V ≤ gridFlowConstU sys V' ∧
    0 ≤ gLzU sys V ∧ 0 ≤ gLzU sys V' ∧ gLzU sys V ≤ gLzU sys V' ∧
    0 ≤ sys.couplingWeight * ((1 + V) * PlaneWaveGridG.ctailU Hunit) ∧
    sys.couplingWeight * ((1 + V) * PlaneWaveGridG.ctailU Hunit) ≤
      sys.couplingWeight * ((1 + V') * PlaneWaveGridG.ctailU Hunit) := by
  have hV' := hV.trans hVV
  have hct : 0 ≤ PlaneWaveGridG.ctailU Hunit := by
    unfold PlaneWaveGridG.ctailU PlaneWaveGridG.tBU
    positivity
  have hcw := sys.couplingWeight_nonneg
  have : 0 ≤ 1 + V := by linarith
  refine ⟨relBU_nonneg sys hV hH, relBU_nonneg sys hV' hH, KineticLog.relBU_mono sys hV hVV hH,
    gridFlowConstU_nonneg sys hV, gridFlowConstU_nonneg sys hV',
    KineticLog.gridFlowConstU_mono sys hV hVV, gLzU_nonneg sys hV, gLzU_nonneg sys hV',
    KineticLog.gLzU_mono sys hVV, by positivity, by gcongr⟩

set_option maxHeartbeats 1000000 in
private lemma gridConstsSharp_gLU_mono_V1 (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit)
    {Cχ CO D2 D4 s0 hu hs hv : ℝ} (hCχ : 0 ≤ Cχ) (hCO : 0 ≤ CO) (h0 : 0 ≤ s0) (h1 : 0 ≤ hu)
    (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).1 ≤
      (gridConstsSharp_gLU sys V' Hunit Cχ CO D2 D4 s0 hu hs hv).1 := by
  obtain ⟨hb, hb', hbb, -, -, -, -, -, -, hk, hkk⟩ := consts_facts sys hV hVV hH
  have hM := sys.one_le_maxMass
  have hm0 : 0 ≤ sys.maxMass := by linarith
  have he : (0 : ℝ) ≤ eta := Nat.cast_nonneg _
  simp only [gridConstsSharp_gLU, gLtailMU]
  generalize relBU sys V Hunit = b at hb hbb ⊢
  generalize relBU sys V' Hunit = b' at hb' hbb ⊢
  generalize sys.couplingWeight * ((1 + V) * PlaneWaveGridG.ctailU Hunit) = k at hk hkk ⊢
  generalize sys.couplingWeight * ((1 + V') * PlaneWaveGridG.ctailU Hunit) = k' at hkk ⊢
  generalize sys.maxMass = mm at hm0 ⊢
  have : 0 ≤ k' := hk.trans hkk
  gcongr

set_option maxHeartbeats 1000000 in
private lemma gridConstsSharp_gLU_mono_V2 (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit)
    {Cχ CO D2 D4 s0 hu hs hv : ℝ} (hCχ : 0 ≤ Cχ) (hD2 : 0 ≤ D2) (hD4 : 0 ≤ D4) (h0 : 0 ≤ s0)
    (h1 : 0 ≤ hu) (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).2.1 ≤
      (gridConstsSharp_gLU sys V' Hunit Cχ CO D2 D4 s0 hu hs hv).2.1 := by
  obtain ⟨hb, hb', hbb, hcJ, hcJ', hcJJ, hz, hz', hzz, hk, hkk⟩ := consts_facts sys hV hVV hH
  have hV' := hV.trans hVV
  have hΦ := gridPhiU_nonneg sys (hs := hs) (hv := hv) hV hH hCχ hD2 hD4 h0 h1
  have hΦ' := gridPhiU_nonneg sys (hs := hs) (hv := hv) hV' hH hCχ hD2 hD4 h0 h1
  have hΦΦ := gridPhiU_mono_V sys hV hVV hH (D4 := D4) hCχ hD2 h0 h1 h2 h3
  have hM := sys.one_le_maxMass
  have hm0 : 0 ≤ sys.maxMass := by linarith
  have he : (0 : ℝ) ≤ eta := Nat.cast_nonneg _
  simp only [gridConstsSharp_gLU, gLtailMU]
  generalize relBU sys V Hunit = b at hb hbb ⊢
  generalize relBU sys V' Hunit = b' at hb' hbb ⊢
  generalize gridFlowConstU sys V = cJ at hcJ hcJJ ⊢
  generalize gridFlowConstU sys V' = cJ' at hcJ' hcJJ ⊢
  generalize gLzU sys V = z at hz hzz ⊢
  generalize gLzU sys V' = z' at hz' hzz ⊢
  generalize gridPhiU sys V Hunit Cχ D2 D4 s0 hu hs hv = Φ at hΦ hΦΦ ⊢
  generalize gridPhiU sys V' Hunit Cχ D2 D4 s0 hu hs hv = Φ' at hΦ' hΦΦ ⊢
  generalize sys.couplingWeight * ((1 + V) * PlaneWaveGridG.ctailU Hunit) = k at hk hkk ⊢
  generalize sys.couplingWeight * ((1 + V') * PlaneWaveGridG.ctailU Hunit) = k' at hkk ⊢
  generalize sys.maxMass = mm at hm0 ⊢
  have : 0 ≤ k' := hk.trans hkk
  gcongr

set_option maxHeartbeats 1000000 in
private lemma gridConstsSharp_gLU_mono_V3 (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit)
    {Cχ CO D2 D4 s0 hu hs hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) (h2 : 0 ≤ hs) :
    (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).2.2 ≤
      (gridConstsSharp_gLU sys V' Hunit Cχ CO D2 D4 s0 hu hs hv).2.2 := by
  obtain ⟨hb, hb', hbb, -, -, -, -, -, -, hk, hkk⟩ := consts_facts sys hV hVV hH
  have hM := sys.one_le_maxMass
  have hm0 : 0 ≤ sys.maxMass := by linarith
  have he : (0 : ℝ) ≤ eta := Nat.cast_nonneg _
  simp only [gridConstsSharp_gLU, gLtailMU]
  generalize relBU sys V Hunit = b at hb hbb ⊢
  generalize relBU sys V' Hunit = b' at hb' hbb ⊢
  generalize sys.couplingWeight * ((1 + V) * PlaneWaveGridG.ctailU Hunit) = k at hk hkk ⊢
  generalize sys.couplingWeight * ((1 + V') * PlaneWaveGridG.ctailU Hunit) = k' at hkk ⊢
  generalize sys.maxMass = mm at hm0 ⊢
  have : 0 ≤ k' := hk.trans hkk
  gcongr

/-- **The grid constants `(A₁, A₂, A₃)` are increasing in `V`** (componentwise, at fixed data). -/
lemma gridConstsSharp_gLU_mono_V (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit)
    {Cχ CO D2 D4 s0 hu hs hv : ℝ} (hCχ : 0 ≤ Cχ) (hCO : 0 ≤ CO) (hD2 : 0 ≤ D2) (hD4 : 0 ≤ D4)
    (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).1 ≤
        (gridConstsSharp_gLU sys V' Hunit Cχ CO D2 D4 s0 hu hs hv).1 ∧
      (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).2.1 ≤
        (gridConstsSharp_gLU sys V' Hunit Cχ CO D2 D4 s0 hu hs hv).2.1 ∧
      (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).2.2 ≤
        (gridConstsSharp_gLU sys V' Hunit Cχ CO D2 D4 s0 hu hs hv).2.2 :=
  ⟨gridConstsSharp_gLU_mono_V1 sys hV hVV hH hCχ hCO h0 h1 h2 h3,
    gridConstsSharp_gLU_mono_V2 sys hV hVV hH hCχ hD2 hD4 h0 h1 h2 h3,
    gridConstsSharp_gLU_mono_V3 sys hV hVV hH h0 h1 h2⟩

end Mono

/-! ## The constants of `prop:free-dyn` are increasing in `V` -/

section ConstMono

lemma dynConst_mono {A A' : ℝ × ℝ × ℝ} {N T c : ℝ} (m1 : A.1 ≤ A'.1) (m2 : A.2.1 ≤ A'.2.1)
    (m3 : A.2.2 ≤ A'.2.2) (hT : 0 ≤ T) : dynConst A N T c ≤ dynConst A' N T c := by
  unfold dynConst
  have e3 : A.2.2 * Real.sqrt 3 ^ 5 ≤ A'.2.2 * Real.sqrt 3 ^ 5 :=
    mul_le_mul_of_nonneg_right m3 (by positivity)
  have e4 : (A.2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * T ≤ (A'.2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * T :=
    mul_le_mul_of_nonneg_right (by linarith) hT
  have e5 := max_le_max (by linarith : A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * T ≤
    A'.1 + (A'.2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * T) (le_refl (0 : ℝ))
  have e6 := max_le_max m2 (le_refl (0 : ℝ))
  linarith

lemma spinScale_mono {A A' : ℝ × ℝ × ℝ} (N : ℝ) (m1 : A.1 ≤ A'.1) (m2 : A.2.1 ≤ A'.2.1)
    (m3 : A.2.2 ≤ A'.2.2) :
    (spinScale N A).1 ≤ (spinScale N A').1 ∧ (spinScale N A).2.1 ≤ (spinScale N A').2.1 ∧
      (spinScale N A).2.2 ≤ (spinScale N A').2.2 := by
  simp only [spinScale]
  exact ⟨mul_le_mul_of_nonneg_left m1 (sq_nonneg N), mul_le_mul_of_nonneg_left m2 (sq_nonneg N),
    mul_le_mul_of_nonneg_left m3 (sq_nonneg N)⟩

variable (sys : CoulombSystem eta ν) {V V' : ℝ}

/-- **The constant of `free_dyn_endpoint` is increasing in `V`.** -/
lemma freeDynConst_mono (hV : 0 ≤ V) (hVV : V ≤ V') (F : 𝓢(E3, ℂ)) (Dbar : ℝ) {𝒟 : ℝ}
    (h𝒟 : 0 ≤ 𝒟) : freeDynConst sys V F Dbar 𝒟 ≤ freeDynConst sys V' F Dbar 𝒟 := by
  unfold freeDynConst
  obtain ⟨hC6, hD2, hD4, hT⟩ := obs_consts_nonneg F
  obtain ⟨m1, m2, m3⟩ := gridConstsSharp_gLU_mono_V sys hV hVV hardyUnit_nonneg hC6 hC6 hD2 hD4
    h𝒟 h𝒟 h𝒟 h𝒟
  exact dynConst_mono m1 m2 m3 hT

/-- **The constant of `free_dyn_nbo_endpoint` is increasing in `V`.** -/
lemma freeDynConstNBO_mono (hV : 0 ≤ V) (hVV : V ≤ V') (F : 𝓢(E3, ℂ)) {Dbar Cbar D : ℝ}
    (hDb : 0 ≤ Dbar) (hCb : 0 ≤ Cbar) (hD : 0 ≤ D) :
    freeDynConstNBO sys V F Dbar Cbar D ≤ freeDynConstNBO sys V' F Dbar Cbar D := by
  unfold freeDynConstNBO
  obtain ⟨hC6, hD2, hD4, hT⟩ := obs_consts_nonneg F
  have hc₀ : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have hΛ := one_le_domConst sys.charge hc₀ hDb hCb
  have hR := one_le_regConst sys
  have hN : 0 ≤ regConst sys * D := by positivity
  have hΛ0 : 0 ≤ domConst sys.charge (zeroWeight sys / 4) Dbar Cbar := by linarith
  obtain ⟨m1, m2, m3⟩ := gridConstsSharp_gLU_mono_V sys hV hVV hardyUnit_nonneg hC6 hC6 hD2 hD4
    hN (mul_nonneg hΛ0 hN) (mul_nonneg hΛ0 hN) (mul_nonneg (pow_nonneg hΛ0 2) hN)
  exact dynConst_mono m1 m2 m3 hT

/-- **The constant of `free_dyn_grid_bo` is increasing in `V`.** -/
lemma freeDynConstBO_mono (hV : 0 ≤ V) (hVV : V ≤ V') (F : 𝓢(E3, ℂ)) {Dbar Cbar δ D : ℝ}
    (hD : 0 ≤ D) :
    freeDynConstBO sys V F Dbar Cbar δ D ≤ freeDynConstBO sys V' F Dbar Cbar δ D := by
  unfold freeDynConstBO
  have hR := one_le_regConstN sys
  have hN : 0 ≤ regConstN sys * D := by positivity
  exact freeDynConst_mono sys hV hVV F Dbar (mul_nonneg (sq_nonneg _) hN)

/-- **The spin constant without clamped nuclei is increasing in `V`.** -/
lemma freeDynConstSpinNBO_mono (hV : 0 ≤ V) (hVV : V ≤ V') (F : 𝓢(E3, ℂ)) {Dbar Cbar : ℝ}
    (hDb : 0 ≤ Dbar) (hCb : 0 ≤ Cbar) (D : ℝ) :
    freeDynConstSpinNBO sys V F Dbar Cbar D ≤ freeDynConstSpinNBO sys V' F Dbar Cbar D := by
  unfold freeDynConstSpinNBO
  obtain ⟨hC6, hD2, hD4, hT⟩ := obs_consts_nonneg F
  have hc₀ : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have hΛ := one_le_domConst sys.charge hc₀ hDb hCb
  have hΛ0 : 0 ≤ domConst sys.charge (zeroWeight sys / 4) Dbar Cbar := by linarith
  obtain ⟨m1, m2, m3⟩ := gridConstsSharp_gLU_mono_V sys hV hVV hardyUnit_nonneg hC6 hC6 hD2 hD4
    zero_le_one hΛ0 hΛ0 (pow_nonneg hΛ0 2)
  obtain ⟨s1, s2, s3⟩ := spinScale_mono (regConst sys * D) m1 m2 m3
  exact dynConst_mono s1 s2 s3 hT

/-- **The spin constant with clamped nuclei is increasing in `V`.** -/
lemma freeDynConstSpinBO_mono (hV : 0 ≤ V) (hVV : V ≤ V') (F : 𝓢(E3, ℂ)) {Dbar Cbar : ℝ}
    (hDb : 0 ≤ Dbar) (hCb : 0 ≤ Cbar) (δ D : ℝ) :
    freeDynConstSpinBO sys V F Dbar Cbar δ D ≤ freeDynConstSpinBO sys V' F Dbar Cbar δ D := by
  unfold freeDynConstSpinBO
  obtain ⟨hC6, hD2, hD4, hT⟩ := obs_consts_nonneg F
  have hc₀ : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have hΛ := one_le_domConstN sys.charge sys.nuclei.charge (δ := δ) hc₀ hDb hCb
  have hΛ0 : 0 ≤ domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) Dbar Cbar δ := by
    linarith
  obtain ⟨m1, m2, m3⟩ := gridConstsSharp_gLU_mono_V sys hV hVV hardyUnit_nonneg hC6 hC6 hD2 hD4
    zero_le_one hΛ0 hΛ0 (pow_nonneg hΛ0 2)
  obtain ⟨s1, s2, s3⟩ := spinScale_mono (regConstN sys * D) m1 m2 m3
  exact dynConst_mono s1 s2 s3 hT

end ConstMono

/-! ## The endpoints with a uniform bound on the profile variation -/

section Endpoints

/-- The form of the bound is increasing in the constant. -/
lemma vbar_form_le {C C' X t ε : ℝ} (hC : C ≤ C') (hX : 0 ≤ X) (ht : 0 ≤ t) (hε : 0 ≤ ε) :
    C * X + C * (1 + t) * ε ≤ C' * X + C' * (1 + t) * ε := by
  have h1 : 0 ≤ 1 + t := by linarith
  have := mul_le_mul_of_nonneg_right hC hX
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC h1) hε
  linarith

/-- **`prop:free-dyn` (any system, the domain condition (H_dom) assumed) for `V_θ ≤ V̄`**: the
statement of `free_dyn_endpoint` for every profile with total variation at most `V̄`, with the
constant `freeDynConst sys V̄ F D̄ 𝒟`. -/
theorem free_dyn_endpoint_vbar (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Dbar : ℝ} (hD1 : X.D1 ≤ Dbar) (hD2 : X.D2 ≤ Dbar)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0))
      h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁) {𝒟 : ℝ} (hψ0 : ‖ψ 0‖ ≤ 𝒟)
    (hn0 : ‖X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)‖ ≤ 𝒟) (hn1 : ‖h₀‖ ≤ 𝒟)
    (hn2 : ‖h₁‖ ≤ 𝒟)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
      let φ₀ := X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConst sys Vbar F Dbar 𝒟 * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConst sys Vbar F Dbar 𝒟 * (1 + t) * ε := by
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_endpoint sys hL2 hθ hR hR0
    hρ hone P hP hpos X hret hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hε1 hleak0
    hleak1 hdom0 hdom1 hψ0 hn0 hn1 hn2 a hf0 hf1 F hFf hfR hRL m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ φ₀ K ψg
  refine le_trans hbound ?_
  have hv0 := hθ.tv_nonneg
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hX : 0 ≤ (1 / K) ^ 5 + t * (1 / K) ^ 3 := by positivity
  exact vbar_form_le (freeDynConst_mono sys hv0 hVbar F Dbar ((norm_nonneg _).trans hψ0)) hX ht hε

/-- **`prop:free-dyn` (no clamped nuclei, the domain condition proved) for `V_θ ≤ V̄`**: the
statement of `free_dyn_nbo_endpoint` for every profile with total variation at most `V̄`, with the
constant `freeDynConstNBO sys V̄ F D̄ C̄ D`. -/
theorem free_dyn_nbo_endpoint_vbar [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ}
    {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Dbar Cbar : ℝ} (hDbar : X.D ≤ Dbar) (hCbar : X.C ≤ Cbar)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
      let φ₀ := X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConstNBO sys Vbar F Dbar Cbar D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstNBO sys Vbar F Dbar Cbar D * (1 + t) * ε := by
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_nbo_endpoint sys hL2 hθ hR
    hR0 hρ hone P hP hpos X hret hDbar hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hε1
    hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR hRL m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ φ₀ K ψg
  refine le_trans hbound ?_
  have hv0 := hθ.tv_nonneg
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hX : 0 ≤ (1 / K) ^ 5 + t * (1 / K) ^ 3 := by positivity
  exact vbar_form_le
      (freeDynConstNBO_mono sys hv0 hVbar F (X.D_nonneg.trans hDbar) (X.C_nonneg.trans hCbar)
      (le_trans (by positivity) hD)) hX ht hε

/-- **`prop:free-dyn` (clamped nuclei, a cutoff flat near them, the domain condition proved) for
`V_θ ≤ V̄`**: the statement of `free_dyn_grid_bo` for every profile with total variation at most
`V̄`, with the constant `freeDynConstBO sys V̄ F D̄ C̄ δ D`. -/
theorem free_dyn_grid_bo_vbar (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ)
    {Dbar Cbar : ℝ} (hDbar : X.D ≤ Dbar) (hCbar : X.C ≤ Cbar)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
      let φ₀ := X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConstBO sys Vbar F Dbar Cbar δ D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstBO sys Vbar F Dbar Cbar δ D * (1 + t) * ε := by
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_grid_bo sys hL2 hθ hR hR0
    hρ hone P hP hpos X hret hδ hflat hDbar hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε
    hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR hRL m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ φ₀ K ψg
  refine le_trans hbound ?_
  have hv0 := hθ.tv_nonneg
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hX : 0 ≤ (1 / K) ^ 5 + t * (1 / K) ^ 3 := by positivity
  exact vbar_form_le (freeDynConstBO_mono sys hv0 hVbar F (le_trans (by positivity) hD)) hX ht hε

/-- **`prop:free-dyn` (uniform in `L`, (H_dom) assumed) for `V_θ ≤ V̄`**: the statement of
`free_dyn_uniform` for every profile with total variation at most `V̄`, with the constant
`freeDynConst sys V̄ F D₈ 𝒟`. -/
theorem free_dyn_uniform_vbar (sys : CoulombSystem eta ν) {R0 ρ Rf Vbar : ℝ} (hR0 : 0 ≤ R0)
    (hρ : 0 ≤ ρ) (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0) {L R : ℝ} {θ : ℝ → ℝ}
    (hL : freeDynL0 R0 ρ Rf ≤ L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hVbar : tv R θ ≤ Vbar)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r}, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2}, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian (sysAt sys P L) L θ ((quadCutoffL sys.one_le_mass
      (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2 (pos_of_freeDynL0 hL) (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonian (sysAt sys P L) L θ h₀ h₁) {𝒟 : ℝ} (hψ0 : ‖ψ 0‖ ≤ 𝒟)
    (hn0 : ‖(quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
      (pos_of_freeDynL0 hL) (ψ 0)‖ ≤ 𝒟) (hn1 : ‖h₀‖ ≤ 𝒟) (hn2 : ‖h₁‖ ≤ 𝒟)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (pos_of_freeDynL0 hL) (continuous_of_schwartz F hFf) hfR
        (two_Rf_lt_of_freeDynL0 hL)
      let φ₀ := (quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
        (pos_of_freeDynL0 hL) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConst sys Vbar F (quadCutoff8 sys.one_le_mass).D 𝒟 *
            ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConst sys Vbar F (quadCutoff8 sys.one_le_mass).D 𝒟 * (1 + t) * ε := by
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_uniform sys hR0 hρ P hP hL
    hθ hR rfl hone hψd hHam hgrad ht hε hε1 hleak0 hleak1 hdom0 hdom1 hψ0 hn0 hn1 hn2 a hf0 hf1 F
    hFf hfR m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ φ₀ K ψg
  refine le_trans hbound ?_
  have hv0 := hθ.tv_nonneg
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hX : 0 ≤ (1 / K) ^ 5 + t * (1 / K) ^ 3 := by positivity
  exact vbar_form_le (freeDynConst_mono sys hv0 hVbar F _ ((norm_nonneg _).trans hψ0)) hX ht hε

/-- **`prop:free-dyn` (no clamped nuclei, uniform in `L`) for `V_θ ≤ V̄`**: the statement of
`free_dyn_nbo_uniform` for every profile with total variation at most `V̄`, with the constant
`freeDynConstNBO sys V̄ F D₈ C₈ D`. -/
theorem free_dyn_nbo_uniform_vbar [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ Rf Vbar : ℝ}
    (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) {L R : ℝ} {θ : ℝ → ℝ} (hL : freeDynL0 R0 ρ Rf ≤ L)
    (hθ : Profile R θ) (hR : R ≤ L / 2) (hVbar : tv R θ ≤ Vbar)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r}, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2}, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (pos_of_freeDynL0 hL) (continuous_of_schwartz F hFf) hfR
        (two_Rf_lt_of_freeDynL0 hL)
      let φ₀ := (quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
        (pos_of_freeDynL0 hL) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConstNBO sys Vbar F (quadCutoff8 sys.one_le_mass).D (quadCutoff8 sys.one_le_mass).C
            D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstNBO sys Vbar F (quadCutoff8 sys.one_le_mass).D (quadCutoff8 sys.one_le_mass).C
            D * (1 + t) * ε := by
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_nbo_uniform sys hR0 hρ hL
    hθ hR rfl hone P hP hpos hψd hHam hgrad ht hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR m
    hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ φ₀ K ψg
  refine le_trans hbound ?_
  have hv0 := hθ.tv_nonneg
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hX : 0 ≤ (1 / K) ^ 5 + t * (1 / K) ^ 3 := by positivity
  exact vbar_form_le (freeDynConstNBO_mono sys hv0 hVbar F (quadCutoff8 sys.one_le_mass).D_nonneg
      (quadCutoff8 sys.one_le_mass).C_nonneg (le_trans (by positivity) hD)) hX ht hε

/-- **`prop:free-dyn` (clamped nuclei, equal masses, uniform in `L`) for `V_θ ≤ V̄`**: the statement
of `free_dyn_bo_uniform` for every profile with total variation at most `V̄`, with the constant
`freeDynConstBO sys V̄ F D₁₆ C₁₆ δ D`. -/
theorem free_dyn_bo_uniform_vbar {R0 ρ Rf δ L : ℝ}
    (sys : CoulombSystem eta ν) {m₀ : ℝ} (hm : ∀ i, sys.mass i = m₀)
    (hm0 : 1 ≤ m₀) {Vbar : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0) {R : ℝ} {θ : ℝ → ℝ}
    (hL : freeDynBOL0 R0 ρ Rf δ ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hVbar : tv R θ ≤ Vbar)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in {r | ∃ i, L / 16 ≤ ‖particle r i‖}, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in {r | (∃ i, L / 16 ≤ ‖particle r i‖) ∧
      ∀ i, ‖particle r i‖ ≤ L / 8}, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm8 : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (pos_of_freeDynBOL0 hL) (continuous_of_schwartz F hFf) hfR
        (two_Rf_lt_of_freeDynBOL0 hL)
      let φ₀ := (prodCutoffL hm hm0 (sixteen_le_of_freeDynBOL0 hL)).toCutoff.chiW.cutL2
        (pos_of_freeDynBOL0 hL) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConstBO sys Vbar F (prodCutoff16 hm hm0).D (prodCutoff16 hm hm0).C δ D *
            ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstBO sys Vbar F (prodCutoff16 hm hm0).D (prodCutoff16 hm hm0).C δ D *
            (1 + t) * ε := by
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_bo_uniform sys hm hm0 hR0
    hρ hδ P hP hL hθ hR rfl hone hψd hHam hgrad ht hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR
    m hκ hm8 hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ φ₀ K ψg
  refine le_trans hbound ?_
  have hv0 := hθ.tv_nonneg
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hX : 0 ≤ (1 / K) ^ 5 + t * (1 / K) ^ 3 := by positivity
  exact vbar_form_le (freeDynConstBO_mono sys hv0 hVbar F (le_trans (by positivity) hD)) hX ht hε

/-- **`prop:free-dyn` (internal spin, no clamped nuclei) for `V_θ ≤ V̄`**: the statement of
`free_dyn_nbo_spin_endpoint` for every profile with total variation at most `V̄`, with the constant
`freeDynConstSpinNBO sys V̄ F D̄ C̄ D`. -/
theorem free_dyn_nbo_spin_endpoint_vbar [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ}
    {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0)
    (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Dbar Cbar : ℝ} (hDbar : X.D ≤ Dbar) (hCbar : X.C ≤ Cbar)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg : ς → EuclideanSpace ℂ (RCfg eta m) := fun σ => Ug t (idft (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (Ψ 0 σ)))))
      ‖((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
          ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ‖ ≤
        freeDynConstSpinNBO sys Vbar F Dbar Cbar D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstSpinNBO sys Vbar F Dbar Cbar D * (1 + t) * ε := by
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_nbo_spin_endpoint sys hL2
    hθ hR hR0 hρ hone P hP hpos X hret hDbar hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε
    hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR hRL m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ K ψg
  refine le_trans hbound ?_
  have hv0 := hθ.tv_nonneg
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hX : 0 ≤ (1 / K) ^ 5 + t * (1 / K) ^ 3 := by positivity
  exact vbar_form_le
      (freeDynConstSpinNBO_mono sys hv0 hVbar F (X.D_nonneg.trans hDbar)
      (X.C_nonneg.trans hCbar) D) hX ht hε

/-- **`prop:free-dyn` (internal spin, clamped nuclei) for `V_θ ≤ V̄`**: the statement of
`free_dyn_bo_spin_endpoint` for every profile with total variation at most `V̄`, with the constant
`freeDynConstSpinBO sys V̄ F D̄ C̄ δ D`. -/
theorem free_dyn_bo_spin_endpoint_vbar (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ)
    {Dbar Cbar : ℝ} (hDbar : X.D ≤ Dbar) (hCbar : X.C ≤ Cbar)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg : ς → EuclideanSpace ℂ (RCfg eta m) := fun σ => Ug t (idft (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (Ψ 0 σ)))))
      ‖((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
          ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ‖ ≤
        freeDynConstSpinBO sys Vbar F Dbar Cbar δ D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstSpinBO sys Vbar F Dbar Cbar δ D * (1 + t) * ε := by
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_bo_spin_endpoint sys hL2 hθ
    hR hR0 hρ hone P hP hpos X hret hδ hflat hDbar hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad
    ht hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR hRL m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ K ψg
  refine le_trans hbound ?_
  have hv0 := hθ.tv_nonneg
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hX : 0 ≤ (1 / K) ^ 5 + t * (1 / K) ^ 3 := by positivity
  exact vbar_form_le
      (freeDynConstSpinBO_mono sys hv0 hVbar F (X.D_nonneg.trans hDbar)
      (X.C_nonneg.trans hCbar) δ D) hX ht hε

/-- **`prop:free-dyn` (internal spin, no clamped nuclei, uniform in `L`) for `V_θ ≤ V̄`**: the
statement of `free_dyn_nbo_spin_uniform` for every profile with total variation at most `V̄`, with
the constant `freeDynConstSpinNBO sys V̄ F D₈ C₈ D`. -/
theorem free_dyn_nbo_spin_uniform_vbar [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ Rf Vbar : ℝ}
    (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) {L R : ℝ} {θ : ℝ → ℝ} (hL : freeDynL0 R0 ρ Rf ≤ L)
    (hθ : Profile R θ) (hR : R ≤ L / 2) (hVbar : tv R θ ≤ Vbar)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t,
      ∑ σ, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r}, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2}, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (pos_of_freeDynL0 hL) (continuous_of_schwartz F hFf) hfR
        (two_Rf_lt_of_freeDynL0 hL)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg : ς → EuclideanSpace ℂ (RCfg eta m) := fun σ => Ug t (idft (regCoeff m
        ((molecularPositionSynthesis eta).symm
          ((quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
            (pos_of_freeDynL0 hL) (Ψ 0 σ)))))
      ‖((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
          ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ‖ ≤
        freeDynConstSpinNBO sys Vbar F (quadCutoff8 sys.one_le_mass).D
            (quadCutoff8 sys.one_le_mass).C D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstSpinNBO sys Vbar F (quadCutoff8 sys.one_le_mass).D
            (quadCutoff8 sys.one_le_mass).C D * (1 + t) * ε := by
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_nbo_spin_uniform sys hR0 hρ
    hL hθ hR rfl hone P hP hpos hψd hHam hgrad ht hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR
    m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ K ψg
  refine le_trans hbound ?_
  have hv0 := hθ.tv_nonneg
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hX : 0 ≤ (1 / K) ^ 5 + t * (1 / K) ^ 3 := by positivity
  exact vbar_form_le
      (freeDynConstSpinNBO_mono sys hv0 hVbar F (quadCutoff8 sys.one_le_mass).D_nonneg
      (quadCutoff8 sys.one_le_mass).C_nonneg D) hX ht hε

/-- **`prop:free-dyn` (internal spin, clamped nuclei, equal masses, uniform in `L`) for `V_θ ≤
V̄`**: the statement of `free_dyn_bo_spin_uniform` for every profile with total variation at most
`V̄`, with the constant `freeDynConstSpinBO sys V̄ F D₁₆ C₁₆ δ D`. -/
theorem free_dyn_bo_spin_uniform_vbar (sys : CoulombSystem eta ν) {m₀ : ℝ}
    (hm : ∀ i, sys.mass i = m₀) (hm0 : 1 ≤ m₀) {R0 ρ Rf δ L Vbar : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hδ : 0 < δ) (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0) {R : ℝ} {θ : ℝ → ℝ}
    (hL : freeDynBOL0 R0 ρ Rf δ ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hVbar : tv R θ ≤ Vbar)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t,
      ∑ σ, ∫ r in {r | ∃ i, L / 16 ≤ ‖particle r i‖}, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in {r | (∃ i, L / 16 ≤ ‖particle r i‖) ∧
      ∀ i, ‖particle r i‖ ≤ L / 8}, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm8 : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (pos_of_freeDynBOL0 hL) (continuous_of_schwartz F hFf) hfR
        (two_Rf_lt_of_freeDynBOL0 hL)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg : ς → EuclideanSpace ℂ (RCfg eta m) := fun σ => Ug t (idft (regCoeff m
        ((molecularPositionSynthesis eta).symm
          ((prodCutoffL hm hm0 (sixteen_le_of_freeDynBOL0 hL)).toCutoff.chiW.cutL2
            (pos_of_freeDynBOL0 hL) (Ψ 0 σ)))))
      ‖((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
          ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ‖ ≤
        freeDynConstSpinBO sys Vbar F (prodCutoff16 hm hm0).D (prodCutoff16 hm hm0).C δ D *
            ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstSpinBO sys Vbar F (prodCutoff16 hm hm0).D (prodCutoff16 hm hm0).C δ D *
            (1 + t) * ε := by
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_bo_spin_uniform sys hm hm0
    hR0 hρ hδ P hP hL hθ hR rfl hone hψd hHam hgrad ht hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf
    hfR m hκ hm8 hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ K ψg
  refine le_trans hbound ?_
  have hv0 := hθ.tv_nonneg
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hX : 0 ≤ (1 / K) ^ 5 + t * (1 / K) ^ 3 := by positivity
  exact vbar_form_le (freeDynConstSpinBO_mono sys hv0 hVbar F (prodCutoff16 hm hm0).D_nonneg
      (prodCutoff16 hm hm0).C_nonneg δ D) hX ht hε

end Endpoints

end FreeBoundary
