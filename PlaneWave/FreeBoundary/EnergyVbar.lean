import PlaneWave.FreeBoundary.FreeEnergyEndpoint
import PlaneWave.KineticLog.OpenVbar

/-!
# `prop:free` for a uniform bound on the profile variation

`prop:free` and eq:free-energy assume only a uniform bound `V_θ ≤ V̄` on the total variation of
the range-truncation profiles. The endpoints of `PlaneWave.FreeBoundary.FreeEnergyEndpoint` take
`V_θ = V`: the size threshold `K₀ = gLKThresholdU sys V E_b` and the error constant
`C = gLErrorConstU sys V E_b` of the `L`-uniform grid theorem, and the energy budget
`freeUpperBudget sys V …` of the unconditional upper bound. Every one of these is built from the
`L`-free constants `gLzU`, `gLAU` and `gLmassConstU` (increasing in `V`, part 36 of
`PlaneWave.KineticLog`), the factor `1 + V` (in `gLformConstU` and `gLtailConstU`) and the budget
by sums, products, powers, roots and maxima with nonnegative coefficients, so it is increasing in
`V` and in the budget:

* `gLKThresholdU_mono`, `gLErrorConstU_mono`, `freeUpperBudget_mono`.

Hence the endpoints hold with thresholds and constants depending only on `V̄`:

* `gLSectorKernelGridErrorU_vbar` (every kernel of the class) and `gLSectorGridErrorU_vbar` (the
  sharp truncation): `thm:grid-energy` for `g_L`, uniform in `L`, for every profile with
  `V_θ ≤ V̄`;
* `gLTorusGroundEnergy_ge_vbar`: `E_L ≥ -(B² + 1/4)` with `B` at `V̄`;
* `free_grid_two_sidedU_vbar`, `free_grid_exponentialU_vbar`, `free_grid_two_sidedU_prod_vbar`,
  `free_grid_exponentialU_prod_vbar`: the bounds of `prop:free` from near-minimisers (radial and
  product geometry);
* **`free_energy_upper_vbar`**: the unconditional upper bound of `prop:free`;
* **`free_energy_endpoint_vbar`**: eq:free-energy;
* **`free_energy_complexity_vbar`**: the basis size `N = O(ε⁻¹ log³(1/ε))` for a family of
  profiles with `V_{θ_L} ≤ V̄`; `free_grid_complexity_prod_vbar`: the same in the product geometry,
  from near-minimisers (the form of `free_grid_complexity_prod`).

This covers every statement of `PlaneWave.FreeBoundary` on the ground energy that fixes
`V_θ = V`, and every one with `L`-uniform constants evaluated at the profile's own `V_θ`.

The grid kernel keeps the majorant of the actual profile, `(1 + V_θ) ŵ` (eq:rangecut); the
sharp truncation (`ĝ_L` for `0 < |ν|∞ ≤ 2m`, with the zero mode removed and `C₀` added to the
energies) does not depend on the majorant.
-/

set_option autoImplicit false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15
  molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The constants of the grid core are increasing -/

section Core

open PlaneWaveGridG

lemma EllU_mono' {A A' x x' : ℝ} (hA : A ≤ A') (hx : x ≤ x') : EllU A x ≤ EllU A' x' := by
  unfold EllU
  linarith

lemma CbootU_mono {z z' σ : ℝ} (hzz : z ≤ z') : CbootU z σ ≤ CbootU z' σ := by
  unfold CbootU
  exact mul_le_mul_of_nonneg_right hzz (by positivity)

lemma CformU_mono {z z' σ : ℝ} (hz : 0 ≤ z) (hzz : z ≤ z') : CformU z σ ≤ CformU z' σ := by
  unfold CformU
  have := CbootU_nonneg (σ := σ) hz
  have := CbootU_nonneg (σ := σ) (hz.trans hzz)
  have := CbootU_mono (σ := σ) hzz
  have : 0 ≤ z' := hz.trans hzz
  gcongr

lemma EbigU_nonneg {M z σ A Eb : ℝ} (hA : 0 ≤ A) : 0 ≤ EbigU M z σ A Eb := by
  unfold EbigU
  exact le_trans (by linarith) (le_max_left _ _)

lemma EbigU_mono {M z z' σ A A' Eb Eb' : ℝ} (hM : 0 ≤ M) (hz : 0 ≤ z) (hzz : z ≤ z')
    (hA : 0 ≤ A) (hAA : A ≤ A') (hE : 0 ≤ Eb) (hEE : Eb ≤ Eb') :
    EbigU M z σ A Eb ≤ EbigU M z' σ A' Eb' := by
  unfold EbigU
  have := CformU_nonneg (σ := σ) hz
  have := CformU_mono (σ := σ) hz hzz
  have := CformU_nonneg (σ := σ) (hz.trans hzz)
  have := EllU_nonneg hA hE
  have := EllU_mono' hAA hEE
  refine max_le_max (by linarith) ?_
  gcongr

lemma CgridU_mono {M z z' σ A A' Eb Eb' : ℝ} (hM : 0 ≤ M) (hz : 0 ≤ z) (hzz : z ≤ z')
    (hA : 0 ≤ A) (hAA : A ≤ A') (hE : 0 ≤ Eb) (hEE : Eb ≤ Eb') :
    CgridU M z σ A Eb ≤ CgridU M z' σ A' Eb' := by
  unfold CgridU
  have := CformU_nonneg (σ := σ) hz
  have := CformU_mono (σ := σ) hz hzz
  have := CformU_nonneg (σ := σ) (hz.trans hzz)
  have hb := EbigU_nonneg (M := M) (z := z) (σ := σ) (Eb := Eb) hA
  have := EllU_nonneg hA hb
  have := EllU_mono' hAA (EbigU_mono (σ := σ) hM hz hzz hA hAA hE hEE)
  gcongr

end Core

lemma uniformBOEigenH2Constant_mono {E0 E0' B B' : ℝ} (hE : E0 ≤ E0') (hB : 0 ≤ B)
    (hBB : B ≤ B') : uniformBOEigenH2Constant E0 B ≤ uniformBOEigenH2Constant E0' B' := by
  unfold uniformBOEigenH2Constant
  gcongr

/-! ## The `L`-free constants of the grid energy theorem are increasing -/

section Mono

variable (sys : CoulombSystem eta ν) {V V' Eb Eb' : ℝ}

lemma gLformConstU_mono (hVV : V ≤ V') {Hunit : ℝ} (hH : 0 ≤ Hunit) :
    PlaneWaveGridG.gLformConstU sys V Hunit ≤ PlaneWaveGridG.gLformConstU sys V' Hunit := by
  unfold PlaneWaveGridG.gLformConstU
  have := sys.couplingWeight_nonneg
  have := PlaneWaveGridG.tBU_nonneg hH
  gcongr

lemma gLformConstU_nonneg (hV : 0 ≤ V) {Hunit : ℝ} (hH : 0 ≤ Hunit) :
    0 ≤ PlaneWaveGridG.gLformConstU sys V Hunit := by
  unfold PlaneWaveGridG.gLformConstU
  have := sys.couplingWeight_nonneg
  have := PlaneWaveGridG.tBU_nonneg hH
  have : 0 ≤ 1 + V := by linarith
  positivity

lemma gLH2ConstU_nonneg' (hV : 0 ≤ V) {Hunit E0 : ℝ} (hH : 0 ≤ Hunit) (hE : 0 ≤ E0) :
    0 ≤ PlaneWaveGridG.gLH2ConstU sys V Hunit E0 := by
  unfold PlaneWaveGridG.gLH2ConstU
  have := gLmassConstU_nonneg sys hV hH
  exact mul_nonneg sys.maxMass_pos.le (uniformBOEigenH2Constant_nonneg hE)

lemma gLH2ConstU_mono' (hV : 0 ≤ V) (hVV : V ≤ V') {Hunit E0 E0' : ℝ} (hH : 0 ≤ Hunit)
    (hE : E0 ≤ E0') :
    PlaneWaveGridG.gLH2ConstU sys V Hunit E0 ≤ PlaneWaveGridG.gLH2ConstU sys V' Hunit E0' := by
  unfold PlaneWaveGridG.gLH2ConstU
  refine mul_le_mul_of_nonneg_left (uniformBOEigenH2Constant_mono hE
    (gLmassConstU_nonneg sys hV hH) (KineticLog.gLmassConstU_mono sys hVV hH))
    sys.maxMass_pos.le

lemma ctailU_nonneg {Hunit : ℝ} (hH : 0 ≤ Hunit) : 0 ≤ PlaneWaveGridG.ctailU Hunit := by
  unfold PlaneWaveGridG.ctailU
  have := PlaneWaveGridG.tBU_nonneg hH
  positivity

lemma gLtailConstU_nonneg' (hV : 0 ≤ V) {Hunit E0 : ℝ} (hH : 0 ≤ Hunit) (hE : 0 ≤ E0) :
    0 ≤ PlaneWaveGridG.gLtailConstU sys V Hunit E0 := by
  unfold PlaneWaveGridG.gLtailConstU
  have := sys.couplingWeight_nonneg
  have := ctailU_nonneg hH
  have := gLH2ConstU_nonneg' sys hV hH hE
  have : 0 ≤ 1 + V := by linarith
  positivity

lemma gLtailConstU_mono (hV : 0 ≤ V) (hVV : V ≤ V') {Hunit E0 E0' : ℝ} (hH : 0 ≤ Hunit)
    (hE : 0 ≤ E0) (hEE : E0 ≤ E0') :
    PlaneWaveGridG.gLtailConstU sys V Hunit E0 ≤ PlaneWaveGridG.gLtailConstU sys V' Hunit E0' := by
  unfold PlaneWaveGridG.gLtailConstU
  have := sys.couplingWeight_nonneg
  have := ctailU_nonneg hH
  have := gLH2ConstU_nonneg' sys hV hH hE
  have := gLH2ConstU_mono' sys hV hVV hH hEE
  have : 0 ≤ 1 + V := by linarith
  have : 0 ≤ 1 + V' := by linarith
  gcongr

lemma gLCubicConstU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hE : 0 ≤ Eb) (hEE : Eb ≤ Eb') :
    PlaneWaveGridG.gLCubicConstU sys V Eb ≤ PlaneWaveGridG.gLCubicConstU sys V' Eb' := by
  unfold PlaneWaveGridG.gLCubicConstU
  have hH := molecularCanonicalUnitHardyConstant_nonneg
  have := gLformConstU_nonneg sys hV hH
  have := gLformConstU_mono sys hVV hH
  have := gLformConstU_nonneg sys (hV.trans hVV) hH
  have : 0 ≤ Eb' := hE.trans hEE
  have := gLtailConstU_nonneg' sys hV hH hE
  have := gLtailConstU_mono sys hV hVV hH hE hEE
  have : 0 ≤ ∑ a, sys.mass a := Finset.sum_nonneg fun a _ => (sys.mass_pos a).le
  have : 0 ≤ ∑ a, sys.mass a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  gcongr

lemma gLKcubU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hE : 0 ≤ Eb) (hEE : Eb ≤ Eb') :
    PlaneWaveGridG.gLKcubU sys V Eb ≤ PlaneWaveGridG.gLKcubU sys V' Eb' := by
  unfold PlaneWaveGridG.gLKcubU
  have hH := molecularCanonicalUnitHardyConstant_nonneg
  have := gLtailConstU_nonneg' sys hV hH hE
  have := gLtailConstU_mono sys hV hVV hH hE hEE
  have := sys.maxMass_pos
  have : 0 ≤ ∑ a, sys.mass a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  gcongr

lemma gLEbigU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hE : 0 ≤ Eb) (hEE : Eb ≤ Eb') :
    PlaneWaveGridG.gLEbigU sys V Eb ≤ PlaneWaveGridG.gLEbigU sys V' Eb' :=
  EbigU_mono sys.maxMass_pos.le (PlaneWaveGridG.gLzU_nonneg sys hV)
    (KineticLog.gLzU_mono sys hVV) (KineticLog.gLAU_nonneg' sys hV)
    (KineticLog.gLAU_mono sys hV hVV) hE hEE

lemma gLCgridU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hE : 0 ≤ Eb) (hEE : Eb ≤ Eb') :
    PlaneWaveGridG.gLCgridU sys V Eb ≤ PlaneWaveGridG.gLCgridU sys V' Eb' :=
  CgridU_mono sys.maxMass_pos.le (PlaneWaveGridG.gLzU_nonneg sys hV)
    (KineticLog.gLzU_mono sys hVV) (KineticLog.gLAU_nonneg' sys hV)
    (KineticLog.gLAU_mono sys hV hVV) hE hEE

/-- **The size threshold of the `L`-uniform grid energy theorem is increasing** in the profile
variation and the energy budget. -/
lemma gLKThresholdU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hE : 0 ≤ Eb) (hEE : Eb ≤ Eb') :
    PlaneWaveGridG.gLKThresholdU sys V Eb ≤ PlaneWaveGridG.gLKThresholdU sys V' Eb' := by
  unfold PlaneWaveGridG.gLKThresholdU
  have hH := molecularCanonicalUnitHardyConstant_nonneg
  refine max_le_max ?_ (max_le_max ?_ ?_)
  · have := gLEbigU_mono sys hV hVV hE hEE
    have := sys.maxMass_pos
    gcongr
  · exact div_le_div_of_nonneg_right (gLKcubU_mono sys hV hVV hE hEE) (by norm_num)
  · refine div_le_div_of_nonneg_right (Real.rpow_le_rpow ?_ (gLCubicConstU_mono sys hV hVV hE hEE)
      (by norm_num)) (by norm_num)
    exact PlaneWaveGridG.gLCubicConstU_nonneg sys hV hE

/-- **The error constant of the `L`-uniform grid energy theorem is increasing** in the profile
variation and the energy budget. -/
lemma gLErrorConstU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hE : 0 ≤ Eb) (hEE : Eb ≤ Eb') :
    PlaneWaveGridG.gLErrorConstU sys V Eb ≤ PlaneWaveGridG.gLErrorConstU sys V' Eb' := by
  unfold PlaneWaveGridG.gLErrorConstU
  have := gLCgridU_mono sys hV hVV hE hEE
  have := gLCubicConstU_mono sys hV hVV hE hEE
  linarith

/-- The energy budget of the unconditional upper bound is increasing in `V`. -/
lemma freeUpperBudget_mono (hV : 0 ≤ V) (hVV : V ≤ V') (Einf C' : ℝ) :
    freeUpperBudget sys V Einf C' ≤ freeUpperBudget sys V' Einf C' := by
  unfold freeUpperBudget
  have hH := molecularCanonicalUnitHardyConstant_nonneg
  have := gLmassConstU_nonneg sys hV hH
  have := KineticLog.gLmassConstU_mono sys hVV hH
  have : PlaneWaveGridG.gLmassConstU sys V molecularCanonicalUnitHardyConstant ^ 2 + 1 / 4 ≤
      PlaneWaveGridG.gLmassConstU sys V' molecularCanonicalUnitHardyConstant ^ 2 + 1 / 4 := by
    gcongr
  have := max_le_max (le_refl (|Einf| + C' + zeroWeight sys / 4)) this
  linarith

lemma freeUpperBudget_nonneg (V Einf C' : ℝ) : 0 ≤ freeUpperBudget sys V Einf C' := by
  unfold freeUpperBudget
  have : 0 ≤ PlaneWaveGridG.gLmassConstU sys V molecularCanonicalUnitHardyConstant ^ 2 + 1 / 4 :=
    by positivity
  have := le_trans this (le_max_right (|Einf| + C' + zeroWeight sys / 4) _)
  linarith

lemma freeEnergyBudget_nonneg (Einf : ℝ) {C' : ℝ} (hC' : 0 ≤ C') :
    0 ≤ freeEnergyBudget sys Einf C' := by
  unfold freeEnergyBudget
  have := zeroWeight_nonneg sys
  positivity

end Mono

/-! ## `thm:grid-energy` for `g_L` with a uniform bound on the profile variation -/

/-- **`thm:grid-energy` for `g_L`, uniform in `L`, for `V_θ ≤ V̄`**: the statement of
`gLSectorKernelGridErrorU` with the threshold `K₀ = gLKThresholdU sys V̄ E_b` and the constant
`C = gLErrorConstU sys V̄ E_b`; the kernels are those of the class of the actual profile. -/
theorem gLSectorKernelGridErrorU_vbar (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R : ℝ} {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L)
    (hθ : Profile R θ) {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E ∧
      ∀ Eb : ℝ, |E| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys Vbar Eb ≤ (2 * Real.pi / L) * m →
        ∀ κ : PlaneWaveGrid.Lat3 → ℝ, PlaneWaveGridG.IsGridKernel
          (PlaneWaveGridG.gLgamma L (tv R θ)) (PlaneWaveGridG.gLref L θ (tv R θ)) m κ →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m κ Eg ∧
          |Eg - E| ≤ PlaneWaveGridG.gLErrorConstU sys Vbar Eb / ((2 * Real.pi / L) * m) ^ 3 := by
  obtain ⟨E, hE, hgrid⟩ := PlaneWaveGridG.gLSectorKernelGridErrorU sys lab hlab hL hθ
  refine ⟨E, hE, fun Eb hEb m hm hK κ hκ => ?_⟩
  have hv0 := hθ.tv_nonneg
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hE0 : 0 ≤ Eb := le_trans (by positivity) hEb
  obtain ⟨Eg, hEg, herr⟩ := hgrid Eb hEb m hm
    ((gLKThresholdU_mono sys hv0 hVbar hE0 le_rfl).trans hK) κ hκ
  refine ⟨Eg, hEg, herr.trans (div_le_div_of_nonneg_right ?_ (by positivity))⟩
  exact gLErrorConstU_mono sys hv0 hVbar hE0 le_rfl

/-- **`thm:grid-energy` for the truncated kernel `(g_L)_{≤2K}`, uniform in `L`, for
`V_θ ≤ V̄`.** -/
theorem gLSectorGridErrorU_vbar (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R : ℝ} {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L)
    (hθ : Profile R θ) {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E ∧
      ∀ Eb : ℝ, |E| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys Vbar Eb ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg - E| ≤ PlaneWaveGridG.gLErrorConstU sys Vbar Eb / ((2 * Real.pi / L) * m) ^ 3 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨E, hE, hgrid⟩ := gLSectorKernelGridErrorU_vbar sys lab hlab hL hθ hVbar
  exact ⟨E, hE, fun Eb hEb m hm hK => hgrid Eb hEb m hm hK _ (isGridKernel_sharp hL0 hθ m)⟩

/-! ## The single-profile bounds of `prop:free` -/

/-- The grid part of the energy bounds with the threshold and the constant at `V̄`. -/
lemma grid_energy_vbar (sys : CoulombSystem eta ν) {V Vbar : ℝ} (hV : 0 ≤ V) (hVV : V ≤ Vbar)
    {L : ℝ} (hL : 0 < L) {EL B : ℝ} {Q : ℕ → ℝ → Prop} {F : ℝ → ℝ}
    (h : ∀ Eb : ℝ, |EL| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
      PlaneWaveGridG.gLKThresholdU sys V Eb ≤ (2 * Real.pi / L) * m →
      ∃ Eg : ℝ, Q m Eg ∧
        F Eg ≤ B + PlaneWaveGridG.gLErrorConstU sys V Eb / ((2 * Real.pi / L) * (m : ℝ)) ^ 3) :
    ∀ Eb : ℝ, |EL| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
      PlaneWaveGridG.gLKThresholdU sys Vbar Eb ≤ (2 * Real.pi / L) * m →
      ∃ Eg : ℝ, Q m Eg ∧
        F Eg ≤ B +
          PlaneWaveGridG.gLErrorConstU sys Vbar Eb / ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  intro Eb hEb m hm hK
  have hE0 : 0 ≤ Eb := le_trans (by positivity) hEb
  obtain ⟨Eg, hQ, hF⟩ := h Eb hEb m hm ((gLKThresholdU_mono sys hV hVV hE0 le_rfl).trans hK)
  refine ⟨Eg, hQ, hF.trans ?_⟩
  have := gLErrorConstU_mono sys hV hVV hE0 le_rfl (Eb := Eb)
  have : 0 ≤ ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by positivity
  gcongr

/-- **The lower bound for the torus ground energy, for `V_θ ≤ V̄`**: `E_L ≥ -(B² + 1/4)` with
`B = gLmassConstU sys V̄ H_unit`, uniformly in `L ≥ 2π` and in the profiles with `V_θ ≤ V̄`. -/
theorem gLTorusGroundEnergy_ge_vbar (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} {L R : ℝ}
    {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L) (hθ : Profile R θ) {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar)
    {E : ℝ} (hE : IsGLTorusGroundEnergy sys lab L θ E) :
    -(PlaneWaveGridG.gLmassConstU sys Vbar molecularCanonicalUnitHardyConstant ^ 2 + 1 / 4) ≤
      E := by
  have h := gLTorusGroundEnergy_ge sys hL hθ hE
  have hH := molecularCanonicalUnitHardyConstant_nonneg
  have h0 := gLmassConstU_nonneg sys hθ.tv_nonneg hH
  have h1 := KineticLog.gLmassConstU_mono sys hVbar hH
  have : PlaneWaveGridG.gLmassConstU sys (tv R θ) molecularCanonicalUnitHardyConstant ^ 2 ≤
      PlaneWaveGridG.gLmassConstU sys Vbar molecularCanonicalUnitHardyConstant ^ 2 :=
    pow_le_pow_left₀ h0 h1 2
  linarith

/-- **`prop:free`, the two-sided bound from near-minimisers, for `V_θ ≤ V̄`**: the statement of
`free_grid_two_sidedU` with the threshold `gLKThresholdU sys V̄ E_b` and the constant `gLErrorConstU
sys V̄ E_b`. -/
theorem free_grid_two_sidedU_vbar (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L)
    (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar)
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
      ∀ Eb : ℝ, |EL| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys Vbar Eb ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) +
              PlaneWaveGridG.gLErrorConstU sys Vbar Eb /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨h1, h2⟩ := free_grid_two_sidedU sys lab hlab hL hθ hR hR0 hρ hone P hP hpos hw hwL hEL
    hτ hτA hlow happrox hA
  exact ⟨h1, grid_energy_vbar sys hθ.tv_nonneg hVbar hL0 h2⟩

/-- **`prop:free`, the exponential rate from near-minimisers, for `V_θ ≤ V̄`**: the statement of
`free_grid_exponentialU` with the threshold `gLKThresholdU sys V̄ E_b` and the constant
`gLErrorConstU sys V̄ E_b`. -/
theorem free_grid_exponentialU_vbar (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L)
    (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar)
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
      ∀ Eb : ℝ, |EL| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys Vbar Eb ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
              Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) +
              PlaneWaveGridG.gLErrorConstU sys Vbar Eb /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨h1, h2⟩ := free_grid_exponentialU sys lab hlab hL hθ hR hR0 hρ hone P hP hpos hw hwL hEL
    hα hβ hsmall hsmall' hlow happrox hA
  exact ⟨h1, grid_energy_vbar sys hθ.tv_nonneg hVbar hL0 h2⟩

/-- **`prop:free` in the product geometry, the two-sided bound, for `V_θ ≤ V̄`**: the statement of
`free_grid_two_sidedU_prod` with the threshold `gLKThresholdU sys V̄ E_b` and the constant
`gLErrorConstU sys V̄ E_b`. -/
theorem free_grid_two_sidedU_prod_vbar (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L)
    (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar)
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
      ∫ r in {r | ∀ i, ‖particle r i‖ < retainedRadius L R0 ρ - w}ᶜ, ‖φ r‖ ^ 2 ≤ τ)
    (hA : ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy sys L θ u hu ≤ EL + ε ∧
      ∫ x in {x | ∀ i, ‖particle (cellCoord L x) i‖ < retainedRadius L R0 ρ - w}ᶜ,
        ‖u x‖ ^ 2 ≤ τA) :
    |EL + (zeroModeShift sys L θ).re - Einf| ≤
        (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 *
          max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) ∧
      ∀ Eb : ℝ, |EL| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys Vbar Eb ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 *
                max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) +
              PlaneWaveGridG.gLErrorConstU sys Vbar Eb /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨h1, h2⟩ := free_grid_two_sidedU_prod sys lab hlab hL hθ hR hR0 hρ hone P hP hpos hw hwL
    hEL hτ hτA hlow happrox hA
  exact ⟨h1, grid_energy_vbar sys hθ.tv_nonneg hVbar hL0 h2⟩

/-- **`prop:free` in the product geometry, the exponential rate, for `V_θ ≤ V̄`**: the statement of
`free_grid_exponentialU_prod` with the threshold `gLKThresholdU sys V̄ E_b` and the constant
`gLErrorConstU sys V̄ E_b`. -/
theorem free_grid_exponentialU_prod_vbar (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L)
    (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {Vbar : ℝ} (hVbar : tv R θ ≤ Vbar)
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
      ∫ r in {r | ∀ i, ‖particle r i‖ < retainedRadius L R0 ρ - w}ᶜ, ‖φ r‖ ^ 2 ≤
        A * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))))
    (hA : ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy sys L θ u hu ≤ EL + ε ∧
      ∫ x in {x | ∀ i, ‖particle (cellCoord L x) i‖ < retainedRadius L R0 ρ - w}ᶜ,
        ‖u x‖ ^ 2 ≤ A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w)))) :
    |EL + (zeroModeShift sys L θ).re - Einf| ≤
        (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
          Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) ∧
      ∀ Eb : ℝ, |EL| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys Vbar Eb ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
              Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) +
              PlaneWaveGridG.gLErrorConstU sys Vbar Eb /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨h1, h2⟩ := free_grid_exponentialU_prod sys lab hlab hL hθ hR hR0 hρ hone P hP hpos hw
    hwL hEL hα hβ hsmall hsmall' hlow happrox hA
  exact ⟨h1, grid_energy_vbar sys hθ.tv_nonneg hVbar hL0 h2⟩

/-! ## The endpoints of `prop:free` -/

/-- **`prop:free`, the unconditional upper bound, for `V_θ ≤ V̄`**: the statement of
`free_energy_upper` for every profile with total variation at most `V̄`, with the threshold
`K₀ = gLKThresholdU sys V̄ E_b` and the constant `C = gLErrorConstU sys V̄ E_b` at the budget
`E_b = freeUpperBudget sys V̄ E_∞ C'`; `L₀` and `C'` do not depend on the profile. -/
theorem free_energy_upper_vbar (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {R0 ρ w : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hw : 0 < w)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    {ψ : FreeL2 eta} {Einf : ℝ} (hH : HasFreeHamiltonian sys P ψ ((Einf : ℂ) • ψ))
    (hn : ‖ψ‖ = 1)
    (hS : ∀ i j : Fin eta, i ≠ j → lab i = lab j → ∀ᵐ r, ψ (freeSwap i j r) = sys.sign i * ψ r)
    (hlow : ∀ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      IsFreeSector sys.sign lab φ → Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) →
      Einf * ∫ r, ‖φ r‖ ^ 2 ≤ freeEnergy sys P φ)
    {α A : ℝ} (hα : 0 < α)
    (hAi : ∀ i, Integrable fun r => Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2)
    (hA : ∑ i, ∫ r, Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2 ≤ A)
    {L R : ℝ} {θ : ℝ → ℝ} (hL : freeUpperL0 R0 ρ w α A ≤ L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) {Vbar : ℝ}
    (hVbar : tv R θ ≤ Vbar) :
    ∃ EL : ℝ, IsGLTorusGroundEnergy (sysAt sys P L) lab L θ EL ∧
      EL + (zeroModeShift (sysAt sys P L) L θ).re ≤
        Einf + freeUpperConst eta R0 ρ w α A * Real.exp (-(α / 2 * L)) ∧
      ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys Vbar
          (freeUpperBudget sys Vbar Einf (freeUpperConst eta R0 ρ w α A)) ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy (sysAt sys P L) lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          Eg + (zeroModeShift (sysAt sys P L) L θ).re ≤
            Einf + freeUpperConst eta R0 ρ w α A * Real.exp (-(α / 2 * L)) +
              PlaneWaveGridG.gLErrorConstU sys Vbar
                (freeUpperBudget sys Vbar Einf (freeUpperConst eta R0 ρ w α A)) /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  obtain ⟨EL, hEL, hup, hgrid⟩ := free_energy_upper sys lab hlab hR0 hρ hw P hP hH hn hS hlow hα
    hAi hA hL hθ hR hone rfl
  refine ⟨EL, hEL, hup, fun m hm hK => ?_⟩
  have hv0 := hθ.tv_nonneg
  set C' := freeUpperConst eta R0 ρ w α A with hC'
  have hb := freeUpperBudget_mono sys hv0 hVbar Einf C'
  have hb0 := freeUpperBudget_nonneg sys (tv R θ) Einf C'
  obtain ⟨Eg, hEg, herr⟩ := hgrid m hm ((gLKThresholdU_mono sys hv0 hVbar hb0 hb).trans hK)
  refine ⟨Eg, hEg, herr.trans ?_⟩
  have := gLErrorConstU_mono sys hv0 hVbar hb0 hb
  have hm0 : 0 ≤ ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
    have : 0 < L := lt_of_lt_of_le (by positivity) (le_trans (le_max_left _ _) hL)
    positivity
  gcongr

/-- **`prop:free`, eq:free-energy, for `V_θ ≤ V̄`**: the statement of `free_energy_endpoint` for
every profile with total variation at most `V̄`, with the threshold `K₀ = gLKThresholdU sys V̄ E_b`
and the constant `C = gLErrorConstU sys V̄ E_b` (`E_b = freeEnergyBudget sys E_∞ C'`). -/
theorem free_energy_endpoint_vbar (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {R0 ρ w : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hw : 0 < w)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    {ψ : FreeL2 eta} {Einf : ℝ} (hH : HasFreeHamiltonian sys P ψ ((Einf : ℂ) • ψ))
    (hn : ‖ψ‖ = 1)
    (hS : ∀ i j : Fin eta, i ≠ j → lab i = lab j → ∀ᵐ r, ψ (freeSwap i j r) = sys.sign i * ψ r)
    (hlow : ∀ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      IsFreeSector sys.sign lab φ → Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) →
      Einf * ∫ r, ‖φ r‖ ^ 2 ≤ freeEnergy sys P φ)
    {α A : ℝ} (hα : 0 < α)
    (hAi : ∀ i, Integrable fun r => Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2)
    (hA : ∑ i, ∫ r, Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2 ≤ A)
    {β A' : ℝ} (hβ : 0 < β)
    {L R : ℝ} {θ : ℝ → ℝ} (hL : freeEnergyL0 R0 ρ w α A β A' ≤ L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) {Vbar : ℝ}
    (hVbar : tv R θ ≤ Vbar)
    {EL : ℝ} (hEL : IsGLTorusGroundEnergy (sysAt sys P L) lab L θ EL)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam (sysAt sys P L) L θ) N u q)
    (u : MolecularFourierH2 eta)
    (huS : IsSectorCoeff sys.sign lab (molecularH2Coeff (2 * Real.pi / L) u))
    (hun : ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ = 1)
    (hu : H u = (EL : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) u)
    (hA' : ∑ i, ∫ x, Real.exp (2 * β * (‖particle (cellCoord L x) i‖ -
        retainedRadius (L / 2) R0 ρ)) *
      ‖molecularPositionH2StateMap eta (2 * Real.pi / L) u x‖ ^ 2 ≤ A') :
    |EL + (zeroModeShift (sysAt sys P L) L θ).re - Einf| ≤
        freeEnergyConst eta R0 ρ w α A β A' * Real.exp (-(freeEnergyRate α β * L)) ∧
      ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys Vbar
          (freeEnergyBudget sys Einf (freeEnergyConst eta R0 ρ w α A β A')) ≤
            (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy (sysAt sys P L) lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift (sysAt sys P L) L θ).re - Einf| ≤
            freeEnergyConst eta R0 ρ w α A β A' * Real.exp (-(freeEnergyRate α β * L)) +
              PlaneWaveGridG.gLErrorConstU sys Vbar
                (freeEnergyBudget sys Einf (freeEnergyConst eta R0 ρ w α A β A')) /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  obtain ⟨h1, hgrid⟩ := free_energy_endpoint sys lab hlab hR0 hρ hw P hP hH hn hS hlow hα hAi hA
    hβ hL hθ hR hone rfl hEL H hKernel u huS hun hu hA'
  refine ⟨h1, fun m hm hK => ?_⟩
  have hv0 := hθ.tv_nonneg
  have hb0 := freeEnergyBudget_nonneg sys Einf (freeEnergyConst_nonneg eta R0 ρ w α A β A')
  obtain ⟨Eg, hEg, herr⟩ := hgrid m hm ((gLKThresholdU_mono sys hv0 hVbar hb0 le_rfl).trans hK)
  refine ⟨Eg, hEg, herr.trans ?_⟩
  have := gLErrorConstU_mono sys hv0 hVbar hb0 le_rfl
    (Eb := freeEnergyBudget sys Einf (freeEnergyConst eta R0 ρ w α A β A'))
  have hm0 : 0 ≤ ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
    have h2 : 2 * Real.pi ≤ L :=
      le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hL)
    have : 0 < L := lt_of_lt_of_le (by positivity) h2
    positivity
  gcongr

/-- **`prop:free`, the complexity statement, for `V_θ ≤ V̄`** (`N = O(ε⁻¹ log³(1/ε))`): the
statement of `free_energy_complexity` for a family of profiles `θ_L` whose total variations are
bounded by `V̄`, not necessarily equal. -/
theorem free_energy_complexity_vbar (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {R0 ρ w : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hw : 0 < w)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    {ψ : FreeL2 eta} {Einf : ℝ} (hH : HasFreeHamiltonian sys P ψ ((Einf : ℂ) • ψ))
    (hn : ‖ψ‖ = 1)
    (hS : ∀ i j : Fin eta, i ≠ j → lab i = lab j → ∀ᵐ r, ψ (freeSwap i j r) = sys.sign i * ψ r)
    (hlow : ∀ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      IsFreeSector sys.sign lab φ → Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) →
      Einf * ∫ r, ‖φ r‖ ^ 2 ≤ freeEnergy sys P φ)
    {α A : ℝ} (hα : 0 < α)
    (hAi : ∀ i, Integrable fun r => Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2)
    (hA : ∑ i, ∫ r, Real.exp (2 * α * ‖particle r i‖) * ‖ψ r‖ ^ 2 ≤ A)
    {β A' : ℝ} (hβ : 0 < β)
    {R : ℝ → ℝ} {θ : ℝ → ℝ → ℝ} {Vbar L₀ : ℝ} (hL₀ : freeEnergyL0 R0 ρ w α A β A' ≤ L₀)
    (hfam : ∀ L, L₀ ≤ L → Profile (R L) (θ L) ∧ R L ≤ L / 2 ∧
      (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ L r = 1) ∧ tv (R L) (θ L) ≤ Vbar)
    (hgs : ∀ L, L₀ ≤ L → ∀ EL, IsGLTorusGroundEnergy (sysAt sys P L) lab L (θ L) EL →
      ∃ (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
        (u : MolecularFourierH2 eta),
        (∀ N u q, H (molecularH2Truncate N u) q = fourierCubeKernelAction (2 * Real.pi / L)
          (gLlatHam (sysAt sys P L) L (θ L)) N u q) ∧
        IsSectorCoeff sys.sign lab (molecularH2Coeff (2 * Real.pi / L) u) ∧
        ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ = 1 ∧
        H u = (EL : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) u ∧
        ∑ i, ∫ x, Real.exp (2 * β * (‖particle (cellCoord L x) i‖ -
            retainedRadius (L / 2) R0 ρ)) *
          ‖molecularPositionH2StateMap eta (2 * Real.pi / L) u x‖ ^ 2 ≤ A') :
    ∃ D : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ L, L₀ ≤ L ∧ ∃ m : ℕ,
      ((4 * m + 1 : ℕ) : ℝ) ^ 3 ≤ D / ε * Real.log (1 / ε) ^ 3 ∧
      ∃ Eg, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy (sysAt sys P L) lab L m
          (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv (R L) (θ L)))
            (PlaneWaveGridG.gLref L (θ L) (tv (R L) (θ L))) m) Eg ∧
        |Eg + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf| ≤ ε := by
  have hL2 : 2 * Real.pi ≤ L₀ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hL₀)
  have hL₀0 : 0 ≤ L₀ := le_trans (by positivity) hL2
  have hγ : 0 < freeEnergyRate α β := by
    unfold freeEnergyRate
    have := lt_min hα (half_pos hβ)
    positivity
  set C' := freeEnergyConst eta R0 ρ w α A β A' with hC'
  set Eb := freeEnergyBudget sys Einf C' with hEb
  refine complexity_of_rate (Q := fun L m Eg =>
      PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy (sysAt sys P L) lab L m
        (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv (R L) (θ L)))
          (PlaneWaveGridG.gLref L (θ L) (tv (R L) (θ L))) m) Eg)
    (C0 := fun L => (zeroModeShift (sysAt sys P L) L (θ L)).re)
    (Cg := PlaneWaveGridG.gLErrorConstU sys Vbar Eb)
    (K₀ := PlaneWaveGridG.gLKThresholdU sys Vbar Eb) (m₀ := eta + 8) hL₀0 hγ
    (freeEnergyConst_nonneg eta R0 ρ w α A β A') ?_
  intro L hLL₀ hLpos m hm hK
  obtain ⟨hθ, hRL, hone, hv⟩ := hfam L hLL₀
  obtain ⟨EL, hEL⟩ := exists_gLTorusGroundEnergy (sysAt sys P L) hlab hLpos hθ
    molecularCanonicalUnitHardyConstant canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨H, u, hKernel, huS, hun, hu, hA'⟩ := hgs L hLL₀ EL hEL
  obtain ⟨-, h2⟩ := free_energy_endpoint_vbar sys lab hlab hR0 hρ hw P hP hH hn hS hlow hα hAi hA
    hβ (le_trans hL₀ hLL₀) hθ hRL hone hv hEL H hKernel u huS hun hu hA'
  exact h2 m hm hK

/-- **`prop:free`, the complexity statement in the product geometry, for `V_θ ≤ V̄`**: the
statement of `free_grid_complexity_prod` for a family of profiles `θ_L` whose total variations are
bounded by `V̄`, not necessarily equal. -/
theorem free_grid_complexity_prod_vbar (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {R0 ρ w : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hw : 0 < w)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    {R : ℝ → ℝ} {θ : ℝ → ℝ → ℝ} {Vbar L₀ : ℝ} (hL₀ : 2 * Real.pi ≤ L₀)
    (hwL₀ : w < retainedRadius L₀ R0 ρ)
    (hfam : ∀ L, L₀ ≤ L → Profile (R L) (θ L) ∧ R L ≤ L / 2 ∧
      (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ L r = 1) ∧ tv (R L) (θ L) ≤ Vbar)
    {Einf A α A' β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hA0 : 0 ≤ A) (hA'0 : 0 ≤ A')
    (hsmall : A * Real.exp (-(2 * α * (retainedRadius L₀ R0 ρ - w))) ≤ 1 / 2)
    (hsmall' : A' * Real.exp (-(2 * β * (retainedRadius L₀ R0 ρ - w))) ≤ 1 / 2)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (hagmon : ∀ d > 0, ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | ∀ i, ‖particle r i‖ < d}ᶜ, ‖φ r‖ ^ 2 ≤ A * Real.exp (-(2 * α * d)))
    (hA : ∀ L, L₀ ≤ L → ∀ EL, IsGLTorusGroundEnergy (sysAt sys P L) lab L (θ L) EL →
      ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy (sysAt sys P L) L (θ L) u hu ≤ EL + ε ∧
      ∫ x in {x | ∀ i, ‖particle (cellCoord L x) i‖ < retainedRadius L R0 ρ - w}ᶜ,
        ‖u x‖ ^ 2 ≤ A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w)))) :
    ∃ D : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ L, L₀ ≤ L ∧ ∃ m : ℕ,
      ((4 * m + 1 : ℕ) : ℝ) ^ 3 ≤ D / ε * Real.log (1 / ε) ^ 3 ∧
      ∃ Eg, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy (sysAt sys P L) lab L m
          (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv (R L) (θ L)))
            (PlaneWaveGridG.gLref L (θ L) (tv (R L) (θ L))) m) Eg ∧
        |Eg + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf| ≤ ε := by
  set C' := (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
    Real.exp (2 * max α β * (R0 + ρ + w)) with hC'
  have hC'0 : 0 ≤ C' := by
    have : 0 ≤ max A A' := le_trans hA0 (le_max_left _ _)
    positivity
  set γ := min α β / 2 with hγ
  have hγ0 : 0 < γ := by have := lt_min hα hβ; positivity
  set Eb := |Einf| + C' + zeroWeight sys / 4 + 1 with hEb
  have hEb0 : 0 ≤ Eb := by have := zeroWeight_nonneg sys; positivity
  have hL₀0 : 0 ≤ L₀ := le_trans (by positivity) hL₀
  refine complexity_of_rate (Q := fun L m Eg =>
      PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy (sysAt sys P L) lab L m
        (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv (R L) (θ L)))
          (PlaneWaveGridG.gLref L (θ L) (tv (R L) (θ L))) m) Eg)
    (C0 := fun L => (zeroModeShift (sysAt sys P L) L (θ L)).re)
    (Cg := PlaneWaveGridG.gLErrorConstU sys Vbar Eb)
    (K₀ := PlaneWaveGridG.gLKThresholdU sys Vbar Eb) (m₀ := eta + 8) hL₀0 hγ0 hC'0 ?_
  intro L hLL₀ hLpos m hm hK
  obtain ⟨hθ, hRL, hone, htv⟩ := hfam L hLL₀
  have hv0 := hθ.tv_nonneg
  have hL2π : 2 * Real.pi ≤ L := le_trans hL₀ hLL₀
  have hmono : retainedRadius L₀ R0 ρ ≤ retainedRadius L R0 ρ := by
    unfold retainedRadius
    linarith
  have hwL : w < retainedRadius L R0 ρ := lt_of_lt_of_le hwL₀ hmono
  have hd0 : 0 < retainedRadius L R0 ρ - w := by linarith
  have hsm : A * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))) ≤ 1 / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA0) hsmall
    nlinarith
  have hsm' : A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w))) ≤ 1 / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA'0) hsmall'
    nlinarith
  obtain ⟨EL, hEL⟩ := exists_gLTorusGroundEnergy (sysAt sys P L) hlab hLpos hθ
    molecularCanonicalUnitHardyConstant canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨h1, h2⟩ := free_grid_exponentialU_prod (sysAt sys P L) lab hlab hL2π hθ hRL hR0 hρ hone
    P hP (fun l => rfl) hw hwL hEL hα.le hβ.le hsm hsm' hlow
    (hagmon (retainedRadius L R0 ρ - w) hd0) (hA L hLL₀ EL hEL)
  -- the energy budget
  have hexp1 : Real.exp (-(min α β * L / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := lt_min hα hβ
    have : 0 ≤ min α β * L := by positivity
    linarith
  have hEL1 : |EL + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf| ≤ C' := by
    refine h1.trans ?_
    have : C' * Real.exp (-(min α β * L / 2)) ≤ C' * 1 := mul_le_mul_of_nonneg_left hexp1 hC'0
    rw [mul_one] at this
    exact this
  have hz := abs_zeroModeShift_re_le (sysAt sys P L) hLpos hθ hRL
  have hz' : zeroWeight (sysAt sys P L) * (Real.pi / (2 * L)) ≤ zeroWeight sys / 4 := by
    have hq : zeroWeight (sysAt sys P L) = zeroWeight sys := rfl
    rw [hq]
    have hpi : Real.pi / (2 * L) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have := mul_le_mul_of_nonneg_left hpi (zeroWeight_nonneg sys)
    linarith
  have hEb' : |EL| + 1 ≤ Eb := by
    have habs : |EL| ≤ |EL + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf| +
        |(zeroModeShift (sysAt sys P L) L (θ L)).re| + |Einf| := by
      have := abs_add_le (EL + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf)
        (Einf - (zeroModeShift (sysAt sys P L) L (θ L)).re)
      rw [show EL + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf +
          (Einf - (zeroModeShift (sysAt sys P L) L (θ L)).re) = EL by ring] at this
      have h3 := abs_sub Einf (zeroModeShift (sysAt sys P L) L (θ L)).re
      linarith
    rw [hEb]
    linarith
  obtain ⟨Eg, hEg, herr⟩ := h2 Eb hEb' m hm
    ((gLKThresholdU_mono sys hv0 htv hEb0 le_rfl).trans hK)
  refine ⟨Eg, hEg, herr.trans ?_⟩
  have e : Real.exp (-(min α β * L / 2)) = Real.exp (-(γ * L)) := by
    rw [hγ]
    ring_nf
  rw [e]
  have hC : PlaneWaveGridG.gLErrorConstU (sysAt sys P L) (tv (R L) (θ L)) Eb ≤
      PlaneWaveGridG.gLErrorConstU sys Vbar Eb := gLErrorConstU_mono sys hv0 htv hEb0 le_rfl
  have hK3 : 0 ≤ ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by positivity
  gcongr

end

end FreeBoundary
