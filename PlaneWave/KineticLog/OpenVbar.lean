import PlaneWave.KineticLog.OpenFixed
import PlaneWave.KineticLog.OpenSpinCompat

/-!
# Logarithmic kinetic bound, part 36: a uniform bound on the profile variation

The isolated-system endpoints of parts 26–33 take the profile variation `V_θ = tv R θ` as a
parameter: the constants are `C = freeKinC sys V_θ D̄` and `K₀ = cellK0 sys V_θ`, and the
existential forms fix `V_θ = V` for every cell. `prop:free-kinetic-log` only assumes a uniform
bound `V_θ ≤ V̄`. Every constant of the chain is built from the `L`-free constants
`gLzU`, `gLAU`, `gLmassConstU`, `gLtailMU`, `relBU` and `gridFlowConstU` by sums, products,
powers and square roots with nonnegative coefficients, and each of these is increasing in `V`.
Hence (`freeKinC_mono`, `cellK0_mono`, `freeKinConstNBO_mono`, `freeKinConstBO_mono`)

* `C(V_θ) ≤ C(V̄)` and `K₀(V_θ) ≤ K₀(V̄)` whenever `0 ≤ V_θ ≤ V̄`,

and the endpoints hold with constants and cutoff thresholds depending only on `V̄`:

* `free_kinetic_log_vbar`, `free_kinetic_log_at_vbar`, `free_kinetic_log_spin_at_vbar`,
  `free_stopping_log_at_vbar`, `free_stopping_log_spin_at_vbar`: the existential forms of
  `prop:free-kinetic-log` and `cor:free-stopping-log` (scalar and spin; general position and the
  fixed molecule of part 33) for every profile with `V_θ ≤ V̄`;
* `free_kinetic_log_nbo_uniform_vbar`, `free_kinetic_log_bo_uniform_vbar` and their spin forms:
  the explicit cutoffs of parts 28 and 31, uniform in `L`;
* `free_kinetic_log_nbo_vbar`, `free_kinetic_log_bo_vbar` and their spin forms: the compatible
  cutoffs of parts 27 and 31;
* `free_kinetic_log_endpoint_vbar`, `free_stopping_log_vbar`, `free_kinetic_log_N_vbar`,
  `free_kinetic_log_spin_vbar`, `free_stopping_log_spin_vbar`: the explicit forms.

The kernel class keeps the majorant `4π (1 + V_θ)/(L³|k|²)` of the actual profile, as in
eq:free-kinetic-kernel (from eq:rangecut).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter MeasureTheory Set PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid
  PlaneWaveGridDynamics PlaneWaveKinetic FSNormal FreeBoundary

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The `L`-free base constants are increasing in `V` -/

section Base

variable (sys : CoulombSystem eta ν) {V V' Hunit : ℝ}

omit [Fintype ν] in
lemma coupling_mono_gamma {D : PlaneWaveGridG.NucData ν} {γ γ' : ℝ} (hγ : γ ≤ γ')
    (t : PlaneWaveGridG.Term eta ν) :
    PlaneWaveGridG.coupling eta D γ t ≤ PlaneWaveGridG.coupling eta D γ' t := by
  cases t with
  | inl pr => exact hγ
  | inr il => exact mul_le_mul_of_nonneg_left hγ (D.charge_nonneg il.2)

lemma Zc_mono_gamma {P : PlaneWaveGridG.RegParticles eta} {D : PlaneWaveGridG.NucData ν}
    {γ γ' : ℝ} (hγ : γ ≤ γ') : PlaneWaveGridG.Zc P D γ ≤ PlaneWaveGridG.Zc P D γ' := by
  unfold PlaneWaveGridG.Zc
  exact Finset.sum_le_sum fun t _ =>
    mul_le_mul_of_nonneg_left (coupling_mono_gamma hγ t) (abs_nonneg _)

lemma gLzU_mono (hVV : V ≤ V') : PlaneWaveGridG.gLzU sys V ≤ PlaneWaveGridG.gLzU sys V' := by
  unfold PlaneWaveGridG.gLzU
  refine mul_le_mul_of_nonneg_left (Zc_mono_gamma ?_) sys.maxMass_pos.le
  have : 0 < 2 * Real.pi ^ 2 := by positivity
  exact div_le_div_of_nonneg_right (by linarith) this.le

lemma gLAU_nonneg' (hV : 0 ≤ V) : 0 ≤ PlaneWaveGridG.gLAU sys V := by
  unfold PlaneWaveGridG.gLAU
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  positivity

lemma gLAU_mono (hV : 0 ≤ V) (hVV : V ≤ V') :
    PlaneWaveGridG.gLAU sys V ≤ PlaneWaveGridG.gLAU sys V' := by
  unfold PlaneWaveGridG.gLAU
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  have := gLzU_mono sys hVV
  gcongr

lemma gLmassConstU_mono (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    PlaneWaveGridG.gLmassConstU sys V Hunit ≤ PlaneWaveGridG.gLmassConstU sys V' Hunit := by
  unfold PlaneWaveGridG.gLmassConstU
  have := sys.massCouplingWeight_nonneg
  have := PlaneWaveGridG.tBU_nonneg hH
  gcongr

lemma gLtailMU_mono (hVV : V ≤ V') (hH : 0 ≤ Hunit) {M : ℝ} (hM : 0 ≤ M) :
    gLtailMU sys V Hunit M ≤ gLtailMU sys V' Hunit M := by
  unfold gLtailMU
  have := sys.couplingWeight_nonneg
  have : 0 ≤ PlaneWaveGridG.ctailU Hunit := by
    unfold PlaneWaveGridG.ctailU PlaneWaveGridG.tBU
    positivity
  gcongr

lemma relBU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    relBU sys V Hunit ≤ relBU sys V' Hunit := by
  unfold relBU
  have := gLmassConstU_nonneg sys hV hH
  have := gLmassConstU_nonneg sys (hV.trans hVV) hH
  have := gLmassConstU_mono sys hVV hH
  gcongr

lemma gridFlowConstU_mono (hV : 0 ≤ V) (hVV : V ≤ V') :
    gridFlowConstU sys V ≤ gridFlowConstU sys V' := by
  unfold gridFlowConstU
  have := gLAU_mono sys hV hVV
  gcongr

end Base

/-! ## The derived constants are increasing in `V` -/

section Derived

variable (sys : CoulombSystem eta ν) {V V' Hunit : ℝ}

lemma cU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    cU sys V Hunit ≤ cU sys V' Hunit := by
  unfold cU
  have := gLmassConstU_nonneg sys hV hH
  have := gLmassConstU_mono sys hVV hH
  gcongr

lemma cGrU_mono (hV : 0 ≤ V) (hVV : V ≤ V') : cGrU sys V ≤ cGrU sys V' := by
  unfold cGrU
  have := gLAU_mono sys hV hVV
  gcongr

lemma cWvU_mono (hV : 0 ≤ V) (hVV : V ≤ V') {c c' : ℝ} (hcc : c ≤ c') :
    cWvU sys V c ≤ cWvU sys V' c' := by
  unfold cWvU
  have := gLAU_mono sys hV hVV
  gcongr

lemma cGtU_mono (hV : 0 ≤ V) (hVV : V ≤ V') {c c' : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') :
    cGtU sys V c ≤ cGtU sys V' c' := by
  unfold cGtU
  have hV' := hV.trans hVV
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  have := PlaneWaveGridG.gLzU_nonneg sys hV'
  have := gLzU_mono sys hVV
  have := cWvU_nonneg sys hV hc
  have := cWvU_mono sys hV hVV hcc
  have := sys.maxMass_pos
  gcongr

lemma cWtU_mono (hVV : V ≤ V') (hH : 0 ≤ Hunit) : cWtU sys V Hunit ≤ cWtU sys V' Hunit := by
  unfold cWtU
  have := gLtailMU_mono sys hVV hH zero_le_one
  have := sys.maxMass_pos
  gcongr

lemma cZU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    cZU sys V Hunit ≤ cZU sys V' Hunit := by
  unfold cZU
  have := cU_mono sys hV hVV hH
  have := relBU_mono sys hV hVV hH
  gcongr

lemma cAbsU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    cAbsU sys V Hunit ≤ cAbsU sys V' Hunit := by
  unfold cAbsU
  have hV' := hV.trans hVV
  have := cWtU_nonneg (sys := sys) hV hH
  have := cWtU_nonneg (sys := sys) hV' hH
  have := cZU_nonneg (sys := sys) hV hH
  have := cWtU_mono sys hVV hH
  have := cZU_mono sys hV hVV hH
  have := sys.maxMass_pos
  gcongr

lemma xvU_mono (hV : 0 ≤ V) (hVV : V ≤ V') {c c' : ℝ} (hcc : c ≤ c') :
    xvU sys V c ≤ xvU sys V' c' := by
  unfold xvU
  have := cWvU_mono sys hV hVV hcc
  have := sys.maxMass_pos
  gcongr

lemma xuU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    xuU sys V Hunit ≤ xuU sys V' Hunit := by
  unfold xuU
  have := cZU_mono sys hV hVV hH
  have := sys.maxMass_pos
  gcongr

lemma dU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) {c c' : ℝ} (hc : 0 ≤ c)
    (hcc : c ≤ c') : dU sys V Hunit c ≤ dU sys V' Hunit c' := by
  unfold dU
  have hV' := hV.trans hVV
  have hc' := hc.trans hcc
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  have := PlaneWaveGridG.gLzU_nonneg sys hV'
  have := gLzU_mono sys hVV
  have := cAbsU_nonneg (sys := sys) hV hH
  have := cAbsU_nonneg (sys := sys) hV' hH
  have := cAbsU_mono sys hV hVV hH
  have := xvU_nonneg (sys := sys) hV hc
  have := xvU_nonneg (sys := sys) hV' hc'
  have := xvU_mono sys hV hVV hcc
  have := cGtU_nonneg sys hV hc
  have := cGtU_nonneg sys hV' hc'
  have := cGtU_mono sys hV hVV hc hcc
  have := xuU_nonneg (sys := sys) hV hH
  have := xuU_nonneg (sys := sys) hV' hH
  have := xuU_mono sys hV hVV hH
  have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
  have := gLtailMU_nonneg (sys := sys) hV' hH zero_le_one
  have := gLtailMU_mono sys hVV hH zero_le_one
  have : 0 ≤ alphaF := by unfold alphaF; positivity
  gcongr

lemma fU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    fU sys V Hunit ≤ fU sys V' Hunit := by
  unfold fU
  have hV' := hV.trans hVV
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  have := PlaneWaveGridG.gLzU_nonneg sys hV'
  have := gLzU_mono sys hVV
  have := cAbsU_nonneg (sys := sys) hV hH
  have := cAbsU_nonneg (sys := sys) hV' hH
  have := cAbsU_mono sys hV hVV hH
  have := xuU_nonneg (sys := sys) hV hH
  have := xuU_nonneg (sys := sys) hV' hH
  have := xuU_mono sys hV hVV hH
  have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
  have := gLtailMU_nonneg (sys := sys) hV' hH zero_le_one
  have := gLtailMU_mono sys hVV hH zero_le_one
  have : 0 ≤ alphaF := by unfold alphaF; positivity
  gcongr

lemma b0eU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    b0eU sys V Hunit ≤ b0eU sys V' Hunit := by
  unfold b0eU
  have := relBU_mono sys hV hVV hH
  gcongr

lemma cTrU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    cTrU sys V Hunit ≤ cTrU sys V' Hunit := by
  unfold cTrU
  have hV' := hV.trans hVV
  have := relBU_mono sys hV hVV hH
  have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
  have := gLtailMU_nonneg (sys := sys) hV' hH zero_le_one
  have := gLtailMU_mono sys hVV hH zero_le_one
  have := b0eU_nonneg sys hV hH
  have := b0eU_nonneg sys hV' hH
  have := b0eU_mono sys hV hVV hH
  have := sys.maxMass_pos
  gcongr

lemma resU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    resU sys V Hunit ≤ resU sys V' Hunit := by
  unfold resU
  have hV' := hV.trans hVV
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  have := PlaneWaveGridG.gLzU_nonneg sys hV'
  have := gLzU_mono sys hVV
  have := cTrU_nonneg sys hV hH
  have := cTrU_nonneg sys hV' hH
  have := cTrU_mono sys hV hVV hH
  have := b0eU_nonneg sys hV hH
  have := b0eU_nonneg sys hV' hH
  have := b0eU_mono sys hV hVV hH
  have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
  have := gLtailMU_nonneg (sys := sys) hV' hH zero_le_one
  have := gLtailMU_mono sys hVV hH zero_le_one
  have := sys.maxMass_pos
  have : 0 ≤ alphaF := by unfold alphaF; positivity
  gcongr

lemma b0gU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    b0gU sys V Hunit ≤ b0gU sys V' Hunit := by
  unfold b0gU
  have := b0eU_mono sys hV hVV hH
  have := gridFlowConstU_mono sys hV hVV
  have := sys.maxMass_pos
  gcongr

lemma b1gU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    b1gU sys V Hunit ≤ b1gU sys V' Hunit := by
  unfold b1gU
  have hV' := hV.trans hVV
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  have := PlaneWaveGridG.gLzU_nonneg sys hV'
  have := gLzU_mono sys hVV
  have := b0gU_nonneg sys hV hH
  have := b0gU_nonneg sys hV' hH
  have := b0gU_mono sys hV hVV hH
  have := resU_nonneg sys hV hH
  have := resU_nonneg sys hV' hH
  have := resU_mono sys hV hVV hH
  have := sys.maxMass_pos
  gcongr

lemma cPrU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    cPrU sys V Hunit ≤ cPrU sys V' Hunit := by
  unfold cPrU
  have := cU_mono sys hV hVV hH
  have := cGrU_mono sys hV hVV
  gcongr

lemma epsU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    epsU sys V Hunit ≤ epsU sys V' Hunit := by
  unfold epsU
  have := two_le_cU sys V Hunit
  have := cU_mono sys hV hVV hH
  gcongr

lemma zetaU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    zetaU sys V Hunit ≤ zetaU sys V' Hunit := by
  unfold zetaU
  have := b0eU_mono sys hV hVV hH
  have := b0gU_mono sys hV hVV hH
  have := epsU_mono sys hV hVV hH
  gcongr

lemma omegaU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    omegaU sys V Hunit ≤ omegaU sys V' Hunit := by
  unfold omegaU
  have := b0eU_mono sys hV hVV hH
  have := cTrU_mono sys hV hVV hH
  have := b0gU_mono sys hV hVV hH
  have := b1gU_mono sys hV hVV hH
  have := epsU_mono sys hV hVV hH
  have := sys.maxMass_pos
  gcongr

lemma gammaU_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    gammaU sys V Hunit ≤ gammaU sys V' Hunit := by
  unfold gammaU
  have hV' := hV.trans hVV
  have := omegaU_mono sys hV hVV hH
  have := gLAU_nonneg' sys hV
  have := gLAU_nonneg' sys hV'
  have := gLAU_mono sys hV hVV
  have := cPrU_nonneg (sys := sys) (Hunit := Hunit) hV
  have := cPrU_nonneg (sys := sys) (Hunit := Hunit) hV'
  have := cPrU_mono sys hV hVV hH
  have := zetaU_nonneg (sys := sys) hV hH
  have := zetaU_nonneg (sys := sys) hV' hH
  have := zetaU_mono sys hV hVV hH
  gcongr

lemma cellC_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    cellC sys V Hunit ≤ cellC sys V' Hunit := by
  unfold cellC
  have hV' := hV.trans hVV
  have hc := cPrU_nonneg (sys := sys) (Hunit := Hunit) hV
  have := cPrU_nonneg (sys := sys) (Hunit := Hunit) hV'
  have := cTrU_nonneg sys hV hH
  have := cTrU_nonneg sys hV' hH
  have := cTrU_mono sys hV hVV hH
  have := epsU_nonneg (sys := sys) (V := V) (Hunit := Hunit)
  have := epsU_nonneg (sys := sys) (V := V') (Hunit := Hunit)
  have := epsU_mono sys hV hVV hH
  have := zetaU_nonneg (sys := sys) hV hH
  have := zetaU_nonneg (sys := sys) hV' hH
  have := zetaU_mono sys hV hVV hH
  have := fU_nonneg sys hV hH
  have := fU_nonneg sys hV' hH
  have := fU_mono sys hV hVV hH
  have := cPrU_mono sys hV hVV hH
  have := gammaU_nonneg (sys := sys) hV hH
  have := gammaU_nonneg (sys := sys) hV' hH
  have := gammaU_mono sys hV hVV hH
  have := dU_nonneg sys hV hH hc
  have := dU_nonneg sys hV' hH (cPrU_nonneg (sys := sys) (Hunit := Hunit) hV')
  have := dU_mono sys hV hVV hH hc (cPrU_mono sys hV hVV hH)
  have := sys.maxMass_pos
  gcongr

/-- **The cutoff threshold is increasing in `V`**. -/
lemma cellK0_mono (hV : 0 ≤ V) (hVV : V ≤ V') (hH : 0 ≤ Hunit) :
    cellK0 sys V Hunit ≤ cellK0 sys V' Hunit := by
  unfold cellK0
  have := cU_mono sys hV hVV hH
  have := cGrU_mono sys hV hVV
  have := sys.maxMass_pos
  gcongr

lemma locC_mono (hV : 0 ≤ V) (hVV : V ≤ V') {Dbar : ℝ} (hD : 0 ≤ Dbar) :
    locC sys V Dbar ≤ locC sys V' Dbar := by
  unfold locC
  have := relBU_mono sys hV hVV hardyUnit_nonneg
  have := b0eU_mono sys hV hVV hardyUnit_nonneg
  have : 0 ≤ commBar eta Dbar := commBar_nonneg hD
  gcongr

/-- **The constant of `prop:free-kinetic-log` is increasing in `V`**. -/
lemma freeKinC_mono (hV : 0 ≤ V) (hVV : V ≤ V') {Dbar : ℝ} (hD : 0 ≤ Dbar) :
    freeKinC sys V Dbar ≤ freeKinC sys V' Dbar :=
  add_le_add (cellC_mono sys hV hVV hardyUnit_nonneg) (locC_mono sys hV hVV hD)

lemma freeKinConstNBO_mono (hV : 0 ≤ V) (hVV : V ≤ V') {Dbar Cbar : ℝ} (hD : 0 ≤ Dbar) :
    freeKinConstNBO sys V Dbar Cbar ≤ freeKinConstNBO sys V' Dbar Cbar := by
  unfold freeKinConstNBO
  exact mul_le_mul_of_nonneg_right (freeKinC_mono sys hV hVV hD) (sq_nonneg _)

lemma freeKinConstBO_mono (hV : 0 ≤ V) (hVV : V ≤ V') {Dbar Cbar δ : ℝ} (hD : 0 ≤ Dbar) :
    freeKinConstBO sys V Dbar Cbar δ ≤ freeKinConstBO sys V' Dbar Cbar δ := by
  unfold freeKinConstBO
  exact mul_le_mul_of_nonneg_right (freeKinC_mono sys hV hVV hD) (sq_nonneg _)

end Derived

/-! ## The explicit forms with a uniform profile bound -/

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` (general cutoff, (H_dom)) with a profile bound `V_θ ≤ V̄`**: the bound
of `free_kinetic_log_endpoint` with `C = freeKinC sys V̄ D̄` and the threshold `K₀ = cellK0 sys V̄`,
which depend on the profile only through `V̄`. -/
theorem free_kinetic_log_endpoint_vbar (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁)
    {Dinf Dst : ℝ} (hDinf : ‖ψ 0‖ + ‖H 0‖ ≤ Dinf)
    (hDst : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
      freeKinC sys Vbar Dbar * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) /
          (2 * Real.pi / L * m) ^ 3 +
        freeKinC sys Vbar Dbar * (Dinf + Dst) * (1 + t) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := ((abs_nonneg _).trans (X.d1 0 (p₀, 0))).trans hD1
  have hK' := (cellK0_mono sys hv0 hVbar hardyUnit_nonneg).trans hK
  have hC := freeKinC_mono sys hv0 hVbar hDb
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ 1 + t + Real.log (2 + 2 * Real.pi / L * m) := by linarith
  have ht1 : 0 ≤ 1 + t := by linarith
  refine (free_kinetic_log_endpoint sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hD1 hD2 hSm hBm hχB
    hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm hK' hκ Ug hg0
    hgcomm hgderiv).trans ?_
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`cor:free-stopping-log` with a profile bound `V_θ ≤ V̄`**: the bound of `free_stopping_log`
with `C = freeKinC sys V̄ D̄` and `K₀ = cellK0 sys V̄`. -/
theorem free_stopping_log_vbar (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 τ, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 τ, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁)
    {Dinf Dst : ℝ} (hDinf : ‖ψ 0‖ + ‖H 0‖ ≤ Dinf)
    (hDst : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t)
    {vp : ℝ} (hvp : 0 < vp) :
    |(freeKinQ sys p₀ (grad τ) - freeKinQ sys p₀ (grad 0)) / (vp * τ) -
        (regExpect sys (gF L) p₀ (Ug τ (regCoeff m ((molecularPositionSynthesis eta).symm
            (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0))))) -
          regExpect sys (gF L) p₀ (Ug 0 (regCoeff m ((molecularPositionSynthesis eta).symm
            (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))) / (vp * τ)| ≤
      2 * freeKinC sys Vbar Dbar * Dst ^ 2 / vp *
          (1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ) / (2 * Real.pi / L * m) ^ 3 +
        2 * freeKinC sys Vbar Dbar * (Dinf + Dst) / vp * (1 + 1 / τ) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := ((abs_nonneg _).trans (X.d1 0 (p₀, 0))).trans hD1
  have hK' := (cellK0_mono sys hv0 hVbar hardyUnit_nonneg).trans hK
  have hC := freeKinC_mono sys hv0 hVbar hDb
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hvp0 : 0 ≤ vp := hvp.le
  have hq : 0 ≤ 1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ := by
    have := div_nonneg (by linarith : (0 : ℝ) ≤ 1 + Real.log (2 + 2 * Real.pi / L * m)) hτ.le
    linarith
  have hq1 : 0 ≤ 1 + 1 / τ := by
    have := div_nonneg zero_le_one hτ.le
    linarith
  refine (free_stopping_log sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hD1 hD2 hSm hBm hχB hSB hdS
    hd2S hψd hHam hgrad hτ hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm hK' hκ Ug hg0 hgcomm
    hgderiv hvp).trans ?_
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`eq:free-kinetic-N` with a profile bound `V_θ ≤ V̄`**: the bound of `free_kinetic_log_N` with
`C = freeKinC sys V̄ D̄` and `K₀ = cellK0 sys V̄`. -/
theorem free_kinetic_log_N_vbar (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁)
    {Dinf Dst : ℝ} (hDinf : ‖ψ 0‖ + ‖H 0‖ ≤ Dinf)
    (hDst : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
      125 / (4 * Real.pi ^ 3) * freeKinC sys Vbar Dbar * Dst ^ 2 *
          (L ^ 3 / ((4 * m + 1 : ℝ) ^ 3)) *
          (1 + t + Real.log (2 + ((4 * m + 1 : ℝ) ^ 3) ^ (1 / 3 : ℝ) / L)) +
        freeKinC sys Vbar Dbar * (Dinf + Dst) * (1 + t) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := ((abs_nonneg _).trans (X.d1 0 (p₀, 0))).trans hD1
  have hK' := (cellK0_mono sys hv0 hVbar hardyUnit_nonneg).trans hK
  have hC := freeKinC_mono sys hv0 hVbar hDb
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hL0 := pos_of_two_pi_le hL2
  have hlN : 0 ≤ Real.log (2 + ((4 * m + 1 : ℝ) ^ 3) ^ (1 / 3 : ℝ) / L) := by
    apply Real.log_nonneg
    have := div_nonneg (by positivity : (0 : ℝ) ≤ ((4 * m + 1 : ℝ) ^ 3) ^ (1 / 3 : ℝ)) hL0.le
    linarith
  have hQN : 0 ≤ 1 + t + Real.log (2 + ((4 * m + 1 : ℝ) ^ 3) ^ (1 / 3 : ℝ) / L) := by linarith
  have hL3 : 0 ≤ L ^ 3 / ((4 * m + 1 : ℝ) ^ 3) := div_nonneg (pow_nonneg hL0.le 3) (by positivity)
  have ht1 : 0 ≤ 1 + t := by linarith
  refine (free_kinetic_log_N sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hD1 hD2 hSm hBm hχB hSB
    hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm hK' hκ Ug hg0
    hgcomm hgderiv).trans ?_
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with finite internal spin and a profile bound `V_θ ≤ V̄`**: the bound
of `free_kinetic_log_spin` with `C = freeKinC sys V̄ D̄` and `K₀ = cellK0 sys V̄`. -/
theorem free_kinetic_log_spin_vbar (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : ς → MolecularPositionL2 eta}
    (hdom0 : ∀ σ, HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ))
    (hdom1 : ∀ σ, HasGLHamiltonian sys L θ (h₀ σ) (h₁ σ))
    {Dinf Dst : ℝ} (hDinf : ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf)
    (hDst : Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
      Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))| ≤
      freeKinC sys Vbar Dbar * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) /
          (2 * Real.pi / L * m) ^ 3 +
        freeKinC sys Vbar Dbar * (Dinf + Dst) * (1 + t) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := ((abs_nonneg _).trans (X.d1 0 (p₀, 0))).trans hD1
  have hK' := (cellK0_mono sys hv0 hVbar hardyUnit_nonneg).trans hK
  have hC := freeKinC_mono sys hv0 hVbar hDb
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ 1 + t + Real.log (2 + 2 * Real.pi / L * m) := by linarith
  have ht1 : 0 ≤ 1 + t := by linarith
  refine (free_kinetic_log_spin sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hD1 hD2 hSm hBm hχB hSB
    hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm hK' hκ Ug hg0
    hgcomm hgderiv).trans ?_
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`cor:free-stopping-log` with finite internal spin and a profile bound `V_θ ≤ V̄`**: the bound
of `free_stopping_log_spin` with `C = freeKinC sys V̄ D̄` and `K₀ = cellK0 sys V̄`. -/
theorem free_stopping_log_spin_vbar (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 τ, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 τ, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : ς → MolecularPositionL2 eta}
    (hdom0 : ∀ σ, HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ))
    (hdom1 : ∀ σ, HasGLHamiltonian sys L θ (h₀ σ) (h₁ σ))
    {Dinf Dst : ℝ} (hDinf : ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf)
    (hDst : Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
      Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t)
    {vp : ℝ} (hvp : 0 < vp) :
    |(freeKinQS sys p₀ (grad τ) - freeKinQS sys p₀ (grad 0)) / (vp * τ) -
        (∑ σ, regExpect sys (gF L) p₀ (Ug τ (regCoeff m ((molecularPositionSynthesis eta).symm
            (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ))))) -
          ∑ σ, regExpect sys (gF L) p₀ (Ug 0 (regCoeff m ((molecularPositionSynthesis eta).symm
            (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))) / (vp * τ)| ≤
      2 * freeKinC sys Vbar Dbar * Dst ^ 2 / vp *
          (1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ) / (2 * Real.pi / L * m) ^ 3 +
        2 * freeKinC sys Vbar Dbar * (Dinf + Dst) / vp * (1 + 1 / τ) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := ((abs_nonneg _).trans (X.d1 0 (p₀, 0))).trans hD1
  have hK' := (cellK0_mono sys hv0 hVbar hardyUnit_nonneg).trans hK
  have hC := freeKinC_mono sys hv0 hVbar hDb
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hvp0 : 0 ≤ vp := hvp.le
  have hq : 0 ≤ 1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ := by
    have := div_nonneg (by linarith : (0 : ℝ) ≤ 1 + Real.log (2 + 2 * Real.pi / L * m)) hτ.le
    linarith
  have hq1 : 0 ≤ 1 + 1 / τ := by
    have := div_nonneg zero_le_one hτ.le
    linarith
  refine (free_stopping_log_spin sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hD1 hD2 hSm hBm hχB
    hSB hdS hd2S hψd hHam hgrad hτ hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm hK' hκ Ug hg0
    hgcomm hgderiv hvp).trans ?_
  gcongr

/-! ## The compatible cutoffs -/

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` without clamped nuclei, mass-compatible cutoff, profile bound
`V_θ ≤ V̄`**: the bound of `free_kinetic_log_nbo` with `C = freeKinConstNBO sys V̄ D̄ C̄` and
`K₀ = cellK0 sys V̄`. -/
theorem free_kinetic_log_nbo_vbar [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ}
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
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
      freeKinConstNBO sys Vbar Dbar Cbar * D ^ 2 *
          (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstNBO sys Vbar Dbar Cbar * D * (1 + t) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  have hK' := (cellK0_mono sys hv0 hVbar hardyUnit_nonneg).trans hK
  have hC := freeKinConstNBO_mono sys hv0 hVbar (Cbar := Cbar) hDb
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ 1 + t + Real.log (2 + 2 * Real.pi / L * m) := by linarith
  have ht1 : 0 ≤ 1 + t := by linarith
  refine (free_kinetic_log_nbo sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hDbar hCbar hSm hBm hχB
    hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm hK' hκ Ug hg0
        hgcomm hgderiv).trans
    ?_
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with clamped nuclei, cutoff flat near the nuclei, profile bound
`V_θ ≤ V̄`**: the bound of `free_kinetic_log_bo` with `C = freeKinConstBO sys V̄ D̄ C̄ δ` and
`K₀ = cellK0 sys V̄`. -/
theorem free_kinetic_log_bo_vbar (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
      freeKinConstBO sys Vbar Dbar Cbar δ * D ^ 2 *
          (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstBO sys Vbar Dbar Cbar δ * D * (1 + t) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  have hK' := (cellK0_mono sys hv0 hVbar hardyUnit_nonneg).trans hK
  have hC := freeKinConstBO_mono sys hv0 hVbar (Cbar := Cbar) (δ := δ) hDb
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ 1 + t + Real.log (2 + 2 * Real.pi / L * m) := by linarith
  have ht1 : 0 ≤ 1 + t := by linarith
  refine (free_kinetic_log_bo sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hδ hflat hDbar hCbar hSm
    hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm hK' hκ Ug hg0 hgcomm
    hgderiv).trans ?_
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with spin, without clamped nuclei, profile bound `V_θ ≤ V̄`**: the
bound of `free_kinetic_log_nbo_spin` with `C = freeKinConstNBO sys V̄ D̄ C̄` and
`K₀ = cellK0 sys V̄`. -/
theorem free_kinetic_log_nbo_spin_vbar [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ}
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
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))| ≤
      freeKinConstNBO sys Vbar Dbar Cbar * D ^ 2 *
          (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstNBO sys Vbar Dbar Cbar * D * (1 + t) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  have hK' := (cellK0_mono sys hv0 hVbar hardyUnit_nonneg).trans hK
  have hC := freeKinConstNBO_mono sys hv0 hVbar (Cbar := Cbar) hDb
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ 1 + t + Real.log (2 + 2 * Real.pi / L * m) := by linarith
  have ht1 : 0 ≤ 1 + t := by linarith
  refine (free_kinetic_log_nbo_spin sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hDbar hCbar hSm hBm
    hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm hK' hκ Ug hg0 hgcomm
    hgderiv).trans ?_
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with spin, clamped nuclei, profile bound `V_θ ≤ V̄`**: the bound of
`free_kinetic_log_bo_spin` with `C = freeKinConstBO sys V̄ D̄ C̄ δ` and `K₀ = cellK0 sys V̄`. -/
theorem free_kinetic_log_bo_spin_vbar (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))| ≤
      freeKinConstBO sys Vbar Dbar Cbar δ * D ^ 2 *
          (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstBO sys Vbar Dbar Cbar δ * D * (1 + t) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  have hK' := (cellK0_mono sys hv0 hVbar hardyUnit_nonneg).trans hK
  have hC := freeKinConstBO_mono sys hv0 hVbar (Cbar := Cbar) (δ := δ) hDb
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ 1 + t + Real.log (2 + 2 * Real.pi / L * m) := by linarith
  have ht1 : 0 ≤ 1 + t := by linarith
  refine (free_kinetic_log_bo_spin sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hδ hflat hDbar hCbar
    hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm hK' hκ Ug hg0
    hgcomm hgderiv).trans ?_
  gcongr

/-! ## The constants before the quantifiers -/

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log`** (general cutoff, (H_dom)) **for every profile with `V_θ ≤ V̄`**:
there are `C ≥ 0` and `K₀ > 0`, depending only on the system, the profile bound `V̄` and the cutoff
bound `D̄`, such that for every `L ≥ 2π`, every profile with `V_θ ≤ V̄`, every admissible cutoff
with derivative bounds `D̄`, every supplied free-space solution with leakage `ε` on `[0, t]` and
cutoff-domain data, every `m ≥ 8` with `K = 2πm/L ≥ K₀`, every kernel of the open-grid class and
every grid propagator,
`|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C D_*² [1 + t + log(2 + K)]/K³
  + C (𝒟_∞ + D_*) (1 + t) ε`. -/
theorem free_kinetic_log_vbar (sys : CoulombSystem eta ν) (Vbar Dbar : ℝ) (hV : 0 ≤
    Vbar) (hD : 0 ≤ Dbar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ {L R R0 ρ : ℝ} {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L), Profile R θ →
      R ≤ L / 2 → tv R θ ≤ Vbar → 0 ≤ R0 → 0 ≤ ρ → (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) →
      ∀ (P : ν → E3), (∀ l, ‖P l‖ ≤ R0) →
      (∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle)) →
      ∀ (X : Cutoff eta L), (∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ) →
      X.D1 ≤ Dbar → X.D2 ≤ Dbar →
      ∀ {Bone S : Set (Rcfg eta)}, MeasurableSet S → MeasurableSet Bone →
      (∀ r ∈ Bone, X.χ r = 1) → S ⊆ Boneᶜ → (∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0) →
      (∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0) →
      ∀ {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta},
      (∀ s, HasDerivAt ψ (-(Complex.I • H s)) s) → (∀ s, HasFreeHamiltonian sys P (ψ s) (H s)) →
      (∀ s, HasWeakGrad (ψ s) (grad s)) →
      ∀ {t ε : ℝ}, 0 ≤ t → 0 ≤ ε →
      (∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2) →
      (∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2) →
      ∀ {h₀ h₁ : MolecularPositionL2 eta},
      HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀ →
      HasGLHamiltonian sys L θ h₀ h₁ →
      ∀ {Dinf Dst : ℝ}, ‖ψ 0‖ + ‖H 0‖ ≤ Dinf →
      ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
        (PlaneWaveGridG.gLref L θ (tv R θ)) m κ →
      ∀ (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)),
      (∀ x, Ug 0 x = x) →
      (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        κ (2 * Real.pi / L) (Ug t x)) →
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
          (2 * Real.pi / L) x))) t) →
      |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
          ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
        C * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
          C * (Dinf + Dst) * (1 + t) * ε := by
  refine ⟨freeKinC sys Vbar Dbar, freeKinC_nonneg sys hV hD,
    cellK0 sys Vbar molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP hpos X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ψ H grad hψd hHam hgrad t ε ht hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst p₀ m
    hm hK κ hκ Ug hg0 hgcomm hgderiv
  exact free_kinetic_log_endpoint_vbar sys hL2 hθ hR hR0 hρ hone hVθ P hP hpos X hret hD1 hD2 hSm
    hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm hK hκ Ug
    hg0 hgcomm hgderiv

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` for a fixed molecule and every profile with `V_θ ≤ V̄`**: one constant
and one threshold, depending only on the masses and charges, `V̄` and `D̄`, for every cell size,
profile with `V_θ ≤ V̄`, nuclear configuration in `B_{R₀}(0)`, cutoff, solution, kernel and grid
propagator. -/
theorem free_kinetic_log_at_vbar (sys : CoulombSystem eta ν) (Vbar Dbar : ℝ) (hV : 0 ≤ Vbar)
    (hD : 0 ≤ Dbar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ {L R R0 ρ : ℝ} {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L), Profile R θ →
      R ≤ L / 2 → tv R θ ≤ Vbar → 0 ≤ R0 → 0 ≤ ρ → (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) →
      ∀ (P : ν → E3), (∀ l, ‖P l‖ ≤ R0) →
      ∀ (X : Cutoff eta L), (∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ) →
      X.D1 ≤ Dbar → X.D2 ≤ Dbar →
      ∀ {Bone S : Set (Rcfg eta)}, MeasurableSet S → MeasurableSet Bone →
      (∀ r ∈ Bone, X.χ r = 1) → S ⊆ Boneᶜ → (∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0) →
      (∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0) →
      ∀ {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta},
      (∀ s, HasDerivAt ψ (-(Complex.I • H s)) s) → (∀ s, HasFreeHamiltonian sys P (ψ s) (H s)) →
      (∀ s, HasWeakGrad (ψ s) (grad s)) →
      ∀ {t ε : ℝ}, 0 ≤ t → 0 ≤ ε →
      (∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2) →
      (∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2) →
      ∀ {h₀ h₁ : MolecularPositionL2 eta},
      HasGLHamiltonian (sysAt sys P L) L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀ →
      HasGLHamiltonian (sysAt sys P L) L θ h₀ h₁ →
      ∀ {Dinf Dst : ℝ}, ‖ψ 0‖ + ‖H 0‖ ≤ Dinf →
      ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
        (PlaneWaveGridG.gLref L θ (tv R θ)) m κ →
      ∀ (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)),
      (∀ x, Ug 0 x = x) →
      (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x) =
          Hgrid eta m (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei).toNucData
            κ (2 * Real.pi / L) (Ug t x)) →
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys)
          (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x))) t) →
      |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
          ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
        C * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
          C * (Dinf + Dst) * (1 + t) * ε := by
  refine ⟨freeKinC sys Vbar Dbar, freeKinC_nonneg sys hV hD,
    cellK0 sys Vbar molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ψ H grad hψd hHam hgrad t ε ht hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst p₀ m
    hm hK κ hκ Ug hg0 hgcomm hgderiv
  exact free_kinetic_log_endpoint_vbar (sysAt sys P L) hL2 hθ hR hR0 hρ hone hVθ P hP (fun l => rfl)
    X hret hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf
    hDst p₀ m hm hK hκ Ug hg0 hgcomm hgderiv

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` for a fixed molecule with finite internal spin, every profile with
`V_θ ≤ V̄`**: one constant and one threshold for every cell size, profile with `V_θ ≤ V̄`, nuclear
configuration and finite spin set. -/
theorem free_kinetic_log_spin_at_vbar (sys : CoulombSystem eta ν) (Vbar Dbar : ℝ) (hV : 0 ≤ Vbar)
    (hD : 0 ≤ Dbar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ {L R R0 ρ : ℝ} {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L), Profile R θ →
      R ≤ L / 2 → tv R θ ≤ Vbar → 0 ≤ R0 → 0 ≤ ρ → (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) →
      ∀ (P : ν → E3), (∀ l, ‖P l‖ ≤ R0) →
      ∀ (X : Cutoff eta L), (∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ) →
      X.D1 ≤ Dbar → X.D2 ≤ Dbar →
      ∀ {Bone S : Set (Rcfg eta)}, MeasurableSet S → MeasurableSet Bone →
      (∀ r ∈ Bone, X.χ r = 1) → S ⊆ Boneᶜ → (∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0) →
      (∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0) →
      ∀ (ς : Type) [Fintype ς] {Ψ HΨ : ℝ → FreeSpinL2 eta ς}
        {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta},
      (∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s) →
      (∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ)) →
      (∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ)) →
      ∀ {t ε : ℝ}, 0 ≤ t → 0 ≤ ε →
      (∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2) →
      (∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2) →
      ∀ {h₀ h₁ : ς → MolecularPositionL2 eta},
      (∀ σ, HasGLHamiltonian (sysAt sys P L) L θ
        (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ)) →
      (∀ σ, HasGLHamiltonian (sysAt sys P L) L θ (h₀ σ) (h₁ σ)) →
      ∀ {Dinf Dst : ℝ}, ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf →
      Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
        Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
        (PlaneWaveGridG.gLref L θ (tv R θ)) m κ →
      ∀ (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)),
      (∀ x, Ug 0 x = x) →
      (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x) =
          Hgrid eta m (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei).toNucData
            κ (2 * Real.pi / L) (Ug t x)) →
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys)
          (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x))) t) →
      |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
          ((molecularPositionSynthesis eta).symm
            (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))| ≤
        C * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
          C * (Dinf + Dst) * (1 + t) * ε := by
  refine ⟨freeKinC sys Vbar Dbar, freeKinC_nonneg sys hV hD,
    cellK0 sys Vbar molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ς _ Ψ HΨ grad hψd hHam hgrad t ε ht hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst
    p₀ m hm hK κ hκ Ug hg0 hgcomm hgderiv
  exact free_kinetic_log_spin_vbar (sysAt sys P L) hL2 hθ hR hR0 hρ hone hVθ P hP (fun l => rfl) X
    hret hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf hDst
    p₀ m hm hK hκ Ug hg0 hgcomm hgderiv

set_option maxHeartbeats 1000000 in
/-- **`cor:free-stopping-log` for a fixed molecule and every profile with `V_θ ≤ V̄`**: one constant
and one threshold for every cell size, profile with `V_θ ≤ V̄` and nuclear configuration. -/
theorem free_stopping_log_at_vbar (sys : CoulombSystem eta ν) (Vbar Dbar : ℝ) (hV : 0 ≤ Vbar)
    (hD : 0 ≤ Dbar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ {L R R0 ρ : ℝ} {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L), Profile R θ →
      R ≤ L / 2 → tv R θ ≤ Vbar → 0 ≤ R0 → 0 ≤ ρ → (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) →
      ∀ (P : ν → E3), (∀ l, ‖P l‖ ≤ R0) →
      ∀ (X : Cutoff eta L), (∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ) →
      X.D1 ≤ Dbar → X.D2 ≤ Dbar →
      ∀ {Bone S : Set (Rcfg eta)}, MeasurableSet S → MeasurableSet Bone →
      (∀ r ∈ Bone, X.χ r = 1) → S ⊆ Boneᶜ → (∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0) →
      (∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0) →
      ∀ {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta},
      (∀ s, HasDerivAt ψ (-(Complex.I • H s)) s) → (∀ s, HasFreeHamiltonian sys P (ψ s) (H s)) →
      (∀ s, HasWeakGrad (ψ s) (grad s)) →
      ∀ {τ ε : ℝ}, 0 < τ → 0 ≤ ε →
      (∀ s ∈ Icc 0 τ, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2) →
      (∀ s ∈ Icc 0 τ, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2) →
      ∀ {h₀ h₁ : MolecularPositionL2 eta},
      HasGLHamiltonian (sysAt sys P L) L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀ →
      HasGLHamiltonian (sysAt sys P L) L θ h₀ h₁ →
      ∀ {Dinf Dst : ℝ}, ‖ψ 0‖ + ‖H 0‖ ≤ Dinf →
      ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
        (PlaneWaveGridG.gLref L θ (tv R θ)) m κ →
      ∀ (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)),
      (∀ x, Ug 0 x = x) →
      (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x) =
          Hgrid eta m (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei).toNucData
            κ (2 * Real.pi / L) (Ug t x)) →
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys)
          (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x))) t) →
      ∀ {vp : ℝ}, 0 < vp →
      |(freeKinQ sys p₀ (grad τ) - freeKinQ sys p₀ (grad 0)) / (vp * τ) -
          (regExpect sys (gF L) p₀ (Ug τ (regCoeff m ((molecularPositionSynthesis eta).symm
              (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0))))) -
            regExpect sys (gF L) p₀ (Ug 0 (regCoeff m ((molecularPositionSynthesis eta).symm
              (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))) / (vp * τ)| ≤
        C * Dst ^ 2 / vp * (1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ) /
            (2 * Real.pi / L * m) ^ 3 +
          C * (Dinf + Dst) / vp * (1 + 1 / τ) * ε := by
  refine ⟨2 * freeKinC sys Vbar Dbar, by have := freeKinC_nonneg sys hV hD; positivity,
    cellK0 sys Vbar molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ψ H grad hψd hHam hgrad τ ε hτ hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst p₀ m
    hm hK κ hκ Ug hg0 hgcomm hgderiv vp hvp
  exact free_stopping_log_vbar (sysAt sys P L) hL2 hθ hR hR0 hρ hone hVθ P hP (fun l => rfl) X hret
    hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad hτ hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m
    hm hK hκ Ug hg0 hgcomm hgderiv hvp

set_option maxHeartbeats 1000000 in
/-- **`cor:free-stopping-log` for a fixed molecule with finite internal spin, every profile with
`V_θ ≤ V̄`**: one constant and one threshold for every cell size, profile with `V_θ ≤ V̄`, nuclear
configuration and finite spin set. -/
theorem free_stopping_log_spin_at_vbar (sys : CoulombSystem eta ν) (Vbar Dbar : ℝ) (hV : 0 ≤ Vbar)
    (hD : 0 ≤ Dbar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ {L R R0 ρ : ℝ} {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L), Profile R θ →
      R ≤ L / 2 → tv R θ ≤ Vbar → 0 ≤ R0 → 0 ≤ ρ → (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) →
      ∀ (P : ν → E3), (∀ l, ‖P l‖ ≤ R0) →
      ∀ (X : Cutoff eta L), (∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ) →
      X.D1 ≤ Dbar → X.D2 ≤ Dbar →
      ∀ {Bone S : Set (Rcfg eta)}, MeasurableSet S → MeasurableSet Bone →
      (∀ r ∈ Bone, X.χ r = 1) → S ⊆ Boneᶜ → (∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0) →
      (∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0) →
      ∀ (ς : Type) [Fintype ς] {Ψ HΨ : ℝ → FreeSpinL2 eta ς}
        {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta},
      (∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s) →
      (∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ)) →
      (∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ)) →
      ∀ {τ ε : ℝ}, 0 < τ → 0 ≤ ε →
      (∀ s ∈ Icc 0 τ, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2) →
      (∀ s ∈ Icc 0 τ, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2) →
      ∀ {h₀ h₁ : ς → MolecularPositionL2 eta},
      (∀ σ, HasGLHamiltonian (sysAt sys P L) L θ
        (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ)) →
      (∀ σ, HasGLHamiltonian (sysAt sys P L) L θ (h₀ σ) (h₁ σ)) →
      ∀ {Dinf Dst : ℝ}, ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf →
      Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
        Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
        (PlaneWaveGridG.gLref L θ (tv R θ)) m κ →
      ∀ (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)),
      (∀ x, Ug 0 x = x) →
      (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x) =
          Hgrid eta m (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei).toNucData
            κ (2 * Real.pi / L) (Ug t x)) →
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys)
          (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x))) t) →
      ∀ {vp : ℝ}, 0 < vp →
      |(freeKinQS sys p₀ (grad τ) - freeKinQS sys p₀ (grad 0)) / (vp * τ) -
          (∑ σ, regExpect sys (gF L) p₀ (Ug τ (regCoeff m ((molecularPositionSynthesis eta).symm
              (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ))))) -
            ∑ σ, regExpect sys (gF L) p₀ (Ug 0 (regCoeff m ((molecularPositionSynthesis eta).symm
              (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))) / (vp * τ)| ≤
        C * Dst ^ 2 / vp * (1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ) /
            (2 * Real.pi / L * m) ^ 3 +
          C * (Dinf + Dst) / vp * (1 + 1 / τ) * ε := by
  refine ⟨2 * freeKinC sys Vbar Dbar, by have := freeKinC_nonneg sys hV hD; positivity,
    cellK0 sys Vbar molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ς _ Ψ HΨ grad hψd hHam hgrad τ ε hτ hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst
    p₀ m hm hK κ hκ Ug hg0 hgcomm hgderiv vp hvp
  exact free_stopping_log_spin_vbar (sysAt sys P L) hL2 hθ hR hR0 hρ hone hVθ P hP (fun l => rfl) X
    hret hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad hτ hε hleak0 hleak1 hdom0 hdom1 hDinf hDst
    p₀ m hm hK hκ Ug hg0 hgcomm hgderiv hvp

/-! ## The explicit cutoffs -/

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` without clamped nuclei, uniform in `L` and in the profiles with
`V_θ ≤ V`**: the bound of `free_kinetic_log_nbo_uniform` with `C = freeKinConstNBO sys V D_s C_s`
and `K₀ = cellK0 sys V`. -/
theorem free_kinetic_log_nbo_uniform_vbar [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ V : ℝ}
    (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) {L R : ℝ} {θ : ℝ → ℝ} (hL : freeKinL0 R0 ρ ≤ L)
    (hθ : Profile R θ) (hR : R ≤ L / 2) (hV : tv R θ ≤ V)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r}, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2}, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys V molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          ((quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
            (pos_of_freeDynL0 hL) (ψ 0)))))| ≤
      freeKinConstNBO sys V (quadCutoff8 sys.one_le_mass).D (quadCutoff8 sys.one_le_mass).C *
          D ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstNBO sys V (quadCutoff8 sys.one_le_mass).D (quadCutoff8 sys.one_le_mass).C *
          D * (1 + t) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hK' := (cellK0_mono sys hv0 hV hardyUnit_nonneg).trans hK
  have hC :=
      freeKinConstNBO_mono sys hv0 hV (Cbar :=
      (quadCutoff8 sys.one_le_mass).C) (quadCutoff8 sys.one_le_mass).D_nonneg
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ 1 + t + Real.log (2 + 2 * Real.pi / L * m) := by linarith
  have ht1 : 0 ≤ 1 + t := by linarith
  refine (free_kinetic_log_nbo_uniform sys hR0 hρ hL hθ hR rfl hone P hP hpos hψd hHam hgrad ht hε
    hleak0 hleak1 hH1 hD p₀ m hm hK' hκ Ug hg0 hgcomm hgderiv).trans ?_
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with clamped nuclei and equal moving masses, uniform in `L` and in the
profiles with `V_θ ≤ V`**: the bound of `free_kinetic_log_bo_uniform` with
`C = freeKinConstBO sys V D_s C_s δ` and `K₀ = cellK0 sys V`. -/
theorem free_kinetic_log_bo_uniform_vbar (sys : CoulombSystem eta ν) {m₀ : ℝ}
    (hmass : ∀ i, sys.mass i = m₀) (hm0 : 1 ≤ m₀) {V R0 ρ δ : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hδ : 0 < δ) (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0) {L R : ℝ} {θ : ℝ → ℝ}
    (hL : freeKinBOL0 R0 ρ δ ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hV : tv R θ ≤ V)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in {r | ∃ i, L / 16 ≤ ‖particle r i‖}, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in {r | (∃ i, L / 16 ≤ ‖particle r i‖) ∧
      ∀ i, ‖particle r i‖ ≤ L / 8}, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm8 : 8 ≤ m)
    (hK : cellK0 sys V molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys)
      (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x) =
        Hgrid eta m (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei).toNucData
          κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x))) t) :
    |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          ((prodCutoffL hmass hm0 (sixteen_le_of_freeDynBOL0 hL)).toCutoff.chiW.cutL2
            (pos_of_freeDynBOL0 hL) (ψ 0)))))| ≤
      freeKinConstBO sys V (prodCutoff16 hmass hm0).D (prodCutoff16 hmass hm0).C δ * D ^ 2 *
          (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstBO sys V (prodCutoff16 hmass hm0).D (prodCutoff16 hmass hm0).C δ * D *
          (1 + t) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hK' := (cellK0_mono sys hv0 hV hardyUnit_nonneg).trans hK
  have hC :=
      freeKinConstBO_mono sys hv0 hV (Cbar := (prodCutoff16 hmass hm0).C) (δ :=
      δ) (prodCutoff16 hmass hm0).D_nonneg
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ 1 + t + Real.log (2 + 2 * Real.pi / L * m) := by linarith
  have ht1 : 0 ≤ 1 + t := by linarith
  refine (free_kinetic_log_bo_uniform sys hmass hm0 hR0 hρ hδ P hP hL hθ hR rfl hone hψd hHam
    hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm8 hK' hκ Ug hg0 hgcomm hgderiv).trans ?_
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with spin, without clamped nuclei, uniform in `L` and in the profiles
with `V_θ ≤ V`**: the bound of `free_kinetic_log_nbo_spin_uniform` with
`C = freeKinConstNBO sys V D_s C_s` and `K₀ = cellK0 sys V`. -/
theorem free_kinetic_log_nbo_spin_uniform_vbar [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ V : ℝ}
    (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) {L R : ℝ} {θ : ℝ → ℝ} (hL : freeKinL0 R0 ρ ≤ L)
    (hθ : Profile R θ) (hR : R ≤ L / 2) (hV : tv R θ ≤ V)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t,
      ∑ σ, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r}, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2}, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys V molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          ((quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
            (pos_of_freeDynL0 hL) (Ψ 0 σ)))))| ≤
      freeKinConstNBO sys V (quadCutoff8 sys.one_le_mass).D (quadCutoff8 sys.one_le_mass).C *
          D ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstNBO sys V (quadCutoff8 sys.one_le_mass).D (quadCutoff8 sys.one_le_mass).C *
          D * (1 + t) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hK' := (cellK0_mono sys hv0 hV hardyUnit_nonneg).trans hK
  have hC :=
      freeKinConstNBO_mono sys hv0 hV (Cbar :=
      (quadCutoff8 sys.one_le_mass).C) (quadCutoff8 sys.one_le_mass).D_nonneg
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ 1 + t + Real.log (2 + 2 * Real.pi / L * m) := by linarith
  have ht1 : 0 ≤ 1 + t := by linarith
  refine (free_kinetic_log_nbo_spin_uniform sys hR0 hρ hL hθ hR rfl hone P hP hpos hψd hHam hgrad
    ht hε hleak0 hleak1 hH1 hD p₀ m hm hK' hκ Ug hg0 hgcomm hgderiv).trans ?_
  gcongr

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with spin, clamped nuclei and equal moving masses, uniform in `L` and
in the profiles with `V_θ ≤ V`**: the bound of `free_kinetic_log_bo_spin_uniform` with
`C = freeKinConstBO sys V D_s C_s δ` and `K₀ = cellK0 sys V`. -/
theorem free_kinetic_log_bo_spin_uniform_vbar (sys : CoulombSystem eta ν) {m₀ : ℝ}
    (hmass : ∀ i, sys.mass i = m₀) (hm0 : 1 ≤ m₀) {V R0 ρ δ : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hδ : 0 < δ) (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0) {L R : ℝ} {θ : ℝ → ℝ}
    (hL : freeKinBOL0 R0 ρ δ ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hV : tv R θ ≤ V)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t,
      ∑ σ, ∫ r in {r | ∃ i, L / 16 ≤ ‖particle r i‖}, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in {r | (∃ i, L / 16 ≤ ‖particle r i‖) ∧
      ∀ i, ‖particle r i‖ ≤ L / 8}, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm8 : 8 ≤ m)
    (hK : cellK0 sys V molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys)
      (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x) =
        Hgrid eta m (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei).toNucData
          κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x))) t) :
    |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          ((prodCutoffL hmass hm0 (sixteen_le_of_freeDynBOL0 hL)).toCutoff.chiW.cutL2
            (pos_of_freeDynBOL0 hL) (Ψ 0 σ)))))| ≤
      freeKinConstBO sys V (prodCutoff16 hmass hm0).D (prodCutoff16 hmass hm0).C δ * D ^ 2 *
          (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstBO sys V (prodCutoff16 hmass hm0).D (prodCutoff16 hmass hm0).C δ * D *
          (1 + t) * ε := by
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hK' := (cellK0_mono sys hv0 hV hardyUnit_nonneg).trans hK
  have hC :=
      freeKinConstBO_mono sys hv0 hV (Cbar := (prodCutoff16 hmass hm0).C) (δ :=
      δ) (prodCutoff16 hmass hm0).D_nonneg
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hv0 hK').1
  have hK3 : 0 ≤ (2 * Real.pi / L * m) ^ 3 := pow_nonneg (by linarith) 3
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ 1 + t + Real.log (2 + 2 * Real.pi / L * m) := by linarith
  have ht1 : 0 ≤ 1 + t := by linarith
  refine (free_kinetic_log_bo_spin_uniform sys hmass hm0 hR0 hρ hδ P hP hL hθ hR rfl hone hψd hHam
    hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm8 hK' hκ Ug hg0 hgcomm hgderiv).trans ?_
  gcongr

end KineticLog
