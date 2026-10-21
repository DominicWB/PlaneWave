import PlaneWave.FreeBoundary.TorusApproximation

/-!
# `prop:free` in manuscript form

`free_grid_exponentialU_prod` and `free_grid_complexity_prod` take normalised near-minimisers with
small mass outside the retained region. Here those hypotheses are derived
(`PlaneWave.FreeBoundary.AgmonApproximation`, `PlaneWave.FreeBoundary.TorusApproximation`) from the
hypotheses of the manuscript:

* the free-space ground state: `H_∞ ψ_∞ = E_∞ ψ_∞`, `‖ψ_∞‖ = 1`, `ψ_∞` in the sector, `E_∞` the
  bottom of the energy form on the sector, and Agmon decay `Σ_i ∫ e^{2α|x_i|} |ψ_∞|² ≤ A`;
* the torus ground state (lower bound only): `u_L ∈ H²` of the sector with `H u_L = E_L u_L`,
  `‖u_L‖ = 1`, and assumption (A) in the form `Σ_i ∫ e^{2β(|x_i| - R_{L/2})} |u_L|² ≤ A'` (cell
  coordinates, `R_{L/2} = L/8 - R₀ - ρ`). The manuscript's `‖e^{β dist(·, B_{L/2})} u_L‖ ≤ C`
  implies it with `A' = η C²`, since `dist(x, B_{L/2}) ≥ |x_i| - R_{L/2}` for every particle.

The nuclei of the free-space molecule sit at `P_ℓ ∈ B_{R₀}(0)`; on the torus of cell size `L` the
system is `sysAt sys P L`. All constants below are independent of `L`. As in the manuscript the
nuclei are clamped: without clamped nuclei (all particles quantum) the free-space Hamiltonian is
translation invariant and has no normalisable eigenfunction, and the hypotheses on `ψ_∞` cannot
hold.

* `freeUpperL0`, `freeUpperConst`, `freeEnergyL0`, `freeEnergyConst`, `freeEnergyRate`,
  `freeUpperBudget`, `freeEnergyBudget`: the explicit `L₀`, `C'`, `γ` and energy budgets;
* `gLTorusGroundEnergy_ge`: `E_L ≥ -(B² + 1/4)` with `B` independent of `L ≥ 2π`;
* `approx_torus_prod`: the approximate torus ground states in the form used by
  `free_grid_exponentialU_prod`;
* **`free_energy_upper`**: unconditionally (no (A)), for `L ≥ L₀`,
  `E_L + C₀ ≤ E_∞ + C' e^{-αL/2}`, and `E_{N,L} + C₀ ≤ E_∞ + C' e^{-αL/2} + C K^{-3}` for `K ≥ K₀`;
* **`free_energy_endpoint`**: eq:free-energy, under (A): for `L ≥ L₀`,
  `|E_L + C₀ - E_∞| ≤ C' e^{-γL}` and `|E_{N,L} + C₀ - E_∞| ≤ C' e^{-γL} + C K^{-3}` for all
  `K ≥ K₀`, `γ = min(α, β/2)/2`;
* **`free_energy_complexity`**: the basis size `N = O(ε⁻¹ log³(1/ε))`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15
  molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The constants -/

/-- The cell size from which the unconditional upper bound holds. -/
def freeUpperL0 (R0 ρ w α A : ℝ) : ℝ :=
  max (2 * Real.pi) (4 * (R0 + ρ + w + Real.log (4 * max A 1) / (2 * α)))

/-- The constant `C'` of the unconditional upper bound. -/
def freeUpperConst (eta : ℕ) (R0 ρ w α A : ℝ) : ℝ :=
  (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * (2 * max A 1) *
    Real.exp (2 * α * (R0 + ρ + w))

/-- The cell size `L₀` from which eq:free-energy holds. -/
def freeEnergyL0 (R0 ρ w α A β A' : ℝ) : ℝ :=
  max (freeUpperL0 R0 ρ w α A) (4 * (R0 + ρ + 2 * w + Real.log (4 * max A' 1) / β))

/-- The constant `C'` of eq:free-energy. -/
def freeEnergyConst (eta : ℕ) (R0 ρ w α A β A' : ℝ) : ℝ :=
  (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 *
    max (2 * max A 1) (2 * max A' 1 * Real.exp (β * w)) *
    Real.exp (2 * max α (β / 2) * (R0 + ρ + w))

/-- The rate `γ = min(α, β/2)/2` of eq:free-energy. -/
def freeEnergyRate (α β : ℝ) : ℝ := min α (β / 2) / 2

/-- The energy budget `max(|E_∞| + C' + Q/4, B² + 1/4) + 1` of the unconditional upper bound
(`B = gLmassConstU`, the `L`-free mass-weighted coupling constant). -/
def freeUpperBudget (sys : CoulombSystem eta ν) (V Einf C' : ℝ) : ℝ :=
  max (|Einf| + C' + zeroWeight sys / 4)
    (PlaneWaveGridG.gLmassConstU sys V molecularCanonicalUnitHardyConstant ^ 2 + 1 / 4) + 1

/-- The energy budget `|E_∞| + C' + Q/4 + 1` for the grid constants. -/
def freeEnergyBudget (sys : CoulombSystem eta ν) (Einf C' : ℝ) : ℝ :=
  |Einf| + C' + zeroWeight sys / 4 + 1

lemma freeUpperConst_nonneg (eta : ℕ) (R0 ρ w α A : ℝ) : 0 ≤ freeUpperConst eta R0 ρ w α A := by
  unfold freeUpperConst
  have : 0 ≤ 2 * max A 1 := by have := le_max_right A 1; linarith
  positivity

lemma freeEnergyConst_nonneg (eta : ℕ) (R0 ρ w α A β A' : ℝ) :
    0 ≤ freeEnergyConst eta R0 ρ w α A β A' := by
  unfold freeEnergyConst
  have : 0 ≤ max (2 * max A 1) (2 * max A' 1 * Real.exp (β * w)) :=
    le_trans (by have := le_max_right A 1; linarith) (le_max_left _ _)
  positivity

/-- The consequences of `L ≥ L₀` for the Agmon part. -/
lemma freeUpperL0_facts {R0 ρ w α A L : ℝ} (hα : 0 < α) (hL : freeUpperL0 R0 ρ w α A ≤ L) :
    2 * Real.pi ≤ L ∧ w < retainedRadius L R0 ρ ∧
      2 * max A 1 * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))) ≤ 1 / 2 := by
  have h1 : 2 * Real.pi ≤ L := le_trans (le_max_left _ _) hL
  have h2 : 4 * (R0 + ρ + w + Real.log (4 * max A 1) / (2 * α)) ≤ L :=
    le_trans (le_max_right _ _) hL
  have hM : 1 ≤ max A 1 := le_max_right _ _
  have hlog : 0 < Real.log (4 * max A 1) := Real.log_pos (by linarith)
  have hd : Real.log (4 * max A 1) / (2 * α) ≤ retainedRadius L R0 ρ - w := by
    unfold retainedRadius
    linarith
  have hq : 0 < Real.log (4 * max A 1) / (2 * α) := by positivity
  refine ⟨h1, by linarith, ?_⟩
  have hx : Real.log (4 * max A 1) ≤ 2 * α * (retainedRadius L R0 ρ - w) := by
    rw [div_le_iff₀ (by positivity)] at hd
    linarith
  have he : 4 * max A 1 ≤ Real.exp (2 * α * (retainedRadius L R0 ρ - w)) := by
    calc 4 * max A 1 = Real.exp (Real.log (4 * max A 1)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hx
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-- The consequences of `L ≥ L₀` for assumption (A). -/
lemma freeEnergyL0_facts {R0 ρ w α A β A' L : ℝ} (hβ : 0 < β)
    (hL : freeEnergyL0 R0 ρ w α A β A' ≤ L) :
    2 * max A' 1 * Real.exp (β * w) * Real.exp (-(2 * (β / 2) * (retainedRadius L R0 ρ - w))) ≤
      1 / 2 := by
  have h2 : 4 * (R0 + ρ + 2 * w + Real.log (4 * max A' 1) / β) ≤ L :=
    le_trans (le_max_right _ _) hL
  have hM : 1 ≤ max A' 1 := le_max_right _ _
  have hd : Real.log (4 * max A' 1) / β ≤ retainedRadius L R0 ρ - w - w := by
    unfold retainedRadius
    linarith
  have hx : Real.log (4 * max A' 1) ≤ β * (retainedRadius L R0 ρ - w - w) := by
    rw [div_le_iff₀ hβ] at hd
    linarith
  have he : 4 * max A' 1 ≤ Real.exp (β * (retainedRadius L R0 ρ - w - w)) := by
    calc 4 * max A' 1 = Real.exp (Real.log (4 * max A' 1)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hx
  have e : Real.exp (β * w) * Real.exp (-(2 * (β / 2) * (retainedRadius L R0 ρ - w))) =
      (Real.exp (β * (retainedRadius L R0 ρ - w - w)))⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  rw [mul_assoc, e, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-! ## The unconditional upper bound -/

/-- **A lower bound for the torus ground energy, uniform in `L ≥ 2π`**: `E_L ≥ -(B² + 1/4)`,
`B = gLmassConstU sys V_θ H_unit` (the mass-weighted relative bound of the `g_L` potential). -/
theorem gLTorusGroundEnergy_ge (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} {L R : ℝ}
    {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L) (hθ : Profile R θ) {E : ℝ}
    (hE : IsGLTorusGroundEnergy sys lab L θ E) :
    -(PlaneWaveGridG.gLmassConstU sys (tv R θ) molecularCanonicalUnitHardyConstant ^ 2 + 1 / 4) ≤
      E := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  set B := sys.massCouplingWeight * ((1 + tv R θ) * FSNormal.tB (coulombCellAmplitude L ^ 2)
    molecularCanonicalUnitHardyConstant (2 * Real.pi / L)) with hB
  have hB0 : 0 ≤ B := mul_nonneg sys.massCouplingWeight_nonneg
    (mul_nonneg (by linarith [hθ.tv_nonneg]) (FSNormal.tB_nonneg _ _ _))
  have hBU : B = PlaneWaveGridG.gLmassConstU sys (tv R θ) molecularCanonicalUnitHardyConstant := by
    rw [hB, PlaneWaveGridG.tB_gL_eq hL molecularCanonicalUnitHardyConstant_nonneg]
    rfl
  rw [← hBU]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, u, -, hn, hlt⟩ := hE.2 ε hε
  have hmpos : ∀ a, 0 < sys.mass a := fun a => sys.mass_pos a
  have h := diagHamiltonian_form_lower_bound_of_weightedBound
    (massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n))
    (fun p => massKineticSymbol_nonneg hmpos _ p) (gLpot sys L θ n) hB0
    (gLpot_massBound sys hL0 hθ molecularCanonicalUnitHardyConstant
      canonicalPeriodicCoulombHardyBound_explicit n) u
  rw [hn] at h
  change -(B ^ 2 + 1 / 4) * 1 ^ 2 ≤ (inner ℂ u (gLham sys L θ n u)).re at h
  linarith

/-- **`prop:free`, the unconditional upper bound, manuscript form.** For the molecule (nuclei at
`P_ℓ ∈ B_{R₀}(0)`) in cells of size `L ≥ L₀`, range-truncation profiles `θ` of range `R ≤ L/2`
with `θ ≡ 1` on `[0, L/2 - ρ]` and total variation `V`, and a free-space ground state `ψ_∞`
(`H_∞ ψ_∞ = E_∞ ψ_∞`, `‖ψ_∞‖ = 1`, in the sector, `E_∞` bounding the energy form below on the
sector) with Agmon decay `Σ_i ∫ e^{2α|x_i|} |ψ_∞|² ≤ A`: the torus ground energy satisfies
`E_L + C₀ ≤ E_∞ + C' e^{-αL/2}`, and for `m ≥ η + 8` with `K = 2πm/L ≥ K₀` the grid ground energy
satisfies `E_{N,L} + C₀ ≤ E_∞ + C' e^{-αL/2} + C K^{-3}`. `L₀`, `C'`, `K₀`, `C` do not depend on
`L` (`K₀`, `C` are those of `thm:grid-energy` at the budget `freeUpperBudget`, which bounds
`|E_L| + 1` by `gLTorusGroundEnergy_ge` and the upper bound). -/
theorem free_energy_upper (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
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
    {L R V : ℝ} {θ : ℝ → ℝ} (hL : freeUpperL0 R0 ρ w α A ≤ L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) (hV : tv R θ = V) :
    ∃ EL : ℝ, IsGLTorusGroundEnergy (sysAt sys P L) lab L θ EL ∧
      EL + (zeroModeShift (sysAt sys P L) L θ).re ≤
        Einf + freeUpperConst eta R0 ρ w α A * Real.exp (-(α / 2 * L)) ∧
      ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys V
          (freeUpperBudget sys V Einf (freeUpperConst eta R0 ρ w α A)) ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy (sysAt sys P L) lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L V)
              (PlaneWaveGridG.gLref L θ V) m) Eg ∧
          Eg + (zeroModeShift (sysAt sys P L) L θ).re ≤
            Einf + freeUpperConst eta R0 ρ w α A * Real.exp (-(α / 2 * L)) +
              PlaneWaveGridG.gLErrorConstU sys V
                (freeUpperBudget sys V Einf (freeUpperConst eta R0 ρ w α A)) /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  subst hV
  obtain ⟨hL2, hwL, hsmall⟩ := freeUpperL0_facts hα hL
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL2
  set d := retainedRadius L R0 ρ - w with hd
  set τ := 2 * max A 1 * Real.exp (-(2 * α * d)) with hτ
  have hτ0 : 0 ≤ τ := by have := le_max_right A 1; positivity
  have happrox := approx_ground_agmon sys P lab hH hn hS hα.le hAi hA d
  obtain ⟨EL, hEL, hgrid⟩ := PlaneWaveGridG.gLSectorGridErrorU (sysAt sys P L) lab hlab hL2 hθ
  have hup := free_upper_agmon_prod (sysAt sys P L) hL0 hθ hR hR0 hρ hone P hP (fun l => rfl) hEL
    hw hwL (τ := τ) (by linarith) hlow happrox
  -- the rate
  have hrate : (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * τ / (2 * (1 - τ)) ≤
      freeUpperConst eta R0 ρ w α A * Real.exp (-(α / 2 * L)) := by
    have hK0 : 0 ≤ (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 := by positivity
    have h1 : (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * τ / (2 * (1 - τ)) ≤
        (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * τ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (half_ratio_le hτ0 hsmall) hK0
    refine h1.trans (le_of_eq ?_)
    rw [hτ, hd, freeUpperConst, mul_assoc _ (Real.exp _), ← Real.exp_add]
    unfold retainedRadius
    ring_nf
  have hEup : EL + (zeroModeShift (sysAt sys P L) L θ).re ≤
      Einf + freeUpperConst eta R0 ρ w α A * Real.exp (-(α / 2 * L)) := by linarith
  -- the energy budget
  have hC0 := freeUpperConst_nonneg eta R0 ρ w α A
  have hexp1 : Real.exp (-(α / 2 * L)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ α / 2 * L := by positivity
    linarith
  have hCe : freeUpperConst eta R0 ρ w α A * Real.exp (-(α / 2 * L)) ≤
      freeUpperConst eta R0 ρ w α A := by
    have := mul_le_mul_of_nonneg_left hexp1 hC0
    rwa [mul_one] at this
  have hz : |(zeroModeShift (sysAt sys P L) L θ).re| ≤ zeroWeight sys / 4 :=
    (Complex.abs_re_le_norm _).trans (norm_zeroModeShift_le (sysAt sys P L) hL2 hθ hR)
  have hlo := gLTorusGroundEnergy_ge (sysAt sys P L) hL2 hθ hEL
  have hEb : |EL| + 1 ≤ freeUpperBudget sys (tv R θ) Einf (freeUpperConst eta R0 ρ w α A) := by
    unfold freeUpperBudget
    have h1 : EL ≤ |Einf| + freeUpperConst eta R0 ρ w α A + zeroWeight sys / 4 := by
      have := le_abs_self Einf
      have := neg_abs_le (zeroModeShift (sysAt sys P L) L θ).re
      linarith
    have h2 : -EL ≤ PlaneWaveGridG.gLmassConstU sys (tv R θ)
        molecularCanonicalUnitHardyConstant ^ 2 + 1 / 4 := by
      have : -(PlaneWaveGridG.gLmassConstU sys (tv R θ) molecularCanonicalUnitHardyConstant ^ 2 +
          1 / 4) ≤ EL := hlo
      linarith
    have h3 : |EL| ≤ max (|Einf| + freeUpperConst eta R0 ρ w α A + zeroWeight sys / 4)
        (PlaneWaveGridG.gLmassConstU sys (tv R θ) molecularCanonicalUnitHardyConstant ^ 2 +
          1 / 4) := by
      rw [abs_le]
      constructor
      · linarith [le_max_right (|Einf| + freeUpperConst eta R0 ρ w α A + zeroWeight sys / 4)
          (PlaneWaveGridG.gLmassConstU sys (tv R θ) molecularCanonicalUnitHardyConstant ^ 2 +
            1 / 4)]
      · linarith [le_max_left (|Einf| + freeUpperConst eta R0 ρ w α A + zeroWeight sys / 4)
          (PlaneWaveGridG.gLmassConstU sys (tv R θ) molecularCanonicalUnitHardyConstant ^ 2 +
            1 / 4)]
    linarith
  refine ⟨EL, hEL, hEup, fun m hm hK => ?_⟩
  obtain ⟨Eg, hEg, herr⟩ := hgrid _ hEb m hm hK
  refine ⟨Eg, hEg, ?_⟩
  have h : Eg - EL ≤ PlaneWaveGridG.gLErrorConstU sys (tv R θ)
      (freeUpperBudget sys (tv R θ) Einf (freeUpperConst eta R0 ρ w α A)) /
      ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := (abs_le.mp herr).2
  linarith

/-! ## eq:free-energy -/

/-- The approximate torus ground states of `approx_torus_agmon` in the form used by
`free_grid_exponentialU_prod`: mass `≤ 2 max(A', 1) e^{βw} e^{-βd}` outside the product region of
radius `d = R_L - w` (from `e^{-2β(d - R_{L/2})}`, `R_L - R_{L/2} = L/8`). -/
theorem approx_torus_prod (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ) {L R R0 ρ w : ℝ}
    {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (u : MolecularFourierH2 eta)
    (huS : IsSectorCoeff sys.sign lab (molecularH2Coeff (2 * Real.pi / L) u))
    (hun : ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ = 1) {EL : ℝ}
    (hu : H u = (EL : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) u) {β A' : ℝ} (hβ : 0 ≤ β)
    (hA' : ∑ i, ∫ x, Real.exp (2 * β * (‖particle (cellCoord L x) i‖ -
        retainedRadius (L / 2) R0 ρ)) *
      ‖molecularPositionH2StateMap eta (2 * Real.pi / L) u x‖ ^ 2 ≤ A') :
    ∀ ε > 0, ∃ v : C(MolecularPositionTorus eta, ℂ), ∃ hv : ContDiff ℝ 2 (torusRealLift v),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, v (molecularPositionSwap i j x) = sys.sign i * v x) ∧
      ∫ x, ‖v x‖ ^ 2 = 1 ∧ torusEnergy sys L θ v hv ≤ EL + ε ∧
      ∫ x in {x | ∀ i, ‖particle (cellCoord L x) i‖ < retainedRadius L R0 ρ - w}ᶜ,
        ‖v x‖ ^ 2 ≤ 2 * max A' 1 * Real.exp (β * w) *
          Real.exp (-(2 * (β / 2) * (retainedRadius L R0 ρ - w))) := by
  intro ε hε
  have hEu := le_of_eq (h2Form_of_eigen H (2 * Real.pi / L) hu hun)
  obtain ⟨v, hv, hvS, hvn, hvE, hvT⟩ := approx_torus_agmon sys lab hL hθ hR H hKernel u huS hun
    hEu hβ hA' (retainedRadius L R0 ρ - w) ε hε
  refine ⟨v, hv, hvS, hvn, hvE, hvT.trans ?_⟩
  rw [mul_assoc (2 * max A' 1), ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (by have := le_max_right A' 1; positivity)
  unfold retainedRadius
  nlinarith [mul_nonneg hβ (add_nonneg hR0 hρ)]


/-- **`prop:free`, eq:free-energy, manuscript form.** As `free_energy_upper`, and for the torus
ground state `u_L` (`H²` coordinates `u`, `H u_L = E_L u_L` for the completed `g_L` operator `H`,
`‖u_L‖ = 1`, in the sector) assumption (A): `Σ_i ∫ e^{2β(|x_i| - R_{L/2})} |u_L|² ≤ A'`. Then
for `L ≥ L₀`: `|E_L + C₀ - E_∞| ≤ C' e^{-γL}`, and for `m ≥ η + 8` with `K = 2πm/L ≥ K₀`, the
grid ground energy satisfies `|E_{N,L} + C₀ - E_∞| ≤ C' e^{-γL} + C K^{-3}`, with
`γ = min(α, β/2)/2`. `L₀`, `C'`, `γ`, `K₀` and `C` do not depend on `L`. -/
theorem free_energy_endpoint (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
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
    {L R V : ℝ} {θ : ℝ → ℝ} (hL : freeEnergyL0 R0 ρ w α A β A' ≤ L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) (hV : tv R θ = V)
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
        PlaneWaveGridG.gLKThresholdU sys V
          (freeEnergyBudget sys Einf (freeEnergyConst eta R0 ρ w α A β A')) ≤
            (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy (sysAt sys P L) lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L V)
              (PlaneWaveGridG.gLref L θ V) m) Eg ∧
          |Eg + (zeroModeShift (sysAt sys P L) L θ).re - Einf| ≤
            freeEnergyConst eta R0 ρ w α A β A' * Real.exp (-(freeEnergyRate α β * L)) +
              PlaneWaveGridG.gLErrorConstU sys V
                (freeEnergyBudget sys Einf (freeEnergyConst eta R0 ρ w α A β A')) /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  subst hV
  obtain ⟨hL2, hwL, hsmall⟩ := freeUpperL0_facts hα (le_trans (le_max_left _ _) hL)
  have hsmall' := freeEnergyL0_facts hβ hL
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have happrox := approx_ground_agmon sys P lab hH hn hS hα.le hAi hA (retainedRadius L R0 ρ - w)
  have hA2 := approx_torus_prod (sysAt sys P L) lab (w := w) hL0 hθ hR hR0 hρ H hKernel u huS hun
    hu hβ.le hA'
  obtain ⟨h1, h2⟩ := free_grid_exponentialU_prod (sysAt sys P L) lab hlab hL2 hθ hR hR0 hρ hone
    P hP (fun l => rfl) hw hwL hEL hα.le (by positivity : (0 : ℝ) ≤ β / 2) hsmall hsmall' hlow
    happrox hA2
  have hrate : Real.exp (-(min α (β / 2) * L / 2)) = Real.exp (-(freeEnergyRate α β * L)) := by
    unfold freeEnergyRate
    ring_nf
  have hC : (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 *
      max (2 * max A 1) (2 * max A' 1 * Real.exp (β * w)) *
      Real.exp (2 * max α (β / 2) * (R0 + ρ + w)) * Real.exp (-(min α (β / 2) * L / 2)) =
      freeEnergyConst eta R0 ρ w α A β A' * Real.exp (-(freeEnergyRate α β * L)) := by
    rw [hrate]
    rfl
  rw [hC] at h1 h2
  have hC'0 := freeEnergyConst_nonneg eta R0 ρ w α A β A'
  have hexp1 : Real.exp (-(freeEnergyRate α β * L)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have h0 : 0 ≤ freeEnergyRate α β := by
      unfold freeEnergyRate
      have := lt_min hα (half_pos hβ)
      positivity
    have : 0 ≤ freeEnergyRate α β * L := mul_nonneg h0 hL0.le
    linarith
  have hEL1 : |EL + (zeroModeShift (sysAt sys P L) L θ).re - Einf| ≤
      freeEnergyConst eta R0 ρ w α A β A' := by
    refine h1.trans ?_
    have := mul_le_mul_of_nonneg_left hexp1 hC'0
    rwa [mul_one] at this
  have hz : |(zeroModeShift (sysAt sys P L) L θ).re| ≤ zeroWeight sys / 4 :=
    (Complex.abs_re_le_norm _).trans (norm_zeroModeShift_le (sysAt sys P L) hL2 hθ hR)
  have hEb : |EL| + 1 ≤ freeEnergyBudget sys Einf (freeEnergyConst eta R0 ρ w α A β A') := by
    unfold freeEnergyBudget
    have habs : |EL| ≤ |EL + (zeroModeShift (sysAt sys P L) L θ).re - Einf| +
        |(zeroModeShift (sysAt sys P L) L θ).re| + |Einf| := by
      have := abs_add_le (EL + (zeroModeShift (sysAt sys P L) L θ).re - Einf)
        (Einf - (zeroModeShift (sysAt sys P L) L θ).re)
      rw [show EL + (zeroModeShift (sysAt sys P L) L θ).re - Einf +
          (Einf - (zeroModeShift (sysAt sys P L) L θ).re) = EL by ring] at this
      have h3 := abs_sub Einf (zeroModeShift (sysAt sys P L) L θ).re
      linarith
    linarith
  exact ⟨h1, fun m hm hK => h2 _ hEb m hm hK⟩

/-! ## The basis-size complexity -/

/-- **`prop:free`, the complexity statement, manuscript form** (`N = O(ε⁻¹ log³(1/ε))`). For the
molecule in the cells of size `L ≥ L₀` (`L₀ ≥` the `L₀` of eq:free-energy), with
range-truncation profiles `θ_L` of range `R_L ≤ L/2`, `θ_L ≡ 1` on `[0, L/2 - ρ]` and fixed
total variation `V`; the free-space ground state with Agmon decay as in `free_energy_upper`; and
for every such `L` a torus ground state `u_L` with assumption (A) with the same `β`, `A'`: there
is `D` such that for every `0 < ε ≤ 1/2` some cell size `L ≥ L₀` and register radius `2m`
(`N = (4m + 1)³` grid points per particle) with `N ≤ D ε⁻¹ log³(1/ε)` give
`|E_{N,L} + C₀ - E_∞| ≤ ε`. -/
theorem free_energy_complexity (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
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
    {R : ℝ → ℝ} {θ : ℝ → ℝ → ℝ} {V L₀ : ℝ} (hL₀ : freeEnergyL0 R0 ρ w α A β A' ≤ L₀)
    (hfam : ∀ L, L₀ ≤ L → Profile (R L) (θ L) ∧ R L ≤ L / 2 ∧
      (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ L r = 1) ∧ tv (R L) (θ L) = V)
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
          (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L V)
            (PlaneWaveGridG.gLref L (θ L) V) m) Eg ∧
        |Eg + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf| ≤ ε := by
  obtain ⟨hL2, hwL, hsmall⟩ := freeUpperL0_facts hα (le_trans (le_max_left _ _) hL₀)
  have hsmall' := freeEnergyL0_facts hβ hL₀
  have hA0 : 0 ≤ 2 * max A 1 := by have := le_max_right A 1; linarith
  have hA'0 : 0 ≤ 2 * max A' 1 * Real.exp (β * w) := by have := le_max_right A' 1; positivity
  refine free_grid_complexity_prod sys lab hlab hR0 hρ hw P hP hL2 hwL hfam hα (half_pos hβ) hA0
    hA'0 hsmall hsmall' hlow (fun d _ => approx_ground_agmon sys P lab hH hn hS hα.le hAi hA d) ?_
  intro L hL EL hEL
  obtain ⟨hθ, hR, -, -⟩ := hfam L hL
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) (le_trans hL2 hL)
  obtain ⟨H, u, hKernel, huS, hun, hu, hA'⟩ := hgs L hL EL hEL
  exact approx_torus_prod (sysAt sys P L) lab (w := w) hL0 hθ hR hR0 hρ H hKernel u huS hun hu
    hβ.le hA'

end

end FreeBoundary
