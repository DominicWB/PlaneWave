import PlaneWave.KineticLog.OpenCompat

/-!
# Logarithmic kinetic bound, part 28: `prop:free-kinetic-log` with the explicit cutoffs

The compatible-cutoff corollaries of `prop:free-kinetic-log` for the explicit cutoffs of
`prop:free-dyn`, with one constant for every `L ≥ L₀`:

* **`free_kinetic_log_nbo_uniform`** (no clamped nuclei): the mass-weighted cutoff
  `χ_L = F(Σ_i m_i |x_i|²/(L/8)²)` (`quadCutoffL`), leakage measured outside
  `Σ_i m_i |x_i|² < (L/8)²` and on the shell `(L/8)² ≤ Σ_i m_i |x_i|² ≤ 2 (L/8)²`;
* **`free_kinetic_log_bo_uniform`** (clamped nuclei, equal moving masses): the product cutoff
  `prodCutoffL`, leakage outside `max_i |x_i| < L/16` and on `L/16 ≤ max_i |x_i| ≤ L/8`; the
  molecule sits in the cell of size `L` (`sysAt sys P L`).

The cutoff shapes are fixed (`quadCutoff8`, `prodCutoff16`), so the derivative and cancellation
bounds, and hence the constants, do not depend on `L`. The thresholds are those of `prop:free-dyn`
without an observable radius.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter MeasureTheory Set PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic PlaneWaveGrid
  PlaneWaveGridDynamics FreeBoundary FSNormal

namespace KineticLog

attribute [local instance] FreeBoundary.unitAddCircleMeasureSpaceFB15
  FreeBoundary.unitAddCircleProbabilityMeasureFB15 FreeBoundary.molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- The threshold `L₀ = max(8, 2π, 1, 16(R₀ + ρ))` of the mass-weighted cutoff. -/
noncomputable def freeKinL0 (R0 ρ : ℝ) : ℝ := freeDynL0 R0 ρ 0

/-- The threshold `L₀ = max(16, 1, 16(R₀ + ρ + δ))` of the product cutoff. -/
noncomputable def freeKinBOL0 (R0 ρ δ : ℝ) : ℝ := freeDynBOL0 R0 ρ 0 δ

set_option maxHeartbeats 400000 in
/-- **`prop:free-kinetic-log` without clamped nuclei, uniform in `L`**: for `L ≥ L₀`, every
profile with `V_θ = V`, the explicit mass-weighted cutoff and its leakage regions,
`‖ψ₀‖ + ‖H_∞ψ₀‖ + ‖H_∞²ψ₀‖ ≤ 𝒟`, every `m ≥ 8` with `K = 2πm/L ≥ K₀`, every kernel of the class and
every grid propagator,
`|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C 𝒟² [1 + t + log(2 + K)]/K³ + C 𝒟 (1 + t) ε`,
with `C = freeKinConstNBO sys V D_s C_s` (`D_s`, `C_s` the bounds of the fixed shape) and
`K₀ = cellK0 sys V`. -/
theorem free_kinetic_log_nbo_uniform [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ V : ℝ}
    (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) {L R : ℝ} {θ : ℝ → ℝ} (hL : freeKinL0 R0 ρ ≤ L)
    (hθ : Profile R θ) (hR : R ≤ L / 2) (hV : tv R θ = V)
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
  subst hV
  have h8 := eight_le_of_freeDynL0 hL
  have hL2 := two_pi_le_of_freeDynL0 hL
  have hS : MeasurableSet {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2} :=
    (measurableSet_le measurable_const
      (contDiff_massQ sys.mass (n := 0)).continuous.measurable).inter
      (measurableSet_le (contDiff_massQ sys.mass (n := 0)).continuous.measurable measurable_const)
  have hB : MeasurableSet {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2} :=
    measurableSet_lt (contDiff_massQ sys.mass (n := 0)).continuous.measurable measurable_const
  have hSB : {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r ∧ massQ sys.mass r ≤ 2 * (L / 8) ^ 2} ⊆
      {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2}ᶜ := fun r hr h => by
    simp only [Set.mem_setOf_eq] at hr h
    linarith [hr.1]
  have hc : {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2}ᶜ =
      {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r} := by
    ext r
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  have hret : ∀ r, (quadCutoffL sys.one_le_mass h8).χ r ≠ 0 →
      ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ := fun r hr i =>
    (quadCutoffL_ret sys.one_le_mass h8 r hr i).trans (ret_of_freeDynL0 hL)
  exact free_kinetic_log_nbo sys hL2 hθ hR hR0 hρ hone P hP hpos (quadCutoffL sys.one_le_mass h8)
    hret (quadCutoffL_D_le sys.one_le_mass h8) (quadCutoffL_C_le sys.one_le_mass h8) hS hB
    (quadCutoffL_one sys.one_le_mass h8) hSB
    (fun r hr a => (quadCutoffL_derivs sys.one_le_mass h8 r hr a).1)
    (fun r hr a => (quadCutoffL_derivs sys.one_le_mass h8 r hr a).2) hψd hHam hgrad ht hε
    (fun s hs => by rw [hc]; exact hleak0 s hs) hleak1 hH1 hD p₀ m hm hK hκ Ug hg0 hgcomm hgderiv

set_option maxHeartbeats 400000 in
/-- **`prop:free-kinetic-log` with clamped nuclei and equal moving masses, uniform in `L`**: the
molecule (nuclei at `P_ℓ ∈ B_{R₀}(0)`) in the cell of size `L ≥ L₀` (`sysAt sys P L`), the explicit
product cutoff flat within `δ` of the nuclei, `‖ψ₀‖ + ‖H_∞ψ₀‖ + ‖H_∞²ψ₀‖ ≤ 𝒟`:
`|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C 𝒟² [1 + t + log(2 + K)]/K³ + C 𝒟 (1 + t) ε`,
`C = freeKinConstBO sys V D_s C_s δ`. -/
theorem free_kinetic_log_bo_uniform (sys : CoulombSystem eta ν) {m₀ : ℝ}
    (hmass : ∀ i, sys.mass i = m₀) (hm0 : 1 ≤ m₀) {V R0 ρ δ : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hδ : 0 < δ) (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0) {L R : ℝ} {θ : ℝ → ℝ}
    (hL : freeKinBOL0 R0 ρ δ ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hV : tv R θ = V)
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
  subst hV
  have h16 := sixteen_le_of_freeDynBOL0 hL
  have hL2 := two_pi_le_of_freeDynBOL0 hL
  have hS : MeasurableSet {r : Rcfg eta | (∃ i, L / 16 ≤ ‖particle r i‖) ∧
      ∀ i, ‖particle r i‖ ≤ L / 8} := by
    rw [Set.setOf_and, Set.setOf_exists, Set.setOf_forall]
    exact (MeasurableSet.iUnion fun i => measurableSet_le measurable_const
      (continuous_norm_particle i).measurable).inter
      (MeasurableSet.iInter fun i => measurableSet_le (continuous_norm_particle i).measurable
        measurable_const)
  have hB : MeasurableSet {r : Rcfg eta | ∀ i, ‖particle r i‖ < L / 16} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt (continuous_norm_particle i).measurable measurable_const
  have hSB : {r : Rcfg eta | (∃ i, L / 16 ≤ ‖particle r i‖) ∧ ∀ i, ‖particle r i‖ ≤ L / 8} ⊆
      {r : Rcfg eta | ∀ i, ‖particle r i‖ < L / 16}ᶜ := by
    rintro r ⟨⟨i, hi⟩, -⟩ h
    exact absurd (h i) (not_lt.mpr hi)
  have hc : {r : Rcfg eta | ∀ i, ‖particle r i‖ < L / 16}ᶜ =
      {r : Rcfg eta | ∃ i, L / 16 ≤ ‖particle r i‖} := by
    ext r
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt]
  have hret : ∀ r, (prodCutoffL hmass hm0 h16).χ r ≠ 0 →
      ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ := fun r hr i =>
    (prodCutoffL_ret hmass hm0 h16 r hr i).trans (ret_of_freeDynBOL0 hδ.le hL)
  have hflat : IsFlatNear (prodCutoffL hmass hm0 h16).χ P δ :=
    prodCutoffL_isFlatNear hmass hm0 h16 P (flat_of_freeDynBOL0 hρ hL hP)
  exact free_kinetic_log_bo (sysAt sys P L) hL2 hθ hR hR0 hρ hone P hP (fun l => rfl)
    (prodCutoffL hmass hm0 h16) hret hδ hflat (prodCutoffL_D_le hmass hm0 h16)
    (prodCutoffL_C_le hmass hm0 h16) hS hB (prodCutoffL_one hmass hm0 h16) hSB
    (fun r hr a => (prodCutoffL_derivs hmass hm0 h16 r hr a).1)
    (fun r hr a => (prodCutoffL_derivs hmass hm0 h16 r hr a).2) hψd hHam hgrad ht hε
    (fun s hs => by rw [hc]; exact hleak0 s hs) hleak1 hH1 hD p₀ m hm8 hK hκ Ug hg0 hgcomm hgderiv

end KineticLog
