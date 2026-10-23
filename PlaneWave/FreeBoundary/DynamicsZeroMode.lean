import PlaneWave.FreeBoundary.DynamicsVbar
import PlaneWave.KineticLog.OpenZeroMode
import PlaneWave.KineticLog.PeriodicMasses

/-!
# `prop:free-dyn` for the physical Hamiltonians: the zero mode kept

The physical cell Hamiltonian keeps the zero Fourier coefficient of `g_L`,
`H_L = H_L^{(0)} + C_zm` (eq:free-zero-mode), and so does the grid kernel of the isolated system
(`KineticLog.IsGridKernelZ`, `κ(0) = ĝ_L(0)`). The endpoints of `prop:free-dyn` in
`PlaneWave.FreeBoundary` are stated for `H_L^{(0)}` (`HasGLHamiltonian`) and kernels with
`κ(0) = 0`; this file states them for the physical Hamiltonians, with `V_θ ≤ V̄`.

**The grid.** For an even kernel the position-space grid Hamiltonian satisfies
`G[κ] = G[κ⁰] + κ(0) z_g` (`Hpos_update`, from `KineticLog.Hgrid_update` through the DFT), and it
is symmetric (`Hpos_isSymmetric`). Hence every propagator of `G[κ]` is a phase times every
propagator of `G[κ⁰]` (`posProp_phase`, by `KineticLog.propagator_phase` and uniqueness,
`KineticLog.ode_unique`); for a kernel of the class eq:free-kinetic-kernel the phase is
`e^{-itC_zm}`, the phase of the cell (`posProp_phase_zeroMode`, from
`KineticLog.gridZero_eq_zeroModeShift`). The grid observable `⟨ψ_g, O_g ψ_g⟩` is phase invariant
(`inner_unit_smul_lin`).

**The cell.** A propagator `U_Z` of the physical `H_L` gives the propagator
`U(t) = e^{itC_zm} U_Z(t)` of `H_L^{(0)}` (`cell_unphase`), and the free-space step of
`prop:free-dyn` holds in the manuscript's form `‖φ(t) - e^{-itH_L} φ(0)‖ ≤ C ε t`
(`free_dyn_torus_phys`; with spin, `free_dyn_torus_spin_phys`). The domain condition (H_dom)
for the physical `H_L` with budget `𝒟` gives (H_dom) for `H_L^{(0)}` with budget
`(1 + Q/4)² 𝒟` (`budget_zero_mode_each`).

**The endpoints**, for every propagator `U_g` of the physical grid Hamiltonian and every kernel of
the class eq:free-kinetic-kernel:

* `free_dyn_endpoint_phys`, `free_dyn_uniform_phys`: (H_dom) for the physical `H_L` with budget
  `𝒟`; the constant `freeDynConst sys V̄ F D̄ ((1 + Q/4)² 𝒟)`;
* `free_dyn_nbo_endpoint_phys`, `free_dyn_grid_bo_phys`, `free_dyn_nbo_uniform_phys`,
  `free_dyn_bo_uniform_phys`: the domain condition is proved from the free-space data, so only
  the grid changes and the constants are those of the `_vbar` forms;
* `free_dyn_nbo_spin_endpoint_phys`, `free_dyn_bo_spin_endpoint_phys`,
  `free_dyn_nbo_spin_uniform_phys`, `free_dyn_bo_spin_uniform_phys`: internal spin.

The hypotheses can be met: the physical grid and cell propagators exist
(`exists_posPropagatorZ`, `exists_gLPropagatorZ'`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLref)

namespace FreeBoundary

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15
  molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Phase invariance -/

section Phase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `⟨e y, G (e y)⟩ = ⟨y, G y⟩` for `|e| = 1` and a linear `G`. -/
lemma inner_unit_smul_lin (G : E →ₗ[ℂ] E) {e : ℂ} (he : ‖e‖ = 1) (y : E) :
    ⟪e • y, G (e • y)⟫_ℂ = ⟪y, G y⟫_ℂ := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', he]
  simp

/-- The bound for a phase-shifted state. -/
lemma bound_of_phase {A : ℂ} {x y : E} {G : E →ₗ[ℂ] E} {e : ℂ} (he : ‖e‖ = 1) (hxy : x = e • y)
    {B : ℝ} (h : ‖A - ⟪y, G y⟫_ℂ‖ ≤ B) : ‖A - ⟪x, G x⟫_ℂ‖ ≤ B := by
  rw [hxy, inner_unit_smul_lin G he]
  exact h

/-- The bound for phase-shifted spin components (one phase for all components). -/
lemma bound_of_phase_spin {ς : Type*} [Fintype ς] {A : ℂ} {x y : ς → E} {G : E →ₗ[ℂ] E}
    {e : ℂ} (he : ‖e‖ = 1) (hxy : ∀ σ, x σ = e • y σ) {B : ℝ}
    (h : ‖A - ∑ σ, ⟪y σ, G (y σ)⟫_ℂ‖ ≤ B) : ‖A - ∑ σ, ⟪x σ, G (x σ)⟫_ℂ‖ ≤ B := by
  simp only [hxy, inner_unit_smul_lin G he]
  exact h

end Phase

/-! ## The physical grid Hamiltonian -/

section Grid

variable {m : ℕ}

omit [Fintype ν] in
lemma update_zero_even {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x) (x : Lat3) :
    Function.update κ 0 0 (-x) = Function.update κ 0 0 x := by
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : -x ≠ 0 := neg_ne_zero.mpr hx
    rw [Function.update_of_ne hx', Function.update_of_ne hx, hκe]

lemma Hpos_apply_eq (P : RegParticles eta) (N : PosNuclei ν) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x) (g : ℝ) (u : EuclideanSpace ℂ (RCfg eta m)) :
    Hpos (m := m) P N κ g u = idft (Hgrid eta m P N.toNucData κ g (dft u)) := by
  rw [← dft_Hpos P N hκe g u, idft_dft]

/-- **The grid zero mode is a scalar, in position space**: `G[κ] = G[κ⁰] + κ(0) z_g`. -/
lemma Hpos_update (P : RegParticles eta) (N : PosNuclei ν) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x) (g : ℝ) :
    Hpos (m := m) P N κ g = Hpos P N (Function.update κ 0 0) g +
      ((κ 0 : ℂ) * KineticLog.gridZeroWeight P N.toNucData) • LinearMap.id := by
  apply LinearMap.ext
  intro u
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, Hpos_apply_eq P N hκe,
    Hpos_apply_eq P N (update_zero_even hκe), KineticLog.Hgrid_update P N.toNucData κ g,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul, idft_dft]

/-- The position-space grid Hamiltonian of an even kernel is symmetric. -/
lemma Hpos_isSymmetric (P : RegParticles eta) (N : PosNuclei ν) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x) (g : ℝ) : (Hpos (m := m) P N κ g).IsSymmetric := by
  intro u v
  have h1 := inner_dft_dft (Hpos (m := m) P N κ g u) v
  have h2 := inner_dft_dft u (Hpos (m := m) P N κ g v)
  rw [dft_Hpos P N hκe] at h1 h2
  rw [← h1, ← h2]
  exact Hgrid_isSymmetric hκe (dft u) (dft v)

/-- **The phase of the grid propagator**: for an even kernel `κ`, every propagator `U_g` of
`G[κ]` is `e^{-iκ(0) z_g t}` times every propagator `U_g⁰` of `G[κ⁰]`. -/
theorem posProp_phase (P : RegParticles eta) (N : PosNuclei ν) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x) (g : ℝ)
    (Ug Ug0 : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x) (hgcomm : ∀ t x, Ug t (Hpos P N κ g x) = Hpos P N κ g (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos P N κ g x))) t)
    (hg00 : ∀ x, Ug0 0 x = x)
    (hgcomm0 : ∀ t x, Ug0 t (Hpos P N (Function.update κ 0 0) g x) =
      Hpos P N (Function.update κ 0 0) g (Ug0 t x))
    (hgderiv0 : ∀ t x, HasDerivAt (fun s => Ug0 s x)
      (-(Complex.I • Ug0 t (Hpos P N (Function.update κ 0 0) g x))) t) (t : ℝ) :
    ∀ x, Ug t x = Complex.exp (Complex.I * (-((κ 0 : ℂ) * KineticLog.gridZeroWeight P
      N.toNucData)) * t) • Ug0 t x := by
  intro x
  set c : ℂ := (κ 0 : ℂ) * KineticLog.gridZeroWeight P N.toNucData with hcdef
  have hc : c.im = 0 := by
    rw [hcdef, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
      KineticLog.gridZeroWeight_im]
    ring
  obtain ⟨U0, hU, h0, hcomm, hderiv⟩ := KineticLog.propagator_phase _ _ hc
    (Hpos_update P N hκe g) Ug hg0 hgcomm hgderiv
  have hsym := Hpos_isSymmetric (m := m) P N (update_zero_even hκe) g
  have key : U0 t x = Ug0 t x := by
    refine KineticLog.ode_unique (Hpos P N (Function.update κ 0 0) g) hsym
      (x := fun s => U0 s x) (y := fun s => Ug0 s x) (fun s => ?_) (fun s => ?_) ?_ t
    · have h := hderiv s x
      rw [hcomm] at h
      exact h
    · have h := hgderiv0 s x
      rw [hgcomm0] at h
      exact h
    · rw [h0, hg00]
  rw [hU] at key
  have hinv : Complex.exp (Complex.I * (-c) * t) * Complex.exp (Complex.I * c * t) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  calc Ug t x = (Complex.exp (Complex.I * (-c) * t) * Complex.exp (Complex.I * c * t)) • Ug t x :=
        by rw [hinv, one_smul]
    _ = Complex.exp (Complex.I * (-c) * t) • (Complex.exp (Complex.I * c * t) • Ug t x) := by
        rw [smul_smul]
    _ = Complex.exp (Complex.I * (-c) * t) • Ug0 t x := by rw [key]

/-- The phase is a unit. -/
lemma norm_gridPhase (P : RegParticles eta) (N : PosNuclei ν) (κ : Lat3 → ℝ) (t : ℝ) :
    ‖Complex.exp (Complex.I * (-((κ 0 : ℂ) * KineticLog.gridZeroWeight P N.toNucData)) * t)‖ =
      1 := by
  refine KineticLog.norm_cexp_I_mul_real ?_ t
  rw [Complex.neg_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    KineticLog.gridZeroWeight_im]
  ring

/-- **The grid phase is the cell phase**: for a kernel of the class eq:free-kinetic-kernel,
every propagator of the physical grid Hamiltonian is `e^{-itC_zm}` times every propagator of the
zero-mode-free one (`κ(0) z_g = C_zm`), the phase of the cell propagator
(`KineticLog.cell_phase`). -/
theorem posProp_phase_zeroMode (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
    (hθ : Profile R θ) {V : ℝ} {κ : Lat3 → ℝ} (hκ : KineticLog.IsGridKernelZ L θ V m κ)
    (Ug Ug0 : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L)
      x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (regParticlesOf sys)
      (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t)
    (hg00 : ∀ x, Ug0 0 x = x)
    (hgcomm0 : ∀ t x, Ug0 t (Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei)
      (Function.update κ 0 0) (2 * Real.pi / L) x) = Hpos (regParticlesOf sys)
      (posNucleiOf sys.nuclei) (Function.update κ 0 0) (2 * Real.pi / L) (Ug0 t x))
    (hgderiv0 : ∀ t x, HasDerivAt (fun s => Ug0 s x) (-(Complex.I • Ug0 t (Hpos (regParticlesOf
      sys) (posNucleiOf sys.nuclei) (Function.update κ 0 0) (2 * Real.pi / L) x))) t) (t : ℝ)
    (x : EuclideanSpace ℂ (RCfg eta m)) :
    Ug t x = Complex.exp (Complex.I * (-zeroModeShift sys L θ) * t) • Ug0 t x := by
  rw [posProp_phase _ _ hκ.even _ Ug Ug0 hg0 hgcomm hgderiv hg00 hgcomm0 hgderiv0 t x, hκ.zero,
    KineticLog.gridZero_eq_zeroModeShift sys hθ L]

/-- **Propagators of the physical grid Hamiltonian exist**: the kernels of the class
eq:free-kinetic-kernel are even (`exists_posPropagator`). -/
theorem exists_posPropagatorZ (sys : CoulombSystem eta ν) {L : ℝ} {θ : ℝ → ℝ} {V : ℝ}
    {κ : Lat3 → ℝ} (hκ : KineticLog.IsGridKernelZ L θ V m κ) (g : ℝ) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧
      (∀ t x, Ug t (Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ g x) =
        Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ g (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ g x))) t) := by
  obtain ⟨Ug, -, -, -, -, -, h0, -, -, hcomm, hderiv⟩ :=
    exists_posPropagator (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) hκ.even g
  exact ⟨fun t => posConj (Ug t), h0, hcomm, hderiv⟩

end Grid

/-! ## The physical cell Hamiltonian -/

section Cell

variable {sys : CoulombSystem eta ν} {L : ℝ} {θ : ℝ → ℝ}

/-- **(H_dom) across the zero mode**: if `H_L φ₀ = h₀` and `H_L h₀ = h₁` for the physical `H_L`
(zero mode kept), with `‖φ₀‖, ‖h₀‖, ‖h₁‖ ≤ 𝒟` and `|C_zm| ≤ c`, then `H_L^{(0)} φ₀ = h₀'` and
`H_L^{(0)} h₀' = h₁'` with `‖h₀'‖, ‖h₁'‖ ≤ (1 + c)² 𝒟`. -/
theorem budget_zero_mode_each {φ₀ h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : KineticLog.HasGLHamiltonianZ sys L θ φ₀ h₀)
    (hdom1 : KineticLog.HasGLHamiltonianZ sys L θ h₀ h₁) {c : ℝ}
    (hc : ‖zeroModeShift sys L θ‖ ≤ c) {𝒟 : ℝ} (hn0 : ‖φ₀‖ ≤ 𝒟) (hn1 : ‖h₀‖ ≤ 𝒟)
    (hn2 : ‖h₁‖ ≤ 𝒟) :
    ∃ h₀' h₁' : MolecularPositionL2 eta, HasGLHamiltonian sys L θ φ₀ h₀' ∧
      HasGLHamiltonian sys L θ h₀' h₁' ∧ ‖h₀'‖ ≤ (1 + c) ^ 2 * 𝒟 ∧ ‖h₁'‖ ≤ (1 + c) ^ 2 * 𝒟 := by
  set C := zeroModeShift sys L θ with hC
  have A := KineticLog.hasGLHamiltonianZ_iff.mp hdom0
  have B := KineticLog.hasGLHamiltonianZ_iff.mp hdom1
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hc
  have h𝒟 : 0 ≤ 𝒟 := (norm_nonneg _).trans hn0
  have n0 : ‖h₀ - C • φ₀‖ ≤ ‖h₀‖ + c * ‖φ₀‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul]
    have := mul_le_mul_of_nonneg_right hc (norm_nonneg φ₀)
    linarith
  have n1 : ‖(h₁ - C • h₀) - C • (h₀ - C • φ₀)‖ ≤ ‖h₁‖ + 2 * c * ‖h₀‖ + c ^ 2 * ‖φ₀‖ := by
    refine (norm_sub_le _ _).trans ?_
    have a1 : ‖h₁ - C • h₀‖ ≤ ‖h₁‖ + c * ‖h₀‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul]
      have := mul_le_mul_of_nonneg_right hc (norm_nonneg h₀)
      linarith
    have a2 : ‖C • (h₀ - C • φ₀)‖ ≤ c * (‖h₀‖ + c * ‖φ₀‖) := by
      rw [norm_smul]
      exact mul_le_mul hc n0 (norm_nonneg _) hc0
    nlinarith
  refine ⟨h₀ - C • φ₀, (h₁ - C • h₀) - C • (h₀ - C • φ₀), A, B.sub sys (A.smul sys C), ?_, ?_⟩
  · have e1 := mul_le_mul_of_nonneg_left hn0 hc0
    nlinarith
  · have e1 := mul_le_mul_of_nonneg_left hn0 (sq_nonneg c)
    have e2 := mul_le_mul_of_nonneg_left hn1 (by positivity : (0 : ℝ) ≤ 2 * c)
    nlinarith

/-- **From the physical cell propagator to the zero-mode-free one**: if `U_Z` is a strongly
continuous unitary group solving `i ∂_t u = H_L u` for the physical `H_L`, then
`U(t) = e^{itC_zm} U_Z(t)` is one for `H_L^{(0)}`. -/
theorem cell_unphase {R : ℝ} (hθ : Profile R θ)
    (UZ : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hUZ0 : ∀ ψ, UZ 0 ψ = ψ)
    (hUZadd : ∀ s t ψ, UZ (s + t) ψ = UZ s (UZ t ψ)) (hUZcont : ∀ ψ, Continuous fun t => UZ t ψ)
    (hUZderiv : ∀ t f h, KineticLog.HasGLHamiltonianZ sys L θ f h →
      HasDerivAt (fun s => UZ s f) (-(Complex.I • UZ t h)) t) :
    ∃ U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      (∀ t f, U t f = Complex.exp (Complex.I * zeroModeShift sys L θ * t) • UZ t f) ∧
      (∀ ψ, U 0 ψ = ψ) ∧ (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, Continuous fun t => U t ψ) ∧
      (∀ t f h, HasGLHamiltonian sys L θ f h →
        HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) := by
  have hC0 : (zeroModeShift sys L θ).im = 0 := by
    have h := zeroModeShift_re_eq sys hθ L
    rw [← h, Complex.ofReal_im]
  set C := zeroModeShift sys L θ with hCdef
  refine ⟨fun s => (UZ s).trans (KineticLog.phaseLIE (Complex.exp (Complex.I * C * s))
    (KineticLog.norm_cexp_I_mul_real hC0 s)), fun t f => rfl, ?_, ?_, ?_, ?_⟩
  · intro ψ
    change Complex.exp (Complex.I * C * ((0 : ℝ) : ℂ)) • UZ 0 ψ = ψ
    rw [hUZ0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
  · intro s t ψ
    change Complex.exp (Complex.I * C * ((s + t : ℝ) : ℂ)) • UZ (s + t) ψ =
      Complex.exp (Complex.I * C * s) • UZ s (Complex.exp (Complex.I * C * t) • UZ t ψ)
    rw [hUZadd, LinearIsometryEquiv.map_smul, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · intro ψ
    change Continuous fun t : ℝ => Complex.exp (Complex.I * C * t) • UZ t ψ
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul
      (hUZcont ψ)
  · intro t f h hfh
    change HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * C * s) • UZ s f)
      (-(Complex.I • (Complex.exp (Complex.I * C * t) • UZ t h))) t
    have hZ : KineticLog.HasGLHamiltonianZ sys L θ f (h + C • f) := by
      rw [KineticLog.hasGLHamiltonianZ_iff]
      have e : h + C • f - C • f = h := by abel
      rw [e]
      exact hfh
    have hd : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * C * s))
        (Complex.exp (Complex.I * C * t) * (Complex.I * C)) t := by
      have h1 : HasDerivAt (fun s : ℝ => Complex.I * C * (s : ℂ)) (Complex.I * C * 1) t :=
        (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * C)
      rw [mul_one] at h1
      exact h1.cexp
    have hD := hd.smul (hUZderiv t f _ hZ)
    have e2 : Complex.exp (Complex.I * C * t) • -(Complex.I • UZ t (h + C • f)) +
        (Complex.exp (Complex.I * C * t) * (Complex.I * C)) • UZ t f =
        -(Complex.I • (Complex.exp (Complex.I * C * t) • UZ t h)) := by
      rw [map_add, LinearIsometryEquiv.map_smul]
      module
    rw [e2] at hD
    exact hD

/-- **A strongly continuous unitary group of the physical `H_L` exists**: `e^{-itC_zm}` times the
propagator of `H_L^{(0)}` (`exists_gLPropagator`, `KineticLog.cell_phase`). -/
theorem exists_gLPropagatorZ' {R : ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2) :
    ∃ UZ : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      (∀ ψ, UZ 0 ψ = ψ) ∧ (∀ s t ψ, UZ (s + t) ψ = UZ s (UZ t ψ)) ∧
      (∀ ψ, Continuous fun t => UZ t ψ) ∧
      (∀ t f h, KineticLog.HasGLHamiltonianZ sys L θ f h →
        KineticLog.HasGLHamiltonianZ sys L θ (UZ t f) (UZ t h)) ∧
      (∀ t f h, KineticLog.HasGLHamiltonianZ sys L θ f h →
        HasDerivAt (fun s => UZ s f) (-(Complex.I • UZ t h)) t) := by
  obtain ⟨U, hU0, hUadd, hUcont, hgraphU, hderivU, -⟩ := exists_gLPropagator (sys := sys) hL hθ hR
  obtain ⟨UZ, hUZ, h0, hg, hd⟩ := KineticLog.cell_phase hθ U hU0 hgraphU hderivU
  refine ⟨UZ, h0, fun s t ψ => ?_, fun ψ => ?_, hg, hd⟩
  · rw [hUZ, hUZ, hUZ, hUadd, LinearIsometryEquiv.map_smul, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · simp only [hUZ]
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul
      (hUcont ψ)

/-- **`prop:free-dyn`, the free-space step, for the physical `H_L`**: for every strongly continuous
unitary group `U_Z = e^{-itH_L}` of the physical cell Hamiltonian (zero mode kept), under (H_leak),
`‖T(χψ_∞(t)) - e^{-itH_L} T(χψ_∞(0))‖ ≤ C ε t`, and the multiplier-observable comparison
`≤ ε² + (‖ψ_∞(t)‖ + ‖ψ_∞(0)‖) C ε t`, with `C` the commutator constant of the cutoff; the phase
`e^{-itC₀}` of `free_dyn_torus` is absorbed in the propagator. -/
theorem free_dyn_torus_phys (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hθ : Profile R θ) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (UZ : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta)
    (hUZ0 : ∀ ψ, UZ 0 ψ = ψ) (hUZadd : ∀ s t ψ, UZ (s + t) ψ = UZ s (UZ t ψ))
    (hUZcont : ∀ ψ, Continuous fun t => UZ t ψ)
    (hUZderiv : ∀ t f h, KineticLog.HasGLHamiltonianZ sys L θ f h →
      HasDerivAt (fun s => UZ s f) (-(Complex.I • UZ t h)) t)
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
    ‖X.chiW.cutL2 hL (ψ t) - UZ t (X.chiW.cutL2 hL (ψ 0))‖ ≤ X.commConst * ε * t ∧
      ‖((∫ r, χo r * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - inner ℂ (UZ t (X.chiW.cutL2 hL (ψ 0)))
          (PlaneWaveDynamics.mulCLM G (UZ t (X.chiW.cutL2 hL (ψ 0))))‖ ≤
        ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.commConst * ε * t) := by
  obtain ⟨U, hU, hU0, hUadd, hUcont, hUderiv⟩ := cell_unphase hθ UZ hUZ0 hUZadd hUZcont hUZderiv
  obtain ⟨h1, h2⟩ := free_dyn_torus sys hL hθ hR0 hρ hone P hP hpos U hU0 hUadd hUcont hUderiv X
    hret hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hχo0 hχo1 hχom G hG
  have hC := zeroModeShift_re_eq sys hθ L
  have hC0 : (zeroModeShift sys L θ).im = 0 := by rw [← hC, Complex.ofReal_im]
  have hUZ : ∀ f, Complex.exp (-(Complex.I * ((zeroModeShift sys L θ).re : ℂ) * t)) • U t f =
      UZ t f := by
    intro f
    rw [hU, smul_smul, hC, ← Complex.exp_add]
    have e : -(Complex.I * zeroModeShift sys L θ * t) + Complex.I * zeroModeShift sys L θ * t =
        0 := by ring
    rw [e, Complex.exp_zero, one_smul]
  refine ⟨?_, ?_⟩
  · rw [← hUZ]
    exact h1
  · rw [hU, inner_unit_smul _ (KineticLog.norm_cexp_I_mul_real hC0 t)] at h2
    exact h2

/-- **The free-space step with internal spin, for the physical `H_L`**: the statement of
`free_dyn_torus_spin` for every strongly continuous unitary group `U_Z = e^{-itH_L}` of the
physical cell Hamiltonian, acting on each spin component; the phase `e^{-itC₀}` is absorbed in the
propagator. -/
theorem free_dyn_torus_spin_phys (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hθ : Profile R θ) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (UZ : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta)
    (hUZ0 : ∀ ψ, UZ 0 ψ = ψ) (hUZadd : ∀ s t ψ, UZ (s + t) ψ = UZ s (UZ t ψ))
    (hUZcont : ∀ ψ, Continuous fun t => UZ t ψ)
    (hUZderiv : ∀ t f h, KineticLog.HasGLHamiltonianZ sys L θ f h →
      HasDerivAt (fun s => UZ s f) (-(Complex.I • UZ t h)) t)
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
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
    {χo : Rcfg eta → ℝ} (hχo0 : ∀ r, 0 ≤ χo r) (hχo1 : ∀ r, χo r ≤ 1) (hχom : Measurable χo)
    (G : C(MolecularPositionTorus eta, ℂ)) (hG : ∀ x, G x = (χo (cellCoord L x) : ℂ)) :
    ‖piLpMap (X.chiW.cutL2 hL) (Ψ t) - spinIso UZ t (piLpMap (X.chiW.cutL2 hL) (Ψ 0))‖ ≤
        X.commConst * ε * t ∧
      ‖((∑ σ, ∫ r, χo r * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) - ∑ σ, ⟪UZ t (X.chiW.cutL2 hL (Ψ 0 σ)),
          PlaneWaveDynamics.mulCLM G (UZ t (X.chiW.cutL2 hL (Ψ 0 σ)))⟫_ℂ‖ ≤
        ε ^ 2 + (‖Ψ t‖ + ‖Ψ 0‖) * (X.commConst * ε * t) := by
  obtain ⟨U, hU, hU0, hUadd, hUcont, hUderiv⟩ := cell_unphase hθ UZ hUZ0 hUZadd hUZcont hUZderiv
  obtain ⟨h1, h2⟩ := free_dyn_torus_spin sys hL hθ hR0 hρ hone P hP hpos U hU0 hUadd hUcont
    hUderiv X hret hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hχo0 hχo1 hχom G
    hG
  have hC := zeroModeShift_re_eq sys hθ L
  have hC0 : (zeroModeShift sys L θ).im = 0 := by rw [← hC, Complex.ofReal_im]
  have hUZ : ∀ x : PiLp 2 (fun _ : ς => MolecularPositionL2 eta),
      Complex.exp (-(Complex.I * ((zeroModeShift sys L θ).re : ℂ) * t)) • spinIso U t x =
        spinIso UZ t x := by
    intro x
    refine PiLp.ext fun σ => ?_
    rw [PiLp.smul_apply, spinIso_apply, spinIso_apply, hU, smul_smul, hC, ← Complex.exp_add]
    have e : -(Complex.I * zeroModeShift sys L θ * t) + Complex.I * zeroModeShift sys L θ * t =
        0 := by ring
    rw [e, Complex.exp_zero, one_smul]
  refine ⟨?_, ?_⟩
  · rw [← hUZ]
    exact h1
  · simp only [hU, inner_unit_smul _ (KineticLog.norm_cexp_I_mul_real hC0 t)] at h2
    exact h2

end Cell

/-! ## The endpoints for the physical Hamiltonians -/

section Endpoints

/-- **`prop:free-dyn` (any system, (H_dom) for the physical `H_L` with budget `𝒟`) for the physical
Hamiltonians**: the statement of `free_dyn_endpoint_vbar` with the zero modes kept, for every kernel
of the class eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator `U_g` of the physical
grid Hamiltonian; the constant is taken at the budget `(1 + Q/4)² 𝒟` (`budget_zero_mode_each`). -/
theorem free_dyn_endpoint_phys (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    (hdom0 : KineticLog.HasGLHamiltonianZ sys L θ
      (X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)) h₀)
    (hdom1 : KineticLog.HasGLHamiltonianZ sys L θ h₀ h₁) {𝒟 : ℝ} (hψ0 : ‖ψ 0‖ ≤ 𝒟)
    (hn0 : ‖X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)‖ ≤ 𝒟) (hn1 : ‖h₀‖ ≤ 𝒟)
    (hn2 : ‖h₁‖ ≤ 𝒟)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : KineticLog.IsGridKernelZ L θ (tv R θ) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
      (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L)
      (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
      (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) :
    let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
    let φ₀ := X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
    let K : ℝ := (2 * Real.pi / L) * m
    let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
    ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
      freeDynConst sys Vbar F Dbar ((1 + zeroWeight sys / 4) ^ 2 * 𝒟) *
          ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
        freeDynConst sys Vbar F Dbar ((1 + zeroWeight sys / 4) ^ 2 * 𝒟) * (1 + t) * ε := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hv0 := hθ.tv_nonneg
  have hc := norm_zeroModeShift_le sys hL2 hθ hR
  obtain ⟨h₀', h₁', hd0', hd1', hn1', hn2'⟩ := budget_zero_mode_each hdom0 hdom1 hc hn0 hn1 hn2
  have h𝒟 : 0 ≤ 𝒟 := (norm_nonneg _).trans hψ0
  have ha : 𝒟 ≤ (1 + zeroWeight sys / 4) ^ 2 * 𝒟 :=
    le_mul_of_one_le_left h𝒟 (one_le_pow₀ (by have := zeroWeight_nonneg sys; linarith))
  obtain ⟨Ug0, hg00, -, -, hgcomm0, hgderiv0, hbound⟩ := free_dyn_endpoint_vbar sys hL2 hθ hR hR0
    hρ hone hVbar P hP hpos X hret hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hε1
    hleak0 hleak1 hd0' hd1' (hψ0.trans ha) (hn0.trans ha) hn1' hn2' a hf0 hf1 F hFf hfR hRL m
    (hκ.zeroed hL0 hv0) hm hK
  intro χ φ₀ K ψg
  exact bound_of_phase (norm_gridPhase _ _ κ t)
    (posProp_phase _ _ hκ.even _ Ug Ug0 hg0 hgcomm hgderiv hg00 hgcomm0 hgderiv0 t _) hbound

/-- **`prop:free-dyn` (no clamped nuclei, the domain condition proved) for the physical
Hamiltonians**: the statement of `free_dyn_nbo_endpoint_vbar` with the zero modes kept, for every
kernel of the class eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator `U_g` of the
physical grid Hamiltonian; the constant is that of `free_dyn_nbo_endpoint_vbar`. -/
theorem free_dyn_nbo_endpoint_phys [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ}
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
    (hκ : KineticLog.IsGridKernelZ L θ (tv R θ) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
      (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L)
      (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
      (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) :
    let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
    let φ₀ := X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
    let K : ℝ := (2 * Real.pi / L) * m
    let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
    ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
      freeDynConstNBO sys Vbar F Dbar Cbar D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
        freeDynConstNBO sys Vbar F Dbar Cbar D * (1 + t) * ε := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hv0 := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, -, -, hgcomm0, hgderiv0, hbound⟩ := free_dyn_nbo_endpoint_vbar sys hL2 hθ hR
    hR0 hρ hone hVbar P hP hpos X hret hDbar hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε
    hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR hRL m (hκ.zeroed hL0 hv0) hm hK
  intro χ φ₀ K ψg
  exact bound_of_phase (norm_gridPhase _ _ κ t)
    (posProp_phase _ _ hκ.even _ Ug Ug0 hg0 hgcomm hgderiv hg00 hgcomm0 hgderiv0 t _) hbound

/-- **`prop:free-dyn` (clamped nuclei, the domain condition proved) for the physical Hamiltonians**:
the statement of `free_dyn_grid_bo_vbar` with the zero modes kept, for every kernel of the class
eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator `U_g` of the physical grid
Hamiltonian; the constant is that of `free_dyn_grid_bo_vbar`. -/
theorem free_dyn_grid_bo_phys (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    (hκ : KineticLog.IsGridKernelZ L θ (tv R θ) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
      (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L)
      (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
      (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) :
    let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
    let φ₀ := X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
    let K : ℝ := (2 * Real.pi / L) * m
    let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
    ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
      freeDynConstBO sys Vbar F Dbar Cbar δ D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
        freeDynConstBO sys Vbar F Dbar Cbar δ D * (1 + t) * ε := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hv0 := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, -, -, hgcomm0, hgderiv0, hbound⟩ := free_dyn_grid_bo_vbar sys hL2 hθ hR hR0
    hρ hone hVbar P hP hpos X hret hδ hflat hDbar hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht
    hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR hRL m (hκ.zeroed hL0 hv0) hm hK
  intro χ φ₀ K ψg
  exact bound_of_phase (norm_gridPhase _ _ κ t)
    (posProp_phase _ _ hκ.even _ Ug Ug0 hg0 hgcomm hgderiv hg00 hgcomm0 hgderiv0 t _) hbound

/-- **`prop:free-dyn` (uniform in `L`, (H_dom) for the physical `H_L` with budget `𝒟`) for the
physical Hamiltonians**: the statement of `free_dyn_uniform_vbar` with the zero modes kept, for
every kernel of the class eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator `U_g` of the
physical grid Hamiltonian; the constant is taken at the budget `(1 + Q/4)² 𝒟`
(`budget_zero_mode_each`). -/
theorem free_dyn_uniform_phys (sys : CoulombSystem eta ν) {R0 ρ Rf Vbar : ℝ} (hR0 : 0 ≤ R0)
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
    (hdom0 : KineticLog.HasGLHamiltonianZ (sysAt sys P L) L θ ((quadCutoffL sys.one_le_mass
      (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2 (pos_of_freeDynL0 hL) (ψ 0)) h₀)
    (hdom1 : KineticLog.HasGLHamiltonianZ (sysAt sys P L) L θ h₀ h₁) {𝒟 : ℝ} (hψ0 : ‖ψ 0‖ ≤ 𝒟)
    (hn0 : ‖(quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
      (pos_of_freeDynL0 hL) (ψ 0)‖ ≤ 𝒟) (hn1 : ‖h₀‖ ≤ 𝒟) (hn2 : ‖h₁‖ ≤ 𝒟)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : KineticLog.IsGridKernelZ L θ (tv R θ) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
      (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
      (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ (2 * Real.pi / L) x))) t) :
    let χ := cellObs (pos_of_freeDynL0 hL) (continuous_of_schwartz F hFf) hfR
      (two_Rf_lt_of_freeDynL0 hL)
    let φ₀ := (quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
      (pos_of_freeDynL0 hL) (ψ 0)
    let K : ℝ := (2 * Real.pi / L) * m
    let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
    ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
      freeDynConst sys Vbar F (quadCutoff8 sys.one_le_mass).D
          ((1 + zeroWeight sys / 4) ^ 2 * 𝒟) * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
        freeDynConst sys Vbar F (quadCutoff8 sys.one_le_mass).D
          ((1 + zeroWeight sys / 4) ^ 2 * 𝒟) * (1 + t) * ε := by
  have hL0 : 0 < L := pos_of_freeDynL0 hL
  have hv0 := hθ.tv_nonneg
  have hc : ‖zeroModeShift (sysAt sys P L) L θ‖ ≤ zeroWeight sys / 4 :=
    norm_zeroModeShift_le (sysAt sys P L) (two_pi_le_of_freeDynL0 hL) hθ hR
  obtain ⟨h₀', h₁', hd0', hd1', hn1', hn2'⟩ := budget_zero_mode_each hdom0 hdom1 hc hn0 hn1 hn2
  have h𝒟 : 0 ≤ 𝒟 := (norm_nonneg _).trans hψ0
  have ha : 𝒟 ≤ (1 + zeroWeight sys / 4) ^ 2 * 𝒟 :=
    le_mul_of_one_le_left h𝒟 (one_le_pow₀ (by have := zeroWeight_nonneg sys; linarith))
  obtain ⟨Ug0, hg00, -, -, hgcomm0, hgderiv0, hbound⟩ := free_dyn_uniform_vbar sys hR0 hρ P hP hL
    hθ hR hVbar hone hψd hHam hgrad ht hε hε1 hleak0 hleak1 hd0' hd1' (hψ0.trans ha)
    (hn0.trans ha) hn1' hn2' a hf0 hf1 F hFf hfR m (hκ.zeroed hL0 hv0) hm hK
  intro χ φ₀ K ψg
  exact bound_of_phase (norm_gridPhase _ _ κ t)
    (posProp_phase _ _ hκ.even _ Ug Ug0 hg0 hgcomm hgderiv hg00 hgcomm0 hgderiv0 t _) hbound

/-- **`prop:free-dyn` (no clamped nuclei, uniform in `L`) for the physical Hamiltonians**: the
statement of `free_dyn_nbo_uniform_vbar` with the zero modes kept, for every kernel of the class
eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator `U_g` of the physical grid
Hamiltonian; the constant is that of `free_dyn_nbo_uniform_vbar`. -/
theorem free_dyn_nbo_uniform_phys [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ Rf Vbar : ℝ}
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
    (hκ : KineticLog.IsGridKernelZ L θ (tv R θ) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
      (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L)
      (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
      (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) :
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
  have hL0 : 0 < L := pos_of_freeDynL0 hL
  have hv0 := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, -, -, hgcomm0, hgderiv0, hbound⟩ := free_dyn_nbo_uniform_vbar sys hR0 hρ hL
    hθ hR hVbar hone P hP hpos hψd hHam hgrad ht hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR m
    (hκ.zeroed hL0 hv0) hm hK
  intro χ φ₀ K ψg
  exact bound_of_phase (norm_gridPhase _ _ κ t)
    (posProp_phase _ _ hκ.even _ Ug Ug0 hg0 hgcomm hgderiv hg00 hgcomm0 hgderiv0 t _) hbound

/-- **`prop:free-dyn` (clamped nuclei, equal masses, uniform in `L`) for the physical
Hamiltonians**: the statement of `free_dyn_bo_uniform_vbar` with the zero modes kept, for every
kernel of the class eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator `U_g` of the
physical grid Hamiltonian; the constant is that of `free_dyn_bo_uniform_vbar`. -/
theorem free_dyn_bo_uniform_phys {R0 ρ Rf δ L : ℝ}
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
    (hκ : KineticLog.IsGridKernelZ L θ (tv R θ) m κ)
    (hm8 : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
      (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
      (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ (2 * Real.pi / L) x))) t) :
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
  have hL0 : 0 < L := pos_of_freeDynBOL0 hL
  have hv0 := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, -, -, hgcomm0, hgderiv0, hbound⟩ := free_dyn_bo_uniform_vbar sys hm hm0 hR0
    hρ hδ P hP hL hθ hR hVbar hone hψd hHam hgrad ht hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf
    hfR m (hκ.zeroed hL0 hv0) hm8 hK
  intro χ φ₀ K ψg
  exact bound_of_phase (norm_gridPhase _ _ κ t)
    (posProp_phase _ _ hκ.even _ Ug Ug0 hg0 hgcomm hgderiv hg00 hgcomm0 hgderiv0 t _) hbound

/-- **`prop:free-dyn` (internal spin, no clamped nuclei) for the physical Hamiltonians**: the
statement of `free_dyn_nbo_spin_endpoint_vbar` with the zero modes kept, for every kernel of the
class eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator `U_g` of the physical grid
Hamiltonian; the constant is that of `free_dyn_nbo_spin_endpoint_vbar`. -/
theorem free_dyn_nbo_spin_endpoint_phys [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ}
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
    (hκ : KineticLog.IsGridKernelZ L θ (tv R θ) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
      (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L)
      (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
      (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) :
    let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
    let K : ℝ := (2 * Real.pi / L) * m
    let ψg : ς → EuclideanSpace ℂ (RCfg eta m) := fun σ => Ug t (idft (regCoeff m
      ((molecularPositionSynthesis eta).symm
        (X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (Ψ 0 σ)))))
    ‖((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
        ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ‖ ≤
      freeDynConstSpinNBO sys Vbar F Dbar Cbar D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
        freeDynConstSpinNBO sys Vbar F Dbar Cbar D * (1 + t) * ε := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hv0 := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, -, -, hgcomm0, hgderiv0, hbound⟩ := free_dyn_nbo_spin_endpoint_vbar sys hL2
    hθ hR hR0 hρ hone hVbar P hP hpos X hret hDbar hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad
    ht hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR hRL m (hκ.zeroed hL0 hv0) hm hK
  intro χ K ψg
  exact bound_of_phase_spin (norm_gridPhase _ _ κ t)
    (fun σ => posProp_phase _ _ hκ.even _ Ug Ug0 hg0 hgcomm hgderiv hg00 hgcomm0 hgderiv0 t _)
    hbound

/-- **`prop:free-dyn` (internal spin, clamped nuclei) for the physical Hamiltonians**: the statement
of `free_dyn_bo_spin_endpoint_vbar` with the zero modes kept, for every kernel of the class
eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator `U_g` of the physical grid
Hamiltonian; the constant is that of `free_dyn_bo_spin_endpoint_vbar`. -/
theorem free_dyn_bo_spin_endpoint_phys (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    (hκ : KineticLog.IsGridKernelZ L θ (tv R θ) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
      (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L)
      (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
      (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) :
    let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
    let K : ℝ := (2 * Real.pi / L) * m
    let ψg : ς → EuclideanSpace ℂ (RCfg eta m) := fun σ => Ug t (idft (regCoeff m
      ((molecularPositionSynthesis eta).symm
        (X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (Ψ 0 σ)))))
    ‖((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
        ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ‖ ≤
      freeDynConstSpinBO sys Vbar F Dbar Cbar δ D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
        freeDynConstSpinBO sys Vbar F Dbar Cbar δ D * (1 + t) * ε := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hv0 := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, -, -, hgcomm0, hgderiv0, hbound⟩ := free_dyn_bo_spin_endpoint_vbar sys hL2 hθ
    hR hR0 hρ hone hVbar P hP hpos X hret hδ hflat hDbar hCbar hSm hBm hχB hSB hdS hd2S hψd hHam
    hgrad ht hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf hfR hRL m (hκ.zeroed hL0 hv0) hm hK
  intro χ K ψg
  exact bound_of_phase_spin (norm_gridPhase _ _ κ t)
    (fun σ => posProp_phase _ _ hκ.even _ Ug Ug0 hg0 hgcomm hgderiv hg00 hgcomm0 hgderiv0 t _)
    hbound

/-- **`prop:free-dyn` (internal spin, no clamped nuclei, uniform in `L`) for the physical
Hamiltonians**: the statement of `free_dyn_nbo_spin_uniform_vbar` with the zero modes kept, for
every kernel of the class eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator `U_g` of the
physical grid Hamiltonian; the constant is that of `free_dyn_nbo_spin_uniform_vbar`. -/
theorem free_dyn_nbo_spin_uniform_phys [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ Rf Vbar : ℝ}
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
    (hκ : KineticLog.IsGridKernelZ L θ (tv R θ) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
      (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L)
      (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
      (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) :
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
  have hL0 : 0 < L := pos_of_freeDynL0 hL
  have hv0 := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, -, -, hgcomm0, hgderiv0, hbound⟩ := free_dyn_nbo_spin_uniform_vbar sys hR0 hρ
    hL hθ hR hVbar hone P hP hpos hψd hHam hgrad ht hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F hFf
    hfR m (hκ.zeroed hL0 hv0) hm hK
  intro χ K ψg
  exact bound_of_phase_spin (norm_gridPhase _ _ κ t)
    (fun σ => posProp_phase _ _ hκ.even _ Ug Ug0 hg0 hgcomm hgderiv hg00 hgcomm0 hgderiv0 t _)
    hbound

/-- **`prop:free-dyn` (internal spin, clamped nuclei, equal masses, uniform in `L`) for the physical
Hamiltonians**: the statement of `free_dyn_bo_spin_uniform_vbar` with the zero modes kept, for every
kernel of the class eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator `U_g` of the
physical grid Hamiltonian; the constant is that of `free_dyn_bo_spin_uniform_vbar`. -/
theorem free_dyn_bo_spin_uniform_phys (sys : CoulombSystem eta ν) {m₀ : ℝ}
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
    (hκ : KineticLog.IsGridKernelZ L θ (tv R θ) m κ)
    (hm8 : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
      (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
      (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ (2 * Real.pi / L) x))) t) :
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
  have hL0 : 0 < L := pos_of_freeDynBOL0 hL
  have hv0 := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, -, -, hgcomm0, hgderiv0, hbound⟩ := free_dyn_bo_spin_uniform_vbar sys hm hm0
    hR0 hρ hδ P hP hL hθ hR hVbar hone hψd hHam hgrad ht hε hε1 hleak0 hleak1 hH1 hD a hf0 hf1 F
    hFf hfR m (hκ.zeroed hL0 hv0) hm8 hK
  intro χ K ψg
  exact bound_of_phase_spin (norm_gridPhase _ _ κ t)
    (fun σ => posProp_phase _ _ hκ.even _ Ug Ug0 hg0 hgcomm hgderiv hg00 hgcomm0 hgderiv0 t _)
    hbound

end Endpoints

end FreeBoundary
