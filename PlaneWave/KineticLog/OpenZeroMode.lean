import PlaneWave.KineticLog.OpenVbar

/-!
# Logarithmic kinetic bound, part 37: the zero mode of the cell interaction

The physical cell Hamiltonian of Appendix H keeps the zero Fourier coefficient of `g_L`:
`H_L = H_L^{(0)} + C_zm I` (eq:free-zero-mode), `C_zm = ĝ_L(0) (Σ_{i<j} q_i q_j + Σ_{i,ℓ} q_i ζ_ℓ)`
(`zeroModeShift`), and so does the grid kernel of `prop:free-kinetic-log`, which preserves
`ĝ_L(0)` (eq:free-kinetic-kernel). Parts 26–36 state the isolated-system endpoints for
`H_L^{(0)}` (`HasGLHamiltonian`, zero mode removed) and for kernels with `κ(0) = 0`
(`PlaneWaveGridG.IsGridKernel`). This file completes the correspondence.

**The cell.**
* `gLFourierPotentialZ`, `HasGLHamiltonianZ`: the potential `V_L` with its zero mode and the
  physical relation `H_L f = h`; `gLFourierPotentialZ_eq`: `V_L = V_L^{(0)} + C_zm`;
* **`hasGLHamiltonianZ_iff`** (the scalar shift): `H_L f = h ⟺ H_L^{(0)} f = h - C_zm f`;
* **`cell_phase`**, `exists_gLPropagatorZ`, **`cell_phase_eq`** (the phase):
  `e^{-itH_L} = e^{-itC_zm} e^{-itH_L^{(0)}}`: `e^{-itC_zm}` times the propagator of `H_L^{(0)}`
  is a propagator of `H_L`, and every propagator of `H_L` is of this form on its domain;
* **`budget_zero_mode`**, `budget_zero_mode_spin`: the physical budget
  `D_* ≥ ‖φ₀‖ + ‖H_L φ₀‖ + ‖H_L² φ₀‖` gives the shifted one,
  `‖φ₀‖ + ‖H_L^{(0)} φ₀‖ + ‖(H_L^{(0)})² φ₀‖ ≤ (1 + Q/4)² D_*`, since `|C_zm| ≤ Q/4`.

**The grid.**
* `IsGridKernelZ`: the kernel class eq:free-kinetic-kernel (real, even, `κ(0) = ĝ_L(0)`, equal to
  `ĝ_L` for `0 < |k| ≤ K`, supported in the cube `2K`, Coulomb majorant off zero);
  `IsGridKernelZ.zeroed`, `IsGridKernelZ.ofIsGridKernel`: `κ ↦ κ⁰ = κ - κ(0) δ₀` matches it with
  the release's class; `isGridKernelZ_sharp`: the sharp truncation lies in it;
* **`Hgrid_update`**: the grid zero mode is a scalar, `G[κ] = G[κ⁰] + κ(0) z_g`, and
  `gridZero_eq_zeroModeShift`: `κ(0) z_g = C_zm` (both discretisations represent the same scalar);
* **`grid_phase`**: every propagator of `G[κ]` is `e^{-iκ(0) z_g t}` times a propagator of
  `G[κ⁰]`, with the same grid kinetic expectations (`regExpect_phase`).

**The endpoints for the physical Hamiltonians** (cell and grid zero modes kept, profile bound
`V_θ ≤ V̄`, threshold `cellK0 sys V̄`):
* with (H_dom) and the physical budget `D_*`, constant `freeKinCZ = (1 + Q/4)⁴ freeKinC sys V̄ D̄`:
  `free_kinetic_log_phys_endpoint`, `free_stopping_log_phys_endpoint`,
  `free_kinetic_log_N_phys_endpoint` and the spin forms; `free_kinetic_log_phys`,
  `free_kinetic_log_phys_at` (fixed molecule), `free_kinetic_log_spin_phys_at`,
  `free_stopping_log_phys_at`, `free_stopping_log_spin_phys_at` (the constants before the
  quantifiers);
* the compatible cutoffs `free_kinetic_log_nbo_phys`, `free_kinetic_log_bo_phys` and the explicit
  cutoffs `free_kinetic_log_nbo_uniform_phys`, `free_kinetic_log_bo_uniform_phys`, with their spin
  forms: the domain condition is proved there from the free-space data, so only the grid kernel
  and propagator change and the constants are those of the `_vbar` forms.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter MeasureTheory Set PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid
  PlaneWaveGridDynamics PlaneWaveKinetic FSNormal FreeBoundary

namespace KineticLog

attribute [local instance] FreeBoundary.unitAddCircleMeasureSpaceFB15
  FreeBoundary.unitAddCircleProbabilityMeasureFB15 FreeBoundary.molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The physical cell Hamiltonian -/

section Cell

variable (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)

/-- **The cell potential with its zero mode**: the charge-weighted `g_L` multiplication function
`V_L = Σ_{i<j} q_i q_j g_L(x_i - x_j) + Σ_{i,ℓ} q_i ζ_ℓ g_L(x_i + R_ℓ)` (release convention for the
nuclear positions), `g_L` keeping its zero Fourier coefficient. -/
noncomputable def gLFourierPotentialZ (x : MolecularPositionTorus eta) : ℂ :=
  (∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) *
      gLtorus L θ (molecularPositionDifference pair.1.1 pair.1.2 x)) +
    ∑ i : Fin eta, ((sys.charge i : ℝ) : ℂ) *
      ∑ ell : ν, (sys.nuclei.charge ell : ℂ) *
        gLtorus L θ (molecularPositionNuclearArgument i (sys.nuclei.position ell) x)

/-- `V_L = V_L^{(0)} + C_zm`. -/
lemma gLFourierPotentialZ_eq (x : MolecularPositionTorus eta) :
    gLFourierPotentialZ sys L θ x = gLFourierPotential sys L θ x + zeroModeShift sys L θ := by
  unfold gLFourierPotentialZ gLFourierPotential zeroModeShift gLtorus0
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- **The physical cell Hamiltonian relation** `H_L f = h`, `H_L` keeping the zero mode of `g_L`:
`V_L f ∈ L²` and `h - V_L f` is the weak kinetic image of `f`. -/
def HasGLHamiltonianZ (f h : MolecularPositionL2 eta) : Prop :=
  ∃ v : MolecularPositionL2 eta,
    HasL2PointwisePotential volume (gLFourierPotentialZ sys L θ) f v ∧
      HasCoulombContDiffWeakKinetic sys L f (h - v)

variable {sys L θ}

/-- **The scalar shift** (eq:free-zero-mode): `H_L f = h ⟺ H_L^{(0)} f = h - C_zm f`. -/
theorem hasGLHamiltonianZ_iff {f h : MolecularPositionL2 eta} :
    HasGLHamiltonianZ sys L θ f h ↔
      HasGLHamiltonian sys L θ f (h - zeroModeShift sys L θ • f) := by
  constructor
  · rintro ⟨v, hv, hk⟩
    refine ⟨v - zeroModeShift sys L θ • f, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_sub v (zeroModeShift sys L θ • f),
        Lp.coeFn_smul (zeroModeShift sys L θ) f, hv] with x e1 e2 e3
      rw [e1, Pi.sub_apply, e2, Pi.smul_apply, e3, smul_eq_mul, gLFourierPotentialZ_eq]
      ring
    · have e : h - zeroModeShift sys L θ • f - (v - zeroModeShift sys L θ • f) = h - v := by abel
      rw [e]
      exact hk
  · rintro ⟨v, hv, hk⟩
    refine ⟨v + zeroModeShift sys L θ • f, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_add v (zeroModeShift sys L θ • f),
        Lp.coeFn_smul (zeroModeShift sys L θ) f, hv] with x e1 e2 e3
      rw [e1, Pi.add_apply, e2, Pi.smul_apply, e3, smul_eq_mul, gLFourierPotentialZ_eq]
      ring
    · have e : h - (v + zeroModeShift sys L θ • f) = h - zeroModeShift sys L θ • f - v := by abel
      rw [e]
      exact hk

/-- **The graph-norm budget across the zero mode**: if `H_L φ₀ = h₀` and `H_L h₀ = h₁` (zero mode
kept) and `|C_zm| ≤ c`, then `H_L^{(0)} φ₀ = h₀'`, `H_L^{(0)} h₀' = h₁'` with
`‖φ₀‖ + ‖h₀'‖ + ‖h₁'‖ ≤ (1 + c)² (‖φ₀‖ + ‖h₀‖ + ‖h₁‖)`. -/
theorem budget_zero_mode {φ₀ h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonianZ sys L θ φ₀ h₀) (hdom1 : HasGLHamiltonianZ sys L θ h₀ h₁)
    {c : ℝ} (hc : ‖zeroModeShift sys L θ‖ ≤ c) :
    ∃ h₀' h₁' : MolecularPositionL2 eta, HasGLHamiltonian sys L θ φ₀ h₀' ∧
      HasGLHamiltonian sys L θ h₀' h₁' ∧
      ‖φ₀‖ + ‖h₀'‖ + ‖h₁'‖ ≤ (1 + c) ^ 2 * (‖φ₀‖ + ‖h₀‖ + ‖h₁‖) := by
  set C := zeroModeShift sys L θ with hC
  have A := hasGLHamiltonianZ_iff.mp hdom0
  have B := hasGLHamiltonianZ_iff.mp hdom1
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hc
  refine ⟨h₀ - C • φ₀, (h₁ - C • h₀) - C • (h₀ - C • φ₀), A, B.sub sys (A.smul sys C), ?_⟩
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
  have hp := norm_nonneg φ₀
  have hh0 := norm_nonneg h₀
  have hh1 := norm_nonneg h₁
  nlinarith [mul_nonneg hc0 hp, mul_nonneg hc0 hh0, mul_nonneg hc0 hh1,
    mul_nonneg (mul_nonneg hc0 hc0) hp, mul_nonneg (mul_nonneg hc0 hc0) hh0,
    mul_nonneg (mul_nonneg hc0 hc0) hh1]

end Cell

/-! ## The grid zero mode -/

section Grid

variable {m : ℕ}

/-- The zero-transfer coefficient of a term: `1` for a pair, `-ζ_ℓ φ_ℓ(0)` for a nucleus. -/
noncomputable def zt (D : NucData ν) : Term eta ν → ℂ
  | Sum.inl _ => 1
  | Sum.inr il => -(D.charge il.2 : ℂ) * D.phase il.2 0

/-- The zero-transfer weight `z_g = Σ_t c_t z_t` of the grid potential. -/
noncomputable def gridZeroWeight (P : RegParticles eta) (D : NucData ν) : ℂ :=
  ∑ t : Term eta ν, (P.tcoef t : ℂ) * zt D t

omit [Fintype ν] in
lemma gl_zero' {M : ℕ} : gl (0 : GMode (2 * M + 1)) = 0 := by
  funext c
  simp [gl]

omit [Fintype ν] in
lemma eq_of_gTau_zero {M : ℕ} {i : Fin eta} {q p : GConfig eta (2 * M + 1)}
    (h : gTau i q p = 0) : q i = p i := by
  have h' : gl (q i - p i) = gl (0 : GMode (2 * M + 1)) := by rw [gl_zero']; exact h
  exact sub_eq_zero.mp (gl_injective h')

omit [Fintype ν] in
lemma eq_of_gRel2 {M : ℕ} {i j : Fin eta} {q p : GConfig eta (2 * M + 1)}
    (hrel : gRel2 i j q p) (h : gTau i q p = 0) : q = p := by
  have hi := eq_of_gTau_zero h
  have hj : q j = p j := by
    have := hrel.2
    rw [hi] at this
    exact add_left_cancel this
  funext k
  by_cases hki : k = i
  · rw [hki]; exact hi
  by_cases hkj : k = j
  · rw [hkj]; exact hj
  exact hrel.1 k hki hkj

omit [Fintype ν] in
lemma eq_of_spec1 {M : ℕ} {i : Fin eta} {q p : GConfig eta (2 * M + 1)}
    (hrel : Spec1 i q p) (h : gTau i q p = 0) : q = p := by
  have hi := eq_of_gTau_zero h
  funext k
  by_cases hki : k = i
  · rw [hki]; exact hi
  exact hrel k hki

omit [Fintype ν] in
lemma gTau_self {M : ℕ} (i : Fin eta) (q : GConfig eta (2 * M + 1)) : gTau i q q = 0 := by
  unfold gTau
  rw [sub_self, gl_zero']

omit [Fintype ν] in
/-- The grid terms of `κ` and `κ⁰ = κ - κ(0) δ₀` differ by the zero-transfer diagonal. -/
lemma gridTerm_update (D : NucData ν) (κ : Lat3 → ℝ) (t : Term eta ν) (q p : RCfg eta m) :
    gridTerm eta m D κ t q p =
      gridTerm eta m D (Function.update κ 0 0) t q p +
        if q = p then (κ 0 : ℂ) * zt D t else 0 := by
  classical
  rcases t with pr | il
  · simp only [gridTerm, tk, zt]
    by_cases hqp : q = p
    · subst hqp
      have hrel : gRel2 pr.1.1 pr.1.2 q q := ⟨fun _ _ _ => rfl, rfl⟩
      rw [if_pos hrel, if_pos hrel, if_pos rfl, gTau_self]
      simp [kgr]
    · rw [if_neg hqp, add_zero]
      split_ifs with hrel
      · have hne : gTau pr.1.1 q p ≠ 0 := fun h => hqp (eq_of_gRel2 hrel h)
        simp [kgr, Function.update_of_ne hne]
      · rfl
  · simp only [gridTerm, tk, zt]
    by_cases hqp : q = p
    · subst hqp
      have hrel : Spec1 il.1 q q := fun _ _ => rfl
      rw [if_pos hrel, if_pos hrel, if_pos rfl, gTau_self]
      simp [kgn, kgr]
      ring
    · rw [if_neg hqp, add_zero]
      split_ifs with hrel
      · have hne : gTau il.1 q p ≠ 0 := fun h => hqp (eq_of_spec1 hrel h)
        simp [kgn, kgr, Function.update_of_ne hne]
      · rfl

lemma vGridK_update (P : RegParticles eta) (D : NucData ν) (κ : Lat3 → ℝ) (q p : RCfg eta m) :
    vGridK eta m P D κ q p =
      vGridK eta m P D (Function.update κ 0 0) q p +
        if q = p then (κ 0 : ℂ) * gridZeroWeight P D else 0 := by
  classical
  unfold vGridK gridZeroWeight
  simp_rw [gridTerm_update D κ _ q p, mul_add, Finset.sum_add_distrib]
  congr 1
  split_ifs with h
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  · simp

/-- **The grid zero mode is a scalar**: `G[κ] = G[κ⁰] + κ(0) z_g`. -/
lemma Hgrid_update (P : RegParticles eta) (D : NucData ν) (κ : Lat3 → ℝ) (g : ℝ) :
    Hgrid eta m P D κ g =
      Hgrid eta m P D (Function.update κ 0 0) g +
        ((κ 0 : ℂ) * gridZeroWeight P D) • LinearMap.id := by
  classical
  apply LinearMap.ext
  intro v
  ext q
  simp only [Hgrid, LinearMap.add_apply, PiLp.add_apply, kOp_apply, wMul_apply,
    LinearMap.smul_apply, LinearMap.id_apply, PiLp.smul_apply, smul_eq_mul]
  simp_rw [vGridK_update P D κ q, mul_add, Finset.sum_add_distrib]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- For positioned nuclei the zero-transfer weight is real. -/
lemma gridZeroWeight_im (P : RegParticles eta) (N : PosNuclei ν) :
    (gridZeroWeight P N.toNucData).im = 0 := by
  unfold gridZeroWeight
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun t _ => ?_
  rcases t with pr | il
  · simp [zt]
  · simp [zt, PosNuclei.toNucData, UnitAddTorus.mFourier_zero]

/-! ## The phase of the grid propagator -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Multiplication by a unit complex number as a linear isometry. -/
noncomputable def phaseLIE (u : ℂ) (hu : ‖u‖ = 1) : E ≃ₗᵢ[ℂ] E where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℂ E u (by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu)
  norm_map' x := by
    change ‖u • x‖ = ‖x‖
    rw [norm_smul, hu, one_mul]

omit [Fintype ν] in
@[simp] lemma phaseLIE_apply (u : ℂ) (hu : ‖u‖ = 1) (x : E) : phaseLIE u hu x = u • x := rfl

omit [Fintype ν] in
lemma norm_cexp_I_mul_real {c : ℂ} (hc : c.im = 0) (s : ℝ) :
    ‖Complex.exp (Complex.I * c * s)‖ = 1 := by
  rw [Complex.norm_exp]
  have : (Complex.I * c * (s : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, hc]
  rw [this, Real.exp_zero]

omit [Fintype ν] in
/-- **The phase of a propagator**: if `U` is a propagator of `G = G⁰ + c` (`c` real), then
`U⁰(s) = e^{ics} U(s)` is a propagator of `G⁰`. -/
theorem propagator_phase (G G0 : E →ₗ[ℂ] E) {c : ℂ} (hc : c.im = 0)
    (hG : G = G0 + c • LinearMap.id) (U : ℝ → E ≃ₗᵢ[ℂ] E) (hU0 : ∀ x, U 0 x = x)
    (hcomm : ∀ t x, U t (G x) = G (U t x))
    (hderiv : ∀ t x, HasDerivAt (fun s => U s x) (-(Complex.I • U t (G x))) t) :
    ∃ U0 : ℝ → E ≃ₗᵢ[ℂ] E, (∀ t x, U0 t x = Complex.exp (Complex.I * c * t) • U t x) ∧
      (∀ x, U0 0 x = x) ∧ (∀ t x, U0 t (G0 x) = G0 (U0 t x)) ∧
      (∀ t x, HasDerivAt (fun s => U0 s x) (-(Complex.I • U0 t (G0 x))) t) := by
  refine ⟨fun s => (U s).trans (phaseLIE _ (norm_cexp_I_mul_real hc s)), fun t x => rfl, ?_, ?_,
    ?_⟩
  · intro x
    change Complex.exp (Complex.I * c * ((0 : ℝ) : ℂ)) • U 0 x = x
    rw [hU0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
  · intro t x
    change Complex.exp (Complex.I * c * t) • U t (G0 x) =
      G0 (Complex.exp (Complex.I * c * t) • U t x)
    have h1 : G0 x = G x - c • x := by
      rw [hG, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      abel
    have h2 : G0 (U t x) = G (U t x) - c • U t x := by
      rw [hG, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      abel
    rw [map_smul, h1, map_sub, LinearIsometryEquiv.map_smul, hcomm, h2]
  · intro t x
    change HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * c * s) • U s x)
      (-(Complex.I • (Complex.exp (Complex.I * c * t) • U t (G0 x)))) t
    have he : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * c * s))
        (Complex.exp (Complex.I * c * t) * (Complex.I * c)) t := by
      have h1 : HasDerivAt (fun s : ℝ => Complex.I * c * (s : ℂ)) (Complex.I * c * 1) t :=
        (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * c)
      rw [mul_one] at h1
      exact h1.cexp
    have h := he.smul (hderiv t x)
    have h1 : G0 x = G x - c • x := by
      rw [hG, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
      abel
    have e : Complex.exp (Complex.I * c * t) • -(Complex.I • U t (G x)) +
        (Complex.exp (Complex.I * c * t) * (Complex.I * c)) • U t x =
        -(Complex.I • (Complex.exp (Complex.I * c * t) • U t (G0 x))) := by
      rw [h1, map_sub, LinearIsometryEquiv.map_smul]
      module
    rw [e] at h
    exact h

end Grid

/-! ## The phase of the cell propagator -/

section CellPhase

variable {sys : CoulombSystem eta ν} {L : ℝ} {θ : ℝ → ℝ}

/-- **The phase of the cell propagator** (eq:free-zero-mode): if `U` is a propagator of
`H_L^{(0)}`, then `U_Z(t) = e^{-i C_zm t} U(t)` is a propagator of the physical `H_L`:
`e^{-itH_L} = e^{-itC_zm} e^{-itH_L^{(0)}}`. -/
theorem cell_phase {R : ℝ} (hθ : Profile R θ)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hgraphU : ∀ t f h, HasGLHamiltonian sys L θ f h → HasGLHamiltonian sys L θ (U t f) (U t h))
    (hderivU : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) :
    ∃ UZ : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      (∀ t f, UZ t f = Complex.exp (Complex.I * (-zeroModeShift sys L θ) * t) • U t f) ∧
      (∀ ψ, UZ 0 ψ = ψ) ∧
      (∀ t f h, HasGLHamiltonianZ sys L θ f h → HasGLHamiltonianZ sys L θ (UZ t f) (UZ t h)) ∧
      (∀ t f h, HasGLHamiltonianZ sys L θ f h →
        HasDerivAt (fun s => UZ s f) (-(Complex.I • UZ t h)) t) := by
  have hC0 : (zeroModeShift sys L θ).im = 0 := by
    have h := zeroModeShift_re_eq sys hθ L
    rw [← h, Complex.ofReal_im]
  set C := zeroModeShift sys L θ with hCdef
  have hC : (-C).im = 0 := by rw [Complex.neg_im, hC0, neg_zero]
  set e : ℝ → ℂ := fun s => Complex.exp (Complex.I * (-C) * s) with he
  refine ⟨fun s => (U s).trans (phaseLIE (e s) (norm_cexp_I_mul_real hC s)), fun t f => rfl, ?_,
    ?_, ?_⟩
  · intro ψ
    change e 0 • U 0 ψ = ψ
    rw [hU0, he]
    simp
  · intro t f h hfh
    change HasGLHamiltonianZ sys L θ (e t • U t f) (e t • U t h)
    rw [hasGLHamiltonianZ_iff]
    have h1 := (hgraphU t f _ (hasGLHamiltonianZ_iff.mp hfh)).smul sys (e t)
    rw [map_sub, LinearIsometryEquiv.map_smul] at h1
    have e1 : e t • (U t h - C • U t f) = e t • U t h - C • (e t • U t f) := by
      rw [smul_sub, smul_comm]
    rw [e1] at h1
    exact h1
  · intro t f h hfh
    change HasDerivAt (fun s : ℝ => e s • U s f) (-(Complex.I • (e t • U t h))) t
    have hd : HasDerivAt e (e t * (Complex.I * (-C))) t := by
      have h1 : HasDerivAt (fun s : ℝ => Complex.I * (-C) * (s : ℂ)) (Complex.I * (-C) * 1) t :=
        (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * (-C))
      rw [mul_one] at h1
      exact h1.cexp
    have hD := hd.smul (hderivU t f _ (hasGLHamiltonianZ_iff.mp hfh))
    have e2 : e t • -(Complex.I • U t (h - C • f)) + (e t * (Complex.I * -C)) • U t f =
        -(Complex.I • (e t • U t h)) := by
      rw [map_sub, LinearIsometryEquiv.map_smul]
      module
    rw [e2] at hD
    exact hD

/-- **The physical cell propagator exists** (from `exists_gLPropagator`). -/
theorem exists_gLPropagatorZ {L R : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) :
    ∃ UZ : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta, (∀ ψ, UZ 0 ψ = ψ) ∧
      (∀ t f h, HasGLHamiltonianZ sys L θ f h → HasGLHamiltonianZ sys L θ (UZ t f) (UZ t h)) ∧
      (∀ t f h, HasGLHamiltonianZ sys L θ f h →
        HasDerivAt (fun s => UZ s f) (-(Complex.I • UZ t h)) t) := by
  obtain ⟨U, hU0, -, -, hgraphU, hderivU, -⟩ := exists_gLPropagator (sys := sys) hL hθ hR
  obtain ⟨UZ, -, h0, hg, hd⟩ := cell_phase hθ U hU0 hgraphU hderivU
  exact ⟨UZ, h0, hg, hd⟩

/-- **`e^{-itH_L} = e^{-itC_zm} e^{-itH_L^{(0)}}`** (eq:free-zero-mode): every propagator `U_Z` of
the physical `H_L` acts on its domain as `e^{-itC_zm}` times the propagator `U` of `H_L^{(0)}`
(`U` is determined by its uniqueness clause, as in `exists_gLPropagator`). -/
theorem cell_phase_eq
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta)
    (huniq : ∀ φ ζ : ℝ → MolecularPositionL2 eta, (∀ t, HasGLHamiltonian sys L θ (φ t) (ζ t)) →
      (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0))
    (UZ : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hUZ0 : ∀ ψ, UZ 0 ψ = ψ)
    (hgraphZ : ∀ t f h, HasGLHamiltonianZ sys L θ f h →
      HasGLHamiltonianZ sys L θ (UZ t f) (UZ t h))
    (hderivZ : ∀ t f h, HasGLHamiltonianZ sys L θ f h →
      HasDerivAt (fun s => UZ s f) (-(Complex.I • UZ t h)) t)
    {f h : MolecularPositionL2 eta} (hfh : HasGLHamiltonianZ sys L θ f h) (t : ℝ) :
    UZ t f = Complex.exp (Complex.I * (-zeroModeShift sys L θ) * t) • U t f := by
  set C := zeroModeShift sys L θ with hCdef
  set e : ℝ → ℂ := fun s => Complex.exp (Complex.I * C * s) with he
  have hφ : ∀ s, HasGLHamiltonian sys L θ (e s • UZ s f) (e s • (UZ s h - C • UZ s f)) :=
    fun s => (hasGLHamiltonianZ_iff.mp (hgraphZ s f h hfh)).smul sys (e s)
  have hd : ∀ s, HasDerivAt (fun s => e s • UZ s f)
      (-(Complex.I • (e s • (UZ s h - C • UZ s f)))) s := by
    intro s
    have hde : HasDerivAt e (e s * (Complex.I * C)) s := by
      have h1 : HasDerivAt (fun s : ℝ => Complex.I * C * (s : ℂ)) (Complex.I * C * 1) s :=
        (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (Complex.I * C)
      rw [mul_one] at h1
      exact h1.cexp
    have hD := hde.smul (hderivZ s f h hfh)
    have e2 : e s • -(Complex.I • UZ s h) + (e s * (Complex.I * C)) • UZ s f =
        -(Complex.I • (e s • (UZ s h - C • UZ s f))) := by
      module
    rw [e2] at hD
    exact hD
  have key := huniq (fun s => e s • UZ s f) (fun s => e s • (UZ s h - C • UZ s f)) hφ hd t
  simp only [hUZ0, he, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul] at key
  have hinv : Complex.exp (Complex.I * (-C) * t) * Complex.exp (Complex.I * C * t) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  calc UZ t f =
        (Complex.exp (Complex.I * (-C) * t) * Complex.exp (Complex.I * C * t)) • UZ t f := by
        rw [hinv, one_smul]
    _ = Complex.exp (Complex.I * (-C) * t) • (Complex.exp (Complex.I * C * t) • UZ t f) := by
        rw [smul_smul]
    _ = Complex.exp (Complex.I * (-C) * t) • U t f := by rw [key]

end CellPhase

/-! ## The kernel class with the zero mode -/

/-- **The isolated grid kernel class** (eq:free-kinetic-kernel): real, even coefficients that
preserve `ĝ_L(0)`, agree with `ĝ_L` for `0 < |k_ν| ≤ K` (`|ν| ≤ m`), vanish outside the cube of
radius `2m` (`|k_ν|_∞ > 2K`) and obey the majorant `(1 + V) γ_L/|ν|² = 4π(1 + V)/(L³|k_ν|²)` for
`ν ≠ 0`. -/
structure IsGridKernelZ (L : ℝ) (θ : ℝ → ℝ) (V : ℝ) (m : ℕ) (κ : Lat3 → ℝ) : Prop where
  even : ∀ x, κ (-x) = κ x
  bound : ∀ x, x ≠ 0 → |κ x| ≤ PlaneWaveGridG.gLgamma L V * PlaneWaveGridG.coul x
  low : ∀ x, PlaneWaveGridG.nsq x ≤ (m : ℝ) ^ 2 → κ x = (ghat L θ x).re
  support : ∀ x, ¬ PlaneWaveGridG.InBox (2 * m) x → κ x = 0

namespace IsGridKernelZ

variable {L : ℝ} {θ : ℝ → ℝ} {V : ℝ} {m : ℕ} {κ : Lat3 → ℝ}

/-- The class keeps the zero mode: `κ(0) = ĝ_L(0)`. -/
lemma zero (h : IsGridKernelZ L θ V m κ) : κ 0 = (ghat L θ 0).re :=
  h.low 0 (by simp [PlaneWaveGridG.nsq])

/-- **The zero-mode-free kernel** `κ⁰ = κ - κ(0) δ₀` lies in the release's class. -/
lemma zeroed (h : IsGridKernelZ L θ V m κ) (hL : 0 < L) (hV : 0 ≤ V) :
    PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L V) (PlaneWaveGridG.gLref L θ V) m
      (Function.update κ 0 0) where
  even x := by
    by_cases hx : x = 0
    · subst hx
      simp
    · have hx' : -x ≠ 0 := neg_ne_zero.mpr hx
      rw [Function.update_of_ne hx', Function.update_of_ne hx, h.even]
  bound x := by
    by_cases hx : x = 0
    · subst hx
      simp [PlaneWaveGridG.coul, PlaneWaveGridG.nsq]
    · rw [Function.update_of_ne hx]
      exact h.bound x hx
  low x hx := by
    by_cases h0 : x = 0
    · subst h0
      have h00 : (0 : Lat3) = (fun _ => 0) := rfl
      rw [Function.update_self]
      unfold PlaneWaveGridG.gLref gLlat
      rw [if_pos h00]
      simp
    · rw [Function.update_of_ne h0, h.low x hx]
      have hg : PlaneWaveGridG.gLgamma L V ≠ 0 := (PlaneWaveGridG.gLgamma_pos hL hV).ne'
      have h0' : x ≠ (fun _ => 0) := h0
      unfold PlaneWaveGridG.gLref gLlat
      rw [if_neg h0']
      field_simp
  support x hx := by
    by_cases h0 : x = 0
    · exfalso
      apply hx
      subst h0
      intro c
      simp
    · rw [Function.update_of_ne h0]
      exact h.support x hx

/-- **Conversely**, every kernel `κ⁰` of the release's class, with the zero mode `ĝ_L(0)` put back,
lies in the class eq:free-kinetic-kernel; with `zeroed`, the two classes correspond. -/
lemma ofIsGridKernel {κ : Lat3 → ℝ}
    (h : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L V) (PlaneWaveGridG.gLref L θ V) m κ)
    (hL : 0 < L) (hV : 0 ≤ V) :
    IsGridKernelZ L θ V m (Function.update κ 0 (ghat L θ 0).re) where
  even x := by
    by_cases hx : x = 0
    · subst hx
      simp
    · have hx' : -x ≠ 0 := neg_ne_zero.mpr hx
      rw [Function.update_of_ne hx', Function.update_of_ne hx, h.even]
  bound x hx := by
    rw [Function.update_of_ne hx]
    exact h.bound x
  low x hx := by
    by_cases h0 : x = 0
    · subst h0
      simp
    · rw [Function.update_of_ne h0, h.low x hx]
      have hg : PlaneWaveGridG.gLgamma L V ≠ 0 := (PlaneWaveGridG.gLgamma_pos hL hV).ne'
      have h0' : x ≠ (fun _ => 0) := h0
      unfold PlaneWaveGridG.gLref gLlat
      rw [if_neg h0']
      field_simp
  support x hx := by
    have h0 : x ≠ 0 := by
      rintro rfl
      exact hx (fun c => by simp)
    rw [Function.update_of_ne h0]
    exact h.support x hx

end IsGridKernelZ

/-- **The class eq:free-kinetic-kernel is not empty**: the sharp truncation
`ĝ_L 1_{|k_ν|_∞ ≤ 2K}`, with its zero mode, lies in it. -/
lemma isGridKernelZ_sharp {L R : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ) (m : ℕ) :
    IsGridKernelZ L θ (tv R θ) m (Function.update (PlaneWaveGridG.sharpKernel
      (PlaneWaveGridG.gLgamma L (tv R θ)) (PlaneWaveGridG.gLref L θ (tv R θ)) m) 0
        (ghat L θ 0).re) :=
  IsGridKernelZ.ofIsGridKernel (isGridKernel_sharp hL hθ m) hL hθ.tv_nonneg

/-! ## The grid propagators -/

section GridProp

variable {m : ℕ}

omit [Fintype ν] in
/-- **The grid kinetic expectations are phase invariant.** -/
lemma regExpect_phase (sys : CoulombSystem eta ν) (g : ℝ) (r : Fin eta)
    (x : EuclideanSpace ℂ (RCfg eta m)) {u : ℂ} (hu : ‖u‖ = 1) :
    regExpect sys g r (u • x) = regExpect sys g r x := by
  unfold regExpect
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [PiLp.smul_apply, smul_eq_mul, norm_mul, hu, one_mul]

/-- **Grid transfer across the zero mode**: every propagator `U_g` of the physical grid
Hamiltonian `G[κ]` (zero mode kept) is `e^{-iκ(0) z_g t}` times a propagator `U_g⁰` of `G[κ⁰]`,
and the grid kinetic expectations of the two agree. -/
theorem grid_phase (P : RegParticles eta) (N : PosNuclei ν) (κ : Lat3 → ℝ) (g : ℝ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m P N.toNucData κ g x) =
      Hgrid eta m P N.toNucData κ g (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m P N.toNucData κ g x))) t) :
    ∃ Ug0 : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug0 0 x = x) ∧
      (∀ t x, Ug0 t (Hgrid eta m P N.toNucData (Function.update κ 0 0) g x) =
        Hgrid eta m P N.toNucData (Function.update κ 0 0) g (Ug0 t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug0 s x)
        (-(Complex.I • Ug0 t (Hgrid eta m P N.toNucData (Function.update κ 0 0) g x))) t) ∧
      ∀ (sys : CoulombSystem eta ν) (g' : ℝ) (r : Fin eta) t x,
        regExpect sys g' r (Ug t x) = regExpect sys g' r (Ug0 t x) := by
  have hc : ((κ 0 : ℂ) * gridZeroWeight P N.toNucData).im = 0 := by
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, gridZeroWeight_im]
    ring
  obtain ⟨U0, hU, h0, hcomm, hderiv⟩ := propagator_phase _ _ hc (Hgrid_update P _ κ g) Ug hg0
    hgcomm hgderiv
  refine ⟨U0, h0, hcomm, hderiv, fun sys g' r t x => ?_⟩
  rw [hU, regExpect_phase sys g' r _ (norm_cexp_I_mul_real hc t)]

/-- **The grid zero mode is the cell zero mode**: for a kernel of the class eq:free-kinetic-kernel,
`κ(0) z_g = C_zm` (eq:free-zero-mode: the scalar is represented exactly by both
discretisations). -/
lemma gridZero_eq_zeroModeShift (sys : CoulombSystem eta ν) {R : ℝ} {θ : ℝ → ℝ}
    (hθ : Profile R θ) (L : ℝ) :
    ((ghat L θ 0).re : ℂ) * gridZeroWeight (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData =
      zeroModeShift sys L θ := by
  have h00 : (0 : Lattice3) = (fun _ => 0) := rfl
  have hg : ghat L θ (fun _ => 0) = (((ghat L θ (fun _ => 0)).re : ℝ) : ℂ) := by
    rw [ghat_zero_eq hθ L, Complex.ofReal_re]
  rw [h00]
  unfold gridZeroWeight zeroModeShift
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, hg, mul_add]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun pr _ => ?_
    simp only [zt, RegParticles.tcoef, regParticlesOf_charge, Complex.ofReal_re]
    push_cast
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [zt, RegParticles.tcoef, regParticlesOf_charge, PosNuclei.toNucData, posNucleiOf,
      UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, Complex.ofReal_re]
    push_cast
    ring

end GridProp

/-! ## The constant and the arithmetic -/

/-- **The constant of `prop:free-kinetic-log` for the physical cell Hamiltonian**:
`(1 + Q/4)⁴ C`, `Q = Σ_{i<j} |q_i q_j| + Σ_{i,ℓ} |q_i ζ_ℓ|`. -/
noncomputable def freeKinCZ (sys : CoulombSystem eta ν) (V Dbar : ℝ) : ℝ :=
  (1 + zeroWeight sys / 4) ^ 4 * freeKinC sys V Dbar

lemma freeKinCZ_nonneg (sys : CoulombSystem eta ν) {V Dbar : ℝ} (hV : 0 ≤ V) (hD : 0 ≤ Dbar) :
    0 ≤ freeKinCZ sys V Dbar := by
  unfold freeKinCZ
  have := freeKinC_nonneg sys hV hD
  have := zeroWeight_nonneg sys
  positivity

/-- The scaled budget `D_*' = a D_*`, `a = (1 + Q/4)² ≥ 1`, in the bound of
`prop:free-kinetic-log`. -/
lemma zm_arith {C a Dinf Dst Q K t ε : ℝ} (hC : 0 ≤ C) (ha : 1 ≤ a) (hDinf : 0 ≤ Dinf)
    (hDst : 0 ≤ Dst) (ht : 0 ≤ t) (hε : 0 ≤ ε) :
    C * (a * Dst) ^ 2 * Q / K + C * (Dinf + a * Dst) * (1 + t) * ε ≤
      a ^ 2 * C * Dst ^ 2 * Q / K + a ^ 2 * C * (Dinf + Dst) * (1 + t) * ε := by
  have e1 : C * (a * Dst) ^ 2 * Q / K = a ^ 2 * C * Dst ^ 2 * Q / K := by ring
  rw [e1]
  have h2 : Dinf + a * Dst ≤ a ^ 2 * (Dinf + Dst) := by
    have ha2 : a ≤ a ^ 2 := by nlinarith
    have h4 : Dinf ≤ a ^ 2 * Dinf := le_mul_of_one_le_left hDinf (by nlinarith)
    have h5 : a * Dst ≤ a ^ 2 * Dst := mul_le_mul_of_nonneg_right ha2 hDst
    rw [mul_add]
    linarith
  have h3 : 0 ≤ C * ((1 + t) * ε) := mul_nonneg hC (mul_nonneg (by linarith) hε)
  have := mul_le_mul_of_nonneg_left h2 h3
  nlinarith

/-- The scaled budget in the stopping bound. -/
lemma zm_arith_stop {C a Dinf Dst Q K vp q ε : ℝ} (hC : 0 ≤ C) (ha : 1 ≤ a) (hDinf : 0 ≤ Dinf)
    (hDst : 0 ≤ Dst) (hvp : 0 < vp) (hq : 0 ≤ q) (hε : 0 ≤ ε) :
    2 * C * (a * Dst) ^ 2 / vp * Q / K + 2 * C * (Dinf + a * Dst) / vp * q * ε ≤
      2 * (a ^ 2 * C) * Dst ^ 2 / vp * Q / K + 2 * (a ^ 2 * C) * (Dinf + Dst) / vp * q * ε := by
  have e1 : 2 * C * (a * Dst) ^ 2 / vp * Q / K = 2 * (a ^ 2 * C) * Dst ^ 2 / vp * Q / K := by ring
  rw [e1]
  have h2 : Dinf + a * Dst ≤ a ^ 2 * (Dinf + Dst) := by
    have ha2 : a ≤ a ^ 2 := by nlinarith
    have h4 : Dinf ≤ a ^ 2 * Dinf := le_mul_of_one_le_left hDinf (by nlinarith)
    have h5 : a * Dst ≤ a ^ 2 * Dst := mul_le_mul_of_nonneg_right ha2 hDst
    rw [mul_add]
    linarith
  have h3 : 0 ≤ 2 * C / vp * q * ε := by positivity
  have := mul_le_mul_of_nonneg_left h2 h3
  have e2 : 2 * C * (Dinf + a * Dst) / vp * q * ε = 2 * C / vp * q * ε * (Dinf + a * Dst) := by
    ring
  have e3 : 2 * (a ^ 2 * C) * (Dinf + Dst) / vp * q * ε =
      2 * C / vp * q * ε * (a ^ 2 * (Dinf + Dst)) := by ring
  rw [e2, e3]
  linarith

/-! ## The budget with spin -/

lemma sqrt_sum_sq_add_le' {S : Type*} [Fintype S] (a b : S → ℝ) :
    Real.sqrt (∑ σ, (a σ + b σ) ^ 2) ≤ Real.sqrt (∑ σ, a σ ^ 2) + Real.sqrt (∑ σ, b σ ^ 2) := by
  have h := norm_add_le (WithLp.toLp 2 a : EuclideanSpace ℝ S) (WithLp.toLp 2 b)
  simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] at h
  simpa using h

lemma sqrt_sum_sq_le_of_le {S : Type*} [Fintype S] {a b : S → ℝ} (ha : ∀ σ, 0 ≤ a σ)
    (hab : ∀ σ, a σ ≤ b σ) : Real.sqrt (∑ σ, a σ ^ 2) ≤ Real.sqrt (∑ σ, b σ ^ 2) :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun σ _ => pow_le_pow_left₀ (ha σ) (hab σ) 2)

lemma sqrt_sum_sq_smul {S : Type*} [Fintype S] (a : S → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    Real.sqrt (∑ σ, (c * a σ) ^ 2) = c * Real.sqrt (∑ σ, a σ ^ 2) := by
  have e : ∑ σ, (c * a σ) ^ 2 = c ^ 2 * ∑ σ, a σ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  rw [e, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

section CellSpin

variable {sys : CoulombSystem eta ν} {L : ℝ} {θ : ℝ → ℝ}

/-- **The graph-norm budget across the zero mode, with spin**: componentwise relations and the
Hilbert norms of the spin-inclusive space. -/
theorem budget_zero_mode_spin {ς : Type*} [Fintype ς] {φ h₀ h₁ : ς → MolecularPositionL2 eta}
    (hdom0 : ∀ σ, HasGLHamiltonianZ sys L θ (φ σ) (h₀ σ))
    (hdom1 : ∀ σ, HasGLHamiltonianZ sys L θ (h₀ σ) (h₁ σ))
    {c : ℝ} (hc : ‖zeroModeShift sys L θ‖ ≤ c) :
    ∃ h₀' h₁' : ς → MolecularPositionL2 eta, (∀ σ, HasGLHamiltonian sys L θ (φ σ) (h₀' σ)) ∧
      (∀ σ, HasGLHamiltonian sys L θ (h₀' σ) (h₁' σ)) ∧
      Real.sqrt (∑ σ, ‖φ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₀' σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁' σ‖ ^ 2) ≤
        (1 + c) ^ 2 * (Real.sqrt (∑ σ, ‖φ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) +
          Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2)) := by
  set C := zeroModeShift sys L θ with hC
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hc
  refine ⟨fun σ => h₀ σ - C • φ σ, fun σ => (h₁ σ - C • h₀ σ) - C • (h₀ σ - C • φ σ),
    fun σ => hasGLHamiltonianZ_iff.mp (hdom0 σ),
    fun σ => (hasGLHamiltonianZ_iff.mp (hdom1 σ)).sub sys
      ((hasGLHamiltonianZ_iff.mp (hdom0 σ)).smul sys C), ?_⟩
  have n0 : ∀ σ, ‖h₀ σ - C • φ σ‖ ≤ ‖h₀ σ‖ + c * ‖φ σ‖ := fun σ => by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul]
    have := mul_le_mul_of_nonneg_right hc (norm_nonneg (φ σ))
    linarith
  have n1 : ∀ σ, ‖(h₁ σ - C • h₀ σ) - C • (h₀ σ - C • φ σ)‖ ≤
      ‖h₁ σ‖ + (2 * c * ‖h₀ σ‖ + c ^ 2 * ‖φ σ‖) := fun σ => by
    refine (norm_sub_le _ _).trans ?_
    have a1 : ‖h₁ σ - C • h₀ σ‖ ≤ ‖h₁ σ‖ + c * ‖h₀ σ‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul]
      have := mul_le_mul_of_nonneg_right hc (norm_nonneg (h₀ σ))
      linarith
    have a2 : ‖C • (h₀ σ - C • φ σ)‖ ≤ c * (‖h₀ σ‖ + c * ‖φ σ‖) := by
      rw [norm_smul]
      exact mul_le_mul hc (n0 σ) (norm_nonneg _) hc0
    nlinarith
  set Aφ := Real.sqrt (∑ σ, ‖φ σ‖ ^ 2) with hAφ
  set A0 := Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) with hA0
  set A1 := Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) with hA1
  have s0 : Real.sqrt (∑ σ, ‖h₀ σ - C • φ σ‖ ^ 2) ≤ A0 + c * Aφ := by
    refine (sqrt_sum_sq_le_of_le (fun σ => norm_nonneg _) n0).trans ?_
    refine (sqrt_sum_sq_add_le' _ _).trans ?_
    rw [sqrt_sum_sq_smul _ hc0]
  have s1 : Real.sqrt (∑ σ, ‖(h₁ σ - C • h₀ σ) - C • (h₀ σ - C • φ σ)‖ ^ 2) ≤
      A1 + (2 * c * A0 + c ^ 2 * Aφ) := by
    refine (sqrt_sum_sq_le_of_le (fun σ => norm_nonneg _) n1).trans ?_
    refine (sqrt_sum_sq_add_le' _ _).trans ?_
    refine add_le_add le_rfl ((sqrt_sum_sq_add_le' _ _).trans ?_)
    rw [sqrt_sum_sq_smul _ (by positivity), sqrt_sum_sq_smul _ (by positivity)]
  have hp : 0 ≤ Aφ := Real.sqrt_nonneg _
  have h0 : 0 ≤ A0 := Real.sqrt_nonneg _
  have h1 : 0 ≤ A1 := Real.sqrt_nonneg _
  nlinarith [mul_nonneg hc0 hp, mul_nonneg hc0 h0, mul_nonneg hc0 h1,
    mul_nonneg (mul_nonneg hc0 hc0) hp, mul_nonneg (mul_nonneg hc0 hc0) h0,
    mul_nonneg (mul_nonneg hc0 hc0) h1]

end CellSpin

/-! ## The explicit forms for the physical cell Hamiltonian -/

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` for the physical cell Hamiltonian** (general cutoff): the
cutoff-domain condition (H_dom) and the budget `D_* ≥ ‖φ₀‖ + ‖H_L φ₀‖ + ‖H_L² φ₀‖` for `H_L` with
its zero mode (`HasGLHamiltonianZ`), a profile bound `V_θ ≤ V̄`, the kernel class
eq:free-kinetic-kernel (`IsGridKernelZ`, `κ(0) = ĝ_L(0)`) and any propagator `U_g` of the physical
grid Hamiltonian: `|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C D_*² [1 + t + log(2 + K)]/K³
  + C (𝒟_∞ + D_*) (1 + t) ε`, `C = (1 + Q/4)⁴ freeKinC sys V̄ D̄`, `K₀ = cellK0 sys V̄`. -/
theorem free_kinetic_log_phys_endpoint (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    (hdom0 : HasGLHamiltonianZ sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonianZ sys L θ h₀ h₁)
    {Dinf Dst : ℝ} (hDinf : ‖ψ 0‖ + ‖H 0‖ ≤ Dinf)
    (hDst : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
      freeKinCZ sys Vbar Dbar * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) /
          (2 * Real.pi / L * m) ^ 3 +
        freeKinCZ sys Vbar Dbar * (Dinf + Dst) * (1 + t) * ε := by
  have hL := pos_of_two_pi_le hL2
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := ((abs_nonneg _).trans (X.d1 0 (p₀, 0))).trans hD1
  have hq0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have ha : 1 ≤ (1 + zeroWeight sys / 4) ^ 2 := one_le_pow₀ (by linarith)
  have hC := freeKinC_nonneg sys (hv0.trans hVbar) hDb
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  obtain ⟨h₀', h₁', hd0, hd1, hn⟩ :=
    budget_zero_mode hdom0 hdom1 (norm_zeroModeShift_le sys hL2 hθ hR)
  have hDst' : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀'‖ + ‖h₁'‖ ≤
      (1 + zeroWeight sys / 4) ^ 2 * Dst := hn.trans (mul_le_mul_of_nonneg_left hDst (sq_nonneg _))
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  refine (free_kinetic_log_endpoint_vbar sys hL2 hθ hR hR0 hρ hone hVbar P hP hpos X hret hD1 hD2
    hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hd0 hd1 hDinf hDst' p₀ m hm hK
    (hκ.zeroed hL hv0) Ug0 hg00 hgcomm0 hgderiv0).trans ?_
  have hz := zm_arith (Q := 1 + t + Real.log (2 + 2 * Real.pi / L * m))
    (K := (2 * Real.pi / L * m) ^ 3) hC ha hDinf0 hDst0 ht hε
  unfold freeKinCZ
  refine hz.trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
/-- **`cor:free-stopping-log` for the physical cell Hamiltonian** (general cutoff): the hypotheses
of `free_kinetic_log_phys_endpoint` on `[0, τ]`; the secants differ by at most
`(2C D_*²/v_p)[1 + (1 + log(2 + K))/τ]/K³ + (2C(𝒟_∞ + D_*)/v_p)(1 + 1/τ) ε`,
`C = (1 + Q/4)⁴ freeKinC sys V̄ D̄`. -/
theorem free_stopping_log_phys_endpoint (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    (hdom0 : HasGLHamiltonianZ sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonianZ sys L θ h₀ h₁)
    {Dinf Dst : ℝ} (hDinf : ‖ψ 0‖ + ‖H 0‖ ≤ Dinf)
    (hDst : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
      2 * freeKinCZ sys Vbar Dbar * Dst ^ 2 / vp *
          (1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ) / (2 * Real.pi / L * m) ^ 3 +
        2 * freeKinCZ sys Vbar Dbar * (Dinf + Dst) / vp * (1 + 1 / τ) * ε := by
  have hL := pos_of_two_pi_le hL2
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := ((abs_nonneg _).trans (X.d1 0 (p₀, 0))).trans hD1
  have hq0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have ha : 1 ≤ (1 + zeroWeight sys / 4) ^ 2 := one_le_pow₀ (by linarith)
  have hC := freeKinC_nonneg sys (hv0.trans hVbar) hDb
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  obtain ⟨h₀', h₁', hd0, hd1, hn⟩ :=
    budget_zero_mode hdom0 hdom1 (norm_zeroModeShift_le sys hL2 hθ hR)
  have hDst' : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀'‖ + ‖h₁'‖ ≤
      (1 + zeroWeight sys / 4) ^ 2 * Dst := hn.trans (mul_le_mul_of_nonneg_left hDst (sq_nonneg _))
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  refine (free_stopping_log_vbar sys hL2 hθ hR hR0 hρ hone hVbar P hP hpos X hret hD1 hD2 hSm hBm
    hχB hSB hdS hd2S hψd hHam hgrad hτ hε hleak0 hleak1 hd0 hd1 hDinf hDst' p₀ m hm hK
    (hκ.zeroed hL hv0) Ug0 hg00 hgcomm0 hgderiv0 hvp).trans ?_
  have hq : 0 ≤ 1 + 1 / τ := by
    have := div_nonneg zero_le_one hτ.le
    linarith
  have hz := zm_arith_stop (Q := 1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ)
    (K := (2 * Real.pi / L * m) ^ 3) hC ha hDinf0 hDst0 hvp hq hε
  unfold freeKinCZ
  refine hz.trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with finite internal spin for the physical cell Hamiltonian**:
componentwise (H_dom) for `H_L` with its zero mode, the spin-inclusive budget `D_*`, the kernel
class eq:free-kinetic-kernel and any propagator of the physical grid Hamiltonian;
`C = (1 + Q/4)⁴ freeKinC sys V̄ D̄`. -/
theorem free_kinetic_log_spin_phys_endpoint (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    (hdom0 : ∀ σ, HasGLHamiltonianZ sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ))
    (hdom1 : ∀ σ, HasGLHamiltonianZ sys L θ (h₀ σ) (h₁ σ))
    {Dinf Dst : ℝ} (hDinf : ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf)
    (hDst : Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
      Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
      freeKinCZ sys Vbar Dbar * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) /
          (2 * Real.pi / L * m) ^ 3 +
        freeKinCZ sys Vbar Dbar * (Dinf + Dst) * (1 + t) * ε := by
  have hL := pos_of_two_pi_le hL2
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := ((abs_nonneg _).trans (X.d1 0 (p₀, 0))).trans hD1
  have hq0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have ha : 1 ≤ (1 + zeroWeight sys / 4) ^ 2 := one_le_pow₀ (by linarith)
  have hC := freeKinC_nonneg sys (hv0.trans hVbar) hDb
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  obtain ⟨h₀', h₁', hd0, hd1, hn⟩ :=
    budget_zero_mode_spin (φ := fun σ => X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) hdom0 hdom1
      (norm_zeroModeShift_le sys hL2 hθ hR)
  have hDst' : Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
      Real.sqrt (∑ σ, ‖h₀' σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁' σ‖ ^ 2) ≤
      (1 + zeroWeight sys / 4) ^ 2 * Dst := hn.trans (mul_le_mul_of_nonneg_left hDst (sq_nonneg _))
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  refine (free_kinetic_log_spin_vbar sys hL2 hθ hR hR0 hρ hone hVbar P hP hpos X hret hD1 hD2 hSm
    hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hd0 hd1 hDinf hDst' p₀ m hm hK
    (hκ.zeroed hL hv0) Ug0 hg00 hgcomm0 hgderiv0).trans ?_
  have hz := zm_arith (Q := 1 + t + Real.log (2 + 2 * Real.pi / L * m))
    (K := (2 * Real.pi / L * m) ^ 3) hC ha hDinf0 hDst0 ht hε
  unfold freeKinCZ
  refine hz.trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
/-- **`cor:free-stopping-log` with finite internal spin for the physical cell Hamiltonian**;
`C = (1 + Q/4)⁴ freeKinC sys V̄ D̄`. -/
theorem free_stopping_log_spin_phys_endpoint (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    (hdom0 : ∀ σ, HasGLHamiltonianZ sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ))
    (hdom1 : ∀ σ, HasGLHamiltonianZ sys L θ (h₀ σ) (h₁ σ))
    {Dinf Dst : ℝ} (hDinf : ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf)
    (hDst : Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
      Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
      2 * freeKinCZ sys Vbar Dbar * Dst ^ 2 / vp *
          (1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ) / (2 * Real.pi / L * m) ^ 3 +
        2 * freeKinCZ sys Vbar Dbar * (Dinf + Dst) / vp * (1 + 1 / τ) * ε := by
  have hL := pos_of_two_pi_le hL2
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := ((abs_nonneg _).trans (X.d1 0 (p₀, 0))).trans hD1
  have hq0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have ha : 1 ≤ (1 + zeroWeight sys / 4) ^ 2 := one_le_pow₀ (by linarith)
  have hC := freeKinC_nonneg sys (hv0.trans hVbar) hDb
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  obtain ⟨h₀', h₁', hd0, hd1, hn⟩ :=
    budget_zero_mode_spin (φ := fun σ => X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) hdom0 hdom1
      (norm_zeroModeShift_le sys hL2 hθ hR)
  have hDst' : Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
      Real.sqrt (∑ σ, ‖h₀' σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁' σ‖ ^ 2) ≤
      (1 + zeroWeight sys / 4) ^ 2 * Dst := hn.trans (mul_le_mul_of_nonneg_left hDst (sq_nonneg _))
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  refine (free_stopping_log_spin_vbar sys hL2 hθ hR hR0 hρ hone hVbar P hP hpos X hret hD1 hD2 hSm
    hBm hχB hSB hdS hd2S hψd hHam hgrad hτ hε hleak0 hleak1 hd0 hd1 hDinf hDst' p₀ m hm hK
    (hκ.zeroed hL hv0) Ug0 hg00 hgcomm0 hgderiv0 hvp).trans ?_
  have hq : 0 ≤ 1 + 1 / τ := by
    have := div_nonneg zero_le_one hτ.le
    linarith
  have hz := zm_arith_stop (Q := 1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ)
    (K := (2 * Real.pi / L * m) ^ 3) hC ha hDinf0 hDst0 hvp hq hε
  unfold freeKinCZ
  refine hz.trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
/-- **eq:free-kinetic-N for the physical cell and grid Hamiltonians**: the bound of
`free_kinetic_log_N_vbar` with the physical `H_L` in (H_dom) and `D_*`, the kernel class
eq:free-kinetic-kernel and the physical grid propagators; `C = (1 + Q/4)⁴ freeKinC sys V̄ D̄`. -/
theorem free_kinetic_log_N_phys_endpoint (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    (hdom0 : HasGLHamiltonianZ sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonianZ sys L θ h₀ h₁)
    {Dinf Dst : ℝ} (hDinf : ‖ψ 0‖ + ‖H 0‖ ≤ Dinf)
    (hDst : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys Vbar molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
      125 / (4 * Real.pi ^ 3) * freeKinCZ sys Vbar Dbar * Dst ^ 2 *
          (L ^ 3 / ((4 * m + 1 : ℝ) ^ 3)) *
          (1 + t + Real.log (2 + ((4 * m + 1 : ℝ) ^ 3) ^ (1 / 3 : ℝ) / L)) +
        freeKinCZ sys Vbar Dbar * (Dinf + Dst) * (1 + t) * ε := by
  have hL := pos_of_two_pi_le hL2
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  have hDb : 0 ≤ Dbar := ((abs_nonneg _).trans (X.d1 0 (p₀, 0))).trans hD1
  have hq0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have ha : 1 ≤ (1 + zeroWeight sys / 4) ^ 2 := one_le_pow₀ (by linarith)
  have hC := freeKinC_nonneg sys (hv0.trans hVbar) hDb
  have hDinf0 : 0 ≤ Dinf := le_trans (by positivity) hDinf
  have hDst0 : 0 ≤ Dst := le_trans (by positivity) hDst
  obtain ⟨h₀', h₁', hd0, hd1, hn⟩ :=
    budget_zero_mode hdom0 hdom1 (norm_zeroModeShift_le sys hL2 hθ hR)
  have hDst' : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀'‖ + ‖h₁'‖ ≤
      (1 + zeroWeight sys / 4) ^ 2 * Dst := hn.trans (mul_le_mul_of_nonneg_left hDst (sq_nonneg _))
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  refine (free_kinetic_log_N_vbar sys hL2 hθ hR hR0 hρ hone hVbar P hP hpos X hret hD1 hD2 hSm hBm
    hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hd0 hd1 hDinf hDst' p₀ m hm hK
    (hκ.zeroed hL hv0) Ug0 hg00 hgcomm0 hgderiv0).trans ?_
  have hz := zm_arith (Q := 125 / (4 * Real.pi ^ 3) * (L ^ 3 / ((4 * m + 1 : ℝ) ^ 3)) *
      (1 + t + Real.log (2 + ((4 * m + 1 : ℝ) ^ 3) ^ (1 / 3 : ℝ) / L))) (K := 1)
    hC ha hDinf0 hDst0 ht hε
  unfold freeKinCZ
  exact (le_of_eq (by ring)).trans (hz.trans (le_of_eq (by ring)))

/-! ## The constants before the quantifiers, physical cell Hamiltonian -/

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log`** (general cutoff, (H_dom)) **for the physical cell Hamiltonian**:
there are `C ≥ 0` and `K₀ > 0`, depending only on the system, the profile bound `V̄` and the cutoff
bound `D̄`, such that for every `L ≥ 2π`, every profile with `V_θ ≤ V̄`, every admissible cutoff,
every supplied free-space solution with leakage `ε` on `[0, t]`, the cutoff-domain condition and
budget `D_*` for `H_L` with its zero mode, every `m ≥ 8` with `K = 2πm/L ≥ K₀`, every kernel of the
class eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator of the physical grid
Hamiltonian, `|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C D_*² [1 + t + log(2 + K)]/K³
  + C (𝒟_∞ + D_*) (1 + t) ε`. -/
theorem free_kinetic_log_phys (sys : CoulombSystem eta ν) (Vbar Dbar : ℝ) (hV : 0 ≤
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
      HasGLHamiltonianZ sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀ →
      HasGLHamiltonianZ sys L θ h₀ h₁ →
      ∀ {Dinf Dst : ℝ}, ‖ψ 0‖ + ‖H 0‖ ≤ Dinf →
      ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, IsGridKernelZ L θ (tv R θ) m κ →
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
  refine ⟨freeKinCZ sys Vbar Dbar, freeKinCZ_nonneg sys hV hD,
    cellK0 sys Vbar molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP hpos X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ψ H grad hψd hHam hgrad t ε ht hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst p₀ m
    hm hK κ hκ Ug hg0 hgcomm hgderiv
  exact free_kinetic_log_phys_endpoint sys hL2 hθ hR hR0 hρ hone hVθ P hP hpos X hret hD1 hD2 hSm
    hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm hK hκ Ug
    hg0 hgcomm hgderiv

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` for a fixed molecule and the physical cell Hamiltonian**: one constant
and one threshold, depending only on the masses and charges, `V̄` and `D̄`, for every cell size,
profile with `V_θ ≤ V̄`, nuclear configuration in `B_{R₀}(0)`, cutoff, solution with the physical
budget `D_*`, kernel of the class eq:free-kinetic-kernel and propagator of the physical grid
Hamiltonian. -/
theorem free_kinetic_log_phys_at (sys : CoulombSystem eta ν) (Vbar Dbar : ℝ) (hV : 0 ≤ Vbar)
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
      HasGLHamiltonianZ (sysAt sys P L) L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀ →
      HasGLHamiltonianZ (sysAt sys P L) L θ h₀ h₁ →
      ∀ {Dinf Dst : ℝ}, ‖ψ 0‖ + ‖H 0‖ ≤ Dinf →
      ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, IsGridKernelZ L θ (tv R θ) m κ →
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
  refine ⟨freeKinCZ sys Vbar Dbar, freeKinCZ_nonneg sys hV hD,
    cellK0 sys Vbar molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ψ H grad hψd hHam hgrad t ε ht hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst p₀ m
    hm hK κ hκ Ug hg0 hgcomm hgderiv
  exact free_kinetic_log_phys_endpoint (sysAt sys P L) hL2 hθ hR hR0 hρ hone hVθ P hP (fun l => rfl)
    X hret hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf
    hDst p₀ m hm hK hκ Ug hg0 hgcomm hgderiv

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` for a fixed molecule with finite internal spin and the physical cell
Hamiltonian**: one constant and one threshold for every cell size, profile with `V_θ ≤ V̄`, nuclear
configuration, finite spin set, kernel of the class eq:free-kinetic-kernel and physical grid
propagator. -/
theorem free_kinetic_log_spin_phys_at (sys : CoulombSystem eta ν) (Vbar Dbar : ℝ) (hV : 0 ≤ Vbar)
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
      (∀ σ, HasGLHamiltonianZ (sysAt sys P L) L θ
        (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ)) →
      (∀ σ, HasGLHamiltonianZ (sysAt sys P L) L θ (h₀ σ) (h₁ σ)) →
      ∀ {Dinf Dst : ℝ}, ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf →
      Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
        Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, IsGridKernelZ L θ (tv R θ) m κ →
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
  refine ⟨freeKinCZ sys Vbar Dbar, freeKinCZ_nonneg sys hV hD,
    cellK0 sys Vbar molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ς _ Ψ HΨ grad hψd hHam hgrad t ε ht hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst
    p₀ m hm hK κ hκ Ug hg0 hgcomm hgderiv
  exact free_kinetic_log_spin_phys_endpoint (sysAt sys P L) hL2 hθ hR hR0 hρ hone hVθ P hP (fun l =>
    rfl) X hret hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1
    hDinf hDst p₀ m hm hK hκ Ug hg0 hgcomm hgderiv

set_option maxHeartbeats 1000000 in
/-- **`cor:free-stopping-log` for a fixed molecule and the physical cell Hamiltonian**: one constant
and one threshold for every cell size, profile with `V_θ ≤ V̄`, nuclear configuration, kernel of the
class eq:free-kinetic-kernel and physical grid propagator. -/
theorem free_stopping_log_phys_at (sys : CoulombSystem eta ν) (Vbar Dbar : ℝ) (hV : 0 ≤ Vbar)
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
      HasGLHamiltonianZ (sysAt sys P L) L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀ →
      HasGLHamiltonianZ (sysAt sys P L) L θ h₀ h₁ →
      ∀ {Dinf Dst : ℝ}, ‖ψ 0‖ + ‖H 0‖ ≤ Dinf →
      ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, IsGridKernelZ L θ (tv R θ) m κ →
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
  refine ⟨2 * freeKinCZ sys Vbar Dbar, by have := freeKinCZ_nonneg sys hV hD; positivity,
    cellK0 sys Vbar molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ψ H grad hψd hHam hgrad τ ε hτ hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst p₀ m
    hm hK κ hκ Ug hg0 hgcomm hgderiv vp hvp
  exact free_stopping_log_phys_endpoint (sysAt sys P L) hL2 hθ hR hR0 hρ hone hVθ P hP (fun l =>
    rfl) X hret hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad hτ hε hleak0 hleak1 hdom0 hdom1
    hDinf hDst p₀ m hm hK hκ Ug hg0 hgcomm hgderiv hvp

set_option maxHeartbeats 1000000 in
/-- **`cor:free-stopping-log` for a fixed molecule with finite internal spin and the physical cell
Hamiltonian**. -/
theorem free_stopping_log_spin_phys_at (sys : CoulombSystem eta ν) (Vbar Dbar : ℝ) (hV : 0 ≤ Vbar)
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
      (∀ σ, HasGLHamiltonianZ (sysAt sys P L) L θ
        (X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)) (h₀ σ)) →
      (∀ σ, HasGLHamiltonianZ (sysAt sys P L) L θ (h₀ σ) (h₁ σ)) →
      ∀ {Dinf Dst : ℝ}, ‖Ψ 0‖ + ‖HΨ 0‖ ≤ Dinf →
      Real.sqrt (∑ σ, ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)‖ ^ 2) +
        Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤ Dst →
      ∀ (p₀ : Fin eta) (m : ℕ), 8 ≤ m → K₀ ≤ 2 * Real.pi / L * m →
      ∀ {κ : Lat3 → ℝ}, IsGridKernelZ L θ (tv R θ) m κ →
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
  refine ⟨2 * freeKinCZ sys Vbar Dbar, by have := freeKinCZ_nonneg sys hV hD; positivity,
    cellK0 sys Vbar molecularCanonicalUnitHardyConstant, by unfold cellK0; positivity, ?_⟩
  intro L R R0 ρ θ hL2 hθ hR hVθ hR0 hρ hone P hP X hret hD1 hD2 Bone S hSm hBm hχB hSB hdS
    hd2S ς _ Ψ HΨ grad hψd hHam hgrad τ ε hτ hε hleak0 hleak1 h₀ h₁ hdom0 hdom1 Dinf Dst hDinf hDst
    p₀ m hm hK κ hκ Ug hg0 hgcomm hgderiv vp hvp
  exact free_stopping_log_spin_phys_endpoint (sysAt sys P L) hL2 hθ hR hR0 hρ hone hVθ P hP (fun l
    => rfl) X hret hD1 hD2 hSm hBm hχB hSB hdS hd2S hψd hHam hgrad hτ hε hleak0 hleak1 hdom0 hdom1
    hDinf hDst p₀ m hm hK hκ Ug hg0 hgcomm hgderiv hvp

/-! ## The compatible and explicit cutoffs with the physical grid kernel -/

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` without clamped nuclei, mass-compatible cutoff, physical grid
kernel**: the bound of `free_kinetic_log_nbo_vbar` for every kernel of the class
eq:free-kinetic-kernel (`κ(0) = ĝ_L(0)`) and every propagator of the physical grid Hamiltonian. -/
theorem free_kinetic_log_nbo_phys [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ}
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
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
  have hL0 : 0 < L := pos_of_two_pi_le hL2
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  exact free_kinetic_log_nbo_vbar sys hL2 hθ hR hR0 hρ hone hVbar P hP hpos X hret hDbar hCbar hSm
    hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm hK (hκ.zeroed hL0 hv0)
    Ug0 hg00 hgcomm0 hgderiv0

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with clamped nuclei, cutoff flat near the nuclei, physical grid
kernel**: the bound of `free_kinetic_log_bo_vbar` for the class eq:free-kinetic-kernel and the
physical grid propagators. -/
theorem free_kinetic_log_bo_phys (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
  have hL0 : 0 < L := pos_of_two_pi_le hL2
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  exact free_kinetic_log_bo_vbar sys hL2 hθ hR hR0 hρ hone hVbar P hP hpos X hret hδ hflat hDbar
    hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm hK
    (hκ.zeroed hL0 hv0) Ug0 hg00 hgcomm0 hgderiv0

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with spin, without clamped nuclei, physical grid kernel**: the bound
of `free_kinetic_log_nbo_spin_vbar` for the class eq:free-kinetic-kernel and the physical grid
propagators. -/
theorem free_kinetic_log_nbo_spin_phys [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ}
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
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
  have hL0 : 0 < L := pos_of_two_pi_le hL2
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  exact free_kinetic_log_nbo_spin_vbar sys hL2 hθ hR hR0 hρ hone hVbar P hP hpos X hret hDbar
    hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm hK
    (hκ.zeroed hL0 hv0) Ug0 hg00 hgcomm0 hgderiv0

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with spin, clamped nuclei, physical grid kernel**: the bound of
`free_kinetic_log_bo_spin_vbar` for the class eq:free-kinetic-kernel and the physical grid
propagators. -/
theorem free_kinetic_log_bo_spin_phys (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
  have hL0 : 0 < L := pos_of_two_pi_le hL2
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  exact free_kinetic_log_bo_spin_vbar sys hL2 hθ hR hR0 hρ hone hVbar P hP hpos X hret hδ hflat
    hDbar hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm hK
    (hκ.zeroed hL0 hv0) Ug0 hg00 hgcomm0 hgderiv0

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` without clamped nuclei, uniform in `L` and in the profiles with
`V_θ ≤ V`, physical grid kernel**: the bound of `free_kinetic_log_nbo_uniform_vbar` for the class
eq:free-kinetic-kernel and the physical grid propagators. -/
theorem free_kinetic_log_nbo_uniform_phys [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ V : ℝ}
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
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
  have hL0 : 0 < L := pos_of_freeDynL0 hL
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  exact free_kinetic_log_nbo_uniform_vbar sys hR0 hρ hL hθ hR hV hone P hP hpos hψd hHam hgrad ht
    hε hleak0 hleak1 hH1 hD p₀ m hm hK (hκ.zeroed hL0 hv0) Ug0 hg00 hgcomm0 hgderiv0

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with clamped nuclei and equal moving masses, uniform in `L` and in the
profiles with `V_θ ≤ V`, physical grid kernel**: the bound of `free_kinetic_log_bo_uniform_vbar` for
the class eq:free-kinetic-kernel and the physical grid propagators. -/
theorem free_kinetic_log_bo_uniform_phys (sys : CoulombSystem eta ν) {m₀ : ℝ}
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
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
  have hL0 : 0 < L := pos_of_freeDynBOL0 hL
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf (sysAt sys P L).nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  exact free_kinetic_log_bo_uniform_vbar sys hmass hm0 hR0 hρ hδ P hP hL hθ hR hV hone hψd hHam
    hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm8 hK (hκ.zeroed hL0 hv0) Ug0 hg00 hgcomm0 hgderiv0

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with spin, without clamped nuclei, uniform in `L` and in the profiles
with `V_θ ≤ V`, physical grid kernel**. -/
theorem free_kinetic_log_nbo_spin_uniform_phys [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ V : ℝ}
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
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
  have hL0 : 0 < L := pos_of_freeDynL0 hL
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  exact free_kinetic_log_nbo_spin_uniform_vbar sys hR0 hρ hL hθ hR hV hone P hP hpos hψd hHam
    hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm hK (hκ.zeroed hL0 hv0) Ug0 hg00 hgcomm0 hgderiv0

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with spin, clamped nuclei and equal moving masses, uniform in `L` and
in the profiles with `V_θ ≤ V`, physical grid kernel**. -/
theorem free_kinetic_log_bo_spin_uniform_phys (sys : CoulombSystem eta ν) {m₀ : ℝ}
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
    (hκ : IsGridKernelZ L θ (tv R θ) m κ)
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
  have hL0 : 0 < L := pos_of_freeDynBOL0 hL
  have hv0 : 0 ≤ tv R θ := hθ.tv_nonneg
  obtain ⟨Ug0, hg00, hgcomm0, hgderiv0, hexp⟩ := grid_phase (regParticlesOf sys)
    (posNucleiOf (sysAt sys P L).nuclei) κ (2 * Real.pi / L) Ug hg0 hgcomm hgderiv
  simp only [hexp]
  exact free_kinetic_log_bo_spin_uniform_vbar sys hmass hm0 hR0 hρ hδ P hP hL hθ hR hV hone hψd
    hHam hgrad ht hε hleak0 hleak1 hH1 hD p₀ m hm8 hK (hκ.zeroed hL0 hv0) Ug0 hg00 hgcomm0
    hgderiv0

end KineticLog
