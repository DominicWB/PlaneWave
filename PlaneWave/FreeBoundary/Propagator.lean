import PlaneWave.FreeBoundary.Dynamics

/-!
# `prop:free-dyn`: the propagator of the `g_L` Hamiltonian

`free_dyn_torus` (`PlaneWave.FreeBoundary.Dynamics`) holds for any propagator of the torus `g_L`
Hamiltonian `H_L` (zero mode removed). This file constructs that propagator, as the release file
constructs the propagator of the Coulomb Hamiltonian (`exists_coulombPropagator`), and removes
the hypothesis:

* `exists_fourierPropagator_of_relBound`: the release's resolvent construction for any completed
  operator `H : H² → ℓ²` that is symmetric on `H²` and whose potential part `W = H - T`
  satisfies `‖W u‖² ≤ ‖T u‖²/4 + K ‖u‖²` (`HasRelBound`);
* `gLH2_symm`, `gL_potential_sq_le_quarter`: the two hypotheses for the completed `g_L` operator
  of `PlaneWave.FreeBoundary.CompletedHamiltonian`, from the symmetry of the cube Hamiltonians
  and the mass-weighted `H¹` bound of the `g_L` potential
  (`PlaneWave.FreeBoundary.CubeHamiltonian`, Fourier domination);
* `hasGLHamiltonian_iff_H2`: the torus relation `HasGLHamiltonian` is the graph of the completed
  operator;
* **`exists_gLPropagator`**: the strongly continuous unitary group `e^{-iH_L t}` on `L²(T)`: it
  preserves the graph, solves the Schrödinger equation, and every solution in the graph is
  `e^{-iH_L t}` applied to its initial value;
* **`free_dyn_gL`**: `prop:free-dyn`, free-space step, for this propagator.
-/

set_option autoImplicit false

open MeasureTheory Filter Set PlaneWaveCertificate PlaneWaveDynamics
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15
  molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The diagonal inverse of `T + c` -/

section Diagonal

variable (sys : CoulombSystem eta ν) (L : ℝ)

/-- The diagonal inverse of `T + c S` (weighted coordinates), for a shift `c ≥ 2`. -/
def dInvc (c : ℝ) (hc : 2 ≤ c) : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →L[ℂ]
    lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
  diagCLM (fun p => (((molecularFourierH2Weight eta (2 * Real.pi / L) p /
      (coulombKineticEnergySymbol sys (2 * Real.pi / L) p + c)) : ℝ) : ℂ))
    (2 * sys.maxMass) (by have := sys.one_le_maxMass; positivity)
    (dInv_entry_le sys L c (by linarith))

omit [Fintype ν] in
lemma dInvc_apply (c : ℝ) (hc : 2 ≤ c) (f : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (p : FourierConfig eta Lattice3) :
    dInvc sys L c hc f p = (((molecularFourierH2Weight eta (2 * Real.pi / L) p /
      (coulombKineticEnergySymbol sys (2 * Real.pi / L) p + c)) : ℝ) : ℂ) * f p := rfl

omit [Fintype ν] in
lemma coeff_dInvc (c : ℝ) (hc : 2 ≤ c) (f : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (p : FourierConfig eta Lattice3) :
    molecularH2Coeff (2 * Real.pi / L) (dInvc sys L c hc f) p =
      f p / ((coulombKineticEnergySymbol sys (2 * Real.pi / L) p + c : ℝ) : ℂ) := by
  have hk := coulombKineticEnergySymbol_nonneg sys (2 * Real.pi / L) p
  have hw : ((molecularFourierH2Weight eta (2 * Real.pi / L) p : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (molecularFourierH2Weight_pos eta _ p).ne'
  have hd : ((coulombKineticEnergySymbol sys (2 * Real.pi / L) p + c : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by linarith)
  rw [molecularH2Coeff, dInvc_apply]
  push_cast at hd ⊢
  field_simp

omit [Fintype ν] in
/-- `(T + c S) dInvc = 1`. -/
lemma kinetic_dInvc_add (c : ℝ) (hc : 2 ≤ c)
    (f : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    coulombFourierKineticH2 sys (2 * Real.pi / L) (dInvc sys L c hc f) +
      (c : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) (dInvc sys L c hc f) = f := by
  ext p
  have hk := coulombKineticEnergySymbol_nonneg sys (2 * Real.pi / L) p
  have hd : ((coulombKineticEnergySymbol sys (2 * Real.pi / L) p + c : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by linarith)
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    coulombFourierKineticH2_apply, molecularH2StateMap_apply, coeff_dInvc]
  push_cast at hd ⊢
  field_simp

omit [Fintype ν] in
/-- `dInvc (T + c S) = 1`. -/
lemma dInvc_kinetic_add (c : ℝ) (hc : 2 ≤ c)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    dInvc sys L c hc (coulombFourierKineticH2 sys (2 * Real.pi / L) x +
      (c : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) x) = x := by
  ext p
  have hk := coulombKineticEnergySymbol_nonneg sys (2 * Real.pi / L) p
  have hd : ((coulombKineticEnergySymbol sys (2 * Real.pi / L) p + c : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by linarith)
  have hw : ((molecularFourierH2Weight eta (2 * Real.pi / L) p : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (molecularFourierH2Weight_pos eta _ p).ne'
  rw [dInvc_apply]
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    coulombFourierKineticH2_apply, molecularH2StateMap_apply, molecularH2Coeff]
  push_cast at hd hw ⊢
  field_simp

omit [Fintype ν] in
lemma norm_kinetic_dInvc_le (c : ℝ) (hc : 2 ≤ c)
    (f : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    ‖coulombFourierKineticH2 sys (2 * Real.pi / L) (dInvc sys L c hc f)‖ ≤ ‖f‖ := by
  have h := l2_norm_le_of_le (coulombFourierKineticH2 sys (2 * Real.pi / L) (dInvc sys L c hc f))
    f zero_le_one (fun p => ?_)
  · simpa using h
  have hk := coulombKineticEnergySymbol_nonneg sys (2 * Real.pi / L) p
  have hden : 0 < coulombKineticEnergySymbol sys (2 * Real.pi / L) p + c := by linarith
  rw [coulombFourierKineticH2_apply, coeff_dInvc, norm_mul, norm_div, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hk,
    abs_of_pos hden, one_mul]
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith [norm_nonneg (f p)]

omit [Fintype ν] in
lemma norm_stateMap_dInvc_le (c : ℝ) (hc : 2 ≤ c)
    (f : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    ‖molecularH2StateMap eta (2 * Real.pi / L) (dInvc sys L c hc f)‖ ≤ (1 / c) * ‖f‖ := by
  refine l2_norm_le_of_le _ f (by positivity) (fun p => ?_)
  have hk := coulombKineticEnergySymbol_nonneg sys (2 * Real.pi / L) p
  have hden : 0 < coulombKineticEnergySymbol sys (2 * Real.pi / L) p + c := by linarith
  rw [molecularH2StateMap_apply, coeff_dInvc, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hden, div_le_iff₀ hden]
  have hc0 : 0 < c := by linarith
  have : 1 / c * ‖f p‖ * (coulombKineticEnergySymbol sys (2 * Real.pi / L) p + c) =
      ‖f p‖ + ‖f p‖ * coulombKineticEnergySymbol sys (2 * Real.pi / L) p / c := by
    field_simp
    ring
  rw [this]
  have : 0 ≤ ‖f p‖ * coulombKineticEnergySymbol sys (2 * Real.pi / L) p / c := by positivity
  linarith

end Diagonal

/-! ## The resolvent and the propagator of an operator with a relative bound -/

section Resolvent

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)

/-- **The relative bound** `‖W u‖² ≤ ‖T u‖²/4 + K ‖S u‖²` of the potential part `W = H - T`. -/
def HasRelBound (K : ℝ) : Prop :=
  ∀ u : MolecularFourierH2 eta,
    ‖coulombFourierPotentialH2 sys (2 * Real.pi / L) H u‖ ^ 2 ≤
      1 / 4 * ‖coulombFourierKineticH2 sys (2 * Real.pi / L) u‖ ^ 2 +
        K * ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ ^ 2

/-- The shift `4K + 2` of the resolvent. -/
def relShift (K : ℝ) : ℝ := 4 * K + 2

lemma two_le_relShift {K : ℝ} (hK : 0 ≤ K) : 2 ≤ relShift K := by
  unfold relShift
  linarith

/-- The diagonal inverse at the shift `4K + 2`. -/
def dInvK {K : ℝ} (hK : 0 ≤ K) : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →L[ℂ]
    lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
  dInvc sys L (relShift K) (two_le_relShift hK)

omit [Fintype ν] in
/-- `‖W dInvK f‖ ≤ (3/4) ‖f‖`. -/
lemma norm_potential_dInvK_le {K : ℝ} (hK : 0 ≤ K) (hrel : HasRelBound sys L H K)
    (f : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    ‖coulombFourierPotentialH2 sys (2 * Real.pi / L) H (dInvK sys L hK f)‖ ≤ (3 / 4) * ‖f‖ := by
  set x := dInvK sys L hK f
  have h := hrel x
  have hT := norm_kinetic_dInvc_le sys L (relShift K) (two_le_relShift hK) f
  have hS := norm_stateMap_dInvc_le sys L (relShift K) (two_le_relShift hK) f
  have hc : relShift K = 4 * K + 2 := rfl
  have hT2 : ‖coulombFourierKineticH2 sys (2 * Real.pi / L) x‖ ^ 2 ≤ ‖f‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hT 2
  have hS2 : ‖molecularH2StateMap eta (2 * Real.pi / L) x‖ ^ 2 ≤
      (1 / relShift K * ‖f‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hS 2
  have hpos : 0 < 4 * K + 2 := by linarith
  have key : K * (1 / relShift K * ‖f‖) ^ 2 ≤ 1 / 4 * ‖f‖ ^ 2 := by
    rw [hc]
    have e : K * (1 / (4 * K + 2) * ‖f‖) ^ 2 = K / (4 * K + 2) ^ 2 * ‖f‖ ^ 2 := by
      rw [mul_pow, div_pow, one_pow]
      ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hW2 : ‖coulombFourierPotentialH2 sys (2 * Real.pi / L) H x‖ ^ 2 ≤ (3 / 4 * ‖f‖) ^ 2 := by
    calc _ ≤ 1 / 4 * ‖coulombFourierKineticH2 sys (2 * Real.pi / L) x‖ ^ 2 +
          K * ‖molecularH2StateMap eta (2 * Real.pi / L) x‖ ^ 2 := h
      _ ≤ 1 / 4 * ‖f‖ ^ 2 + K * (1 / relShift K * ‖f‖) ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left hT2 (by norm_num))
            (mul_le_mul_of_nonneg_left hS2 hK)
      _ ≤ 1 / 4 * ‖f‖ ^ 2 + 1 / 4 * ‖f‖ ^ 2 := by linarith
      _ ≤ (3 / 4 * ‖f‖) ^ 2 := by nlinarith [sq_nonneg ‖f‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hW2

/-- The operator `W dInvK`. -/
def kOpK {K : ℝ} (hK : 0 ≤ K) : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →L[ℂ]
    lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
  (coulombFourierPotentialH2 sys (2 * Real.pi / L) H).comp (dInvK sys L hK)

omit [Fintype ν] in
lemma norm_kOpK_lt_one {K : ℝ} (hK : 0 ≤ K) (hrel : HasRelBound sys L H K) : ‖kOpK sys L H hK‖ < 1 := by
  have h : ‖kOpK sys L H hK‖ ≤ 3 / 4 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (fun f => norm_potential_dInvK_le sys L H hK hrel f)
  linarith

/-- The unit `1 + W dInvK` (Neumann series). -/
def unitK {K : ℝ} (hK : 0 ≤ K) (hrel : HasRelBound sys L H K) :
    (lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →L[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)ˣ :=
  Units.oneSub (-kOpK sys L H hK) (by rw [norm_neg]; exact norm_kOpK_lt_one sys L H hK hrel)

omit [Fintype ν] in
lemma unitK_val {K : ℝ} (hK : 0 ≤ K) (hrel : HasRelBound sys L H K)
    (v : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    (unitK sys L H hK hrel).val v = v + kOpK sys L H hK v := by
  simp [unitK, Units.val_oneSub]

/-- The resolvent `(H + c S)⁻¹ : ℓ² → H²` (weighted coordinates), `c = 4K + 2`. -/
def resolventGK {K : ℝ} (hK : 0 ≤ K) (hrel : HasRelBound sys L H K) :
    lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →L[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
  (dInvK sys L hK).comp ((unitK sys L H hK hrel)⁻¹).val

omit [Fintype ν] in
/-- `(H + c S) G = 1`. -/
lemma H_add_shift_resolventGK {K : ℝ} (hK : 0 ≤ K) (hrel : HasRelBound sys L H K)
    (f : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    H (resolventGK sys L H hK hrel f) +
      (relShift K : ℂ) • molecularH2StateMap eta (2 * Real.pi / L)
        (resolventGK sys L H hK hrel f) = f := by
  set U := unitK sys L H hK hrel
  set v := (U⁻¹).val f
  have hG : resolventGK sys L H hK hrel f = dInvK sys L hK v := rfl
  rw [hG, coulombFourierHamiltonianH2_decomposition sys (2 * Real.pi / L) H]
  have h1 := kinetic_dInvc_add sys L (relShift K) (two_le_relShift hK) v
  have h2 : U.val v = f := by
    change (U.val * (U⁻¹).val) f = f
    rw [Units.mul_inv]
    rfl
  rw [unitK_val] at h2
  calc coulombFourierKineticH2 sys (2 * Real.pi / L) (dInvK sys L hK v) +
        coulombFourierPotentialH2 sys (2 * Real.pi / L) H (dInvK sys L hK v) +
        (relShift K : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) (dInvK sys L hK v)
      = (coulombFourierKineticH2 sys (2 * Real.pi / L) (dInvK sys L hK v) +
          (relShift K : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) (dInvK sys L hK v)) +
        coulombFourierPotentialH2 sys (2 * Real.pi / L) H (dInvK sys L hK v) := by abel
    _ = v + kOpK sys L H hK v := by rw [show dInvK sys L hK v =
          dInvc sys L (relShift K) (two_le_relShift hK) v from rfl, h1]; rfl
    _ = f := h2

omit [Fintype ν] in
/-- `G (H + c S) = 1`. -/
lemma resolventGK_H_add_shift {K : ℝ} (hK : 0 ≤ K) (hrel : HasRelBound sys L H K)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    resolventGK sys L H hK hrel
      (H x + (relShift K : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) x) = x := by
  set U := unitK sys L H hK hrel
  set y := coulombFourierKineticH2 sys (2 * Real.pi / L) x +
    (relShift K : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) x
  have hy : dInvK sys L hK y = x := dInvc_kinetic_add sys L (relShift K) (two_le_relShift hK) x
  have hsum : H x + (relShift K : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) x =
      U.val y := by
    rw [unitK_val]
    simp only [kOpK, ContinuousLinearMap.coe_comp, Function.comp_apply, hy]
    rw [coulombFourierHamiltonianH2_decomposition sys (2 * Real.pi / L) H]
    simp only [y]
    abel
  rw [hsum]
  change dInvK sys L hK (((U⁻¹).val * U.val) y) = x
  rw [Units.inv_mul]
  exact hy

/-- The resolvent operator `R = S (H + c S)⁻¹` on `ℓ²`. -/
def resolventRK {K : ℝ} (hK : 0 ≤ K) (hrel : HasRelBound sys L H K) :
    lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →L[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
  (molecularH2StateMap eta (2 * Real.pi / L)).comp (resolventGK sys L H hK hrel)

omit [Fintype ν] in
lemma resolventRK_compact {K : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (hrel : HasRelBound sys L H K) :
    IsCompactOperator (resolventRK sys L H hK hrel) := by
  have hS : IsCompactOperator (molecularH2StateMap eta (2 * Real.pi / L)) :=
    isCompactOperator_stateMap (2 * Real.pi / L) (by positivity)
  exact hS.comp_clm (resolventGK sys L H hK hrel)

omit [Fintype ν] in
lemma resolventRK_symm {K : ℝ} (hK : 0 ≤ K) (hrel : HasRelBound sys L H K)
    (hsymm : ∀ u u' : MolecularFourierH2 eta,
      ⟪molecularH2StateMap eta (2 * Real.pi / L) u, H u'⟫_ℂ =
        ⟪H u, molecularH2StateMap eta (2 * Real.pi / L) u'⟫_ℂ) :
    (resolventRK sys L H hK hrel :
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →ₗ[ℂ]
        lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2).IsSymmetric := by
  intro f f'
  set G := resolventGK sys L H hK hrel
  set S := molecularH2StateMap eta (2 * Real.pi / L)
  have hf := H_add_shift_resolventGK sys L H hK hrel f
  have hf' := H_add_shift_resolventGK sys L H hK hrel f'
  change ⟪S (G f), f'⟫_ℂ = ⟪f, S (G f')⟫_ℂ
  conv_lhs => rw [← hf']
  conv_rhs => rw [← hf]
  rw [inner_add_right, inner_add_left, inner_smul_right, inner_smul_left, Complex.conj_ofReal,
    hsymm]

omit [Fintype ν] in
lemma resolventRK_injective {K : ℝ} (hK : 0 ≤ K) (hrel : HasRelBound sys L H K) :
    Function.Injective (resolventRK sys L H hK hrel) := by
  intro f f' h
  have h1 : resolventGK sys L H hK hrel f = resolventGK sys L H hK hrel f' :=
    molecularH2StateMap_injective eta (2 * Real.pi / L) h
  rw [← H_add_shift_resolventGK sys L H hK hrel f, ← H_add_shift_resolventGK sys L H hK hrel f',
    h1]

omit [Fintype ν] in
lemma resolventRK_apply_H {K : ℝ} (hK : 0 ≤ K) (hrel : HasRelBound sys L H K) (u : MolecularFourierH2 eta) :
    resolventRK sys L H hK hrel
      (H u + (relShift K : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) u) =
      molecularH2StateMap eta (2 * Real.pi / L) u := by
  change molecularH2StateMap eta (2 * Real.pi / L) (resolventGK sys L H hK hrel
    (H u + (relShift K : ℂ) • molecularH2StateMap eta (2 * Real.pi / L) u)) = _
  rw [resolventGK_H_add_shift]

omit [Fintype ν] in
/-- **The propagator of a completed operator with a relative bound, Fourier side.** For a
completed operator `H : H² → ℓ²` that is symmetric on `H²` and whose potential part satisfies
the relative bound with constant `K`, there is a strongly continuous unitary group `U` on `ℓ²`
that maps the domain `S(H²)` to itself and commutes with `H`, such that `t ↦ U t (S u)` solves
`i ψ' = H ψ`, and every differentiable solution in `S(H²)` is `U t` applied to its initial
value (the release's `exists_coulombFourierPropagator`, for any such `H`). -/
theorem exists_fourierPropagator_of_relBound {K : ℝ} (hK : 0 ≤ K) (hL : 0 < L) (hrel : HasRelBound sys L H K)
    (hsymm : ∀ u u' : MolecularFourierH2 eta,
      ⟪molecularH2StateMap eta (2 * Real.pi / L) u, H u'⟫_ℂ =
        ⟪H u, molecularH2StateMap eta (2 * Real.pi / L) u'⟫_ℂ) :
    ∃ U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
        lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2,
      (∀ x, U 0 x = x) ∧
      (∀ s t x, U (s + t) x = U s (U t x)) ∧
      (∀ x, Continuous fun t => U t x) ∧
      (∀ t u, ∃ u' : MolecularFourierH2 eta,
        molecularH2StateMap eta (2 * Real.pi / L) u' =
          U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u)) ∧
      (∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
        (-(Complex.I • U t (H u))) t) ∧
      (∀ (φ : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
        (v : ℝ → MolecularFourierH2 eta),
        (∀ t, φ t = molecularH2StateMap eta (2 * Real.pi / L) (v t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • H (v t))) t) → ∀ t, φ t = U t (φ 0)) := by
  set R := resolventRK sys L H hK hrel
  set S := molecularH2StateMap eta (2 * Real.pi / L)
  set G := resolventGK sys L H hK hrel
  set c := relShift K
  obtain ⟨U, h0, hadd, hcont, hcomm, hderiv, huniq⟩ := exists_propagator
    (resolventRK_compact sys L H hK hL hrel) (resolventRK_symm sys L H hK hrel hsymm)
    (resolventRK_injective sys L H hK hrel) c
  have hRy : ∀ u, R (H u + (c : ℂ) • S u) = S u := resolventRK_apply_H sys L H hK hrel
  refine ⟨U, h0, hadd, hcont, ?_, ?_, ?_⟩
  · intro t u
    set y := H u + (c : ℂ) • S u
    refine ⟨G (U t y), ?_, ?_⟩
    · change R (U t y) = U t (S u)
      rw [← hcomm, hRy]
    · have h1 := H_add_shift_resolventGK sys L H hK hrel (U t y)
      have h2 : S (G (U t y)) = U t (S u) := by
        change R (U t y) = U t (S u)
        rw [← hcomm, hRy]
      have h3 : H (G (U t y)) = U t y - (c : ℂ) • S (G (U t y)) := eq_sub_of_add_eq h1
      rw [h3, h2, ← map_smul, ← map_sub]
      congr 1
      simp only [y]
      abel
  · intro t u
    have h := hderiv t (H u + (c : ℂ) • S u)
    rw [show R (H u + (c : ℂ) • S u) = S u from hRy u] at h
    simp only [add_sub_cancel_right] at h
    exact h
  · intro φ v hφ hd t
    refine huniq φ (fun s => H (v s) + (c : ℂ) • S (v s)) (fun s => ?_) (fun s => ?_) t
    · rw [hRy, hφ]
    · have := hd s
      have e : H (v s) + (c : ℂ) • S (v s) - (c : ℂ) • φ s = H (v s) := by
        rw [hφ]
        abel
      rw [e]
      exact this

end Resolvent

/-! ## The completed `g_L` operator: symmetry and the relative bound -/

section GLOperator

variable (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)

include hKernel in
/-- On cubic truncations the completed `g_L` operator has the finite form. -/
lemma gL_inner_truncate_eq_finite (N : ℕ) (x y : MolecularFourierH2 eta) :
    ⟪molecularH2StateMap eta (2 * Real.pi / L) (molecularH2Truncate N x),
        H (molecularH2Truncate N y)⟫_ℂ =
      ⟪fullCoeffVector (finiteFourierCoeffExtract N (molecularH2Coeff (2 * Real.pi / L) x)),
        gLham sys L θ N
          (fullCoeffVector (finiteFourierCoeffExtract N
            (molecularH2Coeff (2 * Real.pi / L) y)))⟫_ℂ := by
  have h := gLFourierDomainEmbedding_inner_eq sys L θ H hKernel N
    (fullCoeffVector (finiteFourierCoeffExtract N (molecularH2Coeff (2 * Real.pi / L) x)))
    (fullCoeffVector (finiteFourierCoeffExtract N (molecularH2Coeff (2 * Real.pi / L) y)))
  rw [finiteFourierDomainEmbedding_extract, finiteFourierDomainEmbedding_extract,
    molecularFourierDomainOperator_apply_equiv, molecularFourierH2DomainEquiv_coe] at h
  exact h

include hKernel in
/-- **Symmetry of the completed `g_L` operator on `H²`.** -/
theorem gLH2_symm {R : ℝ} (hθ : Profile R θ) (u u' : MolecularFourierH2 eta) :
    ⟪molecularH2StateMap eta (2 * Real.pi / L) u, H u'⟫_ℂ =
      ⟪H u, molecularH2StateMap eta (2 * Real.pi / L) u'⟫_ℂ := by
  set S := molecularH2StateMap eta (2 * Real.pi / L)
  have hN : ∀ N, ⟪S (molecularH2Truncate N u), H (molecularH2Truncate N u')⟫_ℂ =
      ⟪H (molecularH2Truncate N u), S (molecularH2Truncate N u')⟫_ℂ := by
    intro N
    rw [gL_inner_truncate_eq_finite sys L θ H hKernel, ← inner_conj_symm (H _) (S _),
      gL_inner_truncate_eq_finite sys L θ H hKernel, inner_conj_symm,
      gLham_isSymmetric hθ sys L N]
  have hu := molecularH2Truncate_tendsto u
  have hu' := molecularH2Truncate_tendsto u'
  have h1 : Tendsto (fun N => ⟪S (molecularH2Truncate N u), H (molecularH2Truncate N u')⟫_ℂ)
      atTop (𝓝 ⟪S u, H u'⟫_ℂ) :=
    ((S.continuous.tendsto u).comp hu).inner ((H.continuous.tendsto u').comp hu')
  have h2 : Tendsto (fun N => ⟪H (molecularH2Truncate N u), S (molecularH2Truncate N u')⟫_ℂ)
      atTop (𝓝 ⟪H u, S u'⟫_ℂ) :=
    ((H.continuous.tendsto u).comp hu).inner ((S.continuous.tendsto u').comp hu')
  refine tendsto_nhds_unique h1 ?_
  exact h2.congr fun N => (hN N).symm

lemma fourierKernelFiniteOutput_gLpot_eq (N : ℕ) (u : MolecularFourierH2 eta) (count : ℕ) :
    fourierKernelFiniteOutput (2 * Real.pi / L) (gLlatPot sys L θ) N u count =
      gLpot sys L θ count
        (fullCoeffVector (finiteFourierCoeffExtract count
          (molecularH2Coeff (2 * Real.pi / L) (molecularH2Truncate N u)))) := by
  ext q
  rw [gLpot_eq_latticeKernel]
  rfl

include hKernel in
/-- The compressions of the completed `g_L` potential are the finite potentials. -/
lemma gL_truncate_potential_eq (N count : ℕ) (hN : N ≤ count) (u : MolecularFourierH2 eta) :
    molecularH2Truncate count
        (coulombFourierPotentialH2 sys (2 * Real.pi / L) H (molecularH2Truncate N u)) =
      finiteFourierLpEmbed eta count
        (gLpot sys L θ count
          (fullCoeffVector (finiteFourierCoeffExtract count
            (molecularH2Coeff (2 * Real.pi / L) (molecularH2Truncate N u))))).ofLp := by
  rw [← fourierKernelFiniteOutput_gLpot_eq]
  exact (fourierKernelFiniteOutput_embed_eq_truncate (2 * Real.pi / L) (gLlatPot sys L θ) N u _
    (fun q => gLFourierPotentialH2_core sys L θ H hKernel N u q) count hN).symm

/-- **Relative bound of the `g_L` potential.** For every `α > 0`,
`‖W u‖² ≤ C² (α ‖T u‖² + (1 + 1/α) ‖S u‖²)`, with the mass-weighted `H¹` constant
`C = gLmassConst` of the `g_L` potential. -/
theorem gL_potential_sq_le {L : ℝ} {R : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {α : ℝ} (hα : 0 < α)
    (u : MolecularFourierH2 eta) :
    ‖coulombFourierPotentialH2 sys (2 * Real.pi / L) H u‖ ^ 2 ≤
      gLmassConst sys L (tv R θ) Hunit ^ 2 *
        (α * ‖coulombFourierKineticH2 sys (2 * Real.pi / L) u‖ ^ 2 +
          (1 + 1 / α) * ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ ^ 2) := by
  set g := 2 * Real.pi / L
  set C := gLmassConst sys L (tv R θ) Hunit
  set W := coulombFourierPotentialH2 sys g H
  set T := coulombFourierKineticH2 sys g
  set S := molecularH2StateMap eta g
  set B : MolecularFourierH2 eta → ℝ := fun x => C ^ 2 * (α * ‖T x‖ ^ 2 + (1 + 1 / α) * ‖S x‖ ^ 2)
    with hB
  -- finite compressions
  have hfin : ∀ N count, N ≤ count →
      ‖molecularH2Truncate count (W (molecularH2Truncate N u))‖ ^ 2 ≤ B
          (molecularH2Truncate N u) := by
    intro N count hc
    rw [gL_truncate_potential_eq sys L θ H hKernel N count hc u,
        finiteFourierLpEmbed_norm_eq_fullCoeffVector]
    have hmass := gLpot_massBound sys hL hθ Hunit hPeriodic count
      (fullCoeffVector (finiteFourierCoeffExtract count
          (molecularH2Coeff g (molecularH2Truncate N u))))
    have hw := weightedNormSq_extract_le sys g (molecularH2Truncate N u) count hα
    calc ‖fullCoeffVector (gLpot sys L θ count
          (fullCoeffVector (finiteFourierCoeffExtract count
            (molecularH2Coeff g (molecularH2Truncate N u))))).ofLp‖ ^ 2
        = ‖gLpot sys L θ count
          (fullCoeffVector (finiteFourierCoeffExtract count
            (molecularH2Coeff g (molecularH2Truncate N u))))‖ ^ 2 := rfl
      _ ≤ C ^ 2 * weightedNormSq
            (fun p => 1 + massKineticSymbol sys.mass (finitePlaneWaveKabs g count) p)
            (fullCoeffVector (finiteFourierCoeffExtract count
              (molecularH2Coeff g (molecularH2Truncate N u)))) := hmass
      _ ≤ B (molecularH2Truncate N u) := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
  -- remove the output truncation
  have hN : ∀ N, ‖W (molecularH2Truncate N u)‖ ^ 2 ≤ B (molecularH2Truncate N u) := by
    intro N
    have ht := (molecularH2Truncate_tendsto (W (molecularH2Truncate N u))).norm.pow 2
    exact le_of_tendsto ht (eventually_atTop.mpr ⟨N, fun count hc => hfin N count hc⟩)
  -- remove the input truncation
  have hu := molecularH2Truncate_tendsto u
  have hL1 : Tendsto (fun N => ‖W (molecularH2Truncate N u)‖ ^ 2) atTop (𝓝 (‖W u‖ ^ 2)) :=
    ((W.continuous.tendsto u).comp hu).norm.pow 2
  have hR1 : Tendsto (fun N => B (molecularH2Truncate N u)) atTop (𝓝 (B u)) := by
    have hT := ((T.continuous.tendsto u).comp hu).norm.pow 2
    have hS := ((S.continuous.tendsto u).comp hu).norm.pow 2
    exact ((hT.const_mul α).add (hS.const_mul (1 + 1 / α))).const_mul (C ^ 2)
  exact le_of_tendsto_of_tendsto' hL1 hR1 hN

/-- The relative-bound constant `C²(4C² + 2)` of the `g_L` potential. -/
def gLrelConst (sys : CoulombSystem eta ν) (L V Hunit : ℝ) : ℝ :=
  gLmassConst sys L V Hunit ^ 2 * (4 * gLmassConst sys L V Hunit ^ 2 + 2)

lemma gLrelConst_nonneg (sys : CoulombSystem eta ν) (L V Hunit : ℝ) :
    0 ≤ gLrelConst sys L V Hunit := by
  unfold gLrelConst
  positivity

/-- **The relative bound with constant `1/4`** for the completed `g_L` operator. -/
theorem gL_potential_sq_le_quarter {L : ℝ} {R : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    HasRelBound sys L H (gLrelConst sys L (tv R θ) Hunit) := by
  intro u
  set C := gLmassConst sys L (tv R θ) Hunit
  have hα : 0 < 1 / (4 * C ^ 2 + 1) := by positivity
  have h := gL_potential_sq_le sys hL hθ H hKernel Hunit hPeriodic hα u
  have h1 : C ^ 2 * (1 / (4 * C ^ 2 + 1)) ≤ 1 / 4 := by
    rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg C]
  have h2 : 1 + 1 / (1 / (4 * C ^ 2 + 1)) = 4 * C ^ 2 + 2 := by
    rw [one_div_one_div]
    ring
  rw [h2] at h
  have hT := sq_nonneg ‖coulombFourierKineticH2 sys (2 * Real.pi / L) u‖
  have hK : gLrelConst sys L (tv R θ) Hunit = C ^ 2 * (4 * C ^ 2 + 2) := rfl
  rw [hK]
  calc _ ≤ C ^ 2 * (1 / (4 * C ^ 2 + 1) * ‖coulombFourierKineticH2 sys (2 * Real.pi / L) u‖ ^ 2 +
          (4 * C ^ 2 + 2) * ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ ^ 2) := h
    _ = (C ^ 2 * (1 / (4 * C ^ 2 + 1))) * ‖coulombFourierKineticH2 sys (2 * Real.pi / L) u‖ ^ 2 +
          C ^ 2 * (4 * C ^ 2 + 2) * ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

end GLOperator

/-! ## The torus relation is the graph of the completed operator -/

section Position

variable (sys : CoulombSystem eta ν)

/-- **The `g_L` Hamiltonian relation is the graph of the completed operator**: `H_L f = h`
(`HasGLHamiltonian`) if and only if `f` and `h` are the position-space images of `u` and `H u`
for some `u ∈ H²`. -/
theorem hasGLHamiltonian_iff_H2 {L R : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (hR : R ≤ L / 2)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
    (f h : MolecularPositionL2 eta) :
    HasGLHamiltonian sys L θ f h ↔
      ∃ u : MolecularFourierH2 eta,
        molecularPositionSynthesis eta (molecularH2StateMap eta (2 * Real.pi / L) u) = f ∧
        molecularPositionSynthesis eta (H u) = h := by
  have hpt : ∀ u, HasL2PointwisePotential volume (gLFourierPotential sys L θ)
      (molecularPositionH2StateMap eta (2 * Real.pi / L) u)
      (coulombPositionPotentialH2 sys (2 * Real.pi / L) H u) := fun u =>
    gLPositionPotentialH2_pointwise sys L θ H hKernel (gLFourierPotential sys L θ)
      (gLFourierPotential_memLp sys hL hθ) (gLFourierPotential_fourierCoeff sys hL hθ hR) u
  have hdec : ∀ u, molecularPositionHamiltonianH2 H u =
      coulombPositionKineticH2 sys (2 * Real.pi / L) u +
        coulombPositionPotentialH2 sys (2 * Real.pi / L) H u :=
    fun u => coulombPositionHamiltonianH2_decomposition sys (2 * Real.pi / L) H u
  constructor
  · rintro ⟨v, hv, hK⟩
    obtain ⟨u, hu1, hu2⟩ := (hasCoulombContDiffWeakKinetic_iff_H2 sys L f (h - v)).mp hK
    refine ⟨u, hu1, ?_⟩
    have hW : coulombPositionPotentialH2 sys (2 * Real.pi / L) H u = v := by
      apply Lp.ext
      have h1 := hpt u
      rw [hu1] at h1
      filter_upwards [h1, hv] with x hx1 hx2
      rw [hx1, hx2]
    have hH := hdec u
    rw [hu2, hW, sub_add_cancel] at hH
    exact hH
  · rintro ⟨u, rfl, rfl⟩
    refine ⟨coulombPositionPotentialH2 sys (2 * Real.pi / L) H u, hpt u, ?_⟩
    have e : molecularPositionSynthesis eta (H u) -
        coulombPositionPotentialH2 sys (2 * Real.pi / L) H u =
        coulombPositionKineticH2 sys (2 * Real.pi / L) u := by
      have hH := hdec u
      change molecularPositionSynthesis eta (H u) = _ at hH
      rw [hH]
      abel
    rw [e]
    exact (hasCoulombContDiffWeakKinetic_iff_H2 sys L _ _).mpr ⟨u, rfl, rfl⟩

/-- **The propagator of the `g_L` Hamiltonian.** On the position space `L²((T³)^η)` there is a
strongly continuous unitary group `U = e^{-iH_L t}` that preserves the graph of the `g_L`
Hamiltonian (zero mode removed), such that `t ↦ U t f` solves `i ψ' = H_L ψ` for every `f` in
the domain, and every differentiable curve in the graph that solves the Schrödinger equation is
`U t` applied to its initial value. -/
theorem exists_gLPropagator {L R : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) :
    ∃ U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, Continuous fun t => U t ψ) ∧
      (∀ t f h, HasGLHamiltonian sys L θ f h → HasGLHamiltonian sys L θ (U t f) (U t h)) ∧
      (∀ t f h, HasGLHamiltonian sys L θ f h →
        HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) ∧
      (∀ φ ζ : ℝ → MolecularPositionL2 eta, (∀ t, HasGLHamiltonian sys L θ (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) := by
  obtain ⟨H, hKernel, -⟩ := exists_gLFourierH2Operator sys hL hθ
    molecularCanonicalUnitHardyConstant canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨UF, h0, hadd, hcont, hgraph, hderiv, huniq⟩ :=
    exists_fourierPropagator_of_relBound sys L H
      (gLrelConst_nonneg sys L (tv R θ) molecularCanonicalUnitHardyConstant) hL
      (gL_potential_sq_le_quarter sys hL hθ H hKernel molecularCanonicalUnitHardyConstant
        canonicalPeriodicCoulombHardyBound_explicit)
      (gLH2_symm sys L θ H hKernel hθ)
  have hiff := hasGLHamiltonian_iff_H2 sys hL hθ hR H hKernel
  set Φ := molecularPositionSynthesis eta
  set U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta :=
    fun t => (Φ.symm.trans (UF t)).trans Φ with hU
  have hUapply : ∀ t ψ, U t ψ = Φ (UF t (Φ.symm ψ)) := fun t ψ => rfl
  -- the Hamiltonian relation is preserved
  have hgraphU : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasGLHamiltonian sys L θ (U t f) (U t h) := by
    intro t f h hfh
    obtain ⟨u, rfl, rfl⟩ := (hiff f h).mp hfh
    obtain ⟨u', hu'1, hu'2⟩ := hgraph t u
    refine (hiff _ _).mpr ⟨u', ?_, ?_⟩
    · rw [hUapply, LinearIsometryEquiv.symm_apply_apply, hu'1]
    · rw [hUapply, LinearIsometryEquiv.symm_apply_apply, hu'2]
  -- the Schrödinger equation
  have hΦd : ∀ (γ : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) γ' t,
      HasDerivAt γ γ' t → HasDerivAt (fun s => Φ (γ s)) (Φ γ') t := fun γ γ' t hγ =>
    ((Φ.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars
        ℝ).hasFDerivAt.comp_hasDerivAt t hγ
  have hΦsd : ∀ (γ : ℝ → MolecularPositionL2 eta) γ' t,
      HasDerivAt γ γ' t → HasDerivAt (fun s => Φ.symm (γ s)) (Φ.symm γ') t := fun γ γ' t hγ =>
    ((Φ.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars
        ℝ).hasFDerivAt.comp_hasDerivAt t hγ
  have hderivU : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t := by
    intro t f h hfh
    obtain ⟨u, rfl, rfl⟩ := (hiff f h).mp hfh
    have h1 := hΦd _ _ t (hderiv t u)
    simp only [hUapply, LinearIsometryEquiv.symm_apply_apply]
    rw [map_neg, map_smul] at h1
    exact h1
  -- uniqueness
  have huniqU : ∀ φ ζ : ℝ → MolecularPositionL2 eta,
      (∀ t, HasGLHamiltonian sys L θ (φ t) (ζ t)) →
      (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0) := by
    intro φ ζ hφζ hd t
    choose v hv1 hv2 using fun s => (hiff (φ s) (ζ s)).mp (hφζ s)
    have hF := huniq (fun s => Φ.symm (φ s)) v
      (fun s => by rw [← hv1 s, LinearIsometryEquiv.symm_apply_apply])
      (fun s => by
        have := hΦsd φ _ s (hd s)
        rw [map_neg, map_smul, ← hv2 s, LinearIsometryEquiv.symm_apply_apply] at this
        exact this) t
    rw [hUapply, ← hF, LinearIsometryEquiv.apply_symm_apply]
  refine ⟨U, fun ψ => ?_, fun s t ψ => ?_, fun ψ => ?_, hgraphU, hderivU, huniqU⟩
  · rw [hUapply, h0, LinearIsometryEquiv.apply_symm_apply]
  · rw [hUapply, hUapply, hUapply, LinearIsometryEquiv.symm_apply_apply, hadd]
  · exact Φ.continuous.comp (hcont _)

end Position

/-! ## `prop:free-dyn`, the free-space step, for the propagator of `H_L` -/

/-- **`prop:free-dyn`, the free-space step, for the propagator of the `g_L` Hamiltonian.** Under
the hypotheses of `free_dyn_torus` (with `R ≤ L/2`), there is a propagator `U = e^{-iH_L t}` of
the `g_L` Hamiltonian (zero mode removed) — strongly continuous, unitary, solving the Schrödinger
equation on the graph, and unique in that sense — for which the transplant `φ(s) = T(χ ψ_∞(s))`
satisfies `‖φ(t) - e^{-iC₀t} U(t) φ(0)‖ ≤ C ε t` and the observable bound of `free_dyn_torus`. -/
theorem free_dyn_gL (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
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
    ∃ U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      ((∀ ψ, U 0 ψ = ψ) ∧ (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
        (∀ ψ, Continuous fun t => U t ψ) ∧
        (∀ t f h, HasGLHamiltonian sys L θ f h →
          HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) ∧
        (∀ φ ζ : ℝ → MolecularPositionL2 eta, (∀ t, HasGLHamiltonian sys L θ (φ t) (ζ t)) →
          (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0))) ∧
      ‖X.chiW.cutL2 hL (ψ t) - Complex.exp (-(Complex.I * (zeroModeShift sys L θ).re * t)) •
          U t (X.chiW.cutL2 hL (ψ 0))‖ ≤ X.commConst * ε * t ∧
      ‖((∫ r, χo r * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - inner ℂ (U t (X.chiW.cutL2 hL (ψ 0)))
          (PlaneWaveDynamics.mulCLM G (U t (X.chiW.cutL2 hL (ψ 0))))‖ ≤
        ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.commConst * ε * t) := by
  obtain ⟨U, h0, hadd, hcont, -, hderiv, huniq⟩ := exists_gLPropagator sys hL hθ hR
  exact ⟨U, ⟨h0, hadd, hcont, hderiv, huniq⟩,
    free_dyn_torus sys hL hθ hR0 hρ hone P hP hpos U h0 hadd hcont hderiv X hret hSm hBm hχB hSB
      hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hχo0 hχo1 hχom G hG⟩

end

end FreeBoundary
