import PlaneWave.FluxBox.FlatElimination

/-!
# Flux route, stage 2, part 7: the flat ledger along the trajectory

* `XN_split`: `X_N = -i[T_N, Ŵ_c] + X^cm`, `X^cm = G^cm - P G^cm P` (the cube commutes with `T_N`);
* **`ledger_flat`**: along the exact evolution,
  `∫₀ᵗ Re⟨u, X_N u⟩ = -[Re⟨u, Ŵ_c u⟩]₀ᵗ + ∫₀ᵗ Re⟨u, i[W_N, Ŵ_c] u⟩ + ∫₀ᵗ e_{Ŵ_c} + ∫₀ᵗ Re⟨u, X^cm u⟩`,
  where the second integrand is `Re e_bd(u) - Re e_bd(φ) + n^fl(u)` (`flat_comm_eq`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Split

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) {N : ℕ} (n : ℕ)

/-- The centre-of-mass part of the projection flux on the box. -/
noncomputable def Xcm : En eta N →ₗ[ℂ] En eta N :=
  GcmN sys L p₀ N - PN N n ∘ₗ GcmN sys L p₀ N ∘ₗ PN N n

variable {sys L p₀}

omit [Fintype ν] in
lemma PN_TN_comm : PN N n ∘ₗ TN sys L N = TN sys L N ∘ₗ PN N n := by
  classical
  ext v q
  simp only [LinearMap.coe_comp, Function.comp_apply, FSKernel.res_apply, FSKernel.dg_apply]
  split_ifs <;> simp

/-- **`X_N = -i[T_N, Ŵ_c] + X^cm`.** -/
theorem XN_split (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    XN sys L p₀ N n = -(Complex.I • (TN sys L N ∘ₗ Whc sys L p₀ n - Whc sys L p₀ n ∘ₗ TN sys L N)) +
      Xcm sys L p₀ n := by
  unfold XN Xcm Whc
  rw [GN_split hL H hKernel]
  have hPT := PN_TN_comm (sys := sys) (L := L) (N := N) n
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, map_add, map_neg, map_smul, map_sub]
  have e1 : PN N n (TN sys L N (WhN sys L p₀ N (PN N n v))) =
      TN sys L N (PN N n (WhN sys L p₀ N (PN N n v))) := by
    have := congrArg (fun T => T (WhN sys L p₀ N (PN N n v))) hPT
    simpa using this
  have e2 : PN N n (WhN sys L p₀ N (TN sys L N (PN N n v))) =
      PN N n (WhN sys L p₀ N (PN N n (TN sys L N v))) := by
    have := congrArg (fun T => T v) hPT
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this]
  rw [e1, e2]
  module

lemma Whc_symm (hL : 0 < L) : (Whc sys L p₀ n : En eta N →ₗ[ℂ] En eta N).IsSymmetric := by
  intro x y
  unfold Whc
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_left, inner_sub_right]
  rw [WhN_symm hL x y, PN_symm n (WhN sys L p₀ N (PN N n x)) y,
    WhN_symm hL (PN N n x) (PN N n y), PN_symm n x (WhN sys L p₀ N (PN N n y))]

end Split

/-! ## Continuity along the trajectory -/

section Cont

variable {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) {N : ℕ}

omit [Fintype ν] in
lemma continuous_ub (D : EvoData L H) : Continuous fun s => ub H D N s :=
  (ext eta N).continuous.comp (D.cont _)

omit [Fintype ν] in
/-- `s ↦ ⟨A u_s, B u_s⟩` is continuous for linear maps `A, B` on the box. -/
lemma continuous_inner_ub (D : EvoData L H) (A B : En eta N →ₗ[ℂ] En eta N) :
    Continuous fun s => ⟪A (ub H D N s), B (ub H D N s)⟫_ℂ :=
  ((LinearMap.toContinuousLinearMap A).continuous.comp (continuous_ub H D)).inner
    ((LinearMap.toContinuousLinearMap B).continuous.comp (continuous_ub H D))

omit [Fintype ν] in
lemma continuous_form_ub (D : EvoData L H) (A : En eta N →ₗ[ℂ] En eta N) :
    Continuous fun s => (⟪ub H D N s, A (ub H D N s)⟫_ℂ).re :=
  Complex.continuous_re.comp (continuous_inner_ub H D LinearMap.id A)

end Cont

/-! ## The flat ledger -/

section Ledger

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta) {N : ℕ} (n : ℕ)

include hL hKernel in
/-- **The flat ledger**: along the exact evolution,
`∫₀ᵗ Re⟨u, X_N u⟩ = -[Re⟨u, Ŵ_c u⟩]₀ᵗ + ∫₀ᵗ Re⟨u, i[W_N, Ŵ_c] u⟩ + ∫₀ᵗ e_{Ŵ_c} + ∫₀ᵗ Re⟨u, X^cm u⟩`. -/
theorem ledger_flat (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, (⟪ub H D N s, XN sys L p₀ N n (ub H D N s)⟫_ℂ).re =
      -((⟪ub H D N t, Whc sys L p₀ n (ub H D N t)⟫_ℂ).re -
          (⟪ub H D N 0, Whc sys L p₀ n (ub H D N 0)⟫_ℂ).re) +
        (∫ s in (0 : ℝ)..t, (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Whc sys L p₀ n -
          Whc sys L p₀ n ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re) +
        (∫ s in (0 : ℝ)..t, eY sys H D (Whc sys L p₀ n : En eta N →ₗ[ℂ] En eta N) s) +
        ∫ s in (0 : ℝ)..t, (⟪ub H D N s, Xcm sys L p₀ n (ub H D N s)⟫_ℂ).re := by
  have hE := elim_box sys hL H hKernel (N := N) Hunit hPeriodic D (Whc sys L p₀ n)
    (Whc_symm (N := N) n hL) t
  have hsplit : ∀ s, (⟪ub H D N s, XN sys L p₀ N n (ub H D N s)⟫_ℂ).re =
      -(⟪ub H D N s, (Complex.I • (TN sys L N ∘ₗ Whc sys L p₀ n - Whc sys L p₀ n ∘ₗ TN sys L N))
        (ub H D N s)⟫_ℂ).re + (⟪ub H D N s, Xcm sys L p₀ n (ub H D N s)⟫_ℂ).re := by
    intro s
    rw [XN_split n hL H hKernel, LinearMap.add_apply, inner_add_right, Complex.add_re,
      LinearMap.neg_apply, inner_neg_right, Complex.neg_re]
  rw [intervalIntegral.integral_congr (fun s _ => hsplit s)]
  have hc1 := continuous_form_ub H (N := N) D
    (Complex.I • (TN sys L N ∘ₗ Whc sys L p₀ n - Whc sys L p₀ n ∘ₗ TN sys L N))
  have hc2 := continuous_form_ub H (N := N) D (Xcm sys L p₀ n)
  have hi1 : IntervalIntegrable (fun s => -(⟪ub H D N s, (Complex.I • (TN sys L N ∘ₗ Whc sys L p₀ n -
      Whc sys L p₀ n ∘ₗ TN sys L N)) (ub H D N s)⟫_ℂ).re) volume 0 t := hc1.neg.intervalIntegrable 0 t
  rw [intervalIntegral.integral_add hi1 (hc2.intervalIntegrable 0 t),
    intervalIntegral.integral_neg, hE]
  ring

end Ledger

end FSFlux
