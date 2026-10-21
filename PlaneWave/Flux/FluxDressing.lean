import PlaneWave.Flux.ForceForm

/-!
# Flux route, part 2: `prop:elim`, the flux dressing `Y = [Σ_b, A_{p₀}]`

The dressing of the bulk-fed force is a commutator with the bulk generator `Σ_b` of `app:source`
(`dev/PlaneWave.Source.BulkGenerator.lean`). With `B = A_{p₀} Σ_b` (bounded, as `ran Σ_b ⊂ D(T)`),

  `Y = [Σ_b, A_{p₀}] = -(B + B†)`,      kernel `Y(q, p) = σ(q, p) (A(p) - A(q))`.

* `Y` is bounded and Hermitian (`adjoint_Yop`);
* **`comm_Y`** (`prop:elim` (i), the weak form of `i[T, Y] = G_b`): for `u ∈ D(T)`,
  `i ⟨T u, Y S u⟩ - i ⟨Y S u, T u⟩ = G_b(u, u)` with
  `G_b(u, v) = i ⟨V_b S u, A v⟩ - i ⟨A u, V_b S v⟩`, the bulk-fed part of the force form
  (`V_b = R W Q + Q W R`);
* **`elim_deriv`, `elim_integral`** (eq:elim): along the exact evolution,
  `∫₀ᵗ G_b = ⟨ψ(t), Y ψ(t)⟩ - ⟨ψ₀, Y ψ₀⟩ - ∫₀ᵗ 𝔚`, `𝔚(u, v) = i ⟨W u, Y S v⟩ - i ⟨Y S u, W v⟩`;
* the kernel of `Y` (`Yop_apply`, `Yop_truncQ_apply`), the symbol bound on a crossing of channel
  `j` with transfer `ν` (`norm_yK_le`: `|Y(q, p)| ≤ (50/3)(m_top/m_{p₀}) c_j |ν|⁻²`) and the
  fibre Gram bound `‖Y 1_Q S u‖ ≤ C n^{-1/2} (‖S u‖ + ‖T u‖)` (`norm_YQ_le`, the dressed
  eq:lam-gen of `prop:elim` (ii));
* **`elim_bdry`** (eq:elim-bdry): `⟨ψ, Y ψ⟩ = 2 Re ⟨R ψ, Y 1_Q ψ⟩` and
  `|⟨ψ(t), Y ψ(t)⟩| ≤ C Ξ² K^{-3}` (`thm_elim_bdry`, uniform).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The dressing -/

section Dressing

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n) (p₀ : Fin eta)

/-- `B = A_{p₀} Σ_b = A_{p₀} Σ_D` (bounded: `ran Σ_b ⊂ D(T)`). -/
noncomputable def Bop : L2 eta →L[ℂ] L2 eta := Ap sys L p₀ ∘L SigD sys L n hL (by omega)

/-- **The flux dressing** `Y = [Σ_b, A_{p₀}] = -(B + B†)`. -/
noncomputable def Yop : L2 eta →L[ℂ] L2 eta :=
  -(Bop sys hL hn p₀ + ContinuousLinearMap.adjoint (Bop sys hL hn p₀))

lemma Bop_apply (x : L2 eta) (q : Cf eta) :
    Bop sys hL hn p₀ x q = (regSymbol sys (gF L) p₀ q : ℂ) * Sig sys L n hL hn x q := by
  unfold Bop
  rw [ContinuousLinearMap.comp_apply, Ap, KinMult.h2_apply, ← molecularH2StateMap_apply,
    stateMap_SigD hL hn x]
  rfl

/-- `Y` is Hermitian. -/
lemma adjoint_Yop : ContinuousLinearMap.adjoint (Yop sys hL hn p₀) = Yop sys hL hn p₀ := by
  unfold Yop
  rw [map_neg, map_add, ContinuousLinearMap.adjoint_adjoint, add_comm]

lemma inner_Yop_right (x y : L2 eta) :
    ⟪y, Yop sys hL hn p₀ x⟫_ℂ = -⟪y, Bop sys hL hn p₀ x⟫_ℂ - ⟪Bop sys hL hn p₀ y, x⟫_ℂ := by
  unfold Yop
  rw [neg_apply, add_apply, inner_neg_right, inner_add_right,
    ContinuousLinearMap.adjoint_inner_right]
  ring

omit [Fintype ν] in
/-- `⟨T u, A v⟩ = ⟨A u, T v⟩` (both are real diagonal multipliers). -/
lemma inner_kin_Ap_swap (u v : MolecularFourierH2 eta) :
    ⟪coulombFourierKineticH2 sys (gF L) u, Ap sys L p₀ v⟫_ℂ =
      ⟪Ap sys L p₀ u, coulombFourierKineticH2 sys (gF L) v⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun q => ?_
  rw [coulombFourierKineticH2_apply, coulombFourierKineticH2_apply, KinMult.h2_apply,
    KinMult.h2_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The bulk-fed part of the force form, `G_b(u, v) = i ⟨V_b S u, A v⟩ - i ⟨A u, V_b S v⟩`
(`V_b = R W Q + Q W R`, the crossings of the potential). -/
noncomputable def Gb (n : ℕ) (u v : MolecularFourierH2 eta) : ℂ :=
  Complex.I * ⟪Vb sys L n hL (Sm eta L u), Ap sys L p₀ v⟫_ℂ -
    Complex.I * ⟪Ap sys L p₀ u, Vb sys L n hL (Sm eta L v)⟫_ℂ

/-- **`prop:elim` (i)**, the weak form of `i[T, Y] = G_b`:
`i ⟨T u, Y S u⟩ - i ⟨Y S u, T u⟩ = G_b(u, u)` for `u ∈ D(T)`. -/
theorem comm_Y (u : MolecularFourierH2 eta) :
    Complex.I * ⟪coulombFourierKineticH2 sys (gF L) u, Yop sys hL hn p₀ (Sm eta L u)⟫_ℂ -
        Complex.I * ⟪Yop sys hL hn p₀ (Sm eta L u), coulombFourierKineticH2 sys (gF L) u⟫_ℂ =
      Gb sys hL p₀ n u u := by
  have hn0 : 0 < n := by omega
  set x := Sm eta L u with hx
  set y := coulombFourierKineticH2 sys (gF L) u with hy
  set a := Ap sys L p₀ u with ha
  -- `⟨y, B x⟩ = ⟨a, Σ_b y + V_b x⟩` (`[T, Σ_b] = V_b`)
  have h1 : ⟪y, Bop sys hL hn p₀ x⟫_ℂ = ⟪a, Sig sys L n hL hn y + Vb sys L n hL x⟫_ℂ := by
    have hk := kinetic_comm (sys := sys) hL hn u
    have e : Sig sys L n hL hn y + Vb sys L n hL x =
        coulombFourierKineticH2 sys (gF L) (SigD sys L n hL hn0 x) := by
      rw [hx, hy, ← hk]; abel
    rw [e]
    exact inner_kin_Ap_swap sys p₀ u (SigD sys L n hL hn0 x)
  -- `⟨B y, x⟩ = ⟨Σ_b y, a⟩`
  have h2 : ⟪Bop sys hL hn p₀ y, x⟫_ℂ = ⟪Sig sys L n hL hn y, a⟫_ℂ := by
    change ⟪Ap sys L p₀ (SigD sys L n hL hn0 y), Sm eta L u⟫_ℂ = _
    rw [Ap, ← (regKin sys (gF L) p₀).inner_stateMap_h2 (SigD sys L n hL hn0 y) u]
    rw [show molecularH2StateMap eta (gF L) (SigD sys L n hL hn0 y) = Sig sys L n hL hn y from
      stateMap_SigD hL hn y]
  have hY : ⟪y, Yop sys hL hn p₀ x⟫_ℂ =
      -⟪a, Sig sys L n hL hn y⟫_ℂ - ⟪a, Vb sys L n hL x⟫_ℂ -
        conj ⟪a, Sig sys L n hL hn y⟫_ℂ := by
    rw [inner_Yop_right, h1, h2, inner_add_right, ← inner_conj_symm (Sig sys L n hL hn y) a]
    ring
  rw [← inner_conj_symm (Yop sys hL hn p₀ x) y, hY]
  unfold Gb
  rw [← hx, ← ha, ← inner_conj_symm (Vb sys L n hL x) a]
  simp only [map_sub, map_neg, Complex.conj_conj]
  ring

/-- The dressed remainder form `𝔚(u, v) = i ⟨W u, Y S v⟩ - i ⟨Y S u, W v⟩`. -/
noncomputable def Wf (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (u v : MolecularFourierH2 eta) : ℂ :=
  Complex.I * ⟪Wp sys L H u, Yop sys hL hn p₀ (Sm eta L v)⟫_ℂ -
    Complex.I * ⟪Yop sys hL hn p₀ (Sm eta L u), Wp sys L H v⟫_ℂ

end Dressing

/-! ## eq:elim along the exact evolution -/

section Elim

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta)

omit [Fintype ν] in
/-- **The derivative of a bounded Hermitian observable** along the exact evolution:
`d/dt ⟨ψ, Z ψ⟩ = i ⟨H ψ, Z ψ⟩ - i ⟨Z ψ, H ψ⟩`. -/
theorem deriv_expect_herm (D : EvoData L H) (Z : L2 eta →L[ℂ] L2 eta)
    (hZ : ContinuousLinearMap.adjoint Z = Z) (t : ℝ) :
    HasDerivAt (fun s => ⟪D.U s (Sm eta L D.u₀), Z (D.U s (Sm eta L D.u₀))⟫_ℂ)
      (Complex.I * ⟪D.U t (H D.u₀), Z (D.U t (Sm eta L D.u₀))⟫_ℂ -
        Complex.I * ⟪Z (D.U t (Sm eta L D.u₀)), D.U t (H D.u₀)⟫_ℂ) t := by
  have hψ := D.deriv t D.u₀
  have hZψ : HasDerivAt (fun s => Z (D.U s (Sm eta L D.u₀)))
      (Z (-(Complex.I • D.U t (H D.u₀)))) t :=
    (Z.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hψ
  have h := hψ.inner ℂ hZψ
  have e : ⟪D.U t (Sm eta L D.u₀), Z (D.U t (H D.u₀))⟫_ℂ =
      ⟪Z (D.U t (Sm eta L D.u₀)), D.U t (H D.u₀)⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left Z (D.U t (H D.u₀)) (D.U t (Sm eta L D.u₀)), hZ]
  refine h.congr_deriv ?_
  rw [map_neg, map_smul, inner_neg_right, inner_smul_right, inner_neg_left, inner_smul_left,
    Complex.conj_I, e]
  ring

/-- **eq:elim, derivative form**: `d/dt ⟨ψ, Y ψ⟩ = G_b(w_t, w_t) + 𝔚(w_t, w_t)`. -/
theorem elim_deriv (D : EvoData L H) (t : ℝ) :
    HasDerivAt (fun s => ⟪D.U s (Sm eta L D.u₀), Yop sys hL hn p₀ (D.U s (Sm eta L D.u₀))⟫_ℂ)
      (Gb sys hL p₀ n (traj H D t) (traj H D t) +
        Wf sys hL hn p₀ H (traj H D t) (traj H D t)) t := by
  have h := deriv_expect_herm H D (Yop sys hL hn p₀) (adjoint_Yop sys hL hn p₀) t
  refine h.congr_deriv ?_
  set w := traj H D t
  have hS : D.U t (Sm eta L D.u₀) = Sm eta L w := (traj_S H D t).symm
  have hH : D.U t (H D.u₀) = coulombFourierKineticH2 sys (gF L) w + Wp sys L H w := by
    rw [← traj_H]; exact coulombFourierHamiltonianH2_decomposition sys (gF L) H w
  rw [hS, hH, inner_add_left, inner_add_right, ← comm_Y sys hL hn p₀ w]
  unfold Wf
  ring

include hKernel hL in
/-- `s ↦ T w_s` is continuous (the elliptic estimate). -/
lemma continuous_T_traj (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) : Continuous fun s => coulombFourierKineticH2 sys (gF L) (traj H D s) := by
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hb := relB_nonneg sys L Hunit hC
  rw [Metric.continuous_iff]
  intro t ε hε
  have hc1 := (D.cont (H D.u₀)).continuousAt (x := t)
  have hc2 := (D.cont (Sm eta L D.u₀)).continuousAt (x := t)
  rw [Metric.continuousAt_iff] at hc1 hc2
  obtain ⟨δ₁, hδ₁, h1⟩ := hc1 (ε / 4) (by positivity)
  obtain ⟨δ₂, hδ₂, h2⟩ := hc2 (ε / (4 * (1 + relB sys L Hunit))) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs => ?_⟩
  have hs1 : dist s t < δ₁ := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : dist s t < δ₂ := lt_of_lt_of_le hs (min_le_right _ _)
  rw [dist_eq_norm, ← map_sub]
  set d := traj H D s - traj H D t
  have hT := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC d
  have hHd : ‖H d‖ < ε / 4 := by
    have := h1 hs1
    rw [dist_eq_norm] at this
    simp only [d, map_sub, traj_H]
    exact this
  have hSd : ‖molecularH2StateMap eta (2 * Real.pi / L) d‖ < ε / (4 * (1 + relB sys L Hunit)) := by
    have := h2 hs2
    rw [dist_eq_norm] at this
    change ‖Sm eta L d‖ < _
    simp only [d, map_sub, traj_S]
    exact this
  have hb1 : 0 < 1 + relB sys L Hunit := by linarith
  have key : 2 * relB sys L Hunit * ‖molecularH2StateMap eta (2 * Real.pi / L) d‖ ≤ ε / 2 := by
    have h3 : relB sys L Hunit * ‖molecularH2StateMap eta (2 * Real.pi / L) d‖ ≤
        (1 + relB sys L Hunit) * (ε / (4 * (1 + relB sys L Hunit))) := by
      apply mul_le_mul (by linarith) hSd.le (norm_nonneg _) hb1.le
    have h4 : (1 + relB sys L Hunit) * (ε / (4 * (1 + relB sys L Hunit))) = ε / 4 := by
      field_simp
    linarith
  change ‖coulombFourierKineticH2 sys (gF L) d‖ < ε
  have : ‖coulombFourierKineticH2 sys (gF L) d‖ ≤
      2 * ‖H d‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta (2 * Real.pi / L) d‖ := hT
  linarith

include hKernel hL in
lemma continuous_W_traj (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) : Continuous fun s => Wp sys L H (traj H D s) := by
  have e : (fun s => Wp sys L H (traj H D s)) =
      fun s => D.U s (H D.u₀) - coulombFourierKineticH2 sys (gF L) (traj H D s) := by
    funext s
    rw [← traj_H, coulombFourierHamiltonianH2_decomposition sys (gF L) H (traj H D s)]
    abel
  rw [e]
  exact (D.cont _).sub (continuous_T_traj sys hL H hKernel Hunit hPeriodic D)

omit [Fintype ν] in
lemma continuous_S_traj (D : EvoData L H) : Continuous fun s => Sm eta L (traj H D s) := by
  have e : (fun s => Sm eta L (traj H D s)) = fun s => D.U s (Sm eta L D.u₀) :=
    funext fun s => traj_S H D s
  rw [e]; exact D.cont _

include hKernel hL in
lemma continuous_Gb_traj (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) : Continuous fun s => Gb sys hL p₀ n (traj H D s) (traj H D s) := by
  have hS := continuous_S_traj H D
  have hA := continuous_Ap_traj sys hL H hKernel p₀ Hunit hPeriodic D
  have hV : Continuous fun s => Vb sys L n hL (Sm eta L (traj H D s)) :=
    (Vb sys L n hL).continuous.comp hS
  unfold Gb
  exact (continuous_const.mul (hV.inner hA)).sub (continuous_const.mul (hA.inner hV))

include hKernel hL in
lemma continuous_Wf_traj (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) : Continuous fun s => Wf sys hL hn p₀ H (traj H D s) (traj H D s) := by
  have hS := continuous_S_traj H D
  have hW := continuous_W_traj sys hL H hKernel Hunit hPeriodic D
  have hY : Continuous fun s => Yop sys hL hn p₀ (Sm eta L (traj H D s)) :=
    (Yop sys hL hn p₀).continuous.comp hS
  unfold Wf
  exact (continuous_const.mul (hW.inner hY)).sub (continuous_const.mul (hY.inner hW))

include hKernel hL in
/-- **eq:elim** (`prop:elim` (i)): along the exact evolution,
`∫₀ᵗ G_b(w_s, w_s) ds = ⟨ψ(t), Y ψ(t)⟩ - ⟨ψ₀, Y ψ₀⟩ - ∫₀ᵗ 𝔚(w_s, w_s) ds` (real parts; both
forms are real on the diagonal). -/
theorem elim_integral (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, (Gb sys hL p₀ n (traj H D s) (traj H D s)).re =
      (⟪D.U t (Sm eta L D.u₀), Yop sys hL hn p₀ (D.U t (Sm eta L D.u₀))⟫_ℂ).re -
        (⟪Sm eta L D.u₀, Yop sys hL hn p₀ (Sm eta L D.u₀)⟫_ℂ).re -
      ∫ s in (0 : ℝ)..t, (Wf sys hL hn p₀ H (traj H D s) (traj H D s)).re := by
  have hcG : Continuous fun s => (Gb sys hL p₀ n (traj H D s) (traj H D s)).re :=
    Complex.continuous_re.comp (continuous_Gb_traj sys hL (n := n) H hKernel p₀ Hunit hPeriodic D)
  have hcW : Continuous fun s => (Wf sys hL hn p₀ H (traj H D s) (traj H D s)).re :=
    Complex.continuous_re.comp (continuous_Wf_traj sys hL hn H hKernel p₀ Hunit hPeriodic D)
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt
      (fun s => (⟪D.U s (Sm eta L D.u₀), Yop sys hL hn p₀ (D.U s (Sm eta L D.u₀))⟫_ℂ).re)
      ((Gb sys hL p₀ n (traj H D s) (traj H D s)).re +
        (Wf sys hL hn p₀ H (traj H D s) (traj H D s)).re) s := by
    intro s _
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (elim_deriv sys hL hn H p₀ D s)
    simp only [Function.comp_def, Complex.reCLM_apply, Complex.add_re] at h
    exact h
  have hint : IntervalIntegrable (fun s => (Gb sys hL p₀ n (traj H D s) (traj H D s)).re +
      (Wf sys hL hn p₀ H (traj H D s) (traj H D s)).re) volume 0 t :=
    (hcG.add hcW).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_add (hcG.intervalIntegrable 0 t) (hcW.intervalIntegrable 0 t),
    D.U0] at hFTC
  linarith

end Elim

/-! ## The kernel of `Y` -/

section Kernel

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (p₀ : Fin eta)

/-- The kernel of `Y`: `Y(q, p) = σ(q, p) (A(p) - A(q))`. -/
noncomputable def yK (q p : Cf eta) : ℂ :=
  sigK sys L n q p * ((regSymbol sys (gF L) p₀ p - regSymbol sys (gF L) p₀ q : ℝ) : ℂ)

variable {sys L n}

lemma Bop_ev (hL : 0 < L) (hn : 2 ≤ n) (q p : Cf eta) :
    Bop sys hL hn p₀ (ev q) p = (regSymbol sys (gF L) p₀ p : ℂ) * sigK sys L n p q := by
  classical
  rw [Bop_apply, Sig_apply]
  congr 1
  rw [tsum_eq_single q]
  · rw [ev, lp.single_apply, Pi.single_eq_same, mul_one]
  · intro r hr
    rw [ev, lp.single_apply, Pi.single_eq_of_ne hr, mul_zero]

lemma adjB_apply (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) (q : Cf eta) :
    ContinuousLinearMap.adjoint (Bop sys hL hn p₀) x q =
      -∑' p, (regSymbol sys (gF L) p₀ p : ℂ) * sigK sys L n q p * x p := by
  rw [← inner_ev_left q, ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum, ← tsum_neg]
  refine tsum_congr fun p => ?_
  rw [Bop_ev p₀ hL hn q p, RCLike.inner_apply, map_mul, Complex.conj_ofReal, sigK_anti hL q p]
  ring

/-- The kernel formula for `Y`: `(Y x)(q) = -A(q) Σ_p σ(q, p) x(p) + Σ_p A(p) σ(q, p) x(p)`. -/
lemma Yop_apply (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) (q : Cf eta) :
    Yop sys hL hn p₀ x q = -((regSymbol sys (gF L) p₀ q : ℂ) * ∑' p, sigK sys L n q p * x p) +
      ∑' p, (regSymbol sys (gF L) p₀ p : ℂ) * sigK sys L n q p * x p := by
  unfold Yop
  rw [neg_apply, add_apply, lp.coeFn_neg, Pi.neg_apply, lp.coeFn_add, Pi.add_apply, Bop_apply,
    adjB_apply p₀ hL hn, Sig_apply]
  ring

/-- A configuration none of whose crossings is charged by `x` is not reached by `Y x`. -/
lemma Yop_apply_eq_zero (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) (q : Cf eta)
    (h : ∀ p, sigK sys L n q p * x p = 0) : Yop sys hL hn p₀ x q = 0 := by
  rw [Yop_apply p₀ hL hn]
  have h1 : (∑' p, sigK sys L n q p * x p) = 0 := by simp [h]
  have h2 : (∑' p, (regSymbol sys (gF L) p₀ p : ℂ) * sigK sys L n q p * x p) = 0 := by
    simp [mul_assoc, h]
  rw [h1, h2]; ring

open Classical in
/-- On the bulk block: `(Y 1_Q x)(q) = Σ_{p ∈ Q} Y(q, p) x(p)`. -/
lemma Yop_truncQ_apply (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) (q : Cf eta) :
    Yop sys hL hn p₀ (lpTruncate (Qs eta n) x) q = ∑ p ∈ Qs eta n, yK sys L n p₀ q p * x p := by
  rw [Yop_apply p₀ hL hn, tsum_eq_sum (s := Qs eta n), tsum_eq_sum (s := Qs eta n)]
  · rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [lpTruncate_apply, if_pos hp]
    unfold yK; push_cast; ring
  · intro p hp; rw [lpTruncate_apply, if_neg hp, mul_zero]
  · intro p hp; rw [lpTruncate_apply, if_neg hp, mul_zero]

/-! ## The symbol bound -/

variable (sys) in
/-- The dressed-symbol constant `c_Y = (50/3) m_top / m_{p₀}`. -/
noncomputable def cY : ℝ := 50 / 3 * mtop sys / sys.mass p₀

omit [Fintype ν] in
lemma cY_nonneg : 0 ≤ cY sys p₀ := by
  unfold cY; have := one_le_mtop sys; have := sys.mass_pos p₀; positivity

/-- The Coulomb tail `ν ↦ |ν|⁻² 1{|ν| > R}`. -/
noncomputable def tailW (R : ℝ) (x : L3) : ℝ := if R ^ 2 < nsq x then (nsq x)⁻¹ else 0

lemma tailW_nonneg (R : ℝ) (x : L3) : 0 ≤ tailW R x := by
  unfold tailW; split_ifs
  · exact inv_nonneg.mpr (nsq_nonneg x)
  · exact le_rfl

lemma tailW_sq (R : ℝ) (x : L3) : tailW R x ^ 2 = tailFn R x := by
  unfold tailW tailFn; split_ifs <;> simp

omit [Fintype ν] in
variable (sys) in
/-- **The force symbol on a crossing**: a crossing hop of channel `j` with transfer `ν`,
`|ν| > 3n/4`, changes `A_{p₀}` by at most `(5/6) g² |ν|²/m_{p₀}` (evaluated at the `Q`-end). -/
lemma force_symbol_le (g : ℝ) {j : Ch eta} {q p : Cf eta} (hj : OnCh j q p)
    (hc : Cross (n : ℝ) q p) (hν : (3 * n / 4) ^ 2 < nsq (q (lead j) - p (lead j))) :
    |regSymbol sys g p₀ p - regSymbol sys g p₀ q| ≤
      5 / 6 * (g ^ 2 / sys.mass p₀) * nsq (q (lead j) - p (lead j)) := by
  set x := q (lead j) - p (lead j) with hxdef
  have hq : q = p + tr j x := hj
  set τ := tr j x p₀ with hτdef
  have hqp : q p₀ = p p₀ + τ := congrFun hq p₀
  have hτ : nsq τ ≤ nsq x := by
    by_cases hm : p₀ ∈ moved j
    · rcases tr_apply_moved j x hm with h | h
      · rw [hτdef, h]
      · rw [hτdef, h, nsq_neg]
    · rw [hτdef, tr_apply_not_moved j x hm]
      have : nsq (0 : L3) = 0 := by simp [nsq]
      rw [this]; exact nsq_nonneg x
  set X := Real.sqrt (nsq x) with hXdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = nsq x := Real.sq_sqrt (nsq_nonneg x)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hXn : 3 * n / 4 < X := by
    rw [show (3 * n / 4 : ℝ) = Real.sqrt ((3 * n / 4) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hν
  have hτX : Real.sqrt (nsq τ) ≤ X := Real.sqrt_le_sqrt hτ
  have key : ∀ k : L3, nsq k ≤ ((n : ℝ) / 4) ^ 2 → |2 * ldot k τ| ≤ 2 / 3 * nsq x := by
    intro k hk
    have hk' : Real.sqrt (nsq k) ≤ n / 4 := Real.sqrt_le_iff.mpr ⟨by positivity, hk⟩
    have h1 : |ldot k τ| ≤ n / 4 * X :=
      (abs_ldot_le k τ).trans (mul_le_mul hk' hτX (Real.sqrt_nonneg _) (by positivity))
    calc |2 * ldot k τ| = 2 * |ldot k τ| := by rw [abs_mul]; norm_num
      _ ≤ 2 * (n / 4 * X) := by linarith
      _ ≤ 2 / 3 * nsq x := by rw [← hX2]; nlinarith
  have hm := sys.mass_pos p₀
  have hsym : regSymbol sys g p₀ p - regSymbol sys g p₀ q =
      -(1 / 2 * (g ^ 2 / sys.mass p₀) * (nsq (q p₀) - nsq (p p₀))) := by
    unfold regSymbol
    rw [← nsq_eq_latticeNormSq]
    field_simp
    ring
  have hdiff : |nsq (q p₀) - nsq (p p₀)| ≤ 5 / 3 * nsq x := by
    rcases hc with ⟨hqQ, -⟩ | ⟨-, hpQ⟩
    · have hpp : p p₀ = q p₀ - τ := by rw [hqp]; abel
      rw [hpp, nsq_sub]
      have h1 := key (q p₀) (hqQ p₀)
      have h0 := nsq_nonneg τ
      rw [abs_le] at h1 ⊢
      constructor <;> nlinarith
    · rw [hqp, nsq_add]
      have h1 := key (p p₀) (hpQ p₀)
      have h0 := nsq_nonneg τ
      rw [abs_le] at h1 ⊢
      constructor <;> nlinarith
  rw [hsym, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 * (g ^ 2 / sys.mass p₀))]
  calc 1 / 2 * (g ^ 2 / sys.mass p₀) * |nsq (q p₀) - nsq (p p₀)|
      ≤ 1 / 2 * (g ^ 2 / sys.mass p₀) * (5 / 3 * nsq x) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = 5 / 6 * (g ^ 2 / sys.mass p₀) * nsq x := by ring

/-- **The dressed-symbol bound** (`prop:elim` (ii)): on a hop of channel `j` with transfer `ν`,
`|Y(q, p)| ≤ (50/3)(m_top/m_{p₀}) c_j |ν|⁻² 1{|ν| > 3n/4}`. -/
lemma norm_yK_le (hL : 0 < L) (hn0 : 0 < n) {j : Ch eta} {q p : Cf eta} (hj : OnCh j q p) :
    ‖yK sys L n p₀ q p‖ ≤
      cY sys p₀ * chC sys L j * tailW (3 * n / 4) (q (lead j) - p (lead j)) := by
  have hRHS : 0 ≤ cY sys p₀ * chC sys L j * tailW (3 * n / 4) (q (lead j) - p (lead j)) :=
    mul_nonneg (mul_nonneg (cY_nonneg p₀) (chC_nonneg sys hL j)) (tailW_nonneg _ _)
  unfold yK sigK
  split_ifs with hc
  · by_cases h0 : potKernel sys L q p = 0
    · rw [h0, zero_div, zero_mul, norm_zero]; exact hRHS
    · obtain ⟨h1, h2⟩ := channel_gap sys (gF_pos hL).ne' (by exact_mod_cast hn0) hj hc
      set x := q (lead j) - p (lead j) with hxdef
      have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
      have hx0 : 0 < nsq x := lt_of_le_of_lt (sq_nonneg _) h1
      have hqp : q ≠ p := by
        intro h
        have : x = 0 := by rw [hxdef, h, sub_self]
        rw [this] at hx0; simp [nsq] at hx0
      have hw : ‖potKernel sys L q p‖ ≤ chC sys L j / nsq x := by
        refine (norm_potKernel_le sys hL q p).trans (le_of_eq ?_)
        unfold potMaj
        rw [Finset.sum_eq_single j]
        · unfold chMaj; rw [if_pos hj]; rfl
        · intro j' _ hj'
          unfold chMaj
          rw [if_neg]
          intro hon
          exact hj' (onCh_unique hon hj hqp)
        · intro h; exact absurd (Finset.mem_univ j) h
      have hA := force_symbol_le sys p₀ (gF L) hj hc h1
      have hcg := cgap_pos sys (gF_pos hL).ne'
      have hg2 : 0 < gF L ^ 2 := by have := gF_pos hL; positivity
      have hm := sys.mass_pos p₀
      have hmt := one_le_mtop sys
      have htail : tailW (3 * n / 4) x = (nsq x)⁻¹ := by unfold tailW; rw [if_pos h1]
      rw [htail, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have hE : 0 < |E sys.mass (gF L) q - E sys.mass (gF L) p| :=
        lt_of_lt_of_le (by positivity) h2
      calc ‖potKernel sys L q p‖ / |Ek sys L q - Ek sys L p| *
            |regSymbol sys (gF L) p₀ p - regSymbol sys (gF L) p₀ q|
          ≤ (chC sys L j / nsq x) / (cgap sys (gF L) * nsq x) *
              (5 / 6 * (gF L ^ 2 / sys.mass p₀) * nsq x) := by
            refine mul_le_mul (div_le_div₀ (div_nonneg (chC_nonneg sys hL j) hx0.le) hw
              (by positivity) h2) hA (abs_nonneg _) ?_
            exact div_nonneg (div_nonneg (chC_nonneg sys hL j) hx0.le) (by positivity)
        _ = cY sys p₀ * chC sys L j * (nsq x)⁻¹ := by
            have hg0 : gF L ≠ 0 := (gF_pos hL).ne'
            unfold cY cgap
            field_simp
            ring
  · rw [zero_mul, norm_zero]; exact hRHS

open Classical in
/-- The channel-`j` part of `|Y|`. -/
noncomputable def kapY (j : Ch eta) (q p : Cf eta) : ℝ :=
  if OnCh j q p then ‖yK sys L n p₀ q p‖ else 0

lemma kapY_nonneg (j : Ch eta) (q p : Cf eta) : 0 ≤ kapY (sys := sys) (L := L) (n := n) p₀ j q p := by
  unfold kapY; split_ifs <;> positivity

lemma norm_yK_le_kapY (hL : 0 < L) (q p : Cf eta) :
    ‖yK sys L n p₀ q p‖ ≤ ∑ j : Ch eta, kapY (sys := sys) (L := L) (n := n) p₀ j q p := by
  classical
  by_cases h0 : yK sys L n p₀ q p = 0
  · rw [h0, norm_zero]; exact Finset.sum_nonneg fun j _ => kapY_nonneg p₀ j q p
  · have hpot : potKernel sys L q p ≠ 0 := by
      intro hp; apply h0; unfold yK sigK; split_ifs <;> simp [hp]
    obtain ⟨j, hj⟩ := exists_onCh_of_ne_zero hL hpot
    calc ‖yK sys L n p₀ q p‖ = kapY (sys := sys) (L := L) (n := n) p₀ j q p := by
          unfold kapY; rw [if_pos hj]
      _ ≤ ∑ j' : Ch eta, kapY (sys := sys) (L := L) (n := n) p₀ j' q p :=
        Finset.single_le_sum (f := fun j' => kapY (sys := sys) (L := L) (n := n) p₀ j' q p)
          (fun j' _ => kapY_nonneg p₀ j' q p) (Finset.mem_univ j)

open Classical in
/-- The columns of the channel-`j` part of `|Y|`: `Σ_q |Y_j(q, p)|² ≤ (c_Y c_j)² · 416/(3n)`. -/
lemma col_kapY (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (p : Cf eta) :
    (Summable fun q => kapY (sys := sys) (L := L) (n := n) p₀ j q p ^ 2) ∧
      ∑' q, kapY (sys := sys) (L := L) (n := n) p₀ j q p ^ 2 ≤
        (cY sys p₀ * chC sys L j) ^ 2 * (416 / (3 * n)) := by
  have hn0 : 0 < n := by omega
  set F : Cf eta → ℝ := fun q => (cY sys p₀ * chC sys L j) ^ 2 * tailFn (3 * n / 4) (q (lead j) - p (lead j))
  have hle : ∀ q, kapY (sys := sys) (L := L) (n := n) p₀ j q p ^ 2 ≤
      if OnCh j q p then F q else 0 := by
    intro q
    unfold kapY
    split_ifs with hj
    · have h := norm_yK_le (sys := sys) p₀ hL hn0 hj
      calc ‖yK sys L n p₀ q p‖ ^ 2
          ≤ (cY sys p₀ * chC sys L j * tailW (3 * n / 4) (q (lead j) - p (lead j))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = F q := by simp only [F]; rw [mul_pow, tailW_sq]
    · simp
  have hsF : Summable fun q => if OnCh j q p then F q else 0 := by
    rw [summable_col_iff]
    simp only [F, lead_add_tr]
    exact (tail_bound hn).1.mul_left _
  have hs := hsF.of_nonneg_of_le (fun q => sq_nonneg _) hle
  refine ⟨hs, ?_⟩
  calc ∑' q, kapY (sys := sys) (L := L) (n := n) p₀ j q p ^ 2
      ≤ ∑' q, (if OnCh j q p then F q else 0) := hs.tsum_le_tsum hle hsF
    _ = ∑' ν, F (p + tr j ν) := tsum_col j p F
    _ = (cY sys p₀ * chC sys L j) ^ 2 * ∑' ν, tailFn (3 * n / 4) ν := by
        simp only [F, lead_add_tr]; rw [tsum_mul_left]
    _ ≤ _ := mul_le_mul_of_nonneg_left (tail_bound hn).2 (sq_nonneg _)

variable (sys L n) in
/-- The column constant of `Y`: `M_Y = Σ_j (c_Y c_j)² · 416/(3n)`. -/
noncomputable def MY : ℝ := ∑ j : Ch eta, (cY sys p₀ * chC sys L j) ^ 2 * (416 / (3 * n))

lemma col_kapY_le_MY (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (p : Cf eta) :
    ∑' q, kapY (sys := sys) (L := L) (n := n) p₀ j q p ^ 2 ≤ MY sys L n p₀ := by
  refine (col_kapY p₀ hL hn j p).2.trans ?_
  unfold MY
  exact Finset.single_le_sum (f := fun j => (cY sys p₀ * chC sys L j) ^ 2 * (416 / (3 * n)))
    (fun j _ => by positivity) (Finset.mem_univ j)

open Classical in
/-- **The fibre Gram bound for `Y 1_Q`**: `‖Y 1_Q x‖² ≤ #Ch² M_Y Z₂ Σ_{p ∈ Q} (1 + |p|²)² |x_p|²`. -/
theorem norm_YQ_sq_le (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) :
    ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)‖ ^ 2 ≤
      Fintype.card (Ch eta) ^ 2 * MY sys L n p₀ * (1 + 26 * (1 + 1 / (2 * (2 * 1) - 3))) *
        ∑ p ∈ Qs eta n, Ws 1 p * ‖x p‖ ^ 2 := by
  classical
  set F := Qs eta n
  set G : Ch eta → Cf eta → ℝ := fun j q => ∑ p ∈ F, ‖x p‖ * kapY (sys := sys) (L := L) (n := n) p₀ j q p
  set N : ℝ := 1 + 26 * (1 + 1 / (2 * (2 * 1) - 3))
  have hj : ∀ j : Ch eta, (Summable fun q => (1 : ℝ) * G j q ^ 2) ∧
      ∑' q, (1 : ℝ) * G j q ^ 2 ≤ MY sys L n p₀ * N * ∑ p ∈ F, Ws 1 p * ‖x p‖ ^ 2 := by
    intro j
    refine fibre_gram F (kapY (sys := sys) (L := L) (n := n) p₀ j)
      (fun q p => kapY_nonneg p₀ j q p) (fun _ => 1) (fun _ => zero_le_one)
      (fun p p' => OnCh j p' p) (fun p p' h => onCh_symm h) ?_ (fun p _ => ?_) (fun p _ => ?_)
      (Ws 1) (Ws_pos 1) (fun p _ => fibre_weight_le n j p (by norm_num)) (fun p => ‖x p‖)
      (fun p => norm_nonneg _)
    · intro q p _ p' _ h1 h2
      have o1 : OnCh j q p := by by_contra h; exact h1 (by unfold kapY; rw [if_neg h])
      have o2 : OnCh j q p' := by by_contra h; exact h2 (by unfold kapY; rw [if_neg h])
      exact onCh_trans o1 o2
    · simpa only [one_mul] using (col_kapY p₀ hL hn j p).1
    · simpa only [one_mul] using col_kapY_le_MY p₀ hL hn j p
  have hpt : ∀ q, ‖Yop sys hL hn p₀ (lpTruncate F x) q‖ ^ 2 ≤
      Fintype.card (Ch eta) * ∑ j : Ch eta, (1 : ℝ) * G j q ^ 2 := by
    intro q
    rw [Yop_truncQ_apply p₀ hL hn x q]
    have h1 : ‖∑ p ∈ F, yK sys L n p₀ q p * x p‖ ≤ ∑ j : Ch eta, G j q := by
      refine (norm_sum_le _ _).trans ?_
      simp only [G]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [norm_mul, ← Finset.mul_sum, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_yK_le_kapY p₀ hL q p) (norm_nonneg _)
    have h2 : (∑ j : Ch eta, G j q) ^ 2 ≤ Fintype.card (Ch eta) * ∑ j : Ch eta, G j q ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h0 : 0 ≤ ∑ j : Ch eta, G j q :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun p _ =>
        mul_nonneg (norm_nonneg _) (kapY_nonneg p₀ j q p)
    simp only [one_mul]
    calc ‖∑ p ∈ F, yK sys L n p₀ q p * x p‖ ^ 2 ≤ (∑ j : Ch eta, G j q) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hs : Summable fun q => (Fintype.card (Ch eta) : ℝ) * ∑ j : Ch eta, (1 : ℝ) * G j q ^ 2 :=
    (summable_sum fun j _ => (hj j).1).mul_left _
  rw [← tsum_sq_coord]
  calc ∑' q, ‖Yop sys hL hn p₀ (lpTruncate F x) q‖ ^ 2
      ≤ ∑' q, (Fintype.card (Ch eta) : ℝ) * ∑ j : Ch eta, (1 : ℝ) * G j q ^ 2 :=
        (summable_sq_coord _).tsum_le_tsum hpt hs
    _ = Fintype.card (Ch eta) * ∑ j : Ch eta, ∑' q, (1 : ℝ) * G j q ^ 2 := by
        rw [tsum_mul_left, Summable.tsum_finsetSum fun j _ => (hj j).1]
    _ ≤ Fintype.card (Ch eta) * ∑ _j : Ch eta, MY sys L n p₀ * N * ∑ p ∈ F, Ws 1 p * ‖x p‖ ^ 2 := by
        gcongr with j
        exact (hj j).2
    _ = Fintype.card (Ch eta) ^ 2 * MY sys L n p₀ * N * ∑ p ∈ F, Ws 1 p * ‖x p‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-! ## The dressed tail of a state -/

variable (sys L) in
/-- `c_L = 1 + 2 m_top/g²`: `1 + |p|² ≤ c_L (1 + A(p))`. -/
noncomputable def cL : ℝ := 1 + 2 * mtop sys / gF L ^ 2

omit [Fintype ν] in
lemma one_add_lsqC_le (hL : 0 < L) (p : Cf eta) : 1 + lsqC p ≤ cL sys L * (1 + Ek sys L p) := by
  have hg2 : 0 < gF L ^ 2 := by have := gF_pos hL; positivity
  have hmt := one_le_mtop sys
  have hE : lsqC p ≤ 2 * mtop sys / gF L ^ 2 * Ek sys L p := by
    unfold lsqC
    rw [Ek, E, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have hmc := sys.mass_pos c
    have hle := mass_le_mtop sys c
    have h0 := nsq_nonneg (p c)
    have hg0 : gF L ≠ 0 := (gF_pos hL).ne'
    rw [show 2 * mtop sys / gF L ^ 2 * (gF L ^ 2 / (2 * sys.mass c) * nsq (p c)) =
      mtop sys / sys.mass c * nsq (p c) by field_simp]
    have : 1 ≤ mtop sys / sys.mass c := by rw [le_div_iff₀ hmc]; linarith
    nlinarith
  have hE0 : 0 ≤ Ek sys L p := by
    rw [Ek, E]
    exact Finset.sum_nonneg fun c _ => by have := sys.mass_pos c; have := nsq_nonneg (p c); positivity
  unfold cL
  have : 0 ≤ 2 * mtop sys / gF L ^ 2 := by positivity
  nlinarith

omit [Fintype ν] in
/-- The `Q`-weights of a state: `Σ_{p ∈ Q} (1 + |p|²)² |(S u)_p|² ≤ c_L² (‖S u‖ + ‖T u‖)²`. -/
lemma sum_Ws_stateMap_le (hL : 0 < L) (n : ℕ) (u : MolecularFourierH2 eta) :
    ∑ p ∈ Qs eta n, Ws 1 p * ‖Sm eta L u p‖ ^ 2 ≤
      cL sys L ^ 2 * (‖Sm eta L u‖ + ‖coulombFourierKineticH2 sys (gF L) u‖) ^ 2 := by
  set v : L2 eta := Sm eta L u + coulombFourierKineticH2 sys (gF L) u
  have hcL : 0 ≤ cL sys L := by
    unfold cL; have := one_le_mtop sys; have : 0 < gF L ^ 2 := by have := gF_pos hL; positivity
    positivity
  have hpt : ∀ p, Ws 1 p * ‖Sm eta L u p‖ ^ 2 ≤ cL sys L ^ 2 * ‖v p‖ ^ 2 := by
    intro p
    have hE0 : 0 ≤ Ek sys L p := by
      rw [Ek, E]
      exact Finset.sum_nonneg fun c _ => by
        have := sys.mass_pos c; have := nsq_nonneg (p c); positivity
    have hv : v p = ((1 + Ek sys L p : ℝ) : ℂ) * Sm eta L u p := by
      simp only [v, lp.coeFn_add, Pi.add_apply, kinetic_apply', Sm]
      push_cast; ring
    have hW : Ws 1 p = (1 + lsqC p) ^ 2 := by
      unfold Ws
      rw [show (2 * (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hW, hv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have h1 := one_add_lsqC_le (sys := sys) hL p
    have h0 : 0 ≤ 1 + lsqC p := by linarith [lsqC_nonneg p]
    have h2 : (1 + lsqC p) ^ 2 ≤ (cL sys L * (1 + Ek sys L p)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have := sq_nonneg ‖Sm eta L u p‖
    nlinarith
  calc ∑ p ∈ Qs eta n, Ws 1 p * ‖Sm eta L u p‖ ^ 2
      ≤ ∑ p ∈ Qs eta n, cL sys L ^ 2 * ‖v p‖ ^ 2 := Finset.sum_le_sum fun p _ => hpt p
    _ = cL sys L ^ 2 * ∑ p ∈ Qs eta n, ‖v p‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ cL sys L ^ 2 * ‖v‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [← tsum_sq_coord v]
        exact (summable_sq_coord v).sum_le_tsum _ fun _ _ => sq_nonneg _
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2)
          (sq_nonneg _)

variable (sys L) in
/-- The constant of the dressed tail: `‖Y 1_Q S u‖ ≤ c_{YQ} n^{-1/2} (‖S u‖ + ‖T u‖)`. -/
noncomputable def cYQ : ℝ :=
  Fintype.card (Ch eta) * cL sys L *
    Real.sqrt (53 * ∑ j : Ch eta, (cY sys p₀ * chC sys L j) ^ 2 * (416 / 3))

lemma cYQ_nonneg (hL : 0 < L) : 0 ≤ cYQ sys L p₀ := by
  unfold cYQ cL
  have := one_le_mtop sys; have : 0 < gF L ^ 2 := by have := gF_pos hL; positivity
  positivity

/-- **The dressed tail** (`prop:elim` (ii), eq:lam-gen for `Y_{RQ}`):
`‖Y 1_Q S u‖ ≤ c_{YQ} n^{-1/2} (‖S u‖ + ‖T u‖)`. -/
theorem norm_YQ_le (hL : 0 < L) (hn : 2 ≤ n) (u : MolecularFourierH2 eta) :
    ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Sm eta L u))‖ ≤
      cYQ sys L p₀ * (‖Sm eta L u‖ + ‖coulombFourierKineticH2 sys (gF L) u‖) / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 := norm_YQ_sq_le (sys := sys) p₀ hL hn (Sm eta L u)
  have h2 := sum_Ws_stateMap_le (sys := sys) hL n u
  set X := ‖Sm eta L u‖ + ‖coulombFourierKineticH2 sys (gF L) u‖
  have hX : 0 ≤ X := by positivity
  set S := ∑ j : Ch eta, (cY sys p₀ * chC sys L j) ^ 2 * (416 / 3)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hMY : MY sys L n p₀ = S / n := by
    unfold MY; simp only [S]; rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  have hN : (1 + 26 * (1 + 1 / (2 * (2 * 1) - 3)) : ℝ) = 53 := by norm_num
  rw [hMY, hN] at h1
  have hcard : (0 : ℝ) ≤ Fintype.card (Ch eta) := Nat.cast_nonneg _
  have hcL : 0 ≤ cL sys L := by
    unfold cL; have := one_le_mtop sys; have : 0 < gF L ^ 2 := by have := gF_pos hL; positivity
    positivity
  have h3 : ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Sm eta L u))‖ ^ 2 ≤
      (cYQ sys L p₀ * X / Real.sqrt n) ^ 2 := by
    refine h1.trans ?_
    have e : (cYQ sys L p₀ * X / Real.sqrt n) ^ 2 =
        Fintype.card (Ch eta) ^ 2 * (S / n) * 53 * (cL sys L ^ 2 * X ^ 2) := by
      have hc : cYQ sys L p₀ = Fintype.card (Ch eta) * cL sys L * Real.sqrt (53 * S) := rfl
      rw [hc, div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hn0.le]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by
    have := cYQ_nonneg (sys := sys) p₀ hL; positivity) two_ne_zero).mp h3

/-! ## eq:elim-bdry -/

omit [Fintype ν] in
lemma inner_eq_of_pt (x x' v v' : L2 eta)
    (h : ∀ q, (x q = x' q ∧ v q = v' q) ∨ (x q = 0 ∧ x' q = 0) ∨ (v q = 0 ∧ v' q = 0)) :
    ⟪x, v⟫_ℂ = ⟪x', v'⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun q => ?_
  rcases h q with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, inner_zero_left, inner_zero_left]
  · rw [h1, h2, inner_zero_right, inner_zero_right]

open Classical in
/-- `Y 1_Q x` vanishes on the cube. -/
lemma YQ_apply_of_inP (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) {q : Cf eta}
    (hq : q ∈ fourierConfigCube eta n) : Yop sys hL hn p₀ (lpTruncate (Qs eta n) x) q = 0 := by
  rw [Yop_truncQ_apply p₀ hL hn x q]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpQ := mem_Qs.mp hp
  have hqP : InP (n : ℝ) q := (inP_iff_mem_cube n q).mpr hq
  have hnc : ¬ Cross (n : ℝ) q p := by
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact h (hpQ.inP (Nat.cast_nonneg n))
    · exact h hqP
  unfold yK sigK
  rw [if_neg hnc, zero_mul, zero_mul]

open Classical in
/-- `Y (x - 1_Q x)` vanishes off `Q`. -/
lemma Ysub_apply_of_not_inQ (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) {q : Cf eta}
    (hq : q ∉ Qs eta n) : Yop sys hL hn p₀ (x - lpTruncate (Qs eta n) x) q = 0 := by
  refine Yop_apply_eq_zero p₀ hL hn _ q fun p => ?_
  by_cases hp : p ∈ Qs eta n
  · rw [lp.coeFn_sub, Pi.sub_apply, lpTruncate_apply, if_pos hp, sub_self, mul_zero]
  · have hnc : ¬ Cross (n : ℝ) q p := by
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact hq (mem_Qs.mpr h)
      · exact hp (mem_Qs.mpr h)
    unfold sigK
    rw [if_neg hnc, zero_mul]

open Classical in
/-- **eq:elim-bdry, the structure**: `⟨x, Y x⟩ = ⟨R x, Y 1_Q x⟩ + ⟨Y 1_Q x, R x⟩`. -/
theorem inner_Y_self (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) :
    ⟪x, Yop sys hL hn p₀ x⟫_ℂ =
      ⟪x - molecularH2Truncate n x, Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)⟫_ℂ +
        ⟪Yop sys hL hn p₀ (lpTruncate (Qs eta n) x), x - molecularH2Truncate n x⟫_ℂ := by
  set Qx := lpTruncate (Qs eta n) x
  set Rx := x - molecularH2Truncate n x
  set Y := Yop sys hL hn p₀
  have hsub : Qs eta n ⊆ fourierConfigCube eta n := Qs_subset_cube (by omega)
  have hRx : ∀ q, q ∉ fourierConfigCube eta n → Rx q = x q := by
    intro q hq
    simp only [Rx, lp.coeFn_sub, Pi.sub_apply, molecularH2Truncate_apply,
      cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq, sub_zero]
  have hsplit : Y x = Y Qx + Y (x - Qx) := by rw [← map_add]; congr 1; abel
  have hA : ⟪x, Y Qx⟫_ℂ = ⟪Rx, Y Qx⟫_ℂ := by
    refine inner_eq_of_pt _ _ _ _ fun q => ?_
    by_cases hq : q ∈ fourierConfigCube eta n
    · right; right; have := YQ_apply_of_inP (sys := sys) p₀ hL hn x hq; exact ⟨this, this⟩
    · left; exact ⟨(hRx q hq).symm, rfl⟩
  have hB : ⟪x, Y (x - Qx)⟫_ℂ = ⟪Qx, Y (x - Qx)⟫_ℂ := by
    refine inner_eq_of_pt _ _ _ _ fun q => ?_
    by_cases hq : q ∈ Qs eta n
    · left; refine ⟨?_, rfl⟩; simp only [Qx, lpTruncate_apply, if_pos hq]
    · right; right; have := Ysub_apply_of_not_inQ (sys := sys) p₀ hL hn x hq; exact ⟨this, this⟩
  have hC : ⟪Qx, Y (x - Qx)⟫_ℂ = ⟪Y Qx, Rx⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_Yop]
    refine inner_eq_of_pt _ _ _ _ fun q => ?_
    by_cases hq : q ∈ fourierConfigCube eta n
    · right; left; have := YQ_apply_of_inP (sys := sys) p₀ hL hn x hq; exact ⟨this, this⟩
    · left
      refine ⟨rfl, ?_⟩
      have hqQ : q ∉ Qs eta n := fun h => hq (hsub h)
      rw [hRx q hq]
      simp only [Qx, lp.coeFn_sub, Pi.sub_apply, lpTruncate_apply, if_neg hqQ, sub_zero]
  rw [hsplit, inner_add_right, hA, hB, hC]

/-- `|⟨x, Y x⟩| ≤ 2 ‖R x‖ ‖Y 1_Q x‖`. -/
lemma norm_inner_Y_self_le (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) :
    ‖⟪x, Yop sys hL hn p₀ x⟫_ℂ‖ ≤
      2 * (‖x - molecularH2Truncate n x‖ * ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)‖) := by
  rw [inner_Y_self (sys := sys) p₀ hL hn x]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (x - molecularH2Truncate n x)
    (Yop sys hL hn p₀ (lpTruncate (Qs eta n) x))
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (Yop sys hL hn p₀ (lpTruncate (Qs eta n) x))
    (x - molecularH2Truncate n x)
  linarith

/-- **eq:elim-bdry** for a good state: `|⟨S w, Y S w⟩| ≤ 2 η c_{YQ} g^{1/2} M² K^{-3}`. -/
theorem elim_bdry_state (hL : 0 < L) (hn : 2 ≤ n) (hK : 1 ≤ gF L * n) {M : ℝ}
    {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    ‖⟪Sm eta L w, Yop sys hL hn p₀ (Sm eta L w)⟫_ℂ‖ ≤
      2 * eta * cYQ sys L p₀ * Real.sqrt (gF L) * M ^ 2 * (gF L * n) ^ (-(3 : ℝ)) := by
  have hg := gF_pos hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hK0 : 0 < gF L * n := by positivity
  have hM := hF.nonneg
  have hc := cYQ_nonneg (sys := sys) p₀ hL
  have hR := fgood_R hF hL hK
  have hY := norm_YQ_le (sys := sys) p₀ hL hn w
  have hYM : ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Sm eta L w))‖ ≤
      cYQ sys L p₀ * M / Real.sqrt n := by
    refine hY.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF.1 hc) (Real.sqrt_nonneg _)
  refine (norm_inner_Y_self_le (sys := sys) p₀ hL hn _).trans ?_
  have hsq : 1 / Real.sqrt n = Real.sqrt (gF L) * (gF L * n) ^ (-(1 / 2 : ℝ)) := by
    rw [rpow_neg_half_eq hK0, Real.sqrt_mul hg.le]
    field_simp
  have e : (gF L * n) ^ (-(5 / 2 : ℝ)) * (gF L * n) ^ (-(1 / 2 : ℝ)) = (gF L * n) ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_add hK0]; norm_num
  have hp := Real.rpow_nonneg hK0.le (-(5 / 2 : ℝ))
  calc 2 * (‖Sm eta L w - molecularH2Truncate n (Sm eta L w)‖ *
        ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Sm eta L w))‖)
      ≤ 2 * ((eta * M * (gF L * n) ^ (-(5 / 2 : ℝ))) * (cYQ sys L p₀ * M / Real.sqrt n)) := by
        gcongr
    _ = 2 * eta * cYQ sys L p₀ * M ^ 2 * (gF L * n) ^ (-(5 / 2 : ℝ)) * (1 / Real.sqrt n) := by
        ring
    _ = _ := by rw [hsq, ← e]; ring

end Kernel

/-! ## The uniform `prop:elim` -/

section Uniform

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta)

include hKernel in
/-- **eq:elim-bdry** (`prop:elim` (ii)): there is `C` with `|⟨ψ(t), Y ψ(t)⟩| ≤ C Ξ² K^{-3}` for
every datum, every time and every cutoff `n ≥ 2` with `K = g n ≥ 1`. -/
theorem thm_elim_bdry (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (hn : 2 ≤ n), 1 ≤ Kc L n → ∀ (D : EvoData L H) (t : ℝ),
      ‖⟪D.U t (Sm eta L D.u₀), Yop sys hL hn p₀ (D.U t (Sm eta L D.u₀))⟫_ℂ‖ ≤
        C * D.Xi ^ 2 * Kc L n ^ (-(3 : ℝ)) := by
  have hc := cTr_nonneg sys hL Hunit
  have hY := cYQ_nonneg (sys := sys) p₀ hL
  refine ⟨2 * eta * cYQ sys L p₀ * Real.sqrt (gF L) * cTr sys L Hunit ^ 2, by positivity, ?_⟩
  intro n hn hK D t
  rw [Kc_eq] at hK ⊢
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D t
  rw [← hw1]
  refine (elim_bdry_state (sys := sys) p₀ hL hn hK hF).trans (le_of_eq ?_)
  ring

include hKernel in
/-- **`prop:elim`**: `|∫₀ᵗ G_b + ∫₀ᵗ 𝔚| ≤ C Ξ² K^{-3}` (eq:elim with eq:elim-bdry). -/
theorem thm_elim (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (hn : 2 ≤ n), 1 ≤ Kc L n → ∀ (D : EvoData L H) (t : ℝ),
      |(∫ s in (0 : ℝ)..t, (Gb sys hL p₀ n (traj H D s) (traj H D s)).re) +
          ∫ s in (0 : ℝ)..t, (Wf sys hL hn p₀ H (traj H D s) (traj H D s)).re| ≤
        C * D.Xi ^ 2 * Kc L n ^ (-(3 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := thm_elim_bdry sys hL H hKernel p₀ Hunit hPeriodic
  refine ⟨2 * C, by positivity, ?_⟩
  intro n hn hK D t
  have hI := elim_integral sys hL hn H hKernel p₀ Hunit hPeriodic D t
  have h1 := hb n hn hK D t
  have h0 := hb n hn hK D 0
  rw [D.U0] at h0
  have e : (∫ s in (0 : ℝ)..t, (Gb sys hL p₀ n (traj H D s) (traj H D s)).re) +
      ∫ s in (0 : ℝ)..t, (Wf sys hL hn p₀ H (traj H D s) (traj H D s)).re =
      (⟪D.U t (Sm eta L D.u₀), Yop sys hL hn p₀ (D.U t (Sm eta L D.u₀))⟫_ℂ).re -
        (⟪Sm eta L D.u₀, Yop sys hL hn p₀ (Sm eta L D.u₀)⟫_ℂ).re := by
    rw [hI]; ring
  rw [e]
  have a1 := Complex.abs_re_le_norm
    ⟪D.U t (Sm eta L D.u₀), Yop sys hL hn p₀ (D.U t (Sm eta L D.u₀))⟫_ℂ
  have a0 := Complex.abs_re_le_norm ⟪Sm eta L D.u₀, Yop sys hL hn p₀ (Sm eta L D.u₀)⟫_ℂ
  calc _ ≤ |(⟪D.U t (Sm eta L D.u₀), Yop sys hL hn p₀ (D.U t (Sm eta L D.u₀))⟫_ℂ).re| +
        |(⟪Sm eta L D.u₀, Yop sys hL hn p₀ (Sm eta L D.u₀)⟫_ℂ).re| := abs_sub _ _
    _ ≤ C * D.Xi ^ 2 * Kc L n ^ (-(3 : ℝ)) + C * D.Xi ^ 2 * Kc L n ^ (-(3 : ℝ)) := by linarith
    _ = 2 * C * D.Xi ^ 2 * Kc L n ^ (-(3 : ℝ)) := by ring

end Uniform

end FSFlux
