import PlaneWave.Source.SourceLeftovers

/-!
# Flux route, part 1: the force form, eq:flux-id, eq:hardy-a and `thm:flux`

The force `G = i[W, A_{p₀}]` of `app:flux` exists only as a form on `D(T)` (its operator contains a
contact term), so it is defined on the `H²` coordinates `u, v` (`ψ = S u`):

  `𝔊(u, v) = i ⟨W u, A v⟩ - i ⟨A u, W v⟩`        (`Gf`; `A = A_{p₀}` on `H²`, `W = H - T`).

* the algebra of `𝔊` (sesquilinear, `𝔊(v, u) = conj 𝔊(u, v)`, `𝔊(u, u)` real);
* **eq:hardy-a** by the direct proof: `|𝔊(u, v)| ≤ ‖W u‖ ‖A v‖ + ‖A u‖ ‖W v‖`, with Hardy
  `‖W u‖ ≤ C_m (Σ (1 + 2E)|S u|²)^{1/2}` (no position-space representation eq:antisym is needed);
* **eq:flux-id** for the exact evolution: `d/dt ⟨ψ(t), A ψ(t)⟩ = 𝔊(w_t, w_t)` (`flux_id`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The force form -/

section Form

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (p₀ : Fin eta)

/-- The observable `A_{p₀}` on the `H²` coordinates. -/
noncomputable abbrev Ap : MolecularFourierH2 eta →L[ℂ] L2 eta := (regKin sys (gF L) p₀).h2

/-- **The force form** `𝔊(u, v) = ⟨S u, i[W, A] S v⟩ := i ⟨W u, A v⟩ - i ⟨A u, W v⟩` on `D(T)`. -/
noncomputable def Gf (u v : MolecularFourierH2 eta) : ℂ :=
  Complex.I * ⟪Wp sys L H u, Ap sys L p₀ v⟫_ℂ - Complex.I * ⟪Ap sys L p₀ u, Wp sys L H v⟫_ℂ

omit [Fintype ν] in
lemma Gf_add_left (u u' v : MolecularFourierH2 eta) :
    Gf sys L H p₀ (u + u') v = Gf sys L H p₀ u v + Gf sys L H p₀ u' v := by
  unfold Gf; rw [map_add, map_add, inner_add_left, inner_add_left]; ring

omit [Fintype ν] in
lemma Gf_add_right (u v v' : MolecularFourierH2 eta) :
    Gf sys L H p₀ u (v + v') = Gf sys L H p₀ u v + Gf sys L H p₀ u v' := by
  unfold Gf; rw [map_add, map_add, inner_add_right, inner_add_right]; ring

omit [Fintype ν] in
lemma Gf_sub_left (u u' v : MolecularFourierH2 eta) :
    Gf sys L H p₀ (u - u') v = Gf sys L H p₀ u v - Gf sys L H p₀ u' v := by
  unfold Gf; rw [map_sub, map_sub, inner_sub_left, inner_sub_left]; ring

omit [Fintype ν] in
lemma Gf_sub_right (u v v' : MolecularFourierH2 eta) :
    Gf sys L H p₀ u (v - v') = Gf sys L H p₀ u v - Gf sys L H p₀ u v' := by
  unfold Gf; rw [map_sub, map_sub, inner_sub_right, inner_sub_right]; ring

omit [Fintype ν] in
/-- `𝔊(v, u) = conj 𝔊(u, v)`. -/
lemma Gf_swap (u v : MolecularFourierH2 eta) :
    Gf sys L H p₀ v u = conj (Gf sys L H p₀ u v) := by
  unfold Gf
  rw [map_sub, map_mul, map_mul, Complex.conj_I, inner_conj_symm, inner_conj_symm]
  ring

omit [Fintype ν] in
/-- `𝔊(u, u)` is real. -/
lemma Gf_self_im (u : MolecularFourierH2 eta) : (Gf sys L H p₀ u u).im = 0 := by
  have h := Gf_swap sys L H p₀ u u
  have h2 := congrArg Complex.im h
  rw [Complex.conj_im] at h2
  linarith

omit [Fintype ν] in
lemma Gf_self_eq (u : MolecularFourierH2 eta) :
    Gf sys L H p₀ u u = ((Gf sys L H p₀ u u).re : ℂ) :=
  Complex.ext (by simp) (by simp [Gf_self_im])

omit [Fintype ν] in
/-- `𝔊(a + d, a + d) - 𝔊(a, a) = 𝔊(d, d) + 2 Re 𝔊(d, a)` (real parts). -/
lemma Gf_expand_re (a d : MolecularFourierH2 eta) :
    (Gf sys L H p₀ (a + d) (a + d)).re - (Gf sys L H p₀ a a).re =
      (Gf sys L H p₀ d d).re + 2 * (Gf sys L H p₀ d a).re := by
  rw [Gf_add_left, Gf_add_right, Gf_add_right, Gf_swap sys L H p₀ d a]
  simp only [Complex.add_re, Complex.conj_re]
  ring

omit [Fintype ν] in
/-- **eq:hardy-a, direct form**: `|𝔊(u, v)| ≤ ‖W u‖ ‖A v‖ + ‖A u‖ ‖W v‖`. -/
lemma norm_Gf_le (u v : MolecularFourierH2 eta) :
    ‖Gf sys L H p₀ u v‖ ≤
      ‖Wp sys L H u‖ * ‖Ap sys L p₀ v‖ + ‖Ap sys L p₀ u‖ * ‖Wp sys L H v‖ := by
  unfold Gf
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_I, one_mul]; exact norm_inner_le_norm _ _
  · rw [norm_mul, Complex.norm_I, one_mul]; exact norm_inner_le_norm _ _

omit [Fintype ν] in
/-- `‖A u‖ ≤ ‖T u‖`. -/
lemma norm_Ap_le (u : MolecularFourierH2 eta) :
    ‖Ap sys L p₀ u‖ ≤ ‖coulombFourierKineticH2 sys (gF L) u‖ :=
  (regKin sys (gF L) p₀).norm_h2_le u

omit [Fintype ν] in
/-- The energy form of an `H²` state: `Σ (1 + 2E)|S u|² ≤ ‖S u‖ (‖S u‖ + 2 ‖T u‖)`. -/
lemma form_le_norm_mul (u : MolecularFourierH2 eta) :
    ∑' q, (1 + 2 * Ek sys L q) * ‖Sm eta L u q‖ ^ 2 ≤
      ‖Sm eta L u‖ * (‖Sm eta L u‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) u‖) := by
  set x := Sm eta L u
  set y := coulombFourierKineticH2 sys (gF L) u
  have hy : ∀ q, y q = (Ek sys L q : ℂ) * x q := fun q => by
    simp only [y, x, coulombFourierKineticH2_apply, Sm, molecularH2StateMap_apply, Ek,
      E_eq_kineticSymbol]
  have hsum := lp.hasSum_inner (𝕜 := ℂ) x (x + (2 : ℂ) • y)
  have e : (fun q => ⟪(x : Cf eta → ℂ) q, ((x + (2 : ℂ) • y : L2 eta) : Cf eta → ℂ) q⟫_ℂ) =
      fun q => (((1 + 2 * Ek sys L q) * ‖x q‖ ^ 2 : ℝ) : ℂ) := by
    funext q
    rw [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hy q,
      RCLike.inner_apply]
    rw [show (x q + 2 * ((Ek sys L q : ℂ) * x q)) = ((1 + 2 * Ek sys L q : ℝ) : ℂ) * x q by
      push_cast; ring]
    rw [mul_comm]
    exact conj_mul_ofReal_mul _ _
  rw [e] at hsum
  have hsumR : HasSum (fun q => (1 + 2 * Ek sys L q) * ‖x q‖ ^ 2) (⟪x, x + (2 : ℂ) • y⟫_ℂ).re := by
    have h := Complex.reCLM.hasSum hsum
    simp only [Complex.reCLM_apply, Complex.ofReal_re] at h
    exact h
  rw [hsumR.tsum_eq]
  have h1 : (⟪x, x + (2 : ℂ) • y⟫_ℂ).re ≤ ‖x‖ * ‖x + (2 : ℂ) • y‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : ‖x + (2 : ℂ) • y‖ ≤ ‖x‖ + 2 * ‖y‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]; simp
  calc (⟪x, x + (2 : ℂ) • y⟫_ℂ).re ≤ ‖x‖ * ‖x + (2 : ℂ) • y‖ := h1
    _ ≤ ‖x‖ * (‖x‖ + 2 * ‖y‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

omit [Fintype ν] in
/-- `⟨T u, A u⟩ = ⟨A u, T u⟩` (both are real diagonal multipliers). -/
lemma inner_kin_Ap_comm (u : MolecularFourierH2 eta) :
    ⟪coulombFourierKineticH2 sys (gF L) u, Ap sys L p₀ u⟫_ℂ =
      ⟪Ap sys L p₀ u, coulombFourierKineticH2 sys (gF L) u⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun q => ?_
  rw [coulombFourierKineticH2_apply, KinMult.h2_apply]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

omit [Fintype ν] in
/-- The energy identity of the form: `E(S a) - E(S b) = Re (⟨S a - S b, A a⟩ + ⟨A b, S a - S b⟩)`. -/
lemma expect_sub_eq (a b : MolecularFourierH2 eta) :
    (regKin sys (gF L) p₀).expect (Sm eta L a) - (regKin sys (gF L) p₀).expect (Sm eta L b) =
      (⟪Sm eta L a - Sm eta L b, Ap sys L p₀ a⟫_ℂ + ⟪Ap sys L p₀ b, Sm eta L a - Sm eta L b⟫_ℂ).re := by
  set m := regKin sys (gF L) p₀
  have e : ((m.expect (Sm eta L a) - m.expect (Sm eta L b) : ℝ) : ℂ) =
      ⟪Sm eta L a - Sm eta L b, m.h2 a⟫_ℂ + ⟪m.h2 b, Sm eta L a - Sm eta L b⟫_ℂ := by
    push_cast
    rw [← m.inner_stateMap_h2_self, ← m.inner_stateMap_h2_self, inner_sub_left, inner_sub_right,
      ← m.inner_stateMap_h2 b a, ← m.inner_stateMap_h2 b b]
    ring
  have h := congrArg Complex.re e
  rw [Complex.ofReal_re] at h
  exact h

end Form

/-! ## eq:flux-id -/

section FluxId

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta)

/-- The `H²` coordinate of `ψ(t)`: `S w_t = U(t) S u₀`, `H w_t = U(t) H u₀`. -/
noncomputable def traj (D : EvoData L H) (t : ℝ) : MolecularFourierH2 eta :=
  Classical.choose (D.graph t D.u₀)

omit [Fintype ν] in
lemma traj_S (D : EvoData L H) (t : ℝ) : Sm eta L (traj H D t) = D.U t (Sm eta L D.u₀) :=
  (Classical.choose_spec (D.graph t D.u₀)).1

omit [Fintype ν] in
lemma traj_H (D : EvoData L H) (t : ℝ) : H (traj H D t) = D.U t (H D.u₀) :=
  (Classical.choose_spec (D.graph t D.u₀)).2

omit [Fintype ν] in
/-- The coordinate is unique. -/
lemma traj_eq (D : EvoData L H) (t : ℝ) (w : MolecularFourierH2 eta)
    (hw : Sm eta L w = D.U t (Sm eta L D.u₀)) : traj H D t = w :=
  molecularH2StateMap_injective eta (gF L) (by
    change Sm eta L (traj H D t) = Sm eta L w; rw [traj_S, hw])

include hKernel hL in
/-- `s ↦ A w_s` is continuous (the elliptic estimate `‖T u‖ ≤ 2 ‖H u‖ + 2b ‖S u‖`). -/
lemma continuous_Ap_traj (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) : Continuous fun s => Ap sys L p₀ (traj H D s) := by
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
  have hA := norm_Ap_le sys L p₀ d
  have hb1 : 0 < 1 + relB sys L Hunit := by linarith
  have key : 2 * relB sys L Hunit * ‖molecularH2StateMap eta (2 * Real.pi / L) d‖ ≤ ε / 2 := by
    have h3 : relB sys L Hunit * ‖molecularH2StateMap eta (2 * Real.pi / L) d‖ ≤
        (1 + relB sys L Hunit) * (ε / (4 * (1 + relB sys L Hunit))) := by
      apply mul_le_mul (by linarith) hSd.le (norm_nonneg _) hb1.le
    have h4 : (1 + relB sys L Hunit) * (ε / (4 * (1 + relB sys L Hunit))) = ε / 4 := by
      field_simp
    linarith
  change ‖Ap sys L p₀ d‖ < ε
  have : ‖coulombFourierKineticH2 sys (gF L) d‖ ≤
      2 * ‖H d‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta (2 * Real.pi / L) d‖ := hT
  linarith

include hKernel hL in
/-- **eq:flux-id** (exact evolution): `d/dt ⟨ψ(t), A_{p₀} ψ(t)⟩ = 𝔊(w_t, w_t)`, the force form of
the state, for `ψ₀ ∈ D(H²)`. -/
theorem flux_id (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (t : ℝ) :
    HasDerivAt (fun s => (regKin sys (gF L) p₀).expect (D.U s (Sm eta L D.u₀)))
      (Gf sys L H p₀ (traj H D t) (traj H D t)).re t := by
  set w := traj H D t
  set ψ' : L2 eta := -(Complex.I • D.U t (H D.u₀))
  have hψ := D.deriv t D.u₀
  rw [hasDerivAt_iff_tendsto_slope] at hψ ⊢
  have hcont := (continuous_Ap_traj sys hL H hKernel p₀ Hunit hPeriodic D).continuousAt (x := t)
  have hcA : Tendsto (fun s => Ap sys L p₀ (traj H D s)) (𝓝[≠] t) (𝓝 (Ap sys L p₀ w)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- the slope of the energy
  have hslope : ∀ s, slope (fun s => (regKin sys (gF L) p₀).expect (D.U s (Sm eta L D.u₀))) t s =
      (⟪slope (fun s => D.U s (Sm eta L D.u₀)) t s, Ap sys L p₀ (traj H D s)⟫_ℂ +
        ⟪Ap sys L p₀ w, slope (fun s => D.U s (Sm eta L D.u₀)) t s⟫_ℂ).re := by
    intro s
    have e := expect_sub_eq sys L p₀ (traj H D s) w
    rw [traj_S, traj_S] at e
    rw [slope_def_field, e, slope_def_module]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (s - t)⁻¹ := ⟨_, rfl⟩
    rw [← hr, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, inner_smul_right,
      div_eq_inv_mul, ← hr]
    simp [Complex.mul_re]
    ring
  have hlim : Tendsto (fun s =>
      (⟪slope (fun s => D.U s (Sm eta L D.u₀)) t s, Ap sys L p₀ (traj H D s)⟫_ℂ +
        ⟪Ap sys L p₀ w, slope (fun s => D.U s (Sm eta L D.u₀)) t s⟫_ℂ).re) (𝓝[≠] t)
      (𝓝 ((⟪ψ', Ap sys L p₀ w⟫_ℂ + ⟪Ap sys L p₀ w, ψ'⟫_ℂ).re)) := by
    refine Complex.continuous_re.continuousAt.tendsto.comp ?_
    exact (hψ.inner hcA).add (tendsto_const_nhds.inner hψ)
  -- identify the limit with the force form
  have hval : (⟪ψ', Ap sys L p₀ w⟫_ℂ + ⟪Ap sys L p₀ w, ψ'⟫_ℂ).re = (Gf sys L H p₀ w w).re := by
    have hHw : D.U t (H D.u₀) = coulombFourierKineticH2 sys (gF L) w + Wp sys L H w := by
      rw [← traj_H]
      exact coulombFourierHamiltonianH2_decomposition sys (gF L) H w
    have hTA := inner_kin_Ap_comm sys L p₀ w
    simp only [ψ', inner_neg_left, inner_neg_right, inner_smul_left, inner_smul_right, hHw,
      inner_add_left, inner_add_right, Complex.conj_I]
    unfold Gf
    rw [hTA]
    ring_nf
  rw [← hval]
  exact hlim.congr (fun s => (hslope s).symm)

end FluxId

/-! ## `thm:flux` -/

section Flux

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta)

omit [Fintype ν] in
/-- The ball block of radius `m/4` lies in the cube of radius `n` when `m ≤ 4n`. -/
lemma Qs_subset_cube {m n : ℕ} (hm : m ≤ 4 * n) : Qs eta m ⊆ fourierConfigCube eta n := by
  intro q hq
  rw [← inP_iff_mem_cube]
  intro c i
  have h1 := coord_sq_le_nsq (q c) i
  have h2 := (mem_Qs.mp hq) c
  have : |((q c i : ℤ) : ℝ)| ≤ (m : ℝ) / 4 := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, h1.trans h2⟩
  have hm' : (m : ℝ) ≤ 4 * n := by exact_mod_cast hm
  linarith

include hL in
omit [Fintype ν] in
/-- **Union bound for the ball block**: `‖(1 - Q_m) x‖ ≤ Σ_a ‖1_{a, > g m/4} x‖`. -/
lemma norm_sub_truncQ_le (m : ℕ) (x : L2 eta) :
    ‖x - lpTruncate (Qs eta m) x‖ ≤ ∑ a : Fin eta, ‖tailMask (gF L) (gF L * m / 4) a x‖ := by
  classical
  have hg := gF_pos hL
  have hsq : ‖x - lpTruncate (Qs eta m) x‖ ^ 2 ≤
      ∑ a : Fin eta, ‖tailMask (gF L) (gF L * m / 4) a x‖ ^ 2 := by
    rw [l2_norm_sq]
    have hsum : ∀ a ∈ (Finset.univ : Finset (Fin eta)),
        Summable fun p => ‖tailMask (gF L) (gF L * m / 4) a x p‖ ^ 2 := fun a _ => l2_summable_sq _
    calc ∑' p, ‖(x - lpTruncate (Qs eta m) x) p‖ ^ 2
        ≤ ∑' p, ∑ a : Fin eta, ‖tailMask (gF L) (gF L * m / 4) a x p‖ ^ 2 := by
          refine (l2_summable_sq _).tsum_le_tsum (fun p => ?_)
            (summable_sum fun a _ => l2_summable_sq _)
          rw [lp.coeFn_sub, Pi.sub_apply, lpTruncate_apply]
          by_cases hp : p ∈ Qs eta m
          · rw [if_pos hp, sub_self, norm_zero]
            simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
            exact Finset.sum_nonneg (fun a _ => sq_nonneg _)
          · rw [if_neg hp, sub_zero]
            have hnq : ¬ InQ (m : ℝ) p := fun h => hp (mem_Qs.mpr h)
            unfold InQ at hnq
            push Not at hnq
            obtain ⟨a, ha⟩ := hnq
            have hlt : gF L * m / 4 < gF L * Real.sqrt (latticeNormSq (p a)) := by
              have h1 : (m : ℝ) / 4 < Real.sqrt (latticeNormSq (p a)) := by
                rw [← nsq_eq_latticeNormSq]
                exact Real.lt_sqrt_of_sq_lt ha
              rw [mul_div_assoc]
              exact mul_lt_mul_of_pos_left h1 hg
            have hterm : ‖tailMask (gF L) (gF L * m / 4) a x p‖ ^ 2 =
                ‖(x : FourierConfig eta Lattice3 → ℂ) p‖ ^ 2 := by
              rw [tailMask_apply, if_pos hlt, one_mul]
            rw [← hterm]
            exact Finset.single_le_sum (f := fun a => ‖tailMask (gF L) (gF L * m / 4) a x p‖ ^ 2)
              (fun a _ => sq_nonneg _) (Finset.mem_univ a)
      _ = ∑ a : Fin eta, ∑' p, ‖tailMask (gF L) (gF L * m / 4) a x p‖ ^ 2 :=
          Summable.tsum_finsetSum hsum
      _ = ∑ a : Fin eta, ‖tailMask (gF L) (gF L * m / 4) a x‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [l2_norm_sq]
  have h2 : ∑ a : Fin eta, ‖tailMask (gF L) (gF L * m / 4) a x‖ ^ 2 ≤
      (∑ a : Fin eta, ‖tailMask (gF L) (gF L * m / 4) a x‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun a _ => norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.sum_nonneg fun a _ => norm_nonneg _)
    two_ne_zero).mp (hsq.trans h2)

/-- The `H²` coordinate of `1_{>λ} P ψ` (`λ = K/2`): `P w - 1_{Q'} w`, `Q'` the `K/2`-balls. -/
noncomputable def hotA (L : ℝ) (n : ℕ) (w : MolecularFourierH2 eta) : MolecularFourierH2 eta :=
  molecularH2Truncate n w - liftQ L (2 * n) (Sm eta L w)

omit [Fintype ν] in
lemma stateMap_hotA (n : ℕ) (w : MolecularFourierH2 eta) :
    Sm eta L (hotA L n w) =
      molecularH2Truncate n (Sm eta L w) - lpTruncate (Qs eta (2 * n)) (Sm eta L w) := by
  unfold hotA
  rw [map_sub, stateMap_liftQ, Sm, stateMap_truncate]

omit [Fintype ν] in
lemma kinetic_liftQ (m : ℕ) (w : MolecularFourierH2 eta) :
    coulombFourierKineticH2 sys (gF L) (liftQ L m (Sm eta L w)) =
      lpTruncate (Qs eta m) (coulombFourierKineticH2 sys (gF L) w) := by
  ext q
  rw [coulombFourierKineticH2_apply, lpTruncate_apply, ← molecularH2StateMap_apply,
    show molecularH2StateMap eta (gF L) (liftQ L m (Sm eta L w)) = lpTruncate (Qs eta m) (Sm eta L w)
      from stateMap_liftQ m (Sm eta L w), lpTruncate_apply]
  split_ifs
  · rw [coulombFourierKineticH2_apply, Sm, molecularH2StateMap_apply]
  · simp

omit [Fintype ν] in
lemma kinetic_hotA (n : ℕ) (w : MolecularFourierH2 eta) :
    coulombFourierKineticH2 sys (gF L) (hotA L n w) =
      molecularH2Truncate n (coulombFourierKineticH2 sys (gF L) w) -
        lpTruncate (Qs eta (2 * n)) (coulombFourierKineticH2 sys (gF L) w) := by
  unfold hotA
  rw [map_sub, kinetic_liftQ, kinetic_truncate]

include hL in
omit [Fintype ν] in
/-- `‖P x - 1_{Q'} x‖ ≤ ‖x - 1_{Q'} x‖` (`Q' ⊂ P`). -/
lemma norm_trunc_sub_truncQ_le (n : ℕ) (x : L2 eta) :
    ‖molecularH2Truncate n x - lpTruncate (Qs eta (2 * n)) x‖ ≤
      ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n / 2) a x‖ := by
  classical
  have hsub := Qs_subset_cube (eta := eta) (m := 2 * n) (n := n) (by omega)
  have h1 : ‖molecularH2Truncate n x - lpTruncate (Qs eta (2 * n)) x‖ ≤
      1 * ‖x - lpTruncate (Qs eta (2 * n)) x‖ := by
    refine l2_norm_le_of_le _ _ zero_le_one fun q => ?_
    rw [one_mul, lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply, molecularH2Truncate_apply,
      lpTruncate_apply]
    by_cases hq : q ∈ fourierConfigCube eta n
    · rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hq]
    · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq, if_neg (fun h => hq (hsub h))]
      simp
  have h2 := norm_sub_truncQ_le hL (2 * n) x
  have e : gF L * ((2 * n : ℕ) : ℝ) / 4 = gF L * n / 2 := by push_cast; ring
  rw [e] at h2
  linarith

include hKernel hL in
/-- **Hardy from the two norms**: `‖S u‖ ≤ a`, `‖T u‖ ≤ b`, `a ≤ b` give `‖W u‖ ≤ C_m (3ab)^{1/2}`. -/
lemma norm_W_le_of (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (u : MolecularFourierH2 eta) {a b : ℝ} (ha : ‖Sm eta L u‖ ≤ a)
    (hb : ‖coulombFourierKineticH2 sys (gF L) u‖ ≤ b) (hab : a ≤ b) :
    ‖Wp sys L H u‖ ≤ finiteCoulombPhysicalMassConstant sys L Hunit * Real.sqrt (3 * a * b) := by
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have h1 := potential_form_bound sys H hKernel Hunit hL hPeriodic u
  have h2 := form_le_norm_mul sys L u
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  have h3 : ‖Sm eta L u‖ * (‖Sm eta L u‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) u‖) ≤
      3 * a * b := by
    have := norm_nonneg (Sm eta L u)
    have := norm_nonneg (coulombFourierKineticH2 sys (gF L) u)
    nlinarith
  have h4 : ‖Wp sys L H u‖ ^ 2 ≤ (finiteCoulombPhysicalMassConstant sys L Hunit *
      Real.sqrt (3 * a * b)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by nlinarith)]
    calc _ ≤ _ := h1
      _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (3 * a * b) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4

omit [Fintype ν] in
/-- `(3 (x l^{-5/2}) (x l^{-1/2}))^{1/2} = √3 x l^{-3/2}`. -/
lemma sqrt_three_tail {x l : ℝ} (hx : 0 ≤ x) (hl : 0 < l) :
    Real.sqrt (3 * (x * l ^ (-(5 / 2 : ℝ))) * (x * l ^ (-(1 / 2 : ℝ)))) =
      Real.sqrt 3 * x * l ^ (-(3 / 2 : ℝ)) := by
  have e : 3 * (x * l ^ (-(5 / 2 : ℝ))) * (x * l ^ (-(1 / 2 : ℝ))) =
      3 * (x * l ^ (-(3 / 2 : ℝ))) ^ 2 := by
    have h1 : l ^ (-(5 / 2 : ℝ)) * l ^ (-(1 / 2 : ℝ)) = l ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_add hl]; norm_num
    have h2 : (l ^ (-(3 / 2 : ℝ))) ^ 2 = l ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]; norm_num
    rw [mul_pow, h2, ← h1]; ring
  rw [e, Real.sqrt_mul (by norm_num), Real.sqrt_sq (mul_nonneg hx (Real.rpow_nonneg hl.le _))]
  ring

/-- The near-cutoff constant of `thm:flux`: `√3 C_m η² (2 + 2(2^{1/2} + 2^{3/2}))`. -/
noncomputable def ncC (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * (eta : ℝ) ^ 2 *
    (2 + 2 * ((2 : ℝ) ^ (1 / 2 : ℝ) + (2 : ℝ) ^ (3 / 2 : ℝ)))

include hKernel hL in
/-- **eq:flux-nc** (`thm:flux`, the near-cutoff component): for a state `w` with `FGood M w`
(the exact `ψ(s)`), `δ = (1-P) w`, `a = P w` and `K = g n ≥ 2`,
`|⟨δ, G δ⟩| + 2 |⟨δ, G 1_{>K/2} a⟩| ≤ ncC M² K^{-2}`. -/
theorem flux_nc (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {n : ℕ} (hK : 2 ≤ gF L * n) {M : ℝ} {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    ‖Gf sys L H p₀ (w - molecularH2Truncate n w) (w - molecularH2Truncate n w)‖ +
        2 * ‖Gf sys L H p₀ (w - molecularH2Truncate n w) (hotA L n w)‖ ≤
      ncC sys L Hunit * M ^ 2 * (gF L * n) ^ (-(2 : ℝ)) := by
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hK2 : 1 ≤ K / 2 := by linarith
  have hM := hF.nonneg
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  set δ := w - molecularH2Truncate n w
  set U := hotA L n w
  set x := (eta : ℝ) * M
  have hx : 0 ≤ x := by positivity
  -- the exterior part
  have hSδ : ‖Sm eta L δ‖ ≤ x * K ^ (-(5 / 2 : ℝ)) := by
    rw [map_sub, Sm, stateMap_truncate]; exact fgood_R hF hL hK1
  have hTδ : ‖coulombFourierKineticH2 sys (gF L) δ‖ ≤ x * K ^ (-(1 / 2 : ℝ)) := by
    rw [map_sub, kinetic_truncate]
    refine (PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) n _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n) a (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ ∑ _a : Fin eta, M * K ^ (-(1 / 2 : ℝ)) := Finset.sum_le_sum fun a _ => (hF.2 a _ hK1).2
      _ = x * K ^ (-(1 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- the hot cube part `1_{>K/2} a`
  have hSU : ‖Sm eta L U‖ ≤ x * (K / 2) ^ (-(5 / 2 : ℝ)) := by
    rw [stateMap_hotA]
    refine (norm_trunc_sub_truncQ_le hL n _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n / 2) a (Sm eta L w)‖
        ≤ ∑ _a : Fin eta, M * (K / 2) ^ (-(5 / 2 : ℝ)) := Finset.sum_le_sum fun a _ => (hF.2 a _ hK2).1
      _ = x * (K / 2) ^ (-(5 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hTU : ‖coulombFourierKineticH2 sys (gF L) U‖ ≤ x * (K / 2) ^ (-(1 / 2 : ℝ)) := by
    rw [kinetic_hotA]
    refine (norm_trunc_sub_truncQ_le hL n _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n / 2) a (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ ∑ _a : Fin eta, M * (K / 2) ^ (-(1 / 2 : ℝ)) := Finset.sum_le_sum fun a _ => (hF.2 a _ hK2).2
      _ = x * (K / 2) ^ (-(1 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hle : ∀ l : ℝ, 1 ≤ l → x * l ^ (-(5 / 2 : ℝ)) ≤ x * l ^ (-(1 / 2 : ℝ)) := fun l hl =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hl (by norm_num)) hx
  have hWδ := norm_W_le_of sys hL H hKernel Hunit hPeriodic δ hSδ hTδ (hle K hK1)
  have hWU := norm_W_le_of sys hL H hKernel Hunit hPeriodic U hSU hTU (hle (K / 2) hK2)
  rw [sqrt_three_tail hx hK0] at hWδ
  rw [sqrt_three_tail hx (by linarith)] at hWU
  have hAδ := (norm_Ap_le sys L p₀ δ).trans hTδ
  have hAU := (norm_Ap_le sys L p₀ U).trans hTU
  have h1 := norm_Gf_le sys L H p₀ δ δ
  have h2 := norm_Gf_le sys L H p₀ δ U
  -- the cutoff powers
  have hK2r : ∀ r : ℝ, (K / 2) ^ r = (2 : ℝ) ^ (-r) * K ^ r := fun r => by
    rw [div_eq_mul_inv, Real.mul_rpow hK0.le (by norm_num), Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num)]
    ring
  have e1 : K ^ (-(3 / 2 : ℝ)) * K ^ (-(1 / 2 : ℝ)) = K ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hK0]; norm_num
  have e2 : K ^ (-(1 / 2 : ℝ)) * K ^ (-(3 / 2 : ℝ)) = K ^ (-(2 : ℝ)) := by
    rw [mul_comm, e1]
  rw [hK2r] at hWU hAU
  rw [show -(-(1 / 2 : ℝ)) = 1 / 2 by norm_num] at hAU
  rw [show -(-(3 / 2 : ℝ)) = 3 / 2 by norm_num] at hWU
  have hp := Real.rpow_nonneg hK0.le (-(1 / 2 : ℝ))
  have hq := Real.rpow_nonneg hK0.le (-(3 / 2 : ℝ))
  have hs3 := Real.sqrt_nonneg 3
  have h21 := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (1 / 2 : ℝ)
  have h23 := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (3 / 2 : ℝ)
  have hA : ‖Gf sys L H p₀ δ δ‖ ≤
      2 * (finiteCoulombPhysicalMassConstant sys L Hunit * (Real.sqrt 3 * x * K ^ (-(3 / 2 : ℝ)))) *
        (x * K ^ (-(1 / 2 : ℝ))) := by
    refine h1.trans ?_
    have := mul_le_mul hWδ hAδ (norm_nonneg _) (by positivity)
    have := mul_le_mul hAδ hWδ (norm_nonneg _) (by positivity)
    nlinarith
  have hB : ‖Gf sys L H p₀ δ U‖ ≤
      finiteCoulombPhysicalMassConstant sys L Hunit * (Real.sqrt 3 * x * K ^ (-(3 / 2 : ℝ))) *
          (x * ((2 : ℝ) ^ (1 / 2 : ℝ) * K ^ (-(1 / 2 : ℝ)))) +
        x * K ^ (-(1 / 2 : ℝ)) * (finiteCoulombPhysicalMassConstant sys L Hunit *
          (Real.sqrt 3 * x * ((2 : ℝ) ^ (3 / 2 : ℝ) * K ^ (-(3 / 2 : ℝ))))) :=
    h2.trans (add_le_add (mul_le_mul hWδ hAU (norm_nonneg _) (by positivity))
      (mul_le_mul hAδ hWU (norm_nonneg _) (by positivity)))
  have hfin : 2 * (finiteCoulombPhysicalMassConstant sys L Hunit *
        (Real.sqrt 3 * x * K ^ (-(3 / 2 : ℝ)))) * (x * K ^ (-(1 / 2 : ℝ))) +
      2 * (finiteCoulombPhysicalMassConstant sys L Hunit * (Real.sqrt 3 * x * K ^ (-(3 / 2 : ℝ))) *
          (x * ((2 : ℝ) ^ (1 / 2 : ℝ) * K ^ (-(1 / 2 : ℝ)))) +
        x * K ^ (-(1 / 2 : ℝ)) * (finiteCoulombPhysicalMassConstant sys L Hunit *
          (Real.sqrt 3 * x * ((2 : ℝ) ^ (3 / 2 : ℝ) * K ^ (-(3 / 2 : ℝ)))))) =
      ncC sys L Hunit * M ^ 2 * K ^ (-(2 : ℝ)) := by
    unfold ncC
    rw [← e1]
    simp only [x]
    ring
  linarith

omit [Fintype ν] in
/-- The arithmetic of eq:flux-bd. -/
lemma bd_arith {Cm η M K m c : ℝ} (hK0 : 0 < K) (hK1 : 1 ≤ K) (hCm : 0 ≤ Cm) (hη : 0 ≤ η)
    (_hM : 0 ≤ M) (_hm : 0 ≤ m) (_hc : 0 ≤ c) :
    2 * (Cm * (Real.sqrt 3 * (η * M) * K ^ (-(3 / 2 : ℝ)))) * ((η * M) * K ^ (-(1 / 2 : ℝ))) +
        2 * (Cm * (Real.sqrt 3 * (η * M) * K ^ (-(3 / 2 : ℝ))) * M +
          (η * M) * K ^ (-(1 / 2 : ℝ)) * (η * (c * (2 * m * M) * K ^ (-(1 / 2 : ℝ))))) ≤
      (2 * Real.sqrt 3 * Cm * η ^ 2 + 2 * Real.sqrt 3 * Cm * η + 4 * η ^ 2 * m * c) * M ^ 2 *
        K ^ (-(1 : ℝ)) := by
  have e1 : K ^ (-(3 / 2 : ℝ)) * K ^ (-(1 / 2 : ℝ)) = K ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hK0]; norm_num
  have e2 : K ^ (-(1 / 2 : ℝ)) * K ^ (-(1 / 2 : ℝ)) = K ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hK0]; norm_num
  have l1 : K ^ (-(2 : ℝ)) ≤ K ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)
  have l2 : K ^ (-(3 / 2 : ℝ)) ≤ K ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)
  obtain ⟨k2, hk2⟩ : ∃ k, k = K ^ (-(2 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨k1, hk1⟩ : ∃ k, k = K ^ (-(1 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨k32, hk32⟩ : ∃ k, k = K ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨k12, hk12⟩ : ∃ k, k = K ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  rw [← hk2, ← hk32, ← hk12] at e1
  rw [← hk12, ← hk1] at e2
  rw [← hk2, ← hk1] at l1
  rw [← hk32, ← hk1] at l2
  rw [← hk32, ← hk12, ← hk1]
  have hs3 := Real.sqrt_nonneg 3
  have h1 : 2 * (Cm * (Real.sqrt 3 * (η * M) * k32)) * ((η * M) * k12) =
      2 * Real.sqrt 3 * Cm * η ^ 2 * M ^ 2 * k2 := by rw [← e1]; ring
  have h2 : 2 * (Cm * (Real.sqrt 3 * (η * M) * k32) * M) = 2 * Real.sqrt 3 * Cm * η * M ^ 2 * k32 := by
    ring
  have h3 : 2 * ((η * M) * k12 * (η * (c * (2 * m * M) * k12))) = 4 * η ^ 2 * m * c * M ^ 2 * k1 := by
    rw [← e2]; ring
  have i1 : 2 * Real.sqrt 3 * Cm * η ^ 2 * M ^ 2 * k2 ≤ 2 * Real.sqrt 3 * Cm * η ^ 2 * M ^ 2 * k1 :=
    mul_le_mul_of_nonneg_left l1 (by positivity)
  have i2 : 2 * Real.sqrt 3 * Cm * η * M ^ 2 * k32 ≤ 2 * Real.sqrt 3 * Cm * η * M ^ 2 * k1 :=
    mul_le_mul_of_nonneg_left l2 (by positivity)
  nlinarith [h1, h2, h3, i1, i2]

/-- The constant of eq:flux-bd: `2√3 C_m η² + 2√3 C_m η + 4 η² m̄ C_tail(1)`. -/
noncomputable def bdC (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  2 * Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * (eta : ℝ) ^ 2 +
    2 * Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * eta +
    4 * (eta : ℝ) ^ 2 * sys.maxMass * CtW sys L Hunit 1

set_option maxHeartbeats 400000 in
include hKernel hL in
/-- **eq:flux-bd** (`thm:flux`, the full projection flux): for a state `w` with `FGood M w`,
`a = P w` and `K = g n ≥ 2`, `n ≥ 2`, `|⟨ψ, G ψ⟩ - ⟨P ψ, G P ψ⟩| ≤ bdC M² K^{-1}`. -/
theorem flux_bd (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {n : ℕ} (hn : 2 ≤ n) (hK : 2 ≤ gF L * n) {M : ℝ} {w : MolecularFourierH2 eta}
    (hF : FGood sys L M w) :
    |(Gf sys L H p₀ w w).re - (Gf sys L H p₀ (molecularH2Truncate n w) (molecularH2Truncate n w)).re| ≤
      bdC sys L Hunit * M ^ 2 * (gF L * n) ^ (-(1 : ℝ)) := by
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hM := hF.nonneg
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  set δ := w - molecularH2Truncate n w
  set a := molecularH2Truncate n w
  set x := (eta : ℝ) * M
  have hx : 0 ≤ x := by positivity
  have hsplit : w = a + δ := by simp only [a, δ]; abel
  have hexp := Gf_expand_re sys L H p₀ a δ
  rw [← hsplit] at hexp
  rw [hexp]
  -- the exterior part, as in `flux_nc`
  have hSδ : ‖Sm eta L δ‖ ≤ x * K ^ (-(5 / 2 : ℝ)) := by
    rw [map_sub, Sm, stateMap_truncate]; exact fgood_R hF hL hK1
  have hTδ : ‖coulombFourierKineticH2 sys (gF L) δ‖ ≤ x * K ^ (-(1 / 2 : ℝ)) := by
    rw [map_sub, kinetic_truncate]
    refine (PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) n _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n) a (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ ∑ _a : Fin eta, M * K ^ (-(1 / 2 : ℝ)) := Finset.sum_le_sum fun a _ => (hF.2 a _ hK1).2
      _ = x * K ^ (-(1 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hle : x * K ^ (-(5 / 2 : ℝ)) ≤ x * K ^ (-(1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)) hx
  have hWδ := norm_W_le_of sys hL H hKernel Hunit hPeriodic δ hSδ hTδ hle
  rw [sqrt_three_tail hx hK0] at hWδ
  have hAδ := (norm_Ap_le sys L p₀ δ).trans hTδ
  -- the cube part
  have hTa : ‖coulombFourierKineticH2 sys (gF L) a‖ ≤ M := by
    simp only [a]
    rw [kinetic_truncate]
    refine (molecularH2Truncate_norm_le n _).trans ?_
    have := hF.1; have := norm_nonneg (Sm eta L w); linarith
  have hAa := (norm_Ap_le sys L p₀ a).trans hTa
  have ha2 : ‖a‖ ≤ 2 * sys.maxMass * M := by
    have h := PlaneWaveDynamics.h2norm_le sys L a
    have hS : ‖molecularH2StateMap eta (2 * Real.pi / L) a‖ ≤ ‖Sm eta L w‖ := by
      change ‖Sm eta L (molecularH2Truncate n w)‖ ≤ _
      rw [Sm, stateMap_truncate]; exact molecularH2Truncate_norm_le n _
    have hT : ‖coulombFourierKineticH2 sys (2 * Real.pi / L) a‖ ≤
        ‖coulombFourierKineticH2 sys (gF L) w‖ := by
      change ‖coulombFourierKineticH2 sys (gF L) (molecularH2Truncate n w)‖ ≤ _
      rw [kinetic_truncate]; exact molecularH2Truncate_norm_le n _
    have hm := sys.one_le_maxMass
    have h1 := hF.1
    have := norm_nonneg (Sm eta L w)
    have := norm_nonneg (coulombFourierKineticH2 sys (gF L) w)
    calc ‖a‖ ≤ sys.maxMass * (‖molecularH2StateMap eta (2 * Real.pi / L) a‖ +
          2 * ‖coulombFourierKineticH2 sys (2 * Real.pi / L) a‖) := h
      _ ≤ sys.maxMass * (2 * M) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          linarith
      _ = 2 * sys.maxMass * M := by ring
  -- the exterior output of `W a`: `‖(1-P) W a‖ ≤ η C_tail K^{-1/2}` (eq:lam-gen)
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  have hM2 : 0 ≤ 2 * sys.maxMass * M := by have := sys.one_le_maxMass; positivity
  have hρ : Real.sqrt (1 / K) ^ 2 * K = 1 := by
    rw [Real.sq_sqrt (by positivity)]; field_simp
  have h2g : 2 * (2 * Real.pi / L) ≤ K := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hg := gF_pos hL
    change 2 * gF L ≤ gF L * n
    nlinarith
  have hsq : Real.sqrt (1 / K) = K ^ (-(1 / 2 : ℝ)) := by
    rw [rpow_neg_half_eq hK0, Real.sqrt_div' 1 hK0.le, Real.sqrt_one]
  have hRW : ‖Wp sys L H a - molecularH2Truncate n (Wp sys L H a)‖ ≤
      eta * (CtW sys L Hunit (2 * sys.maxMass * M) * K ^ (-(1 / 2 : ℝ))) := by
    refine (PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) n _).trans ?_
    calc ∑ r : Fin eta, ‖tailMask (gF L) (gF L * n) r (Wp sys L H a)‖
        ≤ ∑ _r : Fin eta, CtW sys L Hunit (2 * sys.maxMass * M) * K ^ (-(1 / 2 : ℝ)) := by
          refine Finset.sum_le_sum fun r _ => ?_
          have h := potential_tail_le sys L H hKernel Hunit hL hPeriodic r K (Real.sqrt (1 / K))
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) (2 * sys.maxMass * M) hK1 (Real.sqrt_nonneg _) hρ
            hBlow hCs hBker hM2 h2g hLow hKernelScale hSobolev a ha2
          rw [hsq] at h
          exact h
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the cross term
  have hcross : ‖Gf sys L H p₀ δ a‖ ≤
      finiteCoulombPhysicalMassConstant sys L Hunit * (Real.sqrt 3 * x * K ^ (-(3 / 2 : ℝ))) * M +
        x * K ^ (-(1 / 2 : ℝ)) * (eta * (CtW sys L Hunit (2 * sys.maxMass * M) *
          K ^ (-(1 / 2 : ℝ)))) := by
    unfold Gf
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_I, one_mul]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul hWδ hAa (norm_nonneg _) (by positivity))
    · rw [norm_mul, Complex.norm_I, one_mul]
      have hAd : Ap sys L p₀ δ = Ap sys L p₀ w - molecularH2Truncate n (Ap sys L p₀ w) := by
        simp only [δ, map_sub]
        rw [(regKin sys (gF L) p₀).h2_truncate n w]
      rw [hAd, PlaneWaveDynamics.inner_sub_truncate_left, ← hAd]
      refine (norm_inner_le_norm _ _).trans (mul_le_mul hAδ hRW (norm_nonneg _) (by positivity))
  have hnc : ‖Gf sys L H p₀ δ δ‖ ≤
      2 * (finiteCoulombPhysicalMassConstant sys L Hunit * (Real.sqrt 3 * x * K ^ (-(3 / 2 : ℝ)))) *
        (x * K ^ (-(1 / 2 : ℝ))) := by
    refine (norm_Gf_le sys L H p₀ δ δ).trans ?_
    have := mul_le_mul hWδ hAδ (norm_nonneg _) (by positivity)
    have := mul_le_mul hAδ hWδ (norm_nonneg _) (by positivity)
    nlinarith
  -- collect
  have hre1 : |(Gf sys L H p₀ δ δ).re| ≤ ‖Gf sys L H p₀ δ δ‖ := Complex.abs_re_le_norm _
  have hre2 : |(Gf sys L H p₀ δ a).re| ≤ ‖Gf sys L H p₀ δ a‖ := Complex.abs_re_le_norm _
  have habs : |(Gf sys L H p₀ δ δ).re + 2 * (Gf sys L H p₀ δ a).re| ≤
      ‖Gf sys L H p₀ δ δ‖ + 2 * ‖Gf sys L H p₀ δ a‖ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  refine habs.trans ?_
  have hCtW : CtW sys L Hunit (2 * sys.maxMass * M) = CtW sys L Hunit 1 * (2 * sys.maxMass * M) :=
    CtW_eq_mul sys Hunit _
  have hCt1 : 0 ≤ CtW sys L Hunit 1 := CtW_nonneg sys hL Hunit zero_le_one
  rw [hCtW] at hcross
  have key := bd_arith (Cm := finiteCoulombPhysicalMassConstant sys L Hunit) (η := (eta : ℝ))
    (m := sys.maxMass) (c := CtW sys L Hunit 1) hK0 hK1 hCm (by positivity) hM
    (by have := sys.one_le_maxMass; linarith) hCt1
  have hsum : ‖Gf sys L H p₀ δ δ‖ + 2 * ‖Gf sys L H p₀ δ a‖ ≤
      2 * (finiteCoulombPhysicalMassConstant sys L Hunit * (Real.sqrt 3 * x * K ^ (-(3 / 2 : ℝ)))) *
          (x * K ^ (-(1 / 2 : ℝ))) +
        2 * (finiteCoulombPhysicalMassConstant sys L Hunit * (Real.sqrt 3 * x * K ^ (-(3 / 2 : ℝ))) * M +
          x * K ^ (-(1 / 2 : ℝ)) * (eta * (CtW sys L Hunit 1 * (2 * sys.maxMass * M) *
            K ^ (-(1 / 2 : ℝ))))) := by linarith
  refine hsum.trans (key.trans (le_of_eq ?_))
  unfold bdC; ring

end Flux

/-! ## The Galerkin flux identity and the uniform `thm:flux` -/

section Galerkin

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta) {n : ℕ}

omit [Fintype ν] in
/-- The expectation of `A_{p₀}` in a cube state: `⟨y, A_{p₀} y⟩`. -/
lemma expect_emb (y : En eta n) :
    ((regKin sys (gF L) p₀).expect (emb eta n y) : ℂ) = ⟪y, FSSrc1.bdatum sys L p₀ y⟫_ℂ := by
  rw [← stateMap_cubeLift' (L := L) y, ← (regKin sys (gF L) p₀).inner_stateMap_h2_self,
    stateMap_cubeLift', FSSrc1.h2_cubeLift sys p₀ y, inner_emb_emb]

omit [Fintype ν] in
lemma bdatum_symm (x y : En eta n) :
    ⟪FSSrc1.bdatum sys L p₀ x, y⟫_ℂ = ⟪x, FSSrc1.bdatum sys L p₀ y⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [FSSrc1.bdatum_apply, Pi.star_apply, RCLike.star_def, map_mul, Complex.conj_ofReal]
  ring

omit [Fintype ν] in
lemma kin_bdatum_comm (y : En eta n) :
    ⟪FSSpectral.kin (sb eta n) (Asym sys L n) y, FSSrc1.bdatum sys L p₀ y⟫_ℂ =
      ⟪FSSrc1.bdatum sys L p₀ y, FSSpectral.kin (sb eta n) (Asym sys L n) y⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [FSSrc1.bdatum_apply, kin_apply' sys, Pi.star_apply, RCLike.star_def, map_mul,
    Complex.conj_ofReal]
  ring

include hKernel in
/-- **`i[P W P, A_{p₀}] = P i[W, A_{p₀}] P`** on cube states: the Galerkin force form is the force
form of the cube lift. -/
lemma Gf_cubeLift (y : En eta n) :
    Gf sys L H p₀ (cubeLift (gF L) n y) (cubeLift (gF L) n y) =
      Complex.I * ⟪finiteCoulombPotential sys (coulombCellAmplitude L) n y, FSSrc1.bdatum sys L p₀ y⟫_ℂ -
        Complex.I * ⟪FSSrc1.bdatum sys L p₀ y, finiteCoulombPotential sys (coulombCellAmplitude L) n y⟫_ℂ := by
  unfold Gf
  rw [Ap, FSSrc1.h2_cubeLift sys p₀ y, ← inner_ext, ext_W_cubeLift sys H hKernel y,
    ← inner_ext', ext_W_cubeLift sys H hKernel y]

include hKernel in
/-- **eq:flux-id** (Galerkin evolution): `d/dt ⟨ψ_N(t), A_{p₀} ψ_N(t)⟩ = ⟨ψ_N, i[P W P, A_{p₀}] ψ_N⟩`,
the force form of the cube lift of `ψ_N(t) = e^{-iH_N t} v₀`. -/
theorem flux_id_galerkin (v₀ : En eta n) (t : ℝ) :
    HasDerivAt (fun s => (regKin sys (gF L) p₀).expect
        (emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-s) v₀)))
      (Gf sys L H p₀ (cubeLift (gF L) n (retFlow sys L n (zero_isSymmetric (n := n)) (-t) v₀))
        (cubeLift (gF L) n (retFlow sys L n (zero_isSymmetric (n := n)) (-t) v₀))).re t := by
  set y : ℝ → En eta n := fun s => retFlow sys L n (zero_isSymmetric (n := n)) (-s) v₀
  set Bl : En eta n →ₗ[ℂ] En eta n := cfgMul (fun p => (Aproj sys L p₀ p : ℂ))
  have hBl : ∀ v, FSSrc1.bdatum sys L p₀ v = Bl v := fun v => rfl
  set HN := finiteCoulombHamiltonian sys L n
  have hy : ∀ s, HasDerivAt y (-(Complex.I • HN (y s))) s := by
    intro s
    have h1 := hasDerivAt_retFlow sys L n (zero_isSymmetric (n := n)) (-s) v₀
    have h3 := h1.scomp s (hasDerivAt_id' s).neg
    have e : (-1 : ℝ) • (Complex.I • Hret sys L n 0 (retFlow sys L n (zero_isSymmetric (n := n)) (-s) v₀)) =
        -(Complex.I • HN (y s)) := by
      simp only [Hret, add_zero, neg_one_smul, y, HN]
    rw [e] at h3
    exact h3
  -- the energy as a real part of a smooth inner product
  have hE : ∀ s, (regKin sys (gF L) p₀).expect (emb eta n (y s)) = (⟪y s, Bl (y s)⟫_ℂ).re := by
    intro s
    have := congrArg Complex.re (expect_emb sys p₀ (L := L) (y s))
    rwa [Complex.ofReal_re] at this
  have hB : ∀ s, HasDerivAt (fun s => Bl (y s)) (Bl (-(Complex.I • HN (y s)))) s := fun s =>
    ((LinearMap.toContinuousLinearMap Bl).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s (hy s)
  have hin : HasDerivAt (fun s => ⟪y s, Bl (y s)⟫_ℂ)
      (⟪y t, Bl (-(Complex.I • HN (y t)))⟫_ℂ + ⟪-(Complex.I • HN (y t)), Bl (y t)⟫_ℂ) t :=
    (hy t).inner ℂ (hB t)
  have hre := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hin)
  have hfun : (fun s => (regKin sys (gF L) p₀).expect (emb eta n (y s))) =
      fun s => Complex.reCLM ⟪y s, Bl (y s)⟫_ℂ := by
    funext s; rw [hE s]; rfl
  change HasDerivAt (fun s => (regKin sys (gF L) p₀).expect (emb eta n (y s))) _ t
  rw [hfun]
  -- the value: the kinetic part cancels
  have hval : ⟪y t, Bl (-(Complex.I • HN (y t)))⟫_ℂ + ⟪-(Complex.I • HN (y t)), Bl (y t)⟫_ℂ =
      Gf sys L H p₀ (cubeLift (gF L) n (y t)) (cubeLift (gF L) n (y t)) := by
    rw [Gf_cubeLift sys H hKernel p₀ (y t), map_neg, map_smul, inner_neg_right, inner_smul_right,
      inner_neg_left, inner_smul_left, Complex.conj_I, ← hBl, ← hBl,
      ← bdatum_symm sys p₀ (y t) (HN (y t))]
    have hsplit := HN_eq_kin_add sys L n (y t)
    have hkc := kin_bdatum_comm sys p₀ (L := L) (y t)
    simp only [HN] at *
    rw [hsplit, inner_add_left, inner_add_right, hkc]
    ring
  rw [← hval]
  exact hre

end Galerkin

/-! ## The uniform `thm:flux` -/

section Uniform

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta)

include hKernel hL in
/-- **`thm:flux`**: there is `C` such that for every datum `D`, every time `s` and every cutoff
`n ≥ 2` with `K = g n ≥ 2`, the exact state `w_s` (`ψ(s) = S w_s`), `δ = (1-P) w_s`, satisfies
eq:flux-nc `|𝔊(δ, δ)| + 2 |𝔊(δ, 1_{>K/2} P w_s)| ≤ C Ξ² K^{-2}` and
eq:flux-bd `|𝔊(w_s, w_s) - 𝔊(P w_s, P w_s)| ≤ C Ξ² K^{-1}`. -/
theorem thm_flux (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → 2 ≤ Kc L n → ∀ (D : EvoData L H) (s : ℝ),
      ‖Gf sys L H p₀ (traj H D s - molecularH2Truncate n (traj H D s))
            (traj H D s - molecularH2Truncate n (traj H D s))‖ +
          2 * ‖Gf sys L H p₀ (traj H D s - molecularH2Truncate n (traj H D s))
            (hotA L n (traj H D s))‖ ≤ C * D.Xi ^ 2 * Kc L n ^ (-(2 : ℝ)) ∧
        |(Gf sys L H p₀ (traj H D s) (traj H D s)).re -
            (Gf sys L H p₀ (molecularH2Truncate n (traj H D s))
              (molecularH2Truncate n (traj H D s))).re| ≤ C * D.Xi ^ 2 * Kc L n ^ (-(1 : ℝ)) := by
  have hc := cTr_nonneg sys hL Hunit
  refine ⟨(|ncC sys L Hunit| + |bdC sys L Hunit|) * cTr sys L Hunit ^ 2, by positivity, ?_⟩
  intro n hn hK D s
  rw [Kc_eq] at hK ⊢
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D s
  have hw : traj H D s = w := traj_eq H D s w hw1
  rw [hw]
  have hΞ := D.Xi_nonneg
  have hK0 : 0 < gF L * n := by linarith
  have e : (cTr sys L Hunit * D.Xi) ^ 2 = cTr sys L Hunit ^ 2 * D.Xi ^ 2 := by ring
  have hnc := flux_nc sys hL H hKernel p₀ Hunit hPeriodic hK hF
  have hbd := flux_bd sys hL H hKernel p₀ Hunit hPeriodic hn hK hF
  rw [e] at hnc hbd
  have hp2 := Real.rpow_nonneg hK0.le (-(2 : ℝ))
  have hp1 := Real.rpow_nonneg hK0.le (-(1 : ℝ))
  have hX : 0 ≤ cTr sys L Hunit ^ 2 * D.Xi ^ 2 := by positivity
  constructor
  · refine hnc.trans ?_
    have h1 : ncC sys L Hunit ≤ |ncC sys L Hunit| + |bdC sys L Hunit| := by
      have := le_abs_self (ncC sys L Hunit); have := abs_nonneg (bdC sys L Hunit); linarith
    calc ncC sys L Hunit * (cTr sys L Hunit ^ 2 * D.Xi ^ 2) * (gF L * n) ^ (-(2 : ℝ))
        ≤ (|ncC sys L Hunit| + |bdC sys L Hunit|) * (cTr sys L Hunit ^ 2 * D.Xi ^ 2) *
            (gF L * n) ^ (-(2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hX) hp2
      _ = _ := by ring
  · refine hbd.trans ?_
    have h1 : bdC sys L Hunit ≤ |ncC sys L Hunit| + |bdC sys L Hunit| := by
      have := le_abs_self (bdC sys L Hunit); have := abs_nonneg (ncC sys L Hunit); linarith
    calc bdC sys L Hunit * (cTr sys L Hunit ^ 2 * D.Xi ^ 2) * (gF L * n) ^ (-(1 : ℝ))
        ≤ (|ncC sys L Hunit| + |bdC sys L Hunit|) * (cTr sys L Hunit ^ 2 * D.Xi ^ 2) *
            (gF L * n) ^ (-(1 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hX) hp1
      _ = _ := by ring

end Uniform

end FSFlux
