import PlaneWave.Observable.SecondOrder

/-!
# Flux route, stage 2, part 1: the big box

All operators of the second and third elimination rounds are finite matrices on a big cube
`B = E_N` (`N ≥ n`, `g N ≥ K⁶`), the state being the extraction `u_s = ext_N ψ(s)`.

* the box operators `W_N`, `A_N`, `T_N`, `P_n` and the force `G_N = i[W_N, A_N]`;
* `Gf_cubeLift₂`: the force form of two box lifts is `⟨y, G_N y'⟩`;
* **`flux_box`**: the projection flux `𝔊(w, w) - 𝔊(P w, P w)` equals `⟨u, X_N u⟩`,
  `X_N = G_N - P_n G_N P_n`, up to `4√3 η C_m M² (g N)^{-1/2}` for a good `w`;
* **`elim_box`**: for every symmetric `Y` on the box, along the exact evolution,
  `∫₀ᵗ ⟨u, i[T_N, Y] u⟩ = [⟨u, Y u⟩]₀ᵗ - ∫₀ᵗ ⟨u, i[W_N, Y] u⟩ - ∫₀ᵗ e_Y`, with
  `|e_Y(s)| ≤ 2 ‖W (1 - P_N) w_s‖ ‖Y u_s‖` (`norm_eY_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Box operators -/

section Box

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N : ℕ)

/-- The potential on the box. -/
noncomputable abbrev WN : En eta N →ₗ[ℂ] En eta N := finiteCoulombPotential sys (coulombCellAmplitude L) N

/-- `A_{p₀}` on the box. -/
noncomputable abbrev AN : En eta N →ₗ[ℂ] En eta N := FSKernel.dg fun q => (Aproj sys L p₀ q : ℂ)

/-- The kinetic energy on the box. -/
noncomputable abbrev TN : En eta N →ₗ[ℂ] En eta N := FSKernel.dg fun q => (Asym sys L N q : ℂ)

/-- The Galerkin cube `P_n` inside the box. -/
noncomputable abbrev PN (n : ℕ) : En eta N →ₗ[ℂ] En eta N :=
  FSKernel.res fun q : Cfg eta N => InP (n : ℝ) (cidx N q)

/-- The force on the box, `G_N = i[W_N, A_N]`. -/
noncomputable def GN : En eta N →ₗ[ℂ] En eta N :=
  Complex.I • (WN sys L N ∘ₗ AN sys L p₀ N - AN sys L p₀ N ∘ₗ WN sys L N)

/-- The projection flux on the box, `X_N = G_N - P_n G_N P_n`. -/
noncomputable def XN (n : ℕ) : En eta N →ₗ[ℂ] En eta N :=
  GN sys L p₀ N - PN N n ∘ₗ GN sys L p₀ N ∘ₗ PN N n

variable {sys L p₀ N}

lemma WN_symm : (WN sys L N).IsSymmetric := finiteCoulombPotential_isSymmetric sys _ N

omit [Fintype ν] in
lemma dg_real_symm (d : Cfg eta N → ℝ) : (FSKernel.dg fun q => (d q : ℂ)).IsSymmetric := by
  intro u v
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [FSKernel.dg_apply, Pi.star_apply, RCLike.star_def, map_mul, Complex.conj_ofReal]
  ring

omit [Fintype ν] in
lemma AN_symm : (AN sys L p₀ N).IsSymmetric := dg_real_symm _

omit [Fintype ν] in
lemma TN_symm : (TN sys L N).IsSymmetric := dg_real_symm _

omit [Fintype ν] in
lemma PN_symm (n : ℕ) : (PN N n : En eta N →ₗ[ℂ] En eta N).IsSymmetric := by
  classical
  intro u v
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [FSKernel.res_apply, Pi.star_apply, RCLike.star_def]
  split_ifs <;> simp

omit [Fintype ν] in
lemma bdatum_eq_AN (y : En eta N) : FSSrc1.bdatum sys L p₀ y = AN sys L p₀ N y := by
  ext q
  rw [FSSrc1.bdatum_apply, FSKernel.dg_apply]

/-- `⟨y, G_N y'⟩ = i ⟨W_N y, A_N y'⟩ - i ⟨A_N y, W_N y'⟩`. -/
lemma inner_GN (y y' : En eta N) :
    ⟪y, GN sys L p₀ N y'⟫_ℂ =
      Complex.I * ⟪WN sys L N y, AN sys L p₀ N y'⟫_ℂ -
        Complex.I * ⟪AN sys L p₀ N y, WN sys L N y'⟫_ℂ := by
  unfold GN
  rw [LinearMap.smul_apply, inner_smul_right, LinearMap.sub_apply, inner_sub_right,
    LinearMap.comp_apply, LinearMap.comp_apply, ← WN_symm y (AN sys L p₀ N y'),
    ← AN_symm y (WN sys L N y')]
  ring

/-- `G_N` is symmetric. -/
lemma GN_symm : (GN sys L p₀ N).IsSymmetric := by
  intro y y'
  rw [inner_GN, ← inner_conj_symm, inner_GN]
  simp only [map_sub, map_mul, Complex.conj_I, inner_conj_symm]
  ring

lemma XN_symm (n : ℕ) : (XN sys L p₀ N n).IsSymmetric := by
  intro y y'
  unfold XN
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_left, inner_sub_right]
  rw [GN_symm y y', PN_symm n (GN sys L p₀ N (PN N n y)) y', GN_symm (PN N n y) (PN N n y'),
    PN_symm n y (GN sys L p₀ N (PN N n y'))]

end Box

/-! ## The force form on box lifts -/

section Lift

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta) {N : ℕ}

include hKernel in
/-- **The force form of two box lifts**: `𝔊(lift y, lift y') = ⟨y, G_N y'⟩`. -/
lemma Gf_cubeLift₂ (y y' : En eta N) :
    Gf sys L H p₀ (cubeLift (gF L) N y) (cubeLift (gF L) N y') = ⟪y, GN sys L p₀ N y'⟫_ℂ := by
  unfold Gf
  rw [Ap, FSSrc1.h2_cubeLift sys p₀ y', FSSrc1.h2_cubeLift sys p₀ y, ← inner_ext, ← inner_ext',
    ext_W_cubeLift sys H hKernel y, ext_W_cubeLift sys H hKernel y', bdatum_eq_AN, bdatum_eq_AN,
    inner_GN]

omit [Fintype ν] in
/-- `P_n` of the embedding of a box vector is the embedding of `P_n` (`n ≤ N`). -/
lemma trunc_emb {n : ℕ} (hnN : n ≤ N) (v : En eta N) :
    molecularH2Truncate n (emb eta N v) = emb eta N (PN N n v) := by
  classical
  ext q
  rw [molecularH2Truncate_apply]
  by_cases hq : q ∈ fourierConfigCube eta n
  · rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hq]
    have hqN : q ∈ fourierConfigCube eta N := by
      have h1 := (inP_iff_mem_cube n q).mpr hq
      refine (inP_iff_mem_cube N q).mp fun c i => (h1 c i).trans ?_
      exact_mod_cast hnN
    unfold fourierConfigCube at hqN
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hqN
    rw [emb_apply_index, emb_apply_index, FSKernel.res_apply,
      if_pos ((inP_iff_mem_cube n _).mpr hq)]
  · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq]
    refine (emb_apply_eq_zero N _ fun p hp => ?_).symm
    rw [FSKernel.res_apply, if_neg]
    intro h; apply hq; rw [← hp]; exact (inP_iff_mem_cube n _).mp h

omit [Fintype ν] in
/-- `P_n w = lift (P_n u)` with `u = ext_N (S w)`, for `n ≤ N`. -/
lemma trunc_eq_lift_PN {n : ℕ} (hnN : n ≤ N) (w : MolecularFourierH2 eta) :
    molecularH2Truncate n w = cubeLift (gF L) N (PN N n (ext eta N (Sm eta L w))) := by
  apply molecularH2StateMap_injective eta (gF L)
  change Sm eta L (molecularH2Truncate n w) =
    Sm eta L (cubeLift (gF L) N (PN N n (ext eta N (Sm eta L w))))
  rw [stateMap_cubeLift', ← trunc_emb hnN, emb_ext, Sm, stateMap_truncate,
    truncate_truncate_of_le hnN]
where
  truncate_truncate_of_le {n N : ℕ} (h : n ≤ N) (x : L2 eta) :
      molecularH2Truncate n x = molecularH2Truncate n (molecularH2Truncate N x) := by
    classical
    ext q
    rw [molecularH2Truncate_apply, molecularH2Truncate_apply]
    by_cases hq : q ∈ fourierConfigCube eta n
    · have hqN : q ∈ fourierConfigCube eta N := by
        have h1 := (inP_iff_mem_cube n q).mpr hq
        refine (inP_iff_mem_cube N q).mp fun c i => (h1 c i).trans ?_
        exact_mod_cast h
      rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hq, cubicLatticeCoeffTruncate_eq_of_mem n _ q hq,
        molecularH2Truncate_apply, cubicLatticeCoeffTruncate_eq_of_mem N _ q hqN]
    · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq,
        cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq]

omit [Fintype ν] in
/-- Truncation does not increase the `ℓ²` norm. -/
lemma norm_trunc_le (n : ℕ) (x : L2 eta) : ‖molecularH2Truncate n x‖ ≤ ‖x‖ := by
  classical
  have := l2_norm_le_of_le (molecularH2Truncate n x) x zero_le_one fun p => by
    rw [molecularH2Truncate_apply, one_mul]
    by_cases hp : p ∈ fourierConfigCube eta n
    · rw [cubicLatticeCoeffTruncate_eq_of_mem n _ p hp]
    · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ p hp, norm_zero]; exact norm_nonneg _
  rwa [one_mul] at this

end Lift

/-! ## The flux on the box -/

section FluxBox

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta)

/-- The constant of `flux_box`: `4 √3 η C_m`. -/
noncomputable def CB (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  4 * Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit

include hKernel hL in
/-- `‖W w‖ ≤ √3 C_m M` for a good `w`. -/
lemma norm_W_fgood (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {M : ℝ}
    {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    ‖Wp sys L H w‖ ≤ Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * M := by
  have hM := hF.nonneg
  have h1 : ‖Sm eta L w‖ ≤ M := by linarith [hF.1, norm_nonneg (coulombFourierKineticH2 sys (gF L) w)]
  have h2 : ‖coulombFourierKineticH2 sys (gF L) w‖ ≤ M := by linarith [hF.1, norm_nonneg (Sm eta L w)]
  have h := norm_W_le_of sys hL H hKernel Hunit hPeriodic w h1 h2 le_rfl
  have e : Real.sqrt (3 * M * M) = Real.sqrt 3 * M := by
    rw [mul_assoc, Real.sqrt_mul (by norm_num), Real.sqrt_mul_self hM]
  rw [e] at h
  linarith

include hKernel hL in
/-- **The projection flux on the box**: for a good `w`, `n ≤ N` and `g N ≥ 1`, with
`u = ext_N (S w)`, `|𝔊(w, w) - 𝔊(P_n w, P_n w) - ⟨u, X_N u⟩| ≤ 4√3 η C_m M² (g N)^{-1/2}`. -/
theorem flux_box (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {n N : ℕ} (hnN : n ≤ N) (hN : 1 ≤ gF L * N) {M : ℝ} {w : MolecularFourierH2 eta}
    (hF : FGood sys L M w) :
    |(Gf sys L H p₀ w w).re - (Gf sys L H p₀ (molecularH2Truncate n w) (molecularH2Truncate n w)).re -
        (⟪ext eta N (Sm eta L w), XN sys L p₀ N n (ext eta N (Sm eta L w))⟫_ℂ).re| ≤
      CB sys L Hunit * M ^ 2 * (gF L * N) ^ (-(1 / 2 : ℝ)) := by
  set u := ext eta N (Sm eta L w)
  set wN := molecularH2Truncate N w
  set d := w - wN
  have hM := hF.nonneg
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  set Cm := finiteCoulombPhysicalMassConstant sys L Hunit
  set x := (gF L * N) ^ (-(1 / 2 : ℝ))
  have hK0 : 0 < gF L * N := by linarith
  have hx0 : 0 ≤ x := Real.rpow_nonneg hK0.le _
  -- the lifts
  have hwN : wN = cubeLift (gF L) N u := FSSrc1.trunc_eq_cubeLift w
  have hPw : molecularH2Truncate n w = cubeLift (gF L) N (PN N n u) := trunc_eq_lift_PN hnN w
  have hsplit : w = wN + d := by simp only [d]; abel
  -- the main term
  have hmain : Gf sys L H p₀ wN wN - Gf sys L H p₀ (molecularH2Truncate n w) (molecularH2Truncate n w) =
      ⟪u, XN sys L p₀ N n u⟫_ℂ := by
    rw [hwN, hPw, Gf_cubeLift₂ sys H hKernel p₀, Gf_cubeLift₂ sys H hKernel p₀]
    unfold XN
    rw [LinearMap.sub_apply, inner_sub_right, LinearMap.comp_apply, LinearMap.comp_apply, PN_symm]
  -- the remainder
  have hrem : Gf sys L H p₀ w w = Gf sys L H p₀ wN wN + Gf sys L H p₀ wN d + Gf sys L H p₀ d w := by
    conv_lhs => rw [hsplit]
    rw [Gf_add_left, Gf_add_right, ← hsplit]
  -- norms
  have hSw : ‖Sm eta L w‖ ≤ M := by linarith [hF.1, norm_nonneg (coulombFourierKineticH2 sys (gF L) w)]
  have hTw : ‖coulombFourierKineticH2 sys (gF L) w‖ ≤ M := by linarith [hF.1, norm_nonneg (Sm eta L w)]
  have hTd : ‖coulombFourierKineticH2 sys (gF L) d‖ ≤ eta * M * x := by
    simp only [d, wN, map_sub, kinetic_truncate]
    refine (PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) N _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * N) a (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ ∑ _a : Fin eta, M * x := Finset.sum_le_sum fun a _ => (hF.2 a _ hN).2
      _ = eta * M * x := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hAd : ‖Ap sys L p₀ d‖ ≤ eta * M * x := (norm_Ap_le sys L p₀ d).trans hTd
  have hWd : ‖Wp sys L H d‖ ≤ Real.sqrt 3 * eta * Cm * M * x := by
    have h := fgood_W (sys := sys) H hKernel Hunit hL hPeriodic hF hN
    refine h.trans ?_
    have : (gF L * N) ^ (-(3 / 2 : ℝ)) ≤ x := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    have h0 : 0 ≤ Real.sqrt 3 * eta * Cm * M := by positivity
    exact mul_le_mul_of_nonneg_left this h0
  have hTwN : ‖coulombFourierKineticH2 sys (gF L) wN‖ ≤ M := by
    simp only [wN, kinetic_truncate]; exact (norm_trunc_le N _).trans hTw
  have hSwN : ‖Sm eta L wN‖ ≤ M := by
    simp only [wN, Sm, stateMap_truncate]; exact (norm_trunc_le N _).trans hSw
  have hAwN : ‖Ap sys L p₀ wN‖ ≤ M := (norm_Ap_le sys L p₀ wN).trans hTwN
  have hAw : ‖Ap sys L p₀ w‖ ≤ M := (norm_Ap_le sys L p₀ w).trans hTw
  have hWw : ‖Wp sys L H w‖ ≤ Real.sqrt 3 * Cm * M := norm_W_fgood sys hL H hKernel Hunit hPeriodic hF
  have hWwN : ‖Wp sys L H wN‖ ≤ Real.sqrt 3 * Cm * M := by
    have h := norm_W_le_of sys hL H hKernel Hunit hPeriodic wN hSwN hTwN le_rfl
    have e : Real.sqrt (3 * M * M) = Real.sqrt 3 * M := by
      rw [mul_assoc, Real.sqrt_mul (by norm_num), Real.sqrt_mul_self hM]
    rw [e] at h; linarith
  have h1 := norm_Gf_le sys L H p₀ wN d
  have h2 := norm_Gf_le sys L H p₀ d w
  have hs3 := Real.sqrt_nonneg 3
  have hE : ‖Gf sys L H p₀ wN d‖ + ‖Gf sys L H p₀ d w‖ ≤ CB sys L Hunit * M ^ 2 * x := by
    have a1 : ‖Wp sys L H wN‖ * ‖Ap sys L p₀ d‖ ≤ Real.sqrt 3 * Cm * M * (eta * M * x) :=
      mul_le_mul hWwN hAd (norm_nonneg _) (by positivity)
    have a2 : ‖Ap sys L p₀ wN‖ * ‖Wp sys L H d‖ ≤ M * (Real.sqrt 3 * eta * Cm * M * x) :=
      mul_le_mul hAwN hWd (norm_nonneg _) hM
    have a3 : ‖Wp sys L H d‖ * ‖Ap sys L p₀ w‖ ≤ Real.sqrt 3 * eta * Cm * M * x * M :=
      mul_le_mul hWd hAw (norm_nonneg _) (by positivity)
    have a4 : ‖Ap sys L p₀ d‖ * ‖Wp sys L H w‖ ≤ eta * M * x * (Real.sqrt 3 * Cm * M) :=
      mul_le_mul hAd hWw (norm_nonneg _) (by positivity)
    unfold CB
    nlinarith
  -- conclude
  have hre : (Gf sys L H p₀ w w).re - (Gf sys L H p₀ (molecularH2Truncate n w)
      (molecularH2Truncate n w)).re - (⟪u, XN sys L p₀ N n u⟫_ℂ).re =
      (Gf sys L H p₀ wN d + Gf sys L H p₀ d w).re := by
    rw [← hmain, hrem]
    simp only [Complex.add_re, Complex.sub_re]
    ring
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans hE)

end FluxBox

/-! ## The elimination identity on the box -/

section ElimBox

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  {N : ℕ}

omit [Fintype ν] in
/-- `ext_N (T w) = T_N (ext_N (S w))`. -/
lemma ext_kin (w : MolecularFourierH2 eta) :
    ext eta N (coulombFourierKineticH2 sys (gF L) w) = TN sys L N (ext eta N (Sm eta L w)) := by
  ext q
  rw [extractCLM_apply, FSKernel.dg_apply, extractCLM_apply, coulombFourierKineticH2_apply,
    Sm, molecularH2StateMap_apply, Asym_eq_Ek, Ek, E_eq_kineticSymbol]

omit [Fintype ν] in
/-- The box state along the trajectory. -/
noncomputable abbrev ub (D : EvoData L H) (N : ℕ) (s : ℝ) : En eta N := ext eta N (D.U s (Sm eta L D.u₀))

omit [Fintype ν] in
lemma ub_eq (D : EvoData L H) (s : ℝ) : ub H D N s = ext eta N (Sm eta L (traj H D s)) := by
  rw [ub, traj_S]

/-- The out-of-box error of an elimination: `e_Y = -2 Im ⟨ext (W (1 - P_N) w), Y u⟩`. -/
noncomputable def eY (D : EvoData L H) (Y : En eta N →ₗ[ℂ] En eta N) (s : ℝ) : ℝ :=
  (Complex.I * ⟪ext eta N (Wp sys L H (traj H D s - molecularH2Truncate N (traj H D s))),
      Y (ub H D N s)⟫_ℂ -
    Complex.I * ⟪Y (ub H D N s),
      ext eta N (Wp sys L H (traj H D s - molecularH2Truncate N (traj H D s)))⟫_ℂ).re

omit [Fintype ν] in
lemma norm_ext_le' (x : L2 eta) : ‖ext eta N x‖ ≤ ‖x‖ := norm_ext_le (n := N) x

omit [Fintype ν] in
/-- `|e_Y| ≤ 2 ‖W (1 - P_N) w‖ ‖Y u‖`. -/
lemma norm_eY_le (D : EvoData L H) (Y : En eta N →ₗ[ℂ] En eta N) (s : ℝ) :
    |eY sys H D Y s| ≤
      2 * ‖Wp sys L H (traj H D s - molecularH2Truncate N (traj H D s))‖ * ‖Y (ub H D N s)‖ := by
  unfold eY
  set e := ext eta N (Wp sys L H (traj H D s - molecularH2Truncate N (traj H D s)))
  set y := Y (ub H D N s)
  have he : ‖e‖ ≤ ‖Wp sys L H (traj H D s - molecularH2Truncate N (traj H D s))‖ := norm_ext_le' _
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) e y
  have h2 := norm_inner_le_norm (𝕜 := ℂ) y e
  have := norm_nonneg y
  nlinarith

include hKernel in
/-- The derivative of `⟨u, Y u⟩` along the exact evolution. -/
theorem deriv_box (D : EvoData L H) (Y : En eta N →ₗ[ℂ] En eta N) (hY : Y.IsSymmetric) (t : ℝ) :
    HasDerivAt (fun s => ⟪ub H D N s, Y (ub H D N s)⟫_ℂ)
      (⟪ub H D N t, (Complex.I • (TN sys L N ∘ₗ Y - Y ∘ₗ TN sys L N)) (ub H D N t)⟫_ℂ +
        ⟪ub H D N t, (Complex.I • (WN sys L N ∘ₗ Y - Y ∘ₗ WN sys L N)) (ub H D N t)⟫_ℂ +
        (Complex.I * ⟪ext eta N (Wp sys L H (traj H D t - molecularH2Truncate N (traj H D t))),
            Y (ub H D N t)⟫_ℂ -
          Complex.I * ⟪Y (ub H D N t),
            ext eta N (Wp sys L H (traj H D t - molecularH2Truncate N (traj H D t)))⟫_ℂ)) t := by
  set Yc : En eta N →L[ℂ] En eta N := LinearMap.toContinuousLinearMap Y
  set Z : L2 eta →L[ℂ] L2 eta := emb eta N ∘L Yc ∘L ext eta N
  have hZ : ContinuousLinearMap.adjoint Z = Z := by
    ext1 x
    refine ext_inner_left ℂ fun z => ?_
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [Z, ContinuousLinearMap.comp_apply]
    rw [← inner_ext', ← inner_ext]
    simp only [Yc, LinearMap.coe_toContinuousLinearMap']
    exact hY _ _
  have h := deriv_expect_herm H D Z hZ t
  have hfun : (fun s => ⟪D.U s (Sm eta L D.u₀), Z (D.U s (Sm eta L D.u₀))⟫_ℂ) =
      fun s => ⟪ub H D N s, Y (ub H D N s)⟫_ℂ := by
    funext s
    simp only [Z, ContinuousLinearMap.comp_apply]
    rw [← inner_ext]
    rfl
  rw [hfun] at h
  refine h.congr_deriv ?_
  -- the value
  set w := traj H D t
  set u := ub H D N t
  have hu : u = ext eta N (Sm eta L w) := ub_eq H D t
  have hHw : D.U t (H D.u₀) = coulombFourierKineticH2 sys (gF L) w + Wp sys L H w := by
    rw [← traj_H]; exact coulombFourierHamiltonianH2_decomposition sys (gF L) H w
  have hWsplit : ext eta N (Wp sys L H w) =
      WN sys L N u + ext eta N (Wp sys L H (w - molecularH2Truncate N w)) := by
    rw [map_sub, map_sub, FSSrc1.trunc_eq_cubeLift (n := N) w, ext_W_cubeLift sys H hKernel, ← hu]
    abel
  have hext : ext eta N (D.U t (H D.u₀)) =
      TN sys L N u + WN sys L N u + ext eta N (Wp sys L H (w - molecularH2Truncate N w)) := by
    rw [hHw, map_add, ext_kin, hWsplit, ← hu]
    abel
  have e1 : ⟪D.U t (H D.u₀), Z (D.U t (Sm eta L D.u₀))⟫_ℂ = ⟪ext eta N (D.U t (H D.u₀)), Y u⟫_ℂ := by
    simp only [Z, ContinuousLinearMap.comp_apply]
    rw [← inner_ext]; rfl
  have e2 : ⟪Z (D.U t (Sm eta L D.u₀)), D.U t (H D.u₀)⟫_ℂ = ⟪Y u, ext eta N (D.U t (H D.u₀))⟫_ℂ := by
    simp only [Z, ContinuousLinearMap.comp_apply]
    rw [← inner_ext']; rfl
  rw [e1, e2, hext]
  set e := ext eta N (Wp sys L H (w - molecularH2Truncate N w))
  have hT : ⟪u, (Complex.I • (TN sys L N ∘ₗ Y - Y ∘ₗ TN sys L N)) u⟫_ℂ =
      Complex.I * ⟪TN sys L N u, Y u⟫_ℂ - Complex.I * ⟪Y u, TN sys L N u⟫_ℂ := by
    rw [LinearMap.smul_apply, inner_smul_right, LinearMap.sub_apply, inner_sub_right,
      LinearMap.comp_apply, LinearMap.comp_apply, ← TN_symm, ← hY u (TN sys L N u)]
    ring
  have hW : ⟪u, (Complex.I • (WN sys L N ∘ₗ Y - Y ∘ₗ WN sys L N)) u⟫_ℂ =
      Complex.I * ⟪WN sys L N u, Y u⟫_ℂ - Complex.I * ⟪Y u, WN sys L N u⟫_ℂ := by
    rw [LinearMap.smul_apply, inner_smul_right, LinearMap.sub_apply, inner_sub_right,
      LinearMap.comp_apply, LinearMap.comp_apply, ← WN_symm, ← hY u (WN sys L N u)]
    ring
  rw [hT, hW, inner_add_left, inner_add_left, inner_add_right, inner_add_right]
  ring

include hKernel hL in
/-- **The elimination identity on the box**: for every symmetric `Y` on `E_N`,
`∫₀ᵗ ⟨u, i[T_N, Y] u⟩ = ⟨u_t, Y u_t⟩ - ⟨u_0, Y u_0⟩ - ∫₀ᵗ ⟨u, i[W_N, Y] u⟩ - ∫₀ᵗ e_Y`
(real parts). -/
theorem elim_box (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (Y : En eta N →ₗ[ℂ] En eta N) (hY : Y.IsSymmetric) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, (⟪ub H D N s, (Complex.I • (TN sys L N ∘ₗ Y - Y ∘ₗ TN sys L N))
        (ub H D N s)⟫_ℂ).re =
      (⟪ub H D N t, Y (ub H D N t)⟫_ℂ).re - (⟪ub H D N 0, Y (ub H D N 0)⟫_ℂ).re -
        (∫ s in (0 : ℝ)..t, (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y - Y ∘ₗ WN sys L N))
          (ub H D N s)⟫_ℂ).re) -
        ∫ s in (0 : ℝ)..t, eY sys H D Y s := by
  -- continuity
  have hcu : Continuous fun s => ub H D N s := (ext eta N).continuous.comp (D.cont _)
  have hcY : Continuous fun s => Y (ub H D N s) :=
    (LinearMap.toContinuousLinearMap Y).continuous.comp hcu
  have hct := continuous_traj sys hL H hKernel Hunit hPeriodic D
  have hce : Continuous fun s =>
      ext eta N (Wp sys L H (traj H D s - molecularH2Truncate N (traj H D s))) :=
    (ext eta N).continuous.comp ((Wp sys L H).continuous.comp (hct.sub ((continuous_trunc N).comp hct)))
  have hcop : ∀ Op : En eta N →ₗ[ℂ] En eta N,
      Continuous fun s => (⟪ub H D N s, Op (ub H D N s)⟫_ℂ).re := fun Op =>
    Complex.continuous_re.comp (hcu.inner ((LinearMap.toContinuousLinearMap Op).continuous.comp hcu))
  have hcT := hcop (Complex.I • (TN sys L N ∘ₗ Y - Y ∘ₗ TN sys L N))
  have hcW := hcop (Complex.I • (WN sys L N ∘ₗ Y - Y ∘ₗ WN sys L N))
  have hcTW : Continuous fun s =>
      (⟪ub H D N s, (Complex.I • (TN sys L N ∘ₗ Y - Y ∘ₗ TN sys L N)) (ub H D N s)⟫_ℂ).re +
        (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y - Y ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re :=
    hcT.add hcW
  have hcE : Continuous fun s => eY sys H D Y s := by
    unfold eY
    exact Complex.continuous_re.comp ((continuous_const.mul (hce.inner hcY)).sub
      (continuous_const.mul (hcY.inner hce)))
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (fun s => (⟪ub H D N s, Y (ub H D N s)⟫_ℂ).re)
      ((⟪ub H D N s, (Complex.I • (TN sys L N ∘ₗ Y - Y ∘ₗ TN sys L N)) (ub H D N s)⟫_ℂ).re +
        (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y - Y ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re +
        eY sys H D Y s) s := by
    intro s _
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s (deriv_box sys H hKernel D Y hY s)
    simp only [Function.comp_def, Complex.reCLM_apply, Complex.add_re] at h
    exact h
  have hint : IntervalIntegrable (fun s =>
      (⟪ub H D N s, (Complex.I • (TN sys L N ∘ₗ Y - Y ∘ₗ TN sys L N)) (ub H D N s)⟫_ℂ).re +
        (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y - Y ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re +
        eY sys H D Y s) volume 0 t := (hcTW.add hcE).intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_add (hcTW.intervalIntegrable 0 t) (hcE.intervalIntegrable 0 t),
    intervalIntegral.integral_add (hcT.intervalIntegrable 0 t) (hcW.intervalIntegrable 0 t)] at hFTC
  have key : (∫ s in (0 : ℝ)..t, (⟪ub H D N s, (Complex.I • (TN sys L N ∘ₗ Y - Y ∘ₗ TN sys L N))
        (ub H D N s)⟫_ℂ).re) +
      (∫ s in (0 : ℝ)..t, (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y - Y ∘ₗ WN sys L N))
          (ub H D N s)⟫_ℂ).re) +
      (∫ s in (0 : ℝ)..t, eY sys H D Y s) =
      (⟪ub H D N t, Y (ub H D N t)⟫_ℂ).re - (⟪ub H D N 0, Y (ub H D N 0)⟫_ℂ).re := hFTC
  linarith

end ElimBox

end FSFlux
