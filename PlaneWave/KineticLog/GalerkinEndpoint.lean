import PlaneWave.KineticLog.Galerkin

/-!
# Logarithmic kinetic bound, part 7: the Galerkin endpoints

For the constructed periodic Coulomb Hamiltonian `H` (any `H` satisfying the release's kernel
identity `hKernel`), every propagator `EvoData` and every datum `ψ₀ ∈ D(H²)`, with
`𝒟 = Ξ = ‖ψ₀‖ + ‖H ψ₀‖ + ‖H² ψ₀‖` and `K = Kc L n = 2π n/L`:

* **`kinetic_retained_galerkin`** (`eq:kinetic-retained-galerkin`):
  `‖P ψ(t) - ψ_N(t)‖ ≤ C 𝒟 K^{-3} [1 + t + log(2 + K)]` for all `t ≥ 0`, `n ≥ N₀`;
* **`thm_kinetic_log_galerkin`** (`thm:kinetic-log`, Galerkin case, `eq:kinetic-log`):
  `|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_N(t), T_p ψ_N(t)⟩| ≤ C 𝒟² K^{-3} [1 + t + log(2 + K)]`;
* **`cor_stopping_log_galerkin`** (`cor:stopping-log`, `eq:stopping-log`, Galerkin case): for every
  window `[0, τ]`, `τ > 0`, and reference speed `v_p > 0`, the signed secants differ by at most
  `(C 𝒟²/v_p) K^{-3} [1 + (1 + log(2 + K))/τ]`;
* the finite-internal-spin versions (`*_spin`), with the spin-summed data norm `Ξ_S` and no
  factor depending on the number of spin configurations.

The constants `C` and the cutoff threshold `N₀` depend only on the fixed system, the cell and
`Hunit`; they precede the quantifiers over cutoffs, data, times and windows.  The projected
initial data are not renormalised.  The measured particle `p₀` is any quantum particle.

Proof of the kinetic bound: the projection identity `KinMult.expect_split` (no cross term,
`P T_p = T_p P`) with the exact trajectory tails (`traj_good`, `fgood_R`) costs
`η² c_tr² Ξ² K^{-3}`;
the graph-pairing identity (`expect_sub_le`, eq:kinetic-pairing) with the first graph bounds of the
exact and Galerkin trajectories and the retained comparison costs the rest.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FSNormal FSGalerkin

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The graph-pairing identity for kinetic multipliers -/

omit [Fintype ν] in
/-- **Graph pairing** (`eq:kinetic-pairing`): for `H²` states,
`|⟨S x, μ S x⟩ - ⟨S y, μ S y⟩| ≤ ‖S x - S y‖ (‖μ x‖ + ‖μ y‖)`. -/
lemma expect_sub_le {sys : CoulombSystem eta ν} {g : ℝ} (m : KinMult sys g)
    (x y : MolecularFourierH2 eta) :
    |m.expect (molecularH2StateMap eta g x) - m.expect (molecularH2StateMap eta g y)| ≤
      ‖molecularH2StateMap eta g x - molecularH2StateMap eta g y‖ * (‖m.h2 x‖ + ‖m.h2 y‖) := by
  set S := molecularH2StateMap eta g
  have hx := m.inner_stateMap_h2_self x
  have hy := m.inner_stateMap_h2_self y
  have hsym := m.inner_stateMap_h2 y (x - y)
  have e : ((m.expect (S x) - m.expect (S y) : ℝ) : ℂ) =
      ⟪S x - S y, m.h2 x⟫_ℂ + ⟪m.h2 y, S x - S y⟫_ℂ := by
    push_cast
    rw [← hx, ← hy]
    have h1 : ⟪m.h2 y, S x - S y⟫_ℂ = ⟪S y, m.h2 x - m.h2 y⟫_ℂ := by
      rw [← map_sub, ← map_sub, hsym]
    rw [h1, inner_sub_left, inner_sub_right]
    ring
  have h2 := congrArg norm e
  rw [Complex.norm_real, Real.norm_eq_abs] at h2
  rw [h2]
  refine (norm_add_le _ _).trans ?_
  rw [mul_add]
  refine add_le_add (norm_inner_le_norm _ _) ?_
  rw [mul_comm]
  exact norm_inner_le_norm _ _

/-! ## Scales -/

section Scales

variable (sys : CoulombSystem eta ν) (L Hunit : ℝ)

/-- The cutoff threshold `N₀ = max(2, ⌈√(8 m̄ (1 + c)) / g⌉)`. -/
noncomputable def nGal : ℕ :=
  max 2 ⌈Real.sqrt (8 * sys.maxMass * (1 + shiftC sys L Hunit)) / gF L⌉₊

variable {sys L Hunit}

/-- The scale conditions beyond `nGal`. -/
lemma nGal_scales (hL : 0 < L) {n : ℕ} (hn : nGal sys L Hunit ≤ n) :
    1 ≤ gF L * n ∧ 2 * gF L ≤ gF L * n ∧
      8 * sys.maxMass * (1 + shiftC sys L Hunit) ≤ (gF L * n) ^ 2 := by
  have hg := gF_pos hL
  have hm := sys.one_le_maxMass
  have hc := two_le_shiftC sys L Hunit
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
  have hceil : Real.sqrt (8 * sys.maxMass * (1 + shiftC sys L Hunit)) / gF L ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hK0 : Real.sqrt (8 * sys.maxMass * (1 + shiftC sys L Hunit)) ≤ gF L * n := by
    rw [div_le_iff₀ hg] at hceil
    linarith
  have hsq : 8 * sys.maxMass * (1 + shiftC sys L Hunit) ≤ (gF L * n) ^ 2 := by
    have h0 : 0 ≤ 8 * sys.maxMass * (1 + shiftC sys L Hunit) := by positivity
    calc 8 * sys.maxMass * (1 + shiftC sys L Hunit) =
          Real.sqrt (8 * sys.maxMass * (1 + shiftC sys L Hunit)) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ (gF L * n) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hK0 2
  refine ⟨?_, by nlinarith, hsq⟩
  have h1 : 1 ≤ Real.sqrt (8 * sys.maxMass * (1 + shiftC sys L Hunit)) :=
    Real.one_le_sqrt.mpr (by nlinarith)
  linarith

end Scales

/-! ## The retained Galerkin estimate -/

section Endpoint

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- The retained-state constant
`C_ret = 128 m̄² (1+c)² + 96 δ_G (1+c)² + 16 m̄ C_F (1+c)`. -/
noncomputable def cRet (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  128 * sys.maxMass ^ 2 * (1 + shiftC sys L Hunit) ^ 2 +
    96 * dG sys L Hunit * (1 + shiftC sys L Hunit) ^ 2 +
    16 * sys.maxMass * cF sys L Hunit * (1 + shiftC sys L Hunit)

include hL in
lemma cRet_nonneg (Hunit : ℝ) : 0 ≤ cRet sys L Hunit := by
  unfold cRet
  have := dG_nonneg sys Hunit hL
  have := cF_nonneg sys (L := L) Hunit
  have := two_le_shiftC sys L Hunit
  have := sys.one_le_maxMass
  positivity

include hL hKernel in
/-- **`eq:kinetic-retained-galerkin`**: there are `C ≥ 0` and `N₀` such that for every cutoff
`n ≥ N₀`, every datum and every `t ≥ 0`,
`‖P ψ(t) - ψ_N(t)‖ ≤ C 𝒟 [1 + t + log(2 + K)] / K³`. -/
theorem kinetic_retained_galerkin (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : EvoData L H) (t : ℝ), 0 ≤ t →
      ‖molecularH2Truncate n (D.U t (Sm eta L D.u₀)) -
          emb eta n
              (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀)))‖ ≤
        C * D.Xi * (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := by
  obtain ⟨E⟩ := exists_exactEigen sys H hKernel Hunit hL hPeriodic
  refine ⟨cRet sys L Hunit, cRet_nonneg sys hL Hunit, nGal sys L Hunit, fun n hn D t ht => ?_⟩
  obtain ⟨hK1, hK2, hK8⟩ := nGal_scales hL hn
  set K := gF L * n with hKdef
  set c := shiftC sys L Hunit with hcdef
  set m := sys.maxMass with hmdef
  have hm : 1 ≤ m := sys.one_le_maxMass
  have hc : 2 ≤ c := two_le_shiftC sys L Hunit
  have hK0 : 0 < K := by linarith
  set Λ := K ^ 2 / (8 * m) with hΛdef
  have hΛ1c : 1 + c ≤ Λ := by
    rw [hΛdef, le_div_iff₀ (by positivity)]
    linarith
  have hΛ1 : 1 ≤ Λ := by linarith
  have hΛ : Λ + c ≤ K ^ 2 / (4 * m) := by
    have e : K ^ 2 / (4 * m) = 2 * Λ := by rw [hΛdef]; field_simp; ring
    rw [e]
    linarith
  have hcore := galerkin_retained_core sys H hKernel Hunit hL hPeriodic n E rfl hK1 hK2 hΛ1 hΛ D ht
  -- the norm on `ℓ²`
  have hemb : ‖molecularH2Truncate n (D.U t (Sm eta L D.u₀)) -
      emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀)))‖ =
      ‖ext eta n (D.U t (Sm eta L D.u₀)) -
        retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀))‖ := by
    rw [← emb_ext n, ← map_sub]
    exact (finiteFourierLpIsometry eta n).norm_map _
  rw [hemb]
  refine hcore.trans ?_
  -- the bounds of the data vectors
  have hΞ := D.Xi_nonneg
  have hHs2 : ‖ExactEigen.Hs2 (c := c) D‖ ≤ (1 + c) ^ 2 * D.Xi := by
    have := ExactEigen.norm_Hs2_le (c := c) D
    rwa [abs_of_pos (by linarith)] at this
  have hHs1 : ‖Hs1 c D‖ ≤ (1 + c) * D.Xi := norm_Hs1_le (by linarith) D
  have hlog : Real.log (2 + 2 * Λ) ≤ 2 * Real.log (2 + K) := by
    have h1 : 2 + 2 * Λ ≤ (2 + K) ^ 2 := by
      have : 2 * Λ ≤ K ^ 2 := by
        rw [hΛdef, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg K]
      nlinarith
    calc Real.log (2 + 2 * Λ) ≤ Real.log ((2 + K) ^ 2) :=
          Real.log_le_log (by linarith) h1
      _ = 2 * Real.log (2 + K) := by rw [Real.log_pow]; norm_num
  have hlog0 : 0 ≤ Real.log (2 + K) := Real.log_nonneg (by linarith)
  have hK3 : 0 < K ^ 3 := by positivity
  have hdG := dG_nonneg sys Hunit hL
  have hcF := cF_nonneg sys (L := L) Hunit
  set Q := 1 + t + Real.log (2 + K) with hQ
  have hQ1 : 1 ≤ Q := by linarith
  have ht1 : t + Real.log (2 + K) ≤ Q := by linarith
  -- the three terms
  have t1 : 2 * (‖ExactEigen.Hs2 (c := c) D‖ / Λ ^ 2) ≤
      128 * m ^ 2 * (1 + c) ^ 2 * D.Xi / K ^ 3 := by
    have e : 2 / Λ ^ 2 = 128 * m ^ 2 / K ^ 4 := by
      rw [hΛdef]
      field_simp
      ring
    have hK4 : 128 * m ^ 2 / K ^ 4 ≤ 128 * m ^ 2 / K ^ 3 := by
      apply div_le_div_of_nonneg_left (by positivity) hK3
      calc K ^ 3 = K ^ 3 * 1 := by ring
        _ ≤ K ^ 3 * K := by gcongr
        _ = K ^ 4 := by ring
    calc 2 * (‖ExactEigen.Hs2 (c := c) D‖ / Λ ^ 2) = 2 / Λ ^ 2 * ‖ExactEigen.Hs2 (c := c) D‖ := by
          ring
      _ ≤ 128 * m ^ 2 / K ^ 3 * ((1 + c) ^ 2 * D.Xi) := by
          rw [e]
          exact mul_le_mul hK4 hHs2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have t2 : 48 * (dG sys L Hunit / K ^ 3) * (t + Real.log (2 + 2 * Λ)) *
      ‖ExactEigen.Hs2 (c := c) D‖ ≤
      96 * dG sys L Hunit * (1 + c) ^ 2 * D.Xi * (t + Real.log (2 + K)) / K ^ 3 := by
    have h1 : t + Real.log (2 + 2 * Λ) ≤ 2 * (t + Real.log (2 + K)) := by linarith
    have h0 : 0 ≤ t + Real.log (2 + 2 * Λ) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 2 * Λ by linarith)
      linarith
    calc 48 * (dG sys L Hunit / K ^ 3) * (t + Real.log (2 + 2 * Λ)) *
          ‖ExactEigen.Hs2 (c := c) D‖
        ≤ 48 * (dG sys L Hunit / K ^ 3) * (2 * (t + Real.log (2 + K))) *
          ((1 + c) ^ 2 * D.Xi) := by gcongr
      _ = _ := by ring
  have t3 : 2 * (cF sys L Hunit / (K * Λ)) * ‖Hs1 c D‖ ≤
      16 * m * cF sys L Hunit * (1 + c) * D.Xi / K ^ 3 := by
    have e : 2 * (cF sys L Hunit / (K * Λ)) = 16 * m * cF sys L Hunit / K ^ 3 := by
      rw [hΛdef]
      field_simp
      ring
    rw [e]
    calc 16 * m * cF sys L Hunit / K ^ 3 * ‖Hs1 c D‖ ≤
          16 * m * cF sys L Hunit / K ^ 3 * ((1 + c) * D.Xi) := by gcongr
      _ = _ := by ring
  have hKc : Kc L n = K := rfl
  rw [hKc]
  unfold cRet
  rw [← hcdef, ← hmdef]
  have hfin : 128 * m ^ 2 * (1 + c) ^ 2 * D.Xi / K ^ 3 +
      96 * dG sys L Hunit * (1 + c) ^ 2 * D.Xi * (t + Real.log (2 + K)) / K ^ 3 +
      16 * m * cF sys L Hunit * (1 + c) * D.Xi / K ^ 3 ≤
      (128 * m ^ 2 * (1 + c) ^ 2 + 96 * dG sys L Hunit * (1 + c) ^ 2 +
        16 * m * cF sys L Hunit * (1 + c)) * D.Xi * Q / K ^ 3 := by
    rw [← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hK3.le
    have a1 : 0 ≤ 128 * m ^ 2 * (1 + c) ^ 2 * D.Xi := by positivity
    have a2 : 0 ≤ 96 * dG sys L Hunit * (1 + c) ^ 2 * D.Xi := by positivity
    have a3 : 0 ≤ 16 * m * cF sys L Hunit * (1 + c) * D.Xi := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hQ1 a1, mul_le_mul_of_nonneg_left ht1 a2,
      mul_le_mul_of_nonneg_left hQ1 a3]
  linarith

/-! ## The kinetic-energy theorem -/

include hL hKernel in
/-- **`thm:kinetic-log`, Galerkin case** (`eq:kinetic-log`): there are `C ≥ 0` and `N₀` such
that for every cutoff `n ≥ N₀`, every datum `ψ₀ ∈ D(H²)`, the measured particle `p₀` and every
`t ≥ 0`,
`|⟨ψ(t), T_{p₀} ψ(t)⟩ - ⟨ψ_N(t), T_{p₀} ψ_N(t)⟩| ≤ C 𝒟² [1 + t + log(2 + K)] / K³`. -/
theorem thm_kinetic_log_galerkin (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (p₀ : Fin eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : EvoData L H) (t : ℝ), 0 ≤ t →
      |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
          (regKin sys (gF L) p₀).expect (emb eta n (retFlow sys L n (zero_isSymmetric (n := n))
            (-t) (ext eta n (Sm eta L D.u₀))))| ≤
        C * D.Xi ^ 2 * (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := by
  obtain ⟨Cr, hCr, N₁, hret⟩ := kinetic_retained_galerkin sys hL H hKernel Hunit hPeriodic
  set cT := cTr sys L Hunit with hcT
  set Cf := Cfl sys L Hunit 0 with hCf
  have hcT0 : 0 ≤ cT := cTr_nonneg sys hL Hunit
  have hCf0 : 0 ≤ Cf := Cfl_nonneg sys Hunit (le_refl (0 : ℝ))
  refine ⟨(eta : ℝ) ^ 2 * cT ^ 2 + Cr * (cT + 2 * Cf * cT), by positivity,
    max N₁ (nGal sys L Hunit), fun n hn D t ht => ?_⟩
  have hN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨hK1, -, -⟩ := nGal_scales hL (le_trans (le_max_right _ _) hn)
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  have hKc : Kc L n = K := rfl
  have hΞ := D.Xi_nonneg
  set m := regKin sys (gF L) p₀ with hm
  set ψN := retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀)) with hψN
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D t
  set M := cT * D.Xi with hM
  have hM0 : 0 ≤ M := by positivity
  set Q := 1 + t + Real.log (2 + K) with hQ
  have hlog0 : 0 ≤ Real.log (2 + K) := Real.log_nonneg (by linarith)
  have hQ1 : 1 ≤ Q := by linarith
  have hK3 : 0 < K ^ 3 := by positivity
  -- the projection term
  have hsplit := m.expect_split n w
  have htail0 := m.expect_tail_nonneg n w
  have htail := m.expect_tail_le n w
  have hR := fgood_R hF hL hK1
  have hTt : ‖coulombFourierKineticH2 sys (gF L) w -
      molecularH2Truncate n (coulombFourierKineticH2 sys (gF L) w)‖ ≤
      eta * M * K ^ (-(1 / 2 : ℝ)) := by
    refine (PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) n _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n) a (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ ∑ _a : Fin eta, M * K ^ (-(1 / 2 : ℝ)) :=
          Finset.sum_le_sum fun a _ => (hF.2 a K hK1).2
      _ = eta * M * K ^ (-(1 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hpow : K ^ (-(5 / 2 : ℝ)) * K ^ (-(1 / 2 : ℝ)) = 1 / K ^ 3 := by
    rw [← Real.rpow_add hK0, show (-(5 / 2 : ℝ)) + (-(1 / 2)) = -(3 : ℝ) by norm_num,
      Real.rpow_neg hK0.le, one_div]
    congr 1
    exact_mod_cast Real.rpow_natCast K 3
  have hproj : m.expect (molecularH2StateMap eta (gF L) (w - molecularH2Truncate n w)) ≤
      (eta : ℝ) ^ 2 * M ^ 2 / K ^ 3 := by
    refine htail.trans ?_
    have h1 := mul_le_mul hR hTt (norm_nonneg _) (by positivity)
    refine h1.trans (le_of_eq ?_)
    calc eta * M * K ^ (-(5 / 2 : ℝ)) * (eta * M * K ^ (-(1 / 2 : ℝ))) =
          (eta : ℝ) ^ 2 * M ^ 2 * (K ^ (-(5 / 2 : ℝ)) * K ^ (-(1 / 2 : ℝ))) := by ring
      _ = _ := by rw [hpow]; ring
  -- the pairing term
  have hSw : molecularH2StateMap eta (gF L) w = D.U t (Sm eta L D.u₀) := hw1
  have hpair := expect_sub_le m (molecularH2Truncate n w) (cubeLift (gF L) n ψN)
  have hS1 : molecularH2StateMap eta (gF L) (molecularH2Truncate n w) =
      molecularH2Truncate n (D.U t (Sm eta L D.u₀)) := by
    rw [stateMap_truncate, hSw]
  have hS2 : molecularH2StateMap eta (gF L) (cubeLift (gF L) n ψN) = emb eta n ψN :=
    stateMap_cubeLift' ψN
  rw [hS1, hS2] at hpair
  have hdiff := hret n hN₁ D t ht
  rw [hKc] at hdiff
  have hμ1 : ‖m.h2 (molecularH2Truncate n w)‖ ≤ M := by
    refine (m.norm_h2_le _).trans ?_
    rw [kinetic_truncate]
    refine (molecularH2Truncate_norm_le n _).trans ?_
    have := hF.1
    have := norm_nonneg (Sm eta L w)
    linarith
  have hμ2 : ‖m.h2 (cubeLift (gF L) n ψN)‖ ≤ 2 * Cf * cT * D.Xi := by
    refine (m.norm_h2_le _).trans ?_
    rw [norm_kinetic_cubeLift sys ψN]
    refine (norm_kin_le_wt sys ψN).trans ?_
    have h1 := theta_retFlow_le sys Hunit hL hPeriodic (zero_isSymmetric (n := n)) le_rfl
      (fun v => by simp) (-t) (ext eta n (Sm eta L D.u₀))
    have hF0 := datum_fgood sys hL H hKernel Hunit hPeriodic D
    have hg := ext_good sys (n := n) hF0
    have h2 := theta_le_good sys hg
    calc ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 ψN‖
        ≤ Cf * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L D.u₀))‖ := h1
      _ ≤ Cf * (2 * (cT * D.Xi)) := mul_le_mul_of_nonneg_left h2 hCf0
      _ = 2 * Cf * cT * D.Xi := by ring
  have hpb : |m.expect (molecularH2Truncate n (D.U t (Sm eta L D.u₀))) -
      m.expect (emb eta n ψN)| ≤ Cr * D.Xi * Q / K ^ 3 * (M + 2 * Cf * cT * D.Xi) :=
    hpair.trans (mul_le_mul hdiff (add_le_add hμ1 hμ2) (by positivity) (by positivity))
  -- assemble
  have hE : m.expect (D.U t (Sm eta L D.u₀)) =
      m.expect (molecularH2StateMap eta (gF L) (molecularH2Truncate n w)) +
        m.expect (molecularH2StateMap eta (gF L) (w - molecularH2Truncate n w)) := by
    rw [← hSw]
    exact hsplit
  rw [hE, hS1, hKc]
  have habs : |m.expect (molecularH2Truncate n (D.U t (Sm eta L D.u₀))) +
      m.expect (molecularH2StateMap eta (gF L) (w - molecularH2Truncate n w)) -
        m.expect (emb eta n ψN)| ≤
      |m.expect (molecularH2Truncate n (D.U t (Sm eta L D.u₀))) - m.expect (emb eta n ψN)| +
        m.expect (molecularH2StateMap eta (gF L) (w - molecularH2Truncate n w)) := by
    rw [show m.expect (molecularH2Truncate n (D.U t (Sm eta L D.u₀))) +
        m.expect (molecularH2StateMap eta (gF L) (w - molecularH2Truncate n w)) -
          m.expect (emb eta n ψN) =
        (m.expect (molecularH2Truncate n (D.U t (Sm eta L D.u₀))) - m.expect (emb eta n ψN)) +
          m.expect (molecularH2StateMap eta (gF L) (w - molecularH2Truncate n w)) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg htail0]
  refine habs.trans ?_
  have hfin : Cr * D.Xi * Q / K ^ 3 * (M + 2 * Cf * cT * D.Xi) + (eta : ℝ) ^ 2 * M ^ 2 / K ^ 3 ≤
      ((eta : ℝ) ^ 2 * cT ^ 2 + Cr * (cT + 2 * Cf * cT)) * D.Xi ^ 2 * Q / K ^ 3 := by
    rw [hM]
    have e1 : Cr * D.Xi * Q / K ^ 3 * (cT * D.Xi + 2 * Cf * cT * D.Xi) =
        Cr * (cT + 2 * Cf * cT) * D.Xi ^ 2 * Q / K ^ 3 := by ring
    have e2 : (eta : ℝ) ^ 2 * (cT * D.Xi) ^ 2 / K ^ 3 =
        (eta : ℝ) ^ 2 * cT ^ 2 * D.Xi ^ 2 / K ^ 3 := by
      ring
    rw [e1, e2]
    have h3 : (eta : ℝ) ^ 2 * cT ^ 2 * D.Xi ^ 2 / K ^ 3 ≤
        (eta : ℝ) ^ 2 * cT ^ 2 * D.Xi ^ 2 * Q / K ^ 3 := by
      apply div_le_div_of_nonneg_right _ hK3.le
      have : 0 ≤ (eta : ℝ) ^ 2 * cT ^ 2 * D.Xi ^ 2 := by positivity
      nlinarith
    have e3 : ((eta : ℝ) ^ 2 * cT ^ 2 + Cr * (cT + 2 * Cf * cT)) * D.Xi ^ 2 * Q / K ^ 3 =
        Cr * (cT + 2 * Cf * cT) * D.Xi ^ 2 * Q / K ^ 3 +
          (eta : ℝ) ^ 2 * cT ^ 2 * D.Xi ^ 2 * Q / K ^ 3 := by ring
    rw [e3]
    linarith
  linarith [hpb, hproj, hfin]

/-! ## The stopping-power window -/

include hL hKernel in
/-- **`cor:stopping-log`, Galerkin case** (`eq:stopping-log`): for every window `[0, τ]`,
`τ > 0`, and reference speed `v_p > 0`, the signed secants
`Ŝ_τ = (⟨T_{p₀}⟩(τ) - ⟨T_{p₀}⟩(0))/(v_p τ)` of the exact and Galerkin trajectories differ by at
most `(C 𝒟²/v_p) [1 + (1 + log(2 + K))/τ] / K³`. -/
theorem cor_stopping_log_galerkin (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (p₀ : Fin eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : EvoData L H) {vp τ : ℝ}, 0 < vp → 0 < τ →
      let ψN : ℝ → L2 eta := fun s =>
        emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-s) (ext eta n (Sm eta L D.u₀)))
      |((regKin sys (gF L) p₀).expect (D.U τ (Sm eta L D.u₀)) -
            (regKin sys (gF L) p₀).expect (D.U 0 (Sm eta L D.u₀))) / (vp * τ) -
          ((regKin sys (gF L) p₀).expect (ψN τ) - (regKin sys (gF L) p₀).expect (ψN 0)) /
            (vp * τ)| ≤
        C * D.Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 := by
  obtain ⟨C, hC, N₀, h⟩ := thm_kinetic_log_galerkin sys hL H hKernel Hunit hPeriodic p₀
  refine ⟨2 * C, by positivity, max N₀ (nGal sys L Hunit), fun n hn D vp τ hvp hτ => ?_⟩
  intro ψN
  have hN₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨hK1, -, -⟩ := nGal_scales hL (le_trans (le_max_right _ _) hn)
  have hKc : Kc L n = gF L * n := rfl
  have hK0 : 0 < Kc L n := by rw [hKc]; linarith
  have h1 := h n hN₀ D τ hτ.le
  have h0 := h n hN₀ D 0 le_rfl
  set e1 := (regKin sys (gF L) p₀).expect (D.U τ (Sm eta L D.u₀)) -
    (regKin sys (gF L) p₀).expect (ψN τ) with he1
  set e0 := (regKin sys (gF L) p₀).expect (D.U 0 (Sm eta L D.u₀)) -
    (regKin sys (gF L) p₀).expect (ψN 0) with he0
  have hΞ := D.Xi_nonneg
  have hlog : 0 ≤ Real.log (2 + Kc L n) := Real.log_nonneg (by linarith)
  have hvτ : 0 < vp * τ := mul_pos hvp hτ
  have e : ((regKin sys (gF L) p₀).expect (D.U τ (Sm eta L D.u₀)) -
        (regKin sys (gF L) p₀).expect (D.U 0 (Sm eta L D.u₀))) / (vp * τ) -
      ((regKin sys (gF L) p₀).expect (ψN τ) - (regKin sys (gF L) p₀).expect (ψN 0)) / (vp * τ) =
      (e1 - e0) / (vp * τ) := by
    rw [he1, he0]
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hvτ, div_le_iff₀ hvτ]
  have hsum : |e1 - e0| ≤ |e1| + |e0| := abs_sub _ _
  have h0' : |e0| ≤ C * D.Xi ^ 2 * (1 + 0 + Real.log (2 + Kc L n)) / Kc L n ^ 3 := h0
  have h1' : |e1| ≤ C * D.Xi ^ 2 * (1 + τ + Real.log (2 + Kc L n)) / Kc L n ^ 3 := h1
  have hK3 : 0 < Kc L n ^ 3 := by positivity
  have hfin : C * D.Xi ^ 2 * (1 + τ + Real.log (2 + Kc L n)) / Kc L n ^ 3 +
      C * D.Xi ^ 2 * (1 + 0 + Real.log (2 + Kc L n)) / Kc L n ^ 3 ≤
      2 * C * D.Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 * (vp * τ) := by
    have e2 : 2 * C * D.Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 *
        (vp * τ) = 2 * C * D.Xi ^ 2 * (τ + (1 + Real.log (2 + Kc L n))) / Kc L n ^ 3 := by
      field_simp
    rw [e2, ← add_div]
    apply div_le_div_of_nonneg_right _ hK3.le
    have : 0 ≤ C * D.Xi ^ 2 := by positivity
    nlinarith
  linarith

end Endpoint

end KineticLog
