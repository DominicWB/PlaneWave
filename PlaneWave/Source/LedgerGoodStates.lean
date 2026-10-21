import PlaneWave.Source.RefinedBudgets

/-!
# Flux/source build, block 5: the ledger on good states

`norm_inner_Hpp_good`: for a good `u` (`IsGood 1 M u`) and any `φ`,

  `|⟪(H'' - H_N) u, φ⟫| ≤ M (k₀ ‖φ‖ + k_{1/4} ‖ℰ^{1/4} φ‖ + k_{1/2} ‖ℰ^{1/2} φ‖ + k_s ‖ℰ^s φ‖)`,

the ledger bound `norm_inner_ledger_le` with every entry instantiated:

* operator norms: `‖Z₂‖ ≤ z_b + 2 C_mix/e_H`, `‖W_N‖ ≤ C_VN`, `‖ΔH‖ ≤ C_Δ`, `‖G‖ ≤ 2 z₂ A_max`,
  `‖A‖ ≤ A_max`, `‖Σ₃‖ ≤ z₃`;
* good-state vector bounds: `‖Σ₂^bb u‖ ≤ C_Σg M/n³`, `‖Σ₂^mix u‖` (weighted Laplace and the hot
  tail), `‖W_N u‖ ≤ √2 C_m M`, `‖ΔH u‖ ≤ α_Δ M`, `‖G u‖` (`α_bb`, `C_res/n³`, `α_mix` and the
  high-energy tail), `‖P H^{(3)} P u‖ ≤ α₃ M`, `‖ΔH_{≥4} u‖ ≤ α₄ M`;
* the pairings: `R` by `norm_inner_Rc_le` (`lem:res2` and the high-energy tails of `u` and `φ`),
  `[Σ₂^mix, W_N]` by its four orientations (the low-energy weighted potential tail
  `wt_res_low_WN_sq_le` and the hot potential tail `norm_res_hot_WN_le`), and `[Σ₃, W_N]` by
  eq:bulk-completion.

The hypotheses on `Σ₃` and `H₃^res` are those of the conditional `thm:src3`, for the given `u`:
`Σ₃` skew-adjoint, `[Σ₃, A] = -(H₃^ret - H₃^res)`, `‖Σ₃‖ ≤ z₃`,
`‖ℰ^{-1/4} Σ₃ W_N u‖ + ‖ℰ^{1/4} Σ₃ u‖ ≤ β M` and `‖H₃^res u‖ ≤ β M`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

section LedgerGood

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- The tail constant of `W_N` is linear in the budget. -/
lemma CtW_eq_mul (Hunit M₂ : ℝ) : CtW sys L Hunit M₂ = CtW sys L Hunit 1 * M₂ := by
  unfold CtW finiteCoulombPhysicalTailConstant finiteCoulombTailConstant
  ring

/-! ## The constants -/

/-- `‖Z₂‖ ≤ z₂ = z_b + 2 C_mix/e_H`. -/
noncomputable def z2C (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  zbC sys L n + 2 * (CHmix sys L Hunit n / eH sys L n)

/-- `η (K/4)^{-5/2}`: the hot tail of a good state per unit budget. -/
noncomputable def hotF (eta : ℕ) (L : ℝ) (n : ℕ) : ℝ := eta * (Kc L n / 4) ^ (-(5 / 2 : ℝ))

/-- `η l_H^{-5/2}`: the high-energy tail of a good state per unit budget. -/
noncomputable def highF (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  eta * lH sys L n ^ (-(5 / 2 : ℝ))

/-- `‖Z₂ u‖ ≤ z₂ᵤ M` for good `u`. -/
noncomputable def z2uC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  CSg sys L / (n : ℝ) ^ 3 +
    (CZws sys L Hunit n s / eH sys L n + CHmix sys L Hunit n / eH sys L n * hotF eta L n)

/-- `‖G u‖ ≤ g_u M` for good `u`. -/
noncomputable def guC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  alphaBB sys L Hunit n + CRes sys L n / (n : ℝ) ^ 3 +
    (alphaMix sys L Hunit n + CHmix sys L Hunit n * highF sys L n)

/-- `‖ℰ^s 1{A ≤ e_H} W_N u‖ ≤ w_s M` for good `u`. -/
noncomputable def wsC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  Real.sqrt (FSDatum.momentConst1 eta s ((eta : ℝ) / 2) *
    ((CtW sys L Hunit 1 * (3 * sys.maxMass)) ^ 2 +
      2 * finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (1 + 2 * gF L)) *
    Real.sqrt (2 * mmax sys * eH sys L n) ^ (4 * s - 1))

/-- `√2 C_m`. -/
noncomputable def cvC (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit

/-- The first Taylor remainder per unit budget. -/
noncomputable def r2aC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  1 / 2 * (z2C sys L Hunit n * guC sys L Hunit n +
    2 * z2C sys L Hunit n * Amax eta L n * z2uC sys L Hunit n s +
    4 * z2C sys L Hunit n ^ 2 * (CVN sys L Hunit n + CDelta sys L Hunit n) +
    (2 * z2C sys L Hunit n * (2 * z2C sys L Hunit n * Amax eta L n) +
      4 * z2C sys L Hunit n ^ 2 * (CVN sys L Hunit n + CDelta sys L Hunit n)) * z2uC sys L Hunit n s)

/-- `‖D₂ u‖` per unit budget. -/
noncomputable def d2uC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  alphaD sys L Hunit n + guC sys L Hunit n +
    (z2C sys L Hunit n * (cvC sys L Hunit + alphaD sys L Hunit n) +
      (CVN sys L Hunit n + CDelta sys L Hunit n) * z2uC sys L Hunit n s) + r2aC sys L Hunit n s

/-- `‖D₂‖`. -/
noncomputable def d2oC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  CDelta sys L Hunit n + 2 * z2C sys L Hunit n * Amax eta L n +
    2 * z2C sys L Hunit n * (CVN sys L Hunit n + CDelta sys L Hunit n) +
    (2 * z2C sys L Hunit n * (2 * z2C sys L Hunit n * Amax eta L n) +
      4 * z2C sys L Hunit n ^ 2 * (CVN sys L Hunit n + CDelta sys L Hunit n))

/-- `‖H₃^gap u‖` per unit budget. -/
noncomputable def h3guC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (β : ℝ) : ℝ :=
  zbC sys L n * cvC sys L Hunit + CVN sys L Hunit n * (CSg sys L / (n : ℝ) ^ 3) +
    alpha3 sys L Hunit n + β

/-- The second Taylor remainder per unit budget. -/
noncomputable def r2bC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (z3 β : ℝ) : ℝ :=
  1 / 2 * (z3 * h3guC sys L Hunit n β + 2 * z3 * Amax eta L n * β +
    4 * z3 ^ 2 * (CVN sys L Hunit n + d2oC sys L Hunit n) +
    (2 * z3 * (2 * z3 * Amax eta L n) + 4 * z3 ^ 2 * (CVN sys L Hunit n + d2oC sys L Hunit n)) * β)

/-- The coefficient of `‖φ‖`. -/
noncomputable def k0C (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s z3 β : ℝ) : ℝ :=
  CRes sys L n / (n : ℝ) ^ 3 + β + alpha4 sys L Hunit n +
    CVN sys L Hunit n * (CHmix sys L Hunit n / eH sys L n * hotF eta L n) +
    (z2C sys L Hunit n * alphaD sys L Hunit n + CDelta sys L Hunit n * z2uC sys L Hunit n s) +
    r2aC sys L Hunit n s + (z3 * d2uC sys L Hunit n s + d2oC sys L Hunit n * β) +
    r2bC sys L Hunit n z3 β

/-- The coefficient of `‖ℰ^{1/4} φ‖`. -/
noncomputable def k14C (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s β : ℝ) : ℝ :=
  CHmix sys L Hunit n * highF sys L n * (1 + eH sys L n) ^ (-(1 / 4 : ℝ)) +
    CZws sys L Hunit n s / eH sys L n * wsC sys L Hunit n s * (1 + eH sys L n) ^ (-(1 / 4 : ℝ)) +
    (1 + cvC sys L Hunit) * β

/-- The coefficient of `‖ℰ^{1/2} φ‖`. -/
noncomputable def k12C (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  CZws sys L Hunit n s / eH sys L n * cvC sys L Hunit

/-- The coefficient of `‖ℰ^s φ‖`. -/
noncomputable def ksC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  eta * (CtW sys L Hunit 1 * (3 * sys.maxMass)) * (Kc L n / 4) ^ (-(1 / 2 : ℝ)) *
    (CZws sys L Hunit n s / eH sys L n)

/-- **The ledger bound on good states** (per unit budget). -/
noncomputable def ledK (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s z3 β f0 f14 f12 fs : ℝ) :
    ℝ :=
  k0C sys L Hunit n s z3 β * f0 + k14C sys L Hunit n s β * f14 + k12C sys L Hunit n s * f12 +
    ksC sys L Hunit n s * fs

/-- The ledger data on a good state with budget `M`. -/
noncomputable def ledD (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s z3 β M f0 f14 f12 fs : ℝ) :
    FSConj.LedgerData where
  z := z2C sys L Hunit n
  z3 := z3
  v0 := CVN sys L Hunit n
  d0 := CDelta sys L Hunit n
  g0 := 2 * z2C sys L Hunit n * Amax eta L n
  a0 := Amax eta L n
  zb := zbC sys L n
  zu := M * z2uC sys L Hunit n s
  z3u := β * M
  vu := cvC sys L Hunit * M
  du := alphaD sys L Hunit n * M
  gu := M * guC sys L Hunit n
  hfu := alpha3 sys L Hunit n * M
  r3u := β * M
  d4u := alpha4 sys L Hunit n * M
  uu := M
  zbu := M * (CSg sys L / (n : ℝ) ^ 3)
  f0 := f0
  pR := M * (CRes sys L n / (n : ℝ) ^ 3 * f0 +
    CHmix sys L Hunit n * highF sys L n * ((1 + eH sys L n) ^ (-(1 / 4 : ℝ)) * f14))
  pM := M * (CZws sys L Hunit n s / eH sys L n * wsC sys L Hunit n s *
      ((1 + eH sys L n) ^ (-(1 / 4 : ℝ)) * f14) + ksC sys L Hunit n s * fs +
    k12C sys L Hunit n s * f12 +
    CVN sys L Hunit n * (CHmix sys L Hunit n / eH sys L n * hotF eta L n) * f0)
  pS := (1 + cvC sys L Hunit) * β * M * f14

lemma ledD_bound (Hunit : ℝ) (s z3 β M f0 f14 f12 fs : ℝ) :
    (ledD sys L Hunit n s z3 β M f0 f14 f12 fs).bound =
      M * ledK sys L Hunit n s z3 β f0 f14 f12 fs := by
  simp only [FSConj.LedgerData.bound, FSConj.LedgerData.r2a, FSConj.LedgerData.r2b,
    FSConj.LedgerData.d2u, FSConj.LedgerData.d2o, FSConj.LedgerData.h3gu, FSConj.LedgerData.h3go,
    ledD, ledK, k0C, k14C, k12C, ksC, r2aC, r2bC, d2uC, d2oC, h3guC]
  ring

/-! ## Nonnegativity -/

include hL in
lemma zc_nonneg (Hunit : ℝ) : 0 ≤ zc sys L Hunit n := by
  unfold zc
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have := a1c_nonneg sys (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  positivity

lemma CX_nonneg (Hunit : ℝ) : 0 ≤ CX sys L Hunit n := by
  unfold CX
  have := CV_nonneg sys Hunit (L := L) (n := n)
  have := CZ_nonneg sys Hunit (L := L) (n := n)
  positivity

include hL in
lemma alphaD_nonneg (Hunit : ℝ) : 0 ≤ alphaD sys L Hunit n := by
  simp only [alphaD]
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have := a1c_nonneg sys (L := L) (n := n)
  have := a0c_nonneg sys (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  have := CX_nonneg sys Hunit (L := L) (n := n)
  positivity

include hL in
lemma alpha3_nonneg (Hunit : ℝ) : 0 ≤ alpha3 sys L Hunit n := by
  unfold alpha3
  have := zc_nonneg sys hL Hunit (n := n)
  have := a0c_nonneg sys (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  have := CZ_nonneg sys Hunit (L := L) (n := n)
  positivity

include hL in
lemma alpha4_nonneg (Hunit : ℝ) : 0 ≤ alpha4 sys L Hunit n := by
  unfold alpha4
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have := zc_nonneg sys hL Hunit (n := n)
  have := a0c_nonneg sys (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  have := CZ_nonneg sys Hunit (L := L) (n := n)
  have := CV_nonneg sys Hunit (L := L) (n := n)
  have := CX_nonneg sys Hunit (L := L) (n := n)
  positivity

include hL in
lemma alphaBB_nonneg (Hunit : ℝ) : 0 ≤ alphaBB sys L Hunit n := by
  unfold alphaBB
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have := a0c_nonneg sys (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  have := CV_nonneg sys Hunit (L := L) (n := n)
  positivity

include hL in
lemma alphaMix_nonneg (Hunit : ℝ) : 0 ≤ alphaMix sys L Hunit n := by
  unfold alphaMix
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have := a0c_nonneg sys (L := L) (n := n)
  have := a1c_nonneg sys (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  have := CV_nonneg sys Hunit (L := L) (n := n)
  positivity

lemma CVN_nonneg (Hunit : ℝ) : 0 ≤ CVN sys L Hunit n := by
  unfold CVN
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have := Amax_nonneg eta L n
  have : 0 ≤ (1 + Amax eta L n) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  positivity

lemma cvC_nonneg (Hunit : ℝ) : 0 ≤ cvC sys L Hunit := by
  unfold cvC
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  positivity

/-! ## Good-state bounds -/

omit [Fintype ν] in
lemma theta_le_good {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ≤ M := by
  have := hu.1; have := norm_nonneg u; linarith

omit [Fintype ν] in
include hL in
lemma hot_le_good {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) (hK1 : 1 ≤ Kc L n / 4) :
    ‖FSKernel.res (fun p => ¬ IsCold n p) u‖ ≤ M * hotF eta L n := by
  have := norm_res_hot_good sys hL hu hK1
  unfold hotF; linarith

omit [Fintype ν] in
include hL in
lemma high_le_good {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) (hlH : 1 ≤ lH sys L n) :
    ‖FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) u‖ ≤ M * highF sys L n := by
  have := norm_res_high_good sys hL hu hlH
  unfold highF; linarith

omit [Fintype ν] in
lemma hotF_nonneg (hK1 : 1 ≤ Kc L n / 4) : 0 ≤ hotF eta L n := by
  unfold hotF
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ Kc L n / 4 by linarith) (-(5 / 2 : ℝ))
  positivity

omit [Fintype ν] in
lemma highF_nonneg (hlH : 1 ≤ lH sys L n) : 0 ≤ highF sys L n := by
  unfold highF
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ lH sys L n by linarith) (-(5 / 2 : ℝ))
  positivity

include hKernel in
lemma norm_Z2_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {s : ℝ} (hs : 3 / 4 < s) (hs1 : s ≤ 1) (hK1 : 1 ≤ Kc L n / 4) {M : ℝ} {u : En eta n}
    (hu : IsGood sys L 1 M u) :
    ‖Z2b sys L n u‖ ≤ M * (CSg sys L / (n : ℝ) ^ 3) ∧
      ‖(Z2b sys L n + Z2m sys hL hn H) u‖ ≤ M * z2uC sys L Hunit n s := by
  have hΘ := theta_le_good sys hu
  have hws : ‖FSSpectral.wt (sb eta n) (Asym sys L n) s u‖ ≤ M := (wt_mono sys L n hs1 u).trans hΘ
  have heH := eH_pos sys hL (show 0 < n by omega)
  have hCZws := CZws_nonneg sys Hunit s (L := L) (n := n)
  have hCH := CHmix_nonneg sys hL Hunit (n := n)
  have hhot := hot_le_good sys hL hu hK1
  have hZbu : ‖Z2b sys L n u‖ ≤ M * (CSg sys L / (n : ℝ) ^ 3) := by
    have h := norm_Sig2bb_good hL hn hu
    simp only [Z2b, LinearMap.coe_toContinuousLinearMap']
    refine h.trans (le_of_eq ?_); ring
  refine ⟨hZbu, ?_⟩
  have hZmu : ‖Z2m sys hL hn H u‖ ≤
      M * (CZws sys L Hunit n s / eH sys L n + CHmix sys L Hunit n / eH sys L n * hotF eta L n) := by
    have h := norm_Sig2mix_le sys hL hn H hKernel Hunit hPeriodic hs u
    simp only [Z2m, LinearMap.coe_toContinuousLinearMap']
    refine h.trans ?_
    have h1 : CZws sys L Hunit n s / eH sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s u‖ ≤
        CZws sys L Hunit n s / eH sys L n * M := mul_le_mul_of_nonneg_left hws (by positivity)
    have h2 : CHmix sys L Hunit n / eH sys L n * ‖FSKernel.res (fun p => ¬ IsCold n p) u‖ ≤
        CHmix sys L Hunit n / eH sys L n * (M * hotF eta L n) :=
      mul_le_mul_of_nonneg_left hhot (by positivity)
    linarith
  rw [add_apply]
  refine (norm_add_le _ _).trans ?_
  unfold z2uC
  linarith

include hKernel in
lemma norm_G2_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hlH : 1 ≤ lH sys L n) {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) :
    ‖G2 sys hL hn H u‖ ≤ M * guC sys L Hunit n := by
  have hΘ := theta_le_good sys hu
  have hCH := CHmix_nonneg sys hL Hunit (n := n)
  have hhigh := high_le_good sys hL hu hlH
  have e1 := congrArg (fun T : En eta n →ₗ[ℂ] En eta n => T u) (Hbb_split (sys := sys) hL hn)
  have e2 := congrArg (fun T : En eta n →ₗ[ℂ] En eta n => T u) (Hmix_split sys hL hn H hKernel)
  simp only [LinearMap.add_apply] at e1 e2
  change Hbb sys hL hn u = _ at e1
  change Hmix sys hL hn H u = _ at e2
  have hG : G2 sys hL hn H u = (Hbb sys hL hn u - Hres sys L n u) +
      (Hmix sys hL hn H u - HmixRes sys hL hn H u) := by
    simp only [G2, LinearMap.coe_toContinuousLinearMap', LinearMap.add_apply]
    rw [e1, e2]; abel
  rw [hG]
  have k1 : ‖Hbb sys hL hn u‖ ≤ alphaBB sys L Hunit n * M :=
    (norm_Hbb_wt_le sys hL hn H hKernel Hunit hPeriodic u).trans
      (mul_le_mul_of_nonneg_left hΘ (alphaBB_nonneg sys hL Hunit))
  have k2 : ‖Hres sys L n u‖ ≤ CRes sys L n * M / (n : ℝ) ^ 3 := norm_Hres_good hL hn hu
  have k3 : ‖Hmix sys hL hn H u‖ ≤ alphaMix sys L Hunit n * M :=
    (norm_Hmix_wt_le sys hL hn H hKernel Hunit hPeriodic u).trans
      (mul_le_mul_of_nonneg_left hΘ (alphaMix_nonneg sys hL Hunit))
  have k4 : ‖HmixRes sys hL hn H u‖ ≤ CHmix sys L Hunit n * (M * highF sys L n) := by
    classical
    unfold HmixRes
    rw [kop_kRes sys hL hn H]
    refine (FSKernel.norm_res_le _ _).trans ?_
    exact (norm_Hmix_le sys hL hn H hKernel Hunit hPeriodic _).trans
      (mul_le_mul_of_nonneg_left hhigh hCH)
  have := norm_sub_le (Hbb sys hL hn u) (Hres sys L n u)
  have := norm_sub_le (Hmix sys hL hn H u) (HmixRes sys hL hn H u)
  have := norm_add_le (Hbb sys hL hn u - Hres sys L n u) (Hmix sys hL hn H u - HmixRes sys hL hn H u)
  have e3 : CRes sys L n * M / (n : ℝ) ^ 3 = M * (CRes sys L n / (n : ℝ) ^ 3) := by ring
  have e4 : M * guC sys L Hunit n = alphaBB sys L Hunit n * M + M * (CRes sys L n / (n : ℝ) ^ 3) +
      (alphaMix sys L Hunit n * M + CHmix sys L Hunit n * (M * highF sys L n)) := by
    unfold guC; ring
  rw [e4]
  linarith

include hKernel in
/-- The residual pairing on a good state. -/
lemma pair_R2c_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hlH : 1 ≤ lH sys L n) {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) (φ : En eta n) :
    ‖⟪R2c sys hL hn H u, φ⟫_ℂ‖ ≤ M * (CRes sys L n / (n : ℝ) ^ 3 * ‖φ‖ +
      CHmix sys L Hunit n * highF sys L n * ((1 + eH sys L n) ^ (-(1 / 4 : ℝ)) *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖)) := by
  have heH := eH_pos sys hL (show 0 < n by omega)
  have hCH := CHmix_nonneg sys hL Hunit (n := n)
  have hhigh := high_le_good sys hL hu hlH
  have hq : 0 ≤ (1 + eH sys L n) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hφhigh := norm_res_high_le_wt sys (L := L) heH.le φ
  refine (norm_inner_Rc_le sys hL hn H hKernel Hunit hPeriodic u φ).trans ?_
  have k1 : ‖Hres sys L n u‖ * ‖φ‖ ≤ CRes sys L n * M / (n : ℝ) ^ 3 * ‖φ‖ :=
    mul_le_mul_of_nonneg_right (norm_Hres_good hL hn hu) (norm_nonneg _)
  have k2 : CHmix sys L Hunit n * ‖FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) u‖ *
      ‖FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) φ‖ ≤
      CHmix sys L Hunit n * (M * highF sys L n) * ((1 + eH sys L n) ^ (-(1 / 4 : ℝ)) *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hhigh hCH) hφhigh (norm_nonneg _) (by
      have := le_trans (norm_nonneg _) hhigh; positivity)
  have e : M * (CRes sys L n / (n : ℝ) ^ 3 * ‖φ‖ +
      CHmix sys L Hunit n * highF sys L n * ((1 + eH sys L n) ^ (-(1 / 4 : ℝ)) *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖)) =
      CRes sys L n * M / (n : ℝ) ^ 3 * ‖φ‖ +
        CHmix sys L Hunit n * (M * highF sys L n) * ((1 + eH sys L n) ^ (-(1 / 4 : ℝ)) *
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖) := by ring
  rw [e]; linarith

include hL hKernel in
/-- `‖ℰ^s 1{A ≤ e_H} W_N u‖ ≤ w_s M` for good `u`. -/
lemma wt_low_WN_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {s : ℝ} (hs : 1 / 4 < s) (hΛ : 1 ≤ Real.sqrt (2 * mmax sys * eH sys L n))
    {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) s
      (FSKernel.res (fun p => Asym sys L n p ≤ eH sys L n) (VN sys L n u))‖ ≤
      M * wsC sys L Hunit n s := by
  have hΘ := theta_le_good sys hu
  have hM := good_nonneg hu
  have huM : ‖u‖ ≤ M := norm_le_good hu
  have hAu : ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖ ≤ M := (norm_kin_le_wt sys u).trans hΘ
  have hm := sys.one_le_maxMass
  have hM₂ : sys.maxMass * (‖u‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖) ≤
      3 * sys.maxMass * M := by
    have : ‖u‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖ ≤ 3 * M := by linarith
    calc sys.maxMass * (‖u‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖)
        ≤ sys.maxMass * (3 * M) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = _ := by ring
  have hCt : CtW sys L Hunit (3 * sys.maxMass * M) = CtW sys L Hunit 1 * (3 * sys.maxMass) * M := by
    rw [CtW_eq_mul sys Hunit (3 * sys.maxMass * M)]; ring
  have h := wt_res_low_WN_sq_le sys hL H hKernel Hunit hPeriodic hs u hM₂ hΛ
  have hmc := FSDatum.momentConst1_nonneg eta (r := s) (cA := (eta : ℝ) / 2) hs (by positivity)
  have hΛs : 0 ≤ Real.sqrt (2 * mmax sys * eH sys L n) ^ (4 * s - 1) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hg := gF_pos hL
  have hT : CtW sys L Hunit (3 * sys.maxMass * M) ^ 2 +
      2 * finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (1 + 2 * gF L) *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 ≤
      M ^ 2 * ((CtW sys L Hunit 1 * (3 * sys.maxMass)) ^ 2 +
        2 * finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (1 + 2 * gF L)) := by
    rw [hCt]
    have hΘ2 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hΘ 2
    have : 2 * finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (1 + 2 * gF L) *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 ≤
        2 * finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (1 + 2 * gF L) * M ^ 2 :=
      mul_le_mul_of_nonneg_left hΘ2 (by positivity)
    have e : (CtW sys L Hunit 1 * (3 * sys.maxMass) * M) ^ 2 =
        M ^ 2 * (CtW sys L Hunit 1 * (3 * sys.maxMass)) ^ 2 := by ring
    rw [e]; linarith
  have h2 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) s
      (FSKernel.res (fun p => Asym sys L n p ≤ eH sys L n) (VN sys L n u))‖ ^ 2 ≤
      (M * wsC sys L Hunit n s) ^ 2 := by
    rw [mul_pow, wsC, Real.sq_sqrt (by positivity)]
    refine h.trans ?_
    calc FSDatum.momentConst1 eta s ((eta : ℝ) / 2) *
          (CtW sys L Hunit (3 * sys.maxMass * M) ^ 2 +
            2 * finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (1 + 2 * gF L) *
              ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2) *
          Real.sqrt (2 * mmax sys * eH sys L n) ^ (4 * s - 1)
        ≤ FSDatum.momentConst1 eta s ((eta : ℝ) / 2) *
          (M ^ 2 * ((CtW sys L Hunit 1 * (3 * sys.maxMass)) ^ 2 +
            2 * finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (1 + 2 * gF L))) *
          Real.sqrt (2 * mmax sys * eH sys L n) ^ (4 * s - 1) := by gcongr
      _ = _ := by ring
  have hw0 : 0 ≤ wsC sys L Hunit n s := Real.sqrt_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

include hKernel in
/-- The mixed commutator pairing on a good state. -/
lemma pair_Z2mV_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {s : ℝ} (hs : 3 / 4 < s) (hs1 : s ≤ 1)
    (hK1 : 1 ≤ Kc L n / 4) (hK2 : 2 * gF L ≤ Kc L n / 4)
    (hΛ : 1 ≤ Real.sqrt (2 * mmax sys * eH sys L n))
    {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) (φ : En eta n) :
    ‖⟪FSConj.cm (Z2m sys hL hn H) (VN sys L n) u, φ⟫_ℂ‖ ≤
      M * (CZws sys L Hunit n s / eH sys L n * wsC sys L Hunit n s *
          ((1 + eH sys L n) ^ (-(1 / 4 : ℝ)) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖) +
        ksC sys L Hunit n s * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s φ‖ +
        k12C sys L Hunit n s * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ‖ +
        CVN sys L Hunit n * (CHmix sys L Hunit n / eH sys L n * hotF eta L n) * ‖φ‖) := by
  set f0 := ‖φ‖
  set f14 := ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖
  set f12 := ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ‖
  set fs := ‖FSSpectral.wt (sb eta n) (Asym sys L n) s φ‖
  have hΘ := theta_le_good sys hu
  have hM := good_nonneg hu
  have huM : ‖u‖ ≤ M := norm_le_good hu
  have hAu : ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖ ≤ M := (norm_kin_le_wt sys u).trans hΘ
  have hws : ‖FSSpectral.wt (sb eta n) (Asym sys L n) s u‖ ≤ M := (wt_mono sys L n hs1 u).trans hΘ
  have heH := eH_pos sys hL (show 0 < n by omega)
  have hCZws := CZws_nonneg sys Hunit s (L := L) (n := n)
  have hCH := CHmix_nonneg sys hL Hunit (n := n)
  have hm := sys.one_le_maxMass
  have hhot := hot_le_good sys hL hu hK1
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hq : 0 ≤ (1 + eH sys L n) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hφhot : ‖FSKernel.res (fun p => ¬ IsCold n p) φ‖ ≤
      (1 + eH sys L n) ^ (-(1 / 4 : ℝ)) * f14 :=
    (norm_res_hot_le_high sys heH φ).trans (norm_res_high_le_wt sys heH.le φ)
  have hM₂ : sys.maxMass * (‖u‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖) ≤
      3 * sys.maxMass * M := by
    have : ‖u‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖ ≤ 3 * M := by linarith
    calc sys.maxMass * (‖u‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖)
        ≤ sys.maxMass * (3 * M) := mul_le_mul_of_nonneg_left this (by linarith)
      _ = _ := by ring
  have hCt : CtW sys L Hunit (3 * sys.maxMass * M) = CtW sys L Hunit 1 * (3 * sys.maxMass) * M := by
    rw [CtW_eq_mul sys Hunit (3 * sys.maxMass * M)]; ring
  have hCt1 : 0 ≤ CtW sys L Hunit 1 := CtW_nonneg sys hL Hunit zero_le_one
  refine (norm_inner_cm_Z2m_V_le sys hL hn H hKernel Hunit hPeriodic hs u φ).trans ?_
  have hc : 0 ≤ CZws sys L Hunit n s / eH sys L n := by positivity
  -- (a)
  have ha := wt_low_WN_good sys hL H hKernel Hunit hPeriodic (by linarith : 1 / 4 < s) hΛ hu
  have k1 : CZws sys L Hunit n s / eH sys L n *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) s
        (FSKernel.res (fun p => Asym sys L n p ≤ eH sys L n) (VN sys L n u))‖ *
      ‖FSKernel.res (fun p => ¬ IsCold n p) φ‖ ≤
      CZws sys L Hunit n s / eH sys L n * (M * wsC sys L Hunit n s) *
        ((1 + eH sys L n) ^ (-(1 / 4 : ℝ)) * f14) :=
    mul_le_mul (mul_le_mul_of_nonneg_left ha hc) hφhot (norm_nonneg _)
      (mul_nonneg hc (le_trans (norm_nonneg _) ha))
  -- (b)
  have hb : ‖FSKernel.res (fun p => ¬ IsCold n p) (VN sys L n u)‖ ≤
      M * (eta * (CtW sys L Hunit 1 * (3 * sys.maxMass)) * (Kc L n / 4) ^ (-(1 / 2 : ℝ))) := by
    have h := norm_res_hot_WN_le sys hL H hKernel Hunit hPeriodic hK1 hK2 u hM₂
    simp only [VN, LinearMap.coe_toContinuousLinearMap']
    refine h.trans (le_of_eq ?_)
    rw [hCt]; ring
  have k2 : ‖FSKernel.res (fun p => ¬ IsCold n p) (VN sys L n u)‖ *
      (CZws sys L Hunit n s / eH sys L n * fs) ≤ M * (ksC sys L Hunit n s * fs) := by
    have e : M * (ksC sys L Hunit n s * fs) =
        M * (eta * (CtW sys L Hunit 1 * (3 * sys.maxMass)) * (Kc L n / 4) ^ (-(1 / 2 : ℝ))) *
          (CZws sys L Hunit n s / eH sys L n * fs) := by unfold ksC; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  -- (c)
  have k3 : CZws sys L Hunit n s / eH sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s u‖ *
      (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * f12) ≤
      M * (k12C sys L Hunit n s * f12) := by
    have e : M * (k12C sys L Hunit n s * f12) = CZws sys L Hunit n s / eH sys L n * M *
        (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * f12) := by
      unfold k12C cvC; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hws hc) (by positivity)
  -- (d)
  have k4 : CVN sys L Hunit n * (CHmix sys L Hunit n / eH sys L n *
      ‖FSKernel.res (fun p => ¬ IsCold n p) u‖) * f0 ≤
      M * (CVN sys L Hunit n * (CHmix sys L Hunit n / eH sys L n * hotF eta L n) * f0) := by
    have e : M * (CVN sys L Hunit n * (CHmix sys L Hunit n / eH sys L n * hotF eta L n) * f0) =
        CVN sys L Hunit n * (CHmix sys L Hunit n / eH sys L n * (M * hotF eta L n)) * f0 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hhot (by positivity)) (CVN_nonneg sys Hunit)) (norm_nonneg _)
  have e : M * (CZws sys L Hunit n s / eH sys L n * wsC sys L Hunit n s *
        ((1 + eH sys L n) ^ (-(1 / 4 : ℝ)) * f14) + ksC sys L Hunit n s * fs +
      k12C sys L Hunit n s * f12 +
      CVN sys L Hunit n * (CHmix sys L Hunit n / eH sys L n * hotF eta L n) * f0) =
      CZws sys L Hunit n s / eH sys L n * (M * wsC sys L Hunit n s) *
        ((1 + eH sys L n) ^ (-(1 / 4 : ℝ)) * f14) + M * (ksC sys L Hunit n s * fs) +
      M * (k12C sys L Hunit n s * f12) +
      M * (CVN sys L Hunit n * (CHmix sys L Hunit n / eH sys L n * hotF eta L n) * f0) := by ring
  rw [e]; linarith

include hL in
/-- The third-rotation commutator pairing under eq:bulk-completion. -/
lemma pair_S3V_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (S3 : En eta n →L[ℂ] En eta n) {β M : ℝ} (u : En eta n)
    (hβ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤ β * M) (φ : En eta n) :
    ‖⟪FSConj.cm S3 (VN sys L n) u, φ⟫_ℂ‖ ≤
      (1 + cvC sys L Hunit) * β * M * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖ := by
  refine (norm_inner_cm_S3_V_le sys hL Hunit hPeriodic S3 u φ).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h1 := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u)))
  have h2 := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u))
  have hcv : 0 ≤ cvC sys L Hunit := cvC_nonneg sys Hunit
  have h3 : cvC sys L Hunit * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤
      cvC sys L Hunit * (β * M) := mul_le_mul_of_nonneg_left (by linarith) hcv
  have e : Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit = cvC sys L Hunit := rfl
  rw [e]
  have e2 : (1 + cvC sys L Hunit) * β * M = β * M + cvC sys L Hunit * (β * M) := by ring
  rw [e2]; linarith

/-! ## The bound -/

include hKernel in
/-- **The ledger on good states.** -/
theorem norm_inner_Hpp_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {s : ℝ} (hs : 3 / 4 < s) (hs1 : s ≤ 1)
    (hK1 : 1 ≤ Kc L n / 4) (hK2 : 2 * gF L ≤ Kc L n / 4) (hlH : 1 ≤ lH sys L n)
    (hΛ : 1 ≤ Real.sqrt (2 * mmax sys * eH sys L n))
    (S3 R3 : En eta n →L[ℂ] En eta n) (hS3 : S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n))
    (hA3 : FSConj.cm S3 (Akin sys L n) = -(H3ret sys hL hn H - R3))
    {z3 β M : ℝ} (hz3 : ‖S3‖ ≤ z3) (u : En eta n) (hu : IsGood sys L 1 M u)
    (hβ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤ β * M)
    (hR3 : ‖R3 u‖ ≤ β * M) (φ : En eta n) :
    ‖⟪(Hpp sys hL hn H S3 - (Akin sys L n + VN sys L n)) u, φ⟫_ℂ‖ ≤
      M * ledK sys L Hunit n s z3 β ‖φ‖ ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ‖
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) s φ‖ := by
  have hΘ := theta_le_good sys hu
  have huM : ‖u‖ ≤ M := norm_le_good hu
  have hz : ‖Z2b sys L n + Z2m sys hL hn H‖ ≤ z2C sys L Hunit n :=
    (norm_add_le _ _).trans (add_le_add (opNorm_Z2b_le sys hL hn)
      (opNorm_Z2m_le sys hL hn H hKernel Hunit hPeriodic))
  have hv0 := opNorm_VN_le sys hL Hunit hPeriodic (n := n)
  have hd0 := opNorm_dHc_le sys hL hn H hKernel Hunit hPeriodic
  have hg0 := opNorm_G2_le sys hL hn H hKernel hz
  have ha0 := opNorm_Akin_le sys (L := L) (n := n)
  have hzb := opNorm_Z2b_le sys hL hn
  obtain ⟨hZbu, hzu⟩ := norm_Z2_good sys hL hn H hKernel Hunit hPeriodic hs hs1 hK1 hu
  have hvu : ‖VN sys L n u‖ ≤ cvC sys L Hunit * M :=
    (norm_VN_apply_le sys hL Hunit hPeriodic u).trans (by
      unfold cvC
      exact mul_le_mul_of_nonneg_left hΘ (by
        have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit; positivity))
  have hdu : ‖dHc sys hL hn H u‖ ≤ alphaD sys L Hunit n * M :=
    (norm_dH_le_wt sys hL hn H hKernel Hunit hPeriodic u).trans
      (mul_le_mul_of_nonneg_left hΘ (alphaD_nonneg sys hL Hunit))
  have hgu := norm_G2_good sys hL hn H hKernel Hunit hPeriodic hlH hu
  have hhfu : ‖H3first sys hL hn H u‖ ≤ alpha3 sys L Hunit n * M :=
    (norm_H3first_le sys hL hn H hKernel Hunit hPeriodic u).trans
      (mul_le_mul_of_nonneg_left hΘ (alpha3_nonneg sys hL Hunit))
  have hd4u : ‖DH4 sys hL hn H u‖ ≤ alpha4 sys L Hunit n * M :=
    (norm_DH4_le sys hL hn H hKernel Hunit hPeriodic u).trans
      (mul_le_mul_of_nonneg_left hΘ (alpha4_nonneg sys hL Hunit))
  have hz3u : ‖S3 u‖ ≤ β * M := by
    have h1 := norm_le_wt sys L n (by norm_num : (0 : ℝ) ≤ 1 / 4) (S3 u)
    have h2 := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u)))
    linarith
  have hpR := pair_R2c_good sys hL hn H hKernel Hunit hPeriodic hlH hu φ
  have hpM := pair_Z2mV_good sys hL hn H hKernel Hunit hPeriodic hs hs1 hK1 hK2 hΛ hu φ
  have hpS := pair_S3V_good sys hL Hunit hPeriodic S3 u hβ φ
  have hA3' : FSConj.cm S3 (Akin sys L n) =
      -(FSConj.cm (Z2b sys L n) (VN sys L n) + H3first sys hL hn H - R3) := hA3
  have key := FSConj.norm_inner_ledger_le (dHc_eq sys hL hn H hKernel)
    (cm_Z2_A sys hL hn H hKernel) hA3' (Z2_skew sys hL hn H hKernel) hS3 u φ
    (ledD sys L Hunit n s z3 β M ‖φ‖ ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ‖
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) s φ‖)
    hz hz3 hv0 hd0 hg0 ha0 hzb hzu hz3u hvu hdu hgu hhfu hR3 hd4u huM hZbu le_rfl hpR hpM hpS
  exact key.trans (le_of_eq (ledD_bound sys Hunit s z3 β M _ _ _ _))

end LedgerGood

end FSNormal
