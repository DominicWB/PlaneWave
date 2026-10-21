import PlaneWave.Source.TrajectoryBudgets

/-!
# Flux/source build, block 5: the retained comparison with explicit constants

* nonnegativity of the ledger coefficients and the monotone, homogeneous form of the ledger bound
  (`ledK_le`);
* the backward flows of the datum `e^{iH'τ} A_{p₀}^E w` of a good `w`: `‖φ‖ ≤ M`,
  `‖ℰ^{1/4} φ‖ ≤ φ_{1/4} M` (`lem:quarter-flow`), `‖ℰ^σ φ‖ ≤ φ_σ M` (`lem:retflow` and
  `cor:spectail`) (`flow_datum_bounds`);
* **`T1_explicit`**: the retained comparison
  `|⟪χ(t), Oχ(t)⟫ - ⟪ψ_N(t), Oψ_N(t)⟫| ≤ Ξ² (δ_rot (m_χ + m_rot) + t m_rot m_w L + δ_r (m_r + m_N))`
  with the ledger constant `L = ledK(1, φ_{1/4}, φ_{1/2}, φ_s)`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Nonnegativity of the ledger coefficients -/

section Nonneg

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)

include hL in
lemma CSg_nonneg : 0 ≤ CSg sys L := by
  unfold CSg
  have hc := chbT_nonneg (sys := sys) hL
  have hg := gF_pos hL
  have hZ := FSChannel.Zs_pos (by norm_num : (3 / 2 : ℝ) < 2)
  have hcE := one_le_cE sys (L := L)
  have hc0 := c0_pos hL
  refine mul_nonneg hc (Finset.sum_nonneg fun j _ => ?_)
  have := muCh_pos sys j
  positivity

include hL in
lemma CRes_nonneg : 0 ≤ CRes sys L n := by
  unfold CRes
  have hc := chbT_nonneg (sys := sys) hL
  have hc0 := c0_pos hL
  positivity

include hL in
lemma zbC_nonneg : 0 ≤ zbC sys L n := by
  unfold zbC
  have := CS1_nonneg (sys := sys) hL
  positivity

omit [Fintype ν] in
include hL in
lemma hotF_nonneg' : 0 ≤ hotF eta L n := by
  unfold hotF
  have : 0 ≤ Kc L n / 4 := by
    rw [Kc_eq]; have := gF_pos hL; positivity
  have := Real.rpow_nonneg this (-(5 / 2 : ℝ))
  positivity

omit [Fintype ν] in
lemma highF_nonneg' : 0 ≤ highF sys L n := by
  unfold highF
  have := Real.rpow_nonneg (Real.sqrt_nonneg (2 * eH sys L n / eta)) (-(5 / 2 : ℝ))
  unfold lH
  positivity

include hL in
lemma z2C_nonneg (Hunit : ℝ) : 0 ≤ z2C sys L Hunit n := by
  unfold z2C
  have := zbC_nonneg sys hL (n := n)
  have := CHmix_nonneg sys hL Hunit (n := n)
  have := eH_nonneg sys (L := L) (n := n)
  positivity

include hL in
lemma z2uC_nonneg (Hunit s : ℝ) : 0 ≤ z2uC sys L Hunit n s := by
  unfold z2uC
  have := CSg_nonneg sys hL
  have := CZws_nonneg sys Hunit s (L := L) (n := n)
  have := CHmix_nonneg sys hL Hunit (n := n)
  have := eH_nonneg sys (L := L) (n := n)
  have := hotF_nonneg' (eta := eta) hL (n := n)
  positivity

include hL in
lemma guC_nonneg (Hunit : ℝ) : 0 ≤ guC sys L Hunit n := by
  unfold guC
  have := alphaBB_nonneg sys hL Hunit (n := n)
  have := alphaMix_nonneg sys hL Hunit (n := n)
  have := CRes_nonneg sys hL (n := n)
  have := CHmix_nonneg sys hL Hunit (n := n)
  have := highF_nonneg' sys (L := L) (n := n)
  positivity

include hL in
lemma r2aC_nonneg (Hunit s : ℝ) : 0 ≤ r2aC sys L Hunit n s := by
  unfold r2aC
  have := z2C_nonneg sys hL Hunit (n := n)
  have := guC_nonneg sys hL Hunit (n := n)
  have := z2uC_nonneg sys hL Hunit s (n := n)
  have := Amax_nonneg eta L n
  have := CVN_nonneg sys Hunit (L := L) (n := n)
  have := CDelta_nonneg sys hL Hunit (n := n)
  positivity

include hL in
lemma d2uC_nonneg (Hunit s : ℝ) : 0 ≤ d2uC sys L Hunit n s := by
  unfold d2uC
  have := z2C_nonneg sys hL Hunit (n := n)
  have := guC_nonneg sys hL Hunit (n := n)
  have := z2uC_nonneg sys hL Hunit s (n := n)
  have := r2aC_nonneg sys hL Hunit s (n := n)
  have := alphaD_nonneg sys hL Hunit (n := n)
  have := cvC_nonneg sys Hunit (L := L)
  have := CVN_nonneg sys Hunit (L := L) (n := n)
  have := CDelta_nonneg sys hL Hunit (n := n)
  positivity

include hL in
lemma d2oC_nonneg (Hunit : ℝ) : 0 ≤ d2oC sys L Hunit n := by
  unfold d2oC
  have := z2C_nonneg sys hL Hunit (n := n)
  have := Amax_nonneg eta L n
  have := CVN_nonneg sys Hunit (L := L) (n := n)
  have := CDelta_nonneg sys hL Hunit (n := n)
  positivity

include hL in
lemma h3guC_nonneg (Hunit : ℝ) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ h3guC sys L Hunit n β := by
  unfold h3guC
  have := zbC_nonneg sys hL (n := n)
  have := cvC_nonneg sys Hunit (L := L)
  have := CVN_nonneg sys Hunit (L := L) (n := n)
  have := CSg_nonneg sys hL
  have := alpha3_nonneg sys hL Hunit (n := n)
  positivity

include hL in
lemma r2bC_nonneg (Hunit : ℝ) {z3 β : ℝ} (hz3 : 0 ≤ z3) (hβ : 0 ≤ β) :
    0 ≤ r2bC sys L Hunit n z3 β := by
  unfold r2bC
  have := h3guC_nonneg sys hL Hunit (n := n) hβ
  have := Amax_nonneg eta L n
  have := CVN_nonneg sys Hunit (L := L) (n := n)
  have := d2oC_nonneg sys hL Hunit (n := n)
  positivity

include hL in
lemma k0C_nonneg (Hunit s : ℝ) {z3 β : ℝ} (hz3 : 0 ≤ z3) (hβ : 0 ≤ β) :
    0 ≤ k0C sys L Hunit n s z3 β := by
  unfold k0C
  have := CRes_nonneg sys hL (n := n)
  have := alpha4_nonneg sys hL Hunit (n := n)
  have := CVN_nonneg sys Hunit (L := L) (n := n)
  have := CHmix_nonneg sys hL Hunit (n := n)
  have := eH_nonneg sys (L := L) (n := n)
  have := hotF_nonneg' (eta := eta) hL (n := n)
  have := z2C_nonneg sys hL Hunit (n := n)
  have := alphaD_nonneg sys hL Hunit (n := n)
  have := CDelta_nonneg sys hL Hunit (n := n)
  have := z2uC_nonneg sys hL Hunit s (n := n)
  have := r2aC_nonneg sys hL Hunit s (n := n)
  have := d2uC_nonneg sys hL Hunit s (n := n)
  have := d2oC_nonneg sys hL Hunit (n := n)
  have := r2bC_nonneg sys hL Hunit (n := n) hz3 hβ
  positivity

include hL in
lemma k14C_nonneg (Hunit s : ℝ) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ k14C sys L Hunit n s β := by
  unfold k14C
  have := CHmix_nonneg sys hL Hunit (n := n)
  have := highF_nonneg' sys (L := L) (n := n)
  have := eH_nonneg sys (L := L) (n := n)
  have := CZws_nonneg sys Hunit s (L := L) (n := n)
  have : 0 ≤ wsC sys L Hunit n s := Real.sqrt_nonneg _
  have := cvC_nonneg sys Hunit (L := L)
  have : 0 ≤ (1 + eH sys L n) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  positivity

lemma k12C_nonneg (Hunit s : ℝ) : 0 ≤ k12C sys L Hunit n s := by
  unfold k12C
  have := CZws_nonneg sys Hunit s (L := L) (n := n)
  have := eH_nonneg sys (L := L) (n := n)
  have := cvC_nonneg sys Hunit (L := L)
  positivity

include hL in
lemma ksC_nonneg (Hunit s : ℝ) : 0 ≤ ksC sys L Hunit n s := by
  unfold ksC
  have := CtW_nonneg sys hL Hunit zero_le_one
  have := CZws_nonneg sys Hunit s (L := L) (n := n)
  have := eH_nonneg sys (L := L) (n := n)
  have := sys.one_le_maxMass
  have h0 : 0 ≤ Kc L n / 4 := by rw [Kc_eq]; have := gF_pos hL; positivity
  have := Real.rpow_nonneg h0 (-(1 / 2 : ℝ))
  positivity

include hL in
/-- **The ledger bound is monotone and homogeneous in the norms of `φ`.** -/
lemma ledK_le (Hunit s : ℝ) {z3 β : ℝ} (hz3 : 0 ≤ z3) (hβ : 0 ≤ β) {M f0 f14 f12 fs g14 g12 gs : ℝ}
    (h0 : f0 ≤ M) (h14 : f14 ≤ M * g14) (h12 : f12 ≤ M * g12) (hs' : fs ≤ M * gs) :
    ledK sys L Hunit n s z3 β f0 f14 f12 fs ≤ M * ledK sys L Hunit n s z3 β 1 g14 g12 gs := by
  unfold ledK
  have k0 := mul_le_mul_of_nonneg_left h0 (k0C_nonneg sys hL Hunit s (n := n) hz3 hβ)
  have k1 := mul_le_mul_of_nonneg_left h14 (k14C_nonneg sys hL Hunit s (n := n) hβ)
  have k2 := mul_le_mul_of_nonneg_left h12 (k12C_nonneg sys Hunit s (L := L) (n := n))
  have k3 := mul_le_mul_of_nonneg_left hs' (ksC_nonneg sys hL Hunit s (n := n))
  have e : M * (k0C sys L Hunit n s z3 β * 1 + k14C sys L Hunit n s β * g14 +
      k12C sys L Hunit n s * g12 + ksC sys L Hunit n s * gs) =
      k0C sys L Hunit n s z3 β * M + k14C sys L Hunit n s β * (M * g14) +
        k12C sys L Hunit n s * (M * g12) + ksC sys L Hunit n s * (M * gs) := by ring
  rw [e]; linarith

end Nonneg

/-! ## The flows of the datum -/

section Flow

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ}

/-- The dyadic exponent `N` with `Λ ≤ 2^N`. -/
noncomputable def NL (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℕ := Nat.log 2 ⌈Lam sys L n⌉₊ + 1

omit [Fintype ν] in
lemma Lam_le_two_pow : Lam sys L n ≤ (2 : ℝ) ^ NL sys L n := by
  have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌈Lam sys L n⌉₊
  have h2 : (⌈Lam sys L n⌉₊ : ℝ) < ((2 ^ (Nat.log 2 ⌈Lam sys L n⌉₊).succ : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h3 := Nat.le_ceil (Lam sys L n)
  unfold NL
  rw [Nat.succ_eq_add_one] at h2
  push_cast at h2
  linarith

/-- The quarter-flow constant `φ_{1/4}`. -/
noncomputable def phi14C (sys : CoulombSystem eta ν) (L Hunit CΔ : ℝ) (N : ℕ) : ℝ :=
  Crev sys L Hunit CΔ ^ (1 / 4 : ℝ) * (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ (1 / 4 : ℝ) *
    Real.sqrt ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * (1 + 2 * eta * N))

/-- The weighted-flow constant `φ_σ = C_fl(σ) (C_{σ+1} Λ^{4σ-1})^{1/2}`. -/
noncomputable def phiSC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (CΔ σ : ℝ) : ℝ :=
  CflS sys L Hunit CΔ σ * Real.sqrt (momentConst eta (σ + 1) * Lam sys L n ^ (4 * σ - 1))

include hL in
/-- **The backward flows of the datum of a good state.** -/
theorem flow_datum_bounds (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) (hΛ : 1 ≤ Lam sys L n) (p₀ : Fin eta) {M : ℝ}
    (w : En eta n) (hw : IsGood sys L 1 M w) (τ : ℝ) {σ : ℝ} (hσ : 1 / 4 < σ) (hσ1 : σ ≤ 1) :
    ‖retFlow sys L n hΔsym τ (datum sys L p₀ w)‖ ≤ M ∧
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (retFlow sys L n hΔsym τ (datum sys L p₀ w))‖ ≤
        M * phi14C sys L Hunit CΔ (NL sys L n) ∧
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) σ (retFlow sys L n hΔsym τ (datum sys L p₀ w))‖ ≤
        M * phiSC sys L Hunit n CΔ σ := by
  have hM := good_nonneg hw
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_retFlow]
    exact (norm_datum_le sys L p₀ w).trans (theta_le_good sys hw)
  · refine (quarter_flow sys Hunit hL hPeriodic hΔsym hCΔ hΔb (Lam_le_two_pow sys) p₀ w hw τ).trans
      (le_of_eq ?_)
    unfold phi14C
    have e : (1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * (1 * M) ^ 2 * (1 + 2 * eta * (NL sys L n : ℝ)) =
        M ^ 2 * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * (1 + 2 * eta * (NL sys L n : ℝ))) := by ring
    rw [e, Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]
    ring
  · have h1 := retflow sys Hunit hL hPeriodic hΔsym hCΔ hΔb (s := σ) ⟨by linarith, hσ1⟩ τ
      (datum sys L p₀ w)
    have h2 := wt_datum_sq_le sys L p₀ hL (Cg := 1) (Ξ := M) (by linarith) hσ hΛ w hw
    have h3 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) σ (datum sys L p₀ w)‖ ≤
        M * Real.sqrt (momentConst eta (σ + 1) * Lam sys L n ^ (4 * σ - 1)) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      refine (Real.sqrt_le_sqrt h2).trans (le_of_eq ?_)
      have e : momentConst eta (σ + 1) * (1 * M) ^ 2 * Lam sys L n ^ (4 * σ - 1) =
          M ^ 2 * (momentConst eta (σ + 1) * Lam sys L n ^ (4 * σ - 1)) := by ring
      rw [e, Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]
    refine h1.trans ?_
    have hc : 0 ≤ Crev sys L Hunit CΔ ^ σ * (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ σ :=
      CflS_nonneg sys Hunit hCΔ σ
    calc Crev sys L Hunit CΔ ^ σ * (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ σ *
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) σ (datum sys L p₀ w)‖
        ≤ Crev sys L Hunit CΔ ^ σ * (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ σ *
          (M * Real.sqrt (momentConst eta (σ + 1) * Lam sys L n ^ (4 * σ - 1))) :=
          mul_le_mul_of_nonneg_left h3 hc
      _ = M * phiSC sys L Hunit n CΔ σ := by unfold phiSC CflS; ring

end Flow

/-! ## The retained comparison with explicit constants -/

section T1

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- The budget of `w = χ'(t) + ψ_N^{r₀}(t)`. -/
noncomputable def mW (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s β : ℝ) : ℝ :=
  mRot sys L Hunit n s β + mNr sys L Hunit n s β

/-- The ledger constant against the Galerkin flow of the datum. -/
noncomputable def ledC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s z3 β : ℝ) : ℝ :=
  ledK sys L Hunit n s z3 β 1 (phi14C sys L Hunit 0 (NL sys L n)) (phiSC sys L Hunit n 0 (1 / 2))
    (phiSC sys L Hunit n 0 s)

/-- The constant of the retained comparison. -/
noncomputable def T1C (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s z3 β t : ℝ) : ℝ :=
  dRot sys L Hunit n s β * (mChi sys L Hunit n + mRot sys L Hunit n s β) +
    t * (mRot sys L Hunit n s β * (mW sys L Hunit n s β * ledC sys L Hunit n s z3 β)) +
    dR sys L Hunit n s β * (mNr sys L Hunit n s β + mN sys L Hunit n)

include hKernel in
/-- **The retained comparison** (`thm:src3`, first term, explicit). -/
theorem T1_explicit (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) {s : ℝ} (hs : 3 / 4 < s) (hs1 : s ≤ 1)
    (hK1 : 1 ≤ Kc L n / 4) (hK2 : 2 * gF L ≤ Kc L n / 4) (hlH : 1 ≤ lH sys L n)
    (hΛH : 1 ≤ Real.sqrt (2 * mmax sys * eH sys L n)) (hΛ : 1 ≤ Lam sys L n)
    (S3 R3 : En eta n →L[ℂ] En eta n) (hS3 : S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n))
    (hA3 : FSConj.cm S3 (Akin sys L n) = -(H3ret sys hL hn H - R3))
    {z3 β : ℝ} (hz3 : ‖S3‖ ≤ z3) (hβ0 : 0 ≤ β)
    (hβ : ∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u →
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤ β * M)
    (hR3 : ∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u → ‖R3 u‖ ≤ β * M)
    (p₀ : Fin eta) (D : EvoData L H) {t : ℝ} (ht : 0 ≤ t) :
    ‖⟪retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) (aT sys hL hn D.U D.u₀ 0),
        datum sys L p₀ (retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) (aT sys hL hn D.U D.u₀ 0))⟫_ℂ -
      ⟪retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀)),
        datum sys L p₀ (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀)))⟫_ℂ‖ ≤
      D.Xi ^ 2 * T1C sys L Hunit n s z3 β t := by
  have hΞ := D.Xi_nonneg
  have hz30 : 0 ≤ z3 := le_trans (norm_nonneg _) hz3
  set χ₀ := aT sys hL hn D.U D.u₀ 0
  set h0 := zero_isSymmetric (n := n)
  -- the budgets at time `t`
  obtain ⟨hdt, hgt⟩ := rot_good sys hL hn H hKernel Hunit hPeriodic hKg hs hs1 hK1 S3 hS3 hβ D t
  have hχt := chi_good sys hL hn H hKernel Hunit hPeriodic hKg D (-t)
  obtain ⟨hdr, hgr⟩ := psiNr_good sys hL hn H hKernel Hunit hPeriodic hKg hs hs1 hK1 S3 hS3 hβ D (-t)
  have hgN := psiN_good sys hL H hKernel Hunit hPeriodic hKg (n := n) D (-t)
  have hw := isGood_add sys hgt hgr
  have hmRot := good_nonneg hgt
  -- the integrand
  set B := mRot sys L Hunit n s β * D.Xi * (mW sys L Hunit n s β * D.Xi * ledC sys L Hunit n s z3 β)
  have hB : ∀ s' ∈ Set.Icc (0 : ℝ) t,
      ‖⟪(Hpp sys hL hn H S3 - (Akin sys L n + VN sys L n)) (rotT sys hL hn H hKernel S3 χ₀ s'),
        retFlow sys L n h0 (t - s')
          (datum sys L p₀ (rotT sys hL hn H hKernel S3 χ₀ t +
            retFlow sys L n h0 (-t) (Urot sys hL hn H S3 χ₀)))⟫_ℂ‖ ≤ B := by
    intro s' _
    obtain ⟨-, hgs⟩ := rot_good sys hL hn H hKernel Hunit hPeriodic hKg hs hs1 hK1 S3 hS3 hβ D s'
    set φ := retFlow sys L n h0 (t - s')
      (datum sys L p₀ (rotT sys hL hn H hKernel S3 χ₀ t + retFlow sys L n h0 (-t) (Urot sys hL hn H S3 χ₀)))
    have key := norm_inner_Hpp_good sys hL hn H hKernel Hunit hPeriodic hs hs1 hK1 hK2 hlH hΛH S3 R3 hS3
      hA3 hz3 _ hgs (hβ _ _ hgs) (hR3 _ _ hgs) φ
    have hφ := flow_datum_bounds sys hL Hunit hPeriodic h0 le_rfl (fun v => by simp) hΛ p₀ _ hw (t - s')
      (σ := 1 / 2) (by norm_num) (by norm_num)
    have hφs := flow_datum_bounds sys hL Hunit hPeriodic h0 le_rfl (fun v => by simp) hΛ p₀ _ hw (t - s')
      (σ := s) (by linarith) hs1
    have hW : mRot sys L Hunit n s β * D.Xi + mNr sys L Hunit n s β * D.Xi =
        mW sys L Hunit n s β * D.Xi := by unfold mW; ring
    rw [hW] at hφ hφs
    have hl := ledK_le sys hL Hunit s (n := n) hz30 hβ0 hφ.1 hφ.2.1 hφ.2.2 hφs.2.2
    refine key.trans ?_
    exact mul_le_mul_of_nonneg_left hl hmRot
  have h := T1_le sys hL hn H hKernel S3 p₀ χ₀ (ext eta n (Sm eta L D.u₀)) ht hB
  refine h.trans ?_
  have k1 : ‖rotT sys hL hn H hKernel S3 χ₀ t - retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) χ₀‖ *
      (‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) χ₀)‖ +
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (rotT sys hL hn H hKernel S3 χ₀ t)‖) ≤
      dRot sys L Hunit n s β * D.Xi * (mChi sys L Hunit n * D.Xi + mRot sys L Hunit n s β * D.Xi) :=
    mul_le_mul hdt (add_le_add (theta_le_good sys hχt) (theta_le_good sys hgt))
      (by positivity) (le_trans (norm_nonneg _) hdt)
  have k3 : ‖Urot sys hL hn H S3 χ₀ - ext eta n (Sm eta L D.u₀)‖ *
      (‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (retFlow sys L n h0 (-t) (Urot sys hL hn H S3 χ₀))‖ +
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (retFlow sys L n h0 (-t) (ext eta n (Sm eta L D.u₀)))‖) ≤
      dR sys L Hunit n s β * D.Xi * (mNr sys L Hunit n s β * D.Xi + mN sys L Hunit n * D.Xi) :=
    mul_le_mul hdr (add_le_add (theta_le_good sys hgr) (theta_le_good sys hgN))
      (by positivity) (le_trans (norm_nonneg _) hdr)
  have e : D.Xi ^ 2 * T1C sys L Hunit n s z3 β t =
      dRot sys L Hunit n s β * D.Xi * (mChi sys L Hunit n * D.Xi + mRot sys L Hunit n s β * D.Xi) +
        t * B +
        dR sys L Hunit n s β * D.Xi * (mNr sys L Hunit n s β * D.Xi + mN sys L Hunit n * D.Xi) := by
    simp only [B]; unfold T1C; ring
  rw [e]
  linarith

end T1

end FSNormal
