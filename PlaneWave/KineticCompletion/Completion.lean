import PlaneWave.KineticCompletion.QuarterPowerWeights

/-!
# Kinetic completion, part 5: the completion and the unconditional theorems

**`completion`** (`thm:completion` of the completion note): there are fixed constants `C₃ ≥ 0`,
`q` and a threshold `N₁` such that for every cutoff `n ≥ N₁` the same-channel generator
`Σ₃ = Σ₃^sp` and the residual `R₃ = H₃^{res,sp} + H₃^mp` satisfy every completion hypothesis of
`FSAsymp.thm_src3`: skew-adjointness, the homological equation `[Σ₃, A] = -(H₃^ret - R₃)`,
`‖Σ₃‖ ≤ C₃ log^q(2+K)/K²`, and on good states the weighted bound and the residual bound with
`C₃ log^q(2+K)/K³`. The constants are `O(n⁻³ log^q n)`: `C_Σ3`, `C_R3` (`PlaneWave.SamePair.Package`), `C_X`, `C_Y`
(the multi-channel residual, `PlaneWave.KineticCompletion.CrossCommutators`, `PlaneWave.KineticCompletion.FirstRotationWords`) and `C_W` (the weighted bound, `PlaneWave.KineticCompletion.QuarterPowerWeights`).

Hence the **unconditional** forms of `thm:src3` and `cor:stopping3`, with and without spin
(`thm_src3_uncond`, `cor_stopping3_uncond`, `FSSpin.thm_src3_spin_uncond`,
`FSSpin.cor_stopping3_spin_uncond`): for every `ε > 0` there are `C_ε` and `N₀` such that for every
cutoff `n ≥ N₀`, every datum and every `t ≥ 1` (every window `T ≥ 1`), the kinetic-energy
(stopping-power) error is at most `C_ε Ξ² (1 + t) K^{-3+ε}` (`C_ε Ξ²/v_p (K^{-3+ε} + K^{-3+ε}/T)`),
with no further hypotheses.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace

namespace FSAsymp

open FSNormal PL

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ}

/-! ## Orders of the new constants -/

theorem pl_inv_pow (c : ℝ) (m : ℕ) : PL (fun n => c / (n : ℝ) ^ m) (-(m : ℝ)) :=
  (cnpow c (-(m : ℝ))).congr ⟨1, fun n _ => by
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_natCast, div_eq_mul_inv]⟩

theorem pl_CZd (heta : 0 < eta) (j : Ch eta) : PL (fun n => CZd sys L n j) (-3) := by
  have h1 := pl_inv3 (chbT sys L * (2 * muCh sys j / gF L ^ 2))
  have h2 := (((pl_Jn sys heta).add' (const 3)).pow 2).const_mul (FSLattice.CD + 44000)
  refine ((h1.mul h2).mono (by norm_num)).congr ⟨0, fun n _ => ?_⟩
  unfold CZd
  ring

theorem pl_kcCX (heta : 0 < eta) (Hunit : ℝ) : PL (fun n => kcCX sys L n Hunit) (-3) := by
  unfold kcCX
  refine PL.sum _ fun j _ => PL.sum _ fun k _ => ?_
  exact ((((pl_CZd sys (L := L) heta j).mul_const (chC sys L k)).add
    ((pl_CZd sys (L := L) heta k).const_mul (chC sys L j))).mul_const (|Hunit|)).mul_const
      (cLam sys L)

theorem pl_alS (l : Ch eta) : PL (fun n => alS sys L n l) (-3) := by
  have h1 := pl_inv_pow (chC sys L l / cgap sys (gF L) * (256 / 81)) 4
  have h2 : PL (fun n => 1 + 13 * (n : ℝ)) 1 :=
    ((const 1).add' (lin 13)).mono (by norm_num)
  refine ((h1.mul h2).mono (by norm_num)).congr ⟨1, fun n hn => ?_⟩
  unfold alS
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  field_simp
  ring

theorem pl_bW (Hunit : ℝ) (j k l : Ch eta) :
    PL (fun n => bW sys L n Hunit j k l) (-3) := by
  have hs : ∀ m : Ch eta, PL (fun n => Real.sqrt (alS sys L n m * Asj sys L n m)) (-2) := fun m =>
    (((pl_alS sys (L := L) m).mul (pl_Asj sys (L := L) m)).sqrt).mono (by norm_num)
  have t1 := ((((pl_Asj sys (L := L) j).mul_const (chC sys L k * |Hunit|)).mul (hs l)).mono
    (by norm_num : (-1 : ℝ) + -2 ≤ -3))
  have t2 := ((((pl_Asj sys (L := L) j).mul (hs j)).mul_const (chC sys L l * |Hunit|)).mono
    (by norm_num : (-1 : ℝ) + -2 ≤ -3))
  have t3 := ((((pl_Asj sys (L := L) k).const_mul (chC sys L j * |Hunit|)).mul (hs k)).mono
    (by norm_num : (-1 : ℝ) + -2 ≤ -3))
  refine (((t1.add t2).add t3).mul_const (cLam sys L)).congr ⟨0, fun n _ => ?_⟩
  unfold bW
  ring

theorem pl_kcCY (Hunit : ℝ) : PL (fun n => kcCY sys L n Hunit) (-3) := by
  unfold kcCY
  exact PL.sum _ fun j _ => PL.sum _ fun k _ => PL.sum _ fun l _ =>
    pl_bW sys (L := L) Hunit j k l

theorem pl_farC (heta : 0 < eta) (j : Ch eta) : PL (fun n => farC sys L n j) (-3) := by
  have h := (((pl_Bh3 sys (L := L) heta j).const_mul (4 / 3)).mul
    ((pl_Jn sys heta).add' (const 4))).mono (by norm_num : (-3 : ℝ) + max 0 0 ≤ -3)
  refine (h.mul_const (Real.sqrt (8 * (gF L ^ 2 / (2 * muCh sys j))) *
    (7 * (1 + 1 / (gF L ^ 2 / (2 * muCh sys j))) *
      (27 + 13 / Real.sqrt (gF L ^ 2 / (2 * muCh sys j)))))).congr ⟨0, fun n _ => ?_⟩
  unfold farC
  ring

theorem pl_CW (heta : 0 < eta) : PL (fun n => CW sys L n) (-3) := by
  unfold CW
  exact ((pl_CS3 sys (L := L) heta).const_mul 5).add
    (PL.sum _ fun j _ => pl_farC sys (L := L) heta j)

/-! ## From power-polylog bounds to the hypothesis scales `C₃ log^q(2+K)/K^m` -/

omit [Fintype ν] in
lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  linarith

omit [Fintype ν] in
lemma one_le_log_two_add {K : ℝ} (hK : 2 ≤ K) : 1 ≤ Real.log (2 + K) := by
  have h4 : Real.log 4 ≤ Real.log (2 + K) := Real.log_le_log (by norm_num) (by linarith)
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have := half_le_log_two
  linarith

omit [Fintype ν] in
/-- Monotonicity of the hypothesis scales in `C₃` and `q` once `K ≥ 2`. -/
lemma logK_mono {K : ℝ} (hK : 2 ≤ K) {C C' : ℝ} (hC : 0 ≤ C) (hCC : C ≤ C') {q q' : ℕ}
    (hq : q ≤ q') (m : ℕ) :
    C * Real.log (2 + K) ^ q / K ^ m ≤ C' * Real.log (2 + K) ^ q' / K ^ m := by
  have hl := one_le_log_two_add hK
  have h1 : Real.log (2 + K) ^ q ≤ Real.log (2 + K) ^ q' := pow_le_pow_right₀ hl hq
  have h0 : 0 ≤ Real.log (2 + K) ^ q := pow_nonneg (by linarith) q
  have hKm : 0 < K ^ m := pow_pos (by linarith) m
  exact div_le_div_of_nonneg_right (mul_le_mul hCC h1 h0 (hC.trans hCC)) hKm.le

omit [Fintype ν] in
/-- **Power-polylog bounds in the hypothesis scale**: `f ∈ PL(-m)` gives
`|f(n)| ≤ C₃ log^q(2+K)/K^m` for all large `n`, with `q = ⌈k⌉` (`ℓ(n) ≤ 4 log(2+K)` once
`g² n ≥ 1`). -/
theorem exists_logK_bound (hL : 0 < L) {f : ℕ → ℝ} (m : ℕ) (hf : PL f (-(m : ℝ))) :
    ∃ C3 : ℝ, 0 ≤ C3 ∧ ∃ q : ℕ, ∃ N : ℕ, ∀ n, N ≤ n →
      |f n| ≤ C3 * Real.log (2 + Kc L n) ^ q / Kc L n ^ m := by
  obtain ⟨C, k, hC, hk, N, h⟩ := hf
  have hg := gL_pos hL
  refine ⟨C * 4 ^ ⌈k⌉₊ * gL L ^ m, by positivity, ⌈k⌉₊, max N (max 1 ⌈1 / gL L ^ 2⌉₊),
    fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hng : 1 / gL L ^ 2 ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hK : Kc L n = gL L * n := rfl
  have hKpos : 0 < Kc L n := by rw [hK]; positivity
  -- `√n ≤ K`
  have hsq : Real.sqrt n ≤ Kc L n := by
    have h1 : 1 ≤ gL L ^ 2 * n := by
      rw [div_le_iff₀ (by positivity)] at hng
      linarith
    have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hgs : 1 ≤ gL L * Real.sqrt n := by
      have h2 : (1 : ℝ) ≤ (gL L * Real.sqrt n) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hn0.le]; exact h1
      nlinarith [mul_nonneg hg.le hs0]
    have e : gL L * (n : ℝ) = gL L * Real.sqrt n * Real.sqrt n := by rw [mul_assoc, hs]
    rw [hK, e]
    nlinarith [mul_le_mul_of_nonneg_right hgs hs0]
  -- `ℓ(n) ≤ 4 log(2 + K)`
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log (2 + Kc L n) := by
    have : Real.log 2 ≤ Real.log (2 + Kc L n) := Real.log_le_log (by norm_num) (by linarith)
    have := half_le_log_two
    linarith
  have hlogn : Real.log n ≤ 2 * Real.log (2 + Kc L n) := by
    have h1 : Real.log (Real.sqrt n) ≤ Real.log (2 + Kc L n) :=
      Real.log_le_log (Real.sqrt_pos.mpr hn0) (by linarith)
    rw [Real.log_sqrt hn0.le] at h1
    linarith
  have hell : ell n ≤ 4 * Real.log (2 + Kc L n) := by unfold ell; linarith
  have hellk : ell n ^ k ≤ (4 * Real.log (2 + Kc L n)) ^ ⌈k⌉₊ := by
    calc ell n ^ k ≤ ell n ^ (⌈k⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_ell hn1) (Nat.le_ceil k)
      _ = ell n ^ ⌈k⌉₊ := Real.rpow_natCast _ _
      _ ≤ (4 * Real.log (2 + Kc L n)) ^ ⌈k⌉₊ := pow_le_pow_left₀ (ell_pos hn1).le hell _
  -- `n^{-m} = g^m / K^m`
  have hnp : (n : ℝ) ^ (-(m : ℝ)) = gL L ^ m / Kc L n ^ m := by
    rw [Real.rpow_neg hn0.le, Real.rpow_natCast, hK, mul_pow]
    field_simp
  refine (h n hnN).trans ?_
  rw [hnp]
  have hc0 : 0 ≤ C * (gL L ^ m / Kc L n ^ m) := by positivity
  calc C * (gL L ^ m / Kc L n ^ m) * ell n ^ k ≤
        C * (gL L ^ m / Kc L n ^ m) * (4 * Real.log (2 + Kc L n)) ^ ⌈k⌉₊ :=
        mul_le_mul_of_nonneg_left hellk hc0
    _ = C * 4 ^ ⌈k⌉₊ * gL L ^ m * Real.log (2 + Kc L n) ^ ⌈k⌉₊ / Kc L n ^ m := by
        rw [mul_pow]; ring

lemma kcCY_nonneg {n : ℕ} (hL : 0 < L) (Hunit : ℝ) : 0 ≤ kcCY sys L n Hunit := by
  unfold kcCY
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => ?_
  obtain ⟨h1, h2, h3⟩ := bW_terms_nonneg (sys := sys) (n := n) hL Hunit j k l
  unfold bW
  exact mul_nonneg (by linarith) (cLam_pos (sys := sys) L).le

/-! ## The completion -/

/-- **The completion** (`thm:completion`): the same-channel generator `Σ₃ = Σ₃^sp` and the
residual `R₃ = H₃^{res,sp} + H₃^mp` satisfy all completion hypotheses of `thm_src3`, with fixed
`C₃`, `q` and every cutoff `n ≥ N₁`. -/
theorem completion (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (heta : 0 < eta) :
    ∃ C3 : ℝ, 0 ≤ C3 ∧ ∃ q : ℕ, ∃ N₁ : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N₁ ≤ n →
      ∃ S3 R3 : En eta n →L[ℂ] En eta n, S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n) ∧
      FSConj.cm S3 (Akin sys L n) = -(H3ret sys hL hn H - R3) ∧
      ‖S3‖ ≤ z3F L C3 q n ∧
      (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u →
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤ betaF L C3 q n * M) ∧
      (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u → ‖R3 u‖ ≤ betaF L C3 q n * M) := by
  set cM := Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit + 1 with hcM
  obtain ⟨Ca, hCa, qa, Na, ha⟩ := exists_logK_bound hL 2
    ((pl_CS3 sys (L := L) heta).mono (by norm_num : (-3 : ℝ) ≤ -((2 : ℕ) : ℝ)))
  obtain ⟨Cb, hCb, qb, Nb, hb⟩ := exists_logK_bound hL 3
    (((pl_CW sys (L := L) heta).mul_const cM).mono (by norm_num : (-3 : ℝ) ≤ -((3 : ℕ) : ℝ)))
  obtain ⟨Cc, hCc, qc, Nc, hc⟩ := exists_logK_bound hL 3
    (((pl_CR3 sys (L := L) heta).add ((pl_kcCX sys (L := L) heta Hunit).add
      (pl_kcCY sys (L := L) Hunit))).mono (by norm_num : (-3 : ℝ) ≤ -((3 : ℕ) : ℝ)))
  have hg := gL_pos hL
  refine ⟨max Ca (max Cb Cc), le_max_of_le_left hCa, max qa (max qb qc),
    max (max Na (max Nb Nc)) ⌈2 / gL L⌉₊, fun n hn hN => ?_⟩
  have hNa : Na ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : Nb ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hN
  have hNc : Nc ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hN
  have hK2 : 2 ≤ Kc L n := by
    have h1 : 2 / gL L ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
    rw [div_le_iff₀ hg] at h1
    calc (2 : ℝ) ≤ n * gL L := h1
      _ = Kc L n := by rw [Kc, mul_comm]
  obtain ⟨hdec, -, hskew, hcomm, hS, hR⟩ := same_pair_package sys hL hn H hKernel
  -- the three scales
  have hza : CS3 sys L n ≤ z3F L (max Ca (max Cb Cc)) (max qa (max qb qc)) n :=
    (le_abs_self _).trans ((ha n hNa).trans
      (logK_mono hK2 hCa (le_max_left _ _) (le_max_left _ _) 2))
  have hzb : CW sys L n * cM ≤ betaF L (max Ca (max Cb Cc)) (max qa (max qb qc)) n :=
    (le_abs_self _).trans ((hb n hNb).trans
      (logK_mono hK2 hCb ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_left _ _).trans (le_max_right _ _)) 3))
  have hzc : CR3 sys L n + (kcCX sys L n Hunit + kcCY sys L n Hunit) ≤
      betaF L (max Ca (max Cb Cc)) (max qa (max qb qc)) n :=
    (le_abs_self _).trans ((hc n hNc).trans
      (logK_mono hK2 hCc ((le_max_right _ _).trans (le_max_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _)) 3))
  refine ⟨toC (Sig3sp sys L n), toC (H3resSp sys L n + H3mp sys L n), ?_, ?_, ?_, ?_, ?_⟩
  · -- skew-adjointness
    refine mem_skewAdjoint_of_inner _ fun u v => ?_
    simp only [toC, LinearMap.coe_toContinuousLinearMap']
    exact hskew u v
  · -- the homological equation
    ext1 u
    have h1 := LinearMap.congr_fun hcomm u
    have h2 := LinearMap.congr_fun hdec u
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.add_apply,
      ContinuousLinearMap.coe_coe] at h1 h2
    simp only [FSConj.cm, Akin, toC, sub_apply, mul_apply_eq_comp, neg_apply,
      LinearMap.coe_toContinuousLinearMap', LinearMap.add_apply]
    rw [h1, h2]
    abel
  · -- `‖Σ₃‖ ≤ z₃`
    refine le_trans (ContinuousLinearMap.opNorm_le_bound _ (CS3_nonneg (sys := sys) (n := n) hL)
      fun u => ?_) hza
    simp only [toC, LinearMap.coe_toContinuousLinearMap']
    exact hS u
  · -- the weighted bound
    intro M u hu
    have hM := good_nonneg hu
    simp only [toC, LinearMap.coe_toContinuousLinearMap']
    exact (weighted_Sig3sp_good hL hn Hunit hPeriodic hu).trans
      (mul_le_mul_of_nonneg_right hzb hM)
  · -- the residual bound
    intro M u hu
    have hM := good_nonneg hu
    have hw1 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ≤ M := by
      have := hu.1
      have := norm_nonneg u
      linarith
    have h1 := hR M u hu
    have h2 := norm_H3mp_le (sys := sys) hL hn Hunit hPeriodic u
    have hX := kcCX_nonneg (sys := sys) (n := n) hL Hunit
    have hY := kcCY_nonneg sys (n := n) hL Hunit
    simp only [toC, LinearMap.coe_toContinuousLinearMap', LinearMap.add_apply]
    calc ‖H3resSp sys L n u + H3mp sys L n u‖ ≤ ‖H3resSp sys L n u‖ + ‖H3mp sys L n u‖ :=
          norm_add_le _ _
      _ ≤ CR3 sys L n * M + (kcCX sys L n Hunit + kcCY sys L n Hunit) * M :=
          add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hw1 (by positivity)))
      _ = (CR3 sys L n + (kcCX sys L n Hunit + kcCY sys L n Hunit)) * M := by ring
      _ ≤ betaF L (max Ca (max Cb Cc)) (max qa (max qb qc)) n * M :=
          mul_le_mul_of_nonneg_right hzc hM

/-! ## The unconditional theorems -/

section Uncond

variable {sys} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hL hKernel in
/-- **`thm:src3`** (unconditional): the kinetic energy at the cubic rate,
`|⟨ψ(t), A_{p₀} ψ(t)⟩ - ⟨ψ_N(t), A_{p₀} ψ_N(t)⟩| ≤ C_ε Ξ² (1 + t) K^{-3+ε}` for all `t ≥ 1` and
all cutoffs `n ≥ N₀`. -/
theorem thm_src3_uncond (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : EvoData L H) (t : ℝ), 1 ≤ t →
      |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
        (regKin sys (gF L) p₀).expect (emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-t)
          (ext eta n (Sm eta L D.u₀))))| ≤ C * D.Xi ^ 2 * (1 + t) * Kc L n ^ (-3 + ε) := by
  have heta : 0 < eta := Fin.pos p₀
  obtain ⟨C3, hC3, q, N₁, hcomp⟩ := completion sys hL H hKernel Hunit hPeriodic heta
  obtain ⟨C, hC, N₀, h⟩ := thm_src3 sys hL H hKernel Hunit hPeriodic p₀ hε hC3 q
  refine ⟨C, hC, max (max N₀ N₁) 2, fun n hN D t ht => ?_⟩
  have hn : 2 ≤ n := le_trans (le_max_right _ _) hN
  obtain ⟨S3, R3, h1, h2, h3, h4, h5⟩ :=
    hcomp n hn (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  exact h n hn (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) S3 R3 h1 h2 h3 h4 h5
    D t ht

include hL hKernel in
/-- **`cor:stopping3`** (unconditional): the secant estimator of the stopping power over a window
`T ≥ 1` deviates from its Galerkin counterpart by at most `C_ε Ξ²/v_p (K^{-3+ε} + K^{-3+ε}/T)`
for all cutoffs `n ≥ N₀`. -/
theorem cor_stopping3_uncond (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : EvoData L H) {vp T : ℝ}, 0 < vp → 1 ≤ T →
        let ψN : ℝ → L2 eta := fun s =>
          emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-s) (ext eta n (Sm eta L D.u₀)))
        |((regKin sys (gF L) p₀).expect (D.U T (Sm eta L D.u₀)) -
            (regKin sys (gF L) p₀).expect (D.U 0 (Sm eta L D.u₀))) / (vp * T) -
          ((regKin sys (gF L) p₀).expect (ψN T) - (regKin sys (gF L) p₀).expect (ψN 0)) / (vp * T)| ≤
          C * D.Xi ^ 2 / vp * (Kc L n ^ (-3 + ε) + Kc L n ^ (-3 + ε) / T) := by
  have heta : 0 < eta := Fin.pos p₀
  obtain ⟨C3, hC3, q, N₁, hcomp⟩ := completion sys hL H hKernel Hunit hPeriodic heta
  obtain ⟨C, hC, N₀, h⟩ := cor_stopping3 sys hL H hKernel Hunit hPeriodic p₀ hε hC3 q
  refine ⟨C, hC, max (max N₀ N₁) 2, fun n hN D vp T hvp hT => ?_⟩
  have hn : 2 ≤ n := le_trans (le_max_right _ _) hN
  obtain ⟨S3, R3, h1, h2, h3, h4, h5⟩ :=
    hcomp n hn (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  exact h n hn (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) S3 R3 h1 h2 h3 h4 h5
    D hvp hT

end Uncond

end FSAsymp

namespace FSSpin

open FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν] {S : Type} [Fintype S]

section SourceUncond

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hL hKernel in
/-- **`thm:src3` with spin** (unconditional):
`|⟨Ψ(t), A_{p₀} Ψ(t)⟩ - ⟨Ψ_N(t), A_{p₀} Ψ_N(t)⟩| ≤ C_ε Ξ_S² (1 + t) K^{-3+ε}` for every
spin-inclusive datum, every `t ≥ 1` and every cutoff `n ≥ N₀`. -/
theorem thm_src3_spin_uncond (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (Ds : S → EvoData L H) (t : ℝ), 1 ≤ t →
      |expectS (regKin sys (gF L) p₀) (exactS Ds t) -
          expectS (regKin sys (gF L) p₀) (galS sys n Ds t)| ≤
        C * XiS Ds ^ 2 * (1 + t) * Kc L n ^ (-3 + ε) := by
  have heta : 0 < eta := Fin.pos p₀
  obtain ⟨C3, hC3, q, N₁, hcomp⟩ := FSAsymp.completion sys hL H hKernel Hunit hPeriodic heta
  obtain ⟨C, hC, N₀, h⟩ := thm_src3_spin (S := S) sys hL H hKernel Hunit hPeriodic p₀ hε hC3 q
  refine ⟨C, hC, max (max N₀ N₁) 2, fun n hN Ds t ht => ?_⟩
  have hn : 2 ≤ n := le_trans (le_max_right _ _) hN
  obtain ⟨S3, R3, h1, h2, h3, h4, h5⟩ :=
    hcomp n hn (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  exact h n hn (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) S3 R3 h1 h2 h3 h4 h5
    Ds t ht

include hL hKernel in
/-- **`cor:stopping3` with spin** (unconditional): the secant-slope estimator of the stopping power
in the spin-inclusive state deviates from its Galerkin counterpart by at most
`C_ε Ξ_S²/v_p (K^{-3+ε} + K^{-3+ε}/T)` for every window `T ≥ 1` and every cutoff `n ≥ N₀`. -/
theorem cor_stopping3_spin_uncond (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (p₀ : Fin eta) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (Ds : S → EvoData L H) {vp T : ℝ}, 0 < vp →
      1 ≤ T →
        |(expectS (regKin sys (gF L) p₀) (exactS Ds T) -
              expectS (regKin sys (gF L) p₀) (exactS Ds 0)) / (vp * T) -
            (expectS (regKin sys (gF L) p₀) (galS sys n Ds T) -
              expectS (regKin sys (gF L) p₀) (galS sys n Ds 0)) / (vp * T)| ≤
          C * XiS Ds ^ 2 / vp * (Kc L n ^ (-3 + ε) + Kc L n ^ (-3 + ε) / T) := by
  have heta : 0 < eta := Fin.pos p₀
  obtain ⟨C3, hC3, q, N₁, hcomp⟩ := FSAsymp.completion sys hL H hKernel Hunit hPeriodic heta
  obtain ⟨C, hC, N₀, h⟩ :=
    cor_stopping3_spin (S := S) sys hL H hKernel Hunit hPeriodic p₀ hε hC3 q
  refine ⟨C, hC, max (max N₀ N₁) 2, fun n hN Ds vp T hvp hT => ?_⟩
  have hn : 2 ≤ n := le_trans (le_max_right _ _) hN
  obtain ⟨S3, R3, h1, h2, h3, h4, h5⟩ :=
    hcomp n hn (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
  exact h n hn (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) S3 R3 h1 h2 h3 h4 h5
    Ds hvp hT

end SourceUncond

end FSSpin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **The data exist**: for every datum `u₀ ∈ D(H²)` (`H u₀ = S v₀`), the propagator of the
release's `exists_coulombFourierPropagator` gives `D : EvoData L H` with `D.u₀ = u₀`, `D.v₀ = v₀`.
So the theorems above apply to every datum in `D(H²)`. -/
theorem exists_evoData (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = Sm eta L v₀) :
    ∃ D : EvoData L H, D.u₀ = u₀ ∧ D.v₀ = v₀ := by
  obtain ⟨U, h0, -, hc, hg, hd, -⟩ := exists_coulombFourierPropagator sys L hL H hKernel
  exact ⟨⟨U, h0, hg, hd, hc, u₀, v₀, huv⟩, rfl, rfl⟩

end FSNormal
