import PlaneWave.Source.CutoffErrorConstant

/-!
# Flux/source build, block 5: `thm:src3` and `cor:stopping3` (conditional)

**`thm_src3`** (`thm:src3`, conditional analytic completion): for `0 < ε`, `C₃ ≥ 0`, `q ∈ ℕ` there
are `C` and `N₀` such that for every cutoff `n ≥ N₀`, every pair `(Σ₃, H₃^res)` on `ran P` with

* `Σ₃` skew-adjoint and `[Σ₃, A] = -(H₃^ret - H₃^res)` (`H₃^ret = [Σ₂^bb, W_N] + P H^{(3)} P`),
* `‖Σ₃‖ ≤ C₃ log^q(2+K)/K²`,
* eq:bulk-completion: `‖ℰ^{-1/4} Σ₃ W_N u‖ + ‖ℰ^{1/4} Σ₃ u‖ ≤ C₃ log^q(2+K)/K³ · M`, and
* `‖H₃^res u‖ ≤ C₃ log^q(2+K)/K³ · M`

for every good `u` (`IsGood 1 M u`), every datum `u₀ ∈ D(H²)` and every `t ≥ 1`:

  `|⟨ψ(t), A_{p₀} ψ(t)⟩ - ⟨ψ_N(t), A_{p₀} ψ_N(t)⟩| ≤ C Ξ² (1 + t) K^{-3+ε}`.

**`cor_stopping3`**: the secant estimator of the stopping power over `[0, T]`, `T ≥ 1`,
`|ΔŜ| ≤ (C Ξ²/v_p)(K^{-3+ε} + K^{-3+ε}/T)`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace

namespace FSAsymp

open FSNormal PL

/-! ## The hypothesis scales -/

/-- `z₃(n) = C₃ log^q(2+K)/K²`. -/
noncomputable def z3F (L C3 : ℝ) (q n : ℕ) : ℝ := C3 * Real.log (2 + Kc L n) ^ q / Kc L n ^ 2

/-- `β(n) = C₃ log^q(2+K)/K³`. -/
noncomputable def betaF (L C3 : ℝ) (q n : ℕ) : ℝ := C3 * Real.log (2 + Kc L n) ^ q / Kc L n ^ 3

theorem pl_logKc {L : ℝ} (hL : 0 < L) (q : ℕ) : PL (fun n => Real.log (2 + Kc L n) ^ q) 0 := by
  have h := (log_lin (a := 2) (b := gL L) (by norm_num) (gL_pos hL).le).pow q
  exact (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

theorem pl_z3F {L : ℝ} (hL : 0 < L) (C3 : ℝ) (q : ℕ) : PL (z3F L C3 q) (-2) := by
  have h := ((pl_logKc hL q).const_mul C3).mul (pl_Kc hL (-2))
  refine (h.congr ⟨1, fun n hn => ?_⟩).mono (by norm_num)
  have hK : 0 < Kc L n := by
    unfold Kc; have := gL_pos hL; have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  unfold z3F
  rw [Real.rpow_neg hK.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

theorem pl_betaF {L : ℝ} (hL : 0 < L) (C3 : ℝ) (q : ℕ) : PL (betaF L C3 q) (-3) := by
  have h := ((pl_logKc hL q).const_mul C3).mul (pl_Kc hL (-3))
  refine (h.congr ⟨1, fun n hn => ?_⟩).mono (by norm_num)
  have hK : 0 < Kc L n := by
    unfold Kc; have := gL_pos hL; have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  unfold betaF
  rw [Real.rpow_neg hK.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-! ## The scale conditions -/

lemma one_le_lin {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : ⌈1 / c⌉₊ ≤ n) : 1 ≤ c * n := by
  have h1 : 1 / c ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  calc (1 : ℝ) = c * (1 / c) := by field_simp
    _ ≤ c * n := mul_le_mul_of_nonneg_left h1 hc.le

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)

omit [Fintype ν] in
include hL in
lemma sqrt_eH_eq (n : ℕ) : Real.sqrt (2 * mmax sys * eH sys L n) =
    Real.sqrt (2 * mmax sys * (gF L ^ 2 / (64 * mtop sys))) * n := by
  have hg := gF_pos hL
  have hm : 0 < mmax sys := lt_of_lt_of_le one_pos (one_le_mmax sys)
  have hmt : 0 < mtop sys := lt_of_lt_of_le one_pos (one_le_mtop sys)
  have e : 2 * mmax sys * eH sys L n =
      (Real.sqrt (2 * mmax sys * (gF L ^ 2 / (64 * mtop sys))) * n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    unfold eH; ring
  rw [e, Real.sqrt_sq (by positivity)]

/-- The cutoff threshold of the scale conditions. -/
noncomputable def Nscale (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℕ :=
  max (max (max ⌈1 / gF L⌉₊ ⌈1 / (gL L / 4)⌉₊) (max 8 ⌈1 / (gF L / Real.sqrt (32 * mtop sys * eta))⌉₊))
    (max (max ⌈1 / Real.sqrt (2 * mmax sys * (gF L ^ 2 / (64 * mtop sys)))⌉₊
      ⌈1 / (gL L / Real.sqrt 2048)⌉₊)
      (max ⌈Kthr sys L Hunit / gL L⌉₊ ⌈1 / (gL L / Real.sqrt (2048 * mmax sys * eta))⌉₊))

include hL in
/-- **The scale conditions hold beyond `Nscale`.** -/
theorem scale_conditions (Hunit : ℝ) (heta : 0 < eta) {n : ℕ} (hn : Nscale sys L Hunit ≤ n) :
    1 ≤ gF L * n ∧ 1 ≤ Kc L n / 4 ∧ 2 * gF L ≤ Kc L n / 4 ∧ 1 ≤ lH sys L n ∧
      1 ≤ Real.sqrt (2 * mmax sys * eH sys L n) ∧ 1 ≤ Lam sys L n ∧
      TavgScale sys L Hunit (CDelta sys L Hunit n) n ∧ 1 ≤ lamE sys L n := by
  have hg := gF_pos hL
  have hgL := gL_pos hL
  have hm : 0 < mmax sys := lt_of_lt_of_le one_pos (one_le_mmax sys)
  have hmt : 0 < mtop sys := lt_of_lt_of_le one_pos (one_le_mtop sys)
  have he : (0 : ℝ) < eta := by exact_mod_cast heta
  unfold Nscale at hn
  have hle : ∀ {a b c : ℕ}, max a b ≤ c → a ≤ c ∧ b ≤ c := fun h => ⟨le_trans (le_max_left _ _) h,
    le_trans (le_max_right _ _) h⟩
  obtain ⟨hA, hB⟩ := hle hn
  obtain ⟨hA1, hA2⟩ := hle hA
  obtain ⟨hA11, hA12⟩ := hle hA1
  obtain ⟨hA21, hA22⟩ := hle hA2
  obtain ⟨hB1, hB2⟩ := hle hB
  obtain ⟨hB11, hB12⟩ := hle hB1
  obtain ⟨hB21, hB22⟩ := hle hB2
  have hgFL : gF L = gL L := rfl
  refine ⟨one_le_lin hg hA11, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := one_le_lin (show 0 < gL L / 4 by positivity) hA12
    rw [Kc]; linarith
  · have h8 : (8 : ℝ) ≤ n := by exact_mod_cast hA21
    rw [Kc, hgFL]; nlinarith
  · rw [lH_eq sys hL heta]; exact one_le_lin (by positivity) hA22
  · rw [sqrt_eH_eq sys hL]; exact one_le_lin (by positivity) hB11
  · rw [Lam_eq sys hL]; exact one_le_lin (by positivity) hB12
  · refine tavgScale_of_large sys Hunit hL _ ?_
    have h1 : Kthr sys L Hunit / gL L ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hB21)
    rw [Kc]
    rw [div_le_iff₀ hgL] at h1
    linarith
  · rw [lamE_eq sys hL heta]; exact one_le_lin (by positivity) hB22

/-! ## The theorem -/

variable (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel in
/-- **`thm:src3`** (conditional analytic completion). -/
theorem thm_src3 (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (p₀ : Fin eta)
    {ε : ℝ} (hε : 0 < ε) {C3 : ℝ} (hC3 : 0 ≤ C3) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N₀ ≤ n →
      ∀ (S3 R3 : En eta n →L[ℂ] En eta n), S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n) →
      FSConj.cm S3 (Akin sys L n) = -(H3ret sys hL hn H - R3) →
      ‖S3‖ ≤ z3F L C3 q n →
      (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u →
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤ betaF L C3 q n * M) →
      (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u → ‖R3 u‖ ≤ betaF L C3 q n * M) →
      ∀ (D : EvoData L H) (t : ℝ), 1 ≤ t →
        |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
          (regKin sys (gF L) p₀).expect (emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-t)
            (ext eta n (Sm eta L D.u₀))))| ≤ C * D.Xi ^ 2 * (1 + t) * Kc L n ^ (-3 + ε) := by
  have heta : 0 < eta := Fin.pos p₀
  set ε₁ := min ε 1 / 8 with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  have hε₁8 : ε₁ ≤ 1 / 8 := by
    have := min_le_right ε 1; simp only [hε₁def]; linarith
  have hε₁ε : 8 * ε₁ ≤ ε := by
    have := min_le_left ε 1; simp only [hε₁def]; linarith
  obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = 3 / 4 + ε₁ := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁d⟩ : ∃ s₁ : ℝ, s₁ = 3 / 2 + 2 * ε₁ := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂d⟩ : ∃ s₂ : ℝ, s₂ = 3 / 4 + ε₁ := ⟨_, rfl⟩
  have hz := pl_z3F hL C3 q
  have hb := pl_betaF hL C3 q
  have hE0 := (pl_E0err sys hL Hunit heta hb s).mono (q := -3 + 2 * ε₁) (by linarith)
  have hE1 := (pl_E1err sys hL Hunit heta hz hb (s := s) (s₁ := s₁) (s₂ := s₂) (by linarith)
    (by linarith) (by linarith)).mono (q := -3 + 2 * ε₁) (by
      refine max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith))))
  obtain ⟨C₀, hC₀, N₀', h0⟩ := hE0.final hε₁
  obtain ⟨C₁, hC₁, N₁', h1⟩ := hE1.final hε₁
  have hgL := gL_pos hL
  refine ⟨(C₀ + C₁) * gL L ^ (3 - 3 * ε₁), by positivity,
    max (max N₀' N₁') (max (Nscale sys L Hunit) 1), fun n hn hN S3 R3 hS3 hA3 hz3 hβ hR3 D t ht => ?_⟩
  have hN0 : N₀' ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁' ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNs : Nscale sys L Hunit ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  obtain ⟨hKg, hK1, hK2, hlH, hΛH, hΛ, hK, hlam⟩ := scale_conditions sys hL Hunit heta hNs
  have hβ0 : 0 ≤ betaF L C3 q n := by
    unfold betaF
    have : 0 ≤ Real.log (2 + Kc L n) := Real.log_nonneg (by linarith)
    have : 0 ≤ Kc L n := by linarith
    positivity
  have hmain := src3_explicit sys hL hn H hKernel Hunit hPeriodic hKg hK1 hK2 hlH hΛH hΛ hK hlam heta
    (s := s) (s₁ := s₁) (s₂ := s₂) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) S3 R3 hS3 hA3 hz3 hβ0 hβ hR3 p₀ D ht
  rw [errC_eq] at hmain
  have hΞ := D.Xi_nonneg
  have ht0 : 0 ≤ t := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = -3 + 2 * ε₁ + ε₁ := ⟨_, rfl⟩
  have hE0n := (le_abs_self _).trans (h0 n hN0)
  have hE1n := (le_abs_self _).trans (h1 n hN1)
  rw [← hrd] at hE0n hE1n
  have hnr : 0 ≤ (n : ℝ) ^ r := Real.rpow_nonneg hn0.le r
  -- `n^r ≤ g^{3-3ε₁} K^{-3+ε}`
  have hKpos : 0 < Kc L n := by rw [Kc]; positivity
  have hK1' : 1 ≤ Kc L n := by linarith
  have hnK : (n : ℝ) ^ r = gL L ^ (3 - 3 * ε₁) * Kc L n ^ r := by
    have e : (n : ℝ) = Kc L n / gL L := by rw [Kc]; field_simp
    have hr3 : -r = 3 - 3 * ε₁ := by rw [hrd]; ring
    rw [e, Real.div_rpow hKpos.le hgL.le, div_eq_mul_inv, ← Real.rpow_neg hgL.le, hr3]
    ring
  have hKr : Kc L n ^ r ≤ Kc L n ^ (-3 + ε) := Real.rpow_le_rpow_of_exponent_le hK1' (by
    rw [hrd]; linarith)
  have hbound : E0err sys L Hunit n s (betaF L C3 q n) +
      t * E1err sys L Hunit n s s₁ s₂ (z3F L C3 q n) (betaF L C3 q n) ≤
      (C₀ + C₁) * (1 + t) * (n : ℝ) ^ r := by
    have := mul_le_mul_of_nonneg_left hE1n ht0
    nlinarith [mul_nonneg hC₀ hnr, mul_nonneg hC₁ hnr, mul_nonneg ht0 (mul_nonneg hC₀ hnr),
      mul_nonneg ht0 (mul_nonneg hC₁ hnr)]
  refine hmain.trans ?_
  calc D.Xi ^ 2 * (E0err sys L Hunit n s (betaF L C3 q n) +
        t * E1err sys L Hunit n s s₁ s₂ (z3F L C3 q n) (betaF L C3 q n))
      ≤ D.Xi ^ 2 * ((C₀ + C₁) * (1 + t) * (n : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (C₀ + C₁) * gL L ^ (3 - 3 * ε₁) * D.Xi ^ 2 * (1 + t) * Kc L n ^ r := by rw [hnK]; ring
    _ ≤ (C₀ + C₁) * gL L ^ (3 - 3 * ε₁) * D.Xi ^ 2 * (1 + t) * Kc L n ^ (-3 + ε) :=
        mul_le_mul_of_nonneg_left hKr (by positivity)

end FSAsymp
