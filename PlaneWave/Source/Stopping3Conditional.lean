import PlaneWave.Source.Src3Conditional

/-!
# Flux/source build, block 5: `cor:stopping3` (conditional)

* `initial_error`: at `t = 0`, `|⟨ψ₀, A_{p₀} ψ₀⟩ - ⟨P ψ₀, A_{p₀} P ψ₀⟩| ≤ 5 η c_tr² Ξ² ((K/4)^{-3} + λ_E^{-3})`
  (`lem:bulkobs`/`lem:bulkobsE` on `ψ₀` and on `P ψ₀`; the truncated observable does not see `R`);
* **`cor_stopping3`**: the secant estimator `ΔŜ = [Δ⟨A_{p₀}⟩(T) - Δ⟨A_{p₀}⟩(0)]/(v_p T)` of the stopping
  power over a window `1 ≤ T`, Galerkin against exact, satisfies
  `|ΔŜ| ≤ (C Ξ²/v_p) (K^{-3+ε} + K^{-3+ε}/T)` under the hypotheses of `thm_src3`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace

namespace FSAsymp

open FSNormal PL

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- The constant of the initial error. -/
noncomputable def initC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  eta * (5 * cTr sys L Hunit ^ 2) * ((Kc L n / 4) ^ (-(3 : ℝ)) + lamE sys L n ^ (-(3 : ℝ)))

omit [Fintype ν] in
/-- The truncated observable does not see the exterior. -/
lemma dsym_tsum_trunc (n : ℕ) (p₀ : Fin eta) (x : L2 eta) :
    ∑' q, dsymF sys L n p₀ q * ‖x q‖ ^ 2 =
      ∑' q, dsymF sys L n p₀ q * ‖molecularH2Truncate n x q‖ ^ 2 := by
  refine tsum_congr fun q => ?_
  by_cases hq : q ∈ fourierConfigCube eta n
  · rw [molecularH2Truncate_apply, cubicLatticeCoeffTruncate_eq_of_mem n _ q hq]
  · have h0 : dsymF sys L n p₀ q = 0 := dsymF_eq_zero_of_not_mem sys p₀ q (fun hQ =>
      hq ((inP_iff_mem_cube n q).mp ((mem_Qs.mp hQ).inP (Nat.cast_nonneg n))))
    rw [h0, zero_mul, zero_mul]

include hKernel hL in
/-- **The initial error**: `|⟨ψ₀, A_{p₀} ψ₀⟩ - ⟨P ψ₀, A_{p₀} P ψ₀⟩| ≤ Ξ² init(n)`. -/
theorem initial_error (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {n : ℕ} (hK4 : 4 ≤ Kc L n) (hlam : 1 ≤ lamE sys L n) (heta : 0 < eta) (p₀ : Fin eta)
    (D : EvoData L H) :
    |(regKin sys (gF L) p₀).expect (Sm eta L D.u₀) -
      (regKin sys (gF L) p₀).expect (emb eta n (ext eta n (Sm eta L D.u₀)))| ≤
      D.Xi ^ 2 * initC sys L Hunit n := by
  have hF := datum_fgood sys hL H hKernel Hunit hPeriodic D
  have hr1 := obs_reduction sys hL p₀ (Sm eta L D.u₀) (coulombFourierKineticH2 sys (gF L) D.u₀)
    (kinH2_apply sys D.u₀) (M := cTr sys L Hunit * D.Xi) (fun a l hl => hF.2 a l hl) hK4 hlam heta
  have hg := ext_good sys (n := n) hF
  have hr2 := obs_reduction sys hL p₀ (emb eta n (ext eta n (Sm eta L D.u₀)))
    (emb eta n (FSSpectral.kin (sb eta n) (Asym sys L n) (ext eta n (Sm eta L D.u₀))))
    (emb_kin_apply sys _) (M := 2 * (cTr sys L Hunit * D.Xi)) (fun a l hl => cube_tails sys hg a l hl)
    hK4 hlam heta
  have hS := dsym_tsum_trunc sys (L := L) n p₀ (Sm eta L D.u₀)
  rw [← emb_ext] at hS
  rw [← hS] at hr2
  obtain ⟨h1a, h1b⟩ := hr1
  obtain ⟨h2a, h2b⟩ := hr2
  have e : D.Xi ^ 2 * initC sys L Hunit n =
      eta * ((cTr sys L Hunit * D.Xi) ^ 2 * ((Kc L n / 4) ^ (-(3 : ℝ)) + lamE sys L n ^ (-(3 : ℝ)))) +
      eta * ((2 * (cTr sys L Hunit * D.Xi)) ^ 2 *
        ((Kc L n / 4) ^ (-(3 : ℝ)) + lamE sys L n ^ (-(3 : ℝ)))) := by
    unfold initC; ring
  rw [e, abs_le]
  constructor <;> linarith

include hL in
theorem pl_initC (Hunit : ℝ) (heta : 0 < eta) : PL (fun n => initC sys L Hunit n) (-3) := by
  have h := (((pl_Kc4 hL (-(3 : ℝ))).add (pl_lamE sys hL heta (-(3 : ℝ)))).const_mul
    (eta * (5 * cTr sys L Hunit ^ 2)))
  exact h.congr ⟨0, fun n _ => rfl⟩

include hKernel in
/-- **`cor:stopping3`** (conditional): the stopping power at the energy rate. -/
theorem cor_stopping3 (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) {ε : ℝ} (hε : 0 < ε) {C3 : ℝ} (hC3 : 0 ≤ C3) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N₀ ≤ n →
      ∀ (S3 R3 : En eta n →L[ℂ] En eta n), S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n) →
      FSConj.cm S3 (Akin sys L n) = -(H3ret sys hL hn H - R3) →
      ‖S3‖ ≤ z3F L C3 q n →
      (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u →
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤ betaF L C3 q n * M) →
      (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u → ‖R3 u‖ ≤ betaF L C3 q n * M) →
      ∀ (D : EvoData L H) {vp T : ℝ}, 0 < vp → 1 ≤ T →
        let ψN : ℝ → L2 eta := fun s =>
          emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-s) (ext eta n (Sm eta L D.u₀)))
        |((regKin sys (gF L) p₀).expect (D.U T (Sm eta L D.u₀)) -
            (regKin sys (gF L) p₀).expect (D.U 0 (Sm eta L D.u₀))) / (vp * T) -
          ((regKin sys (gF L) p₀).expect (ψN T) - (regKin sys (gF L) p₀).expect (ψN 0)) / (vp * T)| ≤
          C * D.Xi ^ 2 / vp * (Kc L n ^ (-3 + ε) + Kc L n ^ (-3 + ε) / T) := by
  have heta : 0 < eta := Fin.pos p₀
  obtain ⟨C, hC, N₀, hmain⟩ := thm_src3 sys hL H hKernel Hunit hPeriodic p₀ hε hC3 q
  obtain ⟨C₀, hC₀, N₁, h0⟩ := (pl_initC sys hL Hunit heta).final hε
  have hgL := gL_pos hL
  refine ⟨2 * C + C₀ * gL L ^ (3 - ε), by positivity,
    max (max N₀ N₁) (max (Nscale sys L Hunit) 1), fun n hn hN S3 R3 hS3 hA3 hz3 hβ hR3 D vp T hvp hT => ?_⟩
  intro ψN
  have hN0 : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1 : N₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNs : Nscale sys L Hunit ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  obtain ⟨-, hK1, -, -, -, -, -, hlam⟩ := scale_conditions sys hL Hunit heta hNs
  have hK4 : 4 ≤ Kc L n := by linarith
  have hT0 : 0 < T := by linarith
  have hΞ := D.Xi_nonneg
  -- the error at `T`
  have hDT := hmain n hn hN0 S3 R3 hS3 hA3 hz3 hβ hR3 D T hT
  -- the error at `0`
  have hD0 := initial_error sys hL H hKernel Hunit hPeriodic hK4 hlam heta p₀ D
  have hψ0 : D.U 0 (Sm eta L D.u₀) = Sm eta L D.u₀ := D.U0 _
  have hψN0 : ψN 0 = emb eta n (ext eta n (Sm eta L D.u₀)) := by
    simp only [ψN, neg_zero, retFlow_zero]
  rw [← hψN0, ← hψ0] at hD0
  -- `init(n) ≤ C₀ g^{3-ε} K^{-3+ε}`
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hKpos : 0 < Kc L n := by rw [Kc]; positivity
  have hinit := (le_abs_self _).trans (h0 n hN1)
  have hnK : (n : ℝ) ^ (-3 + ε) = gL L ^ (3 - ε) * Kc L n ^ (-3 + ε) := by
    have e : (n : ℝ) = Kc L n / gL L := by rw [Kc]; field_simp
    rw [e, Real.div_rpow hKpos.le hgL.le, div_eq_mul_inv, ← Real.rpow_neg hgL.le,
      show -(-3 + ε) = 3 - ε by ring]
    ring
  rw [hnK] at hinit
  have hD0' : |(regKin sys (gF L) p₀).expect (D.U 0 (Sm eta L D.u₀)) -
      (regKin sys (gF L) p₀).expect (ψN 0)| ≤
      D.Xi ^ 2 * (C₀ * gL L ^ (3 - ε) * Kc L n ^ (-3 + ε)) :=
    hD0.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hsec := secant_slope_le hvp hT0 hD0' hDT
  refine hsec.trans ?_
  have hKe : 0 ≤ Kc L n ^ (-3 + ε) := Real.rpow_nonneg hKpos.le _
  rw [div_le_iff₀ (by positivity)]
  have e : 2 * C + C₀ * gL L ^ (3 - ε) =
      (2 * C + C₀ * gL L ^ (3 - ε)) := rfl
  have hX : C * D.Xi ^ 2 * (1 + T) * Kc L n ^ (-3 + ε) +
      D.Xi ^ 2 * (C₀ * gL L ^ (3 - ε) * Kc L n ^ (-3 + ε)) ≤
      (2 * C + C₀ * gL L ^ (3 - ε)) * D.Xi ^ 2 * (T + 1) * Kc L n ^ (-3 + ε) := by
    have h1 : 0 ≤ C * D.Xi ^ 2 * Kc L n ^ (-3 + ε) := by positivity
    have h2 : 0 ≤ C₀ * gL L ^ (3 - ε) * D.Xi ^ 2 * Kc L n ^ (-3 + ε) := by positivity
    nlinarith
  calc D.Xi ^ 2 * (C₀ * gL L ^ (3 - ε) * Kc L n ^ (-3 + ε)) +
        C * D.Xi ^ 2 * (1 + T) * Kc L n ^ (-3 + ε)
      ≤ (2 * C + C₀ * gL L ^ (3 - ε)) * D.Xi ^ 2 * (T + 1) * Kc L n ^ (-3 + ε) := by linarith
    _ = (2 * C + C₀ * gL L ^ (3 - ε)) * D.Xi ^ 2 / vp *
        (Kc L n ^ (-3 + ε) + Kc L n ^ (-3 + ε) / T) * (vp * T) := by
        field_simp

end FSAsymp
