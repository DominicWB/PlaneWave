import PlaneWave.Source.SourceNonsecularExplicit

/-!
# Flux/source build, block 5: `thm:src3` with explicit constants

* `T2_explicit`, `T4_explicit`, `T5_explicit`: the observable correction, the `RR` term and the
  cross term of eq:nf-assembly;
* `reduction_explicit` (`lem:bulkobs`, `lem:bulkobsE` on both trajectories);
* **`src3_explicit`**: for every `n` satisfying the scale conditions, every datum and every
  `t ≥ 1`,

  `|⟨ψ(t), A_{p₀} ψ(t)⟩ - ⟨ψ_N(t), A_{p₀} ψ_N(t)⟩| ≤ Ξ² (C_red + T₁ + T₂ + T₃ + T₄ + T₅)`,

  each `Tᵢ` an explicit function of `n` (and of `t`, linearly, for `T₁` and `T₃`), under the
  conditional hypotheses on `Σ₃` and `H₃^res`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Nonsec

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- The constant of the observable correction. -/
noncomputable def T2C (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  2 * (Asig sys L n * (2 * a0c sys L n * mChi sys L Hunit n)) * mChi sys L Hunit n +
    E0 sys L n * (Asig sys L n * (2 * a0c sys L n * mChi sys L Hunit n)) ^ 2

/-- The constant of the `RR` term. -/
noncomputable def T4C (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  E0 sys L n * (Asig sys L n * rhoT sys L Hunit n) ^ 2

/-- The constant of the cross term. -/
noncomputable def T5C (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  2 * ((1 + 2 * E0 sys L n * a0c sys L n) * mA sys L Hunit n * (Asig sys L n * rhoT sys L Hunit n))

include hKernel in
theorem T2_explicit (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (p₀ : Fin eta) (D : EvoData L H) (t : ℝ) :
    ‖⟪retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) (aT sys hL hn D.U D.u₀ 0),
        ext eta n ((exp (Sig sys L n hL hn) * Ofull sys L n p₀ * star (exp (Sig sys L n hL hn)))
          (emb eta n (retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) (aT sys hL hn D.U D.u₀ 0)))) -
        ext eta n (Ofull sys L n p₀ (emb eta n
          (retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) (aT sys hL hn D.U D.u₀ 0))))⟫_ℂ‖ ≤
      D.Xi ^ 2 * T2C sys L Hunit n := by
  set χ := retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) (aT sys hL hn D.U D.u₀ 0)
  have hg := chi_good sys hL hn H hKernel Hunit hPeriodic hKg D (-t)
  have hΘ := theta_le_good sys hg
  have hΘ0 := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ)
  refine (T2_le sys hL hn p₀ χ).trans ?_
  set Θ := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ‖
  set M := mChi sys L Hunit n * D.Xi
  have hA0 := Asig_nonneg (sys := sys) (n := n) hL
  have ha0 := a0c_nonneg sys (L := L) (n := n)
  have hE0 := E0_nonneg sys (L := L) (n := n)
  have h1 : Asig sys L n * (2 * a0c sys L n * Θ) ≤ Asig sys L n * (2 * a0c sys L n * M) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΘ (by positivity)) hA0
  have h10 : 0 ≤ Asig sys L n * (2 * a0c sys L n * Θ) := by positivity
  have k1 : 2 * (Asig sys L n * (2 * a0c sys L n * Θ)) * Θ ≤
      2 * (Asig sys L n * (2 * a0c sys L n * M)) * M :=
    mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hΘ hΘ0 (by linarith)
  have k2 : E0 sys L n * (Asig sys L n * (2 * a0c sys L n * Θ)) ^ 2 ≤
      E0 sys L n * (Asig sys L n * (2 * a0c sys L n * M)) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h10 h1 2) hE0
  have e : D.Xi ^ 2 * T2C sys L Hunit n = 2 * (Asig sys L n * (2 * a0c sys L n * M)) * M +
      E0 sys L n * (Asig sys L n * (2 * a0c sys L n * M)) ^ 2 := by
    simp only [M]; unfold T2C; ring
  rw [e]; linarith

include hKernel in
theorem T4_explicit (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (p₀ : Fin eta) (D : EvoData L H) (t : ℝ) :
    ‖⟪psiT sys hL hn D.U D.u₀ t - molecularH2Truncate n (psiT sys hL hn D.U D.u₀ t),
        (exp (Sig sys L n hL hn) * Ofull sys L n p₀ * star (exp (Sig sys L n hL hn)))
          (psiT sys hL hn D.U D.u₀ t - molecularH2Truncate n (psiT sys hL hn D.U D.u₀ t))⟫_ℂ‖ ≤
      D.Xi ^ 2 * T4C sys L Hunit n := by
  have hρ := (aT_bounds sys hL hn H hKernel Hunit hPeriodic hKg D t).1
  refine (T4_le sys hL hn p₀ _).trans ?_
  have hA0 := Asig_nonneg (sys := sys) (n := n) hL
  have hE0 := E0_nonneg sys (L := L) (n := n)
  have h1 := mul_le_mul_of_nonneg_left hρ hA0
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  have e : D.Xi ^ 2 * T4C sys L Hunit n =
      E0 sys L n * (Asig sys L n * (rhoT sys L Hunit n * D.Xi)) ^ 2 := by unfold T4C; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h2 hE0

include hKernel in
theorem T5_explicit (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (p₀ : Fin eta) (D : EvoData L H) (t : ℝ) :
    ‖⟪emb eta n (aT sys hL hn D.U D.u₀ t), (exp (Sig sys L n hL hn) * Ofull sys L n p₀ *
          star (exp (Sig sys L n hL hn)))
          (psiT sys hL hn D.U D.u₀ t - molecularH2Truncate n (psiT sys hL hn D.U D.u₀ t))⟫_ℂ +
      (starRingEnd ℂ) ⟪emb eta n (aT sys hL hn D.U D.u₀ t), (exp (Sig sys L n hL hn) *
          Ofull sys L n p₀ * star (exp (Sig sys L n hL hn)))
          (psiT sys hL hn D.U D.u₀ t - molecularH2Truncate n (psiT sys hL hn D.U D.u₀ t))⟫_ℂ‖ ≤
      D.Xi ^ 2 * T5C sys L Hunit n := by
  obtain ⟨hρ, -, -, hg⟩ := aT_bounds sys hL hn H hKernel Hunit hPeriodic hKg D t
  have h5 := T5_le sys hL hn p₀ (psiT sys hL hn D.U D.u₀ t)
  have hz := norm_add_le (⟪emb eta n (aT sys hL hn D.U D.u₀ t), (exp (Sig sys L n hL hn) *
      Ofull sys L n p₀ * star (exp (Sig sys L n hL hn)))
      (psiT sys hL hn D.U D.u₀ t - molecularH2Truncate n (psiT sys hL hn D.U D.u₀ t))⟫_ℂ)
    ((starRingEnd ℂ) ⟪emb eta n (aT sys hL hn D.U D.u₀ t), (exp (Sig sys L n hL hn) *
      Ofull sys L n p₀ * star (exp (Sig sys L n hL hn)))
      (psiT sys hL hn D.U D.u₀ t - molecularH2Truncate n (psiT sys hL hn D.U D.u₀ t))⟫_ℂ)
  rw [Complex.norm_conj] at hz
  refine hz.trans ?_
  have hA0 := Asig_nonneg (sys := sys) (n := n) hL
  have hE0 := E0_nonneg sys (L := L) (n := n)
  have ha0 := a0c_nonneg sys (L := L) (n := n)
  have hc : 0 ≤ 1 + 2 * E0 sys L n * a0c sys L n := by positivity
  have hΘ := theta_le_good sys hg
  have k : (1 + 2 * E0 sys L n * a0c sys L n) *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (psiT sys hL hn D.U D.u₀ t))‖ *
      (Asig sys L n * ‖psiT sys hL hn D.U D.u₀ t - molecularH2Truncate n (psiT sys hL hn D.U D.u₀ t)‖) ≤
      (1 + 2 * E0 sys L n * a0c sys L n) * (mA sys L Hunit n * D.Xi) *
        (Asig sys L n * (rhoT sys L Hunit n * D.Xi)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hΘ hc) (mul_le_mul_of_nonneg_left hρ hA0)
      (by positivity) (by have := le_trans (norm_nonneg _) hΘ; positivity)
  have e : D.Xi ^ 2 * T5C sys L Hunit n = 2 * ((1 + 2 * E0 sys L n * a0c sys L n) *
      (mA sys L Hunit n * D.Xi) * (Asig sys L n * (rhoT sys L Hunit n * D.Xi))) := by
    unfold T5C; ring
  rw [e]
  have h5' : ‖⟪emb eta n (aT sys hL hn D.U D.u₀ t), (exp (Sig sys L n hL hn) * Ofull sys L n p₀ *
      star (exp (Sig sys L n hL hn)))
      (psiT sys hL hn D.U D.u₀ t - molecularH2Truncate n (psiT sys hL hn D.U D.u₀ t))⟫_ℂ‖ ≤
      (1 + 2 * E0 sys L n * a0c sys L n) * (mA sys L Hunit n * D.Xi) *
        (Asig sys L n * (rhoT sys L Hunit n * D.Xi)) := h5.trans k
  linarith

end Nonsec

end FSNormal
