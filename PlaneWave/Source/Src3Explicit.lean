import PlaneWave.Source.Src3Terms

/-!
# Flux/source build, block 5: `thm:src3` with explicit constants

**`src3_explicit`**: for every cutoff `n ≥ 2` satisfying the scale conditions, every datum
(`EvoData`: the exact propagator and `u₀ ∈ D(H²)`, `H u₀ = S v₀`, with `Ξ = ‖S u₀‖ + ‖H u₀‖ + ‖H v₀‖`),
every `t ≥ 1` and every pair `(Σ₃, H₃^res)` with the conditional properties of `thm:src3`,

  `|⟨ψ(t), A_{p₀} ψ(t)⟩ - ⟨ψ_N(t), A_{p₀} ψ_N(t)⟩| ≤ Ξ² err(n, t)`,

`err = C_red + T₁ + T₂ + T₃ + T₄ + T₅`, with `ψ(t) = U(t) S u₀` the exact and
`ψ_N(t) = e^{-iH_N t} P S u₀` the Galerkin trajectory: `lem:bulkobs`/`lem:bulkobsE` on both
trajectories (`reduction`), then the assembly identity eq:nf-assembly with the dressing `e^{Σ_b}`
and the five terms of `T1_explicit` … `T5_explicit`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Final

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- The reduction constant of `lem:bulkobs` + `lem:bulkobsE` on both trajectories. -/
noncomputable def redC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  eta * (cTr sys L Hunit ^ 2 + mN sys L Hunit n ^ 2) *
    ((Kc L n / 4) ^ (-(3 : ℝ)) + lamE sys L n ^ (-(3 : ℝ)))

/-- **The error constant of `thm:src3`.** -/
noncomputable def errC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s s₁ s₂ z3 β t : ℝ) : ℝ :=
  redC sys L Hunit n + T1C sys L Hunit n s z3 β t + T2C sys L Hunit n + T3C sys L Hunit n s₁ s₂ t +
    T4C sys L Hunit n + T5C sys L Hunit n

omit [Fintype ν] in
lemma kinH2_apply (w : MolecularFourierH2 eta) (q : Cf eta) :
    coulombFourierKineticH2 sys (gF L) w q = (Ek sys L q : ℂ) * Sm eta L w q := by
  rw [coulombFourierKineticH2_apply, Sm, molecularH2StateMap_apply, Ek, E_eq_kineticSymbol]

include hKernel in
/-- **`thm:src3`, explicit form.** -/
theorem src3_explicit (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (hK1 : 1 ≤ Kc L n / 4) (hK2 : 2 * gF L ≤ Kc L n / 4)
    (hlH : 1 ≤ lH sys L n) (hΛH : 1 ≤ Real.sqrt (2 * mmax sys * eH sys L n))
    (hΛ : 1 ≤ Lam sys L n) (hK : TavgScale sys L Hunit (CDelta sys L Hunit n) n)
    (hlam : 1 ≤ lamE sys L n) (heta : 0 < eta)
    {s s₁ s₂ : ℝ} (hs : 3 / 4 < s) (hs1 : s ≤ 1) (hs₁ : 3 / 2 < s₁) (hs₁2 : s₁ ≤ 2)
    (hs₂ : 3 / 4 < s₂) (hs₂1 : s₂ ≤ 1)
    (S3 R3 : En eta n →L[ℂ] En eta n) (hS3 : S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n))
    (hA3 : FSConj.cm S3 (Akin sys L n) = -(H3ret sys hL hn H - R3))
    {z3 β : ℝ} (hz3 : ‖S3‖ ≤ z3) (hβ0 : 0 ≤ β)
    (hβ : ∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u →
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤ β * M)
    (hR3 : ∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u → ‖R3 u‖ ≤ β * M)
    (p₀ : Fin eta) (D : EvoData L H) {t : ℝ} (ht : 1 ≤ t) :
    |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
      (regKin sys (gF L) p₀).expect (emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-t)
        (ext eta n (Sm eta L D.u₀))))| ≤
      D.Xi ^ 2 * errC sys L Hunit n s s₁ s₂ z3 β t := by
  have hΞ := D.Xi_nonneg
  have ht0 : 0 ≤ t := by linarith
  have hK4 : 4 ≤ Kc L n := by linarith
  -- the reduction on the exact trajectory
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D t
  have hr1 := obs_reduction sys hL p₀ (Sm eta L w) (coulombFourierKineticH2 sys (gF L) w)
    (kinH2_apply sys w) (M := cTr sys L Hunit * D.Xi) (fun a l hl => hF.2 a l hl) hK4 hlam heta
  rw [hw1] at hr1
  -- the reduction on the Galerkin trajectory
  have hgN := psiN_good sys hL H hKernel Hunit hPeriodic hKg (n := n) D (-t)
  have hr2 := obs_reduction sys hL p₀
    (emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀))))
    (emb eta n (FSSpectral.kin (sb eta n) (Asym sys L n)
      (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀)))))
    (emb_kin_apply sys _) (M := mN sys L Hunit n * D.Xi) (fun a l hl => cube_tails sys hgN a l hl)
    hK4 hlam heta
  -- the assembly identity
  have hU := (Sig_skew_unitary (sys := sys) hL hn).2
  have hA := assembly n hU (Ofull_selfAdjoint sys p₀ (L := L) (n := n)) (D.U t (Sm eta L D.u₀))
    (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀)))
    (retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) (aT sys hL hn D.U D.u₀ 0))
  simp only [ContinuousLinearMap.comp_apply] at hA
  have hSX := inner_Ofull_self sys p₀ (L := L) (n := n) (D.U t (Sm eta L D.u₀))
  have hSN : ⟪retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀)),
      ext eta n (Ofull sys L n p₀ (emb eta n
        (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀)))))⟫_ℂ =
      ((∑' q, dsymF sys L n p₀ q * ‖emb eta n
        (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀))) q‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_ext']; exact inner_Ofull_self sys p₀ (L := L) (n := n) _
  -- the five terms
  have k1 := T1_explicit sys hL hn H hKernel Hunit hPeriodic hKg hs hs1 hK1 hK2 hlH hΛH hΛ S3 R3 hS3
    hA3 hz3 hβ0 hβ hR3 p₀ D ht0
  simp only [← ext_Ofull_emb sys hL p₀] at k1
  have k2 := T2_explicit sys hL hn H hKernel Hunit hPeriodic hKg p₀ D t
  have k3 := T3_explicit sys hL hn H hKernel Hunit hPeriodic hKg hΛ hs₁ hs₁2 hs₂ hs₂1 hK p₀ D ht
  have k4 := T4_explicit sys hL hn H hKernel Hunit hPeriodic hKg p₀ D t
  have k5 := T5_explicit sys hL hn H hKernel Hunit hPeriodic hKg p₀ D t
  have key5 : ∀ x1 x2 x3 x4 x5 : ℂ,
      ‖x1 + x2 + x3 + x4 + x5‖ ≤ ‖x1‖ + ‖x2‖ + ‖x3‖ + ‖x4‖ + ‖x5‖ := by
    intro x1 x2 x3 x4 x5
    have h1 := norm_add_le x1 x2
    have h2 := norm_add_le (x1 + x2) x3
    have h3 := norm_add_le (x1 + x2 + x3) x4
    have h4 := norm_add_le (x1 + x2 + x3 + x4) x5
    linarith
  have hn1 := congrArg (fun z : ℂ => ‖z‖) hA
  have hdiff := hn1.le.trans (key5 _ _ _ _ _)
  rw [hSX, hSN, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hdiff
  rw [hSN] at k1
  simp only [aT, psiT] at hdiff k1 k2 k3 k4 k5
  have hsum : |(∑' q, dsymF sys L n p₀ q * ‖(D.U t (Sm eta L D.u₀)) q‖ ^ 2) -
      ∑' q, dsymF sys L n p₀ q * ‖emb eta n
        (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀))) q‖ ^ 2| ≤
      D.Xi ^ 2 * T1C sys L Hunit n s z3 β t + D.Xi ^ 2 * T2C sys L Hunit n +
        D.Xi ^ 2 * T3C sys L Hunit n s₁ s₂ t + D.Xi ^ 2 * T4C sys L Hunit n +
        D.Xi ^ 2 * T5C sys L Hunit n := by
    refine hdiff.trans ?_
    linarith
  obtain ⟨h1a, h1b⟩ := hr1
  obtain ⟨h2a, h2b⟩ := hr2
  have hsum' := abs_le.mp hsum
  have e : D.Xi ^ 2 * errC sys L Hunit n s s₁ s₂ z3 β t =
      eta * ((cTr sys L Hunit * D.Xi) ^ 2 * ((Kc L n / 4) ^ (-(3 : ℝ)) + lamE sys L n ^ (-(3 : ℝ)))) +
      eta * ((mN sys L Hunit n * D.Xi) ^ 2 * ((Kc L n / 4) ^ (-(3 : ℝ)) + lamE sys L n ^ (-(3 : ℝ)))) +
      (D.Xi ^ 2 * T1C sys L Hunit n s z3 β t + D.Xi ^ 2 * T2C sys L Hunit n +
        D.Xi ^ 2 * T3C sys L Hunit n s₁ s₂ t + D.Xi ^ 2 * T4C sys L Hunit n +
        D.Xi ^ 2 * T5C sys L Hunit n) := by
    unfold errC redC; ring
  rw [e, abs_le]
  constructor <;> linarith

end Final

end FSNormal
