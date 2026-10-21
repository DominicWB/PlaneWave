import PlaneWave.Source.SourceNonsecularTerms

/-!
# Flux/source build, block 5: the source and the nonsecular terms, explicit

With `Ã = e^{Σ_b} O e^{-Σ_b}` (`O = A_{p₀}^E`), `a(t) = P ψ̃(t)`, `r(t) = R ψ̃(t)` and
`χ(t) = e^{-iH't} a(0)`:

* **`T3_explicit`** (the source): `|⟪a, PÃP a⟫ - ⟪χ, PÃP χ⟫| ≤ Ξ² t (src_c + f_c C_Acorr m_V)`,
  by the midpoint identity for the symmetric `PÃP`, Duhamel, `source_pairing` (`prop:src-nc1` and
  the second-order coupling) and `lem:acorr`;
* `T2_explicit`, `T4_explicit`, `T5_explicit`: the observable correction, the `RR` term and the
  cross term.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Src

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- The budget of `a(t) + χ(t)`. -/
noncomputable def mV (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  mA sys L Hunit n + mChi sys L Hunit n

/-- The moment factor `(C_{σ+1} Λ^{4σ-1})^{1/2}` of the datum. -/
noncomputable def momF (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (σ : ℝ) : ℝ :=
  Real.sqrt (momentConst eta (σ + 1) * Lam sys L n ^ (4 * σ - 1))

/-- **The source constant.** -/
noncomputable def srcC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s₁ s₂ : ℝ) : ℝ :=
  omT sys L Hunit n * mV sys L Hunit n *
      Real.sqrt (Ctavg sys L Hunit (CDelta sys L Hunit n) s₁) * Kc L n ^ (s₁ - 3) *
      (1 + DK (Kc L n)) ^ s₁ +
    (Asig sys L n * rhoT sys L Hunit n * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        (CflS sys L Hunit (CDelta sys L Hunit n) (1 / 2) * (mV sys L Hunit n * momF sys L n (1 / 2)))) +
      omT sys L Hunit n * (cSt sys L n s₂ * cE sys L ^ s₂ *
        (CflS sys L Hunit (CDelta sys L Hunit n) s₂ * (mV sys L Hunit n * momF sys L n s₂))) +
      (2 * Asig sys L n * CZ sys L Hunit n + 4 * Asig sys L n ^ 2 * CX sys L Hunit n) *
        rhoT sys L Hunit n * mV sys L Hunit n)

/-- The constant of the third term. -/
noncomputable def T3C (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s₁ s₂ t : ℝ) : ℝ :=
  t * srcC sys L Hunit n s₁ s₂ + t * (fC sys L Hunit n * (CAcorr sys L n * mV sys L Hunit n))

omit [Fintype ν] in
include hL in
/-- `‖ℰ^σ A_{p₀}^E w‖ ≤ M (C_{σ+1} Λ^{4σ-1})^{1/2}` for good `w`. -/
lemma wt_datum_le (hΛ : 1 ≤ Lam sys L n) (p₀ : Fin eta) {M : ℝ} (w : En eta n)
    (hw : IsGood sys L 1 M w) {σ : ℝ} (hσ : 1 / 4 < σ) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) σ (datum sys L p₀ w)‖ ≤ M * momF sys L n σ := by
  have hM := good_nonneg hw
  have h2 := wt_datum_sq_le sys L p₀ hL (Cg := 1) (Ξ := M) (by linarith) hσ hΛ w hw
  rw [← Real.sqrt_sq (norm_nonneg _)]
  refine (Real.sqrt_le_sqrt h2).trans (le_of_eq ?_)
  have e : momentConst eta (σ + 1) * (1 * M) ^ 2 * Lam sys L n ^ (4 * σ - 1) =
      M ^ 2 * (momentConst eta (σ + 1) * Lam sys L n ^ (4 * σ - 1)) := by ring
  rw [e, Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]
  rfl

include hL in
lemma CAcorr_nonneg : 0 ≤ CAcorr sys L n := by
  unfold CAcorr
  have := E0_nonneg sys (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  have := a0c_nonneg sys (L := L) (n := n)
  positivity

include hKernel in
/-- **The source term** (`thm:src3`, third term of eq:nf-assembly). -/
theorem T3_explicit (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (hΛ : 1 ≤ Lam sys L n) {s₁ s₂ : ℝ} (hs₁ : 3 / 2 < s₁) (hs₁2 : s₁ ≤ 2)
    (hs₂ : 3 / 4 < s₂) (hs₂1 : s₂ ≤ 1) (hK : TavgScale sys L Hunit (CDelta sys L Hunit n) n)
    (p₀ : Fin eta) (D : EvoData L H) {t : ℝ} (ht : 1 ≤ t) :
    ‖⟪aT sys hL hn D.U D.u₀ t, ext eta n ((exp (Sig sys L n hL hn) * Ofull sys L n p₀ *
          star (exp (Sig sys L n hL hn))) (emb eta n (aT sys hL hn D.U D.u₀ t)))⟫_ℂ -
      ⟪retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) (aT sys hL hn D.U D.u₀ 0),
        ext eta n ((exp (Sig sys L n hL hn) * Ofull sys L n p₀ * star (exp (Sig sys L n hL hn)))
          (emb eta n (retFlow sys L n (dH_symm sys hL hn H hKernel) (-t)
            (aT sys hL hn D.U D.u₀ 0))))⟫_ℂ‖ ≤
      D.Xi ^ 2 * T3C sys L Hunit n s₁ s₂ t := by
  have hΞ := D.Xi_nonneg
  have ht0 : 0 ≤ t := by linarith
  set At := exp (Sig sys L n hL hn) * Ofull sys L n p₀ * star (exp (Sig sys L n hL hn))
  set a := aT sys hL hn D.U D.u₀ t
  set χ := retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) (aT sys hL hn D.U D.u₀ 0)
  -- `P Ã P` is symmetric
  have hsa : IsSelfAdjoint At := (Ofull_selfAdjoint sys p₀).conjugate _
  set T : En eta n →ₗ[ℂ] En eta n := (ext eta n ∘L At ∘L emb eta n : En eta n →L[ℂ] En eta n).toLinearMap
  have hTa : ∀ v, T v = ext eta n (At (emb eta n v)) := fun v => rfl
  have hT : T.IsSymmetric := by
    intro x y
    rw [hTa, hTa, inner_ext, inner_ext', ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint, hsa.star_eq]
  have hmid := norm_quad_sub_le T hT a χ
  rw [hTa, hTa] at hmid
  refine hmid.trans ?_
  rw [hTa]
  -- split off the observable correction
  set w := a + χ
  have hsplit : ext eta n (At (emb eta n w)) = datum sys L p₀ w +
      (ext eta n (At (emb eta n w)) - ext eta n (Ofull sys L n p₀ (emb eta n w))) := by
    rw [ext_Ofull_emb sys hL p₀]; abel
  rw [hsplit, inner_add_right]
  refine (norm_add_le _ _).trans ?_
  -- the goodness of `w`
  obtain ⟨-, -, -, hga⟩ := aT_bounds sys hL hn H hKernel Hunit hPeriodic hKg D t
  have hgχ := chi_good sys hL hn H hKernel Hunit hPeriodic hKg D (-t)
  have hgw : IsGood sys L 1 (mV sys L Hunit n * D.Xi) w := by
    refine isGood_mono sys (isGood_add sys hga hgχ) (le_of_eq ?_)
    unfold mV; ring
  have hmV : 0 ≤ mV sys L Hunit n * D.Xi := good_nonneg hgw
  -- the correction part
  have hac := norm_aT_sub_chi_le sys hL hn H hKernel Hunit hPeriodic hKg D ht0
  have hcorr : ‖⟪a - χ, ext eta n (At (emb eta n w)) - ext eta n (Ofull sys L n p₀ (emb eta n w))⟫_ℂ‖ ≤
      t * (fC sys L Hunit n * D.Xi) * (CAcorr sys L n * (mV sys L Hunit n * D.Xi)) := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul hac ?_ (norm_nonneg _) (by
      have := fC_nonneg sys hL (n := n) Hunit; positivity))
    exact (Acorr_le sys hL hn p₀ w).trans (mul_le_mul_of_nonneg_left (theta_le_good sys hgw)
      (CAcorr_nonneg sys hL))
  -- the source part
  have hd := duhamel_weak sys hL hn H hKernel D.U D.u₀ D.graph D.deriv D.cont t (datum sys L p₀ w)
  have e : ⟪a - χ, datum sys L p₀ w⟫_ℂ = Complex.I * ∫ s in (0 : ℝ)..t,
      ⟪fT sys hL hn H D.U D.u₀ s, retFlow sys L n (dH_symm sys hL hn H hKernel) (t - s)
        (datum sys L p₀ w)⟫_ℂ := by
    rw [inner_sub_left, hd]; ring
  rw [e, norm_mul, Complex.norm_I, one_mul]
  have hsrc := source_pairing sys hL hn H hKernel Hunit hPeriodic D.U D.u₀ D.graph D.cont hs₁ hs₁2
    hs₂ hs₂1 hK p₀ (Cg := 1) (Ξ := mV sys L Hunit n * D.Xi) (by linarith) ht w (by
      simpa using hgw)
    (a := omT sys L Hunit n * D.Xi) (ρ := rhoT sys L Hunit n * D.Xi)
    (fun s _ w' hw' => (aT_bounds sys hL hn H hKernel Hunit hPeriodic hKg D s).2.1 w' hw')
    (fun s _ => (aT_bounds sys hL hn H hKernel Hunit hPeriodic hKg D s).1)
  set X1 := ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) (datum sys L p₀ w)‖
  set X2 := ‖FSSpectral.wt (sb eta n) (Asym sys L n) s₂ (datum sys L p₀ w)‖
  set X0 := ‖datum sys L p₀ w‖
  have hX1 : X1 ≤ mV sys L Hunit n * D.Xi * momF sys L n (1 / 2) :=
    wt_datum_le sys hL hΛ p₀ w hgw (by norm_num)
  have hX2 : X2 ≤ mV sys L Hunit n * D.Xi * momF sys L n s₂ :=
    wt_datum_le sys hL hΛ p₀ w hgw (by linarith)
  have hX0 : X0 ≤ mV sys L Hunit n * D.Xi :=
    (norm_datum_le sys L p₀ w).trans (theta_le_good sys hgw)
  have hA0 := Asig_nonneg (sys := sys) (n := n) hL
  have hr0 := rhoT_nonneg sys hL (n := n) Hunit
  have ho0 := omT_nonneg sys hL (n := n) Hunit
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hCD := CDelta_nonneg sys hL Hunit (n := n)
  have hF1 := CflS_nonneg sys Hunit hCD (L := L) (1 / 2)
  have hF2 := CflS_nonneg sys Hunit hCD (L := L) s₂
  have hcS : 0 ≤ cSt sys L n s₂ := Real.sqrt_nonneg _
  have hcE : 0 ≤ cE sys L ^ s₂ := Real.rpow_nonneg (by linarith [one_le_cE sys (L := L)]) _
  have hZ0 := CZ_nonneg sys Hunit (L := L) (n := n)
  have hX0' := CX_nonneg sys Hunit (L := L) (n := n)
  have k1 : Asig sys L n * (rhoT sys L Hunit n * D.Xi) *
      (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        (CflS sys L Hunit (CDelta sys L Hunit n) (1 / 2) * X1)) ≤
      Asig sys L n * (rhoT sys L Hunit n * D.Xi) *
      (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        (CflS sys L Hunit (CDelta sys L Hunit n) (1 / 2) *
          (mV sys L Hunit n * D.Xi * momF sys L n (1 / 2)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX1 hF1)
      (by positivity)) (by positivity)
  have k2 : omT sys L Hunit n * D.Xi * (cSt sys L n s₂ * cE sys L ^ s₂ *
        (CflS sys L Hunit (CDelta sys L Hunit n) s₂ * X2)) ≤
      omT sys L Hunit n * D.Xi * (cSt sys L n s₂ * cE sys L ^ s₂ *
        (CflS sys L Hunit (CDelta sys L Hunit n) s₂ * (mV sys L Hunit n * D.Xi * momF sys L n s₂))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX2 hF2)
      (by positivity)) (by positivity)
  have k3 : (2 * Asig sys L n * CZ sys L Hunit n + 4 * Asig sys L n ^ 2 * CX sys L Hunit n) *
        (rhoT sys L Hunit n * D.Xi) * X0 ≤
      (2 * Asig sys L n * CZ sys L Hunit n + 4 * Asig sys L n ^ 2 * CX sys L Hunit n) *
        (rhoT sys L Hunit n * D.Xi) * (mV sys L Hunit n * D.Xi) :=
    mul_le_mul_of_nonneg_left hX0 (by positivity)
  have hsum := add_le_add (add_le_add k1 k2) k3
  have ht' := mul_le_mul_of_nonneg_left hsum ht0
  have e2 : D.Xi ^ 2 * T3C sys L Hunit n s₁ s₂ t =
      omT sys L Hunit n * D.Xi * t * (1 * (mV sys L Hunit n * D.Xi)) *
          Real.sqrt (Ctavg sys L Hunit (CDelta sys L Hunit n) s₁) * Kc L n ^ (s₁ - 3) *
          (1 + DK (Kc L n)) ^ s₁ +
        t * (Asig sys L n * (rhoT sys L Hunit n * D.Xi) *
          (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
            (CflS sys L Hunit (CDelta sys L Hunit n) (1 / 2) *
              (mV sys L Hunit n * D.Xi * momF sys L n (1 / 2)))) +
          omT sys L Hunit n * D.Xi * (cSt sys L n s₂ * cE sys L ^ s₂ *
            (CflS sys L Hunit (CDelta sys L Hunit n) s₂ * (mV sys L Hunit n * D.Xi * momF sys L n s₂))) +
          (2 * Asig sys L n * CZ sys L Hunit n + 4 * Asig sys L n ^ 2 * CX sys L Hunit n) *
            (rhoT sys L Hunit n * D.Xi) * (mV sys L Hunit n * D.Xi)) +
        t * (fC sys L Hunit n * D.Xi) * (CAcorr sys L n * (mV sys L Hunit n * D.Xi)) := by
    unfold T3C srcC; ring
  rw [e2]
  linarith

end Src

end FSNormal
