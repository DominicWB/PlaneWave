import PlaneWave.Source.FirstRetainedCorrection

/-!
# Flux/source build, block 3h: the source term

The coupling of the retained Duhamel formula (`fT`, `Ṽ_{PR} ψ̃_R`) splits (`fT_decomp`) into the
near-cutoff part `(1 - Q) P W R ψ̃`, the second-order coupling `P [Σ_b, W] R ψ̃` in its two
orientations `-P W Σ_b r` and `-P (W Σ_b)† r = P Σ_b W r`, and the remainders `-½ P [Σ_b, Z] r`,
`-P R₃ r`. Paired with the backward flow `φ = e^{iH'(t-s)} A_{p₀}^E v` of a good state:

* the near-cutoff part by `prop:src-nc1` (`src_nc1_explicit`, block 1);
* `|⟪P W Σ_b r, φ⟫| ≤ A_σ ‖r‖ √2 C_m ‖(1+A)^{1/2} φ‖` (`W_N` symmetric, Hardy);
* `|⟪P Σ_b W r, φ⟫| ≤ ‖W (w - P w)‖ ‖Σ_b φ‖ ≤ ‖W (w - P w)‖ c_s ‖(1+A)^s φ‖` (eq:bulk-weighted-state);
* the remainders by norms.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic NormedSpace FluxSourceTest
  FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- `Z = W Σ_D + (W Σ_D)†` (`[Σ_b, W] = -Z` on `D(T)`). -/
noncomputable def Zsym : L2 eta →L[ℂ] L2 eta :=
  Zw sys hL hn H + ContinuousLinearMap.adjoint (Zw sys hL hn H)

/-- The third-order remainder `R₃ = Bi Σ X₁ - X₁ - ½ [Σ, X₁]` of the correction `B`. -/
noncomputable def R3c : L2 eta →L[ℂ] L2 eta :=
  FSConj.Bi (Sig sys L n hL hn) (X1 sys hL hn H) - X1 sys hL hn H -
    (1 / 2 : ℂ) • FSConj.cm (Sig sys L n hL hn) (X1 sys hL hn H)

omit [Fintype ν] in
lemma cm_add (Z X Y : L2 eta →L[ℂ] L2 eta) : FSConj.cm Z (X + Y) = FSConj.cm Z X + FSConj.cm Z Y := by
  unfold FSConj.cm; noncomm_ring

open Classical in
include hKernel in
/-- **The decomposition of the coupling.** For `S w = ψ̃(t)` and `r = R ψ̃(t)`:
`f = (1 - Q) P W (w - P w) - P W Σ r - P (W Σ)† r - ½ P [Σ, Z] r - P R₃ r`. -/
theorem fT_decomp
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (u₀ : MolecularFourierH2 eta)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      Sm eta L u' = U t (Sm eta L u) ∧ H u' = U t (H u))
    (t : ℝ) (w : MolecularFourierH2 eta) (hw : Sm eta L w = psiT sys hL hn U u₀ t) :
    let r := psiT sys hL hn U u₀ t - molecularH2Truncate n (psiT sys hL hn U u₀ t)
    fT sys hL hn H U u₀ t =
      hotProj L (Kc L n / 4) (ext eta n (Wp sys L H (w - molecularH2Truncate n w))) -
        ext eta n (Zw sys hL hn H r) - ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) r) -
        (1 / 2 : ℂ) • ext eta n (FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) r) -
        ext eta n (R3c sys hL hn H r) := by
  intro r
  rw [fT_eq sys hL hn H hKernel U u₀ hgraph t w hw]
  have hr : Sm eta L (w - molecularH2Truncate n w) = r := by
    simp only [r, map_sub]
    rw [hw, show Sm eta L (molecularH2Truncate n w) = molecularH2Truncate n (Sm eta L w) from
      stateMap_truncate (gF L) n w, hw]
  have hrP : molecularH2Truncate n r = 0 := by
    simp only [r]; rw [molecularH2Truncate_sub, truncate_truncate, sub_self]
  have hrv : ∀ p, InP (n : ℝ) p → Sm eta L (w - molecularH2Truncate n w) p = 0 := by
    intro p hp
    rw [hr]
    have := congrArg (fun y : L2 eta => y p) hrP
    simp only [molecularH2Truncate_apply,
      cubicLatticeCoeffTruncate_eq_of_mem n _ p ((inP_iff_mem_cube n p).mp hp),
      lp.coeFn_zero, Pi.zero_apply] at this
    exact this
  have hVb := Vb_exterior sys hL H hKernel (w - molecularH2Truncate n w) hrv
  rw [hr] at hVb
  have hcm := PSigVbR sys hL hn r hrP
  have hB : Bcorr sys hL hn H = -(X1 sys hL hn H + (1 / 2 : ℂ) • FSConj.cm (Sig sys L n hL hn)
      (X1 sys hL hn H) + R3c sys hL hn H) := by
    simp only [Bcorr, R3c]; abel
  have hX : X1 sys hL hn H = Vb sys L n hL + Zsym sys hL hn H := by
    simp only [X1, Zsym]; abel
  have hcmX : FSConj.cm (Sig sys L n hL hn) (X1 sys hL hn H) =
      FSConj.cm (Sig sys L n hL hn) (Vb sys L n hL) + FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) := by
    rw [hX, cm_add]
  have hext0 : ext eta n (FSConj.cm (Sig sys L n hL hn) (Vb sys L n hL) r) = 0 := by
    rw [← extract_truncate n, hcm, map_zero]
  rw [hB, neg_apply, map_neg, add_apply, add_apply, map_add, map_add, smul_apply, map_smul, hcmX,
    add_apply, map_add, hext0, zero_add, hX, add_apply, map_add, hVb]
  have hhot := ext_sub_truncQ (n := n) hL (Wp sys L H (w - molecularH2Truncate n w))
  simp only [Zsym, add_apply, map_add] at *
  rw [← hhot]
  abel

/-! ## The pairings -/

include hKernel in
/-- `P W Σ_b r = W_N (P Σ_b r)` for `r ∈ ran R`. -/
lemma ext_Zw_exterior (r : L2 eta) (hr : molecularH2Truncate n r = 0) :
    ext eta n (Zw sys hL hn H r) =
      finiteCoulombPotential sys (coulombCellAmplitude L) n (ext eta n (Sig sys L n hL hn r)) := by
  have hS : SigD sys L n hL (by omega) r = cubeLift (gF L) n (ext eta n (Sig sys L n hL hn r)) := by
    apply molecularH2StateMap_injective eta (gF L)
    change Sm eta L _ = Sm eta L _
    rw [stateMap_SigD hL hn, stateMap_cubeLift', emb_ext, sig_interior sys hL hn r, hr, sub_zero]
  rw [Zw, ContinuousLinearMap.comp_apply, hS, ext_W_cubeLift sys H hKernel]

include hKernel in
/-- **`|⟪P W Σ_b r, φ⟫| ≤ A_σ ‖r‖ √2 C_m ‖(1+A)^{1/2} φ‖`**. -/
lemma pair_Zw_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (r : L2 eta) (hr : molecularH2Truncate n r = 0) (φ : En eta n) :
    ‖⟪ext eta n (Zw sys hL hn H r), φ⟫_ℂ‖ ≤
      Asig sys L n * ‖r‖ * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ‖) := by
  rw [ext_Zw_exterior sys hL hn H hKernel r hr,
    finiteCoulombPotential_isSymmetric sys _ n]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul ?_ (potential_le_wt sys Hunit n hL hPeriodic φ)
    (norm_nonneg _) (by have := Asig_nonneg (sys := sys) (n := n) hL; positivity))
  exact (norm_ext_le _).trans (((Sig sys L n hL hn).le_opNorm r).trans
    (mul_le_mul_of_nonneg_right (norm_Sig_le hL hn) (norm_nonneg _)))

include hKernel in
/-- **`|⟪P Σ_b W r, φ⟫| ≤ ‖W (w - P w)‖ ‖Σ_b φ‖`** for `r = S (w - P w)`. -/
lemma pair_Zw_adj_le (w : MolecularFourierH2 eta) (φ : En eta n) :
    ‖⟪ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H)
        (Sm eta L (w - molecularH2Truncate n w))), φ⟫_ℂ‖ ≤
      ‖Wp sys L H (w - molecularH2Truncate n w)‖ * ‖Sig sys L n hL hn (emb eta n φ)‖ := by
  rw [inner_ext, ContinuousLinearMap.adjoint_inner_left, Zw, ContinuousLinearMap.comp_apply]
  have h := potential_symm sys L H hKernel (w - molecularH2Truncate n w)
    (SigD sys L n hL (by omega) (emb eta n φ))
  change ⟪Sm eta L (w - molecularH2Truncate n w), Wp sys L H (SigD sys L n hL (by omega) (emb eta n φ))⟫_ℂ =
    ⟪Wp sys L H (w - molecularH2Truncate n w), Sm eta L (SigD sys L n hL (by omega) (emb eta n φ))⟫_ℂ at h
  rw [h, stateMap_SigD hL hn]
  exact norm_inner_le_norm _ _

/-- `‖Z‖ ≤ 2 C_Z`. -/
lemma norm_Zsym_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKernel' : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    ‖Zsym sys hL hn H‖ ≤ 2 * CZ sys L Hunit n := by
  have h1 := opNorm_Zw_le sys hL hn H hKernel' Hunit hPeriodic
  have h2 : ‖ContinuousLinearMap.adjoint (Zw sys hL hn H)‖ = ‖Zw sys hL hn H‖ :=
    LinearIsometryEquiv.norm_map _ _
  unfold Zsym
  refine (norm_add_le _ _).trans ?_
  rw [h2]; linarith

include hKernel in
lemma norm_R3c_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ‖R3c sys hL hn H‖ ≤ 4 * Asig sys L n ^ 2 * CX sys L Hunit n := by
  have hskew := (Sig_skew_unitary (sys := sys) hL hn).1
  have hS := norm_Sig_le (sys := sys) hL hn
  have hXn := norm_X1_le sys hL hn H hKernel Hunit hPeriodic
  refine (FSConj.norm_Bi_taylor_le hskew _).trans ?_
  calc ‖FSConj.cm (Sig sys L n hL hn) (FSConj.cm (Sig sys L n hL hn) (X1 sys hL hn H))‖
      ≤ 2 * ‖Sig sys L n hL hn‖ * ‖FSConj.cm (Sig sys L n hL hn) (X1 sys hL hn H)‖ := norm_cm_le _ _
    _ ≤ 2 * ‖Sig sys L n hL hn‖ * (2 * ‖Sig sys L n hL hn‖ * ‖X1 sys hL hn H‖) :=
        mul_le_mul_of_nonneg_left (norm_cm_le _ _) (by positivity)
    _ = 4 * ‖Sig sys L n hL hn‖ ^ 2 * ‖X1 sys hL hn H‖ := by ring
    _ ≤ 4 * Asig sys L n ^ 2 * CX sys L Hunit n := by gcongr

include hL in
lemma CDelta_nonneg (Hunit : ℝ) : 0 ≤ CDelta sys L Hunit n := by
  unfold CDelta CX
  have := CZ_nonneg sys Hunit (L := L) (n := n)
  have := CV_nonneg sys Hunit (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  positivity

/-! ## The source pairing -/

/-- The flow constant at weight `σ`. -/
noncomputable def CflS (sys : CoulombSystem eta ν) (L Hunit CΔ σ : ℝ) : ℝ :=
  Crev sys L Hunit CΔ ^ σ * (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ σ

/-- The constant `c_s = (#Ch² M₀ Z_{2s})^{1/2}` of the weighted state bound. -/
noncomputable def cSt (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  Real.sqrt (Fintype.card (Ch eta) ^ 2 * M0 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3))))

lemma CflS_nonneg (Hunit : ℝ) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (σ : ℝ) : 0 ≤ CflS sys L Hunit CΔ σ := by
  unfold CflS
  have h1 : 0 ≤ Crev sys L Hunit CΔ := by
    unfold Crev; have := (Clow_pos sys Hunit hCΔ (L := L)).le; positivity
  have h2 : 0 ≤ CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2 := by
    have := CVret_nonneg sys Hunit hCΔ (L := L)
    have := (Clow_pos sys Hunit hCΔ (L := L)).le
    linarith
  exact mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)

lemma continuous_psiT
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (u₀ : MolecularFourierH2 eta)
    (hcont : ∀ x, Continuous fun t => U t x) : Continuous (psiT sys hL hn U u₀) :=
  (exp (Sig sys L n hL hn)).continuous.comp (hcont _)

lemma continuous_rT
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (u₀ : MolecularFourierH2 eta)
    (hcont : ∀ x, Continuous fun t => U t x) :
    Continuous fun s => psiT sys hL hn U u₀ s - molecularH2Truncate n (psiT sys hL hn U u₀ s) := by
  have h := continuous_psiT sys hL hn U u₀ hcont
  have h2 : Continuous fun s => molecularH2Truncate n (psiT sys hL hn U u₀ s) := by
    have : (fun s => molecularH2Truncate n (psiT sys hL hn U u₀ s)) =
        fun s => emb eta n (ext eta n (psiT sys hL hn U u₀ s)) := by
      funext s; rw [emb_ext]
    rw [this]
    exact (emb eta n).continuous.comp ((ext eta n).continuous.comp h)
  exact h.sub h2

open Classical in
include hKernel in
/-- **The source pairing** (`thm:src3`, the source): for a good `v` and `t ≥ 1`,
`‖∫₀ᵗ ⟪Ṽ_{PR} ψ̃_R(s), e^{iH'(t-s)} A_{p₀}^E v⟫ ds‖ ≤ a t Cg Ξ √C_tavg K^{s₁-3} (1+D_K)^{s₁} + t B`,
`B = A_σ ρ √2 C_m C_fl(½) ‖(1+A)^{1/2} A^E v‖ + a c_{s₂} c_E^{s₂} C_fl(s₂) ‖(1+A)^{s₂} A^E v‖
  + (2 A_σ C_Z + 4 A_σ² C_X) ρ ‖A^E v‖`, given `‖W (w - P w)‖ ≤ a` and `‖R ψ̃‖ ≤ ρ` on `[0, t]`. -/
theorem source_pairing (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (u₀ : MolecularFourierH2 eta)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      Sm eta L u' = U t (Sm eta L u) ∧ H u' = U t (H u))
    (hcont : ∀ x, Continuous fun t => U t x)
    {s₁ s₂ : ℝ} (hs₁ : 3 / 2 < s₁) (hs₁2 : s₁ ≤ 2) (hs₂ : 3 / 4 < s₂) (hs₂1 : s₂ ≤ 1)
    (hK : TavgScale sys L Hunit (CDelta sys L Hunit n) n) (p₀ : Fin eta) {Cg Ξ t : ℝ}
    (hCgΞ : 0 ≤ Cg * Ξ) (ht : 1 ≤ t) (v : En eta n) (hv : IsGood sys L Cg Ξ v)
    {a ρ : ℝ}
    (ha : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ w : MolecularFourierH2 eta, Sm eta L w = psiT sys hL hn U u₀ s →
      ‖Wp sys L H (w - molecularH2Truncate n w)‖ ≤ a)
    (hρ : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖psiT sys hL hn U u₀ s - molecularH2Truncate n (psiT sys hL hn U u₀ s)‖ ≤ ρ) :
    ‖∫ s in (0 : ℝ)..t, ⟪fT sys hL hn H U u₀ s,
        retFlow sys L n (dH_symm sys hL hn H hKernel) (t - s) (datum sys L p₀ v)⟫_ℂ‖ ≤
      a * t * (Cg * Ξ) * Real.sqrt (Ctavg sys L Hunit (CDelta sys L Hunit n) s₁) * Kc L n ^ (s₁ - 3) *
          (1 + DK (Kc L n)) ^ s₁ +
        t * (Asig sys L n * ρ * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
            (CflS sys L Hunit (CDelta sys L Hunit n) (1 / 2) *
              ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) (datum sys L p₀ v)‖)) +
          a * (cSt sys L n s₂ * cE sys L ^ s₂ * (CflS sys L Hunit (CDelta sys L Hunit n) s₂ *
            ‖FSSpectral.wt (sb eta n) (Asym sys L n) s₂ (datum sys L p₀ v)‖)) +
          (2 * Asig sys L n * CZ sys L Hunit n + 4 * Asig sys L n ^ 2 * CX sys L Hunit n) * ρ *
            ‖datum sys L p₀ v‖) := by
  set hΔ := dH_symm sys hL hn H hKernel
  set CΔ := CDelta sys L Hunit n
  have hCΔ : 0 ≤ CΔ := CDelta_nonneg sys hL Hunit
  have hΔb : ∀ x, ‖dH sys hL hn H x‖ ≤ CΔ * ‖x‖ := norm_dH_le sys hL hn H hKernel Hunit hPeriodic
  set φ₀ := datum sys L p₀ v
  set φ : ℝ → En eta n := fun s => retFlow sys L n hΔ (t - s) φ₀
  set r : ℝ → L2 eta := fun s => psiT sys hL hn U u₀ s - molecularH2Truncate n (psiT sys hL hn U u₀ s)
  set y : ℝ → En eta n := fun s => fT sys hL hn H U u₀ s - ext eta n (Bcorr sys hL hn H (r s))
  set G : ℝ → En eta n := fun s => ext eta n (Zw sys hL hn H (r s)) +
    ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) (r s)) +
    (1 / 2 : ℂ) • ext eta n (FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) (r s)) +
    ext eta n (R3c sys hL hn H (r s))
  have ht0 : 0 < t := by linarith
  -- the preimages
  have hpre : ∀ s, ∃ w : MolecularFourierH2 eta, Sm eta L w = psiT sys hL hn U u₀ s := by
    intro s
    obtain ⟨u', hu', -⟩ := hgraph s u₀
    exact ⟨exp (SigG sys hL hn) u', by rw [exp_SigG_apply, hu']; rfl⟩
  -- `y = P W (w - P w)` and `f = (1-Q) y - G`
  have hy : ∀ s, ∀ w : MolecularFourierH2 eta, Sm eta L w = psiT sys hL hn U u₀ s →
      y s = ext eta n (Wp sys L H (w - molecularH2Truncate n w)) := by
    intro s w hw
    simp only [y, r]
    rw [fT_eq sys hL hn H hKernel U u₀ hgraph s w hw]; abel
  have hf : ∀ s, fT sys hL hn H U u₀ s = hotProj L (Kc L n / 4) (y s) - G s := by
    intro s
    obtain ⟨w, hw⟩ := hpre s
    rw [fT_decomp sys hL hn H hKernel U u₀ hgraph s w hw, hy s w hw]
    simp only [G, r]; abel
  -- continuity
  have hrc : Continuous r := continuous_rT sys hL hn U u₀ hcont
  have hyc : Continuous y :=
    (continuous_fT sys hL hn H U u₀ hcont).sub ((ext eta n).continuous.comp
      ((Bcorr sys hL hn H).continuous.comp hrc))
  have hGc : Continuous G := by
    have c1 := (ext eta n).continuous.comp ((Zw sys hL hn H).continuous.comp hrc)
    have c2 := (ext eta n).continuous.comp
      ((ContinuousLinearMap.adjoint (Zw sys hL hn H)).continuous.comp hrc)
    have c3 := ((ext eta n).continuous.comp
      ((FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H)).continuous.comp hrc)).const_smul (1 / 2 : ℂ)
    have c4 := (ext eta n).continuous.comp ((R3c sys hL hn H).continuous.comp hrc)
    exact ((c1.add c2).add c3).add c4
  have hφc : Continuous φ :=
    (continuous_retFlow sys L n hΔ φ₀).comp (continuous_const.sub continuous_id)
  have hI1 : IntervalIntegrable (fun s => ⟪hotProj L (Kc L n / 4) (y s), φ s⟫_ℂ) MeasureTheory.volume 0 t :=
    (((hotProj L (Kc L n / 4)).continuous_of_finiteDimensional.comp hyc).inner hφc).intervalIntegrable 0 t
  have hI2 : IntervalIntegrable (fun s => ⟪G s, φ s⟫_ℂ) MeasureTheory.volume 0 t :=
    (hGc.inner hφc).intervalIntegrable 0 t
  have hsplit : (∫ s in (0 : ℝ)..t, ⟪fT sys hL hn H U u₀ s, φ s⟫_ℂ) =
      (∫ s in (0 : ℝ)..t, ⟪hotProj L (Kc L n / 4) (y s), φ s⟫_ℂ) -
        ∫ s in (0 : ℝ)..t, ⟪G s, φ s⟫_ℂ := by
    rw [← intervalIntegral.integral_sub hI1 hI2]
    congr 1; funext s; rw [hf s, inner_sub_left]
  rw [hsplit]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · -- the near-cutoff part: `prop:src-nc1`
    have hya : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖y s‖ ≤ a := by
      intro s hs
      obtain ⟨w, hw⟩ := hpre s
      rw [hy s w hw]
      exact (norm_ext_le _).trans (ha s hs w hw)
    exact src_nc1_explicit sys Hunit hL hPeriodic hΔ hCΔ hΔb hs₁ hs₁2 hK p₀ hCgΞ ht v hv y hyc hya
  · -- the remaining couplings, pointwise
    have hpt : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖⟪G s, φ s⟫_ℂ‖ ≤
        Asig sys L n * ρ * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
            (CflS sys L Hunit CΔ (1 / 2) *
              ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ₀‖)) +
          a * (cSt sys L n s₂ * cE sys L ^ s₂ * (CflS sys L Hunit CΔ s₂ *
            ‖FSSpectral.wt (sb eta n) (Asym sys L n) s₂ φ₀‖)) +
          (2 * Asig sys L n * CZ sys L Hunit n + 4 * Asig sys L n ^ 2 * CX sys L Hunit n) * ρ *
            ‖φ₀‖ := by
      intro s hs
      have hs' : s ∈ Set.Icc (0 : ℝ) t := by
        rw [Set.uIoc_of_le ht0.le] at hs; exact ⟨hs.1.le, hs.2⟩
      obtain ⟨w, hw⟩ := hpre s
      have hrw : r s = Sm eta L (w - molecularH2Truncate n w) := by
        simp only [r]
        rw [map_sub, hw, show Sm eta L (molecularH2Truncate n w) = molecularH2Truncate n (Sm eta L w)
          from stateMap_truncate (gF L) n w, hw]
      have hrP : molecularH2Truncate n (r s) = 0 := by
        simp only [r]; rw [molecularH2Truncate_sub, truncate_truncate, sub_self]
      have hρs := hρ s hs'
      have hA0 := Asig_nonneg (sys := sys) (n := n) hL
      have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
      have hφn : ‖φ s‖ = ‖φ₀‖ := norm_retFlow sys L n hΔ _ _
      -- the four pairings
      have k1 : ‖⟪ext eta n (Zw sys hL hn H (r s)), φ s⟫_ℂ‖ ≤
          Asig sys L n * ρ * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
            (CflS sys L Hunit CΔ (1 / 2) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ₀‖)) := by
        refine (pair_Zw_le sys hL hn H hKernel Hunit hPeriodic (r s) hrP (φ s)).trans ?_
        have hfl : ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) (φ s)‖ ≤
            CflS sys L Hunit CΔ (1 / 2) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ₀‖ :=
          retflow sys Hunit hL hPeriodic hΔ hCΔ hΔb (s := 1 / 2) ⟨by norm_num, by norm_num⟩
            (t - s) φ₀
        have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) hρs
        exact mul_le_mul (mul_le_mul_of_nonneg_left hρs hA0)
          (mul_le_mul_of_nonneg_left hfl (by positivity)) (by positivity) (by positivity)
      have k2 : ‖⟪ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) (r s)), φ s⟫_ℂ‖ ≤
          a * (cSt sys L n s₂ * cE sys L ^ s₂ * (CflS sys L Hunit CΔ s₂ *
            ‖FSSpectral.wt (sb eta n) (Asym sys L n) s₂ φ₀‖)) := by
        rw [hrw]
        refine (pair_Zw_adj_le sys hL hn H hKernel w (φ s)).trans ?_
        have hfl := retflow sys Hunit hL hPeriodic hΔ hCΔ hΔb (s := s₂) ⟨by linarith, hs₂1⟩
          (t - s) φ₀
        have hst := norm_sig_emb_wt_le sys hL hn hs₂ (φ s)
        have hcE := one_le_cE sys (L := L)
        refine mul_le_mul (ha s hs' w hw) (hst.trans ?_) (norm_nonneg _)
          ((norm_nonneg _).trans (ha s hs' w hw))
        unfold cSt
        exact mul_le_mul_of_nonneg_left hfl (mul_nonneg (Real.sqrt_nonneg _)
          (Real.rpow_nonneg (by linarith) _))
      have k3 : ‖⟪(1 / 2 : ℂ) • ext eta n (FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) (r s)),
          φ s⟫_ℂ‖ ≤ 2 * Asig sys L n * CZ sys L Hunit n * ρ * ‖φ₀‖ := by
        rw [inner_smul_left, norm_mul]
        have : ‖(starRingEnd ℂ) (1 / 2 : ℂ)‖ = 1 / 2 := by simp
        rw [this]
        refine (mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)).trans ?_
        rw [hφn]
        have hcm : ‖FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H)‖ ≤
            2 * Asig sys L n * (2 * CZ sys L Hunit n) :=
          (norm_cm_le _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (norm_Sig_le hL hn)
            (by norm_num)) (norm_Zsym_le sys hL hn H Hunit hPeriodic hKernel) (norm_nonneg _)
            (by positivity))
        have hCZ0 := CZ_nonneg sys Hunit (L := L) (n := n)
        have h1 : ‖ext eta n (FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) (r s))‖ ≤
            2 * Asig sys L n * (2 * CZ sys L Hunit n) * ρ :=
          (norm_ext_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul hcm hρs (norm_nonneg _) (by positivity)))
        calc 1 / 2 * (‖ext eta n (FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) (r s))‖ * ‖φ₀‖)
            ≤ 1 / 2 * (2 * Asig sys L n * (2 * CZ sys L Hunit n) * ρ * ‖φ₀‖) := by gcongr
          _ = _ := by ring
      have k4 : ‖⟪ext eta n (R3c sys hL hn H (r s)), φ s⟫_ℂ‖ ≤
          4 * Asig sys L n ^ 2 * CX sys L Hunit n * ρ * ‖φ₀‖ := by
        refine (norm_inner_le_norm _ _).trans ?_
        rw [hφn]
        refine mul_le_mul_of_nonneg_right ((norm_ext_le _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (norm_R3c_le sys hL hn H hKernel Hunit hPeriodic) hρs (norm_nonneg _) ?_))) (norm_nonneg _)
        have := norm_X1_le sys hL hn H hKernel Hunit hPeriodic
        have : 0 ≤ CX sys L Hunit n := le_trans (norm_nonneg _) this
        positivity
      simp only [G, inner_add_left]
      calc _ ≤ ‖⟪ext eta n (Zw sys hL hn H (r s)), φ s⟫_ℂ‖ +
            ‖⟪ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) (r s)), φ s⟫_ℂ‖ +
            ‖⟪(1 / 2 : ℂ) • ext eta n (FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) (r s)), φ s⟫_ℂ‖ +
            ‖⟪ext eta n (R3c sys hL hn H (r s)), φ s⟫_ℂ‖ := norm_add₄_le
        _ ≤ _ := by
            have e : (2 * Asig sys L n * CZ sys L Hunit n + 4 * Asig sys L n ^ 2 * CX sys L Hunit n) *
                ρ * ‖φ₀‖ = 2 * Asig sys L n * CZ sys L Hunit n * ρ * ‖φ₀‖ +
                  4 * Asig sys L n ^ 2 * CX sys L Hunit n * ρ * ‖φ₀‖ := by ring
            linarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [sub_zero, abs_of_nonneg ht0.le] at this
    calc _ ≤ _ := this
      _ = _ := by ring

end FSNormal
