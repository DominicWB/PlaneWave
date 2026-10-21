import PlaneWave.Source.ObservableNonsecular

/-!
# Flux/source build, block 3g: the first retained correction on good states, and the coupling

* `form_emb_le`: `Σ (1 + 2E) |v|² ≤ 2 Θ(v)²` for cube vectors; `‖W v‖ ≤ √2 C_m Θ(v)`;
* `norm_Zw_emb_le`, `norm_Zw_adj_emb_le`, `norm_Vb_emb_le`: `‖W Σ_b v‖ ≤ 2 C_m a₁ Θ(v)`,
  `‖Σ_b W v‖ ≤ √2 A_σ C_m Θ(v)`, `‖V_b v‖ ≤ √2 C_m Θ(v)`;
* **`norm_dH_le_wt`** (the stability hypothesis of `lem:good-stab` for `D_K = P H̃ P - H_N`):
  `‖ΔH v‖ ≤ α_Δ Θ(v)` with `α_Δ = O(K^{-1})`;
* the general-weight state bound `‖Σ_b v‖ ≤ (#Ch² M₀ Z_{2s})^{1/2} c_E^s ‖(1+A)^s v‖`
  (`norm_sig_emb_wt_le`, eq:bulk-weighted-state at `j = 0`);
* `Vb_exterior`: `V_b R x = Q W R x`; `PSigVbR`: `P [Σ_b, V_b] R = 0` (block parity);
* **`fT_decomp`**: the coupling `Ṽ_{PR} ψ̃_R` is
  `(1 - Q) P W (w - P w) - P W Σ_b r - P (W Σ_b)† r - ½ P [Σ_b, Z] r - P R₃ r`
  (`r = R ψ̃`, `Z = W Σ_D + (W Σ_D)†`, `R₃` the third-order remainder of `B`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic NormedSpace FluxSourceTest
  FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)

/-! ## Forms of cube vectors -/

open Classical in
omit [Fintype ν] in
lemma form_emb (v : En eta n) :
    ∑' q, (1 + 2 * Ek sys L q) * ‖emb eta n v q‖ ^ 2 =
      ∑ p, (1 + 2 * Asym sys L n p) * ‖v.ofLp p‖ ^ 2 := by
  have hz : ∀ q ∉ fourierConfigCube eta n, (1 + 2 * Ek sys L q) * ‖emb eta n v q‖ ^ 2 = 0 := by
    intro q hq
    simp only [emb, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply]
    rw [finiteFourierLpEmbed_apply_not_mem_cube eta n _ q hq]; simp
  rw [tsum_eq_sum hz]
  unfold fourierConfigCube
  rw [Finset.sum_image (fun p _ q _ h => finiteConfigLatticeIndex_injective eta n h)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [emb, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply,
    finiteFourierLpEmbed_apply_index]
  rw [Asym_eq_Ek]

omit [Fintype ν] in
lemma form_emb_le (v : En eta n) :
    ∑' q, (1 + 2 * Ek sys L q) * ‖emb eta n v q‖ ^ 2 ≤
      2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ ^ 2 := by
  rw [form_emb, norm_sq_wt, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Real.rpow_one]
  have h0 := Asym_nonneg sys L n p
  nlinarith [sq_nonneg ‖v.ofLp p‖, sq_nonneg (Asym sys L n p)]

variable (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel hL in
/-- `‖W v‖ ≤ √2 C_m Θ(v)` for cube vectors (Hardy). -/
lemma norm_W_cubeLift_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖Wp sys L H (cubeLift (gF L) n v)‖ ≤
      Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  have h := potential_form_bound sys H hKernel Hunit hL hPeriodic (cubeLift (gF L) n v)
  rw [stateMap_cubeLift'] at h
  have h2 := form_emb_le sys (L := L) v
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have h3 : ‖Wp sys L H (cubeLift (gF L) n v)‖ ^ 2 ≤ (Real.sqrt 2 *
      finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc _ ≤ _ := h
      _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          (2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

/-- `Σ_D (emb v) = Σ_D (Q emb v)`. -/
lemma SigD_emb (v : En eta n) :
    SigD sys L n hL (by omega) (emb eta n v) =
      SigD sys L n hL (by omega) (lpTruncate (Qs eta n) (emb eta n v)) := by
  apply molecularH2StateMap_injective eta (gF L)
  change Sm eta L _ = Sm eta L _
  rw [stateMap_SigD hL hn, stateMap_SigD hL hn, sig_emb sys hL hn v]

include hKernel in
/-- **`‖W Σ_b v‖ ≤ 2 C_m a₁ Θ(v)`** for cube vectors. -/
lemma norm_Zw_emb_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖Zw sys hL hn H (emb eta n v)‖ ≤
      2 * finiteCoulombPhysicalMassConstant sys L Hunit * a1c sys L n *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  have hZ : Zw sys hL hn H (emb eta n v) =
      Wp sys L H (SigD sys L n hL (by omega) (lpTruncate (Qs eta n) (emb eta n v))) := by
    rw [Zw, ContinuousLinearMap.comp_apply, SigD_emb sys hL hn v]
  rw [hZ]
  have hf := potential_form_bound sys H hKernel Hunit hL hPeriodic
    (SigD sys L n hL (by omega) (lpTruncate (Qs eta n) (emb eta n v)))
  rw [show Sm eta L (SigD sys L n hL (by omega) (lpTruncate (Qs eta n) (emb eta n v))) =
    Sig sys L n hL hn (lpTruncate (Qs eta n) (emb eta n v)) from stateMap_SigD hL hn _] at hf
  have hform := form_sigQ_le sys hL hn (cubeLift (gF L) n v)
  rw [stateMap_cubeLift', norm_emb, norm_kinetic_cubeLift] at hform
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have ha1 := a1c_nonneg sys (L := L) (n := n)
  have hθ : ‖v‖ + ‖FSSpectral.kin (sb eta n) (Asym sys L n) v‖ ≤
      2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
    have := norm_le_wt sys L n zero_le_one v; have := norm_kin_le_wt sys (L := L) v; linarith
  have h2 : ‖Wp sys L H (SigD sys L n hL (by omega) (lpTruncate (Qs eta n) (emb eta n v)))‖ ^ 2 ≤
      (2 * finiteCoulombPhysicalMassConstant sys L Hunit * a1c sys L n *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖) ^ 2 := by
    calc _ ≤ _ := hf
      _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          (a1c sys L n * (‖v‖ + ‖FSSpectral.kin (sb eta n) (Asym sys L n) v‖)) ^ 2 :=
          mul_le_mul_of_nonneg_left hform (sq_nonneg _)
      _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          (a1c sys L n * (2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖)) ^ 2 := by
          gcongr
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

include hKernel in
/-- **`‖(W Σ_b)† v‖ = ‖Σ_b W v‖ ≤ √2 A_σ C_m Θ(v)`** for cube vectors. -/
lemma norm_Zw_adj_emb_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖ContinuousLinearMap.adjoint (Zw sys hL hn H) (emb eta n v)‖ ≤
      Asig sys L n * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖) := by
  have h := congrArg (fun A : L2 eta →L[ℂ] L2 eta => A (cubeLift (gF L) n v))
    (sig_W sys hL hn H hKernel)
  simp only [mul_apply_eq_comp, neg_apply] at h
  rw [stateMap_cubeLift'] at h
  have e : ContinuousLinearMap.adjoint (Zw sys hL hn H) (emb eta n v) =
      -Sig sys L n hL hn (Wp sys L H (cubeLift (gF L) n v)) := by rw [h, neg_neg]
  rw [e, norm_neg]
  exact ((Sig sys L n hL hn).le_opNorm _).trans (mul_le_mul (norm_Sig_le hL hn)
    (norm_W_cubeLift_le sys hL H hKernel Hunit hPeriodic v) (norm_nonneg _) (Asig_nonneg hL))

open Classical in
include hKernel in
/-- **`‖V_b v‖ ≤ √2 C_m Θ(v)`** for cube vectors (only the outgoing orientation survives). -/
lemma norm_Vb_emb_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖Vb sys L n hL (emb eta n v)‖ ≤
      Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  set e := emb eta n v
  have hpt : ∀ q, ‖Vb sys L n hL e q‖ ≤ 1 * ‖Wp sys L H (liftQ L n e) q‖ := by
    intro q
    rw [one_mul]
    by_cases hq : InQ (n : ℝ) q
    · rw [Vb_apply]
      have : ∑' p, vbK sys L n q p * e p = 0 := by
        refine (tsum_congr fun p => ?_).trans tsum_zero
        unfold vbK
        split_ifs with hc
        · have hp := not_inP_of_cross_inQ hc hq
          have : e p = 0 := by
            have := congrArg (fun x : L2 eta => x p) (trunc_emb (n := n) v)
            simp only at this
            rw [← this, molecularH2Truncate_apply,
              cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ p
                (fun h => hp ((inP_iff_mem_cube n p).mpr h))]
          rw [this, mul_zero]
        · rw [zero_mul]
      rw [this, norm_zero]; exact norm_nonneg _
    · rw [Vb_apply_out sys H hKernel hL n e hq]
      split_ifs
      · rw [norm_zero]; exact norm_nonneg _
      · exact le_rfl
  refine (l2_norm_le_of_le _ _ zero_le_one hpt).trans ?_
  rw [one_mul]
  have h := potential_form_bound sys H hKernel Hunit hL hPeriodic (liftQ L n e)
  rw [stateMap_liftQ] at h
  have hform : ∑' q, (1 + 2 * Ek sys L q) * ‖lpTruncate (Qs eta n) e q‖ ^ 2 ≤
      ∑' q, (1 + 2 * Ek sys L q) * ‖e q‖ ^ 2 := by
    refine Summable.tsum_le_tsum (fun q => ?_) ?_ (summable_form sys (cubeLift (gF L) n v) |>.congr
      fun q => by rw [stateMap_cubeLift'])
    · refine mul_le_mul_of_nonneg_left ?_ (by linarith [one_le_one_add_two_Ek sys L q])
      rw [lpTruncate_apply]; split_ifs
      · exact le_rfl
      · rw [norm_zero]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact sq_nonneg _
    · exact (summable_form sys (liftQ L n e)).congr fun q => by rw [stateMap_liftQ]
  have h2 := form_emb_le sys (L := L) v
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have h3 : ‖Wp sys L H (liftQ L n e)‖ ^ 2 ≤ (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc _ ≤ _ := h
      _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          (2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hform.trans h2) (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

/-! ## The relative bound for the first retained correction -/

/-- The relative constant `α_Δ` of `‖ΔH v‖ ≤ α_Δ Θ(v)`. -/
noncomputable def alphaD (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  let Cm := finiteCoulombPhysicalMassConstant sys L Hunit
  let A := Asig sys L n
  (2 * Cm * a1c sys L n + A * (Real.sqrt 2 * Cm)) +
    1 / 2 * (A * (Real.sqrt 2 * Cm + 2 * Cm * a1c sys L n + A * (Real.sqrt 2 * Cm)) +
      CX sys L Hunit n * (2 * a0c sys L n)) +
    4 * A ^ 2 * CX sys L Hunit n

include hKernel in
/-- **The stability hypothesis for `P H̃ P - H_N`**: `‖ΔH v‖ ≤ α_Δ Θ(v)`, `α_Δ = O(K^{-1})`. -/
theorem norm_dH_le_wt (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖dH sys hL hn H v‖ ≤ alphaD sys L Hunit n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  set Sg := Sig sys L n hL hn
  set X := X1 sys hL hn H
  set R3 := FSConj.Bi Sg X - X - (1 / 2 : ℂ) • FSConj.cm Sg X
  set e := emb eta n v
  set Θ := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖
  set Cm := finiteCoulombPhysicalMassConstant sys L Hunit
  have hCm : 0 ≤ Cm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hA0 := Asig_nonneg (sys := sys) (n := n) hL
  have hA := norm_Sig_le (sys := sys) hL hn
  have ha0 := a0c_nonneg sys (L := L) (n := n)
  have ha1 := a1c_nonneg sys (L := L) (n := n)
  have hΘ0 : 0 ≤ Θ := norm_nonneg _
  have hvΘ : ‖v‖ ≤ Θ := norm_le_wt sys L n zero_le_one v
  have hskew := (Sig_skew_unitary (sys := sys) hL hn).1
  have hCX := norm_X1_le sys hL hn H hKernel Hunit hPeriodic
  have hCX0 : 0 ≤ CX sys L Hunit n := le_trans (norm_nonneg _) hCX
  have hR3 : ‖R3‖ ≤ 4 * Asig sys L n ^ 2 * CX sys L Hunit n := by
    refine (FSConj.norm_Bi_taylor_le hskew X).trans ?_
    calc ‖FSConj.cm Sg (FSConj.cm Sg X)‖ ≤ 2 * ‖Sg‖ * ‖FSConj.cm Sg X‖ := norm_cm_le _ _
      _ ≤ 2 * ‖Sg‖ * (2 * ‖Sg‖ * ‖X‖) :=
          mul_le_mul_of_nonneg_left (norm_cm_le _ _) (by positivity)
      _ = 4 * ‖Sg‖ ^ 2 * ‖X‖ := by ring
      _ ≤ 4 * Asig sys L n ^ 2 * CX sys L Hunit n := by gcongr
  have hdec : Bcorr sys hL hn H = -(X + (1 / 2 : ℂ) • FSConj.cm Sg X + R3) := by
    simp only [Bcorr, R3]; abel
  -- the pieces on `e`
  have hZ := norm_Zw_emb_le sys hL hn H hKernel Hunit hPeriodic v
  have hZa := norm_Zw_adj_emb_le sys hL hn H hKernel Hunit hPeriodic v
  have hVb := norm_Vb_emb_le sys hL H hKernel Hunit hPeriodic v
  have hVb0 : ext eta n (Vb sys L n hL e) = 0 := by
    have h := PVbP sys hL (n := n) e (trunc_emb v)
    have := congrArg (ext eta n) h
    rwa [← emb_ext, ext_emb, map_zero] at this
  have hXe : ‖X e‖ ≤ Real.sqrt 2 * Cm * Θ + 2 * Cm * a1c sys L n * Θ +
      Asig sys L n * (Real.sqrt 2 * Cm * Θ) := by
    simp only [X, X1, add_apply]
    refine (norm_add₃_le).trans ?_
    linarith
  have hSe := norm_sig_emb_le' sys hL hn v
  have hcm : ‖FSConj.cm Sg X e‖ ≤ Asig sys L n * (Real.sqrt 2 * Cm * Θ + 2 * Cm * a1c sys L n * Θ +
      Asig sys L n * (Real.sqrt 2 * Cm * Θ)) + CX sys L Hunit n * (2 * a0c sys L n * Θ) := by
    unfold FSConj.cm
    rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (Sg.le_opNorm _).trans (mul_le_mul hA hXe (norm_nonneg _) hA0)
    · exact (X.le_opNorm _).trans (mul_le_mul hCX hSe (norm_nonneg _) hCX0)
  rw [dH_apply, hdec, neg_apply, map_neg, norm_neg, add_apply, add_apply, map_add, map_add]
  have hXe' : ext eta n (X e) = ext eta n (Zw sys hL hn H e) +
      ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) e) := by
    simp only [X, X1, add_apply, map_add, hVb0, zero_add]
  rw [hXe']
  calc ‖ext eta n (Zw sys hL hn H e) + ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) e) +
        ext eta n (((1 / 2 : ℂ) • FSConj.cm Sg X) e) + ext eta n (R3 e)‖
      ≤ ‖Zw sys hL hn H e‖ + ‖ContinuousLinearMap.adjoint (Zw sys hL hn H) e‖ +
          ‖((1 / 2 : ℂ) • FSConj.cm Sg X) e‖ + ‖R3 e‖ := by
        refine norm_add₄_le.trans ?_
        gcongr <;> exact norm_ext_le _
    _ ≤ 2 * Cm * a1c sys L n * Θ + Asig sys L n * (Real.sqrt 2 * Cm * Θ) +
          1 / 2 * (Asig sys L n * (Real.sqrt 2 * Cm * Θ + 2 * Cm * a1c sys L n * Θ +
            Asig sys L n * (Real.sqrt 2 * Cm * Θ)) + CX sys L Hunit n * (2 * a0c sys L n * Θ)) +
          4 * Asig sys L n ^ 2 * CX sys L Hunit n * Θ := by
        gcongr
        · rw [smul_apply, norm_smul]
          have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
          rw [this]; exact mul_le_mul_of_nonneg_left hcm (by norm_num)
        · refine (R3.le_opNorm e).trans ?_
          rw [norm_emb]
          exact mul_le_mul hR3 hvΘ (norm_nonneg _) (by positivity)
    _ = alphaD sys L Hunit n * Θ := by unfold alphaD; ring

/-! ## The state bound with a general weight -/

open Classical in
/-- **eq:bulk-weighted-state, `j = 0`, weight `s`**:
`‖Σ_b v‖ ≤ (#Ch² M₀ Z_{2s})^{1/2} c_E^s ‖(1+A)^s v‖` for cube vectors, `3/4 < s`. -/
theorem norm_sig_emb_wt_le {s : ℝ} (hs : 3 / 4 < s) (v : En eta n) :
    ‖Sig sys L n hL hn (emb eta n v)‖ ≤
      Real.sqrt (Fintype.card (Ch eta) ^ 2 * M0 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3)))) *
        cE sys L ^ s * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ := by
  rw [sig_emb sys hL hn v]
  set x := emb eta n v
  have h := norm_sig_Q_state_le sys hL hn hs x
  have hs0 : 0 ≤ s := by linarith
  have hcE := one_le_cE sys (L := L)
  have hM0 : 0 ≤ M0 sys L n := by
    rw [M0_eq sys (by omega)]; have := cM0_nonneg sys (L := L); positivity
  have hZ : 0 ≤ 1 + 26 * (1 + 1 / (2 * (2 * s) - 3)) := by
    have : 0 < 2 * (2 * s) - 3 := by linarith
    positivity
  -- the weighted sum
  have hW : ∑ p ∈ Qs eta n, Ws s p * ‖x p‖ ^ 2 ≤
      (cE sys L ^ s) ^ 2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ ^ 2 := by
    have hsub : Qs eta n ⊆ fourierConfigCube eta n := fun q hq =>
      (inP_iff_mem_cube n q).mp ((mem_Qs.mp hq).inP (Nat.cast_nonneg n))
    have h1 : ∑ p ∈ Qs eta n, Ws s p * ‖x p‖ ^ 2 ≤
        ∑ p ∈ fourierConfigCube eta n, Ws s p * ‖x p‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
        mul_nonneg (Ws_pos s p).le (sq_nonneg _)
    refine h1.trans ?_
    unfold fourierConfigCube
    rw [Finset.sum_image (fun p _ q _ h => finiteConfigLatticeIndex_injective eta n h), norm_sq_wt,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have hxc : x (finiteConfigLatticeIndex eta n c) = v.ofLp c := by
      simp only [x, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply,
        finiteFourierLpEmbed_apply_index]
    rw [hxc]
    have hle := one_add_lsqC_le sys hL (finiteConfigLatticeIndex eta n c)
    rw [← Asym_eq_Ek] at hle
    have hA0 := Asym_nonneg sys L n c
    have hl0 : 0 ≤ 1 + lsqC (finiteConfigLatticeIndex eta n c) := by
      linarith [lsqC_nonneg (finiteConfigLatticeIndex eta n c)]
    have hW' : Ws s (finiteConfigLatticeIndex eta n c) ≤ (cE sys L ^ s) ^ 2 * ((1 + Asym sys L n c) ^ s) ^ 2 := by
      unfold Ws
      rw [← mul_pow, ← Real.mul_rpow (by linarith) (by linarith), ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity)]
      rw [show (s * ((2 : ℕ) : ℝ)) = 2 * s by push_cast; ring]
      exact Real.rpow_le_rpow hl0 hle (by linarith)
    calc Ws s (finiteConfigLatticeIndex eta n c) * ‖v.ofLp c‖ ^ 2 ≤
          (cE sys L ^ s) ^ 2 * ((1 + Asym sys L n c) ^ s) ^ 2 * ‖v.ofLp c‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hW' (sq_nonneg _)
      _ = _ := by ring
  have h2 : ‖Sig sys L n hL hn (lpTruncate (Qs eta n) x)‖ ^ 2 ≤
      (Real.sqrt (Fintype.card (Ch eta) ^ 2 * M0 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3)))) *
        cE sys L ^ s * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖) ^ 2 := by
    rw [← tsum_sq_coord, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    calc _ ≤ _ := h
      _ ≤ Fintype.card (Ch eta) ^ 2 * M0 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3))) *
          ((cE sys L ^ s) ^ 2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ cE sys L) s
    positivity) two_ne_zero).mp h2

/-! ## The coupling `Ṽ_{PR} ψ̃_R` -/

open Classical in
include hKernel in
/-- **`V_b R = Q W R`**: for `u ∈ H²` with `S u` vanishing on the cube,
`V_b (S u) = 1_Q W u`. -/
theorem Vb_exterior (u : MolecularFourierH2 eta) (hu : ∀ p, InP (n : ℝ) p → Sm eta L u p = 0) :
    Vb sys L n hL (Sm eta L u) = lpTruncate (Qs eta n) (Wp sys L H u) := by
  ext q
  rw [Vb_apply, lpTruncate_apply]
  split_ifs with hq
  · have hpa : Wp sys L H u q = ∑' p, molecularH2Coeff (gF L) u p * potKernel sys L q p :=
      potential_apply sys L H hKernel hL u q
    rw [hpa]
    refine tsum_congr fun p => ?_
    have hq' := mem_Qs.mp hq
    have hc : Sm eta L u p = molecularH2Coeff (gF L) u p := molecularH2StateMap_apply _ u p
    unfold vbK
    by_cases hp : InP (n : ℝ) p
    · rw [if_neg (fun h => (inQ_not_cross_left hq').mp h hp), zero_mul]
      rw [← hc, hu p hp, zero_mul]
    · rw [if_pos ((inQ_not_cross_left hq').mpr hp), hc, mul_comm]
  · refine (tsum_congr fun p => ?_).trans tsum_zero
    unfold vbK
    split_ifs with hc
    · rcases hc with ⟨hq', -⟩ | ⟨-, hp⟩
      · exact absurd (mem_Qs.mpr hq') hq
      · rw [hu p (hp.inP (Nat.cast_nonneg n)), mul_zero]
    · rw [zero_mul]

omit [Fintype ν] in
lemma inP_of_mem_cube {p : Cf eta} (hp : p ∈ fourierConfigCube eta n) : InP (n : ℝ) p :=
  (inP_iff_mem_cube n p).mpr hp

open Classical in
/-- **`P [Σ_b, V_b] R = 0`** (block parity). -/
theorem PSigVbR (x : L2 eta) (hx : molecularH2Truncate n x = 0) :
    molecularH2Truncate n (FSConj.cm (Sig sys L n hL hn) (Vb sys L n hL) x) = 0 := by
  set Sg := Sig sys L n hL hn
  set V := Vb sys L n hL
  -- `V x` is supported in `Q`
  have hVsupp : V x - molecularH2Truncate n (V x) = 0 := by
    ext q
    rw [sub_truncate_apply, lp.coeFn_zero, Pi.zero_apply]
    split_ifs with hqP
    · rfl
    · rw [Vb_apply]
      refine (tsum_congr fun p => ?_).trans tsum_zero
      unfold vbK
      split_ifs with hc
      · rcases hc with ⟨hq', -⟩ | ⟨-, hp⟩
        · exact absurd (hq'.inP (Nat.cast_nonneg n)) hqP
        · have hpP : p ∈ fourierConfigCube eta n :=
            (inP_iff_mem_cube n p).mp (hp.inP (Nat.cast_nonneg n))
          have := congrArg (fun y : L2 eta => y p) hx
          simp only [molecularH2Truncate_apply, cubicLatticeCoeffTruncate_eq_of_mem n _ p hpP,
            lp.coeFn_zero, Pi.zero_apply] at this
          rw [this, mul_zero]
      · rw [zero_mul]
  -- `Σ x` lies in the cube
  have hSx : molecularH2Truncate n (Sg x) = Sg x := by
    rw [sig_interior sys hL hn x, hx, sub_zero]
  unfold FSConj.cm
  rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, molecularH2Truncate_sub,
    sig_interior sys hL hn (V x), hVsupp, map_zero, PVbP sys hL (Sg x) hSx, sub_zero]

open Classical in
omit [Fintype ν] in
include hL in
/-- On the cube, `1 - Q` is the hot projector `hotProj (K/4)`. -/
lemma ext_sub_truncQ (y : L2 eta) :
    ext eta n y - ext eta n (lpTruncate (Qs eta n) y) = hotProj L (Kc L n / 4) (ext eta n y) := by
  ext p
  rw [PiLp.sub_apply, extractCLM_apply, extractCLM_apply, lpTruncate_apply]
  unfold hotProj
  rw [cfgMul_apply, extractCLM_apply]
  have hiff := inQ_idx_iff (L := L) hL p
  by_cases hq : finiteConfigLatticeIndex eta n p ∈ Qs eta n
  · have h1 := hiff.mp (mem_Qs.mp hq)
    rw [if_pos hq, if_neg (by push Not; exact h1)]; simp
  · have h1 : ∃ a, Kc L n / 4 < finitePlaneWaveKabs (2 * Real.pi / L) n (p a) := by
      by_contra hno; push Not at hno; exact hq (mem_Qs.mpr (hiff.mpr hno))
    rw [if_neg hq, if_pos h1]; simp

end FSNormal
