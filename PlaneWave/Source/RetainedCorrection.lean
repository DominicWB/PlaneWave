import PlaneWave.Source.FibreBounds

/-!
# Flux/source build, block 3c: `‖W Σ_b‖ ≤ C` and the retained correction

* `sig_supp_of_out`: `Σ_b` maps vectors vanishing on `Q` into vectors supported in `Q`;
* **`norm_Zw_le`** (`lem:bulk-weighted`: `W Σ_b` extends to a bounded operator of norm `C`):
  `‖W Σ_D x‖ ≤ C_Z ‖x‖`, `C_Z = C_m (2 C_op + 2 (1 + η g² n²/16) A_σ²)^{1/2}`, uniformly bounded in
  `n` (`C_op` from eq:bulk-weighted-op, `(1 + η g² n²/16) A_σ² = O(1)`);
* `norm_X1_le`: `‖X₁‖ = ‖[H, Σ_b]‖ ≤ ‖V_b‖ + 2 ‖W Σ_D‖`;
* `PVbP`: `P V_b P = 0` (the crossings leave the cube);
* **`norm_dH_le`** (`cor:opnorm`, first retained correction): `‖ΔH v‖ ≤ C_Δ ‖v‖` with
  `C_Δ = 2 C_Z + A_σ C_X + 4 A_σ² C_X`, `C_X = 2 C_m (1 + η g² n²/16)^{1/2} + 2 C_Z` (uniformly bounded:
  `A_σ C_X = O(1)`), from the second-order expansion `B = -X₁ - ½[Σ, X₁] + O(‖[Σ,[Σ,X₁]]‖)` and
  `P X₁ P = P (W Σ_D + (W Σ_D)†) P`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics NormedSpace FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-! ## Support of `Σ_b` -/

open Classical in
/-- `Σ_b` maps vectors vanishing on `Q` into vectors supported in `Q`. -/
lemma sig_supp_of_out (y : L2 eta) (hy : ∀ p ∈ Qs eta n, y p = 0) (q : Cf eta)
    (hq : q ∉ Qs eta n) : Sig sys L n hL hn y q = 0 := by
  rw [Sig_apply]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  unfold sigK
  split_ifs with hc
  · rcases hc with ⟨hq', -⟩ | ⟨-, hp⟩
    · exact absurd (mem_Qs.mpr hq') hq
    · rw [hy p (mem_Qs.mpr hp), mul_zero]
  · rw [zero_mul]

open Classical in
lemma norm_sub_truncQ_le (x : L2 eta) : ‖x - lpTruncate (Qs eta n) x‖ ≤ ‖x‖ := by
  have := l2_norm_le_of_le (x - lpTruncate (Qs eta n) x) x zero_le_one fun p => by
    rw [lp.coeFn_sub, Pi.sub_apply, lpTruncate_apply, one_mul]
    split_ifs
    · rw [sub_self, norm_zero]; exact norm_nonneg _
    · rw [sub_zero]
  rwa [one_mul] at this

/-! ## `‖W Σ_b‖ ≤ C` -/

/-- The constant of eq:bulk-weighted-op. -/
noncomputable def Cop (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Fintype.card (Ch eta) ^ 2 * M1 sys L n * (2 * ⌈(n : ℝ) / 4⌉₊ + 1 : ℝ) ^ 3

/-- `C_Z = C_m (2 C_op + 2 (1 + η g² n²/16) A_σ²)^{1/2}`. -/
noncomputable def CZ (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  finiteCoulombPhysicalMassConstant sys L Hunit *
    Real.sqrt (2 * Cop sys L n + 2 * (1 + eta * gF L ^ 2 * n ^ 2 / 16) * Asig sys L n ^ 2)

omit [Fintype ν] in
lemma Ek_le_of_mem_Qs (n : ℕ) {q : Cf eta} (hq : q ∈ Qs eta n) :
    1 + 2 * Ek sys L q ≤ 1 + eta * gF L ^ 2 * n ^ 2 / 16 := by
  have := Ek_le_of_inQ (sys := sys) (L := L) (mem_Qs.mp hq)
  linarith

include hKernel in
/-- **`‖W Σ_b‖ ≤ C`** (`lem:bulk-weighted`). -/
theorem norm_Zw_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (x : L2 eta) : ‖Zw sys hL hn H x‖ ≤ CZ sys L Hunit n * ‖x‖ := by
  classical
  set y := lpTruncate (Qs eta n) x
  set z := x - y
  set Sg := Sig sys L n hL hn
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hform := potential_form_bound sys H hKernel Hunit hL hPeriodic (SigD sys L n hL (by omega) x)
  rw [show Sm eta L (SigD sys L n hL (by omega) x) = Sg x from stateMap_SigD hL hn x] at hform
  have hsplit : Sg x = Sg y + Sg z := by rw [← map_add]; simp only [z]; abel_nf
  -- the two forms
  obtain ⟨hs1, h1⟩ := form_sig_Q_le sys hL hn x
  have hzsupp : ∀ q ∉ Qs eta n, Sg z q = 0 := by
    refine sig_supp_of_out sys hL hn z (fun p hp => ?_)
    simp only [z, y, lp.coeFn_sub, Pi.sub_apply, lpTruncate_apply, if_pos hp, sub_self]
  have hs2 : Summable fun q => (1 + 2 * Ek sys L q) * ‖Sg z q‖ ^ 2 :=
    summable_of_ne_finset_zero (s := Qs eta n) fun q hq => by rw [hzsupp q hq]; simp
  have h2 : ∑' q, (1 + 2 * Ek sys L q) * ‖Sg z q‖ ^ 2 ≤
      (1 + eta * gF L ^ 2 * n ^ 2 / 16) * Asig sys L n ^ 2 * ‖x‖ ^ 2 := by
    rw [tsum_eq_sum (s := Qs eta n) fun q hq => by rw [hzsupp q hq]; simp]
    calc ∑ q ∈ Qs eta n, (1 + 2 * Ek sys L q) * ‖Sg z q‖ ^ 2
        ≤ ∑ q ∈ Qs eta n, (1 + eta * gF L ^ 2 * n ^ 2 / 16) * ‖Sg z q‖ ^ 2 :=
          Finset.sum_le_sum fun q hq =>
            mul_le_mul_of_nonneg_right (Ek_le_of_mem_Qs sys n hq) (sq_nonneg _)
      _ = (1 + eta * gF L ^ 2 * n ^ 2 / 16) * ∑ q ∈ Qs eta n, ‖Sg z q‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (1 + eta * gF L ^ 2 * n ^ 2 / 16) * ‖Sg z‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (sum_Qs_sq_le n _) (by positivity)
      _ ≤ (1 + eta * gF L ^ 2 * n ^ 2 / 16) * (Asig sys L n * ‖x‖) ^ 2 := by
          gcongr
          calc ‖Sg z‖ ≤ ‖Sg‖ * ‖z‖ := Sg.le_opNorm z
            _ ≤ Asig sys L n * ‖x‖ :=
                mul_le_mul (norm_Sig_le hL hn) (norm_sub_truncQ_le x) (norm_nonneg _)
                  (Asig_nonneg hL)
      _ = _ := by ring
  -- combine
  have hsum : ∑' q, (1 + 2 * Ek sys L q) * ‖Sg x q‖ ^ 2 ≤
      2 * (Cop sys L n * ‖x‖ ^ 2) +
        2 * ((1 + eta * gF L ^ 2 * n ^ 2 / 16) * Asig sys L n ^ 2 * ‖x‖ ^ 2) := by
    have hpt : ∀ q, (1 + 2 * Ek sys L q) * ‖Sg x q‖ ^ 2 ≤
        2 * ((1 + 2 * Ek sys L q) * ‖Sg y q‖ ^ 2) + 2 * ((1 + 2 * Ek sys L q) * ‖Sg z q‖ ^ 2) := by
      intro q
      rw [hsplit, lp.coeFn_add, Pi.add_apply]
      have hw : 0 ≤ 1 + 2 * Ek sys L q := by linarith [one_le_one_add_two_Ek sys L q]
      have := norm_add_le (Sg y q) (Sg z q)
      have h3 : ‖Sg y q + Sg z q‖ ^ 2 ≤ 2 * ‖Sg y q‖ ^ 2 + 2 * ‖Sg z q‖ ^ 2 := by
        nlinarith [sq_nonneg (‖Sg y q‖ - ‖Sg z q‖), norm_nonneg (Sg y q + Sg z q)]
      nlinarith
    have hs := (hs1.mul_left 2).add (hs2.mul_left 2)
    have hsf : Summable fun q => (1 + 2 * Ek sys L q) * ‖Sg x q‖ ^ 2 := by
      have := summable_form sys (L := L) (SigD sys L n hL (by omega) x)
      rwa [show Sm eta L (SigD sys L n hL (by omega) x) = Sg x from stateMap_SigD hL hn x] at this
    calc ∑' q, (1 + 2 * Ek sys L q) * ‖Sg x q‖ ^ 2
        ≤ ∑' q, (2 * ((1 + 2 * Ek sys L q) * ‖Sg y q‖ ^ 2) +
            2 * ((1 + 2 * Ek sys L q) * ‖Sg z q‖ ^ 2)) := hsf.tsum_le_tsum hpt hs
      _ = 2 * ∑' q, (1 + 2 * Ek sys L q) * ‖Sg y q‖ ^ 2 +
            2 * ∑' q, (1 + 2 * Ek sys L q) * ‖Sg z q‖ ^ 2 := by
          rw [(hs1.mul_left 2).tsum_add (hs2.mul_left 2), tsum_mul_left, tsum_mul_left]
      _ ≤ _ := by
          unfold Cop
          gcongr
  have h3 : ‖Zw sys hL hn H x‖ ^ 2 ≤ (CZ sys L Hunit n * ‖x‖) ^ 2 := by
    unfold CZ
    rw [mul_pow, mul_pow, Real.sq_sqrt (by
      have := Asig_nonneg (sys := sys) (n := n) hL
      have : 0 ≤ Cop sys L n := by
        unfold Cop M1 cSig2 c1E
        have : 0 ≤ ∑ j : Ch eta, (chC sys L j / cgap sys (gF L)) ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        positivity
      positivity)]
    calc ‖Zw sys hL hn H x‖ ^ 2 ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          ∑' q, (1 + 2 * Ek sys L q) * ‖Sg x q‖ ^ 2 := hform
      _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (2 * (Cop sys L n * ‖x‖ ^ 2) +
            2 * ((1 + eta * gF L ^ 2 * n ^ 2 / 16) * Asig sys L n ^ 2 * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (by unfold CZ; positivity)
    (norm_nonneg _)) two_ne_zero).mp h3

/-! ## `‖X₁‖ ≤ C K` and the retained correction -/

/-- `C_V = 2 C_m (1 + η g² n²/16)^{1/2}`, the bound `‖V_b‖ ≤ C K`. -/
noncomputable def CV (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  2 * (finiteCoulombPhysicalMassConstant sys L Hunit * Real.sqrt (1 + eta * gF L ^ 2 * n ^ 2 / 16))

/-- `C_X = C_V + 2 C_Z`, the bound `‖X₁‖ = ‖[H, Σ_b]‖ ≤ C K`. -/
noncomputable def CX (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  CV sys L Hunit n + 2 * CZ sys L Hunit n

lemma CV_nonneg (Hunit : ℝ) : 0 ≤ CV sys L Hunit n := by
  unfold CV
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  positivity

lemma CZ_nonneg (Hunit : ℝ) : 0 ≤ CZ sys L Hunit n := by
  unfold CZ
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  positivity

include hKernel in
lemma opNorm_Vb_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ‖Vb sys L n hL‖ ≤ CV sys L Hunit n :=
  ContinuousLinearMap.opNorm_le_bound _ (CV_nonneg sys Hunit) fun x =>
    norm_Vb_le sys H hKernel Hunit hL hPeriodic n x

include hKernel in
lemma opNorm_Zw_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ‖Zw sys hL hn H‖ ≤ CZ sys L Hunit n :=
  ContinuousLinearMap.opNorm_le_bound _ (CZ_nonneg sys Hunit) fun x =>
    norm_Zw_le sys hL hn H hKernel Hunit hPeriodic x

include hKernel in
/-- `‖X₁‖ ≤ C_X`. -/
theorem norm_X1_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ‖X1 sys hL hn H‖ ≤ CX sys L Hunit n := by
  unfold X1 CX
  have h1 := opNorm_Vb_le sys hL H hKernel Hunit hPeriodic (n := n)
  have h2 := opNorm_Zw_le sys hL hn H hKernel Hunit hPeriodic
  have h3 : ‖ContinuousLinearMap.adjoint (Zw sys hL hn H)‖ = ‖Zw sys hL hn H‖ :=
    LinearIsometryEquiv.norm_map _ _
  calc ‖Vb sys L n hL + Zw sys hL hn H + ContinuousLinearMap.adjoint (Zw sys hL hn H)‖
      ≤ ‖Vb sys L n hL‖ + ‖Zw sys hL hn H‖ + ‖ContinuousLinearMap.adjoint (Zw sys hL hn H)‖ :=
        norm_add₃_le
    _ ≤ CV sys L Hunit n + CZ sys L Hunit n + CZ sys L Hunit n := by rw [h3]; gcongr
    _ = _ := by ring

omit [Fintype ν] in
lemma norm_cm_le (Z X : L2 eta →L[ℂ] L2 eta) : ‖FSConj.cm Z X‖ ≤ 2 * ‖Z‖ * ‖X‖ := by
  unfold FSConj.cm
  calc ‖Z * X - X * Z‖ ≤ ‖Z * X‖ + ‖X * Z‖ := norm_sub_le _ _
    _ ≤ ‖Z‖ * ‖X‖ + ‖X‖ * ‖Z‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖Z‖ * ‖X‖ := by ring

open Classical in
/-- **`P V_b P = 0`**: a crossing has an end outside the cube. -/
lemma PVbP (x : L2 eta) (hx : molecularH2Truncate n x = x) :
    molecularH2Truncate n (Vb sys L n hL x) = 0 := by
  ext q
  rw [molecularH2Truncate_apply, lp.coeFn_zero, Pi.zero_apply]
  by_cases hq : q ∈ fourierConfigCube eta n
  · rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hq, Vb_apply]
    refine (tsum_congr fun p => ?_).trans tsum_zero
    unfold vbK
    split_ifs with hc
    · have hqP : InP (n : ℝ) q := (inP_iff_mem_cube n q).mpr hq
      rcases hc with ⟨-, hp⟩ | ⟨hq', -⟩
      · have : x p = 0 := by
          rw [← hx, molecularH2Truncate_apply,
            cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ p
              (fun h => hp ((inP_iff_mem_cube n p).mpr h))]
        rw [this, mul_zero]
      · exact absurd hqP hq'
    · rw [zero_mul]
  · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq]

omit [Fintype ν] in
lemma norm_ext_le (y : L2 eta) : ‖ext eta n y‖ ≤ ‖y‖ := by
  have h : ‖ext eta n‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  calc ‖ext eta n y‖ ≤ ‖ext eta n‖ * ‖y‖ := (ext eta n).le_opNorm y
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖y‖ := one_mul _

omit [Fintype ν] in
lemma norm_emb (v : En eta n) : ‖emb eta n v‖ = ‖v‖ := (finiteFourierLpIsometry eta n).norm_map v

omit [Fintype ν] in
lemma trunc_emb (v : En eta n) : molecularH2Truncate n (emb eta n v) = emb eta n v := by
  rw [← emb_ext, ext_emb]

/-- `C_Δ = 2 C_Z + A_σ C_X + 4 A_σ² C_X`, the constant of `cor:opnorm` (first correction). -/
noncomputable def CDelta (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  2 * CZ sys L Hunit n + Asig sys L n * CX sys L Hunit n +
    4 * Asig sys L n ^ 2 * CX sys L Hunit n

include hKernel in
/-- **`cor:opnorm`, the first retained correction**: `‖ΔH v‖ ≤ C_Δ ‖v‖`, from
`B = -X₁ - ½[Σ, X₁] + R₃`, `P V_b P = 0` and `‖R₃‖ ≤ ‖[Σ, [Σ, X₁]]‖ ≤ 4 A_σ² C_X`. -/
theorem norm_dH_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) : ‖dH sys hL hn H v‖ ≤ CDelta sys L Hunit n * ‖v‖ := by
  set Sg := Sig sys L n hL hn
  set X := X1 sys hL hn H
  set R3 := FSConj.Bi Sg X - X - (1 / 2 : ℂ) • FSConj.cm Sg X
  have hskew := (Sig_skew_unitary (sys := sys) hL hn).1
  have hR3 : ‖R3‖ ≤ 4 * Asig sys L n ^ 2 * CX sys L Hunit n := by
    refine (FSConj.norm_Bi_taylor_le hskew X).trans ?_
    have hS := norm_Sig_le (sys := sys) hL hn
    have hXn := norm_X1_le sys hL hn H hKernel Hunit hPeriodic
    have hA := Asig_nonneg (sys := sys) (n := n) hL
    calc ‖FSConj.cm Sg (FSConj.cm Sg X)‖ ≤ 2 * ‖Sg‖ * ‖FSConj.cm Sg X‖ := norm_cm_le _ _
      _ ≤ 2 * ‖Sg‖ * (2 * ‖Sg‖ * ‖X‖) :=
          mul_le_mul_of_nonneg_left (norm_cm_le _ _) (by positivity)
      _ = 4 * ‖Sg‖ ^ 2 * ‖X‖ := by ring
      _ ≤ 4 * Asig sys L n ^ 2 * CX sys L Hunit n := by gcongr
  have hdec : Bcorr sys hL hn H = -(X + (1 / 2 : ℂ) • FSConj.cm Sg X + R3) := by
    simp only [Bcorr, R3]; abel
  set e := emb eta n v
  have hVb : ext eta n (Vb sys L n hL e) = 0 := by
    have h := PVbP sys hL (n := n) e (trunc_emb v)
    have := congrArg (ext eta n) h
    rwa [← emb_ext, ext_emb, map_zero] at this
  have hX : ext eta n (X e) = ext eta n (Zw sys hL hn H e) +
      ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) e) := by
    simp only [X, X1, add_apply, map_add, hVb, zero_add]
  rw [dH_apply, hdec, neg_apply, add_apply, add_apply, map_neg, norm_neg, map_add, map_add, hX]
  have he : ‖e‖ = ‖v‖ := norm_emb v
  have hZ := opNorm_Zw_le sys hL hn H hKernel Hunit hPeriodic
  have hZa : ‖ContinuousLinearMap.adjoint (Zw sys hL hn H)‖ ≤ CZ sys L Hunit n := by
    rw [LinearIsometryEquiv.norm_map]; exact hZ
  have hcm : ‖(1 / 2 : ℂ) • FSConj.cm Sg X‖ ≤ Asig sys L n * CX sys L Hunit n := by
    rw [norm_smul]
    have h1 := norm_cm_le Sg X
    have hS := norm_Sig_le (sys := sys) hL hn
    have hXn := norm_X1_le sys hL hn H hKernel Hunit hPeriodic
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    calc 1 / 2 * ‖FSConj.cm Sg X‖ ≤ 1 / 2 * (2 * ‖Sg‖ * ‖X‖) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = ‖Sg‖ * ‖X‖ := by ring
      _ ≤ Asig sys L n * CX sys L Hunit n :=
          mul_le_mul hS hXn (norm_nonneg _) (Asig_nonneg hL)
  calc ‖ext eta n (Zw sys hL hn H e) + ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) e) +
        ext eta n (((1 / 2 : ℂ) • FSConj.cm Sg X) e) + ext eta n (R3 e)‖
      ≤ ‖ext eta n (Zw sys hL hn H e)‖ + ‖ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) e)‖ +
          ‖ext eta n (((1 / 2 : ℂ) • FSConj.cm Sg X) e)‖ + ‖ext eta n (R3 e)‖ := norm_add₄_le
    _ ≤ ‖Zw sys hL hn H e‖ + ‖ContinuousLinearMap.adjoint (Zw sys hL hn H) e‖ +
          ‖((1 / 2 : ℂ) • FSConj.cm Sg X) e‖ + ‖R3 e‖ := by
        gcongr <;> exact norm_ext_le _
    _ ≤ CZ sys L Hunit n * ‖e‖ + CZ sys L Hunit n * ‖e‖ +
          Asig sys L n * CX sys L Hunit n * ‖e‖ + 4 * Asig sys L n ^ 2 * CX sys L Hunit n * ‖e‖ := by
        gcongr
        · exact ((Zw sys hL hn H).le_opNorm e).trans (mul_le_mul_of_nonneg_right hZ (norm_nonneg _))
        · exact (ContinuousLinearMap.le_opNorm _ e).trans
            (mul_le_mul_of_nonneg_right hZa (norm_nonneg _))
        · exact (ContinuousLinearMap.le_opNorm _ e).trans
            (mul_le_mul_of_nonneg_right hcm (norm_nonneg _))
        · exact (ContinuousLinearMap.le_opNorm _ e).trans
            (mul_le_mul_of_nonneg_right hR3 (norm_nonneg _))
    _ = CDelta sys L Hunit n * ‖v‖ := by unfold CDelta; rw [he]; ring

end FSNormal
