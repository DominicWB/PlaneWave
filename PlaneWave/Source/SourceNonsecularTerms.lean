import PlaneWave.Source.RetainedComparisonExplicit

/-!
# Flux/source build, block 5: the source and the nonsecular terms with explicit constants

* nonnegativity of the budgets;
* `norm_fT_le`: the coupling `‖Ṽ_{PR} ψ̃_R(s)‖ ≤ f_c Ξ`, `f_c = ω̃ + (2C_Z + 2A_σC_Z + 4A_σ²C_X) ρ̃`
  (from `fT_decomp`); `norm_aT_sub_chi_le`: `‖a(t) - χ(t)‖ ≤ t f_c Ξ` (Duhamel);
* **`T3_explicit`** (`thm:src3`, the source): with the midpoint identity for the symmetric
  `P Ã P`, the observable correction `lem:acorr` and `source_pairing`,
  `|⟪a, PÃP a⟫ - ⟪χ, PÃP χ⟫| ≤ Ξ² t (src_c + f_c C_Acorr m_V)`;
* the nonsecular terms `T2`, `T4`, `T5` with explicit constants.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Nonnegativity of the budgets -/

section Nonneg

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (Hunit : ℝ)

include hL in
lemma rhoC_nonneg : 0 ≤ rhoC sys L Hunit n := by
  unfold rhoC
  have := cTr_nonneg sys hL Hunit
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ gF L * n by have := gF_pos hL; positivity) (-(5 / 2 : ℝ))
  positivity

include hL in
lemma omC_nonneg : 0 ≤ omC sys L Hunit n := by
  unfold omC
  have := cTr_nonneg sys hL Hunit
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ gF L * n by have := gF_pos hL; positivity) (-(3 / 2 : ℝ))
  positivity

include hL in
lemma rhoT_nonneg : 0 ≤ rhoT sys L Hunit n := by
  unfold rhoT
  have := rhoC_nonneg sys hL (n := n) Hunit
  have := cTr_nonneg sys hL Hunit
  have := a0c_nonneg sys (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  positivity

include hL in
lemma omT_nonneg : 0 ≤ omT sys L Hunit n := by
  unfold omT
  have := omC_nonneg sys hL (n := n) Hunit
  have := rhoC_nonneg sys hL (n := n) Hunit
  have := cTr_nonneg sys hL Hunit
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have := a0c_nonneg sys (L := L) (n := n)
  have := a1c_nonneg sys (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  have := CZ_nonneg sys Hunit (L := L) (n := n)
  positivity

include hL in
lemma dA_nonneg : 0 ≤ dA sys L Hunit n := by
  unfold dA
  have := rhoC_nonneg sys hL (n := n) Hunit
  have := cTr_nonneg sys hL Hunit
  have := a0c_nonneg sys (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  positivity

omit [Fintype ν] in
include hL in
lemma pertF_nonneg {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ pertF eta L n δ := by
  unfold pertF Kq
  have hK : 0 ≤ Real.sqrt 3 * (gF L * n) := by have := gF_pos hL; positivity
  have := Amax_nonneg eta L n
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + Real.sqrt 3 * (gF L * n) by linarith) (5 / 2 : ℝ)
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + Real.sqrt 3 * (gF L * n) by linarith) (1 / 2 : ℝ)
  positivity

include hL in
lemma mA_nonneg : 0 ≤ mA sys L Hunit n := by
  unfold mA
  have := cTr_nonneg sys hL Hunit
  have := pertF_nonneg hL (eta := eta) (n := n) (dA_nonneg sys hL (n := n) Hunit)
  positivity

lemma cvT_nonneg : 0 ≤ cvT sys L Hunit := by
  unfold cvT
  have := relB_nonneg sys L Hunit (finiteCoulombPhysicalMassConstant_nonneg sys L Hunit)
  positivity

include hL in
lemma Mdec_nonneg {a b e d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) (hd : 0 ≤ d) :
    0 ≤ Mdec sys L Hunit n a b e d := by
  unfold Mdec
  have := CtW_nonneg sys hL Hunit (M₂ := 3 * sys.maxMass * a) (by have := sys.one_le_maxMass; positivity)
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have := gF_pos hL
  have := sys.one_le_maxMass
  positivity

include hL in
lemma eps0chi_nonneg : 0 ≤ eps0chi sys L Hunit n := by
  unfold eps0chi
  have := Amax_nonneg eta L n
  have := CVN_nonneg sys Hunit (L := L) (n := n)
  have := dA_nonneg sys hL (n := n) Hunit
  have := alphaD_nonneg sys hL Hunit (n := n)
  have := mA_nonneg sys hL (n := n) Hunit
  have := omC_nonneg sys hL (n := n) Hunit
  positivity

include hL in
lemma mChi_nonneg : 0 ≤ mChi sys L Hunit n := by
  unfold mChi
  have hC := Cfl_nonneg sys Hunit (CDelta_nonneg sys hL Hunit (n := n)) (L := L)
  have := mA_nonneg sys hL (n := n) Hunit
  have := cvT_nonneg sys (L := L) Hunit
  have := alphaD_nonneg sys hL Hunit (n := n)
  exact Mdec_nonneg sys hL Hunit (by positivity) (by positivity) (eps0chi_nonneg sys hL Hunit)
    (by positivity)

include hL in
lemma dRot_nonneg {s β : ℝ} (hβ : 0 ≤ β) : 0 ≤ dRot sys L Hunit n s β := by
  unfold dRot
  have := z2uC_nonneg sys hL Hunit s (n := n)
  have := mChi_nonneg sys hL (n := n) Hunit
  positivity

include hL in
lemma mRot_nonneg {s β : ℝ} (hβ : 0 ≤ β) : 0 ≤ mRot sys L Hunit n s β := by
  unfold mRot
  have := mChi_nonneg sys hL (n := n) Hunit
  have := pertF_nonneg hL (eta := eta) (n := n) (dRot_nonneg sys hL (n := n) Hunit (s := s) hβ)
  positivity

include hL in
lemma mN_nonneg : 0 ≤ mN sys L Hunit n := by
  unfold mN
  have hC := Cfl_nonneg sys Hunit (le_refl (0 : ℝ)) (L := L)
  have := cTr_nonneg sys hL Hunit
  have := cvT_nonneg sys (L := L) Hunit
  exact Mdec_nonneg sys hL Hunit (by positivity) (by positivity) (omC_nonneg sys hL Hunit) le_rfl

include hL in
lemma dRot0_nonneg {s β : ℝ} (hβ : 0 ≤ β) : 0 ≤ dRot0 sys L Hunit n s β := by
  unfold dRot0
  have := z2uC_nonneg sys hL Hunit s (n := n)
  have := mA_nonneg sys hL (n := n) Hunit
  positivity

include hL in
lemma dR_nonneg {s β : ℝ} (hβ : 0 ≤ β) : 0 ≤ dR sys L Hunit n s β := by
  unfold dR
  have := dRot0_nonneg sys hL (n := n) Hunit (s := s) hβ
  have := dA_nonneg sys hL (n := n) Hunit
  positivity

include hL in
lemma mNr_nonneg {s β : ℝ} (hβ : 0 ≤ β) : 0 ≤ mNr sys L Hunit n s β := by
  unfold mNr
  have hC := Cfl_nonneg sys Hunit (le_refl (0 : ℝ)) (L := L)
  have := mA_nonneg sys hL (n := n) Hunit
  have := Amax_nonneg eta L n
  have := dRot0_nonneg sys hL (n := n) Hunit (s := s) hβ
  have := cvT_nonneg sys (L := L) Hunit
  have := CVN_nonneg sys Hunit (L := L) (n := n)
  have := dR_nonneg sys hL (n := n) Hunit (s := s) hβ
  have := omC_nonneg sys hL (n := n) Hunit
  exact Mdec_nonneg sys hL Hunit (by positivity) (by positivity) (by positivity) le_rfl

end Nonneg

/-! ## The coupling -/

section Coupling

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- The coupling constant `f_c = ω̃ + (2C_Z + 2A_σC_Z + 4A_σ²C_X) ρ̃`. -/
noncomputable def fC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  omT sys L Hunit n + (2 * CZ sys L Hunit n + 2 * Asig sys L n * CZ sys L Hunit n +
    4 * Asig sys L n ^ 2 * CX sys L Hunit n) * rhoT sys L Hunit n

include hL in
lemma fC_nonneg (Hunit : ℝ) : 0 ≤ fC sys L Hunit n := by
  unfold fC
  have := omT_nonneg sys hL (n := n) Hunit
  have := rhoT_nonneg sys hL (n := n) Hunit
  have := CZ_nonneg sys Hunit (L := L) (n := n)
  have := CX_nonneg sys Hunit (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  positivity

include hKernel in
/-- **The coupling on good data**: `‖f(s)‖ ≤ f_c Ξ`. -/
theorem norm_fT_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (D : EvoData L H) (s : ℝ) :
    ‖fT sys hL hn H D.U D.u₀ s‖ ≤ fC sys L Hunit n * D.Xi := by
  obtain ⟨hρ, hW, -, -⟩ := aT_bounds sys hL hn H hKernel Hunit hPeriodic hKg D s
  obtain ⟨u', hu'1, -⟩ := D.graph s D.u₀
  have hw : Sm eta L (exp (SigG sys hL hn) u') = psiT sys hL hn D.U D.u₀ s := by
    rw [exp_SigG_apply, hu'1]; rfl
  have hdec := fT_decomp sys hL hn H hKernel D.U D.u₀ D.graph s _ hw
  simp only at hdec
  rw [hdec]
  set r := psiT sys hL hn D.U D.u₀ s - molecularH2Truncate n (psiT sys hL hn D.U D.u₀ s)
  have hΞ := D.Xi_nonneg
  have hA := norm_Sig_le (sys := sys) hL hn
  have hA0 := Asig_nonneg (sys := sys) (n := n) hL
  have hZ := opNorm_Zw_le sys hL hn H hKernel Hunit hPeriodic
  have hZ0 := CZ_nonneg sys Hunit (L := L) (n := n)
  have hZs := norm_Zsym_le sys hL hn H Hunit hPeriodic hKernel
  have hR3 := norm_R3c_le sys hL hn H hKernel Hunit hPeriodic
  have hr0 := norm_nonneg r
  have k1 : ‖hotProj L (Kc L n / 4) (ext eta n (Wp sys L H (exp (SigG sys hL hn) u' -
      molecularH2Truncate n (exp (SigG sys hL hn) u'))))‖ ≤ omT sys L Hunit n * D.Xi :=
    (norm_hotProj_le _ _ _).trans ((norm_ext_le _).trans (hW _ hw))
  have k2 : ‖ext eta n (Zw sys hL hn H r)‖ ≤ CZ sys L Hunit n * ‖r‖ :=
    (norm_ext_le _).trans (((Zw sys hL hn H).le_opNorm r).trans
      (mul_le_mul_of_nonneg_right hZ hr0))
  have k3 : ‖ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) r)‖ ≤ CZ sys L Hunit n * ‖r‖ := by
    refine (norm_ext_le _).trans ((ContinuousLinearMap.le_opNorm _ r).trans ?_)
    rw [LinearIsometryEquiv.norm_map]
    exact mul_le_mul_of_nonneg_right hZ hr0
  have k4 : ‖(1 / 2 : ℂ) • ext eta n (FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) r)‖ ≤
      2 * Asig sys L n * CZ sys L Hunit n * ‖r‖ := by
    rw [norm_smul]
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h2]
    have hc : ‖FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H)‖ ≤
        2 * Asig sys L n * (2 * CZ sys L Hunit n) :=
      (norm_cm_le _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hZs
        (norm_nonneg _) (by positivity))
    have := (norm_ext_le (n := n) _).trans (((FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H)).le_opNorm r).trans
      (mul_le_mul_of_nonneg_right hc hr0))
    linarith
  have k5 : ‖ext eta n (R3c sys hL hn H r)‖ ≤ 4 * Asig sys L n ^ 2 * CX sys L Hunit n * ‖r‖ :=
    (norm_ext_le _).trans (((R3c sys hL hn H).le_opNorm r).trans
      (mul_le_mul_of_nonneg_right hR3 hr0))
  have hsum := norm_sub_le (hotProj L (Kc L n / 4) (ext eta n (Wp sys L H (exp (SigG sys hL hn) u' -
      molecularH2Truncate n (exp (SigG sys hL hn) u')))) - ext eta n (Zw sys hL hn H r) -
      ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) r) -
      (1 / 2 : ℂ) • ext eta n (FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) r))
    (ext eta n (R3c sys hL hn H r))
  have h1 := norm_sub_le (hotProj L (Kc L n / 4) (ext eta n (Wp sys L H (exp (SigG sys hL hn) u' -
      molecularH2Truncate n (exp (SigG sys hL hn) u')))) - ext eta n (Zw sys hL hn H r) -
      ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) r))
    ((1 / 2 : ℂ) • ext eta n (FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) r))
  have h2 := norm_sub_le (hotProj L (Kc L n / 4) (ext eta n (Wp sys L H (exp (SigG sys hL hn) u' -
      molecularH2Truncate n (exp (SigG sys hL hn) u')))) - ext eta n (Zw sys hL hn H r))
    (ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) r))
  have h3 := norm_sub_le (hotProj L (Kc L n / 4) (ext eta n (Wp sys L H (exp (SigG sys hL hn) u' -
      molecularH2Truncate n (exp (SigG sys hL hn) u'))))) (ext eta n (Zw sys hL hn H r))
  have hrb : (2 * CZ sys L Hunit n + 2 * Asig sys L n * CZ sys L Hunit n +
      4 * Asig sys L n ^ 2 * CX sys L Hunit n) * ‖r‖ ≤
      (2 * CZ sys L Hunit n + 2 * Asig sys L n * CZ sys L Hunit n +
        4 * Asig sys L n ^ 2 * CX sys L Hunit n) * (rhoT sys L Hunit n * D.Xi) :=
    mul_le_mul_of_nonneg_left hρ (by have := CX_nonneg sys Hunit (L := L) (n := n); positivity)
  have e : fC sys L Hunit n * D.Xi = omT sys L Hunit n * D.Xi +
      (2 * CZ sys L Hunit n + 2 * Asig sys L n * CZ sys L Hunit n +
        4 * Asig sys L n ^ 2 * CX sys L Hunit n) * (rhoT sys L Hunit n * D.Xi) := by unfold fC; ring
  rw [e]
  linarith

include hKernel in
/-- **`‖a(t) - χ(t)‖ ≤ t f_c Ξ`** (Duhamel for the dressed retained part). -/
theorem norm_aT_sub_chi_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (D : EvoData L H) {t : ℝ} (ht : 0 ≤ t) :
    ‖aT sys hL hn D.U D.u₀ t -
        retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) (aT sys hL hn D.U D.u₀ 0)‖ ≤
      t * (fC sys L Hunit n * D.Xi) := by
  set v := aT sys hL hn D.U D.u₀ t - retFlow sys L n (dH_symm sys hL hn H hKernel) (-t)
    (aT sys hL hn D.U D.u₀ 0)
  have hd := duhamel_weak sys hL hn H hKernel D.U D.u₀ D.graph D.deriv D.cont t v
  have e : ⟪v, v⟫_ℂ = Complex.I * ∫ s in (0 : ℝ)..t, ⟪fT sys hL hn H D.U D.u₀ s,
      retFlow sys L n (dH_symm sys hL hn H hKernel) (t - s) v⟫_ℂ := by
    conv_lhs => rw [show v = aT sys hL hn D.U D.u₀ t - retFlow sys L n (dH_symm sys hL hn H hKernel) (-t)
      (aT sys hL hn D.U D.u₀ 0) from rfl]
    rw [inner_sub_left, hd]; ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (C := fC sys L Hunit n * D.Xi * ‖v‖)
    (f := fun s => ⟪fT sys hL hn H D.U D.u₀ s, retFlow sys L n (dH_symm sys hL hn H hKernel) (t - s) v⟫_ℂ)
    (fun s _ => (norm_inner_le_norm _ _).trans (by
      rw [norm_retFlow]
      exact mul_le_mul_of_nonneg_right (norm_fT_le sys hL hn H hKernel Hunit hPeriodic hKg D s)
        (norm_nonneg _)))
  rw [sub_zero, abs_of_nonneg ht] at hb
  have h2 : ‖v‖ ^ 2 ≤ t * (fC sys L Hunit n * D.Xi) * ‖v‖ := by
    have h3 : ‖⟪v, v⟫_ℂ‖ = ‖v‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]; simp
    rw [← h3, e, norm_mul, Complex.norm_I, one_mul]
    linarith
  rcases eq_or_lt_of_le (norm_nonneg v) with h0 | h0
  · rw [← h0]
    have := fC_nonneg sys hL (n := n) Hunit
    have := D.Xi_nonneg
    positivity
  · have h4 : ‖v‖ * ‖v‖ ≤ t * (fC sys L Hunit n * D.Xi) * ‖v‖ := by nlinarith
    exact le_of_mul_le_mul_right h4 h0

end Coupling

end FSNormal
