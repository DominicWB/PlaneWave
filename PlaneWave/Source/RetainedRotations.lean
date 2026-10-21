import PlaneWave.Source.RetainedLedger

/-!
# Flux/source build, block 5: the retained rotations on `E_n`

The concrete objects of the second and third rotation, as continuous linear maps on `E_n`:
the kinetic operator `A`, `W_N`, `ΔH = P B P`, `Z₂ = Σ₂^bb + Σ₂^mix`, `G = H₂^{bb,gap} + H₂^{mix,gap}`,
`R = H₂^{bb,res} + H₂^{mix,res}`, `H₃^ret = [Σ₂^bb, W_N] + P H^{(3)} P`, and the relations of the
abstract ledger (`dHc_eq`, `cm_Z2_A`, `Z2_skew`). For a third generator `Σ₃` (a hypothesis object
with `[Σ₃, A] = -(H₃^ret - H₃^res)`), `Hpp Σ₃ = e^{Σ₃} e^{Z₂} H' e^{-Z₂} e^{-Σ₃}`;
`Hpp_mul_U`: `H'' U = U H'` with `U = e^{Σ₃} e^{Z₂}`.

The three pairings of the ledger:

* `norm_inner_Rc_le`: `|⟪R u, φ⟫| ≤ ‖H₂^{bb,res} u‖ ‖φ‖ + ‖H₂^mix‖ ‖1{A > e_H} u‖ ‖1{A > e_H} φ‖`;
* `norm_inner_cm_Z2m_V_le`: `[Σ₂^mix, W_N]` in its four orientations — the cold-to-hot generator by the
  weighted Laplace bound against the low-energy weighted potential tail and the hot tail of `φ`,
  the hot-to-cold one by adjoints against `‖(1+A)^s φ‖`, and `W_N Σ₂^mix u` by Hardy on `φ`;
* `norm_inner_cm_S3_V_le`: `|⟪[Σ₃, W_N] u, φ⟫| ≤ (‖E^{-1/4} Σ₃ W_N u‖ + √2 C_m ‖E^{1/4} Σ₃ u‖)
  ‖E^{1/4} φ‖` (eq:bulk-completion with the Coulomb form bound).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Generic facts on `E_n` -/

omit [Fintype ν] in
/-- A skew pairing gives a skew-adjoint operator. -/
lemma mem_skewAdjoint_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) (h : ∀ u v, ⟪T u, v⟫_ℂ = -⟪u, T v⟫_ℂ) :
    T ∈ skewAdjoint (E →L[ℂ] E) := by
  rw [skewAdjoint.mem_iff, ContinuousLinearMap.star_eq_adjoint]
  refine ((ContinuousLinearMap.eq_adjoint_iff (-T) T).mpr fun x y => ?_).symm
  rw [neg_apply, inner_neg_left, h, neg_neg]

omit [Fintype ν] in
/-- The kinetic operator is the diagonal of the symbol. -/
lemma kin_eq_dg (L : ℝ) (n : ℕ) (sys : CoulombSystem eta ν) :
    FSSpectral.kin (sb eta n) (Asym sys L n) = FSKernel.dg (fun q => (Asym sys L n q : ℂ)) := by
  ext v q
  rw [kin_apply', FSKernel.dg_apply]

omit [Fintype ν] in
/-- Weights shift through the pairing: `⟪x, φ⟫ = ⟪(1+A)^{-s} x, (1+A)^s φ⟫`. -/
lemma inner_wt_shift (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (s : ℝ) (x φ : En eta n) :
    ⟪x, φ⟫_ℂ = ⟪FSSpectral.wt (sb eta n) (Asym sys L n) (-s) x,
      FSSpectral.wt (sb eta n) (Asym sys L n) s φ⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, wt_eq_dg,
    FSKernel.dg_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h0 : 0 < 1 + Asym sys L n q := by linarith [FSGalerkin.Asym_nonneg sys L n q]
  have hp : ((1 + Asym sys L n q) ^ s : ℝ) * (1 + Asym sys L n q) ^ (-s) = 1 := by
    rw [← Real.rpow_add h0, add_neg_cancel, Real.rpow_zero]
  have hp' : (((1 + Asym sys L n q) ^ s : ℝ) : ℂ) * (((1 + Asym sys L n q) ^ (-s) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hp, Complex.ofReal_one]
  simp only [star_mul', RCLike.star_def, Complex.conj_ofReal]
  linear_combination (-(φ.ofLp q * (starRingEnd ℂ) (x.ofLp q))) * hp'

/-- The maximal kinetic energy on the cube, `A_max = 3 η g² n²/2`. -/
noncomputable def Amax (eta : ℕ) (L : ℝ) (n : ℕ) : ℝ := 3 * eta * gF L ^ 2 * n ^ 2 / 2

omit [Fintype ν] in
lemma Asym_le_Amax (sys : CoulombSystem eta ν) {L : ℝ} {n : ℕ} (q : Cfg eta n) :
    Asym sys L n q ≤ Amax eta L n := by
  rw [Asym_eq_Ek]
  unfold Ek E Amax
  have hterm : ∀ c ∈ (Finset.univ : Finset (Fin eta)),
      gF L ^ 2 / (2 * sys.mass c) * nsq (finiteConfigLatticeIndex eta n q c) ≤
        gF L ^ 2 * (3 * n ^ 2) / 2 := by
    intro c _
    have hm := sys.one_le_mass c
    have h0 := nsq_nonneg (finiteConfigLatticeIndex eta n q c)
    have hP : InP (n : ℝ) (finiteConfigLatticeIndex eta n q) :=
      inP_of_mem_cube (finiteConfigLatticeIndex_mem_cube eta n q)
    have hnsq : nsq (finiteConfigLatticeIndex eta n q c) ≤ 3 * n ^ 2 := by
      unfold nsq
      have h1 := hP c 0; have h2 := hP c 1; have h3 := hP c 2
      rw [abs_le] at h1 h2 h3
      nlinarith
    calc gF L ^ 2 / (2 * sys.mass c) * nsq (finiteConfigLatticeIndex eta n q c) ≤
        gF L ^ 2 / 2 * nsq (finiteConfigLatticeIndex eta n q c) := by
          gcongr; linarith
      _ ≤ gF L ^ 2 / 2 * (3 * n ^ 2) := by gcongr
      _ = gF L ^ 2 * (3 * n ^ 2) / 2 := by ring
  calc ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (finiteConfigLatticeIndex eta n q c) ≤
      ∑ _c : Fin eta, gF L ^ 2 * (3 * n ^ 2) / 2 := Finset.sum_le_sum hterm
    _ = 3 * eta * gF L ^ 2 * n ^ 2 / 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

omit [Fintype ν] in
lemma Amax_nonneg (eta : ℕ) (L : ℝ) (n : ℕ) : 0 ≤ Amax eta L n := by unfold Amax; positivity

omit [Fintype ν] in
/-- `‖(1+A)^s v‖ ≤ (1 + A_max)^s ‖v‖` for `s ≥ 0`. -/
lemma norm_wt_le_Amax (sys : CoulombSystem eta ν) {L : ℝ} {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (v : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ ≤ (1 + Amax eta L n) ^ s * ‖v‖ := by
  rw [wt_eq_dg]
  refine FSKernel.norm_dg_le _ (Real.rpow_nonneg (by linarith [Amax_nonneg eta L n]) _)
    (fun q => ?_) v
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h0 : 0 ≤ 1 + Asym sys L n q := by linarith [FSGalerkin.Asym_nonneg sys L n q]
  rw [abs_of_nonneg (Real.rpow_nonneg h0 _)]
  exact Real.rpow_le_rpow h0 (by linarith [Asym_le_Amax sys (L := L) q]) hs

/-! ## The concrete operators -/

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- Linear maps of `E_n` as continuous linear maps. -/
noncomputable abbrev toC (T : En eta n →ₗ[ℂ] En eta n) : En eta n →L[ℂ] En eta n :=
  LinearMap.toContinuousLinearMap T

variable (L n) in
/-- The kinetic operator `A` on `E_n`. -/
noncomputable def Akin : En eta n →L[ℂ] En eta n :=
  toC (FSKernel.dg (fun q => (Asym sys L n q : ℂ)))

variable (L n) in
/-- `W_N` on `E_n`. -/
noncomputable def VN : En eta n →L[ℂ] En eta n :=
  toC (finiteCoulombPotential sys (coulombCellAmplitude L) n)

/-- `ΔH = P B P` on `E_n`. -/
noncomputable def dHc : En eta n →L[ℂ] En eta n := toC (dH sys hL hn H)

variable (L n) in
/-- `Σ₂^bb`. -/
noncomputable def Z2b : En eta n →L[ℂ] En eta n := toC (Sig2bb sys L n)

/-- `Σ₂^mix`. -/
noncomputable def Z2m : En eta n →L[ℂ] En eta n := toC (Sig2mix sys hL hn H)

/-- The gapped second-order part `G = H₂^{bb,gap} + H₂^{mix,gap}`. -/
noncomputable def G2 : En eta n →L[ℂ] En eta n := toC (Hgap sys L n + HmixGap sys hL hn H)

/-- The second-order residuals `R = H₂^{bb,res} + H₂^{mix,res}`. -/
noncomputable def R2c : En eta n →L[ℂ] En eta n := toC (Hres sys L n + HmixRes sys hL hn H)

/-- **The retained third-order term** `H₃^ret = [Σ₂^bb, W_N] + P H^{(3)} P`. -/
noncomputable def H3ret : En eta n →L[ℂ] En eta n :=
  FSConj.cm (Z2b sys L n) (VN sys L n) + H3first sys hL hn H

/-- **The fully rotated retained Hamiltonian** `H'' = e^{Σ₃} e^{Z₂} H' e^{-Z₂} e^{-Σ₃}`. -/
noncomputable def Hpp (S3 : En eta n →L[ℂ] En eta n) : En eta n →L[ℂ] En eta n :=
  FSConj.cj S3 1 (FSConj.cj (Z2b sys L n + Z2m sys hL hn H) 1
    (Akin sys L n + VN sys L n + dHc sys hL hn H))

/-- The rotation `U = e^{Σ₃} e^{Z₂}`. -/
noncomputable def Urot (S3 : En eta n →L[ℂ] En eta n) : En eta n →L[ℂ] En eta n :=
  exp S3 * exp (Z2b sys L n + Z2m sys hL hn H)

lemma HN_eq : toC (finiteCoulombHamiltonian sys L n) = Akin sys L n + VN sys L n := by
  ext1 v
  simp only [Akin, VN, LinearMap.coe_toContinuousLinearMap', add_apply]
  rw [HN_eq_kin_add, kin_eq_dg]

include hKernel in
/-- `ΔH = G + R + P H^{(3)} P + ΔH_{≥4}`. -/
theorem dHc_eq : dHc sys hL hn H =
    G2 sys hL hn H + R2c sys hL hn H + H3first sys hL hn H + DH4 sys hL hn H := by
  ext1 v
  simp only [dHc, G2, R2c, LinearMap.coe_toContinuousLinearMap', add_apply,
    LinearMap.add_apply]
  rw [dH_decomp sys hL hn H v]
  have h1 := congrArg (fun T : En eta n →ₗ[ℂ] En eta n => T v) (Hbb_split (sys := sys) hL hn)
  have h2 := congrArg (fun T : En eta n →ₗ[ℂ] En eta n => T v) (Hmix_split sys hL hn H hKernel)
  simp only [LinearMap.add_apply] at h1 h2
  change Hbb sys hL hn v = _ at h1
  change Hmix sys hL hn H v = _ at h2
  rw [h1, h2]
  abel

include hKernel in
/-- **The two homological equations** `[Z₂, A] = -G`. -/
theorem cm_Z2_A : FSConj.cm (Z2b sys L n + Z2m sys hL hn H) (Akin sys L n) = -G2 sys hL hn H := by
  have h1 := comm_Sig2bb (sys := sys) (n := n) hL
  have h2 := comm_Sig2mix sys hL hn H hKernel
  ext1 v
  have e1 := congrArg (fun T : En eta n →ₗ[ℂ] En eta n => T v) h1
  have e2 := congrArg (fun T : En eta n →ₗ[ℂ] En eta n => T v) h2
  simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at e1 e2
  simp only [FSConj.cm, Z2b, Z2m, Akin, G2, sub_apply, mul_apply_eq_comp, add_apply,
    LinearMap.coe_toContinuousLinearMap', neg_apply, map_add]
  rw [← e1, ← e2]
  abel

include hKernel in
lemma Z2_skew : Z2b sys L n + Z2m sys hL hn H ∈ skewAdjoint (En eta n →L[ℂ] En eta n) := by
  refine mem_skewAdjoint_of_inner _ fun u v => ?_
  simp only [Z2b, Z2m, add_apply, LinearMap.coe_toContinuousLinearMap',
    inner_add_left, inner_add_right]
  rw [inner_Sig2bb (sys := sys) hL, inner_Sig2mix sys hL hn H hKernel]
  ring

/-- `H'' U = U H'`: the rotated Hamiltonian intertwines the rotation. -/
lemma Hpp_mul_U (S3 : En eta n →L[ℂ] En eta n) :
    Hpp sys hL hn H S3 * Urot sys hL hn H S3 =
      Urot sys hL hn H S3 * (Akin sys L n + VN sys L n + dHc sys hL hn H) := by
  letI := (FSConj.ratAlg : NormedAlgebra ℚ (En eta n →L[ℂ] En eta n))
  have h1 : exp (-S3) * exp S3 = 1 := by
    have := FSConj.ex_neg_mul S3 1
    rwa [FSConj.ex_one, FSConj.ex_neg_one] at this
  have h2 : exp (-(Z2b sys L n + Z2m sys hL hn H)) * exp (Z2b sys L n + Z2m sys hL hn H) = 1 := by
    have := FSConj.ex_neg_mul (Z2b sys L n + Z2m sys hL hn H) 1
    rwa [FSConj.ex_one, FSConj.ex_neg_one] at this
  simp only [Hpp, Urot, FSConj.cj_one]
  calc exp S3 * (exp (Z2b sys L n + Z2m sys hL hn H) * (Akin sys L n + VN sys L n + dHc sys hL hn H) *
        exp (-(Z2b sys L n + Z2m sys hL hn H))) * exp (-S3) * (exp S3 * exp (Z2b sys L n + Z2m sys hL hn H))
      = exp S3 * exp (Z2b sys L n + Z2m sys hL hn H) * (Akin sys L n + VN sys L n + dHc sys hL hn H) *
          (exp (-(Z2b sys L n + Z2m sys hL hn H)) * (exp (-S3) * exp S3) *
            exp (Z2b sys L n + Z2m sys hL hn H)) := by noncomm_ring
    _ = _ := by rw [h1, mul_one, h2, mul_one]

/-! ## Operator bounds -/

omit [Fintype ν] in
lemma norm_Akin_le (u : En eta n) : ‖Akin sys L n u‖ ≤ Amax eta L n * ‖u‖ := by
  simp only [Akin, LinearMap.coe_toContinuousLinearMap']
  refine FSKernel.norm_dg_le _ (Amax_nonneg eta L n) (fun q => ?_) u
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (FSGalerkin.Asym_nonneg sys L n q)]
  exact Asym_le_Amax sys q

omit [Fintype ν] in
lemma opNorm_Akin_le : ‖Akin sys L n‖ ≤ Amax eta L n :=
  ContinuousLinearMap.opNorm_le_bound _ (Amax_nonneg eta L n) (norm_Akin_le sys)

/-- `‖W_N‖ ≤ √2 C_m (1 + A_max)^{1/2}` on the cube. -/
noncomputable def CVN (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + Amax eta L n) ^ (1 / 2 : ℝ)

include hL in
lemma opNorm_VN_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ‖VN sys L n‖ ≤ CVN sys L Hunit n := by
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hA := Amax_nonneg eta L n
  have hCVN : 0 ≤ CVN sys L Hunit n := by unfold CVN; positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hCVN fun u => ?_
  simp only [VN, LinearMap.coe_toContinuousLinearMap']
  refine (potential_le_wt sys Hunit n hL hPeriodic u).trans ?_
  calc Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) u‖ ≤
      Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        ((1 + Amax eta L n) ^ (1 / 2 : ℝ) * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_wt_le_Amax sys (by norm_num) u) (by positivity)
    _ = CVN sys L Hunit n * ‖u‖ := by unfold CVN; ring

include hL in
lemma norm_VN_apply_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (u : En eta n) : ‖VN sys L n u‖ ≤ Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  simp only [VN, LinearMap.coe_toContinuousLinearMap']
  exact (potential_le_wt sys Hunit n hL hPeriodic u).trans (mul_le_mul_of_nonneg_left
    (wt_mono sys L n (by norm_num) u) (by positivity))

include hKernel in
lemma opNorm_dHc_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ‖dHc sys hL hn H‖ ≤ CDelta sys L Hunit n :=
  ContinuousLinearMap.opNorm_le_bound _ (CDelta_nonneg sys hL Hunit)
    (norm_dH_le sys hL hn H hKernel Hunit hPeriodic)

/-- `‖Σ₂^bb‖ ≤ z_b = C_Σ (2 J_n + 3)/n²`. -/
noncomputable def zbC (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  CS1 sys L * (2 * Jn sys n + 3) / (n : ℝ) ^ 2

include hL hn in
lemma opNorm_Z2b_le : ‖Z2b sys L n‖ ≤ zbC sys L n := by
  have := CS1_nonneg (sys := sys) hL
  have h0 : 0 ≤ zbC sys L n := by unfold zbC; positivity
  exact ContinuousLinearMap.opNorm_le_bound _ h0 (norm_Sig2bb_le hL hn)

include hKernel in
lemma opNorm_Z2m_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ‖Z2m sys hL hn H‖ ≤ 2 * (CHmix sys L Hunit n / eH sys L n) := by
  have := CHmix_nonneg sys hL Hunit (n := n)
  have := eH_pos sys hL (show 0 < n by omega)
  have h0 : 0 ≤ 2 * (CHmix sys L Hunit n / eH sys L n) := by positivity
  exact ContinuousLinearMap.opNorm_le_bound _ h0 (norm_Sig2mix_op_le sys hL hn H hKernel Hunit hPeriodic)

include hKernel in
/-- `‖G‖ = ‖[A, Z₂]‖ ≤ 2 A_max ‖Z₂‖`. -/
lemma opNorm_G2_le {z : ℝ} (hz : ‖Z2b sys L n + Z2m sys hL hn H‖ ≤ z) :
    ‖G2 sys hL hn H‖ ≤ 2 * z * Amax eta L n := by
  have e : G2 sys hL hn H = -FSConj.cm (Z2b sys L n + Z2m sys hL hn H) (Akin sys L n) := by
    rw [cm_Z2_A sys hL hn H hKernel, neg_neg]
  rw [e, norm_neg]
  exact (FSConj.norm_cm_le' _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hz (by norm_num))
    (opNorm_Akin_le sys) (norm_nonneg _) (by have := (norm_nonneg _).trans hz; positivity))

/-! ## The pairings -/

include hKernel in
/-- **The residual pairing**:
`|⟪R u, φ⟫| ≤ ‖H₂^{bb,res} u‖ ‖φ‖ + ‖H₂^mix‖ ‖1{A > e_H} u‖ ‖1{A > e_H} φ‖`. -/
theorem norm_inner_Rc_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (u φ : En eta n) :
    ‖⟪R2c sys hL hn H u, φ⟫_ℂ‖ ≤ ‖Hres sys L n u‖ * ‖φ‖ + CHmix sys L Hunit n *
      ‖FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) u‖ *
        ‖FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) φ‖ := by
  simp only [R2c, LinearMap.coe_toContinuousLinearMap', LinearMap.add_apply, inner_add_left]
  exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _)
    (norm_inner_HmixRes_le sys hL hn H hKernel Hunit hPeriodic u φ))

open Classical in
include hKernel in
/-- **The mixed commutator `[Σ₂^mix, W_N]` paired with a flow**, in its four orientations. -/
theorem norm_inner_cm_Z2m_V_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {s : ℝ} (hs : 3 / 4 < s) (u φ : En eta n) :
    ‖⟪FSConj.cm (Z2m sys hL hn H) (VN sys L n) u, φ⟫_ℂ‖ ≤
      CZws sys L Hunit n s / eH sys L n *
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) s
            (FSKernel.res (fun p => Asym sys L n p ≤ eH sys L n) (VN sys L n u))‖ *
          ‖FSKernel.res (fun p => ¬ IsCold n p) φ‖ +
        ‖FSKernel.res (fun p => ¬ IsCold n p) (VN sys L n u)‖ *
          (CZws sys L Hunit n s / eH sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s φ‖) +
        CZws sys L Hunit n s / eH sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s u‖ *
          (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
            ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ‖) +
        CVN sys L Hunit n * (CHmix sys L Hunit n / eH sys L n *
          ‖FSKernel.res (fun p => ¬ IsCold n p) u‖) * ‖φ‖ := by
  set SHL := FSKernel.kop (FSKernel.divK (Asym sys L n) (kHL sys hL hn H))
  set SLH := FSKernel.kop (FSKernel.divK (Asym sys L n) (kLH sys hL hn H))
  set V := finiteCoulombPotential sys (coulombCellAmplitude L) n
  have hZm : ∀ x, Z2m sys hL hn H x = SHL x + SLH x := by
    intro x
    simp only [Z2m, LinearMap.coe_toContinuousLinearMap']
    rw [Sig2mix_eq, LinearMap.add_apply]
  have hcm : FSConj.cm (Z2m sys hL hn H) (VN sys L n) u =
      SHL (V u) + SLH (V u) - V (SHL u) - V (SLH u) := by
    simp only [FSConj.cm, sub_apply, mul_apply_eq_comp, hZm]
    simp only [VN, LinearMap.coe_toContinuousLinearMap', map_add]
    abel
  rw [hcm, inner_sub_left, inner_sub_left, inner_add_left]
  -- (a): the cold-to-hot generator on the low potential output, against the hot tail of `φ`
  have ka : ‖⟪SHL (V u), φ⟫_ℂ‖ ≤ CZws sys L Hunit n s / eH sys L n *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) s
        (FSKernel.res (fun p => Asym sys L n p ≤ eH sys L n) (VN sys L n u))‖ *
      ‖FSKernel.res (fun p => ¬ IsCold n p) φ‖ := by
    have hin : SHL (V u) = SHL (FSKernel.res (fun p => Asym sys L n p ≤ eH sys L n) (V u)) := by
      refine FSKernel.kop_res_of_cols _ _ (fun q p h => ?_) _
      unfold FSKernel.divK at h
      split_ifs at h
      · exact absurd rfl h
      · exact (kHL_supp sys hL hn H hKernel (fun h0 => h (by rw [h0, zero_div]))).2
    rw [FSKernel.inner_eq_inner_res (fun p => ¬ IsCold n p) _ φ
      (fun q hq => SHL_out sys hL hn H hKernel _ (not_not.mp hq)), hin]
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact norm_SHL_wt_le sys hL hn H hKernel Hunit hPeriodic hs _
  -- (b): the hot-to-cold generator, by adjoints
  have kb : ‖⟪SLH (V u), φ⟫_ℂ‖ ≤ ‖FSKernel.res (fun p => ¬ IsCold n p) (VN sys L n u)‖ *
      (CZws sys L Hunit n s / eH sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s φ‖) := by
    rw [inner_SLH sys hL hn H hKernel, norm_neg]
    have hsupp : ∀ q, ¬ (¬ IsCold n q) → (SHL φ).ofLp q = 0 :=
      fun q hq => SHL_out sys hL hn H hKernel _ (not_not.mp hq)
    rw [← inner_conj_symm, Complex.norm_conj, FSKernel.inner_eq_inner_res (fun p => ¬ IsCold n p)
      _ _ hsupp, ← inner_conj_symm, Complex.norm_conj]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_SHL_wt_le sys hL hn H hKernel Hunit hPeriodic hs φ) (norm_nonneg _))
  -- (c): `W_N Σ_HL u` by Hardy on `φ`
  have kc : ‖⟪V (SHL u), φ⟫_ℂ‖ ≤ CZws sys L Hunit n s / eH sys L n *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) s u‖ *
      (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ‖) := by
    rw [finiteCoulombPotential_isSymmetric sys (coulombCellAmplitude L) n]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul
      (norm_SHL_wt_le sys hL hn H hKernel Hunit hPeriodic hs u)
      (potential_le_wt sys Hunit n hL hPeriodic φ) (norm_nonneg _) (by
        have := CZws_nonneg sys Hunit s (L := L) (n := n)
        have := eH_pos sys hL (show 0 < n by omega)
        positivity))
  -- (d): `W_N Σ_LH u` by the operator bound on the hot input
  have kd : ‖⟪V (SLH u), φ⟫_ℂ‖ ≤ CVN sys L Hunit n * (CHmix sys L Hunit n / eH sys L n *
      ‖FSKernel.res (fun p => ¬ IsCold n p) u‖) * ‖φ‖ := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have h1 : ‖V (SLH u)‖ ≤ CVN sys L Hunit n * ‖SLH u‖ := by
      have := (VN sys L n).le_opNorm (SLH u)
      simp only [VN, LinearMap.coe_toContinuousLinearMap'] at this
      exact this.trans (mul_le_mul_of_nonneg_right (opNorm_VN_le sys hL Hunit hPeriodic)
        (norm_nonneg _))
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (le_trans (norm_nonneg _)
      (opNorm_VN_le sys hL Hunit hPeriodic)))
    rw [SLH_in sys hL hn H hKernel]
    exact norm_SLH_le sys hL hn H hKernel Hunit hPeriodic _
  have := norm_add_le (⟪SHL (V u), φ⟫_ℂ) (⟪SLH (V u), φ⟫_ℂ)
  have := norm_sub_le (⟪SHL (V u), φ⟫_ℂ + ⟪SLH (V u), φ⟫_ℂ) (⟪V (SHL u), φ⟫_ℂ)
  have := norm_sub_le (⟪SHL (V u), φ⟫_ℂ + ⟪SLH (V u), φ⟫_ℂ - ⟪V (SHL u), φ⟫_ℂ) (⟪V (SLH u), φ⟫_ℂ)
  linarith

include hL in
/-- **The third-rotation commutator `[Σ₃, W_N]` paired with a flow**
(eq:bulk-completion and the Coulomb form bound). -/
theorem norm_inner_cm_S3_V_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (S3 : En eta n →L[ℂ] En eta n) (u φ : En eta n) :
    ‖⟪FSConj.cm S3 (VN sys L n) u, φ⟫_ℂ‖ ≤
      (‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
        Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖) *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖ := by
  simp only [FSConj.cm, sub_apply, mul_apply_eq_comp, inner_sub_left]
  refine (norm_sub_le _ _).trans ?_
  have k1 : ‖⟪S3 (VN sys L n u), φ⟫_ℂ‖ ≤
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖ := by
    rw [inner_wt_shift sys L n (1 / 4)]
    exact norm_inner_le_norm _ _
  have k2 : ‖⟪VN sys L n (S3 u), φ⟫_ℂ‖ ≤ Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖ := by
    simp only [VN, LinearMap.coe_toContinuousLinearMap']
    exact kato_pair Hunit hL hPeriodic (S3 u) φ
  linarith

end FSNormal
