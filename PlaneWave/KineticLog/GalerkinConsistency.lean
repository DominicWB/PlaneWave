import PlaneWave.KineticLog.SpectralTails

/-!
# Logarithmic kinetic bound, part 5: the Galerkin consistency estimates

The Galerkin Hamiltonian `H_N = P H P` on `ran P` (`finiteCoulombHamiltonian`, the generator of
the release's flow `retFlow` with `ΔH = 0`) has the orthonormal eigenbasis `gB` with eigenvalues
`gE`; with the common shift `c = shiftC`, `gE + c ≥ 1`.  For an exact eigen-decomposition `E`
and a finite set `s` of exact eigenvectors with `ν ≤ Λ`:

* `gcons a k = (gE_a + c - ν_k) ⟪gB_a, P b_k⟫`, the matrix of the consistency residual
  `C_N = H_N P - P H = -P V_tot (1 - P)` (`eq:kinetic-galerkin-strong`) between eigenvectors;
  `gcons_combo` identifies its action on `zv s d = (H + c)⁻¹ Σ d_k b_k` with
  `-⟪gB_a, P W (1 - P) zv⟫` (from the release's `extract_H_eq`);
* **`galerkin_delta`** (second inequality of `eq:kinetic-galerkin-low`): on the Galerkin rows
  with `H_N + c ≤ 2Λ`, the doubly inverse-weighted residual has norm at most
  `δ_G / K³`, `δ_G = 3 C_W C_rev C_abs`.  The finite test vector only needs the generic
  potential tail; the exact vector uses the absorption bound `norm_tail_zv_le`;
* **`galerkin_transfer`** (`eq:kinetic-galerkin-transfer`): on the rows with `H_N + c > 2Λ`
  the separated Sylvester solution `X_ak = ⟪gB_a, P b_k⟫/ν_k` has `‖X‖ ≤ C_F/(K Λ)`, from
  `norm_sylvester_le` and the strong bound `‖C_N (H + c)⁻¹ S‖ ≤ C_F/K`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FSNormal FSGalerkin

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- The Galerkin eigen-index type. -/
abbrev GIdx (eta n : ℕ) := Fin (Module.finrank ℂ (En eta n))

/-! ## The Galerkin eigenbasis -/

section GalerkinEigen

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

/-- The eigenbasis of `H_N`. -/
noncomputable abbrev gB : OrthonormalBasis (GIdx eta n) ℂ (En eta n) :=
  retBasis sys L n (zero_isSymmetric (n := n))

/-- The eigenvalues of `H_N`. -/
noncomputable abbrev gE : GIdx eta n → ℝ := retEig sys L n (zero_isSymmetric (n := n))

lemma gB_eigen (a : GIdx eta n) :
    finiteCoulombHamiltonian sys L n (gB sys L n a) = (gE sys L n a : ℂ) • gB sys L n a := by
  have h := retBasis_eigen sys L n (zero_isSymmetric (n := n)) a
  simpa [Hret] using h

lemma inner_gB_HN (a : GIdx eta n) (v : En eta n) :
    ⟪gB sys L n a, finiteCoulombHamiltonian sys L n v⟫_ℂ =
      (gE sys L n a : ℂ) * ⟪gB sys L n a, v⟫_ℂ := by
  rw [← finiteCoulombHamiltonian_isSymmetric sys L n (gB sys L n a) v, gB_eigen,
    inner_smul_left, Complex.conj_ofReal]

lemma inner_gB_flow (τ : ℝ) (u : En eta n) (a : GIdx eta n) :
    ⟪gB sys L n a, retFlow sys L n (zero_isSymmetric (n := n)) τ u⟫_ℂ =
      Complex.exp (Complex.I * (gE sys L n a : ℂ) * τ) * ⟪gB sys L n a, u⟫_ℂ :=
  inner_retFlow sys L n _ τ u a

variable {L} (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hL hPeriodic in
/-- The Galerkin eigenvalues are at least `-(C_m² + 1/4)`. -/
lemma gE_lower (a : GIdx eta n) :
    -((finiteCoulombPhysicalMassConstant sys L Hunit) ^ 2 + 1 / 4) ≤ gE sys L n a := by
  have h := eigen_lower (gB sys L n) (gE sys L n) (Hret sys L n 0)
    (retBasis_eigen sys L n (zero_isSymmetric (n := n)))
    (Hret_lower sys Hunit n hL hPeriodic (CΔ := 0) (fun v => by simp)) a
  linarith

include hL hPeriodic in
/-- **The shifted Galerkin eigenvalues are at least one**: `gE + c ≥ 1`. -/
lemma one_le_gE_add (a : GIdx eta n) : 1 ≤ gE sys L n a + shiftC sys L Hunit := by
  have h := gE_lower sys n Hunit hL hPeriodic a
  have hC := sq_nonneg (finiteCoulombPhysicalMassConstant sys L Hunit)
  unfold shiftC
  linarith

include hL hPeriodic in
/-- **Galerkin graph bound**: `‖v‖ + 2 ‖A v‖ ≤ 3 C_rev ‖(H_N + c) v‖`. -/
lemma galerkin_graph (v : En eta n) :
    ‖v‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) v‖ ≤
      3 * Crev sys L Hunit 0 * ‖FSSpectral.fc (gB sys L n) (gE sys L n)
        (fun l => ((l + shiftC sys L Hunit : ℝ) : ℂ)) v‖ := by
  have h1 := norm_le_wt sys L n (by norm_num : (0 : ℝ) ≤ 1) v
  have h2 := norm_kin_le_wt sys v (L := L) (n := n)
  have h3 := wt_one_le_shifted sys Hunit hL hPeriodic (zero_isSymmetric (n := n)) le_rfl
    (fun v => by simp) v
  have h4 : ‖FSSpectral.fc (gB sys L n) (gE sys L n)
      (fun l => ((l + Clow sys L Hunit 0 + 1 : ℝ) : ℂ)) v‖ ≤
      ‖FSSpectral.fc (gB sys L n) (gE sys L n) (fun l =>
          ((l + shiftC sys L Hunit : ℝ) : ℂ)) v‖ := by
    have hsq : ‖FSSpectral.fc (gB sys L n) (gE sys L n)
        (fun l => ((l + Clow sys L Hunit 0 + 1 : ℝ) : ℂ)) v‖ ^ 2 ≤
        ‖FSSpectral.fc (gB sys L n) (gE sys L n)
          (fun l => ((l + shiftC sys L Hunit : ℝ) : ℂ)) v‖ ^ 2 := by
      rw [FSSpectral.norm_sq_fc, FSSpectral.norm_sq_fc]
      refine Finset.sum_le_sum fun a _ => ?_
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hl := gE_lower sys n Hunit hL hPeriodic a
      have hC := sq_nonneg (finiteCoulombPhysicalMassConstant sys L Hunit)
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      unfold Clow shiftC
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
  have hCrev : 0 ≤ Crev sys L Hunit 0 := by
    unfold Crev
    have := (Clow_pos sys Hunit (le_refl (0 : ℝ)) (L := L)).le
    positivity
  have h5 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ ≤ Crev sys L Hunit 0 *
      ‖FSSpectral.fc (gB sys L n) (gE sys L n) (fun l => ((l + shiftC sys L Hunit : ℝ) : ℂ)) v‖ :=
    h3.trans (mul_le_mul_of_nonneg_left h4 hCrev)
  have h1' : ‖v‖ ≤ ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by simpa using h1
  linarith

end GalerkinEigen

/-! ## The consistency matrix -/

section Consistency

variable (sys : CoulombSystem eta ν) {L : ℝ} (n : ℕ)
  {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2} {c : ℝ}

/-- The consistency matrix `(gE_a + c - ν_k) ⟪gB_a, P b_k⟫` between eigenvectors. -/
noncomputable def gcons (E : ExactEigen L H c) (a : GIdx eta n) (k : E.ι) : ℂ :=
  ((gE sys L n a + c - E.nu k : ℝ) : ℂ) * ⟪gB sys L n a, ext eta n (E.b k)⟫_ℂ

variable (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel in
/-- **The residual on low-energy combinations**:
`Σ_k gcons_ak d_k/ν_k = -⟪gB_a, P W (1 - P) zv s d⟫`. -/
lemma gcons_combo (E : ExactEigen L H c) (s : Finset E.ι) (d : EuclideanSpace ℂ s)
    (a : GIdx eta n) :
    ∑ k : s, gcons sys n E a k * (d k / (E.nu k : ℂ)) =
      -⟪gB sys L n a, ext eta n (Wp sys L H (E.zv s d - molecularH2Truncate n (E.zv s d)))⟫_ℂ := by
  have h := extract_H_eq sys L H hKernel n (E.zv s d)
  have h' : ext eta n (H (E.zv s d)) = finiteCoulombHamiltonian sys L n
      (ext eta n (Sm eta L (E.zv s d))) +
        ext eta n (Wp sys L H (E.zv s d - molecularH2Truncate n (E.zv s d))) := h
  have hi := congrArg (fun x => ⟪gB sys L n a, x⟫_ℂ) h'
  simp only [inner_add_right, inner_gB_HN] at hi
  rw [E.H_zv, E.sm_zv, map_sum, map_sum, inner_sum, inner_sum, Finset.mul_sum] at hi
  simp only [map_smul, inner_smul_right] at hi
  have e : ⟪gB sys L n a, ext eta n (Wp sys L H (E.zv s d - molecularH2Truncate n (E.zv s d)))⟫_ℂ
      = ∑ k : s, d k / (E.nu k : ℂ) * ((E.nu k - c : ℝ) : ℂ) * ⟪gB sys L n a, ext eta n (E.b k)⟫_ℂ -
        ∑ k : s,
            (gE sys L n a : ℂ) * (d k / (E.nu k : ℂ) * ⟪gB sys L n a, ext eta n (E.b k)⟫_ℂ) := by
    rw [hi]
    ring
  rw [e, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold gcons
  push_cast
  ring

end Consistency

/-! ## The low-energy consistency bound -/

section Delta

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (n : ℕ)

/-- The low Galerkin block of the consistency matrix (rows with `gE + c ≤ 2Λ`). -/
noncomputable def gA {c : ℝ} (E : ExactEigen L H c) (Λ : ℝ) (s : Finset E.ι) :
    GIdx eta n → s → ℂ :=
  fun a k => if gE sys L n a + c ≤ 2 * Λ then gcons sys n E a k else 0

/-- The clamped Galerkin labels `min (gE + c) (2Λ)`. -/
noncomputable def lamC (L : ℝ) (c Λ : ℝ) (a : GIdx eta n) : ℝ := min (gE sys L n a + c) (2 * Λ)

/-- The Galerkin low-energy consistency constant `δ_G = 3 C_W C_rev C_abs`. -/
noncomputable def dG (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  3 * cWt sys L Hunit * Crev sys L Hunit 0 * cAbs sys L Hunit

include hL in
lemma dG_nonneg : 0 ≤ dG sys L Hunit := by
  unfold dG
  have := cWt_nonneg sys Hunit hL
  have := cAbs_nonneg sys Hunit hL
  have hCrev : 0 ≤ Crev sys L Hunit 0 := by
    unfold Crev
    have := (Clow_pos sys Hunit (le_refl (0 : ℝ)) (L := L)).le
    positivity
  positivity

omit [Fintype ν] in
/-- Coordinates of a combination of an orthonormal basis. -/
lemma inner_gB_combo (b : OrthonormalBasis (GIdx eta n) ℂ (En eta n)) (f : GIdx eta n → ℂ)
    (a : GIdx eta n) : ⟪b a, ∑ a', f a' • b a'⟫_ℂ = f a :=
  b.orthonormal.inner_right_fintype f a

include hKernel hL hPeriodic in
/-- **`eq:kinetic-galerkin-low`, second inequality**: the doubly inverse-weighted consistency
matrix on the low Galerkin rows has norm at most `δ_G / K³`. -/
theorem galerkin_delta {c : ℝ} (E : ExactEigen L H c) (hcdef : c = shiftC sys L Hunit)
    (hK1 : 1 ≤ gF L * n) (hK2 : 2 * gF L ≤ gF L * n) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : Λ + c ≤ (gF L * n) ^ 2 / (4 * sys.maxMass))
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) (d : EuclideanSpace ℂ s) :
    ‖mop (wmat (lamC sys n L c Λ) (fun k : s => E.nu k) (gA sys H n E Λ s)) d‖ ≤
      dG sys L Hunit / (gF L * n) ^ 3 * ‖d‖ := by
  classical
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  set y := mop (wmat (lamC sys n L c Λ) (fun k : s => E.nu k) (gA sys H n E Λ s)) d with hydef
  set X := ext eta n (Wp sys L H (E.zv s d - molecularH2Truncate n (E.zv s d))) with hXdef
  have hlam : ∀ a, 1 ≤ gE sys L n a + c := fun a => hcdef ▸ one_le_gE_add sys n Hunit hL hPeriodic a
  -- coordinates of `y`
  have hy : ∀ a, y a = if gE sys L n a + c ≤ 2 * Λ then
      -(⟪gB sys L n a, X⟫_ℂ / ((gE sys L n a + c : ℝ) : ℂ)) else 0 := by
    intro a
    rw [hydef, mop_apply]
    simp only [wmat, gA, lamC]
    split_ifs with ha
    · rw [min_eq_left ha]
      have hc := gcons_combo sys n hKernel E s d a
      rw [← hXdef] at hc
      have hl0 : ((gE sys L n a + c : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by linarith [hlam a])
      rw [show -(⟪gB sys L n a, X⟫_ℂ / ((gE sys L n a + c : ℝ) : ℂ)) =
        (-⟪gB sys L n a, X⟫_ℂ) / ((gE sys L n a + c : ℝ) : ℂ) by ring, ← hc, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hn0 : (E.nu k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (E.nu_pos k).ne'
      push_cast at hl0 ⊢
      field_simp
    · simp
  -- the dual vector `v = Σ (y_a/λ_a) gB_a`
  set f : GIdx eta n → ℂ := fun a => if gE sys L n a + c ≤ 2 * Λ then
    y a / ((gE sys L n a + c : ℝ) : ℂ) else 0 with hfdef
  set v : En eta n := ∑ a, f a • gB sys L n a with hvdef
  have hyX : ((‖y‖ ^ 2 : ℝ) : ℂ) = -⟪v, X⟫_ℂ := by
    rw [hvdef, sum_inner, norm_sq_eucl]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_smul_left]
    have hya := hy a
    simp only [hfdef]
    split_ifs with ha
    · rw [if_pos ha] at hya
      have hl0 : ((gE sys L n a + c : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by linarith [hlam a])
      rw [map_div₀, Complex.conj_ofReal]
      have e : ⟪gB sys L n a, X⟫_ℂ = -(y a * ((gE sys L n a + c : ℝ) : ℂ)) := by
        rw [hya]
        field_simp
      rw [e, ← Complex.conj_mul']
      field_simp
    · rw [if_neg ha] at hya
      rw [hya]
      simp
  -- `‖(H_N + c) v‖ = ‖y‖`
  have hGv : ‖FSSpectral.fc (gB sys L n) (gE sys L n)
      (fun l => ((l + shiftC sys L Hunit : ℝ) : ℂ)) v‖ = ‖y‖ := by
    have hsq : ‖FSSpectral.fc (gB sys L n) (gE sys L n)
        (fun l => ((l + shiftC sys L Hunit : ℝ) : ℂ)) v‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [FSSpectral.norm_sq_fc, norm_sq_eucl]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hvdef, inner_gB_combo, ← hcdef, ← mul_pow, ← norm_mul]
      congr 1
      simp only [hfdef]
      split_ifs with ha
      · have hl0 : ((gE sys L n a + c : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (by linarith [hlam a])
        field_simp
      · rw [hy a, if_neg ha, mul_zero]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
  -- the pairing `⟪v, P W (1-P) z⟫ = ⟪(1-P) W lift v, (1-P) S z⟫`
  have hpair : ‖⟪v, X⟫_ℂ‖ ≤ ‖Wp sys L H (cubeLift (gF L) n v) -
      molecularH2Truncate n (Wp sys L H (cubeLift (gF L) n v))‖ * ‖E.tailOp n s d‖ := by
    have e1 : ⟪v, X⟫_ℂ =
        ⟪emb eta n v, Wp sys L H (E.zv s d - molecularH2Truncate n (E.zv s d))⟫_ℂ :=
      inner_ext' n _ v
    have e2 : ⟪emb eta n v, Wp sys L H (E.zv s d - molecularH2Truncate n (E.zv s d))⟫_ℂ =
        ⟪Wp sys L H (cubeLift (gF L) n v),
            Sm eta L (E.zv s d - molecularH2Truncate n (E.zv s d))⟫_ℂ := by
      rw [emb_eq_stateMap L n v]
      exact potential_symm sys L H hKernel _ _
    have e3 : Sm eta L (E.zv s d - molecularH2Truncate n (E.zv s d)) = E.tailOp n s d := by
      rw [E.tailOp_apply, map_sub]
      congr 1
      exact stateMap_truncate (gF L) n (E.zv s d)
    have e4 : ⟪Wp sys L H (cubeLift (gF L) n v), E.tailOp n s d⟫_ℂ =
        ⟪Wp sys L H (cubeLift (gF L) n v) -
            molecularH2Truncate n (Wp sys L H (cubeLift (gF L) n v)),
          E.tailOp n s d⟫_ℂ := by
      rw [inner_sub_left, E.tailOp_apply]
      have h0 := inner_sub_truncate_truncate n (Sm eta L (E.zv s d))
        (Wp sys L H (cubeLift (gF L) n v))
      have h1 : ⟪molecularH2Truncate n (Wp sys L H (cubeLift (gF L) n v)),
          Sm eta L (E.zv s d) - molecularH2Truncate n (Sm eta L (E.zv s d))⟫_ℂ = 0 := by
        rw [← inner_conj_symm, h0, map_zero]
      rw [h1, sub_zero]
    rw [e1, e2, e3, e4]
    exact norm_inner_le_norm _ _
  -- the two tails
  have hWv : ‖Wp sys L H (cubeLift (gF L) n v) - molecularH2Truncate n
      (Wp sys L H (cubeLift (gF L) n v))‖ ≤
      cWt sys L Hunit * (3 * Crev sys L Hunit 0 * ‖y‖) / Real.sqrt K := by
    refine (W_tail_le sys H hKernel Hunit hL hPeriodic n hK1 hK2 _).trans ?_
    have hS : ‖Sm eta L (cubeLift (gF L) n v)‖ = ‖v‖ := by
      rw [stateMap_cubeLift' v]
      exact (finiteFourierLpIsometry eta n).norm_map v
    have hT := norm_kinetic_cubeLift sys v (L := L)
    have hg := galerkin_graph sys n Hunit hL hPeriodic v
    rw [hGv] at hg
    rw [hS, hT]
    have := cWt_nonneg sys Hunit hL
    gcongr
  have htail := norm_tail_zv_le sys H hKernel Hunit hL hPeriodic E hcdef n hK1 hK2 hΛ1 hΛ s hs d
  -- conclude
  have hy2 : ‖y‖ ^ 2 ≤ cWt sys L Hunit * (3 * Crev sys L Hunit 0 * ‖y‖) / Real.sqrt K *
      (cAbs sys L Hunit / (K ^ 2 * Real.sqrt K) * ‖d‖) := by
    have h1 : ‖y‖ ^ 2 = ‖⟪v, X⟫_ℂ‖ := by
      have h := congrArg norm hyX
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h
      exact h
    rw [h1]
    refine hpair.trans (mul_le_mul hWv htail (norm_nonneg _) ?_)
    have := cWt_nonneg sys Hunit hL
    have hCrev : 0 ≤ Crev sys L Hunit 0 := by
      unfold Crev
      have := (Clow_pos sys Hunit (le_refl (0 : ℝ)) (L := L)).le
      positivity
    positivity
  have e : cWt sys L Hunit * (3 * Crev sys L Hunit 0 * ‖y‖) / Real.sqrt K *
      (cAbs sys L Hunit / (K ^ 2 * Real.sqrt K) * ‖d‖) =
      ‖y‖ * (dG sys L Hunit / K ^ 3 * ‖d‖) := by
    have hss : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK0.le
    have hK3 : K ^ 3 = K ^ 2 * Real.sqrt K * Real.sqrt K := by rw [mul_assoc, hss]; ring
    unfold dG
    rw [hK3]
    field_simp
  rw [e] at hy2
  by_cases hy0 : ‖y‖ = 0
  · rw [hy0]
    have := dG_nonneg sys Hunit hL
    positivity
  · have hpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
    have : ‖y‖ * ‖y‖ ≤ ‖y‖ * (dG sys L Hunit / K ^ 3 * ‖d‖) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-! ## The separated Galerkin transfer -/

/-- The high Galerkin block of the Sylvester solution: `X_ak = ⟪gB_a, P b_k⟫/ν_k` on the rows
with `gE + c > 2Λ`. -/
noncomputable def gX {c : ℝ} (E : ExactEigen L H c) (Λ : ℝ) (s : Finset E.ι) :
    GIdx eta n → s → ℂ :=
  fun a k => if gE sys L n a + c ≤ 2 * Λ then 0 else
    ⟪gB sys L n a, ext eta n (E.b k)⟫_ℂ / (E.nu k : ℂ)

/-- The strong-consistency constant `C_F = C_m ((c_z/2)² + 2 C_abs²)^{1/2}`. -/
noncomputable def cF (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  finiteCoulombPhysicalMassConstant sys L Hunit *
    Real.sqrt ((cZ sys L Hunit / 2) ^ 2 + 2 * cAbs sys L Hunit ^ 2)

lemma cF_nonneg : 0 ≤ cF sys L Hunit := by
  unfold cF
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  positivity

include hKernel hL hPeriodic in
/-- **`eq:kinetic-galerkin-transfer`**: the separated Galerkin Sylvester solution satisfies
`‖X_N‖ ≤ ‖F_N‖/Λ ≤ C_F/(K Λ)`. -/
theorem galerkin_transfer {c : ℝ} (E : ExactEigen L H c) (hcdef : c = shiftC sys L Hunit)
    (hK1 : 1 ≤ gF L * n) (hK2 : 2 * gF L ≤ gF L * n) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : Λ + c ≤ (gF L * n) ^ 2 / (4 * sys.maxMass))
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) :
    ‖mop (gX sys H n E Λ s)‖ ≤ cF sys L Hunit / (gF L * n * Λ) := by
  classical
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  set F : GIdx eta n → s → ℂ := fun a k => if gE sys L n a + c ≤ 2 * Λ then 0 else
    gcons sys n E a k / (E.nu k : ℂ) with hFdef
  have hsyl : ∀ a (k : s), ((gE sys L n a + c : ℝ) : ℂ) * gX sys H n E Λ s a k -
      gX sys H n E Λ s a k * (E.nu k : ℂ) = F a k := by
    intro a k
    simp only [gX, hFdef, gcons]
    split_ifs
    · ring
    · have hn0 : (E.nu k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (E.nu_pos k).ne'
      field_simp
      push_cast
      ring
  have hX := norm_sylvester_le (fun a => gE sys L n a + c) (fun k : s => E.nu k)
    (gX sys H n E Λ s) F (α := 2 * Λ) (β := Λ) (by linarith) (by linarith)
    (fun a k hx => by
      simp only [gX] at hx
      split_ifs at hx with ha
      · exact absurd rfl hx
      · push Not at ha
        exact ha.le)
    (fun a k hx => by
      rw [abs_of_pos (E.nu_pos k)]
      exact hs k k.2)
    hsyl
  -- the strong bound on `F`
  have hFn : ‖mop F‖ ≤ cF sys L Hunit / K := by
    refine norm_mop_le (by have := cF_nonneg sys (L := L) Hunit; positivity) fun d => ?_
    set Y := Wp sys L H (E.zv s d - molecularH2Truncate n (E.zv s d)) with hYdef
    have hcoord : ∀ a, ‖mop F d a‖ ≤ ‖⟪gB sys L n a, ext eta n Y⟫_ℂ‖ := by
      intro a
      rw [mop_apply]
      simp only [hFdef]
      split_ifs
      · simp
      · have h := gcons_combo sys n hKernel E s d a
        rw [← hYdef] at h
        have e : ∑ k : s, gcons sys n E a k / (E.nu k : ℂ) * d k =
            ∑ k : s, gcons sys n E a k * (d k / (E.nu k : ℂ)) :=
          Finset.sum_congr rfl fun k _ => by ring
        rw [e, h, norm_neg]
    have h1 : ‖mop F d‖ ≤ ‖Y‖ := by
      have hsq : ‖mop F d‖ ^ 2 ≤ ‖Y‖ ^ 2 := by
        rw [norm_sq_eucl]
        calc ∑ a, ‖mop F d a‖ ^ 2 ≤ ∑ a, ‖⟪gB sys L n a, ext eta n Y⟫_ℂ‖ ^ 2 :=
              Finset.sum_le_sum fun a _ => pow_le_pow_left₀ (norm_nonneg _) (hcoord a) 2
          _ = ‖ext eta n Y‖ ^ 2 := (gB sys L n).sum_sq_norm_inner_right _
          _ ≤ ‖Y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_ext_le Y) 2
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
    -- the relative bound with `α = 1/K²`
    have hα : (0 : ℝ) < 1 / K ^ 2 := by positivity
    have hW := potential_sq_le sys L H hKernel Hunit hL hPeriodic hα
      (E.zv s d - molecularH2Truncate n (E.zv s d))
    have hT : ‖coulombFourierKineticH2 sys (2 * Real.pi / L)
        (E.zv s d - molecularH2Truncate n (E.zv s d))‖ ≤ cZ sys L Hunit / 2 * ‖d‖ := by
      have e : coulombFourierKineticH2 sys (2 * Real.pi / L)
          (E.zv s d - molecularH2Truncate n (E.zv s d)) =
          coulombFourierKineticH2 sys (gF L) (E.zv s d) -
            molecularH2Truncate n (coulombFourierKineticH2 sys (gF L) (E.zv s d)) := by
        rw [map_sub]
        congr 1
        exact kinetic_truncate sys (gF L) n (E.zv s d)
      rw [e]
      have hb := zv_budget sys H hKernel Hunit hL hPeriodic E hcdef s d
      have h0 := norm_nonneg (Sm eta L (E.zv s d))
      have h2 := FSNormal.norm_sub_truncate_le n (coulombFourierKineticH2 sys (gF L) (E.zv s d))
      linarith
    have hS : ‖molecularH2StateMap eta (2 * Real.pi / L)
        (E.zv s d - molecularH2Truncate n (E.zv s d))‖ ≤ cAbs sys L Hunit / K ^ 2 * ‖d‖ := by
      have e : molecularH2StateMap eta (2 * Real.pi / L)
          (E.zv s d - molecularH2Truncate n (E.zv s d)) = E.tailOp n s d := by
        rw [E.tailOp_apply, map_sub]
        congr 1
        exact stateMap_truncate (gF L) n (E.zv s d)
      rw [e]
      refine (norm_tail_zv_le sys H hKernel Hunit hL hPeriodic E hcdef n hK1 hK2 hΛ1 hΛ s hs
        d).trans ?_
      have hsK : 1 ≤ Real.sqrt K := by rw [Real.one_le_sqrt]; exact hK1
      have hA := cAbs_nonneg sys Hunit hL
      gcongr
      calc K ^ 2 = K ^ 2 * 1 := by ring
        _ ≤ K ^ 2 * Real.sqrt K := by gcongr
    have hYsq : ‖Y‖ ^ 2 ≤ (cF sys L Hunit / K * ‖d‖) ^ 2 := by
      have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
      have hcz := cZ_nonneg sys (L := L) Hunit
      have hA := cAbs_nonneg sys Hunit hL
      have hY : ‖Y‖ ^ 2 ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          (1 / K ^ 2 * (cZ sys L Hunit / 2 * ‖d‖) ^ 2 +
            (1 + 1 / (1 / K ^ 2)) * (cAbs sys L Hunit / K ^ 2 * ‖d‖) ^ 2) := by
        refine hW.trans ?_
        gcongr
      have hR : (cF sys L Hunit / K * ‖d‖) ^ 2 =
          finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
            ((cZ sys L Hunit / 2) ^ 2 + 2 * cAbs sys L Hunit ^ 2) * ‖d‖ ^ 2 / K ^ 2 := by
        unfold cF
        rw [div_mul_eq_mul_div, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hLe : finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          (1 / K ^ 2 * (cZ sys L Hunit / 2 * ‖d‖) ^ 2 +
            (1 + 1 / (1 / K ^ 2)) * (cAbs sys L Hunit / K ^ 2 * ‖d‖) ^ 2) =
          finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * ‖d‖ ^ 2 / K ^ 2 *
            ((cZ sys L Hunit / 2) ^ 2 + (1 + K ^ 2) / K ^ 2 * cAbs sys L Hunit ^ 2) := by
        field_simp
      rw [hR]
      refine hY.trans (le_of_eq_of_le hLe ?_)
      have e2 : (1 + K ^ 2) / K ^ 2 * cAbs sys L Hunit ^ 2 ≤ 2 * cAbs sys L Hunit ^ 2 := by
        have h2 : (1 + K ^ 2) / K ^ 2 ≤ 2 := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      have hpos : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * ‖d‖ ^ 2 / K ^ 2 := by
        positivity
      calc finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * ‖d‖ ^ 2 / K ^ 2 *
            ((cZ sys L Hunit / 2) ^ 2 + (1 + K ^ 2) / K ^ 2 * cAbs sys L Hunit ^ 2)
          ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * ‖d‖ ^ 2 / K ^ 2 *
            ((cZ sys L Hunit / 2) ^ 2 + 2 * cAbs sys L Hunit ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hpos
        _ = _ := by ring
    have hY := (pow_le_pow_iff_left₀ (norm_nonneg _) (by
      have := cF_nonneg sys (L := L) Hunit
      positivity) two_ne_zero).mp hYsq
    calc ‖mop F d‖ ≤ ‖Y‖ := h1
      _ ≤ cF sys L Hunit / K * ‖d‖ := hY
  have hΛ0 : 0 < Λ := by linarith
  refine hX.trans ?_
  rw [show 2 * Λ - Λ = Λ by ring, div_le_div_iff₀ hΛ0 (by positivity)]
  calc ‖mop F‖ * (K * Λ) ≤ cF sys L Hunit / K * (K * Λ) := by gcongr
    _ = cF sys L Hunit * Λ := by field_simp

end Delta

end KineticLog
