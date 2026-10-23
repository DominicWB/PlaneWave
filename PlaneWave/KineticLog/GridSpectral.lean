import PlaneWave.KineticLog.GalerkinEndpoint
import PlaneWave.Grid

/-!
# Logarithmic kinetic bound, part 9: spectral data of the grid comparison

The grid case of `thm:kinetic-log` (`sec:kinetic-grid`) compares the exact evolution with the
truncated-kernel grid evolution `ψ_g(t) = e^{-iGt} P' ψ₀` on the register of radius `2m`
(`n' = 4m + 1` points per axis, cutoff `2K`, `K = g m`, `g = 2π/L`).  This file supplies the
spectral ingredients that do not involve the consistency error:

* **a common shift** (`ExactEigen.shift`): the exact eigen-decomposition of `H + c` is also one of
  `H + c + d` (eigenvalues `ν + d`), and its inverse-weighted combinations are those of the
  unshifted decomposition with rescaled coefficients (`shift_zv`), so the budgets and the
  momentum-tail absorption transfer (`zv_budget_shift`, `norm_tail_zv_shift_le`);
* **the grid eigenbasis** (`grB`, `grE`) of the symmetric grid Hamiltonian of an even kernel, the
  uniform lower bound `E_a ≥ -c_gr` over the whole kernel class (`grE_lower`, from the
  Kato--Rellich bound of the release, `RegHam.eigen_lower`), and the action of every grid
  propagator on the eigenbasis (`grid_flow_eigen`, `inner_grB_flow`);
* the register shells against continuum truncations (`norm_high_regCoeff_le_trunc`) and the
  generic potential tail with an `H²` budget (`W_tail_le_h2`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal

namespace KineticLog

/-! ## A larger common shift -/

namespace ExactEigen

variable {eta : ℕ} {L c : ℝ}
  {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}
  (E : ExactEigen L H c)

/-- The same eigen-decomposition for the shift `c + d`, `d ≥ 0`, with eigenvalues `ν + d`. -/
def shift (d : ℝ) (hd : 0 ≤ d) : ExactEigen L H (c + d) where
  ι := E.ι
  b := E.b
  nu := fun i => E.nu i + d
  w := E.w
  sm_w := E.sm_w
  H_w := fun i => by
    show H (E.w i) = ((E.nu i + d - (c + d) : ℝ) : ℂ) • E.b i
    rw [E.H_w i, add_sub_add_right_eq_sub]
  one_le := fun i => by
    show 1 ≤ E.nu i + d
    linarith [E.one_le i]
  finite := fun Λ => (E.finite Λ).subset fun i hi => by
    simp only [Set.mem_setOf_eq] at hi ⊢
    linarith

variable {d : ℝ} (hd : 0 ≤ d)

lemma shift_nu (i : E.ι) : (E.shift d hd).nu i = E.nu i + d := rfl

/-- The rescaled coefficients `a_k ν_k/(ν_k + d)`. -/
noncomputable def resc (d : ℝ) (s : Finset E.ι) (a : EuclideanSpace ℂ s) : EuclideanSpace ℂ s :=
  WithLp.toLp 2 (fun k => a k * ((E.nu k / (E.nu k + d) : ℝ) : ℂ))

include hd in
lemma norm_resc_le (s : Finset E.ι) (a : EuclideanSpace ℂ s) : ‖E.resc d s a‖ ≤ ‖a‖ := by
  have h := norm_le_of_coord (s := 1) zero_le_one (x := E.resc d s a) (y := a) fun k => by
    change ‖a k * ((E.nu k / (E.nu k + d) : ℝ) : ℂ)‖ ≤ 1 * ‖a k‖
    have hn := E.nu_pos k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), one_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [div_le_one (by linarith)]
    linarith
  rwa [one_mul] at h

include hd in
/-- The inverse-weighted combinations of the shifted decomposition are those of `E`. -/
lemma shift_zv (s : Finset E.ι) (a : EuclideanSpace ℂ s) :
    (E.shift d hd).zv s a = E.zv s (E.resc d s a) := by
  unfold ExactEigen.zv
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  change a k / ((E.nu k.1 + d : ℝ) : ℂ) =
    a k * ((E.nu k.1 / (E.nu k.1 + d) : ℝ) : ℂ) / (E.nu k.1 : ℂ)
  have hn := E.nu_pos k.1
  have h1 : ((E.nu k.1 + d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have h2 : (E.nu k.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  push_cast at h1 ⊢
  field_simp

end ExactEigen

section ShiftBounds

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- The budget of the shifted combinations: `‖S zv'‖ + 2 ‖T zv'‖ ≤ c_z ‖a‖`. -/
lemma zv_budget_shift {c : ℝ} (E : ExactEigen L H c) (hcdef : c = shiftC sys L Hunit) {d : ℝ}
    (hd : 0 ≤ d) (s : Finset E.ι) (a : EuclideanSpace ℂ s) :
    ‖Sm eta L ((E.shift d hd).zv s a)‖ +
        2 * ‖coulombFourierKineticH2 sys (gF L) ((E.shift d hd).zv s a)‖ ≤
      cZ sys L Hunit * ‖a‖ := by
  rw [E.shift_zv hd]
  refine (zv_budget sys H hKernel Hunit hL hPeriodic E hcdef s _).trans ?_
  exact mul_le_mul_of_nonneg_left (E.norm_resc_le hd s a) (cZ_nonneg sys (L := L) Hunit)

include hKernel hL hPeriodic in
/-- The momentum-tail absorption for the shifted combinations (same hypotheses on the unshifted
eigenvalues as `norm_tail_zv_le`). -/
theorem norm_tail_zv_shift_le {c : ℝ} (E : ExactEigen L H c) (hcdef : c = shiftC sys L Hunit)
    {d : ℝ} (hd : 0 ≤ d) (n : ℕ) (hK1 : 1 ≤ gF L * n) (hK2 : 2 * gF L ≤ gF L * n) {Λ : ℝ}
    (hΛ1 : 1 ≤ Λ) (hΛ : Λ + c ≤ (gF L * n) ^ 2 / (4 * sys.maxMass))
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) (a : EuclideanSpace ℂ s) :
    ‖Sm eta L ((E.shift d hd).zv s a) -
        molecularH2Truncate n (Sm eta L ((E.shift d hd).zv s a))‖ ≤
      cAbs sys L Hunit / ((gF L * n) ^ 2 * Real.sqrt (gF L * n)) * ‖a‖ := by
  rw [E.shift_zv hd]
  have h := norm_tail_zv_le sys H hKernel Hunit hL hPeriodic E hcdef n hK1 hK2 hΛ1 hΛ s hs
    (E.resc d s a)
  rw [E.tailOp_apply] at h
  refine h.trans (mul_le_mul_of_nonneg_left (E.norm_resc_le hd s a) ?_)
  have := cAbs_nonneg sys Hunit hL
  have hK0 : 0 < gF L * n := by linarith
  positivity

end ShiftBounds

/-! ## The grid eigenbasis -/

section GridEigen

variable {eta : ℕ} {ν : Type} [Fintype ν] {m : ℕ} (P : RegParticles eta) (Dn : NucData ν)
  {κ : Lat3 → ℝ} (g : ℝ) (hκe : ∀ x, κ (-x) = κ x)

/-- The index type of the grid eigenbasis. -/
abbrev GrIdx (eta m : ℕ) : Type := Fin (Module.finrank ℂ (EuclideanSpace ℂ (RCfg eta m)))

/-- **The grid eigenbasis**: an orthonormal eigenbasis of the symmetric grid Hamiltonian `G` of an
even kernel. -/
noncomputable def grB : OrthonormalBasis (GrIdx eta m) ℂ (EuclideanSpace ℂ (RCfg eta m)) :=
  (Hgrid_isSymmetric (eta := eta) (m := m) (P := P) (D := Dn) (g := g) hκe).eigenvectorBasis rfl

/-- The grid eigenvalues. -/
noncomputable def grE : GrIdx eta m → ℝ :=
  (Hgrid_isSymmetric (eta := eta) (m := m) (P := P) (D := Dn) (g := g) hκe).eigenvalues rfl

lemma grB_eigen (a : GrIdx eta m) :
    Hgrid eta m P Dn κ g (grB P Dn g hκe a) = (grE P Dn g hκe a : ℂ) • grB P Dn g hκe a :=
  (Hgrid_isSymmetric (eta := eta) (m := m) (P := P) (D := Dn) (g := g) hκe).apply_eigenvectorBasis
    rfl a

/-- `⟪e_a, G x⟫ = E_a ⟪e_a, x⟫`. -/
lemma inner_grB_Hgrid (a : GrIdx eta m) (x : EuclideanSpace ℂ (RCfg eta m)) :
    ⟪grB P Dn g hκe a, Hgrid eta m P Dn κ g x⟫_ℂ =
      (grE P Dn g hκe a : ℂ) * ⟪grB P Dn g hκe a, x⟫_ℂ := by
  rw [← (Hgrid_isSymmetric (eta := eta) (m := m) (P := P) (D := Dn) (g := g) hκe)
    (grB P Dn g hκe a) x, grB_eigen, inner_smul_left, Complex.conj_ofReal]

/-- The lower bound `c_gr = 52 Z J₀ + g²/4` of `-G` over the kernel class (`Z = m̄ Z_c`,
`J₀ = J0g Z g`); it depends on the particles, the nuclei, the amplitude `γ` and `g` only. -/
noncomputable def cGr (P : RegParticles eta) (Dn : NucData ν) (γ g : ℝ) : ℝ :=
  52 * (P.maxMass * Zc P Dn γ) * (J0g (P.maxMass * Zc P Dn γ) g : ℝ) + g ^ 2 / 4

lemma cGr_nonneg {γ : ℝ} (hγ : 0 ≤ γ) : 0 ≤ cGr P Dn γ g := by
  unfold cGr
  have := Zc_nonneg (P := P) (D := Dn) hγ
  have := P.maxMass_pos
  positivity

/-- **The uniform lower bound of the grid spectrum** (`lem:grid-KR`): `E_a ≥ -c_gr` for every
kernel with `|κ| ≤ γ coul`. -/
lemma grE_lower {γ : ℝ} (hγ : 0 ≤ γ) (hκb : ∀ x, |κ x| ≤ γ * coul x) (hg : 0 < g)
    (a : GrIdx eta m) : -cGr P Dn γ g ≤ grE P Dn g hκe a := by
  have h := (gridRegHam (eta := eta) (m := m) (P := P) (D := Dn) hγ hκb hg).eigen_lower
    (grB P Dn g hκe a) ((grB P Dn g hκe).orthonormal.1 a) (grE P Dn g hκe a) (by
      rw [gridRegHam_op]
      exact grB_eigen P Dn g hκe a)
  rw [gridRegHam_Z, gridRegHam_J0, gridRegHam_g] at h
  unfold cGr
  linarith

/-- **Every grid propagator acts on the eigenbasis by phases**: `U_g(t) e_a = e^{-i E_a t} e_a`
for every family with `U_g(0) = 1` solving `∂_t U_g(t) x = -i U_g(t) G x`. -/
lemma grid_flow_eigen
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m P Dn κ g x))) t)
    (a : GrIdx eta m) (t : ℝ) :
    Ug t (grB P Dn g hκe a) =
      Complex.exp (-(Complex.I * (grE P Dn g hκe a : ℂ) * t)) • grB P Dn g hκe a := by
  set e := grB P Dn g hκe a
  set E : ℂ := (grE P Dn g hκe a : ℂ)
  set f : ℝ → EuclideanSpace ℂ (RCfg eta m) := fun s => Ug s e with hf
  have hderiv : ∀ s, HasDerivAt f ((-(Complex.I * E)) • f s) s := by
    intro s
    have h := hgderiv s e
    rw [grB_eigen, LinearIsometryEquiv.map_smul, smul_smul] at h
    refine h.congr_deriv ?_
    rw [neg_smul]
  set k : ℝ → EuclideanSpace ℂ (RCfg eta m) := fun s => Complex.exp (Complex.I * E * s) • f s
    with hk
  have hkd : ∀ s, HasDerivAt k 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * E * s))
        (Complex.exp (Complex.I * E * s) * (Complex.I * E)) s := by
      have h0 : HasDerivAt (fun s : ℝ => Complex.I * E * (s : ℂ)) (Complex.I * E * 1) s :=
        (HasDerivAt.ofReal_comp (hasDerivAt_id s)).const_mul (Complex.I * E)
      have := h0.cexp
      rw [mul_one] at this
      exact this
    have h2 := h1.smul (hderiv s)
    refine h2.congr_deriv ?_
    rw [smul_smul, ← add_smul]
    have : Complex.exp (Complex.I * E * s) * -(Complex.I * E) +
        Complex.exp (Complex.I * E * s) * (Complex.I * E) = 0 := by ring
    rw [this, zero_smul]
  have hconst : ∀ s, k s = k 0 := fun s =>
    is_const_of_deriv_eq_zero (fun s => (hkd s).differentiableAt) (fun s => (hkd s).deriv) s 0
  have hk0 : k 0 = e := by
    simp only [hk, hf, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul, hg0]
  have ht := hconst t
  rw [hk0] at ht
  have hft : f t = Complex.exp (-(Complex.I * E * t)) • k t := by
    simp only [hk, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
  change f t = _
  rw [hft, ht]

/-- **Grid eigen-coordinates of the evolution**: `⟪e_a, U_g(t) y⟫ = e^{-i E_a t} ⟪e_a, y⟫`. -/
lemma inner_grB_flow
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m P Dn κ g x))) t)
    (a : GrIdx eta m) (t : ℝ) (y : EuclideanSpace ℂ (RCfg eta m)) :
    ⟪grB P Dn g hκe a, Ug t y⟫_ℂ =
      Complex.exp (-(Complex.I * (grE P Dn g hκe a : ℂ) * t)) * ⟪grB P Dn g hκe a, y⟫_ℂ := by
  set E : ℂ := (grE P Dn g hκe a : ℂ)
  have hz : Ug t (Complex.exp (Complex.I * E * t) • grB P Dn g hκe a) = grB P Dn g hκe a := by
    rw [LinearIsometryEquiv.map_smul, grid_flow_eigen P Dn g hκe Ug hg0 hgderiv a t, smul_smul,
      ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
  calc ⟪grB P Dn g hκe a, Ug t y⟫_ℂ
      = ⟪Ug t (Complex.exp (Complex.I * E * t) • grB P Dn g hκe a), Ug t y⟫_ℂ := by rw [hz]
    _ = ⟪Complex.exp (Complex.I * E * t) • grB P Dn g hκe a, y⟫_ℂ :=
        LinearIsometryEquiv.inner_map_map _ _ _
    _ = _ := by
        rw [inner_smul_left, ← Complex.exp_conj]
        congr 2
        simp [E, Complex.conj_ofReal]

end GridEigen

/-! ## Helpers: register shells, potential tails, a split pairing -/

section Helpers

variable {eta : ℕ}

/-- A register shell beyond `T` (sup norm) is part of the continuum exterior of the cube `T`:
`‖1_{High T r} P' x‖ ≤ ‖x - P_T x‖`. -/
lemma norm_high_regCoeff_le_trunc {m : ℕ} (T : ℕ) (r : Fin eta)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    ‖maskOp (High T r) (regCoeff m x)‖ ≤ ‖x - molecularH2Truncate T x‖ := by
  refine (norm_le_of_pointwise (Y := regCoeff m (x - molecularH2Truncate T x)) fun q => ?_).trans
    (norm_regCoeff_le _)
  by_cases h : High T r q
  · have hnot : liftCfg q ∉ fourierConfigCube eta T := by
      intro hmem
      rw [mem_fourierConfigCube_iff] at hmem
      exact h fun c => abs_le.mpr (hmem r c)
    rw [maskOp_apply_of _ _ h, regCoeff_apply, regCoeff_apply, sub_trunc_apply, if_neg hnot]
  · rw [maskOp_apply_of_not _ _ h, norm_zero]
    exact norm_nonneg _

/-- **A split pairing in coordinates.** If `X_h` vanishes where `λ_a ≤ M`, then
`|Σ conj(X_l + X_h)_a Z_a| ≤ ‖X_l‖ ‖Z‖ + ‖X_h‖ ‖(λ_a Z_a)‖ / M`. -/
lemma norm_sum_conj_split {ι : Type*} [Fintype ι] (lam : ι → ℝ) {M : ℝ} (hM : 0 < M)
    (Xl Xh Z : EuclideanSpace ℂ ι) (hXh : ∀ a, lam a ≤ M → Xh a = 0) :
    ‖∑ a, conj (Xl a + Xh a) * Z a‖ ≤
      ‖Xl‖ * ‖Z‖ +
        ‖Xh‖ * (‖(WithLp.toLp 2 (fun a => (lam a : ℂ) * Z a) : EuclideanSpace ℂ ι)‖ / M) := by
  classical
  set Z' : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun a => if M < lam a then Z a else 0) with hZ'
  have h1 : ∑ a, conj (Xl a + Xh a) * Z a = ⟪Xl, Z⟫_ℂ + ⟪Xh, Z'⟫_ℂ := by
    rw [PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [RCLike.inner_apply', RCLike.inner_apply', map_add]
    change (conj (Xl a) + conj (Xh a)) * Z a =
      conj (Xl a) * Z a + conj (Xh a) * (if M < lam a then Z a else 0)
    by_cases ha : M < lam a
    · rw [if_pos ha]
      ring
    · rw [if_neg ha, hXh a (not_lt.mp ha), map_zero]
      ring
  have hZ' : ‖Z'‖ ≤ 1 / M *
      ‖(WithLp.toLp 2 (fun a => (lam a : ℂ) * Z a) : EuclideanSpace ℂ ι)‖ := by
    refine norm_le_of_coord (by positivity) fun a => ?_
    change ‖(if M < lam a then Z a else 0)‖ ≤ 1 / M * ‖(lam a : ℂ) * Z a‖
    by_cases ha : M < lam a
    · rw [if_pos ha, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hM.trans ha)]
      rw [← mul_assoc, one_div, ← div_eq_inv_mul]
      exact le_mul_of_one_le_left (norm_nonneg _) ((one_le_div hM).mpr ha.le)
    · rw [if_neg ha, norm_zero]
      positivity
  rw [h1]
  refine (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) ?_)
  refine (norm_inner_le_norm _ _).trans ?_
  calc ‖Xh‖ * ‖Z'‖ ≤ ‖Xh‖ * (1 / M *
        ‖(WithLp.toLp 2 (fun a => (lam a : ℂ) * Z a) : EuclideanSpace ℂ ι)‖) :=
        mul_le_mul_of_nonneg_left hZ' (norm_nonneg _)
    _ = _ := by ring

end Helpers

section WTail

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **Generic potential tail with an `H²` budget**: for `K = g n ≥ max(1, 2g)` and `‖u‖ ≤ M`,
`‖(1 - P_n) W u‖ ≤ η C_tail(1) M / √K`. -/
theorem W_tail_le_h2 (n : ℕ) (hK1 : 1 ≤ gF L * n) (hK2 : 2 * gF L ≤ gF L * n)
    (u : MolecularFourierH2 eta) {M : ℝ} (hM : 0 ≤ M) (hu : ‖u‖ ≤ M) :
    ‖Wp sys L H u - molecularH2Truncate n (Wp sys L H u)‖ ≤
      eta * CtW sys L Hunit 1 * M / Real.sqrt (gF L * n) := by
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  have hρ : Real.sqrt (1 / K) ^ 2 * K = 1 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have ht : ∀ a, ‖tailMask (gF L) K a (Wp sys L H u)‖ ≤
      CtW sys L Hunit M * Real.sqrt (1 / K) := fun a =>
    potential_tail_le sys L H hKernel Hunit hL hPeriodic a K (Real.sqrt (1 / K))
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) M hK1 (Real.sqrt_nonneg _) hρ hBlow hCs hBker hM
      hK2 hLow hKernelScale hSobolev u hu
  have hsq : Real.sqrt (1 / K) = 1 / Real.sqrt K := by
    rw [Real.sqrt_div' 1 hK0.le, Real.sqrt_one]
  calc ‖Wp sys L H u - molecularH2Truncate n (Wp sys L H u)‖
      ≤ ∑ a : Fin eta, ‖tailMask (gF L) K a (Wp sys L H u)‖ :=
        PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) n _
    _ ≤ ∑ _a : Fin eta, CtW sys L Hunit M * Real.sqrt (1 / K) :=
        Finset.sum_le_sum fun a _ => ht a
    _ = eta * CtW sys L Hunit 1 * M / Real.sqrt K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, CtW_linear, hsq]
        ring

end WTail

/-! ## Low grid states and the absorption of their momentum tails -/

section GridLow

variable {eta : ℕ} {ν : Type} [Fintype ν] {m : ℕ} (P : RegParticles eta) (Dn : NucData ν)
  {κ : Lat3 → ℝ} (g : ℝ) (hκe : ∀ x, κ (-x) = κ x)

/-- The low weight `1_{λ_a ≤ 2Λ}/λ_a`, `λ_a = E_a + c`. -/
noncomputable def lowW (c Λ : ℝ) (a : GrIdx eta m) : ℂ :=
  if grE P Dn g hκe a + c ≤ 2 * Λ then (((grE P Dn g hκe a + c : ℝ) : ℂ))⁻¹ else 0

/-- **The low inverse-weighted grid states** `f ↦ Σ_a 1_{λ_a ≤ 2Λ} (f_a/λ_a) e_a`, i.e.
`(G + c)⁻¹ 1_{G + c ≤ 2Λ}` in the grid eigenbasis. -/
noncomputable def grVL (c Λ : ℝ) :
    EuclideanSpace ℂ (GrIdx eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  (grB P Dn g hκe).repr.symm.toLinearIsometry.toContinuousLinearMap ∘L
    mop (fun a b => if a = b then lowW P Dn g hκe c Λ a else 0)

lemma grVL_coord (c Λ : ℝ) (f : EuclideanSpace ℂ (GrIdx eta m)) (a : GrIdx eta m) :
    ⟪grB P Dn g hκe a, grVL P Dn g hκe c Λ f⟫_ℂ = lowW P Dn g hκe c Λ a * f a := by
  classical
  rw [← OrthonormalBasis.repr_apply_apply]
  simp only [grVL, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.apply_symm_apply, mop_apply]
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
    (fun h => absurd (Finset.mem_univ a) h), if_pos rfl]

lemma norm_lowW_le (c Λ : ℝ) (hc1 : ∀ a : GrIdx eta m, 1 ≤ grE P Dn g hκe a + c) (a : GrIdx eta m) :
    ‖lowW P Dn g hκe c Λ a‖ ≤ 1 := by
  unfold lowW
  split_ifs
  · rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hc1 a])]
    exact inv_le_one_of_one_le₀ (hc1 a)
  · simp

lemma norm_grVL_apply_le (c Λ : ℝ) (hc1 : ∀ a : GrIdx eta m, 1 ≤ grE P Dn g hκe a + c)
    (f : EuclideanSpace ℂ (GrIdx eta m)) : ‖grVL P Dn g hκe c Λ f‖ ≤ ‖f‖ := by
  rw [← (grB P Dn g hκe).repr.norm_map]
  have h := norm_le_of_coord (s := 1) zero_le_one
    (x := (grB P Dn g hκe).repr (grVL P Dn g hκe c Λ f)) (y := f) fun a => by
      rw [OrthonormalBasis.repr_apply_apply, grVL_coord, norm_mul, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_lowW_le P Dn g hκe c Λ hc1 a)
  rwa [one_mul] at h

/-- `G (grVL f) = grVL (E_low ⊙ f)`. -/
lemma Hgrid_grVL (c Λ : ℝ) (f : EuclideanSpace ℂ (GrIdx eta m)) :
    Hgrid eta m P Dn κ g (grVL P Dn g hκe c Λ f) =
      grVL P Dn g hκe c Λ (WithLp.toLp 2 (fun a =>
        (if grE P Dn g hκe a + c ≤ 2 * Λ then (grE P Dn g hκe a : ℂ) else 0) * f a)) := by
  apply (grB P Dn g hκe).repr.injective
  ext a
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply, inner_grB_Hgrid,
    grVL_coord, grVL_coord]
  simp only [lowW]
  split_ifs <;> ring

lemma norm_Hgrid_grVL_le {c : ℝ} (Λ : ℝ) (hc : 0 ≤ c)
    (hc1 : ∀ a : GrIdx eta m, 1 ≤ grE P Dn g hκe a + c)
    (f : EuclideanSpace ℂ (GrIdx eta m)) :
    ‖Hgrid eta m P Dn κ g (grVL P Dn g hκe c Λ f)‖ ≤ (1 + c) * ‖f‖ := by
  rw [← (grB P Dn g hκe).repr.norm_map]
  refine norm_le_of_coord (by linarith) fun a => ?_
  rw [OrthonormalBasis.repr_apply_apply, inner_grB_Hgrid, grVL_coord, ← mul_assoc, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  unfold lowW
  split_ifs with ha
  · have h1 := hc1 a
    have hpos : (0 : ℝ) < grE P Dn g hκe a + c := by linarith
    rw [norm_mul, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hpos, ← div_eq_mul_inv, div_le_iff₀ hpos]
    rcases abs_cases (grE P Dn g hκe a) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
  · simp only [mul_zero, norm_zero]
    linarith

/-- The elliptic constant of the low grid states,
`c_W = (4/3)(1 + (2/g²)(1 + c + 26 Z J₀))`. -/
noncomputable def cWv (P : RegParticles eta) (Dn : NucData ν) (γ g c : ℝ) : ℝ :=
  4 / 3 * (1 + 2 / g ^ 2 * (1 + c + 26 * (P.maxMass * Zc P Dn γ) *
    (J0g (P.maxMass * Zc P Dn γ) g : ℝ)))

lemma cWv_nonneg {γ c : ℝ} (hγ : 0 ≤ γ) (hc : 0 ≤ c) : 0 ≤ cWv P Dn γ g c := by
  unfold cWv
  have := Zc_nonneg (P := P) (D := Dn) hγ
  have := P.maxMass_pos
  positivity

/-- **The weight of the low grid states** (`lem:grid-KR`(iv)): `‖W v‖ ≤ c_W ‖f‖`. -/
lemma norm_wM_grVL_le {γ : ℝ} (hγ : 0 ≤ γ) (hκb : ∀ x, |κ x| ≤ γ * coul x) (hg : 0 < g)
    {c : ℝ} (Λ : ℝ) (hc : 0 ≤ c) (hc1 : ∀ a : GrIdx eta m, 1 ≤ grE P Dn g hκe a + c)
    (f : EuclideanSpace ℂ (GrIdx eta m)) :
    ‖wMul (wM P) (grVL P Dn g hκe c Λ f)‖ ≤ cWv P Dn γ g c * ‖f‖ := by
  have h := (gridRegHam (eta := eta) (m := m) (P := P) (D := Dn) hγ hκb hg).elliptic_gen
    (grVL P Dn g hκe c Λ f)
  rw [gridRegHam_W, gridRegHam_op, gridRegHam_g, gridRegHam_Z, gridRegHam_J0] at h
  have h1 := norm_grVL_apply_le P Dn g hκe c Λ hc1 f
  have h2 := norm_Hgrid_grVL_le P Dn g hκe Λ hc hc1 f
  refine h.trans ?_
  have hZ : 0 ≤ P.maxMass * Zc P Dn γ := mul_nonneg P.maxMass_pos.le (Zc_nonneg hγ)
  have hJ : (0 : ℝ) ≤ (J0g (P.maxMass * Zc P Dn γ) g : ℝ) := Nat.cast_nonneg _
  have hg2 : 0 < 2 / g ^ 2 := by positivity
  have hZJ : 0 ≤ 26 * (P.maxMass * Zc P Dn γ) * (J0g (P.maxMass * Zc P Dn γ) g : ℝ) := by
    positivity
  have h3 : ‖Hgrid eta m P Dn κ g (grVL P Dn g hκe c Λ f)‖ +
      26 * (P.maxMass * Zc P Dn γ) * (J0g (P.maxMass * Zc P Dn γ) g : ℝ) *
        ‖grVL P Dn g hκe c Λ f‖ ≤
      (1 + c + 26 * (P.maxMass * Zc P Dn γ) * (J0g (P.maxMass * Zc P Dn γ) g : ℝ)) * ‖f‖ := by
    have := mul_le_mul_of_nonneg_left h1 hZJ
    nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 hg2.le
  unfold cWv
  nlinarith

/-- The absorption constant of the low grid states, `C_gt = 4 m̄ Z_c m̄ c_W (52 + √4134)`. -/
noncomputable def cGt (P : RegParticles eta) (Dn : NucData ν) (γ g c : ℝ) : ℝ :=
  4 * P.maxMass * (Zc P Dn γ * (P.maxMass * cWv P Dn γ g c) * (52 + Real.sqrt 4134))

lemma cGt_nonneg {γ c : ℝ} (hγ : 0 ≤ γ) (hc : 0 ≤ c) : 0 ≤ cGt P Dn γ g c := by
  unfold cGt
  have := Zc_nonneg (P := P) (D := Dn) hγ
  have := P.maxMass_pos
  have := cWv_nonneg P Dn g hγ hc
  positivity

/-- The `T^{-1/2}` arithmetic of the potential shells with `J = ⌊T/2⌋`. -/
lemma shell_half_arith (T : ℕ) (hT : 2 ≤ T) :
    26 * ((T / 2 : ℕ) : ℝ) / (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2 ≤ 52 / Real.sqrt T ∧
      Real.sqrt (1378 / ((T / 2 : ℕ) : ℝ)) ≤ Real.sqrt 4134 / Real.sqrt T := by
  set J := T / 2 with hJ
  have hJ1 : 1 ≤ J := by omega
  have h2J : 2 * J ≤ T := by omega
  have h3J : T ≤ 3 * J := by omega
  have hJT : J ≤ T := by omega
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have h2Jr : 2 * (J : ℝ) ≤ T := by exact_mod_cast h2J
  have h3Jr : (T : ℝ) ≤ 3 * J := by exact_mod_cast h3J
  have hX : ((T - J : ℕ) : ℝ) = T - J := by rw [Nat.cast_sub hJT]
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  have hsTle : Real.sqrt T ≤ T := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  constructor
  · rw [hX, div_le_div_iff₀ (by nlinarith) hsT]
    have h1 : (T : ℝ) / 2 ≤ T - J + 1 := by linarith
    have h2 : ((T : ℝ) / 2) ^ 2 ≤ (T - J + 1) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    nlinarith
  · have e : Real.sqrt 4134 / Real.sqrt T = Real.sqrt (4134 / T) :=
      (Real.sqrt_div' 4134 (by linarith : (0 : ℝ) ≤ T)).symm
    rw [e]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

end GridLow

section GridAbsorb

variable {eta : ℕ} {ν : Type} [Fintype ν] {m : ℕ} (P : RegParticles eta) (Dn : NucData ν)
  {κ : Lat3 → ℝ} (g : ℝ) (hκe : ∀ x, κ (-x) = κ x)

set_option maxHeartbeats 800000 in
/-- **Absorption of the momentum tails of low grid states** (`lem:kinetic-low`, grid side): if
`4 m̄ (2Λ + c_gr) ≤ g² (T+1)²`, then for every register `r`
`‖1_{High T r} (G + c)⁻¹ 1_{G + c ≤ 2Λ} f‖ ≤ C_gt / (g² (T+1)² √T) ‖f‖`, uniformly over the
kernel class. The proof absorbs the operator norm: `G` maps low states to low states with
eigenvalues `|E_a| ≤ 2Λ + c_gr`, the kinetic symbol is at least `g² (T+1)²/(2 m̄)` on the shell,
and the collocated potential has `T^{-1/2}` shells (`vGridK_tail`, `sq_mul_norm_high_le_gen`). -/
theorem grid_low_tail {γ : ℝ} (hγ : 0 ≤ γ) (hκb : ∀ x, |κ x| ≤ γ * coul x) (hg : 0 < g)
    {c Λ : ℝ} (hc : 0 ≤ c) (hΛ0 : 0 ≤ Λ) (hc1 : ∀ a : GrIdx eta m, 1 ≤ grE P Dn g hκe a + c)
    (T : ℕ) (hT : 2 ≤ T) (hTm : T ≤ 2 * m) (r : Fin eta)
    (hΛ : 4 * P.maxMass * (2 * Λ + cGr P Dn γ g) ≤ g ^ 2 * ((T : ℝ) + 1) ^ 2)
    (f : EuclideanSpace ℂ (GrIdx eta m)) :
    ‖maskOp (High T r) (grVL P Dn g hκe c Λ f)‖ ≤
      cGt P Dn γ g c / (g ^ 2 * ((T : ℝ) + 1) ^ 2 * Real.sqrt T) * ‖f‖ := by
  classical
  have hM := P.maxMass_pos
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  have hgT : 0 < g ^ 2 * ((T : ℝ) + 1) ^ 2 := by positivity
  have hcG := cGr_nonneg P Dn g hγ
  set A := 2 * P.maxMass / (g ^ 2 * ((T : ℝ) + 1) ^ 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hAΛ : A * (2 * Λ + cGr P Dn γ g) ≤ 1 / 2 := by
    rw [hA, div_mul_eq_mul_div, div_le_iff₀ hgT]
    linarith
  set tailG : EuclideanSpace ℂ (GrIdx eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
    (LinearMap.toContinuousLinearMap (maskOp (High T r))) ∘L grVL P Dn g hκe c Λ with htailG
  have htail : ∀ f, tailG f = maskOp (High T r) (grVL P Dn g hκe c Λ f) := fun f => rfl
  set N := ‖tailG‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  set Vt := Zc P Dn γ * (P.maxMass * cWv P Dn γ g c) * (52 + Real.sqrt 4134) with hVt
  have hVt0 : 0 ≤ Vt := by
    have := Zc_nonneg (P := P) (D := Dn) hγ
    have := cWv_nonneg P Dn g hγ hc
    positivity
  -- the potential part
  have hV : ∀ f, ‖maskOp (High T r) (kOp (vGridK eta m P Dn κ) (grVL P Dn g hκe c Λ f))‖ ≤
      Vt / Real.sqrt T * ‖f‖ := by
    intro f
    set v := grVL P Dn g hκe c Λ f
    have hJ1 : 1 ≤ T / 2 := by omega
    have hJT : T / 2 ≤ T := Nat.div_le_self T 2
    have h := vGridK_tail (P := P) (D := Dn) hγ hκb (T / 2) T hJ1 hJT hTm r v
    have hsh := sq_mul_norm_high_le_gen P (T - T / 2) r v
    have hW := norm_wMul_wTot_le P v
    have hE := norm_wM_grVL_le P Dn g hκe hγ hκb hg Λ hc hc1 f
    obtain ⟨ha1, ha2⟩ := shell_half_arith T hT
    have hZ := Zc_nonneg (P := P) (D := Dn) hγ
    have hX : 0 < ((T - T / 2 : ℕ) : ℝ) + 1 := by positivity
    have hcW := cWv_nonneg P Dn g hγ hc
    have hf := norm_nonneg f
    -- the shell term
    have hs1 : 26 * ((T / 2 : ℕ) : ℝ) * ‖maskOp (High (T - T / 2) r) v‖ ≤
        52 / Real.sqrt T * (P.maxMass * (cWv P Dn γ g c * ‖f‖)) := by
      have hm1 : ‖maskOp (High (T - T / 2) r) v‖ ≤
          P.maxMass * ‖wMul (wM P) v‖ / (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2 := by
        rw [le_div_iff₀ (by positivity), mul_comm]
        exact hsh
      have hm2 : P.maxMass * ‖wMul (wM P) v‖ ≤ P.maxMass * (cWv P Dn γ g c * ‖f‖) :=
        mul_le_mul_of_nonneg_left hE hM.le
      calc 26 * ((T / 2 : ℕ) : ℝ) * ‖maskOp (High (T - T / 2) r) v‖
          ≤ 26 * ((T / 2 : ℕ) : ℝ) * (P.maxMass * ‖wMul (wM P) v‖ /
              (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2) := by gcongr
        _ = 26 * ((T / 2 : ℕ) : ℝ) / (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2 *
              (P.maxMass * ‖wMul (wM P) v‖) := by ring
        _ ≤ 52 / Real.sqrt T * (P.maxMass * (cWv P Dn γ g c * ‖f‖)) :=
            mul_le_mul ha1 hm2 (by positivity) (by positivity)
    have hs2 : Real.sqrt (1378 / ((T / 2 : ℕ) : ℝ)) * ‖wMul wTot v‖ ≤
        Real.sqrt 4134 / Real.sqrt T * (P.maxMass * (cWv P Dn γ g c * ‖f‖)) := by
      have hm2 : ‖wMul wTot v‖ ≤ P.maxMass * (cWv P Dn γ g c * ‖f‖) :=
        hW.trans (mul_le_mul_of_nonneg_left hE hM.le)
      exact mul_le_mul ha2 hm2 (norm_nonneg _) (by positivity)
    refine h.trans ?_
    have e : Vt / Real.sqrt T * ‖f‖ = Zc P Dn γ * (52 / Real.sqrt T *
        (P.maxMass * (cWv P Dn γ g c * ‖f‖))) +
        Zc P Dn γ * (Real.sqrt 4134 / Real.sqrt T * (P.maxMass * (cWv P Dn γ g c * ‖f‖))) := by
      rw [hVt]
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hs1 hZ
    have := mul_le_mul_of_nonneg_left hs2 hZ
    nlinarith
  -- the eigenvalue part
  have hE : ∀ f, ‖maskOp (High T r) (Hgrid eta m P Dn κ g (grVL P Dn g hκe c Λ f))‖ ≤
      N * ((2 * Λ + cGr P Dn γ g) * ‖f‖) := by
    intro f
    rw [Hgrid_grVL, ← htail]
    refine (tailG.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ hN0)
    refine norm_le_of_coord (by positivity) fun a => ?_
    change ‖(if grE P Dn g hκe a + c ≤ 2 * Λ then (grE P Dn g hκe a : ℂ) else 0) * f a‖ ≤
      (2 * Λ + cGr P Dn γ g) * ‖f a‖
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    split_ifs with ha
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      have hl := grE_lower P Dn g hκe hγ hκb hg a
      constructor <;> linarith
    · rw [norm_zero]
      positivity
  -- absorption
  have hstep : ∀ f, ‖tailG f‖ ≤ (A * (2 * Λ + cGr P Dn γ g) * N + A * (Vt / Real.sqrt T)) * ‖f‖ :=
    by
    intro f
    rw [htail]
    set v := grVL P Dn g hκe c Λ f
    have h1 := norm_high_le_kinT P hg T r v
    have hsplit : wMul (kinT eta m P g) v =
        Hgrid eta m P Dn κ g v - kOp (vGridK eta m P Dn κ) v := by
      simp only [Hgrid, LinearMap.add_apply]
      abel
    rw [hsplit, map_sub] at h1
    have h2 := norm_sub_le (maskOp (High T r) (Hgrid eta m P Dn κ g v))
      (maskOp (High T r) (kOp (vGridK eta m P Dn κ) v))
    have h3 := hE f
    have h4 := hV f
    calc ‖maskOp (High T r) v‖
        ≤ A * ‖maskOp (High T r) (Hgrid eta m P Dn κ g v) -
            maskOp (High T r) (kOp (vGridK eta m P Dn κ) v)‖ := h1
      _ ≤ A * (N * ((2 * Λ + cGr P Dn γ g) * ‖f‖) + Vt / Real.sqrt T * ‖f‖) :=
          mul_le_mul_of_nonneg_left (h2.trans (add_le_add h3 h4)) hA0
      _ = _ := by ring
  have hNle : N ≤ A * (2 * Λ + cGr P Dn γ g) * N + A * (Vt / Real.sqrt T) :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) hstep
  have hN2 : N ≤ 2 * (A * (Vt / Real.sqrt T)) := by nlinarith
  have hfin : 2 * (A * (Vt / Real.sqrt T)) =
      cGt P Dn γ g c / (g ^ 2 * ((T : ℝ) + 1) ^ 2 * Real.sqrt T) := by
    rw [hA, hVt]
    unfold cGt
    field_simp
    ring
  have hfinal : ‖tailG f‖ ≤ N * ‖f‖ := tailG.le_opNorm f
  rw [htail] at hfinal
  calc ‖maskOp (High T r) (grVL P Dn g hκe c Λ f)‖ ≤ N * ‖f‖ := hfinal
    _ ≤ 2 * (A * (Vt / Real.sqrt T)) * ‖f‖ := mul_le_mul_of_nonneg_right hN2 (norm_nonneg _)
    _ = _ := by rw [hfin]

end GridAbsorb

end KineticLog
