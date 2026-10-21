import PlaneWave.Source.RetainedCorrection
import PlaneWave.Source.ExponentialBounds

/-!
# Flux/source build, block 3e: the dressed state (`lem:dressed-tails`)

Block structure of the bulk generator on `ℓ²` (`P` the cube, `Q` the Euclidean bulk block,
`R = 1 - P`):

* `sig_exterior`: `R Σ_b = Σ_b Q` (the exterior part of `Σ_b x` is `Σ_b` of the bulk part of `x`);
* `sig_interior`: `P Σ_b = Σ_b R` (its cube part is `Σ_b` of the exterior part, supported in `Q`);
* `sig_split`: `Σ_b x = Σ_b Q x + Σ_b R x` (`Σ_b` vanishes on `P - Q`).

The exact remainder `e^{Z} - 1 - Z = Z J` with `J = ∫₀¹ (e^{rZ} - 1) dr` and `‖J x‖ ≤ ‖Z x‖`
(`FSConj.mul_Jx`, `FSConj.norm_Jx_apply_le`), so that for the dressed state `ψ̃ = e^{Σ_b} x`:

* `dressed_exterior`: `R ψ̃ = R x + Σ_b Q x + Σ_b Q J x`;
* `dressed_interior`: `P ψ̃ = P x + Σ_b R x + Σ_b R J x`;
* `dressed_lift`: in `H²` coordinates (`x = S w₀`, `ψ̃ = S w`),
  `w - P w = (w₀ - P w₀) + Σ_D Q x + Σ_D Q J x`, so `W (w - P w) = W (w₀ - P w₀) + Zw Q x + Zw Q J x`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics NormedSpace FluxSourceTest FSGalerkin
open MeasureTheory intervalIntegral

/-! ## The exact remainder `e^{Z} - 1 - Z = Z J` -/

namespace FSConj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {Z : E →L[ℂ] E}

lemma continuous_ex (Z : E →L[ℂ] E) : Continuous (ex Z) :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_ex Z r).continuousAt

/-- `J = ∫₀¹ (e^{rZ} - 1) dr`. -/
noncomputable def Jx (Z : E →L[ℂ] E) : E →L[ℂ] E := ∫ r in (0 : ℝ)..1, (ex Z r - 1)

lemma intervalIntegrable_ex_sub (Z : E →L[ℂ] E) :
    IntervalIntegrable (fun r => ex Z r - 1) volume 0 1 :=
  ((continuous_ex Z).sub continuous_const).intervalIntegrable 0 1

/-- **`e^{Z} - 1 - Z = Z J`.** -/
theorem mul_Jx (Z : E →L[ℂ] E) : Z * Jx Z = exp Z - 1 - Z := by
  have h1 : Z * Jx Z = ∫ r in (0 : ℝ)..1, Z * (ex Z r - 1) := by
    have := (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) Z).intervalIntegral_comp_comm
      (intervalIntegrable_ex_sub Z)
    simpa [Jx] using this.symm
  have h2 : ∀ r : ℝ, Z * (ex Z r - 1) = ex Z r * Z - Z := by
    intro r
    rw [mul_sub, mul_one, (commute_ex Z r).eq]
  simp_rw [h2] at h1
  have hcont : Continuous fun r => ex Z r * Z := (continuous_ex Z).mul continuous_const
  have hftc := integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun r _ => hasDerivAt_ex Z r)
    (hcont.intervalIntegrable 0 1)
  rw [h1, intervalIntegral.integral_sub (hcont.intervalIntegrable 0 1) intervalIntegrable_const,
    hftc, intervalIntegral.integral_const, ex_one, ex_zero]
  simp

lemma Jx_apply (Z : E →L[ℂ] E) (x : E) : Jx Z x = ∫ r in (0 : ℝ)..1, (ex Z r x - x) := by
  have := ContinuousLinearMap.intervalIntegral_apply (intervalIntegrable_ex_sub Z) x
  simpa [Jx] using this

/-- **`‖J x‖ ≤ ‖Z x‖`** for skew-adjoint `Z`. -/
theorem norm_Jx_apply_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (x : E) : ‖Jx Z x‖ ≤ ‖Z x‖ := by
  rw [Jx_apply]
  have := norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := ‖Z x‖)
    (f := fun r => ex Z r x - x) fun r hr => by
      refine (norm_ex_sub_apply_le hZ r x).trans ?_
      have hr' : r ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hr
      have : |r| ≤ 1 := by rw [abs_of_pos hr'.1]; exact hr'.2
      exact mul_le_of_le_one_left (norm_nonneg _) this
  simpa using this

/-- `e^{Z} x = x + Z x + Z (J x)`. -/
lemma exp_apply_eq (Z : E →L[ℂ] E) (x : E) : exp Z x = x + Z x + Z (Jx Z x) := by
  have h := congrArg (fun A : E →L[ℂ] E => A x) (mul_Jx Z)
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] at h
  rw [h]; abel

end FSConj

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)

/-! ## Block structure of `Σ_b` -/

open Classical in
/-- **`R Σ_b = Σ_b Q`.** -/
theorem sig_exterior (x : L2 eta) :
    Sig sys L n hL hn x - molecularH2Truncate n (Sig sys L n hL hn x) =
      Sig sys L n hL hn (lpTruncate (Qs eta n) x) := by
  ext q
  rw [sub_truncate_apply, Sig_truncQ_apply]
  split_ifs with hqP
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    unfold sigK
    rw [if_neg, zero_mul]
    rintro (⟨-, hpP⟩ | ⟨hq', -⟩)
    · exact hpP ((mem_Qs.mp hp).inP (Nat.cast_nonneg n))
    · exact hq' hqP
  · rw [Sig_apply, tsum_eq_sum (s := Qs eta n)]
    intro p hp
    unfold sigK
    rw [if_neg, zero_mul]
    rintro (⟨hq', -⟩ | ⟨-, hp'⟩)
    · exact hqP (hq'.inP (Nat.cast_nonneg n))
    · exact hp (mem_Qs.mpr hp')

open Classical in
/-- **`P Σ_b = Σ_b R`.** -/
theorem sig_interior (x : L2 eta) :
    molecularH2Truncate n (Sig sys L n hL hn x) =
      Sig sys L n hL hn (x - molecularH2Truncate n x) := by
  ext q
  rw [molecularH2Truncate_apply]
  by_cases hq : q ∈ fourierConfigCube eta n
  · have hqP : InP (n : ℝ) q := (inP_iff_mem_cube n q).mpr hq
    rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hq, Sig_apply, Sig_apply]
    refine tsum_congr fun p => ?_
    rw [sub_truncate_apply]
    unfold sigK
    split_ifs with hc hp
    · rcases hc with ⟨-, hp'⟩ | ⟨hq', -⟩
      · exact absurd hp hp'
      · exact absurd hqP hq'
    · rfl
    · rw [zero_mul, zero_mul]
    · rfl
  · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq, Sig_apply]
    have hqP : ¬ InP (n : ℝ) q := fun h => hq ((inP_iff_mem_cube n q).mp h)
    symm
    refine (tsum_congr fun p => ?_).trans tsum_zero
    rw [sub_truncate_apply]
    unfold sigK
    split_ifs with hc hp
    · rw [mul_zero]
    · rcases hc with ⟨hq', -⟩ | ⟨-, hp'⟩
      · exact absurd (hq'.inP (Nat.cast_nonneg n)) hqP
      · exact absurd (hp'.inP (Nat.cast_nonneg n)) hp
    · rw [zero_mul]
    · rw [zero_mul]

open Classical in
omit [Fintype ν] in
lemma truncQ_sub_truncate (x : L2 eta) :
    lpTruncate (Qs eta n) x - molecularH2Truncate n (lpTruncate (Qs eta n) x) = 0 := by
  ext q
  rw [sub_truncate_apply, lpTruncate_apply, lp.coeFn_zero, Pi.zero_apply]
  split_ifs with h1 h2
  · rfl
  · exact absurd ((mem_Qs.mp h2).inP (Nat.cast_nonneg n)) h1
  · rfl

open Classical in
/-- **`Σ_b x = Σ_b Q x + Σ_b R x`.** -/
theorem sig_split (x : L2 eta) :
    Sig sys L n hL hn x = Sig sys L n hL hn (lpTruncate (Qs eta n) x) +
      Sig sys L n hL hn (x - molecularH2Truncate n x) := by
  set Sg := Sig sys L n hL hn
  set y := x - lpTruncate (Qs eta n) x
  have hy0 : lpTruncate (Qs eta n) y = 0 := by
    ext q
    simp only [y, lpTruncate_apply, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_zero, Pi.zero_apply]
    split_ifs <;> simp
  have hext := sig_exterior sys hL hn y
  rw [hy0, map_zero, sub_eq_zero] at hext
  have hint := sig_interior sys hL hn y
  have hRy : y - molecularH2Truncate n y = x - molecularH2Truncate n x := by
    have := truncQ_sub_truncate (n := n) x
    simp only [y, molecularH2Truncate_sub]
    rw [← sub_eq_zero]
    have e : x - lpTruncate (Qs eta n) x - (molecularH2Truncate n x -
        molecularH2Truncate n (lpTruncate (Qs eta n) x)) - (x - molecularH2Truncate n x) =
        -(lpTruncate (Qs eta n) x - molecularH2Truncate n (lpTruncate (Qs eta n) x)) := by abel
    rw [e, this, neg_zero]
  have hSy : Sg y = Sg (x - molecularH2Truncate n x) := by
    rw [hext, hint, hRy]
  have : Sg x = Sg (lpTruncate (Qs eta n) x) + Sg y := by
    rw [← map_add]; simp only [y]; abel_nf
  rw [this, hSy]

/-! ## The dressed state -/

open Classical in
/-- **`R e^{Σ_b} x = R x + Σ_b Q x + Σ_b Q J x`.** -/
theorem dressed_exterior (x : L2 eta) :
    exp (Sig sys L n hL hn) x - molecularH2Truncate n (exp (Sig sys L n hL hn) x) =
      (x - molecularH2Truncate n x) + Sig sys L n hL hn (lpTruncate (Qs eta n) x) +
        Sig sys L n hL hn (lpTruncate (Qs eta n) (FSConj.Jx (Sig sys L n hL hn) x)) := by
  set Sg := Sig sys L n hL hn
  set J := FSConj.Jx Sg x
  rw [FSConj.exp_apply_eq Sg x, molecularH2Truncate_add, molecularH2Truncate_add]
  have h1 := sig_exterior sys hL hn x
  have h2 := sig_exterior sys hL hn J
  rw [← h1, ← h2]
  abel

open Classical in
/-- **`P e^{Σ_b} x = P x + Σ_b R x + Σ_b R J x`.** -/
theorem dressed_interior (x : L2 eta) :
    molecularH2Truncate n (exp (Sig sys L n hL hn) x) =
      molecularH2Truncate n x + Sig sys L n hL hn (x - molecularH2Truncate n x) +
        Sig sys L n hL hn (FSConj.Jx (Sig sys L n hL hn) x -
          molecularH2Truncate n (FSConj.Jx (Sig sys L n hL hn) x)) := by
  set Sg := Sig sys L n hL hn
  rw [FSConj.exp_apply_eq Sg x, molecularH2Truncate_add, molecularH2Truncate_add,
    sig_interior sys hL hn x,
    sig_interior sys hL hn (FSConj.Jx Sg x)]

variable (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)

open Classical in
/-- **The dressed state in `H²` coordinates**: for `S w₀ = x` and `w = e^{Σ_G} w₀` (`S w = e^{Σ} x`),
`w - P w = (w₀ - P w₀) + Σ_D Q x + Σ_D Q J x`. -/
theorem dressed_lift (w₀ : MolecularFourierH2 eta) :
    exp (SigG sys hL hn) w₀ - molecularH2Truncate n (exp (SigG sys hL hn) w₀) =
      (w₀ - molecularH2Truncate n w₀) +
        SigD sys L n hL (by omega) (lpTruncate (Qs eta n) (Sm eta L w₀)) +
        SigD sys L n hL (by omega) (lpTruncate (Qs eta n)
          (FSConj.Jx (Sig sys L n hL hn) (Sm eta L w₀))) := by
  apply molecularH2StateMap_injective eta (gF L)
  change Sm eta L _ = Sm eta L _
  rw [map_sub, map_add, map_add, map_sub, stateMap_SigD hL hn, stateMap_SigD hL hn]
  have hS : ∀ y : MolecularFourierH2 eta, Sm eta L (molecularH2Truncate n y) =
      molecularH2Truncate n (Sm eta L y) := fun y => stateMap_truncate (gF L) n y
  rw [hS, hS, exp_SigG_apply]
  exact dressed_exterior sys hL hn (Sm eta L w₀)

open Classical in
/-- `W (w - P w) = W (w₀ - P w₀) + Zw Q x + Zw Q J x`. -/
theorem dressed_potential (w₀ : MolecularFourierH2 eta) :
    Wp sys L H (exp (SigG sys hL hn) w₀ - molecularH2Truncate n (exp (SigG sys hL hn) w₀)) =
      Wp sys L H (w₀ - molecularH2Truncate n w₀) +
        Zw sys hL hn H (lpTruncate (Qs eta n) (Sm eta L w₀)) +
        Zw sys hL hn H (lpTruncate (Qs eta n) (FSConj.Jx (Sig sys L n hL hn) (Sm eta L w₀))) := by
  rw [dressed_lift sys hL hn w₀, map_add, map_add]
  rfl


/-! ## Uniform constants -/

/-- `A₀ = A_σ n`. -/
noncomputable def A0 (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  ∑ j : Ch eta, chC sys L j / cgap sys (gF L) * (416 / 3)

include hL in
lemma A0_nonneg : 0 ≤ A0 sys L := by
  unfold A0
  refine Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg (chC_nonneg sys hL j)
    (cgap_pos sys (gF_pos hL).ne').le) (by norm_num)

lemma Asig_eq (hn0 : 0 < n) : Asig sys L n = A0 sys L / n := by
  unfold Asig A0
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  field_simp

/-- `M₀ n⁵`. -/
noncomputable def cM0 (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  Fintype.card (Ch eta) * cSig2 sys L * (256 / 81) * (416 / 3)

/-- `M₁ n³`. -/
noncomputable def cM1 (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  Fintype.card (Ch eta) * cSig2 sys L * c1E eta L * (16 / 9) * (416 / 3)

lemma M0_eq (hn0 : 0 < n) : M0 sys L n = cM0 sys L / (n : ℝ) ^ 5 := by
  unfold M0 cM0
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  field_simp
  ring

lemma M1_eq (hn0 : 0 < n) : M1 sys L n = cM1 sys L / (n : ℝ) ^ 3 := by
  unfold M1 cM1
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  field_simp
  ring

lemma cSig2_nonneg : 0 ≤ cSig2 sys L :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [Fintype ν] in
lemma c1E_pos : 0 < c1E eta L := by unfold c1E; positivity

lemma cM0_nonneg : 0 ≤ cM0 sys L := by
  unfold cM0; have := cSig2_nonneg sys (L := L); positivity

lemma cM1_nonneg : 0 ≤ cM1 sys L := by
  unfold cM1; have := cSig2_nonneg sys (L := L); have := c1E_pos (eta := eta) (L := L); positivity

/-- The kinetic comparison constant `c_E = 1 + 2 m_top/g²`: `1 + |p|² ≤ c_E (1 + E(p))`. -/
noncomputable def cE (sys : CoulombSystem eta ν) (L : ℝ) : ℝ := 1 + 2 * mtop sys / gF L ^ 2

omit [Fintype ν] in
lemma one_le_cE : 1 ≤ cE sys L := by
  unfold cE
  have := one_le_mtop sys
  have : 0 ≤ 2 * mtop sys / gF L ^ 2 := by positivity
  linarith

omit [Fintype ν] in
include hL in
lemma one_add_lsqC_le (p : Cf eta) : 1 + lsqC p ≤ cE sys L * (1 + Ek sys L p) := by
  have hg := gF_pos hL
  have hmt := one_le_mtop sys
  have hE : gF L ^ 2 / (2 * mtop sys) * lsqC p ≤ Ek sys L p := by
    rw [Ek, E, lsqC, Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (nsq_nonneg _)
    have := mass_le_mtop sys c
    have := sys.mass_pos c
    gcongr
  have hE0 : 0 ≤ Ek sys L p := E_nonneg (fun c => sys.mass_pos c) p
  have hl : lsqC p ≤ 2 * mtop sys / gF L ^ 2 * Ek sys L p := by
    have h2 : lsqC p = 2 * mtop sys / gF L ^ 2 * (gF L ^ 2 / (2 * mtop sys) * lsqC p) := by
      field_simp
    rw [h2]
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  have hc : 0 ≤ 2 * mtop sys / gF L ^ 2 := by positivity
  unfold cE
  nlinarith [mul_nonneg hc hE0]

omit [Fintype ν] in
include hL in
/-- `Σ_{p ∈ Q} (1 + |p|²)² |x_p|² ≤ c_E² (‖S w‖ + ‖T w‖)²`. -/
lemma sum_Ws_one_le (w : MolecularFourierH2 eta) :
    ∑ p ∈ Qs eta n, Ws 1 p * ‖Sm eta L w p‖ ^ 2 ≤
      cE sys L ^ 2 * (‖Sm eta L w‖ + ‖coulombFourierKineticH2 sys (gF L) w‖) ^ 2 := by
  set x := Sm eta L w
  set y := x + coulombFourierKineticH2 sys (gF L) w
  have hy : ∀ p, y p = ((1 + Ek sys L p : ℝ) : ℂ) * x p := by
    intro p
    simp only [y, x, lp.coeFn_add, Pi.add_apply, coulombFourierKineticH2_apply, Sm,
      molecularH2StateMap_apply]
    rw [Ek, E_eq_kineticSymbol]
    push_cast; ring
  have hpt : ∀ p, Ws 1 p * ‖x p‖ ^ 2 ≤ cE sys L ^ 2 * ‖y p‖ ^ 2 := by
    intro p
    rw [hy, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [E_nonneg (g := gF L) (fun c => sys.mass_pos c) p])]
    unfold Ws
    rw [mul_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h1 := one_add_lsqC_le sys hL p
    have h0 : 0 ≤ 1 + lsqC p := by linarith [lsqC_nonneg p]
    have h2 : (1 + lsqC p) ^ 2 ≤ (cE sys L * (1 + Ek sys L p)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    calc (1 + lsqC p) ^ 2 * ‖x p‖ ^ 2 ≤ (cE sys L * (1 + Ek sys L p)) ^ 2 * ‖x p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = _ := by ring
  calc ∑ p ∈ Qs eta n, Ws 1 p * ‖x p‖ ^ 2 ≤ ∑ p ∈ Qs eta n, cE sys L ^ 2 * ‖y p‖ ^ 2 :=
        Finset.sum_le_sum fun p _ => hpt p
    _ = cE sys L ^ 2 * ∑ p ∈ Qs eta n, ‖y p‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ cE sys L ^ 2 * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_left (sum_Qs_sq_le n y) (sq_nonneg _)
    _ ≤ cE sys L ^ 2 * (‖x‖ + ‖coulombFourierKineticH2 sys (gF L) w‖) ^ 2 := by
        gcongr
        exact norm_add_le _ _

/-! ## The dressed tails (`lem:dressed-tails`) -/

/-- The state constant `a₀ = (#Ch² M₀ Z₂)^{1/2} c_E` of `‖Σ_b Q x‖ ≤ a₀ (‖x‖ + ‖T x‖)`. -/
noncomputable def a0c (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (Ch eta) ^ 2 * M0 sys L n * 53) * cE sys L

/-- The form constant `a₁ = (#Ch² M₁ Z₂)^{1/2} c_E` of `‖E^{1/2} Σ_b Q x‖ ≤ a₁ (‖x‖ + ‖T x‖)`. -/
noncomputable def a1c (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (Ch eta) ^ 2 * M1 sys L n * 53) * cE sys L

lemma a0c_nonneg : 0 ≤ a0c sys L n := by
  unfold a0c; have := one_le_cE sys (L := L); positivity

lemma a1c_nonneg : 0 ≤ a1c sys L n := by
  unfold a1c; have := one_le_cE sys (L := L); positivity

open Classical in
/-- **`‖Σ_b Q x‖ ≤ a₀ (‖x‖ + ‖T x‖)`** (eq:bulk-weighted-state, `j = 0`, `s = 1`). -/
theorem norm_sigQ_le (w : MolecularFourierH2 eta) :
    ‖Sig sys L n hL hn (lpTruncate (Qs eta n) (Sm eta L w))‖ ≤
      a0c sys L n * (‖Sm eta L w‖ + ‖coulombFourierKineticH2 sys (gF L) w‖) := by
  set y := Sig sys L n hL hn (lpTruncate (Qs eta n) (Sm eta L w))
  have h := norm_sig_Q_state_le sys hL hn (s := 1) (by norm_num) (Sm eta L w)
  have hW := sum_Ws_one_le sys hL (n := n) w
  have hc : (1 + 26 * (1 + 1 / (2 * (2 * (1 : ℝ)) - 3))) = 53 := by norm_num
  rw [hc] at h
  have hM0 : 0 ≤ M0 sys L n := by
    rw [M0_eq sys (by omega)]; have := cM0_nonneg sys (L := L); positivity
  have h2 : ‖y‖ ^ 2 ≤ (a0c sys L n * (‖Sm eta L w‖ +
      ‖coulombFourierKineticH2 sys (gF L) w‖)) ^ 2 := by
    rw [← tsum_sq_coord y]
    unfold a0c
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    calc ∑' q, ‖y q‖ ^ 2 ≤ Fintype.card (Ch eta) ^ 2 * M0 sys L n * 53 *
          ∑ p ∈ Qs eta n, Ws 1 p * ‖Sm eta L w p‖ ^ 2 := h
      _ ≤ Fintype.card (Ch eta) ^ 2 * M0 sys L n * 53 *
          (cE sys L ^ 2 * (‖Sm eta L w‖ + ‖coulombFourierKineticH2 sys (gF L) w‖) ^ 2) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (a0c_nonneg sys) (by positivity))
    two_ne_zero).mp h2

open Classical in
/-- The form of `Σ_b Q x`: `Σ (1 + 2E) |Σ_b Q x|² ≤ (a₁ (‖x‖ + ‖T x‖))²` (eq:bulk-weighted-state,
`j = 1`, `s = 1`). -/
theorem form_sigQ_le (w : MolecularFourierH2 eta) :
    ∑' q, (1 + 2 * Ek sys L q) *
        ‖Sig sys L n hL hn (lpTruncate (Qs eta n) (Sm eta L w)) q‖ ^ 2 ≤
      (a1c sys L n * (‖Sm eta L w‖ + ‖coulombFourierKineticH2 sys (gF L) w‖)) ^ 2 := by
  have h := (form_sig_Q_state_le sys hL hn (s := 1) (by norm_num) (Sm eta L w)).2
  have hW := sum_Ws_one_le sys hL (n := n) w
  have hc : (1 + 26 * (1 + 1 / (2 * (2 * (1 : ℝ)) - 3))) = 53 := by norm_num
  rw [hc] at h
  have hM1 : 0 ≤ M1 sys L n := by
    rw [M1_eq sys (by omega)]; have := cM1_nonneg sys (L := L); positivity
  unfold a1c
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  calc _ ≤ Fintype.card (Ch eta) ^ 2 * M1 sys L n * 53 *
        ∑ p ∈ Qs eta n, Ws 1 p * ‖Sm eta L w p‖ ^ 2 := h
    _ ≤ Fintype.card (Ch eta) ^ 2 * M1 sys L n * 53 *
        (cE sys L ^ 2 * (‖Sm eta L w‖ + ‖coulombFourierKineticH2 sys (gF L) w‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = _ := by ring

variable (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

open Classical in
include hKernel in
/-- **`lem:dressed-tails`** (exterior bounds) for `x = S w₀` with `‖x‖ + ‖T w₀‖ ≤ M`,
`‖R x‖ ≤ ρ` and `‖W (w₀ - P w₀)‖ ≤ ω`: with `a₀ M` the bound of `‖Σ_b Q x‖`,

* `‖Σ_b x‖ ≤ a₀ M + A_σ ρ`;
* `‖R ψ̃‖ ≤ ρ + a₀ M + A_σ (a₀ M + A_σ ρ)`;
* `‖W (w - P w)‖ ≤ ω + C_m a₁ M + C_Z (a₀ M + A_σ ρ)` (`ψ̃ = e^{Σ_b} x = S w`);
* `‖P ψ̃ - P x‖ ≤ A_σ (ρ + a₀ M + A_σ ρ)`. -/
theorem dressed_tails (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (w₀ : MolecularFourierH2 eta) {ρ ω M : ℝ}
    (hR : ‖Sm eta L w₀ - molecularH2Truncate n (Sm eta L w₀)‖ ≤ ρ)
    (hW : ‖Wp sys L H (w₀ - molecularH2Truncate n w₀)‖ ≤ ω)
    (hM : ‖Sm eta L w₀‖ + ‖coulombFourierKineticH2 sys (gF L) w₀‖ ≤ M) :
    ‖Sig sys L n hL hn (Sm eta L w₀)‖ ≤ a0c sys L n * M + Asig sys L n * ρ ∧
    ‖exp (Sig sys L n hL hn) (Sm eta L w₀) -
        molecularH2Truncate n (exp (Sig sys L n hL hn) (Sm eta L w₀))‖ ≤
      ρ + a0c sys L n * M + Asig sys L n * (a0c sys L n * M + Asig sys L n * ρ) ∧
    ‖Wp sys L H (exp (SigG sys hL hn) w₀ - molecularH2Truncate n (exp (SigG sys hL hn) w₀))‖ ≤
      ω + finiteCoulombPhysicalMassConstant sys L Hunit * (a1c sys L n * M) +
        CZ sys L Hunit n * (a0c sys L n * M + Asig sys L n * ρ) ∧
    ‖molecularH2Truncate n (exp (Sig sys L n hL hn) (Sm eta L w₀)) -
        molecularH2Truncate n (Sm eta L w₀)‖ ≤
      Asig sys L n * (ρ + (a0c sys L n * M + Asig sys L n * ρ)) := by
  set x := Sm eta L w₀
  set Sg := Sig sys L n hL hn
  set J := FSConj.Jx Sg x
  have hskew := (Sig_skew_unitary (sys := sys) hL hn).1
  have hA := norm_Sig_le (sys := sys) hL hn
  have hA0 := Asig_nonneg (sys := sys) (n := n) hL
  have ha0 := a0c_nonneg sys (L := L) (n := n)
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  -- `‖Σ Q x‖ ≤ a₀ M`
  have hQ : ‖Sg (lpTruncate (Qs eta n) x)‖ ≤ a0c sys L n * M :=
    (norm_sigQ_le sys hL hn w₀).trans (mul_le_mul_of_nonneg_left hM ha0)
  -- `‖Σ x‖ ≤ a₀ M + A_σ ρ`
  have hSx : ‖Sg x‖ ≤ a0c sys L n * M + Asig sys L n * ρ := by
    rw [sig_split sys hL hn x]
    refine (norm_add_le _ _).trans (add_le_add hQ ?_)
    exact (Sg.le_opNorm _).trans (mul_le_mul hA hR (norm_nonneg _) hA0)
  have hJ : ‖J‖ ≤ a0c sys L n * M + Asig sys L n * ρ :=
    (FSConj.norm_Jx_apply_le hskew x).trans hSx
  have hJQ : ‖Sg (lpTruncate (Qs eta n) J)‖ ≤ Asig sys L n * (a0c sys L n * M + Asig sys L n * ρ) := by
    refine (Sg.le_opNorm _).trans (mul_le_mul hA ?_ (norm_nonneg _) hA0)
    exact (lpTruncate_norm_le _ J).trans hJ
  refine ⟨hSx, ?_, ?_, ?_⟩
  · rw [dressed_exterior sys hL hn x]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add hR hQ)) hJQ
  · rw [dressed_potential sys hL hn H w₀]
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans (add_le_add hW ?_)) ?_
    · -- `‖W Σ_D Q x‖ ≤ C_m a₁ M`
      have hf := potential_form_bound sys H hKernel Hunit hL hPeriodic
        (SigD sys L n hL (by omega) (lpTruncate (Qs eta n) x))
      rw [show Sm eta L (SigD sys L n hL (by omega) (lpTruncate (Qs eta n) x)) =
        Sg (lpTruncate (Qs eta n) x) from stateMap_SigD hL hn _] at hf
      have hform := form_sigQ_le sys hL hn w₀
      have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
      have ha1 := a1c_nonneg sys (L := L) (n := n)
      have h2 : ‖Zw sys hL hn H (lpTruncate (Qs eta n) x)‖ ^ 2 ≤
          (finiteCoulombPhysicalMassConstant sys L Hunit * (a1c sys L n * M)) ^ 2 := by
        calc ‖Zw sys hL hn H (lpTruncate (Qs eta n) x)‖ ^ 2 ≤
              finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
                ∑' q, (1 + 2 * Ek sys L q) * ‖Sg (lpTruncate (Qs eta n) x) q‖ ^ 2 := hf
          _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
                (a1c sys L n * (‖x‖ + ‖coulombFourierKineticH2 sys (gF L) w₀‖)) ^ 2 :=
              mul_le_mul_of_nonneg_left hform (sq_nonneg _)
          _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (a1c sys L n * M) ^ 2 := by
              gcongr
          _ = _ := by ring
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
    · refine ((Zw sys hL hn H).le_opNorm _).trans ?_
      exact mul_le_mul (opNorm_Zw_le sys hL hn H hKernel Hunit hPeriodic)
        ((lpTruncate_norm_le _ J).trans hJ) (norm_nonneg _) (CZ_nonneg sys Hunit)
  · rw [dressed_interior sys hL hn x]
    have e : molecularH2Truncate n x + Sg (x - molecularH2Truncate n x) +
        Sg (J - molecularH2Truncate n J) - molecularH2Truncate n x =
        Sg ((x - molecularH2Truncate n x) + (J - molecularH2Truncate n J)) := by
      rw [map_add]; abel
    rw [e]
    refine (Sg.le_opNorm _).trans (mul_le_mul hA ((norm_add_le _ _).trans (add_le_add hR ?_))
      (norm_nonneg _) hA0)
    exact (norm_sub_truncate_le n J).trans hJ

end FSNormal
