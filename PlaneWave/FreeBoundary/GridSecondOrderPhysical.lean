import PlaneWave.FreeBoundary.GridDynamicsUniform

/-!
# `L`-uniform grid dynamics, stage 4: second-order estimates in the physical weight
(development file)

The second-order estimates of the sharp grid-dynamics proof (`DevGS1`, `DevGS3`,
`PlaneWave.FreeBoundary.GridDynamicsSharp`) with the physical weight `w_g = 1 + g² Σ_b |n_b|²/m_b`
(`wPhys`, `PlaneWave.FreeBoundary.GridDynamicsUniform`) in place of the lattice weight
`wM = 1 + Σ_b |n_b|²/m_b`, and the physical Sobolev constant `S = sobP g = 1 + 78/g³` in place of
the lattice constants `53` and `1378`:

* the physical slice-Young inequality and the weighted transfer bound with the physical slice
  weight `1 + g²|X|²` (`kOp_sq_le_slicePh`, `norm_wMul_kOp_tk_lePh`);
* the weight across a transfer, `w_g q ≤ 2 w_g p + 4 |gτ|²`, and across a translation of the
  observable, `w_g q ≤ 2 w_g p + 2 |gν|²` (`wPhys_le_of_gRel2`, `wPhys_le_cyc`, `g ≤ 1`);
* the weighted Kato--Rellich bound `‖w_g (V u)‖ ≤ (1/4)‖w_g² u‖ + C₂ ‖w_g u‖` with
  `C₂ = Z_c (52 J₀ + 4 m̄ g² √(S (4m+1)³))`, `J₀ = J0P` (`norm_wPhys_vGridK_le_second`), and the
  second-order elliptic estimate `‖w_g² u‖ ≤ 2‖w_g u‖ + 4‖w_g (H u)‖ + 4 C₂ ‖w_g u‖`
  (`second_ellipticP`): the lattice estimates with kinetic scale `1/2` in place of `g²/2`;
* for the `g_L` coupling and `L ≥ 2π`, `C₂ ≤ σ_U r_g` with the `L`-free `σ_U = 2A + 4√79 z` and
  the physical growth `r_g = (g(4m+1))^{3/2}` (`secondConstP_le_gL`);
* the double kinetic division `(g(T+1))⁴ t_r(T; u) ≤ m̄² ‖w_g² u‖`
  (`sq_sq_mul_norm_high_le_phys`) and the observable `‖w_g² (O_g u)‖ ≤ 8 C_χ ‖w_g² u‖ +
  8 g⁴ D⁽⁴⁾_χ ‖u‖` (`norm_wPhys_sq_gridObs_le`);
* the second moments of grid trajectories, `flow2` at `g = 1` with the `L`-free constants
  `c_J = (4/3)(1 + 4A)`, `c_H = A` (`norm_wPhys_sq_gridFlow_le_gL`), and the shells of the backward
  flows of `O_g v` (`shell_gridFlow_gridObs_le_gLU`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics

open PlaneWaveGridG (gLgamma gLgamma_pos regParticlesOfG posNucleiOfG gLzU gLzU_nonneg gLAU sobP
  sobP_pos sobP_mul_cube J0P J0P_pos J0P_small gLGridCoupling)

namespace FreeBoundary

/-! ## Slices with the physical weight -/

section SlicePh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {rel : ι → ι → Prop} {tau : ι → ι → Lat3} {kappa : Lat3 → ℂ} {c : ℝ}

/-- The physical slice weight `1 + a² |X|²`. -/
def sliceWeightPh (a : ℝ) (X : ι → Lat3) (q : ι) : ℝ := 1 + a ^ 2 * nsq (X q)

lemma sliceWeightPh_pos (a : ℝ) (X : ι → Lat3) (q : ι) : 0 < sliceWeightPh a X q := by
  unfold sliceWeightPh
  have := nsq_nonneg (X q)
  positivity

lemma slice_weightPh_sum_le {a : ℝ} (ha : 0 < a) {σ : Type*} [DecidableEq σ] {S : ι → σ}
    {X : ι → Lat3} (h : SliceData rel S X) (p : ι) :
    ∑ p', (if S p' = S p then (sliceWeightPh a X p')⁻¹ ^ 2 else 0) ≤ sobP a := by
  classical
  rw [← Finset.sum_filter]
  set s := univ.filter fun p' => S p' = S p
  calc ∑ p' ∈ s, (sliceWeightPh a X p')⁻¹ ^ 2 = ∑ p' ∈ s, ((1 + a ^ 2 * nsq (X p'))⁻¹) ^ 2 := rfl
    _ ≤ ∑ nu ∈ s.image X, ((1 + a ^ 2 * nsq nu)⁻¹) ^ 2 := by
        refine sum_comp_le_of_injOn s X ?_ (fun nu => ((1 + a ^ 2 * nsq nu)⁻¹) ^ 2) _
          (fun q hq => mem_image_of_mem _ hq) (fun nu _ => sq_nonneg _)
        intro q hq q' hq' hX
        exact h.inj q q' ((mem_filter.mp hq).2.trans (mem_filter.mp hq').2.symm) hX
    _ ≤ sobP a := PlaneWaveGridG.sum_sobolevP_le ha _

/-- Slice-Young with the physical weight. -/
lemma kOp_sq_le_slicePh {a : ℝ} (ha : 0 < a) {σ : Type*} [DecidableEq σ] {S : ι → σ}
    {X : ι → Lat3} (h : SliceData rel S X) (kernel : ι → ι → ℂ)
    (hsupp : ∀ q p, kernel q p ≠ 0 → rel q p) {B : ℝ}
    (hcol : ∀ p, ∑ q, ‖kernel q p‖ ^ 2 ≤ B) (hvec : ι → ℝ) (hh : ∀ p, 0 ≤ hvec p) :
    ∑ q, (∑ p, ‖kernel q p‖ * hvec p) ^ 2 ≤
      B * sobP a * ∑ p, (sliceWeightPh a X p * hvec p) ^ 2 := by
  have hY := slice_young_sq S (fun q p => ‖kernel q p‖) hvec (fun _ _ => norm_nonneg _) hh
    (fun q p hk => h.compat q p (hsupp q p (fun h0 => hk (by simp [h0])))) hcol
  have hM := slice_mass_le S hvec (sliceWeightPh a X) hh (sliceWeightPh_pos a X)
    (slice_weightPh_sum_le ha h)
  calc ∑ q, (∑ p, ‖kernel q p‖ * hvec p) ^ 2 ≤ B * ∑ p, hvec p * sliceMass S hvec p := hY
    _ ≤ B * (sobP a * ∑ p, (sliceWeightPh a X p * hvec p) ^ 2) := by
        rcases isEmpty_or_nonempty ι with hι | hι
        · simp
        · have hB' : 0 ≤ B := (sum_nonneg fun q _ => sq_nonneg _).trans
            (hcol (Classical.arbitrary ι))
          exact mul_le_mul_of_nonneg_left hM hB'
    _ = B * sobP a * ∑ p, (sliceWeightPh a X p * hvec p) ^ 2 := by ring

lemma norm_kOp_high_lePh {a : ℝ} (ha : 0 < a) (hk : KernelBound kappa c) (hc : 0 ≤ c)
    (hcol : ColInj rel tau) {σ : Type*} [DecidableEq σ] {S : ι → σ} {X : ι → Lat3}
    (hS : SliceData rel S X) (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ ι) :
    ‖kOp (tk (highRel rel tau J) tau kappa) u‖ ≤
      c * Real.sqrt (26 * sobP a / J) * ‖wMul (sliceWeightPh a X) u‖ := by
  have hle : ∀ q p, highRel rel tau J q p → rel q p := fun _ _ h => h.1
  have hX : 0 ≤ c * Real.sqrt (26 * sobP a / J) * ‖wMul (sliceWeightPh a X) u‖ :=
    mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (norm_nonneg _)
  apply norm_kOp_le_of_sq _ u hX
  have h := kOp_sq_le_slicePh ha (hS.mono hle) (tk (highRel rel tau J) tau kappa)
    (fun q p h0 => rel_of_tk_ne_zero h0)
    (tk_col_l2 hk hc (hcol.mono hle) J hJ (fun _ _ h => h.2)) (fun p => ‖u p‖)
    (fun _ => norm_nonneg _)
  rw [← norm_wMul_sq _ (fun q => (sliceWeightPh_pos a X q).le)] at h
  refine h.trans (le_of_eq ?_)
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hS0 : 0 ≤ sobP a := (sobP_pos ha).le
  rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hS0) hJpos.le)]
  ring

/-- Operator bound for a transfer kernel with a slice structure, physical weight. -/
lemma norm_kOp_tk_lePh {a : ℝ} (ha : 0 < a) (hk : KernelBound kappa c) (hc : 0 ≤ c)
    (hrow : RowInj rel tau) (hcol : ColInj rel tau) {σ : Type*} [DecidableEq σ] {S : ι → σ}
    {X : ι → Lat3} (hS : SliceData rel S X) (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ ι) :
    ‖kOp (tk rel tau kappa) u‖ ≤
      c * (26 * J) * ‖u‖ + c * Real.sqrt (26 * sobP a / J) * ‖wMul (sliceWeightPh a X) u‖ := by
  rw [tk_eq_low_add_high rel tau kappa J, kOp_add, LinearMap.add_apply]
  exact (norm_add_le _ _).trans (add_le_add (norm_kOp_low_le hk hc hrow hcol J u)
    (norm_kOp_high_lePh ha hk hc hcol hS J hJ u))

/-- **Weighted transfer bound, physical slices.** For a transfer kernel with coefficients bounded
by `c coul`, supported in the box of radius `R`, on whose connected pairs `W q ≤ 2 W p + A |τ|²`:
`‖W (K u)‖ ≤ 2 (c 26J ‖W u‖ + c √(26 S/J) ‖σ_a (W u)‖) + A c √(S (2R+1)³) ‖σ_a u‖`,
`S = sobP a`. -/
lemma norm_wMul_kOp_tk_lePh {a : ℝ} (ha : 0 < a) (hk : KernelBound kappa c) (hc : 0 ≤ c)
    (hrow : RowInj rel tau) (hcol : ColInj rel tau) {σ : Type*} [DecidableEq σ] {S : ι → σ}
    {X : ι → Lat3} (hS : SliceData rel S X) {W : ι → ℝ} (hW0 : ∀ q, 0 ≤ W q) {A : ℝ}
    (hA : 0 ≤ A) (hWcomp : ∀ q p, rel q p → W q ≤ 2 * W p + A * nsq (tau q p))
    {R : ℕ} (hsupp : ∀ x, ¬ InBox R x → kappa x = 0) (J : ℕ) (hJ : 1 ≤ J)
    (u : EuclideanSpace ℂ ι) :
    ‖wMul W (kOp (tk rel tau kappa) u)‖ ≤
      2 * (c * (26 * J) * ‖wMul W u‖ + c * Real.sqrt (26 * sobP a / J) *
        ‖wMul (sliceWeightPh a X) (wMul W u)‖) +
        A * (c * Real.sqrt (sobP a * (2 * R + 1) ^ 3)) * ‖wMul (sliceWeightPh a X) u‖ := by
  classical
  set k1 : Lat3 → ℂ := fun x => ((‖kappa x‖ : ℝ) : ℂ) with hk1
  set k2 : Lat3 → ℂ := fun x => ((‖kappa x‖ * nsq x : ℝ) : ℂ) with hk2
  set Y1 := kOp (tk rel tau k1) (absVec (wMul W u)) with hY1
  set Y2 := kOp (tk rel tau k2) (absVec u) with hY2
  have hY1q : ∀ q, ‖Y1 q‖ = ∑ p, ‖tk rel tau kappa q p‖ * (W p * ‖u p‖) := by
    intro q
    have e : Y1 q = ((∑ p, ‖tk rel tau kappa q p‖ * (W p * ‖u p‖) : ℝ) : ℂ) := by
      rw [hY1, kOp_apply]
      push_cast
      refine sum_congr rfl fun p _ => ?_
      by_cases hr : rel q p
      · rw [tk_of_rel hr, tk_of_rel hr]
        simp only [absVec, wMul_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hW0 p),
          k1]
        push_cast
        ring
      · rw [tk_of_not_rel hr, tk_of_not_rel hr]
        simp
    rw [e, Complex.norm_real, Real.norm_of_nonneg]
    exact sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (mul_nonneg (hW0 p) (norm_nonneg _))
  have hY2q : ∀ q, ‖Y2 q‖ = ∑ p, ‖tk rel tau kappa q p‖ * nsq (tau q p) * ‖u p‖ := by
    intro q
    have e : Y2 q = ((∑ p, ‖tk rel tau kappa q p‖ * nsq (tau q p) * ‖u p‖ : ℝ) : ℂ) := by
      rw [hY2, kOp_apply]
      push_cast
      refine sum_congr rfl fun p _ => ?_
      by_cases hr : rel q p
      · rw [tk_of_rel hr, tk_of_rel hr]
        simp only [absVec, k2]
        push_cast
        ring
      · rw [tk_of_not_rel hr, tk_of_not_rel hr]
        simp
    rw [e, Complex.norm_real, Real.norm_of_nonneg]
    exact sum_nonneg fun p _ => mul_nonneg (mul_nonneg (norm_nonneg _) (nsq_nonneg _))
      (norm_nonneg _)
  have hpt : ∀ q, ‖(wMul W (kOp (tk rel tau kappa) u)) q‖ ≤ 2 * ‖Y1 q‖ + A * ‖Y2 q‖ := by
    intro q
    rw [hY1q, hY2q, wMul_apply, kOp_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hW0 q),
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hW0 q)).trans ?_
    rw [Finset.mul_sum]
    refine sum_le_sum fun p _ => ?_
    rw [norm_mul]
    by_cases hr : rel q p
    · have hw := hWcomp q p hr
      have h0 : 0 ≤ ‖tk rel tau kappa q p‖ * ‖u p‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc W q * (‖u p‖ * ‖tk rel tau kappa q p‖)
          = W q * (‖tk rel tau kappa q p‖ * ‖u p‖) := by ring
        _ ≤ (2 * W p + A * nsq (tau q p)) * (‖tk rel tau kappa q p‖ * ‖u p‖) :=
            mul_le_mul_of_nonneg_right hw h0
        _ = 2 * (‖tk rel tau kappa q p‖ * (W p * ‖u p‖)) +
            A * (‖tk rel tau kappa q p‖ * nsq (tau q p) * ‖u p‖) := by ring
    · rw [tk_of_not_rel hr, norm_zero]
      simp
  refine (norm_le_add2_of_pointwise (by norm_num) hA hpt).trans ?_
  have hk1b : KernelBound k1 c := fun x => by
    rw [hk1, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact hk x
  have h1 := norm_kOp_tk_lePh ha hk1b hc hrow hcol hS J hJ (absVec (wMul W u))
  rw [norm_absVec, norm_wMul_absVec _ (fun q => (sliceWeightPh_pos a X q).le)] at h1
  have hsupp2 : ∀ q p, tk rel tau k2 q p ≠ 0 → rel q p := fun q p h => rel_of_tk_ne_zero h
  have hcol2 : ∀ p, ∑ q, ‖tk rel tau k2 q p‖ ^ 2 ≤ c ^ 2 * (2 * R + 1) ^ 3 := by
    intro p
    rw [sum_col_eq rel tau k2 p (fun z => ‖z‖ ^ 2) (by simp)]
    set s := univ.filter fun q => rel q p
    have hterm : ∀ q ∈ s, ‖k2 (tau q p)‖ ^ 2 ≤
        (if InBox R (tau q p) then c ^ 2 else 0) := by
      intro q _
      by_cases hb : InBox R (tau q p)
      · rw [if_pos hb]
        simp only [hk2]
        rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (nsq_nonneg _))]
        have hkb := hk (tau q p)
        have hcn : coul (tau q p) * nsq (tau q p) ≤ 1 := by
          unfold coul
          by_cases h0 : nsq (tau q p) = 0
          · rw [h0]; norm_num
          · rw [one_div, inv_mul_cancel₀ h0]
        have h3 : ‖kappa (tau q p)‖ * nsq (tau q p) ≤ c := by
          calc ‖kappa (tau q p)‖ * nsq (tau q p) ≤ c * coul (tau q p) * nsq (tau q p) :=
                mul_le_mul_of_nonneg_right hkb (nsq_nonneg _)
            _ = c * (coul (tau q p) * nsq (tau q p)) := by ring
            _ ≤ c * 1 := mul_le_mul_of_nonneg_left hcn hc
            _ = c := mul_one c
        exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (nsq_nonneg _)) h3 2
      · rw [if_neg hb]
        simp [hk2, hsupp _ hb]
    calc ∑ q ∈ s, ‖k2 (tau q p)‖ ^ 2 ≤ ∑ q ∈ s, (if InBox R (tau q p) then c ^ 2 else 0) :=
          sum_le_sum hterm
      _ ≤ ∑ x ∈ PlaneWaveGrid.box R, c ^ 2 := by
          rw [← Finset.sum_filter]
          refine sum_comp_le_of_injOn _ (fun q => tau q p) ?_ (fun _ => c ^ 2)
            (PlaneWaveGrid.box R) ?_ (fun _ _ => sq_nonneg c)
          · intro q hq q' hq' h
            exact hcol q q' p (mem_filter.mp (mem_filter.mp hq).1).2
              (mem_filter.mp (mem_filter.mp hq').1).2 h
          · intro q hq
            exact mem_box.mpr (mem_filter.mp hq).2
      _ = c ^ 2 * (2 * R + 1) ^ 3 := by
          rw [sum_const, card_box, nsmul_eq_mul]
          push_cast
          ring
  have h2sq := kOp_sq_le_slicePh ha hS (tk rel tau k2) hsupp2 hcol2 (fun p => ‖u p‖)
    (fun _ => norm_nonneg _)
  have hS0 : 0 ≤ sobP a := (sobP_pos ha).le
  have hY2sq : ‖Y2‖ ^ 2 ≤
      (c * Real.sqrt (sobP a * (2 * R + 1) ^ 3) * ‖wMul (sliceWeightPh a X) u‖) ^ 2 := by
    rw [norm_sq_eq_sum]
    have e1 : ∑ q, ‖Y2 q‖ ^ 2 = ∑ q, (∑ p, ‖tk rel tau k2 q p‖ * ‖u p‖) ^ 2 := by
      refine sum_congr rfl fun q _ => ?_
      rw [hY2q]
      congr 1
      refine sum_congr rfl fun p _ => ?_
      by_cases hr : rel q p
      · rw [tk_of_rel hr, tk_of_rel hr]
        simp only [hk2]
        rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (nsq_nonneg _))]
      · rw [tk_of_not_rel hr, tk_of_not_rel hr]
        simp
    rw [e1]
    refine h2sq.trans (le_of_eq ?_)
    rw [← norm_wMul_sq _ (fun q => (sliceWeightPh_pos a X q).le) u, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity)]
    ring
  have hY2 : ‖Y2‖ ≤ c * Real.sqrt (sobP a * (2 * R + 1) ^ 3) * ‖wMul (sliceWeightPh a X) u‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hY2sq
  have := mul_le_mul_of_nonneg_left hY2 hA
  have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
  linarith

end SlicePh

/-! ## Physical weights on the register -/

section WeightsPh

variable {eta m : ℕ}

/-- The physical total weight `1 + a² Σ_b |n_b|²` (the `H²` weight of the lifted
configuration). -/
noncomputable def wTotPh (a : ℝ) (q : RCfg eta m) : ℝ := 1 + a ^ 2 * ∑ b, nsq (gl (q b))

lemma sum_nsq_gl_nonneg (q : RCfg eta m) : 0 ≤ ∑ b, nsq (gl (q b)) :=
  sum_nonneg fun _ _ => nsq_nonneg _

lemma wTotPh_ge_one (a : ℝ) (q : RCfg eta m) : 1 ≤ wTotPh a q := by
  unfold wTotPh
  have := sum_nsq_gl_nonneg q
  have := sq_nonneg a
  nlinarith

lemma wTotPh_eq_h2Weight (a : ℝ) (q : RCfg eta m) :
    wTotPh a q = molecularFourierH2Weight eta a (liftCfg q) := by
  rw [h2Weight_liftCfg]
  rfl

lemma sliceWeightPh_le_wTotPh (a : ℝ) (i : Fin eta) (q : RCfg eta m) :
    sliceWeightPh a (regCoord i) q ≤ wTotPh a q := by
  unfold sliceWeightPh regCoord wTotPh
  have h := Finset.single_le_sum (f := fun b => nsq (gl (q b)))
    (fun b _ => nsq_nonneg _) (Finset.mem_univ i)
  have := mul_le_mul_of_nonneg_left h (sq_nonneg a)
  linarith

lemma norm_wMul_slicePh_le (a : ℝ) (i : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (sliceWeightPh a (regCoord i)) u‖ ≤ ‖wMul (wTotPh a) u‖ :=
  norm_wMul_mono (fun q => (sliceWeightPh_pos _ _ q).le) (sliceWeightPh_le_wTotPh a i) u

variable (P : RegParticles eta)

lemma wPhys_nonneg (g : ℝ) (q : RCfg eta m) : 0 ≤ wPhys P g q :=
  le_trans zero_le_one (wPhys_ge_one P g q)

lemma wTotPh_le_maxMass_mul_wPhys (a : ℝ) (q : RCfg eta m) :
    wTotPh a q ≤ P.maxMass * wPhys P a q := by
  unfold wTotPh wPhys
  have hM := P.one_le_maxMass
  have h : ∀ b ∈ (univ : Finset (Fin eta)),
      nsq (gl (q b)) ≤ P.maxMass * (nsq (gl (q b)) / P.mass b) := by
    intro b _
    have hmb := P.mass_pos b
    rw [mul_div_assoc', le_div_iff₀ hmb]
    have := nsq_nonneg (gl (q b))
    nlinarith [P.mass_le_maxMass b]
  have hs := Finset.sum_le_sum h
  rw [← Finset.mul_sum] at hs
  have h2 := mul_le_mul_of_nonneg_left hs (sq_nonneg a)
  have h3 : 0 ≤ a ^ 2 * ∑ b, nsq (gl (q b)) / P.mass b :=
    mul_nonneg (sq_nonneg a) (sum_nonneg fun b _ => div_nonneg (nsq_nonneg _) (P.mass_pos b).le)
  linarith

lemma norm_wTotPh_le (a : ℝ) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wTotPh a) u‖ ≤ P.maxMass * ‖wMul (wPhys P a) u‖ := by
  have h1 := norm_wMul_mono (fun q => le_trans zero_le_one (wTotPh_ge_one a q))
    (wTotPh_le_maxMass_mul_wPhys P a) u
  have h2 : wMul (fun q => P.maxMass * wPhys P a q) u =
      ((P.maxMass : ℝ) : ℂ) • wMul (wPhys P a) u := by
    ext q
    simp only [wMul_apply, PiLp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [h2, norm_smul, Complex.norm_real, Real.norm_of_nonneg P.maxMass_pos.le] at h1
  exact h1

lemma wPhys_le_wTotPh (a : ℝ) (q : RCfg eta m) : wPhys P a q ≤ wTotPh a q := by
  unfold wPhys wTotPh
  have h : ∀ b ∈ (univ : Finset (Fin eta)), nsq (gl (q b)) / P.mass b ≤ nsq (gl (q b)) :=
    fun b _ => div_le_self (nsq_nonneg _) (P.one_le_mass b)
  have := mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (sq_nonneg a)
  linarith

/-- Across a one-register transfer: `w_g q ≤ 2 w_g p + 2 |gτ|²` (`g ≤ 1`). -/
lemma wPhys_le_of_spec1 {g : ℝ} (hg : g ^ 2 ≤ 1) {i : Fin eta} {q p : RCfg eta m}
    (h : Spec1 i q p) : wPhys P g q ≤ 2 * wPhys P g p + 2 * g ^ 2 * nsq (gTau i q p) := by
  have h1 := mul_le_mul_of_nonneg_left (wM_le_of_spec1 P h) (sq_nonneg g)
  rw [wPhys_eq_wM, wPhys_eq_wM]
  linarith

/-- Across a pair transfer: `w_g q ≤ 2 w_g p + 4 |gτ|²` (`g ≤ 1`). -/
lemma wPhys_le_of_gRel2 {g : ℝ} (hg : g ^ 2 ≤ 1) {i j : Fin eta} (hij : i ≠ j)
    {q p : RCfg eta m} (h : gRel2 i j q p) :
    wPhys P g q ≤ 2 * wPhys P g p + 4 * g ^ 2 * nsq (gTau i q p) := by
  have h1 := mul_le_mul_of_nonneg_left (wM_le_of_gRel2 P hij h) (sq_nonneg g)
  rw [wPhys_eq_wM, wPhys_eq_wM]
  linarith

/-- Across a cyclic translation of register `a`: `w_g q ≤ 2 w_g p + 2 |gν|²` (`g ≤ 1`). -/
lemma wPhys_le_cyc {g : ℝ} (hg : g ^ 2 ≤ 1) (a : Fin eta) (ν : Lat3) (q : RCfg eta m) :
    wPhys P g q ≤ 2 * wPhys P g (cfgShift a (ofLat ν) q) + 2 * g ^ 2 * nsq ν := by
  have h1 := mul_le_mul_of_nonneg_left (wM_le_cyc P a ν q) (sq_nonneg g)
  rw [wPhys_eq_wM, wPhys_eq_wM]
  linarith

lemma wPhys_ge_of_high (g : ℝ) {T : ℕ} {r : Fin eta} {q : RCfg eta m} (h : High T r q) :
    1 + g ^ 2 * ((T : ℝ) + 1) ^ 2 / P.maxMass ≤ wPhys P g q := by
  have h1 := wM_ge_of_high P h
  rw [wPhys_eq_wM]
  have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg g)
  have e : g ^ 2 * ((T : ℝ) + 1) ^ 2 / P.maxMass = g ^ 2 * (((T : ℝ) + 1) ^ 2 / P.maxMass) := by
    ring
  rw [e]
  linarith

/-- `(g(T+1))² t_r(T; u) ≤ m̄ ‖w_g u‖`. -/
lemma sq_mul_norm_high_le_phys {g : ℝ} (hg : 0 < g) (T : ℕ) (r : Fin eta)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    (g * ((T : ℝ) + 1)) ^ 2 * ‖maskOp (High T r) u‖ ≤ P.maxMass * ‖wMul (wPhys P g) u‖ := by
  have hM := P.maxMass_pos
  have hb : 0 < 1 + g ^ 2 * ((T : ℝ) + 1) ^ 2 / P.maxMass := by positivity
  have h := norm_maskOp_le_wMul (High T r) (wPhys P g) (wPhys_nonneg P g) hb
    (fun q hq => wPhys_ge_of_high P g hq) u
  have hX := norm_nonneg (wMul (wPhys P g) u)
  have hfac : (g * ((T : ℝ) + 1)) ^ 2 / (1 + g ^ 2 * ((T : ℝ) + 1) ^ 2 / P.maxMass) ≤
      P.maxMass := by
    rw [div_le_iff₀ hb]
    have e : P.maxMass * (1 + g ^ 2 * ((T : ℝ) + 1) ^ 2 / P.maxMass) =
        P.maxMass + g ^ 2 * ((T : ℝ) + 1) ^ 2 := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hM.ne']
    rw [e, mul_pow]
    linarith
  calc (g * ((T : ℝ) + 1)) ^ 2 * ‖maskOp (High T r) u‖
      ≤ (g * ((T : ℝ) + 1)) ^ 2 *
          (‖wMul (wPhys P g) u‖ / (1 + g ^ 2 * ((T : ℝ) + 1) ^ 2 / P.maxMass)) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = (g * ((T : ℝ) + 1)) ^ 2 / (1 + g ^ 2 * ((T : ℝ) + 1) ^ 2 / P.maxMass) *
          ‖wMul (wPhys P g) u‖ := by ring
    _ ≤ P.maxMass * ‖wMul (wPhys P g) u‖ := mul_le_mul_of_nonneg_right hfac hX

/-- **The double kinetic division, physical:** `(g(T+1))⁴ t_r(T; u) ≤ m̄² ‖w_g² u‖`. -/
lemma sq_sq_mul_norm_high_le_phys {g : ℝ} (hg : 0 < g) (T : ℕ) (r : Fin eta)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    (g * ((T : ℝ) + 1)) ^ 4 * ‖maskOp (High T r) u‖ ≤
      P.maxMass ^ 2 * ‖wMul (wPhys P g) (wMul (wPhys P g) u)‖ := by
  have hM := P.maxMass_pos
  have h1 := sq_mul_norm_high_le_phys P hg T r (maskOp (High T r) u)
  rw [maskOp_maskOp] at h1
  have h2 := sq_mul_norm_high_le_phys P hg T r (wMul (wPhys P g) u)
  rw [maskOp_wMul_comm] at h2
  have hT : (0 : ℝ) ≤ (g * ((T : ℝ) + 1)) ^ 2 := sq_nonneg _
  calc (g * ((T : ℝ) + 1)) ^ 4 * ‖maskOp (High T r) u‖
      = (g * ((T : ℝ) + 1)) ^ 2 * ((g * ((T : ℝ) + 1)) ^ 2 * ‖maskOp (High T r) u‖) := by ring
    _ ≤ (g * ((T : ℝ) + 1)) ^ 2 * (P.maxMass * ‖wMul (wPhys P g) (maskOp (High T r) u)‖) :=
        mul_le_mul_of_nonneg_left h1 hT
    _ = P.maxMass * ((g * ((T : ℝ) + 1)) ^ 2 * ‖wMul (wPhys P g) (maskOp (High T r) u)‖) := by
        ring
    _ ≤ P.maxMass * (P.maxMass * ‖wMul (wPhys P g) (wMul (wPhys P g) u)‖) :=
        mul_le_mul_of_nonneg_left h2 hM.le
    _ = P.maxMass ^ 2 * ‖wMul (wPhys P g) (wMul (wPhys P g) u)‖ := by ring

/-- One translation, second moment: `X_g(S_ν u) ≤ 8 X_g(u) + 8 |gν|⁴ ‖u‖`. -/
lemma norm_wPhys_sq_cycCLM_le {g : ℝ} (hg : g ^ 2 ≤ 1) (a : Fin eta) (ν : Lat3)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wPhys P g) (wMul (wPhys P g) (cycCLM a ν u))‖ ≤
      8 * ‖wMul (wPhys P g) (wMul (wPhys P g) u)‖ + 8 * (g ^ 2 * nsq ν) ^ 2 * ‖u‖ := by
  have hpt : ∀ q, ‖(wMul (wPhys P g) (wMul (wPhys P g) (cycCLM a ν u))) q‖ ≤
      8 * ‖(cycCLM a ν (wMul (wPhys P g) (wMul (wPhys P g) u))) q‖ +
        8 * (g ^ 2 * nsq ν) ^ 2 * ‖(cycCLM a ν u) q‖ := by
    intro q
    have hw := wPhys_le_cyc P hg a ν q
    have hW0 := wPhys_nonneg P g q
    have hWp := wPhys_nonneg P g (cfgShift a (ofLat ν) q)
    simp only [wMul_apply, cycCLM_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg hW0,
      Real.norm_of_nonneg hWp]
    have hsq : wPhys P g q ^ 2 ≤
        8 * wPhys P g (cfgShift a (ofLat ν) q) ^ 2 + 8 * (g ^ 2 * nsq ν) ^ 2 := by
      have hw' : wPhys P g q ≤ 2 * wPhys P g (cfgShift a (ofLat ν) q) + 2 * (g ^ 2 * nsq ν) := by
        linarith
      calc wPhys P g q ^ 2 ≤ (2 * wPhys P g (cfgShift a (ofLat ν) q) + 2 * (g ^ 2 * nsq ν)) ^ 2 :=
            pow_le_pow_left₀ hW0 hw' 2
        _ ≤ 8 * wPhys P g (cfgShift a (ofLat ν) q) ^ 2 + 8 * (g ^ 2 * nsq ν) ^ 2 := by
            nlinarith [sq_nonneg (wPhys P g (cfgShift a (ofLat ν) q) - g ^ 2 * nsq ν)]
    have hx := norm_nonneg (u (cfgShift a (ofLat ν) q))
    have e1 : wPhys P g q * (wPhys P g q * ‖u (cfgShift a (ofLat ν) q)‖) =
        wPhys P g q ^ 2 * ‖u (cfgShift a (ofLat ν) q)‖ := by ring
    have e2 : 8 * (wPhys P g (cfgShift a (ofLat ν) q) * (wPhys P g (cfgShift a (ofLat ν) q) *
        ‖u (cfgShift a (ofLat ν) q)‖)) + 8 * (g ^ 2 * nsq ν) ^ 2 * ‖u (cfgShift a (ofLat ν) q)‖ =
        (8 * wPhys P g (cfgShift a (ofLat ν) q) ^ 2 + 8 * (g ^ 2 * nsq ν) ^ 2) *
          ‖u (cfgShift a (ofLat ν) q)‖ := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right hsq hx
  refine (norm_le_add2_of_pointwise (by norm_num) (by positivity) hpt).trans (le_of_eq ?_)
  rw [norm_cycCLM_apply, norm_cycCLM_apply]

/-- **The collocated observable: second moment, physical weight**:
`X_g(O_g u) ≤ 8 C_χ X_g(u) + 8 g⁴ D⁽⁴⁾_χ ‖u‖`. -/
theorem norm_wPhys_sq_gridObs_le {g : ℝ} (hg : g ^ 2 ≤ 1) (a : Fin eta) {c : Lat3 → ℂ}
    (hc : Summable fun ν => ‖c ν‖) (hc4 : Summable fun ν => nsq ν ^ 2 * ‖c ν‖)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wPhys P g) (wMul (wPhys P g) (gridObs a c u))‖ ≤
      8 * (∑' ν, ‖c ν‖) * ‖wMul (wPhys P g) (wMul (wPhys P g) u)‖ +
        8 * (g ^ 4 * momFour c) * ‖u‖ := by
  set W := LinearMap.toContinuousLinearMap ((wMul (wPhys P g)).comp (wMul (wPhys P g)) :
    EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m))
  have hS : HasSum (fun ν => c ν • W (cycCLM a ν u)) (W (gridObs a c u)) := by
    have h := ((hasSum_gridObs (m := m) a hc).mapL (ContinuousLinearMap.apply ℂ _ u)).mapL W
    simpa only [ContinuousLinearMap.apply_apply, smul_apply, map_smul]
      using h
  set X := ‖wMul (wPhys P g) (wMul (wPhys P g) u)‖
  have hg4 : HasSum (fun ν => ‖c ν‖ * (8 * X) + 8 * g ^ 4 * (nsq ν ^ 2 * ‖c ν‖) * ‖u‖)
      ((∑' ν, ‖c ν‖) * (8 * X) + 8 * g ^ 4 * momFour c * ‖u‖) := by
    have h1 := hc.hasSum.mul_right (8 * X)
    have h2 := (hc4.hasSum.mul_left (8 * g ^ 4)).mul_right ‖u‖
    exact h1.add h2
  have hbound := hS.norm_le_of_bounded hg4 fun ν => by
    rw [norm_smul]
    have h1 : ‖W (cycCLM a ν u)‖ ≤ 8 * X + 8 * (g ^ 2 * nsq ν) ^ 2 * ‖u‖ :=
      norm_wPhys_sq_cycCLM_le P hg a ν u
    calc ‖c ν‖ * ‖W (cycCLM a ν u)‖ ≤ ‖c ν‖ * (8 * X + 8 * (g ^ 2 * nsq ν) ^ 2 * ‖u‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖c ν‖ * (8 * X) + 8 * g ^ 4 * (nsq ν ^ 2 * ‖c ν‖) * ‖u‖ := by ring
  show ‖W (gridObs a c u)‖ ≤ _
  have e : (∑' ν, ‖c ν‖) * (8 * X) = 8 * (∑' ν, ‖c ν‖) * X := by ring
  have e2 : 8 * g ^ 4 * momFour c * ‖u‖ = 8 * (g ^ 4 * momFour c) * ‖u‖ := by ring
  linarith

end WeightsPh

/-! ## The grid potential in the physical weight -/

section GridPh

variable {ν : Type*} [Fintype ν] {eta m : ℕ} (P : RegParticles eta) (D : NucData ν)
  {gamma : ℝ} {κ : Lat3 → ℝ} {g : ℝ}

/-- The physically weighted bound of one grid term. -/
lemma norm_wPhys_gridTerm_le (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0) (hg0 : 0 < g) (hg1 : g ^ 2 ≤ 1)
    (t : Term eta ν) (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wPhys P g) (kOp (gridTerm eta m D κ t) u)‖ ≤
      coupling eta D gamma t * (2 * (26 * J) * ‖wMul (wPhys P g) u‖ +
        2 * Real.sqrt (26 * sobP g / J) * ‖wMul (wTotPh g) (wMul (wPhys P g) u)‖ +
        4 * g ^ 2 * Real.sqrt (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) *
          ‖wMul (wTotPh g) u‖) := by
  have hc := coupling_nonneg (D := D) hg t
  have hW0 : ∀ q : RCfg eta m, 0 ≤ wPhys P g q := wPhys_nonneg P g
  have hA : (0 : ℝ) ≤ 4 * g ^ 2 := by positivity
  cases t with
  | inl pr =>
    have hsupp' : ∀ x, ¬ InBox (2 * m) x → kgr κ x = 0 := fun x hx => by
      simp [kgr, hsupp x hx]
    have h := norm_wMul_kOp_tk_lePh hg0 (kgr_bound hκ) hg (gRel2_rowInj pr.1.1 pr.1.2)
      (gRel2_colInj pr.1.1 pr.1.2) (gSlice2_data pr.1.1 pr.1.2) hW0 hA
      (fun q p h => wPhys_le_of_gRel2 P hg1 (ne_of_lt pr.2) h) hsupp' J hJ u
    have hs1 := norm_wMul_slicePh_le g pr.1.1 (wMul (wPhys P g) u)
    have hs2 := norm_wMul_slicePh_le g pr.1.1 u
    simp only [gridTerm, coupling]
    have e1 := mul_le_mul_of_nonneg_left hs1
      (mul_nonneg hg (Real.sqrt_nonneg (26 * sobP g / J)))
    have e2 := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hA
      (mul_nonneg hg (Real.sqrt_nonneg (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3))))
    linarith
  | inr il =>
    have hc' : 0 ≤ D.charge il.2 * gamma := mul_nonneg (D.charge_nonneg il.2) hg
    have hsupp' : ∀ x, ¬ InBox (2 * m) x → kgn D κ il.2 x = 0 := fun x hx => by
      simp [kgn, kgr, hsupp x hx]
    have h := norm_wMul_kOp_tk_lePh hg0 (kgn_bound D hκ il.2) hc' (spec1_rowInj_g il.1)
      (spec1_colInj_g il.1) (slice1_data il.1) hW0 hA
      (fun q p h => (wPhys_le_of_spec1 P hg1 h).trans (by
        have := mul_nonneg (sq_nonneg g) (nsq_nonneg (gTau il.1 q p))
        nlinarith))
      hsupp' J hJ u
    have hs1 := norm_wMul_slicePh_le g il.1 (wMul (wPhys P g) u)
    have hs2 := norm_wMul_slicePh_le g il.1 u
    simp only [gridTerm, coupling]
    have e1 := mul_le_mul_of_nonneg_left hs1
      (mul_nonneg hc' (Real.sqrt_nonneg (26 * sobP g / J)))
    have e2 := mul_le_mul_of_nonneg_left hs2 (mul_nonneg hA
      (mul_nonneg hc' (Real.sqrt_nonneg (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3))))
    linarith

/-- **Weighted Kato--Rellich bound of the grid potential, physical weight**:
`‖w_g (V u)‖ ≤ Z_c (52 J ‖w_g u‖ + 2 √(26 S/J) ‖wTot_g (w_g u)‖ + 4 g² √(S (4m+1)³) ‖wTot_g u‖)`
with `S = sobP g` and `wTot_g = 1 + g² Σ |n_b|²`. -/
theorem norm_wPhys_vGridK_le (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0) (hg0 : 0 < g) (hg1 : g ^ 2 ≤ 1) (J : ℕ)
    (hJ : 1 ≤ J) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wPhys P g) (kOp (vGridK eta m P D κ) u)‖ ≤
      Zc P D gamma * (2 * (26 * J) * ‖wMul (wPhys P g) u‖ +
        2 * Real.sqrt (26 * sobP g / J) * ‖wMul (wTotPh g) (wMul (wPhys P g) u)‖ +
        4 * g ^ 2 * Real.sqrt (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) *
          ‖wMul (wTotPh g) u‖) := by
  rw [kOp_vGridK_eq, map_sum]
  refine (norm_sum_le _ _).trans ?_
  unfold Zc
  rw [Finset.sum_mul]
  refine sum_le_sum fun t _ => ?_
  rw [LinearMap.map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (norm_wPhys_gridTerm_le P D hg hκ hsupp hg0 hg1 t J hJ u) (abs_nonneg _)

/-- The constant `C₂ = Z_c (52 J₀ + 4 m̄ g² √(S (4m+1)³))` of the physical second-order estimates,
`S = sobP g`, `J₀ = J0P (m̄ Z_c) g`. -/
noncomputable def secondConstP (P : RegParticles eta) (D : NucData ν) (gamma g : ℝ) (m : ℕ) : ℝ :=
  Zc P D gamma * (52 * (J0P (P.maxMass * Zc P D gamma) g : ℝ) +
    4 * g ^ 2 * Real.sqrt (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) * P.maxMass)

lemma secondConstP_nonneg (hg : 0 ≤ gamma) : 0 ≤ secondConstP P D gamma g m := by
  unfold secondConstP
  have := Zc_nonneg (P := P) (D := D) hg
  have := P.maxMass_pos
  positivity

/-- `‖w_g (V u)‖ ≤ (1/4) ‖w_g² u‖ + C₂ ‖w_g u‖`. -/
lemma norm_wPhys_vGridK_le_second (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0) (hg0 : 0 < g) (hg1 : g ^ 2 ≤ 1)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wPhys P g) (kOp (vGridK eta m P D κ) u)‖ ≤
      1 / 4 * ‖wMul (wPhys P g) (wMul (wPhys P g) u)‖ +
        secondConstP P D gamma g m * ‖wMul (wPhys P g) u‖ := by
  set J := J0P (P.maxMass * Zc P D gamma) g
  have hZ := Zc_nonneg (P := P) (D := D) hg
  have hM := P.maxMass_pos
  have h := norm_wPhys_vGridK_le P D hg hκ hsupp hg0 hg1 J (J0P_pos _ _) u
  have hsmall : (P.maxMass * Zc P D gamma) * Real.sqrt (26 * sobP g / J) ≤ 1 / 8 :=
    J0P_small (mul_nonneg hM.le hZ) hg0
  have h1 := norm_wTotPh_le P g (wMul (wPhys P g) u)
  have h2 := norm_wTotPh_le P g u
  set X := ‖wMul (wPhys P g) (wMul (wPhys P g) u)‖
  set Y := ‖wMul (wPhys P g) u‖
  have hX := norm_nonneg (wMul (wPhys P g) (wMul (wPhys P g) u))
  have hs0 := Real.sqrt_nonneg (26 * sobP g / (J : ℝ))
  have hs1 := Real.sqrt_nonneg (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3)
  have e1 : Zc P D gamma * (2 * Real.sqrt (26 * sobP g / J) *
      ‖wMul (wTotPh g) (wMul (wPhys P g) u)‖) ≤ 1 / 4 * X := by
    calc Zc P D gamma * (2 * Real.sqrt (26 * sobP g / J) *
          ‖wMul (wTotPh g) (wMul (wPhys P g) u)‖)
        ≤ Zc P D gamma * (2 * Real.sqrt (26 * sobP g / J) * (P.maxMass * X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) hZ
      _ = 2 * ((P.maxMass * Zc P D gamma) * Real.sqrt (26 * sobP g / J)) * X := by ring
      _ ≤ 2 * (1 / 8) * X := by
          apply mul_le_mul_of_nonneg_right _ hX
          linarith
      _ = 1 / 4 * X := by ring
  have e2 : Zc P D gamma * (4 * g ^ 2 * Real.sqrt (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) *
      ‖wMul (wTotPh g) u‖) ≤ Zc P D gamma * (4 * g ^ 2 *
        Real.sqrt (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) * (P.maxMass * Y)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) hZ
  have e3 : secondConstP P D gamma g m * Y = Zc P D gamma * (2 * (26 * (J : ℝ)) * Y) +
      Zc P D gamma * (4 * g ^ 2 * Real.sqrt (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) *
        (P.maxMass * Y)) := by
    simp only [secondConstP, J]
    ring
  have e4 : Zc P D gamma * (2 * (26 * (J : ℝ)) * Y + 2 * Real.sqrt (26 * sobP g / J) *
      ‖wMul (wTotPh g) (wMul (wPhys P g) u)‖ +
        4 * g ^ 2 * Real.sqrt (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) *
          ‖wMul (wTotPh g) u‖) = Zc P D gamma * (2 * (26 * (J : ℝ)) * Y) +
      Zc P D gamma * (2 * Real.sqrt (26 * sobP g / J) * ‖wMul (wTotPh g) (wMul (wPhys P g) u)‖) +
      Zc P D gamma * (4 * g ^ 2 * Real.sqrt (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) *
        ‖wMul (wTotPh g) u‖) := by
    ring
  linarith

/-- The kinetic symbol in the physical weight: `kin = (w_g - 1)/2`. -/
lemma kinT_eq_wPhys (q : RCfg eta m) : kinT eta m P g q = (wPhys P g q - 1) / 2 := by
  unfold kinT
  rw [wPhys_eq_wM]
  ring

/-- `w_g² u = w_g u + 2 (w_g (H u) - w_g (V u))`. -/
lemma wPhys_wPhys_eq (u : EuclideanSpace ℂ (RCfg eta m)) :
    wMul (wPhys P g) (wMul (wPhys P g) u) = wMul (wPhys P g) u +
      (2 : ℂ) • (wMul (wPhys P g) (Hgrid eta m P D κ g u) -
        wMul (wPhys P g) (kOp (vGridK eta m P D κ) u)) := by
  ext q
  simp only [wMul_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, Hgrid,
    LinearMap.add_apply]
  rw [kinT_eq_wPhys]
  push_cast
  ring

/-- **Second-order elliptic estimate, physical weight**:
`‖w_g² u‖ ≤ 2 ‖w_g u‖ + 4 ‖w_g (H u)‖ + 4 C₂ ‖w_g u‖`. -/
theorem second_ellipticP (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0) (hg0 : 0 < g) (hg1 : g ^ 2 ≤ 1)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wPhys P g) (wMul (wPhys P g) u)‖ ≤ 2 * ‖wMul (wPhys P g) u‖ +
      4 * ‖wMul (wPhys P g) (Hgrid eta m P D κ g u)‖ +
      4 * secondConstP P D gamma g m * ‖wMul (wPhys P g) u‖ := by
  have hV := norm_wPhys_vGridK_le_second P D hg hκ hsupp hg0 hg1 u
  have h := congrArg norm (wPhys_wPhys_eq P D (κ := κ) (g := g) u)
  have h1 : ‖wMul (wPhys P g) (wMul (wPhys P g) u)‖ ≤ ‖wMul (wPhys P g) u‖ +
      2 * (‖wMul (wPhys P g) (Hgrid eta m P D κ g u)‖ +
        ‖wMul (wPhys P g) (kOp (vGridK eta m P D κ) u)‖) := by
    rw [h]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul]
    have e : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
  linarith

/-- `‖w_g (H w)‖ ≤ (3/4) ‖w_g² w‖ + C₂ ‖w_g w‖`. -/
theorem norm_wPhys_Hgrid_leP (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0) (hg0 : 0 < g) (hg1 : g ^ 2 ≤ 1)
    (w : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wPhys P g) (Hgrid eta m P D κ g w)‖ ≤
      3 / 4 * ‖wMul (wPhys P g) (wMul (wPhys P g) w)‖ +
        secondConstP P D gamma g m * ‖wMul (wPhys P g) w‖ := by
  have hV := norm_wPhys_vGridK_le_second P D hg hκ hsupp hg0 hg1 w
  have hT : ‖wMul (wPhys P g) (wMul (kinT eta m P g) w)‖ ≤
      1 / 2 * ‖wMul (wPhys P g) (wMul (wPhys P g) w)‖ := by
    have hpt : ∀ q, ‖(wMul (wPhys P g) (wMul (kinT eta m P g) w)) q‖ ≤
        ‖((((1 / 2 : ℝ) : ℂ)) • wMul (wPhys P g) (wMul (wPhys P g) w)) q‖ := by
      intro q
      have hW0 := wPhys_nonneg P g q
      have hW1 := wPhys_ge_one P g q
      have hk0 : 0 ≤ kinT eta m P g q := by
        rw [kinT_eq_wPhys]
        linarith
      simp only [wMul_apply, PiLp.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hW0, Real.norm_of_nonneg hk0,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have hk : kinT eta m P g q ≤ 1 / 2 * wPhys P g q := by
        rw [kinT_eq_wPhys]
        linarith
      have hx := norm_nonneg (w q)
      nlinarith [mul_le_mul_of_nonneg_left hk (mul_nonneg hW0 hx)]
    refine (norm_le_of_pointwise hpt).trans (le_of_eq ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  have hsplit : wMul (wPhys P g) (Hgrid eta m P D κ g w) =
      wMul (wPhys P g) (wMul (kinT eta m P g) w) +
        wMul (wPhys P g) (kOp (vGridK eta m P D κ) w) := by
    rw [Hgrid, LinearMap.add_apply, map_add]
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  linarith

end GridPh

/-! ## The `g_L` coupling: the growth constant -/

section GrowthGL

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- The `L`-free growth constant `σ_U = 2A + 4√79 z` of the physical second-order estimates. -/
noncomputable def sigmaU (sys : CoulombSystem eta ν) (V : ℝ) : ℝ :=
  2 * gLAU sys V + 4 * Real.sqrt 79 * gLzU sys V

/-- The physical growth `r_g = (g(4m+1))^{3/2}`. -/
noncomputable def rPhys (g : ℝ) (m : ℕ) : ℝ := Real.sqrt (g * (((4 * m : ℕ) : ℝ) + 1)) ^ 3

lemma one_le_rPhys {g : ℝ} {m : ℕ} (h : 1 ≤ g * (((4 * m : ℕ) : ℝ) + 1)) : 1 ≤ rPhys g m := by
  unfold rPhys
  have h1 : 1 ≤ Real.sqrt (g * (((4 * m : ℕ) : ℝ) + 1)) :=
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (g * (((4 * m : ℕ) : ℝ) + 1)) := Real.sqrt_le_sqrt h
  exact one_le_pow₀ h1

lemma sigmaU_nonneg (sys : CoulombSystem eta ν) {V : ℝ} (hV : 0 ≤ V) : 0 ≤ sigmaU sys V := by
  unfold sigmaU gLAU
  have := gLzU_nonneg sys hV
  positivity

/-- `g³ √(S (4m+1)³) ≤ √79 (g(4m+1))^{3/2}` for `0 < g ≤ 1`, `S = sobP g`. -/
lemma cube_sqrt_sobP_le {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (N : ℝ) (hN : 0 ≤ N) :
    g ^ 3 * Real.sqrt (sobP g * N ^ 3) ≤ Real.sqrt 79 * Real.sqrt (g * N) ^ 3 := by
  have hS := sobP_mul_cube hg
  have hg3 : g ^ 3 ≤ 1 := pow_le_one₀ hg.le hg1
  have hS0 := (sobP_pos hg).le
  have e1 : g ^ 3 * Real.sqrt (sobP g * N ^ 3) = Real.sqrt ((g ^ 3) ^ 2 * (sobP g * N ^ 3)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have e2 : Real.sqrt 79 * Real.sqrt (g * N) ^ 3 = Real.sqrt (79 * (g * N) ^ 3) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 79) ((g * N) ^ 3),
      sqrt_pow_three (by positivity : (0 : ℝ) ≤ g * N)]
  rw [e1, e2]
  apply Real.sqrt_le_sqrt
  have e3 : (g ^ 3) ^ 2 * (sobP g * N ^ 3) = (sobP g * g ^ 3) * (g ^ 3 * N ^ 3) := by ring
  have e4 : 79 * (g * N) ^ 3 = 79 * (g ^ 3 * N ^ 3) := by ring
  rw [e3, e4, hS]
  have hgN : 0 ≤ g ^ 3 * N ^ 3 := by positivity
  nlinarith

/-- **The physical second-order constant is `O(r_g)` uniformly in `L ≥ 2π`**:
`C₂ ≤ σ_U r_g`, `σ_U = 2A + 4√79 z`, when `g(4m+1) ≥ 1`. -/
theorem secondConstP_le_gL (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) {V : ℝ}
    (hV : 0 ≤ V) (m : ℕ) (hm : 1 ≤ (2 * Real.pi / L) * (((4 * m : ℕ) : ℝ) + 1)) :
    secondConstP (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (gLgamma L V)
      (2 * Real.pi / L) m ≤ sigmaU sys V * rPhys (2 * Real.pi / L) m := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  set g := 2 * Real.pi / L with hgdef
  have hg : 0 < g := by positivity
  have hg1 : g ≤ 1 := PlaneWaveGridG.g_le_one hL
  set Zg := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (gLgamma L V) with hZgdef
  have hZg : 0 ≤ Zg := Zc_nonneg (gLgamma_pos hL0 hV).le
  have hM := sys.one_le_maxMass
  have hz0 := gLzU_nonneg sys hV
  have hcoup : sys.maxMass * Zg = gLGridCoupling sys L V := rfl
  have hZz : sys.maxMass * Zg = gLzU sys V * g := by
    rw [hcoup, PlaneWaveGridG.gLGridCoupling_eq sys hL0 V]
  have hA := gLGridA_le_U sys hL hV
  rw [← hcoup] at hA
  have hr := one_le_rPhys hm
  have hA0 : 0 ≤ gLAU sys V := by unfold gLAU; positivity
  -- the low-transfer part: `Z_c 52 J₀ ≤ 2A`
  have hJ : Zg * (52 * (J0P (sys.maxMass * Zg) g : ℝ)) ≤ 2 * gLAU sys V := by
    have hJ0 : (0 : ℝ) ≤ (J0P (sys.maxMass * Zg) g : ℝ) := Nat.cast_nonneg _
    have h1 : Zg * (52 * (J0P (sys.maxMass * Zg) g : ℝ)) ≤
        sys.maxMass * Zg * (52 * (J0P (sys.maxMass * Zg) g : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hM (mul_nonneg hZg (by positivity :
        (0 : ℝ) ≤ 52 * (J0P (sys.maxMass * Zg) g : ℝ)))
      linarith
    have e : sys.maxMass * Zg * (52 * (J0P (sys.maxMass * Zg) g : ℝ)) =
        2 * (26 * (sys.maxMass * Zg) * (J0P (sys.maxMass * Zg) g : ℝ)) := by ring
    linarith
  -- the growth part: `4 g² √(S (4m+1)³) m̄ Z_c ≤ 4 √79 z r_g`
  have hN : 2 * ((2 * m : ℕ) : ℝ) + 1 = ((4 * m : ℕ) : ℝ) + 1 := by push_cast; ring
  have hcube := cube_sqrt_sobP_le hg hg1 (((4 * m : ℕ) : ℝ) + 1) (by positivity)
  have hG : Zg * (4 * g ^ 2 * Real.sqrt (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) *
      sys.maxMass) ≤ 4 * Real.sqrt 79 * gLzU sys V * rPhys g m := by
    rw [hN]
    have e : Zg * (4 * g ^ 2 * Real.sqrt (sobP g * (((4 * m : ℕ) : ℝ) + 1) ^ 3) * sys.maxMass) =
        4 * gLzU sys V * (g ^ 3 * Real.sqrt (sobP g * (((4 * m : ℕ) : ℝ) + 1) ^ 3)) := by
      have : Zg * sys.maxMass = gLzU sys V * g := by rw [mul_comm]; exact hZz
      calc Zg * (4 * g ^ 2 * Real.sqrt (sobP g * (((4 * m : ℕ) : ℝ) + 1) ^ 3) * sys.maxMass)
          = 4 * g ^ 2 * Real.sqrt (sobP g * (((4 * m : ℕ) : ℝ) + 1) ^ 3) *
              (Zg * sys.maxMass) := by ring
        _ = 4 * g ^ 2 * Real.sqrt (sobP g * (((4 * m : ℕ) : ℝ) + 1) ^ 3) * (gLzU sys V * g) := by
            rw [this]
        _ = _ := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hcube (by positivity : (0 : ℝ) ≤ 4 * gLzU sys V)
    unfold rPhys
    linarith
  unfold secondConstP
  show Zg * (52 * (J0P ((regParticlesOf sys).maxMass * Zg) g : ℝ) +
    4 * g ^ 2 * Real.sqrt (sobP g * (2 * ((2 * m : ℕ) : ℝ) + 1) ^ 3) *
      (regParticlesOf sys).maxMass) ≤ _
  have e2 : (regParticlesOf sys).maxMass = sys.maxMass := rfl
  rw [e2, mul_add]
  have hsig : sigmaU sys V * rPhys g m = 2 * gLAU sys V * rPhys g m +
      4 * Real.sqrt 79 * gLzU sys V * rPhys g m := by unfold sigmaU; ring
  rw [hsig]
  have h2A : 2 * gLAU sys V ≤ 2 * gLAU sys V * rPhys g m :=
    le_mul_of_one_le_right (by positivity) hr
  linarith

end GrowthGL

/-! ## Second moments of grid trajectories, `g_L`, physical weight -/

section FlowGL

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **Second moment of a grid trajectory, physical weight, uniform in `L`** (`L ≥ 2π`): for a
unitary `V` that commutes with the grid Hamiltonian,
`X_g(V w) ≤ flow2(1; c_J, A, C₂; X_g(w), ‖w_g w‖, ‖w‖)` with the `L`-free `c_J = (4/3)(1 + 4A)`. -/
theorem norm_wPhys_sq_gridFlow_le_gL (sys : CoulombSystem eta ν) {L V : ℝ}
    (hL : 2 * Real.pi ≤ L) (hV : 0 ≤ V) {m : ℕ} {κ : Lat3 → ℝ}
    (hκb : ∀ x, |κ x| ≤ gLgamma L V * coul x) (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0)
    (U : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hcomm : ∀ x, U (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (U x))
    (w : EuclideanSpace ℂ (RCfg eta m)) {X Y S : ℝ}
    (hX : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L))
      (wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) w)‖ ≤ X)
    (hY : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) w‖ ≤ Y) (hS : ‖w‖ ≤ S) :
    ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L))
        (wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (U w))‖ ≤
      flow2 1 (gridFlowConstU sys V) (gLAU sys V)
        (secondConstP (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (gLgamma L V)
          (2 * Real.pi / L) m) X Y S := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hγ : 0 ≤ gLgamma L V := (gLgamma_pos hL0 hV).le
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hg1 : (2 * Real.pi / L) ^ 2 ≤ 1 := pow_le_one₀ hg.le (PlaneWaveGridG.g_le_one hL)
  have hsc : 0 ≤ secondConstP (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (gLgamma L V) (2 * Real.pi / L) m := secondConstP_nonneg _ _ hγ
  have hcJ := gridFlowConstU_nonneg sys hV
  have hA0 : 0 ≤ gLAU sys V := by
    unfold gLAU
    have := gLzU_nonneg sys hV
    positivity
  have h1 := second_ellipticP (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData hγ hκb
    hsupp hg hg1 (U w)
  have h2 : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (U w)‖ ≤
      5 / 3 * Y + gridFlowConstU sys V * S := by
    have h := norm_wPhys_gridFlow_le_gL sys hL hV hκb U hcomm w
    have h3 := mul_le_mul_of_nonneg_left hY (by norm_num : (0 : ℝ) ≤ 5 / 3)
    have h4 := mul_le_mul_of_nonneg_left hS hcJ
    linarith
  have h4 : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (Hgrid eta m (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) (U w))‖ ≤
      5 / 3 * ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (Hgrid eta m
        (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) w)‖ +
      gridFlowConstU sys V * ‖Hgrid eta m (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) w‖ := by
    rw [← hcomm]
    exact norm_wPhys_gridFlow_le_gL sys hL hV hκb U hcomm _
  have h5 : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (Hgrid eta m (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) w)‖ ≤
      3 * 1 ^ 2 / 4 * X + secondConstP (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (gLgamma L V) (2 * Real.pi / L) m * Y := by
    have h := norm_wPhys_Hgrid_leP (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData hγ hκb
      hsupp hg hg1 w
    have h6 := mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 3 / 4)
    have h7 := mul_le_mul_of_nonneg_left hY hsc
    norm_num
    linarith
  have h8 : ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) w‖ ≤ 5 * 1 ^ 2 / 8 * Y + gLAU sys V * S := by
    have h := (gridGraphNorm_gL sys hL hV hκb w).1
    have h6 := mul_le_mul_of_nonneg_left hY (by norm_num : (0 : ℝ) ≤ 5 / 8)
    have h7 := mul_le_mul_of_nonneg_left hS hA0
    norm_num
    linarith
  have h1' : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L))
      (wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (U w))‖ ≤
      2 * ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (U w)‖ +
        4 / 1 ^ 2 * ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L))
          (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
            (2 * Real.pi / L) (U w))‖ +
        4 / 1 ^ 2 * secondConstP (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
          (gLgamma L V) (2 * Real.pi / L) m *
          ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (U w)‖ := by
    norm_num
    linarith
  exact flow2_of_bounds one_pos hsc hcJ h1' h2 h4 h5 h8

/-- **The shells of the backward flows, physical weight** (`thm:grid-dyn-sharp`): if
`X_g(v) ≤ r F`, `‖w_g v‖ ≤ X_b` and `‖v‖ ≤ S₀`, then for every time `τ` and register `r'`,
`(g(⌊m/4⌋+1))⁴ ‖1_{|q_{r'}|∞ > ⌊m/4⌋} U_g(τ) O_g v‖ ≤ m̄² r Φ` with
`Φ = flow2(1; c_J, A, σ; 8 C_χ F + 8 g⁴ D⁽⁴⁾_χ S₀, W_o, C_χ S₀)`,
`W_o = (2 + 12 m̄) C_χ X_b + ((3 + 12 m̄) C_χ + 14 g² D'_χ) S₀`, whenever `C₂ ≤ σ r`, `r ≥ 1`. -/
theorem shell_gridFlow_gridObs_le_gLU (sys : CoulombSystem eta ν) {L V : ℝ}
    (hL : 2 * Real.pi ≤ L) (hV : 0 ≤ V) {m : ℕ} {κ : Lat3 → ℝ}
    (hκb : ∀ x, |κ x| ≤ gLgamma L V * coul x) (hsupp : ∀ x, ¬ InBox (2 * m) x → κ x = 0)
    (Vt : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hcomm : ∀ τ x, Vt τ (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Vt τ x))
    (a : Fin eta) {χ : Lat3 → ℂ} (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (hχ4 : Summable fun ν => nsq ν ^ 2 * ‖χ ν‖)
    (v : EuclideanSpace ℂ (RCfg eta m)) {F Xb S0 r σ : ℝ} (hr : 1 ≤ r)
    (hX : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L))
      (wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) v)‖ ≤ r * F)
    (hY : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) v‖ ≤ Xb) (hS : ‖v‖ ≤ S0)
    (hXb : 0 ≤ Xb) (hS0 : 0 ≤ S0)
    (hsc : secondConstP (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (gLgamma L V)
      (2 * Real.pi / L) m ≤ σ * r) (τ : ℝ) (r' : Fin eta) :
    ((2 * Real.pi / L) * (((m / 4 : ℕ) : ℝ) + 1)) ^ 4 *
        ‖maskOp (High (m / 4) r') (Vt τ (gridObs a χ v))‖ ≤
      sys.maxMass ^ 2 * (r * flow2 1 (gridFlowConstU sys V) (gLAU sys V) σ
        (8 * (∑' ν, ‖χ ν‖) * F + 8 * ((2 * Real.pi / L) ^ 4 * momFour χ) * S0)
        ((2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * Xb +
          ((3 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) +
            14 * ((2 * Real.pi / L) ^ 2 * momTwo χ)) * S0)
        ((∑' ν, ‖χ ν‖) * S0)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hg1 : (2 * Real.pi / L) ^ 2 ≤ 1 := pow_le_one₀ hg.le (PlaneWaveGridG.g_le_one hL)
  have hM := sys.one_le_maxMass
  have hCχ : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hD2 : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hD4 := momFour_nonneg χ
  have hcJ := gridFlowConstU_nonneg sys hV
  have hA0 : 0 ≤ gLAU sys V := by
    unfold gLAU
    have := gLzU_nonneg sys hV
    positivity
  have hXo : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L))
      (wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (gridObs a χ v))‖ ≤
      (8 * (∑' ν, ‖χ ν‖) * F + 8 * ((2 * Real.pi / L) ^ 4 * momFour χ) * S0) * r := by
    have h := norm_wPhys_sq_gridObs_le (regParticlesOf sys) hg1 a hχ1 hχ4 v
    have h1 := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 8 * (∑' ν, ‖χ ν‖))
    have h2 := mul_le_mul_of_nonneg_left hS
      (by positivity : (0 : ℝ) ≤ 8 * ((2 * Real.pi / L) ^ 4 * momFour χ))
    have h3 : 8 * ((2 * Real.pi / L) ^ 4 * momFour χ) * S0 ≤
        8 * ((2 * Real.pi / L) ^ 4 * momFour χ) * S0 * r :=
      le_mul_of_one_le_right (by positivity) hr
    have e : (8 * (∑' ν, ‖χ ν‖) * F + 8 * ((2 * Real.pi / L) ^ 4 * momFour χ) * S0) * r =
        8 * (∑' ν, ‖χ ν‖) * (r * F) + 8 * ((2 * Real.pi / L) ^ 4 * momFour χ) * S0 * r := by ring
    rw [e]
    linarith
  have hWo : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (gridObs a χ v)‖ ≤
      (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * Xb +
        ((3 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) +
          14 * ((2 * Real.pi / L) ^ 2 * momTwo χ)) * S0 := by
    have h := norm_wPhys_gridObs_le (regParticlesOf sys) hg1 a hχ1 hχ2 v
    have hc1 : 0 ≤ (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) := mul_nonneg (by linarith) hCχ
    have hc2 : 0 ≤ (3 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) +
        14 * ((2 * Real.pi / L) ^ 2 * momTwo χ) :=
      add_nonneg (mul_nonneg (by linarith) hCχ) (by positivity)
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hY hc1)
      (mul_le_mul_of_nonneg_left hS hc2))
  have hSo : ‖gridObs a χ v‖ ≤ (∑' ν, ‖χ ν‖) * S0 :=
    (((gridObs a χ).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_gridObs_le a hχ1) (norm_nonneg v))).trans
      (mul_le_mul_of_nonneg_left hS hCχ)
  have hflow := norm_wPhys_sq_gridFlow_le_gL sys hL hV hκb hsupp (Vt τ) (hcomm τ) _ hXo hWo hSo
  have hWo0 : 0 ≤ (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * Xb +
      ((3 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) + 14 * ((2 * Real.pi / L) ^ 2 * momTwo χ)) * S0 :=
    add_nonneg (mul_nonneg (mul_nonneg (by linarith) hCχ) hXb)
      (mul_nonneg (add_nonneg (mul_nonneg (by linarith) hCχ) (by positivity)) hS0)
  have hhom := flow2_le_mul (g := 1)
    (x := 8 * (∑' ν, ‖χ ν‖) * F + 8 * ((2 * Real.pi / L) ^ 4 * momFour χ) * S0) hcJ hA0 hWo0
    (mul_nonneg hCχ hS0) hr hsc le_rfl
  have hsh := sq_sq_mul_norm_high_le_phys (regParticlesOf sys) hg (m / 4) r' (Vt τ (gridObs a χ v))
  exact hsh.trans (mul_le_mul_of_nonneg_left (hflow.trans hhom) (sq_nonneg _))

end FlowGL

end FreeBoundary
