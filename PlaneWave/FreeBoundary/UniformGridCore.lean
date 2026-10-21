import PlaneWave.FreeBoundary.Scaling
import PlaneWave.FreeBoundary.GridCoreGeneral

/-!
# `app:free`, `L`-uniform constants, part 1: the grid core in physical units

The grid core of `PlaneWave.FreeBoundary.GridCoreGeneral` measures the `H²` regularity of eigenvectors with the lattice weight
`1 + Σ_a |ν_a|²`. In these units the Coulomb coupling of the `g_L` system is `Z/g² ~ L`
(`g = 2π/L`), so its constants grow polynomially in `L`. Here the same comparison is proved with
the physical weight `1 + g² Σ_a |ν_a|²` (that is `1 + Σ_a |k_a|²`), the one-particle Sobolev sum
`Σ_ν (1 + g²|ν|²)⁻² ≤ 1 + 78/g³` (`sum_sobolevP_le`) and a coupling `Z ≤ z g`. The kernel bounds
(`|κ| ≤ γ/|ν|²` and the lattice sums `26 J`, `26/J`) are those of `PlaneWave.FreeBoundary.GridCoreGeneral`. All constants are
functions of the physical coupling `z`, of `σ ≥ g³ + 78` and of an energy budget; for the `g_L`
system `z` does not depend on `L`, and `σ = g₀³ + 78` serves for all `L ≥ 2π/g₀`.

The Hamiltonians, the kernels, the sector machinery and the abstract spectral steps are reused
from `PlaneWave.FreeBoundary.GridCoreGeneral` (namespace `PlaneWaveGridG`); the new declarations carry the suffix `P` (physical
weights) or `U` (constants that are uniform in `L`).

Main result:
* `grid_galerkin_energyP`: for `2 ≤ s ≤ m ≤ 8s`, a kernel of the class at threshold `s`,
  `m̄ Z_c ≤ z g`, `g³ + 78 ≤ σ`, `43264 σ z³ + 52 z g ≤ A`, `|E_gal| ≤ E_b` and
  `4 m̄ E_big ≤ K²` (`K = g s`), the grid and Galerkin sector energies satisfy
  `|E_grid - E_gal| ≤ C_grid / K³`, with `E_big = EbigU m̄ z σ A E_b` and
  `C_grid = CgridU m̄ z σ A E_b` independent of `g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace PlaneWaveGridG

/-! ## The one-particle Sobolev sum with the physical weight -/

section SobolevP

/-- The physical Sobolev constant `1 + 78/a³`. -/
noncomputable def sobP (a : ℝ) : ℝ := 1 + 78 / a ^ 3

lemma sobP_pos {a : ℝ} (ha : 0 < a) : 0 < sobP a := by
  unfold sobP; positivity

lemma sobP_mul_cube {a : ℝ} (ha : 0 < a) : sobP a * a ^ 3 = a ^ 3 + 78 := by
  unfold sobP
  have : a ^ 3 ≠ 0 := by positivity
  field_simp

/-- A box is the origin and its shells. -/
lemma sum_box_eq_shells (f : Lat3 → ℝ) : ∀ R : ℕ,
    ∑ nu ∈ box R, f nu = f 0 + ∑ J ∈ range R, ∑ nu ∈ shell J, f nu
  | 0 => by
      have hb : box 0 = {0} := by
        ext nu
        simp [mem_box, inBox_zero_iff]
      rw [hb, sum_singleton, range_zero, sum_empty, add_zero]
  | R + 1 => by
      rw [sum_box_succ, sum_box_eq_shells f R, sum_range_succ]
      ring

lemma sobolevP_le_of_not_inBox (a : ℝ) {J : ℕ} {nu : Lat3} (h : ¬ InBox J nu) :
    ((1 + a ^ 2 * nsq nu)⁻¹) ^ 2 ≤ ((1 + a ^ 2 * ((J : ℝ) + 1) ^ 2)⁻¹) ^ 2 := by
  have h1 := nsq_ge_of_not_inBox h
  have hpos : 0 < 1 + a ^ 2 * ((J : ℝ) + 1) ^ 2 := by positivity
  have h2 : 1 + a ^ 2 * ((J : ℝ) + 1) ^ 2 ≤ 1 + a ^ 2 * nsq nu := by
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
    linarith
  have h3 : (1 + a ^ 2 * nsq nu)⁻¹ ≤ (1 + a ^ 2 * ((J : ℝ) + 1) ^ 2)⁻¹ := inv_anti₀ hpos h2
  have h4 : 0 ≤ (1 + a ^ 2 * nsq nu)⁻¹ := by
    have := nsq_nonneg nu
    positivity
  exact pow_le_pow_left₀ h4 h3 2

/-- One shell: a head part (`|ν| ≤ 1/a`) and a tail part. -/
lemma shell_termP {a : ℝ} (ha : 0 < a) (J : ℕ) :
    26 * ((J : ℝ) + 1) ^ 2 * ((1 + a ^ 2 * ((J : ℝ) + 1) ^ 2)⁻¹) ^ 2 ≤
      26 * (if (J : ℝ) + 1 ≤ 1 / a then ((J : ℝ) + 1) ^ 2 else 0) +
        26 / a ^ 4 * (if 1 / a < (J : ℝ) + 1 then 1 / ((J : ℝ) + 1) ^ 2 else 0) := by
  have hm1 : (0 : ℝ) < (J : ℝ) + 1 := by positivity
  set n : ℝ := (J : ℝ) + 1 with hn
  have hden : 1 ≤ 1 + a ^ 2 * n ^ 2 := by nlinarith [sq_nonneg (a * n)]
  by_cases h1 : n ≤ 1 / a
  · rw [if_pos h1, if_neg (not_lt.2 h1), mul_zero, add_zero]
    have hinv : ((1 + a ^ 2 * n ^ 2)⁻¹) ^ 2 ≤ 1 := by
      rw [inv_pow]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ hden)
    have : n ^ 2 * ((1 + a ^ 2 * n ^ 2)⁻¹) ^ 2 ≤ n ^ 2 := by
      calc n ^ 2 * ((1 + a ^ 2 * n ^ 2)⁻¹) ^ 2 ≤ n ^ 2 * 1 := by gcongr
        _ = n ^ 2 := mul_one _
    nlinarith
  · have h2 : 1 / a < n := lt_of_not_ge h1
    rw [if_neg h1, if_pos h2, mul_zero, zero_add]
    have hge : a ^ 4 * n ^ 4 ≤ (1 + a ^ 2 * n ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (a ^ 2 * n ^ 2)]
    have hpos : 0 < a ^ 4 * n ^ 4 := by positivity
    have key : ((1 + a ^ 2 * n ^ 2)⁻¹) ^ 2 ≤ 1 / (a ^ 4 * n ^ 4) := by
      rw [inv_pow, ← one_div]
      exact one_div_le_one_div_of_le hpos hge
    have ha0 : a ≠ 0 := ha.ne'
    have hn0 : n ≠ 0 := hm1.ne'
    calc 26 * n ^ 2 * ((1 + a ^ 2 * n ^ 2)⁻¹) ^ 2 ≤ 26 * n ^ 2 * (1 / (a ^ 4 * n ^ 4)) := by
          gcongr
      _ = 26 / a ^ 4 * (1 / n ^ 2) := by
          field_simp

/-- **The physical one-particle Sobolev sum**: `Σ_ν (1 + a²|ν|²)⁻² ≤ 1 + 78/a³` over every finite
set of lattice points. -/
theorem sum_sobolevP_le {a : ℝ} (ha : 0 < a) (S : Finset Lat3) :
    ∑ nu ∈ S, ((1 + a ^ 2 * nsq nu)⁻¹) ^ 2 ≤ sobP a := by
  obtain ⟨R, hR⟩ := exists_box_superset S
  have h1 : ∑ nu ∈ S, ((1 + a ^ 2 * nsq nu)⁻¹) ^ 2 ≤
      ∑ nu ∈ box R, ((1 + a ^ 2 * nsq nu)⁻¹) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hR fun _ _ _ => sq_nonneg _
  refine h1.trans ?_
  rw [sum_box_eq_shells, nsq_zero, mul_zero, add_zero, inv_one, one_pow]
  have hsh : ∑ J ∈ range R, ∑ nu ∈ shell J, ((1 + a ^ 2 * nsq nu)⁻¹) ^ 2 ≤
      ∑ J ∈ range R, 26 * ((J : ℝ) + 1) ^ 2 * ((1 + a ^ 2 * ((J : ℝ) + 1) ^ 2)⁻¹) ^ 2 :=
    sum_le_sum fun J _ => sum_shell_le _ J (by positivity)
      fun nu h => sobolevP_le_of_not_inBox a h
  have hterm := sum_le_sum fun J (_ : J ∈ range R) => shell_termP ha J
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hterm
  have hy : 0 < 1 / a := by positivity
  have hhead := FreeBoundary.sum_sq_head_le hy.le R
  have htail := FreeBoundary.sum_inv_sq_tail_le hy R
  have e : 26 * (1 / a) ^ 3 + 26 / a ^ 4 * (2 / (1 / a)) = 78 / a ^ 3 := by
    have ha0 : a ≠ 0 := ha.ne'
    field_simp
    ring
  have h2 : 26 * ∑ J ∈ range R, (if (J : ℝ) + 1 ≤ 1 / a then ((J : ℝ) + 1) ^ 2 else 0) ≤
      26 * (1 / a) ^ 3 :=
    mul_le_mul_of_nonneg_left hhead (by norm_num)
  have h3 : 26 / a ^ 4 * ∑ J ∈ range R,
      (if 1 / a < (J : ℝ) + 1 then 1 / ((J : ℝ) + 1) ^ 2 else 0) ≤
      26 / a ^ 4 * (2 / (1 / a)) :=
    mul_le_mul_of_nonneg_left htail (by positivity)
  unfold sobP
  linarith

end SobolevP

/-! ## Slices with the physical weight -/

section SlicesP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The physical slice weight `1 + a²|X|²`. -/
def sliceWeightP (a : ℝ) (X : ι → Lat3) (q : ι) : ℝ := 1 + a ^ 2 * nsq (X q)

lemma sliceWeightP_pos (a : ℝ) (X : ι → Lat3) (q : ι) : 0 < sliceWeightP a X q := by
  unfold sliceWeightP
  have := nsq_nonneg (X q)
  positivity

lemma slice_weightP_sum_le {a : ℝ} (ha : 0 < a) {σ : Type*} [DecidableEq σ]
    {rel : ι → ι → Prop} {S : ι → σ} {X : ι → Lat3} (h : SliceData rel S X) (p : ι) :
    ∑ p', (if S p' = S p then (sliceWeightP a X p')⁻¹ ^ 2 else 0) ≤ sobP a := by
  classical
  rw [← Finset.sum_filter]
  set s := univ.filter fun p' => S p' = S p
  calc ∑ p' ∈ s, (sliceWeightP a X p')⁻¹ ^ 2 = ∑ p' ∈ s, ((1 + a ^ 2 * nsq (X p'))⁻¹) ^ 2 := rfl
    _ ≤ ∑ nu ∈ s.image X, ((1 + a ^ 2 * nsq nu)⁻¹) ^ 2 := by
        refine sum_comp_le_of_injOn s X ?_ (fun nu => ((1 + a ^ 2 * nsq nu)⁻¹) ^ 2) _
          (fun q hq => mem_image_of_mem _ hq) (fun nu _ => sq_nonneg _)
        intro q hq q' hq' hX
        exact h.inj q q' ((mem_filter.mp hq).2.trans (mem_filter.mp hq').2.symm) hX
    _ ≤ sobP a := sum_sobolevP_le ha _

/-- Slice-Young for a transfer kernel with the physical weight: if the column `ℓ²` sums are at
most `B`, the output is bounded by `S B` times the squared weighted input norm. -/
lemma kOp_sq_le_sliceP {a : ℝ} (ha : 0 < a) {σ : Type*} [DecidableEq σ] {rel : ι → ι → Prop}
    {S : ι → σ} {X : ι → Lat3} (h : SliceData rel S X) (kernel : ι → ι → ℂ)
    (hsupp : ∀ q p, kernel q p ≠ 0 → rel q p) {B : ℝ}
    (hcol : ∀ p, ∑ q, ‖kernel q p‖ ^ 2 ≤ B) (hvec : ι → ℝ) (hh : ∀ p, 0 ≤ hvec p) :
    ∑ q, (∑ p, ‖kernel q p‖ * hvec p) ^ 2 ≤
      B * sobP a * ∑ p, (sliceWeightP a X p * hvec p) ^ 2 := by
  have hY := slice_young_sq S (fun q p => ‖kernel q p‖) hvec (fun _ _ => norm_nonneg _) hh
    (fun q p hk => h.compat q p (hsupp q p (fun h0 => hk (by simp [h0])))) hcol
  have hM := slice_mass_le S hvec (sliceWeightP a X) hh (sliceWeightP_pos a X)
    (slice_weightP_sum_le ha h)
  calc ∑ q, (∑ p, ‖kernel q p‖ * hvec p) ^ 2 ≤ B * ∑ p, hvec p * sliceMass S hvec p := hY
    _ ≤ B * (sobP a * ∑ p, (sliceWeightP a X p * hvec p) ^ 2) := by
        rcases isEmpty_or_nonempty ι with hι | hι
        · simp
        · have hB' : 0 ≤ B := (sum_nonneg fun q _ => sq_nonneg _).trans
            (hcol (Classical.arbitrary ι))
          exact mul_le_mul_of_nonneg_left hM hB'
    _ = B * sobP a * ∑ p, (sliceWeightP a X p * hvec p) ^ 2 := by ring

end SlicesP

/-! ## Operator and form bounds with the physical weight -/

section OperatorBoundsP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {rel : ι → ι → Prop} {tau : ι → ι → Lat3} {kappa : Lat3 → ℂ} {c : ℝ}

lemma norm_kOp_high_leP {a : ℝ} (ha : 0 < a) (hk : KernelBound kappa c) (hc : 0 ≤ c)
    (hcol : ColInj rel tau) {σ : Type*} [DecidableEq σ] {S : ι → σ} {X : ι → Lat3}
    (hS : SliceData rel S X) (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ ι) :
    ‖kOp (tk (highRel rel tau J) tau kappa) u‖ ≤
      c * Real.sqrt (26 * sobP a / J) * ‖wMul (sliceWeightP a X) u‖ := by
  have hle : ∀ q p, highRel rel tau J q p → rel q p := fun _ _ h => h.1
  have hX : 0 ≤ c * Real.sqrt (26 * sobP a / J) * ‖wMul (sliceWeightP a X) u‖ :=
    mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (norm_nonneg _)
  apply norm_kOp_le_of_sq _ u hX
  have h := kOp_sq_le_sliceP ha (hS.mono hle) (tk (highRel rel tau J) tau kappa)
    (fun q p h0 => rel_of_tk_ne_zero h0)
    (tk_col_l2 hk hc (hcol.mono hle) J hJ (fun _ _ h => h.2)) (fun p => ‖u p‖)
    (fun _ => norm_nonneg _)
  rw [← norm_wMul_sq _ (fun q => (sliceWeightP_pos a X q).le)] at h
  refine h.trans (le_of_eq ?_)
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hS0 : 0 ≤ sobP a := (sobP_pos ha).le
  rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hS0) hJpos.le)]
  ring

/-- Operator bound for a transfer kernel with a slice structure, physical weight. -/
lemma norm_kOp_tk_leP {a : ℝ} (ha : 0 < a) (hk : KernelBound kappa c) (hc : 0 ≤ c)
    (hrow : RowInj rel tau) (hcol : ColInj rel tau) {σ : Type*} [DecidableEq σ] {S : ι → σ}
    {X : ι → Lat3} (hS : SliceData rel S X) (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ ι) :
    ‖kOp (tk rel tau kappa) u‖ ≤
      c * (26 * J) * ‖u‖ + c * Real.sqrt (26 * sobP a / J) * ‖wMul (sliceWeightP a X) u‖ := by
  rw [tk_eq_low_add_high rel tau kappa J, kOp_add, LinearMap.add_apply]
  exact (norm_add_le _ _).trans (add_le_add (norm_kOp_low_le hk hc hrow hcol J u)
    (norm_kOp_high_leP ha hk hc hcol hS J hJ u))

/-- Tail version of `norm_kOp_tk_leP`. -/
lemma norm_mask_kOp_tk_leP {a : ℝ} (ha : 0 < a) (hk : KernelBound kappa c) (hc : 0 ≤ c)
    (hrow : RowInj rel tau) (hcol : ColInj rel tau) {σ : Type*} [DecidableEq σ] {S : ι → σ}
    {X : ι → Lat3} (hS : SliceData rel S X) (J : ℕ) (hJ : 1 ≤ J) (P P' : ι → Prop)
    (hdich : ∀ q p, rel q p → InBox J (tau q p) → P q → P' p) (u : EuclideanSpace ℂ ι) :
    ‖maskOp P (kOp (tk rel tau kappa) u)‖ ≤
      c * (26 * J) * ‖maskOp P' u‖ +
        c * Real.sqrt (26 * sobP a / J) * ‖wMul (sliceWeightP a X) u‖ := by
  rw [tk_eq_low_add_high rel tau kappa J, kOp_add, LinearMap.add_apply, map_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have heq : maskOp P (kOp (tk (lowRel rel tau J) tau kappa) u) =
        maskOp P (kOp (tk (lowRel rel tau J) tau kappa) (maskOp P' u)) := by
      ext q
      by_cases hq : P q
      · rw [maskOp_apply_of P _ hq, maskOp_apply_of P _ hq, kOp_apply, kOp_apply]
        refine sum_congr rfl fun p _ => ?_
        by_cases hr : lowRel rel tau J q p
        · rw [maskOp_apply_of P' u (hdich q p hr.1 hr.2 hq)]
        · rw [tk_of_not_rel hr, mul_zero, mul_zero]
      · rw [maskOp_apply_of_not P _ hq, maskOp_apply_of_not P _ hq]
    rw [heq]
    exact (norm_maskOp_le P _).trans (norm_kOp_low_le hk hc hrow hcol J _)
  · exact (norm_maskOp_le P _).trans (norm_kOp_high_leP ha hk hc hcol hS J hJ u)

/-- One-sided bilinear bound with the physical weight. -/
lemma norm_inner_kOp_le_oneSidedP {a : ℝ} (ha : 0 < a) {σ : Type*} [DecidableEq σ] {S : ι → σ}
    {X : ι → Lat3} (hS : SliceData rel S X) (kernel : ι → ι → ℂ)
    (hsupp : ∀ q p, kernel q p ≠ 0 → rel q p)
    (P : ι → Prop) (hdich : ∀ q p, kernel q p ≠ 0 → P q ∨ P p) {B : ℝ} (hB : 0 ≤ B)
    (hcolB : ∀ p, ∑ q, ‖kernel q p‖ ^ 2 ≤ B) (hrowB : ∀ q, ∑ p, ‖kernel q p‖ ^ 2 ≤ B)
    (v u : EuclideanSpace ℂ ι) :
    ‖inner ℂ v (kOp kernel u)‖ ≤ Real.sqrt (sobP a * B) *
      (‖maskOp P u‖ * ‖wMul (sliceWeightP a X) v‖ +
        ‖maskOp P v‖ * ‖wMul (sliceWeightP a X) u‖) := by
  have hT : SliceData (fun p q => rel q p) S X :=
    ⟨fun p q h => (hS.compat q p h).symm, hS.inj⟩
  have hw : ∀ q, 0 ≤ sliceWeightP a X q := fun q => (sliceWeightP_pos a X q).le
  have hS0 : 0 ≤ sobP a := (sobP_pos ha).le
  have hpt : ∀ q p, ‖v q‖ * (‖kernel q p‖ * ‖u p‖) ≤
      ‖v q‖ * (‖kernel q p‖ * ‖(maskOp P u) p‖) +
        ‖(maskOp P v) q‖ * (‖kernel q p‖ * ‖u p‖) := by
    intro q p
    by_cases hk : kernel q p = 0
    · simp [hk]
    · rcases hdich q p hk with hq | hp
      · rw [maskOp_apply_of P v hq]
        exact le_add_of_nonneg_left (by positivity)
      · rw [maskOp_apply_of P u hp]
        exact le_add_of_nonneg_right (by positivity)
  have hsplit : ∑ q, ‖v q‖ * ∑ p, ‖kernel q p‖ * ‖u p‖ ≤
      ∑ p, ‖(maskOp P u) p‖ * ∑ q, ‖kernel q p‖ * ‖v q‖ +
        ∑ q, ‖(maskOp P v) q‖ * ∑ p, ‖kernel q p‖ * ‖u p‖ := by
    calc ∑ q, ‖v q‖ * ∑ p, ‖kernel q p‖ * ‖u p‖
        = ∑ q, ∑ p, ‖v q‖ * (‖kernel q p‖ * ‖u p‖) := by simp_rw [mul_sum]
      _ ≤ ∑ q, ∑ p, (‖v q‖ * (‖kernel q p‖ * ‖(maskOp P u) p‖) +
            ‖(maskOp P v) q‖ * (‖kernel q p‖ * ‖u p‖)) :=
          sum_le_sum fun q _ => sum_le_sum fun p _ => hpt q p
      _ = ∑ q, ∑ p, ‖v q‖ * (‖kernel q p‖ * ‖(maskOp P u) p‖) +
            ∑ q, ∑ p, ‖(maskOp P v) q‖ * (‖kernel q p‖ * ‖u p‖) := by
          simp_rw [sum_add_distrib]
      _ = _ := by
          congr 1
          · rw [sum_comm]
            exact sum_congr rfl fun p _ => by
              rw [mul_sum]; exact sum_congr rfl fun q _ => by ring
          · exact sum_congr rfl fun q _ => by rw [mul_sum]
  have hsq : 0 ≤ Real.sqrt (sobP a * B) := Real.sqrt_nonneg _
  have hb1 : ∑ p, (∑ q, ‖kernel q p‖ * ‖v q‖) ^ 2 ≤
      (Real.sqrt (sobP a * B) * ‖wMul (sliceWeightP a X) v‖) ^ 2 := by
    have h := kOp_sq_le_sliceP ha hT (fun p q => kernel q p) (fun p q h0 => hsupp q p h0)
      hrowB (fun q => ‖v q‖) (fun _ => norm_nonneg _)
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hS0 hB), norm_wMul_sq _ hw]
    linarith
  have hb2 : ∑ q, (∑ p, ‖kernel q p‖ * ‖u p‖) ^ 2 ≤
      (Real.sqrt (sobP a * B) * ‖wMul (sliceWeightP a X) u‖) ^ 2 := by
    have h := kOp_sq_le_sliceP ha hS kernel hsupp hcolB (fun p => ‖u p‖)
      (fun _ => norm_nonneg _)
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hS0 hB), norm_wMul_sq _ hw]
    linarith
  have e1 : ∑ p, ‖(maskOp P u) p‖ ^ 2 ≤ ‖maskOp P u‖ ^ 2 := le_of_eq (sum_norm_sq_eq_norm_sq _)
  have e2 : ∑ q, ‖(maskOp P v) q‖ ^ 2 ≤ ‖maskOp P v‖ ^ 2 := le_of_eq (sum_norm_sq_eq_norm_sq _)
  have t1 := bilinear_le (fun p q => ‖kernel q p‖) (fun p => ‖(maskOp P u) p‖)
    (fun q => ‖v q‖) (norm_nonneg _) (by positivity) e1 hb1
  have t2 := bilinear_le (fun q p => ‖kernel q p‖) (fun q => ‖(maskOp P v) q‖)
    (fun p => ‖u p‖) (norm_nonneg _) (by positivity) e2 hb2
  calc ‖inner ℂ v (kOp kernel u)‖ ≤ ∑ q, ‖v q‖ * ∑ p, ‖kernel q p‖ * ‖u p‖ :=
        norm_inner_kOp_le kernel v u
    _ ≤ _ := hsplit
    _ ≤ ‖maskOp P u‖ * (Real.sqrt (sobP a * B) * ‖wMul (sliceWeightP a X) v‖) +
          ‖maskOp P v‖ * (Real.sqrt (sobP a * B) * ‖wMul (sliceWeightP a X) u‖) :=
        add_le_add t1 t2
    _ = _ := by ring

end OperatorBoundsP

/-! ## Physical weights on the register -/

section WeightsP

variable {eta m : ℕ}

/-- The physical total weight `1 + a² Σ_b |ν_b|²`. -/
noncomputable def wTotP (a : ℝ) (q : RCfg eta m) : ℝ := 1 + a ^ 2 * ∑ b, nsq (gl (q b))

lemma wTotP_ge_one (a : ℝ) (q : RCfg eta m) : 1 ≤ wTotP a q := by
  unfold wTotP
  have h : 0 ≤ ∑ b, nsq (gl (q b)) := sum_nonneg fun b _ => nsq_nonneg _
  have := mul_nonneg (sq_nonneg a) h
  linarith

lemma sliceWeightP_le_wTotP (a : ℝ) (i : Fin eta) (q : RCfg eta m) :
    sliceWeightP a (regCoord i) q ≤ wTotP a q := by
  unfold sliceWeightP regCoord wTotP
  have h := Finset.single_le_sum (f := fun b => nsq (gl (q b)))
    (fun b _ => nsq_nonneg _) (Finset.mem_univ i)
  have := mul_le_mul_of_nonneg_left h (sq_nonneg a)
  linarith

lemma norm_wMul_sliceP_le (a : ℝ) (i : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (sliceWeightP a (regCoord i)) u‖ ≤ ‖wMul (wTotP a) u‖ :=
  norm_wMul_mono (fun q => (sliceWeightP_pos a _ q).le) (sliceWeightP_le_wTotP a i) u

lemma wTotP_ge_of_high (a : ℝ) {T : ℕ} {r : Fin eta} {q : RCfg eta m} (h : High T r q) :
    1 + a ^ 2 * ((T : ℝ) + 1) ^ 2 ≤ wTotP a q := by
  have h1 := nsq_ge_of_not_inBox h
  have h2 := Finset.single_le_sum (f := fun b => nsq (gl (q b)))
    (fun b _ => nsq_nonneg _) (Finset.mem_univ r)
  have h3 : ((T : ℝ) + 1) ^ 2 ≤ ∑ b, nsq (gl (q b)) := h1.trans h2
  have := mul_le_mul_of_nonneg_left h3 (sq_nonneg a)
  unfold wTotP
  linarith

variable (P : RegParticles eta)

/-- The physical mass-weighted weight `1 + a² Σ_b |ν_b|²/m_b`. -/
noncomputable def wMP (a : ℝ) (q : RCfg eta m) : ℝ := 1 + a ^ 2 * ∑ b, nsq (gl (q b)) / P.mass b

lemma wMP_ge_one (a : ℝ) (q : RCfg eta m) : 1 ≤ wMP P a q := by
  unfold wMP
  have h : 0 ≤ ∑ b, nsq (gl (q b)) / P.mass b :=
    sum_nonneg fun b _ => div_nonneg (nsq_nonneg _) (P.mass_pos b).le
  have := mul_nonneg (sq_nonneg a) h
  linarith

lemma wTotP_le_maxMass_mul_wMP (a : ℝ) (q : RCfg eta m) : wTotP a q ≤ P.maxMass * wMP P a q := by
  unfold wTotP wMP
  have hM := P.one_le_maxMass
  have h : ∀ b ∈ (univ : Finset (Fin eta)),
      nsq (gl (q b)) ≤ P.maxMass * (nsq (gl (q b)) / P.mass b) := by
    intro b _
    have hmb := P.mass_pos b
    have hn := nsq_nonneg (gl (q b))
    rw [mul_div_assoc', le_div_iff₀ hmb]
    nlinarith [P.mass_le_maxMass b]
  have hs := Finset.sum_le_sum h
  rw [← Finset.mul_sum] at hs
  have hs2 := mul_le_mul_of_nonneg_left hs (sq_nonneg a)
  have h0 : 0 ≤ ∑ b, nsq (gl (q b)) / P.mass b :=
    sum_nonneg fun b _ => div_nonneg (nsq_nonneg _) (P.mass_pos b).le
  have h1 : a ^ 2 * (P.maxMass * ∑ b, nsq (gl (q b)) / P.mass b) =
      P.maxMass * (a ^ 2 * ∑ b, nsq (gl (q b)) / P.mass b) := by ring
  rw [mul_add, mul_one]
  linarith

lemma norm_wMul_wTotP_le (a : ℝ) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wTotP a) u‖ ≤ P.maxMass * ‖wMul (wMP P a) u‖ := by
  have h1 := norm_wMul_mono (fun q => le_trans zero_le_one (wTotP_ge_one a q))
    (wTotP_le_maxMass_mul_wMP P a) u
  have h2 : wMul (fun q => P.maxMass * wMP P a q) u =
      ((P.maxMass : ℝ) : ℂ) • wMul (wMP P a) u := by
    ext q
    simp only [wMul_apply, PiLp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [h2, norm_smul, Complex.norm_real, Real.norm_of_nonneg P.maxMass_pos.le] at h1
  exact h1

/-- The kinetic symbol is `(1/2)(wMP g - 1)`. -/
lemma kinT_eq_wMP (g : ℝ) (q : RCfg eta m) : kinT eta m P g q = 1 / 2 * (wMP P g q - 1) := by
  unfold kinT wM wMP
  ring

end WeightsP

/-! ## Per-term bounds with the physical weight -/

section TermBoundsP

variable {ν : Type*} [Fintype ν] {eta m : ℕ} {D : NucData ν} {gamma : ℝ} {κ : Lat3 → ℝ}

lemma gridTerm_opP {a : ℝ} (ha : 0 < a) (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (t : Term eta ν) (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖kOp (gridTerm eta m D κ t) u‖ ≤ coupling eta D gamma t * (26 * J) * ‖u‖ +
      coupling eta D gamma t * Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖ := by
  have hc := coupling_nonneg (D := D) hg t
  cases t with
  | inl pr =>
    have h := norm_kOp_tk_leP ha (kgr_bound hκ) hg (gRel2_rowInj pr.1.1 pr.1.2)
      (gRel2_colInj pr.1.1 pr.1.2) (gSlice2_data pr.1.1 pr.1.2) J hJ u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_sliceP_le a _ u)
      (mul_nonneg hc (Real.sqrt_nonneg _))
  | inr il =>
    have h := norm_kOp_tk_leP ha (kgn_bound D hκ il.2) (mul_nonneg (D.charge_nonneg il.2) hg)
      (spec1_rowInj_g il.1) (spec1_colInj_g il.1) (slice1_data il.1) J hJ u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_sliceP_le a _ u)
      (mul_nonneg hc (Real.sqrt_nonneg _))

lemma galTerm_opP {a : ℝ} (ha : 0 < a) (hg : 0 ≤ gamma) (t : Term eta ν) (J : ℕ) (hJ : 1 ≤ J)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖kOp (galTerm eta m D gamma t) u‖ ≤ coupling eta D gamma t * (26 * J) * ‖u‖ +
      coupling eta D gamma t * Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖ := by
  have hc := coupling_nonneg (D := D) hg t
  cases t with
  | inl pr =>
    have h := norm_kOp_tk_leP ha (kee_bound D hg) hg (wRel2_rowInj pr.1.1 pr.1.2)
      (wRel2_colInj pr.1.1 pr.1.2) (wSlice2_data pr.1.1 pr.1.2) J hJ u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_sliceP_le a _ u)
      (mul_nonneg hc (Real.sqrt_nonneg _))
  | inr il =>
    have h := norm_kOp_tk_leP ha (knuc_bound D hg il.2) (mul_nonneg (D.charge_nonneg il.2) hg)
      (spec1_rowInj_w il.1) (spec1_colInj_w il.1) (slice1_data il.1) J hJ u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_sliceP_le a _ u)
      (mul_nonneg hc (Real.sqrt_nonneg _))

lemma gridTerm_tailP {a : ℝ} (ha : 0 < a) (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (t : Term eta ν) (J T : ℕ) (hJ : 1 ≤ J) (hJT : J ≤ T) (hT : T ≤ 2 * m) (r : Fin eta)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) (kOp (gridTerm eta m D κ t) u)‖ ≤
      coupling eta D gamma t * (26 * J) * ‖maskOp (High (T - J) r) u‖ +
      coupling eta D gamma t * Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖ := by
  have hc := coupling_nonneg (D := D) hg t
  cases t with
  | inl pr =>
    have h := norm_mask_kOp_tk_leP ha (kgr_bound hκ) hg (gRel2_rowInj pr.1.1 pr.1.2)
      (gRel2_colInj pr.1.1 pr.1.2) (gSlice2_data pr.1.1 pr.1.2) J hJ (High T r)
      (High (T - J) r)
      (fun q p hr hd hq => gRel2_lowDich pr.1.1 pr.1.2 J T hJT hT r q p hr hd hq) u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_sliceP_le a _ u)
      (mul_nonneg hc (Real.sqrt_nonneg _))
  | inr il =>
    have h := norm_mask_kOp_tk_leP ha (kgn_bound D hκ il.2)
      (mul_nonneg (D.charge_nonneg il.2) hg)
      (spec1_rowInj_g il.1) (spec1_colInj_g il.1) (slice1_data il.1) J hJ (High T r)
      (High (T - J) r) (fun q p hr hd hq => spec1_lowDich_g il.1 J T hJT hT r q p hr hd hq) u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_sliceP_le a _ u)
      (mul_nonneg hc (Real.sqrt_nonneg _))

lemma galTerm_tailP {a : ℝ} (ha : 0 < a) (hg : 0 ≤ gamma) (t : Term eta ν) (J T : ℕ)
    (hJ : 1 ≤ J) (hJT : J ≤ T) (r : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) (kOp (galTerm eta m D gamma t) u)‖ ≤
      coupling eta D gamma t * (26 * J) * ‖maskOp (High (T - J) r) u‖ +
      coupling eta D gamma t * Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖ := by
  have hc := coupling_nonneg (D := D) hg t
  cases t with
  | inl pr =>
    have h := norm_mask_kOp_tk_leP ha (kee_bound D hg) hg (wRel2_rowInj pr.1.1 pr.1.2)
      (wRel2_colInj pr.1.1 pr.1.2) (wSlice2_data pr.1.1 pr.1.2) J hJ (High T r)
      (High (T - J) r)
      (fun q p hr hd hq => wRel2_lowDich pr.1.1 pr.1.2 J T hJT r q p hr hd hq) u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_sliceP_le a _ u)
      (mul_nonneg hc (Real.sqrt_nonneg _))
  | inr il =>
    have h := norm_mask_kOp_tk_leP ha (knuc_bound D hg il.2)
      (mul_nonneg (D.charge_nonneg il.2) hg)
      (spec1_rowInj_w il.1) (spec1_colInj_w il.1) (slice1_data il.1) J hJ (High T r)
      (High (T - J) r) (fun q p hr hd hq => spec1_lowDich_w il.1 J T hJT r q p hr hd hq) u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_sliceP_le a _ u)
      (mul_nonneg hc (Real.sqrt_nonneg _))

/-- The form constant of the aliasing estimate with the physical weight. -/
noncomputable def formAP (a : ℝ) (s m : ℕ) : ℝ :=
  2 * Real.sqrt (26 * sobP a / (2 * s)) + 2 * Real.sqrt (26 * sobP a / m)

lemma formAP_nonneg (a : ℝ) (s m : ℕ) : 0 ≤ formAP a s m := by
  unfold formAP; positivity

/-- `√(S c² (26/J)) = c √(26 S/J)`. -/
lemma sqrt_coupling_eqP (a c : ℝ) (hc : 0 ≤ c) (J : ℕ) :
    Real.sqrt (sobP a * (c ^ 2 * (26 / (J : ℝ)))) = c * Real.sqrt (26 * sobP a / J) := by
  rw [show sobP a * (c ^ 2 * (26 / (J : ℝ))) = c ^ 2 * (26 * sobP a / J) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

/-- Form bound for the dropped and wrap parts of one term, physical weight. -/
lemma term_formP {a : ℝ} (ha : 0 < a) (hg : 0 ≤ gamma) {s : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    (hκ : GridKernel gamma D.ref s κ)
    (t : Term eta ν) (u v : EuclideanSpace ℂ (RCfg eta m)) {τu τv : ℝ} (hτu0 : 0 ≤ τu)
    (hτv0 : 0 ≤ τv) (hτu : ∀ r, ‖maskOp (High s r) u‖ ≤ τu)
    (hτv : ∀ r, ‖maskOp (High s r) v‖ ≤ τv) :
    ‖inner ℂ v (kOp (dTerm eta m D gamma κ t) u)‖ + ‖inner ℂ v (kOp (rTerm eta m D κ t) u)‖ ≤
      coupling eta D gamma t * (formAP a s m * (τu * ‖wMul (wTotP a) v‖ +
        τv * ‖wMul (wTotP a) u‖) + 52 * m * (τv * τu)) := by
  have hm : 1 ≤ m := hs.trans hsm
  have hs2 : 1 ≤ 2 * s := by omega
  have h2sm : 2 * s ≤ 2 * m := by omega
  have hc := coupling_nonneg (D := D) hg t
  set Xu := ‖wMul (wTotP a) u‖
  set Xv := ‖wMul (wTotP a) v‖
  have hτu' : ∀ r, ‖maskOp (High m r) u‖ ≤ τu := fun r =>
    (norm_maskOp_mono (fun q hq => High.mono hsm hq) u).trans (hτu r)
  have hτv' : ∀ r, ‖maskOp (High m r) v‖ ≤ τv := fun r =>
    (norm_maskOp_mono (fun q hq => High.mono hsm hq) v).trans (hτv r)
  have orBound : ∀ (P P' : RCfg eta m → Prop) (w : EuclideanSpace ℂ (RCfg eta m)) (τ : ℝ),
      ‖maskOp P w‖ ≤ τ → ‖maskOp P' w‖ ≤ τ → ‖maskOp (fun q => P q ∨ P' q) w‖ ≤ 2 * τ :=
    fun P P' w τ h1 h2 => (norm_maskOp_or_le P P' w).trans (by linarith)
  cases t with
  | inl pr =>
    obtain ⟨⟨i, j⟩, hij⟩ := pr
    simp only [dTerm, rTerm, coupling]
    rw [tk_eq_high_of_zero (wRel2 i j) (wTau i) (kdr D gamma κ (2 * m)) (2 * s)
      (fun x hx => kdr_eq_zero D hκ h2sm hx)]
    have hleD : ∀ q p, highRel (wRel2 i j) (wTau i) (2 * s) q p → wRel2 (M := 2 * m) i j q p :=
      fun _ _ h => h.1
    have hD := norm_inner_kOp_le_oneSidedP ha ((wSlice2_data i j).mono hleD)
      (tk (highRel (wRel2 i j) (wTau i) (2 * s)) (wTau i) (kdr D gamma κ (2 * m)))
      (fun q p h0 => rel_of_tk_ne_zero h0) (High s i)
      (fun q p h0 => wRel2_high_dich s i j q p (rel_of_tk_ne_zero h0))
      (B := (2 * gamma) ^ 2 * (26 / ((2 * s : ℕ) : ℝ))) (by positivity)
      (tk_col_l2 (kdr_bound D hg hκ.bound _) (by positivity) ((wRel2_colInj i j).mono hleD)
        (2 * s) hs2 (fun _ _ h => h.2))
      (tk_row_l2 (kdr_bound D hg hκ.bound _) (by positivity) ((wRel2_rowInj i j).mono hleD)
        (2 * s) hs2 (fun _ _ h => h.2)) v u
    rw [sqrt_coupling_eqP a (2 * gamma) (by positivity)] at hD
    have hD' := hD.trans (oneSided_to_tau (by positivity) hτu0 hτv0 (hτu i) (hτv i)
      (norm_wMul_sliceP_le a i v) (norm_wMul_sliceP_le a i u) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _))
    rw [tk_eq_low_add_high (rRel2 i j) (gTau i) (kgr κ) m, kOp_add, LinearMap.add_apply,
      inner_add_right]
    have hleS : ∀ q p, lowRel (rRel2 i j) (gTau i) m q p → gRel2 (M := 2 * m) i j q p :=
      fun _ _ h => h.1.1
    have hS := norm_inner_kOp_le_twoSided
      (tk (lowRel (rRel2 i j) (gTau i) m) (gTau i) (kgr κ)) (High m i) (High m j)
      (fun q p h0 => rRel2_strong_dich m i j q p (rel_of_tk_ne_zero h0))
      (α := gamma * (26 * m)) (by positivity)
      (tk_row_l1 (kgr_bound hκ.bound) hg ((gRel2_rowInj i j).mono hleS) m (fun _ _ h => h.2))
      (tk_col_l1 (kgr_bound hκ.bound) hg ((gRel2_colInj i j).mono hleS) m (fun _ _ h => h.2))
      v u
    have hS' : gamma * (26 * m) * (‖maskOp (High m i) v‖ * ‖maskOp (High m i) u‖ +
        ‖maskOp (High m j) v‖ * ‖maskOp (High m j) u‖) ≤ gamma * (52 * m * (τv * τu)) := by
      have h1 := mul_le_mul (hτv' i) (hτu' i) (norm_nonneg _) hτv0
      have h2 := mul_le_mul (hτv' j) (hτu' j) (norm_nonneg _) hτv0
      have : 0 ≤ gamma * (26 * m) := by positivity
      nlinarith
    have hleW : ∀ q p, highRel (rRel2 i j) (gTau i) m q p → gRel2 (M := 2 * m) i j q p :=
      fun _ _ h => h.1.1
    have hW := norm_inner_kOp_le_oneSidedP ha ((gSlice2_data i j).mono hleW)
      (tk (highRel (rRel2 i j) (gTau i) m) (gTau i) (kgr κ))
      (fun q p h0 => rel_of_tk_ne_zero h0) (fun q => High m i q ∨ High m j q)
      (fun q p h0 => rRel2_weak_dich m i j q p (rel_of_tk_ne_zero h0))
      (B := gamma ^ 2 * (26 / (m : ℝ))) (by positivity)
      (tk_col_l2 (kgr_bound hκ.bound) hg ((gRel2_colInj i j).mono hleW) m hm
        (fun _ _ h => h.2))
      (tk_row_l2 (kgr_bound hκ.bound) hg ((gRel2_rowInj i j).mono hleW) m hm
        (fun _ _ h => h.2)) v u
    rw [sqrt_coupling_eqP a gamma hg] at hW
    have hW' := hW.trans (oneSided_to_tau (by positivity) (by positivity : 0 ≤ 2 * τu)
      (by positivity : 0 ≤ 2 * τv) (orBound _ _ u τu (hτu' i) (hτu' j))
      (orBound _ _ v τv (hτv' i) (hτv' j)) (norm_wMul_sliceP_le a i v)
      (norm_wMul_sliceP_le a i u)
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _))
    have htot := add_le_add hD' (norm_add_le _ _ |>.trans (add_le_add (hS.trans hS') hW'))
    refine htot.trans (le_of_eq ?_)
    unfold formAP
    push_cast
    ring
  | inr il =>
    obtain ⟨i, l⟩ := il
    simp only [dTerm, rTerm, coupling]
    have hcl : 0 ≤ D.charge l * gamma := mul_nonneg (D.charge_nonneg l) hg
    rw [tk_eq_high_of_zero (Spec1 i) (wTau i) (kdn D gamma κ (2 * m) l) (2 * s)
      (fun x hx => kdn_eq_zero D hκ h2sm l hx)]
    have hleD : ∀ q p, highRel (Spec1 i) (wTau i) (2 * s) q p → Spec1 (M := 2 * m) i q p :=
      fun _ _ h => h.1
    have hD := norm_inner_kOp_le_oneSidedP ha ((slice1_data i).mono hleD)
      (tk (highRel (Spec1 i) (wTau i) (2 * s)) (wTau i) (kdn D gamma κ (2 * m) l))
      (fun q p h0 => rel_of_tk_ne_zero h0) (High s i)
      (fun q p h0 => spec1_high_dich s i q p (rel_of_tk_ne_zero h0))
      (B := (2 * (D.charge l * gamma)) ^ 2 * (26 / ((2 * s : ℕ) : ℝ))) (by positivity)
      (tk_col_l2 (kdn_bound D hg hκ.bound _ l) (by positivity) ((spec1_colInj_w i).mono hleD)
        (2 * s) hs2 (fun _ _ h => h.2))
      (tk_row_l2 (kdn_bound D hg hκ.bound _ l) (by positivity) ((spec1_rowInj_w i).mono hleD)
        (2 * s) hs2 (fun _ _ h => h.2)) v u
    rw [sqrt_coupling_eqP a _ (by positivity)] at hD
    have hD' := hD.trans (oneSided_to_tau (by positivity) hτu0 hτv0 (hτu i) (hτv i)
      (norm_wMul_sliceP_le a i v) (norm_wMul_sliceP_le a i u) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _))
    rw [tk_eq_low_add_high (rRel1 i) (gTau i) (kgn D κ l) m, kOp_add,
      LinearMap.add_apply, inner_add_right]
    have hleS : ∀ q p, lowRel (rRel1 i) (gTau i) m q p → Spec1 (M := 2 * m) i q p :=
      fun _ _ h => h.1.1
    have hS := norm_inner_kOp_le_twoSided
      (tk (lowRel (rRel1 i) (gTau i) m) (gTau i) (kgn D κ l)) (High m i) (High m i)
      (fun q p h0 => Or.inl (rRel1_strong_dich m i q p (rel_of_tk_ne_zero h0)))
      (α := D.charge l * gamma * (26 * m)) (by positivity)
      (tk_row_l1 (kgn_bound D hκ.bound l) hcl ((spec1_rowInj_g i).mono hleS) m
        (fun _ _ h => h.2))
      (tk_col_l1 (kgn_bound D hκ.bound l) hcl ((spec1_colInj_g i).mono hleS) m
        (fun _ _ h => h.2)) v u
    have hS' : D.charge l * gamma * (26 * m) * (‖maskOp (High m i) v‖ * ‖maskOp (High m i) u‖ +
        ‖maskOp (High m i) v‖ * ‖maskOp (High m i) u‖) ≤
          D.charge l * gamma * (52 * m * (τv * τu)) := by
      have h1 := mul_le_mul (hτv' i) (hτu' i) (norm_nonneg _) hτv0
      have : 0 ≤ D.charge l * gamma * (26 * m) := by positivity
      nlinarith
    have hleW : ∀ q p, highRel (rRel1 i) (gTau i) m q p → Spec1 (M := 2 * m) i q p :=
      fun _ _ h => h.1.1
    have hW := norm_inner_kOp_le_oneSidedP ha ((slice1_data i).mono hleW)
      (tk (highRel (rRel1 i) (gTau i) m) (gTau i) (kgn D κ l))
      (fun q p h0 => rel_of_tk_ne_zero h0) (High m i)
      (fun q p h0 => rRel1_weak_dich m i q p (rel_of_tk_ne_zero h0))
      (B := (D.charge l * gamma) ^ 2 * (26 / (m : ℝ))) (by positivity)
      (tk_col_l2 (kgn_bound D hκ.bound l) hcl ((spec1_colInj_g i).mono hleW) m hm
        (fun _ _ h => h.2))
      (tk_row_l2 (kgn_bound D hκ.bound l) hcl ((spec1_rowInj_g i).mono hleW) m hm
        (fun _ _ h => h.2)) v u
    rw [sqrt_coupling_eqP a _ hcl] at hW
    have hW' := hW.trans (oneSided_to_tau (by positivity) hτu0 hτv0 (hτu' i) (hτv' i)
      (norm_wMul_sliceP_le a i v) (norm_wMul_sliceP_le a i u) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _))
    have htot := add_le_add hD' (norm_add_le _ _ |>.trans (add_le_add (hS.trans hS') hW'))
    refine htot.trans ?_
    unfold formAP
    push_cast
    have hX : 0 ≤ τu * Xv + τv * Xu := by positivity
    have hq : 0 ≤ Real.sqrt (26 * sobP a / (m : ℝ)) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hcl (mul_nonneg hq hX)]

end TermBoundsP

/-! ## Summed bounds with the physical weight -/

section TotalsP

variable {ν : Type*} [Fintype ν] {eta m : ℕ} {P : RegParticles eta} {D : NucData ν}
  {gamma : ℝ} {κ : Lat3 → ℝ}

lemma vGridK_opP {a : ℝ} (ha : 0 < a) (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖kOp (vGridK eta m P D κ) u‖ ≤ Zc P D gamma * (26 * J) * ‖u‖ +
      Zc P D gamma * Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖ := by
  rw [kOp_vGridK_eq]
  refine (norm_sum_le _ _).trans ?_
  have := sum_coupling_bound (P := P) (D := D) (gamma := gamma)
    (fun t => ‖(P.tcoef t : ℂ) • kOp (gridTerm eta m D κ t) u‖) ((26 * J) * ‖u‖)
    (Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖)
    (fun t => (norm_coef_smul_le _ _ (gridTerm_opP (D := D) ha hg hκ t J hJ u)).trans
      (le_of_eq (by ring)))
  linarith

lemma vGalK_opP {a : ℝ} (ha : 0 < a) (hg : 0 ≤ gamma) (J : ℕ) (hJ : 1 ≤ J)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖kOp (vGalK eta m P D gamma) u‖ ≤ Zc P D gamma * (26 * J) * ‖u‖ +
      Zc P D gamma * Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖ := by
  rw [kOp_vGalK_eq]
  refine (norm_sum_le _ _).trans ?_
  have := sum_coupling_bound (P := P) (D := D) (gamma := gamma)
    (fun t => ‖(P.tcoef t : ℂ) • kOp (galTerm eta m D gamma t) u‖) ((26 * J) * ‖u‖)
    (Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖)
    (fun t => (norm_coef_smul_le _ _ (galTerm_opP (D := D) ha hg t J hJ u)).trans
      (le_of_eq (by ring)))
  linarith

lemma vGridK_tailP {a : ℝ} (ha : 0 < a) (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (J T : ℕ) (hJ : 1 ≤ J) (hJT : J ≤ T) (hT : T ≤ 2 * m) (r : Fin eta)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) (kOp (vGridK eta m P D κ) u)‖ ≤
      Zc P D gamma * (26 * J) * ‖maskOp (High (T - J) r) u‖ +
      Zc P D gamma * Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖ := by
  rw [kOp_vGridK_eq, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have := sum_coupling_bound (P := P) (D := D) (gamma := gamma)
    (fun t => ‖maskOp (High T r) ((P.tcoef t : ℂ) • kOp (gridTerm eta m D κ t) u)‖)
    ((26 * J) * ‖maskOp (High (T - J) r) u‖)
    (Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖)
    (fun t => by
      rw [LinearMap.map_smul]
      exact (norm_coef_smul_le _ _ (gridTerm_tailP (D := D) ha hg hκ t J T hJ hJT hT r u)).trans
        (le_of_eq (by ring)))
  linarith

lemma vGalK_tailP {a : ℝ} (ha : 0 < a) (hg : 0 ≤ gamma) (J T : ℕ) (hJ : 1 ≤ J) (hJT : J ≤ T)
    (r : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) (kOp (vGalK eta m P D gamma) u)‖ ≤
      Zc P D gamma * (26 * J) * ‖maskOp (High (T - J) r) u‖ +
      Zc P D gamma * Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖ := by
  rw [kOp_vGalK_eq, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have := sum_coupling_bound (P := P) (D := D) (gamma := gamma)
    (fun t => ‖maskOp (High T r) ((P.tcoef t : ℂ) • kOp (galTerm eta m D gamma t) u)‖)
    ((26 * J) * ‖maskOp (High (T - J) r) u‖)
    (Real.sqrt (26 * sobP a / J) * ‖wMul (wTotP a) u‖)
    (fun t => by
      rw [LinearMap.map_smul]
      exact (norm_coef_smul_le _ _ (galTerm_tailP (D := D) ha hg t J T hJ hJT r u)).trans
        (le_of_eq (by ring)))
  linarith

lemma Delta_formP {a : ℝ} (ha : 0 < a) (hg : 0 ≤ gamma) {s : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    (hκ : GridKernel gamma D.ref s κ) (u v : EuclideanSpace ℂ (RCfg eta m))
    {τu τv : ℝ} (hτu0 : 0 ≤ τu) (hτv0 : 0 ≤ τv)
    (hτu : ∀ r, ‖maskOp (High s r) u‖ ≤ τu) (hτv : ∀ r, ‖maskOp (High s r) v‖ ≤ τv) :
    ‖inner ℂ v (Delta eta m P D gamma κ u)‖ ≤
      Zc P D gamma * (formAP a s m * (τu * ‖wMul (wTotP a) v‖ + τv * ‖wMul (wTotP a) u‖) +
        52 * m * (τv * τu)) := by
  rw [Delta, LinearMap.sub_apply, kOp_rK_eq, kOp_dK_eq, inner_sub_right, inner_sum, inner_sum]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_sum_le _ _) (norm_sum_le _ _)).trans ?_
  rw [← Finset.sum_add_distrib]
  unfold Zc
  rw [Finset.sum_mul]
  refine sum_le_sum fun t _ => ?_
  have h := term_formP (D := D) ha hg hs hsm hκ t u v hτu0 hτv0 hτu hτv
  rw [inner_smul_right, inner_smul_right, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  have hc := abs_nonneg (P.tcoef t)
  calc |P.tcoef t| * ‖inner ℂ v (kOp (rTerm eta m D κ t) u)‖ +
        |P.tcoef t| * ‖inner ℂ v (kOp (dTerm eta m D gamma κ t) u)‖
      = |P.tcoef t| * (‖inner ℂ v (kOp (dTerm eta m D gamma κ t) u)‖ +
          ‖inner ℂ v (kOp (rTerm eta m D κ t) u)‖) := by ring
    _ ≤ |P.tcoef t| * (coupling eta D gamma t * (formAP a s m * (τu * ‖wMul (wTotP a) v‖ +
          τv * ‖wMul (wTotP a) u‖) + 52 * m * (τv * τu))) := mul_le_mul_of_nonneg_left h hc
    _ = |P.tcoef t| * coupling eta D gamma t * (formAP a s m * (τu * ‖wMul (wTotP a) v‖ +
          τv * ‖wMul (wTotP a) u‖) + 52 * m * (τv * τu)) := by ring

end TotalsP

/-! ## Spectral consequences with a general kinetic scale -/

section SpectralP

/-- A register Hamiltonian `wMul kin + V` with kinetic symbol `c (W - 1)` and the operator bound
`‖V u‖ ≤ A ‖u‖ + B ‖W u‖`, `B ≤ c/4`. `PlaneWave.FreeBoundary.GridCoreGeneral`'s `RegHam` is the case `c = g²/2`,
`A = 26 Z J₀`, `B = Z √(1378/J₀)`. -/
structure RegHamP (ι : Type*) [Fintype ι] where
  W : ι → ℝ
  kin : ι → ℝ
  V : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι
  c : ℝ
  c_pos : 0 < c
  kin_eq : ∀ q, kin q = c * (W q - 1)
  W_ge_one : ∀ q, 1 ≤ W q
  A : ℝ
  A_nonneg : 0 ≤ A
  B : ℝ
  small : B ≤ c / 4
  op_bound : ∀ u, ‖V u‖ ≤ A * ‖u‖ + B * ‖wMul W u‖

namespace RegHamP

variable {ι : Type*} [Fintype ι] (H : RegHamP ι)

/-- The Hamiltonian. -/
noncomputable def op : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι := wMul H.kin + H.V

lemma kin_nonneg (q : ι) : 0 ≤ H.kin q := by
  rw [H.kin_eq]
  have h1 := H.W_ge_one q
  have h2 := H.c_pos
  have : 0 ≤ H.W q - 1 := by linarith
  positivity

lemma wMul_W_eq (u : EuclideanSpace ℂ ι) :
    wMul H.W u = u + ((1 / H.c : ℝ) : ℂ) • wMul H.kin u := by
  have hc : H.c ≠ 0 := H.c_pos.ne'
  ext q
  simp only [wMul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have e : (1 / H.c) * H.kin q = H.W q - 1 := by
    rw [H.kin_eq]
    field_simp
  have e' : ((1 / H.c : ℝ) : ℂ) * ((H.kin q : ℂ) * u q) = ((H.W q - 1 : ℝ) : ℂ) * u q := by
    rw [← mul_assoc, ← Complex.ofReal_mul, e]
  rw [e']
  push_cast
  ring

/-- Elliptic estimate for normalised eigenvectors. -/
lemma elliptic (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) (E : ℝ)
    (hE : H.op u = (E : ℂ) • u) :
    ‖wMul H.W u‖ ≤ 4 / 3 * (1 + (|E| + H.A) / H.c) := by
  have hc := H.c_pos
  have hc0 : H.c ≠ 0 := hc.ne'
  have hkin : wMul H.kin u = (E : ℂ) • u - H.V u := by
    have : wMul H.kin u + H.V u = (E : ℂ) • u := hE
    rw [← this]; abel
  have h1 : ‖wMul H.kin u‖ ≤ |E| + ‖H.V u‖ := by
    rw [hkin]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hV := H.op_bound u
  rw [hu, mul_one] at hV
  have h2 : ‖wMul H.W u‖ ≤ 1 + 1 / H.c * ‖wMul H.kin u‖ := by
    rw [H.wMul_W_eq u]
    refine (norm_add_le _ _).trans ?_
    rw [hu, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hX := norm_nonneg (wMul H.W u)
  have hBX : H.B * ‖wMul H.W u‖ ≤ H.c / 4 * ‖wMul H.W u‖ :=
    mul_le_mul_of_nonneg_right H.small hX
  have h3 : ‖wMul H.W u‖ ≤ 1 + 1 / H.c * (|E| + H.A + H.c / 4 * ‖wMul H.W u‖) := by
    have : ‖wMul H.kin u‖ ≤ |E| + H.A + H.c / 4 * ‖wMul H.W u‖ := by linarith
    calc ‖wMul H.W u‖ ≤ 1 + 1 / H.c * ‖wMul H.kin u‖ := h2
      _ ≤ 1 + 1 / H.c * (|E| + H.A + H.c / 4 * ‖wMul H.W u‖) := by gcongr
  have e : 1 / H.c * (|E| + H.A + H.c / 4 * ‖wMul H.W u‖) =
      (|E| + H.A) / H.c + ‖wMul H.W u‖ / 4 := by
    field_simp
  rw [e] at h3
  linarith

/-- Lower bound on any eigenvalue with a normalised eigenvector. -/
lemma eigen_lower (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) (E : ℝ)
    (hE : H.op u = (E : ℂ) • u) :
    -(2 * H.A + H.c / 2) ≤ E := by
  have hc := H.c_pos
  have hc0 : H.c ≠ 0 := hc.ne'
  have hEre : (inner ℂ u (H.op u)).re = E := by
    rw [hE, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
    simp
  have hsplit : (inner ℂ u (H.op u)).re =
      (inner ℂ u (wMul H.kin u)).re + (inner ℂ u (H.V u)).re := by
    simp only [op, LinearMap.add_apply, inner_add_right, Complex.add_re]
  have hkin := re_inner_wMul_nonneg H.kin H.kin_nonneg u
  have hVre : -‖H.V u‖ ≤ (inner ℂ u (H.V u)).re := by
    have := (Complex.abs_re_le_norm (inner ℂ u (H.V u))).trans (norm_inner_le_norm u (H.V u))
    rw [hu, one_mul] at this
    linarith [neg_abs_le (inner ℂ u (H.V u)).re]
  have hV := H.op_bound u
  rw [hu, mul_one] at hV
  have hell := H.elliptic u hu E hE
  have hA := H.A_nonneg
  have hX := norm_nonneg (wMul H.W u)
  have hVle : ‖H.V u‖ ≤ H.A + H.c / 3 + (|E| + H.A) / 3 := by
    have h1 : H.B * ‖wMul H.W u‖ ≤ H.c / 4 * ‖wMul H.W u‖ :=
      mul_le_mul_of_nonneg_right H.small hX
    have h2 : H.c / 4 * ‖wMul H.W u‖ ≤ H.c / 4 * (4 / 3 * (1 + (|E| + H.A) / H.c)) :=
      mul_le_mul_of_nonneg_left hell (by positivity)
    have h3 : H.c / 4 * (4 / 3 * (1 + (|E| + H.A) / H.c)) = H.c / 3 + (|E| + H.A) / 3 := by
      field_simp
    linarith
  by_cases hEn : 0 ≤ E
  · have : 0 ≤ 2 * H.A + H.c / 2 := by positivity
    linarith
  · push Not at hEn
    rw [abs_of_neg hEn] at hVle
    linarith

end RegHamP

end SpectralP

/-! ## The constants, uniform in `L` -/

section ConstantsP

/-- The splitting radius of the elliptic estimate with the physical weight. -/
noncomputable def J0P (Z g : ℝ) : ℕ := Nat.ceil (1664 * sobP g * Z ^ 2) + 1

lemma J0P_pos (Z g : ℝ) : 1 ≤ J0P Z g := by
  unfold J0P; omega

lemma J0P_small {Z g : ℝ} (hZ : 0 ≤ Z) (hg : 0 < g) :
    Z * Real.sqrt (26 * sobP g / J0P Z g) ≤ 1 / 8 := by
  set J : ℕ := J0P Z g with hJdef
  have hJ : (0 : ℝ) < J := by exact_mod_cast J0P_pos Z g
  have hS := (sobP_pos hg).le
  have hJge : 1664 * sobP g * Z ^ 2 ≤ (J : ℝ) := by
    rw [hJdef]
    unfold J0P
    push_cast
    linarith [Nat.le_ceil (1664 * sobP g * Z ^ 2)]
  have key : Z ^ 2 * (26 * sobP g / J) ≤ (1 / 8) ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ hJ]
    nlinarith
  calc Z * Real.sqrt (26 * sobP g / J) = Real.sqrt (Z ^ 2 * (26 * sobP g / J)) := by
        rw [Real.sqrt_mul (sq_nonneg Z), Real.sqrt_sq hZ]
    _ ≤ Real.sqrt ((1 / 8) ^ 2) := Real.sqrt_le_sqrt key
    _ = 1 / 8 := Real.sqrt_sq (by norm_num)

lemma J0P_le {Z g : ℝ} (hg : 0 < g) : (J0P Z g : ℝ) ≤ 1664 * sobP g * Z ^ 2 + 2 := by
  have hS := (sobP_pos hg).le
  have h0 : 0 ≤ 1664 * sobP g * Z ^ 2 := by positivity
  unfold J0P
  push_cast
  linarith [Nat.ceil_lt_add_one h0]

lemma nonneg_of_le_mul {Z z g : ℝ} (hZ : 0 ≤ Z) (hg : 0 < g) (hz : Z ≤ z * g) : 0 ≤ z := by
  by_contra h
  push Not at h
  have : z * g < 0 := mul_neg_of_neg_of_pos h hg
  linarith

/-- The low-transfer part of the operator bound is uniform: `26 Z J₀ ≤ 43264 σ z³ + 52 z g`. -/
lemma J0P_A_le {Z g z σ : ℝ} (hZ : 0 ≤ Z) (hg : 0 < g) (hz : Z ≤ z * g)
    (hσ : g ^ 3 + 78 ≤ σ) :
    26 * Z * (J0P Z g : ℝ) ≤ 43264 * σ * z ^ 3 + 52 * z * g := by
  have hJ := J0P_le (Z := Z) hg
  have hS0 := (sobP_pos hg).le
  have hz0 := nonneg_of_le_mul hZ hg hz
  have hZ3 : Z ^ 3 ≤ (z * g) ^ 3 := pow_le_pow_left₀ hZ hz 3
  have h1 : 26 * Z * (J0P Z g : ℝ) ≤ 26 * Z * (1664 * sobP g * Z ^ 2 + 2) :=
    mul_le_mul_of_nonneg_left hJ (by positivity)
  have h2 : sobP g * Z ^ 3 ≤ σ * z ^ 3 := by
    calc sobP g * Z ^ 3 ≤ sobP g * (z * g) ^ 3 := mul_le_mul_of_nonneg_left hZ3 hS0
      _ = (sobP g * g ^ 3) * z ^ 3 := by ring
      _ = (g ^ 3 + 78) * z ^ 3 := by rw [sobP_mul_cube hg]
      _ ≤ σ * z ^ 3 := mul_le_mul_of_nonneg_right hσ (by positivity)
  nlinarith

/-- Elliptic constant: `‖wMP u‖ ≤ EllU A |E|` for a normalised eigenvector. -/
noncomputable def EllU (A x : ℝ) : ℝ := 4 / 3 * (1 + 2 * (x + A))

/-- Tail-bootstrap constant: `τ ≤ CbootU ‖wTotP u‖ / K^{5/2}`. -/
noncomputable def CbootU (z σ : ℝ) : ℝ := z * (208 + 4 * Real.sqrt (104 * σ))

/-- Form-error constant: error `≤ CformU ‖wTotP u‖² / K³`. -/
noncomputable def CformU (z σ : ℝ) : ℝ :=
  z * (36 * Real.sqrt σ * CbootU z σ + 416 * CbootU z σ ^ 2)

/-- A common bound for the Galerkin and grid ground energies; `M` is the largest mass. -/
noncomputable def EbigU (M z σ A Eb : ℝ) : ℝ :=
  max (2 * A + 1 / 4) (Eb + CformU z σ * (M * EllU A Eb) ^ 2)

/-- The comparison constant. -/
noncomputable def CgridU (M z σ A Eb : ℝ) : ℝ :=
  CformU z σ * (M * EllU A (EbigU M z σ A Eb)) ^ 2

lemma EllU_nonneg {A x : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x) : 0 ≤ EllU A x := by
  unfold EllU; positivity

lemma EllU_mono {A x y : ℝ} (hxy : x ≤ y) : EllU A x ≤ EllU A y := by
  unfold EllU; linarith

lemma CbootU_nonneg {z σ : ℝ} (hz : 0 ≤ z) : 0 ≤ CbootU z σ := by
  unfold CbootU; positivity

lemma CformU_nonneg {z σ : ℝ} (hz : 0 ≤ z) : 0 ≤ CformU z σ := by
  unfold CformU
  have := CbootU_nonneg (σ := σ) hz
  positivity

/-- `g √(g T) = √(g³ T)`. -/
lemma mul_sqrt_eq {g T : ℝ} (hg : 0 ≤ g) : g * Real.sqrt (g * T) = Real.sqrt (g ^ 3 * T) := by
  rw [show g ^ 3 * T = g ^ 2 * (g * T) by ring, Real.sqrt_mul (sq_nonneg g), Real.sqrt_sq hg]

/-- Simplification of the tail bootstrap with `J = T/2`, physical weight. -/
lemma boot_arithP {Z g X z σ : ℝ} (hZ : 0 ≤ Z) (hg : 0 < g) (hX : 0 ≤ X) (hz : Z ≤ z * g)
    (hσ : g ^ 3 + 78 ≤ σ) {T : ℕ} (hT : 2 ≤ T) (hK : 1 ≤ g * T) :
    (Z * (26 * ((T / 2 : ℕ) : ℝ)) * (X / (1 + g ^ 2 * (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2)) +
        Z * Real.sqrt (26 * sobP g / ((T / 2 : ℕ) : ℝ)) * X) / (g ^ 2 / 4 * ((T : ℝ) + 1) ^ 2) ≤
      CbootU z σ * X / ((g * T) ^ 2 * Real.sqrt (g * T)) := by
  set J : ℕ := T / 2 with hJdef
  have hJ1 : 1 ≤ J := by omega
  have h2J : 2 * J ≤ T := by omega
  have h4J : T ≤ 4 * J := by omega
  have hJT : J ≤ T := by omega
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have hJ0 : (0 : ℝ) < J := by linarith
  have h2Jr : 2 * (J : ℝ) ≤ T := by exact_mod_cast h2J
  have h4Jr : (T : ℝ) ≤ 4 * J := by exact_mod_cast h4J
  have hsub : ((T - J : ℕ) : ℝ) = (T : ℝ) - J := by push_cast [Nat.cast_sub hJT]; ring
  have hz0 := nonneg_of_le_mul hZ hg hz
  have hS0 : 0 ≤ sobP g := (sobP_pos hg).le
  have hg0 : g ≠ 0 := hg.ne'
  have hT0' : (T : ℝ) ≠ 0 := hT0.ne'
  -- the first term: `≤ 52 Z X / (g² T)`
  have hden : g ^ 2 * (T : ℝ) ^ 2 / 4 ≤ 1 + g ^ 2 * (((T - J : ℕ) : ℝ) + 1) ^ 2 := by
    rw [hsub]
    have h1 : (T : ℝ) / 2 ≤ (T : ℝ) - J + 1 := by linarith
    have h2 : ((T : ℝ) / 2) ^ 2 ≤ ((T : ℝ) - J + 1) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg g)
    have e : g ^ 2 * ((T : ℝ) / 2) ^ 2 = g ^ 2 * (T : ℝ) ^ 2 / 4 := by ring
    linarith
  have t1 : Z * (26 * (J : ℝ)) * (X / (1 + g ^ 2 * (((T - J : ℕ) : ℝ) + 1) ^ 2)) ≤
      52 * Z * X / (g ^ 2 * T) := by
    have hpos : 0 < g ^ 2 * (T : ℝ) ^ 2 / 4 := by positivity
    have hdiv : X / (1 + g ^ 2 * (((T - J : ℕ) : ℝ) + 1) ^ 2) ≤ X / (g ^ 2 * (T : ℝ) ^ 2 / 4) :=
      div_le_div_of_nonneg_left hX hpos hden
    have e1 : Z * (26 * (J : ℝ)) * (X / (g ^ 2 * (T : ℝ) ^ 2 / 4)) =
        104 * Z * X * J / (g ^ 2 * (T : ℝ) ^ 2) := by
      field_simp
      ring
    have e2 : 52 * Z * X / (g ^ 2 * T) = 52 * Z * X * T / (g ^ 2 * (T : ℝ) ^ 2) := by
      field_simp
    calc Z * (26 * (J : ℝ)) * (X / (1 + g ^ 2 * (((T - J : ℕ) : ℝ) + 1) ^ 2))
        ≤ Z * (26 * (J : ℝ)) * (X / (g ^ 2 * (T : ℝ) ^ 2 / 4)) := by gcongr
      _ = 104 * Z * X * J / (g ^ 2 * (T : ℝ) ^ 2) := e1
      _ ≤ 52 * Z * X * T / (g ^ 2 * (T : ℝ) ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [mul_nonneg hZ hX]
      _ = 52 * Z * X / (g ^ 2 * T) := e2.symm
  -- the second term: `J ≥ T/4`
  have t2 : Z * Real.sqrt (26 * sobP g / (J : ℝ)) * X ≤
      Z * Real.sqrt (104 * sobP g / T) * X := by
    have hq : Real.sqrt (26 * sobP g / (J : ℝ)) ≤ Real.sqrt (104 * sobP g / T) := by
      apply Real.sqrt_le_sqrt
      rw [div_le_div_iff₀ hJ0 hT0]
      nlinarith [mul_le_mul_of_nonneg_left h4Jr hS0]
    gcongr
  have hnum := add_le_add t1 t2
  have hdenle : g ^ 2 / 4 * (T : ℝ) ^ 2 ≤ g ^ 2 / 4 * ((T : ℝ) + 1) ^ 2 := by
    gcongr; linarith
  have hstep := div_le_div₀ (by positivity) hnum (by positivity) hdenle
  have e3 : (52 * Z * X / (g ^ 2 * T) + Z * Real.sqrt (104 * sobP g / T) * X) /
      (g ^ 2 / 4 * (T : ℝ) ^ 2) = 208 * Z * X / (g ^ 4 * (T : ℝ) ^ 3) +
        4 * Z * Real.sqrt (104 * sobP g / T) * X / (g ^ 2 * (T : ℝ) ^ 2) := by
    field_simp
    ring
  -- the uniform bounds
  have hK0 : 0 < g * T := by positivity
  have hsK : 0 < Real.sqrt (g * T) := Real.sqrt_pos.mpr hK0
  have hsK_le : Real.sqrt (g * T) ≤ g * T := by
    rw [Real.sqrt_le_left hK0.le]; nlinarith
  have i1 : 208 * Z * X / (g ^ 4 * (T : ℝ) ^ 3) ≤
      208 * z * X / ((g * T) ^ 2 * Real.sqrt (g * T)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Z * Real.sqrt (g * T) ≤ z * g * (g * T) :=
      calc Z * Real.sqrt (g * T) ≤ (z * g) * Real.sqrt (g * T) :=
            mul_le_mul_of_nonneg_right hz hsK.le
        _ ≤ (z * g) * (g * T) := mul_le_mul_of_nonneg_left hsK_le (hZ.trans hz)
    have h2 := mul_le_mul_of_nonneg_left h1
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 208) hX) (sq_nonneg (g * T)))
    have e : 208 * X * (g * T) ^ 2 * (z * g * (g * T)) = 208 * z * X * (g ^ 4 * (T : ℝ) ^ 3) := by
      ring
    have e' : 208 * X * (g * T) ^ 2 * (Z * Real.sqrt (g * T)) =
        208 * Z * X * ((g * T) ^ 2 * Real.sqrt (g * T)) := by ring
    linarith [h2, e, e']
  have hkey : Real.sqrt (104 * sobP g / T) * (g * Real.sqrt (g * T)) ≤ Real.sqrt (104 * σ) := by
    rw [mul_sqrt_eq hg.le, ← Real.sqrt_mul (div_nonneg (mul_nonneg (by norm_num) hS0) hT0.le)]
    apply Real.sqrt_le_sqrt
    have e : 104 * sobP g / T * (g ^ 3 * T) = 104 * (sobP g * g ^ 3) := by
      field_simp
    rw [e, sobP_mul_cube hg]
    linarith
  have i2 : 4 * Z * Real.sqrt (104 * sobP g / T) * X / (g ^ 2 * (T : ℝ) ^ 2) ≤
      4 * z * Real.sqrt (104 * σ) * X / ((g * T) ^ 2 * Real.sqrt (g * T)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : Z * Real.sqrt (104 * sobP g / T) * Real.sqrt (g * T) ≤ z * Real.sqrt (104 * σ) := by
      calc Z * Real.sqrt (104 * sobP g / T) * Real.sqrt (g * T)
          ≤ (z * g) * Real.sqrt (104 * sobP g / T) * Real.sqrt (g * T) := by gcongr
        _ = z * (Real.sqrt (104 * sobP g / T) * (g * Real.sqrt (g * T))) := by ring
        _ ≤ z * Real.sqrt (104 * σ) := mul_le_mul_of_nonneg_left hkey hz0
    have h2 := mul_le_mul_of_nonneg_left h1
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hX) (sq_nonneg (g * T)))
    have e : 4 * X * (g * T) ^ 2 * (z * Real.sqrt (104 * σ)) =
        4 * z * Real.sqrt (104 * σ) * X * (g ^ 2 * (T : ℝ) ^ 2) := by ring
    have e' : 4 * X * (g * T) ^ 2 * (Z * Real.sqrt (104 * sobP g / T) * Real.sqrt (g * T)) =
        4 * Z * Real.sqrt (104 * sobP g / T) * X * ((g * T) ^ 2 * Real.sqrt (g * T)) := by ring
    linarith [h2, e, e']
  calc _ ≤ (52 * Z * X / (g ^ 2 * T) + Z * Real.sqrt (104 * sobP g / T) * X) /
        (g ^ 2 / 4 * (T : ℝ) ^ 2) := hstep
    _ = 208 * Z * X / (g ^ 4 * (T : ℝ) ^ 3) +
        4 * Z * Real.sqrt (104 * sobP g / T) * X / (g ^ 2 * (T : ℝ) ^ 2) := e3
    _ ≤ 208 * z * X / ((g * T) ^ 2 * Real.sqrt (g * T)) +
        4 * z * Real.sqrt (104 * σ) * X / ((g * T) ^ 2 * Real.sqrt (g * T)) := add_le_add i1 i2
    _ = CbootU z σ * X / ((g * T) ^ 2 * Real.sqrt (g * T)) := by
        unfold CbootU; ring

/-- `formAP a s m ≤ 18 √S / √s` for `1 ≤ s ≤ m`. -/
lemma formAP_le {a : ℝ} (ha : 0 < a) {s m : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m) :
    formAP a s m ≤ 18 * Real.sqrt (sobP a) / Real.sqrt s := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsmr : (s : ℝ) ≤ m := by exact_mod_cast hsm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hs0 hsmr
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hS0 : 0 ≤ sobP a := (sobP_pos ha).le
  have hSS : 0 ≤ Real.sqrt (sobP a) := Real.sqrt_nonneg _
  have a1 : Real.sqrt (26 * sobP a / (2 * (s : ℝ))) ≤
      361 / 100 * Real.sqrt (sobP a) / Real.sqrt s := by
    rw [le_div_iff₀ hss,
      ← Real.sqrt_mul (div_nonneg (mul_nonneg (by norm_num) hS0) (by positivity))]
    have e2 : 361 / 100 * Real.sqrt (sobP a) = Real.sqrt ((361 / 100) ^ 2 * sobP a) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [e2]
    apply Real.sqrt_le_sqrt
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hS0 hs0.le]
  have a2 : Real.sqrt (26 * sobP a / (m : ℝ)) ≤ 51 / 10 * Real.sqrt (sobP a) / Real.sqrt s := by
    rw [le_div_iff₀ hss, ← Real.sqrt_mul (div_nonneg (mul_nonneg (by norm_num) hS0) hm0.le)]
    have e2 : 51 / 10 * Real.sqrt (sobP a) = Real.sqrt ((51 / 10) ^ 2 * sobP a) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    rw [e2]
    apply Real.sqrt_le_sqrt
    rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
    nlinarith [mul_le_mul_of_nonneg_left hsmr hS0, mul_nonneg hS0 hm0.le]
  unfold formAP
  have e : 2 * (361 / 100 * Real.sqrt (sobP a) / Real.sqrt s) +
      2 * (51 / 10 * Real.sqrt (sobP a) / Real.sqrt s) =
        1742 / 100 * Real.sqrt (sobP a) / Real.sqrt s := by ring
  have h18 : 1742 / 100 * Real.sqrt (sobP a) / Real.sqrt s ≤
      18 * Real.sqrt (sobP a) / Real.sqrt s := by
    apply div_le_div_of_nonneg_right _ hss.le
    nlinarith
  linarith

/-- The coupling times the form constant: `Z_q formAP ≤ 18 z √σ / √K`, `K = a s`. -/
lemma coupling_formAP_le {a Zq z σ : ℝ} (ha : 0 < a) (hZq : 0 ≤ Zq) (hz : Zq ≤ z * a)
    (hσ : a ^ 3 + 78 ≤ σ) {s m : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m) :
    Zq * formAP a s m ≤ 18 * z * Real.sqrt σ / Real.sqrt (a * s) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hS0 : 0 ≤ sobP a := (sobP_pos ha).le
  have hz0 := nonneg_of_le_mul hZq ha hz
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have has : 0 < Real.sqrt (a * s) := Real.sqrt_pos.mpr (by positivity)
  have hσ0 : 0 ≤ σ := le_trans (by positivity) hσ
  have h1 := formAP_le ha hs hsm
  have h2 : Zq * formAP a s m ≤ (z * a) * (18 * Real.sqrt (sobP a) / Real.sqrt s) :=
    mul_le_mul hz h1 (formAP_nonneg a s m) (by positivity)
  refine h2.trans ?_
  have key : a * Real.sqrt (sobP a) * Real.sqrt (a * s) ≤ Real.sqrt σ * Real.sqrt s := by
    have e1 : a * Real.sqrt (sobP a) * Real.sqrt (a * s) = Real.sqrt (sobP a * a ^ 3 * s) := by
      rw [show sobP a * a ^ 3 * s = a ^ 2 * (sobP a * (a * s)) by ring,
        Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le, Real.sqrt_mul hS0]
      ring
    have e2 : Real.sqrt σ * Real.sqrt s = Real.sqrt (σ * s) := (Real.sqrt_mul hσ0 s).symm
    rw [e1, e2, sobP_mul_cube ha]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hσ hs0.le)
  have key2 : a * Real.sqrt (sobP a) / Real.sqrt s ≤ Real.sqrt σ / Real.sqrt (a * s) := by
    rw [div_le_div_iff₀ hss has]
    exact key
  calc (z * a) * (18 * Real.sqrt (sobP a) / Real.sqrt s) =
        18 * z * (a * Real.sqrt (sobP a) / Real.sqrt s) := by ring
    _ ≤ 18 * z * (Real.sqrt σ / Real.sqrt (a * s)) := by gcongr
    _ = 18 * z * Real.sqrt σ / Real.sqrt (a * s) := by ring

/-- Simplification of the form error with tails bootstrapped at the threshold `s`, physical
weight: the error is `≤ CformU X² / K³`, `K = g s ≥ 1`. -/
lemma form_arithP {g Zq z σ X τ : ℝ} (hg : 0 < g) (hZq : 0 ≤ Zq) (hz : Zq ≤ z * g)
    (hσ : g ^ 3 + 78 ≤ σ) (hX : 0 ≤ X) (hτ0 : 0 ≤ τ) {s m : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    (hms : m ≤ 8 * s) (hK : 1 ≤ g * s)
    (hτ : τ ≤ CbootU z σ * X / ((g * s) ^ 2 * Real.sqrt (g * s))) :
    Zq * (formAP g s m * (τ * X + τ * X) + 52 * m * (τ * τ)) ≤
      CformU z σ * X ^ 2 / (g * s) ^ 3 := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hmsr : (m : ℝ) ≤ 8 * s := by exact_mod_cast hms
  have hz0 := nonneg_of_le_mul hZq hg hz
  have hK0 : 0 < g * s := by linarith
  have hsK : 0 < Real.sqrt (g * s) := Real.sqrt_pos.mpr hK0
  have hsK2 : Real.sqrt (g * s) * Real.sqrt (g * s) = g * s := Real.mul_self_sqrt hK0.le
  have hCb0 : 0 ≤ CbootU z σ := CbootU_nonneg hz0
  have hA := coupling_formAP_le hg hZq hz hσ hs hsm
  have hA0 := formAP_nonneg g s m
  have p1 : Zq * (formAP g s m * (τ * X + τ * X)) ≤
      36 * z * Real.sqrt σ * CbootU z σ * X ^ 2 / (g * s) ^ 3 := by
    calc Zq * (formAP g s m * (τ * X + τ * X)) = 2 * (Zq * formAP g s m) * τ * X := by ring
      _ ≤ 2 * (18 * z * Real.sqrt σ / Real.sqrt (g * s)) *
            (CbootU z σ * X / ((g * s) ^ 2 * Real.sqrt (g * s))) * X := by gcongr
      _ = 36 * z * Real.sqrt σ * CbootU z σ * X ^ 2 /
            ((g * s) ^ 2 * (Real.sqrt (g * s) * Real.sqrt (g * s))) := by ring
      _ = 36 * z * Real.sqrt σ * CbootU z σ * X ^ 2 / (g * s) ^ 3 := by rw [hsK2]; ring
  have p2 : Zq * (52 * m * (τ * τ)) ≤ 416 * z * CbootU z σ ^ 2 * X ^ 2 / (g * s) ^ 3 := by
    have hτ2 : τ * τ ≤ (CbootU z σ * X / ((g * s) ^ 2 * Real.sqrt (g * s))) ^ 2 := by
      rw [← sq]; exact pow_le_pow_left₀ hτ0 hτ 2
    have e : (CbootU z σ * X / ((g * s) ^ 2 * Real.sqrt (g * s))) ^ 2 =
        CbootU z σ ^ 2 * X ^ 2 / (g * s) ^ 5 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hK0.le]; ring
    rw [e] at hτ2
    have hZm : Zq * (52 * m) ≤ 416 * z * (g * s) := by
      have : Zq * m ≤ (z * g) * (8 * s) := mul_le_mul hz hmsr (by positivity) (by positivity)
      nlinarith
    have hK4 : (g * s) ^ 3 ≤ (g * s) ^ 4 := by
      calc (g * s) ^ 3 = (g * s) ^ 3 * 1 := by ring
        _ ≤ (g * s) ^ 3 * (g * s) := by gcongr
        _ = (g * s) ^ 4 := by ring
    calc Zq * (52 * m * (τ * τ)) = (Zq * (52 * m)) * (τ * τ) := by ring
      _ ≤ (416 * z * (g * s)) * (CbootU z σ ^ 2 * X ^ 2 / (g * s) ^ 5) := by gcongr
      _ = 416 * z * CbootU z σ ^ 2 * X ^ 2 / (g * s) ^ 4 := by
          field_simp
      _ ≤ 416 * z * CbootU z σ ^ 2 * X ^ 2 / (g * s) ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hK4
  calc Zq * (formAP g s m * (τ * X + τ * X) + 52 * m * (τ * τ))
      = Zq * (formAP g s m * (τ * X + τ * X)) + Zq * (52 * m * (τ * τ)) := by ring
    _ ≤ 36 * z * Real.sqrt σ * CbootU z σ * X ^ 2 / (g * s) ^ 3 +
          416 * z * CbootU z σ ^ 2 * X ^ 2 / (g * s) ^ 3 := add_le_add p1 p2
    _ = CformU z σ * X ^ 2 / (g * s) ^ 3 := by unfold CformU; ring

end ConstantsP

/-! ## The finite comparison theorem in physical units -/

section MainP

variable {ν : Type*} [Fintype ν] {eta m : ℕ} {P : RegParticles eta} {D : NucData ν}
  {gamma : ℝ} {κ : Lat3 → ℝ} {g : ℝ}

/-- An operator bound with the weight `wTotP` gives one with `wMP` and the coupling multiplied
by the largest mass. -/
lemma op_bound_massP (P : RegParticles eta) (a : ℝ) {X : EuclideanSpace ℂ (RCfg eta m)}
    (u : EuclideanSpace ℂ (RCfg eta m)) {Zq : ℝ} (hZ : 0 ≤ Zq) (J : ℕ) (S : ℝ)
    (h : ‖X‖ ≤ Zq * (26 * J) * ‖u‖ + Zq * Real.sqrt (26 * S / J) * ‖wMul (wTotP a) u‖) :
    ‖X‖ ≤ (P.maxMass * Zq) * (26 * J) * ‖u‖ +
      (P.maxMass * Zq) * Real.sqrt (26 * S / J) * ‖wMul (wMP P a) u‖ := by
  have hM := P.one_le_maxMass
  have hW := norm_wMul_wTotP_le P a u
  have h0 : 0 ≤ Zq * (26 * J) * ‖u‖ := by positivity
  have h1 : Zq * (26 * J) * ‖u‖ ≤ (P.maxMass * Zq) * (26 * J) * ‖u‖ :=
    calc Zq * (26 * J) * ‖u‖ = 1 * (Zq * (26 * J) * ‖u‖) := by ring
      _ ≤ P.maxMass * (Zq * (26 * J) * ‖u‖) := mul_le_mul_of_nonneg_right hM h0
      _ = (P.maxMass * Zq) * (26 * J) * ‖u‖ := by ring
  have hs : 0 ≤ Zq * Real.sqrt (26 * S / J) := by positivity
  have h2 : Zq * Real.sqrt (26 * S / J) * ‖wMul (wTotP a) u‖ ≤
      (P.maxMass * Zq) * Real.sqrt (26 * S / J) * ‖wMul (wMP P a) u‖ :=
    calc Zq * Real.sqrt (26 * S / J) * ‖wMul (wTotP a) u‖
        ≤ Zq * Real.sqrt (26 * S / J) * (P.maxMass * ‖wMul (wMP P a) u‖) :=
          mul_le_mul_of_nonneg_left hW hs
      _ = (P.maxMass * Zq) * Real.sqrt (26 * S / J) * ‖wMul (wMP P a) u‖ := by ring
  linarith

lemma A_nonneg_of_le (hgamma : 0 ≤ gamma) (A : ℝ)
    (hA : 26 * (P.maxMass * Zc P D gamma) * (J0P (P.maxMass * Zc P D gamma) g : ℝ) ≤ A) :
    0 ≤ A :=
  le_trans (mul_nonneg (mul_nonneg (by norm_num)
    (mul_nonneg P.maxMass_pos.le (Zc_nonneg hgamma))) (Nat.cast_nonneg _)) hA

/-- The grid Hamiltonian as a register Hamiltonian with the physical weight `wMP g`. -/
noncomputable def gridRegHamP (hgamma : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hg : 0 < g) (A : ℝ)
    (hA : 26 * (P.maxMass * Zc P D gamma) * (J0P (P.maxMass * Zc P D gamma) g : ℝ) ≤ A) :
    RegHamP (RCfg eta m) where
  W := wMP P g
  kin := kinT eta m P g
  V := kOp (vGridK eta m P D κ)
  c := 1 / 2
  c_pos := by norm_num
  kin_eq := kinT_eq_wMP P g
  W_ge_one := wMP_ge_one P g
  A := A
  A_nonneg := A_nonneg_of_le hgamma A hA
  B := (P.maxMass * Zc P D gamma) *
    Real.sqrt (26 * sobP g / J0P (P.maxMass * Zc P D gamma) g)
  small := (J0P_small (mul_nonneg P.maxMass_pos.le (Zc_nonneg hgamma)) hg).trans (by norm_num)
  op_bound := fun u => by
    have h := op_bound_massP P g u (Zc_nonneg hgamma) (J0P (P.maxMass * Zc P D gamma) g)
      (sobP g) (vGridK_opP (P := P) (D := D) hg hgamma hκ _ (J0P_pos _ _) u)
    have h2 : (P.maxMass * Zc P D gamma) * (26 * (J0P (P.maxMass * Zc P D gamma) g : ℝ)) *
        ‖u‖ ≤ A * ‖u‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg u)
    linarith

/-- The Galerkin Hamiltonian as a register Hamiltonian with the physical weight. -/
noncomputable def galRegHamP (hgamma : 0 ≤ gamma) (hg : 0 < g) (A : ℝ)
    (hA : 26 * (P.maxMass * Zc P D gamma) * (J0P (P.maxMass * Zc P D gamma) g : ℝ) ≤ A) :
    RegHamP (RCfg eta m) where
  W := wMP P g
  kin := kinT eta m P g
  V := kOp (vGalK eta m P D gamma)
  c := 1 / 2
  c_pos := by norm_num
  kin_eq := kinT_eq_wMP P g
  W_ge_one := wMP_ge_one P g
  A := A
  A_nonneg := A_nonneg_of_le hgamma A hA
  B := (P.maxMass * Zc P D gamma) *
    Real.sqrt (26 * sobP g / J0P (P.maxMass * Zc P D gamma) g)
  small := (J0P_small (mul_nonneg P.maxMass_pos.le (Zc_nonneg hgamma)) hg).trans (by norm_num)
  op_bound := fun u => by
    have h := op_bound_massP P g u (Zc_nonneg hgamma) (J0P (P.maxMass * Zc P D gamma) g)
      (sobP g) (vGalK_opP (P := P) (D := D) hg hgamma _ (J0P_pos _ _) u)
    have h2 : (P.maxMass * Zc P D gamma) * (26 * (J0P (P.maxMass * Zc P D gamma) g : ℝ)) *
        ‖u‖ ≤ A * ‖u‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg u)
    linarith

/-- Tail bootstrap at the threshold `T` for a normalised eigenvector, physical weight:
`‖1_{High T} u‖ ≤ CbootU ‖wTotP u‖ / K^{5/2}`, `K = g T ≥ 1`. -/
lemma boot_tailP (hgamma : 0 ≤ gamma) (hg : 0 < g) {T : ℕ} (hT : 2 ≤ T) {z σ : ℝ}
    (hz : P.maxMass * Zc P D gamma ≤ z * g) (hσ : g ^ 3 + 78 ≤ σ) (hK : 1 ≤ g * T)
    (V : EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hVtail : ∀ (r : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)),
      ‖maskOp (High T r) (V u)‖ ≤
        Zc P D gamma * (26 * ((T / 2 : ℕ) : ℝ)) * ‖maskOp (High (T - T / 2) r) u‖ +
        Zc P D gamma * Real.sqrt (26 * sobP g / ((T / 2 : ℕ) : ℝ)) * ‖wMul (wTotP g) u‖)
    (u : EuclideanSpace ℂ (RCfg eta m)) (E : ℝ)
    (hE : (wMul (kinT eta m P g) + V) u = (E : ℂ) • u)
    (hEb : |E| ≤ g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2) (r : Fin eta) :
    ‖maskOp (High T r) u‖ ≤
      CbootU z σ * ‖wMul (wTotP g) u‖ / ((g * T) ^ 2 * Real.sqrt (g * T)) := by
  have hZ := Zc_nonneg (P := P) (D := D) hgamma
  have hM := P.maxMass_pos
  have hMZ : 0 ≤ P.maxMass * Zc P D gamma := mul_nonneg hM.le hZ
  have hb : 0 < g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2 := by positivity
  have h1 := tail_bootstrap (kinT eta m P g) V u E hE (High T r) hb
    (fun q hq => kinT_ge_of_high hg hq) hEb
  have hX := norm_nonneg (wMul (wTotP g) u)
  have hapri : ‖maskOp (High (T - T / 2) r) u‖ ≤
      ‖wMul (wTotP g) u‖ / (1 + g ^ 2 * (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2) :=
    norm_maskOp_le_wMul _ (wTotP g) (fun q => le_trans zero_le_one (wTotP_ge_one g q))
      (by positivity) (fun q hq => wTotP_ge_of_high g hq) u
  have h2 := hVtail r u
  have h3 : ‖maskOp (High T r) (V u)‖ ≤
      Zc P D gamma * (26 * ((T / 2 : ℕ) : ℝ)) *
          (‖wMul (wTotP g) u‖ / (1 + g ^ 2 * (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2)) +
        Zc P D gamma * Real.sqrt (26 * sobP g / ((T / 2 : ℕ) : ℝ)) * ‖wMul (wTotP g) u‖ := by
    have : 0 ≤ Zc P D gamma * (26 * ((T / 2 : ℕ) : ℝ)) := by positivity
    nlinarith
  calc ‖maskOp (High T r) u‖
      ≤ ‖maskOp (High T r) (V u)‖ / (g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2) := h1
    _ ≤ (Zc P D gamma * (26 * ((T / 2 : ℕ) : ℝ)) *
          (‖wMul (wTotP g) u‖ / (1 + g ^ 2 * (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2)) +
        Zc P D gamma * Real.sqrt (26 * sobP g / ((T / 2 : ℕ) : ℝ)) * ‖wMul (wTotP g) u‖) /
          (g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2) := by gcongr
    _ = ((P.maxMass * Zc P D gamma) * (26 * ((T / 2 : ℕ) : ℝ)) *
          (‖wMul (wTotP g) u‖ / (1 + g ^ 2 * (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2)) +
        (P.maxMass * Zc P D gamma) * Real.sqrt (26 * sobP g / ((T / 2 : ℕ) : ℝ)) *
          ‖wMul (wTotP g) u‖) / (g ^ 2 / 4 * ((T : ℝ) + 1) ^ 2) := by
        rw [show g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2 =
            (g ^ 2 / 4 * ((T : ℝ) + 1) ^ 2) / P.maxMass by ring, div_div_eq_mul_div]
        ring
    _ ≤ CbootU z σ * ‖wMul (wTotP g) u‖ / ((g * T) ^ 2 * Real.sqrt (g * T)) :=
        boot_arithP hMZ hg hX hz hσ hT hK

/-- Form error at a normalised eigenvector with tails bootstrapped at the threshold `s`. -/
lemma form_error_eigenP (hgamma : 0 ≤ gamma) (hg : 0 < g) {z σ : ℝ}
    (hz : P.maxMass * Zc P D gamma ≤ z * g) (hσ : g ^ 3 + 78 ≤ σ) {s : ℕ} (hs : 1 ≤ s)
    (hsm : s ≤ m) (hms : m ≤ 8 * s) (hK : 1 ≤ g * s) (hκ : GridKernel gamma D.ref s κ)
    (u : EuclideanSpace ℂ (RCfg eta m))
    (hτ : ∀ r, ‖maskOp (High s r) u‖ ≤
      CbootU z σ * ‖wMul (wTotP g) u‖ / ((g * s) ^ 2 * Real.sqrt (g * s))) :
    ‖inner ℂ u (Delta eta m P D gamma κ u)‖ ≤
      CformU z σ * ‖wMul (wTotP g) u‖ ^ 2 / (g * s) ^ 3 := by
  have hZ := Zc_nonneg (P := P) (D := D) hgamma
  have hM := P.one_le_maxMass
  have hZz : Zc P D gamma ≤ z * g := le_trans (le_mul_of_one_le_left hZ hM) hz
  have hz0 := nonneg_of_le_mul hZ hg hZz
  have hK0 : 0 < g * s := by linarith
  have hτ0 : 0 ≤ CbootU z σ * ‖wMul (wTotP g) u‖ / ((g * s) ^ 2 * Real.sqrt (g * s)) := by
    have := CbootU_nonneg (σ := σ) hz0
    positivity
  have h := Delta_formP (P := P) (D := D) hg hgamma hs hsm hκ u u hτ0 hτ0 hτ hτ
  exact h.trans (form_arithP hg hZ hZz hσ (norm_nonneg _) hτ0 hs hsm hms hK le_rfl)

/-- **Finite grid–Galerkin comparison in physical units.** On the padded register (radius
`2m`), for an even kernel `κ` with `|κ| ≤ γ/|ν|²` that agrees with the reference `γ ρ` on the box
`‖ν‖∞ ≤ 2s` (`2 ≤ s ≤ m ≤ 8s`), the grid and Galerkin Ritz energies in the exchange sector
`(sgn, lab)` differ by at most `CgridU / K³`, `K = g s`. The coupling enters through
`m̄ Z_c ≤ z g`, the Sobolev sum through `σ ≥ g³ + 78`; the constants depend on `m̄`, `z`, `σ`,
`A` and the energy budget `E_b` only. -/
theorem grid_galerkin_energyP (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ)
    (hP : ∀ a b, lab a = lab b → P.mass a = P.mass b ∧ P.charge a = P.charge b)
    (hgamma : 0 ≤ gamma) (hg : 0 < g) {s : ℕ} (hs : 2 ≤ s) (hsm : s ≤ m) (hms : m ≤ 8 * s)
    (hκ : GridKernel gamma D.ref s κ)
    (hNZ : ∃ u : EuclideanSpace ℂ (RCfg eta m), IsSec sgn lab u ∧ u ≠ 0)
    {z σ A : ℝ} (hz : P.maxMass * Zc P D gamma ≤ z * g) (hσ : g ^ 3 + 78 ≤ σ)
    (hA : 43264 * σ * z ^ 3 + 52 * z * g ≤ A)
    (Egal Eb : ℝ) (hEb : |Egal| ≤ Eb)
    (hGal : IsSecRitz sgn lab (Hgal eta m P D gamma g) Egal)
    (hbig : 4 * P.maxMass * EbigU P.maxMass z σ A Eb ≤ (g * s) ^ 2) :
    ∃ Egrid : ℝ, IsSecRitz sgn lab (Hgrid eta m P D κ g) Egrid ∧
      |Egrid - Egal| ≤ CgridU P.maxMass z σ A Eb / (g * s) ^ 3 := by
  have hM0 : 0 < P.maxMass := P.maxMass_pos
  have hM1 : 1 ≤ P.maxMass := P.one_le_maxMass
  have hZq : 0 ≤ Zc P D gamma := Zc_nonneg hgamma
  have hZ : 0 ≤ P.maxMass * Zc P D gamma := mul_nonneg hM0.le hZq
  have hz0 := nonneg_of_le_mul hZ hg hz
  have hAJ : 26 * (P.maxMass * Zc P D gamma) * (J0P (P.maxMass * Zc P D gamma) g : ℝ) ≤ A :=
    (J0P_A_le hZ hg hz hσ).trans hA
  have hA0 : 0 ≤ A := A_nonneg_of_le hgamma A hAJ
  have hs1 : 1 ≤ s := by omega
  set M := P.maxMass with hMdef
  -- `K = g s ≥ 1`
  have hEbig1 : 2 * A + 1 / 4 ≤ EbigU M z σ A Eb := le_max_left _ _
  have hK : 1 ≤ g * s := by
    have hq : (1 : ℝ) / 4 ≤ EbigU M z σ A Eb := by linarith
    have hq2 : EbigU M z σ A Eb ≤ M * EbigU M z σ A Eb :=
      le_mul_of_one_le_left (by linarith) hM1
    have h1 : 1 ≤ (g * s) ^ 2 := by linarith
    have hpos : 0 < g * s := by
      have : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
      positivity
    nlinarith
  have hK3 : (1 : ℝ) ≤ (g * s) ^ 3 := one_le_pow₀ hK
  set F := secSubmodule eta (2 * (2 * m) + 1) sgn lab
  have hNZ' : ∃ u, u ∈ F ∧ u ≠ 0 := hNZ
  -- ground eigenpairs
  obtain ⟨E2, u2, hu2F, hu2n, hu2E, hu2low⟩ := exists_ground_eigenpair_on_invariant'
    (Hgal eta m P D gamma g) Hgal_isSymmetric F (fun u hu => Hgal_sec hP u hu) hNZ'
  obtain ⟨E1, u1, hu1F, hu1n, hu1E, hu1low⟩ := exists_ground_eigenpair_on_invariant'
    (Hgrid eta m P D κ g) (Hgrid_isSymmetric hκ.even) F (fun u hu => Hgrid_sec hκ.even hP u hu)
    hNZ'
  obtain ⟨hLow, u', hu'F, hu'n, hu'v⟩ := hGal
  have hE2 : E2 = Egal := ritz_unique (Hgal eta m P D gamma g) {v | IsSec sgn lab v} E2 Egal
    (fun v hv => hu2low v hv) (fun v hv => hLow v hv) u2 u' hu2F hu'F hu2n hu'n
    (re_inner_eigen _ u2 hu2n E2 hu2E) hu'v
  subst hE2
  -- energy budget facts
  have hCf := CformU_nonneg (σ := σ) hz0
  have hEb0 : 0 ≤ Eb := (abs_nonneg _).trans hEb
  have hEll0 : 0 ≤ EllU A Eb := EllU_nonneg hA0 hEb0
  have hEbig2 : Eb + CformU z σ * (M * EllU A Eb) ^ 2 ≤ EbigU M z σ A Eb := le_max_right _ _
  have hEbEbig : Eb ≤ EbigU M z σ A Eb := by nlinarith [sq_nonneg (M * EllU A Eb)]
  have habs : ∀ x : ℝ, x ≤ EbigU M z σ A Eb → x ≤ g ^ 2 / (4 * M) * ((s : ℝ) + 1) ^ 2 := by
    intro x hx
    have h1 : (g * s) ^ 2 ≤ g ^ 2 * ((s : ℝ) + 1) ^ 2 := by
      rw [mul_pow]; gcongr; linarith
    have h2 : g ^ 2 / (4 * M) * ((s : ℝ) + 1) ^ 2 = g ^ 2 * ((s : ℝ) + 1) ^ 2 / (4 * M) := by
      ring
    rw [h2, le_div_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_right hx (by positivity : (0 : ℝ) ≤ 4 * M)]
  -- Galerkin ground state: elliptic, bootstrap and form error
  have hell2 := (galRegHamP (P := P) (D := D) (m := m) hgamma hg A hAJ).elliptic u2 hu2n E2 hu2E
  change ‖wMul (wMP P g) u2‖ ≤ 4 / 3 * (1 + (|E2| + A) / (1 / 2)) at hell2
  have hell2' : ‖wMul (wMP P g) u2‖ ≤ EllU A Eb := by
    refine hell2.trans ?_
    unfold EllU
    have e : (|E2| + A) / (1 / 2) = 2 * (|E2| + A) := by ring
    rw [e]
    linarith
  have hX2 : ‖wMul (wTotP g) u2‖ ≤ M * EllU A Eb :=
    (norm_wMul_wTotP_le P g u2).trans (mul_le_mul_of_nonneg_left hell2' hM0.le)
  have hboot2 : ∀ r, ‖maskOp (High s r) u2‖ ≤
      CbootU z σ * ‖wMul (wTotP g) u2‖ / ((g * s) ^ 2 * Real.sqrt (g * s)) := by
    intro r
    refine boot_tailP hgamma hg hs hz hσ hK (kOp (vGalK eta m P D gamma)) ?_ u2 E2 hu2E
      (habs _ (hEb.trans hEbEbig)) r
    intro r' u
    exact vGalK_tailP hg hgamma (s / 2) s (by omega) (Nat.div_le_self s 2) r' u
  have hform2 := form_error_eigenP hgamma hg hz hσ hs1 hsm hms hK hκ u2 hboot2
  have hX2sq : ‖wMul (wTotP g) u2‖ ^ 2 ≤ (M * EllU A Eb) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hX2 2
  have heps2 : ‖inner ℂ u2 (Delta eta m P D gamma κ u2)‖ ≤
      CformU z σ * (M * EllU A Eb) ^ 2 / (g * s) ^ 3 :=
    hform2.trans (by gcongr)
  -- grid ground energy bounds
  have hE1up : E1 ≤ E2 + ‖inner ℂ u2 (Delta eta m P D gamma κ u2)‖ := by
    have h := hu1low u2 hu2F
    rw [hu2n, one_pow, mul_one, Hgrid_eq (gamma := gamma), inner_add_right, Complex.add_re,
      re_inner_eigen _ u2 hu2n E2 hu2E] at h
    have := Complex.re_le_norm (inner ℂ u2 (Delta eta m P D gamma κ u2))
    linarith
  have hE1low :=
    (gridRegHamP (P := P) (D := D) (m := m) hgamma hκ.bound hg A hAJ).eigen_lower u1 hu1n E1 hu1E
  change -(2 * A + 1 / 2 / 2) ≤ E1 at hE1low
  have hE1abs : |E1| ≤ EbigU M z σ A Eb := by
    rw [abs_le]
    constructor
    · linarith
    · have h1 : CformU z σ * (M * EllU A Eb) ^ 2 / (g * s) ^ 3 ≤
          CformU z σ * (M * EllU A Eb) ^ 2 := div_le_self (by positivity) hK3
      have h2 : E2 ≤ Eb := (le_abs_self E2).trans hEb
      linarith
  -- grid ground state: elliptic, bootstrap and form error
  have hell1 :=
    (gridRegHamP (P := P) (D := D) (m := m) hgamma hκ.bound hg A hAJ).elliptic u1 hu1n E1 hu1E
  change ‖wMul (wMP P g) u1‖ ≤ 4 / 3 * (1 + (|E1| + A) / (1 / 2)) at hell1
  have hell1' : ‖wMul (wMP P g) u1‖ ≤ EllU A (EbigU M z σ A Eb) := by
    refine hell1.trans ?_
    unfold EllU
    have e : (|E1| + A) / (1 / 2) = 2 * (|E1| + A) := by ring
    rw [e]
    linarith
  have hX1 : ‖wMul (wTotP g) u1‖ ≤ M * EllU A (EbigU M z σ A Eb) :=
    (norm_wMul_wTotP_le P g u1).trans (mul_le_mul_of_nonneg_left hell1' hM0.le)
  have hboot1 : ∀ r, ‖maskOp (High s r) u1‖ ≤
      CbootU z σ * ‖wMul (wTotP g) u1‖ / ((g * s) ^ 2 * Real.sqrt (g * s)) := by
    intro r
    refine boot_tailP hgamma hg hs hz hσ hK (kOp (vGridK eta m P D κ)) ?_ u1 E1 hu1E
      (habs _ hE1abs) r
    intro r' u
    exact vGridK_tailP hg hgamma hκ.bound (s / 2) s (by omega) (Nat.div_le_self s 2) (by omega)
      r' u
  have hform1 := form_error_eigenP hgamma hg hz hσ hs1 hsm hms hK hκ u1 hboot1
  have hX1sq : ‖wMul (wTotP g) u1‖ ^ 2 ≤ (M * EllU A (EbigU M z σ A Eb)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hX1 2
  have hEllmono : (M * EllU A Eb) ^ 2 ≤ (M * EllU A (EbigU M z σ A Eb)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hM0.le hEll0)
      (mul_le_mul_of_nonneg_left (EllU_mono hEbEbig) hM0.le) 2
  have heps1 : ‖inner ℂ u1 (Delta eta m P D gamma κ u1)‖ ≤ CgridU M z σ A Eb / (g * s) ^ 3 := by
    unfold CgridU
    exact hform1.trans (by gcongr)
  have heps2' : ‖inner ℂ u2 (Delta eta m P D gamma κ u2)‖ ≤
      CgridU M z σ A Eb / (g * s) ^ 3 := by
    unfold CgridU
    exact heps2.trans (by gcongr)
  -- min--max
  refine ⟨E1, ⟨fun v hv => hu1low v hv, u1, hu1F, hu1n, re_inner_eigen _ u1 hu1n E1 hu1E⟩, ?_⟩
  exact ritz_compare (Hgrid eta m P D κ g) (Hgal eta m P D gamma g)
    (Delta eta m P D gamma κ) Hgrid_eq {v | IsSec sgn lab v} E1 E2
    (fun v hv => hu1low v hv) (fun v hv => hu2low v hv)
    u1 u2 hu1F hu2F hu1n hu2n (re_inner_eigen _ u1 hu1n E1 hu1E)
    (re_inner_eigen _ u2 hu2n E2 hu2E) heps1 heps2'

end MainP

end PlaneWaveGridG
