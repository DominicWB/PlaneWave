import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# `app:free`, part 4: the grid core with a general Galerkin reference kernel

A copy of the release file `PlaneWave.GridCore.lean` (namespace `PlaneWaveGridG` instead of
`PlaneWaveGrid`) in which the Galerkin reference coefficients `γ/|ν|²` are replaced by
`γ ρ(ν)` for a real, even reference kernel `ρ` with `|ρ| ≤ 1/|ν|²` (`NucData.ref`, `ref_neg`,
`ref_bound`). The release's core is the case `ρ = 1/|ν|²` (`PosNuclei.toNucData` uses it). The
only places where the release used the exact Coulomb coefficients were the norm identity of the
pair coefficient (now an inequality, `norm_kee_le`) and the agreement of the grid kernel with the
reference on the low box (`GridKernel.low`, `IsGridKernel.low`: `κ = γ ρ` there).

For the range-truncated kernel `g_L` of `app:free`, `γ ρ` is the Fourier coefficient `ĝ_L` (zero
mode left out) with `γ = (1 + V_θ)/(πL)` (`PlaneWave.FreeBoundary.RangeCut`, `rangecut`), and the grid kernel is its sharp
truncation `(ĝ_L)_{≤2K}` (`sharpKernel γ ρ m`).

Main results (namespace `PlaneWaveGridG`):
* `grid_galerkin_energy`: on the padded register (radius `2m`), the Ritz energies in the
  sector `(sgn, lab)` of the collocation Hamiltonian `Hgrid` of an even kernel `κ` with
  `|κ| ≤ γ/|ν|²` that agrees with `γ ρ` on the box `‖ν‖∞ ≤ 2s` (`GridKernel γ ρ s κ`) and of the
  Galerkin Hamiltonian `Hgal` of the reference coefficients `γ ρ` differ by at most `Cgrid / s³`,
  for `2 ≤ s ≤ m ≤ 8s` with `4 m̄ E_big ≤ g² s²`; a kernel of the class
  (`IsGridKernel γ ρ m κ`) qualifies with `s = ⌊m/4⌋`;
* `isSecRitz_Hpos_iff`, `Hpos_gridPermute`: as in the release (they do not involve `ρ`).
-/

/-! ════════════════════════════════════════════════════════════════════
## Part `Lattice`
════════════════════════════════════════════════════════════════════ -/

/-!
# Lattice sums for the truncated periodic Coulomb kernel

Elementary sums over the integer lattice `ℤ^3`, organised by sup-norm boxes:

* `∑_{0 < ‖ν‖∞ ≤ J} 1/|ν|² ≤ 26 J`  (`sum_coul_of_inBox`);
* `∑_{‖ν‖∞ > J} 1/|ν|⁴ ≤ 26/J`      (`sum_coul_sq_of_not_inBox`);
* `∑_ν (1+|ν|²)⁻² ≤ 53`              (`sum_sobolev_le`).

All three follow from the shell count `#{‖ν‖∞ = s} = 24 s² + 2 ≤ 26 s²`.
-/

set_option autoImplicit false

namespace PlaneWaveGridG

open Finset

/-- Integer reciprocal-lattice vectors in three dimensions. -/
abbrev Lat3 := Fin 3 → ℤ

/-- Squared Euclidean norm of a lattice vector (same expression as the release
file's `latticeNormSq`). -/
def nsq (nu : Lat3) : ℝ :=
  (nu (0 : Fin 3) : ℝ) ^ 2 +
  (nu (1 : Fin 3) : ℝ) ^ 2 +
  (nu (2 : Fin 3) : ℝ) ^ 2

lemma nsq_nonneg (nu : Lat3) : 0 ≤ nsq nu := by
  unfold nsq; positivity

lemma nsq_eq_sum (nu : Lat3) : nsq nu = ∑ c : Fin 3, ((nu c : ℤ) : ℝ) ^ 2 := by
  simp [nsq, Fin.sum_univ_three]

lemma sq_le_nsq (nu : Lat3) (c : Fin 3) : ((nu c : ℤ) : ℝ) ^ 2 ≤ nsq nu := by
  rw [nsq_eq_sum]
  exact Finset.single_le_sum (f := fun c => ((nu c : ℤ) : ℝ) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ c)

lemma nsq_neg (nu : Lat3) : nsq (-nu) = nsq nu := by
  simp [nsq]

lemma nsq_zero : nsq 0 = 0 := by
  simp [nsq]

/-- Unnormalised Coulomb coefficient `1/|ν|²`; it vanishes at the origin. -/
noncomputable def coul (nu : Lat3) : ℝ := 1 / nsq nu

lemma coul_nonneg (nu : Lat3) : 0 ≤ coul nu :=
  div_nonneg zero_le_one (nsq_nonneg nu)

lemma coul_neg (nu : Lat3) : coul (-nu) = coul nu := by
  simp [coul, nsq_neg]

lemma coul_zero : coul 0 = 0 := by
  simp [coul, nsq_zero]

/-- Sup-norm box membership `‖ν‖∞ ≤ J`. -/
def InBox (J : ℕ) (nu : Lat3) : Prop := ∀ c : Fin 3, |nu c| ≤ (J : ℤ)

instance (J : ℕ) (nu : Lat3) : Decidable (InBox J nu) := by
  unfold InBox; infer_instance

lemma InBox.mono {J J' : ℕ} (h : J ≤ J') {nu : Lat3} (hnu : InBox J nu) :
    InBox J' nu :=
  fun c => (hnu c).trans (by exact_mod_cast h)

lemma inBox_neg_iff {J : ℕ} {nu : Lat3} : InBox J (-nu) ↔ InBox J nu := by
  simp [InBox, abs_neg]

lemma inBox_zero_iff {nu : Lat3} : InBox 0 nu ↔ nu = 0 := by
  constructor
  · intro h
    funext c
    have := h c
    simp only [Nat.cast_zero, abs_nonpos_iff] at this
    simpa using this
  · rintro rfl c
    simp

/-- The finite sup-norm box `{ν : ‖ν‖∞ ≤ J}`. -/
noncomputable def box (J : ℕ) : Finset Lat3 :=
  Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(J : ℤ)) (J : ℤ)

lemma mem_box {J : ℕ} {nu : Lat3} : nu ∈ box J ↔ InBox J nu := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc, InBox, abs_le]

lemma box_mono {J J' : ℕ} (h : J ≤ J') : box J ⊆ box J' := fun _ hnu =>
  mem_box.mpr ((mem_box.mp hnu).mono h)

lemma card_box (J : ℕ) : (box J).card = (2 * J + 1) ^ 3 := by
  rw [box, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show ((J : ℤ) + 1 - -(J : ℤ)) = ((2 * J + 1 : ℕ) : ℤ) by push_cast; ring,
    Int.toNat_natCast]

/-- Every finite set of lattice vectors lies in some box. -/
lemma exists_box_superset (S : Finset Lat3) : ∃ R : ℕ, S ⊆ box R := by
  refine ⟨S.sup fun nu => ∑ c, (nu c).natAbs, fun nu hnu => mem_box.mpr fun c => ?_⟩
  have h1 : (nu c).natAbs ≤ ∑ c', (nu c').natAbs :=
    Finset.single_le_sum (f := fun c' => (nu c').natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ c)
  have h2 : (∑ c', (nu c').natAbs) ≤ S.sup fun nu => ∑ c, (nu c).natAbs :=
    Finset.le_sup (f := fun nu => ∑ c, (nu c).natAbs) hnu
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1.trans h2

/-- Outside the box of radius `J` the squared norm is at least `(J+1)²`. -/
lemma nsq_ge_of_not_inBox {J : ℕ} {nu : Lat3} (h : ¬ InBox J nu) :
    ((J : ℝ) + 1) ^ 2 ≤ nsq nu := by
  simp only [InBox, not_forall, not_le] at h
  obtain ⟨c, hc⟩ := h
  have h1 : (J : ℤ) + 1 ≤ |nu c| := hc
  have h2 : ((J : ℝ) + 1) ≤ |((nu c : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast h1
  have h3 : ((J : ℝ) + 1) ^ 2 ≤ ((nu c : ℤ) : ℝ) ^ 2 := by
    rw [← sq_abs ((nu c : ℤ) : ℝ)]
    exact pow_le_pow_left₀ (by positivity) h2 2
  exact h3.trans (sq_le_nsq nu c)

lemma coul_le_of_not_inBox {J : ℕ} {nu : Lat3} (h : ¬ InBox J nu) :
    coul nu ≤ 1 / ((J : ℝ) + 1) ^ 2 := by
  unfold coul
  exact one_div_le_one_div_of_le (by positivity) (nsq_ge_of_not_inBox h)

lemma coul_sq_le_of_not_inBox {J : ℕ} {nu : Lat3} (h : ¬ InBox J nu) :
    coul nu ^ 2 ≤ 1 / ((J : ℝ) + 1) ^ 4 := by
  have h1 := coul_le_of_not_inBox h
  have h2 : coul nu ^ 2 ≤ (1 / ((J : ℝ) + 1) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (coul_nonneg nu) h1 2
  calc coul nu ^ 2 ≤ (1 / ((J : ℝ) + 1) ^ 2) ^ 2 := h2
    _ = 1 / ((J : ℝ) + 1) ^ 4 := by
      rw [div_pow, one_pow, ← pow_mul]

lemma sobolev_le_of_not_inBox {J : ℕ} {nu : Lat3} (h : ¬ InBox J nu) :
    ((1 + nsq nu)⁻¹) ^ 2 ≤ 1 / ((J : ℝ) + 1) ^ 4 := by
  have hpos : 0 < ((J : ℝ) + 1) ^ 2 := by positivity
  have h1 : ((J : ℝ) + 1) ^ 2 ≤ 1 + nsq nu := (nsq_ge_of_not_inBox h).trans (by linarith)
  have h2 : (1 + nsq nu)⁻¹ ≤ (((J : ℝ) + 1) ^ 2)⁻¹ :=
    inv_anti₀ hpos h1
  have h3 : ((1 + nsq nu)⁻¹) ^ 2 ≤ ((((J : ℝ) + 1) ^ 2)⁻¹) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (by linarith [nsq_nonneg nu])) h2 2
  calc ((1 + nsq nu)⁻¹) ^ 2 ≤ ((((J : ℝ) + 1) ^ 2)⁻¹) ^ 2 := h3
    _ = 1 / ((J : ℝ) + 1) ^ 4 := by
      rw [inv_pow, ← pow_mul]; simp

/-! ### Shells -/

/-- The shell `‖ν‖∞ = J+1`. -/
noncomputable def shell (J : ℕ) : Finset Lat3 := box (J + 1) \ box J

lemma mem_shell {J : ℕ} {nu : Lat3} : nu ∈ shell J ↔ InBox (J + 1) nu ∧ ¬ InBox J nu := by
  simp [shell, mem_box]

lemma card_shell_real (J : ℕ) : ((shell J).card : ℝ) ≤ 26 * ((J : ℝ) + 1) ^ 2 := by
  have hsub : box J ⊆ box (J + 1) := box_mono (Nat.le_succ J)
  have hcard : (shell J).card + (box J).card = (box (J + 1)).card := by
    rw [shell]; exact Finset.card_sdiff_add_card_eq_card hsub
  rw [card_box, card_box] at hcard
  have hreal : ((shell J).card : ℝ) + ((2 * J + 1) ^ 3 : ℕ) = ((2 * (J + 1) + 1) ^ 3 : ℕ) := by
    exact_mod_cast hcard
  push_cast at hreal
  have e : ((shell J).card : ℝ) = 24 * (J : ℝ) ^ 2 + 48 * J + 26 := by
    have h3 : (2 * ((J : ℝ) + 1) + 1) ^ 3 - (2 * (J : ℝ) + 1) ^ 3 =
        24 * (J : ℝ) ^ 2 + 48 * J + 26 := by ring
    linarith
  rw [e]
  nlinarith [sq_nonneg (J : ℝ)]

lemma sum_box_succ (f : Lat3 → ℝ) (J : ℕ) :
    ∑ nu ∈ box (J + 1), f nu = ∑ nu ∈ box J, f nu + ∑ nu ∈ shell J, f nu := by
  rw [shell]
  exact (Finset.sum_sdiff (box_mono (Nat.le_succ J)) (f := f)).symm.trans (add_comm _ _)

lemma sum_shell_le (f : Lat3 → ℝ) (J : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ nu, ¬ InBox J nu → f nu ≤ b) :
    ∑ nu ∈ shell J, f nu ≤ 26 * ((J : ℝ) + 1) ^ 2 * b := by
  calc ∑ nu ∈ shell J, f nu ≤ ∑ _nu ∈ shell J, b :=
        Finset.sum_le_sum fun nu hnu => hf nu (mem_shell.mp hnu).2
    _ = ((shell J).card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 26 * ((J : ℝ) + 1) ^ 2 * b := mul_le_mul_of_nonneg_right (card_shell_real J) hb

/-! ### The three lattice sums -/

lemma sum_box_coul (J : ℕ) : ∑ nu ∈ box J, coul nu ≤ 26 * (J : ℝ) := by
  induction J with
  | zero =>
    have h0 : ∀ nu ∈ box 0, coul nu = 0 := by
      intro nu hnu
      rw [inBox_zero_iff.mp (mem_box.mp hnu), coul_zero]
    rw [Finset.sum_eq_zero h0]
    simp
  | succ J ih =>
    rw [sum_box_succ]
    have hshell : ∑ nu ∈ shell J, coul nu ≤ 26 := by
      have hb : (0 : ℝ) ≤ 1 / ((J : ℝ) + 1) ^ 2 := by positivity
      refine (sum_shell_le coul J hb fun nu h => coul_le_of_not_inBox h).trans ?_
      have hpos : 0 < ((J : ℝ) + 1) ^ 2 := by positivity
      rw [mul_assoc, mul_one_div_cancel hpos.ne', mul_one]
    push_cast
    linarith

/-- `∑_{‖ν‖∞ ≤ J} 1/|ν|² ≤ 26 J` for every finite set inside the box. -/
lemma sum_coul_of_inBox (J : ℕ) (S : Finset Lat3) (hS : ∀ nu ∈ S, InBox J nu) :
    ∑ nu ∈ S, coul nu ≤ 26 * (J : ℝ) := by
  have hsub : S ⊆ box J := fun nu hnu => mem_box.mpr (hS nu hnu)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun nu _ _ => coul_nonneg nu).trans
    (sum_box_coul J)

lemma sum_shells_coul_sq (J : ℕ) (hJ : 1 ≤ J) : ∀ k : ℕ,
    ∑ nu ∈ box (J + k) \ box J, coul nu ^ 2 ≤ 26 * (1 / (J : ℝ) - 1 / ((J : ℝ) + k)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hJk : box J ⊆ box (J + k) := box_mono (Nat.le_add_right J k)
    have hsplit : box (J + (k + 1)) \ box J =
        (box (J + k) \ box J) ∪ shell (J + k) := by
      ext nu
      simp only [shell, Finset.mem_sdiff, Finset.mem_union, mem_box, ← add_assoc]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h3 : InBox (J + k) nu
        · exact Or.inl ⟨h3, h2⟩
        · exact Or.inr ⟨h1, h3⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h1.mono (Nat.le_succ _), h2⟩
        · exact ⟨h1, fun h => h2 (h.mono (Nat.le_add_right J k))⟩
    have hdisj : Disjoint (box (J + k) \ box J) (shell (J + k)) := by
      rw [Finset.disjoint_left]
      intro nu h1 h2
      exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_sdiff.mp h1).1
    rw [hsplit, Finset.sum_union hdisj]
    have hshell : ∑ nu ∈ shell (J + k), coul nu ^ 2 ≤ 26 / ((J : ℝ) + k + 1) ^ 2 := by
      have hb : (0 : ℝ) ≤ 1 / (((J + k : ℕ) : ℝ) + 1) ^ 4 := by positivity
      refine (sum_shell_le (fun nu => coul nu ^ 2) (J + k) hb
        fun nu h => coul_sq_le_of_not_inBox h).trans (le_of_eq ?_)
      push_cast
      have hpos : ((J : ℝ) + k + 1) ≠ 0 := by positivity
      field_simp
    have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have htele : 26 / ((J : ℝ) + k + 1) ^ 2 ≤
        26 * (1 / ((J : ℝ) + k) - 1 / ((J : ℝ) + k + 1)) := by
      have ha : (0 : ℝ) < (J : ℝ) + k := by
        have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
        positivity
      have e : 1 / ((J : ℝ) + k) - 1 / ((J : ℝ) + k + 1) =
          1 / (((J : ℝ) + k) * ((J : ℝ) + k + 1)) := by
        field_simp
        ring
      rw [e, mul_one_div]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    push_cast at ih ⊢
    have e : (J : ℝ) + ((k : ℝ) + 1) = (J : ℝ) + k + 1 := by ring
    rw [e]
    linarith

/-- `∑_{‖ν‖∞ > J} 1/|ν|⁴ ≤ 26/J` for every finite set outside the box. -/
lemma sum_coul_sq_of_not_inBox (J : ℕ) (hJ : 1 ≤ J) (S : Finset Lat3)
    (hS : ∀ nu ∈ S, ¬ InBox J nu) :
    ∑ nu ∈ S, coul nu ^ 2 ≤ 26 / (J : ℝ) := by
  obtain ⟨R, hR⟩ := exists_box_superset S
  have hsub : S ⊆ box (J + R) \ box J := by
    intro nu hnu
    exact Finset.mem_sdiff.mpr ⟨box_mono (Nat.le_add_left R J) (hR hnu),
      fun h => hS nu hnu (mem_box.mp h)⟩
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun nu => coul nu ^ 2) fun nu _ _ => sq_nonneg _
  have h2 := sum_shells_coul_sq J hJ R
  have h3 : 26 * (1 / (J : ℝ) - 1 / ((J : ℝ) + R)) ≤ 26 / (J : ℝ) := by
    have : 0 ≤ 1 / ((J : ℝ) + R) := by positivity
    rw [mul_sub, mul_one_div]
    linarith
  exact h1.trans (h2.trans h3)

lemma sum_box_sobolev : ∀ k : ℕ,
    ∑ nu ∈ box (k + 1), ((1 + nsq nu)⁻¹) ^ 2 ≤ 53 - 26 / ((k : ℝ) + 1) := by
  intro k
  induction k with
  | zero =>
    rw [sum_box_succ]
    have hbox0 : ∑ nu ∈ box 0, ((1 + nsq nu)⁻¹) ^ 2 = 1 := by
      have hb : box 0 = {0} := by
        ext nu
        simp [mem_box, inBox_zero_iff]
      rw [hb, Finset.sum_singleton, nsq_zero]
      norm_num
    have hshell : ∑ nu ∈ shell 0, ((1 + nsq nu)⁻¹) ^ 2 ≤ 26 := by
      have hb : (0 : ℝ) ≤ 1 / (((0 : ℕ) : ℝ) + 1) ^ 4 := by positivity
      refine (sum_shell_le (fun nu => ((1 + nsq nu)⁻¹) ^ 2) 0 hb
        fun nu h => sobolev_le_of_not_inBox h).trans ?_
      norm_num
    rw [hbox0]
    simp only [Nat.cast_zero, zero_add, div_one]
    linarith
  | succ k ih =>
    rw [sum_box_succ]
    have hshell : ∑ nu ∈ shell (k + 1), ((1 + nsq nu)⁻¹) ^ 2 ≤ 26 / ((k : ℝ) + 2) ^ 2 := by
      have hb : (0 : ℝ) ≤ 1 / (((k + 1 : ℕ) : ℝ) + 1) ^ 4 := by positivity
      refine (sum_shell_le (fun nu => ((1 + nsq nu)⁻¹) ^ 2) (k + 1) hb
        fun nu h => sobolev_le_of_not_inBox h).trans (le_of_eq ?_)
      push_cast
      have hpos : ((k : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      ring
    have htele : 26 / ((k : ℝ) + 2) ^ 2 ≤ 26 / ((k : ℝ) + 1) - 26 / ((k : ℝ) + 2) := by
      have e : 26 / ((k : ℝ) + 1) - 26 / ((k : ℝ) + 2) = 26 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
        field_simp
        ring
      rw [e]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
    push_cast at ih ⊢
    have e : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by ring
    rw [e]
    linarith

/-- The uniform one-particle Sobolev sum `∑_ν (1+|ν|²)⁻² ≤ 53`, for every finite set. -/
lemma sum_sobolev_le (S : Finset Lat3) : ∑ nu ∈ S, ((1 + nsq nu)⁻¹) ^ 2 ≤ 53 := by
  obtain ⟨R, hR⟩ := exists_box_superset S
  have hsub : S ⊆ box (R + 1) := hR.trans (box_mono (Nat.le_succ R))
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun nu => ((1 + nsq nu)⁻¹) ^ 2) fun nu _ _ => sq_nonneg _
  have h2 := sum_box_sobolev R
  have h3 : 0 ≤ 26 / ((R : ℝ) + 1) := by positivity
  linarith

/-! ### Injective reindexing -/

/-- Summing a nonnegative function along an injective map into `ℤ^3`. -/
lemma sum_comp_le_of_injOn {α : Type*} [DecidableEq α] (s : Finset α) (tau : α → Lat3)
    (htau : Set.InjOn tau s) (f : Lat3 → ℝ) (T : Finset Lat3)
    (hT : ∀ a ∈ s, tau a ∈ T) (hf : ∀ nu ∈ T, 0 ≤ f nu) :
    ∑ a ∈ s, f (tau a) ≤ ∑ nu ∈ T, f nu := by
  rw [← Finset.sum_image htau]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun nu hnu _ => hf nu hnu
  intro nu hnu
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hnu
  exact hT a ha

end PlaneWaveGridG

/-! ════════════════════════════════════════════════════════════════════
## Part `Register`
════════════════════════════════════════════════════════════════════ -/

/-!
# The cyclic momentum register

A one-particle register with `n = 2M+1` points per Cartesian direction has cyclic momentum
labels `ZMod n`.  The centred representative `valMinAbs` identifies them with the integer
zone `{-M, …, M}`.  This file proves the arithmetic of differences of centred
representatives (no wrap / one wrap) and the dichotomy lemmas used by the aliasing
estimates.
-/

set_option autoImplicit false

namespace PlaneWaveGridG

/-- One-particle register modes: three cyclic momentum components. -/
abbrev GMode (n : ℕ) := Fin 3 → ZMod n

/-- Centred integer representative of a register mode. -/
def gl {n : ℕ} (x : GMode n) : Lat3 := fun c => (x c).valMinAbs

section Odd

variable {M : ℕ}

lemma valMinAbs_bounds (x : ZMod (2 * M + 1)) :
    -(M : ℤ) ≤ x.valMinAbs ∧ x.valMinAbs ≤ M := by
  have h := ZMod.valMinAbs_mem_Ioc x
  simp only [Set.mem_Ioc] at h
  push_cast at h
  constructor <;> omega

lemma abs_valMinAbs_le (x : ZMod (2 * M + 1)) : |x.valMinAbs| ≤ M := by
  have h := valMinAbs_bounds x
  rw [abs_le]
  exact h

/-- The centred representative of a cast integer in the zone is that integer. -/
lemma valMinAbs_intCast_of_abs_le (t : ℤ) (ht : |t| ≤ M) :
    ((t : ZMod (2 * M + 1))).valMinAbs = t := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  rw [abs_le] at ht
  simp only [Set.mem_Ioc]
  push_cast
  constructor <;> omega

lemma valMinAbs_eq_of_cast (z : ZMod (2 * M + 1)) (t : ℤ) (h : (t : ZMod (2 * M + 1)) = z)
    (ht : |t| ≤ M) : z.valMinAbs = t := by
  rw [← h]
  exact valMinAbs_intCast_of_abs_le t ht

lemma valMinAbs_neg' (x : ZMod (2 * M + 1)) : (-x).valMinAbs = -x.valMinAbs := by
  apply valMinAbs_eq_of_cast
  · push_cast
    rfl
  · rw [abs_neg]
    exact abs_valMinAbs_le x

/-- Difference of centred representatives: it equals the centred representative of the
difference up to one multiple of the register size. -/
lemma valMinAbs_sub_decomp (x y : ZMod (2 * M + 1)) :
    ∃ k : ℤ, (k = -1 ∨ k = 0 ∨ k = 1) ∧
      x.valMinAbs - y.valMinAbs = (x - y).valMinAbs + k * (2 * M + 1) := by
  have hx := valMinAbs_bounds x
  have hy := valMinAbs_bounds y
  have hd := valMinAbs_bounds (x - y)
  have hcast : ((x.valMinAbs - y.valMinAbs - (x - y).valMinAbs : ℤ) : ZMod (2 * M + 1)) = 0 := by
    push_cast
    simp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hcast
  obtain ⟨k, hk⟩ := hcast
  push_cast at hk
  refine ⟨k, ?_, by linarith⟩
  -- |k| ≤ 1 because the left side is at most 3M in absolute value
  have h1 : -(3 * (M : ℤ)) ≤ (2 * (M : ℤ) + 1) * k := by rw [← hk]; omega
  have h2 : (2 * (M : ℤ) + 1) * k ≤ 3 * M := by rw [← hk]; omega
  have hk1 : k ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have : (2 * (M : ℤ) + 1) * 2 ≤ (2 * (M : ℤ) + 1) * k :=
      mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  have hk2 : -1 ≤ k := by
    by_contra hcon
    push Not at hcon
    have : (2 * (M : ℤ) + 1) * k ≤ (2 * (M : ℤ) + 1) * (-2) :=
      mul_le_mul_of_nonneg_left (by omega) (by omega)
    omega
  omega

/-- If the difference of centred representatives lies in the zone, it is the centred
representative of the difference (no wrap). -/
lemma valMinAbs_sub_of_small (x y : ZMod (2 * M + 1))
    (h : |x.valMinAbs - y.valMinAbs| ≤ M) :
    (x - y).valMinAbs = x.valMinAbs - y.valMinAbs := by
  apply valMinAbs_eq_of_cast _ _ _ h
  push_cast
  rfl

/-- Low-transfer dichotomy for one component: if the centred transfer is at most `J`, the
output lies beyond `T` and `T ≤ M`, then the input lies beyond `T - J`, whether or not the
transfer wraps. -/
lemma lowTransfer_component (x y : ZMod (2 * M + 1)) (J T : ℤ) (hT : T ≤ M)
    (hd : |(x - y).valMinAbs| ≤ J) (hx : T < |x.valMinAbs|) :
    T - J < |y.valMinAbs| := by
  obtain ⟨k, hk, he⟩ := valMinAbs_sub_decomp x y
  have hxb := valMinAbs_bounds x
  have hyb := valMinAbs_bounds y
  rw [abs_le] at hd
  rw [lt_abs] at hx ⊢
  rcases hk with rfl | rfl | rfl <;> omega

/-- Strong-wrap dichotomy (register radius `M = 2m`): a wrapping transfer whose centred
representative is at most `m` connects two modes that both lie beyond `m`. -/
lemma strongWrap_component (m : ℕ) (x y : ZMod (2 * (2 * m) + 1))
    (hd : |(x - y).valMinAbs| ≤ m) (hw : (2 * m : ℤ) < |x.valMinAbs - y.valMinAbs|) :
    (m : ℤ) < |x.valMinAbs| ∧ (m : ℤ) < |y.valMinAbs| := by
  obtain ⟨k, hk, he⟩ := valMinAbs_sub_decomp (M := 2 * m) x y
  have hxb := valMinAbs_bounds (M := 2 * m) x
  have hyb := valMinAbs_bounds (M := 2 * m) y
  rw [abs_le] at hd
  rw [lt_abs] at hw
  push_cast at hxb hyb he
  rw [lt_abs, lt_abs]
  rcases hk with rfl | rfl | rfl <;> omega

/-- Large integer transfers (beyond `2m`) force one endpoint beyond `m`. -/
lemma largeTransfer_component (m : ℕ) (a b : ℤ) (h : (2 * m : ℤ) < |a - b|) :
    (m : ℤ) < |a| ∨ (m : ℤ) < |b| := by
  rw [lt_abs] at h
  rw [lt_abs, lt_abs]
  omega

end Odd

/-! ### Lattice-level statements -/

section Lattice

variable {M : ℕ}

lemma gl_inBox (x : GMode (2 * M + 1)) : InBox M (gl x) := fun c => abs_valMinAbs_le (x c)

lemma gl_injective : Function.Injective (gl : GMode (2 * M + 1) → Lat3) := by
  intro x y h
  funext c
  have := congrFun h c
  exact ZMod.valMinAbs_inj.mp this

/-- The cast of an integer vector into the register. -/
def ofLat (nu : Lat3) : GMode (2 * M + 1) := fun c => ((nu c : ℤ) : ZMod (2 * M + 1))

lemma gl_ofLat {nu : Lat3} (h : InBox M nu) : gl (ofLat (M := M) nu) = nu := by
  funext c
  exact valMinAbs_intCast_of_abs_le (nu c) (h c)

lemma ofLat_gl (x : GMode (2 * M + 1)) : ofLat (gl x) = x := by
  funext c
  exact ZMod.coe_valMinAbs (x c)

lemma gl_neg (x : GMode (2 * M + 1)) : gl (-x) = -gl x := by
  funext c
  exact valMinAbs_neg' (x c)

lemma gl_sub_of_inBox (x y : GMode (2 * M + 1)) (h : InBox M (gl x - gl y)) :
    gl (x - y) = gl x - gl y := by
  funext c
  exact valMinAbs_sub_of_small (x c) (y c) (h c)

/-- Output beyond `T`, centred transfer at most `J`, `T ≤ M`: input beyond `T - J`. -/
lemma lowTransfer_lattice (x y : GMode (2 * M + 1)) (J T : ℕ) (hJT : J ≤ T) (hT : T ≤ M)
    (hd : InBox J (gl (x - y))) (hx : ¬ InBox T (gl x)) : ¬ InBox (T - J) (gl y) := by
  simp only [InBox, not_forall, not_le] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  refine ⟨c, ?_⟩
  have h := lowTransfer_component (x c) (y c) J T (by exact_mod_cast hT) (hd c) hc
  push_cast [Nat.cast_sub hJT]
  exact h

/-- The integer analogue (Galerkin transfers never wrap). -/
lemma lowTransfer_lattice_int (a b : Lat3) (J T : ℕ) (hJT : J ≤ T)
    (hd : InBox J (a - b)) (ha : ¬ InBox T a) : ¬ InBox (T - J) b := by
  simp only [InBox, not_forall, not_le] at ha ⊢
  obtain ⟨c, hc⟩ := ha
  refine ⟨c, ?_⟩
  have hdc := hd c
  simp only [Pi.sub_apply] at hdc
  rw [abs_le] at hdc
  rw [lt_abs] at hc ⊢
  push_cast [Nat.cast_sub hJT]
  omega

lemma largeTransfer_lattice (m : ℕ) (a b : Lat3) (h : ¬ InBox (2 * m) (a - b)) :
    ¬ InBox m a ∨ ¬ InBox m b := by
  simp only [InBox, not_forall, not_le] at h
  obtain ⟨c, hc⟩ := h
  simp only [Pi.sub_apply] at hc
  rcases largeTransfer_component m (a c) (b c) (by exact_mod_cast hc) with h1 | h1
  · exact Or.inl fun hh => absurd (hh c) (not_le.mpr h1)
  · exact Or.inr fun hh => absurd (hh c) (not_le.mpr h1)

lemma strongWrap_lattice (m : ℕ) (x y : GMode (2 * (2 * m) + 1))
    (hd : InBox m (gl (x - y))) (hw : ¬ InBox (2 * m) (gl x - gl y)) :
    ¬ InBox m (gl x) ∧ ¬ InBox m (gl y) := by
  simp only [InBox, not_forall, not_le] at hw
  obtain ⟨c, hc⟩ := hw
  simp only [Pi.sub_apply] at hc
  have h := strongWrap_component m (x c) (y c) (hd c) (by exact_mod_cast hc)
  exact ⟨fun hh => absurd (hh c) (not_le.mpr h.1), fun hh => absurd (hh c) (not_le.mpr h.2)⟩

end Lattice

end PlaneWaveGridG

/-! ════════════════════════════════════════════════════════════════════
## Part `KernelBoundsReal`
════════════════════════════════════════════════════════════════════ -/

/-!
# General bounds for finite kernel operators

For a finite index type `ι`, a nonnegative kernel `κ : ι → ι → ℝ` acts on nonnegative
functions by `h ↦ (q ↦ ∑_p κ q p * h p)`.  We prove

* the Schur test (`schur_sq`);
* a slice form of Young's inequality: if the kernel only connects points with the
  same slice label and has column `ℓ²` sums at most `B`, then the output is bounded by
  `B` times the squared slice `ℓ¹` masses (`slice_young_sq`);
* the slice-mass bound, a weighted Cauchy--Schwarz inequality inside each slice
  (`slice_mass_le`).

The complex kernel operator `kOp` uses the output-first convention of the release
file's `finiteCoefficientKernelOperator`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PlaneWaveGridG

open Finset

section RealBounds

variable {ι : Type*} [Fintype ι]

/-- Weighted Cauchy--Schwarz: `(∑ a b)² ≤ (∑ a)(∑ a b²)` for `a ≥ 0`. -/
lemma weighted_cs (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, a i * b i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (a i))
    (fun i => Real.sqrt (a i) * b i)
  have e1 : ∀ i ∈ s, Real.sqrt (a i) * (Real.sqrt (a i) * b i) = a i * b i := by
    intro i hi
    rw [← mul_assoc, Real.mul_self_sqrt (ha i hi)]
  have e2 : ∀ i ∈ s, Real.sqrt (a i) ^ 2 = a i := fun i hi => Real.sq_sqrt (ha i hi)
  have e3 : ∀ i ∈ s, (Real.sqrt (a i) * b i) ^ 2 = a i * b i ^ 2 := by
    intro i hi
    rw [mul_pow, Real.sq_sqrt (ha i hi)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at h
  exact h

/-- The Schur test, in squared form. -/
lemma schur_sq (κ : ι → ι → ℝ) (h : ι → ℝ) (hκ : ∀ q p, 0 ≤ κ q p) {α β : ℝ}
    (hα : 0 ≤ α) (hrow : ∀ q, ∑ p, κ q p ≤ α) (hcol : ∀ p, ∑ q, κ q p ≤ β) :
    ∑ q, (∑ p, κ q p * h p) ^ 2 ≤ α * β * ∑ p, h p ^ 2 := by
  have step : ∀ q, (∑ p, κ q p * h p) ^ 2 ≤ α * ∑ p, κ q p * h p ^ 2 := by
    intro q
    refine (weighted_cs univ (κ q) h fun p _ => hκ q p).trans ?_
    exact mul_le_mul_of_nonneg_right (hrow q)
      (sum_nonneg fun p _ => mul_nonneg (hκ q p) (sq_nonneg _))
  calc ∑ q, (∑ p, κ q p * h p) ^ 2 ≤ ∑ q, α * ∑ p, κ q p * h p ^ 2 :=
        sum_le_sum fun q _ => step q
    _ = α * ∑ p, (∑ q, κ q p) * h p ^ 2 := by
        rw [← mul_sum, sum_comm]
        congr 1
        exact sum_congr rfl fun p _ => by rw [sum_mul]
    _ ≤ α * ∑ p, β * h p ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hα
        exact sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hcol p) (sq_nonneg _)
    _ = α * β * ∑ p, h p ^ 2 := by rw [← mul_sum]; ring

/-- The `ℓ¹` mass of the slice through `p`. -/
noncomputable def sliceMass {σ : Type*} [DecidableEq σ] (S : ι → σ) (h : ι → ℝ) (p : ι) : ℝ :=
  ∑ p', if S p' = S p then h p' else 0

lemma sliceMass_nonneg {σ : Type*} [DecidableEq σ] (S : ι → σ) (h : ι → ℝ)
    (hh : ∀ p, 0 ≤ h p) (p : ι) : 0 ≤ sliceMass S h p :=
  sum_nonneg fun p' _ => by split_ifs <;> simp [hh]

lemma sliceMass_congr {σ : Type*} [DecidableEq σ] (S : ι → σ) (h : ι → ℝ) {p q : ι}
    (hpq : S p = S q) : sliceMass S h p = sliceMass S h q := by
  unfold sliceMass
  rw [hpq]

/-- Young's inequality inside slices, in squared form. -/
lemma slice_young_sq {σ : Type*} [DecidableEq σ] (S : ι → σ) (κ : ι → ι → ℝ) (h : ι → ℝ)
    (_hκ : ∀ q p, 0 ≤ κ q p) (hh : ∀ p, 0 ≤ h p)
    (hslice : ∀ q p, κ q p ≠ 0 → S q = S p)
    {B : ℝ} (hcol : ∀ p, ∑ q, κ q p ^ 2 ≤ B) :
    ∑ q, (∑ p, κ q p * h p) ^ 2 ≤ B * ∑ p, h p * sliceMass S h p := by
  have step : ∀ q, (∑ p, κ q p * h p) ^ 2 ≤ sliceMass S h q * ∑ p, h p * κ q p ^ 2 := by
    intro q
    have e : ∑ p, κ q p * h p = ∑ p, (if S p = S q then h p else 0) * κ q p := by
      apply sum_congr rfl
      intro p _
      by_cases hk : κ q p = 0
      · simp [hk]
      · rw [if_pos (hslice q p hk).symm]
        ring
    rw [e]
    refine (weighted_cs univ (fun p => if S p = S q then h p else 0) (κ q) ?_).trans ?_
    · intro p _
      split_ifs <;> simp [hh]
    · apply mul_le_mul_of_nonneg_left _ (sliceMass_nonneg S h hh q)
      apply sum_le_sum
      intro p _
      split_ifs
      · exact le_refl _
      · rw [zero_mul]
        exact mul_nonneg (hh p) (sq_nonneg _)
  calc ∑ q, (∑ p, κ q p * h p) ^ 2 ≤ ∑ q, sliceMass S h q * ∑ p, h p * κ q p ^ 2 :=
        sum_le_sum fun q _ => step q
    _ = ∑ p, h p * ∑ q, κ q p ^ 2 * sliceMass S h q := by
        simp_rw [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring
    _ = ∑ p, h p * (sliceMass S h p * ∑ q, κ q p ^ 2) := by
        refine sum_congr rfl fun p _ => ?_
        congr 1
        rw [mul_sum]
        refine sum_congr rfl fun q _ => ?_
        by_cases hk : κ q p = 0
        · simp [hk]
        · rw [sliceMass_congr S h (hslice q p hk)]
          ring
    _ ≤ ∑ p, h p * (sliceMass S h p * B) := by
        apply sum_le_sum
        intro p _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hcol p) (sliceMass_nonneg S h hh p)) (hh p)
    _ = B * ∑ p, h p * sliceMass S h p := by
        rw [mul_sum]
        exact sum_congr rfl fun p _ => by ring

/-- Weighted Cauchy--Schwarz inside slices: the squared slice masses are controlled by a
weighted `ℓ²` norm, with the slice sums of inverse squared weights as constant. -/
lemma slice_mass_le {σ : Type*} [DecidableEq σ] (S : ι → σ) (h w : ι → ℝ)
    (_hh : ∀ p, 0 ≤ h p) (hw : ∀ p, 0 < w p) {C : ℝ}
    (hC : ∀ p, ∑ p', (if S p' = S p then (w p')⁻¹ ^ 2 else 0) ≤ C) :
    ∑ p, h p * sliceMass S h p ≤ C * ∑ p, (w p * h p) ^ 2 := by
  -- pointwise AM--GM with weights
  have amgm : ∀ p p', h p * h p' ≤
      ((w p * h p) ^ 2 * (w p')⁻¹ ^ 2 + (w p' * h p') ^ 2 * (w p)⁻¹ ^ 2) / 2 := by
    intro p p'
    have hwp := (hw p).ne'
    have hwp' := (hw p').ne'
    have key := two_mul_le_add_sq (w p * h p * (w p')⁻¹) (w p' * h p' * (w p)⁻¹)
    have e : w p * h p * (w p')⁻¹ * (w p' * h p' * (w p)⁻¹) = h p * h p' := by
      field_simp
    have e2 : (w p * h p * (w p')⁻¹) ^ 2 = (w p * h p) ^ 2 * (w p')⁻¹ ^ 2 := by ring
    have e3 : (w p' * h p' * (w p)⁻¹) ^ 2 = (w p' * h p') ^ 2 * (w p)⁻¹ ^ 2 := by ring
    rw [mul_assoc, e, e2, e3] at key
    linarith
  have hsum : ∑ p, h p * sliceMass S h p =
      ∑ p, ∑ p', (if S p' = S p then h p * h p' else 0) := by
    apply sum_congr rfl
    intro p _
    rw [sliceMass, mul_sum]
    exact sum_congr rfl fun p' _ => by split_ifs <;> simp
  rw [hsum]
  have bound : ∀ p p', 2 * (if S p' = S p then h p * h p' else 0) ≤
      (if S p' = S p then (w p')⁻¹ ^ 2 else 0) * (w p * h p) ^ 2 +
       (if S p = S p' then (w p)⁻¹ ^ 2 else 0) * (w p' * h p') ^ 2 := by
    intro p p'
    by_cases hs : S p' = S p
    · rw [if_pos hs, if_pos hs, if_pos hs.symm]
      have := amgm p p'
      linarith
    · rw [if_neg hs, if_neg hs, if_neg (Ne.symm hs)]
      simp
  have h2 : 2 * ∑ p, ∑ p', (if S p' = S p then h p * h p' else 0) ≤
      C * ∑ p, (w p * h p) ^ 2 + C * ∑ p, (w p * h p) ^ 2 := by
    calc 2 * ∑ p, ∑ p', (if S p' = S p then h p * h p' else 0)
        = ∑ p, ∑ p', 2 * (if S p' = S p then h p * h p' else 0) := by
          rw [mul_sum]; simp_rw [mul_sum]
      _ ≤ ∑ p, ∑ p', ((if S p' = S p then (w p')⁻¹ ^ 2 else 0) * (w p * h p) ^ 2 +
            (if S p = S p' then (w p)⁻¹ ^ 2 else 0) * (w p' * h p') ^ 2) :=
          sum_le_sum fun p _ => sum_le_sum fun p' _ => bound p p'
      _ = ∑ p, (∑ p', if S p' = S p then (w p')⁻¹ ^ 2 else 0) * (w p * h p) ^ 2 +
            ∑ p', (∑ p, if S p = S p' then (w p)⁻¹ ^ 2 else 0) * (w p' * h p') ^ 2 := by
          simp_rw [sum_add_distrib]
          congr 1
          · exact sum_congr rfl fun p _ => by rw [sum_mul]
          · rw [sum_comm]
            exact sum_congr rfl fun p' _ => by rw [sum_mul]
      _ ≤ ∑ p, C * (w p * h p) ^ 2 + ∑ p', C * (w p' * h p') ^ 2 := by
          apply add_le_add
          · exact sum_le_sum fun p _ => mul_le_mul_of_nonneg_right (hC p) (sq_nonneg _)
          · exact sum_le_sum fun p' _ => mul_le_mul_of_nonneg_right (hC p') (sq_nonneg _)
      _ = C * ∑ p, (w p * h p) ^ 2 + C * ∑ p, (w p * h p) ^ 2 := by
          rw [mul_sum]
  linarith

/-- Cauchy--Schwarz for the bilinear form of a kernel. -/
lemma bilinear_sq (κ : ι → ι → ℝ) (f h : ι → ℝ) :
    (∑ q, f q * ∑ p, κ q p * h p) ^ 2 ≤ (∑ q, f q ^ 2) * ∑ q, (∑ p, κ q p * h p) ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq univ f fun q => ∑ p, κ q p * h p

/-- Square-root form of the bilinear Cauchy--Schwarz bound. -/
lemma bilinear_le (κ : ι → ι → ℝ) (f h : ι → ℝ) {Y Z : ℝ} (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hf : ∑ q, f q ^ 2 ≤ Y ^ 2) (hK : ∑ q, (∑ p, κ q p * h p) ^ 2 ≤ Z ^ 2) :
    ∑ q, f q * ∑ p, κ q p * h p ≤ Y * Z := by
  have h1 := bilinear_sq κ f h
  have h2 : (∑ q, f q * ∑ p, κ q p * h p) ^ 2 ≤ (Y * Z) ^ 2 := by
    rw [mul_pow]
    exact h1.trans (mul_le_mul hf hK (sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _))
  exact abs_le_of_sq_le_sq' h2 (mul_nonneg hY hZ) |>.2

end RealBounds

end PlaneWaveGridG

/-! ════════════════════════════════════════════════════════════════════
## Part `KernelBounds`
════════════════════════════════════════════════════════════════════ -/

/-!
# Complex kernel operators

The output-first kernel action `kOp` (the release file's `finiteCoefficientKernelOperator`)
and its elementary norm and inner-product bounds.
-/

set_option autoImplicit false

namespace PlaneWaveGridG

open Finset

section ComplexOperators

variable {ι : Type*} [Fintype ι]

/-- Matrix action with the output-first kernel convention. -/
noncomputable def kOp (kernel : ι → ι → ℂ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun u := WithLp.toLp 2 (fun q => ∑ p : ι, u p * kernel q p)
  map_add' := by
    intro u v
    ext q
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro z u
    ext q
    simp [smul_eq_mul, mul_assoc, Finset.mul_sum]

@[simp] lemma kOp_apply (kernel : ι → ι → ℂ) (u : EuclideanSpace ℂ ι) (q : ι) :
    (kOp kernel u) q = ∑ p : ι, u p * kernel q p := rfl

lemma kOp_add (k1 k2 : ι → ι → ℂ) : kOp (k1 + k2) = kOp k1 + kOp k2 := by
  apply LinearMap.ext
  intro u
  ext q
  simp [mul_add, Finset.sum_add_distrib]

lemma kOp_sub (k1 k2 : ι → ι → ℂ) : kOp (k1 - k2) = kOp k1 - kOp k2 := by
  apply LinearMap.ext
  intro u
  ext q
  simp [mul_sub, Finset.sum_sub_distrib]

lemma kOp_sum {τ : Type*} (s : Finset τ) (k : τ → ι → ι → ℂ) :
    kOp (fun q p => ∑ t ∈ s, k t q p) = ∑ t ∈ s, kOp (k t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply LinearMap.ext
    intro u
    ext q
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih, ← kOp_add]
    congr 1
    funext q p
    simp [Finset.sum_insert ha]

lemma norm_sq_eq_sum (u : EuclideanSpace ℂ ι) : ‖u‖ ^ 2 = ∑ q, ‖u q‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℂ) u

/-- Pointwise domination of a kernel action by the absolute kernel. -/
lemma norm_kOp_apply_le (kernel : ι → ι → ℂ) (u : EuclideanSpace ℂ ι) (q : ι) :
    ‖(kOp kernel u) q‖ ≤ ∑ p, ‖kernel q p‖ * ‖u p‖ := by
  rw [kOp_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact sum_congr rfl fun p _ => by rw [norm_mul, mul_comm]

lemma norm_kOp_sq_le (kernel : ι → ι → ℂ) (u : EuclideanSpace ℂ ι) :
    ‖kOp kernel u‖ ^ 2 ≤ ∑ q, (∑ p, ‖kernel q p‖ * ‖u p‖) ^ 2 := by
  rw [norm_sq_eq_sum]
  exact sum_le_sum fun q _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_kOp_apply_le kernel u q) 2

lemma norm_inner_kOp_le (kernel : ι → ι → ℂ) (v u : EuclideanSpace ℂ ι) :
    ‖inner ℂ v (kOp kernel u)‖ ≤ ∑ q, ‖v q‖ * ∑ p, ‖kernel q p‖ * ‖u p‖ := by
  rw [PiLp.inner_apply]
  refine (norm_sum_le _ _).trans (sum_le_sum fun q _ => ?_)
  refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_kOp_apply_le kernel u q) (norm_nonneg _)

/-- From a squared bound on the absolute kernel action to an operator bound. -/
lemma norm_kOp_le_of_sq (kernel : ι → ι → ℂ) (u : EuclideanSpace ℂ ι) {X : ℝ} (hX : 0 ≤ X)
    (h : ∑ q, (∑ p, ‖kernel q p‖ * ‖u p‖) ^ 2 ≤ X ^ 2) : ‖kOp kernel u‖ ≤ X := by
  have := (norm_kOp_sq_le kernel u).trans h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hX two_ne_zero).mp this

end ComplexOperators

end PlaneWaveGridG

/-! ════════════════════════════════════════════════════════════════════
## Part `Transfer`
════════════════════════════════════════════════════════════════════ -/

/-!
# Transfer kernels

A transfer kernel on a finite configuration space `ι` is
`tk rel tau kappa q p = if rel q p then kappa (tau q p) else 0`,
where `rel` says which configurations are connected and `tau q p ∈ ℤ³` is the momentum
transfer.  If `tau` is injective in each argument on the connected set and
`‖kappa ν‖ ≤ c/|ν|²`, the lattice sums give the Schur and slice-Young inputs:

* transfers with `‖ν‖∞ ≤ J`: row and column `ℓ¹` sums `≤ 26 c J`;
* transfers with `‖ν‖∞ > J`: row and column `ℓ²` sums `≤ 26 c²/J`.

Combined with a slice structure (a slice label and an injective slice coordinate) these
give the operator bound `‖K u‖ ≤ 26 c J ‖u‖ + c √(26·53/J) ‖w u‖`, its tail version, and
the bilinear bounds used for the dropped-transfer and wrap forms.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PlaneWaveGridG

open Finset

section Masks

variable {ι : Type*} [Fintype ι]

open Classical in
/-- Restriction of a state to a set of configurations. -/
noncomputable def maskOp (P : ι → Prop) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun u := WithLp.toLp 2 (fun q => if P q then u q else 0)
  map_add' := by
    intro u v
    ext q
    simp only [PiLp.add_apply]
    split_ifs <;> simp
  map_smul' := by
    intro z u
    ext q
    simp only [PiLp.smul_apply, RingHom.id_apply, smul_eq_mul]
    split_ifs <;> simp

open Classical in
lemma maskOp_apply (P : ι → Prop) (u : EuclideanSpace ℂ ι) (q : ι) :
    (maskOp P u) q = if P q then u q else 0 := rfl

lemma maskOp_apply_of (P : ι → Prop) (u : EuclideanSpace ℂ ι) {q : ι} (h : P q) :
    (maskOp P u) q = u q := by
  classical
  rw [maskOp_apply, if_pos h]

lemma maskOp_apply_of_not (P : ι → Prop) (u : EuclideanSpace ℂ ι) {q : ι} (h : ¬ P q) :
    (maskOp P u) q = 0 := by
  classical
  rw [maskOp_apply, if_neg h]

lemma norm_maskOp_apply_le (P : ι → Prop) (u : EuclideanSpace ℂ ι) (q : ι) :
    ‖(maskOp P u) q‖ ≤ ‖u q‖ := by
  classical
  rw [maskOp_apply]
  split_ifs <;> simp

lemma norm_maskOp_le (P : ι → Prop) (u : EuclideanSpace ℂ ι) : ‖maskOp P u‖ ≤ ‖u‖ := by
  have h : ‖maskOp P u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum]
    exact sum_le_sum fun q _ => pow_le_pow_left₀ (norm_nonneg _) (norm_maskOp_apply_le P u q) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

lemma norm_maskOp_mono {P P' : ι → Prop} (hPP' : ∀ q, P q → P' q) (u : EuclideanSpace ℂ ι) :
    ‖maskOp P u‖ ≤ ‖maskOp P' u‖ := by
  have h : ‖maskOp P u‖ ^ 2 ≤ ‖maskOp P' u‖ ^ 2 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum]
    refine sum_le_sum fun q _ => ?_
    by_cases hq : P q
    · rw [maskOp_apply_of P u hq, maskOp_apply_of P' u (hPP' q hq)]
    · rw [maskOp_apply_of_not P u hq]
      simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- Union bound for masks. -/
lemma norm_maskOp_or_le (P P' : ι → Prop) (u : EuclideanSpace ℂ ι) :
    ‖maskOp (fun q => P q ∨ P' q) u‖ ≤ ‖maskOp P u‖ + ‖maskOp P' u‖ := by
  have h : ‖maskOp (fun q => P q ∨ P' q) u‖ ^ 2 ≤ ‖maskOp P u‖ ^ 2 + ‖maskOp P' u‖ ^ 2 := by
    rw [norm_sq_eq_sum, norm_sq_eq_sum, norm_sq_eq_sum, ← sum_add_distrib]
    refine sum_le_sum fun q _ => ?_
    by_cases h1 : P q
    · rw [maskOp_apply_of _ u (Or.inl h1), maskOp_apply_of P u h1]
      exact le_add_of_nonneg_right (sq_nonneg _)
    · by_cases h2 : P' q
      · rw [maskOp_apply_of _ u (Or.inr h2), maskOp_apply_of P' u h2]
        exact le_add_of_nonneg_left (sq_nonneg _)
      · rw [maskOp_apply_of_not _ u (fun h => h.elim h1 h2), norm_zero, zero_pow two_ne_zero]
        positivity
  have h2 : ‖maskOp P u‖ ^ 2 + ‖maskOp P' u‖ ^ 2 ≤ (‖maskOp P u‖ + ‖maskOp P' u‖) ^ 2 := by
    nlinarith [norm_nonneg (maskOp P u), norm_nonneg (maskOp P' u)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (h.trans h2)

/-- Multiplication by a real weight. -/
noncomputable def wMul (w : ι → ℝ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun u := WithLp.toLp 2 (fun q => (w q : ℂ) * u q)
  map_add' := by
    intro u v
    ext q
    simp [mul_add]
  map_smul' := by
    intro z u
    ext q
    simp only [PiLp.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

lemma wMul_apply (w : ι → ℝ) (u : EuclideanSpace ℂ ι) (q : ι) :
    (wMul w u) q = (w q : ℂ) * u q := rfl

lemma norm_wMul_sq (w : ι → ℝ) (hw : ∀ q, 0 ≤ w q) (u : EuclideanSpace ℂ ι) :
    ‖wMul w u‖ ^ 2 = ∑ q, (w q * ‖u q‖) ^ 2 := by
  rw [norm_sq_eq_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [wMul_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw q)]

lemma norm_wMul_mono {w w' : ι → ℝ} (hw : ∀ q, 0 ≤ w q) (hww' : ∀ q, w q ≤ w' q)
    (u : EuclideanSpace ℂ ι) : ‖wMul w u‖ ≤ ‖wMul w' u‖ := by
  have hw' : ∀ q, 0 ≤ w' q := fun q => (hw q).trans (hww' q)
  have h : ‖wMul w u‖ ^ 2 ≤ ‖wMul w' u‖ ^ 2 := by
    rw [norm_wMul_sq w hw, norm_wMul_sq w' hw']
    exact sum_le_sum fun q _ => pow_le_pow_left₀ (mul_nonneg (hw q) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (hww' q) (norm_nonneg _)) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- A priori tail: on a set where the weight is at least `b > 0`, the masked norm is at most
the weighted norm divided by `b`. -/
lemma norm_maskOp_le_wMul (P : ι → Prop) (w : ι → ℝ) (hw : ∀ q, 0 ≤ w q) {b : ℝ} (hb : 0 < b)
    (hPw : ∀ q, P q → b ≤ w q) (u : EuclideanSpace ℂ ι) :
    ‖maskOp P u‖ ≤ ‖wMul w u‖ / b := by
  rw [le_div_iff₀ hb]
  have h : (‖maskOp P u‖ * b) ^ 2 ≤ ‖wMul w u‖ ^ 2 := by
    rw [mul_pow, norm_sq_eq_sum, norm_wMul_sq w hw, sum_mul]
    refine sum_le_sum fun q _ => ?_
    by_cases hq : P q
    · rw [maskOp_apply_of P u hq, ← mul_pow, mul_comm]
      exact pow_le_pow_left₀ (mul_nonneg hb.le (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hPw q hq) (norm_nonneg _)) 2
    · rw [maskOp_apply_of_not P u hq]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact sq_nonneg _
  exact (pow_le_pow_iff_left₀ (mul_nonneg (norm_nonneg _) hb.le) (norm_nonneg _)
    two_ne_zero).mp h

end Masks

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The transfer kernel `if rel q p then kappa (tau q p) else 0`. -/
noncomputable def tk (rel : ι → ι → Prop) (tau : ι → ι → Lat3) (kappa : Lat3 → ℂ)
    (q p : ι) : ℂ :=
  if rel q p then kappa (tau q p) else 0

lemma tk_of_rel {rel : ι → ι → Prop} {tau : ι → ι → Lat3} {kappa : Lat3 → ℂ} {q p : ι}
    (h : rel q p) : tk rel tau kappa q p = kappa (tau q p) := by
  classical
  unfold tk
  rw [if_pos h]

lemma tk_of_not_rel {rel : ι → ι → Prop} {tau : ι → ι → Lat3} {kappa : Lat3 → ℂ} {q p : ι}
    (h : ¬ rel q p) : tk rel tau kappa q p = 0 := by
  classical
  unfold tk
  rw [if_neg h]

lemma rel_of_tk_ne_zero {rel : ι → ι → Prop} {tau : ι → ι → Lat3} {kappa : Lat3 → ℂ}
    {q p : ι} (h : tk rel tau kappa q p ≠ 0) : rel q p := by
  by_contra hr
  exact h (tk_of_not_rel hr)

/-- Splitting a transfer kernel by a predicate on the transfer. -/
lemma tk_split (rel : ι → ι → Prop) (tau : ι → ι → Lat3) (kappa : Lat3 → ℂ)
    (Q : Lat3 → Prop) :
    tk rel tau kappa = tk (fun q p => rel q p ∧ Q (tau q p)) tau kappa +
      tk (fun q p => rel q p ∧ ¬ Q (tau q p)) tau kappa := by
  classical
  funext q p
  simp only [Pi.add_apply, tk]
  by_cases h : rel q p <;> by_cases hQ : Q (tau q p) <;> simp [h, hQ]

/-- Injectivity of the transfer in the input (for fixed output) on connected pairs. -/
def RowInj (rel : ι → ι → Prop) (tau : ι → ι → Lat3) : Prop :=
  ∀ q p p', rel q p → rel q p' → tau q p = tau q p' → p = p'

/-- Injectivity of the transfer in the output (for fixed input) on connected pairs. -/
def ColInj (rel : ι → ι → Prop) (tau : ι → ι → Lat3) : Prop :=
  ∀ q q' p, rel q p → rel q' p → tau q p = tau q' p → q = q'

lemma RowInj.mono {rel rel' : ι → ι → Prop} {tau : ι → ι → Lat3} (h : RowInj rel tau)
    (hle : ∀ q p, rel' q p → rel q p) : RowInj rel' tau :=
  fun q p p' h1 h2 h3 => h q p p' (hle q p h1) (hle q p' h2) h3

lemma ColInj.mono {rel rel' : ι → ι → Prop} {tau : ι → ι → Lat3} (h : ColInj rel tau)
    (hle : ∀ q p, rel' q p → rel q p) : ColInj rel' tau :=
  fun q q' p h1 h2 h3 => h q q' p (hle q p h1) (hle q' p h2) h3

/-- Coulomb-type kernel bound. -/
def KernelBound (kappa : Lat3 → ℂ) (c : ℝ) : Prop := ∀ nu, ‖kappa nu‖ ≤ c * coul nu

open Classical in
lemma sum_row_eq (rel : ι → ι → Prop) (tau : ι → ι → Lat3) (kappa : Lat3 → ℂ) (q : ι)
    (F : ℂ → ℝ) (hF : F 0 = 0) :
    ∑ p, F (tk rel tau kappa q p) =
      ∑ p ∈ (univ.filter fun p => rel q p), F (kappa (tau q p)) := by
  classical
  rw [Finset.sum_filter]
  refine sum_congr rfl fun p _ => ?_
  by_cases h : rel q p
  · rw [tk_of_rel h, if_pos h]
  · rw [tk_of_not_rel h, if_neg h, hF]

open Classical in
lemma sum_col_eq (rel : ι → ι → Prop) (tau : ι → ι → Lat3) (kappa : Lat3 → ℂ) (p : ι)
    (F : ℂ → ℝ) (hF : F 0 = 0) :
    ∑ q, F (tk rel tau kappa q p) =
      ∑ q ∈ (univ.filter fun q => rel q p), F (kappa (tau q p)) := by
  classical
  rw [Finset.sum_filter]
  refine sum_congr rfl fun q _ => ?_
  by_cases h : rel q p
  · rw [tk_of_rel h, if_pos h]
  · rw [tk_of_not_rel h, if_neg h, hF]

variable {rel : ι → ι → Prop} {tau : ι → ι → Lat3} {kappa : Lat3 → ℂ} {c : ℝ}

lemma tk_row_l1 (hk : KernelBound kappa c) (hc : 0 ≤ c) (hinj : RowInj rel tau) (J : ℕ)
    (hJ : ∀ q p, rel q p → InBox J (tau q p)) (q : ι) :
    ∑ p, ‖tk rel tau kappa q p‖ ≤ c * (26 * J) := by
  classical
  rw [sum_row_eq rel tau kappa q (fun z => ‖z‖) norm_zero]
  set s := univ.filter fun p => rel q p
  calc ∑ p ∈ s, ‖kappa (tau q p)‖ ≤ ∑ p ∈ s, c * coul (tau q p) :=
        sum_le_sum fun p _ => hk _
    _ = c * ∑ p ∈ s, coul (tau q p) := by rw [mul_sum]
    _ ≤ c * ∑ nu ∈ s.image (tau q), coul nu := by
        apply mul_le_mul_of_nonneg_left _ hc
        refine sum_comp_le_of_injOn s (tau q) ?_ coul _ (fun p hp => mem_image_of_mem _ hp)
          (fun nu _ => coul_nonneg nu)
        intro p hp p' hp' h
        exact hinj q p p' (mem_filter.mp hp).2 (mem_filter.mp hp').2 h
    _ ≤ c * (26 * J) := by
        apply mul_le_mul_of_nonneg_left _ hc
        apply sum_coul_of_inBox
        intro nu hnu
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hnu
        exact hJ q p (mem_filter.mp hp).2

lemma tk_col_l1 (hk : KernelBound kappa c) (hc : 0 ≤ c) (hinj : ColInj rel tau) (J : ℕ)
    (hJ : ∀ q p, rel q p → InBox J (tau q p)) (p : ι) :
    ∑ q, ‖tk rel tau kappa q p‖ ≤ c * (26 * J) := by
  classical
  rw [sum_col_eq rel tau kappa p (fun z => ‖z‖) norm_zero]
  set s := univ.filter fun q => rel q p
  calc ∑ q ∈ s, ‖kappa (tau q p)‖ ≤ ∑ q ∈ s, c * coul (tau q p) :=
        sum_le_sum fun q _ => hk _
    _ = c * ∑ q ∈ s, coul (tau q p) := by rw [mul_sum]
    _ ≤ c * ∑ nu ∈ s.image (fun q => tau q p), coul nu := by
        apply mul_le_mul_of_nonneg_left _ hc
        refine sum_comp_le_of_injOn s (fun q => tau q p) ?_ coul _
          (fun q hq => mem_image_of_mem _ hq) (fun nu _ => coul_nonneg nu)
        intro q hq q' hq' h
        exact hinj q q' p (mem_filter.mp hq).2 (mem_filter.mp hq').2 h
    _ ≤ c * (26 * J) := by
        apply mul_le_mul_of_nonneg_left _ hc
        apply sum_coul_of_inBox
        intro nu hnu
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hnu
        exact hJ q p (mem_filter.mp hq).2

lemma tk_row_l2 (hk : KernelBound kappa c) (_hc : 0 ≤ c) (hinj : RowInj rel tau) (J : ℕ)
    (hJ1 : 1 ≤ J) (hJ : ∀ q p, rel q p → ¬ InBox J (tau q p)) (q : ι) :
    ∑ p, ‖tk rel tau kappa q p‖ ^ 2 ≤ c ^ 2 * (26 / J) := by
  classical
  rw [sum_row_eq rel tau kappa q (fun z => ‖z‖ ^ 2) (by simp)]
  set s := univ.filter fun p => rel q p
  calc ∑ p ∈ s, ‖kappa (tau q p)‖ ^ 2 ≤ ∑ p ∈ s, c ^ 2 * coul (tau q p) ^ 2 := by
        refine sum_le_sum fun p _ => ?_
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hk _) 2
    _ = c ^ 2 * ∑ p ∈ s, coul (tau q p) ^ 2 := by rw [mul_sum]
    _ ≤ c ^ 2 * ∑ nu ∈ s.image (tau q), coul nu ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
        refine sum_comp_le_of_injOn s (tau q) ?_ (fun nu => coul nu ^ 2) _
          (fun p hp => mem_image_of_mem _ hp) (fun nu _ => sq_nonneg _)
        intro p hp p' hp' h
        exact hinj q p p' (mem_filter.mp hp).2 (mem_filter.mp hp').2 h
    _ ≤ c ^ 2 * (26 / J) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
        apply sum_coul_sq_of_not_inBox J hJ1
        intro nu hnu
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hnu
        exact hJ q p (mem_filter.mp hp).2

lemma tk_col_l2 (hk : KernelBound kappa c) (_hc : 0 ≤ c) (hinj : ColInj rel tau) (J : ℕ)
    (hJ1 : 1 ≤ J) (hJ : ∀ q p, rel q p → ¬ InBox J (tau q p)) (p : ι) :
    ∑ q, ‖tk rel tau kappa q p‖ ^ 2 ≤ c ^ 2 * (26 / J) := by
  classical
  rw [sum_col_eq rel tau kappa p (fun z => ‖z‖ ^ 2) (by simp)]
  set s := univ.filter fun q => rel q p
  calc ∑ q ∈ s, ‖kappa (tau q p)‖ ^ 2 ≤ ∑ q ∈ s, c ^ 2 * coul (tau q p) ^ 2 := by
        refine sum_le_sum fun q _ => ?_
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hk _) 2
    _ = c ^ 2 * ∑ q ∈ s, coul (tau q p) ^ 2 := by rw [mul_sum]
    _ ≤ c ^ 2 * ∑ nu ∈ s.image (fun q => tau q p), coul nu ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
        refine sum_comp_le_of_injOn s (fun q => tau q p) ?_ (fun nu => coul nu ^ 2) _
          (fun q hq => mem_image_of_mem _ hq) (fun nu _ => sq_nonneg _)
        intro q hq q' hq' h
        exact hinj q q' p (mem_filter.mp hq).2 (mem_filter.mp hq').2 h
    _ ≤ c ^ 2 * (26 / J) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
        apply sum_coul_sq_of_not_inBox J hJ1
        intro nu hnu
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hnu
        exact hJ q p (mem_filter.mp hq).2

end Generic

/-! ### Slices -/

section Slices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A slice structure: connected configurations share a slice label, and inside a slice a
configuration is determined by the lattice coordinate `X`. -/
structure SliceData (rel : ι → ι → Prop) {σ : Type*} (S : ι → σ) (X : ι → Lat3) : Prop where
  compat : ∀ q p, rel q p → S q = S p
  inj : ∀ q q', S q = S q' → X q = X q' → q = q'

lemma SliceData.mono {rel rel' : ι → ι → Prop} {σ : Type*} {S : ι → σ} {X : ι → Lat3}
    (h : SliceData rel S X) (hle : ∀ q p, rel' q p → rel q p) : SliceData rel' S X :=
  ⟨fun q p hr => h.compat q p (hle q p hr), h.inj⟩

/-- The slice weight `1 + |X|²`. -/
def sliceWeight (X : ι → Lat3) (q : ι) : ℝ := 1 + nsq (X q)

lemma sliceWeight_pos (X : ι → Lat3) (q : ι) : 0 < sliceWeight X q := by
  unfold sliceWeight
  linarith [nsq_nonneg (X q)]

lemma slice_weight_sum_le {σ : Type*} [DecidableEq σ] {rel : ι → ι → Prop} {S : ι → σ}
    {X : ι → Lat3} (h : SliceData rel S X) (p : ι) :
    ∑ p', (if S p' = S p then (sliceWeight X p')⁻¹ ^ 2 else 0) ≤ 53 := by
  classical
  rw [← Finset.sum_filter]
  set s := univ.filter fun p' => S p' = S p
  calc ∑ p' ∈ s, (sliceWeight X p')⁻¹ ^ 2 = ∑ p' ∈ s, ((1 + nsq (X p'))⁻¹) ^ 2 := rfl
    _ ≤ ∑ nu ∈ s.image X, ((1 + nsq nu)⁻¹) ^ 2 := by
        refine sum_comp_le_of_injOn s X ?_ (fun nu => ((1 + nsq nu)⁻¹) ^ 2) _
          (fun q hq => mem_image_of_mem _ hq) (fun nu _ => sq_nonneg _)
        intro q hq q' hq' hX
        exact h.inj q q' ((mem_filter.mp hq).2.trans (mem_filter.mp hq').2.symm) hX
    _ ≤ 53 := sum_sobolev_le _

/-- Slice-Young for a transfer kernel, in squared form: if the column `ℓ²` sums are at
most `B`, the output is bounded by `53 B` times the squared weighted input norm. -/
lemma kOp_sq_le_slice {σ : Type*} [DecidableEq σ] {rel : ι → ι → Prop} {S : ι → σ}
    {X : ι → Lat3} (h : SliceData rel S X) (kernel : ι → ι → ℂ)
    (hsupp : ∀ q p, kernel q p ≠ 0 → rel q p) {B : ℝ}
    (hcol : ∀ p, ∑ q, ‖kernel q p‖ ^ 2 ≤ B) (hvec : ι → ℝ) (hh : ∀ p, 0 ≤ hvec p) :
    ∑ q, (∑ p, ‖kernel q p‖ * hvec p) ^ 2 ≤ B * 53 * ∑ p, (sliceWeight X p * hvec p) ^ 2 := by
  have hY := slice_young_sq S (fun q p => ‖kernel q p‖) hvec (fun _ _ => norm_nonneg _) hh
    (fun q p hk => h.compat q p (hsupp q p (fun h0 => hk (by simp [h0])))) hcol
  have hM := slice_mass_le S hvec (sliceWeight X) hh (sliceWeight_pos X)
    (slice_weight_sum_le h)
  calc ∑ q, (∑ p, ‖kernel q p‖ * hvec p) ^ 2 ≤ B * ∑ p, hvec p * sliceMass S hvec p := hY
    _ ≤ B * (53 * ∑ p, (sliceWeight X p * hvec p) ^ 2) := by
        rcases isEmpty_or_nonempty ι with hι | hι
        · simp
        · have hB' : 0 ≤ B := (sum_nonneg fun q _ => sq_nonneg _).trans
            (hcol (Classical.arbitrary ι))
          exact mul_le_mul_of_nonneg_left hM hB'
    _ = B * 53 * ∑ p, (sliceWeight X p * hvec p) ^ 2 := by ring

end Slices

end PlaneWaveGridG

/-! ### Operator and form bounds for transfer kernels -/

namespace PlaneWaveGridG

open Finset

section OperatorBounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {rel : ι → ι → Prop} {tau : ι → ι → Lat3} {kappa : Lat3 → ℂ} {c : ℝ}

/-- Connected pairs with transfer in the box of radius `J`. -/
def lowRel (rel : ι → ι → Prop) (tau : ι → ι → Lat3) (J : ℕ) : ι → ι → Prop :=
  fun q p => rel q p ∧ InBox J (tau q p)

/-- Connected pairs with transfer outside the box of radius `J`. -/
def highRel (rel : ι → ι → Prop) (tau : ι → ι → Lat3) (J : ℕ) : ι → ι → Prop :=
  fun q p => rel q p ∧ ¬ InBox J (tau q p)

lemma tk_eq_low_add_high (rel : ι → ι → Prop) (tau : ι → ι → Lat3) (kappa : Lat3 → ℂ)
    (J : ℕ) :
    tk rel tau kappa = tk (lowRel rel tau J) tau kappa + tk (highRel rel tau J) tau kappa :=
  tk_split rel tau kappa (InBox J)

/-- A transfer kernel is linear in its coefficients. -/
lemma tk_sub_kernel (rel : ι → ι → Prop) (tau : ι → ι → Lat3) (k1 k2 : Lat3 → ℂ) :
    tk rel tau (fun x => k1 x - k2 x) = tk rel tau k1 - tk rel tau k2 := by
  funext q p
  simp only [Pi.sub_apply]
  by_cases h : rel q p
  · rw [tk_of_rel h, tk_of_rel h, tk_of_rel h]
  · rw [tk_of_not_rel h, tk_of_not_rel h, tk_of_not_rel h, sub_zero]

/-- Cutting the coefficients off outside the box of radius `J` restricts the transfers to it. -/
lemma tk_box_kernel (rel : ι → ι → Prop) (tau : ι → ι → Lat3) (kappa : Lat3 → ℂ) (J : ℕ) :
    tk rel tau (fun x => if InBox J x then kappa x else 0) = tk (lowRel rel tau J) tau kappa := by
  funext q p
  by_cases h : rel q p
  · by_cases hb : InBox J (tau q p)
    · rw [tk_of_rel h, tk_of_rel (show lowRel rel tau J q p from ⟨h, hb⟩), if_pos hb]
    · rw [tk_of_rel h, tk_of_not_rel (fun h' : lowRel rel tau J q p => hb h'.2), if_neg hb]
  · rw [tk_of_not_rel h, tk_of_not_rel (fun h' : lowRel rel tau J q p => h h'.1)]

/-- Coefficients that vanish on the box of radius `J` only connect transfers outside it. -/
lemma tk_eq_high_of_zero (rel : ι → ι → Prop) (tau : ι → ι → Lat3) (kappa : Lat3 → ℂ) (J : ℕ)
    (hk : ∀ x, InBox J x → kappa x = 0) :
    tk rel tau kappa = tk (highRel rel tau J) tau kappa := by
  funext q p
  by_cases h : rel q p
  · by_cases hb : InBox J (tau q p)
    · rw [tk_of_rel h, tk_of_not_rel (fun h' : highRel rel tau J q p => h'.2 hb), hk _ hb]
    · rw [tk_of_rel h, tk_of_rel (show highRel rel tau J q p from ⟨h, hb⟩)]
  · rw [tk_of_not_rel h, tk_of_not_rel (fun h' : highRel rel tau J q p => h h'.1)]

lemma sum_norm_sq_eq_norm_sq (u : EuclideanSpace ℂ ι) : ∑ p, ‖u p‖ ^ 2 = ‖u‖ ^ 2 :=
  (norm_sq_eq_sum u).symm

lemma norm_kOp_low_le (hk : KernelBound kappa c) (hc : 0 ≤ c) (hrow : RowInj rel tau)
    (hcol : ColInj rel tau) (J : ℕ) (u : EuclideanSpace ℂ ι) :
    ‖kOp (tk (lowRel rel tau J) tau kappa) u‖ ≤ c * (26 * J) * ‖u‖ := by
  have hle : ∀ q p, lowRel rel tau J q p → rel q p := fun _ _ h => h.1
  have hα : 0 ≤ c * (26 * J) := mul_nonneg hc (by positivity)
  apply norm_kOp_le_of_sq _ u (mul_nonneg hα (norm_nonneg u))
  have hS := schur_sq (fun q p => ‖tk (lowRel rel tau J) tau kappa q p‖) (fun p => ‖u p‖)
    (fun _ _ => norm_nonneg _) hα
    (tk_row_l1 hk hc (hrow.mono hle) J (fun _ _ h => h.2))
    (tk_col_l1 hk hc (hcol.mono hle) J (fun _ _ h => h.2))
  rw [sum_norm_sq_eq_norm_sq] at hS
  calc _ ≤ c * (26 * J) * (c * (26 * J)) * ‖u‖ ^ 2 := hS
    _ = (c * (26 * J) * ‖u‖) ^ 2 := by ring

lemma norm_kOp_high_le (hk : KernelBound kappa c) (hc : 0 ≤ c) (hcol : ColInj rel tau)
    {σ : Type*} [DecidableEq σ] {S : ι → σ} {X : ι → Lat3} (hS : SliceData rel S X)
    (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ ι) :
    ‖kOp (tk (highRel rel tau J) tau kappa) u‖ ≤
      c * Real.sqrt (1378 / J) * ‖wMul (sliceWeight X) u‖ := by
  have hle : ∀ q p, highRel rel tau J q p → rel q p := fun _ _ h => h.1
  have hX : 0 ≤ c * Real.sqrt (1378 / J) * ‖wMul (sliceWeight X) u‖ :=
    mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (norm_nonneg _)
  apply norm_kOp_le_of_sq _ u hX
  have h := kOp_sq_le_slice (hS.mono hle) (tk (highRel rel tau J) tau kappa)
    (fun q p h0 => rel_of_tk_ne_zero h0)
    (tk_col_l2 hk hc (hcol.mono hle) J hJ (fun _ _ h => h.2)) (fun p => ‖u p‖)
    (fun _ => norm_nonneg _)
  rw [← norm_wMul_sq _ (fun q => (sliceWeight_pos X q).le)] at h
  refine h.trans (le_of_eq ?_)
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-- Operator bound for a transfer kernel with a slice structure. -/
lemma norm_kOp_tk_le (hk : KernelBound kappa c) (hc : 0 ≤ c) (hrow : RowInj rel tau)
    (hcol : ColInj rel tau) {σ : Type*} [DecidableEq σ] {S : ι → σ} {X : ι → Lat3}
    (hS : SliceData rel S X) (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ ι) :
    ‖kOp (tk rel tau kappa) u‖ ≤
      c * (26 * J) * ‖u‖ + c * Real.sqrt (1378 / J) * ‖wMul (sliceWeight X) u‖ := by
  rw [tk_eq_low_add_high rel tau kappa J, kOp_add, LinearMap.add_apply]
  exact (norm_add_le _ _).trans (add_le_add (norm_kOp_low_le hk hc hrow hcol J u)
    (norm_kOp_high_le hk hc hcol hS J hJ u))

/-- Tail version: if small transfers can only reach `P` from `P'`, the `P`-part of the output
is controlled by the `P'`-part of the input plus the slice-regular high-transfer term. -/
lemma norm_mask_kOp_tk_le (hk : KernelBound kappa c) (hc : 0 ≤ c) (hrow : RowInj rel tau)
    (hcol : ColInj rel tau) {σ : Type*} [DecidableEq σ] {S : ι → σ} {X : ι → Lat3}
    (hS : SliceData rel S X) (J : ℕ) (hJ : 1 ≤ J) (P P' : ι → Prop)
    (hdich : ∀ q p, rel q p → InBox J (tau q p) → P q → P' p) (u : EuclideanSpace ℂ ι) :
    ‖maskOp P (kOp (tk rel tau kappa) u)‖ ≤
      c * (26 * J) * ‖maskOp P' u‖ + c * Real.sqrt (1378 / J) * ‖wMul (sliceWeight X) u‖ := by
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
  · exact (norm_maskOp_le P _).trans (norm_kOp_high_le hk hc hcol hS J hJ u)

/-- Bilinear bound with a one-sided dichotomy: every connection has its output or its input
in `P`.  The `P`-side carries the mask; the other side carries the slice weight. -/
lemma norm_inner_kOp_le_oneSided {σ : Type*} [DecidableEq σ] {S : ι → σ} {X : ι → Lat3}
    (hS : SliceData rel S X) (kernel : ι → ι → ℂ) (hsupp : ∀ q p, kernel q p ≠ 0 → rel q p)
    (P : ι → Prop) (hdich : ∀ q p, kernel q p ≠ 0 → P q ∨ P p) {B : ℝ} (hB : 0 ≤ B)
    (hcolB : ∀ p, ∑ q, ‖kernel q p‖ ^ 2 ≤ B) (hrowB : ∀ q, ∑ p, ‖kernel q p‖ ^ 2 ≤ B)
    (v u : EuclideanSpace ℂ ι) :
    ‖inner ℂ v (kOp kernel u)‖ ≤ Real.sqrt (53 * B) *
      (‖maskOp P u‖ * ‖wMul (sliceWeight X) v‖ + ‖maskOp P v‖ * ‖wMul (sliceWeight X) u‖) := by
  have hT : SliceData (fun p q => rel q p) S X :=
    ⟨fun p q h => (hS.compat q p h).symm, hS.inj⟩
  have hw : ∀ q, 0 ≤ sliceWeight X q := fun q => (sliceWeight_pos X q).le
  -- pointwise splitting
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
  have hsq : 0 ≤ Real.sqrt (53 * B) := Real.sqrt_nonneg _
  have hb1 : ∑ p, (∑ q, ‖kernel q p‖ * ‖v q‖) ^ 2 ≤
      (Real.sqrt (53 * B) * ‖wMul (sliceWeight X) v‖) ^ 2 := by
    have h := kOp_sq_le_slice hT (fun p q => kernel q p) (fun p q h0 => hsupp q p h0)
      hrowB (fun q => ‖v q‖) (fun _ => norm_nonneg _)
    rw [mul_pow, Real.sq_sqrt (by linarith), norm_wMul_sq _ hw]
    linarith
  have hb2 : ∑ q, (∑ p, ‖kernel q p‖ * ‖u p‖) ^ 2 ≤
      (Real.sqrt (53 * B) * ‖wMul (sliceWeight X) u‖) ^ 2 := by
    have h := kOp_sq_le_slice hS kernel hsupp hcolB (fun p => ‖u p‖) (fun _ => norm_nonneg _)
    rw [mul_pow, Real.sq_sqrt (by linarith), norm_wMul_sq _ hw]
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
    _ ≤ ‖maskOp P u‖ * (Real.sqrt (53 * B) * ‖wMul (sliceWeight X) v‖) +
          ‖maskOp P v‖ * (Real.sqrt (53 * B) * ‖wMul (sliceWeight X) u‖) := add_le_add t1 t2
    _ = _ := by ring

/-- Bilinear bound with a two-sided dichotomy: every connection has both endpoints in `P` or
both in `P'`.  Uses only the `ℓ¹` (Schur) bound. -/
lemma norm_inner_kOp_le_twoSided (kernel : ι → ι → ℂ) (P P' : ι → Prop)
    (hdich : ∀ q p, kernel q p ≠ 0 → (P q ∧ P p) ∨ (P' q ∧ P' p)) {α : ℝ} (hα : 0 ≤ α)
    (hrow : ∀ q, ∑ p, ‖kernel q p‖ ≤ α) (hcol : ∀ p, ∑ q, ‖kernel q p‖ ≤ α)
    (v u : EuclideanSpace ℂ ι) :
    ‖inner ℂ v (kOp kernel u)‖ ≤
      α * (‖maskOp P v‖ * ‖maskOp P u‖ + ‖maskOp P' v‖ * ‖maskOp P' u‖) := by
  have hpt : ∀ q p, ‖v q‖ * (‖kernel q p‖ * ‖u p‖) ≤
      ‖(maskOp P v) q‖ * (‖kernel q p‖ * ‖(maskOp P u) p‖) +
        ‖(maskOp P' v) q‖ * (‖kernel q p‖ * ‖(maskOp P' u) p‖) := by
    intro q p
    by_cases hk : kernel q p = 0
    · simp [hk]
    · rcases hdich q p hk with ⟨hq, hp⟩ | ⟨hq, hp⟩
      · rw [maskOp_apply_of P v hq, maskOp_apply_of P u hp]
        exact le_add_of_nonneg_right (by positivity)
      · rw [maskOp_apply_of P' v hq, maskOp_apply_of P' u hp]
        exact le_add_of_nonneg_left (by positivity)
  have hbound : ∀ (Q : ι → Prop), ∑ q, ‖(maskOp Q v) q‖ * ∑ p, ‖kernel q p‖ * ‖(maskOp Q u) p‖
      ≤ ‖maskOp Q v‖ * (α * ‖maskOp Q u‖) := by
    intro Q
    have hS := schur_sq (fun q p => ‖kernel q p‖) (fun p => ‖(maskOp Q u) p‖)
      (fun _ _ => norm_nonneg _) hα hrow hcol
    rw [sum_norm_sq_eq_norm_sq] at hS
    exact bilinear_le _ _ _ (norm_nonneg _) (mul_nonneg hα (norm_nonneg _))
      (le_of_eq (sum_norm_sq_eq_norm_sq _)) (by rw [mul_pow]; nlinarith [norm_nonneg (maskOp Q u)])
  calc ‖inner ℂ v (kOp kernel u)‖ ≤ ∑ q, ‖v q‖ * ∑ p, ‖kernel q p‖ * ‖u p‖ :=
        norm_inner_kOp_le kernel v u
    _ = ∑ q, ∑ p, ‖v q‖ * (‖kernel q p‖ * ‖u p‖) := by simp_rw [mul_sum]
    _ ≤ ∑ q, ∑ p, (‖(maskOp P v) q‖ * (‖kernel q p‖ * ‖(maskOp P u) p‖) +
          ‖(maskOp P' v) q‖ * (‖kernel q p‖ * ‖(maskOp P' u) p‖)) :=
        sum_le_sum fun q _ => sum_le_sum fun p _ => hpt q p
    _ = ∑ q, ‖(maskOp P v) q‖ * ∑ p, ‖kernel q p‖ * ‖(maskOp P u) p‖ +
          ∑ q, ‖(maskOp P' v) q‖ * ∑ p, ‖kernel q p‖ * ‖(maskOp P' u) p‖ := by
        simp_rw [mul_sum, ← sum_add_distrib]
    _ ≤ ‖maskOp P v‖ * (α * ‖maskOp P u‖) + ‖maskOp P' v‖ * (α * ‖maskOp P' u‖) :=
        add_le_add (hbound P) (hbound P')
    _ = _ := by ring

end OperatorBounds

end PlaneWaveGridG

/-! ════════════════════════════════════════════════════════════════════
## Part `Terms`
════════════════════════════════════════════════════════════════════ -/

/-!
# The interaction terms on the register

Configurations of `η` registers with `n = 2M+1` modes per direction.  For a register pair
`(i,j)` and a single register `i` we define

* grid (collocation) terms: cyclic transfers, coefficient at the centred transfer
  `gl (q i - p i)`, pair terms conserving the total momentum modulo `n`;
* Galerkin terms: integer transfers `gl (q i) - gl (p i)`, pair terms conserving the
  total momentum exactly.

We prove the injectivity and slice structures, the dichotomies, and the exact kernel
identity  `grid = Galerkin − (dropped large transfers) + (wraps)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PlaneWaveGridG

open Finset

/-- Many-particle register configurations. -/
abbrev GConfig (eta n : ℕ) := Fin eta → GMode n

section Kinds

variable {eta M : ℕ}

/-- Spectators of a one-register term. -/
def Spec1 (i : Fin eta) (q p : GConfig eta (2 * M + 1)) : Prop := ∀ k, k ≠ i → q k = p k

/-- Spectators of a pair term. -/
def Spec2 (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) : Prop :=
  ∀ k, k ≠ i → k ≠ j → q k = p k

/-- Cyclic pair relation of the collocated (grid) operator. -/
def gRel2 (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) : Prop :=
  Spec2 i j q p ∧ q i + q j = p i + p j

/-- Exact pair relation of the Galerkin operator. -/
def wRel2 (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) : Prop :=
  Spec2 i j q p ∧ gl (q i) + gl (q j) = gl (p i) + gl (p j)

/-- Centred cyclic transfer in register `i`. -/
def gTau (i : Fin eta) (q p : GConfig eta (2 * M + 1)) : Lat3 := gl (q i - p i)

/-- Integer transfer in register `i`. -/
def wTau (i : Fin eta) (q p : GConfig eta (2 * M + 1)) : Lat3 := gl (q i) - gl (p i)

/-- A register lies beyond `T` (sup norm of its centred momentum). -/
def High (T : ℕ) (r : Fin eta) (q : GConfig eta (2 * M + 1)) : Prop := ¬ InBox T (gl (q r))

lemma High.mono {T T' : ℕ} (h : T' ≤ T) {r : Fin eta} {q : GConfig eta (2 * M + 1)}
    (hq : High T r q) : High T' r q :=
  fun hh => hq (hh.mono h)

/-! ### Elementary consequences of the relations -/

lemma ofLat_add (a b : Lat3) : ofLat (M := M) (a + b) = ofLat a + ofLat b := by
  funext c
  simp [ofLat]

lemma gRel2_of_wRel2 {i j : Fin eta} {q p : GConfig eta (2 * M + 1)} (h : wRel2 i j q p) :
    gRel2 i j q p := by
  refine ⟨h.1, ?_⟩
  have h2 := congrArg (ofLat (M := M)) h.2
  rw [ofLat_add, ofLat_add, ofLat_gl, ofLat_gl, ofLat_gl, ofLat_gl] at h2
  exact h2

lemma gTau_partner {i j : Fin eta} {q p : GConfig eta (2 * M + 1)} (h : gRel2 i j q p) :
    gl (q j - p j) = -gl (q i - p i) := by
  have e : q j - p j = -(q i - p i) := by
    have := h.2
    rw [neg_sub]
    calc q j - p j = (q i + q j) - q i - p j := by abel
      _ = (p i + p j) - q i - p j := by rw [this]
      _ = p i - q i := by abel
  rw [e, gl_neg]

lemma wTau_partner {i j : Fin eta} {q p : GConfig eta (2 * M + 1)} (h : wRel2 i j q p) :
    gl (q j) - gl (p j) = -(gl (q i) - gl (p i)) := by
  have := h.2
  calc gl (q j) - gl (p j) = (gl (q i) + gl (q j)) - gl (q i) - gl (p j) := by abel
    _ = (gl (p i) + gl (p j)) - gl (q i) - gl (p j) := by rw [this]
    _ = -(gl (q i) - gl (p i)) := by abel

/-! ### Injectivity -/

lemma gRel2_rowInj (i j : Fin eta) : RowInj (gRel2 (M := M) i j) (gTau i) := by
  intro q p p' h h' ht
  have hi : p i = p' i := by
    have := gl_injective ht
    simpa using this
  funext k
  by_cases hki : k = i
  · subst hki; exact hi
  by_cases hkj : k = j
  · subst hkj
    have e1 := h.2
    have e2 := h'.2
    rw [hi] at e1
    exact add_left_cancel (e1.symm.trans e2)
  · exact (h.1 k hki hkj).symm.trans (h'.1 k hki hkj)

lemma gRel2_colInj (i j : Fin eta) : ColInj (gRel2 (M := M) i j) (gTau i) := by
  intro q q' p h h' ht
  have hi : q i = q' i := by
    have := gl_injective ht
    simpa using this
  funext k
  by_cases hki : k = i
  · subst hki; exact hi
  by_cases hkj : k = j
  · subst hkj
    have e1 := h.2
    have e2 := h'.2
    rw [hi] at e1
    exact add_left_cancel (e1.trans e2.symm)
  · exact (h.1 k hki hkj).trans (h'.1 k hki hkj).symm

lemma wRel2_rowInj (i j : Fin eta) : RowInj (wRel2 (M := M) i j) (wTau i) := by
  intro q p p' h h' ht
  have hgi : gl (p i) = gl (p' i) := by
    simp only [wTau] at ht
    exact sub_right_injective ht
  have hi : p i = p' i := gl_injective hgi
  funext k
  by_cases hki : k = i
  · subst hki; exact hi
  by_cases hkj : k = j
  · subst hkj
    have e1 := h.2
    have e2 := h'.2
    rw [hgi] at e1
    exact gl_injective (add_left_cancel (e1.symm.trans e2))
  · exact (h.1 k hki hkj).symm.trans (h'.1 k hki hkj)

lemma wRel2_colInj (i j : Fin eta) : ColInj (wRel2 (M := M) i j) (wTau i) := by
  intro q q' p h h' ht
  have hgi : gl (q i) = gl (q' i) := by
    simp only [wTau] at ht
    exact sub_left_injective ht
  have hi : q i = q' i := gl_injective hgi
  funext k
  by_cases hki : k = i
  · subst hki; exact hi
  by_cases hkj : k = j
  · subst hkj
    have e1 := h.2
    have e2 := h'.2
    rw [hgi] at e1
    exact gl_injective (add_left_cancel (e1.trans e2.symm))
  · exact (h.1 k hki hkj).trans (h'.1 k hki hkj).symm

lemma spec1_rowInj_g (i : Fin eta) : RowInj (Spec1 (M := M) i) (gTau i) := by
  intro q p p' h h' ht
  have hi : p i = p' i := by
    have := gl_injective ht
    simpa using this
  funext k
  by_cases hki : k = i
  · subst hki; exact hi
  · exact (h k hki).symm.trans (h' k hki)

lemma spec1_colInj_g (i : Fin eta) : ColInj (Spec1 (M := M) i) (gTau i) := by
  intro q q' p h h' ht
  have hi : q i = q' i := by
    have := gl_injective ht
    simpa using this
  funext k
  by_cases hki : k = i
  · subst hki; exact hi
  · exact (h k hki).trans (h' k hki).symm

lemma spec1_rowInj_w (i : Fin eta) : RowInj (Spec1 (M := M) i) (wTau i) := by
  intro q p p' h h' ht
  have hi : p i = p' i := by
    simp only [wTau] at ht
    exact gl_injective (sub_right_injective ht)
  funext k
  by_cases hki : k = i
  · subst hki; exact hi
  · exact (h k hki).symm.trans (h' k hki)

lemma spec1_colInj_w (i : Fin eta) : ColInj (Spec1 (M := M) i) (wTau i) := by
  intro q q' p h h' ht
  have hi : q i = q' i := by
    simp only [wTau] at ht
    exact gl_injective (sub_left_injective ht)
  funext k
  by_cases hki : k = i
  · subst hki; exact hi
  · exact (h k hki).trans (h' k hki).symm

/-! ### Slices -/

/-- Spectator configuration with registers `i, j` erased. -/
def erase2 (i j : Fin eta) (q : GConfig eta (2 * M + 1)) : GConfig eta (2 * M + 1) :=
  fun k => if k = i ∨ k = j then 0 else q k

/-- Spectator configuration with register `i` erased. -/
def erase1 (i : Fin eta) (q : GConfig eta (2 * M + 1)) : GConfig eta (2 * M + 1) :=
  fun k => if k = i then 0 else q k

/-- Slice label of a grid pair term: cyclic pair momentum and spectators. -/
def gSlice2 (i j : Fin eta) (q : GConfig eta (2 * M + 1)) :
    GMode (2 * M + 1) × GConfig eta (2 * M + 1) := (q i + q j, erase2 i j q)

/-- Slice label of a Galerkin pair term: integer pair momentum and spectators. -/
def wSlice2 (i j : Fin eta) (q : GConfig eta (2 * M + 1)) : Lat3 × GConfig eta (2 * M + 1) :=
  (gl (q i) + gl (q j), erase2 i j q)

/-- Slice coordinate: the centred momentum of register `i`. -/
def regCoord (i : Fin eta) (q : GConfig eta (2 * M + 1)) : Lat3 := gl (q i)

lemma erase2_eq_of_spec {i j : Fin eta} {q p : GConfig eta (2 * M + 1)} (h : Spec2 i j q p) :
    erase2 i j q = erase2 i j p := by
  funext k
  unfold erase2
  split_ifs with hk
  · rfl
  · push Not at hk
    exact h k hk.1 hk.2

lemma eq_of_erase2 {i j : Fin eta} {q q' : GConfig eta (2 * M + 1)}
    (he : erase2 i j q = erase2 i j q') (hi : q i = q' i) (hj : q j = q' j) : q = q' := by
  funext k
  by_cases hki : k = i
  · subst hki; exact hi
  by_cases hkj : k = j
  · subst hkj; exact hj
  have := congrFun he k
  simp only [erase2, hki, hkj, or_self, if_false] at this
  exact this

lemma gSlice2_data (i j : Fin eta) :
    SliceData (gRel2 (M := M) i j) (gSlice2 i j) (regCoord i) := by
  constructor
  · intro q p h
    simp only [gSlice2, Prod.mk.injEq]
    exact ⟨h.2, erase2_eq_of_spec h.1⟩
  · intro q q' hS hX
    simp only [gSlice2, Prod.mk.injEq] at hS
    have hi : q i = q' i := gl_injective hX
    refine eq_of_erase2 hS.2 hi ?_
    have := hS.1
    rw [hi] at this
    exact add_left_cancel this

lemma wSlice2_data (i j : Fin eta) :
    SliceData (wRel2 (M := M) i j) (wSlice2 i j) (regCoord i) := by
  constructor
  · intro q p h
    simp only [wSlice2, Prod.mk.injEq]
    exact ⟨h.2, erase2_eq_of_spec h.1⟩
  · intro q q' hS hX
    simp only [wSlice2, Prod.mk.injEq] at hS
    have hi : q i = q' i := gl_injective hX
    refine eq_of_erase2 hS.2 hi ?_
    have := hS.1
    simp only [regCoord] at hX
    rw [hX] at this
    exact gl_injective (add_left_cancel this)

lemma slice1_data (i : Fin eta) :
    SliceData (Spec1 (M := M) i) (erase1 i) (regCoord i) := by
  constructor
  · intro q p h
    funext k
    unfold erase1
    split_ifs with hk
    · rfl
    · exact h k hk
  · intro q q' hS hX
    funext k
    by_cases hki : k = i
    · subst hki; exact gl_injective hX
    · have := congrFun hS k
      simp only [erase1, hki, if_false] at this
      exact this

/-! ### Dichotomies for small transfers -/

lemma gRel2_lowDich (i j : Fin eta) (J T : ℕ) (hJT : J ≤ T) (hT : T ≤ M) (r : Fin eta)
    (q p : GConfig eta (2 * M + 1)) (h : gRel2 i j q p) (hd : InBox J (gTau i q p))
    (hq : High T r q) : High (T - J) r p := by
  by_cases hri : r = i
  · subst hri
    exact lowTransfer_lattice (q r) (p r) J T hJT hT hd hq
  by_cases hrj : r = j
  · subst hrj
    have hd' : InBox J (gl (q r - p r)) := by
      rw [gTau_partner h]; exact inBox_neg_iff.mpr hd
    exact lowTransfer_lattice (q r) (p r) J T hJT hT hd' hq
  · have e : q r = p r := h.1 r hri hrj
    unfold High at hq ⊢
    rw [← e]
    exact fun hh => hq (hh.mono (Nat.sub_le T J))

lemma wRel2_lowDich (i j : Fin eta) (J T : ℕ) (hJT : J ≤ T) (r : Fin eta)
    (q p : GConfig eta (2 * M + 1)) (h : wRel2 i j q p) (hd : InBox J (wTau i q p))
    (hq : High T r q) : High (T - J) r p := by
  by_cases hri : r = i
  · subst hri
    exact lowTransfer_lattice_int (gl (q r)) (gl (p r)) J T hJT hd hq
  by_cases hrj : r = j
  · subst hrj
    have hd' : InBox J (gl (q r) - gl (p r)) := by
      rw [wTau_partner h]; exact inBox_neg_iff.mpr hd
    exact lowTransfer_lattice_int (gl (q r)) (gl (p r)) J T hJT hd' hq
  · have e : q r = p r := h.1 r hri hrj
    unfold High at hq ⊢
    rw [← e]
    exact fun hh => hq (hh.mono (Nat.sub_le T J))

lemma spec1_lowDich_g (i : Fin eta) (J T : ℕ) (hJT : J ≤ T) (hT : T ≤ M) (r : Fin eta)
    (q p : GConfig eta (2 * M + 1)) (h : Spec1 i q p) (hd : InBox J (gTau i q p))
    (hq : High T r q) : High (T - J) r p := by
  by_cases hri : r = i
  · subst hri
    exact lowTransfer_lattice (q r) (p r) J T hJT hT hd hq
  · have e : q r = p r := h r hri
    unfold High at hq ⊢
    rw [← e]
    exact fun hh => hq (hh.mono (Nat.sub_le T J))

lemma spec1_lowDich_w (i : Fin eta) (J T : ℕ) (hJT : J ≤ T) (r : Fin eta)
    (q p : GConfig eta (2 * M + 1)) (h : Spec1 i q p) (hd : InBox J (wTau i q p))
    (hq : High T r q) : High (T - J) r p := by
  by_cases hri : r = i
  · subst hri
    exact lowTransfer_lattice_int (gl (q r)) (gl (p r)) J T hJT hd hq
  · have e : q r = p r := h r hri
    unfold High at hq ⊢
    rw [← e]
    exact fun hh => hq (hh.mono (Nat.sub_le T J))

/-! ### The kernel identity: grid = low Galerkin + wraps -/

/-- A pair connection wraps if one of its two integer transfers leaves the zone. -/
def Wrap2 (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) : Prop :=
  ¬ InBox M (gl (q i) - gl (p i)) ∨ ¬ InBox M (gl (q j) - gl (p j))

/-- The wrap relation of a pair term. -/
def rRel2 (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) : Prop :=
  gRel2 i j q p ∧ Wrap2 i j q p

/-- The wrap relation of a one-register term. -/
def rRel1 (i : Fin eta) (q p : GConfig eta (2 * M + 1)) : Prop :=
  Spec1 i q p ∧ ¬ InBox M (wTau i q p)

lemma tk_grid_pair_eq (i j : Fin eta) (kappa : Lat3 → ℂ) :
    tk (gRel2 (M := M) i j) (gTau i) kappa =
      tk (lowRel (wRel2 i j) (wTau i) M) (wTau i) kappa +
        tk (rRel2 i j) (gTau i) kappa := by
  funext q p
  simp only [Pi.add_apply]
  by_cases hg : gRel2 i j q p
  · by_cases hw : Wrap2 i j q p
    · have hlow : ¬ lowRel (wRel2 i j) (wTau i) M q p := by
        rintro ⟨hwr, hbox⟩
        rcases hw with h | h
        · exact h hbox
        · apply h
          rw [wTau_partner hwr]
          exact inBox_neg_iff.mpr hbox
      have hr : rRel2 i j q p := ⟨hg, hw⟩
      rw [tk_of_rel hg, tk_of_rel hr, tk_of_not_rel hlow, zero_add]
    · simp only [Wrap2, not_or, not_not] at hw
      have e1 : gl (q i - p i) = gl (q i) - gl (p i) := gl_sub_of_inBox _ _ hw.1
      have e2 : gl (q j - p j) = gl (q j) - gl (p j) := gl_sub_of_inBox _ _ hw.2
      have hwr : wRel2 i j q p := by
        refine ⟨hg.1, ?_⟩
        have h3 := gTau_partner hg
        rw [e1, e2] at h3
        have : gl (q j) - gl (p j) + (gl (q i) - gl (p i)) = 0 := by rw [h3]; abel
        calc gl (q i) + gl (q j) = gl (p i) + gl (p j) +
              (gl (q j) - gl (p j) + (gl (q i) - gl (p i))) := by abel
          _ = gl (p i) + gl (p j) := by rw [this, add_zero]
      have hlow : lowRel (wRel2 i j) (wTau i) M q p := ⟨hwr, hw.1⟩
      have hr : ¬ rRel2 i j q p := fun h =>
        Or.elim h.2 (fun h' => h' hw.1) (fun h' => h' hw.2)
      rw [tk_of_rel hg, tk_of_rel hlow, tk_of_not_rel hr, add_zero]
      simp only [gTau, wTau, e1]
  · have hlow : ¬ lowRel (wRel2 i j) (wTau i) M q p := fun h => hg (gRel2_of_wRel2 h.1)
    have hr : ¬ rRel2 i j q p := fun h => hg h.1
    rw [tk_of_not_rel hg, tk_of_not_rel hlow, tk_of_not_rel hr, add_zero]

lemma tk_grid_single_eq (i : Fin eta) (kappa : Lat3 → ℂ) :
    tk (Spec1 (M := M) i) (gTau i) kappa =
      tk (lowRel (Spec1 i) (wTau i) M) (wTau i) kappa + tk (rRel1 i) (gTau i) kappa := by
  funext q p
  simp only [Pi.add_apply]
  by_cases hs : Spec1 i q p
  · by_cases hb : InBox M (wTau i q p)
    · have e1 : gl (q i - p i) = gl (q i) - gl (p i) := gl_sub_of_inBox _ _ hb
      have hlow : lowRel (Spec1 i) (wTau i) M q p := ⟨hs, hb⟩
      have hr : ¬ rRel1 i q p := fun h => h.2 hb
      rw [tk_of_rel hs, tk_of_rel hlow, tk_of_not_rel hr, add_zero]
      simp only [gTau, wTau, e1]
    · have hlow : ¬ lowRel (Spec1 i) (wTau i) M q p := fun h => hb h.2
      have hr : rRel1 i q p := ⟨hs, hb⟩
      rw [tk_of_rel hs, tk_of_not_rel hlow, tk_of_rel hr, zero_add]
  · have hlow : ¬ lowRel (Spec1 i) (wTau i) M q p := fun h => hs h.1
    have hr : ¬ rRel1 i q p := fun h => hs h.1
    rw [tk_of_not_rel hs, tk_of_not_rel hlow, tk_of_not_rel hr, add_zero]

/-! ### Dichotomies for dropped transfers and wraps (wraps on the register of radius `2m`) -/

lemma wRel2_high_dich (s : ℕ) (i j : Fin eta) (q p : GConfig eta (2 * M + 1))
    (h : highRel (wRel2 i j) (wTau i) (2 * s) q p) :
    High s i q ∨ High s i p :=
  largeTransfer_lattice s (gl (q i)) (gl (p i)) h.2

lemma spec1_high_dich (s : ℕ) (i : Fin eta) (q p : GConfig eta (2 * M + 1))
    (h : highRel (Spec1 i) (wTau i) (2 * s) q p) :
    High s i q ∨ High s i p :=
  largeTransfer_lattice s (gl (q i)) (gl (p i)) h.2

lemma rRel2_strong_dich (m : ℕ) (i j : Fin eta) (q p : GConfig eta (2 * (2 * m) + 1))
    (h : lowRel (rRel2 i j) (gTau i) m q p) :
    (High m i q ∧ High m i p) ∨ (High m j q ∧ High m j p) := by
  obtain ⟨⟨hg, hw⟩, hd⟩ := h
  rcases hw with hw | hw
  · exact Or.inl (strongWrap_lattice m (q i) (p i) hd hw)
  · have hd' : InBox m (gl (q j - p j)) := by
      rw [gTau_partner hg]; exact inBox_neg_iff.mpr hd
    exact Or.inr (strongWrap_lattice m (q j) (p j) hd' hw)

lemma rRel2_weak_dich (m : ℕ) (i j : Fin eta) (q p : GConfig eta (2 * (2 * m) + 1))
    (h : highRel (rRel2 i j) (gTau i) m q p) :
    (High m i q ∨ High m j q) ∨ (High m i p ∨ High m j p) := by
  obtain ⟨⟨_, hw⟩, _⟩ := h
  rcases hw with hw | hw
  · rcases largeTransfer_lattice m (gl (q i)) (gl (p i)) hw with h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inr (Or.inl h1)
  · rcases largeTransfer_lattice m (gl (q j)) (gl (p j)) hw with h1 | h1
    · exact Or.inl (Or.inr h1)
    · exact Or.inr (Or.inr h1)

lemma rRel1_strong_dich (m : ℕ) (i : Fin eta) (q p : GConfig eta (2 * (2 * m) + 1))
    (h : lowRel (rRel1 i) (gTau i) m q p) : High m i q ∧ High m i p :=
  strongWrap_lattice m (q i) (p i) h.2 h.1.2

lemma rRel1_weak_dich (m : ℕ) (i : Fin eta) (q p : GConfig eta (2 * (2 * m) + 1))
    (h : highRel (rRel1 i) (gTau i) m q p) : High m i q ∨ High m i p :=
  largeTransfer_lattice m (gl (q i)) (gl (p i)) h.1.2

end Kinds

end PlaneWaveGridG

/-! ════════════════════════════════════════════════════════════════════
## Part `Spectral`
════════════════════════════════════════════════════════════════════ -/

/-!
# Spectral consequences of the operator and tail bounds

Let `H = kin + V` on a finite configuration space, with diagonal kinetic symbol
`kin = (g²/2)(W - 1)` for a weight `W ≥ 1`.  Assume the Kato--Rellich-type bound

  `‖V u‖ ≤ 26 Z J ‖u‖ + Z √(1378/J) ‖W u‖`        (some fixed `J₀ ≥ 1`)

with `Z √(1378/J₀) ≤ g²/8`.  Then, for a normalised eigenvector `H u = E u`,

* the elliptic estimate `‖W u‖ ≤ (4/3)(1 + (2/g²)(|E| + 26 Z J₀))`;
* the eigenvalue lower bound `-(52 Z J₀ + g²/4) ≤ E`;
* the pointwise tail bootstrap `‖1_P u‖ ≤ (4/(g²(T+1)²)) ‖1_P V u‖` on a set `P` where
  the kinetic symbol is at least `(g²/2)(T+1)²` and `4|E| ≤ g²(T+1)²`.

Finally the min--max comparison of two Ritz energies differing by a form error.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PlaneWaveGridG

open Finset

section Spectral

variable {ι : Type*} [Fintype ι]

/-- `Re ⟪u, (wMul w) u⟫ = ∑ w ‖u‖²`. -/
lemma re_inner_wMul (w : ι → ℝ) (u : EuclideanSpace ℂ ι) :
    (inner ℂ u (wMul w u)).re = ∑ q, w q * ‖u q‖ ^ 2 := by
  rw [PiLp.inner_apply, Complex.re_sum]
  refine sum_congr rfl fun q _ => ?_
  rw [wMul_apply, RCLike.inner_apply, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma re_inner_wMul_nonneg (w : ι → ℝ) (hw : ∀ q, 0 ≤ w q) (u : EuclideanSpace ℂ ι) :
    0 ≤ (inner ℂ u (wMul w u)).re := by
  rw [re_inner_wMul]
  exact sum_nonneg fun q _ => mul_nonneg (hw q) (sq_nonneg _)

/-- Hypotheses on a register Hamiltonian `H = wMul kin + V`. -/
structure RegHam (ι : Type*) [Fintype ι] where
  /-- The weight `W = 1 + (2/g²) kin`. -/
  W : ι → ℝ
  /-- The kinetic symbol. -/
  kin : ι → ℝ
  /-- The potential. -/
  V : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι
  /-- Momentum unit `g = 2π/L`. -/
  g : ℝ
  g_pos : 0 < g
  kin_eq : ∀ q, kin q = g ^ 2 / 2 * (W q - 1)
  W_ge_one : ∀ q, 1 ≤ W q
  /-- Total coupling. -/
  Z : ℝ
  Z_nonneg : 0 ≤ Z
  /-- The operator bound at a fixed splitting radius `J₀`. -/
  J0 : ℕ
  J0_pos : 1 ≤ J0
  small : Z * Real.sqrt (1378 / J0) ≤ g ^ 2 / 8
  op_bound : ∀ u, ‖V u‖ ≤ Z * (26 * J0) * ‖u‖ + Z * Real.sqrt (1378 / J0) * ‖wMul W u‖

namespace RegHam

variable {ι : Type*} [Fintype ι] (H : RegHam ι)

/-- The Hamiltonian. -/
noncomputable def op : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι := wMul H.kin + H.V

lemma kin_nonneg (q : ι) : 0 ≤ H.kin q := by
  rw [H.kin_eq]
  have := H.W_ge_one q
  have hg := H.g_pos
  positivity

/-- The weight in terms of the kinetic symbol. -/
lemma wMul_W_eq (u : EuclideanSpace ℂ ι) :
    wMul H.W u = u + ((2 / H.g ^ 2 : ℝ) : ℂ) • wMul H.kin u := by
  have hg := H.g_pos.ne'
  ext q
  simp only [wMul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have e : (2 / H.g ^ 2) * H.kin q = H.W q - 1 := by
    rw [H.kin_eq]
    field_simp
  have e' : ((2 / H.g ^ 2 : ℝ) : ℂ) * ((H.kin q : ℂ) * u q) = ((H.W q - 1 : ℝ) : ℂ) * u q := by
    rw [← mul_assoc, ← Complex.ofReal_mul, e]
  rw [e']
  push_cast
  ring

/-- Elliptic estimate for normalised eigenvectors. -/
lemma elliptic (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) (E : ℝ)
    (hE : H.op u = (E : ℂ) • u) :
    ‖wMul H.W u‖ ≤ 4 / 3 * (1 + 2 / H.g ^ 2 * (|E| + 26 * H.Z * H.J0)) := by
  have hg2 : 0 < H.g ^ 2 := by have := H.g_pos; positivity
  have hkin : wMul H.kin u = (E : ℂ) • u - H.V u := by
    have : wMul H.kin u + H.V u = (E : ℂ) • u := hE
    rw [← this]; abel
  have h1 : ‖wMul H.kin u‖ ≤ |E| + ‖H.V u‖ := by
    rw [hkin]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hV := H.op_bound u
  rw [hu, mul_one] at hV
  have h2 : ‖wMul H.W u‖ ≤ 1 + 2 / H.g ^ 2 * ‖wMul H.kin u‖ := by
    rw [H.wMul_W_eq u]
    refine (norm_add_le _ _).trans ?_
    rw [hu, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hsmall := H.small
  have hX := norm_nonneg (wMul H.W u)
  -- combine: ‖Wu‖ ≤ 1 + (2/g²)(|E| + 26ZJ₀ + (g²/8)‖Wu‖)
  have h3 : ‖wMul H.W u‖ ≤ 1 + 2 / H.g ^ 2 * (|E| + 26 * H.Z * H.J0) +
      2 / H.g ^ 2 * (H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖) := by
    have : ‖wMul H.kin u‖ ≤ |E| + 26 * H.Z * H.J0 +
        H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖ := by linarith
    calc ‖wMul H.W u‖ ≤ 1 + 2 / H.g ^ 2 * ‖wMul H.kin u‖ := h2
      _ ≤ 1 + 2 / H.g ^ 2 * (|E| + 26 * H.Z * H.J0 +
            H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖) := by gcongr
      _ = _ := by ring
  have h4 : 2 / H.g ^ 2 * (H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖) ≤
      1 / 4 * ‖wMul H.W u‖ := by
    have : 2 / H.g ^ 2 * (H.Z * Real.sqrt (1378 / H.J0)) ≤ 1 / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hg2]
      linarith
    calc 2 / H.g ^ 2 * (H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖)
        = (2 / H.g ^ 2 * (H.Z * Real.sqrt (1378 / H.J0))) * ‖wMul H.W u‖ := by ring
      _ ≤ 1 / 4 * ‖wMul H.W u‖ := mul_le_mul_of_nonneg_right this hX
  linarith

/-- Lower bound on any eigenvalue with a normalised eigenvector. -/
lemma eigen_lower (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) (E : ℝ)
    (hE : H.op u = (E : ℂ) • u) :
    -(52 * H.Z * H.J0 + H.g ^ 2 / 4) ≤ E := by
  have hg2 : 0 < H.g ^ 2 := by have := H.g_pos; positivity
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
  have hsmall := H.small
  have hZJ : 0 ≤ 26 * H.Z * H.J0 := by have := H.Z_nonneg; positivity
  -- ‖V u‖ ≤ 26 Z J₀ + (g²/8) ‖W u‖ ≤ 26ZJ₀ + g²/6 + (|E| + 26ZJ₀)/3
  have hVle : ‖H.V u‖ ≤ 26 * H.Z * H.J0 + H.g ^ 2 / 6 + (|E| + 26 * H.Z * H.J0) / 3 := by
    have hX := norm_nonneg (wMul H.W u)
    have h1 : H.Z * Real.sqrt (1378 / H.J0) * ‖wMul H.W u‖ ≤ H.g ^ 2 / 8 * ‖wMul H.W u‖ :=
      mul_le_mul_of_nonneg_right hsmall hX
    have h2 : H.g ^ 2 / 8 * ‖wMul H.W u‖ ≤
        H.g ^ 2 / 8 * (4 / 3 * (1 + 2 / H.g ^ 2 * (|E| + 26 * H.Z * H.J0))) :=
      mul_le_mul_of_nonneg_left hell (by positivity)
    have h3 : H.g ^ 2 / 8 * (4 / 3 * (1 + 2 / H.g ^ 2 * (|E| + 26 * H.Z * H.J0))) =
        H.g ^ 2 / 6 + (|E| + 26 * H.Z * H.J0) / 3 := by
      have hgne : H.g ≠ 0 := H.g_pos.ne'
      field_simp
      ring
    linarith
  by_cases hEn : 0 ≤ E
  · have : 0 ≤ 52 * H.Z * H.J0 + H.g ^ 2 / 4 := by have := H.Z_nonneg; positivity
    linarith
  · push Not at hEn
    rw [abs_of_neg hEn] at hVle
    linarith

end RegHam

/-- Pointwise bootstrap on a set where the kinetic symbol dominates the eigenvalue. -/
lemma tail_bootstrap (kin : ι → ℝ) (V : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (u : EuclideanSpace ℂ ι) (E : ℝ) (hE : (wMul kin + V) u = (E : ℂ) • u)
    (P : ι → Prop) {b : ℝ} (hb : 0 < b) (hkinP : ∀ q, P q → 2 * b ≤ kin q)
    (hEb : |E| ≤ b) :
    ‖maskOp P u‖ ≤ ‖maskOp P (V u)‖ / b := by
  rw [le_div_iff₀ hb]
  have hpt : ∀ q, P q → ‖u q‖ * b ≤ ‖(V u) q‖ := by
    intro q hq
    have heq : (kin q : ℂ) * u q + (V u) q = (E : ℂ) * u q := by
      have := congrArg (fun v : EuclideanSpace ℂ ι => v q) hE
      simpa [wMul_apply] using this
    have h2 : (V u) q = ((E - kin q : ℝ) : ℂ) * u q := by
      push_cast
      linear_combination heq
    rw [h2, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : b ≤ |E - kin q| := by
      rw [abs_sub_comm]
      have hk := hkinP q hq
      have hEle : E ≤ |E| := le_abs_self E
      rw [abs_of_nonneg (by linarith)]
      linarith
    nlinarith [norm_nonneg (u q)]
  have hsq : (‖maskOp P u‖ * b) ^ 2 ≤ ‖maskOp P (V u)‖ ^ 2 := by
    rw [mul_pow, norm_sq_eq_sum, norm_sq_eq_sum, sum_mul]
    refine sum_le_sum fun q _ => ?_
    by_cases hq : P q
    · rw [maskOp_apply_of P _ hq, maskOp_apply_of P _ hq, ← mul_pow]
      exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hb.le) (hpt q hq) 2
    · rw [maskOp_apply_of_not P _ hq, maskOp_apply_of_not P _ hq]
      simp
  exact (pow_le_pow_iff_left₀ (mul_nonneg (norm_nonneg _) hb.le) (norm_nonneg _)
    two_ne_zero).mp hsq

/-- The Rayleigh quotient of a normalised eigenvector is its eigenvalue. -/
lemma re_inner_eigen {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (H : V →ₗ[ℂ] V) (u : V) (hu : ‖u‖ = 1) (E : ℝ) (hE : H u = (E : ℂ) • u) :
    (inner ℂ u (H u)).re = E := by
  rw [hE, inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
  simp

/-! ### Min--max comparison -/

/-- Two Ritz energies on a common trial subspace, whose Hamiltonians differ by `Δ`, differ by
at most the larger of the two form errors at the respective minimisers. -/
lemma ritz_compare {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (H1 H2 Δ : V →ₗ[ℂ] V) (hΔ : ∀ v, H1 v = H2 v + Δ v) (F : Set V)
    (E1 E2 : ℝ) (hE1 : ∀ v ∈ F, E1 * ‖v‖ ^ 2 ≤ (inner ℂ v (H1 v)).re)
    (hE2 : ∀ v ∈ F, E2 * ‖v‖ ^ 2 ≤ (inner ℂ v (H2 v)).re)
    (u1 u2 : V) (hu1 : u1 ∈ F) (hu2 : u2 ∈ F) (hn1 : ‖u1‖ = 1) (hn2 : ‖u2‖ = 1)
    (hv1 : (inner ℂ u1 (H1 u1)).re = E1) (hv2 : (inner ℂ u2 (H2 u2)).re = E2)
    {ε : ℝ} (hε1 : ‖inner ℂ u1 (Δ u1)‖ ≤ ε) (hε2 : ‖inner ℂ u2 (Δ u2)‖ ≤ ε) :
    |E1 - E2| ≤ ε := by
  have h1 : E1 ≤ E2 + ε := by
    have h := hE1 u2 hu2
    rw [hn2, one_pow, mul_one, hΔ, inner_add_right, Complex.add_re, hv2] at h
    have := (Complex.re_le_norm (inner ℂ u2 (Δ u2))).trans hε2
    linarith
  have h2 : E2 ≤ E1 + ε := by
    have h := hE2 u1 hu1
    rw [hn1, one_pow, mul_one] at h
    have hH : (inner ℂ u1 (H2 u1)).re = E1 - (inner ℂ u1 (Δ u1)).re := by
      have e : H2 u1 = H1 u1 - Δ u1 := by rw [hΔ]; abel
      rw [e, inner_sub_right, Complex.sub_re, hv1]
    rw [hH] at h
    have h3 : |(inner ℂ u1 (Δ u1)).re| ≤ ε := (Complex.abs_re_le_norm _).trans hε1
    have := neg_le_of_abs_le h3
    linarith
  rw [abs_le]
  constructor <;> linarith

end Spectral

end PlaneWaveGridG

/-! ════════════════════════════════════════════════════════════════════
## Part `Hamiltonians`
════════════════════════════════════════════════════════════════════ -/

/-!
# The grid and Galerkin Hamiltonians on the padded register

Register radius `M = 2m` (`n' = 4m+1` points per direction), `η` registers, Coulomb amplitude
`γ`, momentum unit `g`.  The grid method collocates a kernel with real, even Fourier
coefficients `κ`; the sharp truncation `sharpKernel γ m` (`γ/|ν|²` for `‖ν‖∞ ≤ 2m`) is one of
them.  The interaction is a sum over the term index `Term η ν = Pairs η ⊕ (Fin η × ν)`
(particle pairs and particle--nucleus terms):

* `gridTerm`: collocation of the kernel `κ` (cyclic transfers, centred coefficient);
* `galTerm`: Galerkin projection of the periodic Coulomb kernel (integer transfers);
* `dTerm`: the Galerkin terms of the dropped coefficients: `γ/|ν|²` minus `κ` on the zone
  `‖ν‖∞ ≤ 2m`, and all of `γ/|ν|²` beyond it;
* `rTerm`: the wrap terms of the grid operator.

Per term, `gridTerm = galTerm - dTerm + rTerm`.  Each term satisfies the operator, tail and
form bounds of Part `Transfer` with coupling `γ` (pairs) or `ζ_ℓ γ` (nuclei) when
`|κ| ≤ γ/|ν|²`.  When `κ` agrees with `γ/|ν|²` on the box `‖ν‖∞ ≤ 2s` (`GridKernel`), the
dropped coefficients vanish there, so `dTerm` only connects transfers beyond `2s`.

The quantum particles (`RegParticles`) have masses `m_a ≥ 1` and charges `q_a`.  A term enters
the Hamiltonians with the coefficient `tcoef`: `q_i q_j` for a pair and `-q_i` for the
interaction of particle `i` with a nucleus, whose kernel carries `-ζ_ℓ`.  The kinetic weight is
`wM = 1 + Σ_a |ν_a|²/m_a` (`ν_a` the register momenta), and `wTot ≤ m̄ wM` with
`m̄ = max(1, max_a m_a)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PlaneWaveGridG

open Finset

/-- Ordered register pairs `i < j`. -/
abbrev Pairs (eta : ℕ) := {ij : Fin eta × Fin eta // ij.1 < ij.2}

/-- Clamped-nucleus data on the register: nonnegative charges and Fourier phases. -/
structure NucData (ν : Type*) where
  charge : ν → ℝ
  charge_nonneg : ∀ l, 0 ≤ charge l
  phase : ν → Lat3 → ℂ
  phase_norm : ∀ l x, ‖phase l x‖ ≤ 1
  phase_neg : ∀ l x, phase l (-x) = (starRingEnd ℂ) (phase l x)
  /-- The Galerkin reference kernel `ρ`: real, even, `|ρ| ≤ 1/|ν|²`. -/
  ref : Lat3 → ℝ
  ref_neg : ∀ x, ref (-x) = ref x
  ref_bound : ∀ x, |ref x| ≤ coul x

/-- The term index: particle pairs and (particle, nucleus) pairs. -/
abbrev Term (eta : ℕ) (ν : Type*) := Pairs eta ⊕ (Fin eta × ν)

/-- Configurations on the padded register of radius `2m`. -/
abbrev RCfg (eta m : ℕ) := GConfig eta (2 * (2 * m) + 1)

section Kernels

variable {ν : Type*} [Fintype ν]

/-- Pair coefficient `γ ρ(ν)`; the charges enter through `RegParticles.tcoef`. -/
noncomputable def kee (D : NucData ν) (gamma : ℝ) (x : Lat3) : ℂ := ((gamma * D.ref x : ℝ) : ℂ)

/-- Nuclear coefficient `-ζ_ℓ φ_ℓ(ν) γ/|ν|²`; the charges of the particles enter through
`RegParticles.tcoef`. -/
noncomputable def knuc (D : NucData ν) (gamma : ℝ) (l : ν) (x : Lat3) : ℂ :=
  -(D.charge l : ℂ) * (D.phase l x * kee D gamma x)

lemma norm_kee_le (D : NucData ν) {gamma : ℝ} (hg : 0 ≤ gamma) (x : Lat3) :
    ‖kee D gamma x‖ ≤ gamma * coul x := by
  rw [kee, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hg]
  exact mul_le_mul_of_nonneg_left (D.ref_bound x) hg

lemma kee_bound (D : NucData ν) {gamma : ℝ} (hg : 0 ≤ gamma) : KernelBound (kee D gamma) gamma :=
  fun x => norm_kee_le D hg x

lemma knuc_bound (D : NucData ν) {gamma : ℝ} (hg : 0 ≤ gamma) (l : ν) :
    KernelBound (knuc D gamma l) (D.charge l * gamma) := by
  intro x
  rw [knuc, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (D.charge_nonneg l),
    norm_mul]
  have h1 := D.phase_norm l x
  have h2 := norm_kee_le D hg x
  have h3 := D.charge_nonneg l
  calc D.charge l * (‖D.phase l x‖ * ‖kee D gamma x‖)
      ≤ D.charge l * (1 * (gamma * coul x)) := by gcongr
    _ = D.charge l * gamma * coul x := by ring

lemma kee_neg (D : NucData ν) (gamma : ℝ) (x : Lat3) : kee D gamma (-x) = kee D gamma x := by
  simp [kee, D.ref_neg]

lemma kee_conj (D : NucData ν) (gamma : ℝ) (x : Lat3) :
    (starRingEnd ℂ) (kee D gamma x) = kee D gamma x := by
  simp [kee]

lemma knuc_neg (D : NucData ν) (gamma : ℝ) (l : ν) (x : Lat3) :
    knuc D gamma l (-x) = (starRingEnd ℂ) (knuc D gamma l x) := by
  simp only [knuc, D.phase_neg, kee_neg, map_mul, map_neg, Complex.conj_ofReal, kee_conj]

/-- The pair coefficient `κ(ν)` of a grid kernel with real Fourier coefficients `κ`. -/
noncomputable def kgr (κ : Lat3 → ℝ) (x : Lat3) : ℂ := ((κ x : ℝ) : ℂ)

/-- The nuclear coefficient `-ζ_ℓ φ_ℓ(ν) κ(ν)` of a grid kernel. -/
noncomputable def kgn (D : NucData ν) (κ : Lat3 → ℝ) (l : ν) (x : Lat3) : ℂ :=
  -(D.charge l : ℂ) * (D.phase l x * kgr κ x)

/-- The dropped pair coefficient: `γ/|ν|²` minus the grid coefficient on the box of radius
`J`. -/
noncomputable def kdr (D : NucData ν) (gamma : ℝ) (κ : Lat3 → ℝ) (J : ℕ) (x : Lat3) : ℂ :=
  kee D gamma x - (if InBox J x then kgr κ x else 0)

/-- The dropped nuclear coefficient. -/
noncomputable def kdn (D : NucData ν) (gamma : ℝ) (κ : Lat3 → ℝ) (J : ℕ) (l : ν) (x : Lat3) :
    ℂ :=
  knuc D gamma l x - (if InBox J x then kgn D κ l x else 0)

/-- A grid kernel for the comparison at tail threshold `s`: real coefficients `κ` that are even,
bounded by the Coulomb coefficients `γ/|ν|²` and equal to them on the box `‖ν‖∞ ≤ 2s`. -/
structure GridKernel (gamma : ℝ) (ref : Lat3 → ℝ) (s : ℕ) (κ : Lat3 → ℝ) : Prop where
  even : ∀ x, κ (-x) = κ x
  bound : ∀ x, |κ x| ≤ gamma * coul x
  low : ∀ x, InBox (2 * s) x → κ x = gamma * ref x

/-- The sharp truncation of the Coulomb coefficients: `γ/|ν|²` for `‖ν‖∞ ≤ 2m`, else `0`. Its
kernel `wKer (sharpKernel γ m) m` is the truncated kernel `w_{≤2K}` of the manuscript. -/
noncomputable def sharpKernel (gamma : ℝ) (ref : Lat3 → ℝ) (m : ℕ) (x : Lat3) : ℝ :=
  if InBox (2 * m) x then gamma * ref x else 0

/-- The kernel class `𝒦_K` of the manuscript at `K = g m`, in the unit-torus Fourier
coefficients `κ` of the kernel: real and even (so the kernel is a real, even function),
bounded by the Coulomb coefficients `γ/|ν|²`, equal to them for `|ν| ≤ m` (that is,
`‖k_ν‖ ≤ K`), and zero outside the zone `‖ν‖∞ ≤ 2m` (`‖k_ν‖∞ ≤ 2K`). -/
structure IsGridKernel (gamma : ℝ) (ref : Lat3 → ℝ) (m : ℕ) (κ : Lat3 → ℝ) : Prop where
  even : ∀ x, κ (-x) = κ x
  bound : ∀ x, |κ x| ≤ gamma * coul x
  low : ∀ x, nsq x ≤ (m : ℝ) ^ 2 → κ x = gamma * ref x
  support : ∀ x, ¬ InBox (2 * m) x → κ x = 0

/-- A kernel of the class agrees with the Coulomb coefficients on the box of radius
`2 ⌊m/4⌋`, so the comparison runs at the tail threshold `⌊m/4⌋`. -/
lemma IsGridKernel.gridKernel {gamma : ℝ} {ref : Lat3 → ℝ} {m : ℕ} {κ : Lat3 → ℝ}
    (h : IsGridKernel gamma ref m κ) : GridKernel gamma ref (m / 4) κ := by
  refine ⟨h.even, h.bound, fun x hx => h.low x ?_⟩
  have hb : ((2 * (m / 4) : ℕ) : ℝ) ≤ (m : ℝ) / 2 := by
    have h1 : 2 * (m / 4) * 2 ≤ m := by omega
    have h2 : ((2 * (m / 4) * 2 : ℕ) : ℝ) ≤ m := by exact_mod_cast h1
    push_cast at h2 ⊢
    linarith
  have hc : ∀ c : Fin 3, ((x c : ℤ) : ℝ) ^ 2 ≤ ((m : ℝ) / 2) ^ 2 := by
    intro c
    have h0 : |x c| ≤ ((2 * (m / 4) : ℕ) : ℤ) := hx c
    have h1 : |((x c : ℤ) : ℝ)| ≤ ((2 * (m / 4) : ℕ) : ℝ) := by
      have h1' : ((|x c| : ℤ) : ℝ) ≤ (((2 * (m / 4) : ℕ) : ℤ) : ℝ) := Int.cast_le.mpr h0
      rwa [Int.cast_abs, Int.cast_natCast] at h1'
    calc ((x c : ℤ) : ℝ) ^ 2 = |((x c : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ ((m : ℝ) / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (h1.trans hb) 2
  rw [nsq_eq_sum, Fin.sum_univ_three]
  nlinarith [hc 0, hc 1, hc 2]

lemma sharpKernel_isGridKernel {gamma : ℝ} (hg : 0 ≤ gamma) {ref : Lat3 → ℝ}
    (hneg : ∀ x, ref (-x) = ref x) (hb : ∀ x, |ref x| ≤ coul x) (m : ℕ) :
    IsGridKernel gamma ref m (sharpKernel gamma ref m) := by
  refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · simp only [sharpKernel, inBox_neg_iff, hneg]
  · unfold sharpKernel
    split_ifs
    · rw [abs_mul, abs_of_nonneg hg]
      exact mul_le_mul_of_nonneg_left (hb x) hg
    · rw [abs_zero]
      exact mul_nonneg hg (coul_nonneg x)
  · unfold sharpKernel
    rw [if_pos]
    intro c
    have h2 : ((x c : ℤ) : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := (sq_le_nsq x c).trans hx
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h3 : |((x c : ℤ) : ℝ)| ≤ |(m : ℝ)| := sq_le_sq.mp h2
    rw [abs_of_nonneg hm0] at h3
    have h4 : ((|x c| : ℤ) : ℝ) ≤ (((2 * m : ℕ) : ℤ) : ℝ) := by
      rw [Int.cast_abs, Int.cast_natCast]
      push_cast
      linarith
    exact Int.cast_le.mp h4
  · unfold sharpKernel
    rw [if_neg hx]

lemma kgr_bound {gamma : ℝ} {κ : Lat3 → ℝ} (hκ : ∀ x, |κ x| ≤ gamma * coul x) :
    KernelBound (kgr κ) gamma := fun x => by
  rw [kgr, Complex.norm_real, Real.norm_eq_abs]
  exact hκ x

lemma kgn_bound (D : NucData ν) {gamma : ℝ} {κ : Lat3 → ℝ} (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (l : ν) : KernelBound (kgn D κ l) (D.charge l * gamma) := by
  intro x
  rw [kgn, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (D.charge_nonneg l),
    norm_mul]
  have h1 := D.phase_norm l x
  have h2 := kgr_bound hκ x
  have h3 := D.charge_nonneg l
  calc D.charge l * (‖D.phase l x‖ * ‖kgr κ x‖)
      ≤ D.charge l * (1 * (gamma * coul x)) := by gcongr
    _ = D.charge l * gamma * coul x := by ring

lemma kdr_bound (D : NucData ν) {gamma : ℝ} (hg : 0 ≤ gamma) {κ : Lat3 → ℝ}
    (hκ : ∀ x, |κ x| ≤ gamma * coul x) (J : ℕ) : KernelBound (kdr D gamma κ J) (2 * gamma) := by
  intro x
  unfold kdr
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖kee D gamma x‖ ≤ gamma * coul x := kee_bound D hg x
  have h2 : ‖(if InBox J x then kgr κ x else 0 : ℂ)‖ ≤ gamma * coul x := by
    split_ifs
    · exact kgr_bound hκ x
    · rw [norm_zero]; exact mul_nonneg hg (coul_nonneg x)
  linarith

lemma kdn_bound (D : NucData ν) {gamma : ℝ} (hg : 0 ≤ gamma) {κ : Lat3 → ℝ}
    (hκ : ∀ x, |κ x| ≤ gamma * coul x) (J : ℕ) (l : ν) :
    KernelBound (kdn D gamma κ J l) (2 * (D.charge l * gamma)) := by
  intro x
  unfold kdn
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖knuc D gamma l x‖ ≤ D.charge l * gamma * coul x := knuc_bound D hg l x
  have h2 : ‖(if InBox J x then kgn D κ l x else 0 : ℂ)‖ ≤ D.charge l * gamma * coul x := by
    split_ifs
    · exact kgn_bound D hκ l x
    · rw [norm_zero]; exact mul_nonneg (mul_nonneg (D.charge_nonneg l) hg) (coul_nonneg x)
  linarith

lemma kdr_eq_zero (D : NucData ν) {gamma : ℝ} {κ : Lat3 → ℝ} {s : ℕ}
    (hκ : GridKernel gamma D.ref s κ) {J : ℕ}
    (hJ : 2 * s ≤ J) {x : Lat3} (hx : InBox (2 * s) x) : kdr D gamma κ J x = 0 := by
  rw [kdr, if_pos (hx.mono hJ), kgr, hκ.low x hx, kee, sub_self]

lemma kdn_eq_zero (D : NucData ν) {gamma : ℝ} {κ : Lat3 → ℝ} {s : ℕ}
    (hκ : GridKernel gamma D.ref s κ)
    {J : ℕ} (hJ : 2 * s ≤ J) (l : ν) {x : Lat3} (hx : InBox (2 * s) x) :
    kdn D gamma κ J l x = 0 := by
  rw [kdn, if_pos (hx.mono hJ), kgn, kgr, hκ.low x hx, knuc, kee, sub_self]

lemma kgr_neg {κ : Lat3 → ℝ} (hκ : ∀ x, κ (-x) = κ x) (x : Lat3) : kgr κ (-x) = kgr κ x := by
  rw [kgr, kgr, hκ]

lemma kgr_conj (κ : Lat3 → ℝ) (x : Lat3) : (starRingEnd ℂ) (kgr κ x) = kgr κ x :=
  Complex.conj_ofReal _

lemma kgn_neg (D : NucData ν) {κ : Lat3 → ℝ} (hκ : ∀ x, κ (-x) = κ x) (l : ν) (x : Lat3) :
    kgn D κ l (-x) = (starRingEnd ℂ) (kgn D κ l x) := by
  simp only [kgn, D.phase_neg, kgr_neg hκ, map_mul, map_neg, Complex.conj_ofReal, kgr_conj]

variable (eta m : ℕ) (D : NucData ν) (gamma : ℝ) (κ : Lat3 → ℝ)

/-- Collocation (grid) terms of the kernel `κ`. -/
noncomputable def gridTerm : Term eta ν → RCfg eta m → RCfg eta m → ℂ
  | Sum.inl pr => tk (gRel2 pr.1.1 pr.1.2) (gTau pr.1.1) (kgr κ)
  | Sum.inr il => tk (Spec1 il.1) (gTau il.1) (kgn D κ il.2)

/-- Galerkin terms. -/
noncomputable def galTerm : Term eta ν → RCfg eta m → RCfg eta m → ℂ
  | Sum.inl pr => tk (wRel2 pr.1.1 pr.1.2) (wTau pr.1.1) (kee D gamma)
  | Sum.inr il => tk (Spec1 il.1) (wTau il.1) (knuc D gamma il.2)

/-- Dropped Galerkin transfers: the Galerkin terms of the Coulomb coefficients minus the
kernel `κ` on the zone `‖ν‖∞ ≤ 2m`. -/
noncomputable def dTerm : Term eta ν → RCfg eta m → RCfg eta m → ℂ
  | Sum.inl pr => tk (wRel2 pr.1.1 pr.1.2) (wTau pr.1.1) (kdr D gamma κ (2 * m))
  | Sum.inr il => tk (Spec1 il.1) (wTau il.1) (kdn D gamma κ (2 * m) il.2)

/-- Wrap terms of the grid operator. -/
noncomputable def rTerm : Term eta ν → RCfg eta m → RCfg eta m → ℂ
  | Sum.inl pr => tk (rRel2 pr.1.1 pr.1.2) (gTau pr.1.1) (kgr κ)
  | Sum.inr il => tk (rRel1 il.1) (gTau il.1) (kgn D κ il.2)

/-- Coupling constant of a term. -/
noncomputable def coupling : Term eta ν → ℝ
  | Sum.inl _ => gamma
  | Sum.inr il => D.charge il.2 * gamma

variable {eta m D gamma κ}

lemma coupling_nonneg (hg : 0 ≤ gamma) (t : Term eta ν) : 0 ≤ coupling eta D gamma t := by
  cases t with
  | inl pr => exact hg
  | inr il => exact mul_nonneg (D.charge_nonneg il.2) hg

/-- The exact kernel identity, per term. -/
lemma gridTerm_eq (t : Term eta ν) :
    gridTerm eta m D κ t = galTerm eta m D gamma t - dTerm eta m D gamma κ t +
      rTerm eta m D κ t := by
  cases t with
  | inl pr =>
    simp only [gridTerm, galTerm, dTerm, rTerm]
    have key : tk (wRel2 (M := 2 * m) pr.1.1 pr.1.2) (wTau pr.1.1) (kee D gamma) -
        tk (wRel2 (M := 2 * m) pr.1.1 pr.1.2) (wTau pr.1.1) (kdr D gamma κ (2 * m)) =
        tk (lowRel (wRel2 (M := 2 * m) pr.1.1 pr.1.2) (wTau pr.1.1) (2 * m)) (wTau pr.1.1)
          (kgr κ) := by
      rw [← tk_sub_kernel, ← tk_box_kernel]
      congr 1
      funext x
      simp only [kdr]
      ring
    rw [tk_grid_pair_eq, key]
  | inr il =>
    simp only [gridTerm, galTerm, dTerm, rTerm]
    have key : tk (Spec1 (M := 2 * m) il.1) (wTau il.1) (knuc D gamma il.2) -
        tk (Spec1 (M := 2 * m) il.1) (wTau il.1) (kdn D gamma κ (2 * m) il.2) =
        tk (lowRel (Spec1 (M := 2 * m) il.1) (wTau il.1) (2 * m)) (wTau il.1)
          (kgn D κ il.2) := by
      rw [← tk_sub_kernel, ← tk_box_kernel]
      congr 1
      funext x
      simp only [kdn]
      ring
    rw [tk_grid_single_eq, key]

end Kernels

/-! ### Weights -/

section Weights

variable {eta m : ℕ}

/-- The total weight `1 + ∑_a |gl q_a|²`. -/
noncomputable def wTot (q : RCfg eta m) : ℝ := 1 + ∑ a, nsq (gl (q a))

lemma wTot_ge_one (q : RCfg eta m) : 1 ≤ wTot q := by
  unfold wTot
  linarith [sum_nonneg fun a (_ : a ∈ univ) => nsq_nonneg (gl (q a))]

lemma sliceWeight_le_wTot (i : Fin eta) (q : RCfg eta m) :
    sliceWeight (regCoord i) q ≤ wTot q := by
  unfold sliceWeight regCoord wTot
  have := Finset.single_le_sum (f := fun a => nsq (gl (q a)))
    (fun a _ => nsq_nonneg _) (Finset.mem_univ i)
  linarith

lemma norm_wMul_slice_le (i : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (sliceWeight (regCoord i)) u‖ ≤ ‖wMul wTot u‖ :=
  norm_wMul_mono (fun q => (sliceWeight_pos _ q).le) (sliceWeight_le_wTot i) u

lemma wTot_ge_of_high {T : ℕ} {r : Fin eta} {q : RCfg eta m} (h : High T r q) :
    1 + ((T : ℝ) + 1) ^ 2 ≤ wTot q := by
  have h1 := nsq_ge_of_not_inBox h
  have h2 := Finset.single_le_sum (f := fun a => nsq (gl (q a)))
    (fun a _ => nsq_nonneg _) (Finset.mem_univ r)
  unfold wTot
  linarith

end Weights

/-! ### Particles: masses and charges -/

section Particles

/-- The quantum particles on the register, in atomic units: masses at least one and
charges. -/
structure RegParticles (eta : ℕ) where
  mass : Fin eta → ℝ
  one_le_mass : ∀ a, 1 ≤ mass a
  charge : Fin eta → ℝ

namespace RegParticles

variable {eta : ℕ} (P : RegParticles eta)

/-- Electrons: mass one and charge `-1`. -/
def electrons (eta : ℕ) : RegParticles eta where
  mass := fun _ => 1
  one_le_mass := fun _ => le_rfl
  charge := fun _ => -1

lemma mass_pos (a : Fin eta) : 0 < P.mass a := lt_of_lt_of_le one_pos (P.one_le_mass a)

/-- The largest mass, at least one. -/
def maxMass : ℝ := Finset.univ.fold max 1 P.mass

lemma one_le_maxMass : 1 ≤ P.maxMass := by
  unfold maxMass
  exact (Finset.le_fold_max _).mpr (Or.inl le_rfl)

lemma maxMass_pos : 0 < P.maxMass := lt_of_lt_of_le one_pos P.one_le_maxMass

lemma mass_le_maxMass (a : Fin eta) : P.mass a ≤ P.maxMass := by
  unfold maxMass
  exact (Finset.le_fold_max _).mpr (Or.inr ⟨a, Finset.mem_univ a, le_rfl⟩)

/-- The coefficient of a term: `q_i q_j` for the pair `(i, j)` and `-q_i` for the interaction
of particle `i` with a nucleus, whose kernel `knuc` carries the factor `-ζ_ℓ`. -/
def tcoef {ν : Type*} : Term eta ν → ℝ
  | Sum.inl pr => P.charge pr.1.1 * P.charge pr.1.2
  | Sum.inr il => -P.charge il.1

end RegParticles

variable {eta m : ℕ} (P : RegParticles eta)

/-- The mass-weighted weight `1 + ∑_a |gl q_a|² / m_a`. -/
noncomputable def wM (q : RCfg eta m) : ℝ := 1 + ∑ a, nsq (gl (q a)) / P.mass a

lemma wM_ge_one (q : RCfg eta m) : 1 ≤ wM P q := by
  unfold wM
  have : 0 ≤ ∑ a, nsq (gl (q a)) / P.mass a :=
    sum_nonneg fun a _ => div_nonneg (nsq_nonneg _) (P.mass_pos a).le
  linarith

/-- `1 + ∑_a |ν_a|² ≤ m̄ (1 + ∑_a |ν_a|²/m_a)`. -/
lemma wTot_le_maxMass_mul_wM (q : RCfg eta m) : wTot q ≤ P.maxMass * wM P q := by
  unfold wTot wM
  have hM := P.one_le_maxMass
  rw [mul_add, mul_one, Finset.mul_sum]
  have h : ∀ a ∈ (univ : Finset (Fin eta)),
      nsq (gl (q a)) ≤ P.maxMass * (nsq (gl (q a)) / P.mass a) := by
    intro a _
    have hma := P.mass_pos a
    have hn := nsq_nonneg (gl (q a))
    rw [mul_div_assoc', le_div_iff₀ hma]
    nlinarith [P.mass_le_maxMass a]
  linarith [Finset.sum_le_sum h]

lemma norm_wMul_wTot_le (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul wTot u‖ ≤ P.maxMass * ‖wMul (wM P) u‖ := by
  have h1 := norm_wMul_mono (fun q => le_trans zero_le_one (wTot_ge_one q))
    (wTot_le_maxMass_mul_wM P) u
  have h2 : wMul (fun q => P.maxMass * wM P q) u = ((P.maxMass : ℝ) : ℂ) • wMul (wM P) u := by
    ext q
    simp only [wMul_apply, PiLp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [h2, norm_smul, Complex.norm_real, Real.norm_of_nonneg P.maxMass_pos.le] at h1
  exact h1

lemma wM_ge_of_high {T : ℕ} {r : Fin eta} {q : RCfg eta m} (h : High T r q) :
    1 + ((T : ℝ) + 1) ^ 2 / P.maxMass ≤ wM P q := by
  have hM := P.maxMass_pos
  have h1 := nsq_ge_of_not_inBox h
  have h2 := Finset.single_le_sum (f := fun a => nsq (gl (q a)) / P.mass a)
    (fun a _ => div_nonneg (nsq_nonneg _) (P.mass_pos a).le) (Finset.mem_univ r)
  have h3 : ((T : ℝ) + 1) ^ 2 / P.maxMass ≤ nsq (gl (q r)) / P.mass r :=
    calc ((T : ℝ) + 1) ^ 2 / P.maxMass ≤ nsq (gl (q r)) / P.maxMass := by gcongr
      _ ≤ nsq (gl (q r)) / P.mass r :=
          div_le_div_of_nonneg_left (nsq_nonneg _) (P.mass_pos r) (P.mass_le_maxMass r)
  unfold wM
  linarith

end Particles

/-! ### Per-term bounds -/

section TermBounds

variable {ν : Type*} [Fintype ν] {eta m : ℕ} {D : NucData ν} {gamma : ℝ} {κ : Lat3 → ℝ}

lemma gridTerm_op (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x) (t : Term eta ν) (J : ℕ)
    (hJ : 1 ≤ J) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖kOp (gridTerm eta m D κ t) u‖ ≤ coupling eta D gamma t * (26 * J) * ‖u‖ +
      coupling eta D gamma t * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  have hc := coupling_nonneg (D := D) hg t
  cases t with
  | inl pr =>
    have h := norm_kOp_tk_le (kgr_bound hκ) hg (gRel2_rowInj pr.1.1 pr.1.2)
      (gRel2_colInj pr.1.1 pr.1.2) (gSlice2_data pr.1.1 pr.1.2) J hJ u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))
  | inr il =>
    have h := norm_kOp_tk_le (kgn_bound D hκ il.2) (mul_nonneg (D.charge_nonneg il.2) hg)
      (spec1_rowInj_g il.1) (spec1_colInj_g il.1) (slice1_data il.1) J hJ u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))

lemma galTerm_op (hg : 0 ≤ gamma) (t : Term eta ν) (J : ℕ) (hJ : 1 ≤ J)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖kOp (galTerm eta m D gamma t) u‖ ≤ coupling eta D gamma t * (26 * J) * ‖u‖ +
      coupling eta D gamma t * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  have hc := coupling_nonneg (D := D) hg t
  cases t with
  | inl pr =>
    have h := norm_kOp_tk_le (kee_bound D hg) hg (wRel2_rowInj pr.1.1 pr.1.2)
      (wRel2_colInj pr.1.1 pr.1.2) (wSlice2_data pr.1.1 pr.1.2) J hJ u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))
  | inr il =>
    have h := norm_kOp_tk_le (knuc_bound D hg il.2) (mul_nonneg (D.charge_nonneg il.2) hg)
      (spec1_rowInj_w il.1) (spec1_colInj_w il.1) (slice1_data il.1) J hJ u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))

lemma gridTerm_tail (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x) (t : Term eta ν)
    (J T : ℕ) (hJ : 1 ≤ J) (hJT : J ≤ T) (hT : T ≤ 2 * m) (r : Fin eta)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) (kOp (gridTerm eta m D κ t) u)‖ ≤
      coupling eta D gamma t * (26 * J) * ‖maskOp (High (T - J) r) u‖ +
      coupling eta D gamma t * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  have hc := coupling_nonneg (D := D) hg t
  cases t with
  | inl pr =>
    have h := norm_mask_kOp_tk_le (kgr_bound hκ) hg (gRel2_rowInj pr.1.1 pr.1.2)
      (gRel2_colInj pr.1.1 pr.1.2) (gSlice2_data pr.1.1 pr.1.2) J hJ (High T r)
      (High (T - J) r) (fun q p hr hd hq => gRel2_lowDich pr.1.1 pr.1.2 J T hJT hT r q p hr hd hq) u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))
  | inr il =>
    have h := norm_mask_kOp_tk_le (kgn_bound D hκ il.2) (mul_nonneg (D.charge_nonneg il.2) hg)
      (spec1_rowInj_g il.1) (spec1_colInj_g il.1) (slice1_data il.1) J hJ (High T r)
      (High (T - J) r) (fun q p hr hd hq => spec1_lowDich_g il.1 J T hJT hT r q p hr hd hq) u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))

lemma galTerm_tail (hg : 0 ≤ gamma) (t : Term eta ν) (J T : ℕ) (hJ : 1 ≤ J) (hJT : J ≤ T)
    (r : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) (kOp (galTerm eta m D gamma t) u)‖ ≤
      coupling eta D gamma t * (26 * J) * ‖maskOp (High (T - J) r) u‖ +
      coupling eta D gamma t * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  have hc := coupling_nonneg (D := D) hg t
  cases t with
  | inl pr =>
    have h := norm_mask_kOp_tk_le (kee_bound D hg) hg (wRel2_rowInj pr.1.1 pr.1.2)
      (wRel2_colInj pr.1.1 pr.1.2) (wSlice2_data pr.1.1 pr.1.2) J hJ (High T r)
      (High (T - J) r) (fun q p hr hd hq => wRel2_lowDich pr.1.1 pr.1.2 J T hJT r q p hr hd hq) u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))
  | inr il =>
    have h := norm_mask_kOp_tk_le (knuc_bound D hg il.2) (mul_nonneg (D.charge_nonneg il.2) hg)
      (spec1_rowInj_w il.1) (spec1_colInj_w il.1) (slice1_data il.1) J hJ (High T r)
      (High (T - J) r) (fun q p hr hd hq => spec1_lowDich_w il.1 J T hJT r q p hr hd hq) u
    refine h.trans (add_le_add le_rfl ?_)
    exact mul_le_mul_of_nonneg_left (norm_wMul_slice_le _ u) (mul_nonneg hc (Real.sqrt_nonneg _))

/-- The form constant of the aliasing estimate with tails at threshold `s`. -/
noncomputable def formA (s m : ℕ) : ℝ :=
  2 * Real.sqrt (1378 / (2 * s)) + 2 * Real.sqrt (1378 / m)

lemma formA_nonneg (s m : ℕ) : 0 ≤ formA s m := by
  unfold formA; positivity

/-- `√(53 c² (26/J)) = c √(1378/J)`. -/
lemma sqrt_coupling_eq (c : ℝ) (hc : 0 ≤ c) (J : ℕ) :
    Real.sqrt (53 * (c ^ 2 * (26 / (J : ℝ)))) = c * Real.sqrt (1378 / J) := by
  rw [show 53 * (c ^ 2 * (26 / (J : ℝ))) = c ^ 2 * (1378 / J) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

/-- One-sided form bound with masks bounded by `τ` and slice weights by `wTot`. -/
lemma oneSided_to_tau {X Y Z τu τv Xu Xv a b : ℝ} (hc : 0 ≤ X)
    (hτu0 : 0 ≤ τu) (hτv0 : 0 ≤ τv) (ha : a ≤ τu) (hb : b ≤ τv) (hY : Y ≤ Xv) (hZ : Z ≤ Xu)
    (hY0 : 0 ≤ Y) (hZ0 : 0 ≤ Z) (_ha0 : 0 ≤ a) (_hb0 : 0 ≤ b) :
    X * (a * Y + b * Z) ≤ X * (τu * Xv + τv * Xu) := by
  apply mul_le_mul_of_nonneg_left _ hc
  exact add_le_add (mul_le_mul ha hY hY0 hτu0) (mul_le_mul hb hZ hZ0 hτv0)

/-- Form bound for the dropped and wrap parts of one term, with the tails of both states
beyond `s` bounded by `τu`, `τv`. The dropped transfers only connect transfers beyond `2s`. -/
lemma term_form (hg : 0 ≤ gamma) {s : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    (hκ : GridKernel gamma D.ref s κ)
    (t : Term eta ν) (u v : EuclideanSpace ℂ (RCfg eta m)) {τu τv : ℝ} (hτu0 : 0 ≤ τu)
    (hτv0 : 0 ≤ τv) (hτu : ∀ r, ‖maskOp (High s r) u‖ ≤ τu)
    (hτv : ∀ r, ‖maskOp (High s r) v‖ ≤ τv) :
    ‖inner ℂ v (kOp (dTerm eta m D gamma κ t) u)‖ + ‖inner ℂ v (kOp (rTerm eta m D κ t) u)‖ ≤
      coupling eta D gamma t * (formA s m * (τu * ‖wMul wTot v‖ + τv * ‖wMul wTot u‖) +
        52 * m * (τv * τu)) := by
  have hm : 1 ≤ m := hs.trans hsm
  have hs2 : 1 ≤ 2 * s := by omega
  have h2sm : 2 * s ≤ 2 * m := by omega
  have hc := coupling_nonneg (D := D) hg t
  set Xu := ‖wMul wTot u‖
  set Xv := ‖wMul wTot v‖
  -- the tails beyond `m` are at most those beyond `s`
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
    -- dropped transfers, all beyond `2s`
    rw [tk_eq_high_of_zero (wRel2 i j) (wTau i) (kdr D gamma κ (2 * m)) (2 * s)
      (fun x hx => kdr_eq_zero D hκ h2sm hx)]
    have hleD : ∀ q p, highRel (wRel2 i j) (wTau i) (2 * s) q p → wRel2 (M := 2 * m) i j q p :=
      fun _ _ h => h.1
    have hD := norm_inner_kOp_le_oneSided ((wSlice2_data i j).mono hleD)
      (tk (highRel (wRel2 i j) (wTau i) (2 * s)) (wTau i) (kdr D gamma κ (2 * m)))
      (fun q p h0 => rel_of_tk_ne_zero h0) (High s i)
      (fun q p h0 => wRel2_high_dich s i j q p (rel_of_tk_ne_zero h0))
      (B := (2 * gamma) ^ 2 * (26 / ((2 * s : ℕ) : ℝ))) (by positivity)
      (tk_col_l2 (kdr_bound D hg hκ.bound _) (by positivity) ((wRel2_colInj i j).mono hleD)
        (2 * s) hs2 (fun _ _ h => h.2))
      (tk_row_l2 (kdr_bound D hg hκ.bound _) (by positivity) ((wRel2_rowInj i j).mono hleD)
        (2 * s) hs2 (fun _ _ h => h.2)) v u
    rw [sqrt_coupling_eq (2 * gamma) (by positivity)] at hD
    have hD' := hD.trans (oneSided_to_tau (by positivity) hτu0 hτv0 (hτu i) (hτv i)
      (norm_wMul_slice_le i v) (norm_wMul_slice_le i u) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _))
    -- wraps: strong and weak parts
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
    have hW := norm_inner_kOp_le_oneSided ((gSlice2_data i j).mono hleW)
      (tk (highRel (rRel2 i j) (gTau i) m) (gTau i) (kgr κ))
      (fun q p h0 => rel_of_tk_ne_zero h0) (fun q => High m i q ∨ High m j q)
      (fun q p h0 => rRel2_weak_dich m i j q p (rel_of_tk_ne_zero h0))
      (B := gamma ^ 2 * (26 / (m : ℝ))) (by positivity)
      (tk_col_l2 (kgr_bound hκ.bound) hg ((gRel2_colInj i j).mono hleW) m hm
        (fun _ _ h => h.2))
      (tk_row_l2 (kgr_bound hκ.bound) hg ((gRel2_rowInj i j).mono hleW) m hm
        (fun _ _ h => h.2)) v u
    rw [sqrt_coupling_eq gamma hg] at hW
    have hW' := hW.trans (oneSided_to_tau (by positivity) (by positivity : 0 ≤ 2 * τu)
      (by positivity : 0 ≤ 2 * τv) (orBound _ _ u τu (hτu' i) (hτu' j))
      (orBound _ _ v τv (hτv' i) (hτv' j)) (norm_wMul_slice_le i v) (norm_wMul_slice_le i u)
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _))
    have htot := add_le_add hD' (norm_add_le _ _ |>.trans (add_le_add (hS.trans hS') hW'))
    refine htot.trans (le_of_eq ?_)
    unfold formA
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
    have hD := norm_inner_kOp_le_oneSided ((slice1_data i).mono hleD)
      (tk (highRel (Spec1 i) (wTau i) (2 * s)) (wTau i) (kdn D gamma κ (2 * m) l))
      (fun q p h0 => rel_of_tk_ne_zero h0) (High s i)
      (fun q p h0 => spec1_high_dich s i q p (rel_of_tk_ne_zero h0))
      (B := (2 * (D.charge l * gamma)) ^ 2 * (26 / ((2 * s : ℕ) : ℝ))) (by positivity)
      (tk_col_l2 (kdn_bound D hg hκ.bound _ l) (by positivity) ((spec1_colInj_w i).mono hleD)
        (2 * s) hs2 (fun _ _ h => h.2))
      (tk_row_l2 (kdn_bound D hg hκ.bound _ l) (by positivity) ((spec1_rowInj_w i).mono hleD)
        (2 * s) hs2 (fun _ _ h => h.2)) v u
    rw [sqrt_coupling_eq _ (by positivity)] at hD
    have hD' := hD.trans (oneSided_to_tau (by positivity) hτu0 hτv0 (hτu i) (hτv i)
      (norm_wMul_slice_le i v) (norm_wMul_slice_le i u) (norm_nonneg _) (norm_nonneg _)
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
    have hW := norm_inner_kOp_le_oneSided ((slice1_data i).mono hleW)
      (tk (highRel (rRel1 i) (gTau i) m) (gTau i) (kgn D κ l))
      (fun q p h0 => rel_of_tk_ne_zero h0) (High m i)
      (fun q p h0 => rRel1_weak_dich m i q p (rel_of_tk_ne_zero h0))
      (B := (D.charge l * gamma) ^ 2 * (26 / (m : ℝ))) (by positivity)
      (tk_col_l2 (kgn_bound D hκ.bound l) hcl ((spec1_colInj_g i).mono hleW) m hm
        (fun _ _ h => h.2))
      (tk_row_l2 (kgn_bound D hκ.bound l) hcl ((spec1_rowInj_g i).mono hleW) m hm
        (fun _ _ h => h.2)) v u
    rw [sqrt_coupling_eq _ hcl] at hW
    have hW' := hW.trans (oneSided_to_tau (by positivity) hτu0 hτv0 (hτu' i) (hτv' i)
      (norm_wMul_slice_le i v) (norm_wMul_slice_le i u) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _))
    have htot := add_le_add hD' (norm_add_le _ _ |>.trans (add_le_add (hS.trans hS') hW'))
    refine htot.trans ?_
    unfold formA
    push_cast
    have hX : 0 ≤ τu * Xv + τv * Xu := by positivity
    have hq : 0 ≤ Real.sqrt (1378 / (m : ℝ)) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hcl (mul_nonneg hq hX)]

end TermBounds

end PlaneWaveGridG

/-! ════════════════════════════════════════════════════════════════════
## Part `Symmetry`
════════════════════════════════════════════════════════════════════ -/

/-!
# Hermiticity, exchange symmetry and ground eigenpairs

The Galerkin Hamiltonian, and the grid Hamiltonian of an even kernel `κ`, are symmetric
operators that commute with every exchange of two registers of equal mass and charge, so they
preserve every exchange sector of a labelling whose blocks have equal masses and charges, and
have normalised ground eigenpairs in a sector whenever the sector is nonzero.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PlaneWaveGridG

open Finset

/-! ### Symmetric kernel operators -/

section Herm

variable {ι : Type*} [Fintype ι]

lemma kOp_isSymmetric (k : ι → ι → ℂ) (hk : ∀ q p, k p q = (starRingEnd ℂ) (k q p)) :
    (kOp k).IsSymmetric := by
  intro u v
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [kOp_apply, RCLike.inner_apply, map_sum, map_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
  rw [hk p q, Complex.conj_conj]
  ring

lemma wMul_isSymmetric (w : ι → ℝ) : (wMul w).IsSymmetric := by
  intro u v
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine sum_congr rfl fun q _ => ?_
  simp only [wMul_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

end Herm

/-! ### Exchange of registers -/

section Exchange

variable {eta n : ℕ}

/-- Exchange of registers `a` and `b` (the release file's `swapConfig`). -/
def swapCfg (a b : Fin eta) (q : GConfig eta n) : GConfig eta n :=
  fun k => q (Equiv.swap a b k)

lemma swapCfg_involutive (a b : Fin eta) : Function.Involutive (swapCfg (n := n) a b) := by
  intro q
  funext k
  simp [swapCfg]

/-- The exchange as an equivalence of configurations. -/
def swapCfgEquiv (a b : Fin eta) : GConfig eta n ≃ GConfig eta n :=
  (swapCfg_involutive a b).toPerm _

/-- The exchange sector of the labelling `lab` with exchange signs `sgn`: exchanging two
registers with equal labels multiplies a state by the sign of the register. With the signs
`-1` and the constant labelling this is full antisymmetry. -/
def IsSec [NeZero n] (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ)
    (u : EuclideanSpace ℂ (GConfig eta n)) : Prop :=
  ∀ a b : Fin eta, a ≠ b → lab a = lab b → ∀ q, u (swapCfg a b q) = sgn a * u q

variable [NeZero n]

/-- The exchange sector `(sgn, lab)`. -/
def secSubmodule (eta n : ℕ) [NeZero n] (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (GConfig eta n)) where
  carrier := IsSec sgn lab
  zero_mem' := by
    intro a b _ _ q
    simp
  add_mem' := by
    intro u v hu hv a b hab hlab q
    simp only [PiLp.add_apply]
    rw [hu a b hab hlab q, hv a b hab hlab q]
    ring
  smul_mem' := by
    intro z u hu a b hab hlab q
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [hu a b hab hlab q]
    ring

lemma kOp_preserves_sec (k : GConfig eta n → GConfig eta n → ℂ) {sgn : Fin eta → ℂ}
    {lab : Fin eta → ℕ}
    (hk : ∀ a b : Fin eta, a ≠ b → lab a = lab b →
      ∀ q p, k (swapCfg a b q) (swapCfg a b p) = k q p)
    (u : EuclideanSpace ℂ (GConfig eta n)) (hu : IsSec sgn lab u) :
    IsSec sgn lab (kOp k u) := by
  intro a b hab hlab q
  rw [kOp_apply, kOp_apply, Finset.mul_sum]
  refine (Fintype.sum_equiv (swapCfgEquiv a b) _ _ fun p => ?_).symm
  change sgn a * (u p * k q p) = u (swapCfg a b p) * k (swapCfg a b q) (swapCfg a b p)
  rw [hu a b hab hlab p, hk a b hab hlab]
  ring

lemma wMul_preserves_sec (w : GConfig eta n → ℝ) {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ}
    (hw : ∀ a b : Fin eta, a ≠ b → lab a = lab b → ∀ q, w (swapCfg a b q) = w q)
    (u : EuclideanSpace ℂ (GConfig eta n)) (hu : IsSec sgn lab u) :
    IsSec sgn lab (wMul w u) := by
  intro a b hab hlab q
  rw [wMul_apply, wMul_apply, hu a b hab hlab q, hw a b hab hlab]
  ring

/-- A function of the registers that agrees at `a` and `b` is invariant under their
exchange. -/
lemma swap_invariant {α : Type*} {f : Fin eta → α} {a b : Fin eta} (h : f a = f b)
    (k : Fin eta) : f (Equiv.swap a b k) = f k := by
  rcases eq_or_ne k a with rfl | hka
  · rw [Equiv.swap_apply_left, h]
  · rcases eq_or_ne k b with rfl | hkb
    · rw [Equiv.swap_apply_right, h]
    · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]

/-- Ritz energy of a register operator in the exchange sector `(sgn, lab)`: a lower bound for
the Rayleigh quotients of the sector that one normalised state of the sector attains. -/
def IsSecRitz (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ)
    (H : EuclideanSpace ℂ (GConfig eta n) →ₗ[ℂ] EuclideanSpace ℂ (GConfig eta n)) (E : ℝ) :
    Prop :=
  (∀ v, IsSec sgn lab v → E * ‖v‖ ^ 2 ≤ (inner ℂ v (H v)).re) ∧
    ∃ u, IsSec sgn lab u ∧ ‖u‖ = 1 ∧ (inner ℂ u (H u)).re = E

/-- Unordered pair sums of symmetric functions are exchange invariant. -/
lemma pairs_sum_symm {M : Type*} [AddCommGroup M] [Module ℚ M] (f : Fin eta → Fin eta → M)
    (hf : ∀ i j, f i j = f j i) (σ : Equiv.Perm (Fin eta)) :
    ∑ pr : {ij : Fin eta × Fin eta // ij.1 < ij.2}, f (σ pr.1.1) (σ pr.1.2) =
      ∑ pr : {ij : Fin eta × Fin eta // ij.1 < ij.2}, f pr.1.1 pr.1.2 := by
  -- both sides equal one half of the off-diagonal double sum
  have key : ∀ g : Fin eta → Fin eta → M, (∀ i j, g i j = g j i) →
      (2 : ℚ) • ∑ pr : {ij : Fin eta × Fin eta // ij.1 < ij.2}, g pr.1.1 pr.1.2 =
        ∑ i, ∑ j, if i ≠ j then g i j else 0 := by
    intro g hg
    have hsub : ∑ pr : {ij : Fin eta × Fin eta // ij.1 < ij.2}, g pr.1.1 pr.1.2 =
        ∑ ij : Fin eta × Fin eta, if ij.1 < ij.2 then g ij.1 ij.2 else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (univ.filter fun ij : Fin eta × Fin eta => ij.1 < ij.2)
        (fun x => by simp) (fun x : Fin eta × Fin eta => g x.1 x.2)).symm
    have hswap : ∑ ij : Fin eta × Fin eta, (if ij.1 < ij.2 then g ij.1 ij.2 else 0) =
        ∑ ij : Fin eta × Fin eta, if ij.2 < ij.1 then g ij.1 ij.2 else 0 := by
      refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun ij => ?_
      simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
      rw [hg]
    rw [two_smul, hsub]
    conv_lhs => arg 2; rw [hswap]
    rw [← Finset.sum_add_distrib, Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have hfσ : ∀ i j, f (σ i) (σ j) = f (σ j) (σ i) := fun i j => hf _ _
  have h1 := key (fun i j => f (σ i) (σ j)) hfσ
  have h2 := key f hf
  have h3 : (∑ i, ∑ j, if i ≠ j then f (σ i) (σ j) else 0) =
      ∑ i, ∑ j, if i ≠ j then f i j else 0 := by
    rw [← Equiv.sum_comp σ (fun i => ∑ j, if i ≠ j then f i j else 0)]
    refine sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp σ (fun j => if σ i ≠ j then f (σ i) j else 0)]
    refine sum_congr rfl fun j _ => ?_
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
  have h4 : (2 : ℚ) • ∑ pr : {ij : Fin eta × Fin eta // ij.1 < ij.2}, f (σ pr.1.1) (σ pr.1.2) =
      (2 : ℚ) • ∑ pr : {ij : Fin eta × Fin eta // ij.1 < ij.2}, f pr.1.1 pr.1.2 := by
    rw [h1, h2, h3]
  have h5 := congrArg (fun x : M => (1 / 2 : ℚ) • x) h4
  simp only [smul_smul] at h5
  norm_num at h5
  exact h5

end Exchange

/-! ### Ground eigenpairs on invariant subspaces -/

section Ground

/-- A symmetric operator on a nontrivial finite-dimensional space has a normalised ground
eigenvector, whose eigenvalue is a lower bound for the quadratic form. -/
theorem exists_normalized_ground_eigenpair'
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V]
    (A : V →ₗ[ℂ] V) (hA : A.IsSymmetric) :
    ∃ e : ℝ, ∃ u : V,
      ‖u‖ = 1 ∧ A u = (e : ℂ) • u ∧
        ∀ v : V, e * ‖v‖ ^ 2 ≤ (inner ℂ v (A v)).re := by
  classical
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let q : {v : V // v ≠ 0} → ℝ :=
    fun v => (inner ℂ (A v.val) v.val).re / ‖v.val‖ ^ 2
  let e : ℝ := ⨅ v, q v
  have he : Module.End.HasEigenvalue A (e : ℂ) :=
    hA.hasEigenvalue_iInf_of_finiteDimensional
  obtain ⟨x, hx⟩ := he.exists_hasEigenvector
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx.2
  let u : V := ((‖x‖ : ℂ)⁻¹) • x
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, norm_inv]
    have hcast : ‖(‖x‖ : ℂ)‖ = ‖x‖ := by simp
    rw [hcast, inv_mul_cancel₀ hnx]
  have hAu : A u = (e : ℂ) • u := by
    calc
      A u = ((‖x‖ : ℂ)⁻¹) • A x := A.map_smul ((‖x‖ : ℂ)⁻¹) x
      _ = ((‖x‖ : ℂ)⁻¹) • ((e : ℂ) • x) :=
        congrArg (fun v : V => ((‖x‖ : ℂ)⁻¹) • v) hx.apply_eq_smul
      _ = (e : ℂ) • u := smul_comm ((‖x‖ : ℂ)⁻¹) (e : ℂ) x
  let T : V →L[ℂ] V := hA.toSelfAdjoint.val
  have hquadraticLower (v : V) :
      -‖T‖ * ‖v‖ ^ 2 ≤ (inner ℂ (A v) v).re := by
    have hnorm := T.le_opNorm v
    change ‖A v‖ ≤ ‖T‖ * ‖v‖ at hnorm
    have hinner : |(inner ℂ (A v) v).re| ≤ ‖A v‖ * ‖v‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
    have hnegative := (abs_le.mp hinner).1
    have hproduct := mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)
    nlinarith only [hnegative, hproduct]
  have hbounded : BddBelow (Set.range q) := by
    refine ⟨-‖T‖, ?_⟩
    rintro y ⟨v, rfl⟩
    change -‖T‖ ≤ (inner ℂ (A v.val) v.val).re / ‖v.val‖ ^ 2
    exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr v.property))).mpr
      (hquadraticLower v.val)
  refine ⟨e, u, hu, hAu, ?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hq : e ≤ (inner ℂ (A v) v).re / ‖v‖ ^ 2 :=
    ciInf_le hbounded ⟨v, hv⟩
  have hn : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hform := (le_div_iff₀ hn).mp hq
  rwa [hA v v] at hform

/-- A nonzero invariant subspace has a normalised ground eigenvector of the full operator,
with the lower bound restricted to that subspace. -/
theorem exists_ground_eigenpair_on_invariant'
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (H : V →ₗ[ℂ] V) (hH : H.IsSymmetric)
    (S : Submodule ℂ V) (hInvariant : ∀ u ∈ S, H u ∈ S)
    (hNonzero : ∃ u : V, u ∈ S ∧ u ≠ 0) :
    ∃ E : ℝ, ∃ u : V, u ∈ S ∧ ‖u‖ = 1 ∧ H u = (E : ℂ) • u ∧
      ∀ v : V, v ∈ S → E * ‖v‖ ^ 2 ≤ (inner ℂ v (H v)).re := by
  rcases hNonzero with ⟨w, hw, hw0⟩
  have hwS : (⟨w, hw⟩ : S) ≠ 0 := by
    intro h
    exact hw0 (congrArg (fun v : S => (v : V)) h)
  letI : Nontrivial S := ⟨⟨⟨w, hw⟩, 0, hwS⟩⟩
  rcases exists_normalized_ground_eigenpair' (H.restrict hInvariant)
      (hH.restrict_invariant hInvariant) with ⟨E, u, hNorm, hEigen, hLower⟩
  refine ⟨E, (u : V), u.property, hNorm, ?_, ?_⟩
  · exact congrArg (fun v : S => (v : V)) hEigen
  · intro v hv
    exact hLower (⟨v, hv⟩ : S)

/-- Ritz minima are unique. -/
lemma ritz_unique {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (H : V →ₗ[ℂ] V) (S : Set V) (E1 E2 : ℝ)
    (h1 : ∀ v ∈ S, E1 * ‖v‖ ^ 2 ≤ (inner ℂ v (H v)).re)
    (h2 : ∀ v ∈ S, E2 * ‖v‖ ^ 2 ≤ (inner ℂ v (H v)).re)
    (u1 u2 : V) (hu1 : u1 ∈ S) (hu2 : u2 ∈ S) (hn1 : ‖u1‖ = 1) (hn2 : ‖u2‖ = 1)
    (hv1 : (inner ℂ u1 (H u1)).re = E1) (hv2 : (inner ℂ u2 (H u2)).re = E2) : E1 = E2 := by
  have a := h1 u2 hu2
  have b := h2 u1 hu1
  rw [hn2, one_pow, mul_one, hv2] at a
  rw [hn1, one_pow, mul_one, hv1] at b
  linarith

end Ground

end PlaneWaveGridG

/-! ════════════════════════════════════════════════════════════════════
## Part `Comparison`
════════════════════════════════════════════════════════════════════ -/

/-!
# Grid versus Galerkin ground energies on the padded register

Summing the per-term estimates, each weighted by `|c_t|`, gives the operator and tail
bounds for both register Hamiltonians with the total coupling `Z_c = Σ_t |c_t| γ_t`, and the
form bound for their difference `Δ = R - D`.  The spectral layer then yields, for an even
kernel `κ` with `|κ| ≤ γ/|ν|²` that agrees with `γ/|ν|²` on the box `‖ν‖∞ ≤ 2s`,
`2 ≤ s ≤ m ≤ 8s` and `4 m̄ E_big ≤ g² s²`,

  `|E_grid - E_gal| ≤ C_grid / s³`,

with explicit constants.  This is the finite-dimensional core of Theorem `thm:grid-energy`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PlaneWaveGridG

open Finset

section Totals

variable {ν : Type*} [Fintype ν] (eta m : ℕ) (P : RegParticles eta) (D : NucData ν)
  (gamma : ℝ) (κ : Lat3 → ℝ) (g : ℝ)

/-- Collocated (grid) potential kernel `∑_t c_t (grid term t)` of the kernel `κ`. -/
noncomputable def vGridK (q p : RCfg eta m) : ℂ :=
  ∑ t, (P.tcoef t : ℂ) * gridTerm eta m D κ t q p

/-- Galerkin potential kernel. -/
noncomputable def vGalK (q p : RCfg eta m) : ℂ :=
  ∑ t, (P.tcoef t : ℂ) * galTerm eta m D gamma t q p

/-- Dropped transfers. -/
noncomputable def dK (q p : RCfg eta m) : ℂ :=
  ∑ t, (P.tcoef t : ℂ) * dTerm eta m D gamma κ t q p

/-- Wraps. -/
noncomputable def rK (q p : RCfg eta m) : ℂ :=
  ∑ t, (P.tcoef t : ℂ) * rTerm eta m D κ t q p

/-- Kinetic symbol `(g²/2) ∑_a |gl q_a|² / m_a`. -/
noncomputable def kinT (q : RCfg eta m) : ℝ := g ^ 2 / 2 * (wM P q - 1)

/-- The grid Hamiltonian of the kernel `κ` in the momentum basis of the register. -/
noncomputable def Hgrid : EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  wMul (kinT eta m P g) + kOp (vGridK eta m P D κ)

/-- The Galerkin Hamiltonian `P' H P'` on the register. -/
noncomputable def Hgal : EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  wMul (kinT eta m P g) + kOp (vGalK eta m P D gamma)

/-- The difference operator `R - D`. -/
noncomputable def Delta : EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  kOp (rK eta m P D κ) - kOp (dK eta m P D gamma κ)

variable {eta m}

/-- Total coupling `∑_t |c_t| γ_t`. -/
noncomputable def Zc : ℝ := ∑ t : Term eta ν, |P.tcoef t| * coupling eta D gamma t

variable {P D gamma κ g}

lemma vGridK_eq : vGridK eta m P D κ = vGalK eta m P D gamma - dK eta m P D gamma κ +
    rK eta m P D κ := by
  funext q p
  simp only [vGridK, vGalK, dK, rK, Pi.add_apply, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine sum_congr rfl fun t _ => ?_
  have := congrFun (congrFun (gridTerm_eq (eta := eta) (m := m) (D := D) (gamma := gamma)
    (κ := κ) t) q) p
  simp only [Pi.add_apply, Pi.sub_apply] at this
  rw [this]
  ring

lemma Hgrid_eq (u : EuclideanSpace ℂ (RCfg eta m)) :
    Hgrid eta m P D κ g u = Hgal eta m P D gamma g u + Delta eta m P D gamma κ u := by
  simp only [Hgrid, Hgal, Delta]
  rw [vGridK_eq (gamma := gamma), kOp_add, kOp_sub]
  simp only [LinearMap.add_apply, LinearMap.sub_apply]
  abel

lemma Zc_nonneg (hg : 0 ≤ gamma) : 0 ≤ Zc P D gamma :=
  sum_nonneg fun t _ => mul_nonneg (abs_nonneg _) (coupling_nonneg hg t)

lemma kOp_const_mul {ι : Type*} [Fintype ι] (c : ℂ) (k : ι → ι → ℂ) :
    kOp (fun q p => c * k q p) = c • kOp k := by
  apply LinearMap.ext
  intro u
  ext q
  simp only [kOp_apply, LinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact sum_congr rfl fun p _ => by ring

lemma kOp_coef_sum (k : Term eta ν → RCfg eta m → RCfg eta m → ℂ)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    kOp (fun q p => ∑ t, (P.tcoef t : ℂ) * k t q p) u =
      ∑ t, (P.tcoef t : ℂ) • kOp (k t) u := by
  rw [kOp_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine sum_congr rfl fun t _ => ?_
  simp only [kOp_const_mul, LinearMap.smul_apply]

lemma kOp_vGridK_eq (u : EuclideanSpace ℂ (RCfg eta m)) :
    kOp (vGridK eta m P D κ) u =
      ∑ t, (P.tcoef t : ℂ) • kOp (gridTerm eta m D κ t) u :=
  kOp_coef_sum (gridTerm eta m D κ) u

lemma kOp_vGalK_eq (u : EuclideanSpace ℂ (RCfg eta m)) :
    kOp (vGalK eta m P D gamma) u =
      ∑ t, (P.tcoef t : ℂ) • kOp (galTerm eta m D gamma t) u :=
  kOp_coef_sum (galTerm eta m D gamma) u

lemma kOp_dK_eq (u : EuclideanSpace ℂ (RCfg eta m)) :
    kOp (dK eta m P D gamma κ) u = ∑ t, (P.tcoef t : ℂ) • kOp (dTerm eta m D gamma κ t) u :=
  kOp_coef_sum (dTerm eta m D gamma κ) u

lemma kOp_rK_eq (u : EuclideanSpace ℂ (RCfg eta m)) :
    kOp (rK eta m P D κ) u = ∑ t, (P.tcoef t : ℂ) • kOp (rTerm eta m D κ t) u :=
  kOp_coef_sum (rTerm eta m D κ) u

/-! ### Summed bounds -/

lemma norm_coef_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℝ) (x : E)
    {A : ℝ} (h : ‖x‖ ≤ A) : ‖(c : ℂ) • x‖ ≤ |c| * A := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg c)

lemma sum_coupling_bound (f : Term eta ν → ℝ) (A B : ℝ)
    (hf : ∀ t, f t ≤ |P.tcoef t| * coupling eta D gamma t * A +
      |P.tcoef t| * coupling eta D gamma t * B) :
    ∑ t, f t ≤ Zc P D gamma * A + Zc P D gamma * B := by
  unfold Zc
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact sum_le_sum fun t _ => hf t

lemma vGridK_op (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x) (J : ℕ) (hJ : 1 ≤ J)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖kOp (vGridK eta m P D κ) u‖ ≤ Zc P D gamma * (26 * J) * ‖u‖ +
      Zc P D gamma * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  rw [kOp_vGridK_eq]
  refine (norm_sum_le _ _).trans ?_
  have := sum_coupling_bound (P := P) (D := D) (gamma := gamma)
    (fun t => ‖(P.tcoef t : ℂ) • kOp (gridTerm eta m D κ t) u‖) ((26 * J) * ‖u‖)
    (Real.sqrt (1378 / J) * ‖wMul wTot u‖)
    (fun t => (norm_coef_smul_le _ _ (gridTerm_op (D := D) hg hκ t J hJ u)).trans
      (le_of_eq (by ring)))
  linarith

lemma vGalK_op (hg : 0 ≤ gamma) (J : ℕ) (hJ : 1 ≤ J) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖kOp (vGalK eta m P D gamma) u‖ ≤ Zc P D gamma * (26 * J) * ‖u‖ +
      Zc P D gamma * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  rw [kOp_vGalK_eq]
  refine (norm_sum_le _ _).trans ?_
  have := sum_coupling_bound (P := P) (D := D) (gamma := gamma)
    (fun t => ‖(P.tcoef t : ℂ) • kOp (galTerm eta m D gamma t) u‖) ((26 * J) * ‖u‖)
    (Real.sqrt (1378 / J) * ‖wMul wTot u‖)
    (fun t => (norm_coef_smul_le _ _ (galTerm_op (D := D) hg t J hJ u)).trans
      (le_of_eq (by ring)))
  linarith

lemma vGridK_tail (hg : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x) (J T : ℕ) (hJ : 1 ≤ J)
    (hJT : J ≤ T) (hT : T ≤ 2 * m) (r : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) (kOp (vGridK eta m P D κ) u)‖ ≤
      Zc P D gamma * (26 * J) * ‖maskOp (High (T - J) r) u‖ +
      Zc P D gamma * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  rw [kOp_vGridK_eq, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have := sum_coupling_bound (P := P) (D := D) (gamma := gamma)
    (fun t => ‖maskOp (High T r) ((P.tcoef t : ℂ) • kOp (gridTerm eta m D κ t) u)‖)
    ((26 * J) * ‖maskOp (High (T - J) r) u‖) (Real.sqrt (1378 / J) * ‖wMul wTot u‖)
    (fun t => by
      rw [LinearMap.map_smul]
      exact (norm_coef_smul_le _ _ (gridTerm_tail (D := D) hg hκ t J T hJ hJT hT r u)).trans
        (le_of_eq (by ring)))
  linarith

lemma vGalK_tail (hg : 0 ≤ gamma) (J T : ℕ) (hJ : 1 ≤ J) (hJT : J ≤ T)
    (r : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) (kOp (vGalK eta m P D gamma) u)‖ ≤
      Zc P D gamma * (26 * J) * ‖maskOp (High (T - J) r) u‖ +
      Zc P D gamma * Real.sqrt (1378 / J) * ‖wMul wTot u‖ := by
  rw [kOp_vGalK_eq, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have := sum_coupling_bound (P := P) (D := D) (gamma := gamma)
    (fun t => ‖maskOp (High T r) ((P.tcoef t : ℂ) • kOp (galTerm eta m D gamma t) u)‖)
    ((26 * J) * ‖maskOp (High (T - J) r) u‖) (Real.sqrt (1378 / J) * ‖wMul wTot u‖)
    (fun t => by
      rw [LinearMap.map_smul]
      exact (norm_coef_smul_le _ _ (galTerm_tail (D := D) hg t J T hJ hJT r u)).trans
        (le_of_eq (by ring)))
  linarith

lemma Delta_form (hg : 0 ≤ gamma) {s : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    (hκ : GridKernel gamma D.ref s κ) (u v : EuclideanSpace ℂ (RCfg eta m))
    {τu τv : ℝ} (hτu0 : 0 ≤ τu) (hτv0 : 0 ≤ τv)
    (hτu : ∀ r, ‖maskOp (High s r) u‖ ≤ τu) (hτv : ∀ r, ‖maskOp (High s r) v‖ ≤ τv) :
    ‖inner ℂ v (Delta eta m P D gamma κ u)‖ ≤
      Zc P D gamma * (formA s m * (τu * ‖wMul wTot v‖ + τv * ‖wMul wTot u‖) +
        52 * m * (τv * τu)) := by
  rw [Delta, LinearMap.sub_apply, kOp_rK_eq, kOp_dK_eq, inner_sub_right, inner_sum, inner_sum]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_sum_le _ _) (norm_sum_le _ _)).trans ?_
  rw [← Finset.sum_add_distrib]
  unfold Zc
  rw [Finset.sum_mul]
  refine sum_le_sum fun t _ => ?_
  have h := term_form (D := D) hg hs hsm hκ t u v hτu0 hτv0 hτu hτv
  rw [inner_smul_right, inner_smul_right, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  have hc := abs_nonneg (P.tcoef t)
  calc |P.tcoef t| * ‖inner ℂ v (kOp (rTerm eta m D κ t) u)‖ +
        |P.tcoef t| * ‖inner ℂ v (kOp (dTerm eta m D gamma κ t) u)‖
      = |P.tcoef t| * (‖inner ℂ v (kOp (dTerm eta m D gamma κ t) u)‖ +
          ‖inner ℂ v (kOp (rTerm eta m D κ t) u)‖) := by ring
    _ ≤ |P.tcoef t| * (coupling eta D gamma t * (formA s m * (τu * ‖wMul wTot v‖ +
          τv * ‖wMul wTot u‖) + 52 * m * (τv * τu))) := mul_le_mul_of_nonneg_left h hc
    _ = |P.tcoef t| * coupling eta D gamma t * (formA s m * (τu * ‖wMul wTot v‖ +
          τv * ‖wMul wTot u‖) + 52 * m * (τv * τu)) := by ring

end Totals

end PlaneWaveGridG

/-! ### Exchange symmetry and Hermiticity of the register Hamiltonians -/

namespace PlaneWaveGridG

open Finset

section SymmetryOfTerms

variable {eta M : ℕ}

lemma spec2_perm (π : Equiv.Perm (Fin eta)) (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) :
    Spec2 i j (q ∘ π) (p ∘ π) ↔ Spec2 (π i) (π j) q p := by
  constructor
  · intro h k hki hkj
    have h1 : π.symm k ≠ i := fun hh => hki (by rw [← hh, Equiv.apply_symm_apply])
    have h2 : π.symm k ≠ j := fun hh => hkj (by rw [← hh, Equiv.apply_symm_apply])
    have := h (π.symm k) h1 h2
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using this
  · intro h k hki hkj
    exact h (π k) (fun hh => hki (π.injective hh)) (fun hh => hkj (π.injective hh))

lemma spec1_perm (π : Equiv.Perm (Fin eta)) (i : Fin eta) (q p : GConfig eta (2 * M + 1)) :
    Spec1 i (q ∘ π) (p ∘ π) ↔ Spec1 (π i) q p := by
  constructor
  · intro h k hki
    have h1 : π.symm k ≠ i := fun hh => hki (by rw [← hh, Equiv.apply_symm_apply])
    have := h (π.symm k) h1
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using this
  · intro h k hki
    exact h (π k) (fun hh => hki (π.injective hh))

lemma gRel2_perm (π : Equiv.Perm (Fin eta)) (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) :
    gRel2 i j (q ∘ π) (p ∘ π) ↔ gRel2 (π i) (π j) q p := by
  unfold gRel2
  rw [spec2_perm]
  rfl

lemma wRel2_perm (π : Equiv.Perm (Fin eta)) (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) :
    wRel2 i j (q ∘ π) (p ∘ π) ↔ wRel2 (π i) (π j) q p := by
  unfold wRel2
  rw [spec2_perm]
  rfl

lemma tk_swap_congr {ι : Type*} [Fintype ι] [DecidableEq ι] {rel rel' : ι → ι → Prop}
    {tau tau' : ι → ι → Lat3} {kappa : Lat3 → ℂ} {q p q' p' : ι}
    (hrel : rel q p ↔ rel' q' p') (htau : tau q p = tau' q' p') :
    tk rel tau kappa q p = tk rel' tau' kappa q' p' := by
  by_cases h : rel q p
  · rw [tk_of_rel h, tk_of_rel (hrel.mp h), htau]
  · rw [tk_of_not_rel h, tk_of_not_rel (fun h' => h (hrel.mpr h'))]

lemma tk_herm {ι : Type*} [Fintype ι] [DecidableEq ι] {rel : ι → ι → Prop}
    {tau : ι → ι → Lat3} {kappa : Lat3 → ℂ} (hrel : ∀ q p, rel q p → rel p q)
    (htau : ∀ q p, tau p q = -tau q p) (hk : ∀ x, kappa (-x) = (starRingEnd ℂ) (kappa x))
    (q p : ι) : tk rel tau kappa p q = (starRingEnd ℂ) (tk rel tau kappa q p) := by
  by_cases h : rel q p
  · rw [tk_of_rel (hrel q p h), tk_of_rel h, htau, hk]
  · rw [tk_of_not_rel (fun h' => h (hrel p q h')), tk_of_not_rel h, map_zero]

lemma gRel2_symm' (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) (h : gRel2 i j q p) :
    gRel2 i j p q :=
  ⟨fun k hki hkj => (h.1 k hki hkj).symm, h.2.symm⟩

lemma wRel2_symm' (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) (h : wRel2 i j q p) :
    wRel2 i j p q :=
  ⟨fun k hki hkj => (h.1 k hki hkj).symm, h.2.symm⟩

lemma spec1_symm' (i : Fin eta) (q p : GConfig eta (2 * M + 1)) (h : Spec1 i q p) :
    Spec1 i p q :=
  fun k hki => (h k hki).symm

lemma gTau_antisymm (i : Fin eta) (q p : GConfig eta (2 * M + 1)) :
    gTau i p q = -gTau i q p := by
  unfold gTau
  rw [← gl_neg, neg_sub]

lemma wTau_antisymm (i : Fin eta) (q p : GConfig eta (2 * M + 1)) :
    wTau i p q = -wTau i q p := by
  unfold wTau
  rw [neg_sub]

lemma gRel2_comm (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) :
    gRel2 i j q p ↔ gRel2 j i q p := by
  unfold gRel2 Spec2
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun k hkj hki => h1 k hki hkj, by
      rw [add_comm (q j) (q i), add_comm (p j) (p i)]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun k hki hkj => h1 k hkj hki, by
      rw [add_comm (q i) (q j), add_comm (p i) (p j)]; exact h2⟩

lemma wRel2_comm (i j : Fin eta) (q p : GConfig eta (2 * M + 1)) :
    wRel2 i j q p ↔ wRel2 j i q p := by
  unfold wRel2 Spec2
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun k hkj hki => h1 k hki hkj, by rw [add_comm, h2, add_comm]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun k hki hkj => h1 k hkj hki, by rw [add_comm, h2, add_comm]⟩

lemma gPair_comm {k : Lat3 → ℂ} (hk : ∀ x, k (-x) = k x) (i j : Fin eta)
    (q p : GConfig eta (2 * M + 1)) :
    tk (gRel2 i j) (gTau i) k q p = tk (gRel2 j i) (gTau j) k q p := by
  by_cases h : gRel2 i j q p
  · rw [tk_of_rel h, tk_of_rel ((gRel2_comm i j q p).mp h)]
    unfold gTau
    rw [gTau_partner h, hk]
  · rw [tk_of_not_rel h, tk_of_not_rel (fun h' => h ((gRel2_comm i j q p).mpr h'))]

lemma wPair_comm {k : Lat3 → ℂ} (hk : ∀ x, k (-x) = k x) (i j : Fin eta)
    (q p : GConfig eta (2 * M + 1)) :
    tk (wRel2 i j) (wTau i) k q p = tk (wRel2 j i) (wTau j) k q p := by
  by_cases h : wRel2 i j q p
  · rw [tk_of_rel h, tk_of_rel ((wRel2_comm i j q p).mp h)]
    unfold wTau
    rw [wTau_partner h, hk]
  · rw [tk_of_not_rel h, tk_of_not_rel (fun h' => h ((wRel2_comm i j q p).mpr h'))]

end SymmetryOfTerms

section SymmetryOfTotals

variable {ν : Type*} [Fintype ν] {eta m : ℕ} {P : RegParticles eta} {D : NucData ν}
  {gamma : ℝ} {κ : Lat3 → ℝ} {g : ℝ}

lemma pairs_sum_symm_C (f : Fin eta → Fin eta → ℂ) (hf : ∀ i j, f i j = f j i)
    (σ : Equiv.Perm (Fin eta)) :
    ∑ pr : Pairs eta, f (σ pr.1.1) (σ pr.1.2) = ∑ pr : Pairs eta, f pr.1.1 pr.1.2 :=
  pairs_sum_symm f hf σ

lemma charge_symm_apply {π : Equiv.Perm (Fin eta)} (hπ : ∀ k, P.charge (π k) = P.charge k)
    (i : Fin eta) : P.charge (π.symm i) = P.charge i := by
  have h := hπ (π.symm i)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The grid kernel of an even `κ` is invariant under a relabelling of the registers that
preserves the charges. -/
lemma vGridK_perm (hκe : ∀ x, κ (-x) = κ x) (π : Equiv.Perm (Fin eta))
    (hπ : ∀ k, P.charge (π k) = P.charge k) (q p : RCfg eta m) :
    vGridK eta m P D κ (q ∘ π) (p ∘ π) = vGridK eta m P D κ q p := by
  unfold vGridK
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · simp only [gridTerm, RegParticles.tcoef]
    have h := pairs_sum_symm_C (fun i j => ((P.charge i * P.charge j : ℝ) : ℂ) *
        tk (gRel2 i j) (gTau i) (kgr κ) q p)
      (fun i j => by rw [mul_comm (P.charge i), gPair_comm (kgr_neg hκe) i j q p]) π
    rw [← h]
    refine sum_congr rfl fun pr _ => ?_
    simp only [hπ]
    congr 1
    exact tk_swap_congr (gRel2_perm π _ _ q p) rfl
  · simp only [gridTerm, RegParticles.tcoef]
    rw [← Equiv.sum_comp (Equiv.prodCongr π.symm (Equiv.refl ν))]
    refine sum_congr rfl fun il _ => ?_
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply]
    rw [charge_symm_apply hπ]
    congr 1
    refine tk_swap_congr ?_ ?_
    · rw [spec1_perm, Equiv.apply_symm_apply]
    · simp only [gTau, Function.comp_apply, Equiv.apply_symm_apply]

/-- The Galerkin kernel is invariant under a relabelling of the registers that preserves the
charges. -/
lemma vGalK_perm (π : Equiv.Perm (Fin eta)) (hπ : ∀ k, P.charge (π k) = P.charge k)
    (q p : RCfg eta m) :
    vGalK eta m P D gamma (q ∘ π) (p ∘ π) = vGalK eta m P D gamma q p := by
  unfold vGalK
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  · simp only [galTerm, RegParticles.tcoef]
    have h := pairs_sum_symm_C (fun i j => ((P.charge i * P.charge j : ℝ) : ℂ) *
        tk (wRel2 i j) (wTau i) (kee D gamma) q p)
      (fun i j => by rw [mul_comm (P.charge i), wPair_comm (kee_neg D gamma) i j q p]) π
    rw [← h]
    refine sum_congr rfl fun pr _ => ?_
    simp only [hπ]
    congr 1
    exact tk_swap_congr (wRel2_perm π _ _ q p) rfl
  · simp only [galTerm, RegParticles.tcoef]
    rw [← Equiv.sum_comp (Equiv.prodCongr π.symm (Equiv.refl ν))]
    refine sum_congr rfl fun il _ => ?_
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply]
    rw [charge_symm_apply hπ]
    congr 1
    refine tk_swap_congr ?_ ?_
    · rw [spec1_perm, Equiv.apply_symm_apply]
    · simp only [wTau, Function.comp_apply, Equiv.apply_symm_apply]

lemma vGridK_herm (hκe : ∀ x, κ (-x) = κ x) (q p : RCfg eta m) :
    vGridK eta m P D κ p q = (starRingEnd ℂ) (vGridK eta m P D κ q p) := by
  unfold vGridK
  rw [map_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  cases t with
  | inl pr =>
    exact tk_herm (fun q p h => gRel2_symm' _ _ q p h) (gTau_antisymm _)
      (fun x => by rw [kgr_neg hκe, kgr_conj]) q p
  | inr il =>
    exact tk_herm (fun q p h => spec1_symm' _ q p h) (gTau_antisymm _)
      (kgn_neg D hκe il.2) q p

lemma vGalK_herm (q p : RCfg eta m) :
    vGalK eta m P D gamma p q = (starRingEnd ℂ) (vGalK eta m P D gamma q p) := by
  unfold vGalK
  rw [map_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  cases t with
  | inl pr =>
    exact tk_herm (fun q p h => wRel2_symm' _ _ q p h) (wTau_antisymm _)
      (fun x => by rw [kee_neg, kee_conj]) q p
  | inr il =>
    exact tk_herm (fun q p h => spec1_symm' _ q p h) (wTau_antisymm _)
      (knuc_neg D gamma il.2) q p

/-- The kinetic weight is invariant under a relabelling of the registers that preserves the
masses. -/
lemma wM_perm (π : Equiv.Perm (Fin eta)) (hπ : ∀ k, P.mass (π k) = P.mass k)
    (q : RCfg eta m) : wM P (q ∘ π) = wM P q := by
  unfold wM
  congr 1
  calc ∑ k, nsq (gl ((q ∘ π) k)) / P.mass k = ∑ k, nsq (gl (q (π k))) / P.mass (π k) :=
        sum_congr rfl fun k _ => by simp only [Function.comp_apply, hπ k]
    _ = ∑ k, nsq (gl (q k)) / P.mass k :=
        Equiv.sum_comp π (fun k => nsq (gl (q k)) / P.mass k)

lemma kinT_perm (π : Equiv.Perm (Fin eta)) (hπ : ∀ k, P.mass (π k) = P.mass k)
    (q : RCfg eta m) : kinT eta m P g (q ∘ π) = kinT eta m P g q := by
  unfold kinT
  rw [wM_perm π hπ]

lemma Hgrid_isSymmetric (hκe : ∀ x, κ (-x) = κ x) : (Hgrid eta m P D κ g).IsSymmetric :=
  (wMul_isSymmetric _).add (kOp_isSymmetric _ (vGridK_herm hκe))

lemma Hgal_isSymmetric : (Hgal eta m P D gamma g).IsSymmetric :=
  (wMul_isSymmetric _).add (kOp_isSymmetric _ vGalK_herm)

lemma Hgrid_sec (hκe : ∀ x, κ (-x) = κ x) {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ}
    (hP : ∀ a b, lab a = lab b → P.mass a = P.mass b ∧ P.charge a = P.charge b)
    (u : EuclideanSpace ℂ (RCfg eta m)) (hu : IsSec sgn lab u) :
    IsSec sgn lab (Hgrid eta m P D κ g u) := by
  intro a b hab hlab q
  have h1 := wMul_preserves_sec (kinT eta m P g)
    (fun a b _ hl q => kinT_perm (Equiv.swap a b) (swap_invariant (hP a b hl).1) q) u hu
    a b hab hlab q
  have h2 := kOp_preserves_sec (vGridK eta m P D κ)
    (fun a b _ hl q p => vGridK_perm hκe (Equiv.swap a b) (swap_invariant (hP a b hl).2) q p)
    u hu a b hab hlab q
  simp only [Hgrid, LinearMap.add_apply, PiLp.add_apply]
  rw [h1, h2]
  ring

lemma Hgal_sec {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ}
    (hP : ∀ a b, lab a = lab b → P.mass a = P.mass b ∧ P.charge a = P.charge b)
    (u : EuclideanSpace ℂ (RCfg eta m)) (hu : IsSec sgn lab u) :
    IsSec sgn lab (Hgal eta m P D gamma g u) := by
  intro a b hab hlab q
  have h1 := wMul_preserves_sec (kinT eta m P g)
    (fun a b _ hl q => kinT_perm (Equiv.swap a b) (swap_invariant (hP a b hl).1) q) u hu
    a b hab hlab q
  have h2 := kOp_preserves_sec (vGalK eta m P D gamma)
    (fun a b _ hl q p => vGalK_perm (Equiv.swap a b) (swap_invariant (hP a b hl).2) q p) u hu
    a b hab hlab q
  simp only [Hgal, LinearMap.add_apply, PiLp.add_apply]
  rw [h1, h2]
  ring

end SymmetryOfTotals

end PlaneWaveGridG

/-! ════════════════════════════════════════════════════════════════════
## Part `MainFinite`
════════════════════════════════════════════════════════════════════ -/

/-!
# The finite comparison theorem `|E_grid - E_gal| ≤ C/s³`

The grid kernel `κ` is even, satisfies `|κ| ≤ γ/|ν|²` and agrees with `γ/|ν|²` on the box
`‖ν‖∞ ≤ 2s`, with `2 ≤ s ≤ m ≤ 8s` (`GridKernel γ s κ`), so the tails of the eigenvectors are
bootstrapped at the threshold `s` (for the sharp kernel any `s ≤ m` would do; for the kernel
class `s = ⌊m/4⌋`).  Explicit constants:

* `J0g Z g = ⌈1378 (8Z/g²)²⌉ + 1`, the fixed Kato--Rellich splitting radius;
* `Ell Z g x = (4/3)(1 + (2/g²)(x + 26 Z J₀))`, the elliptic constant: `‖wM u‖ ≤ Ell` for a
  normalised eigenvector at energy `|E| ≤ x`;
* `Cboot Z g = 508 Z / g²`, the tail-bootstrap constant: `t ≤ Cboot ‖wTot u‖ / (s² √s)`;
* `Cform Z g = Z (260 Cboot + 416 Cboot²)`, the form-error constant:
  error `≤ Cform ‖wTot u‖²/s³`;
* `Ebig M Z g Eb`, a bound on both ground energies, and
  `Cgrid M Z g Eb = Cform (M Ell(Ebig))²`.

They are evaluated at `Z = m̄ Z_c`, with `Z_c = Σ_t |c_t| γ_t` the total coupling and `M = m̄`
the largest mass: the operator bound holds with the mass-weighted weight `wM` and the coupling
`m̄ Z_c` because `wTot ≤ m̄ wM`, the bootstrap divides by the kinetic energy
`(g²/(2 m̄)) (T+1)²` of the shell, and the form error is in terms of `‖wTot u‖ ≤ m̄ ‖wM u‖`.
The bootstrap needs `4 m̄ E_big ≤ g² s²`. With all masses one, `M = 1` and `wM = wTot`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PlaneWaveGridG

open Finset

/-- The fixed splitting radius of the elliptic estimate. -/
noncomputable def J0g (Z g : ℝ) : ℕ := Nat.ceil (1378 * (8 * Z / g ^ 2) ^ 2) + 1

/-- Elliptic constant. -/
noncomputable def Ell (Z g x : ℝ) : ℝ := 4 / 3 * (1 + 2 / g ^ 2 * (x + 26 * Z * J0g Z g))

/-- Tail-bootstrap constant. -/
noncomputable def Cboot (Z g : ℝ) : ℝ := 508 * Z / g ^ 2

/-- Form-error constant. -/
noncomputable def Cform (Z g : ℝ) : ℝ := Z * (260 * Cboot Z g + 416 * Cboot Z g ^ 2)

/-- A common bound for the Galerkin and grid ground energies; `M` is the largest mass. -/
noncomputable def Ebig (M Z g Eb : ℝ) : ℝ :=
  max (52 * Z * J0g Z g + g ^ 2 / 4) (Eb + Cform Z g * (M * Ell Z g Eb) ^ 2)

/-- The final finite comparison constant. -/
noncomputable def Cgrid (M Z g Eb : ℝ) : ℝ := Cform Z g * (M * Ell Z g (Ebig M Z g Eb)) ^ 2

section Arithmetic

lemma J0g_pos (Z g : ℝ) : 1 ≤ J0g Z g := by
  unfold J0g; omega

lemma J0g_small {Z g : ℝ} (hZ : 0 ≤ Z) (hg : 0 < g) :
    Z * Real.sqrt (1378 / J0g Z g) ≤ g ^ 2 / 8 := by
  set J : ℕ := J0g Z g with hJdef
  have hJ : (0 : ℝ) < J := by exact_mod_cast J0g_pos Z g
  have hJge : 1378 * (8 * Z / g ^ 2) ^ 2 ≤ (J : ℝ) := by
    rw [hJdef]
    unfold J0g
    push_cast
    linarith [Nat.le_ceil (1378 * (8 * Z / g ^ 2) ^ 2)]
  have hg2 : 0 < g ^ 2 := by positivity
  have key : Z ^ 2 * (1378 / J) ≤ (g ^ 2 / 8) ^ 2 := by
    rw [mul_div_assoc', div_le_iff₀ hJ]
    have e : (8 * Z / g ^ 2) ^ 2 = 64 * Z ^ 2 / (g ^ 2) ^ 2 := by ring
    rw [e, mul_div_assoc', div_le_iff₀ (by positivity)] at hJge
    nlinarith
  calc Z * Real.sqrt (1378 / J) = Real.sqrt (Z ^ 2 * (1378 / J)) := by
        rw [Real.sqrt_mul (sq_nonneg Z), Real.sqrt_sq hZ]
    _ ≤ Real.sqrt ((g ^ 2 / 8) ^ 2) := Real.sqrt_le_sqrt key
    _ = g ^ 2 / 8 := Real.sqrt_sq (by positivity)

lemma Ell_nonneg {Z g x : ℝ} (hZ : 0 ≤ Z) (hx : 0 ≤ x) : 0 ≤ Ell Z g x := by
  unfold Ell
  have : 0 ≤ 2 / g ^ 2 := by positivity
  positivity

lemma Ell_mono {Z g x y : ℝ} (_hZ : 0 ≤ Z) (hxy : x ≤ y) : Ell Z g x ≤ Ell Z g y := by
  unfold Ell
  have : 0 ≤ 2 / g ^ 2 := by positivity
  gcongr

lemma Cboot_nonneg {Z g : ℝ} (hZ : 0 ≤ Z) : 0 ≤ Cboot Z g := by
  unfold Cboot; positivity

lemma Cform_nonneg {Z g : ℝ} (hZ : 0 ≤ Z) : 0 ≤ Cform Z g := by
  unfold Cform
  have := Cboot_nonneg (g := g) hZ
  positivity

/-- Simplification of the tail bootstrap with `J = m/2`. -/
lemma boot_arith {Z g X : ℝ} (hZ : 0 ≤ Z) (hg : 0 < g) (hX : 0 ≤ X) {m : ℕ} (hm : 2 ≤ m) :
    (Z * (26 * ((m / 2 : ℕ) : ℝ)) * (X / (1 + (((m - m / 2 : ℕ) : ℝ) + 1) ^ 2)) +
        Z * Real.sqrt (1378 / ((m / 2 : ℕ) : ℝ)) * X) / (g ^ 2 / 4 * ((m : ℝ) + 1) ^ 2) ≤
      Cboot Z g * X / ((m : ℝ) ^ 2 * Real.sqrt m) := by
  set J : ℕ := m / 2 with hJdef
  have hJ1 : 1 ≤ J := by omega
  have h2J : 2 * J ≤ m := by omega
  have h4J : m ≤ 4 * J := by omega
  have hJm : J ≤ m := by omega
  have hmr : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have h2Jr : 2 * (J : ℝ) ≤ m := by exact_mod_cast h2J
  have h4Jr : (m : ℝ) ≤ 4 * J := by exact_mod_cast h4J
  have hsub : ((m - J : ℕ) : ℝ) = (m : ℝ) - J := by push_cast [Nat.cast_sub hJm]; ring
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hsm2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0.le
  have hsm_le : Real.sqrt m ≤ m := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  -- first term: ≤ 52 X / m
  have hden : (m : ℝ) ^ 2 / 4 ≤ 1 + (((m - J : ℕ) : ℝ) + 1) ^ 2 := by
    rw [hsub]
    nlinarith
  have t1 : Z * (26 * (J : ℝ)) * (X / (1 + (((m - J : ℕ) : ℝ) + 1) ^ 2)) ≤
      Z * (52 * X / m) := by
    have hpos : 0 < (m : ℝ) ^ 2 / 4 := by positivity
    have hdiv : X / (1 + (((m - J : ℕ) : ℝ) + 1) ^ 2) ≤ X / ((m : ℝ) ^ 2 / 4) :=
      div_le_div_of_nonneg_left hX hpos hden
    have : (26 * (J : ℝ)) * (X / ((m : ℝ) ^ 2 / 4)) ≤ 52 * X / m := by
      rw [div_div_eq_mul_div, mul_div_assoc', div_le_div_iff₀ (by positivity) hm0]
      nlinarith [mul_nonneg (mul_nonneg hX hm0.le) (sub_nonneg.mpr h2Jr)]
    calc Z * (26 * (J : ℝ)) * (X / (1 + (((m - J : ℕ) : ℝ) + 1) ^ 2))
        ≤ Z * (26 * (J : ℝ)) * (X / ((m : ℝ) ^ 2 / 4)) := by gcongr
      _ = Z * ((26 * (J : ℝ)) * (X / ((m : ℝ) ^ 2 / 4))) := by ring
      _ ≤ Z * (52 * X / m) := by gcongr
  -- second term: ≤ 75 X / √m
  have t2 : Z * Real.sqrt (1378 / (J : ℝ)) * X ≤ Z * (75 * X / Real.sqrt m) := by
    have hq : Real.sqrt (1378 / (J : ℝ)) ≤ 75 / Real.sqrt m := by
      rw [le_div_iff₀ hsm, ← Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_le_left (by norm_num)]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    calc Z * Real.sqrt (1378 / (J : ℝ)) * X ≤ Z * (75 / Real.sqrt m) * X := by gcongr
      _ = Z * (75 * X / Real.sqrt m) := by ring
  have t12 : 52 * X / m ≤ 52 * X / Real.sqrt m :=
    div_le_div_of_nonneg_left (by positivity) hsm hsm_le
  have hnum : Z * (26 * (J : ℝ)) * (X / (1 + (((m - J : ℕ) : ℝ) + 1) ^ 2)) +
      Z * Real.sqrt (1378 / (J : ℝ)) * X ≤ Z * (127 * X / Real.sqrt m) := by
    have : Z * (52 * X / m) ≤ Z * (52 * X / Real.sqrt m) := by gcongr
    have e : Z * (52 * X / Real.sqrt m) + Z * (75 * X / Real.sqrt m) =
        Z * (127 * X / Real.sqrt m) := by ring
    linarith
  have hdenpos : 0 < g ^ 2 / 4 * ((m : ℝ) + 1) ^ 2 := by positivity
  rw [div_le_div_iff₀ hdenpos (by positivity)]
  have hgm : g ^ 2 / 4 * (m : ℝ) ^ 2 ≤ g ^ 2 / 4 * ((m : ℝ) + 1) ^ 2 := by
    gcongr; linarith
  calc (Z * (26 * (J : ℝ)) * (X / (1 + (((m - J : ℕ) : ℝ) + 1) ^ 2)) +
        Z * Real.sqrt (1378 / (J : ℝ)) * X) * ((m : ℝ) ^ 2 * Real.sqrt m)
      ≤ Z * (127 * X / Real.sqrt m) * ((m : ℝ) ^ 2 * Real.sqrt m) := by gcongr
    _ = 127 * Z * X * (m : ℝ) ^ 2 * (Real.sqrt m / Real.sqrt m) := by ring
    _ = 127 * Z * X * (m : ℝ) ^ 2 := by rw [div_self hsm.ne', mul_one]
    _ = Cboot Z g * X * (g ^ 2 / 4 * (m : ℝ) ^ 2) := by
        have hg2 : g ^ 2 ≠ 0 := by positivity
        have e : Cboot Z g * X * (g ^ 2 / 4 * (m : ℝ) ^ 2) =
            127 * Z * X * (m : ℝ) ^ 2 * (g ^ 2 / g ^ 2) := by
          unfold Cboot; ring
        rw [e, div_self hg2, mul_one]
    _ ≤ Cboot Z g * X * (g ^ 2 / 4 * ((m : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hgm (mul_nonneg (Cboot_nonneg hZ) hX)

/-- `formA s m ≤ 130/√s` for `1 ≤ s ≤ m`. -/
lemma formA_le {s m : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m) : formA s m ≤ 130 / Real.sqrt s := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsmr : (s : ℝ) ≤ m := by exact_mod_cast hsm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hs0 hsmr
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have a1 : Real.sqrt (1378 / (2 * (s : ℝ))) ≤ 27 / Real.sqrt s := by
    rw [le_div_iff₀ hss, ← Real.sqrt_mul (by positivity), Real.sqrt_le_left (by norm_num)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have a2 : Real.sqrt (1378 / (m : ℝ)) ≤ 38 / Real.sqrt s := by
    rw [le_div_iff₀ hss, ← Real.sqrt_mul (by positivity), Real.sqrt_le_left (by norm_num)]
    rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
    nlinarith
  unfold formA
  have e : 2 * (27 / Real.sqrt s) + 2 * (38 / Real.sqrt s) = 130 / Real.sqrt s := by ring
  linarith

/-- Simplification of the form error with tails bootstrapped at the threshold `s`. -/
lemma form_arith {Z g X τ : ℝ} (hZ : 0 ≤ Z) (hX : 0 ≤ X) (hτ0 : 0 ≤ τ) {s m : ℕ} (hs : 1 ≤ s)
    (hsm : s ≤ m) (hms : m ≤ 8 * s)
    (hτ : τ ≤ Cboot Z g * X / ((s : ℝ) ^ 2 * Real.sqrt s)) :
    Z * (formA s m * (τ * X + τ * X) + 52 * m * (τ * τ)) ≤ Cform Z g * X ^ 2 / (s : ℝ) ^ 3 := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hmsr : (m : ℝ) ≤ 8 * s := by exact_mod_cast hms
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hss2 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0.le
  have hC := Cboot_nonneg (g := g) hZ
  set C := Cboot Z g
  have hA := formA_le hs hsm
  have hA0 := formA_nonneg s m
  -- first part
  have p1 : formA s m * (τ * X + τ * X) ≤ 260 * C * X ^ 2 / (s : ℝ) ^ 3 := by
    calc formA s m * (τ * X + τ * X) = 2 * formA s m * τ * X := by ring
      _ ≤ 2 * (130 / Real.sqrt s) * (C * X / ((s : ℝ) ^ 2 * Real.sqrt s)) * X := by gcongr
      _ = 260 * C * X ^ 2 / ((s : ℝ) ^ 2 * (Real.sqrt s * Real.sqrt s)) := by
          ring
      _ = 260 * C * X ^ 2 / (s : ℝ) ^ 3 := by rw [hss2]; ring
  -- second part
  have p2 : 52 * (m : ℝ) * (τ * τ) ≤ 416 * C ^ 2 * X ^ 2 / (s : ℝ) ^ 3 := by
    have hτ2 : τ * τ ≤ (C * X / ((s : ℝ) ^ 2 * Real.sqrt s)) ^ 2 := by
      rw [← sq]; exact pow_le_pow_left₀ hτ0 hτ 2
    have e : (C * X / ((s : ℝ) ^ 2 * Real.sqrt s)) ^ 2 = C ^ 2 * X ^ 2 / (s : ℝ) ^ 5 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hs0.le]; ring
    rw [e] at hτ2
    calc 52 * (m : ℝ) * (τ * τ) ≤ 52 * (8 * (s : ℝ)) * (C ^ 2 * X ^ 2 / (s : ℝ) ^ 5) := by
          gcongr
      _ = 416 * C ^ 2 * X ^ 2 / (s : ℝ) ^ 4 := by
          have hsne : (s : ℝ) ≠ 0 := hs0.ne'
          field_simp
          ring
      _ ≤ 416 * C ^ 2 * X ^ 2 / (s : ℝ) ^ 3 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          calc (s : ℝ) ^ 3 = (s : ℝ) ^ 3 * 1 := by ring
            _ ≤ (s : ℝ) ^ 3 * s := by gcongr
            _ = (s : ℝ) ^ 4 := by ring
  unfold Cform
  calc Z * (formA s m * (τ * X + τ * X) + 52 * m * (τ * τ))
      ≤ Z * (260 * C * X ^ 2 / (s : ℝ) ^ 3 + 416 * C ^ 2 * X ^ 2 / (s : ℝ) ^ 3) := by gcongr
    _ = Z * (260 * C + 416 * C ^ 2) * X ^ 2 / (s : ℝ) ^ 3 := by ring

end Arithmetic

end PlaneWaveGridG

namespace PlaneWaveGridG

open Finset

section Main

variable {ν : Type*} [Fintype ν] {eta m : ℕ} {P : RegParticles eta} {D : NucData ν}
  {gamma : ℝ} {κ : Lat3 → ℝ} {g : ℝ}

/-- An operator bound with the weight `wTot = 1 + Σ_a |ν_a|²` (the `H²` weight without masses)
gives one with the mass-weighted weight `wM` and the coupling multiplied by the largest mass. -/
lemma op_bound_mass (P : RegParticles eta) {X : EuclideanSpace ℂ (RCfg eta m)}
    (u : EuclideanSpace ℂ (RCfg eta m)) {Z : ℝ} (hZ : 0 ≤ Z) (J : ℕ)
    (h : ‖X‖ ≤ Z * (26 * J) * ‖u‖ + Z * Real.sqrt (1378 / J) * ‖wMul wTot u‖) :
    ‖X‖ ≤ (P.maxMass * Z) * (26 * J) * ‖u‖ +
      (P.maxMass * Z) * Real.sqrt (1378 / J) * ‖wMul (wM P) u‖ := by
  have hM := P.one_le_maxMass
  have hW := norm_wMul_wTot_le P u
  have h0 : 0 ≤ Z * (26 * J) * ‖u‖ := by positivity
  have h1 : Z * (26 * J) * ‖u‖ ≤ (P.maxMass * Z) * (26 * J) * ‖u‖ :=
    calc Z * (26 * J) * ‖u‖ = 1 * (Z * (26 * J) * ‖u‖) := by ring
      _ ≤ P.maxMass * (Z * (26 * J) * ‖u‖) := mul_le_mul_of_nonneg_right hM h0
      _ = (P.maxMass * Z) * (26 * J) * ‖u‖ := by ring
  have hs : 0 ≤ Z * Real.sqrt (1378 / J) := by positivity
  have h2 : Z * Real.sqrt (1378 / J) * ‖wMul wTot u‖ ≤
      (P.maxMass * Z) * Real.sqrt (1378 / J) * ‖wMul (wM P) u‖ :=
    calc Z * Real.sqrt (1378 / J) * ‖wMul wTot u‖
        ≤ Z * Real.sqrt (1378 / J) * (P.maxMass * ‖wMul (wM P) u‖) :=
          mul_le_mul_of_nonneg_left hW hs
      _ = (P.maxMass * Z) * Real.sqrt (1378 / J) * ‖wMul (wM P) u‖ := by ring
  linarith

/-- The grid Hamiltonian as a register Hamiltonian: mass-weighted weight, coupling `m̄ Z_c`. -/
noncomputable def gridRegHam (hgamma : 0 ≤ gamma) (hκ : ∀ x, |κ x| ≤ gamma * coul x)
    (hg : 0 < g) : RegHam (RCfg eta m) where
  W := wM P
  kin := kinT eta m P g
  V := kOp (vGridK eta m P D κ)
  g := g
  g_pos := hg
  kin_eq := fun _ => rfl
  W_ge_one := wM_ge_one P
  Z := P.maxMass * Zc P D gamma
  Z_nonneg := mul_nonneg P.maxMass_pos.le (Zc_nonneg hgamma)
  J0 := J0g (P.maxMass * Zc P D gamma) g
  J0_pos := J0g_pos _ _
  small := J0g_small (mul_nonneg P.maxMass_pos.le (Zc_nonneg hgamma)) hg
  op_bound := fun u => op_bound_mass P u (Zc_nonneg hgamma) _
    (vGridK_op hgamma hκ _ (J0g_pos _ _) u)

/-- The Galerkin Hamiltonian as a register Hamiltonian. -/
noncomputable def galRegHam (hgamma : 0 ≤ gamma) (hg : 0 < g) : RegHam (RCfg eta m) where
  W := wM P
  kin := kinT eta m P g
  V := kOp (vGalK eta m P D gamma)
  g := g
  g_pos := hg
  kin_eq := fun _ => rfl
  W_ge_one := wM_ge_one P
  Z := P.maxMass * Zc P D gamma
  Z_nonneg := mul_nonneg P.maxMass_pos.le (Zc_nonneg hgamma)
  J0 := J0g (P.maxMass * Zc P D gamma) g
  J0_pos := J0g_pos _ _
  small := J0g_small (mul_nonneg P.maxMass_pos.le (Zc_nonneg hgamma)) hg
  op_bound := fun u => op_bound_mass P u (Zc_nonneg hgamma) _
    (vGalK_op hgamma _ (J0g_pos _ _) u)

lemma kinT_ge_of_high (hg : 0 < g) {T : ℕ} {r : Fin eta} {q : RCfg eta m} (h : High T r q) :
    2 * (g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2) ≤ kinT eta m P g q := by
  unfold kinT
  have h1 := wM_ge_of_high P h
  have hM := P.maxMass_pos
  have hg2 : 0 < g ^ 2 := by positivity
  have h2 : ((T : ℝ) + 1) ^ 2 / P.maxMass ≤ wM P q - 1 := by linarith
  calc 2 * (g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2)
      = g ^ 2 / 2 * (((T : ℝ) + 1) ^ 2 / P.maxMass) := by ring
    _ ≤ g ^ 2 / 2 * (wM P q - 1) := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Tail bootstrap at the threshold `T` for a normalised eigenvector, given the potential tail
bound at `J = T/2`. -/
lemma boot_tail (hgamma : 0 ≤ gamma) (hg : 0 < g) {T : ℕ} (hT : 2 ≤ T)
    (V : EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hVtail : ∀ (r : Fin eta) (u : EuclideanSpace ℂ (RCfg eta m)),
      ‖maskOp (High T r) (V u)‖ ≤
        Zc P D gamma * (26 * ((T / 2 : ℕ) : ℝ)) * ‖maskOp (High (T - T / 2) r) u‖ +
        Zc P D gamma * Real.sqrt (1378 / ((T / 2 : ℕ) : ℝ)) * ‖wMul wTot u‖)
    (u : EuclideanSpace ℂ (RCfg eta m)) (E : ℝ)
    (hE : (wMul (kinT eta m P g) + V) u = (E : ℂ) • u)
    (hEb : |E| ≤ g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2) (r : Fin eta) :
    ‖maskOp (High T r) u‖ ≤
      Cboot (P.maxMass * Zc P D gamma) g * ‖wMul wTot u‖ / ((T : ℝ) ^ 2 * Real.sqrt T) := by
  have hZ := Zc_nonneg (P := P) (D := D) hgamma
  have hM := P.maxMass_pos
  have hMZ : 0 ≤ P.maxMass * Zc P D gamma := mul_nonneg hM.le hZ
  have hb : 0 < g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2 := by positivity
  have h1 := tail_bootstrap (kinT eta m P g) V u E hE (High T r) hb
    (fun q hq => kinT_ge_of_high hg hq) hEb
  have hX := norm_nonneg (wMul wTot u)
  have hapri : ‖maskOp (High (T - T / 2) r) u‖ ≤
      ‖wMul wTot u‖ / (1 + (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2) :=
    norm_maskOp_le_wMul _ wTot (fun q => le_trans zero_le_one (wTot_ge_one q)) (by positivity)
      (fun q hq => wTot_ge_of_high hq) u
  have h2 := hVtail r u
  have h3 : ‖maskOp (High T r) (V u)‖ ≤
      Zc P D gamma * (26 * ((T / 2 : ℕ) : ℝ)) *
          (‖wMul wTot u‖ / (1 + (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2)) +
        Zc P D gamma * Real.sqrt (1378 / ((T / 2 : ℕ) : ℝ)) * ‖wMul wTot u‖ := by
    have : 0 ≤ Zc P D gamma * (26 * ((T / 2 : ℕ) : ℝ)) := by positivity
    nlinarith
  calc ‖maskOp (High T r) u‖
      ≤ ‖maskOp (High T r) (V u)‖ / (g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2) := h1
    _ ≤ (Zc P D gamma * (26 * ((T / 2 : ℕ) : ℝ)) *
          (‖wMul wTot u‖ / (1 + (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2)) +
        Zc P D gamma * Real.sqrt (1378 / ((T / 2 : ℕ) : ℝ)) * ‖wMul wTot u‖) /
          (g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2) := by gcongr
    _ = ((P.maxMass * Zc P D gamma) * (26 * ((T / 2 : ℕ) : ℝ)) *
          (‖wMul wTot u‖ / (1 + (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2)) +
        (P.maxMass * Zc P D gamma) * Real.sqrt (1378 / ((T / 2 : ℕ) : ℝ)) * ‖wMul wTot u‖) /
          (g ^ 2 / 4 * ((T : ℝ) + 1) ^ 2) := by
        rw [show g ^ 2 / (4 * P.maxMass) * ((T : ℝ) + 1) ^ 2 =
            (g ^ 2 / 4 * ((T : ℝ) + 1) ^ 2) / P.maxMass by ring, div_div_eq_mul_div]
        ring
    _ ≤ Cboot (P.maxMass * Zc P D gamma) g * ‖wMul wTot u‖ / ((T : ℝ) ^ 2 * Real.sqrt T) :=
        boot_arith hMZ hg hX hT

/-- Form error at a normalised eigenvector with tails bootstrapped at the threshold `s`. -/
lemma form_error_eigen (hgamma : 0 ≤ gamma) {s : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    (hms : m ≤ 8 * s) (hκ : GridKernel gamma D.ref s κ) (u : EuclideanSpace ℂ (RCfg eta m))
    (hτ : ∀ r, ‖maskOp (High s r) u‖ ≤
      Cboot (P.maxMass * Zc P D gamma) g * ‖wMul wTot u‖ / ((s : ℝ) ^ 2 * Real.sqrt s)) :
    ‖inner ℂ u (Delta eta m P D gamma κ u)‖ ≤
      Cform (P.maxMass * Zc P D gamma) g * ‖wMul wTot u‖ ^ 2 / (s : ℝ) ^ 3 := by
  have hZ := Zc_nonneg (P := P) (D := D) hgamma
  have hM := P.one_le_maxMass
  have hMZ : 0 ≤ P.maxMass * Zc P D gamma := mul_nonneg P.maxMass_pos.le hZ
  have hτ0 : 0 ≤ Cboot (P.maxMass * Zc P D gamma) g * ‖wMul wTot u‖ /
      ((s : ℝ) ^ 2 * Real.sqrt s) := by
    have := Cboot_nonneg (g := g) hMZ
    positivity
  have h := Delta_form (P := P) (D := D) hgamma hs hsm hκ u u hτ0 hτ0 hτ hτ
  set τ := Cboot (P.maxMass * Zc P D gamma) g * ‖wMul wTot u‖ / ((s : ℝ) ^ 2 * Real.sqrt s)
    with hτdef
  have hA := formA_nonneg s m
  have hF : 0 ≤ formA s m * (τ * ‖wMul wTot u‖ + τ * ‖wMul wTot u‖) + 52 * m * (τ * τ) := by
    positivity
  have h2 : Zc P D gamma * (formA s m * (τ * ‖wMul wTot u‖ + τ * ‖wMul wTot u‖) +
      52 * m * (τ * τ)) ≤ (P.maxMass * Zc P D gamma) * (formA s m * (τ * ‖wMul wTot u‖ +
        τ * ‖wMul wTot u‖) + 52 * m * (τ * τ)) :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hZ hM) hF
  exact h.trans (h2.trans (form_arith hMZ (norm_nonneg _) hτ0 hs hsm hms le_rfl))

/-- **Finite grid–Galerkin comparison.**  On the padded register (radius `2m`), the
collocation Hamiltonian of an even kernel `κ` with `|κ| ≤ γ/|ν|²` that agrees with `γ/|ν|²` on
the box `‖ν‖∞ ≤ 2s` (`GridKernel γ s κ`, `2 ≤ s ≤ m ≤ 8s`) and the Galerkin Hamiltonian have
Ritz energies in the exchange sector
`(sgn, lab)` within `Cgrid / s³`, uniformly in `m`, `κ`, `sgn` and `lab`, when the masses and
charges are constant on the blocks of `lab`. -/
theorem grid_galerkin_energy (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ)
    (hP : ∀ a b, lab a = lab b → P.mass a = P.mass b ∧ P.charge a = P.charge b)
    (hgamma : 0 ≤ gamma) (hg : 0 < g) {s : ℕ} (hs : 2 ≤ s) (hsm : s ≤ m) (hms : m ≤ 8 * s)
    (hκ : GridKernel gamma D.ref s κ)
    (hNZ : ∃ u : EuclideanSpace ℂ (RCfg eta m), IsSec sgn lab u ∧ u ≠ 0)
    (Egal Eb : ℝ) (hEb : |Egal| ≤ Eb)
    (hGal : IsSecRitz sgn lab (Hgal eta m P D gamma g) Egal)
    (hbig : 4 * P.maxMass * Ebig P.maxMass (P.maxMass * Zc P D gamma) g Eb ≤
      g ^ 2 * (s : ℝ) ^ 2) :
    ∃ Egrid : ℝ, IsSecRitz sgn lab (Hgrid eta m P D κ g) Egrid ∧
      |Egrid - Egal| ≤ Cgrid P.maxMass (P.maxMass * Zc P D gamma) g Eb / (s : ℝ) ^ 3 := by
  set M := P.maxMass with hMdef
  set Z := M * Zc P D gamma with hZdef
  have hM0 : 0 < M := P.maxMass_pos
  have hZq : 0 ≤ Zc P D gamma := Zc_nonneg hgamma
  have hZ : 0 ≤ Z := mul_nonneg hM0.le hZq
  have hs1 : 1 ≤ s := by omega
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hs3 : (1 : ℝ) ≤ (s : ℝ) ^ 3 := one_le_pow₀ hsr
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
  have hCf := Cform_nonneg (g := g) hZ
  have hEb0 : 0 ≤ Eb := (abs_nonneg _).trans hEb
  have hEll0 : 0 ≤ Ell Z g Eb := Ell_nonneg hZ hEb0
  have hEbig1 : Eb + Cform Z g * (M * Ell Z g Eb) ^ 2 ≤ Ebig M Z g Eb := le_max_right _ _
  have hEbig2 : 52 * Z * J0g Z g + g ^ 2 / 4 ≤ Ebig M Z g Eb := le_max_left _ _
  have hEbEbig : Eb ≤ Ebig M Z g Eb := by nlinarith [sq_nonneg (M * Ell Z g Eb)]
  have habs : ∀ x : ℝ, x ≤ Ebig M Z g Eb → x ≤ g ^ 2 / (4 * M) * ((s : ℝ) + 1) ^ 2 := by
    intro x hx
    have h1 : g ^ 2 * (s : ℝ) ^ 2 ≤ g ^ 2 * ((s : ℝ) + 1) ^ 2 := by gcongr; linarith
    have h2 : g ^ 2 / (4 * M) * ((s : ℝ) + 1) ^ 2 = g ^ 2 * ((s : ℝ) + 1) ^ 2 / (4 * M) := by
      ring
    rw [h2, le_div_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_right hx (by positivity : (0 : ℝ) ≤ 4 * M)]
  -- Galerkin ground state: elliptic, bootstrap and form error
  have hell2 := (galRegHam (P := P) (D := D) (m := m) hgamma hg).elliptic u2 hu2n E2 hu2E
  change ‖wMul (wM P) u2‖ ≤ Ell Z g |E2| at hell2
  have hX2 : ‖wMul wTot u2‖ ≤ M * Ell Z g Eb :=
    (norm_wMul_wTot_le P u2).trans
      (mul_le_mul_of_nonneg_left (hell2.trans (Ell_mono hZ hEb)) hM0.le)
  have hboot2 : ∀ r, ‖maskOp (High s r) u2‖ ≤
      Cboot Z g * ‖wMul wTot u2‖ / ((s : ℝ) ^ 2 * Real.sqrt s) := by
    intro r
    refine boot_tail hgamma hg hs (kOp (vGalK eta m P D gamma)) ?_ u2 E2 hu2E
      (habs _ (hEb.trans hEbEbig)) r
    intro r' u
    exact vGalK_tail hgamma (s / 2) s (by omega) (Nat.div_le_self s 2) r' u
  have hform2 := form_error_eigen hgamma hs1 hsm hms hκ u2 hboot2
  have hX2sq : ‖wMul wTot u2‖ ^ 2 ≤ (M * Ell Z g Eb) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hX2 2
  have heps2 : ‖inner ℂ u2 (Delta eta m P D gamma κ u2)‖ ≤
      Cform Z g * (M * Ell Z g Eb) ^ 2 / (s : ℝ) ^ 3 :=
    hform2.trans (by gcongr)
  -- grid ground energy bounds
  have hE1up : E1 ≤ E2 + ‖inner ℂ u2 (Delta eta m P D gamma κ u2)‖ := by
    have h := hu1low u2 hu2F
    rw [hu2n, one_pow, mul_one, Hgrid_eq (gamma := gamma), inner_add_right, Complex.add_re,
      re_inner_eigen _ u2 hu2n E2 hu2E] at h
    have := Complex.re_le_norm (inner ℂ u2 (Delta eta m P D gamma κ u2))
    linarith
  have hE1low :=
    (gridRegHam (P := P) (D := D) (m := m) hgamma hκ.bound hg).eigen_lower u1 hu1n E1 hu1E
  change -(52 * Z * J0g Z g + g ^ 2 / 4) ≤ E1 at hE1low
  have hE1abs : |E1| ≤ Ebig M Z g Eb := by
    rw [abs_le]
    constructor
    · linarith
    · have h1 : Cform Z g * (M * Ell Z g Eb) ^ 2 / (s : ℝ) ^ 3 ≤
          Cform Z g * (M * Ell Z g Eb) ^ 2 := div_le_self (by positivity) hs3
      have h2 : E2 ≤ Eb := (le_abs_self E2).trans hEb
      linarith
  -- grid ground state: elliptic, bootstrap and form error
  have hell1 :=
    (gridRegHam (P := P) (D := D) (m := m) hgamma hκ.bound hg).elliptic u1 hu1n E1 hu1E
  change ‖wMul (wM P) u1‖ ≤ Ell Z g |E1| at hell1
  have hX1 : ‖wMul wTot u1‖ ≤ M * Ell Z g (Ebig M Z g Eb) :=
    (norm_wMul_wTot_le P u1).trans
      (mul_le_mul_of_nonneg_left (hell1.trans (Ell_mono hZ hE1abs)) hM0.le)
  have hboot1 : ∀ r, ‖maskOp (High s r) u1‖ ≤
      Cboot Z g * ‖wMul wTot u1‖ / ((s : ℝ) ^ 2 * Real.sqrt s) := by
    intro r
    refine boot_tail hgamma hg hs (kOp (vGridK eta m P D κ)) ?_ u1 E1 hu1E
      (habs _ hE1abs) r
    intro r' u
    exact vGridK_tail hgamma hκ.bound (s / 2) s (by omega) (Nat.div_le_self s 2) (by omega) r' u
  have hform1 := form_error_eigen hgamma hs1 hsm hms hκ u1 hboot1
  have hX1sq : ‖wMul wTot u1‖ ^ 2 ≤ (M * Ell Z g (Ebig M Z g Eb)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hX1 2
  have hEllmono : (M * Ell Z g Eb) ^ 2 ≤ (M * Ell Z g (Ebig M Z g Eb)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hM0.le hEll0)
      (mul_le_mul_of_nonneg_left (Ell_mono hZ hEbEbig) hM0.le) 2
  have heps1 : ‖inner ℂ u1 (Delta eta m P D gamma κ u1)‖ ≤ Cgrid M Z g Eb / (s : ℝ) ^ 3 := by
    unfold Cgrid
    exact hform1.trans (by gcongr)
  have heps2' : ‖inner ℂ u2 (Delta eta m P D gamma κ u2)‖ ≤ Cgrid M Z g Eb / (s : ℝ) ^ 3 := by
    unfold Cgrid
    exact heps2.trans (by gcongr)
  -- min--max
  refine ⟨E1, ⟨fun v hv => hu1low v hv, u1, hu1F, hu1n, re_inner_eigen _ u1 hu1n E1 hu1E⟩, ?_⟩
  exact ritz_compare (Hgrid eta m P D κ g) (Hgal eta m P D gamma g)
    (Delta eta m P D gamma κ) Hgrid_eq {v | IsSec sgn lab v} E1 E2
    (fun v hv => hu1low v hv) (fun v hv => hu2low v hv)
    u1 u2 hu1F hu2F hu1n hu2n (re_inner_eigen _ u1 hu1n E1 hu1E)
    (re_inner_eigen _ u2 hu2n E2 hu2E) heps1 heps2'

end Main

end PlaneWaveGridG

/-! ════════════════════════════════════════════════════════════════════
## Part `Collocation`
════════════════════════════════════════════════════════════════════ -/

/-!
# Collocation on the position grid

The padded register has `n = 4m+1` grid points per direction, at `x_j = L j / n`, i.e. at the
unit-torus points `j/n`.  The truncated kernel of the manuscript (eq. `wtrunc`),

  `w_{≤2K}(x) = (4π/Ω) ∑_{0 < ‖k_ν‖∞ ≤ 2K} e^{i k_ν·x} / |k_ν|²`,

is in unit-torus coordinates `wKer (sharpKernel γ m) m y = ∑_{0 < ‖ν‖∞ ≤ 2m} γ/|ν|² e^{2πi ν·y}`
with `γ = 1/(πL)`; a kernel of the class `𝒦_K` is `wKer κ m` for its coefficients `κ`.
The position-space grid Hamiltonian of the kernel `w_κ = wKer κ m` is

  `H_pos = F⁻¹ (kinetic multiplier) F + diag( ∑_{a<b} q_a q_b w_κ(x_{j_a} - x_{j_b})
            + ∑_{a,ℓ} q_a ζ_ℓ w_κ(x_{j_a} - R_ℓ) )`,

with the kinetic multiplier `Σ_a |k_{ν_a}|²/(2 m_a) = (g²/2) Σ_a |ν_a|²/m_a`, `g = 2π/L`, at
the register momenta `ν_a`, and `F` the unitary discrete Fourier transform (plane waves
`e^{-2πi q·j/n}`, the manuscript's convention).  For even `κ` we prove `F H_pos F⁻¹ = Hgrid`
(the fold identity with a single term, since the kernel support is a complete residue
system; for general `κ` the cyclic transfers built from `κ` are the collocation of the
reflected coefficients `κ(-ν)`), so the Ritz energies of `H_pos` and `Hgrid` coincide in every
exchange sector.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PlaneWaveGridG

open Finset UnitAddTorus

section Characters

variable {n : ℕ} [NeZero n]

/-- The standard character `z ↦ exp(2πi z/n)` of `ZMod n`. -/
noncomputable def ech (z : ZMod n) : ℂ := ZMod.stdAddChar z

lemma ech_add (x y : ZMod n) : ech (x + y) = ech x * ech y :=
  AddChar.map_add_eq_mul _ x y

lemma ech_zero : ech (0 : ZMod n) = 1 := AddChar.map_zero_eq_one _

lemma ech_sum {τ : Type*} (s : Finset τ) (f : τ → ZMod n) :
    ech (∑ t ∈ s, f t) = ∏ t ∈ s, ech (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ech_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ech_add, ih]

lemma norm_ech (z : ZMod n) : ‖ech z‖ = 1 := by
  rw [ech, ZMod.stdAddChar_apply, Circle.norm_coe]

lemma ech_neg (z : ZMod n) : ech (-z) = (starRingEnd ℂ) (ech z) := by
  have h1 : ech (-z) * ech z = 1 := by rw [← ech_add, neg_add_cancel, ech_zero]
  have h2 : (starRingEnd ℂ) (ech z) * ech z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_ech]; simp
  have hz : ech z ≠ 0 := by
    intro h; have := norm_ech z; rw [h, norm_zero] at this; exact zero_ne_one this
  exact mul_right_cancel₀ hz (h1.trans h2.symm)

lemma sum_ech_mul (b : ZMod n) :
    ∑ x : ZMod n, ech (x * b) = if b = 0 then (n : ℂ) else 0 := by
  classical
  have h := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod n) ℂ)) b
    (ZMod.isPrimitive_stdAddChar n)
  simp only [ZMod.card] at h
  change ∑ x : ZMod n, ZMod.stdAddChar (x * b) = _
  rw [h]
  split_ifs <;> simp

/-- Dot product on one register. -/
def dot3 (x y : Fin 3 → ZMod n) : ZMod n := ∑ c, x c * y c

/-- Dot product on configurations. -/
def dotC {eta : ℕ} (q j : GConfig eta n) : ZMod n := ∑ a, dot3 (q a) (j a)

lemma sum_ech_dot3 (μ : Fin 3 → ZMod n) :
    ∑ y : Fin 3 → ZMod n, ech (dot3 μ y) = if μ = 0 then (n : ℂ) ^ 3 else 0 := by
  classical
  have e : ∀ y : Fin 3 → ZMod n, ech (dot3 μ y) = ∏ c, ech (y c * μ c) := by
    intro y
    rw [dot3, ech_sum]
    exact prod_congr rfl fun c _ => by rw [mul_comm]
  simp_rw [e]
  rw [← Fintype.prod_sum (fun c x => ech (x * μ c))]
  simp_rw [sum_ech_mul]
  by_cases hμ : μ = 0
  · rw [if_pos hμ]
    simp [hμ]
  · rw [if_neg hμ]
    obtain ⟨c, hc⟩ : ∃ c, μ c ≠ 0 := by
      by_contra h; push Not at h; exact hμ (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [if_neg hc])

lemma sum_ech_dotC {eta : ℕ} (μ : GConfig eta n) :
    ∑ j : GConfig eta n, ech (dotC μ j) = if μ = 0 then ((n : ℂ) ^ 3) ^ eta else 0 := by
  classical
  have e : ∀ j : GConfig eta n, ech (dotC μ j) = ∏ a, ech (dot3 (μ a) (j a)) := by
    intro j; rw [dotC, ech_sum]
  simp_rw [e]
  rw [← Fintype.prod_sum (fun a y => ech (dot3 (μ a) y))]
  simp_rw [sum_ech_dot3]
  by_cases hμ : μ = 0
  · rw [if_pos hμ]
    simp [hμ, Finset.prod_const, Finset.card_univ]
  · rw [if_neg hμ]
    obtain ⟨a, ha⟩ : ∃ a, μ a ≠ 0 := by
      by_contra h; push Not at h; exact hμ (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [if_neg ha])

lemma dot3_sub_left (x x' y : Fin 3 → ZMod n) : dot3 (x - x') y = dot3 x y - dot3 x' y := by
  simp only [dot3, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma dotC_sub_left {eta : ℕ} (q q' j : GConfig eta n) :
    dotC (q - q') j = dotC q j - dotC q' j := by
  simp only [dotC, Pi.sub_apply, dot3_sub_left, Finset.sum_sub_distrib]

lemma dotC_comm {eta : ℕ} (q j : GConfig eta n) : dotC q j = dotC j q := by
  simp only [dotC, dot3]
  exact sum_congr rfl fun a _ => sum_congr rfl fun c _ => mul_comm _ _

end Characters

section DFT

variable {eta n : ℕ} [NeZero n]

/-- Number of configurations, `n^{3η}`, as a real. -/
noncomputable def Ncfg (eta n : ℕ) : ℝ := ((n : ℝ) ^ 3) ^ eta

lemma Ncfg_pos : 0 < Ncfg eta n := by
  unfold Ncfg
  have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  positivity

/-- The character `χ(q,j) = exp(2πi q·j/n)`. -/
noncomputable def chi (q j : GConfig eta n) : ℂ := ech (dotC q j)

/-- The unitary discrete Fourier transform from grid values to momentum coefficients. -/
noncomputable def dft : EuclideanSpace ℂ (GConfig eta n) →ₗ[ℂ] EuclideanSpace ℂ (GConfig eta n) :=
  kOp fun q j => chi q j / (Real.sqrt (Ncfg eta n) : ℂ)

/-- Its inverse (synthesis with the plane waves `e^{-2πi q·j/n}/√N`). -/
noncomputable def idft : EuclideanSpace ℂ (GConfig eta n) →ₗ[ℂ] EuclideanSpace ℂ (GConfig eta n) :=
  kOp fun j q => (starRingEnd ℂ) (chi q j) / (Real.sqrt (Ncfg eta n) : ℂ)

lemma chi_mul_conj (q q' j : GConfig eta n) :
    chi q j * (starRingEnd ℂ) (chi q' j) = chi (q - q') j := by
  rw [chi, chi, chi, ← ech_neg, ← ech_add, dotC_sub_left, sub_eq_add_neg]

lemma sum_chi_conj (q q' : GConfig eta n) :
    ∑ j, chi q j * (starRingEnd ℂ) (chi q' j) = if q = q' then (Ncfg eta n : ℂ) else 0 := by
  simp_rw [chi_mul_conj]
  have := sum_ech_dotC (eta := eta) (q - q')
  simp only [chi] at *
  rw [this]
  by_cases h : q = q'
  · rw [if_pos (sub_eq_zero.mpr h), if_pos h]
    simp [Ncfg]
  · rw [if_neg (fun h' => h (sub_eq_zero.mp h')), if_neg h]

lemma sum_conj_chi (j j' : GConfig eta n) :
    ∑ q, chi q j' * (starRingEnd ℂ) (chi q j) = if j' = j then (Ncfg eta n : ℂ) else 0 := by
  have e : ∀ q, chi q j' * (starRingEnd ℂ) (chi q j) = chi j' q * (starRingEnd ℂ) (chi j q) := by
    intro q; simp only [chi, dotC_comm q j', dotC_comm q j]
  simp_rw [e]
  exact sum_chi_conj j' j

lemma sqrt_Ncfg_sq : ((Real.sqrt (Ncfg eta n) : ℂ)) * (Real.sqrt (Ncfg eta n) : ℂ) =
    (Ncfg eta n : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt Ncfg_pos.le]

lemma dft_idft (c : EuclideanSpace ℂ (GConfig eta n)) : dft (idft c) = c := by
  have hN : (Ncfg eta n : ℂ) ≠ 0 := by exact_mod_cast Ncfg_pos.ne'
  ext q
  simp only [dft, idft, kOp_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ p, ∑ j, c p * ((starRingEnd ℂ) (chi p j) / (Real.sqrt (Ncfg eta n) : ℂ)) *
      (chi q j / (Real.sqrt (Ncfg eta n) : ℂ)) =
      c p * (∑ j, chi q j * (starRingEnd ℂ) (chi p j)) / (Ncfg eta n : ℂ) := by
    intro p
    rw [← sqrt_Ncfg_sq, Finset.mul_sum, Finset.sum_div]
    refine sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e, sum_chi_conj]
  rw [Finset.sum_eq_single q]
  · rw [if_pos rfl, mul_div_assoc, div_self hN, mul_one]
  · intro p _ hp; rw [if_neg (Ne.symm hp)]; simp
  · simp

lemma idft_dft (u : EuclideanSpace ℂ (GConfig eta n)) : idft (dft u) = u := by
  have hN : (Ncfg eta n : ℂ) ≠ 0 := by exact_mod_cast Ncfg_pos.ne'
  ext j
  simp only [dft, idft, kOp_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ j', ∑ q, u j' * (chi q j' / (Real.sqrt (Ncfg eta n) : ℂ)) *
      ((starRingEnd ℂ) (chi q j) / (Real.sqrt (Ncfg eta n) : ℂ)) =
      u j' * (∑ q, chi q j' * (starRingEnd ℂ) (chi q j)) / (Ncfg eta n : ℂ) := by
    intro j'
    rw [← sqrt_Ncfg_sq, Finset.mul_sum, Finset.sum_div]
    refine sum_congr rfl fun q _ => ?_
    ring
  simp_rw [e, sum_conj_chi]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_div_assoc, div_self hN, mul_one]
  · intro p _ hp; rw [if_neg hp]; simp
  · simp

/-- Adjointness of a kernel operator and its conjugate transpose. -/
lemma inner_kOp_adjoint {ι : Type*} [Fintype ι] (k : ι → ι → ℂ) (u w : EuclideanSpace ℂ ι) :
    inner ℂ (kOp k u) w = inner ℂ u (kOp (fun j q => (starRingEnd ℂ) (k q j)) w) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [kOp_apply, RCLike.inner_apply, map_sum, map_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun j _ => sum_congr rfl fun q _ => by ring

lemma inner_dft_dft (u v : EuclideanSpace ℂ (GConfig eta n)) :
    inner ℂ (dft u) (dft v) = inner ℂ u v := by
  rw [dft, inner_kOp_adjoint]
  have : kOp (fun j q => (starRingEnd ℂ) (chi q j / (Real.sqrt (Ncfg eta n) : ℂ))) =
      (idft : EuclideanSpace ℂ (GConfig eta n) →ₗ[ℂ] _) := by
    unfold idft
    congr 1
    funext j q
    rw [map_div₀, Complex.conj_ofReal]
  rw [this, ← dft, idft_dft]

lemma norm_dft (u : EuclideanSpace ℂ (GConfig eta n)) : ‖dft u‖ = ‖u‖ := by
  have h := inner_dft_dft u u
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖dft u‖ ^ 2 = ‖u‖ ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

lemma dotC_swap {eta : ℕ} (a b : Fin eta) (q j : GConfig eta n) :
    dotC (swapCfg a b q) (swapCfg a b j) = dotC q j := by
  unfold dotC swapCfg
  exact Equiv.sum_comp (Equiv.swap a b) (fun k => dot3 (q k) (j k))

lemma dft_sec {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ} (u : EuclideanSpace ℂ (GConfig eta n))
    (hu : IsSec sgn lab u) : IsSec sgn lab (dft u) := by
  apply kOp_preserves_sec
  · intro a b _ _ q p
    simp only [chi, dotC_swap]
  · exact hu

lemma idft_sec {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ} (u : EuclideanSpace ℂ (GConfig eta n))
    (hu : IsSec sgn lab u) : IsSec sgn lab (idft u) := by
  apply kOp_preserves_sec
  · intro a b _ _ q p
    simp only [chi, dotC_swap]
  · exact hu

end DFT

end PlaneWaveGridG

/-! ### Grid points, the truncated kernel and the fold identity -/

namespace PlaneWaveGridG

open Finset UnitAddTorus

section GridPoints

variable {n : ℕ} [NeZero n]

/-- Cast of an integer vector to register modes. -/
def castLat (nu : Lat3) : Fin 3 → ZMod n := fun c => ((nu c : ℤ) : ZMod n)

/-- The grid point `j/n` of the unit torus (physical point `L j / n`). -/
noncomputable def gridPoint (j : Fin 3 → ZMod n) : UnitAddTorus (Fin 3) :=
  fun c => ((((j c).val : ℝ) / n : ℝ) : AddCircle (1 : ℝ))

lemma ech_intCast (k : ℤ) :
    ech ((k : ZMod n)) = Complex.exp (2 * Real.pi * Complex.I * k / n) := by
  rw [ech, ZMod.stdAddChar_coe]

lemma mFourier_gridPoint (nu : Lat3) (j : Fin 3 → ZMod n) :
    mFourier nu (gridPoint j) = ech (dot3 (castLat nu) j) := by
  rw [dot3, ech_sum]
  simp only [mFourier, ContinuousMap.coe_mk, gridPoint]
  refine prod_congr rfl fun c _ => ?_
  rw [fourier_coe_apply]
  have e : (castLat nu c * j c : ZMod n) = (((nu c * (j c).val : ℤ)) : ZMod n) := by
    simp [castLat]
  rw [e, ech_intCast]
  congr 1
  push_cast
  ring

lemma mFourier_add_pt (nu : Lat3) (x y : UnitAddTorus (Fin 3)) :
    mFourier nu (x + y) = mFourier nu x * mFourier nu y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

lemma mFourier_neg_pt (nu : Lat3) (x : UnitAddTorus (Fin 3)) :
    mFourier nu (-x) = mFourier (-nu) x := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, smul_neg, neg_smul]

lemma dot3_castLat_neg (nu : Lat3) (y : Fin 3 → ZMod n) :
    dot3 (castLat (-nu)) y = -dot3 (castLat nu) y := by
  simp [dot3, castLat, Finset.sum_neg_distrib]

lemma mFourier_sub_gridPoint (nu : Lat3) (j k : Fin 3 → ZMod n) :
    mFourier nu (gridPoint j - gridPoint k) = ech (dot3 (castLat nu) (j - k)) := by
  rw [sub_eq_add_neg, mFourier_add_pt, mFourier_neg_pt, mFourier_gridPoint, mFourier_gridPoint,
    dot3_castLat_neg, ← ech_add]
  congr 1
  simp only [dot3, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

lemma mFourier_sub_pos (nu : Lat3) (j : Fin 3 → ZMod n) (R : UnitAddTorus (Fin 3)) :
    mFourier nu (gridPoint j - R) = ech (dot3 (castLat nu) j) * mFourier (-nu) R := by
  rw [sub_eq_add_neg, mFourier_add_pt, mFourier_neg_pt, mFourier_gridPoint]

end GridPoints

section TruncatedKernel

/-- The kernel of the grid method in unit-torus coordinates: the finite Fourier series
`∑_{‖ν‖∞ ≤ 2m} κ(ν) e^{2πi ν·y}` of its coefficients on the zone. For `κ = sharpKernel γ m`
it is the truncated Coulomb kernel `w_{≤2K}` of the manuscript,
`∑_{0 < ‖ν‖∞ ≤ 2m} (γ/|ν|²) e^{2πi ν·y}`. -/
noncomputable def wKer (κ : Lat3 → ℝ) (m : ℕ) (y : UnitAddTorus (Fin 3)) : ℂ :=
  ∑ nu ∈ box (2 * m), ((κ nu : ℝ) : ℂ) * mFourier nu y

variable {M : ℕ}

/-- Summing over the zone `box M` is summing over register modes. -/
lemma sum_box_eq_sum_modes (f : Lat3 → ℂ) :
    ∑ nu ∈ box M, f nu = ∑ d : GMode (2 * M + 1), f (gl d) := by
  classical
  have himg : (Finset.univ.image (gl : GMode (2 * M + 1) → Lat3)) = box M := by
    ext nu
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_box]
    constructor
    · rintro ⟨d, rfl⟩; exact gl_inBox d
    · intro h; exact ⟨ofLat nu, gl_ofLat h⟩
  rw [← himg, Finset.sum_image (fun x _ y _ h => gl_injective h)]

lemma castLat_gl (d : GMode (2 * M + 1)) : castLat (gl d) = d := ofLat_gl d

end TruncatedKernel

section Shifts

variable {eta M : ℕ}

/-- Shift of a register pair by a cyclic transfer `d` (output `q`, input `p`). -/
def shift2 (a b : Fin eta) (d : GMode (2 * M + 1)) (q : GConfig eta (2 * M + 1)) :
    GConfig eta (2 * M + 1) :=
  Function.update (Function.update q a (q a - d)) b (q b + d)

/-- Shift of one register. -/
def shift1 (a : Fin eta) (d : GMode (2 * M + 1)) (q : GConfig eta (2 * M + 1)) :
    GConfig eta (2 * M + 1) :=
  Function.update q a (q a - d)

lemma shift2_apply_a {a b : Fin eta} (hab : a ≠ b) (d : GMode (2 * M + 1))
    (q : GConfig eta (2 * M + 1)) : shift2 a b d q a = q a - d := by
  simp [shift2, Function.update_of_ne hab]

lemma shift2_apply_b (a b : Fin eta) (d : GMode (2 * M + 1)) (q : GConfig eta (2 * M + 1)) :
    shift2 a b d q b = q b + d := by
  simp [shift2]

lemma shift2_apply_other {a b k : Fin eta} (hka : k ≠ a) (hkb : k ≠ b) (d : GMode (2 * M + 1))
    (q : GConfig eta (2 * M + 1)) : shift2 a b d q k = q k := by
  simp [shift2, Function.update_of_ne hka, Function.update_of_ne hkb]

lemma gRel2_iff_shift {a b : Fin eta} (hab : a ≠ b) (q p : GConfig eta (2 * M + 1)) :
    gRel2 a b q p ↔ p = shift2 a b (q a - p a) q := by
  constructor
  · rintro ⟨hs, hsum⟩
    funext k
    by_cases hka : k = a
    · subst hka; rw [shift2_apply_a hab]; abel
    by_cases hkb : k = b
    · subst hkb
      rw [shift2_apply_b]
      have : p k = q a + q k - p a := by rw [hsum]; abel
      rw [this]; abel
    · rw [shift2_apply_other hka hkb]
      exact (hs k hka hkb).symm
  · intro hp
    refine ⟨fun k hka hkb => ?_, ?_⟩
    · rw [hp, shift2_apply_other hka hkb]
    · have h1 : p a = q a - (q a - p a) := by abel
      rw [hp, shift2_apply_a hab, shift2_apply_b]
      abel

/-- A grid pair kernel is a sum of point masses on the shifted configurations. -/
lemma tk_gpair_eq_sum {a b : Fin eta} (hab : a ≠ b) (kappa : Lat3 → ℂ)
    (q p : GConfig eta (2 * M + 1)) :
    tk (gRel2 a b) (gTau a) kappa q p =
      ∑ d : GMode (2 * M + 1), if p = shift2 a b d q then kappa (gl d) else 0 := by
  classical
  by_cases h : gRel2 a b q p
  · rw [tk_of_rel h, Finset.sum_eq_single (q a - p a)]
    · rw [if_pos ((gRel2_iff_shift hab q p).mp h)]; rfl
    · intro d _ hd
      rw [if_neg]
      intro hp
      apply hd
      have := congrFun hp a
      rw [shift2_apply_a hab] at this
      rw [this]; abel
    · simp
  · rw [tk_of_not_rel h]
    symm
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [if_neg]
    intro hp
    apply h
    have hd : q a - p a = d := by rw [hp, shift2_apply_a hab]; abel
    rw [gRel2_iff_shift hab, hd]
    exact hp

lemma spec1_iff_shift (a : Fin eta) (q p : GConfig eta (2 * M + 1)) :
    Spec1 a q p ↔ p = shift1 a (q a - p a) q := by
  constructor
  · intro hs
    funext k
    by_cases hka : k = a
    · subst hka; simp [shift1]
    · simp only [shift1, Function.update_of_ne hka]
      exact (hs k hka).symm
  · intro hp k hka
    rw [hp]
    simp [shift1, Function.update_of_ne hka]

lemma tk_gsing_eq_sum (a : Fin eta) (kappa : Lat3 → ℂ) (q p : GConfig eta (2 * M + 1)) :
    tk (Spec1 a) (gTau a) kappa q p =
      ∑ d : GMode (2 * M + 1), if p = shift1 a d q then kappa (gl d) else 0 := by
  classical
  by_cases h : Spec1 a q p
  · rw [tk_of_rel h, Finset.sum_eq_single (q a - p a)]
    · rw [if_pos ((spec1_iff_shift a q p).mp h)]; rfl
    · intro d _ hd
      rw [if_neg]
      intro hp
      apply hd
      have := congrFun hp a
      simp only [shift1, Function.update_self] at this
      rw [this]; abel
    · simp
  · rw [tk_of_not_rel h]
    symm
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [if_neg]
    intro hp
    apply h
    have hd : q a - p a = d := by rw [hp]; simp [shift1]
    rw [spec1_iff_shift, hd]
    exact hp

lemma dotC_shift2 {a b : Fin eta} (hab : a ≠ b) (d : GMode (2 * M + 1))
    (q j : GConfig eta (2 * M + 1)) :
    dotC (shift2 a b d q) j = dotC q j + dot3 d (j b - j a) := by
  classical
  have hdiff : shift2 a b d q - q = Pi.single a (-d) + Pi.single b d := by
    funext k
    by_cases hka : k = a
    · subst hka
      simp [shift2_apply_a hab, hab]
    by_cases hkb : k = b
    · subst hkb
      simp [shift2_apply_b, Ne.symm hab]
    · simp [shift2_apply_other hka hkb, hka, hkb]
  have hlin : ∀ x y : GConfig eta (2 * M + 1), dotC (x + y) j = dotC x j + dotC y j := by
    intro x y
    simp only [dotC, dot3, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsingle : ∀ (k : Fin eta) (x : GMode (2 * M + 1)),
      dotC (Pi.single k x : GConfig eta (2 * M + 1)) j = dot3 x (j k) := by
    intro k x
    rw [dotC, Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'
      simp [hk', dot3]
    · simp
  have h1 : shift2 a b d q = q + (Pi.single a (-d) + Pi.single b d) := by
    rw [← hdiff]; abel
  rw [h1, hlin, hlin, hsingle, hsingle]
  simp only [dot3, Pi.sub_apply, Pi.neg_apply, neg_mul, mul_sub, Finset.sum_neg_distrib,
    Finset.sum_sub_distrib]
  ring

lemma dotC_shift1 (a : Fin eta) (d : GMode (2 * M + 1)) (q j : GConfig eta (2 * M + 1)) :
    dotC (shift1 a d q) j = dotC q j - dot3 d (j a) := by
  classical
  have h1 : shift1 a d q = q + Pi.single a (-d) := by
    funext k
    by_cases hka : k = a
    · subst hka; simp [shift1, sub_eq_add_neg]
    · simp [shift1, hka]
  have hlin : ∀ x y : GConfig eta (2 * M + 1), dotC (x + y) j = dotC x j + dotC y j := by
    intro x y
    simp only [dotC, dot3, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hsingle : ∀ (k : Fin eta) (x : GMode (2 * M + 1)),
      dotC (Pi.single k x : GConfig eta (2 * M + 1)) j = dot3 x (j k) := by
    intro k x
    rw [dotC, Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'
      simp [hk', dot3]
    · simp
  rw [h1, hlin, hsingle]
  simp only [dot3, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

end Shifts

end PlaneWaveGridG

/-! ### The position-space grid Hamiltonian and the fold identity -/

namespace PlaneWaveGridG

open Finset UnitAddTorus

section PositionHamiltonian

variable {ν : Type*} [Fintype ν] {eta m : ℕ}

/-- Clamped nuclei given by nonnegative charges and positions on the unit torus. -/
structure PosNuclei (ν : Type*) where
  charge : ν → ℝ
  charge_nonneg : ∀ l, 0 ≤ charge l
  position : ν → UnitAddTorus (Fin 3)

/-- The register phases `e^{2πi ν·R_ℓ}` of positioned nuclei. -/
noncomputable def PosNuclei.toNucData (N : PosNuclei ν) : NucData ν where
  charge := N.charge
  charge_nonneg := N.charge_nonneg
  phase l x := mFourier x (N.position l)
  phase_norm l x := by
    have h := (mFourier x).norm_coe_le_norm (N.position l)
    rwa [mFourier_norm] at h
  phase_neg l x := mFourier_neg
  ref := coul
  ref_neg := coul_neg
  ref_bound x := le_of_eq (abs_of_nonneg (coul_nonneg x))

/-- The collocated potential at the grid configuration `j`: the kernel `wKer κ m` sampled at
all particle separations, weighted by `q_a q_b`, and at all particle--nucleus separations,
weighted by `q_a ζ_ℓ`. -/
noncomputable def collPot (P : RegParticles eta) (N : PosNuclei ν) (κ : Lat3 → ℝ)
    (j : RCfg eta m) : ℂ :=
  (∑ pr : Pairs eta, ((P.charge pr.1.1 * P.charge pr.1.2 : ℝ) : ℂ) *
      wKer κ m (gridPoint (j pr.1.1) - gridPoint (j pr.1.2))) +
    ∑ i : Fin eta, ∑ l : ν,
      ((P.charge i * N.charge l : ℝ) : ℂ) * wKer κ m (gridPoint (j i) - N.position l)

/-- Complex diagonal multiplication (a collocated potential). -/
noncomputable def cMul {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun u := WithLp.toLp 2 (fun q => f q * u q)
  map_add' := by
    intro u v
    ext q
    simp [mul_add]
  map_smul' := by
    intro z u
    ext q
    simp only [PiLp.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

lemma cMul_apply {ι : Type*} [Fintype ι] (f : ι → ℂ) (u : EuclideanSpace ℂ ι) (q : ι) :
    (cMul f u) q = f q * u q := rfl

/-- The position-space grid Hamiltonian of the kernel `κ`: kinetic multiplier through the
DFT, potential by collocation. -/
noncomputable def Hpos (P : RegParticles eta) (N : PosNuclei ν) (κ : Lat3 → ℝ) (g : ℝ) :
    EuclideanSpace ℂ (RCfg eta m) →ₗ[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
  idft ∘ₗ wMul (kinT eta m P g) ∘ₗ dft + cMul (collPot (m := m) P N κ)

lemma sum_chi_gpair {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x) {a b : Fin eta} (hab : a ≠ b)
    (q j : RCfg eta m) :
    ∑ p, chi p j * tk (gRel2 a b) (gTau a) (kgr κ) q p =
      chi q j * wKer κ m (gridPoint (j a) - gridPoint (j b)) := by
  classical
  simp_rw [tk_gpair_eq_sum hab, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  -- left: ∑_d chi (shift d) j * κ (gl d)
  have hl : ∀ d : GMode (2 * (2 * m) + 1), chi (shift2 a b d q) j * kgr κ (gl d) =
      chi q j * (kgr κ (gl d) * ech (dot3 d (j b - j a))) := by
    intro d
    rw [chi, dotC_shift2 hab, ech_add, ← chi]
    ring
  simp_rw [hl]
  rw [← Finset.mul_sum]
  congr 1
  rw [wKer, sum_box_eq_sum_modes]
  simp_rw [mFourier_sub_gridPoint, castLat_gl]
  rw [← Equiv.sum_comp (Equiv.neg (GMode (2 * (2 * m) + 1)))]
  refine sum_congr rfl fun d _ => ?_
  simp only [Equiv.neg_apply, gl_neg, hκe, kgr]
  congr 2
  simp only [dot3, Pi.sub_apply, Pi.neg_apply]
  exact sum_congr rfl fun c _ => by ring

lemma sum_chi_gsing (N : PosNuclei ν) {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x) (a : Fin eta)
    (l : ν) (q j : RCfg eta m) :
    ∑ p, chi p j * tk (Spec1 a) (gTau a) (kgn N.toNucData κ l) q p =
      chi q j * ((-(N.charge l : ℂ)) * wKer κ m (gridPoint (j a) - N.position l)) := by
  classical
  simp_rw [tk_gsing_eq_sum, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hl : ∀ d : GMode (2 * (2 * m) + 1),
      chi (shift1 a d q) j * kgn N.toNucData κ l (gl d) =
        chi q j * (kgn N.toNucData κ l (gl d) * ech (-dot3 d (j a))) := by
    intro d
    rw [chi, dotC_shift1, sub_eq_add_neg, ech_add, ← chi]
    ring
  simp_rw [hl]
  rw [← Finset.mul_sum]
  congr 1
  rw [wKer, sum_box_eq_sum_modes, Finset.mul_sum]
  simp_rw [mFourier_sub_pos, castLat_gl]
  rw [← Equiv.sum_comp (Equiv.neg (GMode (2 * (2 * m) + 1)))]
  refine sum_congr rfl fun d _ => ?_
  simp only [Equiv.neg_apply, gl_neg, hκe, kgn, kgr, PosNuclei.toNucData]
  have e : dot3 (-d) (j a) = -dot3 d (j a) := by
    simp only [dot3, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [e, neg_neg]
  ring

lemma sum_mul_coef {ι : Type*} [Fintype ι] (f : ι → ℂ) (c : ℂ) (X : ι → ℂ) :
    ∑ p, f p * (c * X p) = c * ∑ p, f p * X p := by
  rw [Finset.mul_sum]
  exact sum_congr rfl fun p _ => by ring

/-- **Fold identity.**  The DFT intertwines collocation of the kernel `wKer κ m` with the
cyclic momentum operator `vGridK`. -/
lemma sum_chi_vGridK (P : RegParticles eta) (N : PosNuclei ν) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x) (q j : RCfg eta m) :
    ∑ p, chi p j * vGridK eta m P N.toNucData κ q p = chi q j * collPot P N κ j := by
  unfold vGridK collPot
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Fintype.sum_sum_type, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine sum_congr rfl fun pr _ => ?_
    simp only [gridTerm, RegParticles.tcoef]
    rw [sum_mul_coef, sum_chi_gpair hκe (ne_of_lt pr.2) q j]
    ring
  · rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun l _ => ?_
    simp only [gridTerm, RegParticles.tcoef]
    rw [sum_mul_coef, sum_chi_gsing N hκe i l q j]
    push_cast
    ring

lemma dft_cMul (P : RegParticles eta) (N : PosNuclei ν) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x) (u : EuclideanSpace ℂ (RCfg eta m)) :
    dft (cMul (collPot P N κ) u) = kOp (vGridK eta m P N.toNucData κ) (dft u) := by
  ext q
  simp only [dft, kOp_apply, cMul_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun j _ => ?_
  have h := sum_chi_vGridK P N hκe q j
  calc collPot P N κ j * u j * (chi q j / (Real.sqrt (Ncfg eta (2 * (2 * m) + 1)) : ℂ))
      = u j * (chi q j * collPot P N κ j) /
          (Real.sqrt (Ncfg eta (2 * (2 * m) + 1)) : ℂ) := by ring
    _ = u j * (∑ p, chi p j * vGridK eta m P N.toNucData κ q p) /
          (Real.sqrt (Ncfg eta (2 * (2 * m) + 1)) : ℂ) := by rw [h]
    _ = ∑ p, u j * (chi p j / (Real.sqrt (Ncfg eta (2 * (2 * m) + 1)) : ℂ)) *
          vGridK eta m P N.toNucData κ q p := by
        rw [Finset.mul_sum, Finset.sum_div]
        exact sum_congr rfl fun p _ => by ring

/-- The DFT conjugates the position-space grid Hamiltonian to the momentum operator. -/
lemma dft_Hpos (P : RegParticles eta) (N : PosNuclei ν) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x) (g : ℝ) (u : EuclideanSpace ℂ (RCfg eta m)) :
    dft (Hpos P N κ g u) = Hgrid eta m P N.toNucData κ g (dft u) := by
  simp only [Hpos, Hgrid, LinearMap.add_apply, LinearMap.comp_apply, map_add, dft_idft,
    dft_cMul P N hκe]

lemma inner_Hpos (P : RegParticles eta) (N : PosNuclei ν) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x) (g : ℝ) (u : EuclideanSpace ℂ (RCfg eta m)) :
    inner ℂ u (Hpos P N κ g u) =
      inner ℂ (dft u) (Hgrid eta m P N.toNucData κ g (dft u)) := by
  rw [← dft_Hpos P N hκe, inner_dft_dft]

/-- The position-space and momentum-space grid Ritz energies of an even kernel coincide in
every exchange sector. -/
theorem isSecRitz_Hpos_iff (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ) (P : RegParticles eta)
    (N : PosNuclei ν) (κ : Lat3 → ℝ) (hκe : ∀ x, κ (-x) = κ x) (g E : ℝ) :
    IsSecRitz sgn lab (Hpos (m := m) P N κ g) E ↔
      IsSecRitz sgn lab (Hgrid eta m P N.toNucData κ g) E := by
  constructor
  · rintro ⟨hlow, u, hu, hn, hv⟩
    refine ⟨fun c hc => ?_, dft u, dft_sec u hu, by rw [norm_dft, hn], ?_⟩
    · have h := hlow (idft c) (idft_sec c hc)
      rw [inner_Hpos P N hκe, dft_idft] at h
      have hn' : ‖idft c‖ = ‖c‖ := by
        have := norm_dft (idft c); rw [dft_idft] at this; exact this.symm
      rwa [hn'] at h
    · rw [← inner_Hpos P N hκe]; exact hv
  · rintro ⟨hlow, c, hc, hn, hv⟩
    refine ⟨fun u hu => ?_, idft c, idft_sec c hc, ?_, ?_⟩
    · have h := hlow (dft u) (dft_sec u hu)
      rw [norm_dft, ← inner_Hpos P N hκe] at h
      exact h
    · have := norm_dft (idft c); rw [dft_idft] at this; rw [← this, hn]
    · rw [inner_Hpos P N hκe, dft_idft]; exact hv

end PositionHamiltonian

/-! ### Relabelling of registers -/

section Relabel

variable {eta n : ℕ} [NeZero n]

/-- Relabelling of the registers of a grid state: `(gridPermute π u) q = u (q ∘ π)`. For a
transposition this is the exchange `swapCfg`. -/
noncomputable def gridPermute (π : Equiv.Perm (Fin eta)) :
    EuclideanSpace ℂ (GConfig eta n) →ₗᵢ[ℂ] EuclideanSpace ℂ (GConfig eta n) where
  toFun u := WithLp.toLp 2 (fun q => u (q ∘ π))
  map_add' := by
    intro u v
    rfl
  map_smul' := by
    intro c u
    rfl
  norm_map' := by
    intro u
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp (Equiv.arrowCongr π.symm (Equiv.refl (GMode n)))
      (fun q => ‖u q‖ ^ 2)

@[simp] lemma gridPermute_apply (π : Equiv.Perm (Fin eta)) (u : EuclideanSpace ℂ (GConfig eta n))
    (q : GConfig eta n) : gridPermute π u q = u (q ∘ π) := rfl

lemma gridPermute_mul (π ρ : Equiv.Perm (Fin eta)) (u : EuclideanSpace ℂ (GConfig eta n)) :
    gridPermute π (gridPermute ρ u) = gridPermute (π * ρ) u := rfl

lemma gridPermute_one (u : EuclideanSpace ℂ (GConfig eta n)) : gridPermute 1 u = u := rfl

/-- The exchange sector in terms of the relabelling operator. -/
lemma isSec_iff_gridPermute (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ)
    (u : EuclideanSpace ℂ (GConfig eta n)) :
    IsSec sgn lab u ↔ ∀ a b : Fin eta, a ≠ b → lab a = lab b →
      gridPermute (Equiv.swap a b) u = sgn a • u := by
  constructor
  · intro h a b hab hlab
    ext q
    exact h a b hab hlab q
  · intro h a b hab hlab q
    exact congrArg (fun v : EuclideanSpace ℂ (GConfig eta n) => v q) (h a b hab hlab)

/-- A kernel operator commutes with a relabelling that leaves its kernel invariant. -/
lemma kOp_gridPermute (π : Equiv.Perm (Fin eta)) (k : GConfig eta n → GConfig eta n → ℂ)
    (hk : ∀ q p, k (q ∘ π) (p ∘ π) = k q p) (u : EuclideanSpace ℂ (GConfig eta n)) :
    kOp k (gridPermute π u) = gridPermute π (kOp k u) := by
  ext q
  rw [kOp_apply, gridPermute_apply, kOp_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr π.symm (Equiv.refl (GMode n))) _ _ fun p => ?_
  change u (p ∘ π) * k q p = u (p ∘ π) * k (q ∘ π) (p ∘ π)
  rw [hk]

/-- A multiplier commutes with a relabelling that leaves it invariant. -/
lemma wMul_gridPermute (π : Equiv.Perm (Fin eta)) (w : GConfig eta n → ℝ)
    (hw : ∀ q, w (q ∘ π) = w q) (u : EuclideanSpace ℂ (GConfig eta n)) :
    wMul w (gridPermute π u) = gridPermute π (wMul w u) := by
  ext q
  rw [wMul_apply, gridPermute_apply, gridPermute_apply, wMul_apply, hw]

lemma dotC_comp_perm (π : Equiv.Perm (Fin eta)) (q j : GConfig eta n) :
    dotC (q ∘ π) (j ∘ π) = dotC q j := by
  unfold dotC
  exact Equiv.sum_comp π (fun k => dot3 (q k) (j k))

lemma dft_gridPermute (π : Equiv.Perm (Fin eta)) (u : EuclideanSpace ℂ (GConfig eta n)) :
    dft (gridPermute π u) = gridPermute π (dft u) := by
  apply kOp_gridPermute
  intro q p
  simp only [chi, dotC_comp_perm]

lemma idft_gridPermute (π : Equiv.Perm (Fin eta)) (u : EuclideanSpace ℂ (GConfig eta n)) :
    idft (gridPermute π u) = gridPermute π (idft u) := by
  apply kOp_gridPermute
  intro q p
  simp only [chi, dotC_comp_perm]

end Relabel

section RelabelHamiltonian

variable {ν : Type*} [Fintype ν] {eta m : ℕ}

/-- The grid Hamiltonian of an even kernel commutes with every relabelling of the registers
that preserves the masses and charges. -/
lemma Hgrid_gridPermute (P : RegParticles eta) (D : NucData ν) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x) (g : ℝ) (π : Equiv.Perm (Fin eta))
    (hπ : ∀ k, P.mass (π k) = P.mass k ∧ P.charge (π k) = P.charge k)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    Hgrid eta m P D κ g (gridPermute π u) = gridPermute π (Hgrid eta m P D κ g u) := by
  simp only [Hgrid, LinearMap.add_apply, map_add]
  rw [wMul_gridPermute _ _ (fun q => kinT_perm π (fun k => (hπ k).1) q),
    kOp_gridPermute _ _ (fun q p => vGridK_perm hκe π (fun k => (hπ k).2) q p)]

/-- The position-space grid Hamiltonian of an even kernel commutes with every relabelling of
the registers that preserves the masses and charges. -/
lemma Hpos_gridPermute (P : RegParticles eta) (N : PosNuclei ν) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x) (g : ℝ) (π : Equiv.Perm (Fin eta))
    (hπ : ∀ k, P.mass (π k) = P.mass k ∧ P.charge (π k) = P.charge k)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    Hpos P N κ g (gridPermute π u) = gridPermute π (Hpos P N κ g u) := by
  have hconj : ∀ v : EuclideanSpace ℂ (RCfg eta m),
      Hpos P N κ g v = idft (Hgrid eta m P N.toNucData κ g (dft v)) := by
    intro v
    rw [← dft_Hpos P N hκe, idft_dft]
  rw [hconj, hconj, dft_gridPermute, Hgrid_gridPermute P _ hκe g π hπ, idft_gridPermute]

end RelabelHamiltonian

end PlaneWaveGridG

/-! ## Kernel axiom-dependency report -/
