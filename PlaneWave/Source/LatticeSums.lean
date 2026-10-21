import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Lattice sums on `ℤ³`

Elementary lattice-sum estimates on `L3 = ℤ³`, all obtained from the sup-norm shells
`box n \ box (n - 1)` (`n ≥ 1`), which have at most `26 n²` points, each with `|ν|² ≥ n²`:

* `card_box`, `mem_box_of_lsq_le`, `card_shell_le`, `lsq_ge_of_not_mem`: boxes and shells;
* `sum_inv_lsq_box_le`, `sum_inv_lsq_ball_le`: the low-pass Coulomb sums
  `Σ_{0 < ‖ν‖_∞ ≤ N} |ν|⁻² ≤ 26 N` and `Σ_{0 < |ν| ≤ R} |ν|⁻² ≤ 26 (R + 1)`;
* `sum_weight_le`, `summable_weight`, `tsum_weight_le`: for `s > 3/2`,
  `Σ_ν (1 + |ν|²)^{-s} ≤ 1 + 26 (1 + 1/(2s - 3))`, over any finite set and over all of `ℤ³`;
* `sum_norm_le_weighted`, `sum_norm_le_weighted_shift`: the weighted Cauchy–Schwarz bound
  `Σ_{ν ∈ S} ‖x ν‖ ≤ √Z √(Σ_{ν ∈ S} (1 + |ν + c|²)^s ‖x ν‖²)` with `Z` the bound above;
* `card_euclid_shell_le`: the Euclidean shell `lam < |ν| ≤ 2 lam` has at most `125 lam³` points.

The p-series bound `Σ_{n=1}^N n^{-q} ≤ 1 + 1/(q - 1)` (`sum_Icc_rpow_neg_le`) is proved by
telescoping with the mean value theorem, so no integral-comparison module is needed.
-/

set_option autoImplicit false

open Finset

namespace FSLattice

abbrev L3 := Fin 3 → ℤ
/-- squared Euclidean norm of a lattice vector -/
def lsq (ν : L3) : ℝ := (ν 0 : ℝ) ^ 2 + (ν 1 : ℝ) ^ 2 + (ν 2 : ℝ) ^ 2
/-- the sup-norm box of radius N -/
noncomputable def box (N : ℕ) : Finset L3 := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

/-! ## Elementary facts about `lsq` and `box` -/

lemma lsq_nonneg (ν : L3) : 0 ≤ lsq ν := by unfold lsq; positivity

lemma lsq_zero : lsq 0 = 0 := by simp [lsq]

lemma sq_le_lsq (ν : L3) (i : Fin 3) : (ν i : ℝ) ^ 2 ≤ lsq ν := by
  have h0 := sq_nonneg (ν 0 : ℝ)
  have h1 := sq_nonneg (ν 1 : ℝ)
  have h2 := sq_nonneg (ν 2 : ℝ)
  unfold lsq
  fin_cases i <;> simp <;> linarith

lemma mem_box {N : ℕ} {ν : L3} : ν ∈ box N ↔ ∀ i, -(N : ℤ) ≤ ν i ∧ ν i ≤ N := by
  simp [box, Fintype.mem_piFinset]

lemma zero_mem_box (N : ℕ) : (0 : L3) ∈ box N := by
  rw [mem_box]
  intro i
  simp

lemma box_zero : box 0 = {0} := by
  ext ν
  rw [mem_box, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    have := h i
    simp only [CharP.cast_eq_zero, neg_zero] at this
    simp only [Pi.zero_apply]
    omega
  · rintro rfl i
    simp

lemma box_mono {M N : ℕ} (h : M ≤ N) : box M ⊆ box N := by
  intro ν hν
  rw [mem_box] at hν ⊢
  intro i
  have := hν i
  omega

/-- Every finite set of lattice points lies in some box. -/
lemma exists_box (S : Finset L3) : ∃ N : ℕ, S ⊆ box N := by
  refine ⟨S.sup fun ν => (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs, fun ν hν => ?_⟩
  have hle : (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs ≤
      S.sup fun ν => (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs :=
    Finset.le_sup (f := fun ν => (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs) hν
  rw [mem_box]
  intro i
  have hi : (ν i).natAbs ≤ (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs := by
    fin_cases i <;> simp <;> omega
  omega

/-- **Result 1.** The box of radius `N` has `(2N + 1)³` points. -/
theorem card_box (N : ℕ) : (box N).card = (2 * N + 1) ^ 3 := by
  simp only [box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

/-- A lattice point with `|ν| ≤ R` (`R ≥ 0`) lies in the box of radius `⌊R⌋₊`. -/
lemma mem_box_floor_of_lsq_le {ν : L3} {R : ℝ} (hR : 0 ≤ R) (h : lsq ν ≤ R ^ 2) :
    ν ∈ box ⌊R⌋₊ := by
  rw [mem_box]
  intro i
  have hi : |(ν i : ℝ)| ≤ R := abs_le_of_sq_le_sq ((sq_le_lsq ν i).trans h) hR
  have hn : (ν i).natAbs ≤ ⌊R⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact hi
  omega

/-- **Result 2.** A lattice point with `|ν|² ≤ N²` lies in the box of radius `N`. -/
theorem mem_box_of_lsq_le {ν : L3} {N : ℕ} (h : lsq ν ≤ (N : ℝ) ^ 2) : ν ∈ box N := by
  have := mem_box_floor_of_lsq_le (Nat.cast_nonneg N) h
  rwa [Nat.floor_natCast] at this

/-- **Result 3a.** The sup-norm shell `box n \ box (n - 1)` has at most `26 n²` points
(exactly `24 n² + 2`). -/
theorem card_shell_le (n : ℕ) (hn : 1 ≤ n) : ((box n) \ (box (n - 1))).card ≤ 26 * n ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Finset.card_sdiff_of_subset (box_mono (Nat.le_succ m)), card_box,
    card_box]
  have h : (2 * (m + 1) + 1) ^ 3 - (2 * m + 1) ^ 3 = 24 * (m + 1) ^ 2 + 2 := by
    have : (2 * m + 1) ^ 3 ≤ (2 * (m + 1) + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    zify [this]
    ring
  rw [h]
  have h1 : 1 ≤ (m + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos m)
  omega

/-- **Result 3b.** Outside the box of radius `n - 1` (`n ≥ 1`), `|ν|² ≥ n²`. -/
theorem lsq_ge_of_not_mem {ν : L3} {n : ℕ} (h : ν ∉ box (n - 1)) (hn : 1 ≤ n) :
    (n : ℝ) ^ 2 ≤ lsq ν := by
  simp only [mem_box, not_forall, not_and_or, not_le] at h
  obtain ⟨i, hi⟩ := h
  have hi' : (n : ℤ) ≤ ν i ∨ ν i ≤ -(n : ℤ) := by omega
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsq : (n : ℝ) ^ 2 ≤ (ν i : ℝ) ^ 2 := by
    rcases hi' with h1 | h1
    · have h2 : (n : ℝ) ≤ ν i := by exact_mod_cast h1
      nlinarith
    · have h2 : (ν i : ℝ) ≤ -(n : ℝ) := by exact_mod_cast h1
      nlinarith
  exact hsq.trans (sq_le_lsq ν i)

/-! ## Shell decomposition of box sums -/

/-- Shell decomposition: if `g ≤ b n` on each shell `box n \ box (n - 1)` (`n ≥ 1`, `b n ≥ 0`),
then `Σ_{box N} g ≤ g 0 + Σ_{n=1}^{N} 26 n² b n`. -/
lemma sum_box_le_shells (g : L3 → ℝ) (b : ℕ → ℝ) (hb : ∀ n, 1 ≤ n → 0 ≤ b n)
    (hg : ∀ n : ℕ, 1 ≤ n → ∀ ν ∈ box n \ box (n - 1), g ν ≤ b n) (N : ℕ) :
    ∑ ν ∈ box N, g ν ≤ g 0 + ∑ n ∈ Icc 1 N, 26 * (n : ℝ) ^ 2 * b n := by
  induction N with
  | zero =>
    rw [box_zero, Finset.sum_singleton, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty,
      add_zero]
  | succ N ih =>
    have hsplit : box (N + 1) = box N ∪ (box (N + 1) \ box N) :=
      (Finset.union_sdiff_of_subset (box_mono (Nat.le_succ N))).symm
    have hcard : ((box (N + 1) \ box N).card : ℝ) ≤ 26 * ((N + 1 : ℕ) : ℝ) ^ 2 := by
      have := card_shell_le (N + 1) (by omega)
      rw [Nat.add_sub_cancel] at this
      exact_mod_cast this
    have hshell : ∑ ν ∈ box (N + 1) \ box N, g ν ≤ 26 * ((N + 1 : ℕ) : ℝ) ^ 2 * b (N + 1) := by
      calc ∑ ν ∈ box (N + 1) \ box N, g ν ≤ ∑ _ν ∈ box (N + 1) \ box N, b (N + 1) :=
            Finset.sum_le_sum fun ν hν =>
              hg (N + 1) (by omega) ν (by rw [Nat.add_sub_cancel]; exact hν)
        _ = (box (N + 1) \ box N).card * b (N + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 26 * ((N + 1 : ℕ) : ℝ) ^ 2 * b (N + 1) :=
            mul_le_mul_of_nonneg_right hcard (hb _ (by omega))
    rw [hsplit, Finset.sum_union Finset.disjoint_sdiff, Finset.sum_Icc_succ_top (by omega)]
    linarith

/-! ## Low-pass Coulomb sums -/

/-- On the shell of radius `n ≥ 1`, `1/|ν|² ≤ 1/n²`. -/
lemma inv_lsq_le_shell {n : ℕ} (hn : 1 ≤ n) {ν : L3} (hν : ν ∈ box n \ box (n - 1)) :
    1 / lsq ν ≤ 1 / (n : ℝ) ^ 2 := by
  have hl := lsq_ge_of_not_mem (Finset.mem_sdiff.mp hν).2 hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact one_div_le_one_div_of_le (by positivity) hl

/-- **Result 4a (low-pass Coulomb sum).** `Σ_{ν ∈ box N, ν ≠ 0} 1/|ν|² ≤ 26 N` (any `N`). -/
theorem sum_inv_lsq_box_le (N : ℕ) :
    ∑ ν ∈ (box N).filter (fun ν => ν ≠ 0), 1 / lsq ν ≤ 26 * N := by
  have hfilt : ∑ ν ∈ (box N).filter (fun ν => ν ≠ 0), 1 / lsq ν = ∑ ν ∈ box N, 1 / lsq ν :=
    Finset.sum_filter_of_ne fun ν _ h h0 => h (by rw [h0, lsq_zero, div_zero])
  rw [hfilt]
  have key := sum_box_le_shells (fun ν => 1 / lsq ν) (fun n => 1 / (n : ℝ) ^ 2)
    (fun n _ => div_nonneg zero_le_one (sq_nonneg _)) (fun n hn ν hν => inv_lsq_le_shell hn hν) N
  have hterm : ∀ n ∈ Icc 1 N, 26 * (n : ℝ) ^ 2 * (1 / (n : ℝ) ^ 2) = 26 := by
    intro n hn
    have : (n : ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      positivity
    field_simp
  rw [lsq_zero, div_zero, zero_add, Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul, Nat.add_sub_cancel, mul_comm] at key
  exact key

/-- Low-pass Coulomb sum over a Euclidean ball, sharp form: `Σ_{0 < |ν| ≤ R} 1/|ν|² ≤ 26 R`
for `R ≥ 0` (the ambient box `box N` is arbitrary). -/
theorem sum_inv_lsq_ball_le' {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    ∑ ν ∈ (box N).filter (fun ν => ν ≠ 0 ∧ lsq ν ≤ R ^ 2), 1 / lsq ν ≤ 26 * R := by
  calc ∑ ν ∈ (box N).filter (fun ν => ν ≠ 0 ∧ lsq ν ≤ R ^ 2), 1 / lsq ν
      ≤ ∑ ν ∈ (box ⌊R⌋₊).filter (fun ν => ν ≠ 0), 1 / lsq ν := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ν hν
          rw [Finset.mem_filter] at hν ⊢
          exact ⟨mem_box_floor_of_lsq_le hR hν.2.2, hν.2.1⟩
        · intro ν _ _
          exact div_nonneg zero_le_one (lsq_nonneg ν)
    _ ≤ 26 * (⌊R⌋₊ : ℝ) := sum_inv_lsq_box_le _
    _ ≤ 26 * R := by
        have := Nat.floor_le hR
        linarith

/-- **Result 4b (low-pass Coulomb sum, Euclidean ball).**
`Σ_{ν ∈ box ⌈R⌉₊, ν ≠ 0, |ν| ≤ R} 1/|ν|² ≤ 26 (R + 1)` for `R ≥ 1`. -/
theorem sum_inv_lsq_ball_le {R : ℝ} (hR : 1 ≤ R) :
    ∑ ν ∈ (box ⌈R⌉₊).filter (fun ν => ν ≠ 0 ∧ lsq ν ≤ R ^ 2), 1 / lsq ν ≤ 26 * (R + 1) := by
  have := sum_inv_lsq_ball_le' (by linarith : (0 : ℝ) ≤ R) ⌈R⌉₊
  linarith

/-! ## The p-series bound -/

/-- Mean value theorem for `t ↦ t^{-r}`: `r (x + 1)^{-r-1} ≤ x^{-r} - (x + 1)^{-r}` (`x, r > 0`). -/
lemma rpow_neg_sub_ge {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    r * (x + 1) ^ (-r - 1) ≤ x ^ (-r) - (x + 1) ^ (-r) := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-r))
    (fun t => -r * t ^ (-r - 1)) (by linarith : x < x + 1)
    (fun t ht => (Real.continuousAt_rpow_const t (-r)
      (Or.inl (by linarith [ht.1] : t ≠ 0))).continuousWithinAt)
    (fun t ht => Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1] : t ≠ 0)))
  rw [add_sub_cancel_left, div_one] at hcd
  have hc0 : 0 < c := by linarith [hc.1]
  have hmono : (x + 1) ^ (-r - 1) ≤ c ^ (-r - 1) :=
    Real.rpow_le_rpow_of_nonpos hc0 hc.2.le (by linarith)
  have := mul_le_mul_of_nonneg_left hmono hr.le
  linarith

/-- Telescoped p-series: `(q - 1) Σ_{n=1}^{N+1} n^{-q} + (N + 1)^{1-q} ≤ q` for `q > 1`. -/
lemma sum_Icc_rpow_neg_aux {q : ℝ} (hq : 1 < q) (N : ℕ) :
    (q - 1) * ∑ n ∈ Icc 1 (N + 1), (n : ℝ) ^ (-q) + ((N : ℝ) + 1) ^ (1 - q) ≤ q := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hstep := rpow_neg_sub_ge (r := q - 1) (x := (N : ℝ) + 1) (by linarith) (by positivity)
    rw [show -(q - 1) - 1 = -q by ring, show -(q - 1) = 1 - q by ring] at hstep
    push_cast
    linarith

/-- **p-series bound**: `Σ_{n=1}^N n^{-q} ≤ 1 + 1/(q - 1)` for `q > 1`. -/
lemma sum_Icc_rpow_neg_le {q : ℝ} (hq : 1 < q) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-q) ≤ 1 + 1 / (q - 1) := by
  have hq1 : 0 < q - 1 := by linarith
  have hfrac : 0 < 1 / (q - 1) := by positivity
  rcases N with _ | N
  · rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    linarith
  · have h := sum_Icc_rpow_neg_aux hq N
    have hpos : 0 ≤ ((N : ℝ) + 1) ^ (1 - q) := by positivity
    have key : (q - 1) * (1 + 1 / (q - 1)) = q := by
      rw [mul_add, mul_one, mul_one_div_cancel hq1.ne']
      ring
    exact le_of_mul_le_mul_left (by rw [key]; linarith) hq1

/-! ## Weighted square-summability -/

/-- On the shell of radius `n ≥ 1`, `(1 + |ν|²)^{-s} ≤ (n²)^{-s}` (`s ≥ 0`). -/
lemma weight_le_shell {s : ℝ} (hs : 0 ≤ s) {n : ℕ} (hn : 1 ≤ n) {ν : L3}
    (hν : ν ∈ box n \ box (n - 1)) : (1 + lsq ν) ^ (-s) ≤ ((n : ℝ) ^ 2) ^ (-s) := by
  have hl := lsq_ge_of_not_mem (Finset.mem_sdiff.mp hν).2 hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)

lemma sq_mul_rpow_neg {x : ℝ} (hx : 0 < x) (s : ℝ) :
    x ^ 2 * (x ^ 2) ^ (-s) = x ^ (-(2 * s - 2)) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

/-- The weight sum over a box: `Σ_{box N} (1 + |ν|²)^{-s} ≤ 1 + 26 (1 + 1/(2s - 3))`. -/
lemma sum_box_weight_le {s : ℝ} (hs : 3 / 2 < s) (N : ℕ) :
    ∑ ν ∈ box N, (1 + lsq ν) ^ (-s) ≤ 1 + 26 * (1 + 1 / (2 * s - 3)) := by
  have key := sum_box_le_shells (fun ν => (1 + lsq ν) ^ (-s)) (fun n => ((n : ℝ) ^ 2) ^ (-s))
    (fun n _ => Real.rpow_nonneg (sq_nonneg _) _)
    (fun n hn ν hν => weight_le_shell (by linarith) hn hν) N
  have hsum : ∑ n ∈ Icc 1 N, 26 * (n : ℝ) ^ 2 * ((n : ℝ) ^ 2) ^ (-s) =
      26 * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(2 * s - 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast this
    rw [mul_assoc, sq_mul_rpow_neg this]
  have hp := sum_Icc_rpow_neg_le (q := 2 * s - 2) (by linarith) N
  rw [show 2 * s - 2 - 1 = 2 * s - 3 by ring] at hp
  rw [lsq_zero, add_zero, Real.one_rpow, hsum] at key
  linarith

/-- **Result 5a (finite form).** For `s > 3/2` and every finite `S ⊆ ℤ³`,
`Σ_{ν ∈ S} (1 + |ν|²)^{-s} ≤ 1 + 26 (1 + 1/(2s - 3))`. -/
theorem sum_weight_le {s : ℝ} (hs : 3 / 2 < s) (S : Finset L3) :
    ∑ ν ∈ S, (1 + lsq ν) ^ (-s) ≤ 1 + 26 * (1 + 1 / (2 * s - 3)) := by
  obtain ⟨N, hN⟩ := exists_box S
  refine (Finset.sum_le_sum_of_subset_of_nonneg hN fun ν _ _ => ?_).trans (sum_box_weight_le hs N)
  exact Real.rpow_nonneg (by linarith [lsq_nonneg ν]) _

/-- **Result 5b.** `ν ↦ (1 + |ν|²)^{-s}` is summable over `ℤ³` for `s > 3/2`. -/
theorem summable_weight {s : ℝ} (hs : 3 / 2 < s) :
    Summable (fun ν : L3 => (1 + lsq ν) ^ (-s)) :=
  summable_of_sum_le (fun ν => Real.rpow_nonneg (by linarith [lsq_nonneg ν]) _)
    (sum_weight_le hs)

/-- **Result 5c.** `Σ_{ν ∈ ℤ³} (1 + |ν|²)^{-s} ≤ 1 + 26 (1 + 1/(2s - 3))` for `s > 3/2`. -/
theorem tsum_weight_le {s : ℝ} (hs : 3 / 2 < s) :
    ∑' ν : L3, (1 + lsq ν) ^ (-s) ≤ 1 + 26 * (1 + 1 / (2 * s - 3)) :=
  Real.tsum_le_of_sum_le (fun ν => Real.rpow_nonneg (by linarith [lsq_nonneg ν]) _)
    (sum_weight_le hs)

/-- Translation invariance: the shifted weight sum obeys the same bound. -/
lemma sum_weight_shift_le {s : ℝ} (hs : 3 / 2 < s) (S : Finset L3) (c : L3) :
    ∑ ν ∈ S, (1 + lsq (ν + c)) ^ (-s) ≤ 1 + 26 * (1 + 1 / (2 * s - 3)) := by
  have := sum_weight_le hs (S.image (· + c))
  rwa [Finset.sum_image fun a _ b _ h => add_right_cancel h] at this

/-! ## Weighted Cauchy–Schwarz -/

/-- Weighted Cauchy–Schwarz for a general positive weight `w` with `Σ_{S} w^{-s} ≤ Z`. -/
lemma sum_norm_le_of_weight (S : Finset L3) (x : L3 → ℂ) (w : L3 → ℝ) (hw : ∀ ν, 0 < w ν)
    (s Z : ℝ) (hZ : ∑ ν ∈ S, w ν ^ (-s) ≤ Z) :
    ∑ ν ∈ S, ‖x ν‖ ≤ Real.sqrt Z * Real.sqrt (∑ ν ∈ S, w ν ^ s * ‖x ν‖ ^ 2) := by
  have hsplit : ∀ ν, ‖x ν‖ = w ν ^ (-s / 2) * (w ν ^ (s / 2) * ‖x ν‖) := by
    intro ν
    rw [← mul_assoc, ← Real.rpow_add (hw ν), show -s / 2 + s / 2 = (0 : ℝ) by ring,
      Real.rpow_zero, one_mul]
  have h1 : ∀ ν, (w ν ^ (-s / 2)) ^ 2 = w ν ^ (-s) := by
    intro ν
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hw ν).le]
    congr 1
    push_cast
    ring
  have h2 : ∀ ν, (w ν ^ (s / 2) * ‖x ν‖) ^ 2 = w ν ^ s * ‖x ν‖ ^ 2 := by
    intro ν
    rw [mul_pow, ← Real.rpow_natCast (w ν ^ (s / 2)), ← Real.rpow_mul (hw ν).le,
      show s / 2 * ((2 : ℕ) : ℝ) = s by push_cast; ring]
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt S (fun ν => w ν ^ (-s / 2))
    (fun ν => w ν ^ (s / 2) * ‖x ν‖)
  simp only [h1, h2] at hCS
  calc ∑ ν ∈ S, ‖x ν‖ = ∑ ν ∈ S, w ν ^ (-s / 2) * (w ν ^ (s / 2) * ‖x ν‖) :=
        Finset.sum_congr rfl fun ν _ => hsplit ν
    _ ≤ Real.sqrt (∑ ν ∈ S, w ν ^ (-s)) * Real.sqrt (∑ ν ∈ S, w ν ^ s * ‖x ν‖ ^ 2) := hCS
    _ ≤ Real.sqrt Z * Real.sqrt (∑ ν ∈ S, w ν ^ s * ‖x ν‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hZ) (Real.sqrt_nonneg _)

/-- **Result 6a (weighted Cauchy–Schwarz).** For `s > 3/2` and finite `S`,
`Σ_{S} ‖x ν‖ ≤ √(1 + 26 (1 + 1/(2s-3))) √(Σ_{S} (1 + |ν|²)^s ‖x ν‖²)`. -/
theorem sum_norm_le_weighted {s : ℝ} (hs : 3 / 2 < s) (S : Finset L3) (x : L3 → ℂ) :
    ∑ ν ∈ S, ‖x ν‖ ≤ Real.sqrt (1 + 26 * (1 + 1 / (2 * s - 3))) *
      Real.sqrt (∑ ν ∈ S, (1 + lsq ν) ^ s * ‖x ν‖ ^ 2) :=
  sum_norm_le_of_weight S x (fun ν => 1 + lsq ν) (fun ν => by linarith [lsq_nonneg ν]) s _
    (sum_weight_le hs S)

/-- **Result 6b (weighted Cauchy–Schwarz, shifted weight).** The same with the weight centred
at `-c`: `Σ_{S} ‖x ν‖ ≤ √Z √(Σ_{S} (1 + |ν + c|²)^s ‖x ν‖²)`. -/
theorem sum_norm_le_weighted_shift {s : ℝ} (hs : 3 / 2 < s) (S : Finset L3) (x : L3 → ℂ)
    (c : L3) :
    ∑ ν ∈ S, ‖x ν‖ ≤ Real.sqrt (1 + 26 * (1 + 1 / (2 * s - 3))) *
      Real.sqrt (∑ ν ∈ S, (1 + lsq (ν + c)) ^ s * ‖x ν‖ ^ 2) :=
  sum_norm_le_of_weight S x (fun ν => 1 + lsq (ν + c))
    (fun ν => by linarith [lsq_nonneg (ν + c)]) s _ (sum_weight_shift_le hs S c)

/-- `|c - ν|² = |ν + (-c)|²`. -/
lemma lsq_sub_eq_lsq_add_neg (c ν : L3) : lsq (c - ν) = lsq (ν + -c) := by
  simp only [lsq, Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Int.cast_sub, Int.cast_add,
    Int.cast_neg]
  ring

/-- Weighted Cauchy–Schwarz with the weight centred at `c` in the form used on fibres
(input momentum `c - ν`): `Σ_{S} ‖x ν‖ ≤ √Z √(Σ_{S} (1 + |c - ν|²)^s ‖x ν‖²)`. -/
theorem sum_norm_le_weighted_sub {s : ℝ} (hs : 3 / 2 < s) (S : Finset L3) (x : L3 → ℂ)
    (c : L3) :
    ∑ ν ∈ S, ‖x ν‖ ≤ Real.sqrt (1 + 26 * (1 + 1 / (2 * s - 3))) *
      Real.sqrt (∑ ν ∈ S, (1 + lsq (c - ν)) ^ s * ‖x ν‖ ^ 2) := by
  simp only [lsq_sub_eq_lsq_add_neg c]
  exact sum_norm_le_weighted_shift hs S x (-c)

/-! ## Euclidean shells -/

/-- **Result 7.** The Euclidean shell `lam < |ν| ≤ 2 lam` has at most `125 lam³` points
(`lam ≥ 1`). -/
theorem card_euclid_shell_le {lam : ℝ} (hlam : 1 ≤ lam) :
    ((box ⌈2 * lam⌉₊).filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2)).card ≤
      125 * lam ^ 3 := by
  have hsub : (box ⌈2 * lam⌉₊).filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2) ⊆
      box ⌊2 * lam⌋₊ := by
    intro ν hν
    rw [Finset.mem_filter] at hν
    exact mem_box_floor_of_lsq_le (by linarith) hν.2.2
  have hcard := Finset.card_le_card hsub
  rw [card_box] at hcard
  have hcast : (((box ⌈2 * lam⌉₊).filter
      (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2)).card : ℝ) ≤
      (2 * (⌊2 * lam⌋₊ : ℝ) + 1) ^ 3 := by
    exact_mod_cast hcard
  have hfl : (⌊2 * lam⌋₊ : ℝ) ≤ 2 * lam := Nat.floor_le (by linarith)
  calc _ ≤ (2 * (⌊2 * lam⌋₊ : ℝ) + 1) ^ 3 := hcast
    _ ≤ (5 * lam) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    _ = 125 * lam ^ 3 := by ring

end FSLattice
