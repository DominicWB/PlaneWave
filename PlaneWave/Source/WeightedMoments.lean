import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Flux/source build, block 1b: weighted moments of states with register tails

The analytic step of `cor:spectail`.  On a finite configuration set `X`, a state `v` whose
register tails decay like `‖1{k_a > λ} v‖² ≤ T² λ⁻⁵` (`λ ≥ 1`, every register `a`) has, on the
low-energy set `{A ≤ E₀}` where every register momentum is at most `Λ ≥ 1`, the weighted moment

  `Σ_{A ≤ E₀} (1 + A)^{2r} |v|² ≤ C T² Λ^{4r - 5}`  for `r > 5/4`,

with `C = (1 + c_A)^{2r} (1 + 32 η 4^{4r-5}/(2^{4r-5} - 1))`, where `A ≤ c_A R²` whenever all
register momenta are at most `R`.  The proof decomposes by the dyadic size `2^j` of the largest
register momentum: on that shell `(1 + A)^{2r} ≤ (1 + c_A)^{2r} 2^{4rj}`, some register exceeds
`2^{j-1}`, and the tails give `T² 2^{-5(j-1)}` per register; the geometric series with ratio
`2^{4r-5} > 1` is dominated by its last term, `j ≈ log₂ Λ`.

Mathlib only.
-/

set_option autoImplicit false

open Finset

namespace FSDatum

/-- Dyadic shell bound: if `a ≤ c (2^m)²` with `a, c ≥ 0`, then
`(1 + a)^{2r} ≤ (1 + c)^{2r} (4^{2r})^m`. -/
lemma one_add_rpow_le_shell {a c r : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hr : 0 ≤ r) (m : ℕ)
    (h : a ≤ c * ((2 : ℝ) ^ m) ^ 2) :
    (1 + a) ^ (2 * r) ≤ (1 + c) ^ (2 * r) * ((4 : ℝ) ^ (2 * r)) ^ m := by
  have h4 : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h4] at h
  have h1 : (1 : ℝ) ≤ (4 : ℝ) ^ m := one_le_pow₀ (by norm_num)
  have h2 : 1 + a ≤ (1 + c) * (4 : ℝ) ^ m := by nlinarith
  calc (1 + a) ^ (2 * r) ≤ ((1 + c) * (4 : ℝ) ^ m) ^ (2 * r) :=
        Real.rpow_le_rpow (by linarith) h2 (by linarith)
    _ = (1 + c) ^ (2 * r) * ((4 : ℝ) ^ m) ^ (2 * r) :=
        Real.mul_rpow (by linarith) (by positivity)
    _ = (1 + c) ^ (2 * r) * ((4 : ℝ) ^ (2 * r)) ^ m := by
        rw [Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 4)]

/-- Pointwise dyadic decomposition: if every register momentum `κ i` is at most `2^n`, and
`a ≤ c R²` whenever all `κ i ≤ R`, then for `w ≥ 0`
`(1 + a)^{2r} w ≤ (1 + c)^{2r} (w + Σ_{j<n} Σ_i (4^{2r})^{j+1} 1{2^j < κ i} w)`. -/
lemma rpow_mul_le_dyadic {ι : Type*} [Fintype ι] (κ : ι → ℝ) {a c r w : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hw : 0 ≤ w)
    (hAk : ∀ R : ℝ, 0 ≤ R → (∀ i, κ i ≤ R) → a ≤ c * R ^ 2) :
    ∀ n : ℕ, (∀ i, κ i ≤ (2 : ℝ) ^ n) →
      (1 + a) ^ (2 * r) * w ≤ (1 + c) ^ (2 * r) *
        (w + ∑ j ∈ range n, ∑ i, ((4 : ℝ) ^ (2 * r)) ^ (j + 1) *
          (if (2 : ℝ) ^ j < κ i then w else 0)) := by
  have hC : 0 ≤ (1 + c) ^ (2 * r) := Real.rpow_nonneg (by linarith) _
  have hB : 0 ≤ (4 : ℝ) ^ (2 * r) := Real.rpow_nonneg (by norm_num) _
  have hterm : ∀ (j : ℕ) (i : ι),
      0 ≤ ((4 : ℝ) ^ (2 * r)) ^ (j + 1) * (if (2 : ℝ) ^ j < κ i then w else 0) := by
    intro j i
    apply mul_nonneg (pow_nonneg hB _)
    split_ifs <;> linarith
  intro n
  induction n with
  | zero =>
    intro hn
    have h := one_add_rpow_le_shell ha hc hr 0 (hAk ((2 : ℝ) ^ 0) (by positivity) hn)
    simp only [pow_zero, mul_one] at h
    simp only [range_zero, sum_empty, add_zero]
    exact mul_le_mul_of_nonneg_right h hw
  | succ n ih =>
    intro hn
    by_cases hP : ∀ i, κ i ≤ (2 : ℝ) ^ n
    · refine (ih hP).trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl w) ?_) hC)
      rw [sum_range_succ]
      exact le_add_of_nonneg_right (sum_nonneg fun i _ => hterm n i)
    · obtain ⟨i₀, hi₀⟩ := not_forall.mp hP
      replace hi₀ : (2 : ℝ) ^ n < κ i₀ := not_le.mp hi₀
      have h := one_add_rpow_le_shell ha hc hr (n + 1)
        (hAk ((2 : ℝ) ^ (n + 1)) (by positivity) hn)
      have hsingle : ((4 : ℝ) ^ (2 * r)) ^ (n + 1) * w ≤
          ∑ j ∈ range (n + 1), ∑ i, ((4 : ℝ) ^ (2 * r)) ^ (j + 1) *
            (if (2 : ℝ) ^ j < κ i then w else 0) := by
        calc ((4 : ℝ) ^ (2 * r)) ^ (n + 1) * w
            = ((4 : ℝ) ^ (2 * r)) ^ (n + 1) * (if (2 : ℝ) ^ n < κ i₀ then w else 0) := by
              rw [if_pos hi₀]
          _ ≤ ∑ i, ((4 : ℝ) ^ (2 * r)) ^ (n + 1) * (if (2 : ℝ) ^ n < κ i then w else 0) :=
              single_le_sum (fun i _ => hterm n i) (mem_univ i₀)
          _ ≤ _ := single_le_sum (f := fun j => ∑ i, ((4 : ℝ) ^ (2 * r)) ^ (j + 1) *
                (if (2 : ℝ) ^ j < κ i then w else 0))
                (fun j _ => sum_nonneg fun i _ => hterm j i) (self_mem_range_succ n)
      calc (1 + a) ^ (2 * r) * w ≤ (1 + c) ^ (2 * r) * ((4 : ℝ) ^ (2 * r)) ^ (n + 1) * w :=
            mul_le_mul_of_nonneg_right h hw
        _ = (1 + c) ^ (2 * r) * (((4 : ℝ) ^ (2 * r)) ^ (n + 1) * w) := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hC
          linarith

/-- **Weighted moments from register tails** (`cor:spectail`, the dyadic sum). -/
theorem moment_le_of_tails {X : Type*} [Fintype X] {η : ℕ} (A : X → ℝ) (k : Fin η → X → ℝ)
    (v : X → ℂ) {cA E₀ Λ T r : ℝ} (hcA : 0 ≤ cA) (hA0 : ∀ x, 0 ≤ A x) (hΛ : 1 ≤ Λ)
    (hr : 5 / 4 < r) (hT : 0 ≤ T)
    (hAk : ∀ x (R : ℝ), 0 ≤ R → (∀ a, k a x ≤ R) → A x ≤ cA * R ^ 2)
    (hkA : ∀ x, A x ≤ E₀ → ∀ a, k a x ≤ Λ)
    (hv : ∑ x, ‖v x‖ ^ 2 ≤ T ^ 2)
    (htail : ∀ a (l : ℝ), 1 ≤ l → ∑ x, (if l < k a x then ‖v x‖ ^ 2 else 0) ≤ T ^ 2 / l ^ 5) :
    ∑ x, (if A x ≤ E₀ then (1 + A x) ^ (2 * r) * ‖v x‖ ^ 2 else 0) ≤
      (1 + cA) ^ (2 * r) * (1 + 32 * η * (4 : ℝ) ^ (4 * r - 5) / ((2 : ℝ) ^ (4 * r - 5) - 1)) *
        T ^ 2 * Λ ^ (4 * r - 5) := by
  have h45 : 0 < 4 * r - 5 := by linarith
  have hr0 : 0 ≤ r := by linarith
  -- dyadic cutoff `2^(n+1)` with `Λ ≤ 2^(n+1) ≤ 2Λ`
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hΛ (by norm_num : (1 : ℝ) < 2)
  have hJ1 : ∀ x, A x ≤ E₀ → ∀ a, k a x ≤ (2 : ℝ) ^ (n + 1) :=
    fun x hx a => (hkA x hx a).trans hn2.le
  have hJ2 : (2 : ℝ) ^ (n + 1) ≤ 2 * Λ := by rw [pow_succ]; linarith
  -- the ratio `q = 2^(4r-5) > 1`
  obtain ⟨q, hq⟩ : ∃ q : ℝ, (2 : ℝ) ^ (4 * r - 5) = q := ⟨_, rfl⟩
  rw [hq]
  have hq1 : 1 < q := hq ▸ Real.one_lt_rpow (by norm_num) h45
  have hq0 : 0 < q := by linarith
  have hB : (4 : ℝ) ^ (2 * r) = 32 * q := by
    rw [← hq]
    calc (4 : ℝ) ^ (2 * r) = (2 : ℝ) ^ (4 * r) := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
          congr 1; push_cast; ring
      _ = (2 : ℝ) ^ ((4 * r - 5) + 5) := by rw [sub_add_cancel]
      _ = (2 : ℝ) ^ (4 * r - 5) * (2 : ℝ) ^ (5 : ℝ) := Real.rpow_add (by norm_num) _ _
      _ = 32 * (2 : ℝ) ^ (4 * r - 5) := by norm_num; ring
  have hq2 : q ^ 2 = (4 : ℝ) ^ (4 * r - 5) := by
    rw [← hq, Real.rpow_pow_comm (by norm_num)]; norm_num
  have hqJ : q ^ (n + 1) ≤ q * Λ ^ (4 * r - 5) := by
    rw [← hq, Real.rpow_pow_comm (by norm_num), ← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) hJ2 h45.le
  have hL : 1 ≤ Λ ^ (4 * r - 5) := Real.one_le_rpow hΛ h45.le
  -- geometric sum, dominated by its last term
  have hgeom : ∑ j ∈ range (n + 1), q ^ (j + 1) ≤
      (4 : ℝ) ^ (4 * r - 5) * Λ ^ (4 * r - 5) / (q - 1) := by
    rw [le_div_iff₀ (by linarith)]
    have hsum : ∑ j ∈ range (n + 1), q ^ (j + 1) = q * ∑ j ∈ range (n + 1), q ^ j := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => pow_succ' q j
    rw [hsum, mul_assoc, geom_sum_mul, ← hq2]
    nlinarith
  -- constants
  have hC : 0 ≤ (1 + cA) ^ (2 * r) := Real.rpow_nonneg (by linarith) _
  -- pointwise dyadic bound
  have hpt : ∀ x, (if A x ≤ E₀ then (1 + A x) ^ (2 * r) * ‖v x‖ ^ 2 else 0) ≤
      (1 + cA) ^ (2 * r) * (‖v x‖ ^ 2 + ∑ j ∈ range (n + 1), ∑ a,
        ((4 : ℝ) ^ (2 * r)) ^ (j + 1) * (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0)) := by
    intro x
    by_cases hx : A x ≤ E₀
    · rw [if_pos hx]
      exact rpow_mul_le_dyadic (fun a => k a x) (hA0 x) hcA hr0 (by positivity) (hAk x) (n + 1)
        (hJ1 x hx)
    · rw [if_neg hx]
      apply mul_nonneg hC
      apply add_nonneg (by positivity)
      apply sum_nonneg; intro j _; apply sum_nonneg; intro a _
      apply mul_nonneg (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
      split_ifs <;> positivity
  -- per-shell tail bound
  have htl : ∀ j : ℕ, ∑ a : Fin η, ((4 : ℝ) ^ (2 * r)) ^ (j + 1) *
      ∑ x, (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0) ≤
        (η : ℝ) * (32 * T ^ 2 * q ^ (j + 1)) := by
    intro j
    have h1 : ∀ a : Fin η, ((4 : ℝ) ^ (2 * r)) ^ (j + 1) *
        ∑ x, (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0) ≤ 32 * T ^ 2 * q ^ (j + 1) := by
      intro a
      have h32 : ((2 : ℝ) ^ j) ^ 5 = (32 : ℝ) ^ j := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      calc ((4 : ℝ) ^ (2 * r)) ^ (j + 1) * ∑ x, (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0)
          ≤ ((4 : ℝ) ^ (2 * r)) ^ (j + 1) * (T ^ 2 / ((2 : ℝ) ^ j) ^ 5) :=
            mul_le_mul_of_nonneg_left (htail a _ (one_le_pow₀ (by norm_num))) (by positivity)
        _ = 32 * T ^ 2 * q ^ (j + 1) := by
            rw [hB, h32, mul_pow, pow_succ (32 : ℝ)]
            field_simp
    calc _ ≤ ∑ a : Fin η, 32 * T ^ 2 * q ^ (j + 1) := sum_le_sum fun a _ => h1 a
      _ = (η : ℝ) * (32 * T ^ 2 * q ^ (j + 1)) := by simp
  calc ∑ x, (if A x ≤ E₀ then (1 + A x) ^ (2 * r) * ‖v x‖ ^ 2 else 0)
      ≤ ∑ x, (1 + cA) ^ (2 * r) * (‖v x‖ ^ 2 + ∑ j ∈ range (n + 1), ∑ a,
          ((4 : ℝ) ^ (2 * r)) ^ (j + 1) * (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0)) :=
        sum_le_sum fun x _ => hpt x
    _ = (1 + cA) ^ (2 * r) * (∑ x, ‖v x‖ ^ 2 + ∑ j ∈ range (n + 1), ∑ a,
          ((4 : ℝ) ^ (2 * r)) ^ (j + 1) *
            ∑ x, (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0)) := by
      rw [← mul_sum, sum_add_distrib]
      congr 2
      simp_rw [mul_sum]
      exact sum_comm.trans (sum_congr rfl fun j _ => sum_comm)
    _ ≤ (1 + cA) ^ (2 * r) *
          (T ^ 2 + ∑ j ∈ range (n + 1), (η : ℝ) * (32 * T ^ 2 * q ^ (j + 1))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add hv (sum_le_sum fun j _ => htl j)
    _ = (1 + cA) ^ (2 * r) * (T ^ 2 + 32 * η * T ^ 2 * ∑ j ∈ range (n + 1), q ^ (j + 1)) := by
      rw [mul_sum]
      congr 2
      exact sum_congr rfl fun j _ => by ring
    _ ≤ (1 + cA) ^ (2 * r) * (T ^ 2 * Λ ^ (4 * r - 5) + 32 * η * T ^ 2 *
          ((4 : ℝ) ^ (4 * r - 5) * Λ ^ (4 * r - 5) / (q - 1))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add (le_mul_of_one_le_right (pow_nonneg hT 2) hL)
      exact mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

/-- **The borderline moment** (`lem:quarter-flow`).  For weights `w ≥ 0` with
`Σ w ≤ T²` and weighted register tails `Σ_{k_a > λ} w ≤ T²/λ` (`λ ≥ 1`), and every register
momentum at most `2^n` on `{A ≤ E₀}`, the moment `Σ_{A ≤ E₀} (1 + A)^{1/2} w` is at most
`(1 + c_A)^{1/2} T² (1 + 2 η n)`: each dyadic shell contributes `O(T²)`, and there are `n` of
them. -/
theorem moment_quarter_le_of_tails {X : Type*} [Fintype X] {η : ℕ} (A : X → ℝ)
    (k : Fin η → X → ℝ) (w : X → ℝ) {cA E₀ T : ℝ} (n : ℕ) (hcA : 0 ≤ cA) (hA0 : ∀ x, 0 ≤ A x)
    (hw : ∀ x, 0 ≤ w x) (hAk : ∀ x (R : ℝ), 0 ≤ R → (∀ a, k a x ≤ R) → A x ≤ cA * R ^ 2)
    (hkn : ∀ x, A x ≤ E₀ → ∀ a, k a x ≤ (2 : ℝ) ^ n)
    (hw1 : ∑ x, w x ≤ T ^ 2)
    (htail : ∀ a (l : ℝ), 1 ≤ l → ∑ x, (if l < k a x then w x else 0) ≤ T ^ 2 / l) :
    ∑ x, (if A x ≤ E₀ then (1 + A x) ^ (1 / 2 : ℝ) * w x else 0) ≤
      (1 + cA) ^ (1 / 2 : ℝ) * T ^ 2 * (1 + 2 * η * n) := by
  have hC : 0 ≤ (1 + cA) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h12 : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  -- pointwise
  have hpt : ∀ x, (if A x ≤ E₀ then (1 + A x) ^ (1 / 2 : ℝ) * w x else 0) ≤
      (1 + cA) ^ (1 / 2 : ℝ) * (w x + ∑ j ∈ range n, ∑ a,
        (2 : ℝ) ^ (j + 1) * (if (2 : ℝ) ^ j < k a x then w x else 0)) := by
    intro x
    by_cases hx : A x ≤ E₀
    · rw [if_pos hx]
      have h := rpow_mul_le_dyadic (fun a => k a x) (hA0 x) hcA (r := 1 / 4) (by norm_num) (hw x)
        (hAk x) n (hkn x hx)
      rw [h12, h4] at h
      exact h
    · rw [if_neg hx]
      apply mul_nonneg hC
      apply add_nonneg (hw x)
      apply sum_nonneg; intro j _; apply sum_nonneg; intro a _
      apply mul_nonneg (by positivity)
      split_ifs
      · exact hw x
      · exact le_rfl
  -- the shells
  have hshell : ∀ j : ℕ, ∑ a : Fin η, (2 : ℝ) ^ (j + 1) *
      ∑ x, (if (2 : ℝ) ^ j < k a x then w x else 0) ≤ (η : ℝ) * (2 * T ^ 2) := by
    intro j
    have h1 : ∀ a : Fin η, (2 : ℝ) ^ (j + 1) * ∑ x, (if (2 : ℝ) ^ j < k a x then w x else 0) ≤
        2 * T ^ 2 := by
      intro a
      calc (2 : ℝ) ^ (j + 1) * ∑ x, (if (2 : ℝ) ^ j < k a x then w x else 0)
          ≤ (2 : ℝ) ^ (j + 1) * (T ^ 2 / (2 : ℝ) ^ j) :=
            mul_le_mul_of_nonneg_left (htail a _ (one_le_pow₀ (by norm_num))) (by positivity)
        _ = 2 * T ^ 2 := by rw [pow_succ]; field_simp
    calc _ ≤ ∑ a : Fin η, 2 * T ^ 2 := sum_le_sum fun a _ => h1 a
      _ = (η : ℝ) * (2 * T ^ 2) := by simp
  calc ∑ x, (if A x ≤ E₀ then (1 + A x) ^ (1 / 2 : ℝ) * w x else 0)
      ≤ ∑ x, (1 + cA) ^ (1 / 2 : ℝ) * (w x + ∑ j ∈ range n, ∑ a,
          (2 : ℝ) ^ (j + 1) * (if (2 : ℝ) ^ j < k a x then w x else 0)) :=
        sum_le_sum fun x _ => hpt x
    _ = (1 + cA) ^ (1 / 2 : ℝ) * (∑ x, w x + ∑ j ∈ range n, ∑ a,
          (2 : ℝ) ^ (j + 1) * ∑ x, (if (2 : ℝ) ^ j < k a x then w x else 0)) := by
      rw [← mul_sum, sum_add_distrib]
      congr 2
      simp_rw [mul_sum]
      exact sum_comm.trans (sum_congr rfl fun j _ => sum_comm)
    _ ≤ (1 + cA) ^ (1 / 2 : ℝ) * (T ^ 2 + ∑ j ∈ range n, (η : ℝ) * (2 * T ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add hw1 (sum_le_sum fun j _ => hshell j)
    _ = _ := by
      rw [sum_const, card_range, nsmul_eq_mul]
      ring

end FSDatum
