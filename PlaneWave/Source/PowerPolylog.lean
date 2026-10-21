import PlaneWave.Source.Src3Explicit

/-!
# Flux/source build, block 5: power-polylog bounds in the cutoff (Mathlib only)

`PL f p`: `|f(n)| ≤ C n^p (1 + log n)^k` for all large `n`, for some `C, k ≥ 0`.  The class is
closed under sums, products, square roots and nonnegative real powers, contains the constants, the
powers `n^p` and `log n`, and absorbs the logarithms at the end (`PL.final`):
`PL f p → |f(n)| ≤ C_ε n^{p+ε}`.  The `K`-dependence of every constant of the flux/source
argument is recorded in this form.
-/

namespace FSAsymp

open Real

/-- `ℓ(n) = 1 + log n`. -/
noncomputable def ell (n : ℕ) : ℝ := 1 + Real.log n

lemma one_le_ell {n : ℕ} (hn : 1 ≤ n) : 1 ≤ ell n := by
  unfold ell
  have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  linarith

lemma ell_pos {n : ℕ} (hn : 1 ≤ n) : 0 < ell n := lt_of_lt_of_le one_pos (one_le_ell hn)

/-- **Power-polylog bounds**: `|f(n)| ≤ C n^p ℓ(n)^k` for large `n`. -/
def PL (f : ℕ → ℝ) (p : ℝ) : Prop :=
  ∃ C k : ℝ, 0 ≤ C ∧ 0 ≤ k ∧ ∃ N : ℕ, ∀ n, N ≤ n → |f n| ≤ C * (n : ℝ) ^ p * ell n ^ k

namespace PL

variable {f g : ℕ → ℝ} {p q : ℝ}

lemma npow_le {n : ℕ} (hn : 1 ≤ n) (h : p ≤ q) : (n : ℝ) ^ p ≤ (n : ℝ) ^ q :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) h

lemma ellpow_le {n : ℕ} (hn : 1 ≤ n) {k k' : ℝ} (h : k ≤ k') : ell n ^ k ≤ ell n ^ k' :=
  Real.rpow_le_rpow_of_exponent_le (one_le_ell hn) h

lemma npow_nonneg (n : ℕ) (p : ℝ) : 0 ≤ (n : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg n) p

lemma ellpow_nonneg {n : ℕ} (hn : 1 ≤ n) (k : ℝ) : 0 ≤ ell n ^ k :=
  Real.rpow_nonneg (ell_pos hn).le k

theorem mono (hf : PL f p) (hpq : p ≤ q) : PL f q := by
  obtain ⟨C, k, hC, hk, N, h⟩ := hf
  refine ⟨C, k, hC, hk, max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  refine (h n (le_trans (le_max_left _ _) hn)).trans ?_
  have := npow_le hn1 hpq
  have := ellpow_nonneg hn1 k
  gcongr

theorem of_le (hg : PL g p) (h : ∃ N : ℕ, ∀ n, N ≤ n → |f n| ≤ |g n|) : PL f p := by
  obtain ⟨C, k, hC, hk, N, hb⟩ := hg
  obtain ⟨N', h'⟩ := h
  exact ⟨C, k, hC, hk, max N N', fun n hn =>
    (h' n (le_trans (le_max_right _ _) hn)).trans (hb n (le_trans (le_max_left _ _) hn))⟩

theorem of_le' (hg : PL g p) (h : ∃ N : ℕ, ∀ n, N ≤ n → |f n| ≤ g n) : PL f p :=
  hg.of_le (by obtain ⟨N, h'⟩ := h; exact ⟨N, fun n hn => (h' n hn).trans (le_abs_self _)⟩)

theorem congr (hf : PL f p) (h : ∃ N : ℕ, ∀ n, N ≤ n → g n = f n) : PL g p :=
  hf.of_le (by obtain ⟨N, h'⟩ := h; exact ⟨N, fun n hn => by rw [h' n hn]⟩)

theorem add (hf : PL f p) (hg : PL g p) : PL (fun n => f n + g n) p := by
  obtain ⟨C, k, hC, hk, N, h⟩ := hf
  obtain ⟨C', k', hC', hk', N', h'⟩ := hg
  refine ⟨C + C', max k k', by positivity, le_trans hk (le_max_left _ _), max (max N N') 1,
    fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hN' : N' ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have e1 := ellpow_le hn1 (le_max_left k k')
  have e2 := ellpow_le hn1 (le_max_right k k')
  have hp := npow_nonneg n p
  have h1 : |f n| ≤ C * (n : ℝ) ^ p * ell n ^ max k k' :=
    (h n hN).trans (mul_le_mul_of_nonneg_left e1 (by positivity))
  have h2 : |g n| ≤ C' * (n : ℝ) ^ p * ell n ^ max k k' :=
    (h' n hN').trans (mul_le_mul_of_nonneg_left e2 (by positivity))
  calc |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ _ := by nlinarith

theorem add' (hf : PL f p) (hg : PL g q) : PL (fun n => f n + g n) (max p q) :=
  (hf.mono (le_max_left p q)).add (hg.mono (le_max_right p q))

theorem mul (hf : PL f p) (hg : PL g q) : PL (fun n => f n * g n) (p + q) := by
  obtain ⟨C, k, hC, hk, N, h⟩ := hf
  obtain ⟨C', k', hC', hk', N', h'⟩ := hg
  refine ⟨C * C', k + k', by positivity, by positivity, max (max N N') 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hN' : N' ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [abs_mul, Real.rpow_add hn0, Real.rpow_add (ell_pos hn1)]
  have := npow_nonneg n p
  have := npow_nonneg n q
  have := ellpow_nonneg hn1 k
  have := ellpow_nonneg hn1 k'
  calc |f n| * |g n| ≤ (C * (n : ℝ) ^ p * ell n ^ k) * (C' * (n : ℝ) ^ q * ell n ^ k') :=
        mul_le_mul (h n hN) (h' n hN') (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem const (c : ℝ) : PL (fun _ => c) 0 :=
  ⟨|c|, 0, abs_nonneg c, le_rfl, 1, fun n hn => by
    rw [Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]⟩

theorem npow (p : ℝ) : PL (fun n => (n : ℝ) ^ p) p :=
  ⟨1, 0, zero_le_one, le_rfl, 1, fun n hn => by
    rw [abs_of_nonneg (npow_nonneg n p), Real.rpow_zero, one_mul, mul_one]⟩

theorem ell' : PL ell 0 :=
  ⟨1, 1, zero_le_one, zero_le_one, 1, fun n hn => by
    rw [abs_of_pos (ell_pos hn), Real.rpow_zero, Real.rpow_one, one_mul, one_mul]⟩

theorem log : PL (fun n => Real.log n) 0 := by
  refine ell'.of_le ⟨1, fun n hn => ?_⟩
  have h0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [abs_of_nonneg h0, abs_of_pos (ell_pos hn)]
  unfold ell; linarith

theorem const_mul (hf : PL f p) (c : ℝ) : PL (fun n => c * f n) p := by
  have := (const c).mul hf
  simpa using this

theorem mul_const (hf : PL f p) (c : ℝ) : PL (fun n => f n * c) p := by
  have := hf.mul (const c)
  simpa using this

theorem neg (hf : PL f p) : PL (fun n => -f n) p :=
  hf.of_le ⟨0, fun n _ => by rw [abs_neg]⟩

theorem sub (hf : PL f p) (hg : PL g p) : PL (fun n => f n - g n) p := by
  have := hf.add hg.neg
  simpa [sub_eq_add_neg] using this

theorem cnpow (c p : ℝ) : PL (fun n => c * (n : ℝ) ^ p) p := (npow p).const_mul c

theorem sqrt (hf : PL f p) : PL (fun n => Real.sqrt (f n)) (p / 2) := by
  obtain ⟨C, k, hC, hk, N, h⟩ := hf
  refine ⟨C ^ (1 / 2 : ℝ), k / 2, Real.rpow_nonneg hC _, by positivity, max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := npow_nonneg n p
  have := ellpow_nonneg hn1 k
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : Real.sqrt (f n) ≤ (C * (n : ℝ) ^ p * ell n ^ k) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans (h n hN))
  refine h1.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC (by positivity),
    ← Real.rpow_mul hn0, ← Real.rpow_mul (ell_pos hn1).le,
    show p * (1 / 2 : ℝ) = p / 2 by ring, show k * (1 / 2 : ℝ) = k / 2 by ring]

theorem rpow (hf : PL f p) (h0 : ∃ N : ℕ, ∀ n, N ≤ n → 0 ≤ f n) {r : ℝ} (hr : 0 ≤ r) :
    PL (fun n => f n ^ r) (p * r) := by
  obtain ⟨C, k, hC, hk, N, h⟩ := hf
  obtain ⟨N₀, h0'⟩ := h0
  refine ⟨C ^ r, k * r, Real.rpow_nonneg hC r, by positivity, max (max N N₀) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hN₀ : N₀ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hf0 := h0' n hN₀
  rw [abs_of_nonneg (Real.rpow_nonneg hf0 r)]
  have h1 : f n ^ r ≤ (C * (n : ℝ) ^ p * ell n ^ k) ^ r :=
    Real.rpow_le_rpow hf0 ((le_abs_self _).trans (h n hN)) hr
  refine h1.trans (le_of_eq ?_)
  have := npow_nonneg n p
  have := ellpow_nonneg hn1 k
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hC (by positivity),
    ← Real.rpow_mul hn0, ← Real.rpow_mul (ell_pos hn1).le]

theorem pow (hf : PL f p) (m : ℕ) : PL (fun n => f n ^ m) (p * m) := by
  induction m with
  | zero => simpa using const 1
  | succ m ih =>
    have := ih.mul hf
    refine (this.congr ⟨0, fun n _ => by ring⟩).mono (le_of_eq (by push_cast; ring))

theorem zero : PL (fun _ => 0) p := ⟨0, 0, le_rfl, le_rfl, 0, fun n _ => by simp⟩

theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℕ → ℝ} (h : ∀ i ∈ s, PL (F i) p) :
    PL (fun n => ∑ i ∈ s, F i n) p := by
  classical
  induction s using Finset.induction_on with
  | empty => exact zero.congr ⟨0, fun n _ => by simp⟩
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact (h1.add h2).congr ⟨0, fun n _ => Finset.sum_insert ha⟩

/-- **Absorbing the logarithms.** -/
theorem final (hf : PL f p) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n → |f n| ≤ C * (n : ℝ) ^ (p + ε) := by
  obtain ⟨C, k, hC, hk, N, h⟩ := hf
  -- `ℓ(n)^k ≤ (1 + k/ε)^k n^ε`
  set δ := ε / (k + 1)
  have hδ : 0 < δ := by positivity
  refine ⟨C * (1 + 1 / δ) ^ k, by positivity, max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog := Real.log_le_rpow_div hn0.le hδ
  have hnδ : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow hn1' hδ.le
  have hell : ell n ≤ (1 + 1 / δ) * (n : ℝ) ^ δ := by
    unfold ell
    have : (n : ℝ) ^ δ / δ = 1 / δ * (n : ℝ) ^ δ := by ring
    nlinarith
  have hellk : ell n ^ k ≤ (1 + 1 / δ) ^ k * (n : ℝ) ^ (δ * k) := by
    calc ell n ^ k ≤ ((1 + 1 / δ) * (n : ℝ) ^ δ) ^ k :=
          Real.rpow_le_rpow (ell_pos hn1).le hell hk
      _ = (1 + 1 / δ) ^ k * (n : ℝ) ^ (δ * k) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hn0.le]
  have hδk : δ * k ≤ ε := by
    simp only [δ]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hpow : (n : ℝ) ^ (δ * k) ≤ (n : ℝ) ^ ε := npow_le hn1 hδk
  refine (h n hN).trans ?_
  have := npow_nonneg n p
  calc C * (n : ℝ) ^ p * ell n ^ k ≤ C * (n : ℝ) ^ p * ((1 + 1 / δ) ^ k * (n : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left (hellk.trans (mul_le_mul_of_nonneg_left hpow (by positivity)))
          (by positivity)
    _ = C * (1 + 1 / δ) ^ k * ((n : ℝ) ^ p * (n : ℝ) ^ ε) := by ring
    _ = C * (1 + 1 / δ) ^ k * (n : ℝ) ^ (p + ε) := by rw [Real.rpow_add hn0]

end PL

end FSAsymp
