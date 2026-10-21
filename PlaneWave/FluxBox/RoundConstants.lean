import PlaneWave.FluxBox.DataScaling

/-!
# Flux route, stage 3, part 51: the cutoff dependence of the round constants

The box is `N(n) = n⁶` (`Nbox`), with the dyadic parameters `ndB` (`g·2N ≤ 2^{ndB}`) and `ndQ`
(`g n/4 ≤ 2^{ndQ}`). All constants of the box ledger are `PL` in `n` (`|f(n)| ≤ C n^p (1 + log n)^k`):
the logarithmic leaves (`pl_lgB`, `pl_LamB`, `pl_LamS2`, `pl_ndB`, `pl_ndQ`, …), the rpow leaves, and the
composite constants up to **`pl_RateBox`** and **`pl_EndBox`** (both `PL (-3)`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory FSAsymp

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The box parameters -/

/-- The box size `N(n) = n⁶`. -/
def Nbox (n : ℕ) : ℕ := n ^ 6

/-- The dyadic parameter of the box: `g·2N ≤ 2^{ndB}`. -/
noncomputable def ndB (L : ℝ) (n : ℕ) : ℕ := Nat.log 2 (⌈gF L⌉₊ * (2 * Nbox n)) + 1

/-- The dyadic parameter of the bulk ball: `g n/4 ≤ 2^{ndQ}`. -/
noncomputable def ndQ (L : ℝ) (n : ℕ) : ℕ := Nat.log 2 (⌈gF L⌉₊ * n) + 1

lemma Nbox_ge (n : ℕ) : n ≤ Nbox n := by
  unfold Nbox
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ 6 := Nat.pow_le_pow_right h (by norm_num)

lemma ndB_spec {L : ℝ} (hL : 0 < L) (n : ℕ) : gF L * (2 * (Nbox n : ℝ)) ≤ 2 ^ ndB L n := by
  have hg := gF_pos hL
  have h1 : gF L ≤ (⌈gF L⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ⌈gF L⌉₊ * (2 * Nbox n) < 2 ^ ndB L n := by
    unfold ndB
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : ((⌈gF L⌉₊ * (2 * Nbox n) : ℕ) : ℝ) < ((2 ^ ndB L n : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  have h4 : gF L * (2 * (Nbox n : ℝ)) ≤ (⌈gF L⌉₊ : ℝ) * (2 * (Nbox n : ℝ)) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith

lemma ndQ_spec {L : ℝ} (hL : 0 < L) (n : ℕ) : gF L * ((n : ℝ) / 4) ≤ 2 ^ ndQ L n := by
  have hg := gF_pos hL
  have h1 : gF L ≤ (⌈gF L⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : ⌈gF L⌉₊ * n < 2 ^ ndQ L n := by
    unfold ndQ
    exact Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : ((⌈gF L⌉₊ * n : ℕ) : ℝ) < ((2 ^ ndQ L n : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : gF L * ((n : ℝ) / 4) ≤ (⌈gF L⌉₊ : ℝ) * n := by
    calc gF L * ((n : ℝ) / 4) ≤ gF L * n := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hn
  linarith

/-! ## The leaves -/

section Leaves

/-- `⌊log₂ m(n)⌋` for polynomially bounded `1 ≤ m(n) ≤ c n^k`. -/
theorem pl_natlog_nat {m : ℕ → ℕ} {c : ℝ} (k : ℕ)
    (h : ∃ N : ℕ, ∀ n, N ≤ n → 1 ≤ m n ∧ (m n : ℝ) ≤ c * (n : ℝ) ^ k) :
    PL (fun n => (Nat.log 2 (m n) : ℝ)) 0 := by
  obtain ⟨N, h⟩ := h
  refine (PL.natlog_of_le (x := fun n => (m n : ℝ)) k ⟨N, fun n hn =>
    ⟨by exact_mod_cast (h n hn).1, (h n hn).2⟩⟩).congr ⟨0, fun n _ => ?_⟩
  simp only [Nat.ceil_natCast]

theorem pl_lgB : PL (fun n => (Nat.log 2 (2 * Nbox n) : ℝ)) 0 :=
  pl_natlog_nat (c := 2) 6 ⟨1, fun n hn => by
    unfold Nbox
    constructor
    · have : 1 ≤ n ^ 6 := Nat.one_le_pow _ _ hn
      omega
    · push_cast; exact le_rfl⟩

theorem pl_lgN : PL (fun n => (Nat.log 2 (Nbox n) : ℝ)) 0 :=
  pl_natlog_nat (c := 1) 6 ⟨1, fun n hn => by
    unfold Nbox
    exact ⟨Nat.one_le_pow _ _ hn, by push_cast; rw [one_mul]⟩⟩

theorem pl_lg8 : PL (fun n => (Nat.log 2 (8 * Nbox n) : ℝ)) 0 :=
  pl_natlog_nat (c := 8) 6 ⟨1, fun n hn => by
    unfold Nbox
    constructor
    · have : 1 ≤ n ^ 6 := Nat.one_le_pow _ _ hn
      omega
    · push_cast; exact le_rfl⟩

theorem pl_lgn : PL (fun n => (Nat.log 2 n : ℝ)) 0 :=
  pl_natlog_nat (c := 1) 1 ⟨1, fun n hn => ⟨hn, by rw [one_mul, pow_one]⟩⟩

theorem pl_ndB {L : ℝ} (hL : 0 < L) : PL (fun n => (ndB L n : ℝ)) 0 := by
  have hg := gF_pos hL
  have hc : 1 ≤ ⌈gF L⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  have h := pl_natlog_nat (m := fun n => ⌈gF L⌉₊ * (2 * Nbox n)) (c := ⌈gF L⌉₊ * 2) 6
    ⟨1, fun n hn => by
      unfold Nbox
      constructor
      · have : 1 ≤ n ^ 6 := Nat.one_le_pow _ _ hn
        have : 1 ≤ 2 * n ^ 6 := by omega
        exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · push_cast; ring_nf; exact le_rfl⟩
  refine (h.add (PL.const 1)).congr ⟨0, fun n _ => ?_⟩
  unfold ndB
  push_cast
  ring

theorem pl_ndQ {L : ℝ} (hL : 0 < L) : PL (fun n => (ndQ L n : ℝ)) 0 := by
  have hg := gF_pos hL
  have hc : 1 ≤ ⌈gF L⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  have h := pl_natlog_nat (m := fun n => ⌈gF L⌉₊ * n) (c := ⌈gF L⌉₊) 1
    ⟨1, fun n hn => by
      constructor
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · push_cast; rw [pow_one]⟩
  refine (h.add (PL.const 1)).congr ⟨0, fun n _ => ?_⟩
  unfold ndQ
  push_cast
  ring

variable (sys : CoulombSystem eta ν)

omit [Fintype ν] in
theorem pl_Jn2 (heta : 0 < eta) : PL (fun n => (Jn sys (2 * Nbox n) : ℝ)) 0 := by
  have he : (1 : ℝ) ≤ eta := by exact_mod_cast heta
  have hm := one_le_mtop sys
  refine PL.natlog_of_le (x := fun n => mtop sys * eta * ((2 * Nbox n : ℕ) : ℝ) ^ 2)
    (c := mtop sys * eta * 4) 12 ⟨1, fun n hn => ?_⟩
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h6 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ h1
  unfold Nbox
  push_cast
  constructor
  · have : (1 : ℝ) ≤ (2 * (n : ℝ) ^ 6) ^ 2 := by nlinarith
    have : (1 : ℝ) ≤ mtop sys * eta := by nlinarith
    nlinarith
  · ring_nf; exact le_rfl

omit [Fintype ν] in
theorem pl_LamB (heta : 0 < eta) : PL (fun n => LamB sys (Nbox n)) 0 := by
  have h1 := ((pl_Jn2 sys heta).const_mul 2).add (PL.const 3)
  have h2 := pl_lg8.add (PL.const 1)
  refine ((h1.mul h2).const_mul 11000).congr ⟨0, fun n _ => ?_⟩ |>.mono (by norm_num)
  unfold LamB
  ring

omit [Fintype ν] in
theorem pl_LamS2 : PL (fun n => LamS (2 * Nbox n)) 0 := by
  refine ((pl_lgB.add (PL.const 2)).const_mul (2 * Real.sqrt 2 * 125)).congr ⟨0, fun n _ => ?_⟩
  unfold LamS
  ring

end Leaves

/-! ## The rpow leaves -/

section Rpow

theorem pl_lin_rpow' {c : ℝ} (hc : 0 ≤ c) (k : ℕ) (r : ℝ) :
    PL (fun n => (c * ((n ^ k : ℕ) : ℝ)) ^ r) (k * r) :=
  (PL.cnpow (c ^ r) (k * r)).congr ⟨0, fun n _ => by
    push_cast
    rw [Real.mul_rpow hc (by positivity), Real.rpow_natCast_mul (Nat.cast_nonneg n)]⟩

theorem pl_inv_pow (c : ℝ) (k : ℕ) : PL (fun n => c / (n : ℝ) ^ k) (-(k : ℝ)) :=
  (PL.cnpow c (-(k : ℝ))).congr ⟨1, fun n hn => by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_neg hn0.le, Real.rpow_natCast, div_eq_mul_inv]⟩

theorem pl_div_pow {f : ℕ → ℝ} {p : ℝ} (hf : PL f p) (k : ℕ) :
    PL (fun n => f n / (n : ℝ) ^ k) (p - k) := by
  refine ((hf.mul (pl_inv_pow 1 k)).congr ⟨0, fun n _ => by ring⟩).mono (le_of_eq (by ring))

/-- `a/(3n/4)³` is `n⁻³`. -/
theorem pl_cube34 (a : ℝ) : PL (fun n => a / (3 * (n : ℝ) / 4) ^ 3) (-3) := by
  refine ((pl_inv_pow (a * (64 / 27)) 3).congr ⟨1, fun n hn => ?_⟩).mono (by norm_num)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp
  ring

end Rpow

end FSFlux
