import PlaneWave.Source.PowerPolylog

/-!
# Flux/source build, block 5: the cutoff dependence of the basic constants

`PL` bounds (`f(n) = O(n^p polylog n)`) for the constants of blocks 1–5, as functions of the
cutoff `n` (`K = g n`):

| constant | order | constant | order |
|---|---|---|---|
| `A_σ` | `n^{-1}` | `a₀`, `a₁` | `n^{-5/2}`, `n^{-3/2}` |
| `C_V`, `C_X`, `C_{VN}` | `n` | `C_Z`, `C_Δ`, `C_mix` | `1` |
| `A_max`, `E₀`, `e_H` | `n²` | `z_b` | `n^{-2} log n` |
| `C_Zws(s)` | `n^{-3/2}` | `c_s` (`cSt`) | `n^{-5/2}` |
| `C_res`, `J_n`, `N_Λ`, `D_K` | `log n` | `C_fl`, `C_fl(σ)`, `C_tavg` at `C_Δ(n)` | `1` |
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSAsymp

open FSNormal

namespace PL

/-- `n^m` for a natural exponent. -/
theorem npow_nat (m : ℕ) : PL (fun n => (n : ℝ) ^ m) m :=
  (npow (m : ℝ)).congr ⟨0, fun n _ => by rw [Real.rpow_natCast]⟩

/-- A linear scale. -/
theorem lin (c : ℝ) : PL (fun n => c * (n : ℝ)) 1 :=
  (cnpow c 1).congr ⟨0, fun n _ => by rw [Real.rpow_one]⟩

/-- Real powers of a nonnegative linear scale. -/
theorem lin_rpow {c : ℝ} (hc : 0 ≤ c) (r : ℝ) : PL (fun n => (c * (n : ℝ)) ^ r) r :=
  (cnpow (c ^ r) r).congr ⟨0, fun n _ => by rw [Real.mul_rpow hc (Nat.cast_nonneg n)]⟩

/-- Logarithms of polynomially bounded quantities `1 ≤ x(n) ≤ c n^m`. -/
theorem log_of_le {x : ℕ → ℝ} {c : ℝ} (m : ℕ)
    (h : ∃ N : ℕ, ∀ n, N ≤ n → 1 ≤ x n ∧ x n ≤ c * (n : ℝ) ^ m) :
    PL (fun n => Real.log (x n)) 0 := by
  obtain ⟨N, h⟩ := h
  refine ⟨|Real.log c| + m, 1, by positivity, zero_le_one, max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨h1, h2⟩ := h n hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnm : (0 : ℝ) < (n : ℝ) ^ m := by positivity
  have hc : 0 < c := by
    by_contra hc
    push Not at hc
    have : c * (n : ℝ) ^ m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hnm.le
    linarith
  have hlog0 : 0 ≤ Real.log (x n) := Real.log_nonneg h1
  have hlog1 : Real.log (x n) ≤ Real.log c + m * Real.log n := by
    calc Real.log (x n) ≤ Real.log (c * (n : ℝ) ^ m) := Real.log_le_log (by linarith) h2
      _ = Real.log c + m * Real.log n := by
          rw [Real.log_mul hc.ne' hnm.ne', Real.log_pow]
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  rw [abs_of_nonneg hlog0, Real.rpow_zero, mul_one, Real.rpow_one]
  unfold ell
  have := le_abs_self (Real.log c)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith [abs_nonneg (Real.log c), mul_nonneg hm hln, mul_nonneg (abs_nonneg (Real.log c)) hln]

/-- `⌊log₂ ⌈x(n)⌉⌋` for polynomially bounded `1 ≤ x(n) ≤ c n^m`. -/
theorem natlog_of_le {x : ℕ → ℝ} {c : ℝ} (m : ℕ)
    (h : ∃ N : ℕ, ∀ n, N ≤ n → 1 ≤ x n ∧ x n ≤ c * (n : ℝ) ^ m) :
    PL (fun n => (Nat.log 2 ⌈x n⌉₊ : ℝ)) 0 := by
  have hl : PL (fun n => Real.log (⌈x n⌉₊ : ℝ)) 0 := by
    refine log_of_le (c := 2 * c) m ?_
    obtain ⟨N, h⟩ := h
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := h n hn
    have hc1 : (⌈x n⌉₊ : ℝ) < x n + 1 := Nat.ceil_lt_add_one (by linarith)
    have hc2 : x n ≤ (⌈x n⌉₊ : ℝ) := Nat.le_ceil _
    constructor
    · linarith
    · nlinarith
  obtain ⟨N, h'⟩ := h
  refine (hl.const_mul (1 / Real.log 2)).of_le ⟨N, fun n hn => ?_⟩
  have hx1 := (h' n hn).1
  have hm : ⌈x n⌉₊ ≠ 0 := by
    have : (1 : ℝ) ≤ ⌈x n⌉₊ := hx1.trans (Nat.le_ceil _)
    intro h0; rw [h0] at this; norm_num at this
  have hp := Nat.pow_log_le_self 2 hm
  have hp' : ((2 : ℝ) ^ Nat.log 2 ⌈x n⌉₊) ≤ (⌈x n⌉₊ : ℝ) := by exact_mod_cast hp
  have hlg := Real.log_le_log (by positivity) hp'
  rw [Real.log_pow] at hlg
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : (0 : ℝ) ≤ (Nat.log 2 ⌈x n⌉₊ : ℝ) := Nat.cast_nonneg _
  rw [abs_of_nonneg h0]
  refine le_trans ?_ (le_abs_self _)
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hl2]
  exact hlg

/-- `log(a + b n)` for `a ≥ 1`, `b ≥ 0`. -/
theorem log_lin {a b : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) :
    PL (fun n => Real.log (a + b * (n : ℝ))) 0 :=
  log_of_le (c := a + b) 1 ⟨1, fun n hn => by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    constructor
    · nlinarith
    · rw [pow_one]; nlinarith⟩

end PL

open PL

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (Hunit : ℝ)

/-! ## The bulk generator -/

theorem pl_Asig : PL (fun n => Asig sys L n) (-1) :=
  (cnpow (A0 sys L) (-1)).congr ⟨1, fun n hn => by
    rw [Asig_eq sys (by omega), Real.rpow_neg_one, div_eq_mul_inv]⟩

theorem pl_M0 : PL (fun n => M0 sys L n) (-5) :=
  (cnpow (cM0 sys L) (-5)).congr ⟨1, fun n hn => by
    rw [M0_eq sys (by omega), Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv,
      show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]⟩

theorem pl_M1 : PL (fun n => M1 sys L n) (-3) :=
  (cnpow (cM1 sys L) (-3)).congr ⟨1, fun n hn => by
    rw [M1_eq sys (by omega), Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]⟩

theorem pl_a0c : PL (fun n => a0c sys L n) (-5 / 2) := by
  have h := ((((pl_M0 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul_const 53).sqrt).mul_const
    (cE sys L)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

theorem pl_a1c : PL (fun n => a1c sys L n) (-3 / 2) := by
  have h := ((((pl_M1 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul_const 53).sqrt).mul_const
    (cE sys L)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

/-- `1 + c n²` is `O(n²)`. -/
theorem pl_one_add_sq (c : ℝ) : PL (fun n => 1 + c * (n : ℝ) ^ 2) 2 := by
  have h := (const 1).add' ((npow_nat 2).const_mul c)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

theorem pl_CV : PL (fun n => CV sys L Hunit n) 1 := by
  have h1 : PL (fun n => 1 + eta * gF L ^ 2 / 16 * (n : ℝ) ^ 2) 2 := pl_one_add_sq _
  have h := (h1.sqrt.const_mul (finiteCoulombPhysicalMassConstant sys L Hunit)).const_mul 2
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold CV; ring_nf

theorem pl_Cop : PL (fun n => Cop sys L n) 0 := by
  have hc : PL (fun n => (2 * (⌈(n : ℝ) / 4⌉₊ : ℝ) + 1)) 1 := by
    refine (lin 4).of_le' ⟨1, fun n hn => ?_⟩
    have h1 : (⌈(n : ℝ) / 4⌉₊ : ℝ) < (n : ℝ) / 4 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg (by positivity)]
    linarith
  have h := ((pl_M1 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul (hc.pow 3)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold Cop; ring

theorem pl_CZ : PL (fun n => CZ sys L Hunit n) 0 := by
  have h1 : PL (fun n => 1 + eta * gF L ^ 2 / 16 * (n : ℝ) ^ 2) 2 := pl_one_add_sq _
  have h2 := (h1.mul ((pl_Asig sys (L := L)).pow 2)).const_mul 2
  have h3 := ((pl_Cop sys (L := L)).const_mul 2).add' h2
  have h := (h3.sqrt).const_mul (finiteCoulombPhysicalMassConstant sys L Hunit)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold CZ; ring_nf

theorem pl_CX : PL (fun n => CX sys L Hunit n) 1 := by
  have h := (pl_CV sys Hunit (L := L)).add' ((pl_CZ sys Hunit (L := L)).const_mul 2)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

theorem pl_CDelta : PL (fun n => CDelta sys L Hunit n) 0 := by
  have hA := pl_Asig sys (L := L)
  have hZ := pl_CZ sys Hunit (L := L)
  have hX := pl_CX sys Hunit (L := L)
  have h := ((hZ.const_mul 2).add' (hA.mul hX)).add' (((hA.pow 2).mul hX).const_mul 4)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold CDelta; ring

theorem pl_CHmix : PL (fun n => CHmix sys L Hunit n) 0 := by
  have h := ((pl_CZ sys Hunit (L := L)).const_mul 2).add'
    (((pl_Asig sys (L := L)).const_mul 2).mul (pl_CV sys Hunit (L := L)))
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold CHmix; ring

/-! ## Energies and scales -/

theorem pl_Amax : PL (fun n => Amax eta L n) 2 := by
  have h := (npow_nat 2).const_mul (3 * eta * gF L ^ 2 / 2)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold Amax; ring

theorem pl_CVN : PL (fun n => CVN sys L Hunit n) 1 := by
  have h1 := (const 1).add' (pl_Amax (eta := eta) (L := L))
  have h2 := (h1.rpow ⟨0, fun n _ => by have := Amax_nonneg eta L n; positivity⟩
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).const_mul (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit)
  refine (h2.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

omit [Fintype ν] in
theorem pl_E0 : PL (fun n => E0 sys L n) 2 := by
  have h := (npow_nat 2).const_mul (gL L ^ 2 / (4096 * mmax sys))
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold E0 Kc; ring

omit [Fintype ν] in
theorem pl_eH : PL (fun n => eH sys L n) 2 := by
  have h := (npow_nat 2).const_mul (gF L ^ 2 / (64 * mtop sys))
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold eH; ring

omit [Fintype ν] in
include hL in
theorem pl_inv_eH : PL (fun n => 1 / eH sys L n) (-2) := by
  have hg := gF_pos hL
  have hm := one_le_mtop sys
  refine (cnpow (64 * mtop sys / gF L ^ 2) (-2)).congr ⟨1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_neg hn0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold eH
  field_simp

omit [Fintype ν] in
include hL in
/-- `(1 + e_H)^{-1/4} ≤ e_H^{-1/4}`. -/
theorem pl_eHq : PL (fun n => (1 + eH sys L n) ^ (-(1 / 4 : ℝ))) (-1 / 2) := by
  have hg := gF_pos hL
  have hm := one_le_mtop sys
  set c := gF L ^ 2 / (64 * mtop sys)
  have hc : 0 < c := by positivity
  refine (cnpow (c ^ (-(1 / 4 : ℝ))) (-1 / 2)).of_le ⟨1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : eH sys L n = c * (n : ℝ) ^ 2 := by unfold eH; simp only [c]; ring
  have hpos : 0 < c * (n : ℝ) ^ 2 := by positivity
  rw [abs_of_nonneg (Real.rpow_nonneg (by rw [heq]; positivity) _),
    abs_of_nonneg (by positivity)]
  calc (1 + eH sys L n) ^ (-(1 / 4 : ℝ)) ≤ (c * (n : ℝ) ^ 2) ^ (-(1 / 4 : ℝ)) := by
        rw [heq]
        exact Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by norm_num)
    _ = c ^ (-(1 / 4 : ℝ)) * (n : ℝ) ^ (-1 / 2 : ℝ) := by
        rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        norm_num

omit [Fintype ν] in
include hL in
/-- `(K/4)^r` is `n^r` up to a constant. -/
theorem pl_Kc4 (r : ℝ) : PL (fun n => (Kc L n / 4) ^ r) r := by
  have h := lin_rpow (show (0 : ℝ) ≤ gL L / 4 by have := gL_pos hL; positivity) r
  exact h.congr ⟨0, fun n _ => by unfold Kc; ring_nf⟩

omit [Fintype ν] in
include hL in
theorem pl_Kc (r : ℝ) : PL (fun n => Kc L n ^ r) r := by
  have h := lin_rpow (show (0 : ℝ) ≤ gL L by have := gL_pos hL; positivity) r
  exact h.congr ⟨0, fun n _ => by unfold Kc; ring_nf⟩

end FSAsymp
