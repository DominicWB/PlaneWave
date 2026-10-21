import PlaneWave.Source.GoodStates

/-!
# Flux/source build, block 1b: eq:tavg-quarter with explicit `K`-dependence

The spectral bound `tavg_hot` (`dev/PlaneWave.Source.TimeAveragedHotContent.lean`) applied to the truncated datum
`u₀ = A_{p₀}^E v` of a good state `v` (`dev/PlaneWave.Source.GoodStates.lean`), with the manuscript's scales:
`λ = K/4`, `E₀ = K²/(4096 m_max)`, the quasi-eigenstate range `X = 3E₀ = 3E₁/4`, and the window
width `Δ = D_K/t`, `D_K = √(6 log(2+K))`, so that the Gaussian tail is `(2+K)^{-3}`.

`tavg_quarter_explicit` (eq:tavg-quarter): for `1 ≤ t` and `K` above the thresholds collected in
`TavgScale` (`K ≥ 1`, `Λ ≥ 1`, `D_K ≤ E₀`, and `λ = K/4` beyond twice every register threshold of
`lem:qtail` at energy `3E₀`),

  `(1/t) ∫₀ᵗ ‖(1-Q) e^{iH'τ} A_{p₀}^E v‖² dτ ≤ C_tavg (Cg Ξ)² K^{2s-6} (1 + D_K)^{2s}`,

for `3/2 < s ≤ 2`; with `s = 3/2 + 2ε` this is `C (Cg Ξ)² K^{-3+4ε} (1 + D_K)^{3+4ε}`.  The power of
`D_K ~ log^{1/2}` differs from the manuscript's single `log(2+K)` (see `dev/PlaneWave.Source.SpectralLayer.lean`: the
window bound carries `(1+Δ)^s`); `thm:src3` absorbs every power of `log K`.
`TavgScale` holds for all large `K` (`tavgScale_of_large`).
-/

set_option autoImplicit false

open scoped InnerProductSpace Real
open PlaneWaveCertificate MeasureTheory

namespace FSGalerkin

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type*}

/-- `D_K = √(6 log(2+K))`. -/
noncomputable def DK (K : ℝ) : ℝ := Real.sqrt (6 * Real.log (2 + K))

lemma DK_nonneg (K : ℝ) : 0 ≤ DK K := Real.sqrt_nonneg _

lemma DK_sq {K : ℝ} (hK : 0 ≤ K) : DK K ^ 2 = 6 * Real.log (2 + K) := by
  unfold DK
  rw [Real.sq_sqrt]
  have : 0 ≤ Real.log (2 + K) := Real.log_nonneg (by linarith)
  positivity

section Explicit

variable [Fintype ν] (sys : CoulombSystem eta ν) (L : ℝ) (Hunit : ℝ)

/-- `P_A = Σ_a (4 c₂(a) (1 + C_Δ) + 2 c(a)²)²`. -/
noncomputable def PA (s CΔ : ℝ) : ℝ :=
  ∑ a, (4 * qtailC2 sys L a s * (1 + CΔ) + 2 * qtailC sys L a ^ 2) ^ 2

/-- `P_B = Σ_a c₂(a)² κ_a^s (2(1 + C_low + C_V²/2))^s`. -/
noncomputable def PB (s CΔ : ℝ) : ℝ :=
  ∑ a, qtailC2 sys L a s ^ 2 * latConst sys L a ^ s *
    (2 * (1 + Clow sys L Hunit CΔ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ s

/-- The scale conditions of eq:tavg-quarter at the cutoff `K = Kc L n`. -/
structure TavgScale (CΔ : ℝ) (n : ℕ) : Prop where
  one_le_K : 1 ≤ Kc L n
  one_le_Lam : 1 ≤ Lam sys L n
  DK_le : DK (Kc L n) ≤ E0 sys L n
  qtail : ∀ a, 2 * qtailL1 sys L Hunit a (3 * E0 sys L n) < Kc L n / 4

/-- The constant of eq:tavg-quarter. -/
noncomputable def Ctavg (CΔ s : ℝ) : ℝ :=
  2 * Real.exp 1 * (Real.sqrt π * (512 * PA sys L s CΔ +
      32768 * PB sys L Hunit s CΔ *
        (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ s * momentConst eta (s / 2 + 1) +
      CVret sys L Hunit CΔ ^ 2 * (4096 * mmax sys) ^ 2 * momentConst eta (1 / 2 + 1)) +
    Real.sqrt (2 * π))

variable {L}

lemma regA_quarter {s CΔ γ K : ℝ} (hK : 0 < K) (a : Fin eta) :
    regA sys L a s CΔ γ (K / 4) =
      16 * (4 * qtailC2 sys L a s * (γ + CΔ) + 2 * qtailC sys L a ^ 2) / K ^ 2 := by
  unfold regA
  field_simp
  ring

lemma hotA_quarter_le (hL : 0 < L) {s CΔ γ D K : ℝ} (hCΔ : 0 ≤ CΔ) (hγ : 0 ≤ γ) (hγD : γ ≤ D)
    (hK : 0 < K) :
    hotA sys L s CΔ γ (K / 4) ≤ 512 / K ^ 4 * PA sys L s CΔ * (1 + D) ^ 2 := by
  unfold hotA PA
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [regA_quarter sys hK a]
  have hc₂ := qtailC2_nonneg sys a hL s
  have hc := qtailC_nonneg sys a hL
  have hD : 0 ≤ D := hγ.trans hγD
  have h1 : 4 * qtailC2 sys L a s * (γ + CΔ) + 2 * qtailC sys L a ^ 2 ≤
      (4 * qtailC2 sys L a s * (1 + CΔ) + 2 * qtailC sys L a ^ 2) * (1 + D) := by
    have : γ + CΔ ≤ (1 + CΔ) * (1 + D) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 4 * qtailC2 sys L a s),
      sq_nonneg (qtailC sys L a)]
  have h0 : 0 ≤ 4 * qtailC2 sys L a s * (γ + CΔ) + 2 * qtailC sys L a ^ 2 := by positivity
  have h2 := pow_le_pow_left₀ h0 h1 2
  calc 2 * (16 * (4 * qtailC2 sys L a s * (γ + CΔ) + 2 * qtailC sys L a ^ 2) / K ^ 2) ^ 2
      = 512 / K ^ 4 * (4 * qtailC2 sys L a s * (γ + CΔ) + 2 * qtailC sys L a ^ 2) ^ 2 := by
        field_simp; ring
    _ ≤ 512 / K ^ 4 * ((4 * qtailC2 sys L a s * (1 + CΔ) + 2 * qtailC sys L a ^ 2) * (1 + D)) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

lemma hotB_quarter_le (_hL : 0 < L) {s CΔ γ D K : ℝ} (hs : 0 ≤ s) (hCΔ : 0 ≤ CΔ) (hγ : 0 ≤ γ)
    (hγD : γ ≤ D) (hK : 0 < K) :
    hotB sys L Hunit s CΔ γ (K / 4) ≤ 32768 / K ^ 5 * PB sys L Hunit s CΔ * (1 + D) ^ s := by
  unfold hotB PB
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  unfold regB
  set c₂ := qtailC2 sys L a s
  set κ := latConst sys L a
  set Y := 1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2
  set Y₀ := 1 + Clow sys L Hunit CΔ + CVret sys L Hunit CΔ ^ 2 / 2
  have hκ : 0 < κ := latConst_pos sys a
  have hC₀ := (Clow_pos sys Hunit hCΔ (L := L)).le
  have hD : 0 ≤ D := hγ.trans hγD
  have hY0 : 0 ≤ Y₀ := by positivity
  have hY : 0 ≤ 2 * Y := by positivity
  have hl : 0 < K / 4 := by positivity
  -- square of the register coefficient
  have hsq : (4 * c₂ * (K / 4) ^ (-(1 / 2 : ℝ)) / (K / 4) ^ 2 * κ ^ (s / 2) * (2 * Y) ^ (s / 2)) ^ 2 =
      16 * c₂ ^ 2 * (1024 / K ^ 5) * κ ^ s * (2 * Y) ^ s := by
    have e1 : ((K / 4) ^ (-(1 / 2 : ℝ))) ^ 2 = (K / 4)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le,
        show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    have e2 : (κ ^ (s / 2)) ^ 2 = κ ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]; norm_num
    have e3 : ((2 * Y) ^ (s / 2)) ^ 2 = (2 * Y) ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY]; norm_num
    rw [mul_pow, mul_pow, div_pow, mul_pow, mul_pow, e1, e2, e3]
    field_simp
    ring
  rw [hsq]
  -- the energy factor
  have hYle : 2 * Y ≤ (2 * Y₀) * (1 + D) := by
    have hYdef : Y = Y₀ + γ := by simp only [Y, Y₀]; ring
    have hY01 : 1 ≤ Y₀ := by
      simp only [Y₀]; have := sq_nonneg (CVret sys L Hunit CΔ); linarith
    have : Y ≤ Y₀ * (1 + D) := by
      rw [hYdef]; nlinarith [mul_le_mul_of_nonneg_right hY01 hD]
    linarith
  have hYs : (2 * Y) ^ s ≤ (2 * Y₀) ^ s * (1 + D) ^ s := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow hY hYle hs
  have hκs : 0 ≤ κ ^ s := Real.rpow_nonneg hκ.le _
  calc 2 * (16 * c₂ ^ 2 * (1024 / K ^ 5) * κ ^ s * (2 * Y) ^ s)
      = 32768 / K ^ 5 * (c₂ ^ 2 * κ ^ s) * (2 * Y) ^ s := by ring
    _ ≤ 32768 / K ^ 5 * (c₂ ^ 2 * κ ^ s) * ((2 * Y₀) ^ s * (1 + D) ^ s) :=
        mul_le_mul_of_nonneg_left hYs (by positivity)
    _ = _ := by ring

/-- `1/K^m ≤ K^e` for `K ≥ 1` and `e ≥ -m`. -/
lemma inv_pow_le_rpow {K : ℝ} (hK : 1 ≤ K) (m : ℕ) {e : ℝ} (he : -(m : ℝ) ≤ e) :
    1 / K ^ m ≤ K ^ e := by
  have hK0 : 0 < K := by linarith
  have h1 : 1 / K ^ m = K ^ (-(m : ℝ)) := by
    rw [Real.rpow_neg hK0.le, Real.rpow_natCast, one_div]
  rw [h1]
  exact Real.rpow_le_rpow_of_exponent_le hK he

/-- The Gaussian tail at `tΔ = D_K` is `(2+K)^{-3} ≤ 1/K³`. -/
lemma gauss_tail_le {K t : ℝ} (hK : 1 ≤ K) (ht : 0 < t) :
    Real.exp (-(t ^ 2 * (DK K / t) ^ 2) / 2) ≤ 1 / K ^ 3 := by
  have hK0 : 0 < K := by linarith
  have h1 : t ^ 2 * (DK K / t) ^ 2 = 6 * Real.log (2 + K) := by
    rw [div_pow, ← DK_sq hK0.le]; field_simp
  rw [h1]
  have h2 : -(6 * Real.log (2 + K)) / 2 = -(((3 : ℕ) : ℝ) * Real.log (2 + K)) := by
    push_cast; ring
  rw [h2, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by linarith), ← one_div]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hK0.le (by linarith) 3)

omit [Fintype ν] in
lemma Lam_le_K {n : ℕ} (hK : 1 ≤ Kc L n) : Lam sys L n ≤ Kc L n := by
  have hm := one_le_mmax sys
  have hK0 : 0 < Kc L n := by linarith
  unfold Lam E0
  rw [Real.sqrt_le_left hK0.le]
  have : 2 * mmax sys * (Kc L n ^ 2 / (4096 * mmax sys)) = Kc L n ^ 2 / 2048 := by
    field_simp; ring
  rw [this]
  nlinarith

lemma momentConst_nonneg (eta : ℕ) {r : ℝ} (hr : 5 / 4 < r) : 0 ≤ momentConst eta r := by
  unfold momentConst
  have h1 : 0 < (1 + (eta : ℝ) / 2) ^ (2 * r) := Real.rpow_pos_of_pos (by positivity) _
  have h2 : 0 < (2 : ℝ) ^ (4 * r - 5) - 1 := by
    have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by linarith : 0 < 4 * r - 5)
    linarith
  have h3 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (4 * r - 5)
  positivity

/-- The real-number bookkeeping of eq:tavg-quarter. -/
lemma tavg_combine {K D s PA PB CG Ms Mh CV mm M : ℝ}
    (hK1 : 1 ≤ K) (hD0 : 0 ≤ D) (hs : 3 / 2 < s)
    (hPA : 0 ≤ PA) (_hPB : 0 ≤ PB) (hCG : 0 ≤ CG) (_hMs : 0 ≤ Ms) (hMh : 0 ≤ Mh) (hM : 0 ≤ M)
    {a b y c g N0 Ns Nh : ℝ}
    (ha : a ≤ 512 / K ^ 4 * PA * (1 + D) ^ 2) (ha0 : 0 ≤ a)
    (hb : b ≤ 32768 / K ^ 5 * PB * (1 + D) ^ s) (hb0 : 0 ≤ b) (hy : y ≤ (1 + D) ^ s) (hy0 : 0 ≤ y)
    (hc : c ≤ CV ^ 2 * (4096 * mm) ^ 2 * (1 / K ^ 4)) (hc0 : 0 ≤ c)
    (hg : g ≤ 1 / K ^ 3) (_hg0 : 0 ≤ g)
    (hN0 : N0 ≤ M) (hN00 : 0 ≤ N0) (hNs : Ns ≤ Ms * M * K ^ (2 * s - 1)) (hNs0 : 0 ≤ Ns)
    (hNh : Nh ≤ Mh * M * K) (hNh0 : 0 ≤ Nh) :
    2 * Real.exp 1 * (Real.sqrt π * (a * N0 + b * y * CG ^ s * Ns + c * Nh) +
        Real.sqrt (2 * π) * g * N0) ≤
      2 * Real.exp 1 * (Real.sqrt π * (512 * PA + 32768 * PB * CG ^ s * Ms +
          CV ^ 2 * (4096 * mm) ^ 2 * Mh) + Real.sqrt (2 * π)) *
        M * K ^ (2 * s - 6) * (1 + D) ^ (2 * s) := by
  have hK0 : 0 < K := by linarith
  have hKs : 0 ≤ K ^ (2 * s - 6) := Real.rpow_nonneg hK0.le _
  have hDs1 : 1 ≤ (1 + D) ^ (2 * s) := Real.one_le_rpow (by linarith) (by linarith)
  have hK4 : 1 / K ^ 4 ≤ K ^ (2 * s - 6) := inv_pow_le_rpow hK1 4 (by push_cast; linarith)
  have hK3 : 1 / K ^ 3 ≤ K ^ (2 * s - 6) := inv_pow_le_rpow hK1 3 (by push_cast; linarith)
  have hK51 : K ^ (2 * s - 1) / K ^ 5 = K ^ (2 * s - 6) := by
    have : K ^ (2 * s - 6) = K ^ (2 * s - 1) / K ^ ((5 : ℕ) : ℝ) := by
      rw [← Real.rpow_sub hK0]; congr 1; push_cast; ring
    rw [this, Real.rpow_natCast]
  have hD2 : (1 + D) ^ 2 ≤ (1 + D) ^ (2 * s) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  have hDss : (1 + D) ^ s * (1 + D) ^ s = (1 + D) ^ (2 * s) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hK3D : 1 / K ^ 3 ≤ K ^ (2 * s - 6) * (1 + D) ^ (2 * s) := by
    calc 1 / K ^ 3 = 1 / K ^ 3 * 1 := by ring
      _ ≤ K ^ (2 * s - 6) * (1 + D) ^ (2 * s) := mul_le_mul hK3 hDs1 zero_le_one hKs
  have hCGs : 0 ≤ CG ^ s := Real.rpow_nonneg hCG _
  have hDs0 : 0 ≤ (1 + D) ^ s := Real.rpow_nonneg (by linarith) _
  have hk : 1 / K ^ 4 * K = 1 / K ^ 3 := by
    rw [pow_succ, one_div_mul_eq_div, div_mul_cancel_right₀ hK0.ne', one_div]
  -- the four terms, each against `Z = M K^{2s-6} (1+D)^{2s}`
  have hT1 : a * N0 ≤ 512 * PA * (M * K ^ (2 * s - 6) * (1 + D) ^ (2 * s)) := by
    have h512 : 0 ≤ 512 * PA * M := mul_nonneg (mul_nonneg (by norm_num) hPA) hM
    calc a * N0 ≤ (512 / K ^ 4 * PA * (1 + D) ^ 2) * M := mul_le_mul ha hN0 hN00 (ha0.trans ha)
      _ = 512 * PA * M * (1 / K ^ 4 * (1 + D) ^ 2) := by ring
      _ ≤ 512 * PA * M * (K ^ (2 * s - 6) * (1 + D) ^ (2 * s)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hK4 hD2 (sq_nonneg _) hKs) h512
      _ = _ := by ring
  have hT2 : b * y * CG ^ s * Ns ≤
      32768 * PB * CG ^ s * Ms * (M * K ^ (2 * s - 6) * (1 + D) ^ (2 * s)) := by
    have hbd : 0 ≤ 32768 / K ^ 5 * PB * (1 + D) ^ s := hb0.trans hb
    calc b * y * CG ^ s * Ns ≤ (32768 / K ^ 5 * PB * (1 + D) ^ s) * (1 + D) ^ s * CG ^ s *
          (Ms * M * K ^ (2 * s - 1)) := by
          have h1 : b * y ≤ (32768 / K ^ 5 * PB * (1 + D) ^ s) * (1 + D) ^ s :=
            mul_le_mul hb hy hy0 hbd
          have h2 : b * y * CG ^ s ≤ (32768 / K ^ 5 * PB * (1 + D) ^ s) * (1 + D) ^ s * CG ^ s :=
            mul_le_mul_of_nonneg_right h1 hCGs
          exact mul_le_mul h2 hNs hNs0 (mul_nonneg (mul_nonneg hbd hDs0) hCGs)
      _ = 32768 * PB * CG ^ s * Ms * (M * (K ^ (2 * s - 1) / K ^ 5) * ((1 + D) ^ s * (1 + D) ^ s)) := by
          ring
      _ = _ := by rw [hK51, hDss]
  have hT3 : c * Nh ≤ CV ^ 2 * (4096 * mm) ^ 2 * Mh * (M * K ^ (2 * s - 6) * (1 + D) ^ (2 * s)) := by
    have h0 : 0 ≤ CV ^ 2 * (4096 * mm) ^ 2 * Mh :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hMh
    calc c * Nh ≤ (CV ^ 2 * (4096 * mm) ^ 2 * (1 / K ^ 4)) * (Mh * M * K) :=
          mul_le_mul hc hNh hNh0 (hc0.trans hc)
      _ = CV ^ 2 * (4096 * mm) ^ 2 * Mh * (M * (1 / K ^ 4 * K)) := by ring
      _ = CV ^ 2 * (4096 * mm) ^ 2 * Mh * (M * (1 / K ^ 3)) := by rw [hk]
      _ ≤ CV ^ 2 * (4096 * mm) ^ 2 * Mh * (M * (K ^ (2 * s - 6) * (1 + D) ^ (2 * s))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK3D hM) h0
      _ = _ := by ring
  have hT4 : g * N0 ≤ M * K ^ (2 * s - 6) * (1 + D) ^ (2 * s) := by
    calc g * N0 ≤ 1 / K ^ 3 * M := mul_le_mul hg hN0 hN00 (by positivity)
      _ ≤ K ^ (2 * s - 6) * (1 + D) ^ (2 * s) * M := mul_le_mul_of_nonneg_right hK3D hM
      _ = _ := by ring
  have hpi := Real.sqrt_nonneg π
  have h2pi := Real.sqrt_nonneg (2 * π)
  have hsum := add_le_add (add_le_add hT1 hT2) hT3
  have h3 := add_le_add (mul_le_mul_of_nonneg_left hsum hpi) (mul_le_mul_of_nonneg_left hT4 h2pi)
  have he : 0 ≤ 2 * Real.exp 1 := by positivity
  have h4 := mul_le_mul_of_nonneg_left h3 he
  calc 2 * Real.exp 1 * (Real.sqrt π * (a * N0 + b * y * CG ^ s * Ns + c * Nh) +
        Real.sqrt (2 * π) * g * N0)
      = 2 * Real.exp 1 * (Real.sqrt π * (a * N0 + b * y * CG ^ s * Ns + c * Nh) +
        Real.sqrt (2 * π) * (g * N0)) := by ring
    _ ≤ _ := h4
    _ = _ := by ring

omit [Fintype ν] in
/-- The datum norms at the scale `K`: `‖u‖² ≤ (Cg Ξ)²`, `‖(1+A)^{s/2} u‖² ≤ M_s (Cg Ξ)² K^{2s-1}`,
`‖(1+A)^{1/2} u‖² ≤ M_h (Cg Ξ)² K`. -/
lemma datum_norms (hL : 0 < L) {n : ℕ} (hK1 : 1 ≤ Kc L n) (hΛ1 : 1 ≤ Lam sys L n) (p₀ : Fin eta)
    {Cg Ξ s : ℝ} (hCgΞ : 0 ≤ Cg * Ξ) (hs : 3 / 2 < s) (v : En eta n) (hv : IsGood sys L Cg Ξ v) :
    ‖datum sys L p₀ v‖ ^ 2 ≤ (Cg * Ξ) ^ 2 ∧
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (s / 2) (datum sys L p₀ v)‖ ^ 2 ≤
      momentConst eta (s / 2 + 1) * (Cg * Ξ) ^ 2 * Kc L n ^ (2 * s - 1) ∧
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) (datum sys L p₀ v)‖ ^ 2 ≤
      momentConst eta (1 / 2 + 1) * (Cg * Ξ) ^ 2 * Kc L n := by
  have hΛK := Lam_le_K sys hK1
  refine ⟨?_, ?_, ?_⟩
  · have hun : ‖datum sys L p₀ v‖ ≤ Cg * Ξ := (norm_datum_le sys L p₀ v).trans
      (by linarith [norm_nonneg v, hv.1])
    exact pow_le_pow_left₀ (norm_nonneg _) hun 2
  · refine (wt_datum_sq_le sys L p₀ hL hCgΞ (r' := s / 2) (by linarith) hΛ1 v hv).trans ?_
    have hMs := momentConst_nonneg eta (r := s / 2 + 1) (by linarith)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [show 4 * (s / 2) - 1 = 2 * s - 1 by ring]
    exact Real.rpow_le_rpow (by linarith) hΛK (by linarith)
  · refine (wt_datum_sq_le sys L p₀ hL hCgΞ (r' := 1 / 2) (by norm_num) hΛ1 v hv).trans ?_
    have hMh := momentConst_nonneg eta (r := 1 / 2 + 1) (by norm_num)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [show 4 * (1 / 2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    exact hΛK

/-- **eq:tavg-quarter with explicit `K`-dependence.** -/
theorem tavg_quarter_explicit (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {n : ℕ} {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {s : ℝ} (hs : 3 / 2 < s) (hs2 : s ≤ 2)
    (hK : TavgScale sys L Hunit CΔ n) (p₀ : Fin eta) {Cg Ξ t : ℝ} (hCgΞ : 0 ≤ Cg * Ξ)
    (ht : 1 ≤ t) (v : En eta n) (hv : IsGood sys L Cg Ξ v) :
    (1 / t) * ∫ τ in (0 : ℝ)..t,
        ‖hotProj L (Kc L n / 4) (retFlow sys L n hΔsym τ (datum sys L p₀ v))‖ ^ 2 ≤
      Ctavg sys L Hunit CΔ s * (Cg * Ξ) ^ 2 * Kc L n ^ (2 * s - 6) * (1 + DK (Kc L n)) ^ (2 * s) := by
  have hK1 : 1 ≤ Kc L n := hK.one_le_K
  have hK0 : 0 < Kc L n := by linarith
  have ht0 : 0 < t := by linarith
  have hD0 : 0 ≤ DK (Kc L n) := DK_nonneg _
  have hΔ0 : 0 ≤ DK (Kc L n) / t := div_nonneg hD0 ht0.le
  have hΔD : DK (Kc L n) / t ≤ DK (Kc L n) := div_le_self hD0 ht
  have hm := one_le_mmax sys
  have hE₀pos : 0 < E0 sys L n := by unfold E0; positivity
  have hDE : DK (Kc L n) ≤ E0 sys L n := hK.DK_le
  have hC₀ := (Clow_pos sys Hunit hCΔ (L := L)).le
  have hCV := CVret_nonneg sys Hunit hCΔ (L := L)
  have hmain := tavg_hot sys Hunit hL hPeriodic hΔsym hCΔ hΔb (t := t) (Δ := DK (Kc L n) / t)
    (X := 3 * E0 sys L n) (s := s) (l := Kc L n / 4) (E₀ := E0 sys L n) ht0 hΔ0 hs hs2
    (by linarith) (by linarith) hK.qtail (datum sys L p₀ v)
    (fun k hk => datum_support sys L p₀ v k hk)
  refine hmain.trans ?_
  obtain ⟨hN0, hNs, hNh⟩ := datum_norms sys hL hK1 hK.one_le_Lam p₀ hCgΞ hs v hv
  have hCG0 : 0 ≤ CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2 := by linarith
  have hCGs : ((CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ (s / 2)) ^ 2 =
      (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hCG0]; norm_num
  rw [hCGs]
  have hX : E0 sys L n ≤ 3 * E0 sys L n - DK (Kc L n) / t - E0 sys L n := by linarith
  have hc : (CVret sys L Hunit CΔ / (3 * E0 sys L n - DK (Kc L n) / t - E0 sys L n)) ^ 2 ≤
      CVret sys L Hunit CΔ ^ 2 * (4096 * mmax sys) ^ 2 * (1 / Kc L n ^ 4) := by
    have h1 : CVret sys L Hunit CΔ / (3 * E0 sys L n - DK (Kc L n) / t - E0 sys L n) ≤
        CVret sys L Hunit CΔ / E0 sys L n := div_le_div_of_nonneg_left hCV hE₀pos hX
    have h2 : (CVret sys L Hunit CΔ / E0 sys L n) ^ 2 =
        CVret sys L Hunit CΔ ^ 2 * (4096 * mmax sys) ^ 2 * (1 / Kc L n ^ 4) := by
      unfold E0; field_simp
    rw [← h2]
    exact pow_le_pow_left₀ (div_nonneg hCV (by linarith)) h1 2
  have hcomb := tavg_combine (K := Kc L n) (D := DK (Kc L n)) (s := s) (PA := PA sys L s CΔ)
    (PB := PB sys L Hunit s CΔ) (CG := CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2)
    (Ms := momentConst eta (s / 2 + 1)) (Mh := momentConst eta (1 / 2 + 1))
    (CV := CVret sys L Hunit CΔ) (mm := mmax sys) (M := (Cg * Ξ) ^ 2)
    (a := hotA sys L s CΔ (DK (Kc L n) / t) (Kc L n / 4))
    (b := hotB sys L Hunit s CΔ (DK (Kc L n) / t) (Kc L n / 4))
    (y := (1 + DK (Kc L n) / t) ^ s)
    (c := (CVret sys L Hunit CΔ / (3 * E0 sys L n - DK (Kc L n) / t - E0 sys L n)) ^ 2)
    (g := Real.exp (-(t ^ 2 * (DK (Kc L n) / t) ^ 2) / 2))
    (N0 := ‖datum sys L p₀ v‖ ^ 2)
    (Ns := ‖FSSpectral.wt (sb eta n) (Asym sys L n) (s / 2) (datum sys L p₀ v)‖ ^ 2)
    (Nh := ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) (datum sys L p₀ v)‖ ^ 2)
    hK1 hD0 hs (Finset.sum_nonneg fun a _ => sq_nonneg _)
    (Finset.sum_nonneg fun a _ => by
      have := latConst_pos sys a (L := L)
      have : 0 ≤ 2 * (1 + Clow sys L Hunit CΔ + CVret sys L Hunit CΔ ^ 2 / 2) := by positivity
      positivity)
    hCG0 (momentConst_nonneg eta (by linarith)) (momentConst_nonneg eta (by norm_num))
    (sq_nonneg _)
    (hotA_quarter_le sys hL hCΔ hΔ0 hΔD hK0) (Finset.sum_nonneg fun a _ => by positivity)
    (hotB_quarter_le sys Hunit hL (by linarith) hCΔ hΔ0 hΔD hK0)
    (Finset.sum_nonneg fun a _ => by positivity)
    (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
    (Real.rpow_nonneg (by linarith) _) hc (sq_nonneg _) (gauss_tail_le hK1 ht0) (Real.exp_nonneg _)
    hN0 (sq_nonneg _) hNs (sq_nonneg _) hNh (sq_nonneg _)
  refine hcomb.trans (le_of_eq ?_)
  unfold Ctavg
  ring

/-! ## The scale conditions hold for large `K` -/

/-- The threshold `K₀ = 46 + 12 (4096 m_max)² + 8g + Σ_a (64 c(a) + 64 √(m_a C_sh(a))) + 1`. -/
noncomputable def Kthr (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  46 + 12 * (4096 * mmax sys) ^ 2 + 8 * gL L +
    ∑ a, (64 * qtailC sys L a + 64 * Real.sqrt (sys.mass a * Csh sys L Hunit a)) + 1

lemma Csh_nonneg (a : Fin eta) : 0 ≤ Csh sys L Hunit a := by
  unfold Csh
  have := sys.mass_pos a
  positivity

/-- **The scale conditions of eq:tavg-quarter hold for `K ≥ K₀`.** -/
theorem tavgScale_of_large (hL : 0 < L) (CΔ : ℝ) {n : ℕ} (hK : Kthr sys L Hunit ≤ Kc L n) :
    TavgScale sys L Hunit CΔ n := by
  have hm := one_le_mmax sys
  have hg := gL_pos hL
  have hterm : ∀ a, 0 ≤ 64 * qtailC sys L a + 64 * Real.sqrt (sys.mass a * Csh sys L Hunit a) :=
    fun a => add_nonneg (mul_nonneg (by norm_num) (qtailC_nonneg sys a hL))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hsum0 : 0 ≤ ∑ a, (64 * qtailC sys L a + 64 * Real.sqrt (sys.mass a * Csh sys L Hunit a)) :=
    Finset.sum_nonneg fun a _ => hterm a
  have hmm0 : 0 ≤ 12 * (4096 * mmax sys) ^ 2 := by positivity
  set K := Kc L n with hKdef
  have hK46 : 46 ≤ K := by unfold Kthr at hK; linarith
  have hK0 : 0 < K := by linarith
  have hE₀ : E0 sys L n = K ^ 2 / (4096 * mmax sys) := rfl
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · -- `Λ ≥ 1`
    unfold Lam
    rw [Real.le_sqrt (by norm_num) (by rw [hE₀]; positivity), hE₀]
    have : 2 * mmax sys * (K ^ 2 / (4096 * mmax sys)) = K ^ 2 / 2048 := by field_simp; ring
    rw [this, le_div_iff₀ (by norm_num)]
    nlinarith
  · -- `D_K ≤ E₀`
    have hlog : Real.log (2 + K) ≤ 1 + K := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 2 + K)
      linarith
    have hKbig : 12 * (4096 * mmax sys) ^ 2 ≤ K := by unfold Kthr at hK; linarith
    have hE0 : 0 ≤ E0 sys L n := by rw [hE₀]; positivity
    unfold DK
    rw [Real.sqrt_le_left hE0]
    calc 6 * Real.log (2 + K) ≤ 12 * K := by linarith
      _ ≤ E0 sys L n ^ 2 := by
        rw [hE₀, div_pow]
        rw [le_div_iff₀ (by positivity)]
        have hK3 : K ≤ K ^ 3 := by nlinarith
        have : 12 * (4096 * mmax sys) ^ 2 * K ≤ K * K := mul_le_mul_of_nonneg_right hKbig hK0.le
        nlinarith
  · -- the register thresholds
    intro a
    have hma := mass_le_mmax sys a
    have hmpos := sys.mass_pos a
    have hCs := Csh_nonneg sys Hunit a (L := L)
    have hsingle : 64 * qtailC sys L a + 64 * Real.sqrt (sys.mass a * Csh sys L Hunit a) ≤
        ∑ b, (64 * qtailC sys L b + 64 * Real.sqrt (sys.mass b * Csh sys L Hunit b)) :=
      Finset.single_le_sum (f := fun b => 64 * qtailC sys L b +
        64 * Real.sqrt (sys.mass b * Csh sys L Hunit b)) (fun b _ => hterm b) (Finset.mem_univ a)
    have hKa : 64 * qtailC sys L a + 64 * Real.sqrt (sys.mass a * Csh sys L Hunit a) + 8 * gL L + 1 ≤ K := by
      unfold Kthr at hK; linarith
    have hq0 := qtailC_nonneg sys a hL
    have hs0 := Real.sqrt_nonneg (sys.mass a * Csh sys L Hunit a)
    unfold qtailL1
    rw [mul_comm, ← lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    refine max_lt (max_lt (by linarith) (by linarith)) ?_
    rw [Real.sqrt_lt' (by linarith)]
    -- `16 m_a (C_sh + 3E₀) < (K/8)²`
    have h1 : 16 * sys.mass a * (3 * E0 sys L n) ≤ 3 * K ^ 2 / 256 := by
      rw [hE₀]
      rw [show 16 * sys.mass a * (3 * (K ^ 2 / (4096 * mmax sys))) =
        (sys.mass a / mmax sys) * (3 * K ^ 2 / 256) by field_simp; ring]
      have : sys.mass a / mmax sys ≤ 1 := (div_le_one (by linarith)).mpr hma
      have h3 : 0 ≤ 3 * K ^ 2 / 256 := by positivity
      nlinarith
    have h2 : 16 * sys.mass a * Csh sys L Hunit a < K ^ 2 / 256 := by
      have hsq := Real.sq_sqrt (mul_nonneg hmpos.le hCs)
      have hKs : 64 * Real.sqrt (sys.mass a * Csh sys L Hunit a) < K := by linarith
      have := pow_lt_pow_left₀ hKs (by positivity) two_ne_zero
      nlinarith
    rw [← hKdef]
    have h3 : (K / 4 / 2) ^ 2 = 4 * K ^ 2 / 256 := by ring
    rw [h3]
    linarith

end Explicit

end FSGalerkin
