import PlaneWave.SourceBand.SrcRes

/-!
# Source band block, part 7: the band bounds of `lem:qtail` and `prop:tavgU`

On the Galerkin space `E_n` (cube `‖ν_a‖_∞ ≤ n`, `K = g n`), for `H' = H_N + ΔH` and a
quasi-eigenstate `‖(H' - E) q‖ ≤ γ ‖q‖`:

* `bnear_sum_le`, `bfar_sum_le`, `norm_wop_band_le` (namespace `FSChannel`): an output weight
  `|θ| ≤ c_θ` supported on outputs with register momentum in a finite set `S`; hops split at
  `|Δν| = R`. Near hops by a Schur test (rows and columns `26 R c_θ c_w`) on the inputs they reach;
  far hops (`|κ| ≤ c_w/R²`) by fibre Cauchy–Schwarz, `‖far‖² ≤ (c_θ c_w/R²)² Z_s |S| W_s²`
  (the line injection with the target count of the band);
* `bandMask L K ρ a` = `B_{a,ϱ}` (`K - ϱ < g ‖ν_a‖_∞`), `card_bandSet_le` (`≤ 2250 n² (ϱ/g + 1)`),
  `band_le_resolvent` (the denominator on the band, through `tail_le_resolvent`);
* **`qtail_band_raw`**, **`qtail_band`** (eq:qtail, second bound):
  `‖B_{a,ϱ} q‖ ≤ K^{-2} (C_B K^{-1} ϱ^{1/2} W_s(q) + C_A (γ + C_Δ + 1) ‖q‖)` for
  `1 ≤ ϱ ≤ K/4` and `K/2` beyond twice the threshold of the first bound;
* `bandProj` (`B_ϱ`, some register in its band), `norm_sq_bandProj_le` (union bound),
  `bandProj_sq_le_of_quasi`, **`tavg_band`** (spectral form) and **`tavg_band_explicit`**
  (eq:tavgU, band part): `(1/t) ∫₀ᵗ ‖B_ϱ e^{iH'τ} A_{p₀}^E v‖² ≤ C (C_g Ξ)² (ϱ K^{2s-7} (1+D_K)^{2s} + K^{-3})`
  for `1 ≤ t`, `1 ≤ ϱ ≤ K/4`, `3/2 < s ≤ 2`; with `s = 3/2 + 2ε` the exponent is `-4 + 4ε`;
* **`tavg_half_explicit`** (eq:tavgU, first part): the union tail at `K/2` is dominated by the hot
  projector at `K/4`, so eq:tavg-quarter applies.
-/

set_option autoImplicit false

open scoped InnerProductSpace
open PlaneWaveCertificate MeasureTheory

/-! ## The band channel estimate -/

namespace FSChannel

open FSLattice Finset

variable {X : Type*} [Fintype X] (π : X → L3) (κ : X → X → ℂ) {cw : ℝ}

/-- Row sums of the sharp near kernel `θ_q 1[|π q - π p| < R] κ_{qp}`: `≤ 26 R c_θ c_w`. -/
lemma bnear_row_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R : ℝ}
    (hcθ : 0 ≤ cθ) (hR : 0 ≤ R) (hθ : ∀ q, |θ q| ≤ cθ) (q : X) :
    ∑ p, ‖(θ q : ℂ) * (if lsq (π q - π p) < R ^ 2 then κ q p else 0)‖ ≤ 26 * R * cθ * cw := by
  have hpt : ∀ p, ‖(θ q : ℂ) * (if lsq (π q - π p) < R ^ 2 then κ q p else 0)‖ ≤
      cθ * cw * (if lsq (π q - π p) < R ^ 2 ∧ κ q p ≠ 0 then 1 / lsq (π q - π p) else 0) := by
    intro p
    by_cases hc : lsq (π q - π p) < R ^ 2 ∧ κ q p ≠ 0
    · rw [if_pos hc.1, if_pos hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |θ q| * ‖κ q p‖ ≤ cθ * (cw / lsq (π q - π p)) :=
            mul_le_mul (hθ q) (hch.bound q p) (norm_nonneg _) hcθ
        _ = _ := by ring
    · rw [if_neg hc]
      have h0 : (if lsq (π q - π p) < R ^ 2 then κ q p else 0) = 0 := by
        split_ifs with h
        · by_contra hk; exact hc ⟨h, hk⟩
        · rfl
      rw [h0, mul_zero, norm_zero, mul_zero]
  calc ∑ p, ‖(θ q : ℂ) * (if lsq (π q - π p) < R ^ 2 then κ q p else 0)‖
      ≤ ∑ p, cθ * cw *
          (if lsq (π q - π p) < R ^ 2 ∧ κ q p ≠ 0 then 1 / lsq (π q - π p) else 0) :=
        sum_le_sum fun p _ => hpt p
    _ = cθ * cw * ∑ p ∈ univ.filter (fun p => lsq (π q - π p) < R ^ 2 ∧ κ q p ≠ 0),
          1 / lsq (π q - π p) := by rw [sum_filter, mul_sum]
    _ ≤ cθ * cw * (26 * R) := by
        gcongr
        refine sum_inv_lsq_image_le _ (fun p => π q - π p) ?_ hR ?_ ?_
        · intro p hp p' hp' h
          have hp1 := (mem_filter.mp (mem_coe.mp hp)).2
          have hp2 := (mem_filter.mp (mem_coe.mp hp')).2
          exact hch.row q p p' hp1.2 hp2.2 (sub_right_injective h)
        · intro p hp
          exact hch.sub_ne_zero (mem_filter.mp hp).2.2
        · intro p hp
          exact (mem_filter.mp hp).2.1.le
    _ = 26 * R * cθ * cw := by ring

/-- Column sums of the sharp near kernel: `≤ 26 R c_θ c_w`. -/
lemma bnear_col_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R : ℝ}
    (hcθ : 0 ≤ cθ) (hR : 0 ≤ R) (hθ : ∀ q, |θ q| ≤ cθ) (p : X) :
    ∑ q, ‖(θ q : ℂ) * (if lsq (π q - π p) < R ^ 2 then κ q p else 0)‖ ≤ 26 * R * cθ * cw := by
  have hpt : ∀ q, ‖(θ q : ℂ) * (if lsq (π q - π p) < R ^ 2 then κ q p else 0)‖ ≤
      cθ * cw * (if lsq (π q - π p) < R ^ 2 ∧ κ q p ≠ 0 then 1 / lsq (π q - π p) else 0) := by
    intro q
    by_cases hc : lsq (π q - π p) < R ^ 2 ∧ κ q p ≠ 0
    · rw [if_pos hc.1, if_pos hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |θ q| * ‖κ q p‖ ≤ cθ * (cw / lsq (π q - π p)) :=
            mul_le_mul (hθ q) (hch.bound q p) (norm_nonneg _) hcθ
        _ = _ := by ring
    · rw [if_neg hc]
      have h0 : (if lsq (π q - π p) < R ^ 2 then κ q p else 0) = 0 := by
        split_ifs with h
        · by_contra hk; exact hc ⟨h, hk⟩
        · rfl
      rw [h0, mul_zero, norm_zero, mul_zero]
  calc ∑ q, ‖(θ q : ℂ) * (if lsq (π q - π p) < R ^ 2 then κ q p else 0)‖
      ≤ ∑ q, cθ * cw *
          (if lsq (π q - π p) < R ^ 2 ∧ κ q p ≠ 0 then 1 / lsq (π q - π p) else 0) :=
        sum_le_sum fun q _ => hpt q
    _ = cθ * cw * ∑ q ∈ univ.filter (fun q => lsq (π q - π p) < R ^ 2 ∧ κ q p ≠ 0),
          1 / lsq (π q - π p) := by rw [sum_filter, mul_sum]
    _ ≤ cθ * cw * (26 * R) := by
        gcongr
        refine sum_inv_lsq_image_le _ (fun q => π q - π p) ?_ hR ?_ ?_
        · intro q hq q' hq' h
          have hq1 := (mem_filter.mp (mem_coe.mp hq)).2
          have hq2 := (mem_filter.mp (mem_coe.mp hq')).2
          exact hch.col p q q' hq1.2 hq2.2 (sub_left_injective h)
        · intro q hq
          exact hch.sub_ne_zero (mem_filter.mp hq).2.2
        · intro q hq
          exact (mem_filter.mp hq).2.1.le
    _ = 26 * R * cθ * cw := by ring

/-- **Near hops of a band weight.**  The near hops of outputs with `θ_q ≠ 0` reach only inputs
in `T`; Schur gives the factor `26 R c_θ c_w` on `1_T u`. -/
theorem bnear_sum_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R : ℝ}
    (hcθ : 0 ≤ cθ) (hR : 0 ≤ R) (hθ : ∀ q, |θ q| ≤ cθ) (T : X → Prop) [DecidablePred T]
    (hT : ∀ q p, θ q ≠ 0 → lsq (π q - π p) < R ^ 2 → κ q p ≠ 0 → T p) (u : X → ℂ) :
    ∑ q, ‖(θ q : ℂ) * ∑ p, u p * (if lsq (π q - π p) < R ^ 2 then κ q p else 0)‖ ^ 2 ≤
      (26 * R * cθ * cw) ^ 2 * ∑ p, (if T p then ‖u p‖ ^ 2 else 0) := by
  have hS := schur_sum_sq
    (fun q p => (θ q : ℂ) * (if lsq (π q - π p) < R ^ 2 then κ q p else 0))
    (fun p => if T p then u p else 0)
    (R := 26 * R * cθ * cw) (C := 26 * R * cθ * cw) (by positivity) (by positivity)
    (bnear_row_le π κ hch hcw θ hcθ hR hθ) (bnear_col_le π κ hch hcw θ hcθ hR hθ)
  have hLHS : ∀ q,
      (θ q : ℂ) * ∑ p, u p * (if lsq (π q - π p) < R ^ 2 then κ q p else 0) =
        ∑ p, (if T p then u p else 0) *
          ((θ q : ℂ) * (if lsq (π q - π p) < R ^ 2 then κ q p else 0)) := by
    intro q
    rw [mul_sum]
    refine sum_congr rfl fun p _ => ?_
    by_cases hθq : θ q = 0
    · rw [hθq, Complex.ofReal_zero]; ring
    · by_cases hn : lsq (π q - π p) < R ^ 2
      · by_cases hk : κ q p = 0
        · rw [if_pos hn, hk]; ring
        · rw [if_pos hn, if_pos (hT q p hθq hn hk)]; ring
      · rw [if_neg hn]; ring
  have hRHS : ∑ p, ‖(if T p then u p else 0)‖ ^ 2 = ∑ p, (if T p then ‖u p‖ ^ 2 else 0) := by
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  calc ∑ q, ‖(θ q : ℂ) * ∑ p, u p * (if lsq (π q - π p) < R ^ 2 then κ q p else 0)‖ ^ 2
      = ∑ q, ‖∑ p, (if T p then u p else 0) *
          ((θ q : ℂ) * (if lsq (π q - π p) < R ^ 2 then κ q p else 0))‖ ^ 2 :=
        sum_congr rfl fun q _ => by rw [hLHS q]
    _ ≤ 26 * R * cθ * cw * (26 * R * cθ * cw) * ∑ p, ‖(if T p then u p else 0)‖ ^ 2 := hS
    _ = _ := by rw [hRHS]; ring

/-- Far hops of a band weight, one output. -/
lemma bfar_row_sq_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R s : ℝ}
    (hcθ : 0 ≤ cθ) (hR : 0 < R) (hs : 3 / 2 < s) (hθ : ∀ q, |θ q| ≤ cθ) (u : X → ℂ) (q : X) :
    ‖(θ q : ℂ) * ∑ p, u p * (if lsq (π q - π p) < R ^ 2 then 0 else κ q p)‖ ^ 2 ≤
      (cθ * cw / R ^ 2) ^ 2 * Zs s * ∑ p, (if κ q p ≠ 0 ∧ θ q ≠ 0 then
        (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 else 0) := by
  have hZ := Zs_pos hs
  have hw : ∀ p, 0 ≤ (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := fun p =>
    mul_nonneg (Real.rpow_nonneg (by linarith [lsq_nonneg (π p)]) s) (sq_nonneg _)
  by_cases hθq : θ q = 0
  · simp [hθq]
  have h1 : ‖∑ p, u p * (if lsq (π q - π p) < R ^ 2 then 0 else κ q p)‖ ≤
      cw / R ^ 2 * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [sum_filter, mul_sum]
    refine sum_le_sum fun p _ => ?_
    rw [norm_mul]
    by_cases hn : lsq (π q - π p) < R ^ 2
    · rw [if_pos hn, norm_zero, mul_zero]
      split_ifs <;> positivity
    · rw [if_neg hn]
      by_cases hk : κ q p = 0
      · rw [if_neg (not_not.mpr hk), hk, norm_zero, mul_zero, mul_zero]
      · rw [if_pos hk]
        have hD : R ^ 2 ≤ lsq (π q - π p) := not_lt.mp hn
        have hb : ‖κ q p‖ ≤ cw / R ^ 2 :=
          (hch.bound q p).trans (div_le_div_of_nonneg_left hcw (by positivity) hD)
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have hCS : (∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖) ^ 2 ≤
      Zs s * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := by
    calc (∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖) ^ 2
        ≤ (∑ p ∈ univ.filter (fun p => κ q p ≠ 0), (1 + lsq (π p)) ^ (-s)) *
            ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := by
          apply sum_sq_le_sum_mul_sum_of_sq_le_mul
          · intro p _
            exact Real.rpow_nonneg (by linarith [lsq_nonneg (π p)]) _
          · intro p _
            exact hw p
          · intro p _
            have hpos : 0 < 1 + lsq (π p) := by linarith [lsq_nonneg (π p)]
            rw [← mul_assoc, ← Real.rpow_add hpos, neg_add_cancel, Real.rpow_zero, one_mul]
      _ ≤ Zs s * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun p _ => hw p)
          apply sum_weight_image_le _ π _ hs
          intro p hp p' hp' h
          exact hch.row q p p' (mem_filter.mp (mem_coe.mp hp)).2
            (mem_filter.mp (mem_coe.mp hp')).2 h
  have e : ∀ p, (if κ q p ≠ 0 ∧ θ q ≠ 0 then (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 else 0) =
      (if κ q p ≠ 0 then (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 else 0) := fun p => by
    by_cases hk : κ q p ≠ 0
    · rw [if_pos ⟨hk, hθq⟩, if_pos hk]
    · rw [if_neg (fun h => hk h.1), if_neg hk]
  calc ‖(θ q : ℂ) * ∑ p, u p * (if lsq (π q - π p) < R ^ 2 then 0 else κ q p)‖ ^ 2
      ≤ (cθ * (cw / R ^ 2 * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖)) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hθ q) h1 (norm_nonneg _) hcθ
    _ = (cθ * cw / R ^ 2) ^ 2 * (∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖) ^ 2 := by ring
    _ ≤ (cθ * cw / R ^ 2) ^ 2 *
          (Zs s * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = _ := by
        rw [sum_congr rfl fun p _ => e p, ← sum_filter]
        ring

/-- **Far hops of a band weight.**  `|S|` bounds the number of outputs fed by one input. -/
theorem bfar_sum_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R s : ℝ}
    (hcθ : 0 ≤ cθ) (hR : 0 < R) (hs : 3 / 2 < s) (hθ : ∀ q, |θ q| ≤ cθ)
    (S : Finset L3) (hS : ∀ q, θ q ≠ 0 → π q ∈ S) (u : X → ℂ) :
    ∑ q, ‖(θ q : ℂ) * ∑ p, u p * (if lsq (π q - π p) < R ^ 2 then 0 else κ q p)‖ ^ 2 ≤
      (cθ * cw / R ^ 2) ^ 2 * Zs s * S.card * ∑ p, (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := by
  have hZ := Zs_pos hs
  have hw : ∀ p, 0 ≤ (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := fun p =>
    mul_nonneg (Real.rpow_nonneg (by linarith [lsq_nonneg (π p)]) s) (sq_nonneg _)
  calc ∑ q, ‖(θ q : ℂ) * ∑ p, u p * (if lsq (π q - π p) < R ^ 2 then 0 else κ q p)‖ ^ 2
      ≤ ∑ q, (cθ * cw / R ^ 2) ^ 2 * Zs s * ∑ p, (if κ q p ≠ 0 ∧ θ q ≠ 0 then
          (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 else 0) :=
        sum_le_sum fun q _ => bfar_row_sq_le π κ hch hcw θ hcθ hR hs hθ u q
    _ = (cθ * cw / R ^ 2) ^ 2 * Zs s * ∑ p, ∑ q, (if κ q p ≠ 0 ∧ θ q ≠ 0 then
          (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 else 0) := by
        rw [← mul_sum, sum_comm]
    _ ≤ (cθ * cw / R ^ 2) ^ 2 * Zs s * ∑ p, (S.card : ℝ) * ((1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum
        intro p _
        have e : ∑ q, (if κ q p ≠ 0 ∧ θ q ≠ 0 then (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 else 0) =
            ((univ.filter (fun q => κ q p ≠ 0 ∧ θ q ≠ 0)).card : ℝ) *
              ((1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) := by
          rw [← sum_filter, sum_const, nsmul_eq_mul]
        rw [e]
        apply mul_le_mul_of_nonneg_right _ (hw p)
        have hinj : Set.InjOn π (univ.filter (fun q => κ q p ≠ 0 ∧ θ q ≠ 0) : Finset X) := by
          intro q hq q' hq' h
          exact hch.col p q q' (mem_filter.mp (mem_coe.mp hq)).2.1
            (mem_filter.mp (mem_coe.mp hq')).2.1 h
        have hsub : (univ.filter (fun q => κ q p ≠ 0 ∧ θ q ≠ 0)).image π ⊆ S := by
          intro y hy
          obtain ⟨q, hq, rfl⟩ := mem_image.mp hy
          exact hS q (mem_filter.mp hq).2.2
        have h := card_le_card hsub
        rw [card_image_of_injOn hinj] at h
        exact_mod_cast h
    _ = _ := by rw [← mul_sum]; ring

/-- **The band channel bound**: near plus far. -/
theorem norm_wop_band_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R s : ℝ}
    (hcθ : 0 ≤ cθ) (hR : 0 < R) (hs : 3 / 2 < s) (hθ : ∀ q, |θ q| ≤ cθ)
    (T : X → Prop) [DecidablePred T]
    (hT : ∀ q p, θ q ≠ 0 → lsq (π q - π p) < R ^ 2 → κ q p ≠ 0 → T p)
    (S : Finset L3) (hS : ∀ q, θ q ≠ 0 → π q ∈ S) (u : EuclideanSpace ℂ X) :
    ‖wop κ θ u‖ ≤
      26 * R * cθ * cw * Real.sqrt (∑ p, if T p then ‖u.ofLp p‖ ^ 2 else 0) +
        cθ * cw / R ^ 2 * Real.sqrt (Zs s * S.card) *
          Real.sqrt (∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2) := by
  have hZ := Zs_pos hs
  have hsplit : wop κ θ u =
      WithLp.toLp 2 (fun q => (θ q : ℂ) * ∑ p, u.ofLp p *
        (if lsq (π q - π p) < R ^ 2 then κ q p else 0)) +
      WithLp.toLp 2 (fun q => (θ q : ℂ) * ∑ p, u.ofLp p *
        (if lsq (π q - π p) < R ^ 2 then 0 else κ q p)) := by
    rw [← WithLp.toLp_add]
    unfold wop
    congr 1
    funext q
    simp only [Pi.add_apply]
    rw [← mul_add, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  have hnear := bnear_sum_le π κ hch hcw θ hcθ hR.le hθ T hT u.ofLp
  have hfar := bfar_sum_le π κ hch hcw θ hcθ hR hs hθ S hS u.ofLp
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [EuclideanSpace.norm_eq]
    dsimp only
    calc Real.sqrt (∑ q, ‖(θ q : ℂ) * ∑ p, u.ofLp p *
            (if lsq (π q - π p) < R ^ 2 then κ q p else 0)‖ ^ 2)
        ≤ Real.sqrt ((26 * R * cθ * cw) ^ 2 *
            ∑ p, (if T p then ‖u.ofLp p‖ ^ 2 else 0)) := Real.sqrt_le_sqrt hnear
      _ = 26 * R * cθ * cw * Real.sqrt (∑ p, if T p then ‖u.ofLp p‖ ^ 2 else 0) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  · rw [EuclideanSpace.norm_eq]
    dsimp only
    have hS2 : 0 ≤ ∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2 := sum_nonneg fun p _ =>
      mul_nonneg (Real.rpow_nonneg (by linarith [lsq_nonneg (π p)]) s) (sq_nonneg _)
    calc Real.sqrt (∑ q, ‖(θ q : ℂ) * ∑ p, u.ofLp p *
            (if lsq (π q - π p) < R ^ 2 then 0 else κ q p)‖ ^ 2)
        ≤ Real.sqrt ((cθ * cw / R ^ 2) ^ 2 * Zs s * S.card *
            ∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2) := Real.sqrt_le_sqrt hfar
      _ = cθ * cw / R ^ 2 * Real.sqrt (Zs s * S.card) *
            Real.sqrt (∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2) := by
          rw [show (cθ * cw / R ^ 2) ^ 2 * Zs s * S.card *
              ∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2 =
              (cθ * cw / R ^ 2) ^ 2 * ((Zs s * S.card) *
                ∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2) by ring,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity),
            Real.sqrt_mul (by positivity)]
          ring

end FSChannel

open scoped Real

/-! ## The band bound of `lem:qtail` -/

namespace FSGalerkin

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type*}

section BandVa

variable [Fintype ν] (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (a : Fin eta)

/-- `V_a` through its channels: if every channel `(κ, c_w)` of register `a` has
`‖θ ⊙ T_κ u‖ ≤ c_w B`, then `‖θ ⊙ V_a u‖ ≤ Q_a γ_c B`. -/
theorem norm_regMul_Va_le_of (θ : FinitePlaneWaveMode n → ℝ) (hL : 0 < L) (u : En eta n) {B : ℝ}
    (hch : ∀ (κ : Cfg eta n → Cfg eta n → ℂ) (cw : ℝ), IsChannel (piA (n := n) a) κ cw → 0 ≤ cw →
      ‖wop κ (fun q => θ (q a)) u‖ ≤ cw * B) :
    ‖regMul a (fun μ => (θ μ : ℂ)) (Va sys L n a u)‖ ≤
      chargeA sys a * coulombCellAmplitude L * B := by
  classical
  set γc := coulombCellAmplitude L with hγc
  have hγ : 0 ≤ γc := (coulombCellAmplitude_pos hL).le
  have hVa : regMul a (fun μ => (θ μ : ℂ)) (Va sys L n a u) =
      ((-sys.charge a : ℝ) : ℂ) • ∑ ell : ν,
        wop (referenceConfigurationKernel a (finiteElectronNuclearKernel sys.nuclei γc n ell))
          (fun q => θ (q a)) u +
      ∑ pr ∈ pairsWith a, ((sys.charge pr.1.1 * sys.charge pr.1.2 : ℝ) : ℂ) •
        wop (finiteElectronPairConfigurationKernel a (other a pr) (γc ^ 2) n)
          (fun q => θ (q a)) u := by
    unfold Va Vnuc Vpair
    rw [LinearMap.add_apply, map_add, LinearMap.smul_apply, map_smul, LinearMap.sum_apply, map_sum,
      LinearMap.sum_apply, map_sum]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun ell _ => ?_
      exact regMul_kernel n a θ _ _ (fun u q => referenceKernelConvolutionOperator_apply a _ u q) u
    · refine Finset.sum_congr rfl fun pr hpr => ?_
      rw [LinearMap.smul_apply, map_smul]
      congr 1
      rw [← pairKernel_eq_other a pr hpr]
      exact regMul_kernel n a θ _ _ (fun u q => finiteElectronPairCoulombOperator_apply _ _ _ n u q) u
  rw [hVa]
  have hNuc : ‖((-sys.charge a : ℝ) : ℂ) • ∑ ell : ν,
      wop (referenceConfigurationKernel a (finiteElectronNuclearKernel sys.nuclei γc n ell))
        (fun q => θ (q a)) u‖ ≤ |sys.charge a| * (sys.nuclei.totalCharge * γc * B) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ ∑ ell : ν, ‖wop (referenceConfigurationKernel a
            (finiteElectronNuclearKernel sys.nuclei γc n ell)) (fun q => θ (q a)) u‖ :=
          norm_sum_le _ _
      _ ≤ ∑ ell : ν, sys.nuclei.charge ell * γc * B := Finset.sum_le_sum fun ell _ =>
          hch _ _ (isChannel_nuc a sys.nuclei hγ ell) (mul_nonneg (sys.nuclei.charge_nonneg ell) hγ)
      _ = sys.nuclei.totalCharge * γc * B := by
          unfold FiniteBONuclearData.totalCharge
          rw [Finset.sum_mul, Finset.sum_mul]
  have hPair : ‖∑ pr ∈ pairsWith a, ((sys.charge pr.1.1 * sys.charge pr.1.2 : ℝ) : ℂ) •
      wop (finiteElectronPairConfigurationKernel a (other a pr) (γc ^ 2) n)
        (fun q => θ (q a)) u‖ ≤
      (∑ pr ∈ pairsWith a, |sys.charge pr.1.1 * sys.charge pr.1.2|) * (γc * B) := by
    calc _ ≤ ∑ pr ∈ pairsWith a, ‖((sys.charge pr.1.1 * sys.charge pr.1.2 : ℝ) : ℂ) •
            wop (finiteElectronPairConfigurationKernel a (other a pr) (γc ^ 2) n)
              (fun q => θ (q a)) u‖ := norm_sum_le _ _
      _ ≤ ∑ pr ∈ pairsWith a, |sys.charge pr.1.1 * sys.charge pr.1.2| * (γc * B) := by
          refine Finset.sum_le_sum fun pr hpr => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left
            (hch _ _ (isChannel_pair a (ne_other a pr hpr) hγ) hγ) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ |sys.charge a| * (sys.nuclei.totalCharge * γc * B) +
        (∑ pr ∈ pairsWith a, |sys.charge pr.1.1 * sys.charge pr.1.2|) * (γc * B) :=
        add_le_add hNuc hPair
    _ = chargeA sys a * γc * B := by unfold chargeA; ring

end BandVa

section BandMask

variable {n : ℕ}

/-- The cube band of register `a`: `K - ϱ < g ‖ν_a‖_∞` (on `E_n`, `g ‖ν_a‖_∞ ≤ K = g n`). -/
abbrev InBand (L K ρ : ℝ) (μ : FinitePlaneWaveMode n) : Prop :=
  K - ρ < gL L * FSBand.supn (finitePlaneWaveLatticeIndex n μ)

/-- The band mask `B_{a,ϱ}`. -/
noncomputable def bandMask (L K ρ : ℝ) (a : Fin eta) : En eta n →ₗ[ℂ] En eta n :=
  regMul a (fun μ => if InBand L K ρ μ then 1 else 0)

lemma bandMask_apply (L K ρ : ℝ) (a : Fin eta) (u : En eta n) (p : Cfg eta n) :
    (bandMask L K ρ a u).ofLp p = if InBand L K ρ (p a) then u.ofLp p else 0 := by
  unfold bandMask
  rw [regMul_apply]
  split_ifs <;> simp

lemma norm_sq_bandMask (L K ρ : ℝ) (a : Fin eta) (u : En eta n) :
    ‖bandMask L K ρ a u‖ ^ 2 = ∑ p, if InBand L K ρ (p a) then ‖u.ofLp p‖ ^ 2 else 0 := by
  rw [norm_sq_En]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [bandMask_apply]
  split_ifs <;> simp

lemma norm_bandMask_le (L K ρ : ℝ) (a : Fin eta) (u : En eta n) : ‖bandMask L K ρ a u‖ ≤ ‖u‖ := by
  have h := norm_regMul_le a (fun μ => if InBand L K ρ μ then (1 : ℂ) else 0) zero_le_one
    (fun μ => by split_ifs <;> simp) u
  rw [one_mul] at h
  exact h

/-- On `E_n` every register has `‖ν_a‖_∞ ≤ n`. -/
lemma supn_index_le (μ : FinitePlaneWaveMode n) :
    FSBand.supn (finitePlaneWaveLatticeIndex n μ) ≤ n := by
  have h : ∀ i, |((finitePlaneWaveLatticeIndex n μ i : ℤ) : ℝ)| ≤ n := fun i => by
    obtain ⟨h1, h2⟩ := finitePlaneWaveLatticeIndex_coord_bounds n μ i
    rw [abs_le]
    constructor
    · have : (-(n : ℝ)) ≤ ((finitePlaneWaveLatticeIndex n μ i : ℤ) : ℝ) := by exact_mod_cast h1
      exact this
    · exact_mod_cast h2
  unfold FSBand.supn
  exact max_le (h 0) (max_le (h 1) (h 2))

/-- `g ‖ν‖_∞ ≤ |k|`. -/
lemma g_supn_le_kabs {L : ℝ} (hL : 0 < L) (μ : FinitePlaneWaveMode n) :
    gL L * FSBand.supn (finitePlaneWaveLatticeIndex n μ) ≤
      finitePlaneWaveKabs (2 * Real.pi / L) n μ := by
  have hg := gL_pos hL
  have hk := kabs_sq_eq L μ
  have hk0 := kabs_nonneg hL μ
  have hs0 := FSBand.supn_nonneg (finitePlaneWaveLatticeIndex n μ)
  have hsq := FSBand.supn_sq_le_lsq (finitePlaneWaveLatticeIndex n μ)
  have h2 : (gL L * FSBand.supn (finitePlaneWaveLatticeIndex n μ)) ^ 2 ≤
      finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 := by
    rw [hk, mul_pow]
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (by positivity) hk0 two_ne_zero).mp h2

/-- The band modes as lattice points. -/
noncomputable def bandSet (L K ρ : ℝ) (n : ℕ) : Finset L3 :=
  ((Finset.univ : Finset (FinitePlaneWaveMode n)).filter (fun μ => InBand L K ρ μ)).image
    (finitePlaneWaveLatticeIndex n)

/-- **The band count**: `|B| ≤ 2250 n² (ϱ/g + 1)` for `0 ≤ ϱ ≤ K/4`, `n ≥ 2`. -/
lemma card_bandSet_le {L : ℝ} (hL : 0 < L) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρK : ρ ≤ Kc L n / 4)
    (hn : 2 ≤ n) :
    ((bandSet L (Kc L n) ρ n).card : ℝ) ≤ 2250 * (n : ℝ) ^ 2 * (ρ / gL L + 1) := by
  have hg := gL_pos hL
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hρg : ρ / gL L ≤ n / 4 := by
    rw [div_le_iff₀ hg]
    have : Kc L n = gL L * n := rfl
    rw [this] at hρK
    linarith
  have hρg0 : 0 ≤ ρ / gL L := div_nonneg hρ0 hg.le
  have hΛ1 : 1 ≤ (n : ℝ) - ρ / gL L := by linarith
  have hRΛ : ρ / gL L + 1 ≤ (n : ℝ) - ρ / gL L := by linarith
  have h := FSBand.shC_count hΛ1 (by positivity : (0 : ℝ) ≤ ρ / gL L + 1) hRΛ
    (bandSet L (Kc L n) ρ n) (fun y hy => by
      obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hy
      have hb : Kc L n - ρ < gL L * FSBand.supn (finitePlaneWaveLatticeIndex n μ) :=
        (Finset.mem_filter.mp hμ).2
      have hs := supn_index_le μ
      have hK : Kc L n = gL L * n := rfl
      constructor
      · have e : (n : ℝ) - ρ / gL L = (gL L * n - ρ) / gL L := by field_simp
        rw [e, div_le_iff₀ hg]
        rw [hK] at hb
        linarith
      · linarith)
  have hR1 : max (ρ / gL L + 1) 1 = ρ / gL L + 1 := max_eq_left (by linarith)
  rw [hR1] at h
  have hΛn : ((n : ℝ) - ρ / gL L) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  calc _ ≤ 2250 * ((n : ℝ) - ρ / gL L) ^ 2 * (ρ / gL L + 1) := h
    _ ≤ 2250 * (n : ℝ) ^ 2 * (ρ / gL L + 1) := by gcongr

end BandMask

section BandBound

variable [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) {n : ℕ} (a : Fin eta)

/-- The output weight on the band: `θ(μ) = 1_B(μ)/w(μ)`. -/
noncomputable def bandW (sys : CoulombSystem eta ν) (L Hunit : ℝ) (a : Fin eta) (E l K ρ : ℝ)
    (μ : FinitePlaneWaveMode n) : ℝ :=
  if InBand L K ρ μ then outW n sys L Hunit a E l μ else 0

/-- **The denominator on the band**: `‖B_{a,ϱ} q‖ ≤ ‖θ (H_ā - E) q‖` when the band lies beyond
`l`. -/
theorem band_le_resolvent (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {E l K ρ : ℝ} (hl : 0 < l) (hl2 : 16 * sys.mass a * (Csh sys L Hunit a + E) < l ^ 2)
    (hband : ∀ μ : FinitePlaneWaveMode n, InBand L K ρ μ →
      l < finitePlaneWaveKabs (2 * Real.pi / L) n μ) (q : En eta n) :
    ‖bandMask L K ρ a q‖ ≤
      ‖regMul a (fun μ => (bandW sys L Hunit a E l K ρ μ : ℂ)) (Hbar sys L n a q - (E : ℂ) • q)‖ := by
  have h := tail_le_resolvent sys Hunit a hL hPeriodic hl hl2 (bandMask L K ρ a q)
  have e1 : regTail L a l (bandMask L K ρ a q) = bandMask L K ρ a q := by
    ext p
    rw [regTail_apply, bandMask_apply]
    by_cases h2 : InBand L K ρ (p a)
    · rw [if_pos h2, if_pos (hband _ h2)]
    · rw [if_neg h2]
      split_ifs <;> rfl
  have e2 : Hbar sys L n a (bandMask L K ρ a q) - (E : ℂ) • bandMask L K ρ a q =
      bandMask L K ρ a (Hbar sys L n a q - (E : ℂ) • q) := by
    rw [map_sub, map_smul]
    unfold bandMask
    rw [Hbar_regLocal sys L n a]
  rw [e1, e2] at h
  refine h.trans (le_of_eq ?_)
  unfold bandMask
  rw [regMul_regMul]
  have hfun : (fun μ => ((outW n sys L Hunit a E l μ : ℝ) : ℂ) *
      (if InBand L K ρ μ then (1 : ℂ) else 0)) =
      (fun μ => ((bandW sys L Hunit a E l K ρ μ : ℝ) : ℂ)) := by
    funext μ
    unfold bandW
    split_ifs <;> simp
  rw [hfun]

/-- **eq:qtail, second bound, explicit form.**  For `0 ≤ ϱ ≤ K/4` and `K/2` beyond twice the
threshold of the first bound: the remainder and `ΔH` with the band denominator `(3K/4)²/(16 m_a)`,
the near hops (`|Δν| < n/4`, inputs beyond `K/2`) and the far hops (band count). -/
theorem qtail_band_raw (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} {CΔ : ℝ} (_hCΔ : 0 ≤ CΔ) (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {E γr s : ℝ} (_hγr : 0 ≤ γr) (hs : 3 / 2 < s) (q : En eta n)
    (hq : ‖Hret sys L n ΔH q - (E : ℂ) • q‖ ≤ γr * ‖q‖)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρK : ρ ≤ Kc L n / 4)
    (hK : 2 * qtailL1 sys L Hunit a E < Kc L n / 2) :
    ‖bandMask L (Kc L n) ρ a q‖ ≤
      16 * sys.mass a / (3 * Kc L n / 4) ^ 2 * ((γr + CΔ) * ‖q‖) +
      chargeA sys a * coulombCellAmplitude L *
        (26 * ((n : ℝ) / 4) * (16 * sys.mass a / (3 * Kc L n / 4) ^ 2) *
            ‖regTail L a (Kc L n / 2) q‖ +
          16 * sys.mass a / (3 * Kc L n / 4) ^ 2 / ((n : ℝ) / 4) ^ 2 *
            Real.sqrt (Zs s * (2250 * (n : ℝ) ^ 2 * (ρ / gL L + 1))) * Wlat a s q) := by
  classical
  have hg := gL_pos hL
  have hm := sys.mass_pos a
  have hKg : Kc L n = gL L * n := rfl
  have hlg : gL L ≤ qtailL1 sys L Hunit a E := (le_max_right _ _).trans (le_max_left _ _)
  have hlsq : Real.sqrt (16 * sys.mass a * (Csh sys L Hunit a + E)) ≤ qtailL1 sys L Hunit a E :=
    le_max_right _ _
  have hK4 : gL L * 4 < gL L * n := by rw [← hKg]; linarith
  have hn4 : (4 : ℝ) < n := lt_of_mul_lt_mul_left hK4 hg.le
  have hn2 : 2 ≤ n := by
    have : (2 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hKpos : 0 < Kc L n := by rw [hKg]; positivity
  have hl : 0 < 3 * Kc L n / 4 := by positivity
  have hl2 : 16 * sys.mass a * (Csh sys L Hunit a + E) < (3 * Kc L n / 4) ^ 2 := by
    by_cases h0 : 16 * sys.mass a * (Csh sys L Hunit a + E) < 0
    · nlinarith
    · push Not at h0
      have h1 : Real.sqrt (16 * sys.mass a * (Csh sys L Hunit a + E)) < 3 * Kc L n / 4 := by
        linarith
      exact (Real.sqrt_lt' hl).mp h1
  -- the band lies beyond `3K/4`
  have hband : ∀ μ : FinitePlaneWaveMode n, InBand L (Kc L n) ρ μ →
      3 * Kc L n / 4 < finitePlaneWaveKabs (2 * Real.pi / L) n μ := by
    intro μ hμ
    have h1 := g_supn_le_kabs hL μ
    have h2 : Kc L n - ρ < gL L * FSBand.supn (finitePlaneWaveLatticeIndex n μ) := hμ
    linarith
  -- the denominator
  have hres := band_le_resolvent sys Hunit a hL hPeriodic hl hl2 hband q
  have hDq : Hbar sys L n a q - (E : ℂ) • q =
      (Hret sys L n ΔH q - (E : ℂ) • q) - ΔH q - Va sys L n a q := by
    rw [Hbar, LinearMap.sub_apply, Hret, LinearMap.add_apply]
    abel
  rw [hDq, map_sub, map_sub] at hres
  have hcθ0 : 0 ≤ 16 * sys.mass a / (3 * Kc L n / 4) ^ 2 := by positivity
  have hθb : ∀ μ : FinitePlaneWaveMode n, |bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ μ| ≤
      16 * sys.mass a / (3 * Kc L n / 4) ^ 2 := fun μ => by
    unfold bandW
    split_ifs
    · exact outW_le sys Hunit a hL hl hl2 μ
    · rw [abs_zero]; exact hcθ0
  have hθb' : ∀ μ : FinitePlaneWaveMode n,
      ‖((bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ μ : ℝ) : ℂ)‖ ≤
      16 * sys.mass a / (3 * Kc L n / 4) ^ 2 := fun μ => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hθb μ
  have hr := (norm_regMul_le a _ hcθ0 hθb' (Hret sys L n ΔH q - (E : ℂ) • q)).trans
    (mul_le_mul_of_nonneg_left hq hcθ0)
  have hΔ := (norm_regMul_le a _ hcθ0 hθb' (ΔH q)).trans
    (mul_le_mul_of_nonneg_left (hΔb q) hcθ0)
  -- the channel part
  have hS : ∀ q' : Cfg eta n, bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ (q' a) ≠ 0 →
      piA a q' ∈ bandSet L (Kc L n) ρ n := by
    intro q' hq'
    unfold bandW at hq'
    split_ifs at hq' with hb
    · exact Finset.mem_image.mpr ⟨q' a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩
    · exact absurd rfl hq'
  have hT : ∀ q' p : Cfg eta n, bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ (q' a) ≠ 0 →
      lsq (piA a q' - piA a p) < ((n : ℝ) / 4) ^ 2 →
      Kc L n / 2 < finitePlaneWaveKabs (2 * Real.pi / L) n (p a) := by
    intro q' p hq' hnear
    have hb : InBand L (Kc L n) ρ (q' a) := by
      unfold bandW at hq'
      split_ifs at hq' with hb
      · exact hb
      · exact absurd rfl hq'
    have h1 : Kc L n - ρ < gL L * FSBand.supn (piA a q') := hb
    have hd : FSBand.supn (piA a q' - piA a p) < (n : ℝ) / 4 := by
      have h0 := FSBand.supn_le_rho (piA a q' - piA a p)
      have h2 : rho (piA a q' - piA a p) < (n : ℝ) / 4 := by
        unfold rho
        rw [Real.sqrt_lt' (by positivity)]
        exact hnear
      linarith
    have htri : FSBand.supn (piA a q') ≤
        FSBand.supn (piA a p) + FSBand.supn (piA a q' - piA a p) := by
      have h0 := FSBand.supn_add_le (piA a p) (piA a q' - piA a p)
      rwa [show piA a p + (piA a q' - piA a p) = piA a q' by abel] at h0
    have h3 : gL L * ((n : ℝ) / 2) < gL L * FSBand.supn (piA a p) := by
      have e1 := mul_le_mul_of_nonneg_left htri hg.le
      have e2 := mul_lt_mul_of_pos_left hd hg
      rw [hKg] at h1 hρK
      nlinarith
    have h4 := g_supn_le_kabs hL (p a)
    have e : Kc L n / 2 = gL L * ((n : ℝ) / 2) := by rw [hKg]; ring
    unfold piA at h3
    linarith
  have hcard := card_bandSet_le hL hρ0 hρK hn2
  have hsqc : Real.sqrt (Zs s * ((bandSet L (Kc L n) ρ n).card : ℝ)) ≤
      Real.sqrt (Zs s * (2250 * (n : ℝ) ^ 2 * (ρ / gL L + 1))) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hcard (Zs_pos hs).le)
  have hVa : ‖regMul a (fun μ => (bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ μ : ℂ))
      (Va sys L n a q)‖ ≤ chargeA sys a * coulombCellAmplitude L *
        (26 * ((n : ℝ) / 4) * (16 * sys.mass a / (3 * Kc L n / 4) ^ 2) *
            ‖regTail L a (Kc L n / 2) q‖ +
          16 * sys.mass a / (3 * Kc L n / 4) ^ 2 / ((n : ℝ) / 4) ^ 2 *
            Real.sqrt (Zs s * (2250 * (n : ℝ) ^ 2 * (ρ / gL L + 1))) * Wlat a s q) := by
    refine norm_regMul_Va_le_of sys L n a _ hL q (fun κ cw hκ hcw => ?_)
    have h := norm_wop_band_le (piA (n := n) a) κ hκ hcw
      (fun q' => bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ (q' a)) hcθ0
      (R := (n : ℝ) / 4) (by positivity) hs (fun q' => hθb (q' a))
      (fun p => Kc L n / 2 < finitePlaneWaveKabs (2 * Real.pi / L) n (p a))
      (fun q' p h1 h2 _ => hT q' p h1 h2) (bandSet L (Kc L n) ρ n) hS q
    have e1 : Real.sqrt (∑ p, if Kc L n / 2 < finitePlaneWaveKabs (2 * Real.pi / L) n (p a)
        then ‖q.ofLp p‖ ^ 2 else 0) = ‖regTail L a (Kc L n / 2) q‖ := by
      rw [← norm_sq_regTail, Real.sqrt_sq (norm_nonneg _)]
    have hW : Real.sqrt (∑ p, (1 + lsq (piA a p)) ^ s * ‖q.ofLp p‖ ^ 2) = Wlat a s q := rfl
    rw [e1, hW] at h
    have h2 : 16 * sys.mass a / (3 * Kc L n / 4) ^ 2 * cw / ((n : ℝ) / 4) ^ 2 *
          Real.sqrt (Zs s * ((bandSet L (Kc L n) ρ n).card : ℝ)) * Wlat a s q ≤
        16 * sys.mass a / (3 * Kc L n / 4) ^ 2 * cw / ((n : ℝ) / 4) ^ 2 *
          Real.sqrt (Zs s * (2250 * (n : ℝ) ^ 2 * (ρ / gL L + 1))) * Wlat a s q := by
      have := Wlat_nonneg a s q
      gcongr
    calc _ ≤ _ := h
      _ ≤ 26 * ((n : ℝ) / 4) * (16 * sys.mass a / (3 * Kc L n / 4) ^ 2) * cw *
            ‖regTail L a (Kc L n / 2) q‖ +
          16 * sys.mass a / (3 * Kc L n / 4) ^ 2 * cw / ((n : ℝ) / 4) ^ 2 *
            Real.sqrt (Zs s * (2250 * (n : ℝ) ^ 2 * (ρ / gL L + 1))) * Wlat a s q := by
          linarith
      _ = _ := by ring
  refine hres.trans ?_
  calc _ ≤ ‖regMul a (fun μ => (bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ μ : ℂ))
          (Hret sys L n ΔH q - (E : ℂ) • q) -
        regMul a (fun μ => (bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ μ : ℂ)) (ΔH q)‖ +
      ‖regMul a (fun μ => (bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ μ : ℂ))
          (Va sys L n a q)‖ := norm_sub_le _ _
    _ ≤ (‖regMul a (fun μ => (bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ μ : ℂ))
          (Hret sys L n ΔH q - (E : ℂ) • q)‖ +
        ‖regMul a (fun μ => (bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ μ : ℂ))
          (ΔH q)‖) +
      ‖regMul a (fun μ => (bandW sys L Hunit a E (3 * Kc L n / 4) (Kc L n) ρ μ : ℂ))
          (Va sys L n a q)‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add hr hΔ) hVa
    _ = _ := by ring


/-- The band constant in front of `K^{-1} ϱ^{1/2} W_s(q)`. -/
noncomputable def bandCB (sys : CoulombSystem eta ν) (L : ℝ) (a : Fin eta) (s : ℝ) : ℝ :=
  chargeA sys a * coulombCellAmplitude L *
    (1664 * sys.mass a / (9 * gL L) * (16 * Real.sqrt 2 * qtailC2 sys L a s) +
      4096 * sys.mass a * gL L / 9 * Real.sqrt (2250 * Zs s * (1 + 1 / gL L)))

/-- The band constant in front of `(γ + C_Δ + 1) ‖q‖`. -/
noncomputable def bandCA (sys : CoulombSystem eta ν) (L : ℝ) (a : Fin eta) (s : ℝ) : ℝ :=
  256 * sys.mass a / 9 + chargeA sys a * coulombCellAmplitude L *
    (1664 * sys.mass a / (9 * gL L)) * (16 * qtailC2 sys L a s + 8 * qtailC sys L a ^ 2)

lemma bandCB_nonneg (hL : 0 < L) {s : ℝ} (hs : 3 / 2 < s) : 0 ≤ bandCB sys L a s := by
  unfold bandCB
  have := chargeA_nonneg sys a
  have := coulombCellAmplitude_pos hL
  have := sys.mass_pos a
  have := gL_pos hL
  have := qtailC2_nonneg sys a hL s
  have := Zs_pos hs
  positivity

lemma bandCA_nonneg (hL : 0 < L) (s : ℝ) : 0 ≤ bandCA sys L a s := by
  unfold bandCA
  have := chargeA_nonneg sys a
  have := coulombCellAmplitude_pos hL
  have := sys.mass_pos a
  have := gL_pos hL
  have := qtailC2_nonneg sys a hL s
  positivity

set_option maxHeartbeats 400000 in
/-- **`lem:qtail`, second bound (eq:qtail)**: for `1 ≤ ϱ ≤ K/4`, `K ≥ 1` and `K/2` beyond twice
the threshold of the first bound,
`‖B_{a,ϱ} q‖ ≤ K^{-2} (C_B K^{-1} ϱ^{1/2} W_s(q) + C_A (γ + C_Δ + 1) ‖q‖)`. -/
theorem qtail_band (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {E γr s : ℝ} (hγr : 0 ≤ γr) (hs : 3 / 2 < s) (q : En eta n)
    (hq : ‖Hret sys L n ΔH q - (E : ℂ) • q‖ ≤ γr * ‖q‖)
    {ρ : ℝ} (hρ1 : 1 ≤ ρ) (hρK : ρ ≤ Kc L n / 4) (hK1 : 1 ≤ Kc L n)
    (hK : 2 * qtailL1 sys L Hunit a E < Kc L n / 2) :
    ‖bandMask L (Kc L n) ρ a q‖ ≤ 1 / Kc L n ^ 2 *
      (bandCB sys L a s * (Kc L n)⁻¹ * Real.sqrt ρ * Wlat a s q +
        bandCA sys L a s * (γr + CΔ + 1) * ‖q‖) := by
  have hraw := qtail_band_raw sys Hunit a hL hPeriodic hCΔ hΔb hγr hs q hq (by linarith) hρK hK
  have hqt := qtail sys Hunit a hL hPeriodic hCΔ hΔb hγr hs q hq (Kc L n / 2) hK
  have hg : 0 < gL L := gL_pos hL
  have hm : 0 < sys.mass a := sys.mass_pos a
  have hQ : 0 ≤ chargeA sys a * coulombCellAmplitude L :=
    mul_nonneg (chargeA_nonneg sys a) (coulombCellAmplitude_pos hL).le
  have hc₂ : 0 ≤ qtailC2 sys L a s := qtailC2_nonneg sys a hL s
  have hc : 0 ≤ qtailC sys L a := qtailC_nonneg sys a hL
  have hZ : 0 < Zs s := Zs_pos hs
  have hKg : Kc L n = gL L * n := rfl
  have hW0 : 0 ≤ Wlat a s q := Wlat_nonneg a s q
  have hN0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hh0 : 0 ≤ ‖regTail L a (Kc L n / 2) q‖ := norm_nonneg _
  unfold bandCB bandCA
  unfold FSQtail.F at hqt
  generalize ‖bandMask L (Kc L n) ρ a q‖ = B at hraw ⊢
  generalize ‖regTail L a (Kc L n / 2) q‖ = h at hraw hqt hh0
  generalize Wlat a s q = W at hraw hqt hW0 ⊢
  generalize ‖q‖ = N at hraw hqt hN0 ⊢
  generalize qtailC2 sys L a s = c₂ at hqt hc₂ ⊢
  generalize qtailC sys L a = c at hqt hc ⊢
  generalize chargeA sys a * coulombCellAmplitude L = Q at hraw hQ ⊢
  generalize sys.mass a = m at hraw hm ⊢
  generalize Zs s = Z at hraw hZ ⊢
  generalize Kc L n = K at hraw hqt hKg hK1 hρK ⊢
  generalize gL L = g at hraw hKg hg ⊢
  generalize (n : ℝ) = x at hraw hKg
  have hK0 : 0 < K := by linarith
  have hx : x = K / g := by rw [hKg]; field_simp
  have hxpos : 0 < x := by rw [hx]; positivity
  have hsρ : 1 ≤ Real.sqrt ρ := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hρ1
  -- `(K/2)^{-1/2} ≤ √2 √ϱ`
  have hpow : (K / 2) ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt 2 * Real.sqrt ρ := by
    have hK2 : (0 : ℝ) < K / 2 := by positivity
    have e : (K / 2) ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt (K / 2) := by
      rw [Real.rpow_neg hK2.le, ← Real.sqrt_eq_rpow, one_div]
    rw [e]
    have hpos : 0 < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
    have hs2 : Real.sqrt (1 / 2) ≤ Real.sqrt (K / 2) := Real.sqrt_le_sqrt (by linarith)
    have hsq2 : Real.sqrt 2 * Real.sqrt (1 / 2) = 1 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    calc 1 / Real.sqrt (K / 2) ≤ 1 / Real.sqrt (1 / 2) := one_div_le_one_div_of_le hpos hs2
      _ = Real.sqrt 2 := by rw [div_eq_iff hpos.ne', hsq2]
      _ ≤ Real.sqrt 2 * Real.sqrt ρ := le_mul_of_one_le_right (Real.sqrt_nonneg _) hsρ
  -- the first bound at `K/2`
  have hh : h ≤ 16 * c₂ * (1 / K ^ 2) * (Real.sqrt 2 * Real.sqrt ρ * W + (γr + CΔ) * N) +
      8 * c ^ 2 * N * (1 / K ^ 2) := by
    refine hqt.trans ?_
    have e1 : 4 * (c₂ / (K / 2) ^ 2 * ((K / 2) ^ (-(1 / 2 : ℝ)) * W + (γr + CΔ) * N)) =
        16 * c₂ * (1 / K ^ 2) * ((K / 2) ^ (-(1 / 2 : ℝ)) * W + (γr + CΔ) * N) := by ring
    have e2 : 2 * c ^ 2 * N / (K / 2) ^ 2 = 8 * c ^ 2 * N * (1 / K ^ 2) := by ring
    rw [e1, e2]
    have h1 : (K / 2) ^ (-(1 / 2 : ℝ)) * W ≤ Real.sqrt 2 * Real.sqrt ρ * W :=
      mul_le_mul_of_nonneg_right hpow hW0
    have h16 : 0 ≤ 16 * c₂ * (1 / K ^ 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h16]
  -- the band count in `ϱ`
  have hsq : Real.sqrt (Z * (2250 * x ^ 2 * (ρ / g + 1))) ≤
      x * Real.sqrt (2250 * Z * (1 + 1 / g)) * Real.sqrt ρ := by
    have h1 : ρ / g + 1 ≤ (1 + 1 / g) * ρ := by
      have e : (1 + 1 / g) * ρ = ρ + ρ / g := by ring
      rw [e]; linarith
    have h2 : Z * (2250 * x ^ 2 * (ρ / g + 1)) ≤ x ^ 2 * ((2250 * Z * (1 + 1 / g)) * ρ) := by
      calc Z * (2250 * x ^ 2 * (ρ / g + 1)) = (Z * 2250 * x ^ 2) * (ρ / g + 1) := by ring
        _ ≤ (Z * 2250 * x ^ 2) * ((1 + 1 / g) * ρ) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by ring
    calc _ ≤ Real.sqrt (x ^ 2 * ((2250 * Z * (1 + 1 / g)) * ρ)) := Real.sqrt_le_sqrt h2
      _ = _ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hxpos.le,
            Real.sqrt_mul (by positivity)]
          ring
  -- monotone step
  have hc0 : 0 ≤ 16 * m / (3 * K / 4) ^ 2 := by positivity
  have hstep : B ≤ 16 * m / (3 * K / 4) ^ 2 * ((γr + CΔ) * N) +
      Q * (26 * (x / 4) * (16 * m / (3 * K / 4) ^ 2) *
          (16 * c₂ * (1 / K ^ 2) * (Real.sqrt 2 * Real.sqrt ρ * W + (γr + CΔ) * N) +
            8 * c ^ 2 * N * (1 / K ^ 2)) +
        16 * m / (3 * K / 4) ^ 2 / (x / 4) ^ 2 *
          (x * Real.sqrt (2250 * Z * (1 + 1 / g)) * Real.sqrt ρ) * W) := by
    refine hraw.trans ?_
    gcongr
  have hr2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsX : 0 ≤ Real.sqrt (2250 * Z * (1 + 1 / g)) := Real.sqrt_nonneg _
  generalize Real.sqrt 2 = r2 at hstep hr2 ⊢
  generalize Real.sqrt ρ = sρ at hstep hsρ ⊢
  generalize Real.sqrt (2250 * Z * (1 + 1 / g)) = sX at hstep hsX ⊢
  have e6 : 16 * m / (3 * K / 4) ^ 2 * ((γr + CΔ) * N) +
      Q * (26 * (x / 4) * (16 * m / (3 * K / 4) ^ 2) *
          (16 * c₂ * (1 / K ^ 2) * (r2 * sρ * W + (γr + CΔ) * N) + 8 * c ^ 2 * N * (1 / K ^ 2)) +
        16 * m / (3 * K / 4) ^ 2 / (x / 4) ^ 2 * (x * sX * sρ) * W) =
      1 / K ^ 2 * (256 * m / 9 * ((γr + CΔ) * N) +
        Q * (1664 * m / (9 * g) * K⁻¹ *
          (16 * c₂ * (r2 * sρ * W + (γr + CΔ) * N) + 8 * c ^ 2 * N) +
          4096 * m * g / 9 * K⁻¹ * sX * sρ * W)) := by
    rw [hx]; field_simp; ring
  rw [e6] at hstep
  refine hstep.trans ?_
  have hKi : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK1
  have hKi0 : 0 ≤ K⁻¹ := inv_nonneg.mpr hK0.le
  have hKK : 0 ≤ 1 / K ^ 2 := by positivity
  have hY0 : 0 ≤ 16 * c₂ * (γr + CΔ) + 8 * c ^ 2 := by positivity
  have hY1 : K⁻¹ * (16 * c₂ * (γr + CΔ) + 8 * c ^ 2) ≤ 16 * c₂ * (γr + CΔ) + 8 * c ^ 2 :=
    mul_le_of_le_one_left hY0 hKi
  have hY : K⁻¹ * (16 * c₂ * (γr + CΔ) + 8 * c ^ 2) ≤ (16 * c₂ + 8 * c ^ 2) * (γr + CΔ + 1) := by
    have h3 : 0 ≤ c ^ 2 * (γr + CΔ) := mul_nonneg (sq_nonneg c) (add_nonneg hγr hCΔ)
    linarith
  have F1 : 0 ≤ 1 / K ^ 2 * (Q * (1664 * m / (9 * g)) * N *
      ((16 * c₂ + 8 * c ^ 2) * (γr + CΔ + 1) - K⁻¹ * (16 * c₂ * (γr + CΔ) + 8 * c ^ 2))) := by
    apply mul_nonneg hKK
    apply mul_nonneg (by positivity)
    linarith
  have F2 : 0 ≤ 1 / K ^ 2 * (256 * m / 9 * N) := by positivity
  linarith [F1, F2]

/-- `W_s(q)` of a quasi-eigenstate (the weighted norm step of `regTail_le_of_quasi`). -/
lemma Wlat_le_of_quasi (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {E γ s : ℝ} (hγ : 0 ≤ γ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hE : -Clow sys L Hunit CΔ ≤ E)
    (q : En eta n) (hq : ‖Hret sys L n ΔH q - (E : ℂ) • q‖ ≤ γ * ‖q‖) :
    Wlat a s q ≤ latConst sys L a ^ (s / 2) *
      ((2 * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ (s / 2) *
        (1 + E + Clow sys L Hunit CΔ) ^ (s / 2) * ‖q‖) := by
  have hC₀ := (Clow_pos sys Hunit hCΔ (L := L)).le
  have hV0 : 0 ≤ CVret sys L Hunit CΔ ^ 2 / 2 := by positivity
  set x := 1 + E + Clow sys L Hunit CΔ with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  refine (Wlat_le_wt sys a hL hs0 q).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (latConst_pos sys a).le _)
  refine (wt_le_of_quasi sys Hunit hL hPeriodic hCΔ hΔb hγ hs0 hs2 q hq).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have hf := quasi_factor_le hγ hC₀ hV0 hE
  rw [← hx] at hf
  calc (2 * (1 + |E| + γ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ (s / 2)
      ≤ (2 * (x * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2))) ^ (s / 2) := by
        apply Real.rpow_le_rpow (by have := abs_nonneg E; positivity) _ (by positivity)
        rw [add_assoc (1 + |E|), add_assoc (1 + Clow sys L Hunit CΔ)] at *
        nlinarith
    _ = _ := by
        rw [show 2 * (x * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) =
            (2 * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) * x by ring,
          Real.mul_rpow (by positivity) (by linarith)]

/-- The constant term of the register band bound. -/
noncomputable def bandA1 (sys : CoulombSystem eta ν) (L : ℝ) (a : Fin eta) (s CΔ γ K : ℝ) : ℝ :=
  1 / K ^ 2 * (bandCA sys L a s * (γ + CΔ + 1))

/-- The energy term of the register band bound. -/
noncomputable def bandB1 (sys : CoulombSystem eta ν) (L Hunit : ℝ) (a : Fin eta)
    (s CΔ γ K ρ : ℝ) : ℝ :=
  1 / K ^ 2 * (bandCB sys L a s * K⁻¹ * Real.sqrt ρ) * latConst sys L a ^ (s / 2) *
    (2 * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ (s / 2)

/-- **The register band of a quasi-eigenstate**:
`‖B_{a,ϱ} q‖ ≤ (a₁ + b₁ (1 + E + C_low)^{s/2}) ‖q‖`. -/
theorem band_le_of_quasi (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {E γ s ρ : ℝ} (hγ : 0 ≤ γ) (hs : 3 / 2 < s) (hs2 : s ≤ 2) (hE : -Clow sys L Hunit CΔ ≤ E)
    (q : En eta n) (hq : ‖Hret sys L n ΔH q - (E : ℂ) • q‖ ≤ γ * ‖q‖)
    (hρ1 : 1 ≤ ρ) (hρK : ρ ≤ Kc L n / 4) (hK1 : 1 ≤ Kc L n)
    (hK : 2 * qtailL1 sys L Hunit a E < Kc L n / 2) :
    ‖bandMask L (Kc L n) ρ a q‖ ≤ (bandA1 sys L a s CΔ γ (Kc L n) +
      bandB1 sys L Hunit a s CΔ γ (Kc L n) ρ * (1 + E + Clow sys L Hunit CΔ) ^ (s / 2)) * ‖q‖ := by
  have hb := qtail_band sys Hunit a hL hPeriodic hCΔ hΔb hγ hs q hq hρ1 hρK hK1 hK
  have hW := Wlat_le_of_quasi sys Hunit a hL hPeriodic hCΔ hΔb hγ (by linarith) hs2 hE q hq
  have hCB := bandCB_nonneg sys a hL hs
  have hK0 : 0 < Kc L n := by linarith
  refine hb.trans ?_
  have hKK : 0 ≤ 1 / Kc L n ^ 2 * (bandCB sys L a s * (Kc L n)⁻¹ * Real.sqrt ρ) := by positivity
  calc 1 / Kc L n ^ 2 * (bandCB sys L a s * (Kc L n)⁻¹ * Real.sqrt ρ * Wlat a s q +
        bandCA sys L a s * (γ + CΔ + 1) * ‖q‖)
      = 1 / Kc L n ^ 2 * (bandCB sys L a s * (Kc L n)⁻¹ * Real.sqrt ρ) * Wlat a s q +
          1 / Kc L n ^ 2 * (bandCA sys L a s * (γ + CΔ + 1)) * ‖q‖ := by ring
    _ ≤ 1 / Kc L n ^ 2 * (bandCB sys L a s * (Kc L n)⁻¹ * Real.sqrt ρ) *
          (latConst sys L a ^ (s / 2) *
            ((2 * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ (s / 2) *
              (1 + E + Clow sys L Hunit CΔ) ^ (s / 2) * ‖q‖)) +
          1 / Kc L n ^ 2 * (bandCA sys L a s * (γ + CΔ + 1)) * ‖q‖ := by
        gcongr
    _ = _ := by unfold bandA1 bandB1; ring

end BandBound

/-! ## The band projector and the time average -/

section BandProj

variable {n : ℕ}

/-- The band projector `B_ϱ`: some register in its cube band. -/
noncomputable def bandProj (L K ρ : ℝ) : En eta n →ₗ[ℂ] En eta n :=
  cfgMul (fun p => if ∃ a, InBand L K ρ (p a) then 1 else 0)

lemma norm_sq_bandProj (L K ρ : ℝ) (u : En eta n) :
    ‖bandProj L K ρ u‖ ^ 2 = ∑ p, if (∃ a, InBand L K ρ (p a)) then ‖u.ofLp p‖ ^ 2 else 0 := by
  classical
  rw [norm_sq_En]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold bandProj
  rw [cfgMul_apply]
  split_ifs <;> simp

lemma norm_bandProj_le (L K ρ : ℝ) (u : En eta n) : ‖bandProj L K ρ u‖ ≤ ‖u‖ := by
  classical
  have h2 : ‖bandProj L K ρ u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [norm_sq_bandProj, norm_sq_En]
    refine Finset.sum_le_sum fun p _ => ?_
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- `‖B_ϱ u‖² ≤ Σ_a ‖B_{a,ϱ} u‖²`. -/
lemma norm_sq_bandProj_le (L K ρ : ℝ) (u : En eta n) :
    ‖bandProj L K ρ u‖ ^ 2 ≤ ∑ a, ‖bandMask L K ρ a u‖ ^ 2 := by
  classical
  rw [norm_sq_bandProj]
  simp_rw [norm_sq_bandMask]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun p _ => ?_
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    calc ‖u.ofLp p‖ ^ 2 = (if InBand L K ρ (p a) then ‖u.ofLp p‖ ^ 2 else 0) := by rw [if_pos ha]
      _ ≤ ∑ b, (if InBand L K ρ (p b) then ‖u.ofLp p‖ ^ 2 else 0) :=
          Finset.single_le_sum (f := fun b => if InBand L K ρ (p b) then ‖u.ofLp p‖ ^ 2 else 0)
            (fun b _ => by split_ifs <;> positivity) (Finset.mem_univ a)
  · exact Finset.sum_nonneg fun b _ => by split_ifs <;> positivity

/-- The hot projector decreases with the threshold. -/
lemma hotProj_anti (L : ℝ) {l l' : ℝ} (hll : l ≤ l') (u : En eta n) :
    ‖hotProj L l' u‖ ≤ ‖hotProj L l u‖ := by
  classical
  have h2 : ‖hotProj L l' u‖ ^ 2 ≤ ‖hotProj L l u‖ ^ 2 := by
    rw [norm_sq_hotProj, norm_sq_hotProj]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases h1 : ∃ a, l' < finitePlaneWaveKabs (2 * Real.pi / L) n (p a)
    · obtain ⟨a, ha⟩ := h1
      rw [if_pos ⟨a, ha⟩, if_pos ⟨a, lt_of_le_of_lt hll ha⟩]
    · rw [if_neg h1]
      split_ifs <;> positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

end BandProj

section BandQuasi

variable [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) {n : ℕ}

/-- `α = Σ_a 2 a₁(a)²`. -/
noncomputable def bandAlpha (sys : CoulombSystem eta ν) (L : ℝ) (s CΔ γ K : ℝ) : ℝ :=
  ∑ a, 2 * bandA1 sys L a s CΔ γ K ^ 2

/-- `β = Σ_a 2 b₁(a)²`. -/
noncomputable def bandBeta (sys : CoulombSystem eta ν) (L Hunit : ℝ) (s CΔ γ K ρ : ℝ) : ℝ :=
  ∑ a, 2 * bandB1 sys L Hunit a s CΔ γ K ρ ^ 2

/-- **The band content of a quasi-eigenstate.** -/
theorem bandProj_sq_le_of_quasi (hL : 0 < L)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {E γ s ρ X : ℝ} (hγ : 0 ≤ γ) (hs : 3 / 2 < s) (hs2 : s ≤ 2)
    (hE : -Clow sys L Hunit CΔ ≤ E) (hEX : E ≤ X)
    (hρ1 : 1 ≤ ρ) (hρK : ρ ≤ Kc L n / 4) (hK1 : 1 ≤ Kc L n)
    (hK : ∀ a, 2 * qtailL1 sys L Hunit a X < Kc L n / 2) (q : En eta n)
    (hq : ‖Hret sys L n ΔH q - (E : ℂ) • q‖ ≤ γ * ‖q‖) :
    ‖bandProj L (Kc L n) ρ q‖ ^ 2 ≤
      (bandAlpha sys L s CΔ γ (Kc L n) +
        bandBeta sys L Hunit s CΔ γ (Kc L n) ρ * (1 + E + Clow sys L Hunit CΔ) ^ s) * ‖q‖ ^ 2 := by
  refine (norm_sq_bandProj_le L (Kc L n) ρ q).trans ?_
  unfold bandAlpha bandBeta
  rw [add_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  have hKa : 2 * qtailL1 sys L Hunit a E < Kc L n / 2 :=
    lt_of_le_of_lt (by linarith [qtailL1_mono sys Hunit (L := L) a hEX]) (hK a)
  have h := band_le_of_quasi sys Hunit a hL hPeriodic hCΔ hΔb hγ hs hs2 hE q hq hρ1 hρK hK1 hKa
  set x := 1 + E + Clow sys L Hunit CΔ with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  set A1 := bandA1 sys L a s CΔ γ (Kc L n)
  set B1 := bandB1 sys L Hunit a s CΔ γ (Kc L n) ρ
  have hxs : (x ^ (s / 2)) ^ 2 = x ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hsq : (A1 + B1 * x ^ (s / 2)) ^ 2 ≤ 2 * A1 ^ 2 + 2 * B1 ^ 2 * x ^ s := by
    rw [← hxs]
    nlinarith [sq_nonneg (A1 - B1 * x ^ (s / 2))]
  calc ‖bandMask L (Kc L n) ρ a q‖ ^ 2 ≤ ((A1 + B1 * x ^ (s / 2)) * ‖q‖) ^ 2 := h2
    _ = (A1 + B1 * x ^ (s / 2)) ^ 2 * ‖q‖ ^ 2 := by ring
    _ ≤ (2 * A1 ^ 2 + 2 * B1 ^ 2 * x ^ s) * ‖q‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = _ := by ring

/-- **eq:tavgU, band part, spectral form.** -/
theorem tavg_band (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {t Δ X s E₀ ρ : ℝ} (ht : 0 < t) (hΔ : 0 ≤ Δ) (hs : 3 / 2 < s) (hs2 : s ≤ 2)
    (hX : -Clow sys L Hunit CΔ ≤ X) (hE₀ : E₀ < X - Δ)
    (hρ1 : 1 ≤ ρ) (hρK : ρ ≤ Kc L n / 4) (hK1 : 1 ≤ Kc L n)
    (hK : ∀ a, 2 * qtailL1 sys L Hunit a X < Kc L n / 2)
    (u : En eta n) (hu : ∀ k, E₀ < Asym sys L n k → u.ofLp k = 0) :
    (1 / t) * ∫ τ in (0 : ℝ)..t, ‖bandProj L (Kc L n) ρ (retFlow sys L n hΔsym τ u)‖ ^ 2 ≤
      2 * Real.exp 1 * (Real.sqrt π * (bandAlpha sys L s CΔ Δ (Kc L n) * ‖u‖ ^ 2 +
          bandBeta sys L Hunit s CΔ Δ (Kc L n) ρ * (1 + Δ) ^ s *
            ((CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ (s / 2)) ^ 2 *
              ‖FSSpectral.wt (sb eta n) (Asym sys L n) (s / 2) u‖ ^ 2 +
          (CVret sys L Hunit CΔ / (X - Δ - E₀)) ^ 2 *
            ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) u‖ ^ 2) +
        Real.sqrt (2 * π) * Real.exp (-(t ^ 2 * Δ ^ 2) / 2) * ‖u‖ ^ 2) := by
  classical
  have hH := Hret_isSymmetric sys L n hΔsym
  have hα : 0 ≤ bandAlpha sys L s CΔ Δ (Kc L n) :=
    Finset.sum_nonneg fun a _ => by positivity
  have hβ : 0 ≤ bandBeta sys L Hunit s CΔ Δ (Kc L n) ρ :=
    Finset.sum_nonneg fun a _ => by positivity
  have hlow : ∀ i, -Clow sys L Hunit CΔ ≤ retEig sys L n hΔsym i := fun i =>
    eigen_lower (retBasis sys L n hΔsym) (retEig sys L n hΔsym) (Hret sys L n ΔH)
      (retBasis_eigen sys L n hΔsym) (Hret_lower sys Hunit n hL hPeriodic hΔb) i
  have hCG : 0 ≤ CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2 := by
    have := CVret_nonneg sys Hunit hCΔ (L := L)
    have := (Clow_pos sys Hunit hCΔ (L := L)).le
    linarith
  have hu' : ∀ k, E₀ < Asym sys L n k → ⟪sb eta n k, u⟫_ℂ = 0 := fun k hk => by
    rw [inner_sb]; exact hu k hk
  exact FSSpectral.tavg_hot_abstract (retBasis sys L n hΔsym) (retEig sys L n hΔsym) (sb eta n)
    (Asym sys L n) (Asym_nonneg sys L n) (Hret sys L n ΔH) (Vret sys L n ΔH) hH
    (retBasis_eigen sys L n hΔsym) (Hret_eq_kin_add sys L n ΔH) (CVret_nonneg sys Hunit hCΔ)
    (Vret_le_wt sys Hunit n hL hPeriodic hCΔ hΔb) hlow hCG
    (graph_le sys Hunit hL hPeriodic hΔsym hCΔ hΔb) (bandProj L (Kc L n) ρ)
    (norm_bandProj_le L (Kc L n) ρ)
    ht hΔ hX (by linarith) hs2 hα hβ hE₀
    (fun E' hE' hE'X q hq => bandProj_sq_le_of_quasi sys Hunit hL hPeriodic hCΔ hΔb hΔ hs hs2 hE'
      hE'X hρ1 hρK hK1 hK q hq) u hu'

end BandQuasi

/-! ## eq:tavgU with explicit `K`-dependence -/

section BandExplicit

variable [Fintype ν] (sys : CoulombSystem eta ν) (L : ℝ) (Hunit : ℝ)

/-- `P_A^band = Σ_a (C_A(a) (C_Δ + 1))²`. -/
noncomputable def PAband (s CΔ : ℝ) : ℝ := ∑ a, (bandCA sys L a s * (CΔ + 1)) ^ 2

/-- `P_B^band = Σ_a C_B(a)² κ_a^s (2(1 + C_low + C_V²/2))^s`. -/
noncomputable def PBband (s CΔ : ℝ) : ℝ :=
  ∑ a, bandCB sys L a s ^ 2 * latConst sys L a ^ s *
    (2 * (1 + Clow sys L Hunit CΔ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ s

/-- The constant of the band part of eq:tavgU. -/
noncomputable def Cband (CΔ s : ℝ) : ℝ :=
  2 * Real.exp 1 * (Real.sqrt π * (2 * PAband sys L s CΔ +
      2 * PBband sys L Hunit s CΔ *
        (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ s * momentConst eta (s / 2 + 1) +
      CVret sys L Hunit CΔ ^ 2 * (4096 * mmax sys) ^ 2 * momentConst eta (1 / 2 + 1)) +
    Real.sqrt (2 * π))

variable {L}

lemma bandAlpha_le (hL : 0 < L) {s CΔ γ D K : ℝ} (hCΔ : 0 ≤ CΔ) (hγ : 0 ≤ γ) (hγD : γ ≤ D)
    (hK : 0 < K) :
    bandAlpha sys L s CΔ γ K ≤ 2 / K ^ 4 * PAband sys L s CΔ * (1 + D) ^ 2 := by
  unfold bandAlpha PAband
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  unfold bandA1
  have hCA := bandCA_nonneg sys a hL s
  have hD : 0 ≤ D := hγ.trans hγD
  have h1 : γ + CΔ + 1 ≤ (CΔ + 1) * (1 + D) := by nlinarith
  have h0 : 0 ≤ bandCA sys L a s * (γ + CΔ + 1) := by positivity
  have h2 : bandCA sys L a s * (γ + CΔ + 1) ≤ bandCA sys L a s * (CΔ + 1) * (1 + D) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hCA
  have h3 := pow_le_pow_left₀ h0 h2 2
  calc 2 * (1 / K ^ 2 * (bandCA sys L a s * (γ + CΔ + 1))) ^ 2
      = 2 / K ^ 4 * (bandCA sys L a s * (γ + CΔ + 1)) ^ 2 := by ring
    _ ≤ 2 / K ^ 4 * (bandCA sys L a s * (CΔ + 1) * (1 + D)) ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

lemma bandBeta_le (_hL : 0 < L) {s CΔ γ D K ρ : ℝ} (hs : 0 ≤ s) (hCΔ : 0 ≤ CΔ) (hγ : 0 ≤ γ)
    (hγD : γ ≤ D) (hK : 0 < K) (hρ : 0 ≤ ρ) :
    bandBeta sys L Hunit s CΔ γ K ρ ≤ 2 * ρ / K ^ 6 * PBband sys L Hunit s CΔ * (1 + D) ^ s := by
  unfold bandBeta PBband
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  unfold bandB1
  set cB := bandCB sys L a s
  set κ := latConst sys L a
  set Y := 1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2
  set Y₀ := 1 + Clow sys L Hunit CΔ + CVret sys L Hunit CΔ ^ 2 / 2
  have hκ : 0 < κ := latConst_pos sys a
  have hC₀ := (Clow_pos sys Hunit hCΔ (L := L)).le
  have hD : 0 ≤ D := hγ.trans hγD
  have hY : 0 ≤ 2 * Y := by positivity
  have hY0 : 0 ≤ Y₀ := by positivity
  have hsq : (1 / K ^ 2 * (cB * K⁻¹ * Real.sqrt ρ) * κ ^ (s / 2) * (2 * Y) ^ (s / 2)) ^ 2 =
      ρ / K ^ 6 * cB ^ 2 * κ ^ s * (2 * Y) ^ s := by
    have e1 : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ
    have e2 : (κ ^ (s / 2)) ^ 2 = κ ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]; norm_num
    have e3 : ((2 * Y) ^ (s / 2)) ^ 2 = (2 * Y) ^ s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY]; norm_num
    rw [show (1 / K ^ 2 * (cB * K⁻¹ * Real.sqrt ρ) * κ ^ (s / 2) * (2 * Y) ^ (s / 2)) ^ 2 =
        (1 / K ^ 2) ^ 2 * cB ^ 2 * (K⁻¹) ^ 2 * Real.sqrt ρ ^ 2 * (κ ^ (s / 2)) ^ 2 *
          ((2 * Y) ^ (s / 2)) ^ 2 by ring, e1, e2, e3]
    ring
  rw [hsq]
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
  calc 2 * (ρ / K ^ 6 * cB ^ 2 * κ ^ s * (2 * Y) ^ s)
      = 2 * ρ / K ^ 6 * (cB ^ 2 * κ ^ s) * (2 * Y) ^ s := by ring
    _ ≤ 2 * ρ / K ^ 6 * (cB ^ 2 * κ ^ s) * ((2 * Y₀) ^ s * (1 + D) ^ s) :=
        mul_le_mul_of_nonneg_left hYs (by positivity)
    _ = _ := by ring

omit [Fintype ν] in
/-- The real-number bookkeeping of the band part of eq:tavgU. -/
lemma tavg_band_combine {K D s ρ PA PB CG Ms Mh CV mm M : ℝ}
    (hK1 : 1 ≤ K) (hD0 : 0 ≤ D) (hs : 3 / 2 < s) (hρ1 : 1 ≤ ρ)
    (hPA : 0 ≤ PA) (hPB : 0 ≤ PB) (hCG : 0 ≤ CG) (hMs : 0 ≤ Ms) (hMh : 0 ≤ Mh) (hM : 0 ≤ M)
    {a b y c g N0 Ns Nh : ℝ}
    (ha : a ≤ 2 / K ^ 4 * PA * (1 + D) ^ 2) (ha0 : 0 ≤ a)
    (hb : b ≤ 2 * ρ / K ^ 6 * PB * (1 + D) ^ s) (hb0 : 0 ≤ b) (hy : y ≤ (1 + D) ^ s)
    (hy0 : 0 ≤ y) (hc : c ≤ CV ^ 2 * (4096 * mm) ^ 2 * (1 / K ^ 4)) (hc0 : 0 ≤ c)
    (hg : g ≤ 1 / K ^ 3) (_hg0 : 0 ≤ g)
    (hN0 : N0 ≤ M) (hN00 : 0 ≤ N0) (hNs : Ns ≤ Ms * M * K ^ (2 * s - 1)) (hNs0 : 0 ≤ Ns)
    (hNh : Nh ≤ Mh * M * K) (hNh0 : 0 ≤ Nh) :
    2 * Real.exp 1 * (Real.sqrt π * (a * N0 + b * y * CG ^ s * Ns + c * Nh) +
        Real.sqrt (2 * π) * g * N0) ≤
      2 * Real.exp 1 * (Real.sqrt π * (2 * PA + 2 * PB * CG ^ s * Ms +
          CV ^ 2 * (4096 * mm) ^ 2 * Mh) + Real.sqrt (2 * π)) *
        M * (ρ * K ^ (2 * s - 7) * (1 + D) ^ (2 * s) + 1 / K ^ 3) := by
  have hK0 : 0 < K := by linarith
  have hKs : 0 ≤ K ^ (2 * s - 7) := Real.rpow_nonneg hK0.le _
  have hDs1 : 1 ≤ (1 + D) ^ (2 * s) := Real.one_le_rpow (by linarith) (by linarith)
  have hZ10 : 0 ≤ ρ * K ^ (2 * s - 7) * (1 + D) ^ (2 * s) := by positivity
  have hZ20 : 0 ≤ 1 / K ^ 3 := by positivity
  have hK4 : 1 / K ^ 4 ≤ K ^ (2 * s - 7) := inv_pow_le_rpow hK1 4 (by push_cast; linarith)
  have hK67 : K ^ (2 * s - 1) / K ^ 6 = K ^ (2 * s - 7) := by
    have : K ^ (2 * s - 7) = K ^ (2 * s - 1) / K ^ ((6 : ℕ) : ℝ) := by
      rw [← Real.rpow_sub hK0]; congr 1; push_cast; ring
    rw [this, Real.rpow_natCast]
  have hD2 : (1 + D) ^ 2 ≤ (1 + D) ^ (2 * s) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  have hDss : (1 + D) ^ s * (1 + D) ^ s = (1 + D) ^ (2 * s) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hCGs : 0 ≤ CG ^ s := Real.rpow_nonneg hCG _
  have hDs0 : 0 ≤ (1 + D) ^ s := Real.rpow_nonneg (by linarith) _
  have hk : 1 / K ^ 4 * K = 1 / K ^ 3 := by
    rw [pow_succ, one_div_mul_eq_div, div_mul_cancel_right₀ hK0.ne', one_div]
  have hT1 : a * N0 ≤ 2 * PA * (M * (ρ * K ^ (2 * s - 7) * (1 + D) ^ (2 * s))) := by
    have hρZ : K ^ (2 * s - 7) * (1 + D) ^ (2 * s) ≤ ρ * K ^ (2 * s - 7) * (1 + D) ^ (2 * s) := by
      have := mul_le_mul_of_nonneg_right hρ1
        (by positivity : 0 ≤ K ^ (2 * s - 7) * (1 + D) ^ (2 * s))
      linarith
    calc a * N0 ≤ (2 / K ^ 4 * PA * (1 + D) ^ 2) * M := mul_le_mul ha hN0 hN00 (ha0.trans ha)
      _ = 2 * PA * M * (1 / K ^ 4 * (1 + D) ^ 2) := by ring
      _ ≤ 2 * PA * M * (K ^ (2 * s - 7) * (1 + D) ^ (2 * s)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hK4 hD2 (sq_nonneg _) hKs) (by positivity)
      _ ≤ 2 * PA * M * (ρ * K ^ (2 * s - 7) * (1 + D) ^ (2 * s)) :=
          mul_le_mul_of_nonneg_left hρZ (by positivity)
      _ = _ := by ring
  have hT2 : b * y * CG ^ s * Ns ≤
      2 * PB * CG ^ s * Ms * (M * (ρ * K ^ (2 * s - 7) * (1 + D) ^ (2 * s))) := by
    have hbd : 0 ≤ 2 * ρ / K ^ 6 * PB * (1 + D) ^ s := hb0.trans hb
    calc b * y * CG ^ s * Ns ≤ (2 * ρ / K ^ 6 * PB * (1 + D) ^ s) * (1 + D) ^ s * CG ^ s *
          (Ms * M * K ^ (2 * s - 1)) := by
          have h1 : b * y ≤ (2 * ρ / K ^ 6 * PB * (1 + D) ^ s) * (1 + D) ^ s :=
            mul_le_mul hb hy hy0 hbd
          have h2 : b * y * CG ^ s ≤ (2 * ρ / K ^ 6 * PB * (1 + D) ^ s) * (1 + D) ^ s * CG ^ s :=
            mul_le_mul_of_nonneg_right h1 hCGs
          exact mul_le_mul h2 hNs hNs0 (mul_nonneg (mul_nonneg hbd hDs0) hCGs)
      _ = 2 * PB * CG ^ s * Ms * (M * ρ * (K ^ (2 * s - 1) / K ^ 6) *
            ((1 + D) ^ s * (1 + D) ^ s)) := by ring
      _ = _ := by rw [hK67, hDss]; ring
  have hT3 : c * Nh ≤ CV ^ 2 * (4096 * mm) ^ 2 * Mh * (M * (1 / K ^ 3)) := by
    calc c * Nh ≤ (CV ^ 2 * (4096 * mm) ^ 2 * (1 / K ^ 4)) * (Mh * M * K) :=
          mul_le_mul hc hNh hNh0 (hc0.trans hc)
      _ = CV ^ 2 * (4096 * mm) ^ 2 * Mh * (M * (1 / K ^ 4 * K)) := by ring
      _ = _ := by rw [hk]
  have hT4 : g * N0 ≤ M * (1 / K ^ 3) := by
    calc g * N0 ≤ 1 / K ^ 3 * M := mul_le_mul hg hN0 hN00 (by positivity)
      _ = _ := by ring
  have hpi := Real.sqrt_nonneg π
  have h2pi := Real.sqrt_nonneg (2 * π)
  have hsum : a * N0 + b * y * CG ^ s * Ns + c * Nh ≤
      (2 * PA + 2 * PB * CG ^ s * Ms + CV ^ 2 * (4096 * mm) ^ 2 * Mh) *
        (M * (ρ * K ^ (2 * s - 7) * (1 + D) ^ (2 * s) + 1 / K ^ 3)) := by
    have e1 : 0 ≤ (2 * PA + 2 * PB * CG ^ s * Ms) * (M * (1 / K ^ 3)) := by positivity
    have e2 : 0 ≤ CV ^ 2 * (4096 * mm) ^ 2 * Mh * (M * (ρ * K ^ (2 * s - 7) * (1 + D) ^ (2 * s))) := by
      positivity
    linarith [hT1, hT2, hT3, e1, e2]
  have hg4 : g * N0 ≤ M * (ρ * K ^ (2 * s - 7) * (1 + D) ^ (2 * s) + 1 / K ^ 3) := by
    have := mul_nonneg hM hZ10
    linarith [hT4]
  calc 2 * Real.exp 1 * (Real.sqrt π * (a * N0 + b * y * CG ^ s * Ns + c * Nh) +
        Real.sqrt (2 * π) * g * N0)
      = 2 * Real.exp 1 * (Real.sqrt π * (a * N0 + b * y * CG ^ s * Ns + c * Nh) +
        Real.sqrt (2 * π) * (g * N0)) := by ring
    _ ≤ 2 * Real.exp 1 * (Real.sqrt π *
          ((2 * PA + 2 * PB * CG ^ s * Ms + CV ^ 2 * (4096 * mm) ^ 2 * Mh) *
            (M * (ρ * K ^ (2 * s - 7) * (1 + D) ^ (2 * s) + 1 / K ^ 3))) +
          Real.sqrt (2 * π) * (M * (ρ * K ^ (2 * s - 7) * (1 + D) ^ (2 * s) + 1 / K ^ 3))) := by
        gcongr
    _ = _ := by ring

/-- **eq:tavgU, band part, with explicit `K`-dependence**: for `1 ≤ t`, `1 ≤ ϱ ≤ K/4`, a good
`v` and the scale conditions of eq:tavg-quarter,
`(1/t) ∫₀ᵗ ‖B_ϱ e^{iH'τ} A_{p₀}^E v‖² dτ ≤ C (C_g Ξ)² (ϱ K^{2s-7} (1 + D_K)^{2s} + K^{-3})`. -/
theorem tavg_band_explicit (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {n : ℕ} {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {s : ℝ} (hs : 3 / 2 < s) (hs2 : s ≤ 2)
    (hK : TavgScale sys L Hunit CΔ n) {ρ : ℝ} (hρ1 : 1 ≤ ρ) (hρK : ρ ≤ Kc L n / 4)
    (p₀ : Fin eta) {Cg Ξ t : ℝ} (hCgΞ : 0 ≤ Cg * Ξ)
    (ht : 1 ≤ t) (v : En eta n) (hv : IsGood sys L Cg Ξ v) :
    (1 / t) * ∫ τ in (0 : ℝ)..t,
        ‖bandProj L (Kc L n) ρ (retFlow sys L n hΔsym τ (datum sys L p₀ v))‖ ^ 2 ≤
      Cband sys L Hunit CΔ s * (Cg * Ξ) ^ 2 *
        (ρ * Kc L n ^ (2 * s - 7) * (1 + DK (Kc L n)) ^ (2 * s) + 1 / Kc L n ^ 3) := by
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
  have hqK : ∀ a, 2 * qtailL1 sys L Hunit a (3 * E0 sys L n) < Kc L n / 2 := fun a => by
    have := hK.qtail a
    linarith
  have hmain := tavg_band sys Hunit hL hPeriodic hΔsym hCΔ hΔb (t := t) (Δ := DK (Kc L n) / t)
    (X := 3 * E0 sys L n) (s := s) (E₀ := E0 sys L n) ht0 hΔ0 hs hs2
    (by linarith) (by linarith) hρ1 hρK hK1 hqK (datum sys L p₀ v)
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
  have hPB : 0 ≤ PBband sys L Hunit s CΔ := Finset.sum_nonneg fun a _ => by
    have := latConst_pos sys a (L := L)
    have : 0 ≤ 2 * (1 + Clow sys L Hunit CΔ + CVret sys L Hunit CΔ ^ 2 / 2) := by positivity
    positivity
  have hcomb := tavg_band_combine (K := Kc L n) (D := DK (Kc L n)) (s := s) (ρ := ρ)
    (PA := PAband sys L s CΔ) (PB := PBband sys L Hunit s CΔ)
    (CG := CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2)
    (Ms := momentConst eta (s / 2 + 1)) (Mh := momentConst eta (1 / 2 + 1))
    (CV := CVret sys L Hunit CΔ) (mm := mmax sys) (M := (Cg * Ξ) ^ 2)
    (a := bandAlpha sys L s CΔ (DK (Kc L n) / t) (Kc L n))
    (b := bandBeta sys L Hunit s CΔ (DK (Kc L n) / t) (Kc L n) ρ)
    (y := (1 + DK (Kc L n) / t) ^ s)
    (c := (CVret sys L Hunit CΔ / (3 * E0 sys L n - DK (Kc L n) / t - E0 sys L n)) ^ 2)
    (g := Real.exp (-(t ^ 2 * (DK (Kc L n) / t) ^ 2) / 2))
    (N0 := ‖datum sys L p₀ v‖ ^ 2)
    (Ns := ‖FSSpectral.wt (sb eta n) (Asym sys L n) (s / 2) (datum sys L p₀ v)‖ ^ 2)
    (Nh := ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) (datum sys L p₀ v)‖ ^ 2)
    hK1 hD0 hs hρ1 (Finset.sum_nonneg fun a _ => sq_nonneg _) hPB
    hCG0 (momentConst_nonneg eta (by linarith)) (momentConst_nonneg eta (by norm_num))
    (sq_nonneg _)
    (bandAlpha_le sys hL hCΔ hΔ0 hΔD hK0) (Finset.sum_nonneg fun a _ => by positivity)
    (bandBeta_le sys Hunit hL (by linarith) hCΔ hΔ0 hΔD hK0 (by linarith))
    (Finset.sum_nonneg fun a _ => by positivity)
    (Real.rpow_le_rpow (by linarith) (by linarith) (by linarith))
    (Real.rpow_nonneg (by linarith) _) hc (sq_nonneg _) (gauss_tail_le hK1 ht0) (Real.exp_nonneg _)
    hN0 (sq_nonneg _) hNs (sq_nonneg _) hNh (sq_nonneg _)
  refine hcomb.trans (le_of_eq ?_)
  unfold Cband
  ring

/-- **eq:tavgU, first part**: the union tail beyond `K/2` is dominated by the hot projector at
`K/4`, so eq:tavg-quarter bounds its time average. -/
theorem tavg_half_explicit (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {n : ℕ} {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {s : ℝ} (hs : 3 / 2 < s) (hs2 : s ≤ 2)
    (hK : TavgScale sys L Hunit CΔ n) (p₀ : Fin eta) {Cg Ξ t : ℝ} (hCgΞ : 0 ≤ Cg * Ξ)
    (ht : 1 ≤ t) (v : En eta n) (hv : IsGood sys L Cg Ξ v) :
    (1 / t) * ∫ τ in (0 : ℝ)..t,
        ‖hotProj L (Kc L n / 2) (retFlow sys L n hΔsym τ (datum sys L p₀ v))‖ ^ 2 ≤
      Ctavg sys L Hunit CΔ s * (Cg * Ξ) ^ 2 * Kc L n ^ (2 * s - 6) *
        (1 + DK (Kc L n)) ^ (2 * s) := by
  refine le_trans ?_
    (tavg_quarter_explicit sys Hunit hL hPeriodic hΔsym hCΔ hΔb hs hs2 hK p₀ hCgΞ ht v hv)
  have ht0 : 0 < t := by linarith
  have hK0 : 0 < Kc L n := by linarith [hK.one_le_K]
  have hcont : ∀ l : ℝ, Continuous fun τ =>
      ‖hotProj L l (retFlow sys L n hΔsym τ (datum sys L p₀ v))‖ ^ 2 := fun l =>
    (((hotProj L l).continuous_of_finiteDimensional).comp
      (continuous_retFlow sys L n hΔsym _)).norm.pow 2
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on ht0.le ((hcont _).intervalIntegrable _ _)
    ((hcont _).intervalIntegrable _ _)
  intro τ _
  exact pow_le_pow_left₀ (norm_nonneg _) (hotProj_anti L (by linarith) _) 2

end BandExplicit

end FSGalerkin

/-! ## eq:phi-band at `s = t` -/

open Filter PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin NormedSpace FSNormal FSFlux

namespace FSBand

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type} [Fintype ν]

section PhiBand

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

omit [Fintype ν] in
lemma norm_emb_apply_le {x y : En eta n} (h : ∀ p, ‖x.ofLp p‖ ≤ ‖y.ofLp p‖) (q : Cf eta) :
    ‖emb eta n x q‖ ≤ ‖emb eta n y q‖ := by
  classical
  by_cases hq : ∃ p : Cfg eta n, finiteConfigLatticeIndex eta n p = q
  · obtain ⟨p, rfl⟩ := hq
    rw [emb_apply_index, emb_apply_index]
    exact h p
  · rw [emb_apply_eq_zero n x (fun p hp => absurd ⟨p, hp⟩ hq)]
    simp

omit [Fintype ν] in
/-- The band of `A_{p₀} χ` is dominated by the band of `(1 + A) χ`. -/
lemma shMask_bdatum_le (p₀ a : Fin eta) (sh : Lattice3 → Prop) (χ : En eta n) :
    ‖shMask a sh (emb eta n (FSSrc1.bdatum sys L p₀ χ))‖ ≤
      ‖shMask a sh (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ))‖ := by
  have h := l2_norm_le_of_le (shMask a sh (emb eta n (FSSrc1.bdatum sys L p₀ χ)))
    (shMask a sh (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ))) zero_le_one
    fun q => by
      rw [shMask_apply, shMask_apply, one_mul, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_emb_apply_le (FSSrc1.norm_bdatum_apply_le sys L p₀ χ) q) (norm_nonneg _)
  rwa [one_mul] at h

omit [Fintype ν] in
/-- A shell of width `2ϱ` is the union of two shells of width `ϱ`. -/
lemma norm_shMask_two_le {g : ℝ} (hg : 0 < g) (a : Fin eta) (cube : Bool) {lam ρ : ℝ}
    (hlam : 0 ≤ lam) (hρ : 0 < ρ) (x : L2 eta) :
    ‖shMask a (physSh cube g lam (2 * ρ)) x‖ ≤
      ‖shMask a (physSh cube g lam ρ) x‖ + ‖shMask a (physSh cube g (lam + ρ) ρ) x‖ := by
  classical
  have e : shMask a (physSh cube g lam (2 * ρ)) x =
      shMask a (physSh cube g lam ρ) x + shMask a (physSh cube g (lam + ρ) ρ) x := by
    ext q
    rw [lp.coeFn_add, Pi.add_apply, shMask_apply, shMask_apply, shMask_apply]
    have i1 := physSh_iff (cube := cube) hg hlam (by linarith : (0 : ℝ) < 2 * ρ) (q a)
    have i2 := physSh_iff (cube := cube) hg hlam hρ (q a)
    have i3 := physSh_iff (cube := cube) hg (by linarith : (0 : ℝ) ≤ lam + ρ) hρ (q a)
    have hsum : (lam + 2 * ρ) / g = (lam + ρ + ρ) / g := by ring
    have hmid : lam / g ≤ (lam + ρ) / g := div_le_div_of_nonneg_right (by linarith) hg.le
    by_cases h2 : physSh cube g lam ρ (q a)
    · have h1 : physSh cube g lam (2 * ρ) (q a) := by
        rw [i1, hsum]; rw [i2] at h2
        exact ⟨h2.1, lt_of_lt_of_le h2.2 (div_le_div_of_nonneg_right (by linarith) hg.le)⟩
      have h3 : ¬ physSh cube g (lam + ρ) ρ (q a) := by
        rw [i3]; rw [i2] at h2; intro h; linarith [h.1, h2.2]
      rw [if_pos h1, if_pos h2, if_neg h3]; ring
    · by_cases h3 : physSh cube g (lam + ρ) ρ (q a)
      · have h1 : physSh cube g lam (2 * ρ) (q a) := by
          rw [i1, hsum]; rw [i3] at h3
          exact ⟨le_trans hmid h3.1, h3.2⟩
        rw [if_pos h1, if_neg h2, if_pos h3]; ring
      · have h1 : ¬ physSh cube g lam (2 * ρ) (q a) := by
          rw [i1, hsum]; rw [i2] at h2; rw [i3] at h3
          intro h
          by_cases hc : rad cube (q a) < (lam + ρ) / g
          · exact h2 ⟨h.1, hc⟩
          · exact h3 ⟨not_lt.mp hc, h.2⟩
        rw [if_neg h1, if_neg h2, if_neg h3]; ring
  rw [e]
  exact norm_add_le _ _

include hKernel hL in
/-- **eq:phi-band at `s = t`** (range `1 ≤ ϱ ≤ K/2`, review S1): for `v = ψ_N(t)` (the Galerkin flow
`e^{iH_N τ} P ψ₀`) and for `v = P ψ(t)`, the band `K - ϱ ≤ |k_a| < K + ϱ` (Euclidean or cube;
on the cube this contains `[K - ϱ, K]`) of `φ_v(t) = A_{p₀} v` carries at most
`3 C Ξ K^{-1} ϱ^{1/2}`. -/
theorem phi_band_at_t (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hn : 2 ≤ n) (hK4 : 4 ≤ gF L * n) (D : EvoData L H) (t τ : ℝ) (p₀ a : Fin eta) (cube : Bool)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (hρK : ρ ≤ gF L * n / 2) :
    ‖shMask a (physSh cube (gF L) (gF L * n - ρ) (2 * ρ)) (emb eta n (FSSrc1.bdatum sys L p₀
        (retFlow sys L n (zero_isSymmetric (n := n)) τ (ext eta n (Sm eta L D.u₀)))))‖ ≤
        3 * bandN sys L Hunit * D.Xi * (gF L * n)⁻¹ * Real.sqrt ρ ∧
    ‖shMask a (physSh cube (gF L) (gF L * n - ρ) (2 * ρ)) (emb eta n (FSSrc1.bdatum sys L p₀
        (ext eta n (Sm eta L (traj H D t)))))‖ ≤
        3 * bandN sys L Hunit * D.Xi * (gF L * n)⁻¹ * Real.sqrt ρ := by
  have hg := gF_pos hL
  have hK0 : 0 < gF L * n := by linarith
  have hKg : 1 ≤ gF L * n := by linarith
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h2g : gF L * 2 ≤ gF L * n := mul_le_mul_of_nonneg_left hn' hg.le
  have hlam2 : 2 ≤ gF L * n - ρ := by linarith
  have hlamg : gF L ≤ gF L * n - ρ := by linarith
  have hρl : ρ ≤ gF L * n - ρ := by linarith
  have hlam0 : 0 ≤ gF L * n - ρ := by linarith
  have hK2 : 2 ≤ gF L * n := by linarith
  have hKgK : gF L ≤ gF L * n := by linarith
  have hρK' : ρ ≤ gF L * n := by linarith
  have hlam : (gF L * n - ρ)⁻¹ ≤ 2 * (gF L * n)⁻¹ := by
    have h1 : (gF L * n - ρ)⁻¹ ≤ (gF L * n / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    rwa [inv_div, div_eq_mul_inv] at h1
  have hKi : (gF L * n)⁻¹ ≤ 2 * (gF L * n)⁻¹ := by
    have : 0 ≤ (gF L * n)⁻¹ := inv_nonneg.mpr hK0.le
    linarith
  -- a generic state with both band bounds
  have key : ∀ χ : En eta n,
      ‖shMask a (physSh cube (gF L) (gF L * n - ρ) ρ)
          (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ))‖ ≤
        bandN sys L Hunit * D.Xi * (gF L * n - ρ)⁻¹ * Real.sqrt ρ →
      ‖shMask a (physSh cube (gF L) (gF L * n - ρ + ρ) ρ)
          (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ))‖ ≤
        bandN sys L Hunit * D.Xi * (gF L * n - ρ + ρ)⁻¹ * Real.sqrt ρ →
      ‖shMask a (physSh cube (gF L) (gF L * n - ρ) (2 * ρ))
          (emb eta n (FSSrc1.bdatum sys L p₀ χ))‖ ≤
        3 * bandN sys L Hunit * D.Xi * (gF L * n)⁻¹ * Real.sqrt ρ := by
    intro χ h1 h2
    rw [show gF L * n - ρ + ρ = gF L * n by ring] at h2
    have hX : 0 ≤ bandN sys L Hunit * D.Xi * Real.sqrt ρ := by
      have h0 : 0 ≤ bandN sys L Hunit * D.Xi * (gF L * n)⁻¹ * Real.sqrt ρ := (norm_nonneg _).trans h2
      have hKi0 : 0 < (gF L * n)⁻¹ := inv_pos.mpr hK0
      have : 0 ≤ bandN sys L Hunit * D.Xi * Real.sqrt ρ * (gF L * n)⁻¹ := by linarith
      exact nonneg_of_mul_nonneg_left this hKi0
    refine (shMask_bdatum_le sys p₀ a _ χ).trans ?_
    refine (norm_shMask_two_le hg a cube hlam0 (by linarith) _).trans ?_
    rw [show gF L * n - ρ + ρ = gF L * n by ring]
    have e1 := mul_le_mul_of_nonneg_left hlam hX
    have e2 := mul_le_mul_of_nonneg_left hKi hX
    nlinarith
  constructor
  · have hb1 := (band_galerkin sys hL H hKernel Hunit hPeriodic hKg D τ a cube hlam2 hlamg hρ
      hρl).1
    have hb2 := (band_galerkin sys hL H hKernel Hunit hPeriodic hKg D τ a cube
      (by linarith : (2 : ℝ) ≤ gF L * n - ρ + ρ) (by linarith : gF L ≤ gF L * n - ρ + ρ) hρ
      (by linarith : ρ ≤ gF L * n - ρ + ρ)).1
    exact key _ hb1 hb2
  · have hb1 := (band_backward sys hL H hKernel Hunit hPeriodic hKg D t 0 a cube hlam2 hlamg hρ
      hρl).1
    have hb2 := (band_backward sys hL H hKernel Hunit hPeriodic hKg D t 0 a cube
      (by linarith : (2 : ℝ) ≤ gF L * n - ρ + ρ) (by linarith : gF L ≤ gF L * n - ρ + ρ) hρ
      (by linarith : ρ ≤ gF L * n - ρ + ρ)).1
    rw [retFlow_zero] at hb1 hb2
    exact key _ hb1 hb2

end PhiBand

end FSBand
