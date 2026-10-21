import PlaneWave.FluxSourceSpin

/-!
# Kinetic completion, part 1: the inverse mismatch relative to one direction

Lattice estimates on `ℤ³` behind `lem:relativeD` of the completion note
(`kinetic_energy_completion.tex`). For a centre `c` (the drift of a hop), the mismatch
`F_c(τ) = |τ|² + 2τ·c` (`slabF`), transfers `τ` above the floor `|F_c(τ)| ≥ 2|τ|` and below the
cap `|F_c(τ)| < 2^{J+2}`, and a base point `z₀` (the directional coordinate of the fixed end of a
hop, so that the other end has coordinate `z₀ + τ`):

* `qd_ge_of_sep` (the separated geometry): if `|z₀ + τ| < |z₀|/8` and `|F_c(τ)| ≤ |z₀|²/128`, then
  `|τ + c| ≥ |z₀|/8`, for every centre `c`;
* `sep_row`: over the separated transfers, `⟨z₀⟩ Σ_τ |F_c(τ)|⁻¹ ⟨z₀ + τ⟩⁻² ≤ 55296 (J + 2)²`
  (dyadic shells of `z₀ + τ` and dyadic mismatch windows: `window_box_count` in the small windows,
  the box count in the large ones);
* **`inv_mismatch_row`**, **`inv_mismatch_col`** (eq:Drelative, in the two forms used by Schur's
  test with the weight `⟨·⟩⁻¹`): `⟨z₀⟩ Σ_τ |F_c(τ)|⁻¹ ⟨z₀ + τ⟩⁻² ≤ C_D (J + 2)²` and
  `Σ_τ |F_c(τ)|⁻¹ ⟨z₀ + τ⟩⁻¹ ≤ (C_D + 44000) (J + 2)²`, `C_D = 2300000`: away from the separated
  region the weights are at most `96/|τ|` (`near_weight_le`), and `sig3_core` applies;
* `wschur` (Schur's test with two test functions between finite sets), `sum_box_inv_le`
  (`Σ_{w ∈ box M} (1 + |w|²)⁻¹ ≤ 1 + 26 M`).

Here `⟨y⟩ = (1 + |y|²)^{1/2}`. The bounds are uniform in `c`, `z₀` and the finite set of transfers.
-/

set_option autoImplicit false

open Finset

namespace FSLattice

open FSChannel

/-! ## Elementary facts -/

lemma one_le_lsq_of_ne_zero {z : L3} (hz : z ≠ 0) : 1 ≤ lsq z := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  have h1 : (1 : ℝ) ≤ ((z i : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (z i) ^ 2 := by
      have := Int.one_le_abs hi
      nlinarith [sq_abs (z i)]
    exact_mod_cast this
  exact h1.trans (sq_le_lsq z i)

lemma one_le_lsq_of_pos {z : L3} (hz : 0 < lsq z) : 1 ≤ lsq z := by
  apply one_le_lsq_of_ne_zero
  rintro rfl
  rw [lsq_zero] at hz
  exact lt_irrefl _ hz

lemma lsq_add_le (a b : L3) : lsq (a + b) ≤ 2 * lsq a + 2 * lsq b := by
  simp only [lsq, Pi.add_apply, Int.cast_add]
  nlinarith [sq_nonneg ((a 0 : ℝ) - b 0), sq_nonneg ((a 1 : ℝ) - b 1),
    sq_nonneg ((a 2 : ℝ) - b 2)]

lemma lsq_neg' (a : L3) : lsq (-a) = lsq a := by
  simp only [lsq, Pi.neg_apply, Int.cast_neg, neg_sq]

/-- A dyadic window: every `x ≥ 1` lies in some `[2^m, 2^{m+1})`. -/
lemma exists_dyadic {x : ℝ} (hx : 1 ≤ x) : ∃ m : ℕ, (2 : ℝ) ^ m ≤ x ∧ x < 2 ^ (m + 1) := by
  set k := ⌊x⌋₊ with hk
  have hk1 : 1 ≤ k := Nat.le_floor (by exact_mod_cast hx)
  refine ⟨Nat.log 2 k, ?_, ?_⟩
  · have h1 : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 ^ Nat.log 2 k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by linarith))
  · have h1 : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
    have h2 : k + 1 ≤ 2 ^ (Nat.log 2 k + 1) := h1
    have h3 : ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 k + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    have h4 : x < (k : ℝ) + 1 := Nat.lt_floor_add_one x
    linarith

/-! ## The separated geometry -/

/-- **The separated geometry**: if `64 |z₀ + τ|² < |z₀|²` and `|F_c(τ)| ≤ |z₀|²/128`, then
`|τ + c|² ≥ |z₀|²/64`, for every centre `c`. -/
lemma qd_ge_of_sep (c : Fin 3 → ℝ) (z₀ τ : L3) (hw : 64 * lsq (z₀ + τ) < lsq z₀)
    (hF : |slabF c τ| ≤ lsq z₀ / 128) : lsq z₀ / 64 ≤ qd c τ := by
  by_contra hq
  push Not at hq
  have hqe := qd_eq c τ
  have key : ∀ i, (z₀ i : ℝ) ^ 2 / 2 - 2 * ((z₀ i : ℝ) + τ i) ^ 2 - 2 * ((τ i : ℝ) + c i) ^ 2 ≤
      c i ^ 2 := fun i => by
    nlinarith [sq_nonneg ((z₀ i : ℝ) + 2 * (((τ i : ℝ) + c i) - ((z₀ i : ℝ) + τ i))),
      sq_nonneg (((τ i : ℝ) + c i) + ((z₀ i : ℝ) + τ i))]
  have hl0 : lsq z₀ = (z₀ 0 : ℝ) ^ 2 + (z₀ 1 : ℝ) ^ 2 + (z₀ 2 : ℝ) ^ 2 := rfl
  have hl1 : lsq (z₀ + τ) = ((z₀ 0 : ℝ) + τ 0) ^ 2 + ((z₀ 1 : ℝ) + τ 1) ^ 2 +
      ((z₀ 2 : ℝ) + τ 2) ^ 2 := by
    simp only [lsq, Pi.add_apply, Int.cast_add]
  have hqd : qd c τ = ((τ 0 : ℝ) + c 0) ^ 2 + ((τ 1 : ℝ) + c 1) ^ 2 + ((τ 2 : ℝ) + c 2) ^ 2 := by
    unfold qd; rw [Fin.sum_univ_three]
  have hcs : ∑ i, c i ^ 2 = c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2 := Fin.sum_univ_three _
  have hlz : 0 < lsq z₀ := by have := lsq_nonneg (z₀ + τ); linarith
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  have hF' := (abs_le.mp hF).1
  rw [hcs] at hqe
  linarith

/-! ## The separated sum -/

/-- The shell predicate for `w = z₀ + τ`: `|w|² ≤ 4^i`, and `|w|² ≥ 4^{i-1}` when `i ≥ 1`. -/
abbrev shellP (z₀ : L3) (i : ℕ) (τ : L3) : Prop :=
  lsq (z₀ + τ) ≤ 4 ^ i ∧ (i = 0 ∨ (4 : ℝ) ^ (i - 1) ≤ lsq (z₀ + τ))

/-- The window predicate `2^m ≤ |F_c(τ)| < 2^{m+1}`. -/
abbrev winP (c : Fin 3 → ℝ) (m : ℕ) (τ : L3) : Prop :=
  (2 : ℝ) ^ m ≤ |slabF c τ| ∧ |slabF c τ| < 2 ^ (m + 1)

lemma exists_shellP (z₀ τ : L3) : ∃ i, shellP z₀ i τ := by
  by_cases h : lsq (z₀ + τ) ≤ 1
  · exact ⟨0, by simpa [shellP] using h⟩
  · push Not at h
    obtain ⟨i, hi1, hi2⟩ := FSNormal.exists_shell h.le
    exact ⟨i + 1, hi2, Or.inr (by simpa using hi1)⟩

/-- In shell `i`, `w ∈ box 2^i` and `(1 + |w|²)⁻¹ ≤ 4/4^i`. -/
lemma shellP_facts {z₀ τ : L3} {i : ℕ} (h : shellP z₀ i τ) :
    z₀ + τ ∈ box (2 ^ i) ∧ 1 / (1 + lsq (z₀ + τ)) ≤ 4 / 4 ^ i := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨mem_box_of_lsq_le (by push_cast; rw [FSBand.two_pow_sq]; exact h1), ?_⟩
  have hl := lsq_nonneg (z₀ + τ)
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    rw [pow_zero, div_one, div_le_iff₀ (by linarith)]
    linarith
  · rcases h2 with h2 | h2
    · omega
    · have e : (4 : ℝ) ^ i = 4 * 4 ^ (i - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e, div_mul_cancel_left₀ (by norm_num : (4 : ℝ) ≠ 0), one_div]
      exact inv_anti₀ (by positivity) (by linarith)

/-- `√(1 + x) ≤ 2 √x` for `x ≥ 1`. -/
lemma sqrt_one_add_le {x : ℝ} (hx : 1 ≤ x) : Real.sqrt (1 + x) ≤ 2 * Real.sqrt x := by
  have h : Real.sqrt (1 + x) ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
  rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  exact h

/-- Hypotheses of the separated sum: floor, cap, and `64 |z₀ + τ|² < |z₀|²`. -/
abbrev SepHyp (c : Fin 3 → ℝ) (z₀ : L3) (J : ℕ) (τ : L3) : Prop :=
  1 ≤ lsq τ ∧ 2 * rho τ ≤ |slabF c τ| ∧ |slabF c τ| < 2 ^ (J + 1) * 2 ∧
    64 * lsq (z₀ + τ) < lsq z₀

lemma sepHyp_lsq_tau {c : Fin 3 → ℝ} {z₀ : L3} {J : ℕ} {τ : L3} (h : SepHyp c z₀ J τ) :
    31 / 64 * lsq z₀ < lsq τ := by
  obtain ⟨-, -, -, hw⟩ := h
  have e : z₀ = (z₀ + τ) + -τ := by abel
  have h1 := lsq_add_le (z₀ + τ) (-τ)
  rw [← e, lsq_neg'] at h1
  linarith

lemma sepHyp_F_gt {c : Fin 3 → ℝ} {z₀ : L3} {J : ℕ} {τ : L3} (h : SepHyp c z₀ J τ) :
    Real.sqrt (lsq z₀) < |slabF c τ| := by
  have h1 := sepHyp_lsq_tau h
  obtain ⟨-, hfl, -, -⟩ := h
  have h4 : Real.sqrt (lsq z₀) < 2 * rho τ := by
    have e : 2 * rho τ = Real.sqrt (4 * lsq τ) := by
      rw [rho, Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    rw [e]
    apply Real.sqrt_lt_sqrt (lsq_nonneg _)
    have := lsq_nonneg z₀
    linarith
  exact lt_of_lt_of_le h4 hfl

lemma sepHyp_shell_le {c : Fin 3 → ℝ} {z₀ : L3} {J : ℕ} {τ : L3} (h : SepHyp c z₀ J τ) {i : ℕ}
    (hi : shellP z₀ i τ) : i ≤ J := by
  have h1 := sepHyp_lsq_tau h
  obtain ⟨-, hfl, hcap, hw⟩ := h
  have hρ : rho τ < 2 ^ (J + 1) := by
    have : 2 * rho τ < 2 ^ (J + 1) * 2 := lt_of_le_of_lt hfl hcap
    linarith
  have hl : lsq τ < 4 ^ (J + 1) := by
    rw [← rho_sq, ← FSBand.two_pow_sq]
    exact pow_lt_pow_left₀ hρ (rho_nonneg τ) two_ne_zero
  have hw4 : lsq (z₀ + τ) < 4 ^ J := by
    have e : (4 : ℝ) ^ (J + 1) = 4 * 4 ^ J := by rw [pow_succ']
    have h2 := lsq_add_le (z₀ + τ) (-τ)
    have e2 : z₀ + τ + -τ = z₀ := by abel
    rw [e2, lsq_neg'] at h2
    have := lsq_nonneg (z₀ + τ)
    have : (0 : ℝ) ≤ 4 ^ J := by positivity
    linarith
  obtain ⟨-, hi2⟩ := hi
  rcases hi2 with rfl | hi2
  · omega
  · by_contra hJ
    push Not at hJ
    have : (4 : ℝ) ^ J ≤ 4 ^ (i - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith

lemma sepHyp_win_le {c : Fin 3 → ℝ} {z₀ : L3} {J : ℕ} {τ : L3} (h : SepHyp c z₀ J τ) {m : ℕ}
    (hm : winP c m τ) : m ≤ J + 1 := by
  obtain ⟨-, -, hcap, -⟩ := h
  obtain ⟨hm1, -⟩ := hm
  by_contra hJ
  push Not at hJ
  have : (2 : ℝ) ^ (J + 1) * 2 ≤ 2 ^ m := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

lemma sepHyp_exists_win {c : Fin 3 → ℝ} {z₀ : L3} {J : ℕ} {τ : L3} (h : SepHyp c z₀ J τ) :
    ∃ m, winP c m τ := by
  obtain ⟨h1, hfl, -, -⟩ := h
  have hρ : 1 ≤ rho τ := one_le_rho h1
  exact exists_dyadic (by linarith)

/-- **One block of the separated sum** (shell `i`, window `m`). -/
lemma sep_block (c : Fin 3 → ℝ) (z₀ : L3) {J : ℕ} (i m : ℕ) (B : Finset L3)
    (hB : ∀ τ ∈ B, SepHyp c z₀ J τ ∧ shellP z₀ i τ ∧ winP c m τ) :
    Real.sqrt (1 + lsq z₀) * ∑ τ ∈ B, 1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ))) ≤ 55296 := by
  rcases B.eq_empty_or_nonempty with rfl | ⟨τ₁, hτ₁⟩
  · simp
  obtain ⟨h₁, hsh₁, hwin₁⟩ := hB τ₁ hτ₁
  have hlz : 0 < lsq z₀ := by
    have := lsq_nonneg (z₀ + τ₁); have := h₁.2.2.2; linarith
  have hlz1 : 1 ≤ lsq z₀ := one_le_lsq_of_pos hlz
  set R := Real.sqrt (lsq z₀) with hR
  have hR1 : 1 ≤ R := by rw [hR, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlz1
  have hR0 : 0 < R := by linarith
  have hRsq : R ^ 2 = lsq z₀ := Real.sq_sqrt (lsq_nonneg _)
  -- each term
  have hterm : ∀ τ ∈ B, 1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ))) ≤
      1 / 2 ^ m * (4 / 4 ^ i) := by
    intro τ hτ
    obtain ⟨-, hsh, hwin⟩ := hB τ hτ
    have hF : (2 : ℝ) ^ m ≤ |slabF c τ| := hwin.1
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    exact mul_le_mul (one_div_le_one_div_of_le hp hF) (shellP_facts hsh).2 (by
      have := lsq_nonneg (z₀ + τ); positivity) (by positivity)
  have hsum : ∑ τ ∈ B, 1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ))) ≤
      (B.card : ℝ) * (1 / 2 ^ m * (4 / 4 ^ i)) := by
    refine (sum_le_sum hterm).trans (le_of_eq ?_)
    rw [sum_const, nsmul_eq_mul]
  have hsq : Real.sqrt (1 + lsq z₀) ≤ 2 * R := sqrt_one_add_le hlz1
  -- `2^m > R/2`
  have hmR : R < 2 ^ (m + 1) := lt_trans (sepHyp_F_gt h₁) hwin₁.2
  -- `2^i ≤ R`
  have hiR : (2 : ℝ) ^ i ≤ R := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; simpa using hR1
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      have hk : (4 : ℝ) ^ k ≤ lsq (z₀ + τ₁) := by
        rcases hsh₁.2 with h | h
        · omega
        · simpa using h
      rw [hR]
      apply Real.le_sqrt_of_sq_le
      rw [FSBand.two_pow_sq, pow_succ]
      have hw := h₁.2.2.2
      linarith
  have h4i : (0 : ℝ) < 4 ^ i := by positivity
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hB0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hfac : (0 : ℝ) ≤ 1 / 2 ^ m * (4 / 4 ^ i) := by positivity
  by_cases hsmall : (2 : ℝ) ^ (m + 1) ≤ lsq z₀ / 128
  · -- small window: `window_box_count` on both signs
    set Bp := B.filter (fun τ => 0 ≤ slabF c τ)
    set Bn := B.filter (fun τ => ¬ 0 ≤ slabF c τ)
    have hcard : (B.card : ℝ) = Bp.card + Bn.card := by
      rw [← Nat.cast_add, card_filter_add_card_filter_not]
    have hr₀ : (0 : ℝ) < R / 8 := by positivity
    have hr₀sq : (R / 8) ^ 2 = lsq z₀ / 64 := by rw [div_pow, hRsq]; norm_num
    have hqd : ∀ τ ∈ B, (R / 8) ^ 2 ≤ qd c τ := by
      intro τ hτ
      obtain ⟨hh, -, hwin⟩ := hB τ hτ
      rw [hr₀sq]
      refine qd_ge_of_sep c z₀ τ hh.2.2.2 ?_
      have := hwin.2
      linarith
    have hbox : ∀ τ ∈ B, τ - (-z₀) ∈ box (2 ^ i) := by
      intro τ hτ
      have := (shellP_facts (hB τ hτ).2.1).1
      rwa [sub_neg_eq_add, add_comm]
    have hp : (Bp.card : ℝ) ≤ 6 * (2 * ((2 ^ i : ℕ) : ℝ) + 1) ^ 2 *
        ((2 ^ (m + 1) - 2 ^ m) * Real.sqrt 3 / (2 * (R / 8)) + 1) := by
      apply window_box_count (a := 2 ^ m) (b := 2 ^ (m + 1)) c (-z₀) (2 ^ i) hr₀
        (pow_le_pow_right₀ (by norm_num) (by omega)) Bp
      intro τ hτ
      obtain ⟨hτB, hpos⟩ := mem_filter.mp hτ
      obtain ⟨-, -, hwin⟩ := hB τ hτB
      refine ⟨hbox τ hτB, ?_, ?_, hqd τ hτB⟩
      · have := hwin.1; rw [abs_of_nonneg hpos] at this; exact this
      · have := hwin.2; rw [abs_of_nonneg hpos] at this; exact this.le
    have hn : (Bn.card : ℝ) ≤ 6 * (2 * ((2 ^ i : ℕ) : ℝ) + 1) ^ 2 *
        ((-(2 : ℝ) ^ m - -2 ^ (m + 1)) * Real.sqrt 3 / (2 * (R / 8)) + 1) := by
      apply window_box_count (a := -2 ^ (m + 1)) (b := -2 ^ m) c (-z₀) (2 ^ i) hr₀
        (by have : (2 : ℝ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
            linarith) Bn
      intro τ hτ
      obtain ⟨hτB, hneg⟩ := mem_filter.mp hτ
      push Not at hneg
      obtain ⟨-, -, hwin⟩ := hB τ hτB
      refine ⟨hbox τ hτB, ?_, ?_, hqd τ hτB⟩
      · have := hwin.2; rw [abs_of_neg hneg] at this; linarith
      · have := hwin.1; rw [abs_of_neg hneg] at this; linarith
    have e1 : ((2 : ℝ) ^ (m + 1) - 2 ^ m) = 2 ^ m := by rw [pow_succ]; ring
    have e2 : (-(2 : ℝ) ^ m - -2 ^ (m + 1)) = 2 ^ m := by rw [pow_succ]; ring
    rw [e1] at hp
    rw [e2] at hn
    have hc : ((2 ^ i : ℕ) : ℝ) = 2 ^ i := by push_cast; ring
    rw [hc] at hp hn
    have hs3 : Real.sqrt 3 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hs30 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have h2i : (2 * (2 : ℝ) ^ i + 1) ^ 2 ≤ 9 * 4 ^ i := by
      have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      have h3 : 2 * (2 : ℝ) ^ i + 1 ≤ 3 * 2 ^ i := by linarith
      calc (2 * (2 : ℝ) ^ i + 1) ^ 2 ≤ (3 * 2 ^ i) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
        _ = 9 * 4 ^ i := by rw [mul_pow, FSBand.two_pow_sq]; norm_num
    -- the count times `2^{-m}`
    have hm' : 1 / (2 : ℝ) ^ m < 2 / R := by
      rw [div_lt_div_iff₀ h2m hR0]
      have : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
      linarith
    have hA : (2 : ℝ) ^ m * Real.sqrt 3 / (2 * (R / 8)) * (1 / 2 ^ m) ≤ 8 / R := by
      rw [show (2 : ℝ) ^ m * Real.sqrt 3 / (2 * (R / 8)) * (1 / 2 ^ m) =
        4 * Real.sqrt 3 / R by field_simp; ring]
      rw [div_le_div_iff_of_pos_right hR0]
      linarith
    have hcnt : (B.card : ℝ) * (1 / 2 ^ m) ≤ 12 * (9 * 4 ^ i) * (8 / R + 2 / R) := by
      rw [hcard]
      have hX : 0 ≤ (2 : ℝ) ^ m * Real.sqrt 3 / (2 * (R / 8)) + 1 := by positivity
      calc ((Bp.card : ℝ) + Bn.card) * (1 / 2 ^ m)
          ≤ (6 * (2 * 2 ^ i + 1) ^ 2 * ((2 : ℝ) ^ m * Real.sqrt 3 / (2 * (R / 8)) + 1) +
              6 * (2 * 2 ^ i + 1) ^ 2 * ((2 : ℝ) ^ m * Real.sqrt 3 / (2 * (R / 8)) + 1)) *
            (1 / 2 ^ m) := by
            apply mul_le_mul_of_nonneg_right (add_le_add hp hn) (by positivity)
        _ = 12 * (2 * 2 ^ i + 1) ^ 2 * ((2 : ℝ) ^ m * Real.sqrt 3 / (2 * (R / 8)) * (1 / 2 ^ m) +
              1 / 2 ^ m) := by ring
        _ ≤ 12 * (9 * 4 ^ i) * (8 / R + 2 / R) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h2i (by norm_num))
              (add_le_add hA hm'.le) (by positivity) (by positivity)
    calc Real.sqrt (1 + lsq z₀) * ∑ τ ∈ B, 1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ)))
        ≤ 2 * R * ((B.card : ℝ) * (1 / 2 ^ m * (4 / 4 ^ i))) :=
          mul_le_mul hsq hsum (sum_nonneg fun τ _ => by
            have := lsq_nonneg (z₀ + τ); positivity) (by positivity)
      _ = 2 * R * (4 / 4 ^ i) * ((B.card : ℝ) * (1 / 2 ^ m)) := by ring
      _ ≤ 2 * R * (4 / 4 ^ i) * (12 * (9 * 4 ^ i) * (8 / R + 2 / R)) :=
          mul_le_mul_of_nonneg_left hcnt (by positivity)
      _ = 8640 := by field_simp; ring
      _ ≤ 55296 := by norm_num
  · -- large window: the box count
    push Not at hsmall
    have hcard : (B.card : ℝ) ≤ (2 * 2 ^ i + 1) ^ 3 := by
      have hsub : B.image (fun τ => z₀ + τ) ⊆ box (2 ^ i) := by
        intro w hw
        obtain ⟨τ, hτ, rfl⟩ := mem_image.mp hw
        exact (shellP_facts (hB τ hτ).2.1).1
      have hinj : Set.InjOn (fun τ => z₀ + τ) B := fun a _ b _ h => add_left_cancel h
      have h1 := card_le_card hsub
      rw [card_image_of_injOn hinj, card_box] at h1
      have h2 : ((B.card : ℕ) : ℝ) ≤ (((2 * 2 ^ i + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at h2
      exact h2
    have h2i : (2 * (2 : ℝ) ^ i + 1) ^ 3 ≤ 27 * (2 ^ i) ^ 3 := by
      have h1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      have h3 : 2 * (2 : ℝ) ^ i + 1 ≤ 3 * 2 ^ i := by linarith
      calc (2 * (2 : ℝ) ^ i + 1) ^ 3 ≤ (3 * 2 ^ i) ^ 3 := pow_le_pow_left₀ (by positivity) h3 3
        _ = 27 * (2 ^ i) ^ 3 := by ring
    have hm' : 1 / (2 : ℝ) ^ m < 256 / lsq z₀ := by
      rw [div_lt_div_iff₀ h2m hlz]
      have : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
      linarith
    calc Real.sqrt (1 + lsq z₀) * ∑ τ ∈ B, 1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ)))
        ≤ 2 * R * ((B.card : ℝ) * (1 / 2 ^ m * (4 / 4 ^ i))) :=
          mul_le_mul hsq hsum (sum_nonneg fun τ _ => by
            have := lsq_nonneg (z₀ + τ); positivity) (by positivity)
      _ = 2 * R * (4 / 4 ^ i) * (B.card : ℝ) * (1 / 2 ^ m) := by ring
      _ ≤ 2 * R * (4 / 4 ^ i) * (27 * (2 ^ i) ^ 3) * (256 / lsq z₀) := by
          apply mul_le_mul _ hm'.le (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (hcard.trans h2i) (by positivity)
      _ = 55296 * 2 ^ i / R := by
          rw [← hRsq, ← FSBand.two_pow_sq]
          field_simp
          ring
      _ ≤ 55296 := by
          rw [div_le_iff₀ hR0]
          linarith

/-- **The separated sum**: over transfers with `64 |z₀ + τ|² < |z₀|²`,
`⟨z₀⟩ Σ_τ |F_c(τ)|⁻¹ ⟨z₀ + τ⟩⁻² ≤ 55296 (J + 2)²`. -/
theorem sep_row (c : Fin 3 → ℝ) (z₀ : L3) {J : ℕ} (T : Finset L3)
    (hT : ∀ τ ∈ T, SepHyp c z₀ J τ) :
    Real.sqrt (1 + lsq z₀) * ∑ τ ∈ T, 1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ))) ≤
      55296 * (J + 2) ^ 2 := by
  set f : L3 → ℝ := fun τ => 1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ))) with hf
  have hf0 : ∀ τ, 0 ≤ f τ := fun τ => by
    have := lsq_nonneg (z₀ + τ); simp only [hf]; positivity
  have h1 : ∑ τ ∈ T, f τ ≤ ∑ i ∈ range (J + 1), ∑ τ ∈ T.filter (shellP z₀ i), f τ :=
    sum_le_sum_shells T f (fun τ _ => hf0 τ) (shellP z₀) J (fun τ hτ => by
      obtain ⟨i, hi⟩ := exists_shellP z₀ τ
      exact ⟨i, sepHyp_shell_le (hT τ hτ) hi, hi⟩)
  have h2 : ∀ i ∈ range (J + 1), ∑ τ ∈ T.filter (shellP z₀ i), f τ ≤
      ∑ m ∈ range (J + 1 + 1), ∑ τ ∈ (T.filter (shellP z₀ i)).filter (winP c m), f τ :=
    fun i _ => sum_le_sum_shells _ f (fun τ _ => hf0 τ) (winP c) (J + 1) (fun τ hτ => by
      have hh := hT τ (mem_filter.mp hτ).1
      obtain ⟨m, hm⟩ := sepHyp_exists_win hh
      exact ⟨m, sepHyp_win_le hh hm, hm⟩)
  have h3 : ∀ i ∈ range (J + 1), ∀ m ∈ range (J + 1 + 1),
      Real.sqrt (1 + lsq z₀) * ∑ τ ∈ (T.filter (shellP z₀ i)).filter (winP c m), f τ ≤ 55296 :=
    fun i _ m _ => sep_block c z₀ i m _ (fun τ hτ => by
      obtain ⟨hτ', hw⟩ := mem_filter.mp hτ
      obtain ⟨hτT, hs⟩ := mem_filter.mp hτ'
      exact ⟨hT τ hτT, hs, hw⟩)
  have hsq0 : 0 ≤ Real.sqrt (1 + lsq z₀) := Real.sqrt_nonneg _
  calc Real.sqrt (1 + lsq z₀) * ∑ τ ∈ T, f τ
      ≤ Real.sqrt (1 + lsq z₀) * ∑ i ∈ range (J + 1), ∑ m ∈ range (J + 1 + 1),
          ∑ τ ∈ (T.filter (shellP z₀ i)).filter (winP c m), f τ :=
        mul_le_mul_of_nonneg_left (h1.trans (sum_le_sum h2)) hsq0
    _ = ∑ i ∈ range (J + 1), ∑ m ∈ range (J + 1 + 1),
          Real.sqrt (1 + lsq z₀) * ∑ τ ∈ (T.filter (shellP z₀ i)).filter (winP c m), f τ := by
        rw [mul_sum]; exact sum_congr rfl fun i _ => mul_sum _ _ _
    _ ≤ ∑ _i ∈ range (J + 1), ∑ _m ∈ range (J + 1 + 1), (55296 : ℝ) :=
        sum_le_sum fun i hi => sum_le_sum fun m hm => h3 i hi m hm
    _ = 55296 * ((J + 1) * (J + 2)) := by
        rw [sum_const, sum_const, card_range, card_range, nsmul_eq_mul, nsmul_eq_mul]
        push_cast; ring
    _ ≤ 55296 * (J + 2) ^ 2 := by
        have : ((J : ℝ) + 1) * (J + 2) ≤ (J + 2) ^ 2 := by nlinarith
        linarith

/-! ## The inverse mismatch relative to one direction -/

/-- The constant of eq:Drelative. -/
def CD : ℝ := 2300000

/-- Hypotheses of the core sums: floor and cap. -/
abbrev CoreHyp (c : Fin 3 → ℝ) (J : ℕ) (τ : L3) : Prop :=
  1 ≤ lsq τ ∧ 2 * rho τ ≤ |slabF c τ| ∧ |slabF c τ| < 2 ^ (J + 1) * 2

/-- Away from the separated region the row weight is at most `96/|τ|`. -/
lemma near_weight_le (z₀ τ : L3) (h1 : 1 ≤ lsq τ) (hnear : lsq z₀ ≤ 64 * lsq (z₀ + τ)) :
    Real.sqrt (1 + lsq z₀) * (1 / (1 + lsq (z₀ + τ))) ≤ 96 * (1 / rho τ) := by
  set W := lsq (z₀ + τ)
  set Z := lsq z₀
  have hW := lsq_nonneg (z₀ + τ)
  have hZ := lsq_nonneg z₀
  have hτ : lsq τ ≤ 2 * W + 2 * Z := by
    have e : τ = (z₀ + τ) + -z₀ := by abel
    have h := lsq_add_le (z₀ + τ) (-z₀)
    rw [← e, lsq_neg'] at h
    exact h
  have hρ : 0 < rho τ := lt_of_lt_of_le one_pos (one_le_rho h1)
  have hprod : rho τ * Real.sqrt (1 + Z) ≤ 96 * (1 + W) := by
    rw [rho, ← Real.sqrt_mul (lsq_nonneg τ)]
    rw [show 96 * (1 + W) = Real.sqrt ((96 * (1 + W)) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have h2 : lsq τ ≤ 130 * (1 + W) := by linarith
    have h3 : 1 + Z ≤ 64 * (1 + W) := by linarith
    calc lsq τ * (1 + Z) ≤ (130 * (1 + W)) * (64 * (1 + W)) :=
          mul_le_mul h2 h3 (by linarith) (by positivity)
      _ ≤ (96 * (1 + W)) ^ 2 := by nlinarith
  have hW1 : 0 < 1 + W := by linarith
  rw [mul_one_div, mul_one_div, div_le_div_iff₀ hW1 hρ]
  linarith

/-- **eq:Drelative, row form**: `⟨z₀⟩ Σ_τ |F_c(τ)|⁻¹ ⟨z₀ + τ⟩⁻² ≤ C_D (J + 2)²`. -/
theorem inv_mismatch_row (c : Fin 3 → ℝ) (z₀ : L3) {J : ℕ} (T : Finset L3)
    (hT : ∀ τ ∈ T, CoreHyp c J τ) :
    Real.sqrt (1 + lsq z₀) * ∑ τ ∈ T, 1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ))) ≤
      CD * (J + 2) ^ 2 := by
  set f : L3 → ℝ := fun τ => 1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ))) with hf
  set Tf := T.filter (fun τ => 64 * lsq (z₀ + τ) < lsq z₀)
  set Tn := T.filter (fun τ => ¬ 64 * lsq (z₀ + τ) < lsq z₀)
  have hsplit : ∑ τ ∈ T, f τ = ∑ τ ∈ Tf, f τ + ∑ τ ∈ Tn, f τ :=
    (sum_filter_add_sum_filter_not T _ f).symm
  have hfar : Real.sqrt (1 + lsq z₀) * ∑ τ ∈ Tf, f τ ≤ 55296 * (J + 2) ^ 2 :=
    sep_row c z₀ Tf (fun τ hτ => by
      obtain ⟨hτT, hw⟩ := mem_filter.mp hτ
      obtain ⟨h1, h2, h3⟩ := hT τ hτT
      exact ⟨h1, h2, h3, hw⟩)
  have hnear : Real.sqrt (1 + lsq z₀) * ∑ τ ∈ Tn, f τ ≤
      96 * (11000 * (2 * J + 3) * (J + 1)) := by
    rw [mul_sum]
    calc ∑ τ ∈ Tn, Real.sqrt (1 + lsq z₀) * f τ
        ≤ ∑ τ ∈ Tn, 96 * (1 / |slabF c τ| * (1 / rho τ)) := by
          refine sum_le_sum fun τ hτ => ?_
          obtain ⟨hτT, hw⟩ := mem_filter.mp hτ
          push Not at hw
          have h1 := (hT τ hτT).1
          have hw' := near_weight_le z₀ τ h1 hw
          have hF : 0 ≤ 1 / |slabF c τ| := by positivity
          calc Real.sqrt (1 + lsq z₀) * f τ =
              1 / |slabF c τ| * (Real.sqrt (1 + lsq z₀) * (1 / (1 + lsq (z₀ + τ)))) := by
                simp only [hf]; ring
            _ ≤ 1 / |slabF c τ| * (96 * (1 / rho τ)) := mul_le_mul_of_nonneg_left hw' hF
            _ = 96 * (1 / |slabF c τ| * (1 / rho τ)) := by ring
      _ = 96 * ∑ τ ∈ Tn, 1 / |slabF c τ| * (1 / rho τ) := by rw [mul_sum]
      _ ≤ 96 * (11000 * (2 * J + 3) * (J + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact sig3_core c Tn (fun τ hτ => hT τ (mem_filter.mp hτ).1)
  rw [hsplit, mul_add]
  have hJ : (96 : ℝ) * (11000 * (2 * J + 3) * (J + 1)) ≤ 2112000 * (J + 2) ^ 2 := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have hJ2 : (0 : ℝ) ≤ (J + 2) ^ 2 := by positivity
  unfold CD
  linarith

/-- **eq:Drelative, column form**: `Σ_τ |F_c(τ)|⁻¹ ⟨z₀ + τ⟩⁻¹ ≤ C_D (J + 2)²`... with the constant
`C_D + 44000`. -/
theorem inv_mismatch_col (c : Fin 3 → ℝ) (z₀ : L3) {J : ℕ} (T : Finset L3)
    (hT : ∀ τ ∈ T, CoreHyp c J τ) :
    ∑ τ ∈ T, 1 / |slabF c τ| * (1 / Real.sqrt (1 + lsq (z₀ + τ))) ≤
      (CD + 44000) * (J + 2) ^ 2 := by
  set g : L3 → ℝ := fun τ => 1 / |slabF c τ| * (1 / Real.sqrt (1 + lsq (z₀ + τ))) with hg
  set Th := T.filter (fun τ => lsq z₀ ≤ lsq (z₀ + τ))
  set Tl := T.filter (fun τ => ¬ lsq z₀ ≤ lsq (z₀ + τ))
  have hsplit : ∑ τ ∈ T, g τ = ∑ τ ∈ Th, g τ + ∑ τ ∈ Tl, g τ :=
    (sum_filter_add_sum_filter_not T _ g).symm
  have hhigh : ∑ τ ∈ Th, g τ ≤ 2 * (11000 * (2 * J + 3) * (J + 1)) := by
    calc ∑ τ ∈ Th, g τ ≤ ∑ τ ∈ Th, 2 * (1 / |slabF c τ| * (1 / rho τ)) := by
          refine sum_le_sum fun τ hτ => ?_
          obtain ⟨hτT, hw⟩ := mem_filter.mp hτ
          have h1 := (hT τ hτT).1
          have hρ : 0 < rho τ := lt_of_lt_of_le one_pos (one_le_rho h1)
          have hτ : lsq τ ≤ 4 * (1 + lsq (z₀ + τ)) := by
            have e : τ = (z₀ + τ) + -z₀ := by abel
            have h := lsq_add_le (z₀ + τ) (-z₀)
            rw [← e, lsq_neg'] at h
            linarith
          have hs : rho τ ≤ 2 * Real.sqrt (1 + lsq (z₀ + τ)) := by
            rw [rho, show (2 : ℝ) = Real.sqrt 4 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
              ← Real.sqrt_mul (by norm_num)]
            exact Real.sqrt_le_sqrt hτ
          have hs0 : 0 < Real.sqrt (1 + lsq (z₀ + τ)) := by
            apply Real.sqrt_pos.mpr; have := lsq_nonneg (z₀ + τ); linarith
          have hF : 0 ≤ 1 / |slabF c τ| := by positivity
          simp only [hg]
          rw [show 2 * (1 / |slabF c τ| * (1 / rho τ)) = 1 / |slabF c τ| * (2 / rho τ) by ring]
          apply mul_le_mul_of_nonneg_left _ hF
          rw [div_le_div_iff₀ hs0 hρ]
          linarith
      _ = 2 * ∑ τ ∈ Th, 1 / |slabF c τ| * (1 / rho τ) := by rw [mul_sum]
      _ ≤ 2 * (11000 * (2 * J + 3) * (J + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact sig3_core c Th (fun τ hτ => hT τ (mem_filter.mp hτ).1)
  have hlow : ∑ τ ∈ Tl, g τ ≤ CD * (J + 2) ^ 2 := by
    have hB := inv_mismatch_row c z₀ T hT
    refine le_trans ?_ hB
    rw [mul_sum]
    calc ∑ τ ∈ Tl, g τ ≤ ∑ τ ∈ Tl, Real.sqrt (1 + lsq z₀) *
          (1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ)))) := by
          refine sum_le_sum fun τ hτ => ?_
          obtain ⟨-, hw⟩ := mem_filter.mp hτ
          push Not at hw
          have hW := lsq_nonneg (z₀ + τ)
          have hs0 : 0 < Real.sqrt (1 + lsq (z₀ + τ)) := Real.sqrt_pos.mpr (by linarith)
          have hss : Real.sqrt (1 + lsq (z₀ + τ)) ≤ Real.sqrt (1 + lsq z₀) :=
            Real.sqrt_le_sqrt (by linarith)
          have hF : 0 ≤ 1 / |slabF c τ| := by positivity
          simp only [hg]
          rw [show Real.sqrt (1 + lsq z₀) * (1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ)))) =
            1 / |slabF c τ| * (Real.sqrt (1 + lsq z₀) / (1 + lsq (z₀ + τ))) by ring]
          apply mul_le_mul_of_nonneg_left _ hF
          rw [div_le_div_iff₀ hs0 (by linarith : (0 : ℝ) < 1 + lsq (z₀ + τ)), one_mul]
          calc 1 + lsq (z₀ + τ) = Real.sqrt (1 + lsq (z₀ + τ)) * Real.sqrt (1 + lsq (z₀ + τ)) :=
                (Real.mul_self_sqrt (by linarith)).symm
            _ ≤ Real.sqrt (1 + lsq z₀) * Real.sqrt (1 + lsq (z₀ + τ)) :=
                mul_le_mul_of_nonneg_right hss hs0.le
      _ ≤ ∑ τ ∈ T, Real.sqrt (1 + lsq z₀) *
          (1 / |slabF c τ| * (1 / (1 + lsq (z₀ + τ)))) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun τ _ _ => by
            have := lsq_nonneg (z₀ + τ); positivity)
  rw [hsplit]
  have hJ : 2 * (11000 * (2 * (J : ℝ) + 3) * (J + 1)) ≤ 44000 * (J + 2) ^ 2 := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have e : (CD + 44000) * ((J : ℝ) + 2) ^ 2 = CD * (J + 2) ^ 2 + 44000 * (J + 2) ^ 2 := by ring
  rw [e]
  linarith

/-! ## Schur's test with test functions, and a box sum -/

/-- **Schur's test** between finite sets with test functions `p` (outputs) and `q` (inputs):
rows `Σ_y |κ(x,y)| q(y) ≤ a p(x)` and columns `Σ_x |κ(x,y)| p(x) ≤ b q(y)` give
`Σ_x |Σ_y κ(x,y) v(y)|² ≤ a b Σ_y |v(y)|²`. -/
theorem wschur {α β : Type*} (X : Finset α) (Y : Finset β) (κ : α → β → ℂ) (p : α → ℝ)
    (q : β → ℝ) (hq : ∀ y ∈ Y, 0 < q y) {a b : ℝ} (ha : 0 ≤ a)
    (hrow : ∀ x ∈ X, ∑ y ∈ Y, ‖κ x y‖ * q y ≤ a * p x)
    (hcol : ∀ y ∈ Y, ∑ x ∈ X, ‖κ x y‖ * p x ≤ b * q y) (v : β → ℂ) :
    ∑ x ∈ X, ‖∑ y ∈ Y, κ x y * v y‖ ^ 2 ≤ a * b * ∑ y ∈ Y, ‖v y‖ ^ 2 := by
  have hx : ∀ x ∈ X, ‖∑ y ∈ Y, κ x y * v y‖ ^ 2 ≤
      a * p x * ∑ y ∈ Y, ‖κ x y‖ * (‖v y‖ ^ 2 / q y) := by
    intro x hxX
    have h1 : ‖∑ y ∈ Y, κ x y * v y‖ ≤ ∑ y ∈ Y, ‖κ x y‖ * ‖v y‖ :=
      (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun y _ => norm_mul _ _))
    have h2 : (∑ y ∈ Y, ‖κ x y‖ * ‖v y‖) ^ 2 ≤
        (∑ y ∈ Y, ‖κ x y‖ * q y) * ∑ y ∈ Y, ‖κ x y‖ * (‖v y‖ ^ 2 / q y) := by
      apply sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro y hy; have := hq y hy; positivity
      · intro y hy; have := hq y hy; positivity
      · intro y hy
        have := hq y hy
        apply le_of_eq
        field_simp
    calc ‖∑ y ∈ Y, κ x y * v y‖ ^ 2 ≤ (∑ y ∈ Y, ‖κ x y‖ * ‖v y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ y ∈ Y, ‖κ x y‖ * q y) * ∑ y ∈ Y, ‖κ x y‖ * (‖v y‖ ^ 2 / q y) := h2
      _ ≤ a * p x * ∑ y ∈ Y, ‖κ x y‖ * (‖v y‖ ^ 2 / q y) :=
          mul_le_mul_of_nonneg_right (hrow x hxX) (sum_nonneg fun y hy => by
            have := hq y hy; positivity)
  calc ∑ x ∈ X, ‖∑ y ∈ Y, κ x y * v y‖ ^ 2
      ≤ ∑ x ∈ X, a * p x * ∑ y ∈ Y, ‖κ x y‖ * (‖v y‖ ^ 2 / q y) := sum_le_sum hx
    _ = a * ∑ y ∈ Y, ‖v y‖ ^ 2 / q y * ∑ x ∈ X, ‖κ x y‖ * p x := by
        rw [mul_sum]
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
        ring
    _ ≤ a * ∑ y ∈ Y, ‖v y‖ ^ 2 / q y * (b * q y) := by
        apply mul_le_mul_of_nonneg_left _ ha
        exact sum_le_sum fun y hy => mul_le_mul_of_nonneg_left (hcol y hy) (by
          have := hq y hy; positivity)
    _ = a * b * ∑ y ∈ Y, ‖v y‖ ^ 2 := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun y hy => ?_
        have := hq y hy
        field_simp

/-- `Σ_{w ∈ box M} (1 + |w|²)⁻¹ ≤ 1 + 26 M`. -/
theorem sum_box_inv_le (M : ℕ) : ∑ w ∈ box M, 1 / (1 + lsq w) ≤ 1 + 26 * M := by
  induction M with
  | zero =>
    rw [box_zero, sum_singleton, lsq_zero]
    norm_num
  | succ M ih =>
    have hsub : box M ⊆ box (M + 1) := box_mono (Nat.le_succ M)
    rw [← sum_sdiff hsub (f := fun w => 1 / (1 + lsq w))]
    have hsh : ∑ w ∈ box (M + 1) \ box M, 1 / (1 + lsq w) ≤ 26 := by
      have hcard := card_shell_le (M + 1) (by omega)
      rw [Nat.add_sub_cancel] at hcard
      have hM : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) ^ 2 := by positivity
      calc ∑ w ∈ box (M + 1) \ box M, 1 / (1 + lsq w)
          ≤ ∑ _w ∈ box (M + 1) \ box M, 1 / ((M + 1 : ℕ) : ℝ) ^ 2 := by
            refine sum_le_sum fun w hw => ?_
            have hnot : w ∉ box (M + 1 - 1) := by
              rw [Nat.add_sub_cancel]; exact (mem_sdiff.mp hw).2
            have hl := lsq_ge_of_not_mem hnot (by omega)
            exact one_div_le_one_div_of_le hM (by linarith)
        _ = ((box (M + 1) \ box M).card : ℝ) * (1 / ((M + 1 : ℕ) : ℝ) ^ 2) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ((26 * (M + 1) ^ 2 : ℕ) : ℝ) * (1 / ((M + 1 : ℕ) : ℝ) ^ 2) := by
            gcongr
        _ = 26 := by push_cast; field_simp
    push_cast
    linarith

end FSLattice
