import PlaneWave.SamePair.SameChannelKernel

/-!
# Same-pair third order, part 3: two more lattice sums

* `h3_diag_core`: the diagonal (`θ = 0`) form of the core sum of eq:h3,
  `Σ_τ |F_c(τ)|⁻¹ |τ|⁻² ≤ 22000 (2J + 3)`;
* `sig3_core`: the Schur sum of the third generator,
  `Σ_τ |F_c(τ)|⁻¹ |τ|⁻¹ ≤ 11000 (2J + 3)(J + 1)`;

both for transfers above the floor `|F_c(τ)| ≥ 2|τ|` and below the cap `|F_c(τ)| < 2^{J+2}`, by
the dyadic shells and the slab-weighted sum `slab_inv_sum_le` (the Schur rows of `Σ₂^bb`).
`log_ceil_le` bounds the logarithmic factor of eq:h3 below the cap.
-/

open Finset

namespace FSLattice

open FSChannel

/-- The slab-weighted sum on the dyadic shell `4^i ≤ |τ|² ≤ 4^{i+1}` above the floor and below
the cap: `Σ |F_c(τ)|⁻¹ ≤ 11000 (2J + 3) 2^i`. -/
lemma shell_inv_sum_le (c : Fin 3 → ℝ) {J : ℕ} (i : ℕ) (T : Finset L3)
    (hT : ∀ τ ∈ T, 1 ≤ lsq τ ∧ 2 * rho τ ≤ |slabF c τ| ∧ |slabF c τ| < 2 ^ (J + 1) * 2)
    (hsh : ∀ τ ∈ T, (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1)) :
    ∑ τ ∈ T, 1 / |slabF c τ| ≤ 11000 * (2 * J + 3) * 2 ^ i := by
  have hρ : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have h := slab_inv_sum_le c hρ (by positivity : (0 : ℝ) < 2 ^ (i + 1)) (J := J) T (by
    intro τ hτ
    obtain ⟨hs1, hs2⟩ := hsh τ hτ
    obtain ⟨-, hfl, hcap⟩ := hT τ hτ
    have e4 : ((2 : ℝ) ^ i) ^ 2 = 4 ^ i := FSBand.two_pow_sq i
    refine ⟨by rw [e4]; exact hs1, by rw [e4, ← pow_succ']; exact hs2, ?_, ?_⟩
    · have hr : (2 : ℝ) ^ i ≤ rho τ := by
        unfold rho; apply Real.le_sqrt_of_sq_le; rw [e4]; exact hs1
      rw [pow_succ]; linarith
    · calc |slabF c τ| < 2 ^ (J + 1) * 2 := hcap
        _ ≤ 2 ^ (J + 1) * 2 ^ (i + 1) := by
            gcongr
            calc (2 : ℝ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega))
  have e : 11000 * ((2 : ℝ) ^ i) ^ 2 * (2 / 2 ^ (i + 1) + 2 * (J + 1) / 2 ^ i) =
      11000 * (2 * J + 3) * 2 ^ i := by
    field_simp; ring
  rwa [e] at h

/-- Every transfer below the cap lies in a dyadic shell `i ≤ J`. -/
lemma exists_shell_le (c : Fin 3 → ℝ) {J : ℕ} {τ : L3}
    (h : 1 ≤ lsq τ ∧ 2 * rho τ ≤ |slabF c τ| ∧ |slabF c τ| < 2 ^ (J + 1) * 2) :
    ∃ i ≤ J, (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1) := by
  obtain ⟨h1, hfl, hcap⟩ := h
  obtain ⟨i, hi1, hi2⟩ := FSNormal.exists_shell h1
  refine ⟨i, ?_, hi1, hi2⟩
  by_contra hJ
  push Not at hJ
  have hρ : rho τ < 2 ^ (J + 1) := by
    have : 2 * rho τ < 2 ^ (J + 1) * 2 := lt_of_le_of_lt hfl hcap
    linarith
  have h4 : (4 : ℝ) ^ (J + 1) ≤ 4 ^ i := pow_le_pow_right₀ (by norm_num) hJ
  have hl : lsq τ < 4 ^ (J + 1) := by
    rw [← rho_sq, ← FSBand.two_pow_sq]
    exact pow_lt_pow_left₀ hρ (rho_nonneg τ) two_ne_zero
  linarith

/-- **The diagonal core sum**: `Σ_τ |F_c(τ)|⁻¹ |τ|⁻² ≤ 22000 (2J + 3)`. -/
theorem h3_diag_core (c : Fin 3 → ℝ) {J : ℕ} (T : Finset L3)
    (hT : ∀ τ ∈ T, 1 ≤ lsq τ ∧ 2 * rho τ ≤ |slabF c τ| ∧ |slabF c τ| < 2 ^ (J + 1) * 2) :
    ∑ τ ∈ T, 1 / |slabF c τ| * (1 / lsq τ) ≤ 22000 * (2 * J + 3) := by
  classical
  have hnn : ∀ τ ∈ T, 0 ≤ 1 / |slabF c τ| * (1 / lsq τ) := fun τ _ => by
    have := lsq_nonneg τ; positivity
  refine (sum_le_sum_shells T _ hnn (fun i τ => (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1)) J
    (fun τ hτ => exists_shell_le c (hT τ hτ))).trans ?_
  have hper : ∀ i ∈ range (J + 1),
      ∑ τ ∈ T.filter (fun τ => (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1)),
        1 / |slabF c τ| * (1 / lsq τ) ≤ 11000 * (2 * J + 3) * (1 / 2) ^ i := by
    intro i _
    set Ti := T.filter (fun τ => (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1))
    have h1 : ∀ τ ∈ Ti, 1 / |slabF c τ| * (1 / lsq τ) ≤ 1 / (4 : ℝ) ^ i * (1 / |slabF c τ|) := by
      intro τ hτ
      have hs := (mem_filter.mp hτ).2.1
      have hF : 0 ≤ 1 / |slabF c τ| := by positivity
      calc 1 / |slabF c τ| * (1 / lsq τ) ≤ 1 / |slabF c τ| * (1 / 4 ^ i) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hs) hF
        _ = _ := by ring
    refine (sum_le_sum h1).trans ?_
    rw [← mul_sum]
    have h := shell_inv_sum_le c i Ti (fun τ hτ => hT τ (mem_filter.mp hτ).1)
      (fun τ hτ => (mem_filter.mp hτ).2)
    calc 1 / (4 : ℝ) ^ i * ∑ τ ∈ Ti, 1 / |slabF c τ| ≤
          1 / (4 : ℝ) ^ i * (11000 * (2 * J + 3) * 2 ^ i) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 11000 * (2 * J + 3) * (1 / 2) ^ i := by
          rw [← FSBand.two_pow_sq, one_div_pow]
          field_simp
  refine (sum_le_sum hper).trans ?_
  rw [← mul_sum]
  have hg : ∑ i ∈ range (J + 1), (1 / 2 : ℝ) ^ i ≤ 2 := by
    have := geom_sum_eq (show (1 / 2 : ℝ) ≠ 1 by norm_num) (J + 1)
    rw [this]
    have h0 : (0 : ℝ) ≤ (1 / 2) ^ (J + 1) := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    linarith
  calc 11000 * (2 * (J : ℝ) + 3) * ∑ i ∈ range (J + 1), (1 / 2 : ℝ) ^ i ≤
        11000 * (2 * J + 3) * 2 := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = 22000 * (2 * J + 3) := by ring

/-- **The Schur sum of the third generator**: `Σ_τ |F_c(τ)|⁻¹ |τ|⁻¹ ≤ 11000 (2J + 3)(J + 1)`. -/
theorem sig3_core (c : Fin 3 → ℝ) {J : ℕ} (T : Finset L3)
    (hT : ∀ τ ∈ T, 1 ≤ lsq τ ∧ 2 * rho τ ≤ |slabF c τ| ∧ |slabF c τ| < 2 ^ (J + 1) * 2) :
    ∑ τ ∈ T, 1 / |slabF c τ| * (1 / rho τ) ≤ 11000 * (2 * J + 3) * (J + 1) := by
  classical
  have hnn : ∀ τ ∈ T, 0 ≤ 1 / |slabF c τ| * (1 / rho τ) := fun τ _ => by
    have := rho_nonneg τ; positivity
  refine (sum_le_sum_shells T _ hnn (fun i τ => (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1)) J
    (fun τ hτ => exists_shell_le c (hT τ hτ))).trans ?_
  have hper : ∀ i ∈ range (J + 1),
      ∑ τ ∈ T.filter (fun τ => (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1)),
        1 / |slabF c τ| * (1 / rho τ) ≤ 11000 * (2 * J + 3) := by
    intro i _
    set Ti := T.filter (fun τ => (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1))
    have h1 : ∀ τ ∈ Ti, 1 / |slabF c τ| * (1 / rho τ) ≤ 1 / (2 : ℝ) ^ i * (1 / |slabF c τ|) := by
      intro τ hτ
      have hs := (mem_filter.mp hτ).2.1
      have hr : (2 : ℝ) ^ i ≤ rho τ := by
        unfold rho; apply Real.le_sqrt_of_sq_le; rw [FSBand.two_pow_sq]; exact hs
      have hF : 0 ≤ 1 / |slabF c τ| := by positivity
      calc 1 / |slabF c τ| * (1 / rho τ) ≤ 1 / |slabF c τ| * (1 / 2 ^ i) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hr) hF
        _ = _ := by ring
    refine (sum_le_sum h1).trans ?_
    rw [← mul_sum]
    have h := shell_inv_sum_le c i Ti (fun τ hτ => hT τ (mem_filter.mp hτ).1)
      (fun τ hτ => (mem_filter.mp hτ).2)
    calc 1 / (2 : ℝ) ^ i * ∑ τ ∈ Ti, 1 / |slabF c τ| ≤
          1 / (2 : ℝ) ^ i * (11000 * (2 * J + 3) * 2 ^ i) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 11000 * (2 * J + 3) := by field_simp
  refine (sum_le_sum hper).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  rfl

/-- The logarithmic factor of eq:h3 below `2^{J+1}`: `⌊log₂⌈x⌉⌋ ≤ J + 1`. -/
lemma log_ceil_le {x : ℝ} {J : ℕ} (h : x < 2 ^ (J + 1)) : Nat.log 2 ⌈x⌉₊ ≤ J + 1 := by
  have h1 : ⌈x⌉₊ ≤ 2 ^ (J + 1) := by
    rw [Nat.ceil_le]; push_cast; exact h.le
  calc Nat.log 2 ⌈x⌉₊ ≤ Nat.log 2 (2 ^ (J + 1)) := Nat.log_mono_right h1
    _ = J + 1 := Nat.log_pow (by norm_num) _

end FSLattice
