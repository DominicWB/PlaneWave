import PlaneWave.Source.GalerkinSpectralLayer

/-!
# Flux/source build, block 1b: the retained Hamiltonian and its regularity

On the Galerkin space `E_n` of `dev/PlaneWave.Source.GalerkinSpectralLayer.lean`:

* `Hret sys L n ΔH = H_N + ΔH` for a symmetric `ΔH` with `‖ΔH v‖ ≤ C_Δ ‖v‖` (the two retained
  Hamiltonians of the manuscript, `H_N` and `P H̃ P`, are of this form by `cor:opnorm`);
* `Hret_eq_kin_add`, `Vret_le_wt`: `H' = A + V'` with `‖V' v‖ ≤ (√2 C_m + C_Δ) ‖(1+A)^{1/2} v‖`
  (the hypotheses of `lem:specleak`);
* `Hret_lower`: `H' ≥ -C_low` with `C_low = C_m² + 1/4 + C_Δ`;
* `wt_le_holder`: `‖(1+A)^s q‖ ≤ ‖(1+A) q‖^s ‖q‖^{1-s}` for `s ∈ [0,1]` (Hölder);
* `wt_one_le_of_quasi`: a quasi-eigenstate `‖(H' - E) q‖ ≤ γ ‖q‖` has
  `‖(1+A) q‖ ≤ 2 (1 + |E| + γ + C_V²/2) ‖q‖` (the last claim of `lem:qtail`).
-/

set_option autoImplicit false

open scoped InnerProductSpace
open PlaneWaveCertificate

namespace FSGalerkin

variable {eta : ℕ} {ν : Type*} [Fintype ν]

/-- The retained Hamiltonian `H' = H_N + ΔH`. -/
noncomputable def Hret (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)
    (ΔH : En eta n →ₗ[ℂ] En eta n) : En eta n →ₗ[ℂ] En eta n :=
  finiteCoulombHamiltonian sys L n + ΔH

lemma Hret_isSymmetric (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔ : ΔH.IsSymmetric) : (Hret sys L n ΔH).IsSymmetric :=
  (finiteCoulombHamiltonian_isSymmetric sys L n).add hΔ

/-- The potential part `V' = W_N + ΔH`. -/
noncomputable def Vret (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)
    (ΔH : En eta n →ₗ[ℂ] En eta n) : En eta n →ₗ[ℂ] En eta n :=
  finiteCoulombPotential sys (coulombCellAmplitude L) n + ΔH

lemma Hret_eq_kin_add (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)
    (ΔH : En eta n →ₗ[ℂ] En eta n) (v : En eta n) :
    Hret sys L n ΔH v = FSSpectral.kin (sb eta n) (Asym sys L n) v + Vret sys L n ΔH v := by
  unfold Hret Vret
  rw [LinearMap.add_apply, HN_eq_kin_add, LinearMap.add_apply]
  abel

lemma Vret_le_wt (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) (n : ℕ) (hL : 0 < L)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {ΔH : En eta n →ₗ[ℂ] En eta n}
    {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) (v : En eta n) :
    ‖Vret sys L n ΔH v‖ ≤ (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit + CΔ) *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖ := by
  unfold Vret
  rw [LinearMap.add_apply]
  have h1 := potential_le_wt sys Hunit n hL hPeriodic v
  have h2 : ‖ΔH v‖ ≤ CΔ * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖ :=
    (hΔb v).trans (mul_le_mul_of_nonneg_left (norm_le_wt sys L n (by norm_num) v) hCΔ)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

lemma Hret_lower (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) (n : ℕ) (hL : 0 < L)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {ΔH : En eta n →ₗ[ℂ] En eta n}
    {CΔ : ℝ} (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) (v : En eta n) :
    -((finiteCoulombPhysicalMassConstant sys L Hunit) ^ 2 + 1 / 4 + CΔ) * ‖v‖ ^ 2 ≤
      (⟪v, Hret sys L n ΔH v⟫_ℂ).re := by
  unfold Hret
  rw [LinearMap.add_apply, inner_add_right, Complex.add_re]
  have h1 := HN_lower sys Hunit n hL hPeriodic v
  have h2 : -(CΔ * ‖v‖ ^ 2) ≤ (⟪v, ΔH v⟫_ℂ).re := by
    have := Complex.abs_re_le_norm ⟪v, ΔH v⟫_ℂ
    have h3 : ‖⟪v, ΔH v⟫_ℂ‖ ≤ ‖v‖ * (CΔ * ‖v‖) :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hΔb v) (norm_nonneg _))
    have := neg_abs_le (⟪v, ΔH v⟫_ℂ).re
    nlinarith
  nlinarith

/-- Eigenvalues of a symmetric operator bounded below are bounded below. -/
lemma eigen_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (H : E →ₗ[ℂ] E)
    (hb : ∀ i, H (b i) = (lam i : ℂ) • b i) {C : ℝ}
    (hlow : ∀ v, -C * ‖v‖ ^ 2 ≤ (⟪v, H v⟫_ℂ).re) (i : ι) : -C ≤ lam i := by
  have h := hlow (b i)
  rw [hb i, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i] at h
  simpa using h

/-! ## Hölder interpolation of the kinetic weights -/

lemma sq_rpow_eq {x : ℝ} (hx : 0 ≤ x) (s : ℝ) : (x ^ 2) ^ s = (x ^ s) ^ 2 := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx, ← Real.rpow_natCast (x ^ s) 2,
    ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

omit [Fintype ν] in
/-- **Hölder**: `‖(1+A)^s q‖ ≤ ‖(1+A) q‖^s ‖q‖^{1-s}` for `0 ≤ s ≤ 1`. -/
lemma wt_le_holder (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (q : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) s q‖ ≤
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 q‖ ^ s * ‖q‖ ^ (1 - s) := by
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    have : FSSpectral.wt (sb eta n) (Asym sys L n) 0 q = q := by
      ext k
      rw [FSSpectral.wt, fc_sb_apply]
      simp
    rw [this]; simp
  rcases hs1.eq_or_lt with h1 | hlt
  · subst h1; simp
  -- the main case `0 < s < 1`
  set a : Cfg eta n → ℝ := fun k => (1 + Asym sys L n k) ^ 2 * ‖q.ofLp k‖ ^ 2 with ha
  set c : Cfg eta n → ℝ := fun k => ‖q.ofLp k‖ ^ 2 with hc
  have hA1 : ∀ k, 0 ≤ 1 + Asym sys L n k := fun k => by linarith [Asym_nonneg sys L n k]
  have ha0 : ∀ k, 0 ≤ a k := fun k => by simp only [ha]; positivity
  have hc0 : ∀ k, 0 ≤ c k := fun k => by simp only [hc]; positivity
  have hconj := Real.holderConjugate_one_div hpos (by linarith : 0 < 1 - s) (by ring)
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hconj
    (f := fun k => a k ^ s) (g := fun k => c k ^ (1 - s))
    (fun k _ => Real.rpow_nonneg (ha0 k) _) (fun k _ => Real.rpow_nonneg (hc0 k) _)
  -- identify the three sums
  have hL : ∑ k, a k ^ s * c k ^ (1 - s) =
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) s q‖ ^ 2 := by
    rw [norm_sq_wt]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ha, hc]
    have hX := hA1 k
    have hY := norm_nonneg (q.ofLp k)
    rw [Real.mul_rpow (sq_nonneg _) (sq_nonneg _), mul_assoc,
      ← Real.rpow_add' (sq_nonneg _) (by ring_nf; norm_num), sq_rpow_eq hX]
    norm_num
  have hR1 : ∑ k, (a k ^ s) ^ (1 / s) = ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 q‖ ^ 2 := by
    rw [norm_sq_wt]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Real.rpow_mul (ha0 k), mul_one_div_cancel hpos.ne', Real.rpow_one, Real.rpow_one]
  have hR2 : ∑ k, (c k ^ (1 - s)) ^ (1 / (1 - s)) = ‖q‖ ^ 2 := by
    rw [norm_sq_En]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Real.rpow_mul (hc0 k), mul_one_div_cancel (by linarith : (1 - s) ≠ 0), Real.rpow_one]
  rw [hL, hR1, hR2, one_div_one_div, one_div_one_div] at hH
  -- take square roots
  have hW0 := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) 1 q)
  have hq0 := norm_nonneg q
  have hrhs : (‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 q‖ ^ 2) ^ s * (‖q‖ ^ 2) ^ (1 - s) =
      (‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 q‖ ^ s * ‖q‖ ^ (1 - s)) ^ 2 := by
    rw [sq_rpow_eq hW0, sq_rpow_eq hq0, mul_pow]
  rw [hrhs] at hH
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hH

/-! ## Regularity of quasi-eigenstates -/

omit [Fintype ν] in
/-- `‖(1+A)^{1/2} q‖² ≤ ‖(1+A) q‖ ‖q‖`. -/
lemma wt_half_sq_le (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (q : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) q‖ ^ 2 ≤
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 q‖ * ‖q‖ := by
  have h := wt_le_holder sys L n (s := 1 / 2) (by norm_num) (by norm_num) q
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  refine h2.trans (le_of_eq ?_)
  have hW0 := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) 1 q)
  have hq0 := norm_nonneg q
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hW0,
    ← Real.rpow_mul hq0]
  norm_num

omit [Fintype ν] in
/-- `(1 + A) q = q + A q`. -/
lemma wt_one_eq (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (q : En eta n) :
    FSSpectral.wt (sb eta n) (Asym sys L n) 1 q = q + FSSpectral.kin (sb eta n) (Asym sys L n) q := by
  ext k
  rw [PiLp.add_apply, FSSpectral.wt, fc_sb_apply, FSSpectral.kin, fc_sb_apply, Real.rpow_one]
  push_cast
  ring

omit [Fintype ν] in
/-- **The last claim of `lem:qtail`**: a quasi-eigenstate `‖(H' - E) q‖ ≤ γ ‖q‖` of
`H' = A + V'` with `‖V' v‖ ≤ C_V ‖(1+A)^{1/2} v‖` has `‖(1+A) q‖ ≤ 2(1 + |E| + γ + C_V²/2) ‖q‖`. -/
lemma wt_one_le_of_quasi (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)
    (H V : En eta n →ₗ[ℂ] En eta n)
    (hHV : ∀ v, H v = FSSpectral.kin (sb eta n) (Asym sys L n) v + V v) {CV : ℝ} (hCV : 0 ≤ CV)
    (hV : ∀ v, ‖V v‖ ≤ CV * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖)
    {E γ : ℝ} (q : En eta n) (hq : ‖H q - (E : ℂ) • q‖ ≤ γ * ‖q‖) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 q‖ ≤ 2 * (1 + |E| + γ + CV ^ 2 / 2) * ‖q‖ := by
  set W1 := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 q‖ with hW1
  set Wh := ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) q‖ with hWh
  set N := ‖q‖ with hN
  have hkin : FSSpectral.kin (sb eta n) (Asym sys L n) q = H q - V q := by
    rw [hHV]; abel
  have hHq : ‖H q‖ ≤ (|E| + γ) * N := by
    have : H q = (H q - (E : ℂ) • q) + (E : ℂ) • q := by abel
    rw [this]
    calc _ ≤ ‖H q - (E : ℂ) • q‖ + ‖(E : ℂ) • q‖ := norm_add_le _ _
      _ ≤ γ * N + |E| * N := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add hq le_rfl
      _ = _ := by ring
  have h1 : W1 ≤ N + (|E| + γ) * N + CV * Wh := by
    rw [hW1, wt_one_eq, hkin]
    calc _ ≤ ‖q‖ + ‖H q - V q‖ := norm_add_le _ _
      _ ≤ ‖q‖ + (‖H q‖ + ‖V q‖) := add_le_add le_rfl (norm_sub_le _ _)
      _ ≤ N + ((|E| + γ) * N + CV * Wh) := add_le_add le_rfl (add_le_add hHq (hV q))
      _ = _ := by ring
  have h2 : Wh ^ 2 ≤ W1 * N := wt_half_sq_le sys L n q
  have hWh0 : 0 ≤ Wh := norm_nonneg _
  have hW10 : 0 ≤ W1 := norm_nonneg _
  have hN0 : 0 ≤ N := norm_nonneg _
  -- `C_V Wh ≤ W1/2 + C_V² N / 2`
  have h3 : CV * Wh ≤ W1 / 2 + CV ^ 2 / 2 * N := by
    have hsq : (CV * Wh) ^ 2 ≤ (W1 / 2 + CV ^ 2 / 2 * N) ^ 2 := by
      have h4 : (CV * Wh) ^ 2 ≤ CV ^ 2 * (W1 * N) := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left h2 (sq_nonneg CV)
      nlinarith [sq_nonneg (W1 - CV ^ 2 * N)]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have hE0 : 0 ≤ |E| := abs_nonneg E
  linarith [h1, h3]

end FSGalerkin
