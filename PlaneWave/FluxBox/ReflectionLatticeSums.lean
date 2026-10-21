import PlaneWave.FluxBox.SameChannelSetting

/-!
# Flux route, stage 3, part 34: lattice sums for the reflection pairing

Pure lattice estimates on `ℤ³` used by the same-channel word:

* **the 2–2 convolution** (`conv22_le`): `Σ_θ 1/(|α - θ|² |θ - β|²) ≤ 864/|α - β|` (`α ≠ β`);
* **slices** (`slice_inv_max_sq_le`): `Σ_{θ_i = t} 1/max(R², |θ|²)² ≤ 8864/R²` (thickening a slice
  into a slab of width `⌊R⌋` and the radial sum);
* **thin sets of integers** (`card_layer_le`): `#{t : n - w < |a + ε t| ≤ n + w} ≤ 2(2w + 1)`;
* the four sums of the pairing: the common part `Σ_{|θ| ≥ n/2} |θ|⁻⁶ ≲ n⁻³`, the layer
  `Σ_{|θ| ≥ n/2, θ_i ∈ T} |θ|⁻⁵ ≲ |T| n⁻³`, and the tail `Σ_{|θ| > R} |θ|⁻⁵ ≲ R⁻²`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

/-! ## The 2–2 convolution -/

section Conv

open Classical in
lemma sum_inv_lsq_filter_ball_le (S : Finset Lattice3) {R : ℝ} (hR : 0 ≤ R) :
    ∑ ψ ∈ S.filter (fun ψ => ψ ≠ 0 ∧ FSLattice.lsq ψ ≤ R ^ 2), 1 / FSLattice.lsq ψ ≤ 26 * R := by
  obtain ⟨M, hM⟩ := FSLattice.exists_box S
  refine le_trans ?_ (FSLattice.sum_inv_lsq_ball_le' hR M)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ψ hψ
    rw [Finset.mem_filter] at hψ ⊢
    exact ⟨hM hψ.1, hψ.2⟩
  · intro ψ _ _; exact div_nonneg zero_le_one (FSLattice.lsq_nonneg ψ)

lemma rho_sub_ge (a b : Lattice3) : FSChannel.rho a - FSChannel.rho b ≤ FSChannel.rho (a - b) := by
  have h := FSChannel.rho_add_le (a - b) b
  rw [sub_add_cancel] at h
  linarith

lemma lsq_eq_rho_sq (a : Lattice3) : FSLattice.lsq a = FSChannel.rho a ^ 2 := (FSChannel.rho_sq a).symm

open Classical in
/-- **The 2–2 convolution on `ℤ³`**: `Σ_{θ ∈ S} 1/(|θ|² |γ - θ|²) ≤ 864/|γ|` for `γ ≠ 0`. -/
theorem conv22_zero (S : Finset Lattice3) {γ : Lattice3} (hγ : γ ≠ 0) :
    ∑ θ ∈ S, 1 / (FSLattice.lsq θ * FSLattice.lsq (γ - θ)) ≤ 864 / FSChannel.rho γ := by
  classical
  have hl1 : 1 ≤ FSLattice.lsq γ := one_le_latticeNormSq hγ
  have hρ1 : 1 ≤ FSChannel.rho γ := by
    unfold FSChannel.rho; rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hl1
  have hρ0 : 0 < FSChannel.rho γ := by linarith
  have hlr : FSLattice.lsq γ = FSChannel.rho γ ^ 2 := lsq_eq_rho_sq γ
  set ρ := FSChannel.rho γ
  set F : Lattice3 → ℝ := fun θ => 1 / (FSLattice.lsq θ * FSLattice.lsq (γ - θ)) with hF
  have hF0 : ∀ θ, 0 ≤ F θ := fun θ =>
    div_nonneg zero_le_one (mul_nonneg (FSLattice.lsq_nonneg _) (FSLattice.lsq_nonneg _))
  -- three regions
  set S1 := S.filter (fun θ => FSLattice.lsq θ ≤ (ρ / 2) ^ 2)
  set S2 := S.filter (fun θ => (ρ / 2) ^ 2 < FSLattice.lsq θ ∧ FSLattice.lsq θ ≤ (2 * ρ) ^ 2)
  set S3 := S.filter (fun θ => (2 * ρ) ^ 2 < FSLattice.lsq θ)
  have hsplit : ∑ θ ∈ S, F θ ≤ ∑ θ ∈ S1, F θ + ∑ θ ∈ S2, F θ + ∑ θ ∈ S3, F θ := by
    have h1 : ∑ θ ∈ S, F θ = ∑ θ ∈ S, ((if FSLattice.lsq θ ≤ (ρ / 2) ^ 2 then F θ else 0) +
        (if (ρ / 2) ^ 2 < FSLattice.lsq θ ∧ FSLattice.lsq θ ≤ (2 * ρ) ^ 2 then F θ else 0) +
        (if (2 * ρ) ^ 2 < FSLattice.lsq θ then F θ else 0)) := by
      refine Finset.sum_congr rfl fun θ _ => ?_
      by_cases h1 : FSLattice.lsq θ ≤ (ρ / 2) ^ 2
      · have h2 : ¬ ((ρ / 2) ^ 2 < FSLattice.lsq θ ∧ FSLattice.lsq θ ≤ (2 * ρ) ^ 2) := fun h => by linarith [h.1]
        have h3 : ¬ ((2 * ρ) ^ 2 < FSLattice.lsq θ) := by nlinarith
        rw [if_pos h1, if_neg h2, if_neg h3]; ring
      · by_cases h3 : (2 * ρ) ^ 2 < FSLattice.lsq θ
        · have h2 : ¬ ((ρ / 2) ^ 2 < FSLattice.lsq θ ∧ FSLattice.lsq θ ≤ (2 * ρ) ^ 2) := fun h => by linarith [h.2]
          rw [if_neg h1, if_neg h2, if_pos h3]; ring
        · have h2 : (ρ / 2) ^ 2 < FSLattice.lsq θ ∧ FSLattice.lsq θ ≤ (2 * ρ) ^ 2 :=
            ⟨not_le.mp h1, not_lt.mp h3⟩
          rw [if_neg h1, if_pos h2, if_neg h3]; ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter,
      Finset.sum_filter]
  refine hsplit.trans ?_
  -- region 1: `|θ| ≤ ρ/2`, so `|γ - θ| ≥ ρ/2`
  have hS1 : ∑ θ ∈ S1, F θ ≤ 52 / ρ := by
    have hpt : ∀ θ ∈ S1, F θ ≤ 4 / FSLattice.lsq γ * (if θ ≠ 0 ∧ FSLattice.lsq θ ≤ (ρ / 2) ^ 2 then
        1 / FSLattice.lsq θ else 0) := by
      intro θ hθ
      have hθ1 := (Finset.mem_filter.mp hθ).2
      by_cases h0 : θ = 0
      · subst h0
        simp only [hF]
        have : FSLattice.lsq (0 : Lattice3) = 0 := by simp [FSLattice.lsq]
        rw [this, zero_mul, div_zero]
        split_ifs <;> simp
      rw [if_pos ⟨h0, hθ1⟩]
      have hρθ : FSChannel.rho θ ≤ ρ / 2 := by
        unfold FSChannel.rho
        rw [Real.sqrt_le_left (by positivity)]; exact hθ1
      have h2 : ρ / 2 ≤ FSChannel.rho (γ - θ) := by
        have := rho_sub_ge γ θ; linarith
      have h3 : FSLattice.lsq γ / 4 ≤ FSLattice.lsq (γ - θ) := by
        rw [lsq_eq_rho_sq (γ - θ), hlr]
        have := pow_le_pow_left₀ (by positivity) h2 2
        nlinarith
      have hθ0 : 0 < FSLattice.lsq θ := lt_of_lt_of_le one_pos (one_le_latticeNormSq h0)
      have hg0 : 0 < FSLattice.lsq (γ - θ) := by linarith
      simp only [hF]
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (mul_pos hθ0 hg0) (mul_pos (by linarith) hθ0)]
      nlinarith
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum, ← Finset.sum_filter]
    have hball := sum_inv_lsq_filter_ball_le (S1) (by positivity : (0 : ℝ) ≤ ρ / 2)
    have hsub : S1.filter (fun θ => θ ≠ 0 ∧ FSLattice.lsq θ ≤ (ρ / 2) ^ 2) =
        S1.filter (fun ψ => ψ ≠ 0 ∧ FSLattice.lsq ψ ≤ (ρ / 2) ^ 2) := rfl
    calc 4 / FSLattice.lsq γ * ∑ θ ∈ S1.filter (fun θ => θ ≠ 0 ∧ FSLattice.lsq θ ≤ (ρ / 2) ^ 2),
          1 / FSLattice.lsq θ ≤ 4 / FSLattice.lsq γ * (26 * (ρ / 2)) :=
          mul_le_mul_of_nonneg_left hball (by positivity)
      _ = 52 / ρ := by rw [hlr]; field_simp; ring
  -- region 2: `ρ/2 < |θ| ≤ 2ρ`, so `|γ - θ| ≤ 3ρ`
  have hS2 : ∑ θ ∈ S2, F θ ≤ 312 / ρ := by
    have hpt : ∀ θ ∈ S2, F θ ≤ 4 / FSLattice.lsq γ * (if γ - θ ≠ 0 ∧ FSLattice.lsq (γ - θ) ≤ (3 * ρ) ^ 2 then
        1 / FSLattice.lsq (γ - θ) else 0) := by
      intro θ hθ
      have hθ2 := (Finset.mem_filter.mp hθ).2
      by_cases h0 : γ - θ = 0
      · simp only [hF]
        rw [h0]
        have : FSLattice.lsq (0 : Lattice3) = 0 := by simp [FSLattice.lsq]
        rw [this, mul_zero, div_zero]
        split_ifs <;> simp
      have hρθ : FSChannel.rho θ ≤ 2 * ρ := by
        unfold FSChannel.rho
        rw [Real.sqrt_le_left (by positivity)]; exact hθ2.2
      have h3 : FSLattice.lsq (γ - θ) ≤ (3 * ρ) ^ 2 := by
        rw [lsq_eq_rho_sq (γ - θ)]
        have := rho_sub_le γ θ
        have h4 : FSChannel.rho (γ - θ) ≤ 3 * ρ := by linarith
        exact pow_le_pow_left₀ (FSChannel.rho_nonneg _) h4 2
      rw [if_pos ⟨h0, h3⟩]
      have hθ0 : FSLattice.lsq γ / 4 < FSLattice.lsq θ := by
        rw [hlr]; nlinarith [hθ2.1]
      have hg0 : 0 < FSLattice.lsq (γ - θ) := lt_of_lt_of_le one_pos (one_le_latticeNormSq h0)
      have hθ0' : 0 < FSLattice.lsq θ := by linarith
      simp only [hF]
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (mul_pos hθ0' hg0) (mul_pos (by linarith) hg0)]
      nlinarith
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum, ← Finset.sum_filter]
    have hinj : Set.InjOn (fun θ => γ - θ)
        ↑(S2.filter (fun θ => γ - θ ≠ 0 ∧ FSLattice.lsq (γ - θ) ≤ (3 * ρ) ^ 2)) :=
      fun θ _ θ' _ h => by simpa using h
    have e : ∑ θ ∈ S2.filter (fun θ => γ - θ ≠ 0 ∧ FSLattice.lsq (γ - θ) ≤ (3 * ρ) ^ 2),
        1 / FSLattice.lsq (γ - θ) =
        ∑ ψ ∈ (S2.filter (fun θ => γ - θ ≠ 0 ∧ FSLattice.lsq (γ - θ) ≤ (3 * ρ) ^ 2)).image
          (fun θ => γ - θ), 1 / FSLattice.lsq ψ :=
      (Finset.sum_image (f := fun ψ => 1 / FSLattice.lsq ψ) hinj).symm
    rw [e]
    have hball := sum_inv_lsq_filter_ball_le
      ((S2.filter (fun θ => γ - θ ≠ 0 ∧ FSLattice.lsq (γ - θ) ≤ (3 * ρ) ^ 2)).image (fun θ => γ - θ))
      (by positivity : (0 : ℝ) ≤ 3 * ρ)
    have hfil : ((S2.filter (fun θ => γ - θ ≠ 0 ∧ FSLattice.lsq (γ - θ) ≤ (3 * ρ) ^ 2)).image
        (fun θ => γ - θ)).filter (fun ψ => ψ ≠ 0 ∧ FSLattice.lsq ψ ≤ (3 * ρ) ^ 2) =
        (S2.filter (fun θ => γ - θ ≠ 0 ∧ FSLattice.lsq (γ - θ) ≤ (3 * ρ) ^ 2)).image (fun θ => γ - θ) := by
      rw [Finset.filter_true_of_mem]
      intro ψ hψ
      obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hψ
      exact (Finset.mem_filter.mp hθ).2
    rw [hfil] at hball
    calc 4 / FSLattice.lsq γ * ∑ ψ ∈ (S2.filter (fun θ => γ - θ ≠ 0 ∧
          FSLattice.lsq (γ - θ) ≤ (3 * ρ) ^ 2)).image (fun θ => γ - θ), 1 / FSLattice.lsq ψ ≤
        4 / FSLattice.lsq γ * (26 * (3 * ρ)) := mul_le_mul_of_nonneg_left hball (by positivity)
      _ = 312 / ρ := by rw [hlr]; field_simp; ring
  -- region 3: `|θ| > 2ρ`, so `|γ - θ| ≥ |θ|/2`
  have hS3 : ∑ θ ∈ S3, F θ ≤ 500 / ρ := by
    have hpt : ∀ θ ∈ S3, F θ ≤ 4 * (1 / FSLattice.lsq θ ^ 2) := by
      intro θ hθ
      have hθ3 := (Finset.mem_filter.mp hθ).2
      have hρθ : 2 * ρ < FSChannel.rho θ := by
        unfold FSChannel.rho
        rw [Real.lt_sqrt (by positivity)]; exact hθ3
      have h2 : FSChannel.rho θ / 2 ≤ FSChannel.rho (γ - θ) := by
        have := rho_sub_ge θ γ
        have e : FSChannel.rho (θ - γ) = FSChannel.rho (γ - θ) := by
          unfold FSChannel.rho; rw [← lsq_neg, neg_sub]
        linarith
      have h3 : FSLattice.lsq θ / 4 ≤ FSLattice.lsq (γ - θ) := by
        rw [lsq_eq_rho_sq (γ - θ), lsq_eq_rho_sq θ]
        have := pow_le_pow_left₀ (by have := FSChannel.rho_nonneg θ; positivity) h2 2
        nlinarith
      have hθ0 : 0 < FSLattice.lsq θ := lt_of_le_of_lt (by positivity) hθ3
      have hg0 : 0 < FSLattice.lsq (γ - θ) := by linarith
      simp only [hF]
      rw [div_le_iff₀ (mul_pos hθ0 hg0)]
      calc (1 : ℝ) = 4 * (1 / FSLattice.lsq θ ^ 2) * (FSLattice.lsq θ * (FSLattice.lsq θ / 4)) := by
            field_simp
        _ ≤ 4 * (1 / FSLattice.lsq θ ^ 2) * (FSLattice.lsq θ * FSLattice.lsq (γ - θ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left h3 hθ0.le
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.mul_sum]
    have ht := FSLattice.sum_tail_inv_sq_le S (by linarith : (1 : ℝ) ≤ 2 * ρ)
    calc 4 * ∑ θ ∈ S3, 1 / FSLattice.lsq θ ^ 2 ≤ 4 * (250 / (2 * ρ)) :=
          mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = 500 / ρ := by field_simp; ring
  calc ∑ θ ∈ S1, F θ + ∑ θ ∈ S2, F θ + ∑ θ ∈ S3, F θ ≤ 52 / ρ + 312 / ρ + 500 / ρ := by linarith
    _ = 864 / ρ := by ring

open Classical in
/-- **The 2–2 convolution, shifted**: `Σ_θ 1/(|α - θ|² |θ - β|²) ≤ 864/|α - β|` for `α ≠ β`. -/
theorem conv22_le (S : Finset Lattice3) {α β : Lattice3} (hαβ : α ≠ β) :
    ∑ θ ∈ S, 1 / (FSLattice.lsq (α - θ) * FSLattice.lsq (θ - β)) ≤ 864 / FSChannel.rho (α - β) := by
  have hγ : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  have hinj : Set.InjOn (fun θ => α - θ) ↑S := fun θ _ θ' _ h => by simpa using h
  have e : ∑ θ ∈ S, 1 / (FSLattice.lsq (α - θ) * FSLattice.lsq (θ - β)) =
      ∑ ψ ∈ S.image (fun θ => α - θ), 1 / (FSLattice.lsq ψ * FSLattice.lsq ((α - β) - ψ)) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun θ _ => ?_
    congr 3; abel
  rw [e]
  exact conv22_zero _ hγ

end Conv

/-! ## Slices -/

section Slices

lemma lsq_add_single_le (θ : Lattice3) (i : Fin 3) (k : ℤ) :
    FSLattice.lsq (θ + (Pi.single i k : Lattice3)) ≤ 2 * FSLattice.lsq θ + 2 * (k : ℝ) ^ 2 := by
  unfold FSLattice.lsq
  fin_cases i <;> simp <;>
    nlinarith [sq_nonneg ((θ 0 : ℝ) - k), sq_nonneg ((θ 1 : ℝ) - k), sq_nonneg ((θ 2 : ℝ) - k),
      sq_nonneg (θ 0 : ℝ), sq_nonneg (θ 1 : ℝ), sq_nonneg (θ 2 : ℝ)]

lemma single_coord (θ : Lattice3) (i : Fin 3) (k : ℤ) :
    (θ + (Pi.single i k : Lattice3)) i = θ i + k := by
  simp

open Classical in
/-- **A slice of the radial sum**: `Σ_{θ ∈ S, θ_i = t} 1/max(R², |θ|²)² ≤ 8864/R²` for `R ≥ 1`. -/
theorem slice_inv_max_sq_le (S : Finset Lattice3) (i : Fin 3) (t : ℤ) {R : ℝ} (hR : 1 ≤ R) :
    ∑ θ ∈ S.filter (fun θ => θ i = t), 1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2 ≤ 8864 / R ^ 2 := by
  classical
  set K : ℕ := ⌊R⌋₊ with hK
  have hK1 : 1 ≤ K := Nat.le_floor (by exact_mod_cast hR)
  have hKR : (K : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hK2 : R / 2 ≤ (K : ℝ) := by
    have := Nat.lt_floor_add_one R
    have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    linarith
  have hR0 : 0 < R := by linarith
  set T := S.filter (fun θ => θ i = t)
  set F : Lattice3 → ℝ := fun θ => 1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2 with hF
  have hF0 : ∀ θ, 0 ≤ F θ := fun θ => by
    simp only [hF]; exact div_nonneg zero_le_one (pow_nonneg (le_trans (sq_nonneg R) (le_max_left _ _)) 2)
  -- each term is dominated by the shifted ones
  have hpt : ∀ θ ∈ T, ∀ k ∈ Finset.range K, F θ ≤ 16 * F (θ + (Pi.single i (k : ℤ) : Lattice3)) := by
    intro θ _ k hk
    have hk' : (k : ℝ) ≤ R := by
      have := Finset.mem_range.mp hk
      have : (k : ℝ) < K := by exact_mod_cast this
      linarith
    have h1 := lsq_add_single_le θ i (k : ℤ)
    push_cast at h1
    set M := max (R ^ 2) (FSLattice.lsq θ)
    set M' := max (R ^ 2) (FSLattice.lsq (θ + (Pi.single i (k : ℤ) : Lattice3)))
    have hM : R ^ 2 ≤ M := le_max_left _ _
    have hM2 : FSLattice.lsq θ ≤ M := le_max_right _ _
    have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hM' : M' ≤ 4 * M := by
      apply max_le
      · linarith
      · have : (k : ℝ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hk0 hk' 2
        linarith
    have hM'0 : 0 < M' := lt_of_lt_of_le (by positivity) (le_max_left _ _)
    simp only [hF]
    rw [div_le_iff₀ (by positivity)]
    have h2 : M' ^ 2 ≤ 16 * M ^ 2 := by nlinarith
    calc (1 : ℝ) = M' ^ 2 * (1 / M' ^ 2) := by field_simp
      _ ≤ 16 * M ^ 2 * (1 / M' ^ 2) := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = 16 * (1 / M' ^ 2) * M ^ 2 := by ring
  -- sum over the slab
  have hsum : (K : ℝ) * ∑ θ ∈ T, F θ ≤ 16 * (277 / R) := by
    have h1 : (K : ℝ) * ∑ θ ∈ T, F θ = ∑ θ ∈ T, ∑ k ∈ Finset.range K, F θ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun θ _ => ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h1]
    calc ∑ θ ∈ T, ∑ k ∈ Finset.range K, F θ ≤
        ∑ θ ∈ T, ∑ k ∈ Finset.range K, 16 * F (θ + (Pi.single i (k : ℤ) : Lattice3)) :=
          Finset.sum_le_sum fun θ hθ => Finset.sum_le_sum fun k hk => hpt θ hθ k hk
      _ = 16 * ∑ p ∈ T ×ˢ Finset.range K, F (p.1 + (Pi.single i (p.2 : ℤ) : Lattice3)) := by
          rw [Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun θ _ => ?_
          rw [Finset.mul_sum]
      _ = 16 * ∑ ψ ∈ (T ×ˢ Finset.range K).image (fun p => p.1 + (Pi.single i (p.2 : ℤ) : Lattice3)), F ψ := by
          congr 1
          rw [Finset.sum_image]
          intro p hp q hq h
          have hp1 := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
          have hq1 := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
          have hi := congrFun h i
          simp only [single_coord] at hi
          rw [hp1, hq1] at hi
          have hk : p.2 = q.2 := by exact_mod_cast add_left_cancel hi
          have hθ : p.1 = q.1 := by
            have := h
            simp only at this
            rw [hk] at this
            exact add_right_cancel this
          exact Prod.ext hθ hk
      _ ≤ 16 * (277 / R) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact sum_inv_max_sq_le _ hR
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have h3 : ∑ θ ∈ T, F θ ≤ 16 * (277 / R) / K := by
    rw [le_div_iff₀ hK0, mul_comm]; exact hsum
  calc ∑ θ ∈ T, F θ ≤ 16 * (277 / R) / K := h3
    _ ≤ 16 * (277 / R) / (R / 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hK2
    _ = 8864 / R ^ 2 := by field_simp; ring

end Slices

/-! ## Thin sets of integers -/

section Thin

/-- `#{t : n - w < |a + ε t| ≤ n + w} ≤ 2 (2w + 1)` for `ε = ±1`. -/
theorem card_layer_le (T : Finset ℤ) (a ε : ℤ) (hε : ε = 1 ∨ ε = -1) {n w : ℝ} (hw : 0 ≤ w)
    (hT : ∀ t ∈ T, n - w < |((a + ε * t : ℤ) : ℝ)| ∧ |((a + ε * t : ℤ) : ℝ)| ≤ n + w) :
    (T.card : ℝ) ≤ 2 * (2 * w + 1) := by
  classical
  have hε2 : ∀ t t' : ℤ, |((t - t' : ℤ) : ℝ)| = |((a + ε * t : ℤ) : ℝ) - ((a + ε * t' : ℤ) : ℝ)| := by
    intro t t'
    push_cast
    rcases hε with rfl | rfl
    · congr 1; ring
    · rw [← abs_neg]; congr 1; push_cast; ring
  set T₁ := T.filter (fun t => (0 : ℝ) ≤ ((a + ε * t : ℤ) : ℝ))
  set T₂ := T.filter (fun t => ¬ (0 : ℝ) ≤ ((a + ε * t : ℤ) : ℝ))
  have h1 : (T₁.card : ℝ) ≤ 2 * w + 1 := by
    apply FSLattice.card_int_le_of_diam T₁ (by linarith)
    intro x hx y hy
    have hx1 := (Finset.mem_filter.mp hx)
    have hy1 := (Finset.mem_filter.mp hy)
    have hxa := hT x hx1.1
    have hya := hT y hy1.1
    rw [abs_of_nonneg hx1.2] at hxa
    rw [abs_of_nonneg hy1.2] at hya
    have := hε2 x y
    have h5 : |((a + ε * x : ℤ) : ℝ) - ((a + ε * y : ℤ) : ℝ)| ≤ 2 * w := by
      rw [abs_le]; constructor <;> linarith [hxa.1, hxa.2, hya.1, hya.2]
    have h6 : ((x : ℝ) - y) ≤ |((x - y : ℤ) : ℝ)| := by
      push_cast; exact le_abs_self _
    linarith
  have h2 : (T₂.card : ℝ) ≤ 2 * w + 1 := by
    apply FSLattice.card_int_le_of_diam T₂ (by linarith)
    intro x hx y hy
    have hx1 := (Finset.mem_filter.mp hx)
    have hy1 := (Finset.mem_filter.mp hy)
    have hxa := hT x hx1.1
    have hya := hT y hy1.1
    rw [abs_of_neg (not_le.mp hx1.2)] at hxa
    rw [abs_of_neg (not_le.mp hy1.2)] at hya
    have := hε2 x y
    have h5 : |((a + ε * x : ℤ) : ℝ) - ((a + ε * y : ℤ) : ℝ)| ≤ 2 * w := by
      rw [abs_le]; constructor <;> linarith [hxa.1, hxa.2, hya.1, hya.2]
    have h6 : ((x : ℝ) - y) ≤ |((x - y : ℤ) : ℝ)| := by
      push_cast; exact le_abs_self _
    linarith
  have hsplit : T.card = T₁.card + T₂.card := (Finset.card_filter_add_card_filter_not _).symm
  have : (T.card : ℝ) = T₁.card + T₂.card := by exact_mod_cast hsplit
  linarith

end Thin

/-! ## The sums of the pairing -/

section PairSums

lemma max_le_four_lsq {R : ℝ} {θ : Lattice3} (h : (R / 2) ^ 2 ≤ FSLattice.lsq θ) :
    max (R ^ 2) (FSLattice.lsq θ) ≤ 4 * FSLattice.lsq θ := by
  apply max_le _ (by have := FSLattice.lsq_nonneg θ; linarith)
  nlinarith

open Classical in
/-- **The common part**: `Σ_{|θ| ≥ R/2} 1/|θ|⁶ ≤ 64·277/R³`. -/
theorem sum_far_inv_six_le (S : Finset Lattice3) {R : ℝ} (hR : 1 ≤ R) :
    ∑ θ ∈ S.filter (fun θ => (R / 2) ^ 2 ≤ FSLattice.lsq θ), 1 / FSLattice.lsq θ ^ 3 ≤
      64 * 277 / R ^ 3 := by
  have hpt : ∀ θ ∈ S.filter (fun θ => (R / 2) ^ 2 ≤ FSLattice.lsq θ),
      1 / FSLattice.lsq θ ^ 3 ≤ 64 * (1 / max (R ^ 2) (FSLattice.lsq θ) ^ 3) := by
    intro θ hθ
    have h := (Finset.mem_filter.mp hθ).2
    have hm := max_le_four_lsq h
    have hR0 : 0 < R := by linarith
    have hl : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) h
    have hM0 : 0 < max (R ^ 2) (FSLattice.lsq θ) := lt_of_lt_of_le (by positivity) (le_max_left _ _)
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have := pow_le_pow_left₀ hM0.le hm 3
    nlinarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  calc 64 * ∑ θ ∈ S.filter (fun θ => (R / 2) ^ 2 ≤ FSLattice.lsq θ),
        1 / max (R ^ 2) (FSLattice.lsq θ) ^ 3 ≤ 64 * (277 / R ^ 3) :=
        mul_le_mul_of_nonneg_left (sum_inv_max_cube_le _ hR) (by norm_num)
    _ = 64 * 277 / R ^ 3 := by ring

lemma inv_rho_le_of_lsq {R : ℝ} (hR : 0 < R) {θ : Lattice3} (h : (R / 2) ^ 2 ≤ FSLattice.lsq θ) :
    1 / FSChannel.rho θ ≤ 2 / R := by
  have hρ : R / 2 ≤ FSChannel.rho θ := by
    unfold FSChannel.rho; exact Real.le_sqrt_of_sq_le h
  rw [div_le_div_iff₀ (by linarith) hR]
  linarith

open Classical in
/-- **The layer**: `Σ_{|θ| ≥ R/2, θ_i ∈ T} 1/(|θ|⁴ |θ|) ≤ 2·16·8864 |T|/R³`. -/
theorem sum_layer_le (S : Finset Lattice3) (i : Fin 3) (T : Finset ℤ) {R : ℝ} (hR : 1 ≤ R) :
    ∑ θ ∈ S.filter (fun θ => (R / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ T),
      1 / (FSLattice.lsq θ ^ 2 * FSChannel.rho θ) ≤ 2 * 16 * 8864 * T.card / R ^ 3 := by
  classical
  have hR0 : 0 < R := by linarith
  have hpt : ∀ θ ∈ S.filter (fun θ => (R / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ T),
      1 / (FSLattice.lsq θ ^ 2 * FSChannel.rho θ) ≤
        2 / R * (16 * (1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2)) := by
    intro θ hθ
    have h := (Finset.mem_filter.mp hθ).2.1
    have hm := max_le_four_lsq h
    have hl : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) h
    have hρ : R / 2 ≤ FSChannel.rho θ := by
      unfold FSChannel.rho; exact Real.le_sqrt_of_sq_le h
    have hρ0 : 0 < FSChannel.rho θ := by linarith
    have hM0 : 0 < max (R ^ 2) (FSLattice.lsq θ) := lt_of_lt_of_le (by positivity) (le_max_left _ _)
    have h1 : 1 / FSLattice.lsq θ ^ 2 ≤ 16 * (1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have := pow_le_pow_left₀ hM0.le hm 2
      nlinarith
    have h2 := inv_rho_le_of_lsq hR0 h
    calc 1 / (FSLattice.lsq θ ^ 2 * FSChannel.rho θ) = 1 / FSChannel.rho θ * (1 / FSLattice.lsq θ ^ 2) := by
          ring
      _ ≤ 2 / R * (16 * (1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2)) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- fibre over the coordinate
  have hfib : ∑ θ ∈ S.filter (fun θ => (R / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ T),
      1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2 ≤
      ∑ t ∈ T, ∑ θ ∈ S.filter (fun θ => θ i = t), 1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := S.filter (fun θ => (R / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ T))
      (t := T) (g := fun θ => θ i) (fun θ hθ => (Finset.mem_filter.mp hθ).2.2)]
    refine Finset.sum_le_sum fun t _ => ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro θ hθ
      rw [Finset.mem_filter] at hθ ⊢
      exact ⟨(Finset.mem_filter.mp hθ.1).1, hθ.2⟩
    · intro θ _ _
      exact div_nonneg zero_le_one (pow_nonneg (le_trans (sq_nonneg R) (le_max_left _ _)) 2)
  have hsl : ∑ t ∈ T, ∑ θ ∈ S.filter (fun θ => θ i = t), 1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2 ≤
      T.card * (8864 / R ^ 2) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun t _ => slice_inv_max_sq_le S i t hR
  calc 2 / R * (16 * ∑ θ ∈ S.filter (fun θ => (R / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ T),
        1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2) ≤ 2 / R * (16 * (T.card * (8864 / R ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (hfib.trans hsl) (by norm_num)
    _ = 2 * 16 * 8864 * T.card / R ^ 3 := by field_simp

open Classical in
/-- **The tail**: `Σ_{|θ| > R} 1/(|θ|⁴ |θ|) ≤ 250/R²`. -/
theorem sum_tail_inv_five_le (S : Finset Lattice3) {R : ℝ} (hR : 1 ≤ R) :
    ∑ θ ∈ S.filter (fun θ => R ^ 2 < FSLattice.lsq θ), 1 / (FSLattice.lsq θ ^ 2 * FSChannel.rho θ) ≤
      250 / R ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hpt : ∀ θ ∈ S.filter (fun θ => R ^ 2 < FSLattice.lsq θ),
      1 / (FSLattice.lsq θ ^ 2 * FSChannel.rho θ) ≤ 1 / R * (1 / FSLattice.lsq θ ^ 2) := by
    intro θ hθ
    have h := (Finset.mem_filter.mp hθ).2
    have hρ : R < FSChannel.rho θ := by
      unfold FSChannel.rho; rw [Real.lt_sqrt hR0.le]; exact h
    have hl : 0 < FSLattice.lsq θ := lt_of_le_of_lt (by positivity) h
    rw [one_div_mul_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    calc R * FSLattice.lsq θ ^ 2 ≤ FSChannel.rho θ * FSLattice.lsq θ ^ 2 :=
          mul_le_mul_of_nonneg_right hρ.le (sq_nonneg _)
      _ = FSLattice.lsq θ ^ 2 * FSChannel.rho θ := mul_comm _ _
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  calc 1 / R * ∑ θ ∈ S.filter (fun θ => R ^ 2 < FSLattice.lsq θ), 1 / FSLattice.lsq θ ^ 2 ≤
      1 / R * (250 / R) := mul_le_mul_of_nonneg_left (FSLattice.sum_tail_inv_sq_le S hR) (by positivity)
    _ = 250 / R ^ 2 := by field_simp

end PairSums

end FSFlux
