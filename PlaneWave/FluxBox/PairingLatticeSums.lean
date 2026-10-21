import PlaneWave.FluxBox.PairingGeometry

/-!
# Flux route, stage 3, part 36: the same-channel word — lattice sums of the pairing

* **slabs** (`sum_slab_inv_sq_le`): `Σ_{|θ| ≥ R/2, θ_i ∈ T} 1/|θ|⁴ ≤ 16·8864 |T|/R²`;
* **the 4–2 convolution off the core** (`conv42_far`): for `|φ| ≥ R ≥ 1`,
  `Σ_{|θ| ≥ R} 1/(|θ|⁴ |θ - φ|²) ≤ 1316/(R |φ|²)`;
* **layer sets** (`layT`, `card_layT_le`, `sum_X_le`, `sum_card_layT_le`): the transfers `θ` with
  `[b + θ ∈ P_s] ≠ [c - θ ∈ P_s]` lie in `≤ 6` slabs whose total thickness is `≤ 12 (1 + wgt b + wgt c)`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Slabs and the 4–2 convolution -/

section Sums

open Classical in
/-- **A slab**: `Σ_{|θ| ≥ R/2, θ_i ∈ T} 1/|θ|⁴ ≤ 16·8864 |T|/R²`. -/
theorem sum_slab_inv_sq_le (S : Finset Lattice3) (i : Fin 3) (T : Finset ℤ) {R : ℝ} (hR : 1 ≤ R) :
    ∑ θ ∈ S.filter (fun θ => (R / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ T), 1 / FSLattice.lsq θ ^ 2 ≤
      16 * 8864 * T.card / R ^ 2 := by
  classical
  have hR0 : 0 < R := by linarith
  have hpt : ∀ θ ∈ S.filter (fun θ => (R / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ T),
      1 / FSLattice.lsq θ ^ 2 ≤ 16 * (1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2) := by
    intro θ hθ
    have h := (Finset.mem_filter.mp hθ).2.1
    have hm := max_le_four_lsq h
    have hl : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) h
    have hM0 : 0 < max (R ^ 2) (FSLattice.lsq θ) := lt_of_lt_of_le (by positivity) (le_max_left _ _)
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have := pow_le_pow_left₀ hM0.le hm 2
    nlinarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
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
  calc 16 * ∑ θ ∈ S.filter (fun θ => (R / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ T),
        1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2 ≤ 16 * (T.card * (8864 / R ^ 2)) :=
        mul_le_mul_of_nonneg_left (hfib.trans hsl) (by norm_num)
    _ = 16 * 8864 * T.card / R ^ 2 := by ring

omit [Fintype ν] in
lemma lsq_zero' : FSLattice.lsq (0 : Lattice3) = 0 := by simp [FSLattice.lsq]

open Classical in
/-- **The 4–2 convolution off the core**: for `R ≤ |φ|`, `R ≥ 1`,
`Σ_{|θ| ≥ R} 1/(|θ|⁴ |θ - φ|²) ≤ 1316/(R |φ|²)`. -/
theorem conv42_far (S : Finset Lattice3) {R : ℝ} (hR : 1 ≤ R) {φ : Lattice3}
    (hφ : R ≤ FSChannel.rho φ) :
    ∑ θ ∈ S.filter (fun θ => R ^ 2 ≤ FSLattice.lsq θ),
      1 / (FSLattice.lsq θ ^ 2 * FSLattice.lsq (θ - φ)) ≤ 1316 / (R * FSLattice.lsq φ) := by
  classical
  have hR0 : 0 < R := by linarith
  have hρ0 : 0 < FSChannel.rho φ := lt_of_lt_of_le hR0 hφ
  have hlφ : FSLattice.lsq φ = FSChannel.rho φ ^ 2 := lsq_eq_rho_sq φ
  have hlφ0 : 0 < FSLattice.lsq φ := by rw [hlφ]; positivity
  set B := FSChannel.rho φ / 2 with hB
  have hB0 : 0 ≤ B := by positivity
  set g : Lattice3 → ℝ := fun ψ => if ψ ≠ 0 ∧ FSLattice.lsq ψ ≤ B ^ 2 then 1 / FSLattice.lsq ψ else 0
    with hg
  have hpt : ∀ θ ∈ S.filter (fun θ => R ^ 2 ≤ FSLattice.lsq θ),
      1 / (FSLattice.lsq θ ^ 2 * FSLattice.lsq (θ - φ)) ≤
        4 / FSLattice.lsq φ * (1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2) +
        16 / FSLattice.lsq φ ^ 2 * g (θ - φ) := by
    intro θ hθ
    have h := (Finset.mem_filter.mp hθ).2
    have hl : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) h
    have hmax : max (R ^ 2) (FSLattice.lsq θ) = FSLattice.lsq θ := max_eq_right h
    by_cases hc : θ - φ ≠ 0 ∧ FSLattice.lsq (θ - φ) ≤ B ^ 2
    · have hgv : g (θ - φ) = 1 / FSLattice.lsq (θ - φ) := by simp only [hg]; rw [if_pos hc]
      rw [hgv]
      have hd0 : 0 < FSLattice.lsq (θ - φ) := lt_of_lt_of_le zero_lt_one (one_le_latticeNormSq hc.1)
      have hρd : FSChannel.rho (θ - φ) ≤ B := by
        rw [← Real.sqrt_sq hB0]; unfold FSChannel.rho; exact Real.sqrt_le_sqrt hc.2
      have h1 := rho_sub_ge φ (φ - θ)
      have e1 : φ - (φ - θ) = θ := by abel
      rw [e1] at h1
      have e2 : FSChannel.rho (φ - θ) = FSChannel.rho (θ - φ) := by rw [← rho_neg' (θ - φ), neg_sub]
      rw [e2] at h1
      have hθρ : FSChannel.rho φ / 2 ≤ FSChannel.rho θ := by linarith
      have hlθ : FSLattice.lsq φ / 4 ≤ FSLattice.lsq θ := by
        rw [hlφ, lsq_eq_rho_sq θ]
        have := pow_le_pow_left₀ (by positivity) hθρ 2
        nlinarith
      have h2 : 1 / (FSLattice.lsq θ ^ 2 * FSLattice.lsq (θ - φ)) ≤
          16 / FSLattice.lsq φ ^ 2 * (1 / FSLattice.lsq (θ - φ)) := by
        rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
        have := pow_le_pow_left₀ (by positivity) hlθ 2
        have hd := hd0.le
        nlinarith [mul_le_mul_of_nonneg_right this hd]
      have : 0 ≤ 4 / FSLattice.lsq φ * (1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2) := by positivity
      linarith
    · have hgv : g (θ - φ) = 0 := by simp only [hg]; rw [if_neg hc]
      rw [hgv, mul_zero, add_zero, hmax]
      by_cases hz : θ - φ = 0
      · rw [hz, lsq_zero', mul_zero, div_zero]; positivity
      · have hfar : B ^ 2 < FSLattice.lsq (θ - φ) := by
          by_contra h'; exact hc ⟨hz, not_lt.mp h'⟩
        have hB2 : B ^ 2 = FSLattice.lsq φ / 4 := by rw [hlφ, hB]; ring
        rw [hB2] at hfar
        have hd0 : 0 < FSLattice.lsq (θ - φ) := lt_of_le_of_lt (by positivity) hfar
        rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (mul_pos (pow_pos hl 2) hd0) (by positivity),
          one_mul]
        have := pow_pos hl 2
        nlinarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hA : ∑ θ ∈ S.filter (fun θ => R ^ 2 ≤ FSLattice.lsq θ), 1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2 ≤
      277 / R := by
    refine le_trans ?_ (sum_inv_max_sq_le S hR)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro θ _ _
    exact div_nonneg zero_le_one (pow_nonneg (le_trans (sq_nonneg R) (le_max_left _ _)) 2)
  have hgn : ∀ ψ, 0 ≤ g ψ := fun ψ => by
    simp only [hg]; split_ifs
    · exact div_nonneg zero_le_one (FSLattice.lsq_nonneg _)
    · exact le_refl 0
  have hBall : ∑ θ ∈ S.filter (fun θ => R ^ 2 ≤ FSLattice.lsq θ), g (θ - φ) ≤ 26 * B := by
    calc ∑ θ ∈ S.filter (fun θ => R ^ 2 ≤ FSLattice.lsq θ), g (θ - φ) ≤ ∑ θ ∈ S, g (θ - φ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun θ _ _ => hgn _
      _ = ∑ ψ ∈ S.image (fun θ => θ - φ), g ψ := by
          rw [Finset.sum_image]
          intro x _ y _ hxy
          simpa using hxy
      _ = ∑ ψ ∈ (S.image (fun θ => θ - φ)).filter (fun ψ => ψ ≠ 0 ∧ FSLattice.lsq ψ ≤ B ^ 2),
            1 / FSLattice.lsq ψ := by
          rw [Finset.sum_filter]
      _ ≤ 26 * B := sum_inv_lsq_filter_ball_le _ hB0
  have hfin : 4 / FSLattice.lsq φ * (277 / R) + 16 / FSLattice.lsq φ ^ 2 * (26 * B) ≤
      1316 / (R * FSLattice.lsq φ) := by
    have e : 16 / FSLattice.lsq φ ^ 2 * (26 * B) = 208 / (FSChannel.rho φ * FSLattice.lsq φ) := by
      rw [hB, hlφ]; field_simp; ring
    rw [e]
    have h3 : 208 / (FSChannel.rho φ * FSLattice.lsq φ) ≤ 208 / (R * FSLattice.lsq φ) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_right hφ hlφ0.le
    have e2 : 4 / FSLattice.lsq φ * (277 / R) = 1108 / (R * FSLattice.lsq φ) := by
      field_simp; ring
    rw [e2]
    have e3 : (1316 : ℝ) / (R * FSLattice.lsq φ) = 1108 / (R * FSLattice.lsq φ) + 208 / (R * FSLattice.lsq φ) := by
      ring
    linarith
  calc 4 / FSLattice.lsq φ * ∑ θ ∈ S.filter (fun θ => R ^ 2 ≤ FSLattice.lsq θ),
        1 / max (R ^ 2) (FSLattice.lsq θ) ^ 2 +
      16 / FSLattice.lsq φ ^ 2 * ∑ θ ∈ S.filter (fun θ => R ^ 2 ≤ FSLattice.lsq θ), g (θ - φ) ≤
      4 / FSLattice.lsq φ * (277 / R) + 16 / FSLattice.lsq φ ^ 2 * (26 * B) := by
        gcongr
    _ ≤ _ := hfin

end Sums

/-! ## Layer sets -/

section Layers

open Classical in
/-- The `(r, i)` layer of the disagreement set at scale `s`: the values `t = θ_i` with
`s - w < |b_{r,i} + ε_r t| ≤ s + w`, `w = |b_{r,i} + c_{r,i}|`. -/
noncomputable def layT (S : Finset Lattice3) (s : ℝ) (j : Ch eta) (B C : Cf eta) (r : Fin eta)
    (i : Fin 3) : Finset ℤ :=
  (S.image (fun θ => θ i)).filter (fun t =>
    s - |((B r i + C r i : ℤ) : ℝ)| < |((B r i + sgnR j r * t : ℤ) : ℝ)| ∧
      |((B r i + sgnR j r * t : ℤ) : ℝ)| ≤ s + |((B r i + C r i : ℤ) : ℝ)|)

omit [Fintype ν] in
lemma card_layT_le (S : Finset Lattice3) (s : ℝ) (j : Ch eta) (B C : Cf eta) (r : Fin eta) (i : Fin 3) :
    ((layT S s j B C r i).card : ℝ) ≤ 2 * (2 * |((B r i + C r i : ℤ) : ℝ)| + 1) := by
  classical
  exact card_layer_le _ (B r i) (sgnR j r) (sgnR_sign j r) (abs_nonneg _)
    (fun t ht => (Finset.mem_filter.mp ht).2)

omit [Fintype ν] in
lemma mem_layT_of_X {S : Finset Lattice3} {s : ℝ} {j : Ch eta} {B C : Cf eta} (hcb : OnCh j C B)
    {θ : Lattice3} (hθ : θ ∈ S) (h : ¬ (InP s (B + tr j θ) ↔ InP s (C - tr j θ))) :
    ∃ r ∈ moved j, ∃ i, θ i ∈ layT S s j B C r i := by
  classical
  obtain ⟨r, hr, i, h1, h2⟩ := layer_of hcb h
  exact ⟨r, hr, i, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hθ, h1, h2⟩⟩

omit [Fintype ν] in
lemma abs_add_sgn_le (j : Ch eta) (r : Fin eta) (a t : ℤ) :
    |((a + sgnR j r * t : ℤ) : ℝ)| ≤ |((a : ℤ) : ℝ)| + |((t : ℤ) : ℝ)| := by
  rcases sgnR_sign j r with h | h <;> rw [h] <;> push_cast
  · rw [one_mul]; exact abs_add_le _ _
  · rw [neg_one_mul, ← sub_eq_add_neg]; exact abs_sub _ _

omit [Fintype ν] in
lemma lsq_ge_of_mem_layT {S : Finset Lattice3} {s : ℝ} {j : Ch eta} {B C : Cf eta} {r : Fin eta}
    {i : Fin 3} {θ : Lattice3} (ht : θ i ∈ layT S s j B C r i)
    (hBC : |((B r i + C r i : ℤ) : ℝ)| + |((B r i : ℤ) : ℝ)| ≤ s / 2) :
    (s / 2) ^ 2 ≤ FSLattice.lsq θ := by
  classical
  have h1 := (Finset.mem_filter.mp ht).2.1
  have h2 := abs_add_sgn_le j r (B r i) (θ i)
  have h3 : s / 2 ≤ |((θ i : ℤ) : ℝ)| := by linarith
  have h0 : 0 ≤ s / 2 := le_trans (add_nonneg (abs_nonneg _) (abs_nonneg _)) hBC
  have h4 := sq_coord_le_lsq θ i
  have h5 : (s / 2) ^ 2 ≤ ((θ i : ℤ) : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ h0 h3 2
    rwa [sq_abs] at this
  linarith

omit [Fintype ν] in
lemma lsq_ge_of_X {S : Finset Lattice3} {s : ℝ} {j : Ch eta} {B C : Cf eta} (hcb : OnCh j C B)
    (hBC : ∀ r ∈ moved j, ∀ i, |((B r i + C r i : ℤ) : ℝ)| + |((B r i : ℤ) : ℝ)| ≤ s / 2)
    {θ : Lattice3} (hθ : θ ∈ S) (h : ¬ (InP s (B + tr j θ) ↔ InP s (C - tr j θ))) :
    (s / 2) ^ 2 ≤ FSLattice.lsq θ := by
  obtain ⟨r, hr, i, ht⟩ := mem_layT_of_X hcb hθ h
  exact lsq_ge_of_mem_layT ht (hBC r hr i)

omit [Fintype ν] in
open Classical in
/-- **Covering the disagreement set by slabs**. -/
lemma sum_X_le (S : Finset Lattice3) (f : Lattice3 → ℝ) (hf : ∀ θ, 0 ≤ f θ) {s : ℝ} {j : Ch eta}
    {B C : Cf eta} (hcb : OnCh j C B)
    (hBC : ∀ r ∈ moved j, ∀ i, |((B r i + C r i : ℤ) : ℝ)| + |((B r i : ℤ) : ℝ)| ≤ s / 2)
    (Q : Lattice3 → Prop) :
    ∑ θ ∈ S.filter (fun θ => Q θ ∧ ¬ (InP s (B + tr j θ) ↔ InP s (C - tr j θ))), f θ ≤
      ∑ r ∈ moved j, ∑ i : Fin 3,
        ∑ θ ∈ S.filter (fun θ => (s / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ layT S s j B C r i), f θ := by
  classical
  set G : Lattice3 → Fin eta → Fin 3 → ℝ := fun θ r i =>
    if (s / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ layT S s j B C r i then f θ else 0 with hG
  have hG0 : ∀ θ r i, 0 ≤ G θ r i := fun θ r i => by
    simp only [hG]; split_ifs
    · exact hf θ
    · exact le_refl 0
  have hpt : ∀ θ ∈ S.filter (fun θ => Q θ ∧ ¬ (InP s (B + tr j θ) ↔ InP s (C - tr j θ))),
      f θ ≤ ∑ r ∈ moved j, ∑ i : Fin 3, G θ r i := by
    intro θ hθ
    rw [Finset.mem_filter] at hθ
    obtain ⟨r, hr, i, ht⟩ := mem_layT_of_X hcb hθ.1 hθ.2.2
    have hl := lsq_ge_of_mem_layT ht (hBC r hr i)
    have hv : G θ r i = f θ := by simp only [hG]; rw [if_pos ⟨hl, ht⟩]
    calc f θ = G θ r i := hv.symm
      _ ≤ ∑ i' : Fin 3, G θ r i' :=
          Finset.single_le_sum (f := fun i' => G θ r i') (fun i' _ => hG0 θ r i') (Finset.mem_univ i)
      _ ≤ ∑ r' ∈ moved j, ∑ i' : Fin 3, G θ r' i' :=
          Finset.single_le_sum (f := fun r' => ∑ i' : Fin 3, G θ r' i')
            (fun r' _ => Finset.sum_nonneg fun i' _ => hG0 θ r' i') hr
  refine (Finset.sum_le_sum hpt).trans ?_
  calc ∑ θ ∈ S.filter (fun θ => Q θ ∧ ¬ (InP s (B + tr j θ) ↔ InP s (C - tr j θ))),
        ∑ r ∈ moved j, ∑ i : Fin 3, G θ r i ≤ ∑ θ ∈ S, ∑ r ∈ moved j, ∑ i : Fin 3, G θ r i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun θ _ _ =>
          Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun i _ => hG0 θ r i
    _ = ∑ r ∈ moved j, ∑ i : Fin 3, ∑ θ ∈ S, G θ r i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => ?_
        simp only [hG]
        rw [Finset.sum_filter]

omit [Fintype ν] in
/-- **The total thickness of the layers**: `Σ_{r,i} |T_{r,i}| ≤ 12 (1 + wgt b + wgt c)`. -/
lemma sum_card_layT_le (S : Finset Lattice3) (s : ℝ) (j : Ch eta) (B C : Cf eta) :
    ∑ r ∈ moved j, ∑ i : Fin 3, ((layT S s j B C r i).card : ℝ) ≤ 12 * (1 + wgt j B + wgt j C) := by
  have hr : ∀ r, ∑ i : Fin 3, ((layT S s j B C r i).card : ℝ) ≤
      6 + 12 * (FSChannel.rho (B r) + FSChannel.rho (C r)) := by
    intro r
    have h := fun i => card_layT_le S s j B C r i
    have hw : ∀ i, |((B r i + C r i : ℤ) : ℝ)| ≤ FSChannel.rho (B r) + FSChannel.rho (C r) := by
      intro i
      push_cast
      exact (abs_add_le _ _).trans (add_le_add (abs_coord_le_rho (B r) i) (abs_coord_le_rho (C r) i))
    rw [Fin.sum_univ_three]
    linarith [h 0, h 1, h 2, hw 0, hw 1, hw 2]
  calc ∑ r ∈ moved j, ∑ i : Fin 3, ((layT S s j B C r i).card : ℝ) ≤
      ∑ r ∈ moved j, (6 + 12 * (FSChannel.rho (B r) + FSChannel.rho (C r))) :=
        Finset.sum_le_sum fun r _ => hr r
    _ = 6 * (moved j).card + 12 * (wgt j B + wgt j C) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
          Finset.sum_add_distrib]
        unfold wgt; ring
    _ ≤ 12 * (1 + wgt j B + wgt j C) := by
        have : ((moved j).card : ℝ) ≤ 2 := by exact_mod_cast card_moved_le j
        linarith

end Layers

end FSFlux
