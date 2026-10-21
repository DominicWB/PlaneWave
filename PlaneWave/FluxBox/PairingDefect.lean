import PlaneWave.FluxBox.PairingLatticeSums

/-!
# Flux route, stage 3, part 37: the same-channel word — the pairing defect

For cold `b, c` on one `j`-line, the same-channel composite `A(c,b) = Σ_f conj w_j(f,c) ỹ_{ss}(f,b)`
and its reflection `conj A(b,c)` have the same summand `W(θ_c - θ) W(θ - φ) W(φ)` (after `θ ↦ -θ`)
with different indicators and energies (`ssA_box`, `ssA_conj_box`). Pointwise
(`norm_F_sub_le`) the difference is controlled by

* the energy difference `|1/e_b(θ) - 1/e_c(-θ)| ≲ (wgt b + wgt c) |θ|/|θ|⁴` (common part, `gc`),
* the disagreement layers `[b + θ ∈ P] ≠ [c - θ ∈ P]` (`gx`, at scales `n` and `N`) and
  `[b + φ ∈ P] ≠ [c - φ ∈ P]` (`gy`),

whose double sums are `O((1 + wgt b + wgt c)/n³)` (`sum_gc_le`, `sum_gx_le`, `sum_gy_le`). Hence
**`|A(c,b) - conj A(b,c)| ≤ K_ss (1 + wgt b + wgt c)/n³`** (`norm_ssD_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The majorants and their double sums -/

section Maj

open Classical in
/-- The majorant of the common part. -/
noncomputable def gc (n : ℕ) (θ φ : Lattice3) : ℝ :=
  if ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ then
    FSChannel.rho θ / FSLattice.lsq θ ^ 3 * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) else 0

open Classical in
/-- The majorant of a disagreement in the far transfer (scale `s`). -/
noncomputable def gx (n : ℕ) (s : ℝ) (j : Ch eta) (B C : Cf eta) (θ φ : Lattice3) : ℝ :=
  if ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ ∧ ¬ (InP s (B + tr j θ) ↔ InP s (C - tr j θ)) then
    1 / FSLattice.lsq θ ^ 2 * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) else 0

open Classical in
/-- The majorant of a disagreement in the near transfer. -/
noncomputable def gy (n : ℕ) (j : Ch eta) (B C : Cf eta) (θ φ : Lattice3) : ℝ :=
  if ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ ∧
      ¬ (InP (n : ℝ) (B + tr j φ) ↔ InP (n : ℝ) (C - tr j φ)) then
    1 / FSLattice.lsq φ * (1 / (FSLattice.lsq θ ^ 2 * FSLattice.lsq (θ - φ))) else 0

omit [Fintype ν] in
lemma one_div_lsq_nonneg (θ : Lattice3) : 0 ≤ 1 / FSLattice.lsq θ :=
  div_nonneg zero_le_one (FSLattice.lsq_nonneg θ)

omit [Fintype ν] in
lemma gc_nonneg (n : ℕ) (θ φ : Lattice3) : 0 ≤ gc n θ φ := by
  unfold gc
  split_ifs
  · exact mul_nonneg (div_nonneg (FSChannel.rho_nonneg θ) (pow_nonneg (FSLattice.lsq_nonneg θ) 3))
      (div_nonneg zero_le_one (mul_nonneg (FSLattice.lsq_nonneg _) (FSLattice.lsq_nonneg _)))
  · exact le_refl 0

omit [Fintype ν] in
lemma gx_nonneg (n : ℕ) (s : ℝ) (j : Ch eta) (B C : Cf eta) (θ φ : Lattice3) : 0 ≤ gx n s j B C θ φ := by
  unfold gx
  split_ifs
  · exact mul_nonneg (div_nonneg zero_le_one (pow_nonneg (FSLattice.lsq_nonneg θ) 2))
      (div_nonneg zero_le_one (mul_nonneg (FSLattice.lsq_nonneg _) (FSLattice.lsq_nonneg _)))
  · exact le_refl 0

omit [Fintype ν] in
lemma gy_nonneg (n : ℕ) (j : Ch eta) (B C : Cf eta) (θ φ : Lattice3) : 0 ≤ gy n j B C θ φ := by
  unfold gy
  split_ifs
  · exact mul_nonneg (one_div_lsq_nonneg φ)
      (div_nonneg zero_le_one (mul_nonneg (pow_nonneg (FSLattice.lsq_nonneg _) 2) (FSLattice.lsq_nonneg _)))
  · exact le_refl 0

omit [Fintype ν] in
lemma rho_pos_of_lsq_pos {θ : Lattice3} (h : 0 < FSLattice.lsq θ) : 0 < FSChannel.rho θ := by
  unfold FSChannel.rho; exact Real.sqrt_pos.mpr h

omit [Fintype ν] in
/-- The covering of `sum_X_le` for any finset of disagreements. -/
lemma sum_X_le_of (S F : Finset Lattice3) (f : Lattice3 → ℝ) (hf : ∀ θ, 0 ≤ f θ) {s : ℝ} {j : Ch eta}
    {B C : Cf eta} (hcb : OnCh j C B)
    (hBC : ∀ r ∈ moved j, ∀ i, |((B r i + C r i : ℤ) : ℝ)| + |((B r i : ℤ) : ℝ)| ≤ s / 2)
    (hF : ∀ θ ∈ F, θ ∈ S ∧ ¬ (InP s (B + tr j θ) ↔ InP s (C - tr j θ))) :
    ∑ θ ∈ F, f θ ≤ ∑ r ∈ moved j, ∑ i : Fin 3,
        ∑ θ ∈ S.filter (fun θ => (s / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ layT S s j B C r i), f θ := by
  classical
  set G : Lattice3 → Fin eta → Fin 3 → ℝ := fun θ r i =>
    if (s / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ layT S s j B C r i then f θ else 0 with hG
  have hG0 : ∀ θ r i, 0 ≤ G θ r i := fun θ r i => by
    simp only [hG]; split_ifs
    · exact hf θ
    · exact le_refl 0
  have hpt : ∀ θ ∈ F, f θ ≤ ∑ r ∈ moved j, ∑ i : Fin 3, G θ r i := by
    intro θ hθ
    obtain ⟨r, hr, i, ht⟩ := mem_layT_of_X hcb (hF θ hθ).1 (hF θ hθ).2
    have hl := lsq_ge_of_mem_layT ht (hBC r hr i)
    have hv : G θ r i = f θ := by simp only [hG]; rw [if_pos ⟨hl, ht⟩]
    calc f θ = G θ r i := hv.symm
      _ ≤ ∑ i' : Fin 3, G θ r i' :=
          Finset.single_le_sum (f := fun i' => G θ r i') (fun i' _ => hG0 θ r i') (Finset.mem_univ i)
      _ ≤ ∑ r' ∈ moved j, ∑ i' : Fin 3, G θ r' i' :=
          Finset.single_le_sum (f := fun r' => ∑ i' : Fin 3, G θ r' i')
            (fun r' _ => Finset.sum_nonneg fun i' _ => hG0 θ r' i') hr
  refine (Finset.sum_le_sum hpt).trans ?_
  have hFS : F ⊆ S := fun θ hθ => (hF θ hθ).1
  calc ∑ θ ∈ F, ∑ r ∈ moved j, ∑ i : Fin 3, G θ r i ≤ ∑ θ ∈ S, ∑ r ∈ moved j, ∑ i : Fin 3, G θ r i :=
        Finset.sum_le_sum_of_subset_of_nonneg hFS fun θ _ _ =>
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
/-- `Σ_θ Σ_φ g_c ≤ 864·64·277/n³`. -/
lemma sum_gc_le (S : Finset Lattice3) {n : ℕ} (hn : 1 ≤ n) :
    ∑ θ ∈ S, ∑ φ ∈ S, gc n θ φ ≤ 864 * (64 * 277) / (n : ℝ) ^ 3 := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpt : ∀ θ ∈ S, ∑ φ ∈ S, gc n θ φ ≤
      if ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ then 864 * (1 / FSLattice.lsq θ ^ 3) else 0 := by
    intro θ _
    unfold gc
    by_cases h : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ
    · simp only [if_pos h]
      rw [← Finset.mul_sum]
      have hl : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) h
      have hθ0 : θ ≠ 0 := by rintro rfl; rw [lsq_zero'] at hl; exact lt_irrefl _ hl
      have hc := conv22_le S (α := θ) (β := 0) hθ0
      simp only [sub_zero] at hc
      have hρ := rho_pos_of_lsq_pos hl
      have := hρ.ne'
      have := hl.ne'
      calc FSChannel.rho θ / FSLattice.lsq θ ^ 3 *
            ∑ φ ∈ S, 1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ) ≤
          FSChannel.rho θ / FSLattice.lsq θ ^ 3 * (864 / FSChannel.rho θ) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ = 864 * (1 / FSLattice.lsq θ ^ 3) := by field_simp
    · simp only [if_neg h, Finset.sum_const_zero]; exact le_refl 0
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  have := sum_far_inv_six_le S (R := n) hn1
  calc 864 * ∑ θ ∈ S.filter (fun θ => ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ), 1 / FSLattice.lsq θ ^ 3 ≤
      864 * (64 * 277 / (n : ℝ) ^ 3) := mul_le_mul_of_nonneg_left this (by norm_num)
    _ = 864 * (64 * 277) / (n : ℝ) ^ 3 := by ring

omit [Fintype ν] in
lemma sum_layers_div (S : Finset Lattice3) (s : ℝ) (j : Ch eta) (B C : Cf eta) (K D : ℝ) :
    ∑ r ∈ moved j, ∑ i : Fin 3, K * ((layT S s j B C r i).card : ℝ) / D =
      K * (∑ r ∈ moved j, ∑ i : Fin 3, ((layT S s j B C r i).card : ℝ)) / D := by
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum, Finset.sum_div]

omit [Fintype ν] in
/-- `Σ_θ Σ_φ g_x ≤ 864·2·16·8864·12 (1 + wgt b + wgt c)/s³`. -/
lemma sum_gx_le (S : Finset Lattice3) (n : ℕ) {s : ℝ} (hs : 1 ≤ s) {j : Ch eta} {B C : Cf eta}
    (hcb : OnCh j C B)
    (hBC : ∀ r ∈ moved j, ∀ i, |((B r i + C r i : ℤ) : ℝ)| + |((B r i : ℤ) : ℝ)| ≤ s / 2) :
    ∑ θ ∈ S, ∑ φ ∈ S, gx n s j B C θ φ ≤
      864 * (2 * 16 * 8864 * (12 * (1 + wgt j B + wgt j C))) / s ^ 3 := by
  classical
  have hs0 : 0 < s := by linarith
  have hpt : ∀ θ ∈ S, ∑ φ ∈ S, gx n s j B C θ φ ≤
      if ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ ∧ ¬ (InP s (B + tr j θ) ↔ InP s (C - tr j θ)) then
        864 * (1 / (FSLattice.lsq θ ^ 2 * FSChannel.rho θ)) else 0 := by
    intro θ _
    unfold gx
    by_cases h : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ ∧ ¬ (InP s (B + tr j θ) ↔ InP s (C - tr j θ))
    · simp only [if_pos h]
      rw [← Finset.mul_sum]
      by_cases hθ0 : θ = 0
      · subst hθ0; simp [lsq_zero']
      have hl : 0 < FSLattice.lsq θ := lt_of_lt_of_le zero_lt_one (one_le_latticeNormSq hθ0)
      have hρ := rho_pos_of_lsq_pos hl
      have := hρ.ne'
      have := hl.ne'
      have hc := conv22_le S (α := θ) (β := 0) hθ0
      simp only [sub_zero] at hc
      calc 1 / FSLattice.lsq θ ^ 2 * ∑ φ ∈ S, 1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ) ≤
          1 / FSLattice.lsq θ ^ 2 * (864 / FSChannel.rho θ) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ = 864 * (1 / (FSLattice.lsq θ ^ 2 * FSChannel.rho θ)) := by field_simp
    · simp only [if_neg h, Finset.sum_const_zero]; exact le_refl 0
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  have h1 := sum_X_le S (fun θ => 1 / (FSLattice.lsq θ ^ 2 * FSChannel.rho θ))
    (fun θ => div_nonneg zero_le_one (mul_nonneg (pow_nonneg (FSLattice.lsq_nonneg θ) 2)
      (FSChannel.rho_nonneg θ))) hcb hBC (fun θ => ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ)
  have h2 : ∀ r ∈ moved j, ∀ i : Fin 3,
      ∑ θ ∈ S.filter (fun θ => (s / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ layT S s j B C r i),
        1 / (FSLattice.lsq θ ^ 2 * FSChannel.rho θ) ≤
        2 * 16 * 8864 * ((layT S s j B C r i).card : ℝ) / s ^ 3 :=
    fun r _ i => sum_layer_le S i _ hs
  have h3 := sum_card_layT_le S s j B C
  have h4 : ∑ θ ∈ S.filter (fun θ => ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ ∧
      ¬ (InP s (B + tr j θ) ↔ InP s (C - tr j θ))), 1 / (FSLattice.lsq θ ^ 2 * FSChannel.rho θ) ≤
      2 * 16 * 8864 * (12 * (1 + wgt j B + wgt j C)) / s ^ 3 := by
    refine h1.trans ((Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun i _ => h2 r hr i).trans ?_)
    rw [sum_layers_div]
    gcongr
  calc 864 * ∑ θ ∈ S.filter (fun θ => ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ ∧
        ¬ (InP s (B + tr j θ) ↔ InP s (C - tr j θ))), 1 / (FSLattice.lsq θ ^ 2 * FSChannel.rho θ) ≤
      864 * (2 * 16 * 8864 * (12 * (1 + wgt j B + wgt j C)) / s ^ 3) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = _ := by ring

omit [Fintype ν] in
/-- `Σ_θ Σ_φ g_y ≤ (1316/(n/2)) 16·8864·12 (1 + wgt b + wgt c)/n²`. -/
lemma sum_gy_le (S : Finset Lattice3) {n : ℕ} (hn : 2 ≤ n) {j : Ch eta} {B C : Cf eta}
    (hcb : OnCh j C B)
    (hBC : ∀ r ∈ moved j, ∀ i, |((B r i + C r i : ℤ) : ℝ)| + |((B r i : ℤ) : ℝ)| ≤ (n : ℝ) / 2) :
    ∑ θ ∈ S, ∑ φ ∈ S, gy n j B C θ φ ≤
      1316 / ((n : ℝ) / 2) * (16 * 8864 * (12 * (1 + wgt j B + wgt j C)) / (n : ℝ) ^ 2) := by
  classical
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hR : (1 : ℝ) ≤ (n : ℝ) / 2 := by linarith
  rw [Finset.sum_comm]
  have hpt : ∀ φ ∈ S, ∑ θ ∈ S, gy n j B C θ φ ≤
      if ¬ (InP (n : ℝ) (B + tr j φ) ↔ InP (n : ℝ) (C - tr j φ)) then
        1316 / ((n : ℝ) / 2) * (1 / FSLattice.lsq φ ^ 2) else 0 := by
    intro φ hφ
    unfold gy
    by_cases h : ¬ (InP (n : ℝ) (B + tr j φ) ↔ InP (n : ℝ) (C - tr j φ))
    · rw [if_pos h]
      have hl := lsq_ge_of_X hcb hBC hφ h
      have hρ : (n : ℝ) / 2 ≤ FSChannel.rho φ := rho_ge_of_lsq hl
      have hlφ : 0 < FSLattice.lsq φ := lt_of_lt_of_le (by positivity) hl
      have e : ∑ θ ∈ S, (if ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ ∧
          ¬ (InP (n : ℝ) (B + tr j φ) ↔ InP (n : ℝ) (C - tr j φ)) then
            1 / FSLattice.lsq φ * (1 / (FSLattice.lsq θ ^ 2 * FSLattice.lsq (θ - φ))) else 0) =
          1 / FSLattice.lsq φ * ∑ θ ∈ S.filter (fun θ => ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ),
            1 / (FSLattice.lsq θ ^ 2 * FSLattice.lsq (θ - φ)) := by
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun θ _ => ?_
        by_cases hθ : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ
        · rw [if_pos ⟨hθ, h⟩, if_pos hθ]
        · rw [if_neg (fun h' => hθ h'.1), if_neg hθ]
      rw [e]
      have hc := conv42_far S hR hρ
      have := hlφ.ne'
      calc 1 / FSLattice.lsq φ * ∑ θ ∈ S.filter (fun θ => ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ),
            1 / (FSLattice.lsq θ ^ 2 * FSLattice.lsq (θ - φ)) ≤
          1 / FSLattice.lsq φ * (1316 / ((n : ℝ) / 2 * FSLattice.lsq φ)) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ = 1316 / ((n : ℝ) / 2) * (1 / FSLattice.lsq φ ^ 2) := by field_simp
    · rw [if_neg h]
      apply le_of_eq
      refine Finset.sum_eq_zero fun θ _ => ?_
      rw [if_neg (fun h' => h h'.2)]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h2 : ∀ r ∈ moved j, ∀ i : Fin 3,
      ∑ θ ∈ S.filter (fun θ => ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ ∧ θ i ∈ layT S (n : ℝ) j B C r i),
        1 / FSLattice.lsq θ ^ 2 ≤ 16 * 8864 * ((layT S (n : ℝ) j B C r i).card : ℝ) / (n : ℝ) ^ 2 :=
    fun r _ i => sum_slab_inv_sq_le S i _ hn1
  have h3 := sum_card_layT_le S (n : ℝ) j B C
  refine (sum_X_le_of S _ (fun φ => 1 / FSLattice.lsq φ ^ 2)
    (fun φ => div_nonneg zero_le_one (pow_nonneg (FSLattice.lsq_nonneg φ) 2)) hcb hBC
    (fun φ hφ => Finset.mem_filter.mp hφ)).trans ?_
  refine (Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun i _ => h2 r hr i).trans ?_
  rw [sum_layers_div]
  gcongr

end Maj

/-! ## The pairing -/

section Pair

/-- The summand of the same-channel composite. -/
noncomputable def Hs (sys : CoulombSystem eta ν) (L : ℝ) (j : Ch eta) (θc θ φ : Lattice3) : ℂ :=
  Wl sys L j (θc - θ) * Wl sys L j (θ - φ) * Wl sys L j φ

open Classical in
/-- The direct summand `[b+θ ∈ P_N ∖ P_n, b+φ ∈ P_n] H/e_b(θ)`. -/
noncomputable def F1 (sys : CoulombSystem eta ν) (L : ℝ) (N n : ℕ) (j : Ch eta) (B : Cf eta)
    (θc θ φ : Lattice3) : ℂ :=
  if InP (N : ℝ) (B + tr j θ) ∧ ¬ InP (n : ℝ) (B + tr j θ) ∧ InP (n : ℝ) (B + tr j φ) then
    Hs sys L j θc θ φ / ((eL sys L j B θ : ℝ) : ℂ) else 0

open Classical in
/-- The reflected summand `[c-θ ∈ P_N ∖ P_n, c-φ ∈ P_n] H/e_c(-θ)`. -/
noncomputable def F2 (sys : CoulombSystem eta ν) (L : ℝ) (N n : ℕ) (j : Ch eta) (C : Cf eta)
    (θc θ φ : Lattice3) : ℂ :=
  if InP (N : ℝ) (C - tr j θ) ∧ ¬ InP (n : ℝ) (C - tr j θ) ∧ InP (n : ℝ) (C - tr j φ) then
    Hs sys L j θc θ φ / ((eL sys L j C (-θ) : ℝ) : ℂ) else 0

/-- The pairing defect `D(c,b) = A(c,b) - conj A(b,c)`. -/
noncomputable def ssD (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ) (j : Ch eta)
    (c b : Cfg eta N) : ℂ :=
  ssA sys L p₀ N n j c b - conj (ssA sys L p₀ N n j b c)

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

omit [Fintype ν] in
lemma inP_mono' {s t : ℝ} (h : s ≤ t) {x : Cf eta} (hx : InP s x) : InP t x :=
  fun c i => (hx c i).trans h

omit [Fintype ν] in
lemma sum_box_neg {β : Type*} [AddCommMonoid β] (M : ℕ) (g : Lattice3 → β) :
    ∑ θ ∈ FSLattice.box M, g θ = ∑ θ ∈ FSLattice.box M, g (-θ) := by
  refine Finset.sum_nbij' (fun θ => -θ) (fun θ => -θ) ?_ ?_ ?_ ?_ ?_
  · intro θ hθ
    rw [FSLattice.mem_box] at hθ ⊢
    intro i
    have := hθ i
    simp only [Pi.neg_apply]
    omega
  · intro θ hθ
    rw [FSLattice.mem_box] at hθ ⊢
    intro i
    have := hθ i
    simp only [Pi.neg_apply]
    omega
  · intro θ _; simp
  · intro θ _; simp
  · intro θ _; simp

open Classical in
/-- **The composite as a box sum**. -/
theorem ssA_box (hL : 0 < L) (hnN : n ≤ N) {j : Ch eta} {c b : Cfg eta N}
    (hb : InC (n : ℝ) (cst sys) (cidx N b)) (hcb : OnCh j (cidx N c) (cidx N b)) :
    ssA sys L p₀ N n j c b = -(lamC sys p₀ j : ℂ) * ∑ θ ∈ FSLattice.box (2 * N),
      ∑ φ ∈ FSLattice.box (2 * N), F1 sys L N n j (cidx N b) (chT N j c b) θ φ := by
  classical
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  rw [ssA_eq hL hb hcb]
  congr 1
  unfold lineT
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun θ _ => ?_
  by_cases hθ : cidx N b + tr j θ ∈ fourierConfigCube eta N
  · rw [if_pos hθ, Finset.sum_filter]
    have hθ' : InP (N : ℝ) (cidx N b + tr j θ) := (inP_iff_mem_cube N _).mpr hθ
    refine Finset.sum_congr rfl fun φ _ => ?_
    unfold F1 Hs
    by_cases hφ : cidx N b + tr j φ ∈ fourierConfigCube eta N
    · rw [if_pos hφ]
      by_cases h : ¬ InP (n : ℝ) (cidx N b + tr j θ) ∧ InP (n : ℝ) (cidx N b + tr j φ)
      · rw [if_pos h, if_pos ⟨hθ', h⟩]
      · rw [if_neg h, if_neg (fun h' => h h'.2)]
    · rw [if_neg hφ]
      have h1 : ¬ InP (n : ℝ) (cidx N b + tr j φ) := fun h' =>
        hφ ((inP_iff_mem_cube N _).mp (inP_mono' hnN' h'))
      rw [if_neg (fun h' => h1 h'.2.2)]
  · rw [if_neg hθ]
    symm
    refine Finset.sum_eq_zero fun φ _ => ?_
    unfold F1
    rw [if_neg (fun h' => hθ ((inP_iff_mem_cube N _).mp h'.1))]

open Classical in
/-- **The reflected composite as a box sum** (after `θ ↦ -θ`, `φ ↦ -φ`). -/
theorem ssA_conj_box (hL : 0 < L) (hnN : n ≤ N) {j : Ch eta} {c b : Cfg eta N}
    (hc : InC (n : ℝ) (cst sys) (cidx N c)) (hcb : OnCh j (cidx N c) (cidx N b)) :
    conj (ssA sys L p₀ N n j b c) = -(lamC sys p₀ j : ℂ) * ∑ θ ∈ FSLattice.box (2 * N),
      ∑ φ ∈ FSLattice.box (2 * N), F2 sys L N n j (cidx N c) (chT N j c b) θ φ := by
  classical
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  rw [ssA_eq hL hc (onCh_symm hcb), map_mul, map_neg, Complex.conj_ofReal, map_sum]
  congr 1
  have hbc : chT N j b c = -chT N j c b := by unfold chT; abel
  have hconj : ∀ x, conj (Wl sys L j x) = Wl sys L j (-x) := fun x => (Wl_neg hL j x).symm
  have hCneg : ∀ x, cidx N c - tr j (-x) = cidx N c + tr j x := fun x => by
    rw [tr_neg', sub_neg_eq_add]
  conv_rhs => rw [sum_box_neg (2 * N)]
  unfold lineT
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun θ _ => ?_
  conv_rhs => rw [sum_box_neg (2 * N)]
  by_cases hθ : cidx N c + tr j θ ∈ fourierConfigCube eta N
  · rw [if_pos hθ, map_sum, Finset.sum_filter]
    have hθ' : InP (N : ℝ) (cidx N c + tr j θ) := (inP_iff_mem_cube N _).mpr hθ
    refine Finset.sum_congr rfl fun φ _ => ?_
    unfold F2 Hs
    simp only [hCneg, neg_neg]
    by_cases hφ : cidx N c + tr j φ ∈ fourierConfigCube eta N
    · rw [if_pos hφ]
      by_cases h : ¬ InP (n : ℝ) (cidx N c + tr j θ) ∧ InP (n : ℝ) (cidx N c + tr j φ)
      · rw [if_pos h, if_pos ⟨hθ', h⟩, map_div₀, map_mul, map_mul, hconj, hconj, hconj,
          Complex.conj_ofReal, hbc]
        have a1 : -(-chT N j c b - θ) = chT N j c b - -θ := by abel
        have a2 : -(θ - φ) = -θ - -φ := by abel
        rw [a1, a2]
      · rw [if_neg h, if_neg (fun h' => h h'.2), map_zero]
    · rw [if_neg hφ]
      have h1 : ¬ InP (n : ℝ) (cidx N c + tr j φ) := fun h' =>
        hφ ((inP_iff_mem_cube N _).mp (inP_mono' hnN' h'))
      rw [if_neg (fun h' => h1 h'.2.2)]
  · rw [if_neg hθ]
    symm
    refine Finset.sum_eq_zero fun φ _ => ?_
    unfold F2
    simp only [hCneg]
    rw [if_neg (fun h' => hθ ((inP_iff_mem_cube N _).mp h'.1))]

omit [Fintype ν] in
lemma le_gsum {j : Ch eta} {B C : Cf eta} {θ φ : Lattice3}
    (hfar : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ)
    (hX : ¬ (InP (N : ℝ) (B + tr j θ) ↔ InP (N : ℝ) (C - tr j θ)) ∨
      ¬ (InP (n : ℝ) (B + tr j θ) ↔ InP (n : ℝ) (C - tr j θ)) ∨
      ¬ (InP (n : ℝ) (B + tr j φ) ↔ InP (n : ℝ) (C - tr j φ))) :
    1 / FSLattice.lsq θ ^ 2 * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) ≤
      gx n (N : ℝ) j B C θ φ + gx n (n : ℝ) j B C θ φ + gy n j B C θ φ := by
  classical
  have h1 := gx_nonneg n (N : ℝ) j B C θ φ
  have h2 := gx_nonneg n (n : ℝ) j B C θ φ
  have h3 := gy_nonneg n j B C θ φ
  rcases hX with h | h | h
  · have : gx n (N : ℝ) j B C θ φ =
        1 / FSLattice.lsq θ ^ 2 * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) := by
      unfold gx; rw [if_pos ⟨hfar, h⟩]
    linarith
  · have : gx n (n : ℝ) j B C θ φ =
        1 / FSLattice.lsq θ ^ 2 * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) := by
      unfold gx; rw [if_pos ⟨hfar, h⟩]
    linarith
  · have : gy n j B C θ φ =
        1 / FSLattice.lsq θ ^ 2 * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) := by
      unfold gy; rw [if_pos ⟨hfar, h⟩]; ring
    linarith

/-- **The pointwise bound of the pairing**. -/
theorem norm_F_sub_le (hL : 0 < L) (hn : 2 ≤ n) {j : Ch eta} {B C : Cf eta} {θc : Lattice3}
    (hB : InC (n : ℝ) (cst sys) B) (hC : InC (n : ℝ) (cst sys) C)
    (hθc : FSChannel.rho θc ≤ 2 * (cst sys * n)) (θ φ : Lattice3) :
    ‖F1 sys L N n j B θc θ φ - F2 sys L N n j C θc θ φ‖ ≤
      4 * chC sys L j ^ 3 * (384 * mmax sys ^ 2 / gF L ^ 2 * (wgt j B + wgt j C) * gc n θ φ +
        8 * mmax sys / gF L ^ 2 *
          (gx n (N : ℝ) j B C θ φ + gx n (n : ℝ) j B C θ φ + gy n j B C θ φ)) := by
  classical
  set c := chC sys L j with hc
  have hc0 : 0 ≤ c := chC_nonneg sys hL j
  have hc3 : 0 ≤ 4 * c ^ 3 := mul_nonneg (by norm_num) (pow_nonneg hc0 3)
  have hg : 0 < gF L := by unfold gF; positivity
  have hm1 := one_le_mmax (sys := sys)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set κ := gF L ^ 2 / (8 * mmax sys) with hκ
  have hκ0 : 0 < κ := by positivity
  have hgc := gc_nonneg n θ φ
  have hw := add_nonneg (wgt_nonneg j B) (wgt_nonneg j C)
  set G := gx n (N : ℝ) j B C θ φ + gx n (n : ℝ) j B C θ φ + gy n j B C θ φ with hG
  have hG0 : 0 ≤ G := add_nonneg (add_nonneg (gx_nonneg _ _ _ _ _ _ _) (gx_nonneg _ _ _ _ _ _ _))
    (gy_nonneg _ _ _ _ _ _)
  have hA0 : 0 ≤ 384 * mmax sys ^ 2 / gF L ^ 2 * (wgt j B + wgt j C) * gc n θ φ :=
    mul_nonneg (mul_nonneg (by positivity) hw) hgc
  have hK0 : 0 ≤ 8 * mmax sys / gF L ^ 2 * G := mul_nonneg (by positivity) hG0
  -- the majorant of `H` on far transfers
  have hH : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ →
      ‖Hs sys L j θc θ φ‖ ≤
        4 * c ^ 3 / FSLattice.lsq θ * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) := by
    intro hfar
    have hl : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) hfar
    have hρ := rho_ge_of_lsq hfar
    have hcs := mul_le_mul_of_nonneg_right (cst_le32 sys) (Nat.cast_nonneg (α := ℝ) n)
    have h2 : 2 * FSChannel.rho θc ≤ FSChannel.rho θ := by linarith
    have hlo := lsq_sub_ge_of_small h2
    have hlo0 : 0 < FSLattice.lsq θ / 4 := by positivity
    unfold Hs
    rw [norm_mul, norm_mul]
    have w1 := norm_Wl_le (sys := sys) hL j (θc - θ)
    have w2 := norm_Wl_le (sys := sys) hL j (θ - φ)
    have w3 := norm_Wl_le (sys := sys) hL j φ
    have w1' : c / FSLattice.lsq (θc - θ) ≤ 4 * c / FSLattice.lsq θ := by
      calc c / FSLattice.lsq (θc - θ) ≤ c / (FSLattice.lsq θ / 4) :=
            div_le_div_of_nonneg_left hc0 hlo0 hlo
        _ = 4 * c / FSLattice.lsq θ := by field_simp
    have n2 := norm_nonneg (Wl sys L j (θ - φ))
    have n3 := norm_nonneg (Wl sys L j φ)
    have d1 : 0 ≤ 4 * c / FSLattice.lsq θ := div_nonneg (by linarith) hl.le
    have d2 : 0 ≤ c / FSLattice.lsq (θ - φ) := div_nonneg hc0 (FSLattice.lsq_nonneg _)
    calc ‖Wl sys L j (θc - θ)‖ * ‖Wl sys L j (θ - φ)‖ * ‖Wl sys L j φ‖ ≤
        (4 * c / FSLattice.lsq θ) * (c / FSLattice.lsq (θ - φ)) * (c / FSLattice.lsq φ) :=
          mul_le_mul (mul_le_mul (w1.trans w1') w2 n2 d1) w3 n3 (mul_nonneg d1 d2)
      _ = 4 * c ^ 3 / FSLattice.lsq θ * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) := by ring
  unfold F1 F2
  by_cases hp : InP (N : ℝ) (B + tr j θ) ∧ ¬ InP (n : ℝ) (B + tr j θ) ∧ InP (n : ℝ) (B + tr j φ) <;>
  by_cases hq : InP (N : ℝ) (C - tr j θ) ∧ ¬ InP (n : ℝ) (C - tr j θ) ∧ InP (n : ℝ) (C - tr j φ)
  · -- both: the energy difference
    rw [if_pos hp, if_pos hq]
    have hfar := lsq_ge_of_notP hB hp.2.1
    have hl : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) hfar
    have he1 := eL_ge (L := L) j hB hfar
    have hfar' : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq (-θ) := by rwa [lsq_neg]
    have he2 := eL_ge (L := L) j hC hfar'
    rw [lsq_neg] at he2
    have hd := eL_sub_le (sys := sys) (L := L) j B C θ
    set e1 := eL sys L j B θ with he1d
    set e2 := eL sys L j C (-θ) with he2d
    have hκl : 0 < κ * FSLattice.lsq θ := by positivity
    have he10 : 0 < e1 := lt_of_lt_of_le hκl he1
    have he20 : 0 < e2 := lt_of_lt_of_le hκl he2
    have e : Hs sys L j θc θ φ / (e1 : ℂ) - Hs sys L j θc θ φ / (e2 : ℂ) =
        Hs sys L j θc θ φ * (((e2 - e1) / (e1 * e2) : ℝ) : ℂ) := by
      have : (e1 : ℂ) ≠ 0 := by exact_mod_cast he10.ne'
      have : (e2 : ℂ) ≠ 0 := by exact_mod_cast he20.ne'
      push_cast
      field_simp
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hprod : (κ * FSLattice.lsq θ) ^ 2 ≤ e1 * e2 := by
      rw [sq]; exact mul_le_mul he1 he2 hκl.le he10.le
    have hfrac : |(e2 - e1) / (e1 * e2)| ≤
        384 * mmax sys ^ 2 / gF L ^ 2 * (wgt j B + wgt j C) *
          (FSChannel.rho θ / FSLattice.lsq θ ^ 2) := by
      rw [abs_div, abs_of_pos (mul_pos he10 he20), abs_sub_comm]
      calc |e1 - e2| / (e1 * e2) ≤
          (6 * gF L ^ 2 * FSChannel.rho θ * (wgt j B + wgt j C)) / (κ * FSLattice.lsq θ) ^ 2 :=
            div_le_div₀ (by have := FSChannel.rho_nonneg θ; positivity) hd (by positivity) hprod
        _ = 384 * mmax sys ^ 2 / gF L ^ 2 * (wgt j B + wgt j C) *
              (FSChannel.rho θ / FSLattice.lsq θ ^ 2) := by
            rw [hκ]; field_simp; ring
    have hgcv : gc n θ φ = FSChannel.rho θ / FSLattice.lsq θ ^ 3 *
        (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) := by
      unfold gc; rw [if_pos hfar]
    have hm0 : 0 ≤ 4 * c ^ 3 / FSLattice.lsq θ * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) :=
      mul_nonneg (div_nonneg hc3 hl.le)
        (div_nonneg zero_le_one (mul_nonneg (FSLattice.lsq_nonneg _) (FSLattice.lsq_nonneg _)))
    calc ‖Hs sys L j θc θ φ‖ * |(e2 - e1) / (e1 * e2)| ≤
        (4 * c ^ 3 / FSLattice.lsq θ * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ))) *
          (384 * mmax sys ^ 2 / gF L ^ 2 * (wgt j B + wgt j C) *
            (FSChannel.rho θ / FSLattice.lsq θ ^ 2)) :=
          mul_le_mul (hH hfar) hfrac (abs_nonneg _) hm0
      _ = 4 * c ^ 3 * (384 * mmax sys ^ 2 / gF L ^ 2 * (wgt j B + wgt j C) * gc n θ φ) := by
          rw [hgcv]; field_simp
      _ ≤ _ := by
          have := mul_nonneg hc3 hK0
          rw [mul_add]; linarith
  · -- only the direct one
    rw [if_pos hp, if_neg hq, sub_zero]
    have hfar := lsq_ge_of_notP hB hp.2.1
    have hl : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) hfar
    have he1 := eL_ge (L := L) j hB hfar
    have hκl : 0 < κ * FSLattice.lsq θ := by positivity
    have he10 : 0 < eL sys L j B θ := lt_of_lt_of_le hκl he1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he10]
    have hX : ¬ (InP (N : ℝ) (B + tr j θ) ↔ InP (N : ℝ) (C - tr j θ)) ∨
        ¬ (InP (n : ℝ) (B + tr j θ) ↔ InP (n : ℝ) (C - tr j θ)) ∨
        ¬ (InP (n : ℝ) (B + tr j φ) ↔ InP (n : ℝ) (C - tr j φ)) := by
      by_cases h1 : InP (N : ℝ) (C - tr j θ)
      · by_cases h2 : InP (n : ℝ) (C - tr j θ)
        · right; left; exact fun h => hp.2.1 (h.mpr h2)
        · right; right; exact fun h => hq ⟨h1, h2, h.mp hp.2.2⟩
      · left; exact fun h => h1 (h.mp hp.1)
    have hv := le_gsum (N := N) hfar hX
    have hm0 : 0 ≤ 4 * c ^ 3 / FSLattice.lsq θ * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) :=
      mul_nonneg (div_nonneg hc3 hl.le)
        (div_nonneg zero_le_one (mul_nonneg (FSLattice.lsq_nonneg _) (FSLattice.lsq_nonneg _)))
    calc ‖Hs sys L j θc θ φ‖ / eL sys L j B θ ≤
        (4 * c ^ 3 / FSLattice.lsq θ * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ))) /
          (κ * FSLattice.lsq θ) := div_le_div₀ hm0 (hH hfar) hκl he1
      _ = 4 * c ^ 3 * (8 * mmax sys / gF L ^ 2 *
            (1 / FSLattice.lsq θ ^ 2 * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)))) := by
          rw [hκ]; field_simp
      _ ≤ 4 * c ^ 3 * (8 * mmax sys / gF L ^ 2 * G) := by
          apply mul_le_mul_of_nonneg_left _ hc3
          exact mul_le_mul_of_nonneg_left hv (by positivity)
      _ ≤ _ := by
          have := mul_nonneg hc3 hA0
          rw [mul_add (4 * c ^ 3)]; linarith
  · -- only the reflected one
    rw [if_neg hp, if_pos hq, zero_sub, norm_neg]
    have hfar := lsq_ge_of_notP' hC hq.2.1
    have hl : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) hfar
    have hfar' : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq (-θ) := by rwa [lsq_neg]
    have he2 := eL_ge (L := L) j hC hfar'
    rw [lsq_neg] at he2
    have hκl : 0 < κ * FSLattice.lsq θ := by positivity
    have he20 : 0 < eL sys L j C (-θ) := lt_of_lt_of_le hκl he2
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he20]
    have hX : ¬ (InP (N : ℝ) (B + tr j θ) ↔ InP (N : ℝ) (C - tr j θ)) ∨
        ¬ (InP (n : ℝ) (B + tr j θ) ↔ InP (n : ℝ) (C - tr j θ)) ∨
        ¬ (InP (n : ℝ) (B + tr j φ) ↔ InP (n : ℝ) (C - tr j φ)) := by
      by_cases h1 : InP (N : ℝ) (B + tr j θ)
      · by_cases h2 : InP (n : ℝ) (B + tr j θ)
        · right; left; exact fun h => hq.2.1 (h.mp h2)
        · right; right; exact fun h => hp ⟨h1, h2, h.mpr hq.2.2⟩
      · left; exact fun h => h1 (h.mpr hq.1)
    have hv := le_gsum (N := N) hfar hX
    have hm0 : 0 ≤ 4 * c ^ 3 / FSLattice.lsq θ * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)) :=
      mul_nonneg (div_nonneg hc3 hl.le)
        (div_nonneg zero_le_one (mul_nonneg (FSLattice.lsq_nonneg _) (FSLattice.lsq_nonneg _)))
    calc ‖Hs sys L j θc θ φ‖ / eL sys L j C (-θ) ≤
        (4 * c ^ 3 / FSLattice.lsq θ * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ))) /
          (κ * FSLattice.lsq θ) := div_le_div₀ hm0 (hH hfar) hκl he2
      _ = 4 * c ^ 3 * (8 * mmax sys / gF L ^ 2 *
            (1 / FSLattice.lsq θ ^ 2 * (1 / (FSLattice.lsq (θ - φ) * FSLattice.lsq φ)))) := by
          rw [hκ]; field_simp
      _ ≤ 4 * c ^ 3 * (8 * mmax sys / gF L ^ 2 * G) := by
          apply mul_le_mul_of_nonneg_left _ hc3
          exact mul_le_mul_of_nonneg_left hv (by positivity)
      _ ≤ _ := by
          have := mul_nonneg hc3 hA0
          rw [mul_add (4 * c ^ 3)]; linarith
  · rw [if_neg hp, if_neg hq, sub_zero, norm_zero]
    exact mul_nonneg hc3 (add_nonneg hA0 hK0)

/-- The constant of the same-channel pairing. -/
noncomputable def Kss (sys : CoulombSystem eta ν) (L : ℝ) (j : Ch eta) : ℝ :=
  4 * chC sys L j ^ 3 * (384 * mmax sys ^ 2 / gF L ^ 2 * (864 * (64 * 277)) +
    8 * mmax sys / gF L ^ 2 * (2 * (864 * (2 * 16 * 8864 * 12)) + 2 * 1316 * (16 * 8864 * 12)))

/-- **The pairing defect** (same channel): for cold `b, c` on one `j`-line,
`|A(c,b) - conj A(b,c)| ≤ K_ss (1 + wgt b + wgt c)/n³`. -/
theorem norm_ssD_le (hL : 0 < L) (hn : 2 ≤ n) (hnN : n ≤ N) {j : Ch eta} {c b : Cfg eta N}
    (hb : InC (n : ℝ) (cst sys) (cidx N b)) (hc : InC (n : ℝ) (cst sys) (cidx N c))
    (hcb : OnCh j (cidx N c) (cidx N b)) :
    ‖ssD sys L p₀ N n j c b‖ ≤
      Kss sys L j * (1 + wgt j (cidx N b) + wgt j (cidx N c)) / (n : ℝ) ^ 3 := by
  classical
  set B := cidx N b with hBd
  set C := cidx N c with hCd
  set S := FSLattice.box (2 * N) with hS
  set θc := chT N j c b with hθcd
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hθc : FSChannel.rho θc ≤ 2 * (cst sys * n) := rho_sub_cold_le hc hb (lead j)
  -- the layer hypotheses
  have hcs := mul_le_mul_of_nonneg_right (cst_le32 sys) (Nat.cast_nonneg (α := ℝ) n)
  have hBC : ∀ r ∈ moved j, ∀ i, |((B r i + C r i : ℤ) : ℝ)| + |((B r i : ℤ) : ℝ)| ≤ (n : ℝ) / 2 := by
    intro r _ i
    have h1 := (abs_coord_le_rho (B r) i).trans (rho_le_of_inC hb r)
    have h2 := (abs_coord_le_rho (C r) i).trans (rho_le_of_inC hc r)
    have h3 : |((B r i + C r i : ℤ) : ℝ)| ≤ |((B r i : ℤ) : ℝ)| + |((C r i : ℤ) : ℝ)| := by
      push_cast; exact abs_add_le _ _
    linarith
  have hBCN : ∀ r ∈ moved j, ∀ i, |((B r i + C r i : ℤ) : ℝ)| + |((B r i : ℤ) : ℝ)| ≤ (N : ℝ) / 2 :=
    fun r hr i => (hBC r hr i).trans (by linarith)
  have hcb' : OnCh j C B := hcb
  unfold ssD
  rw [ssA_box hL hnN hb hcb, ssA_conj_box hL hnN hc hcb, ← mul_sub, ← Finset.sum_sub_distrib]
  have e : ∀ θ ∈ S, (∑ φ ∈ S, F1 sys L N n j B θc θ φ) - ∑ φ ∈ S, F2 sys L N n j C θc θ φ =
      ∑ φ ∈ S, (F1 sys L N n j B θc θ φ - F2 sys L N n j C θc θ φ) :=
    fun θ _ => (Finset.sum_sub_distrib _ _).symm
  rw [Finset.sum_congr rfl e, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (lamC_nonneg sys p₀ j)]
  set c3 := 4 * chC sys L j ^ 3 with hc3d
  have hc3 : 0 ≤ c3 := mul_nonneg (by norm_num) (pow_nonneg (chC_nonneg sys hL j) 3)
  have hg : 0 < gF L := by unfold gF; positivity
  have hm1 := one_le_mmax (sys := sys)
  set Ke := 384 * mmax sys ^ 2 / gF L ^ 2 with hKe
  set K1 := 8 * mmax sys / gF L ^ 2 with hK1
  have hKe0 : 0 ≤ Ke := by positivity
  have hK10 : 0 ≤ K1 := by positivity
  set w := wgt j B + wgt j C with hwd
  have hw := add_nonneg (wgt_nonneg j B) (wgt_nonneg j C)
  set A1 := c3 * (Ke * w) with hA1
  set A2 := c3 * K1 with hA2
  have hA10 : 0 ≤ A1 := mul_nonneg hc3 (mul_nonneg hKe0 hw)
  have hA20 : 0 ≤ A2 := mul_nonneg hc3 hK10
  have hpt : ∀ θ ∈ S, ∀ φ ∈ S, ‖F1 sys L N n j B θc θ φ - F2 sys L N n j C θc θ φ‖ ≤
      A1 * gc n θ φ + A2 * gx n (N : ℝ) j B C θ φ + A2 * gx n (n : ℝ) j B C θ φ +
        A2 * gy n j B C θ φ := by
    intro θ _ φ _
    refine (norm_F_sub_le hL hn hb hc hθc θ φ).trans (le_of_eq ?_)
    rw [hA1, hA2, hc3d, hKe, hK1, hwd]; ring
  have hsum : ‖∑ θ ∈ S, ∑ φ ∈ S, (F1 sys L N n j B θc θ φ - F2 sys L N n j C θc θ φ)‖ ≤
      A1 * ∑ θ ∈ S, ∑ φ ∈ S, gc n θ φ + A2 * ∑ θ ∈ S, ∑ φ ∈ S, gx n (N : ℝ) j B C θ φ +
        A2 * ∑ θ ∈ S, ∑ φ ∈ S, gx n (n : ℝ) j B C θ φ + A2 * ∑ θ ∈ S, ∑ φ ∈ S, gy n j B C θ φ := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun θ _ => norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun θ hθ => Finset.sum_le_sum fun φ hφ => hpt θ hθ φ hφ).trans
      (le_of_eq ?_)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := sum_gc_le S (n := n) (by omega)
  have h2 := sum_gx_le S n hN1 hcb' hBCN
  have h3 := sum_gx_le S n (by linarith : (1 : ℝ) ≤ n) hcb' hBC
  have h4 := sum_gy_le S hn hcb' hBC
  have hN3 : (n : ℝ) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ hn0.le hnN' 3
  have hW : 0 ≤ 864 * (2 * 16 * 8864 * (12 * (1 + w))) := by positivity
  have h2' : ∑ θ ∈ S, ∑ φ ∈ S, gx n (N : ℝ) j B C θ φ ≤
      864 * (2 * 16 * 8864 * (12 * (1 + w))) / (n : ℝ) ^ 3 := by
    have e1 : 1 + wgt j B + wgt j C = 1 + w := by rw [hwd]; ring
    rw [e1] at h2
    exact h2.trans (div_le_div_of_nonneg_left hW (by positivity) hN3)
  have h3' : ∑ θ ∈ S, ∑ φ ∈ S, gx n (n : ℝ) j B C θ φ ≤
      864 * (2 * 16 * 8864 * (12 * (1 + w))) / (n : ℝ) ^ 3 := by
    refine h3.trans (le_of_eq ?_)
    rw [hwd]; ring
  have h4' : ∑ θ ∈ S, ∑ φ ∈ S, gy n j B C θ φ ≤
      1316 / ((n : ℝ) / 2) * (16 * 8864 * (12 * (1 + w)) / (n : ℝ) ^ 2) := by
    refine h4.trans (le_of_eq ?_)
    rw [hwd]; ring
  have hfin : A1 * (864 * (64 * 277) / (n : ℝ) ^ 3) +
      A2 * (864 * (2 * 16 * 8864 * (12 * (1 + w))) / (n : ℝ) ^ 3) +
      A2 * (864 * (2 * 16 * 8864 * (12 * (1 + w))) / (n : ℝ) ^ 3) +
      A2 * (1316 / ((n : ℝ) / 2) * (16 * 8864 * (12 * (1 + w)) / (n : ℝ) ^ 2)) +
      c3 * Ke * (864 * (64 * 277)) / (n : ℝ) ^ 3 =
      Kss sys L j * (1 + wgt j B + wgt j C) / (n : ℝ) ^ 3 := by
    unfold Kss
    rw [hA1, hA2, ← hc3d, ← hKe, ← hK1]
    have : (n : ℝ) ≠ 0 := hn0.ne'
    field_simp
    rw [hwd]
    ring
  have hextra : 0 ≤ c3 * Ke * (864 * (64 * 277)) / (n : ℝ) ^ 3 := by positivity
  have hlam := lamC_le_one sys p₀ j
  have hbound : ‖∑ θ ∈ S, ∑ φ ∈ S, (F1 sys L N n j B θc θ φ - F2 sys L N n j C θc θ φ)‖ ≤
      Kss sys L j * (1 + wgt j B + wgt j C) / (n : ℝ) ^ 3 := by
    refine hsum.trans ?_
    have := mul_le_mul_of_nonneg_left h1 hA10
    have := mul_le_mul_of_nonneg_left h2' hA20
    have := mul_le_mul_of_nonneg_left h3' hA20
    have := mul_le_mul_of_nonneg_left h4' hA20
    linarith
  calc lamC sys p₀ j * ‖∑ θ ∈ S, ∑ φ ∈ S, (F1 sys L N n j B θc θ φ - F2 sys L N n j C θc θ φ)‖ ≤
      1 * ‖∑ θ ∈ S, ∑ φ ∈ S, (F1 sys L N n j B θc θ φ - F2 sys L N n j C θc θ φ)‖ :=
        mul_le_mul_of_nonneg_right hlam (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hbound

end Pair

end FSFlux
