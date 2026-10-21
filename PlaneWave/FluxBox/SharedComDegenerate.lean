import PlaneWave.FluxBox.SharedComCoordinate

/-!
# Flux route, stage 3, part 41: the shared com words, degenerate triples

For the shared word `R Y_{j₂} W_{j₁}` (long first hop, `t ∈ j₂` not moved by `j₁`) against an outer
channel `j₃` moving `t` without a common coordinate (the **degenerate** triples), the C×C kernel is
bounded pointwise and the trace closes on the `(j₁, j₂)`-fibres:

* geometry (`long_of_cold_notQ`, `eq_of_two_routes`, `rho_two_ge`): the outer hop is long
  (`|θ₃| ≥ n/8`), the intermediate `d` is unique, and `|θ₂| ≥ |θ₃| - 2 c_* n` (register `t`);
* **the pointwise bound** (`Kdeg_le`): `K(c,b) = Σ_{f∉Q} |w₃(f,c)| ω_F(f) Σ_d |y₂(f,d)| W^L₁(d,b)
  ≤ κ₀ ≈ n⁻⁴ (1 + log N)` for cold `c, b`;
* **the fibre trace** (`fibre_l1_le`, `tri_deg_le`): `K(c,b) ≠ 0` forces `ℓ(c) = ℓ(b)` for a label `ℓ`
  killed by `j₁, j₂, j₃`, injective with `(k_a, k_t)` on its fibres, and
  `(Σ_F x)² ≤ (Σ_{F∩C} 1/ω)(Σ_F ω x²)`, `ω = w32(k_a)(1 + |k_t|²)`, `Σ_{F∩C} 1/ω ≲ log n · c_* n`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section DegGeom

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

omit [Fintype ν] in
/-- **From cold to outside the bulk ball the hop is long**: `|θ|² ≥ (n/8)²`. -/
lemma long_of_cold_notQ {j : Ch eta} {f c : Cfg eta N} (hc : InC (n : ℝ) (cst sys) (cidx N c))
    (hf : ¬ InQ (n : ℝ) (cidx N f)) (h : OnCh j (cidx N f) (cidx N c)) :
    ((n : ℝ) / 8) ^ 2 ≤ FSLattice.lsq (chT N j f c) := by
  obtain ⟨r, hr⟩ := exists_rho_gt_of_notQ hf
  have h1 := rho_le_of_inC hc r
  have h2 := FSChannel.rho_le_add_rho_sub (cidx N f r) (cidx N c r)
  have h3 := rho_reg_hop_le h r
  have hcs := mul_le_mul_of_nonneg_right (cst_le32 sys) (Nat.cast_nonneg (α := ℝ) n)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : (n : ℝ) / 8 ≤ FSChannel.rho (chT N j f c) := by
    show (n : ℝ) / 8 ≤ FSChannel.rho (cidx N f (lead j) - cidx N c (lead j))
    linarith
  rw [← FSChannel.rho_sq]
  exact pow_le_pow_left₀ (by positivity) h4 2

omit [Fintype ν] in
/-- On a hop, a moved register changes by the transfer up to sign. -/
lemma rho_moved_hop {j : Ch eta} {q p : Cf eta} (h : OnCh j q p) {r : Fin eta} (hr : r ∈ moved j) :
    FSChannel.rho (q r - p r) = FSChannel.rho (q (lead j) - p (lead j)) := by
  have e : q = p + tr j (q (lead j) - p (lead j)) := h
  generalize q (lead j) - p (lead j) = θ at e ⊢
  have h1 : q r - p r = tr j θ r := by rw [e, Pi.add_apply]; abel
  rw [h1]
  rcases tr_apply_moved j θ hr with h2 | h2
  · rw [h2]
  · rw [h2, rho_neg']

omit [Fintype ν] in
/-- On a hop, an unmoved register is unchanged. -/
lemma reg_hop_not_moved {j : Ch eta} {q p : Cf eta} (h : OnCh j q p) {r : Fin eta} (hr : r ∉ moved j) :
    q r = p r := by
  rw [h, Pi.add_apply, tr_apply_not_moved j _ hr, add_zero]

omit [Fintype ν] in
/-- **The intermediate of a two-hop route is unique** when `j₂` moves a register `t` not moved by `j₁`. -/
lemma eq_of_two_routes {j₁ j₂ : Ch eta} {t : Fin eta} (ht2 : t ∈ moved j₂) (ht1 : t ∉ moved j₁)
    {f d d' b : Cfg eta N} (h₂ : OnCh j₂ (cidx N f) (cidx N d)) (h₁ : OnCh j₁ (cidx N d) (cidx N b))
    (h₂' : OnCh j₂ (cidx N f) (cidx N d')) (h₁' : OnCh j₁ (cidx N d') (cidx N b)) : d = d' := by
  have hdt : cidx N d t = cidx N d' t := by
    rw [reg_hop_not_moved h₁ ht1, reg_hop_not_moved h₁' ht1]
  -- `d` and `d'` on the `j₂`-line of `f`
  have hdd' : OnCh j₂ (cidx N d') (cidx N d) := onCh_trans h₂ h₂'
  have e : cidx N d' = cidx N d + tr j₂ (cidx N d' (lead j₂) - cidx N d (lead j₂)) := hdd'
  set θ := cidx N d' (lead j₂) - cidx N d (lead j₂)
  have hθ : tr j₂ θ t = 0 := by
    have := congrFun e t
    rw [Pi.add_apply, hdt] at this
    exact (left_eq_add.mp this)
  have hθ0 : θ = 0 := by
    rcases tr_apply_moved j₂ θ ht2 with h | h
    · rw [h] at hθ; exact hθ
    · rw [h] at hθ; exact neg_eq_zero.mp hθ
  apply finiteConfigLatticeIndex_injective eta N
  show cidx N d = cidx N d'
  rw [e, hθ0, tr_zero, add_zero]

omit [Fintype ν] in
/-- **The two outer transfers at the register `t`**: `|θ₂| ≥ |θ₃| - 2 c_* n`. -/
lemma rho_two_ge {j₁ j₂ j₃ : Ch eta} {t : Fin eta} (ht2 : t ∈ moved j₂) (ht3 : t ∈ moved j₃)
    (ht1 : t ∉ moved j₁) {f d b c : Cfg eta N} (hb : InC (n : ℝ) (cst sys) (cidx N b))
    (hc : InC (n : ℝ) (cst sys) (cidx N c)) (h₃ : OnCh j₃ (cidx N f) (cidx N c))
    (h₂ : OnCh j₂ (cidx N f) (cidx N d)) (h₁ : OnCh j₁ (cidx N d) (cidx N b)) :
    FSChannel.rho (chT N j₃ f c) - 2 * (cst sys * n) ≤ FSChannel.rho (chT N j₂ f d) := by
  have e3 := rho_moved_hop h₃ ht3
  have e2 := rho_moved_hop h₂ ht2
  have hdt := reg_hop_not_moved h₁ ht1
  have hbc := rho_sub_cold_le hb hc t
  -- `f_t - c_t = (f_t - d_t) + (b_t - c_t)`
  have e : cidx N f t - cidx N c t = (cidx N f t - cidx N d t) + (cidx N b t - cidx N c t) := by
    rw [hdt]; abel
  have h := FSChannel.rho_add_le (cidx N f t - cidx N d t) (cidx N b t - cidx N c t)
  rw [← e, e3, e2] at h
  show FSChannel.rho (cidx N f (lead j₃) - cidx N c (lead j₃)) - 2 * (cst sys * n) ≤
    FSChannel.rho (cidx N f (lead j₂) - cidx N d (lead j₂))
  linarith

omit [Fintype ν] in
/-- A sum with at most one nonzero term is bounded by any common bound. -/
lemma sum_le_of_unique {ι : Type*} (s : Finset ι) (F : ι → ℝ) (_hF0 : ∀ i, 0 ≤ F i) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ i, F i ≤ B) (hu : ∀ i i', F i ≠ 0 → F i' ≠ 0 → i = i') :
    ∑ i ∈ s, F i ≤ B := by
  classical
  by_cases h : ∃ i ∈ s, F i ≠ 0
  · obtain ⟨i, hi, hFi⟩ := h
    rw [Finset.sum_eq_single i]
    · exact hB i
    · intro i' _ hne
      by_contra h'
      exact hne (hu i' i h' hFi)
    · intro h'; exact absurd hi h'
  · push Not at h
    rw [Finset.sum_eq_zero h]
    exact hB0

end DegGeom

/-! ## The pointwise bound -/

section DegPoint

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

variable (sys L) in
/-- The pointwise constant of a degenerate shared word. -/
noncomputable def kap0 (N n : ℕ) (j₁ j₂ j₃ : Ch eta) : ℝ :=
  32 * mmax sys / gF L ^ 2 / (n : ℝ) ^ 2 * (chC sys L j₁ / (cst sys * n) ^ 2) * chC sys L j₃ *
    (4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) * (277 / ((n : ℝ) / 8)) +
      chC sys L j₂ * LamS (2 * N))

omit [Fintype ν] in
lemma lsq_le_of_mem_box2 {N : ℕ} {θ : Lattice3} (h : θ ∈ FSLattice.box (2 * N)) :
    FSLattice.lsq θ ≤ 3 * ((2 * N : ℕ) : ℝ) ^ 2 := by
  rw [FSLattice.mem_box] at h
  have hc : ∀ i, ((θ i : ℤ) : ℝ) ^ 2 ≤ ((2 * N : ℕ) : ℝ) ^ 2 := by
    intro i
    have h1 := (h i).1
    have h2 := (h i).2
    have h1' : -((2 * N : ℕ) : ℝ) ≤ ((θ i : ℤ) : ℝ) := by
      have : ((-((2 * N : ℕ) : ℤ) : ℤ) : ℝ) ≤ ((θ i : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast at this ⊢; linarith
    have h2' : ((θ i : ℤ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
      have : ((θ i : ℤ) : ℝ) ≤ (((2 * N : ℕ) : ℤ) : ℝ) := by exact_mod_cast h2
      push_cast at this ⊢; linarith
    nlinarith
  unfold FSLattice.lsq
  linarith [hc 0, hc 1, hc 2]

lemma yj_onCh {j : Ch eta} {f d : Cfg eta N} (h : yj sys L p₀ N j f d ≠ 0) :
    OnCh j (cidx N f) (cidx N d) := by
  by_contra hj; apply h; unfold yj ycKc; rw [if_neg hj]

lemma WL_spec {j : Ch eta} {d b : Cfg eta N} (h : WL sys L N n j d b ≠ 0) :
    OnCh j (cidx N d) (cidx N b) ∧ InC (n : ℝ) (cst sys) (cidx N b) ∧
      (cst sys * n) ^ 2 ≤ FSLattice.lsq (chT N j d b) := by
  by_contra h'; apply h; unfold WL; rw [if_neg h']

lemma WL_le_C1 (hL : 0 < L) (hn : 1 ≤ n) (j : Ch eta) (d b : Cfg eta N) :
    WL sys L N n j d b ≤ chC sys L j / (cst sys * n) ^ 2 := by
  have hc := chC_nonneg sys hL j
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcn : 0 < cst sys * n := mul_pos (cst_pos sys) hn0
  unfold WL
  split_ifs with h
  · exact div_le_div_of_nonneg_left hc (by positivity) h.2.2
  · positivity

/-- **The inner sum of a degenerate shared word** (one intermediate). -/
lemma inner_deg_le (hL : 0 < L) (hn : 8 ≤ n) {j₁ j₂ j₃ : Ch eta} {t : Fin eta}
    (ht2 : t ∈ moved j₂) (ht3 : t ∈ moved j₃) (ht1 : t ∉ moved j₁) {f c b : Cfg eta N}
    (hc : InC (n : ℝ) (cst sys) (cidx N c)) (hb : InC (n : ℝ) (cst sys) (cidx N b))
    (hf : ¬ InQ (n : ℝ) (cidx N f)) (h₃ : OnCh j₃ (cidx N f) (cidx N c)) :
    ∑ d, ‖yj sys L p₀ N j₂ f d‖ * WL sys L N n j₁ d b ≤
      chC sys L j₁ / (cst sys * n) ^ 2 *
        (4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) / FSLattice.lsq (chT N j₃ f c) +
          chC sys L j₂ / FSChannel.rho (chT N j₃ f c)) := by
  classical
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc₁ := chC_nonneg sys hL j₁
  have hc₂ := chC_nonneg sys hL j₂
  have hcs := mul_le_mul_of_nonneg_right (cst_le32 sys) hn0.le
  have hcn : 0 < cst sys * n := mul_pos (cst_pos sys) hn0
  have hfar := long_of_cold_notQ hc hf h₃
  have hl3 : 0 < FSLattice.lsq (chT N j₃ f c) := lt_of_lt_of_le (by positivity) hfar
  have hρ3 : (n : ℝ) / 8 ≤ FSChannel.rho (chT N j₃ f c) := rho_ge_of_lsq hfar
  have hρ30 : 0 < FSChannel.rho (chT N j₃ f c) := by linarith
  have hl3r := lsq_eq_rho_sq (chT N j₃ f c)
  set Y := 4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) / FSLattice.lsq (chT N j₃ f c) +
    chC sys L j₂ / FSChannel.rho (chT N j₃ f c) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hC10 : 0 ≤ chC sys L j₁ / (cst sys * n) ^ 2 := by positivity
  apply sum_le_of_unique _ _ (fun d => mul_nonneg (norm_nonneg _) (WL_nonneg hL j₁ d b))
    (mul_nonneg hC10 hY0)
  · intro d
    by_cases hy : yj sys L p₀ N j₂ f d = 0
    · rw [hy, norm_zero, zero_mul]; exact mul_nonneg hC10 hY0
    by_cases hwl : WL sys L N n j₁ d b = 0
    · rw [hwl, mul_zero]; exact mul_nonneg hC10 hY0
    have h₂ := yj_onCh hy
    have hWL := WL_spec hwl
    have hya := norm_yj_align_le (sys := sys) (L := L) (p₀ := p₀) hL ht2 f d
    have hdt : cidx N d t = cidx N b t := reg_hop_not_moved hWL.1 ht1
    have hbt := rho_le_of_inC hb t
    rw [hdt] at hya
    have h2ge := rho_two_ge (sys := sys) (n := n) ht2 ht3 ht1 hb hc h₃ h₂ hWL.1
    have hρ2 : FSChannel.rho (chT N j₃ f c) / 2 ≤ FSChannel.rho (chT N j₂ f d) := by linarith
    have hρ20 : 0 < FSChannel.rho (chT N j₂ f d) := by linarith
    have hl2 : FSLattice.lsq (chT N j₃ f c) / 4 ≤ FSLattice.lsq (chT N j₂ f d) := by
      rw [hl3r, lsq_eq_rho_sq (chT N j₂ f d)]
      have := pow_le_pow_left₀ (by positivity) hρ2 2
      nlinarith
    have hl20 : 0 < FSLattice.lsq (chT N j₂ f d) := by linarith
    have hy1 : chC sys L j₂ * (1 + 3 * FSChannel.rho (cidx N b t)) / FSLattice.lsq (chT N j₂ f d) ≤
        4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) / FSLattice.lsq (chT N j₃ f c) := by
      have h1 : chC sys L j₂ * (1 + 3 * FSChannel.rho (cidx N b t)) ≤
          chC sys L j₂ * (1 + 3 * (cst sys * n)) := mul_le_mul_of_nonneg_left (by linarith) hc₂
      calc chC sys L j₂ * (1 + 3 * FSChannel.rho (cidx N b t)) / FSLattice.lsq (chT N j₂ f d) ≤
          chC sys L j₂ * (1 + 3 * (cst sys * n)) / (FSLattice.lsq (chT N j₃ f c) / 4) :=
            div_le_div₀ (by positivity) h1 (by positivity) hl2
        _ = 4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) / FSLattice.lsq (chT N j₃ f c) := by
            field_simp
    have hy2 : chC sys L j₂ / 2 / FSChannel.rho (chT N j₂ f d) ≤
        chC sys L j₂ / FSChannel.rho (chT N j₃ f c) := by
      rw [div_div]
      apply div_le_div_of_nonneg_left hc₂ hρ30
      linarith
    have hyb : ‖yj sys L p₀ N j₂ f d‖ ≤ Y := by rw [hY]; linarith
    calc ‖yj sys L p₀ N j₂ f d‖ * WL sys L N n j₁ d b ≤ Y * (chC sys L j₁ / (cst sys * n) ^ 2) :=
          mul_le_mul hyb (WL_le_C1 hL (by omega) j₁ d b) (WL_nonneg hL j₁ d b) hY0
      _ = _ := by ring
  · intro d d' hd hd'
    have hy : yj sys L p₀ N j₂ f d ≠ 0 := fun h0 => hd (by rw [h0, norm_zero, zero_mul])
    have hwl : WL sys L N n j₁ d b ≠ 0 := fun h0 => hd (by rw [h0, mul_zero])
    have hy' : yj sys L p₀ N j₂ f d' ≠ 0 := fun h0 => hd' (by rw [h0, norm_zero, zero_mul])
    have hwl' : WL sys L N n j₁ d' b ≠ 0 := fun h0 => hd' (by rw [h0, mul_zero])
    exact eq_of_two_routes ht2 ht1 (yj_onCh hy) (WL_spec hwl).1 (yj_onCh hy') (WL_spec hwl').1

open Classical in
/-- The majorant of one outer configuration. -/
lemma term_deg_le (hL : 0 < L) (hn : 8 ≤ n) {j₁ j₂ j₃ : Ch eta} {t : Fin eta}
    (ht2 : t ∈ moved j₂) (ht3 : t ∈ moved j₃) (ht1 : t ∉ moved j₁) {c b : Cfg eta N}
    (hc : InC (n : ℝ) (cst sys) (cidx N c)) (hb : InC (n : ℝ) (cst sys) (cidx N b)) (f : Cfg eta N) :
    (if InQ (n : ℝ) (cidx N f) then 0 else ‖wj sys L N j₃ f c‖) * farW sys L N n f *
        (∑ d, ‖yj sys L p₀ N j₂ f d‖ * WL sys L N n j₁ d b) ≤
      if OnCh j₃ (cidx N f) (cidx N c) then
        (if ((n : ℝ) / 8) ^ 2 ≤ FSLattice.lsq (chT N j₃ f c) then
          32 * mmax sys / gF L ^ 2 / (n : ℝ) ^ 2 * (chC sys L j₁ / (cst sys * n) ^ 2) * chC sys L j₃ *
            (4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) * (1 / FSLattice.lsq (chT N j₃ f c) ^ 2) +
              chC sys L j₂ * (1 / FSChannel.rho (chT N j₃ f c) ^ 3)) else 0) else 0 := by
  classical
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hc₁ := chC_nonneg sys hL j₁
  have hc₂ := chC_nonneg sys hL j₂
  have hc₃ := chC_nonneg sys hL j₃
  have hcn : 0 < cst sys * n := mul_pos (cst_pos sys) hn0
  have hS0 : 0 ≤ ∑ d, ‖yj sys L p₀ N j₂ f d‖ * WL sys L N n j₁ d b :=
    Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _) (WL_nonneg hL j₁ d b)
  have hRHS0 : 0 ≤ (if OnCh j₃ (cidx N f) (cidx N c) then
        (if ((n : ℝ) / 8) ^ 2 ≤ FSLattice.lsq (chT N j₃ f c) then
          32 * mmax sys / gF L ^ 2 / (n : ℝ) ^ 2 * (chC sys L j₁ / (cst sys * n) ^ 2) * chC sys L j₃ *
            (4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) * (1 / FSLattice.lsq (chT N j₃ f c) ^ 2) +
              chC sys L j₂ * (1 / FSChannel.rho (chT N j₃ f c) ^ 3)) else 0) else 0) := by
    have := FSLattice.lsq_nonneg (chT N j₃ f c)
    have := FSChannel.rho_nonneg (chT N j₃ f c)
    split_ifs <;> positivity
  by_cases hf : InQ (n : ℝ) (cidx N f)
  · rw [if_pos hf, zero_mul, zero_mul]; exact hRHS0
  rw [if_neg hf]
  by_cases h₃ : OnCh j₃ (cidx N f) (cidx N c)
  swap
  · rw [wj_eq_zero_of_not_onCh h₃, norm_zero, zero_mul, zero_mul]; exact hRHS0
  have hfar := long_of_cold_notQ hc hf h₃
  rw [if_pos h₃, if_pos hfar]
  have hl3 : 0 < FSLattice.lsq (chT N j₃ f c) := lt_of_lt_of_le (by positivity) hfar
  have hρ30 : 0 < FSChannel.rho (chT N j₃ f c) := rho_pos_of_lsq_pos hl3
  have hl3r := lsq_eq_rho_sq (chT N j₃ f c)
  have hw3 : ‖wj sys L N j₃ f c‖ ≤ chC sys L j₃ / FSLattice.lsq (chT N j₃ f c) := by
    have := norm_wj_le (sys := sys) hL j₃ f c
    rwa [if_pos h₃] at this
  have hfw : farW sys L N n f ≤ 32 * mmax sys / gF L ^ 2 / (n : ℝ) ^ 2 := by
    have h1 := farW_le_max (sys := sys) (n := n) hL (by omega) (A := {lead j₃}) (by simp) f
    exact h1.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (le_max_left _ _))
  have hin := inner_deg_le (p₀ := p₀) hL hn ht2 ht3 ht1 hc hb hf h₃
  calc ‖wj sys L N j₃ f c‖ * farW sys L N n f * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * WL sys L N n j₁ d b) ≤
      chC sys L j₃ / FSLattice.lsq (chT N j₃ f c) * (32 * mmax sys / gF L ^ 2 / (n : ℝ) ^ 2) *
        (chC sys L j₁ / (cst sys * n) ^ 2 *
          (4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) / FSLattice.lsq (chT N j₃ f c) +
            chC sys L j₂ / FSChannel.rho (chT N j₃ f c))) :=
        mul_le_mul (mul_le_mul hw3 hfw (farW_nonneg f) (by positivity)) hin hS0 (by positivity)
    _ = _ := by
        rw [hl3r]
        field_simp

open Classical in
/-- **The pointwise bound of a degenerate shared word**: for cold `c, b`,
`Σ_{f∉Q} |w₃(f,c)| ω_F(f) Σ_d |y₂(f,d)| W^L₁(d,b) ≤ κ₀`. -/
theorem Kdeg_le (hL : 0 < L) (hn : 8 ≤ n) (hN : 1 ≤ N) {j₁ j₂ j₃ : Ch eta} {t : Fin eta}
    (ht2 : t ∈ moved j₂) (ht3 : t ∈ moved j₃) (ht1 : t ∉ moved j₁) {c b : Cfg eta N}
    (hc : InC (n : ℝ) (cst sys) (cidx N c)) (hb : InC (n : ℝ) (cst sys) (cidx N b)) :
    ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else ‖wj sys L N j₃ f c‖) * farW sys L N n f *
        (∑ d, ‖yj sys L p₀ N j₂ f d‖ * WL sys L N n j₁ d b) ≤ kap0 sys L N n j₁ j₂ j₃ := by
  classical
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hc₁ := chC_nonneg sys hL j₁
  have hc₂ := chC_nonneg sys hL j₂
  have hc₃ := chC_nonneg sys hL j₃
  have hcn : 0 < cst sys * n := mul_pos (cst_pos sys) hn0
  have hR1 : (1 : ℝ) ≤ (n : ℝ) / 8 := by linarith
  set K0 := 32 * mmax sys / gF L ^ 2 / (n : ℝ) ^ 2 * (chC sys L j₁ / (cst sys * n) ^ 2) *
    chC sys L j₃ with hK0
  have hK00 : 0 ≤ K0 := by positivity
  set H : Lattice3 → ℝ := fun θ => if ((n : ℝ) / 8) ^ 2 ≤ FSLattice.lsq θ then
    K0 * (4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) * (1 / FSLattice.lsq θ ^ 2) +
      chC sys L j₂ * (1 / FSChannel.rho θ ^ 3)) else 0 with hH
  have hpt : ∀ f, (if InQ (n : ℝ) (cidx N f) then 0 else ‖wj sys L N j₃ f c‖) * farW sys L N n f *
      (∑ d, ‖yj sys L p₀ N j₂ f d‖ * WL sys L N n j₁ d b) ≤
      if OnCh j₃ (cidx N f) (cidx N c) then H (chT N j₃ f c) else 0 := fun f =>
    term_deg_le (p₀ := p₀) hL hn ht2 ht3 ht1 hc hb f
  refine (Finset.sum_le_sum fun f _ => hpt f).trans ?_
  rw [sum_line_eq j₃ c H]
  have hfarsum : ∑ θ ∈ lineT N j₃ c,
      (if ((n : ℝ) / 8) ^ 2 ≤ FSLattice.lsq θ then 1 / FSLattice.lsq θ ^ 2 else 0) ≤
      277 / ((n : ℝ) / 8) := by
    refine le_trans ?_ (sum_inv_max_sq_le (lineT N j₃ c) hR1)
    refine Finset.sum_le_sum fun θ _ => ?_
    split_ifs with h
    · rw [max_eq_right h]
    · exact div_nonneg zero_le_one (pow_nonneg (le_trans (sq_nonneg _) (le_max_left _ _)) 2)
  have hcube : ∑ θ ∈ lineT N j₃ c,
      (if ((n : ℝ) / 8) ^ 2 ≤ FSLattice.lsq θ then 1 / FSChannel.rho θ ^ 3 else 0) ≤
      LamS (2 * N) := by
    rw [← Finset.sum_filter]
    apply sum_inv_rho_cube_image_le _ id (fun x _ y _ h => h) (by omega)
    · intro θ hθ h0
      have h := (Finset.mem_filter.mp hθ).2
      simp only [id] at h0
      rw [h0, lsq_zero'] at h
      have : (0 : ℝ) < ((n : ℝ) / 8) ^ 2 := by positivity
      linarith
    · intro θ hθ
      have h := (Finset.mem_filter.mp hθ).1
      unfold lineT at h
      exact lsq_le_of_mem_box2 (Finset.mem_filter.mp h).1
  have e : ∀ θ, H θ = K0 * (4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) *
      (if ((n : ℝ) / 8) ^ 2 ≤ FSLattice.lsq θ then 1 / FSLattice.lsq θ ^ 2 else 0) +
      chC sys L j₂ * (if ((n : ℝ) / 8) ^ 2 ≤ FSLattice.lsq θ then 1 / FSChannel.rho θ ^ 3 else 0)) := by
    intro θ
    simp only [hH]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun θ _ => e θ, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  unfold kap0
  rw [← hK0]
  apply mul_le_mul_of_nonneg_left _ hK00
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left hfarsum (by positivity)
  · exact mul_le_mul_of_nonneg_left hcube hc₂

end DegPoint

/-! ## The fibre trace -/

section Fibre

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

variable (sys) in
/-- The fibre constant `125 (log₂ m + 2)(1 + 26 c_* n)`, `m = ⌊c_* n⌋ + 1`. -/
noncomputable def Kfib (n : ℕ) : ℝ :=
  125 * (Nat.log 2 (⌊cst sys * n⌋₊ + 1) + 2) * (1 + 26 * (cst sys * n))

omit [Fintype ν] in
lemma Kfib_nonneg (n : ℕ) : 0 ≤ Kfib sys n := by
  unfold Kfib
  have := cst_mul_nonneg (sys := sys) (n := n)
  positivity

omit [Fintype ν] in
open Classical in
/-- **The cold part of a fibre**: `Σ_{c ∈ F ∩ C} 1/(w32(c_a)(1 + |c_t|²)) ≤ K_fib` when
`c ↦ (c_a, c_t)` is injective on `F`. -/
lemma sum_fibre_inv_le (F : Finset (Cfg eta N)) {a t : Fin eta}
    (hinj : Set.InjOn (fun c : Cfg eta N => (cidx N c a, cidx N c t)) ↑F)
    (hC : ∀ c ∈ F, InC (n : ℝ) (cst sys) (cidx N c)) :
    ∑ c ∈ F, 1 / (w32 (cidx N c a) * (1 + FSLattice.lsq (cidx N c t))) ≤ Kfib sys n := by
  classical
  set R := cst sys * n with hR
  have hR0 : 0 ≤ R := cst_mul_nonneg
  set m := ⌊R⌋₊ + 1 with hm
  set Y : Finset Lattice3 := (FSLattice.box m).filter (fun y => FSLattice.lsq y ≤ R ^ 2) with hY
  have hmem : ∀ c ∈ F, ∀ r, cidx N c r ∈ Y := by
    intro c hc r
    have hl : FSLattice.lsq (cidx N c r) ≤ R ^ 2 := by
      have h := rho_le_of_inC (hC c hc) r
      rw [lsq_eq_rho_sq]
      exact pow_le_pow_left₀ (FSChannel.rho_nonneg _) h 2
    refine Finset.mem_filter.mpr ⟨?_, hl⟩
    have hb := FSLattice.mem_box_floor_of_lsq_le hR0 hl
    rw [FSLattice.mem_box] at hb ⊢
    intro i
    have := hb i
    constructor <;> omega
  -- the image in `Y ×ˢ Y`
  set g : Lattice3 × Lattice3 → ℝ := fun yz => 1 / w32 yz.1 * (1 / (1 + FSLattice.lsq yz.2)) with hg
  have hg0 : ∀ yz, 0 ≤ g yz := fun yz => by
    simp only [hg]
    have := w32_pos yz.1
    have := FSLattice.lsq_nonneg yz.2
    positivity
  have e1 : ∑ c ∈ F, 1 / (w32 (cidx N c a) * (1 + FSLattice.lsq (cidx N c t))) =
      ∑ yz ∈ F.image (fun c => (cidx N c a, cidx N c t)), g yz := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hg]
    rw [one_div_mul_one_div]
  rw [e1]
  have hsub : F.image (fun c => (cidx N c a, cidx N c t)) ⊆ Y ×ˢ Y := by
    intro yz hyz
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hyz
    exact Finset.mem_product.mpr ⟨hmem c hc a, hmem c hc t⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun yz _ _ => hg0 yz).trans ?_
  rw [Finset.sum_product]
  simp only [hg]
  rw [← Finset.sum_mul_sum]
  have hm1 : 1 ≤ m := by simp [hm]
  have h1 : ∑ y ∈ Y, 1 / w32 y ≤ 125 * (Nat.log 2 m + 2) := by
    have := sum_inv_w32_image_le Y id (fun x _ y _ h => h) hm1 (fun y hy => by
      have h := (Finset.mem_filter.mp hy).2
      simp only [id]
      have hRm : R ≤ m := by
        simp only [hm]; push_cast
        exact (Nat.lt_floor_add_one R).le
      have : R ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ hR0 hRm 2
      have := sq_nonneg (m : ℝ)
      linarith)
    simpa [one_div] using this
  have h2 : ∑ z ∈ Y, 1 / (1 + FSLattice.lsq z) ≤ 1 + 26 * R := by
    rw [← Finset.sum_filter_add_sum_filter_not Y (fun z => z = 0)]
    have h0 : ∑ z ∈ Y.filter (fun z => z = 0), 1 / (1 + FSLattice.lsq z) ≤ 1 := by
      have hsub : Y.filter (fun z => z = 0) ⊆ {0} := fun z hz => by
        simp [(Finset.mem_filter.mp hz).2]
      calc ∑ z ∈ Y.filter (fun z => z = 0), 1 / (1 + FSLattice.lsq z) ≤
          ∑ z ∈ ({0} : Finset Lattice3), 1 / (1 + FSLattice.lsq z) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => by
              have := FSLattice.lsq_nonneg z; positivity
        _ = 1 := by simp [lsq_zero']
    have hne : ∑ z ∈ Y.filter (fun z => ¬ z = 0), 1 / (1 + FSLattice.lsq z) ≤ 26 * R := by
      refine le_trans ?_ (sum_inv_lsq_filter_ball_le Y hR0)
      have hsub : Y.filter (fun z => ¬ z = 0) ⊆ Y.filter (fun ψ => ψ ≠ 0 ∧ FSLattice.lsq ψ ≤ R ^ 2) := by
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, hz.2, (Finset.mem_filter.mp hz.1).2⟩
      refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => by
        have := FSLattice.lsq_nonneg z; positivity)
      refine Finset.sum_le_sum fun z hz => ?_
      have hz0 := (Finset.mem_filter.mp hz).2
      have hl : 1 ≤ FSLattice.lsq z := one_le_latticeNormSq hz0
      apply one_div_le_one_div_of_le (by linarith)
      linarith
    linarith
  unfold Kfib
  rw [← hR, ← hm]
  have hA := Finset.sum_nonneg fun y (_ : y ∈ Y) => (by have := w32_pos y; positivity : (0 : ℝ) ≤ 1 / w32 y)
  exact mul_le_mul h1 h2 (Finset.sum_nonneg fun z _ => by have := FSLattice.lsq_nonneg z; positivity)
    (by positivity)

omit [Fintype ν] in
open Classical in
/-- **The fibre trace**: for a label `ℓ` injective with `(k_a, k_t)` on its fibres and `x ≥ 0` on
the cold ball, `Σ_{ℓc = ℓb} x_c x_b ≤ K_fib Σ_c w32(c_a)(1+|c_t|²) x_c²`. -/
theorem fibre_l1_le (ℓ : Cf eta → Cf eta) {a t : Fin eta}
    (hinj : ∀ k k' : Cf eta, ℓ k = ℓ k' → k a = k' a → k t = k' t → k = k')
    (x : Cfg eta N → ℝ) (_hx : ∀ b, 0 ≤ x b)
    (hxC : ∀ b, x b ≠ 0 → InC (n : ℝ) (cst sys) (cidx N b)) :
    ∑ c, ∑ b, (if ℓ (cidx N c) = ℓ (cidx N b) then x c * x b else 0) ≤
      Kfib sys n * ∑ c, w32 (cidx N c a) * (1 + FSLattice.lsq (cidx N c t)) * x c ^ 2 := by
  classical
  set ω : Cfg eta N → ℝ := fun c => w32 (cidx N c a) * (1 + FSLattice.lsq (cidx N c t)) with hω
  have hω0 : ∀ c, 0 < ω c := fun c => by
    simp only [hω]
    have := w32_pos (cidx N c a)
    have := FSLattice.lsq_nonneg (cidx N c t)
    positivity
  set lb : Cfg eta N → Cf eta := fun c => ℓ (cidx N c) with hlb
  set Fs : Cf eta → ℝ := fun l => ∑ b ∈ Finset.univ.filter (fun b => lb b = l), x b with hFs
  have e1 : ∑ c, ∑ b, (if ℓ (cidx N c) = ℓ (cidx N b) then x c * x b else 0) =
      ∑ c, x c * Fs (lb c) := by
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hFs, hlb]
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : ℓ (cidx N c) = ℓ (cidx N b)
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  rw [e1]
  have hmaps : ∀ c ∈ (Finset.univ : Finset (Cfg eta N)), lb c ∈ Finset.univ.image lb :=
    fun c _ => Finset.mem_image_of_mem lb (Finset.mem_univ c)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have e2 : ∀ l ∈ Finset.univ.image lb, ∑ c ∈ Finset.univ.filter (fun c => lb c = l), x c * Fs (lb c) =
      Fs l ^ 2 := by
    intro l _
    rw [sq, hFs]
    simp only
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [(Finset.mem_filter.mp hc).2]
  rw [Finset.sum_congr rfl e2]
  -- each fibre
  have hfib : ∀ l, Fs l ^ 2 ≤ Kfib sys n *
      ∑ c ∈ Finset.univ.filter (fun c => lb c = l), ω c * x c ^ 2 := by
    intro l
    set F := Finset.univ.filter (fun c => lb c = l) with hF
    set F' := F.filter (fun c => x c ≠ 0) with hF'
    have e3 : Fs l = ∑ c ∈ F', x c := by
      rw [hF', Finset.sum_filter_ne_zero]
    rw [e3]
    have hcs := sq_sum_le_inv_mul F' x ω hω0
    have hinv : ∑ c ∈ F', (ω c)⁻¹ ≤ Kfib sys n := by
      have h := sum_fibre_inv_le (sys := sys) (n := n) F' (a := a) (t := t) (fun c hc c' hc' he => by
        have hc1 := Finset.mem_filter.mp (Finset.mem_filter.mp hc).1
        have hc1' := Finset.mem_filter.mp (Finset.mem_filter.mp hc').1
        have hl : ℓ (cidx N c) = ℓ (cidx N c') := hc1.2.trans hc1'.2.symm
        simp only [Prod.mk.injEq] at he
        exact finiteConfigLatticeIndex_injective eta N (hinj _ _ hl he.1 he.2))
        (fun c hc => hxC c (Finset.mem_filter.mp hc).2)
      simpa [hω, one_div] using h
    have hsub : ∑ c ∈ F', ω c * x c ^ 2 ≤ ∑ c ∈ F, ω c * x c ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun c _ _ =>
        mul_nonneg (hω0 c).le (sq_nonneg _)
    have hS0 : 0 ≤ ∑ c ∈ F', ω c * x c ^ 2 := Finset.sum_nonneg fun c _ =>
      mul_nonneg (hω0 c).le (sq_nonneg _)
    calc (∑ c ∈ F', x c) ^ 2 ≤ (∑ c ∈ F', (ω c)⁻¹) * ∑ c ∈ F', ω c * x c ^ 2 := hcs
      _ ≤ Kfib sys n * ∑ c ∈ F, ω c * x c ^ 2 :=
          mul_le_mul hinv hsub hS0 (Kfib_nonneg n)
  refine (Finset.sum_le_sum fun l _ => hfib l).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hmaps]

end Fibre

/-! ## The degenerate trilinear bound -/

section DegTri

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

lemma kap0_nonneg (hL : 0 < L) (hn : 1 ≤ n) (N : ℕ) (j₁ j₂ j₃ : Ch eta) :
    0 ≤ kap0 sys L N n j₁ j₂ j₃ := by
  unfold kap0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have := chC_nonneg sys hL j₁
  have := chC_nonneg sys hL j₂
  have := chC_nonneg sys hL j₃
  have := cst_pos sys
  have := LamS_nonneg (2 * N)
  positivity

omit [Fintype ν] in
lemma lab_onCh_eq {ℓ : Cf eta → Cf eta} {j : Ch eta} (hℓ : ∀ k σ, ℓ (k + tr j σ) = ℓ k)
    {q p : Cf eta} (h : OnCh j q p) : ℓ q = ℓ p := by
  rw [h, hℓ]

open Classical in
/-- **The degenerate shared word against the outer channel `j₃`**:
`Σ_f G₃ ω_F (Σ_d |y₂| Σ_b W^L₁ x) ≤ κ₀ K_fib Σ_c w32(c_a)(1+|c_t|²) x_c²`. -/
theorem tri_deg_le (hL : 0 < L) (hn : 8 ≤ n) (hN : 1 ≤ N) {j₁ j₂ j₃ : Ch eta} {a t : Fin eta}
    (ht2 : t ∈ moved j₂) (ht3 : t ∈ moved j₃) (ht1 : t ∉ moved j₁) (ℓ : Cf eta → Cf eta)
    (hℓ1 : ∀ k σ, ℓ (k + tr j₁ σ) = ℓ k) (hℓ2 : ∀ k σ, ℓ (k + tr j₂ σ) = ℓ k)
    (hℓ3 : ∀ k σ, ℓ (k + tr j₃ σ) = ℓ k)
    (hinj : ∀ k k' : Cf eta, ℓ k = ℓ k' → k a = k' a → k t = k' t → k = k')
    (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b)
    (hxC : ∀ b, x b ≠ 0 → InC (n : ℝ) (cst sys) (cidx N b)) :
    ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else ∑ c, ‖wj sys L N j₃ f c‖ * x c) *
        farW sys L N n f * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ≤
      kap0 sys L N n j₁ j₂ j₃ *
        (Kfib sys n * ∑ c, w32 (cidx N c a) * (1 + FSLattice.lsq (cidx N c t)) * x c ^ 2) := by
  classical
  set A : Cfg eta N → Cfg eta N → ℝ := fun f c =>
    if InQ (n : ℝ) (cidx N f) then 0 else ‖wj sys L N j₃ f c‖ with hA
  set B : Cfg eta N → Cfg eta N → ℝ := fun f b =>
    ∑ d, ‖yj sys L p₀ N j₂ f d‖ * WL sys L N n j₁ d b with hB
  set K : Cfg eta N → Cfg eta N → ℝ := fun c b => ∑ f, A f c * farW sys L N n f * B f b with hK
  have hA0 : ∀ f c, 0 ≤ A f c := fun f c => by
    simp only [hA]; split_ifs
    · exact le_rfl
    · exact norm_nonneg _
  have hB0 : ∀ f b, 0 ≤ B f b := fun f b => Finset.sum_nonneg fun d _ =>
    mul_nonneg (norm_nonneg _) (WL_nonneg hL j₁ d b)
  -- the expansion
  have e1 : ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else ∑ c, ‖wj sys L N j₃ f c‖ * x c) *
      farW sys L N n f * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) =
      ∑ c, ∑ b, x c * x b * K c b := by
    have eG : ∀ f, (if InQ (n : ℝ) (cidx N f) then 0 else ∑ c, ‖wj sys L N j₃ f c‖ * x c) =
        ∑ c, A f c * x c := by
      intro f
      simp only [hA]
      split_ifs
      · simp
      · rfl
    have eS : ∀ f, ∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b =
        ∑ b, B f b * x b := by
      intro f
      simp only [hB, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => ?_
      ring
    calc ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else ∑ c, ‖wj sys L N j₃ f c‖ * x c) *
          farW sys L N n f * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) =
        ∑ f, ∑ c, ∑ b, x c * x b * (A f c * farW sys L N n f * B f b) := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [eG f, eS f, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
      _ = ∑ c, ∑ b, ∑ f, x c * x b * (A f c * farW sys L N n f * B f b) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ c, ∑ b, x c * x b * K c b := by
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
          simp only [hK]
          rw [Finset.mul_sum]
  rw [e1]
  have hk0 := kap0_nonneg (sys := sys) hL (by omega : 1 ≤ n) N j₁ j₂ j₃
  -- pointwise
  have hpt : ∀ c b, x c * x b * K c b ≤
      kap0 sys L N n j₁ j₂ j₃ * (if ℓ (cidx N c) = ℓ (cidx N b) then x c * x b else 0) := by
    intro c b
    have hxx := mul_nonneg (hx c) (hx b)
    have hR0 : 0 ≤ kap0 sys L N n j₁ j₂ j₃ * (if ℓ (cidx N c) = ℓ (cidx N b) then x c * x b else 0) := by
      split_ifs
      · exact mul_nonneg hk0 hxx
      · rw [mul_zero]
    by_cases hc0 : x c = 0
    · rw [hc0]; simp
    by_cases hb0 : x b = 0
    · rw [hb0]; simp
    have hc := hxC c hc0
    have hb := hxC b hb0
    by_cases hl : ℓ (cidx N c) = ℓ (cidx N b)
    · rw [if_pos hl]
      have hKle : K c b ≤ kap0 sys L N n j₁ j₂ j₃ := by
        simp only [hK, hA, hB]
        exact Kdeg_le (p₀ := p₀) hL hn hN ht2 ht3 ht1 hc hb
      calc x c * x b * K c b ≤ x c * x b * kap0 sys L N n j₁ j₂ j₃ :=
            mul_le_mul_of_nonneg_left hKle hxx
        _ = _ := by ring
    · rw [if_neg hl, mul_zero]
      have hK0 : K c b = 0 := by
        simp only [hK]
        refine Finset.sum_eq_zero fun f _ => ?_
        by_cases hAf : A f c = 0
        · rw [hAf, zero_mul, zero_mul]
        by_cases hBf : B f b = 0
        · rw [hBf, mul_zero]
        exfalso
        have h₃ : OnCh j₃ (cidx N f) (cidx N c) := by
          by_contra h
          apply hAf
          simp only [hA]
          split_ifs
          · rfl
          · rw [wj_eq_zero_of_not_onCh h, norm_zero]
        obtain ⟨d, _, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hBf
        have hy : yj sys L p₀ N j₂ f d ≠ 0 := fun h0 => hd (by rw [h0, norm_zero, zero_mul])
        have hwl : WL sys L N n j₁ d b ≠ 0 := fun h0 => hd (by rw [h0, mul_zero])
        have h₂ := yj_onCh hy
        have h₁ := (WL_spec hwl).1
        apply hl
        rw [← lab_onCh_eq hℓ3 h₃, lab_onCh_eq hℓ2 h₂, lab_onCh_eq hℓ1 h₁]
      rw [hK0, mul_zero]
  refine (Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun b _ => hpt c b).trans ?_
  simp only [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (fibre_l1_le ℓ hinj x hx hxC) hk0

end DegTri

end FSFlux
