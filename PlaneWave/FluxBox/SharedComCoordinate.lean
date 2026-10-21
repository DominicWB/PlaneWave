import PlaneWave.FluxBox.SharedComAlignment

/-!
# Flux route, stage 3, part 40: the shared com words with a common coordinate

The com word `R Y_{j₂} W_{j₁} Π_C` (and `F' Y_{j₂} R W_{j₁} Π_C`) with a long first hop, where `j₁` moves
exactly one register of the pair `j₂` (the **shared** case: `|Π_{j₂}|` is not constant on the
`j₁`-lines). Let `t` be the register of `j₂` not moved by `j₁`.

If a coordinate `ζ = regSum A` of `j₂` is killed by both `j₁` and the outer channel `j₃`, the C×C
trilinear form closes by a weighted Cauchy–Schwarz with `ω(f) = 1 + |ζ_f|²`:

* the outer side (`sum_far_G_sq_weight_le`): `ζ_f = ζ_c` on `j₃`-lines, so the weight moves to the
  cold input: `Σ_{f∉Q} ω G₃² ≤ (64 c₃)² (277/n) L²_{j₃}(x; 1 + |ζ|²)`;
* the word side (`Phi_shared`): with the alignment bound `|y₂| ≤ c₂(1+3|d_t|)/|θ|² + (c₂/2)/|θ|`, the
  A-part by the dual line Hardy on the `j₂`-lines and the I-part by Hardy twice, then the long first
  hop (`long_line_le`): `Σ_f ω_F² ω⁻¹ (Σ_d |y₂| Σ_b W^L₁ x)² ≲ n⁻⁵ (L²_{j₁}(x; 1+|ξ_t|²) + L²_{j₁}(x; 1+|ζ|²))`;
* **`tri_shared_le`**: `Σ_f G₃ ω_F (Σ_d |y₂| Σ_b W^L₁ x) ≤ (n Γ_G + n⁵ Φ)/(2n³)`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section SharedW

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

omit [Fintype ν] in
open Classical in
/-- A factor constant on the lines comes out of the line sums. -/
lemma lineSq_lab_mul (j : Ch eta) (Ω φ : Cf eta → ℝ) (x : Cfg eta N → ℝ) :
    lineSq j Ω (fun b => φ (lab N j b) * x b) = lineSq j (fun t => Ω t * φ t ^ 2) x := by
  unfold lineSq lineSum
  refine Finset.sum_congr rfl fun t _ => ?_
  have e : ∑ p ∈ Finset.univ.filter (fun p => lab N j p = t), φ (lab N j p) * x p =
      φ t * ∑ p ∈ Finset.univ.filter (fun p => lab N j p = t), x p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.mp hp).2]
  rw [e]; ring

omit [Fintype ν] in
lemma lineSq_mono_weight (j : Ch eta) {Ω Ω' : Cf eta → ℝ} (h : ∀ t, Ω t ≤ Ω' t) (x : Cfg eta N → ℝ) :
    lineSq j Ω x ≤ lineSq j Ω' x := by
  unfold lineSq
  exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_right (h t) (sq_nonneg _)

open Classical in
/-- **The outer side with a weight constant on the `j₃`-lines**. -/
theorem sum_far_G_sq_weight_le (hL : 0 < L) (hn : 1 ≤ n) (j : Ch eta) {A : Finset (Fin eta)}
    (hAj : ∀ σ, regSum A (tr j σ) = 0) (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b)
    (hxC : ∀ b, x b ≠ 0 → InC (n : ℝ) (cst sys) (cidx N b)) :
    ∑ f, (1 + FSLattice.lsq (regSum A (cidx N f))) *
        (if InQ (n : ℝ) (cidx N f) then 0 else ∑ c, ‖wj sys L N j f c‖ * x c) ^ 2 ≤
      (64 * chC sys L j) ^ 2 * (277 / n) * lineSq j (fun s => 1 + FSLattice.lsq (regSum A s)) x := by
  classical
  set ω : Cf eta → ℝ := fun t => Real.sqrt (1 + FSLattice.lsq (regSum A t)) with hω
  set x' : Cfg eta N → ℝ := fun b => ω (lab N j b) * x b with hx'
  have hω0 : ∀ t, 0 ≤ ω t := fun t => Real.sqrt_nonneg _
  have hωsq : ∀ t, ω t ^ 2 = 1 + FSLattice.lsq (regSum A t) := fun t =>
    Real.sq_sqrt (by have := FSLattice.lsq_nonneg (regSum A t); linarith)
  have hlab : ∀ b, regSum A (lab N j b) = regSum A (cidx N b) := fun b =>
    regSum_lineLab hAj (cidx N b)
  have h := sum_far_G_sq_le (sys := sys) hL hn j x' (fun b => mul_nonneg (hω0 _) (hx b))
    (fun b hb => hxC b (fun h0 => hb (by simp only [hx']; rw [h0, mul_zero])))
  have e1 : lineSq j (fun _ => 1) x' = lineSq j (fun s => 1 + FSLattice.lsq (regSum A s)) x := by
    rw [hx', lineSq_lab_mul]
    congr 1
    funext t
    rw [hωsq, one_mul]
  rw [e1] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun f _ => ?_) h
  by_cases hf : InQ (n : ℝ) (cidx N f)
  · rw [if_pos hf, if_pos hf]; ring
  · rw [if_neg hf, if_neg hf]
    have e2 : ∑ c, ‖wj sys L N j f c‖ * x' c = ω (lab N j f) * ∑ c, ‖wj sys L N j f c‖ * x c := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hfc : OnCh j (cidx N f) (cidx N c)
      · have hl : lab N j c = lab N j f := (lab_eq_iff.mpr hfc).symm
        simp only [hx']; rw [hl]; ring
      · rw [wj_eq_zero_of_not_onCh hfc, norm_zero, zero_mul, zero_mul, mul_zero]
    rw [e2, mul_pow, hωsq, hlab]

omit [Fintype ν] in
lemma sq_one_add_three_le (r : ℝ) (_hr : 0 ≤ r) : (1 + 3 * r) ^ 2 ≤ 18 * (1 + r ^ 2) := by
  nlinarith [sq_nonneg (3 * r - 1)]

/-- **The shared com word, word side**: for `t ∈ j₂` not moved by `j₁` and a coordinate `ζ = regSum A`
of `j₂` killed by `j₁`,
`Σ_f ω_F² (1+|ζ_f|²)⁻¹ (Σ_d |y₂| Σ_b W^L₁ x)² ≤ (32m/g²)² n⁻⁴ A₁ (36 c₂² H² L²_{j₁}(x; 1+|ξ_t|²)
  + 2 (c₂/2)² 32² H⁴ L²_{j₁}(x; 1+|ζ|²))`, `A₁ = (c₁/c_*²)² 277/n`. -/
theorem Phi_shared {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {j₁ j₂ : Ch eta} {t : Fin eta} (ht : t ∈ moved j₂)
    (ht1 : t ∉ moved j₁) {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j₂ A ε)
    (hA1 : ∀ σ, regSum A (tr j₁ σ) = 0) (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 / (1 + FSLattice.lsq (regSum A (cidx N f))) *
        (∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ^ 2 ≤
      (32 * mmax sys / gF L ^ 2) ^ 2 / (n : ℝ) ^ 4 *
        ((chC sys L j₁ * (1 / cst sys ^ 2)) ^ 2 * (277 / n)) *
        (36 * chC sys L j₂ ^ 2 * Hunit ^ 2 * lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum {t} s)) x +
          2 * (chC sys L j₂ / 2) ^ 2 * (32 ^ 2 * Hunit ^ 4) *
            lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum A s)) x) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hc₂ := chC_nonneg sys hL j₂
  have hc₁ := chC_nonneg sys hL j₁
  set c₂ := chC sys L j₂ with hc₂d
  set v : Cfg eta N → ℝ := fun d => ∑ b, WL sys L N n j₁ d b * x b with hv
  have hv0 : ∀ d, 0 ≤ v d := fun d => Finset.sum_nonneg fun b _ =>
    mul_nonneg (WL_nonneg hL j₁ d b) (hx b)
  set v' : Cfg eta N → ℝ := fun d => c₂ * ((1 + 3 * FSChannel.rho (cidx N d t)) * v d) with hv'
  set v2 : Cfg eta N → ℝ := fun d => c₂ / 2 * v d with hv2
  have hv20 : ∀ d, 0 ≤ v2 d := fun d => mul_nonneg (by positivity) (hv0 d)
  set P : Cfg eta N → ℝ := fun f => ∑ d, if OnCh j₂ (cidx N f) (cidx N d) then
    v' d / FSLattice.lsq (chT N j₂ f d) else 0 with hP
  set Q : Cfg eta N → ℝ := fun f => ∑ d, if OnCh j₂ (cidx N f) (cidx N d) then
    v2 d / FSChannel.rho (chT N j₂ f d) else 0 with hQ
  set ζ : Cfg eta N → ℝ := fun f => 1 + FSLattice.lsq (regSum A (cidx N f)) with hζ
  have hζ0 : ∀ f, 0 < ζ f := fun f => by
    simp only [hζ]; have := FSLattice.lsq_nonneg (regSum A (cidx N f)); linarith
  -- the alignment, pointwise
  have hS : ∀ f, ∑ d, ‖yj sys L p₀ N j₂ f d‖ * v d ≤ P f + Q f := by
    intro f
    simp only [hP, hQ]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun d _ => ?_
    by_cases hfd : OnCh j₂ (cidx N f) (cidx N d)
    · rw [if_pos hfd, if_pos hfd]
      have hy := norm_yj_align_le (sys := sys) (L := L) (p₀ := p₀) hL ht f d
      calc ‖yj sys L p₀ N j₂ f d‖ * v d ≤
          (c₂ * (1 + 3 * FSChannel.rho (cidx N d t)) / FSLattice.lsq (chT N j₂ f d) +
            c₂ / 2 / FSChannel.rho (chT N j₂ f d)) * v d := mul_le_mul_of_nonneg_right hy (hv0 d)
        _ = v' d / FSLattice.lsq (chT N j₂ f d) + v2 d / FSChannel.rho (chT N j₂ f d) := by
            simp only [hv', hv2]; ring
    · rw [if_neg hfd, if_neg hfd]
      have : yj sys L p₀ N j₂ f d = 0 := by unfold yj ycKc; rw [if_neg hfd]
      rw [this, norm_zero, zero_mul, add_zero]
  have hS0 : ∀ f, 0 ≤ ∑ d, ‖yj sys L p₀ N j₂ f d‖ * v d := fun f =>
    Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _) (hv0 d)
  -- the far weight
  have hfar : ∀ f, farW sys L N n f ^ 2 ≤ (32 * mmax sys / gF L ^ 2) ^ 2 / (n : ℝ) ^ 4 := by
    intro f
    have h1 := farW_le_max (sys := sys) hL hn hA.card f
    have h0 := farW_nonneg (sys := sys) (L := L) (n := n) f
    have h2 : farW sys L N n f ≤ 32 * mmax sys / gF L ^ 2 / (n : ℝ) ^ 2 :=
      h1.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) (le_max_left _ _))
    calc farW sys L N n f ^ 2 ≤ (32 * mmax sys / gF L ^ 2 / (n : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ h0 h2 2
      _ = (32 * mmax sys / gF L ^ 2) ^ 2 / (n : ℝ) ^ 4 := by ring
  set CF := (32 * mmax sys / gF L ^ 2) ^ 2 / (n : ℝ) ^ 4 with hCF
  have hCF0 : 0 ≤ CF := by positivity
  have hP0 : ∀ f, 0 ≤ P f := fun f => Finset.sum_nonneg fun d _ => by
    split_ifs
    · exact div_nonneg (mul_nonneg hc₂ (mul_nonneg (by have := FSChannel.rho_nonneg (cidx N d t); linarith)
        (hv0 d))) (FSLattice.lsq_nonneg _)
    · exact le_rfl
  have hQ0 : ∀ f, 0 ≤ Q f := fun f => Finset.sum_nonneg fun d _ => by
    split_ifs
    · exact div_nonneg (hv20 d) (FSChannel.rho_nonneg _)
    · exact le_rfl
  have hstep1 : ∑ f, farW sys L N n f ^ 2 / ζ f * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * v d) ^ 2 ≤
      CF * (2 * ∑ f, P f ^ 2 / ζ f + 2 * ∑ f, Q f ^ 2 / ζ f) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    have h1 : (∑ d, ‖yj sys L p₀ N j₂ f d‖ * v d) ^ 2 ≤ 2 * P f ^ 2 + 2 * Q f ^ 2 := by
      have := pow_le_pow_left₀ (hS0 f) (hS f) 2
      nlinarith [sq_nonneg (P f - Q f)]
    have hζf := hζ0 f
    calc farW sys L N n f ^ 2 / ζ f * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * v d) ^ 2 ≤
        CF / ζ f * (2 * P f ^ 2 + 2 * Q f ^ 2) := by
          apply mul_le_mul (div_le_div_of_nonneg_right (hfar f) hζf.le) h1 (sq_nonneg _)
            (div_nonneg hCF0 hζf.le)
      _ = CF * (2 * (P f ^ 2 / ζ f) + 2 * (Q f ^ 2 / ζ f)) := by ring
  -- the A-part: dual Hardy on the `j₂`-lines
  have hPd := line_hardy_dual (N := N) hH hA (fun _ => 1) (fun _ => zero_le_one) v'
  simp only [one_mul] at hPd
  -- the I-part: Hardy twice
  have hQd := line_hardy_twice (N := N) hH hA v2 hv20
  -- the long first hop
  have hll : ∀ (y : Cfg eta N → ℝ), (∀ b, 0 ≤ y b) →
      ∑ d, (∑ b, WL sys L N n j₁ d b * y b) ^ 2 ≤
        (chC sys L j₁ * (1 / cst sys ^ 2)) ^ 2 * (277 / n) * lineSq j₁ (fun _ => 1) y := by
    intro y hy
    exact long_line_le j₁ y hy (WL sys L N n j₁) (WL_nonneg hL j₁) (kappaL sys L N n {lead j₁} j₁)
      (WL_le_kappa hL hn (coord_lead j₁)) (sum_kappaL_sq_le hn (coord_lead j₁))
  set A₁ := (chC sys L j₁ * (1 / cst sys ^ 2)) ^ 2 * (277 / n) with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  -- the registers of `j₂` on the `j₁`-lines
  have htk : ∀ σ, regSum {t} (tr j₁ σ) = 0 := fun σ => by
    simp only [regSum, Finset.sum_singleton]; exact tr_apply_not_moved j₁ σ ht1
  have hWLd : ∀ d b, WL sys L N n j₁ d b ≠ 0 → OnCh j₁ (cidx N d) (cidx N b) := by
    intro d b h
    by_contra hj; apply h; unfold WL; rw [if_neg (fun h' => hj h'.1)]
  have hPv' : ∑ d, v' d ^ 2 ≤ c₂ ^ 2 * (A₁ * (18 * lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum {t} s)) x)) := by
    set φ : Cf eta → ℝ := fun s => 1 + 3 * FSChannel.rho (regSum {t} s) with hφ
    have hφlab : ∀ b, φ (lab N j₁ b) = 1 + 3 * FSChannel.rho (cidx N b t) := by
      intro b
      simp only [hφ]
      rw [regSum_lineLab htk (cidx N b)]
      simp [regSum]
    have e : ∀ d, v' d = c₂ * ∑ b, WL sys L N n j₁ d b * (φ (lab N j₁ b) * x b) := by
      intro d
      simp only [hv', hv]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases h0 : WL sys L N n j₁ d b = 0
      · rw [h0]; ring
      · have hj := hWLd d b h0
        have hdt : cidx N d t = cidx N b t := by
          rw [hj, Pi.add_apply, tr_apply_not_moved j₁ _ ht1, add_zero]
        rw [hφlab, hdt]; ring
    have hy0 : ∀ b, 0 ≤ φ (lab N j₁ b) * x b := fun b => by
      rw [hφlab]; exact mul_nonneg (by have := FSChannel.rho_nonneg (cidx N b t); linarith) (hx b)
    have h1 := hll _ hy0
    have h2 : lineSq j₁ (fun _ => 1) (fun b => φ (lab N j₁ b) * x b) ≤
        18 * lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum {t} s)) x := by
      rw [lineSq_lab_mul]
      have := lineSq_mono_weight (N := N) j₁ (Ω := fun s => 1 * φ s ^ 2)
        (Ω' := fun s => 18 * (1 + FSLattice.lsq (regSum {t} s))) (fun s => by
          simp only [hφ, one_mul]
          have hr := FSChannel.rho_nonneg (regSum {t} s)
          rw [lsq_eq_rho_sq]
          exact sq_one_add_three_le _ hr) x
      refine this.trans (le_of_eq ?_)
      unfold lineSq
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    calc ∑ d, v' d ^ 2 = c₂ ^ 2 * ∑ d, (∑ b, WL sys L N n j₁ d b * (φ (lab N j₁ b) * x b)) ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [e d]; ring
      _ ≤ c₂ ^ 2 * (A₁ * (18 * lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum {t} s)) x)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact h1.trans (mul_le_mul_of_nonneg_left h2 hA₁0)
  have hQv : ∑ d, (1 + FSLattice.lsq (regSum A (cidx N d))) * v2 d ^ 2 ≤
      (c₂ / 2) ^ 2 * (A₁ * lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum A s)) x) := by
    set ω : Cf eta → ℝ := fun s => Real.sqrt (1 + FSLattice.lsq (regSum A s)) with hω
    have hωsq : ∀ s, ω s ^ 2 = 1 + FSLattice.lsq (regSum A s) := fun s =>
      Real.sq_sqrt (by have := FSLattice.lsq_nonneg (regSum A s); linarith)
    have hωlab : ∀ b, regSum A (lab N j₁ b) = regSum A (cidx N b) := fun b =>
      regSum_lineLab hA1 (cidx N b)
    have e : ∀ d, (1 + FSLattice.lsq (regSum A (cidx N d))) * v2 d ^ 2 =
        (c₂ / 2) ^ 2 * (∑ b, WL sys L N n j₁ d b * (ω (lab N j₁ b) * x b)) ^ 2 := by
      intro d
      have e1 : ∑ b, WL sys L N n j₁ d b * (ω (lab N j₁ b) * x b) = ω (lab N j₁ d) * v d := by
        simp only [hv]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases h0 : WL sys L N n j₁ d b = 0
        · rw [h0]; ring
        · have hl : lab N j₁ b = lab N j₁ d := (lab_eq_iff.mpr (hWLd d b h0)).symm
          rw [hl]; ring
      rw [e1, show (ω (lab N j₁ d) * v d) ^ 2 = ω (lab N j₁ d) ^ 2 * v d ^ 2 by ring, hωsq, hωlab]
      simp only [hv2]; ring
    have hy0 : ∀ b, 0 ≤ ω (lab N j₁ b) * x b := fun b => mul_nonneg (Real.sqrt_nonneg _) (hx b)
    have h1 := hll _ hy0
    have h2 : lineSq j₁ (fun _ => 1) (fun b => ω (lab N j₁ b) * x b) =
        lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum A s)) x := by
      rw [lineSq_lab_mul]
      congr 1; funext s; rw [hωsq, one_mul]
    rw [h2] at h1
    rw [Finset.sum_congr rfl fun d _ => e d, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- assemble
  have hPsum : ∑ f, P f ^ 2 / ζ f ≤ Hunit ^ 2 * ∑ d, v' d ^ 2 := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun f _ => ?_) hPd
    simp only [hP, hζ]
  have hQsum : ∑ f, Q f ^ 2 / ζ f ≤
      32 ^ 2 * Hunit ^ 4 * ∑ d, (1 + FSLattice.lsq (regSum A (cidx N d))) * v2 d ^ 2 := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun f _ => ?_) hQd
    simp only [hQ, hζ]
  have hH2 := sq_nonneg Hunit
  have hH4 : 0 ≤ Hunit ^ 4 := by positivity
  calc ∑ f, farW sys L N n f ^ 2 / (1 + FSLattice.lsq (regSum A (cidx N f))) *
        (∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ^ 2 =
      ∑ f, farW sys L N n f ^ 2 / ζ f * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * v d) ^ 2 := rfl
    _ ≤ CF * (2 * ∑ f, P f ^ 2 / ζ f + 2 * ∑ f, Q f ^ 2 / ζ f) := hstep1
    _ ≤ CF * (2 * (Hunit ^ 2 * (c₂ ^ 2 * (A₁ * (18 * lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum {t} s)) x)))) +
          2 * (32 ^ 2 * Hunit ^ 4 * ((c₂ / 2) ^ 2 * (A₁ * lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum A s)) x)))) := by
        apply mul_le_mul_of_nonneg_left _ hCF0
        have := mul_le_mul_of_nonneg_left hPv' hH2
        have := mul_le_mul_of_nonneg_left hQv (by positivity : (0 : ℝ) ≤ 32 ^ 2 * Hunit ^ 4)
        linarith
    _ = _ := by rw [hCF, hA₁]; ring

omit [Fintype ν] in
/-- `T² ≤ a b` gives `T ≤ (m a + m⁵ b)/(2 m³)`. -/
lemma le_of_sq_le_mul {T a b : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : T ^ 2 ≤ a * b)
    {m : ℝ} (hm : 0 < m) : T ≤ (m * a + m ^ 5 * b) / (2 * m ^ 3) := by
  rw [le_div_iff₀ (by positivity)]
  have hm6 : 0 < m ^ 6 := by positivity
  have h1 : (T * (2 * m ^ 3)) ^ 2 ≤ (m * a + m ^ 5 * b) ^ 2 := by
    have e1 : (T * (2 * m ^ 3)) ^ 2 = 4 * m ^ 6 * T ^ 2 := by ring
    have e2 : (m * a + m ^ 5 * b) ^ 2 = 4 * m ^ 6 * (a * b) + (m * a - m ^ 5 * b) ^ 2 := by ring
    rw [e1, e2]
    nlinarith [sq_nonneg (m * a - m ^ 5 * b), mul_le_mul_of_nonneg_left h hm6.le]
  have hX : 0 ≤ T * (2 * m ^ 3) := by positivity
  have hY : 0 ≤ m * a + m ^ 5 * b := by positivity
  exact (pow_le_pow_iff_left₀ hX hY two_ne_zero).mp h1

open Classical in
/-- **The shared com word against the outer channel `j₃`** (common coordinate `ζ`):
`Σ_f G₃ ω_F (Σ_d |y₂| Σ_b W^L₁ x) ≤ (n Γ + n⁵ Φ)/(2 n³)` with `Γ` the weighted outer bound and `Φ` the
bound of `Phi_shared`. -/
theorem tri_shared_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {j₁ j₂ j₃ : Ch eta} {t : Fin eta} (ht : t ∈ moved j₂)
    (ht1 : t ∉ moved j₁) {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j₂ A ε)
    (hA1 : ∀ σ, regSum A (tr j₁ σ) = 0) (hA3 : ∀ σ, regSum A (tr j₃ σ) = 0)
    (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b)
    (hxC : ∀ b, x b ≠ 0 → InC (n : ℝ) (cst sys) (cidx N b)) :
    ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else ∑ c, ‖wj sys L N j₃ f c‖ * x c) *
        farW sys L N n f * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ≤
      ((n : ℝ) * ((64 * chC sys L j₃) ^ 2 * (277 / n) *
          lineSq j₃ (fun s => 1 + FSLattice.lsq (regSum A s)) x) +
        (n : ℝ) ^ 5 * ((32 * mmax sys / gF L ^ 2) ^ 2 / (n : ℝ) ^ 4 *
          ((chC sys L j₁ * (1 / cst sys ^ 2)) ^ 2 * (277 / n)) *
          (36 * chC sys L j₂ ^ 2 * Hunit ^ 2 * lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum {t} s)) x +
            2 * (chC sys L j₂ / 2) ^ 2 * (32 ^ 2 * Hunit ^ 4) *
              lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum A s)) x))) / (2 * (n : ℝ) ^ 3) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set G : Cfg eta N → ℝ := fun f =>
    if InQ (n : ℝ) (cidx N f) then 0 else ∑ c, ‖wj sys L N j₃ f c‖ * x c with hG
  set S : Cfg eta N → ℝ := fun f => ∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b
    with hS
  set ζ : Cfg eta N → ℝ := fun f => 1 + FSLattice.lsq (regSum A (cidx N f)) with hζ
  have hζ0 : ∀ f, 0 < ζ f := fun f => by
    simp only [hζ]; have := FSLattice.lsq_nonneg (regSum A (cidx N f)); linarith
  have hG0 : ∀ f, 0 ≤ G f := fun f => by
    simp only [hG]; split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg fun c _ => mul_nonneg (norm_nonneg _) (hx c)
  have hS0 : ∀ f, 0 ≤ S f := fun f => Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun b _ => mul_nonneg (WL_nonneg hL j₁ d b) (hx b))
  have hW0 : ∀ f, 0 ≤ farW sys L N n f := fun f => farW_nonneg f
  set a := ∑ f, ζ f * G f ^ 2 with ha
  set b := ∑ f, farW sys L N n f ^ 2 / ζ f * S f ^ 2 with hb
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun f _ => mul_nonneg (hζ0 f).le (sq_nonneg _)
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun f _ =>
    mul_nonneg (div_nonneg (sq_nonneg _) (hζ0 f).le) (sq_nonneg _)
  set T := ∑ f, G f * farW sys L N n f * S f with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun f _ => mul_nonneg (mul_nonneg (hG0 f) (hW0 f)) (hS0 f)
  have hCS : T ^ 2 ≤ a * b := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun f => Real.sqrt (ζ f) * G f)
      (fun f => farW sys L N n f * S f / Real.sqrt (ζ f))
    have e1 : ∀ f, Real.sqrt (ζ f) * G f * (farW sys L N n f * S f / Real.sqrt (ζ f)) =
        G f * farW sys L N n f * S f := by
      intro f
      have : Real.sqrt (ζ f) ≠ 0 := (Real.sqrt_pos.mpr (hζ0 f)).ne'
      field_simp
    have e2 : ∀ f, (Real.sqrt (ζ f) * G f) ^ 2 = ζ f * G f ^ 2 := by
      intro f; rw [mul_pow, Real.sq_sqrt (hζ0 f).le]
    have e3 : ∀ f, (farW sys L N n f * S f / Real.sqrt (ζ f)) ^ 2 =
        farW sys L N n f ^ 2 / ζ f * S f ^ 2 := by
      intro f; rw [div_pow, mul_pow, Real.sq_sqrt (hζ0 f).le]; ring
    simp only [e1, e2, e3] at h
    exact h
  have hT' := le_of_sq_le_mul hT0 ha0 hb0 hCS hn0
  have haB := sum_far_G_sq_weight_le (sys := sys) hL hn j₃ hA3 x hx hxC
  have hbB := Phi_shared (sys := sys) (p₀ := p₀) hH hL hn ht ht1 hA hA1 x hx
  refine hT'.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left haB hn0.le
  · exact mul_le_mul_of_nonneg_left hbB (by positivity)

end SharedW

end FSFlux
