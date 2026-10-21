import PlaneWave.FluxBox.FirstHops

/-!
# Flux route, stage 3, part 29: the far–cold words against cold inputs

For `x ≥ 0` supported on the cold ball, the far-weighted square sums
`Φ(a; x) = Σ_f ω_F(f)² (Σ_b a(f,b) x_b)²` of the five chains of `b^{FC}` are all
`≤ K n⁻³ (L²_{j₁}(x) + L²_{j₂}(x))` (`P2_ch1` … `P2_ch2com`):

* chain majorants (`chain_sum_le`, `chain'_sum_le`): the two hops by real kernels;
* the first hop from cold is split at `c_* n` (`norm_wj_le_split`); a hop from cold off the cube
  is long (`norm_wj_notP_le`), and so is the well-gapped `Y`-hop (`yj_cold_notP_le_kap`);
* the long parts go through the shapes L1-W / L1-Y, the short parts through L2 with the
  ball majorants `farW_wj_ball_le` (flat) and `farW_yj_ball_le'` (com);
* the short first hop in line squares (`lineSq_WS_le`): `(26 c_* n c₁)²` on its own lines, transverse
  Hardy across, with the cold weight `1 + |ξ|² ≤ 2n²` (`lineSq_cold_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Majorants of the chains -/

section ChainMaj

variable {X : Type*} [Fintype X]

omit [Fintype ν] in
/-- **Chain majorant**: two hops dominated by real kernels (`K₁` only needed on the support of `x`). -/
lemma chain_sum_le (S₁ S₂ S₃ : X → Prop) (κ₂ κ₁ : X → X → ℂ) (x : X → ℝ) (hx : ∀ b, 0 ≤ x b)
    (K₂ K₁ : X → X → ℝ) (hK₂0 : ∀ f d, 0 ≤ K₂ f d) (hK₁0 : ∀ d b, 0 ≤ K₁ d b)
    (h₂ : ∀ f d, S₁ f → S₂ d → ‖κ₂ f d‖ ≤ K₂ f d)
    (h₁ : ∀ d b, S₂ d → S₃ b → x b ≠ 0 → ‖κ₁ d b‖ ≤ K₁ d b) (f : X) :
    ∑ b, ‖chainK S₁ S₂ S₃ κ₂ κ₁ f b‖ * x b ≤ ∑ d, K₂ f d * ∑ b, K₁ d b * x b := by
  classical
  have hR : ∑ d, K₂ f d * ∑ b, K₁ d b * x b = ∑ b, ∑ d, K₂ f d * (K₁ d b * x b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
  rw [hR]
  refine Finset.sum_le_sum fun b _ => ?_
  have hnn : 0 ≤ ∑ d, K₂ f d * (K₁ d b * x b) :=
    Finset.sum_nonneg fun d _ => mul_nonneg (hK₂0 f d) (mul_nonneg (hK₁0 d b) (hx b))
  unfold chainK
  by_cases h : S₁ f ∧ S₃ b
  · rw [if_pos h]
    refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (hx b)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun d _ => ?_
    rw [norm_mul]
    by_cases hd : S₂ d
    · rw [if_pos hd]
      by_cases hxb : x b = 0
      · rw [hxb, mul_zero, mul_zero, mul_zero]
      · have e1 := h₂ f d h.1 hd
        have e2 := h₁ d b hd h.2 hxb
        calc ‖κ₂ f d‖ * ‖κ₁ d b‖ * x b ≤ K₂ f d * K₁ d b * x b :=
              mul_le_mul_of_nonneg_right (mul_le_mul e1 e2 (norm_nonneg _) (hK₂0 f d)) (hx b)
          _ = K₂ f d * (K₁ d b * x b) := by ring
    · rw [if_neg hd, norm_zero, mul_zero, zero_mul]
      exact mul_nonneg (hK₂0 f d) (mul_nonneg (hK₁0 d b) (hx b))
  · rw [if_neg h, norm_zero, zero_mul]
    exact hnn

omit [Fintype ν] in
/-- **Chain majorant** for `Π_{S₁} κ₂ κ₁ Π_{S₃}`. -/
lemma chain'_sum_le (S₁ S₃ : X → Prop) (κ₂ κ₁ : X → X → ℂ) (x : X → ℝ) (hx : ∀ b, 0 ≤ x b)
    (K₂ K₁ : X → X → ℝ) (hK₂0 : ∀ f d, 0 ≤ K₂ f d) (hK₁0 : ∀ d b, 0 ≤ K₁ d b)
    (h₂ : ∀ f d, S₁ f → ‖κ₂ f d‖ ≤ K₂ f d)
    (h₁ : ∀ d b, S₃ b → x b ≠ 0 → ‖κ₁ d b‖ ≤ K₁ d b) (f : X) :
    ∑ b, ‖chainK' S₁ S₃ κ₂ κ₁ f b‖ * x b ≤ ∑ d, K₂ f d * ∑ b, K₁ d b * x b := by
  classical
  have hR : ∑ d, K₂ f d * ∑ b, K₁ d b * x b = ∑ b, ∑ d, K₂ f d * (K₁ d b * x b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
  rw [hR]
  refine Finset.sum_le_sum fun b _ => ?_
  have hnn : 0 ≤ ∑ d, K₂ f d * (K₁ d b * x b) :=
    Finset.sum_nonneg fun d _ => mul_nonneg (hK₂0 f d) (mul_nonneg (hK₁0 d b) (hx b))
  unfold chainK'
  by_cases h : S₁ f ∧ S₃ b
  · rw [if_pos h]
    refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (hx b)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun d _ => ?_
    rw [norm_mul]
    by_cases hxb : x b = 0
    · rw [hxb, mul_zero, mul_zero, mul_zero]
    · have e1 := h₂ f d h.1
      have e2 := h₁ d b h.2 hxb
      calc ‖κ₂ f d‖ * ‖κ₁ d b‖ * x b ≤ K₂ f d * K₁ d b * x b :=
            mul_le_mul_of_nonneg_right (mul_le_mul e1 e2 (norm_nonneg _) (hK₂0 f d)) (hx b)
        _ = K₂ f d * (K₁ d b * x b) := by ring
  · rw [if_neg h, norm_zero, zero_mul]
    exact hnn

end ChainMaj

/-! ## Square sums -/

section SqSums

omit [Fintype ν] in
lemma sum_sq_le_of_le {ι : Type*} (s : Finset ι) (w a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (h : ∀ i, a i ≤ b i) : ∑ i ∈ s, w i ^ 2 * a i ^ 2 ≤ ∑ i ∈ s, w i ^ 2 * b i ^ 2 :=
  Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ha i) (h i) 2) (sq_nonneg _)

omit [Fintype ν] in
lemma sum_sq_le_add {ι : Type*} (s : Finset ι) (w a b c : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (h : ∀ i, a i ≤ b i + c i) :
    ∑ i ∈ s, w i ^ 2 * a i ^ 2 ≤ 2 * ∑ i ∈ s, w i ^ 2 * b i ^ 2 + 2 * ∑ i ∈ s, w i ^ 2 * c i ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : a i ^ 2 ≤ (b i + c i) ^ 2 := pow_le_pow_left₀ (ha i) (h i) 2
  have h2 : (b i + c i) ^ 2 ≤ 2 * b i ^ 2 + 2 * c i ^ 2 := by nlinarith [sq_nonneg (b i - c i)]
  have hw := sq_nonneg (w i)
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hw
  have e : w i ^ 2 * (2 * b i ^ 2 + 2 * c i ^ 2) = 2 * (w i ^ 2 * b i ^ 2) + 2 * (w i ^ 2 * c i ^ 2) := by
    ring
  linarith

omit [Fintype ν] in
lemma comb_two {a b L₁ L₂ D X Y : ℝ} (ha : 0 ≤ a) (h2 : 0 ≤ L₂) (hD : 0 < D)
    (hX : X ≤ a / D * L₁) (hY : Y ≤ b / D * (L₁ + L₂)) :
    2 * X + 2 * Y ≤ (2 * a + 2 * b) / D * (L₁ + L₂) := by
  have h3 : a / D * L₁ ≤ a / D * (L₁ + L₂) :=
    mul_le_mul_of_nonneg_left (by linarith) (div_nonneg ha hD.le)
  have e : (2 * a + 2 * b) / D * (L₁ + L₂) = 2 * (a / D * (L₁ + L₂)) + 2 * (b / D * (L₁ + L₂)) := by
    ring
  linarith

omit [Fintype ν] in
lemma weaken_one {a L₁ L₂ D X : ℝ} (ha : 0 ≤ a) (h2 : 0 ≤ L₂) (hD : 0 < D) (hX : X ≤ a / D * L₁) :
    X ≤ a / D * (L₁ + L₂) :=
  hX.trans (mul_le_mul_of_nonneg_left (by linarith) (div_nonneg ha hD.le))

end SqSums

/-! ## Line squares with a weight bounded on the support -/

section SuppWeight

variable {N : ℕ}

omit [Fintype ν] in
lemma lineSq_weight_supp (j : Ch eta) {Ω : Cf eta → ℝ} {x : Cfg eta N → ℝ} {B : ℝ}
    (hB : ∀ p, x p ≠ 0 → Ω (lab N j p) ≤ B) :
    lineSq j Ω x ≤ B * lineSq j (fun _ => 1) x := by
  classical
  unfold lineSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  by_cases h0 : lineSum j x t = 0
  · rw [h0]; simp
  · unfold lineSum at h0
    obtain ⟨p, hp, hxp⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    have hlab : lab N j p = t := (Finset.mem_filter.mp hp).2
    have h1 := hB p hxp
    rw [hlab] at h1
    rw [one_mul]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)

variable {sys : CoulombSystem eta ν} {n : ℕ}

omit [Fintype ν] in
/-- **The cold weight**: `L²_j(x; 1 + |ξ|²) ≤ (1 + (2 c_* n)²) L²_j(x)` for `x` on the cold ball and
`ξ` constant on the `j`-lines. -/
lemma lineSq_cold_le {j : Ch eta} {A : Finset (Fin eta)} (hAc : A.card ≤ 2)
    (hAj : ∀ σ, regSum A (tr j σ) = 0) {x : Cfg eta N → ℝ}
    (hxC : ∀ p, x p ≠ 0 → InC (n : ℝ) (cst sys) (cidx N p)) :
    lineSq j (fun s => 1 + FSLattice.lsq (regSum A s)) x ≤
      (1 + (2 * (cst sys * n)) ^ 2) * lineSq j (fun _ => 1) x := by
  apply lineSq_weight_supp j
  intro p hp
  show 1 + FSLattice.lsq (regSum A (lineLab j (cidx N p))) ≤ 1 + (2 * (cst sys * n)) ^ 2
  rw [regSum_lineLab hAj]
  have h1 := rho_coord_cold hAc (hxC p hp)
  have h2 := FSChannel.rho_sq (regSum A (cidx N p))
  have h3 := FSChannel.rho_nonneg (regSum A (cidx N p))
  have h4 : FSChannel.rho (regSum A (cidx N p)) ^ 2 ≤ (2 * (cst sys * n)) ^ 2 :=
    pow_le_pow_left₀ h3 h1 2
  have h5 : FSLattice.lsq (regSum A (cidx N p)) = FSChannel.rho (regSum A (cidx N p)) ^ 2 := by
    rw [h2]
  linarith

end SuppWeight

/-! ## The short first hop in line squares -/

section ShortFirst

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

/-- **The short first hop in the line squares of the second channel**:
`L²_{j₂}(W^S_{j₁} x) ≤ n² ((26 c_* c₁)² + 2 c₁² H²) (L²_{j₁}(x) + L²_{j₂}(x))` for cold `x`. -/
theorem lineSq_WS_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) (j₁ j₂ : Ch eta) (x : Cfg eta N → ℝ) (hx : ∀ p, 0 ≤ x p)
    (hxC : ∀ p, x p ≠ 0 → InC (n : ℝ) (cst sys) (cidx N p)) :
    lineSq j₂ (fun _ => 1) (fun d => ∑ b, WS sys L N n j₁ d b * x b) ≤
      (n : ℝ) ^ 2 * ((26 * cst sys * chC sys L j₁) ^ 2 + 2 * chC sys L j₁ ^ 2 * Hunit ^ 2) *
        (lineSq j₁ (fun _ => 1) x + lineSq j₂ (fun _ => 1) x) := by
  have hc := chC_nonneg sys hL j₁
  have h1 := lineSq_nonneg j₁ (fun _ => zero_le_one) x
  have h2 := lineSq_nonneg j₂ (fun _ => zero_le_one) x
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcs := cst_le32 sys
  have hc0 := cst_pos sys
  have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hb : 0 ≤ 2 * chC sys L j₁ ^ 2 * Hunit ^ 2 := by positivity
  have ha : 0 ≤ (26 * cst sys * chC sys L j₁) ^ 2 := sq_nonneg _
  by_cases hj : j₁ = j₂
  · subst hj
    have h3 := lineSq_WS_same_le (sys := sys) (n := n) hL j₁ (fun _ => zero_le_one) x hx
    calc lineSq j₁ (fun _ => 1) (fun d => ∑ b, WS sys L N n j₁ d b * x b) ≤
        (26 * (cst sys * n) * chC sys L j₁) ^ 2 * lineSq j₁ (fun _ => 1) x := h3
      _ = (n : ℝ) ^ 2 * (26 * cst sys * chC sys L j₁) ^ 2 * lineSq j₁ (fun _ => 1) x := by ring
      _ ≤ _ := by
        apply mul_le_mul _ (by linarith) h1 (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) hn2
  · obtain ⟨A, ε, hA, hAj⟩ := exists_coord_ne hj
    have h3 := lineSq_WS_cross_le (sys := sys) (n := n) hH hL hA hAj x hx
    have h4 := lineSq_cold_le (sys := sys) (n := n) hA.card hAj hxC
    have e1 : 2 * (cst sys * n) ≤ n := by nlinarith
    have e2 : 0 ≤ 2 * (cst sys * n) := by positivity
    have e3 : (2 * (cst sys * n)) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ e2 e1 2
    have e4 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h5 : 1 + (2 * (cst sys * n)) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by linarith
    have hH2 := sq_nonneg Hunit
    calc lineSq j₂ (fun _ => 1) (fun d => ∑ b, WS sys L N n j₁ d b * x b) ≤
        chC sys L j₁ ^ 2 * (Hunit ^ 2 * lineSq j₂ (fun s => 1 + FSLattice.lsq (regSum A s)) x) := h3
      _ ≤ chC sys L j₁ ^ 2 * (Hunit ^ 2 * ((2 * (n : ℝ) ^ 2) * lineSq j₂ (fun _ => 1) x)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          apply mul_le_mul_of_nonneg_left _ hH2
          exact h4.trans (mul_le_mul_of_nonneg_right h5 h2)
      _ = (n : ℝ) ^ 2 * (2 * chC sys L j₁ ^ 2 * Hunit ^ 2) * lineSq j₂ (fun _ => 1) x := by ring
      _ ≤ _ := by
        apply mul_le_mul _ (by linarith) h2 (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith) hn2

end ShortFirst

/-! ## Line majorants -/

section Kap

variable {N : ℕ}

variable (n) in
/-- `κ(d) = c/max(n², |ζ(d)|²)`. -/
noncomputable def kapM (c : ℝ) (A : Finset (Fin eta)) (d : Cfg eta N) : ℝ :=
  c / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d)))

variable (n) in
/-- `κ(f) = c/max(n², |ζ(f)|²)²`. -/
noncomputable def kapM2 (c : ℝ) (A : Finset (Fin eta)) (d : Cfg eta N) : ℝ :=
  c / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d))) ^ 2

variable {n : ℕ}

omit [Fintype ν] in
lemma max_pos_n (hn : 1 ≤ n) (l : ℝ) : 0 < max ((n : ℝ) ^ 2) l := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact lt_of_lt_of_le (by positivity) (le_max_left _ _)

omit [Fintype ν] in
lemma kapM_nonneg (hn : 1 ≤ n) {c : ℝ} (hc : 0 ≤ c) (A : Finset (Fin eta)) (d : Cfg eta N) :
    0 ≤ kapM n c A d :=
  div_nonneg hc (max_pos_n hn _).le

omit [Fintype ν] in
lemma kapM2_nonneg (hn : 1 ≤ n) {c : ℝ} (hc : 0 ≤ c) (A : Finset (Fin eta)) (d : Cfg eta N) :
    0 ≤ kapM2 n c A d :=
  div_nonneg hc (pow_nonneg (max_pos_n hn _).le 2)

omit [Fintype ν] in
open Classical in
lemma sum_kapM_sq_le (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    (c : ℝ) (q : Cfg eta N) :
    ∑ d ∈ Finset.univ.filter (fun d => lab N j d = lab N j q), kapM n c A d ^ 2 ≤ c ^ 2 * (277 / n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := lineSum_inv_max_sq_le hA q hn1 0
  simp only [sub_zero] at h
  unfold kapM
  have e : ∀ d ∈ Finset.univ.filter (fun d => lab N j d = lab N j q),
      (c / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d)))) ^ 2 =
      c ^ 2 * (1 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d))) ^ 2) := by
    intro d _; ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

omit [Fintype ν] in
open Classical in
lemma sum_kapM2_sq_le (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    (c : ℝ) (q : Cfg eta N) :
    ∑ d ∈ Finset.univ.filter (fun d => lab N j d = lab N j q), kapM2 n c A d ^ 2 ≤
      c ^ 2 * (277 / (n : ℝ) ^ 5) := by
  have h := lineSum_inv_max_four_le hn hA q
  unfold kapM2
  have e : ∀ d ∈ Finset.univ.filter (fun d => lab N j d = lab N j q),
      (c / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d))) ^ 2) ^ 2 =
      c ^ 2 * (1 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d))) ^ 4) := by
    intro d _; ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

end Kap

/-! ## The hops: long, well-gapped and ball majorants -/

section Hops

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

/-- **A Coulomb hop from cold off the cube is long**: `|w_j(d,b)| ≤ W^L_j(d,b)`. -/
lemma norm_wj_notP_le (hL : 0 < L) (j : Ch eta) {d b : Cfg eta N}
    (hb : InC (n : ℝ) (cst sys) (cidx N b)) (hd : ¬ InP (n : ℝ) (cidx N d)) :
    ‖wj sys L N j d b‖ ≤ WL sys L N n j d b := by
  have h := norm_wj_le (sys := sys) hL j d b
  unfold WL
  by_cases hj : OnCh j (cidx N d) (cidx N b)
  · rw [if_pos hj] at h
    have hl := long_of_cold_notP hb hd hj
    have hcs := cst_le32 sys
    have hc := cst_pos sys
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2 : (cst sys * n) ^ 2 ≤ FSLattice.lsq (chT N j d b) := by
      have e1 : cst sys * n ≤ (n : ℝ) / 2 := by nlinarith
      have e2 : 0 ≤ cst sys * n := by positivity
      exact (pow_le_pow_left₀ e2 e1 2).trans hl
    rw [if_pos ⟨hj, hb, h2⟩]
    exact h
  · rw [if_neg hj] at h
    rw [if_neg (fun h' => hj h'.1)]
    exact h

variable (sys L) in
/-- The constant of the well-gapped `Y`-hop: `64 m c_j/(M̄_j c_*)`. -/
noncomputable def cY3 (j : Ch eta) : ℝ := 64 * mmax sys * chC sys L j / Mtot sys j / cst sys

lemma cY3_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ cY3 sys L j := by
  unfold cY3
  have := chC_nonneg sys hL j
  have := Mtot_pos sys j
  have := cst_pos sys
  have := one_le_mmax sys
  apply div_nonneg _ (cst_pos sys).le
  apply div_nonneg _ (Mtot_pos sys j).le
  positivity

/-- **The well-gapped `Y`-hop from cold off the cube on the lines**:
`|y_j(d,b)| ≤ κ(d) = (64 m c_j/(M̄ c_*))/max(n², |ζ(d)|²)`. -/
lemma yj_cold_notP_le_kap (hL : 0 < L) (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ}
    (hA : IsCoord j A ε) {d b : Cfg eta N} (hb : InC (n : ℝ) (cst sys) (cidx N b))
    (hd : ¬ InP (n : ℝ) (cidx N d)) :
    ‖yj sys L p₀ N j d b‖ ≤ if lab N j d = lab N j b then kapM n (cY3 sys L j) A d else 0 := by
  by_cases hj : OnCh j (cidx N d) (cidx N b)
  · rw [if_pos (lab_eq_iff.mpr hj)]
    have h1 := norm_yj_cold_notP_le (p₀ := p₀) hL hn hb hd hj
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hpi : piC j (cidx N b) ≤ 2 * (cst sys * n) :=
      piC_le_of_regs j cst_mul_nonneg (fun c => rho_le_of_inC hb c)
    have hpi0 := piC_nonneg j (cidx N b)
    have hcs := cst_le32 sys
    have hc := cst_pos sys
    have hl0 := long_of_cold_notP hb hd hj
    have hl : (cst sys * n) ^ 2 ≤ FSLattice.lsq (chT N j d b) := by
      have e1 : cst sys * n ≤ (n : ℝ) / 2 := by nlinarith
      have e2 : 0 ≤ cst sys * n := by positivity
      exact (pow_le_pow_left₀ e2 e1 2).trans hl0
    have hk := kappa_long hn hA hb hj hl
    have hθ : 0 < FSLattice.lsq (chT N j d b) := lt_of_lt_of_le (by positivity) hl
    have hcC := chC_nonneg sys hL j
    have hM := Mtot_pos sys j
    have hm := one_le_mmax sys
    have hq : piC j (cidx N b) / n ≤ 2 * cst sys := by
      rw [div_le_iff₀ hn0]; linarith
    have hq0 : 0 ≤ piC j (cidx N b) / n := div_nonneg hpi0 hn0.le
    have hK0 : 0 ≤ 32 * mmax sys * chC sys L j / Mtot sys j := by positivity
    set M := max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d))) with hMdef
    have hMpos : 0 < M := max_pos_n hn _
    unfold kapM
    rw [← hMdef]
    calc ‖yj sys L p₀ N j d b‖ ≤ 32 * mmax sys * chC sys L j / Mtot sys j *
          (piC j (cidx N b) / n) / FSLattice.lsq (chT N j d b) := h1
      _ = 32 * mmax sys * chC sys L j / Mtot sys j * (piC j (cidx N b) / n) *
          (1 / FSLattice.lsq (chT N j d b)) := by ring
      _ ≤ 32 * mmax sys * chC sys L j / Mtot sys j * (2 * cst sys) * ((1 / cst sys ^ 2) / M) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hq hK0) hk (by positivity) (by positivity)
      _ = cY3 sys L j / M := by
          unfold cY3
          field_simp
          ring
  · rw [if_neg (fun h => hj (lab_eq_iff.mp h))]
    unfold yj ycKc
    rw [if_neg hj, norm_zero]

/-- **The flat second hop from the short ball, weighted by `ω_F`**:
`ω_F(f) |w_j(f,d)| ≤ (2048 m c_j/g²)/max(n², |ζ(f)|²)²` on the `j`-lines. -/
lemma farW_wj_ball_le (hL : 0 < L) (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ}
    (hA : IsCoord j A ε) {f d : Cfg eta N} (hd : SB sys N n d) :
    farW sys L N n f * ‖wj sys L N j f d‖ ≤
      if lab N j f = lab N j d then kapM2 n (2048 * mmax sys * chC sys L j / gF L ^ 2) A f else 0 := by
  have hw := norm_wj_le (sys := sys) hL j f d
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hcC := chC_nonneg sys hL j
  have hk0 : 0 ≤ kapM2 n (2048 * mmax sys * chC sys L j / gF L ^ 2) A f :=
    kapM2_nonneg hn (by positivity) A f
  by_cases hfQ : InQ (n : ℝ) (cidx N f)
  · have h0 : farW sys L N n f = 0 := by unfold farW; rw [if_pos hfQ]
    rw [h0, zero_mul]
    split_ifs
    · exact hk0
    · exact le_rfl
  · by_cases hj : OnCh j (cidx N f) (cidx N d)
    · rw [if_pos (lab_eq_iff.mpr hj)]
      rw [if_pos hj] at hw
      have h1 := farW_le_max (sys := sys) hL hn hA.card f
      have h2 := kappa_ball hn hA hd hfQ hj
      set M := max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) with hMdef
      have hMpos : 0 < M := max_pos_n hn _
      have hw2 : ‖wj sys L N j f d‖ ≤ chC sys L j * (64 / M) := by
        refine hw.trans ?_
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left h2 hcC
      unfold kapM2
      rw [← hMdef]
      calc farW sys L N n f * ‖wj sys L N j f d‖ ≤
          (32 * mmax sys / gF L ^ 2 / M) * (chC sys L j * (64 / M)) :=
            mul_le_mul h1 hw2 (norm_nonneg _) (by positivity)
        _ = 2048 * mmax sys * chC sys L j / gF L ^ 2 / M ^ 2 := by
            field_simp
            ring
    · rw [if_neg hj] at hw
      have h0 : ‖wj sys L N j f d‖ = 0 := le_antisymm hw (norm_nonneg _)
      rw [h0, mul_zero]
      split_ifs
      · exact hk0
      · exact le_rfl

variable (sys L) in
/-- The constant of the com second hop from the short ball: `2 c_j g² (32 m/g²)²/M̄_j`. -/
noncomputable def cYb (j : Ch eta) : ℝ :=
  2 * chC sys L j * gF L ^ 2 * (32 * mmax sys / gF L ^ 2) ^ 2 / Mtot sys j

lemma cYb_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ cYb sys L j := by
  unfold cYb
  have := chC_nonneg sys hL j
  have := gF_pos hL
  have := one_le_mmax sys
  apply div_nonneg _ (Mtot_pos sys j).le
  positivity

open Classical in
/-- **The com second hop from the short ball, off the cube, weighted by `ω_F`**. -/
lemma farW_yj_ball_le' (hL : 0 < L) (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ}
    (hA : IsCoord j A ε) {f d : Cfg eta N} (hd : SB sys N n d) :
    farW sys L N n f * (if ¬ InP (n : ℝ) (cidx N f) then ‖yj sys L p₀ N j f d‖ else 0) ≤
      if lab N j f = lab N j d then kapM2 n (cYb sys L j) A f else 0 := by
  have hk0 : 0 ≤ kapM2 n (cYb sys L j) A f := kapM2_nonneg hn (cYb_nonneg hL j) A f
  by_cases hfP : InP (n : ℝ) (cidx N f)
  · rw [if_neg (not_not_intro hfP), mul_zero]
    split_ifs
    · exact hk0
    · exact le_rfl
  · rw [if_pos hfP]
    by_cases hj : OnCh j (cidx N f) (cidx N d)
    · rw [if_pos (lab_eq_iff.mpr hj)]
      exact farW_yj_ball_le hL hn hA.card hfP hd hj
    · have h0 : yj sys L p₀ N j f d = 0 := by unfold yj ycKc; rw [if_neg hj]
      rw [h0, norm_zero, mul_zero]
      split_ifs
      · exact hk0
      · exact le_rfl

end Hops

/-! ## The five chains against cold inputs -/

section Words

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

omit [Fintype ν] in
variable (sys L) in
/-- The L1-W constant `(2048 m²/g⁴) c₂² H² c₁'² 277`. -/
noncomputable def KW1 (Hunit c₂ c₁ : ℝ) : ℝ :=
  2048 * mmax sys ^ 2 / gF L ^ 4 * c₂ ^ 2 * Hunit ^ 2 * c₁ ^ 2 * 277

variable (sys L) in
/-- The L1-Y constant `(2048 m²/g⁴) (C_{j₂} Λ_N)² c₁'² 277`. -/
noncomputable def KY1 (N : ℕ) (j₂ : Ch eta) (c₁ : ℝ) : ℝ :=
  2048 * mmax sys ^ 2 / gF L ^ 4 * (CYc sys L j₂ * LamB sys N) ^ 2 * c₁ ^ 2 * 277

variable (sys L) in
/-- The L2 constant `c₂'² 277 ((26 c_* c₁)² + 2 c₁² H²)`. -/
noncomputable def KL2 (Hunit c₂ : ℝ) (j₁ : Ch eta) : ℝ :=
  c₂ ^ 2 * 277 * ((26 * cst sys * chC sys L j₁) ^ 2 + 2 * chC sys L j₁ ^ 2 * Hunit ^ 2)

omit [Fintype ν] in
lemma KW1_nonneg (hL : 0 < L) (Hunit c₂ c₁ : ℝ) : 0 ≤ KW1 sys L Hunit c₂ c₁ := by
  unfold KW1
  have := gF_pos hL
  positivity

lemma KY1_nonneg (hL : 0 < L) (N : ℕ) (j₂ : Ch eta) (c₁ : ℝ) : 0 ≤ KY1 sys L N j₂ c₁ := by
  unfold KY1
  have := gF_pos hL
  positivity

lemma KL2_nonneg (Hunit c₂ : ℝ) (j₁ : Ch eta) : 0 ≤ KL2 sys L Hunit c₂ j₁ := by
  unfold KL2
  positivity

omit [Fintype ν] in
/-- The L1-W bound in the `n⁻³` form. -/
lemma L1W_form (hL : 0 < L) (hn : 1 ≤ n) (Hunit c₂ c₁ Lx : ℝ) :
    2048 * mmax sys ^ 2 / gF L ^ 4 / (n : ℝ) ^ 2 * c₂ ^ 2 * Hunit ^ 2 * (c₁ ^ 2 * (277 / n) * Lx) =
      KW1 sys L Hunit c₂ c₁ / (n : ℝ) ^ 3 * Lx := by
  unfold KW1
  have hg := (gF_pos hL).ne'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  field_simp

/-- The L1-Y bound in the `n⁻³` form. -/
lemma L1Y_form (hL : 0 < L) (hn : 1 ≤ n) (j₂ : Ch eta) (c₁ Lx : ℝ) :
    2048 * mmax sys ^ 2 / gF L ^ 4 / (n : ℝ) ^ 2 * (CYc sys L j₂ * LamB sys N) ^ 2 *
        (c₁ ^ 2 * (277 / n) * Lx) = KY1 sys L N j₂ c₁ / (n : ℝ) ^ 3 * Lx := by
  unfold KY1
  have hg := (gF_pos hL).ne'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  field_simp

/-- The L2 bound in the `n⁻³` form. -/
lemma L2_form (hn : 1 ≤ n) (Hunit c₂ : ℝ) (j₁ : Ch eta) (Lx : ℝ) :
    c₂ ^ 2 * (277 / (n : ℝ) ^ 5) * ((n : ℝ) ^ 2 * ((26 * cst sys * chC sys L j₁) ^ 2 +
        2 * chC sys L j₁ ^ 2 * Hunit ^ 2) * Lx) = KL2 sys L Hunit c₂ j₁ / (n : ℝ) ^ 3 * Lx := by
  unfold KL2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  field_simp

/-- The support of a short hop applied to `x`: the short ball. -/
lemma vS_supp {j : Ch eta} {x : Cfg eta N → ℝ} {d : Cfg eta N}
    (h : ∑ b, WS sys L N n j d b * x b ≠ 0) : SB sys N n d := by
  obtain ⟨b, _, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact (WS_supp (left_ne_zero_of_mul hb)).1

/-- **Ch1** (`R W₂ P W₁ Π_C`): `Φ ≤ (2 KW1 + 2 KL2) n⁻³ (L²_{j₁} + L²_{j₂})`. -/
theorem P2_ch1 {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit) (hL : 0 < L)
    (hn : 1 ≤ n) (j₂ j₁ : Ch eta) (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b)
    (hxC : ∀ b, x b ≠ 0 → InC (n : ℝ) (cst sys) (cidx N b)) :
    ∑ f, farW sys L N n f ^ 2 * (∑ b, ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun d => InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b) ^ 2 ≤
      (2 * KW1 sys L Hunit (chC sys L j₂) (chC sys L j₁ * (1 / cst sys ^ 2)) +
        2 * KL2 sys L Hunit (2048 * mmax sys * chC sys L j₂ / gF L ^ 2) j₁) / (n : ℝ) ^ 3 *
        (lineSq j₁ (fun _ => 1) x + lineSq j₂ (fun _ => 1) x) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hc₂ := chC_nonneg sys hL j₂
  set vL : Cfg eta N → ℝ := fun d => ∑ b, WL sys L N n j₁ d b * x b with hvL
  set vS : Cfg eta N → ℝ := fun d => ∑ b, WS sys L N n j₁ d b * x b with hvS
  have hpt : ∀ f, ∑ b, ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun d => InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b ≤
      ∑ d, ‖wj sys L N j₂ f d‖ * vL d + ∑ d, ‖wj sys L N j₂ f d‖ * vS d := by
    intro f
    have h := chain_sum_le (fun q => ¬ InP (n : ℝ) (cidx N q))
      (fun d => InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
      (wj sys L N j₂) (wj sys L N j₁) x hx
      (fun f d => ‖wj sys L N j₂ f d‖)
      (fun d b => WL sys L N n j₁ d b + WS sys L N n j₁ d b)
      (fun f d => norm_nonneg _) (fun d b => add_nonneg (WL_nonneg hL j₁ d b) (WS_nonneg hL j₁ d b))
      (fun f d _ _ => le_rfl) (fun d b _ hb _ => norm_wj_le_split hL j₁ hb) f
    refine h.trans (le_of_eq ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hvL, hvS, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hΨ0 : ∀ f, 0 ≤ ∑ b, ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun d => InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b :=
    fun f => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hx b)
  refine (sum_sq_le_add Finset.univ _ _ _ _ hΨ0 hpt).trans ?_
  -- the long part
  have hL1 := shape_L1W (sys := sys) hH hL hn (coord_lead j₂) (fun f d => ‖wj sys L N j₂ f d‖)
    (WL sys L N n j₁) (fun f d => norm_nonneg _) (WL_nonneg hL j₁) hc₂
    (fun f d => norm_wj_le hL j₂ f d) (kappaL sys L N n {lead j₁} j₁)
    (WL_le_kappa hL hn (coord_lead j₁)) (sum_kappaL_sq_le hn (coord_lead j₁)) x hx
  rw [L1W_form hL hn] at hL1
  -- the short part
  have hvS0 : ∀ d, 0 ≤ vS d := fun d =>
    Finset.sum_nonneg fun b _ => mul_nonneg (WS_nonneg hL j₁ d b) (hx b)
  have hL2 := shape_L2 (sys := sys) (L := L) (n := n) j₂ (fun f d => ‖wj sys L N j₂ f d‖)
    (fun f d => norm_nonneg _) vS hvS0 (SB sys N n) (fun d hd => vS_supp hd)
    (kapM2 n (2048 * mmax sys * chC sys L j₂ / gF L ^ 2) {lead j₂})
    (fun f => kapM2_nonneg hn (by positivity) _ f)
    (fun f d hd => farW_wj_ball_le hL hn (coord_lead j₂) hd)
    (sum_kapM2_sq_le hn (coord_lead j₂) _)
  have hWS := lineSq_WS_le hH hL hn j₁ j₂ x hx hxC
  have hL2' : ∑ f, farW sys L N n f ^ 2 * (∑ d, ‖wj sys L N j₂ f d‖ * vS d) ^ 2 ≤
      KL2 sys L Hunit (2048 * mmax sys * chC sys L j₂ / gF L ^ 2) j₁ / (n : ℝ) ^ 3 *
        (lineSq j₁ (fun _ => 1) x + lineSq j₂ (fun _ => 1) x) := by
    refine hL2.trans ?_
    rw [← L2_form hn]
    exact mul_le_mul_of_nonneg_left hWS (by positivity)
  exact comb_two (KW1_nonneg hL _ _ _)
    (lineSq_nonneg j₂ (fun _ => zero_le_one) x) hD hL1 hL2'

/-- **Ch2, flat** (`F' W₂ R W₁ Π_C`, the first hop long): `Φ ≤ KW1 n⁻³ L²_{j₁}`. -/
theorem P2_ch2fl {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit) (hL : 0 < L)
    (hn : 1 ≤ n) (j₂ j₁ : Ch eta) (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b) ^ 2 ≤
      KW1 sys L Hunit (chC sys L j₂) (chC sys L j₁ * (1 / cst sys ^ 2)) / (n : ℝ) ^ 3 *
        (lineSq j₁ (fun _ => 1) x + lineSq j₂ (fun _ => 1) x) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hc₂ := chC_nonneg sys hL j₂
  have hpt : ∀ f, ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b ≤
      ∑ d, ‖wj sys L N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b :=
    chain_sum_le _ _ _ (wj sys L N j₂) (wj sys L N j₁) x hx
      (fun f d => ‖wj sys L N j₂ f d‖) (WL sys L N n j₁)
      (fun f d => norm_nonneg _) (WL_nonneg hL j₁)
      (fun f d _ _ => le_rfl) (fun d b hd hb _ => norm_wj_notP_le hL j₁ hb hd)
  have hΨ0 : ∀ f, 0 ≤ ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b :=
    fun f => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hx b)
  refine (sum_sq_le_of_le Finset.univ _ _ _ hΨ0 hpt).trans ?_
  have hL1 := shape_L1W (sys := sys) hH hL hn (coord_lead j₂) (fun f d => ‖wj sys L N j₂ f d‖)
    (WL sys L N n j₁) (fun f d => norm_nonneg _) (WL_nonneg hL j₁) hc₂
    (fun f d => norm_wj_le hL j₂ f d) (kappaL sys L N n {lead j₁} j₁)
    (WL_le_kappa hL hn (coord_lead j₁)) (sum_kappaL_sq_le hn (coord_lead j₁)) x hx
  rw [L1W_form hL hn] at hL1
  exact weaken_one (KW1_nonneg hL _ _ _) (lineSq_nonneg j₂ (fun _ => zero_le_one) x) hD hL1

/-- **Ch3** (`F W₂ R Y₁ Π_C`, the `Y`-hop well-gapped and long): `Φ ≤ KW1(c₂, cY3₁) n⁻³ L²_{j₁}`. -/
theorem P2_ch3 {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit) (hL : 0 < L)
    (hn : 1 ≤ n) (j₂ j₁ : Ch eta) (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ b, ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (yj sys L p₀ N j₁) f b‖ * x b) ^ 2 ≤
      KW1 sys L Hunit (chC sys L j₂) (cY3 sys L j₁) / (n : ℝ) ^ 3 *
        (lineSq j₁ (fun _ => 1) x + lineSq j₂ (fun _ => 1) x) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hc₂ := chC_nonneg sys hL j₂
  set K₁ : Cfg eta N → Cfg eta N → ℝ := fun d b =>
    if InC (n : ℝ) (cst sys) (cidx N b) ∧ ¬ InP (n : ℝ) (cidx N d) then ‖yj sys L p₀ N j₁ d b‖ else 0
    with hK₁
  have hK₁0 : ∀ d b, 0 ≤ K₁ d b := fun d b => by
    simp only [hK₁]; split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hK₁b : ∀ d b, K₁ d b ≤
      if lab N j₁ d = lab N j₁ b then kapM n (cY3 sys L j₁) {lead j₁} d else 0 := by
    intro d b
    simp only [hK₁]
    split_ifs with h1 h2
    · have := yj_cold_notP_le_kap (p₀ := p₀) hL hn (coord_lead j₁) h1.1 h1.2 (d := d)
      rwa [if_pos h2] at this
    · have := yj_cold_notP_le_kap (p₀ := p₀) hL hn (coord_lead j₁) h1.1 h1.2 (d := d)
      rwa [if_neg h2] at this
    · exact kapM_nonneg hn (cY3_nonneg hL j₁) _ d
    · exact le_rfl
  have hpt : ∀ f, ∑ b, ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (yj sys L p₀ N j₁) f b‖ * x b ≤
      ∑ d, ‖wj sys L N j₂ f d‖ * ∑ b, K₁ d b * x b :=
    chain_sum_le _ _ _ (wj sys L N j₂) (yj sys L p₀ N j₁) x hx
      (fun f d => ‖wj sys L N j₂ f d‖) K₁
      (fun f d => norm_nonneg _) hK₁0
      (fun f d _ _ => le_rfl) (fun d b hd hb _ => by simp only [hK₁]; rw [if_pos ⟨hb, hd⟩])
  have hΨ0 : ∀ f, 0 ≤ ∑ b, ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (yj sys L p₀ N j₁) f b‖ * x b :=
    fun f => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hx b)
  refine (sum_sq_le_of_le Finset.univ _ _ _ hΨ0 hpt).trans ?_
  have hL1 := shape_L1W (sys := sys) hH hL hn (coord_lead j₂) (fun f d => ‖wj sys L N j₂ f d‖)
    K₁ (fun f d => norm_nonneg _) hK₁0 hc₂
    (fun f d => norm_wj_le hL j₂ f d) (kapM n (cY3 sys L j₁) {lead j₁})
    hK₁b (sum_kapM_sq_le hn (coord_lead j₁) _) x hx
  rw [L1W_form hL hn] at hL1
  exact weaken_one (KW1_nonneg hL _ _ _) (lineSq_nonneg j₂ (fun _ => zero_le_one) x) hD hL1

/-- **Ch4** (`R Y₂ W₁ Π_C`): `Φ ≤ (2 KY1 + 2 KL2) n⁻³ (L²_{j₁} + L²_{j₂})`. -/
theorem P2_ch4 {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit) (hL : 0 < L)
    (hn : 1 ≤ n)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (j₂ j₁ : Ch eta) (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b)
    (hxC : ∀ b, x b ≠ 0 → InC (n : ℝ) (cst sys) (cidx N b)) :
    ∑ f, farW sys L N n f ^ 2 * (∑ b, ‖chainK' (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b) ^ 2 ≤
      (2 * KY1 sys L N j₂ (chC sys L j₁ * (1 / cst sys ^ 2)) +
        2 * KL2 sys L Hunit (cYb sys L j₂) j₁) / (n : ℝ) ^ 3 *
        (lineSq j₁ (fun _ => 1) x + lineSq j₂ (fun _ => 1) x) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  set vL : Cfg eta N → ℝ := fun d => ∑ b, WL sys L N n j₁ d b * x b with hvL
  set vS : Cfg eta N → ℝ := fun d => ∑ b, WS sys L N n j₁ d b * x b with hvS
  set K₂ : Cfg eta N → Cfg eta N → ℝ := fun f d =>
    if ¬ InP (n : ℝ) (cidx N f) then ‖yj sys L p₀ N j₂ f d‖ else 0 with hK₂
  have hK₂0 : ∀ f d, 0 ≤ K₂ f d := fun f d => by
    simp only [hK₂]; split_ifs <;> first | exact norm_nonneg _ | exact le_rfl
  have hK₂le : ∀ f d, K₂ f d ≤ ‖yj sys L p₀ N j₂ f d‖ := fun f d => by
    simp only [hK₂]; split_ifs <;> first | exact le_rfl | exact norm_nonneg _
  have hvL0 : ∀ d, 0 ≤ vL d := fun d =>
    Finset.sum_nonneg fun b _ => mul_nonneg (WL_nonneg hL j₁ d b) (hx b)
  have hpt : ∀ f, ∑ b, ‖chainK' (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b ≤
      ∑ d, ‖yj sys L p₀ N j₂ f d‖ * vL d + ∑ d, K₂ f d * vS d := by
    intro f
    have h := chain'_sum_le (fun q => ¬ InP (n : ℝ) (cidx N q))
      (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (yj sys L p₀ N j₂) (wj sys L N j₁) x hx K₂
      (fun d b => WL sys L N n j₁ d b + WS sys L N n j₁ d b)
      hK₂0 (fun d b => add_nonneg (WL_nonneg hL j₁ d b) (WS_nonneg hL j₁ d b))
      (fun f d hf => by simp only [hK₂]; rw [if_pos hf])
      (fun d b hb _ => norm_wj_le_split hL j₁ hb) f
    refine h.trans ?_
    have e : ∑ d, K₂ f d * ∑ b, (WL sys L N n j₁ d b + WS sys L N n j₁ d b) * x b =
        ∑ d, K₂ f d * vL d + ∑ d, K₂ f d * vS d := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hvL, hvS, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [e]
    have h2 : ∑ d, K₂ f d * vL d ≤ ∑ d, ‖yj sys L p₀ N j₂ f d‖ * vL d :=
      Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (hK₂le f d) (hvL0 d)
    linarith
  have hΨ0 : ∀ f, 0 ≤ ∑ b, ‖chainK' (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b :=
    fun f => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hx b)
  refine (sum_sq_le_add Finset.univ _ _ _ _ hΨ0 hpt).trans ?_
  -- the long part
  have hL1 := shape_L1Y (p₀ := p₀) hL hn H hKernel j₂ (WL sys L N n j₁) (WL_nonneg hL j₁)
    (kappaL sys L N n {lead j₁} j₁) (WL_le_kappa hL hn (coord_lead j₁))
    (sum_kappaL_sq_le hn (coord_lead j₁)) x hx
  rw [L1Y_form hL hn] at hL1
  -- the short part
  have hvS0 : ∀ d, 0 ≤ vS d := fun d =>
    Finset.sum_nonneg fun b _ => mul_nonneg (WS_nonneg hL j₁ d b) (hx b)
  have hL2 := shape_L2 (sys := sys) (L := L) (n := n) j₂ K₂ hK₂0 vS hvS0 (SB sys N n)
    (fun d hd => vS_supp hd)
    (kapM2 n (cYb sys L j₂) {lead j₂}) (fun f => kapM2_nonneg hn (cYb_nonneg hL j₂) _ f)
    (fun f d hd => farW_yj_ball_le' hL hn (coord_lead j₂) hd)
    (sum_kapM2_sq_le hn (coord_lead j₂) _)
  have hWS := lineSq_WS_le hH hL hn j₁ j₂ x hx hxC
  have hL2' : ∑ f, farW sys L N n f ^ 2 * (∑ d, K₂ f d * vS d) ^ 2 ≤
      KL2 sys L Hunit (cYb sys L j₂) j₁ / (n : ℝ) ^ 3 *
        (lineSq j₁ (fun _ => 1) x + lineSq j₂ (fun _ => 1) x) := by
    refine hL2.trans ?_
    rw [← L2_form hn]
    exact mul_le_mul_of_nonneg_left hWS (by positivity)
  exact comb_two (KY1_nonneg hL _ _ _)
    (lineSq_nonneg j₂ (fun _ => zero_le_one) x) hD hL1 hL2'

/-- **Ch2, com** (`F' Y₂ R W₁ Π_C`, the first hop long): `Φ ≤ KY1 n⁻³ L²_{j₁}`. -/
theorem P2_ch2com (hL : 0 < L) (hn : 1 ≤ n)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (j₂ j₁ : Ch eta) (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b) ^ 2 ≤
      KY1 sys L N j₂ (chC sys L j₁ * (1 / cst sys ^ 2)) / (n : ℝ) ^ 3 *
        (lineSq j₁ (fun _ => 1) x + lineSq j₂ (fun _ => 1) x) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hpt : ∀ f, ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b ≤
      ∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b :=
    chain_sum_le _ _ _ (yj sys L p₀ N j₂) (wj sys L N j₁) x hx
      (fun f d => ‖yj sys L p₀ N j₂ f d‖) (WL sys L N n j₁)
      (fun f d => norm_nonneg _) (WL_nonneg hL j₁)
      (fun f d _ _ => le_rfl) (fun d b hd hb _ => norm_wj_notP_le hL j₁ hb hd)
  have hΨ0 : ∀ f, 0 ≤ ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b :=
    fun f => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hx b)
  refine (sum_sq_le_of_le Finset.univ _ _ _ hΨ0 hpt).trans ?_
  have hL1 := shape_L1Y (p₀ := p₀) hL hn H hKernel j₂ (WL sys L N n j₁) (WL_nonneg hL j₁)
    (kappaL sys L N n {lead j₁} j₁) (WL_le_kappa hL hn (coord_lead j₁))
    (sum_kappaL_sq_le hn (coord_lead j₁)) x hx
  rw [L1Y_form hL hn] at hL1
  exact weaken_one (KY1_nonneg hL _ _ _) (lineSq_nonneg j₂ (fun _ => zero_le_one) x) hD hL1

end Words

end FSFlux
