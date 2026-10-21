import PlaneWave.FluxBox.FarColdDressing

/-!
# Flux route, stage 3, part 27: the hop bounds of the far–cold words

* the short ball `SB(d)`: every register `≤ 2 c_* n`; a hop from it to the far region is long
  (`long_of_ball`);
* `κ`-bounds: a long hop from cold, `1/|θ|² ≤ c_*⁻²/max(n², |ζ(d)|²)` (`kappa_long`); a hop from the
  short ball to the far region, `1/|θ|² ≤ 64/max(n², |ζ(f)|²)` (`kappa_ball`);
* the channel kernels: `|w_j| ≤ c_j/|θ|²` (`norm_wj_le`); the com dressing on its floor,
  `|y_j| ≤ (C_j/2) |Π_j(p)|/|θ|²` (`norm_yj_le_floor`) and with its gap (`norm_yj_le_gap`);
* the well-gapped Y-hops: from cold off the cube, `|y_j(d,b)| ≤ 32 m c_j (|Π_j(b)|/n)/(M̄ |θ|²)`
  (`norm_yj_cold_notP_le`); from the short ball off the cube, `ω_F |y_j(f,d)| ≤ κ(f)` with
  `κ(f) = 2 c_j g² (32 m/g²)²/(M̄ max(n², |ζ(f)|²)²)` (`farW_yj_ball_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Kappa

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

variable (sys N n) in
/-- The short ball: every register at most `2 c_* n`. -/
def SB (d : Cfg eta N) : Prop := ∀ c, FSChannel.rho (cidx N d c) ≤ 2 * (cst sys * n)

omit [Fintype ν] in
/-- A short hop from cold lands in the short ball. -/
lemma SB_of_short {j : Ch eta} {d b : Cfg eta N} (hb : InC (n : ℝ) (cst sys) (cidx N b))
    (h : OnCh j (cidx N d) (cidx N b)) (hs : FSLattice.lsq (chT N j d b) < (cst sys * n) ^ 2) :
    SB sys N n d := fun c => short_ball hb h hs c

omit [Fintype ν] in
/-- **A hop from the short ball to the far region is long**: `|θ|² ≥ (n/8)²`. -/
lemma long_of_ball {j : Ch eta} {f d : Cfg eta N} (hd : SB sys N n d)
    (hf : ¬ InQ (n : ℝ) (cidx N f)) (h : OnCh j (cidx N f) (cidx N d)) :
    ((n : ℝ) / 8) ^ 2 ≤ FSLattice.lsq (chT N j f d) := by
  obtain ⟨c, hc⟩ := exists_rho_gt_of_notQ hf
  have h1 := hd c
  have h2 := FSChannel.rho_le_add_rho_sub (cidx N f c) (cidx N d c)
  have h3 := rho_reg_hop_le h c
  have hcs := cst_le32 sys
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : (n : ℝ) / 8 ≤ FSChannel.rho (chT N j f d) := by
    show (n : ℝ) / 8 ≤ FSChannel.rho (cidx N f (lead j) - cidx N d (lead j))
    nlinarith
  rw [← FSChannel.rho_sq]
  exact pow_le_pow_left₀ (by positivity) h4 2

omit [Fintype ν] in
lemma rho_sign_smul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (τ : Lattice3) :
    FSChannel.rho (ε • τ) = FSChannel.rho τ := by
  unfold FSChannel.rho
  rw [lsq_sign_smul hε]

omit [Fintype ν] in
/-- A coordinate of a cold configuration: `|ζ| ≤ 2 c_* n`. -/
lemma rho_coord_cold {A : Finset (Fin eta)} (hA : A.card ≤ 2) {b : Cfg eta N}
    (hb : InC (n : ℝ) (cst sys) (cidx N b)) :
    FSChannel.rho (regSum A (cidx N b)) ≤ 2 * (cst sys * n) :=
  rho_regSum_le hA cst_mul_nonneg fun c => rho_le_of_inC hb c

omit [Fintype ν] in
/-- **The long hop from cold**: `1/|θ|² ≤ c_*⁻²/max(n², |ζ(d)|²)` when `|θ| ≥ c_* n`. -/
lemma kappa_long (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    {d b : Cfg eta N} (hb : InC (n : ℝ) (cst sys) (cidx N b)) (h : OnCh j (cidx N d) (cidx N b))
    (hl : (cst sys * n) ^ 2 ≤ FSLattice.lsq (chT N j d b)) :
    1 / FSLattice.lsq (chT N j d b) ≤
      (1 / cst sys ^ 2) / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d))) := by
  have hc := cst_pos sys
  have hcs := cst_le32 sys
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set θ := chT N j d b
  have hθ : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) hl
  have hρθ : cst sys * n ≤ FSChannel.rho θ := by
    unfold FSChannel.rho; exact Real.le_sqrt_of_sq_le hl
  have he := hA.onCh h
  have hz : FSChannel.rho (regSum A (cidx N d)) ≤ 3 * FSChannel.rho θ := by
    have h1 := FSChannel.rho_add_le (regSum A (cidx N b)) (ε • (cidx N d (lead j) - cidx N b (lead j)))
    rw [← he, rho_sign_smul hA.sign] at h1
    have h2 := rho_coord_cold hA.card hb
    have h3 : FSChannel.rho (cidx N d (lead j) - cidx N b (lead j)) = FSChannel.rho θ := rfl
    linarith
  have hz2 : FSLattice.lsq (regSum A (cidx N d)) ≤ 9 * FSLattice.lsq θ := by
    rw [← FSChannel.rho_sq, ← FSChannel.rho_sq]
    have := FSChannel.rho_nonneg (regSum A (cidx N d))
    nlinarith
  have hn2 : (n : ℝ) ^ 2 ≤ FSLattice.lsq θ / cst sys ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc (n : ℝ) ^ 2 * cst sys ^ 2 = (cst sys * n) ^ 2 := by ring
      _ ≤ _ := hl
  have h9 : 9 * FSLattice.lsq θ ≤ FSLattice.lsq θ / cst sys ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : cst sys ^ 2 ≤ 1 / 1024 := by
      have := pow_le_pow_left₀ hc.le hcs 2; norm_num at this ⊢; linarith
    nlinarith
  have hM : max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d))) ≤ FSLattice.lsq θ / cst sys ^ 2 :=
    max_le hn2 (hz2.trans h9)
  have hM0 : 0 < max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d))) :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  rw [div_le_div_iff₀ hθ hM0, one_mul]
  calc max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d))) ≤ FSLattice.lsq θ / cst sys ^ 2 := hM
    _ = 1 / cst sys ^ 2 * FSLattice.lsq θ := by ring

omit [Fintype ν] in
/-- **The hop from the short ball to the far region**: `1/|θ|² ≤ 64/max(n², |ζ(f)|²)`. -/
lemma kappa_ball (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    {f d : Cfg eta N} (hd : SB sys N n d) (hf : ¬ InQ (n : ℝ) (cidx N f))
    (h : OnCh j (cidx N f) (cidx N d)) :
    1 / FSLattice.lsq (chT N j f d) ≤ 64 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) := by
  have hc := cst_pos sys
  have hcs := cst_le32 sys
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set θ := chT N j f d
  have hl := long_of_ball hd hf h
  have hθ : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) hl
  have hρθ : (n : ℝ) / 8 ≤ FSChannel.rho θ := by
    unfold FSChannel.rho; exact Real.le_sqrt_of_sq_le hl
  have he := hA.onCh h
  have hz : FSChannel.rho (regSum A (cidx N f)) ≤ 2 * FSChannel.rho θ := by
    have h1 := FSChannel.rho_add_le (regSum A (cidx N d)) (ε • (cidx N f (lead j) - cidx N d (lead j)))
    rw [← he, rho_sign_smul hA.sign] at h1
    have h2 : FSChannel.rho (regSum A (cidx N d)) ≤ 2 * (2 * (cst sys * n)) :=
      rho_regSum_le hA.card (by positivity) hd
    have h3 : FSChannel.rho (cidx N f (lead j) - cidx N d (lead j)) = FSChannel.rho θ := rfl
    have h4 : 2 * (2 * (cst sys * n)) ≤ (n : ℝ) / 8 := by nlinarith
    linarith
  have hz2 : FSLattice.lsq (regSum A (cidx N f)) ≤ 4 * FSLattice.lsq θ := by
    rw [← FSChannel.rho_sq, ← FSChannel.rho_sq]
    have := FSChannel.rho_nonneg (regSum A (cidx N f))
    nlinarith
  have hn2 : (n : ℝ) ^ 2 ≤ 64 * FSLattice.lsq θ := by nlinarith
  have hM : max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) ≤ 64 * FSLattice.lsq θ :=
    max_le hn2 (by linarith)
  have hM0 : 0 < max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  rw [div_le_div_iff₀ hθ hM0, one_mul]
  exact hM

omit [Fintype ν] in
/-- A coordinate is at most the length: `|k_i| ≤ |k|`. -/
lemma abs_coord_le_rho (k : Lattice3) (i : Fin 3) : |((k i : ℤ) : ℝ)| ≤ FSChannel.rho k := by
  unfold FSChannel.rho
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  unfold FSLattice.lsq
  fin_cases i <;> simp <;> nlinarith [sq_nonneg ((k 0 : ℤ) : ℝ), sq_nonneg ((k 1 : ℤ) : ℝ),
    sq_nonneg ((k 2 : ℤ) : ℝ)]

omit [Fintype ν] in
/-- Cold configurations are in the cube. -/
lemma inP_of_inC {k : Cf eta} (h : InC (n : ℝ) (cst sys) k) : InP (n : ℝ) k := by
  intro c i
  have h1 := rho_le_of_inC h c
  have hcs := cst_le32 sys
  have hc := cst_pos sys
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 := abs_coord_le_rho (k c) i
  nlinarith

omit [Fintype ν] in
/-- The bulk ball is in the cube. -/
lemma inP_of_inQ' {k : Cf eta} (h : InQ (n : ℝ) k) : InP (n : ℝ) k := by
  intro c i
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 := rho_le_of_inQ hn h c
  have h2 := abs_coord_le_rho (k c) i
  linarith

omit [Fintype ν] in
/-- The short ball is in the cube. -/
lemma inP_of_SB {d : Cfg eta N} (h : SB sys N n d) : InP (n : ℝ) (cidx N d) := by
  intro c i
  have h1 := h c
  have hcs := cst_le32 sys
  have hc := cst_pos sys
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 := abs_coord_le_rho (cidx N d c) i
  nlinarith

end Kappa

/-! ## The channel kernels -/

section ChanKernels

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

open Classical in
/-- **The Coulomb kernel on a channel**: `|w_j(q,p)| ≤ c_j/|θ|²`. -/
lemma norm_wj_le (hL : 0 < L) (j : Ch eta) (q p : Cfg eta N) :
    ‖wj sys L N j q p‖ ≤
      if OnCh j (cidx N q) (cidx N p) then chC sys L j / FSLattice.lsq (chT N j q p) else 0 := by
  unfold wj chPart
  split_ifs with hj
  · by_cases hqp : q = p
    · subst hqp
      rw [wNK_self hL, norm_zero]
      exact div_nonneg (chC_nonneg sys hL j) (FSLattice.lsq_nonneg _)
    · exact norm_wNK_chan_le hL hj hqp
  · rw [norm_zero]

lemma ycK_gap {q p : Cfg eta N} (h : ycK sys L p₀ N q p ≠ 0) : gapC sys L N q p := by
  by_contra hg
  apply h
  unfold ycK FSKernel.divK
  dsimp only
  unfold gcmGap
  rw [if_neg hg]
  split_ifs <;> simp

open Classical in
/-- **The com dressing with its gap**: `|y_j(q,p)| ≤ c_j g² |Π_j(p)|/(M̄_j |θ| |E(q) - E(p)|)`. -/
lemma norm_yj_le_gap (hL : 0 < L) {j : Ch eta} {q p : Cfg eta N}
    (hj : OnCh j (cidx N q) (cidx N p)) (hne : q ≠ p) :
    ‖yj sys L p₀ N j q p‖ ≤ chC sys L j * gF L ^ 2 * piC j (cidx N p) / Mtot sys j *
      (1 / (FSChannel.rho (chT N j q p) * |Asym sys L N q - Asym sys L N p|)) := by
  unfold yj ycKc
  rw [if_pos hj]
  exact norm_ycK_chan_le hL hj hne

open Classical in
/-- **The com dressing on its floor**: `|y_j(q,p)| ≤ (C_j/2) |Π_j(p)|/|θ|²`. -/
lemma norm_yj_le_floor (hL : 0 < L) (j : Ch eta) (q p : Cfg eta N) :
    ‖yj sys L p₀ N j q p‖ ≤ if OnCh j (cidx N q) (cidx N p) then
      CYc sys L j / 2 * piC j (cidx N p) / FSLattice.lsq (chT N j q p) else 0 := by
  have hcC := chC_nonneg sys hL j
  have hpi := piC_nonneg j (cidx N p)
  have hM := Mtot_pos sys j
  have hμ := muCh_pos sys j
  have hg := gF_pos hL
  have hCY : 0 ≤ CYc sys L j / 2 * piC j (cidx N p) := by
    have := CYc_nonneg (sys := sys) hL j; positivity
  split_ifs with hj
  · by_cases h0 : yj sys L p₀ N j q p = 0
    · rw [h0, norm_zero]; exact div_nonneg hCY (FSLattice.lsq_nonneg _)
    have h0' : ycK sys L p₀ N q p ≠ 0 := by
      intro h; apply h0; unfold yj ycKc; rw [if_pos hj, h]
    have hgap := ycK_gap h0'
    have hne := hgap.1
    have hfl := gapC_onCh hgap hj
    have h1 := norm_yj_le_gap (sys := sys) (p₀ := p₀) hL hj hne
    have hθ : 1 ≤ FSLattice.lsq (chT N j q p) := one_le_lsq_chT hj hne
    have hρ : 0 < FSChannel.rho (chT N j q p) := by
      unfold FSChannel.rho; exact Real.sqrt_pos.mpr (by linarith)
    have hρsq := FSChannel.rho_sq (chT N j q p)
    have hd : 0 < |Asym sys L N q - Asym sys L N p| := lt_of_lt_of_le (by positivity) hfl
    refine h1.trans ?_
    have h2 : 1 / (FSChannel.rho (chT N j q p) * |Asym sys L N q - Asym sys L N p|) ≤
        1 / (FSChannel.rho (chT N j q p) * (gF L ^ 2 * FSChannel.rho (chT N j q p) / muCh sys j)) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hfl hρ.le)
    calc chC sys L j * gF L ^ 2 * piC j (cidx N p) / Mtot sys j *
          (1 / (FSChannel.rho (chT N j q p) * |Asym sys L N q - Asym sys L N p|)) ≤
        chC sys L j * gF L ^ 2 * piC j (cidx N p) / Mtot sys j *
          (1 / (FSChannel.rho (chT N j q p) * (gF L ^ 2 * FSChannel.rho (chT N j q p) / muCh sys j))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = CYc sys L j / 2 * piC j (cidx N p) / FSLattice.lsq (chT N j q p) := by
          unfold CYc
          rw [← hρsq]
          field_simp
  · have : yj sys L p₀ N j q p = 0 := by unfold yj ycKc; rw [if_neg hj]
    rw [this, norm_zero]

/-- **The well-gapped Y-hop from cold off the cube**:
`|y_j(d,b)| ≤ 32 m c_j (|Π_j(b)|/n)/(M̄ |θ|²)` for `b` cold and `d ∉ P`. -/
lemma norm_yj_cold_notP_le (hL : 0 < L) (hn : 1 ≤ n) {j : Ch eta} {d b : Cfg eta N}
    (hb : InC (n : ℝ) (cst sys) (cidx N b)) (hd : ¬ InP (n : ℝ) (cidx N d))
    (hj : OnCh j (cidx N d) (cidx N b)) :
    ‖yj sys L p₀ N j d b‖ ≤ 32 * mmax sys * chC sys L j / Mtot sys j *
      (piC j (cidx N b) / n) / FSLattice.lsq (chT N j d b) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hne : d ≠ b := by
    intro h; rw [h] at hd
    exact hd (inP_of_inC hb)
  have h1 := norm_yj_le_gap (sys := sys) (p₀ := p₀) hL hj hne
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hcC := chC_nonneg sys hL j
  have hpi := piC_nonneg j (cidx N b)
  have hM := Mtot_pos sys j
  set θ := chT N j d b
  have hl := long_of_cold_notP hb hd hj
  have hθ : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) hl
  have hρθ : (n : ℝ) / 2 ≤ FSChannel.rho θ := by
    unfold FSChannel.rho; exact Real.le_sqrt_of_sq_le hl
  have hρsq := FSChannel.rho_sq θ
  -- the energy of `d` against the transfer, through the lead coordinate
  have hlead := coord_lead j
  have hE1 := Asym_ge_regSum (sys := sys) hL hlead.card d
  have he := hlead.onCh hj
  rw [one_smul] at he
  have hb0 := rho_coord_cold hlead.card hb
  have hcs := cst_le32 sys
  have hz : (7 / 8) * FSChannel.rho θ ≤ FSChannel.rho (regSum {lead j} (cidx N d)) := by
    have h2 := FSChannel.rho_le_add_rho_sub θ (regSum {lead j} (cidx N d))
    have e : θ - regSum {lead j} (cidx N d) = -regSum {lead j} (cidx N b) := by
      rw [he]; show cidx N d (lead j) - cidx N b (lead j) - _ = _; abel
    rw [e, rho_neg'] at h2
    nlinarith
  have hz2 : (49 / 64) * FSLattice.lsq θ ≤ FSLattice.lsq (regSum {lead j} (cidx N d)) := by
    rw [← FSChannel.rho_sq, ← FSChannel.rho_sq]
    have := FSChannel.rho_nonneg θ
    nlinarith
  have hAd : gF L ^ 2 / (8 * mmax sys) * FSLattice.lsq θ ≤ Asym sys L N d := by
    have h3 : gF L ^ 2 / (8 * mmax sys) * FSLattice.lsq θ ≤
        gF L ^ 2 / (4 * mmax sys) * ((49 / 64) * FSLattice.lsq θ) := by
      calc gF L ^ 2 / (8 * mmax sys) * FSLattice.lsq θ =
          gF L ^ 2 / (4 * mmax sys) * (FSLattice.lsq θ / 2) := by field_simp; ring
        _ ≤ gF L ^ 2 / (4 * mmax sys) * ((49 / 64) * FSLattice.lsq θ) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 := mul_le_mul_of_nonneg_left hz2 (by positivity : (0 : ℝ) ≤ gF L ^ 2 / (4 * mmax sys))
    linarith
  have hgap := gap_notP_cold (sys := sys) hL hd hb
  have hd' : gF L ^ 2 / (16 * mmax sys) * FSLattice.lsq θ ≤ |Asym sys L N d - Asym sys L N b| := by
    rw [abs_of_nonneg (by have := FSGalerkin.Asym_nonneg sys L N d; linarith)]
    have : gF L ^ 2 / (16 * mmax sys) * FSLattice.lsq θ =
        gF L ^ 2 / (8 * mmax sys) * FSLattice.lsq θ / 2 := by field_simp; ring
    linarith
  refine h1.trans ?_
  have h5 : 1 / (FSChannel.rho θ * |Asym sys L N d - Asym sys L N b|) ≤
      1 / ((n : ℝ) / 2 * (gF L ^ 2 / (16 * mmax sys) * FSLattice.lsq θ)) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul hρθ hd' (by positivity) (FSChannel.rho_nonneg _))
  calc chC sys L j * gF L ^ 2 * piC j (cidx N b) / Mtot sys j *
        (1 / (FSChannel.rho θ * |Asym sys L N d - Asym sys L N b|)) ≤
      chC sys L j * gF L ^ 2 * piC j (cidx N b) / Mtot sys j *
        (1 / ((n : ℝ) / 2 * (gF L ^ 2 / (16 * mmax sys) * FSLattice.lsq θ))) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = 32 * mmax sys * chC sys L j / Mtot sys j * (piC j (cidx N b) / n) / FSLattice.lsq θ := by
        field_simp; ring

omit [Fintype ν] in
/-- The pair momentum of a configuration whose registers are `≤ r`: `|Π_j| ≤ 2 r`. -/
lemma piC_le_of_regs (j : Ch eta) {k : Cf eta} {r : ℝ} (hr : 0 ≤ r)
    (hk : ∀ c, FSChannel.rho (k c) ≤ r) : piC j k ≤ 2 * r := by
  cases j with
  | inl a => simp only [piC]; positivity
  | inr pr =>
    simp only [piC]
    have := FSChannel.rho_add_le (k pr.1.1) (k pr.1.2)
    linarith [hk pr.1.1, hk pr.1.2]

/-- **The well-gapped Y-hop from the short ball off the cube**:
`ω_F(f) |y_j(f,d)| ≤ 2 c_j g² (32 m/g²)²/(M̄ max(n², |ζ(f)|²)²)` for `f ∉ P`, `d` in the short ball. -/
lemma farW_yj_ball_le (hL : 0 < L) (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} (hA : A.card ≤ 2)
    {f d : Cfg eta N} (hf : ¬ InP (n : ℝ) (cidx N f)) (hd : SB sys N n d)
    (hj : OnCh j (cidx N f) (cidx N d)) :
    farW sys L N n f * ‖yj sys L p₀ N j f d‖ ≤
      2 * chC sys L j * gF L ^ 2 * (32 * mmax sys / gF L ^ 2) ^ 2 / Mtot sys j /
        max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hcC := chC_nonneg sys hL j
  have hM := Mtot_pos sys j
  have hcs := cst_le32 sys
  have hc := cst_pos sys
  have hfQ : ¬ InQ (n : ℝ) (cidx N f) := fun h => hf (inP_of_inQ' h)
  have hne : f ≠ d := by
    intro h; rw [h] at hf; exact hf (inP_of_SB hd)
  have h1 := norm_yj_le_gap (sys := sys) (p₀ := p₀) hL hj hne
  have hpi : piC j (cidx N d) ≤ (n : ℝ) / 8 := by
    have := piC_le_of_regs j (by positivity) hd
    nlinarith
  have hpi0 := piC_nonneg j (cidx N d)
  have hl := long_of_ball hd hfQ hj
  have hρθ : (n : ℝ) / 8 ≤ FSChannel.rho (chT N j f d) := by
    unfold FSChannel.rho; exact Real.le_sqrt_of_sq_le hl
  have hgap := gap_notP_short (sys := sys) hL hf hd
  have hfar := Asym_ge_far (sys := sys) hL hfQ
  have hApos : 0 < Asym sys L N f := lt_of_lt_of_le (by positivity) hfar
  have hd' : Asym sys L N f / 2 ≤ |Asym sys L N f - Asym sys L N d| :=
    hgap.trans (le_abs_self _)
  have hw : farW sys L N n f = 1 / Asym sys L N f := by unfold farW; rw [if_neg hfQ]
  have hy : ‖yj sys L p₀ N j f d‖ ≤ 2 * chC sys L j * gF L ^ 2 / Mtot sys j * (1 / Asym sys L N f) := by
    refine h1.trans ?_
    have h2 : 1 / (FSChannel.rho (chT N j f d) * |Asym sys L N f - Asym sys L N d|) ≤
        1 / ((n : ℝ) / 8 * (Asym sys L N f / 2)) :=
      one_div_le_one_div_of_le (mul_pos (by positivity) (by linarith)) (mul_le_mul hρθ hd'
        (by linarith) (FSChannel.rho_nonneg _))
    calc chC sys L j * gF L ^ 2 * piC j (cidx N d) / Mtot sys j *
          (1 / (FSChannel.rho (chT N j f d) * |Asym sys L N f - Asym sys L N d|)) ≤
        chC sys L j * gF L ^ 2 * ((n : ℝ) / 8) / Mtot sys j *
          (1 / ((n : ℝ) / 8 * (Asym sys L N f / 2))) := by
          apply mul_le_mul _ h2
            (div_nonneg zero_le_one (mul_nonneg (FSChannel.rho_nonneg _) (abs_nonneg _)))
            (div_nonneg (mul_nonneg (mul_nonneg hcC (sq_nonneg _)) (by positivity)) hM.le)
          apply div_le_div_of_nonneg_right _ hM.le
          exact mul_le_mul_of_nonneg_left hpi (mul_nonneg hcC (sq_nonneg _))
      _ = 2 * chC sys L j * gF L ^ 2 / Mtot sys j * (1 / Asym sys L N f) := by
          field_simp
  have hmax := farW_le_max (sys := sys) hL hn hA f
  rw [hw] at hmax
  have hM0 : 0 < max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  rw [hw]
  calc 1 / Asym sys L N f * ‖yj sys L p₀ N j f d‖ ≤
      1 / Asym sys L N f * (2 * chC sys L j * gF L ^ 2 / Mtot sys j * (1 / Asym sys L N f)) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
    _ = 2 * chC sys L j * gF L ^ 2 / Mtot sys j * (1 / Asym sys L N f) ^ 2 := by ring
    _ ≤ 2 * chC sys L j * gF L ^ 2 / Mtot sys j *
          (32 * mmax sys / gF L ^ 2 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f)))) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmax 2) (by positivity)
    _ = _ := by field_simp

end ChanKernels

end FSFlux
