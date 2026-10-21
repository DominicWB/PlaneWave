import PlaneWave.FluxBox.ConservedWeightSchur

/-!
# Flux route, stage 3, part 25: geometry and energies of the far–cold paths

With `c_* = cst ≤ 1/32` and the hop threshold `τ₀ = c_* n`:

* cold registers and coordinates: `|k_c| ≤ c_* n`, `|ζ| ≤ 2 c_* n` (`|A| ≤ 2`);
* a register changes along a hop by at most the transfer (`rho_reg_hop_le`);
* from cold to outside the cube the hop is long: `|θ|² ≥ (n/2)²` (`long_of_cold_notP`);
* after a short hop (`|θ₁| < τ₀`) from cold, every register is `≤ 2 c_* n` (`short_ball`), and a
  second hop to the far region is long, `|θ₂| ≥ n/8` (`long_of_short`);
* energies: `A ≥ g²|ζ|²/(4 m_max)`, `A ≥ g²|Π_j|²/(4 m_max)`; off the cube `A ≥ g²n²/(2 m_max)`;
  on the short ball `A ≤ g²n²/(512 m_max)`; hence the gaps `A(f) - A(d) ≥ A(f)/2` (`f ∉ P`, `d` in
  the short ball) and `A(d) - A(b) ≥ A(d)/2` (`d ∉ P`, `b` cold).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Geometry

variable {sys : CoulombSystem eta ν} {N : ℕ} {n : ℕ}

omit [Fintype ν] in
lemma cst_mul_nonneg : 0 ≤ cst sys * (n : ℝ) := by
  have := cst_pos sys; positivity

omit [Fintype ν] in
/-- A cold register: `|k_c| ≤ c_* n`. -/
lemma rho_le_of_inC {k : Cf eta} (h : InC (n : ℝ) (cst sys) k) (c : Fin eta) :
    FSChannel.rho (k c) ≤ cst sys * n := by
  unfold FSChannel.rho
  rw [Real.sqrt_le_left cst_mul_nonneg]
  exact h c

omit [Fintype ν] in
/-- A register changes along a hop by at most the transfer. -/
lemma rho_reg_hop_le {j : Ch eta} {q p : Cf eta} (h : OnCh j q p) (c : Fin eta) :
    FSChannel.rho (q c - p c) ≤ FSChannel.rho (q (lead j) - p (lead j)) := by
  have e : q = p + tr j (q (lead j) - p (lead j)) := h
  generalize q (lead j) - p (lead j) = θ at e ⊢
  have h1 : q c - p c = tr j θ c := by rw [e, Pi.add_apply]; abel
  rw [h1]
  by_cases hc : c ∈ moved j
  · rcases tr_apply_moved j θ hc with h2 | h2
    · rw [h2]
    · rw [h2, rho_neg']
  · rw [tr_apply_not_moved j θ hc]
    have : FSChannel.rho (0 : Lattice3) = 0 := by simp [FSChannel.rho, FSLattice.lsq]
    rw [this]
    exact FSChannel.rho_nonneg _

omit [Fintype ν] in
/-- A register outside the cube: `|k_c| > n`. -/
lemma exists_rho_gt_of_notP {k : Cf eta} (h : ¬ InP (n : ℝ) k) :
    ∃ c, (n : ℝ) < FSChannel.rho (k c) := by
  simp only [InP, not_forall, not_le] at h
  obtain ⟨c, i, hi⟩ := h
  refine ⟨c, ?_⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (n : ℝ) ^ 2 < ((k c i : ℤ) : ℝ) ^ 2 := by
    have := abs_nonneg ((k c i : ℤ) : ℝ)
    have h2 : (n : ℝ) ^ 2 < |((k c i : ℤ) : ℝ)| ^ 2 := pow_lt_pow_left₀ hi hn two_ne_zero
    rwa [sq_abs] at h2
  have h3 : ((k c i : ℤ) : ℝ) ^ 2 ≤ FSLattice.lsq (k c) := by
    unfold FSLattice.lsq
    fin_cases i <;> simp <;> nlinarith [sq_nonneg ((k c 0 : ℤ) : ℝ), sq_nonneg ((k c 1 : ℤ) : ℝ),
      sq_nonneg ((k c 2 : ℤ) : ℝ)]
  unfold FSChannel.rho
  rw [Real.lt_sqrt hn]
  linarith

omit [Fintype ν] in
/-- A register outside the bulk ball: `|k_c| > n/4`. -/
lemma exists_rho_gt_of_notQ {k : Cf eta} (h : ¬ InQ (n : ℝ) k) :
    ∃ c, (n : ℝ) / 4 < FSChannel.rho (k c) := by
  simp only [InQ, not_forall, not_le] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have hn : (0 : ℝ) ≤ n / 4 := by positivity
  unfold FSChannel.rho
  rw [Real.lt_sqrt hn]
  exact hc

omit [Fintype ν] in
/-- **From cold to outside the cube the hop is long**: `|θ|² ≥ (n/2)²`. -/
lemma long_of_cold_notP {j : Ch eta} {d b : Cfg eta N} (hb : InC (n : ℝ) (cst sys) (cidx N b))
    (hd : ¬ InP (n : ℝ) (cidx N d)) (h : OnCh j (cidx N d) (cidx N b)) :
    ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq (chT N j d b) := by
  obtain ⟨c, hc⟩ := exists_rho_gt_of_notP hd
  have h1 := rho_le_of_inC hb c
  have h2 := FSChannel.rho_le_add_rho_sub (cidx N d c) (cidx N b c)
  have h3 := rho_reg_hop_le h c
  have hcs := cst_le32 sys
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : (n : ℝ) / 2 ≤ FSChannel.rho (chT N j d b) := by
    show (n : ℝ) / 2 ≤ FSChannel.rho (cidx N d (lead j) - cidx N b (lead j))
    nlinarith
  rw [← FSChannel.rho_sq]
  exact pow_le_pow_left₀ (by positivity) h4 2

omit [Fintype ν] in
/-- **The short ball**: after a hop with `|θ₁| < c_* n` from cold, every register is `≤ 2 c_* n`. -/
lemma short_ball {j : Ch eta} {d b : Cfg eta N} (hb : InC (n : ℝ) (cst sys) (cidx N b))
    (h : OnCh j (cidx N d) (cidx N b)) (hs : FSLattice.lsq (chT N j d b) < (cst sys * n) ^ 2)
    (c : Fin eta) : FSChannel.rho (cidx N d c) ≤ 2 * (cst sys * n) := by
  have h1 := rho_le_of_inC hb c
  have h2 := FSChannel.rho_le_add_rho_sub (cidx N d c) (cidx N b c)
  have h3 := rho_reg_hop_le h c
  have h4 : FSChannel.rho (chT N j d b) ≤ cst sys * n := by
    unfold FSChannel.rho
    rw [Real.sqrt_le_left cst_mul_nonneg]
    exact hs.le
  have h5 : FSChannel.rho (cidx N d (lead j) - cidx N b (lead j)) ≤ cst sys * n := h4
  linarith

omit [Fintype ν] in
/-- **The second hop of a short-first path from cold to far is long**: `|θ₂|² ≥ (n/8)²`. -/
lemma long_of_short {j₁ j₂ : Ch eta} {f d b : Cfg eta N} (hb : InC (n : ℝ) (cst sys) (cidx N b))
    (hf : ¬ InQ (n : ℝ) (cidx N f)) (h₁ : OnCh j₁ (cidx N d) (cidx N b))
    (h₂ : OnCh j₂ (cidx N f) (cidx N d)) (hs : FSLattice.lsq (chT N j₁ d b) < (cst sys * n) ^ 2) :
    ((n : ℝ) / 8) ^ 2 ≤ FSLattice.lsq (chT N j₂ f d) := by
  obtain ⟨c, hc⟩ := exists_rho_gt_of_notQ hf
  have h1 := short_ball hb h₁ hs c
  have h2 := FSChannel.rho_le_add_rho_sub (cidx N f c) (cidx N d c)
  have h3 := rho_reg_hop_le h₂ c
  have hcs := cst_le32 sys
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : (n : ℝ) / 8 ≤ FSChannel.rho (chT N j₂ f d) := by
    show (n : ℝ) / 8 ≤ FSChannel.rho (cidx N f (lead j₂) - cidx N d (lead j₂))
    nlinarith
  rw [← FSChannel.rho_sq]
  exact pow_le_pow_left₀ (by positivity) h4 2

omit [Fintype ν] in
/-- A coordinate of a configuration whose registers are `≤ r`: `|ζ| ≤ 2 r` (`|A| ≤ 2`). -/
lemma rho_regSum_le {A : Finset (Fin eta)} (hA : A.card ≤ 2) {k : Cf eta} {r : ℝ} (hr : 0 ≤ r)
    (hk : ∀ c, FSChannel.rho (k c) ≤ r) : FSChannel.rho (regSum A k) ≤ 2 * r := by
  classical
  have h1 : ∀ B : Finset (Fin eta), FSChannel.rho (regSum B k) ≤ B.card * r := by
    intro B
    induction B using Finset.induction_on with
    | empty =>
      simp only [regSum, Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul]
      simp [FSChannel.rho, FSLattice.lsq]
    | insert a B ha ih =>
      simp only [regSum, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have := FSChannel.rho_add_le (k a) (∑ c ∈ B, k c)
      have h2 : FSChannel.rho (∑ c ∈ B, k c) ≤ B.card * r := ih
      push_cast
      linarith [hk a]
  calc FSChannel.rho (regSum A k) ≤ A.card * r := h1 A
    _ ≤ 2 * r := mul_le_mul_of_nonneg_right (by exact_mod_cast hA) hr

end Geometry

/-! ## Energies -/

section Energies

variable {sys : CoulombSystem eta ν} {L : ℝ} {N : ℕ} {n : ℕ}

omit [Fintype ν] in
/-- `A ≥ g² |ζ|²/(4 m_max)` for a coordinate of at most two registers. -/
lemma Asym_ge_regSum (hL : 0 < L) {A : Finset (Fin eta)} (hA : A.card ≤ 2) (q : Cfg eta N) :
    gF L ^ 2 / (4 * mmax sys) * FSLattice.lsq (regSum A (cidx N q)) ≤ Asym sys L N q := by
  have h1 := lsq_regSum_le_Xall A hA q
  have h2 := Xall_le_Asym (sys := sys) hL q
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hA0 := FSGalerkin.Asym_nonneg sys L N q
  have h3 : gF L ^ 2 / (4 * mmax sys) * FSLattice.lsq (regSum A (cidx N q)) ≤
      gF L ^ 2 / (2 * mmax sys) * Xall q := by
    have : gF L ^ 2 / (4 * mmax sys) * FSLattice.lsq (regSum A (cidx N q)) ≤
        gF L ^ 2 / (4 * mmax sys) * (2 * Xall q) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have e : gF L ^ 2 / (4 * mmax sys) * (2 * Xall q) = gF L ^ 2 / (2 * mmax sys) * Xall q := by
      field_simp; ring
    linarith
  have h4 : gF L ^ 2 / (2 * mmax sys) * Xall q ≤ Asym sys L N q := by
    have : gF L ^ 2 / (2 * mmax sys) * Xall q ≤
        gF L ^ 2 / (2 * mmax sys) * (2 * mmax sys / gF L ^ 2 * Asym sys L N q) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e : gF L ^ 2 / (2 * mmax sys) * (2 * mmax sys / gF L ^ 2 * Asym sys L N q) =
        Asym sys L N q := by
      field_simp
    linarith
  linarith

omit [Fintype ν] in
/-- `A ≥ g² |Π_j|²/(4 m_max)`. -/
lemma Asym_ge_piC (hL : 0 < L) (j : Ch eta) (q : Cfg eta N) :
    gF L ^ 2 / (4 * mmax sys) * piC j (cidx N q) ^ 2 ≤ Asym sys L N q := by
  have h1 := piC_le_sqrt j (cidx N q)
  have h2 := movS_le_Xall j q
  have h0 := piC_nonneg j (cidx N q)
  have h3 := pow_le_pow_left₀ h0 h1 2
  rw [Real.sq_sqrt (by have := movS_nonneg j (cidx N q); unfold movS at this; positivity)] at h3
  have h4 := Xall_le_Asym (sys := sys) hL q
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have h5 : piC j (cidx N q) ^ 2 ≤ 2 * Xall q := by unfold movS at h2; linarith
  have h6 : gF L ^ 2 / (4 * mmax sys) * piC j (cidx N q) ^ 2 ≤
      gF L ^ 2 / (4 * mmax sys) * (2 * (2 * mmax sys / gF L ^ 2 * Asym sys L N q)) :=
    mul_le_mul_of_nonneg_left (h5.trans (by linarith)) (by positivity)
  have e : gF L ^ 2 / (4 * mmax sys) * (2 * (2 * mmax sys / gF L ^ 2 * Asym sys L N q)) =
      Asym sys L N q := by
    field_simp; ring
  linarith

omit [Fintype ν] in
/-- Off the cube: `A ≥ g² n²/(2 m_max)`. -/
lemma Asym_ge_notP (hL : 0 < L) {q : Cfg eta N} (hq : ¬ InP (n : ℝ) (cidx N q)) :
    gF L ^ 2 * (n : ℝ) ^ 2 / (2 * mmax sys) ≤ Asym sys L N q := by
  obtain ⟨c, hc⟩ := exists_rho_gt_of_notP hq
  rw [Asym_eq_sum]
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hmc := mass_le_mmax sys c
  have hmc0 := sys.mass_pos c
  have h1 := Finset.single_le_sum (f := fun c => gF L ^ 2 / (2 * sys.mass c) * nsq (cidx N q c))
    (fun c _ => by have := sys.mass_pos c; have := nsq_nonneg (cidx N q c); positivity)
    (Finset.mem_univ c)
  refine le_trans ?_ h1
  show gF L ^ 2 * (n : ℝ) ^ 2 / (2 * mmax sys) ≤ gF L ^ 2 / (2 * sys.mass c) * nsq (cidx N q c)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : (n : ℝ) ^ 2 ≤ nsq (cidx N q c) := by
    have := pow_le_pow_left₀ hn hc.le 2
    rw [FSChannel.rho_sq] at this
    exact this
  have h3 : gF L ^ 2 * (n : ℝ) ^ 2 / (2 * mmax sys) = gF L ^ 2 / (2 * mmax sys) * (n : ℝ) ^ 2 := by
    ring
  rw [h3]
  apply mul_le_mul _ h2 (by positivity) (by positivity)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

omit [Fintype ν] in
/-- On the short ball: `A ≤ g² n²/(512 m_max)`. -/
lemma Asym_le_short (q : Cfg eta N)
    (hq : ∀ c, FSChannel.rho (cidx N q c) ≤ 2 * (cst sys * n)) :
    Asym sys L N q ≤ gF L ^ 2 * (n : ℝ) ^ 2 / (512 * mmax sys) := by
  rw [Asym_eq_sum]
  have hm := one_le_mmax sys
  have hcs := cst_sq sys
  have hterm : ∀ c ∈ Finset.univ, gF L ^ 2 / (2 * sys.mass c) * nsq (cidx N q c) ≤
      gF L ^ 2 / 2 * (2 * (cst sys * n)) ^ 2 := by
    intro c _
    have h1 : nsq (cidx N q c) ≤ (2 * (cst sys * n)) ^ 2 := by
      have := pow_le_pow_left₀ (FSChannel.rho_nonneg _) (hq c) 2
      rw [FSChannel.rho_sq] at this
      exact this
    have h2 := sys.one_le_mass c
    have h0 := nsq_nonneg (cidx N q c)
    calc gF L ^ 2 / (2 * sys.mass c) * nsq (cidx N q c) ≤ gF L ^ 2 / 2 * nsq (cidx N q c) := by
          apply mul_le_mul_of_nonneg_right _ h0
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm0 : 0 < mmax sys := by linarith
  have he : (0 : ℝ) ≤ eta := Nat.cast_nonneg eta
  have h1 : (eta : ℝ) * (gF L ^ 2 / 2 * (2 * (cst sys * n)) ^ 2) =
      gF L ^ 2 * (n : ℝ) ^ 2 / (512 * mmax sys) * (eta / (eta + 1)) := by
    rw [mul_pow, mul_pow, hcs]
    field_simp
    ring
  rw [h1]
  have h2 : (eta : ℝ) / (eta + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have h3 : 0 ≤ gF L ^ 2 * (n : ℝ) ^ 2 / (512 * mmax sys) := by positivity
  nlinarith

omit [Fintype ν] in
/-- **The gap of a hop from the short ball off the cube**: `A(f) - A(d) ≥ A(f)/2`. -/
lemma gap_notP_short (hL : 0 < L) {f d : Cfg eta N} (hf : ¬ InP (n : ℝ) (cidx N f))
    (hd : ∀ c, FSChannel.rho (cidx N d c) ≤ 2 * (cst sys * n)) :
    Asym sys L N f / 2 ≤ Asym sys L N f - Asym sys L N d := by
  have h1 := Asym_ge_notP (sys := sys) hL hf
  have h2 := Asym_le_short (sys := sys) (L := L) d hd
  have hm := one_le_mmax sys
  have hg := gF_pos hL
  have h3 : gF L ^ 2 * (n : ℝ) ^ 2 / (512 * mmax sys) ≤
      gF L ^ 2 * (n : ℝ) ^ 2 / (2 * mmax sys) / 2 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  linarith

omit [Fintype ν] in
/-- **The gap of a hop from cold off the cube**: `A(d) - A(b) ≥ A(d)/2`. -/
lemma gap_notP_cold (hL : 0 < L) {d b : Cfg eta N} (hd : ¬ InP (n : ℝ) (cidx N d))
    (hb : InC (n : ℝ) (cst sys) (cidx N b)) :
    Asym sys L N d / 2 ≤ Asym sys L N d - Asym sys L N b := by
  have h1 := Asym_ge_notP (sys := sys) hL hd
  have h2 := Asym_le_cold (sys := sys) hL hb
  have hm := one_le_mmax sys
  have hg := gF_pos hL
  have h3 : gF L ^ 2 * (n : ℝ) ^ 2 / (128 * mmax sys) ≤
      gF L ^ 2 * (n : ℝ) ^ 2 / (2 * mmax sys) / 2 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  linarith

omit [Fintype ν] in
/-- **The far energy dominates a coordinate**: `A(f) ≥ g² max(n², |ζ|²)/(32 m_max)` on `F`. -/
lemma Asym_ge_far_max (hL : 0 < L) {A : Finset (Fin eta)} (hA : A.card ≤ 2) {f : Cfg eta N}
    (hf : ¬ InQ (n : ℝ) (cidx N f)) :
    gF L ^ 2 / (32 * mmax sys) * max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) ≤
      Asym sys L N f := by
  have h1 := Asym_ge_far (sys := sys) hL hf
  have h2 := Asym_ge_regSum (sys := sys) hL hA f
  have hm := one_le_mmax sys
  have hg := gF_pos hL
  rcases le_total ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) with h | h
  · rw [max_eq_right h]
    have : gF L ^ 2 / (32 * mmax sys) * FSLattice.lsq (regSum A (cidx N f)) ≤
        gF L ^ 2 / (4 * mmax sys) * FSLattice.lsq (regSum A (cidx N f)) := by
      apply mul_le_mul_of_nonneg_right _ (FSLattice.lsq_nonneg _)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    linarith
  · rw [max_eq_left h]
    have e : gF L ^ 2 / (32 * mmax sys) * (n : ℝ) ^ 2 = gF L ^ 2 * (n : ℝ) ^ 2 / (32 * mmax sys) := by
      ring
    linarith

end Energies

end FSFlux
