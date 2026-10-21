import PlaneWave.FluxBox.ComDressing

/-!
# Flux route, stage 2, part 12: the resonant com flux at the target rate

The resonant com elements (`¬ gapC`: `|E(q) - E(p)| < g²|θ|/μ_j`, i.e. `|F_c(θ)| < 2|θ|`) are
thin and pinned:

* `FSLattice.sum_inv_rho_res_le`: transfers with `|F_c(θ)| < 2|θ|`, pinned (`|θ|² ≥ 64` forces
  `(9/64)|θ|² < X`), have `Σ 1/|θ| ≤ 55000 (7 + (16/3) √X)` (dyadic shells, `slab_count`);
* `row_gcmRes_le`: the rows of `G^{cm,res}` on a channel are `≤ C_j (1 + Σ_c |k_c|²)`;
* `norm_form_gcmRes_le`: `|⟨a, G^{cm,res} b⟩| ≤ C_res (Σ (1+X)|a|²)^{1/2} (Σ (1+X)|b|²)^{1/2}`,
  `X = Σ_c |k_c|²` (Schur, row = column by Hermiticity);
* `gcmRes_cross`: a resonant hop from the cube to its complement starts from a configuration
  with a register beyond `3n/64` (crossing within `n/8`, or pinning);
* **`norm_Xres_le`** (the com part of `cor:reslayer`): for a good box state,
  `|⟨u, X^{cm,res} u⟩| ≤ C M² (g n)^{-3}`, `X^{cm,res} = G^{cm,res} - P G^{cm,res} P`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSLattice

open FSChannel Finset

/-- `Σ_{i ≤ I, 2^i < Y} 2^i ≤ 2Y`. -/
lemma sum_pow_two_lt_le (I : ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    ∑ i ∈ range (I + 1), (if (2 : ℝ) ^ i < Y then (2 : ℝ) ^ i else 0) ≤ 2 * Y := by
  have key : ∀ I : ℕ, ∑ i ∈ range (I + 1), (if (2 : ℝ) ^ i < Y then (2 : ℝ) ^ i else 0) ≤ 2 * Y ∧
      ∑ i ∈ range (I + 1), (if (2 : ℝ) ^ i < Y then (2 : ℝ) ^ i else 0) ≤ 2 ^ (I + 1) - 1 := by
    intro I
    induction I with
    | zero =>
      simp only [zero_add, range_one, sum_singleton, pow_zero]
      split_ifs with h
      · constructor <;> linarith
      · constructor <;> linarith
    | succ I ih =>
      rw [sum_range_succ]
      obtain ⟨ih1, ih2⟩ := ih
      split_ifs with h
      · constructor
        · have : (2 : ℝ) ^ (I + 1) = 2 * 2 ^ I := by ring
          have h2 : (2 : ℝ) ^ (I + 1 + 1) = 2 * 2 ^ (I + 1) := by ring
          nlinarith
        · rw [show (2 : ℝ) ^ (I + 1 + 1) = 2 * 2 ^ (I + 1) by ring]; linarith
      · constructor
        · linarith
        · have : (0 : ℝ) ≤ 2 ^ (I + 1) := by positivity
          rw [show (2 : ℝ) ^ (I + 1 + 1) = 2 * 2 ^ (I + 1) by ring]; linarith
  exact (key I).1

/-- **The resonant slab sum**: for transfers with `|F_c(θ)| < 2|θ|`, pinned at `X`
(`64 ≤ |θ|² → (9/64)|θ|² < X`), `Σ 1/|θ| ≤ 55000 (7 + 2 (8/3) √X)`. -/
theorem sum_inv_rho_res_le (c : Fin 3 → ℝ) {X : ℝ} (hX : 0 ≤ X) (T : Finset L3)
    (hT : ∀ θ ∈ T, 1 ≤ lsq θ ∧ |slabF c θ| < 2 * rho θ ∧ (64 ≤ lsq θ → 9 / 64 * lsq θ < X)) :
    ∑ θ ∈ T, 1 / rho θ ≤ 55000 * (7 + 2 * (8 / 3 * Real.sqrt X)) := by
  classical
  set Y := 8 / 3 * Real.sqrt X with hYdef
  have hY : 0 ≤ Y := by positivity
  -- a shell range
  obtain ⟨I, hI⟩ : ∃ I : ℕ, ∀ θ ∈ T, lsq θ ≤ 4 ^ (I + 1) := by
    obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ θ ∈ T, lsq θ ≤ B :=
      ⟨∑ θ ∈ T, lsq θ, fun θ hθ => single_le_sum (fun θ _ => lsq_nonneg θ) hθ⟩
    obtain ⟨I, hI⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℝ) < 4)
    refine ⟨I, fun θ hθ => (hB θ hθ).trans ?_⟩
    have : (4 : ℝ) ^ I ≤ 4 ^ (I + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  set f : L3 → ℝ := fun θ => 1 / rho θ
  have hf0 : ∀ θ, 0 ≤ f θ := fun θ => by simp only [f]; have := rho_nonneg θ; positivity
  have hshell : ∀ θ ∈ T, f θ ≤ ∑ i ∈ range (I + 1),
      if (4 : ℝ) ^ i ≤ lsq θ ∧ lsq θ ≤ 4 ^ (i + 1) then f θ else 0 := by
    intro θ hθ
    obtain ⟨h1, -, -⟩ := hT θ hθ
    have hex : ∃ i : ℕ, lsq θ ≤ 4 ^ (i + 1) := ⟨I, hI θ hθ⟩
    set i := Nat.find hex
    have hiI : i ≤ I := Nat.find_min' hex (hI θ hθ)
    have hi2 : lsq θ ≤ 4 ^ (i + 1) := Nat.find_spec hex
    have hi1 : (4 : ℝ) ^ i ≤ lsq θ := by
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h0, pow_zero]; exact h1
      · have hmin := Nat.find_min hex (show i - 1 < i by omega)
        push Not at hmin
        rw [show i - 1 + 1 = i by omega] at hmin
        exact hmin.le
    calc f θ = (if (4 : ℝ) ^ i ≤ lsq θ ∧ lsq θ ≤ 4 ^ (i + 1) then f θ else 0) := by
          rw [if_pos ⟨hi1, hi2⟩]
      _ ≤ _ := by
          apply single_le_sum (f := fun i => if (4 : ℝ) ^ i ≤ lsq θ ∧ lsq θ ≤ 4 ^ (i + 1)
            then f θ else 0)
          · intro i _; split_ifs
            · exact hf0 θ
            · exact le_rfl
          · exact mem_range.mpr (by omega)
  have hsum := sum_le_sum hshell
  rw [sum_comm] at hsum
  have hpiece : ∀ i ∈ range (I + 1), ∑ θ ∈ T, (if (4 : ℝ) ^ i ≤ lsq θ ∧ lsq θ ≤ 4 ^ (i + 1)
      then f θ else 0) ≤ 55000 * ((if i ≤ 2 then (2 : ℝ) ^ i else 0) +
        (if (2 : ℝ) ^ i < Y then (2 : ℝ) ^ i else 0)) := by
    intro i _
    rw [← sum_filter]
    set S := T.filter fun θ => (4 : ℝ) ^ i ≤ lsq θ ∧ lsq θ ≤ 4 ^ (i + 1)
    have e4 : ((2 : ℝ) ^ i) ^ 2 = 4 ^ i := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hρS : ∀ θ ∈ S, (2 : ℝ) ^ i ≤ rho θ ∧ rho θ ≤ 2 ^ (i + 1) := by
      intro θ hθ
      obtain ⟨-, hs1, hs2⟩ := mem_filter.mp hθ
      constructor
      · unfold rho; apply Real.le_sqrt_of_sq_le; rw [e4]; exact hs1
      · unfold rho
        rw [show (2 : ℝ) ^ (i + 1) = Real.sqrt (((2 : ℝ) ^ (i + 1)) ^ 2) by
          rw [Real.sqrt_sq (by positivity)]]
        apply Real.sqrt_le_sqrt
        rw [← pow_mul, mul_comm, pow_mul]; norm_num; exact hs2
    -- the case of an empty shell
    by_cases hempty : 3 ≤ i ∧ Y ≤ 2 ^ i
    · have hS : S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro θ hθ
        obtain ⟨hθT, hs1, -⟩ := mem_filter.mp hθ
        obtain ⟨-, -, hpin⟩ := hT θ hθT
        have h64 : (64 : ℝ) ≤ 4 ^ i := by
          calc (64 : ℝ) = 4 ^ 3 := by norm_num
            _ ≤ 4 ^ i := pow_le_pow_right₀ (by norm_num) hempty.1
        have hp := hpin (h64.trans hs1)
        have hρ := (hρS θ hθ).1
        have hr : rho θ < Y := by
          have hl : lsq θ < 64 / 9 * X := by linarith
          have hsq : rho θ ^ 2 < Y ^ 2 := by
            rw [rho_sq, hYdef, mul_pow, Real.sq_sqrt hX]; linarith
          exact lt_of_pow_lt_pow_left₀ 2 hY hsq
        linarith [hempty.2]
      rw [hS, sum_empty]
      positivity
    have hρ1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have hcount := slab_count c hρ1 (by positivity : (0 : ℝ) ≤ 4 * 2 ^ i) S (by
      intro θ hθ
      obtain ⟨hθT, hs1, hs2⟩ := mem_filter.mp hθ
      obtain ⟨-, hres, -⟩ := hT θ hθT
      have hr := (hρS θ hθ).2
      refine ⟨by rw [e4]; exact hs1, by rw [e4, ← pow_succ']; linarith, ?_⟩
      have : (2 : ℝ) ^ (i + 1) = 2 * 2 ^ i := by ring
      linarith)
    have hc' : (S.card : ℝ) ≤ 55000 * 4 ^ i := by
      have e : 11000 * ((2 : ℝ) ^ i) ^ 2 * (1 + 4 * 2 ^ i / 2 ^ i) = 55000 * 4 ^ i := by
        rw [e4]; field_simp; ring
      rw [e] at hcount; exact hcount
    have hfS : ∀ θ ∈ S, f θ ≤ 1 / 2 ^ i := fun θ hθ =>
      one_div_le_one_div_of_le (by positivity) (hρS θ hθ).1
    have hb : ∑ θ ∈ S, f θ ≤ 55000 * 2 ^ i := by
      calc ∑ θ ∈ S, f θ ≤ ∑ _θ ∈ S, 1 / (2 : ℝ) ^ i := sum_le_sum hfS
        _ = S.card * (1 / 2 ^ i) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ 55000 * 4 ^ i * (1 / 2 ^ i) := by gcongr
        _ = 55000 * 2 ^ i := by
            rw [← e4]; field_simp
    push Not at hempty
    refine hb.trans ?_
    by_cases hi : i ≤ 2
    · rw [if_pos hi]
      have : (0 : ℝ) ≤ if (2 : ℝ) ^ i < Y then (2 : ℝ) ^ i else 0 := by split_ifs <;> positivity
      linarith
    · have hY' : (2 : ℝ) ^ i < Y := hempty (by omega)
      rw [if_neg hi, if_pos hY']
      linarith
  have h7 : ∑ i ∈ range (I + 1), (if i ≤ 2 then (2 : ℝ) ^ i else 0) ≤ 7 := by
    have : ∀ i ∈ range (I + 1), (if i ≤ 2 then (2 : ℝ) ^ i else 0) ≤
        (if i ∈ range 3 then (2 : ℝ) ^ i else 0) := by
      intro i _; split_ifs with h1 h2 <;> simp_all; omega
    refine (sum_le_sum this).trans ?_
    rw [← sum_filter]
    have hsub : (range (I + 1)).filter (fun i => i ∈ range 3) ⊆ range 3 := fun i hi =>
      (mem_filter.mp hi).2
    calc ∑ i ∈ (range (I + 1)).filter (fun i => i ∈ range 3), (2 : ℝ) ^ i
        ≤ ∑ i ∈ range 3, (2 : ℝ) ^ i :=
          sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ = 7 := by norm_num [sum_range_succ]
  have hgeo := sum_pow_two_lt_le I hY
  calc ∑ θ ∈ T, f θ ≤ _ := hsum
    _ ≤ ∑ i ∈ range (I + 1), 55000 * ((if i ≤ 2 then (2 : ℝ) ^ i else 0) +
          (if (2 : ℝ) ^ i < Y then (2 : ℝ) ^ i else 0)) := sum_le_sum hpiece
    _ = 55000 * (∑ i ∈ range (I + 1), (if i ≤ 2 then (2 : ℝ) ^ i else 0) +
          ∑ i ∈ range (I + 1), (if (2 : ℝ) ^ i < Y then (2 : ℝ) ^ i else 0)) := by
        rw [← mul_sum, sum_add_distrib]
    _ ≤ 55000 * (7 + 2 * Y) := by gcongr

end FSLattice

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The rows of the resonant com force -/

section ResRows

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

/-- The total register weight `X(p) = Σ_c |k_c|²`. -/
noncomputable def Xall (p : Cfg eta N) : ℝ := ∑ c, FSLattice.lsq (cidx N p c)

omit [Fintype ν] in
lemma Xall_nonneg (p : Cfg eta N) : 0 ≤ Xall p :=
  Finset.sum_nonneg fun _ _ => FSLattice.lsq_nonneg _

omit [Fintype ν] in
lemma nsq_le_Xall (p : Cfg eta N) (c : Fin eta) : nsq (cidx N p c) ≤ Xall p :=
  Finset.single_le_sum (f := fun c => FSLattice.lsq (cidx N p c))
    (fun _ _ => FSLattice.lsq_nonneg _) (Finset.mem_univ c)

omit [Fintype ν] in
/-- `|Π_j| ≤ √(2 Σ_{c moved} |k_c|²)`. -/
lemma piC_le_sqrt (j : Ch eta) (k : Cf eta) :
    piC j k ≤ Real.sqrt (2 * ∑ c ∈ moved j, nsq (k c)) := by
  cases j with
  | inl a => simp only [piC]; exact Real.sqrt_nonneg _
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    simp only [piC, moved]
    rw [Finset.sum_pair hne]
    have h1 := FSChannel.rho_add_le (k pr.1.1) (k pr.1.2)
    have ha := FSChannel.rho_sq (k pr.1.1)
    have hb := FSChannel.rho_sq (k pr.1.2)
    have ha0 := FSChannel.rho_nonneg (k pr.1.1)
    have hb0 := FSChannel.rho_nonneg (k pr.1.2)
    refine h1.trans (Real.le_sqrt_of_sq_le ?_)
    have e1 : nsq (k pr.1.1) = FSLattice.lsq (k pr.1.1) := rfl
    have e2 : nsq (k pr.1.2) = FSLattice.lsq (k pr.1.2) := rfl
    rw [e1, e2, ← ha, ← hb]
    nlinarith [sq_nonneg (FSChannel.rho (k pr.1.1) - FSChannel.rho (k pr.1.2))]

/-- The row constant of the resonant com force on channel `j`. -/
noncomputable def CRc (sys : CoulombSystem eta ν) (L : ℝ) (j : Ch eta) : ℝ :=
  chC sys L j * gF L ^ 2 / Mtot sys j * (55000 * 15)

lemma CRc_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ CRc sys L j := by
  unfold CRc
  have := chC_nonneg sys hL j; have := Mtot_pos sys j
  positivity

open Classical in
/-- **The rows of the resonant com force**: `Σ_q |G^{cm,res}(q, p)| 1{q on j from p} ≤
C_j (1 + X(p))`. -/
theorem row_gcmRes_le (hL : 0 < L) (j : Ch eta) (p : Cfg eta N) :
    ∑ q, (if OnCh j (cidx N q) (cidx N p) then ‖gcmRes sys L p₀ N q p‖ else 0) ≤
      CRc sys L j * (1 + Xall p) := by
  classical
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hM := Mtot_pos sys j
  have hcC := chC_nonneg sys hL j
  have hpi := piC_nonneg j (cidx N p)
  set T := Finset.univ.filter fun q : Cfg eta N =>
    OnCh j (cidx N q) (cidx N p) ∧ q ≠ p ∧ ¬ gapC sys L N q p
  have hzero : ∀ q, OnCh j (cidx N q) (cidx N p) → q ∉ T → gcmRes sys L p₀ N q p = 0 := by
    intro q hj hq
    have hT : ¬ (q ≠ p ∧ ¬ gapC sys L N q p) := by
      intro h; apply hq; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, h⟩
    unfold gcmRes
    by_cases hgq : gapC sys L N q p
    · rw [if_pos hgq]
    · rw [if_neg hgq]
      have hqp : q = p := by
        by_contra hne; exact hT ⟨hne, hgq⟩
      subst hqp
      exact gcmK_eq_zero (wNK_self hL q)
  have h1 : ∑ q, (if OnCh j (cidx N q) (cidx N p) then ‖gcmRes sys L p₀ N q p‖ else 0) =
      ∑ q ∈ T, ‖gcmRes sys L p₀ N q p‖ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hj : OnCh j (cidx N q) (cidx N p)
    · by_cases hqT : q ∈ T
      · have hm := (Finset.mem_filter.mp hqT).2
        rw [if_pos hj, if_pos hm]
      · have hm : ¬ (OnCh j (cidx N q) (cidx N p) ∧ q ≠ p ∧ ¬ gapC sys L N q p) := fun h =>
          hqT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        rw [if_pos hj, if_neg hm, hzero q hj hqT, norm_zero]
    · have hm : ¬ (OnCh j (cidx N q) (cidx N p) ∧ q ≠ p ∧ ¬ gapC sys L N q p) := fun h => hj h.1
      rw [if_neg hj, if_neg hm]
  rw [h1]
  -- the kernel bound on the resonant elements
  have h2 : ∀ q ∈ T, ‖gcmRes sys L p₀ N q p‖ ≤ chC sys L j * gF L ^ 2 * piC j (cidx N p) /
      Mtot sys j * (1 / FSChannel.rho (chT N j q p)) := by
    intro q hq
    obtain ⟨hj, hne, hgq⟩ := (Finset.mem_filter.mp hq).2
    have hθ : 1 ≤ FSLattice.lsq (chT N j q p) := one_le_lsq_chT hj hne
    have hρ : 0 < FSChannel.rho (chT N j q p) := by
      unfold FSChannel.rho; exact Real.sqrt_pos.mpr (by linarith)
    have hρsq := FSChannel.rho_sq (chT N j q p)
    unfold gcmRes
    rw [if_neg hgq, gcmK_eq hL hj, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    calc ‖wNK sys L N q p‖ * |comC sys p₀ (gF L) j (cidx N p) (chT N j q p)|
        ≤ chC sys L j / FSLattice.lsq (chT N j q p) *
            (gF L ^ 2 * FSChannel.rho (chT N j q p) * piC j (cidx N p) / Mtot sys j) :=
          mul_le_mul (norm_wNK_chan_le hL hj hne) (abs_comC_le sys p₀ (gF L) j _ _)
            (abs_nonneg _) (by positivity)
      _ = _ := by rw [← hρsq]; field_simp
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.mul_sum]
  -- the transfers
  set c := cCh sys j (cidx N p)
  have hinj : Set.InjOn (fun q => chT N j q p) T := fun q hq q' hq' h =>
    chT_injOn j p (Finset.mem_filter.mp hq).2.1 (Finset.mem_filter.mp hq').2.1 h
  rw [← Finset.sum_image (f := fun θ => 1 / FSChannel.rho θ) hinj]
  set X := ∑ c' ∈ moved j, nsq (cidx N p c')
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun c' _ => nsq_nonneg _
  have h3 := FSLattice.sum_inv_rho_res_le c hX0 (T.image fun q => chT N j q p) (by
    intro θ hθ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨hj, hne, hgq⟩ := (Finset.mem_filter.mp hq).2
    have hθ1 := one_le_lsq_chT hj hne
    have hres : |FSLattice.slabF c (chT N j q p)| < 2 * FSChannel.rho (chT N j q p) := by
      have hfl : ¬ gF L ^ 2 * FSChannel.rho (chT N j q p) / muCh sys j ≤
          |Asym sys L N q - Asym sys L N p| := fun h => hgq ⟨hne, j, hj, h⟩
      push Not at hfl
      rw [Asym_hop hj, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))] at hfl
      have e : gF L ^ 2 * FSChannel.rho (chT N j q p) / muCh sys j =
          gF L ^ 2 / (2 * muCh sys j) * (2 * FSChannel.rho (chT N j q p)) := by field_simp
      rw [e] at hfl
      exact lt_of_mul_lt_mul_left hfl (by positivity)
    refine ⟨hθ1, hres, fun h64 => ?_⟩
    have hρ8 : 8 ≤ FSChannel.rho (chT N j q p) := by
      unfold FSChannel.rho
      rw [show (8 : ℝ) = Real.sqrt 64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt h64
    have hlow : |FSLattice.slabF c (chT N j q p)| < FSLattice.lsq (chT N j q p) / 4 := by
      have := FSChannel.rho_sq (chT N j q p)
      nlinarith
    obtain ⟨c', hc', hpin⟩ := pin_register sys j (cidx N p) (chT N j q p) hlow
    have : nsq (cidx N p c') ≤ X :=
      Finset.single_le_sum (f := fun c' => nsq (cidx N p c')) (fun c' _ => nsq_nonneg _) hc'
    linarith)
  have hXle : X ≤ Xall p := by
    unfold Xall
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun c _ _ => FSLattice.lsq_nonneg _)
  have hpiX : piC j (cidx N p) ≤ Real.sqrt (2 * X) := piC_le_sqrt j (cidx N p)
  have hsX := Real.sqrt_nonneg X
  have hs2X : Real.sqrt (2 * X) = Real.sqrt 2 * Real.sqrt X := by
    rw [Real.sqrt_mul (by norm_num)]
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt (9 / 4) by
      rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsXX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0
  have hkey : piC j (cidx N p) * (7 + 16 / 3 * Real.sqrt X) ≤ 15 * (1 + Xall p) := by
    have hp0 := hpi
    have h2 : piC j (cidx N p) * (7 + 16 / 3 * Real.sqrt X) ≤
        Real.sqrt 2 * Real.sqrt X * (7 + 16 / 3 * Real.sqrt X) := by
      rw [← hs2X]; gcongr
    have hs2' := Real.sqrt_nonneg 2
    have h3 : Real.sqrt X ≤ (1 + X) / 2 := by nlinarith [sq_nonneg (Real.sqrt X - 1)]
    have h4 : Real.sqrt 2 * Real.sqrt X * (7 + 16 / 3 * Real.sqrt X) =
        7 * Real.sqrt 2 * Real.sqrt X + 16 / 3 * Real.sqrt 2 * X := by
      linear_combination (16 / 3 * Real.sqrt 2) * hsXX
    have h5 : 7 * Real.sqrt 2 * Real.sqrt X ≤ 7 * (3 / 2) * ((1 + X) / 2) := by
      have := mul_le_mul hs2 h3 hsX (by norm_num)
      nlinarith
    have h6 : 16 / 3 * Real.sqrt 2 * X ≤ 16 / 3 * (3 / 2) * X := by
      have := mul_le_mul_of_nonneg_right hs2 hX0
      nlinarith
    linarith
  have hA : 0 ≤ chC sys L j * gF L ^ 2 / Mtot sys j := by positivity
  calc chC sys L j * gF L ^ 2 * piC j (cidx N p) / Mtot sys j *
        ∑ θ ∈ T.image (fun q => chT N j q p), 1 / FSChannel.rho θ
      ≤ chC sys L j * gF L ^ 2 * piC j (cidx N p) / Mtot sys j *
          (55000 * (7 + 2 * (8 / 3 * Real.sqrt X))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = chC sys L j * gF L ^ 2 / Mtot sys j * (55000 * (piC j (cidx N p) *
          (7 + 16 / 3 * Real.sqrt X))) := by ring
    _ ≤ chC sys L j * gF L ^ 2 / Mtot sys j * (55000 * (15 * (1 + Xall p))) := by gcongr
    _ = CRc sys L j * (1 + Xall p) := by unfold CRc; ring

end ResRows

/-! ## The form bound -/

section ResForm

variable {X : Type*} [Fintype X]

omit [Fintype ν] in
/-- Bilinear majorant of a kernel form. -/
lemma norm_inner_kop_le₂ (κ : X → X → ℂ) (a b : EuclideanSpace ℂ X) :
    ‖⟪a, FSKernel.kop κ b⟫_ℂ‖ ≤ ∑ q, ∑ p, ‖a.ofLp q‖ * ‖b.ofLp p‖ * ‖κ q p‖ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, FSKernel.kop_apply, Pi.star_apply, RCLike.star_def]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul, Complex.norm_conj]
  calc ‖∑ p, b.ofLp p * κ q p‖ * ‖a.ofLp q‖ ≤ (∑ p, ‖b.ofLp p‖ * ‖κ q p‖) * ‖a.ofLp q‖ := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun p _ => norm_mul _ _
    _ = ∑ p, ‖a.ofLp q‖ * ‖b.ofLp p‖ * ‖κ q p‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun p _ => by ring

omit [Fintype ν] in
/-- Cauchy–Schwarz for a nonnegative kernel. -/
lemma sum_kernel_cs (K : X → X → ℝ) (hK : ∀ q p, 0 ≤ K q p) (x y : X → ℝ) :
    ∑ q, ∑ p, x q * y p * K q p ≤
      Real.sqrt (∑ q, ∑ p, x q ^ 2 * K q p) * Real.sqrt (∑ q, ∑ p, y p ^ 2 * K q p) := by
  rw [← Finset.sum_product', ← Finset.sum_product', ← Finset.sum_product']
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ ×ˢ Finset.univ)
    (fun z : X × X => x z.1 * Real.sqrt (K z.1 z.2)) (fun z => y z.2 * Real.sqrt (K z.1 z.2))
  have e1 : ∀ z : X × X, x z.1 * Real.sqrt (K z.1 z.2) * (y z.2 * Real.sqrt (K z.1 z.2)) =
      x z.1 * y z.2 * K z.1 z.2 := fun z => by
    rw [show x z.1 * Real.sqrt (K z.1 z.2) * (y z.2 * Real.sqrt (K z.1 z.2)) =
      x z.1 * y z.2 * (Real.sqrt (K z.1 z.2) * Real.sqrt (K z.1 z.2)) by ring,
      Real.mul_self_sqrt (hK _ _)]
  have e2 : ∀ z : X × X, (x z.1 * Real.sqrt (K z.1 z.2)) ^ 2 = x z.1 ^ 2 * K z.1 z.2 := fun z => by
    rw [mul_pow, Real.sq_sqrt (hK _ _)]
  have e3 : ∀ z : X × X, (y z.2 * Real.sqrt (K z.1 z.2)) ^ 2 = y z.2 ^ 2 * K z.1 z.2 := fun z => by
    rw [mul_pow, Real.sq_sqrt (hK _ _)]
  simp only [e1, e2, e3] at h
  exact h

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

/-- The constant of the resonant form: `Σ_j C_j`. -/
noncomputable def CRt (sys : CoulombSystem eta ν) (L : ℝ) : ℝ := ∑ j : Ch eta, CRc sys L j

/-- **The resonant com form**: `|⟨a, G^{cm,res} b⟩| ≤ (Σ_j C_j) (Σ(1+X)|a|²)^{1/2} (Σ(1+X)|b|²)^{1/2}`. -/
theorem norm_form_gcmRes_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (a b : En eta N) :
    ‖⟪a, FSKernel.kop (gcmRes sys L p₀ N) b⟫_ℂ‖ ≤ CRt sys L *
      (Real.sqrt (∑ q, (1 + Xall q) * ‖a.ofLp q‖ ^ 2) * Real.sqrt (∑ p, (1 + Xall p) * ‖b.ofLp p‖ ^ 2)) := by
  classical
  refine (norm_inner_kop_le₂ _ a b).trans ?_
  -- channel decomposition
  set K : Ch eta → Cfg eta N → Cfg eta N → ℝ := fun j q p =>
    if OnCh j (cidx N q) (cidx N p) then ‖gcmRes sys L p₀ N q p‖ else 0
  have hK0 : ∀ j q p, 0 ≤ K j q p := fun j q p => by simp only [K]; split_ifs <;> positivity
  have hdec : ∀ q p, ‖gcmRes sys L p₀ N q p‖ ≤ ∑ j, K j q p := by
    intro q p
    by_cases h0 : gcmRes sys L p₀ N q p = 0
    · rw [h0, norm_zero]; exact Finset.sum_nonneg fun j _ => hK0 j q p
    have hw : wNK sys L N q p ≠ 0 := by
      intro hw; apply h0; unfold gcmRes; split_ifs
      · rfl
      · exact gcmK_eq_zero hw
    obtain ⟨j, hj⟩ := exists_onCh_of_ne_zero (sys := sys) hL
      (show potKernel sys L (cidx N q) (cidx N p) ≠ 0 from hw)
    calc ‖gcmRes sys L p₀ N q p‖ = K j q p := by simp only [K]; rw [if_pos hj]
      _ ≤ ∑ j, K j q p := Finset.single_le_sum (f := fun j => K j q p) (fun j _ => hK0 j q p)
          (Finset.mem_univ j)
  have hrow : ∀ j p, ∑ q, K j q p ≤ CRc sys L j * (1 + Xall p) := fun j p =>
    row_gcmRes_le (sys := sys) (p₀ := p₀) hL j p
  have hcol : ∀ j q, ∑ p, K j q p ≤ CRc sys L j * (1 + Xall q) := by
    intro j q
    refine le_trans (le_of_eq ?_) (hrow j q)
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [K]
    by_cases hj : OnCh j (cidx N q) (cidx N p)
    · rw [if_pos hj, if_pos (onCh_symm hj), gcmRes_conj hL H hKernel p q, Complex.norm_conj]
    · rw [if_neg hj, if_neg (fun h => hj (onCh_symm h))]
  set A := ∑ q, (1 + Xall q) * ‖a.ofLp q‖ ^ 2
  set B := ∑ p, (1 + Xall p) * ‖b.ofLp p‖ ^ 2
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun q _ => by have := Xall_nonneg q; positivity
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun q _ => by have := Xall_nonneg q; positivity
  have hj : ∀ j, ∑ q, ∑ p, ‖a.ofLp q‖ * ‖b.ofLp p‖ * K j q p ≤
      CRc sys L j * (Real.sqrt A * Real.sqrt B) := by
    intro j
    refine (sum_kernel_cs (K j) (hK0 j) (fun q => ‖a.ofLp q‖) (fun p => ‖b.ofLp p‖)).trans ?_
    have hc := CRc_nonneg (sys := sys) hL j
    have h1 : ∑ q, ∑ p, ‖a.ofLp q‖ ^ 2 * K j q p ≤ CRc sys L j * A := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q _ => ?_
      rw [← Finset.mul_sum]
      calc ‖a.ofLp q‖ ^ 2 * ∑ p, K j q p ≤ ‖a.ofLp q‖ ^ 2 * (CRc sys L j * (1 + Xall q)) :=
            mul_le_mul_of_nonneg_left (hcol j q) (sq_nonneg _)
        _ = CRc sys L j * ((1 + Xall q) * ‖a.ofLp q‖ ^ 2) := by ring
    have h2 : ∑ q, ∑ p, ‖b.ofLp p‖ ^ 2 * K j q p ≤ CRc sys L j * B := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [← Finset.mul_sum]
      calc ‖b.ofLp p‖ ^ 2 * ∑ q, K j q p ≤ ‖b.ofLp p‖ ^ 2 * (CRc sys L j * (1 + Xall p)) :=
            mul_le_mul_of_nonneg_left (hrow j p) (sq_nonneg _)
        _ = CRc sys L j * ((1 + Xall p) * ‖b.ofLp p‖ ^ 2) := by ring
    calc Real.sqrt (∑ q, ∑ p, ‖a.ofLp q‖ ^ 2 * K j q p) * Real.sqrt (∑ q, ∑ p, ‖b.ofLp p‖ ^ 2 * K j q p)
        ≤ Real.sqrt (CRc sys L j * A) * Real.sqrt (CRc sys L j * B) :=
          mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = CRc sys L j * (Real.sqrt A * Real.sqrt B) := by
          rw [Real.sqrt_mul hc, Real.sqrt_mul hc]
          rw [show Real.sqrt (CRc sys L j) * Real.sqrt A * (Real.sqrt (CRc sys L j) * Real.sqrt B) =
            (Real.sqrt (CRc sys L j) * Real.sqrt (CRc sys L j)) * (Real.sqrt A * Real.sqrt B) by ring,
            Real.mul_self_sqrt hc]
  calc ∑ q, ∑ p, ‖a.ofLp q‖ * ‖b.ofLp p‖ * ‖gcmRes sys L p₀ N q p‖
      ≤ ∑ q, ∑ p, ∑ j, ‖a.ofLp q‖ * ‖b.ofLp p‖ * K j q p := by
        refine Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun p _ => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hdec q p) (by positivity)
    _ = ∑ j, ∑ q, ∑ p, ‖a.ofLp q‖ * ‖b.ofLp p‖ * K j q p :=
        sum3_comm (fun q p j => ‖a.ofLp q‖ * ‖b.ofLp p‖ * K j q p)
    _ ≤ ∑ j, CRc sys L j * (Real.sqrt A * Real.sqrt B) := Finset.sum_le_sum fun j _ => hj j
    _ = CRt sys L * (Real.sqrt A * Real.sqrt B) := by unfold CRt; rw [Finset.sum_mul]

end ResForm



/-! ## The resonant com flux -/

section ResFlux

variable (sys : CoulombSystem eta ν) {L : ℝ} {N : ℕ}

omit [Fintype ν] in
/-- `Σ_c |k_c|² ≤ (2 m_max/g²) A`. -/
lemma Xall_le_Asym (hL : 0 < L) (q : Cfg eta N) : Xall q ≤ 2 * mmax sys / gF L ^ 2 * Asym sys L N q := by
  have hg := gF_pos hL
  unfold Xall Asym massKineticSymbol
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have hm := sys.mass_pos c
  have hmm := mass_le_mmax sys c
  have e := kabs_sq_eq (n := N) L (q c)
  have hgl : gL L = gF L := rfl
  rw [hgl] at e
  rw [e]
  have h0 : 0 ≤ FSLattice.lsq (finitePlaneWaveLatticeIndex N (q c)) := FSLattice.lsq_nonneg _
  change FSLattice.lsq (finitePlaneWaveLatticeIndex N (q c)) ≤ _
  rw [show 2 * mmax sys / gF L ^ 2 * (1 / 2 * (gF L ^ 2 * FSLattice.lsq (finitePlaneWaveLatticeIndex N (q c)) /
    sys.mass c)) = mmax sys / sys.mass c * FSLattice.lsq (finitePlaneWaveLatticeIndex N (q c)) by
    field_simp]
  have : 1 ≤ mmax sys / sys.mass c := by rw [le_div_iff₀ hm]; linarith
  nlinarith

omit [Fintype ν] in
/-- `Σ (1 + A)|v|² ≤ ‖v‖ ‖(1+A) v‖`. -/
lemma sum_wt_le (v : En eta N) :
    ∑ q, (1 + Asym sys L N q) * ‖v.ofLp q‖ ^ 2 ≤ ‖v‖ * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 v‖ := by
  have hcs := norm_inner_le_norm (𝕜 := ℂ) v (FSSpectral.wt (sb eta N) (Asym sys L N) 1 v)
  have e : ∑ q, (1 + Asym sys L N q) * ‖v.ofLp q‖ ^ 2 =
      ‖⟪v, FSSpectral.wt (sb eta N) (Asym sys L N) 1 v⟫_ℂ‖ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    unfold dotProduct
    simp only [wt_one_apply, Pi.star_apply, RCLike.star_def]
    have e2 : ∑ q, ((1 + Asym sys L N q : ℝ) : ℂ) * v.ofLp q * (starRingEnd ℂ) (v.ofLp q) =
        ((∑ q, (1 + Asym sys L N q) * ‖v.ofLp q‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [mul_assoc, Complex.mul_conj']
    rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (by have := Asym_nonneg sys L N q; linarith)
      (sq_nonneg _)
  rw [e]
  exact hcs

/-- The weight constant `1 + 2 m_max/g²`. -/
noncomputable def cXw (sys : CoulombSystem eta ν) (L : ℝ) : ℝ := 1 + 2 * mmax sys / gF L ^ 2

omit [Fintype ν] in
lemma sum_Xall_le (hL : 0 < L) (v : En eta N) :
    ∑ q, (1 + Xall q) * ‖v.ofLp q‖ ^ 2 ≤
      cXw sys L * (‖v‖ * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 v‖) := by
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hc : 0 ≤ 2 * mmax sys / gF L ^ 2 := by positivity
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_wt_le sys v) (by unfold cXw; positivity))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have h1 := Xall_le_Asym sys hL q
  have hA := Asym_nonneg sys L N q
  have : 1 + Xall q ≤ cXw sys L * (1 + Asym sys L N q) := by
    unfold cXw; nlinarith
  calc (1 + Xall q) * ‖v.ofLp q‖ ^ 2 ≤ cXw sys L * (1 + Asym sys L N q) * ‖v.ofLp q‖ ^ 2 :=
        mul_le_mul_of_nonneg_right this (sq_nonneg _)
    _ = _ := by ring

omit [Fintype ν] in
/-- The weighted tail of a good state: `Σ (1+X)|res S u|² ≤ c_X η² M² l⁻³`. -/
lemma sum_Xall_res_le (hL : 0 < L) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u)
    (S : Cfg eta N → Prop) {l : ℝ} (hl : 1 ≤ l)
    (hS : ∀ q, S q → ∃ c, l < finitePlaneWaveKabs (2 * Real.pi / L) N (q c)) :
    ∑ q, (1 + Xall q) * ‖(FSKernel.res S u).ofLp q‖ ^ 2 ≤ cXw sys L * (eta ^ 2 * M ^ 2 * l ^ (-(3 : ℝ))) := by
  have hl0 : 0 < l := by linarith
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  obtain ⟨h1, h2⟩ := res_tails_good sys hu S hl hS
  refine (sum_Xall_le sys hL _).trans ?_
  have hc : 0 ≤ cXw sys L := by unfold cXw; have := gF_pos hL; have := one_le_mmax sys; positivity
  apply mul_le_mul_of_nonneg_left _ hc
  have hp : l ^ (-(5 / 2 : ℝ)) * l ^ (-(1 / 2 : ℝ)) = l ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_add hl0]; norm_num
  calc ‖FSKernel.res S u‖ * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (FSKernel.res S u)‖
      ≤ (eta * M * l ^ (-(5 / 2 : ℝ))) * (eta * M * l ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = eta ^ 2 * M ^ 2 * l ^ (-(3 : ℝ)) := by rw [← hp]; ring

variable {sys}

/-- **A resonant crossing starts beyond `3n/64`**: if `q ∉ P`, `p ∈ P` and `G^{cm,res}(q, p) ≠ 0`
(`n ≥ 64`), then `p` has a register with `|k|² > (3n/64)²`. -/
theorem gcmRes_cross {p₀ : Fin eta} (hL : 0 < L) {n : ℕ} (hn : 64 ≤ n) {q p : Cfg eta N}
    (hq : ¬ InP (n : ℝ) (cidx N q)) (hp : InP (n : ℝ) (cidx N p))
    (h : gcmRes sys L p₀ N q p ≠ 0) : ∃ c, (3 * n / 64 : ℝ) ^ 2 < FSLattice.lsq (cidx N p c) := by
  have hg := gF_pos hL
  have hgq : ¬ gapC sys L N q p := by intro hg'; apply h; unfold gcmRes; rw [if_pos hg']
  have hw : wNK sys L N q p ≠ 0 := by
    intro hw; apply h; unfold gcmRes; rw [if_neg hgq]; exact gcmK_eq_zero hw
  obtain ⟨j, hj⟩ := exists_onCh_of_ne_zero (sys := sys) hL
    (show potKernel sys L (cidx N q) (cidx N p) ≠ 0 from hw)
  have hne : q ≠ p := by intro hqp; rw [hqp] at hq; exact hq hp
  have hμ := muCh_pos sys j
  set θ := chT N j q p
  have hres : |FSLattice.slabF (cCh sys j (cidx N p)) θ| < 2 * FSChannel.rho θ := by
    have hfl : ¬ gF L ^ 2 * FSChannel.rho θ / muCh sys j ≤ |Asym sys L N q - Asym sys L N p| :=
      fun h' => hgq ⟨hne, j, hj, h'⟩
    push Not at hfl
    rw [Asym_hop hj, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))] at hfl
    have e : gF L ^ 2 * FSChannel.rho θ / muCh sys j =
        gF L ^ 2 / (2 * muCh sys j) * (2 * FSChannel.rho θ) := by field_simp
    rw [e] at hfl
    exact lt_of_mul_lt_mul_left hfl (by positivity)
  have hn0 : (64 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hsmall : FSChannel.rho θ ≤ n / 8
  · -- crossing within `n/8`
    simp only [InP, not_forall, not_le] at hq
    obtain ⟨c, i, hci⟩ := hq
    refine ⟨c, ?_⟩
    have e := cidx_onCh hj
    have hqc : (cidx N q c i : ℝ) = (cidx N p c i : ℝ) + (tr j θ c i : ℝ) := by
      rw [e]; simp; rfl
    have htr := abs_tr_le j θ c i
    have hθi := abs_coord_le_rho θ i
    have h1 : (7 * n / 8 : ℝ) < |((cidx N p c i : ℤ) : ℝ)| := by
      rw [hqc] at hci
      have := abs_add_le ((cidx N p c i : ℤ) : ℝ) ((tr j θ c i : ℤ) : ℝ)
      linarith
    have h2 := sq_coord_le_lsq (cidx N p c) i
    have h3 : (7 * n / 8 : ℝ) ^ 2 < ((cidx N p c i : ℤ) : ℝ) ^ 2 := by
      rw [← sq_abs (((cidx N p c i : ℤ) : ℝ))]
      exact pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
    have h4 : (3 * n / 64 : ℝ) ^ 2 ≤ (7 * n / 8) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    linarith
  · -- pinning
    push Not at hsmall
    have hρ8 : 8 ≤ FSChannel.rho θ := by linarith
    have hlow : |FSLattice.slabF (cCh sys j (cidx N p)) θ| < FSLattice.lsq θ / 4 := by
      have := FSChannel.rho_sq θ
      nlinarith
    obtain ⟨c, -, hpin⟩ := pin_register sys j (cidx N p) θ hlow
    refine ⟨c, ?_⟩
    have hsq : (n / 8 : ℝ) ^ 2 < FSLattice.lsq θ := by
      rw [← FSChannel.rho_sq θ]
      exact pow_lt_pow_left₀ hsmall (by positivity) two_ne_zero
    have e : nsq (cidx N p c) = FSLattice.lsq (cidx N p c) := rfl
    rw [← e]
    nlinarith

/-- The resonant com flux `X^{cm,res} = G^{cm,res} - P G^{cm,res} P`. -/
noncomputable def XresN (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ) :
    En eta N →ₗ[ℂ] En eta N :=
  FSKernel.kop (gcmRes sys L p₀ N) - PN N n ∘ₗ FSKernel.kop (gcmRes sys L p₀ N) ∘ₗ PN N n

/-- **The resonant com flux at the target rate** (the com part of `cor:reslayer`): for a good
box state, `n ≥ 64` and `l = g·3n/64 ≥ 1`, `|⟨u, X^{cm,res} u⟩| ≤ 3 C_res c_X η² M² l⁻³`. -/
theorem norm_Xres_le {p₀ : Fin eta} (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {n : ℕ} (hn : 64 ≤ n) (hl : 1 ≤ gF L * (3 * n / 64)) {M : ℝ} {u : En eta N}
    (hu : IsGood sys L 1 M u) :
    ‖⟪u, XresN sys L p₀ N n u⟫_ℂ‖ ≤
      3 * CRt sys L * (cXw sys L * (eta ^ 2 * M ^ 2 * (gF L * (3 * n / 64)) ^ (-(3 : ℝ)))) := by
  classical
  set G := FSKernel.kop (gcmRes sys L p₀ N)
  set l := gF L * (3 * n / 64)
  have hg := gF_pos hL
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hGs : G.IsSymmetric := FSKernel.kop_symm _ fun q p => gcmRes_conj hL H hKernel q p
  have hsplit : u = PN N n u + RN N n u := by rw [RN_eq]; abel
  -- the expansion
  have hexp : ⟪u, XresN sys L p₀ N n u⟫_ℂ =
      ⟪PN N n u, G (RN N n u)⟫_ℂ + ⟪RN N n u, G (PN N n u)⟫_ℂ + ⟪RN N n u, G (RN N n u)⟫_ℂ := by
    unfold XresN
    rw [LinearMap.sub_apply, inner_sub_right, LinearMap.comp_apply, LinearMap.comp_apply,
      ← PN_symm n u]
    have e : ⟪u, G u⟫_ℂ = ⟪PN N n u + RN N n u, G (PN N n u + RN N n u)⟫_ℂ := by rw [← hsplit]
    rw [e, map_add, inner_add_left, inner_add_right, inner_add_right]
    ring
  -- the restricted input of the crossing term
  set Sg : Cfg eta N → Prop := fun q => InP (n : ℝ) (cidx N q) ∧
    ∃ c, (3 * n / 64 : ℝ) ^ 2 < FSLattice.lsq (cidx N q c)
  have hcross : RN N n (G (PN N n u)) = RN N n (G (FSKernel.res Sg u)) := by
    ext q
    simp only [FSKernel.res_apply, G, FSKernel.kop_apply]
    by_cases hq : InP (n : ℝ) (cidx N q)
    · simp [hq]
    simp only [hq, not_false_eq_true, if_true]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h0 : gcmRes sys L p₀ N q p = 0
    · rw [h0, mul_zero, mul_zero]
    by_cases hp : InP (n : ℝ) (cidx N p)
    · have hSg : Sg p := ⟨hp, gcmRes_cross hL hn hq hp h0⟩
      simp [hp, hSg]
    · have hSg : ¬ Sg p := fun h => hp h.1
      simp [hp, hSg]
  have hRPu : ⟪RN N n u, G (PN N n u)⟫_ℂ = ⟪RN N n u, G (FSKernel.res Sg u)⟫_ℂ := by
    have e1 : ⟪RN N n u, G (PN N n u)⟫_ℂ = ⟪RN N n u, RN N n (G (PN N n u))⟫_ℂ := by
      rw [← RN_symm n (RN N n u) (G (PN N n u)), RN_idem]
    have e2 : ⟪RN N n u, G (FSKernel.res Sg u)⟫_ℂ =
        ⟪RN N n u, RN N n (G (FSKernel.res Sg u))⟫_ℂ := by
      rw [← RN_symm n (RN N n u) (G (FSKernel.res Sg u)), RN_idem]
    rw [e1, hcross, ← e2]
  have hPRu : ‖⟪PN N n u, G (RN N n u)⟫_ℂ‖ = ‖⟪RN N n u, G (PN N n u)⟫_ℂ‖ := by
    rw [← hGs (PN N n u) (RN N n u), ← inner_conj_symm, Complex.norm_conj]
  -- the weighted tails
  have tR := sum_Xall_res_le sys hL hu (fun q : Cfg eta N => ¬ InP (n : ℝ) (cidx N q)) hl (by
    intro q hq
    obtain ⟨c, hc⟩ := exists_reg_of_not_inP hn0 hq
    refine ⟨c, lt_of_le_of_lt ?_ (kabs_gt_of_lsq_gt hL hn0 q c hc)⟩
    show gF L * (3 * n / 64) ≤ gF L * n
    nlinarith)
  have tS := sum_Xall_res_le sys hL hu Sg hl (by
    intro q hq
    obtain ⟨c, hc⟩ := hq.2
    exact ⟨c, kabs_gt_of_lsq_gt hL (by positivity) q c hc⟩)
  set T := cXw sys L * (eta ^ 2 * M ^ 2 * l ^ (-(3 : ℝ)))
  have hT0 : 0 ≤ T := by
    have : 0 ≤ cXw sys L := by unfold cXw; have := one_le_mmax sys; positivity
    have : 0 < l := by linarith
    positivity
  have hCt : 0 ≤ CRt sys L :=
    Finset.sum_nonneg (s := Finset.univ) (fun j _ => CRc_nonneg (sys := sys) hL j)
  have b1 : ‖⟪RN N n u, G (FSKernel.res Sg u)⟫_ℂ‖ ≤ CRt sys L * T := by
    refine (norm_form_gcmRes_le hL H hKernel _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCt
    calc Real.sqrt (∑ q, (1 + Xall q) * ‖(RN N n u).ofLp q‖ ^ 2) *
          Real.sqrt (∑ p, (1 + Xall p) * ‖(FSKernel.res Sg u).ofLp p‖ ^ 2)
        ≤ Real.sqrt T * Real.sqrt T :=
          mul_le_mul (Real.sqrt_le_sqrt tR) (Real.sqrt_le_sqrt tS) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = T := Real.mul_self_sqrt hT0
  have b2 : ‖⟪RN N n u, G (RN N n u)⟫_ℂ‖ ≤ CRt sys L * T := by
    refine (norm_form_gcmRes_le hL H hKernel _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCt
    calc Real.sqrt (∑ q, (1 + Xall q) * ‖(RN N n u).ofLp q‖ ^ 2) *
          Real.sqrt (∑ p, (1 + Xall p) * ‖(RN N n u).ofLp p‖ ^ 2)
        ≤ Real.sqrt T * Real.sqrt T :=
          mul_le_mul (Real.sqrt_le_sqrt tR) (Real.sqrt_le_sqrt tR) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = T := Real.mul_self_sqrt hT0
  rw [hexp]
  calc ‖⟪PN N n u, G (RN N n u)⟫_ℂ + ⟪RN N n u, G (PN N n u)⟫_ℂ + ⟪RN N n u, G (RN N n u)⟫_ℂ‖
      ≤ ‖⟪PN N n u, G (RN N n u)⟫_ℂ‖ + ‖⟪RN N n u, G (PN N n u)⟫_ℂ‖ +
          ‖⟪RN N n u, G (RN N n u)⟫_ℂ‖ := norm_add₃_le
    _ ≤ CRt sys L * T + CRt sys L * T + CRt sys L * T := by
        rw [hPRu, hRPu]
        linarith
    _ = 3 * CRt sys L * T := by ring

end ResFlux

end FSFlux
