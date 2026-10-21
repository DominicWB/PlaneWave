import PlaneWave.FluxBox.PairingDefect

/-!
# Flux route, stage 3, part 38: the same-channel word — the trace

* the same-channel composite lives on pairs on one `j`-line (`ssA_eq_zero_of_not_onCh`);
* **rigidity** (`inner_Wj_Yss_eq_zero`): for `j₃ ≠ j` and `v` cold, `⟨W_{j₃} v, Ỹ_{ss_j} v⟩ = 0`, hence
  `⟨W v, Ỹ_{ss_j} v⟩ = ⟨W_j v, Ỹ_{ss_j} v⟩` (`inner_wNK_Yss_eq`);
* **the imaginary part** (`abs_im_W_Yss_le`): `|Im ⟨W_j v, Ỹ_{ss_j} v⟩| ≤ ½ Σ |v_c| |v_b| |D(c,b)|`, and
  with `norm_ssD_le` and the line-pair identity (`sum_pairs_line`):
  `≤ (K_ss/2n³) (2 L²_j(|v|) + L²_j(wgt |v|))` (`abs_im_W_Yss_line_le`);
* for a good state, `L²_j(wgt |u_C|)` costs the critical moment (`lineSq_good_wgt_le`):
  **`|Im ⟨W u_C, Ỹ_{ss_j} u_C⟩| ≲ n⁻³ log N M² (1 + η n_d)`** (`abs_im_W_Yss_good_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section SsTrace

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

lemma wj_eq_zero_of_not_onCh {j : Ch eta} {q p : Cfg eta N} (h : ¬ OnCh j (cidx N q) (cidx N p)) :
    wj sys L N j q p = 0 := by
  unfold wj chPart; rw [if_neg h]

lemma ssK_eq_zero_of_not_onCh {j : Ch eta} {f b : Cfg eta N}
    (h : ¬ OnCh j (cidx N f) (cidx N b)) : ssK sys L p₀ N n j f b = 0 := by
  classical
  unfold ssK chainK
  split_ifs with h1
  · rw [Finset.sum_eq_zero, mul_zero]
    intro d _
    by_cases hfd : OnCh j (cidx N f) (cidx N d)
    · by_cases hdb : OnCh j (cidx N d) (cidx N b)
      · exact absurd (onCh_trans hdb (onCh_symm hfd)) h
      · rw [wj_eq_zero_of_not_onCh hdb]; simp
    · rw [wj_eq_zero_of_not_onCh hfd, zero_mul]
  · rw [mul_zero]

omit [Fintype ν] in
lemma ytK_eq_zero_of_eq_zero {κ : Cfg eta N → Cfg eta N → ℂ} {q p : Cfg eta N} (h : κ q p = 0) :
    ytK sys L N n κ q p = 0 := by
  unfold ytK; split_ifs <;> simp [h]

/-- The same-channel composite lives on pairs on one `j`-line. -/
lemma ssA_eq_zero_of_not_onCh {j : Ch eta} {c b : Cfg eta N} (h : ¬ OnCh j (cidx N c) (cidx N b)) :
    ssA sys L p₀ N n j c b = 0 := by
  unfold ssA
  refine Finset.sum_eq_zero fun f _ => ?_
  by_cases hfc : OnCh j (cidx N f) (cidx N c)
  · have hfb : ¬ OnCh j (cidx N f) (cidx N b) := fun hfb => h (onCh_trans hfb hfc)
    rw [ytK_eq_zero_of_eq_zero (ssK_eq_zero_of_not_onCh hfb), mul_zero]
  · rw [wj_eq_zero_of_not_onCh hfc, map_zero, zero_mul]

lemma ssD_eq_zero_of_not_onCh {j : Ch eta} {c b : Cfg eta N} (h : ¬ OnCh j (cidx N c) (cidx N b)) :
    ssD sys L p₀ N n j c b = 0 := by
  unfold ssD
  rw [ssA_eq_zero_of_not_onCh h, ssA_eq_zero_of_not_onCh (fun h' => h (onCh_symm h')), map_zero,
    sub_zero]

/-- **Rigidity**: for `j₃ ≠ j` and `v` cold, `⟨W_{j₃} v, Ỹ_{ss_j} v⟩ = 0`. -/
lemma inner_Wj_Yss_eq_zero {j j₃ : Ch eta} (hj : j₃ ≠ j) (v : En eta N)
    (hv : ∀ p, ¬ InC (n : ℝ) (cst sys) (cidx N p) → v.ofLp p = 0) :
    ⟪FSKernel.kop (wj sys L N j₃) v, FSKernel.kop (ytK sys L N n (ssK sys L p₀ N n j)) v⟫_ℂ = 0 := by
  classical
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun f _ => ?_
  by_cases hY : (FSKernel.kop (ytK sys L N n (ssK sys L p₀ N n j)) v).ofLp f = 0
  · rw [hY, inner_zero_right]
  · have hW : (FSKernel.kop (wj sys L N j₃) v).ofLp f = 0 := by
      rw [FSKernel.kop_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : InC (n : ℝ) (cst sys) (cidx N c)
      · by_cases h3 : OnCh j₃ (cidx N f) (cidx N c)
        · exfalso
          rw [FSKernel.kop_apply] at hY
          obtain ⟨b, _, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hY
          have hvb : v.ofLp b ≠ 0 := left_ne_zero_of_mul hb
          have hyb : ytK sys L N n (ssK sys L p₀ N n j) f b ≠ 0 := right_ne_zero_of_mul hb
          have hbC : InC (n : ℝ) (cst sys) (cidx N b) := by
            by_contra h; exact hvb (hv b h)
          have hfQ : ¬ InQ (n : ℝ) (cidx N f) := by
            intro hQ
            apply hyb
            unfold ytK
            rw [if_neg (fun h => h.1 hQ)]
          have hfb : OnCh j (cidx N f) (cidx N b) := by
            by_contra hfb
            exact hyb (ytK_eq_zero_of_eq_zero (ssK_eq_zero_of_not_onCh hfb))
          exact hfQ (inQ_of_two_hops (sys := sys) hj hbC hc hfb h3)
        · rw [wj_eq_zero_of_not_onCh h3, mul_zero]
      · rw [hv c hc, zero_mul]
    rw [hW, inner_zero_left]

/-- `W v = Σ_{j₃} W_{j₃} v`. -/
lemma kop_wNK_eq_sum (hL : 0 < L) (v : En eta N) :
    FSKernel.kop (wNK sys L N) v = ∑ j₃, FSKernel.kop (wj sys L N j₃) v := by
  ext q
  rw [WithLp.ofLp_sum, Finset.sum_apply, FSKernel.kop_apply]
  simp only [FSKernel.kop_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [wNK_eq_sum_chPart hL q p, Finset.mul_sum]
  rfl

/-- **Only the channel of the word sees it**: `⟨W v, Ỹ_{ss_j} v⟩ = ⟨W_j v, Ỹ_{ss_j} v⟩` for `v` cold. -/
lemma inner_wNK_Yss_eq (hL : 0 < L) (j : Ch eta) (v : En eta N)
    (hv : ∀ p, ¬ InC (n : ℝ) (cst sys) (cidx N p) → v.ofLp p = 0) :
    ⟪FSKernel.kop (wNK sys L N) v, FSKernel.kop (ytK sys L N n (ssK sys L p₀ N n j)) v⟫_ℂ =
      ⟪FSKernel.kop (wj sys L N j) v, FSKernel.kop (ytK sys L N n (ssK sys L p₀ N n j)) v⟫_ℂ := by
  rw [kop_wNK_eq_sum hL, sum_inner, Finset.sum_eq_single j]
  · intro j₃ _ hj₃; exact inner_Wj_Yss_eq_zero hj₃ v hv
  · intro h; exact absurd (Finset.mem_univ j) h

lemma Kss_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ Kss sys L j := by
  unfold Kss
  have h := chC_nonneg sys hL j
  have := one_le_mmax (sys := sys)
  have : 0 < gF L := by unfold gF; positivity
  exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h 3)) (by positivity)

open Classical in
/-- **The imaginary part of the same-channel word**:
`|Im ⟨W_j v, Ỹ_{ss_j} v⟩| ≤ (K_ss/2n³) Σ_{c ~_j b} |v_c| |v_b| (1 + wgt b + wgt c)` for `v` cold. -/
theorem abs_im_W_Yss_le (hL : 0 < L) (hn : 2 ≤ n) (hnN : n ≤ N) (j : Ch eta) (v : En eta N)
    (hv : ∀ p, ¬ InC (n : ℝ) (cst sys) (cidx N p) → v.ofLp p = 0) :
    |(⟪FSKernel.kop (wj sys L N j) v, FSKernel.kop (ytK sys L N n (ssK sys L p₀ N n j)) v⟫_ℂ).im| ≤
      Kss sys L j / (n : ℝ) ^ 3 / 2 * ∑ c, ∑ b, (if OnCh j (cidx N c) (cidx N b) then
        ‖v.ofLp c‖ * ‖v.ofLp b‖ * (1 + wgt j (cidx N b) + wgt j (cidx N c)) else 0) := by
  classical
  rw [inner_W_Yss]
  set S := ∑ c, ∑ b, conj (v.ofLp c) * v.ofLp b * ssA sys L p₀ N n j c b with hSd
  have hconjS : conj S = ∑ c, ∑ b, conj (v.ofLp c) * v.ofLp b * conj (ssA sys L p₀ N n j b c) := by
    rw [hSd]
    simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hdiff : S - conj S = ∑ c, ∑ b, conj (v.ofLp c) * v.ofLp b * ssD sys L p₀ N n j c b := by
    rw [hconjS, hSd, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold ssD; ring
  have him : |S.im| = ‖S - conj S‖ / 2 := by
    rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul]
    norm_num
  have hK : 0 ≤ Kss sys L j := Kss_nonneg hL j
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hKn : 0 ≤ Kss sys L j / (n : ℝ) ^ 3 := div_nonneg hK (by positivity)
  have hpt : ∀ c b, ‖conj (v.ofLp c) * v.ofLp b * ssD sys L p₀ N n j c b‖ ≤
      Kss sys L j / (n : ℝ) ^ 3 * (if OnCh j (cidx N c) (cidx N b) then
        ‖v.ofLp c‖ * ‖v.ofLp b‖ * (1 + wgt j (cidx N b) + wgt j (cidx N c)) else 0) := by
    intro c b
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hw : 0 ≤ 1 + wgt j (cidx N b) + wgt j (cidx N c) :=
      add_nonneg (add_nonneg zero_le_one (wgt_nonneg _ _)) (wgt_nonneg _ _)
    by_cases hcb : OnCh j (cidx N c) (cidx N b)
    · rw [if_pos hcb]
      by_cases hc : InC (n : ℝ) (cst sys) (cidx N c)
      · by_cases hb : InC (n : ℝ) (cst sys) (cidx N b)
        · have hD := norm_ssD_le (p₀ := p₀) hL hn hnN hb hc hcb
          calc ‖v.ofLp c‖ * ‖v.ofLp b‖ * ‖ssD sys L p₀ N n j c b‖ ≤
              ‖v.ofLp c‖ * ‖v.ofLp b‖ *
                (Kss sys L j * (1 + wgt j (cidx N b) + wgt j (cidx N c)) / (n : ℝ) ^ 3) :=
                mul_le_mul_of_nonneg_left hD (by positivity)
            _ = _ := by ring
        · rw [hv b hb, norm_zero, mul_zero, zero_mul]
          exact mul_nonneg hKn (mul_nonneg (by positivity) hw)
      · rw [hv c hc, norm_zero, zero_mul, zero_mul]
        exact mul_nonneg hKn (mul_nonneg (by positivity) hw)
    · rw [if_neg hcb, ssD_eq_zero_of_not_onCh hcb, norm_zero, mul_zero, mul_zero]
  rw [him, hdiff]
  calc ‖∑ c, ∑ b, conj (v.ofLp c) * v.ofLp b * ssD sys L p₀ N n j c b‖ / 2 ≤
      (∑ c, ∑ b, Kss sys L j / (n : ℝ) ^ 3 * (if OnCh j (cidx N c) (cidx N b) then
        ‖v.ofLp c‖ * ‖v.ofLp b‖ * (1 + wgt j (cidx N b) + wgt j (cidx N c)) else 0)) / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hpt c b))
    _ = _ := by
        simp only [← Finset.mul_sum]
        ring

end SsTrace

/-! ## Line squares of the pairs -/

section PairLines

variable {sys : CoulombSystem eta ν} {L : ℝ} {N : ℕ}

omit [Fintype ν] in
open Classical in
/-- **Pairs on one line**: `Σ_{c ~_j b} F_c G_b = Σ_ℓ L_j(F)(ℓ) L_j(G)(ℓ)`. -/
lemma sum_pairs_line (j : Ch eta) (F G : Cfg eta N → ℝ) :
    ∑ c, ∑ b, (if OnCh j (cidx N c) (cidx N b) then F c * G b else 0) =
      ∑ t ∈ labs N j, lineSum j F t * lineSum j G t := by
  classical
  have h1 : ∀ c, ∑ b, (if OnCh j (cidx N c) (cidx N b) then F c * G b else 0) =
      F c * lineSum j G (lab N j c) := by
    intro c
    unfold lineSum
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : OnCh j (cidx N c) (cidx N b)
    · rw [if_pos h, if_pos (lab_eq_iff.mpr h).symm]
    · rw [if_neg h, if_neg (fun h' => h (lab_eq_iff.mp h'.symm))]
  rw [Finset.sum_congr rfl fun c _ => h1 c, sum_by_lines j]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold lineSum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [(Finset.mem_filter.mp hc).2]

omit [Fintype ν] in
open Classical in
/-- `Σ_{c ~_j b} x_c x_b (1 + wgt b + wgt c) ≤ 2 L²_j(x) + L²_j(wgt x)`. -/
lemma sum_pairs_wgt_le (j : Ch eta) (x : Cfg eta N → ℝ) :
    ∑ c, ∑ b, (if OnCh j (cidx N c) (cidx N b) then
        x c * x b * (1 + wgt j (cidx N b) + wgt j (cidx N c)) else 0) ≤
      2 * lineSq j (fun _ => 1) x + lineSq j (fun _ => 1) (fun b => wgt j (cidx N b) * x b) := by
  classical
  have e : ∀ c b, (if OnCh j (cidx N c) (cidx N b) then
      x c * x b * (1 + wgt j (cidx N b) + wgt j (cidx N c)) else 0) =
      (if OnCh j (cidx N c) (cidx N b) then x c * x b else 0) +
      (if OnCh j (cidx N c) (cidx N b) then x c * (wgt j (cidx N b) * x b) else 0) +
      (if OnCh j (cidx N c) (cidx N b) then (wgt j (cidx N c) * x c) * x b else 0) := by
    intro c b; split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib]
  rw [sum_pairs_line j x x, sum_pairs_line j x (fun b => wgt j (cidx N b) * x b),
    sum_pairs_line j (fun b => wgt j (cidx N b) * x b) x]
  unfold lineSq
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t _ => ?_
  nlinarith [sq_nonneg (lineSum j x t - lineSum j (fun b => wgt j (cidx N b) * x b) t)]

end PairLines

/-! ## The weight `wgt` on a good state -/

section GoodWgt

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

omit [Fintype ν] in
/-- `wgt_j(q)² ≤ 8 c_X (1 + E(q))`. -/
lemma wgt_sq_le (hL : 0 < L) (j : Ch eta) (q : Cfg eta N) :
    wgt j (cidx N q) ^ 2 ≤ 8 * cXw sys L * (1 + Asym sys L N q) := by
  unfold wgt
  have h1 := sq_sum_le_card_mul_sum_sq (s := moved j) (f := fun r => FSChannel.rho (cidx N q r))
  have hc : ((moved j).card : ℝ) ≤ 2 := by exact_mod_cast card_moved_le j
  have hX : 0 ≤ cXw sys L * (1 + Asym sys L N q) := by
    have := cXw_ge_one (sys := sys) hL
    have := FSGalerkin.Asym_nonneg sys L N q
    positivity
  have h2 : ∀ r ∈ moved j, FSChannel.rho (cidx N q r) ^ 2 ≤ 2 * (cXw sys L * (1 + Asym sys L N q)) := by
    intro r _
    have h := one_add_lsq_regSum_le (sys := sys) hL (A := {r}) (by simp) q
    have e : regSum {r} (cidx N q) = cidx N q r := by simp [regSum]
    rw [e] at h
    rw [FSChannel.rho_sq]
    linarith
  have h3 : ∑ r ∈ moved j, FSChannel.rho (cidx N q r) ^ 2 ≤
      (moved j).card * (2 * (cXw sys L * (1 + Asym sys L N q))) := by
    have := Finset.sum_le_card_nsmul (moved j) (fun r => FSChannel.rho (cidx N q r) ^ 2) _ h2
    rwa [nsmul_eq_mul] at this
  have h4 : ((moved j).card : ℝ) * ∑ r ∈ moved j, FSChannel.rho (cidx N q r) ^ 2 ≤
      2 * (2 * (2 * (cXw sys L * (1 + Asym sys L N q)))) := by
    have hs0 : 0 ≤ ∑ r ∈ moved j, FSChannel.rho (cidx N q r) ^ 2 :=
      Finset.sum_nonneg fun r _ => sq_nonneg _
    have hc0 : (0 : ℝ) ≤ (moved j).card := Nat.cast_nonneg _
    calc ((moved j).card : ℝ) * ∑ r ∈ moved j, FSChannel.rho (cidx N q r) ^ 2 ≤
        2 * ((moved j).card * (2 * (cXw sys L * (1 + Asym sys L N q)))) :=
          mul_le_mul hc h3 hs0 (by norm_num)
      _ ≤ 2 * (2 * (2 * (cXw sys L * (1 + Asym sys L N q)))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hc (by positivity)
  calc (∑ r ∈ moved j, FSChannel.rho (cidx N q r)) ^ 2 ≤
      ((moved j).card : ℝ) * ∑ r ∈ moved j, FSChannel.rho (cidx N q r) ^ 2 := h1
    _ ≤ 2 * (2 * (2 * (cXw sys L * (1 + Asym sys L N q)))) := h4
    _ = 8 * cXw sys L * (1 + Asym sys L N q) := by ring

variable (sys L) in
/-- The weight constant of `wgt²` against `w32`. -/
noncomputable def Wwc : ℝ := 2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * (8 * cXw sys L)

omit [Fintype ν] in
lemma Wwc_nonneg (hL : 0 < L) : 0 ≤ Wwc sys L := by
  unfold Wwc
  have := cXw_ge_one (sys := sys) hL
  positivity

omit [Fintype ν] in
/-- **The `wgt`-weighted line squares of a good state**. -/
theorem lineSq_good_wgt_le (hL : 0 < L) (hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd)
    {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) (S : Cfg eta N → Prop) [DecidablePred S]
    (j : Ch eta) :
    lineSq j (fun _ => 1) (fun b => wgt j (cidx N b) * (if S b then ‖u.ofLp b‖ else 0)) ≤
      125 * (Nat.log 2 (2 * N) + 2) *
        (Wwc sys L * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd))) := by
  have h := lineSq_le j (fun _ => zero_le_one)
    (fun b => wgt j (cidx N b) * (if S b then ‖u.ofLp b‖ else 0))
    (fun p => w32 (regSum {lead j} (cidx N p))) (fun p => w32_pos _)
    (fun q => lineSum_inv_w32_le hN (coord_lead j) q)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hcm := crit_moment_box (sys := sys) hL hnd hu
  have hW := Wwc_nonneg (sys := sys) hL
  calc ∑ p, (1 : ℝ) * w32 (regSum {lead j} (cidx N p)) *
        (wgt j (cidx N p) * (if S p then ‖u.ofLp p‖ else 0)) ^ 2 ≤
      ∑ p, Wwc sys L * ((1 + Asym sys L N p) ^ 2 * Real.sqrt (1 + Asym sys L N p) * ‖u.ofLp p‖ ^ 2) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have h1 := wgt_sq_le (sys := sys) hL j p
        have h2 := weight5_le (sys := sys) hL (coord_lead j).card p (sq_nonneg _) h1
        have h3 : (if S p then ‖u.ofLp p‖ else 0) ^ 2 ≤ ‖u.ofLp p‖ ^ 2 := by
          split_ifs
          · exact le_rfl
          · rw [sq, mul_zero]; exact sq_nonneg _
        have hA := FSGalerkin.Asym_nonneg sys L N p
        calc (1 : ℝ) * w32 (regSum {lead j} (cidx N p)) *
              (wgt j (cidx N p) * (if S p then ‖u.ofLp p‖ else 0)) ^ 2 =
            (wgt j (cidx N p) ^ 2 * w32 (regSum {lead j} (cidx N p))) *
              (if S p then ‖u.ofLp p‖ else 0) ^ 2 := by ring
          _ ≤ (Wwc sys L * ((1 + Asym sys L N p) ^ 2 * Real.sqrt (1 + Asym sys L N p))) *
                ‖u.ofLp p‖ ^ 2 := by
              apply mul_le_mul _ h3 (sq_nonneg _) (by positivity)
              unfold Wwc; linarith
          _ = Wwc sys L * ((1 + Asym sys L N p) ^ 2 * Real.sqrt (1 + Asym sys L N p) *
                ‖u.ofLp p‖ ^ 2) := by ring
    _ = Wwc sys L * ∑ p, (1 + Asym sys L N p) ^ 2 * Real.sqrt (1 + Asym sys L N p) *
          ‖u.ofLp p‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcm hW

/-- The bound of the same-channel word on a good state. -/
noncomputable def Bss (sys : CoulombSystem eta ν) (L : ℝ) (N nd : ℕ) (M : ℝ) : ℝ :=
  2 * (125 * (Nat.log 2 (2 * N) + 2) * (4 * cXw sys L ^ 2 * M ^ 2)) +
    125 * (Nat.log 2 (2 * N) + 2) *
      (Wwc sys L * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd)))

open Classical in
/-- **The same-channel word on a good state**:
`|Im ⟨W u_C, Ỹ_{ss_j} u_C⟩| ≤ (K_ss/2n³) B_ss`, `B_ss ≲ log N M² (1 + η n_d)`. -/
theorem abs_im_W_Yss_good_le (hL : 0 < L) (hn : 2 ≤ n) (hnN : n ≤ N) {nd : ℕ}
    (hnd : gF L * (2 * N) ≤ 2 ^ nd) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) (j : Ch eta) :
    |(⟪FSKernel.kop (wNK sys L N) (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u),
        FSKernel.kop (ytK sys L N n (ssK sys L p₀ N n j))
          (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u)⟫_ℂ).im| ≤
      Kss sys L j / (n : ℝ) ^ 3 / 2 * Bss sys L N nd M := by
  classical
  have hN : 1 ≤ N := by omega
  set v := FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u with hvd
  have hv : ∀ p, ¬ InC (n : ℝ) (cst sys) (cidx N p) → v.ofLp p = 0 := by
    intro p hp; rw [hvd, FSKernel.res_apply, if_neg hp]
  have hvn : ∀ p, ‖v.ofLp p‖ = if InC (n : ℝ) (cst sys) (cidx N p) then ‖u.ofLp p‖ else 0 := by
    intro p; rw [hvd, FSKernel.res_apply]; split_ifs <;> simp
  rw [inner_wNK_Yss_eq hL j v hv]
  refine (abs_im_W_Yss_le hL hn hnN j v hv).trans ?_
  have hK : 0 ≤ Kss sys L j / (n : ℝ) ^ 3 / 2 := by
    have := Kss_nonneg (sys := sys) hL j
    positivity
  apply mul_le_mul_of_nonneg_left _ hK
  have h1 := sum_pairs_wgt_le j (fun p => ‖v.ofLp p‖)
  have h2 := lineSq_good_le hL hN hu (fun p => InC (n : ℝ) (cst sys) (cidx N p)) j
  have h3 := lineSq_good_wgt_le hL hN hnd hu (fun p => InC (n : ℝ) (cst sys) (cidx N p)) j
  have e1 : (fun p => ‖v.ofLp p‖) = (fun p => if InC (n : ℝ) (cst sys) (cidx N p) then ‖u.ofLp p‖ else 0) :=
    funext hvn
  have e2 : (fun b => wgt j (cidx N b) * ‖v.ofLp b‖) =
      (fun b => wgt j (cidx N b) * if InC (n : ℝ) (cst sys) (cidx N b) then ‖u.ofLp b‖ else 0) :=
    funext fun b => by rw [hvn]
  rw [e1, e2] at h1
  unfold Bss
  linarith

end GoodWgt

end FSFlux
