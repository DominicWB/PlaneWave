import PlaneWave.FluxBox.LongHops

/-!
# Flux route, stage 2, part 9: the endpoint of the flat elimination

* `wns_le`: `Σ (1 + 2A)|x|² ≤ 2 ‖x‖ ‖(1+A) x‖`;
* `Asym_ge_of_not_inP`: outside the cube `A ≥ K²/(2 m_max)`, `K = g n`;
* `norm_inner_RN_le`: `|⟨R u, x⟩| ≤ ‖(1+A) R u‖ ‖R x‖ / (1 + K²/(2 m_max))`;
* **`norm_Whc_form_le`**: `|⟨u, Ŵ_c u⟩| ≤ C_end M² K⁻³` for a good box state.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Endpoint

omit [Fintype ν] in
/-- Cauchy–Schwarz for coordinates. -/
lemma sum_norm_mul_le {X : Type*} [Fintype X] (a b : EuclideanSpace ℂ X) :
    ∑ q, ‖a.ofLp q‖ * ‖b.ofLp q‖ ≤ ‖a‖ * ‖b‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun q => ‖a.ofLp q‖) (fun q => ‖b.ofLp q‖)
  rw [EuclideanSpace.norm_eq a, EuclideanSpace.norm_eq b]
  exact h

variable (sys : CoulombSystem eta ν) {L : ℝ} {N : ℕ}

omit [Fintype ν] in
lemma wns_le (x : En eta N) :
    weightedNormSq (hw sys L N) x ≤ 2 * ‖x‖ * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 x‖ := by
  have h1 : weightedNormSq (hw sys L N) x ≤ 2 * ∑ q, (1 + Asym sys L N q) * ‖x.ofLp q‖ ^ 2 := by
    unfold weightedNormSq
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have hA := Asym_nonneg sys L N q
    have e : hw sys L N q = 1 + 2 * Asym sys L N q := by
      simp only [hw, Asym]; ring
    rw [e]
    nlinarith [sq_nonneg ‖x.ofLp q‖]
  have h2 : ∑ q, (1 + Asym sys L N q) * ‖x.ofLp q‖ ^ 2 ≤
      ‖x‖ * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 x‖ := by
    have hcs := norm_inner_le_norm (𝕜 := ℂ) x (FSSpectral.wt (sb eta N) (Asym sys L N) 1 x)
    have e : ∑ q, (1 + Asym sys L N q) * ‖x.ofLp q‖ ^ 2 =
        ‖⟪x, FSSpectral.wt (sb eta N) (Asym sys L N) 1 x⟫_ℂ‖ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      unfold dotProduct
      simp only [wt_one_apply, Pi.star_apply, RCLike.star_def]
      have e2 : ∑ q, ((1 + Asym sys L N q : ℝ) : ℂ) * x.ofLp q * (starRingEnd ℂ) (x.ofLp q) =
          ((∑ q, (1 + Asym sys L N q) * ‖x.ofLp q‖ ^ 2 : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [mul_assoc, Complex.mul_conj']
      rw [e2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact Finset.sum_nonneg fun q _ => mul_nonneg (by have := Asym_nonneg sys L N q; linarith)
        (sq_nonneg _)
    rw [e]
    exact hcs
  linarith

omit [Fintype ν] in
lemma sqrt_wns_le (x : En eta N) :
    Real.sqrt (weightedNormSq (hw sys L N) x) ≤
      Real.sqrt (2 * ‖x‖ * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 x‖) :=
  Real.sqrt_le_sqrt (wns_le sys x)

omit [Fintype ν] in
/-- Outside the cube `A ≥ K²/(2 m_max)`. -/
lemma Asym_ge_of_not_inP (hL : 0 < L) {n : ℕ} {q : Cfg eta N} (h : ¬ InP (n : ℝ) (cidx N q)) :
    (gF L * n) ^ 2 / (2 * mmax sys) ≤ Asym sys L N q := by
  obtain ⟨c, hc⟩ := exists_reg_of_not_inP (by positivity) h
  have hk := kabs_gt_of_lsq_gt hL (by positivity : (0 : ℝ) ≤ n) q c hc
  have hm := sys.mass_pos c
  have hmm := mass_le_mmax sys c
  have hk0 : 0 ≤ gF L * n := by have := gF_pos hL; positivity
  have h1 : (gF L * n) ^ 2 ≤ finitePlaneWaveKabs (2 * Real.pi / L) N (q c) ^ 2 :=
    pow_le_pow_left₀ hk0 hk.le 2
  unfold Asym massKineticSymbol
  have h2 : finitePlaneWaveKabs (2 * Real.pi / L) N (q c) ^ 2 / sys.mass c ≤
      ∑ a, finitePlaneWaveKabs (2 * Real.pi / L) N (q a) ^ 2 / sys.mass a :=
    Finset.single_le_sum (f := fun a => finitePlaneWaveKabs (2 * Real.pi / L) N (q a) ^ 2 / sys.mass a)
      (fun a _ => by have := sys.mass_pos a; positivity) (Finset.mem_univ c)
  have h3 : (gF L * n) ^ 2 / mmax sys ≤ finitePlaneWaveKabs (2 * Real.pi / L) N (q c) ^ 2 / sys.mass c := by
    calc (gF L * n) ^ 2 / mmax sys ≤ (gF L * n) ^ 2 / sys.mass c :=
          div_le_div_of_nonneg_left (by positivity) hm hmm
      _ ≤ _ := div_le_div_of_nonneg_right h1 hm.le
  have e : (gF L * n) ^ 2 / (2 * mmax sys) = 1 / 2 * ((gF L * n) ^ 2 / mmax sys) := by
    have := one_le_mmax sys
    field_simp
  rw [e]
  linarith

omit [Fintype ν] in
/-- **The weight trick outside the cube.** -/
lemma norm_inner_RN_le (hL : 0 < L) (n : ℕ) (u x : En eta N) :
    ‖⟪RN N n u, x⟫_ℂ‖ ≤ ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖ * ‖RN N n x‖ /
      (1 + (gF L * n) ^ 2 / (2 * mmax sys)) := by
  classical
  set a₀ := (gF L * n) ^ 2 / (2 * mmax sys)
  have ha₀ : 0 ≤ a₀ := by have := one_le_mmax sys; positivity
  have hpos : 0 < 1 + a₀ := by linarith
  have hxq : ∀ q, ‖(RN N n u).ofLp q‖ * ‖x.ofLp q‖ ≤
      ‖(FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)).ofLp q‖ * ‖(RN N n x).ofLp q‖ / (1 + a₀) := by
    intro q
    rw [wt_one_apply, FSKernel.res_apply, FSKernel.res_apply]
    by_cases h : InP (n : ℝ) (cidx N q)
    · simp [h]
    · simp only [h, not_false_eq_true, if_true]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by have := Asym_nonneg sys L N q; linarith)]
      have hA := Asym_ge_of_not_inP sys hL h
      rw [le_div_iff₀ hpos]
      have h0 := mul_nonneg (norm_nonneg (u.ofLp q)) (norm_nonneg (x.ofLp q))
      nlinarith
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine (norm_sum_le _ _).trans ?_
  calc ∑ q, ‖(x.ofLp q) * star ((RN N n u).ofLp q)‖
      = ∑ q, ‖(RN N n u).ofLp q‖ * ‖x.ofLp q‖ := by
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only
        rw [norm_mul, norm_star, mul_comm]
    _ ≤ ∑ q, ‖(FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)).ofLp q‖ *
          ‖(RN N n x).ofLp q‖ / (1 + a₀) := Finset.sum_le_sum fun q _ => hxq q
    _ = (∑ q, ‖(FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)).ofLp q‖ *
          ‖(RN N n x).ofLp q‖) / (1 + a₀) := by rw [Finset.sum_div]
    _ ≤ _ := by
        gcongr
        exact sum_norm_mul_le _ _

end Endpoint

/-! ## Exponent bookkeeping -/

section Rpow

lemma rpow_half_pow {K : ℝ} (hK : 0 < K) (k : ℕ) :
    K ^ (-(k / 2 : ℝ)) = (K ^ (-(1 / 2 : ℝ))) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]
  congr 1
  ring

lemma rpow_quarter {K : ℝ} (hK : 0 < K) (k : ℕ) :
    (K / 4) ^ (-(k / 2 : ℝ)) = 2 ^ k * (K ^ (-(1 / 2 : ℝ))) ^ k := by
  rw [Real.div_rpow hK.le (by norm_num), rpow_half_pow hK k]
  have h4 : (4 : ℝ) ^ (-(k / 2 : ℝ)) = (2 ^ k)⁻¹ := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    rw [show (2 : ℝ) * -(k / 2 : ℝ) = -(k : ℝ) by ring, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
  rw [h4]
  field_simp

lemma inv_eq_xpow {K : ℝ} (hK : 0 < K) : K⁻¹ = (K ^ (-(1 / 2 : ℝ))) ^ 2 := by
  rw [← rpow_half_pow hK 2]
  norm_num
  rw [Real.rpow_neg_one]

end Rpow

/-! ## The endpoint of the flat elimination -/

section EndpointThm

variable (sys : CoulombSystem eta ν) {L : ℝ} (p₀ : Fin eta) {N : ℕ}

omit [Fintype ν] in
lemma inQ_imp_inP {s : ℝ} (hs : 0 ≤ s) {k : Cf eta} (h : InQ s k) : InP s k := by
  intro c i
  have := abs_coord_le_of_lsq_le (by positivity : (0 : ℝ) ≤ s / 4) (h c) i
  linarith

/-- The constant of the flat endpoint. -/
noncomputable def Cend (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  4 * eta * mmax sys * FSNormal.cE sys L * Real.sqrt (Fintype.card (Ch eta) *
    (∑ j : Ch eta, chC sys L j ^ 2) * (1000 * gF L / 3) * FSChannel.Zs 2) +
  (2 * Real.sqrt 128 + Real.sqrt 2) * CH sys L Hunit * eta ^ 2

omit [Fintype ν] in
lemma PN_eq_QN_add {n : ℕ} (u : En eta N) :
    PN N n u = QN N n u +
      FSKernel.res (fun q : Cfg eta N => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)) u := by
  classical
  ext q
  simp only [FSKernel.res_apply, PiLp.add_apply]
  by_cases hP : InP (n : ℝ) (cidx N q)
  · by_cases hQ : InQ (n : ℝ) (cidx N q)
    · simp [hP, hQ]
    · simp [hP, hQ]
  · have hQ : ¬ InQ (n : ℝ) (cidx N q) := fun h => hP (inQ_imp_inP (Nat.cast_nonneg n) h)
    simp [hP, hQ]

lemma Whc_form_eq (_hL : 0 < L) (n : ℕ) (u : En eta N) :
    ⟪u, Whc sys L p₀ n u⟫_ℂ = ⟪RN N n u, WhN sys L p₀ N (PN N n u)⟫_ℂ +
      ⟪PN N n u, WhN sys L p₀ N (RN N n u)⟫_ℂ + ⟪RN N n u, WhN sys L p₀ N (RN N n u)⟫_ℂ := by
  have hu : u = PN N n u + RN N n u := by rw [RN_eq]; abel
  unfold Whc
  rw [LinearMap.sub_apply, inner_sub_right, LinearMap.comp_apply, LinearMap.comp_apply,
    ← PN_symm n u]
  have e : ⟪u, WhN sys L p₀ N u⟫_ℂ = ⟪PN N n u + RN N n u, WhN sys L p₀ N (PN N n u + RN N n u)⟫_ℂ := by
    rw [← hu]
  rw [e, map_add, inner_add_left, inner_add_right, inner_add_right]
  ring

/-- The bulk-fed piece of the flat endpoint: `|⟨R u, Ŵ Q u⟩| ≤ 2 η m_max c_E √C₁ M² x⁶`. -/
lemma flat_endpoint_bulk (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n) (hK : 4 ≤ gF L * n) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) {x : ℝ} (hx0 : 0 ≤ x)
    (hxdef : x = (gF L * n) ^ (-(1 / 2 : ℝ)))
    (hδ2 : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖ ≤ eta * M * x) :
    ‖⟪RN N n u, WhN sys L p₀ N (QN N n u)⟫_ℂ‖ ≤ 4 * eta * mmax sys * FSNormal.cE sys L *
      Real.sqrt (Fintype.card (Ch eta) * (∑ j : Ch eta, chC sys L j ^ 2) * (1000 * gF L / 3) *
        FSChannel.Zs 2) * M ^ 2 * x ^ 6 / 2 := by
  have hK0 : 0 < gF L * n := by linarith
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := gF_pos hL
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  have h1 := norm_inner_RN_le sys hL n u (WhN sys L p₀ N (QN N n u))
  have h2 := norm_sq_R_kop_Q_le sys hL hn (whK sys L p₀ N) (norm_whK_le sys hL p₀) u
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁ : ℝ, C₁ = Fintype.card (Ch eta) * (∑ j : Ch eta, chC sys L j ^ 2) *
      (1000 * gF L / 3) * FSChannel.Zs 2 := ⟨_, rfl⟩
  rw [← hC₁def]
  have hC₁ : 0 ≤ C₁ := by
    rw [hC₁def]
    have := (FSChannel.Zs_pos (by norm_num : (3 : ℝ) / 2 < 2)).le
    have : 0 ≤ ∑ j : Ch eta, chC sys L j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    positivity
  have hcE := FSNormal.one_le_cE (sys := sys) (L := L)
  have hwt : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖ ≤ M := by
    have := hu.1; have := norm_nonneg u; linarith
  have hx2 : x ^ 2 = 1 / (gF L * n) := by rw [hxdef, ← inv_eq_xpow hK0, one_div]
  have e : (Fintype.card (Ch eta) : ℝ) * ∑ j : Ch eta, chC sys L j ^ 2 * (1000 / (3 * n)) *
      FSChannel.Zs 2 * (FSNormal.cE sys L ^ 2 * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖ ^ 2) =
      C₁ * x ^ 2 * (FSNormal.cE sys L * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖) ^ 2 := by
    rw [hx2, hC₁def, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    field_simp
  rw [e] at h2
  have h3 : ‖RN N n (WhN sys L p₀ N (QN N n u))‖ ≤ Real.sqrt C₁ * x * (FSNormal.cE sys L * M) := by
    have h4 : ‖RN N n (WhN sys L p₀ N (QN N n u))‖ ≤ Real.sqrt C₁ * x *
        (FSNormal.cE sys L * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖) := by
      have h5 := Real.sqrt_le_sqrt h2
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity), Real.sqrt_mul hC₁,
        Real.sqrt_sq hx0, Real.sqrt_sq (by positivity)] at h5
      exact h5
    refine h4.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact mul_le_mul_of_nonneg_left hwt (by positivity)
  have hmm := one_le_mmax sys
  have h5 : 1 / (1 + (gF L * n) ^ 2 / (2 * mmax sys)) ≤ 2 * mmax sys * x ^ 4 := by
    have hx4 : x ^ 4 = 1 / (gF L * n) ^ 2 := by
      rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx2]; field_simp
    rw [hx4, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg (gF L * n)]
  have h6 : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖ *
      ‖RN N n (WhN sys L p₀ N (QN N n u))‖ ≤ (eta * M * x) * (Real.sqrt C₁ * x * (FSNormal.cE sys L * M)) :=
    mul_le_mul hδ2 h3 (norm_nonneg _) (by positivity)
  calc ‖⟪RN N n u, WhN sys L p₀ N (QN N n u)⟫_ℂ‖
      ≤ ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖ * ‖RN N n (WhN sys L p₀ N (QN N n u))‖ /
          (1 + (gF L * n) ^ 2 / (2 * mmax sys)) := h1
    _ = ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖ * ‖RN N n (WhN sys L p₀ N (QN N n u))‖ *
          (1 / (1 + (gF L * n) ^ 2 / (2 * mmax sys))) := by rw [mul_one_div]
    _ ≤ (eta * M * x) * (Real.sqrt C₁ * x * (FSNormal.cE sys L * M)) * (2 * mmax sys * x ^ 4) :=
        mul_le_mul h6 h5 (by positivity) (by positivity)
    _ = _ := by ring

/-- **The endpoint of the flat elimination**: `|⟨u, Ŵ_c u⟩| ≤ C_end M² K⁻³` for a good box state,
`K = g n ≥ 4`. -/
theorem norm_Whc_form_le (hL : 0 < L) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {n : ℕ} (hn : 2 ≤ n) (hK : 4 ≤ gF L * n) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖⟪u, Whc sys L p₀ n u⟫_ℂ‖ ≤ Cend sys L Hunit * M ^ 2 * (gF L * n) ^ (-(3 : ℝ)) := by
  classical
  have hK0 : 0 < gF L * n := by linarith
  have hK1 : 1 ≤ gF L * n := by linarith
  obtain ⟨x, hxdef⟩ : ∃ x, x = (gF L * n) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; exact Real.rpow_nonneg hK0.le _
  have hx1 : x ≤ 1 := by rw [hxdef]; exact Real.rpow_le_one_of_one_le_of_nonpos hK1 (by norm_num)
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hCH := CH_nonneg sys hL Hunit
  -- tails of `δ = R u` and of `φ_r`
  have hδt := res_tails_good sys hu (fun q : Cfg eta N => ¬ InP (n : ℝ) (cidx N q)) hK1 (by
    intro q hq
    obtain ⟨c, hc⟩ := exists_reg_of_not_inP (by positivity) hq
    exact ⟨c, kabs_gt_of_lsq_gt hL (by positivity) q c hc⟩)
  have hK4 : 1 ≤ gF L * n / 4 := by linarith
  have hrt := res_tails_good sys hu
    (fun q : Cfg eta N => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)) hK4 (by
    intro q hq
    obtain ⟨c, hc⟩ := exists_reg_of_not_inQ hq.2
    refine ⟨c, ?_⟩
    have := kabs_gt_of_lsq_gt hL (by positivity : (0 : ℝ) ≤ n / 4) q c hc
    linarith [show gF L * (n / 4) = gF L * n / 4 by ring])
  have e52 : (gF L * n) ^ (-(5 / 2 : ℝ)) = x ^ 5 := by
    have := rpow_half_pow hK0 5; norm_num at this; rw [hxdef]; exact this
  have q52 : (gF L * n / 4) ^ (-(5 / 2 : ℝ)) = 32 * x ^ 5 := by
    have := rpow_quarter hK0 5; norm_num at this; rw [hxdef]; exact this
  have q12 : (gF L * n / 4) ^ (-(1 / 2 : ℝ)) = 2 * x := by
    have := rpow_quarter hK0 1; norm_num at this; rw [hxdef]; exact this
  obtain ⟨hδ1, hδ2⟩ := hδt
  obtain ⟨hr1, hr2⟩ := hrt
  rw [e52] at hδ1
  rw [← hxdef] at hδ2
  rw [q52] at hr1
  rw [q12] at hr2
  -- generic Hardy product: `‖⟨a, Ŵ b⟩‖ ≤ ‖a‖ CH √(2 ‖b‖ ‖(1+A) b‖)`
  have hprod : ∀ a b : En eta N, ‖⟪a, WhN sys L p₀ N b⟫_ℂ‖ ≤
      ‖a‖ * (CH sys L Hunit * Real.sqrt (2 * ‖b‖ * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 b‖)) := by
    intro a b
    refine (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (norm_WhN_le sys hL p₀ Hunit hPeriodic b).trans
      (mul_le_mul_of_nonneg_left (sqrt_wns_le sys b) hCH)
  -- the three pieces
  have hA3 : ‖⟪RN N n u, WhN sys L p₀ N (RN N n u)⟫_ℂ‖ ≤
      Real.sqrt 2 * CH sys L Hunit * eta ^ 2 * M ^ 2 * x ^ 8 := by
    refine (hprod _ _).trans ?_
    have h3 : Real.sqrt (2 * ‖RN N n u‖ * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖) ≤
        Real.sqrt 2 * (eta * M * x ^ 3) := by
      rw [show Real.sqrt 2 * (eta * M * x ^ 3) = Real.sqrt (2 * (eta * M * x ^ 5) * (eta * M * x)) by
        rw [show 2 * (eta * M * x ^ 5) * (eta * M * x) = 2 * (eta * M * x ^ 3) ^ 2 by ring,
          Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by gcongr)
    calc ‖RN N n u‖ * (CH sys L Hunit * Real.sqrt (2 * ‖RN N n u‖ *
          ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖))
        ≤ (eta * M * x ^ 5) * (CH sys L Hunit * (Real.sqrt 2 * (eta * M * x ^ 3))) :=
          mul_le_mul hδ1 (mul_le_mul_of_nonneg_left h3 hCH) (by positivity) (by positivity)
      _ = _ := by ring
  have hA2 : ‖⟪RN N n u, WhN sys L p₀ N (FSKernel.res (fun q : Cfg eta N =>
      InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)) u)⟫_ℂ‖ ≤
      Real.sqrt 128 * CH sys L Hunit * eta ^ 2 * M ^ 2 * x ^ 8 := by
    refine (hprod _ _).trans ?_
    have h3 : Real.sqrt (2 * ‖FSKernel.res (fun q : Cfg eta N =>
        InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)) u‖ *
        ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (FSKernel.res (fun q : Cfg eta N =>
          InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)) u)‖) ≤ Real.sqrt 128 * (eta * M * x ^ 3) := by
      rw [show Real.sqrt 128 * (eta * M * x ^ 3) =
          Real.sqrt (2 * (eta * M * (32 * x ^ 5)) * (eta * M * (2 * x))) by
        rw [show 2 * (eta * M * (32 * x ^ 5)) * (eta * M * (2 * x)) = 128 * (eta * M * x ^ 3) ^ 2 by ring,
          Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by gcongr)
    calc _ ≤ (eta * M * x ^ 5) * (CH sys L Hunit * (Real.sqrt 128 * (eta * M * x ^ 3))) :=
          mul_le_mul hδ1 (mul_le_mul_of_nonneg_left h3 hCH) (by positivity) (by positivity)
      _ = _ := by ring
  have hA1 : ‖⟪RN N n u, WhN sys L p₀ N (QN N n u)⟫_ℂ‖ ≤ 4 * eta * mmax sys * FSNormal.cE sys L *
      Real.sqrt (Fintype.card (Ch eta) * (∑ j : Ch eta, chC sys L j ^ 2) * (1000 * gF L / 3) *
        FSChannel.Zs 2) * M ^ 2 * x ^ 6 / 2 := by
    exact flat_endpoint_bulk sys p₀ hL hn hK hu hx0 hxdef hδ2
  -- assemble
  have hconj : ‖⟪PN N n u, WhN sys L p₀ N (RN N n u)⟫_ℂ‖ =
      ‖⟪RN N n u, WhN sys L p₀ N (PN N n u)⟫_ℂ‖ := by
    rw [← WhN_symm hL (PN N n u) (RN N n u), ← inner_conj_symm, Complex.norm_conj]
  have hsplit : ⟪RN N n u, WhN sys L p₀ N (PN N n u)⟫_ℂ = ⟪RN N n u, WhN sys L p₀ N (QN N n u)⟫_ℂ +
      ⟪RN N n u, WhN sys L p₀ N (FSKernel.res (fun q : Cfg eta N =>
        InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)) u)⟫_ℂ := by
    rw [PN_eq_QN_add, map_add, inner_add_right]
  have hx8 : x ^ 8 ≤ x ^ 6 := pow_le_pow_of_le_one hx0 hx1 (by norm_num)
  have hx6 : x ^ 6 = (gF L * n) ^ (-(3 : ℝ)) := by
    have h6 := rpow_half_pow hK0 6
    have e : -(((6 : ℕ) : ℝ) / 2) = -(3 : ℝ) := by norm_num
    rw [e] at h6
    rw [hxdef]; exact h6.symm
  rw [Whc_form_eq sys p₀ hL n u, ← hx6]
  have h8a : Real.sqrt 128 * CH sys L Hunit * eta ^ 2 * M ^ 2 * x ^ 8 ≤
      Real.sqrt 128 * CH sys L Hunit * eta ^ 2 * M ^ 2 * x ^ 6 :=
    mul_le_mul_of_nonneg_left hx8 (by positivity)
  have h8b : Real.sqrt 2 * CH sys L Hunit * eta ^ 2 * M ^ 2 * x ^ 8 ≤
      Real.sqrt 2 * CH sys L Hunit * eta ^ 2 * M ^ 2 * x ^ 6 :=
    mul_le_mul_of_nonneg_left hx8 (by positivity)
  have htri : ‖⟪RN N n u, WhN sys L p₀ N (PN N n u)⟫_ℂ + ⟪PN N n u, WhN sys L p₀ N (RN N n u)⟫_ℂ +
      ⟪RN N n u, WhN sys L p₀ N (RN N n u)⟫_ℂ‖ ≤ ‖⟪RN N n u, WhN sys L p₀ N (PN N n u)⟫_ℂ‖ +
      ‖⟪PN N n u, WhN sys L p₀ N (RN N n u)⟫_ℂ‖ + ‖⟪RN N n u, WhN sys L p₀ N (RN N n u)⟫_ℂ‖ :=
    norm_add₃_le
  have hs2 := norm_add_le (⟪RN N n u, WhN sys L p₀ N (QN N n u)⟫_ℂ)
    (⟪RN N n u, WhN sys L p₀ N (FSKernel.res (fun q : Cfg eta N =>
      InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)) u)⟫_ℂ)
  rw [← hsplit] at hs2
  rw [hconj] at htri
  unfold Cend
  nlinarith [hA1, hA2, hA3]

end EndpointThm

end FSFlux
