import PlaneWave.FluxBox.BoxCommutator

/-!
# Flux route, stage 2, part 6: tails on the box and the flat elimination

* the tail inventory on the box: a restriction to configurations with a register beyond `l` is
  dominated by the register tails at `l` (`norm_res_le_tails`, `norm_wt_res_le_tails`); good
  states keep goodness under restriction (`isGood_res`);
* **the flat identity** (`flat_comm_eq`): with `φ = P u`, `δ = u - φ`,
  `Re⟨u, i[W_N, Ŵ_c] u⟩ = Re e_bd(u) - Re e_bd(φ) + n^fl(u)`,
  `n^fl(u) = 2 Im⟨W_N δ, P Ŵ_N φ⟩ - 2 Im⟨R W_N φ, R Ŵ_N φ⟩`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Tails on the box -/

section Tails

variable (sys : CoulombSystem eta ν) {L : ℝ} {N : ℕ}

omit [Fintype ν] in
lemma wt_res (S : Cfg eta N → Prop) (v : En eta N) :
    FSSpectral.wt (sb eta N) (Asym sys L N) 1 (FSKernel.res S v) =
      FSKernel.res S (FSSpectral.wt (sb eta N) (Asym sys L N) 1 v) := by
  classical
  ext q
  rw [wt_one_apply, FSKernel.res_apply, FSKernel.res_apply, wt_one_apply]
  split_ifs <;> simp

omit [Fintype ν] in
lemma regTail_res (S : Cfg eta N → Prop) (c : Fin eta) (l : ℝ) (v : En eta N) :
    regTail L c l (FSKernel.res S v) = FSKernel.res S (regTail L c l v) := by
  classical
  ext q
  rw [regTail_apply, FSKernel.res_apply, FSKernel.res_apply, regTail_apply]
  split_ifs <;> simp

omit [Fintype ν] in
/-- A restriction to configurations with a register beyond `l` is dominated by the register tails. -/
lemma norm_res_le_tails (S : Cfg eta N → Prop) {l : ℝ}
    (hS : ∀ q, S q → ∃ c, l < finitePlaneWaveKabs (2 * Real.pi / L) N (q c)) (v : En eta N) :
    ‖FSKernel.res S v‖ ≤ ∑ c : Fin eta, ‖regTail L c l v‖ := by
  classical
  have h2 : ‖FSKernel.res S v‖ ^ 2 ≤ (∑ c : Fin eta, ‖regTail L c l v‖) ^ 2 := by
    refine le_trans ?_ (Finset.sum_sq_le_sq_sum_of_nonneg fun c _ => norm_nonneg _)
    rw [FSKernel.norm_sq_eq]
    simp_rw [FSKernel.norm_sq_eq]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun q _ => ?_
    rw [FSKernel.res_apply]
    split_ifs with hq
    · obtain ⟨c, hc⟩ := hS q hq
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun c => ‖(regTail L c l v).ofLp q‖ ^ 2)
        (fun c _ => sq_nonneg _) (Finset.mem_univ c))
      simp only
      rw [regTail_apply, if_pos hc]
    · rw [norm_zero, sq, mul_zero]
      exact Finset.sum_nonneg fun c _ => sq_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.sum_nonneg fun c _ => norm_nonneg _)
    two_ne_zero).mp h2

omit [Fintype ν] in
lemma norm_wt_res_le_tails (S : Cfg eta N → Prop) {l : ℝ}
    (hS : ∀ q, S q → ∃ c, l < finitePlaneWaveKabs (2 * Real.pi / L) N (q c)) (v : En eta N) :
    ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (FSKernel.res S v)‖ ≤
      ∑ c : Fin eta, ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (regTail L c l v)‖ := by
  rw [wt_res]
  refine (norm_res_le_tails S hS _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [wt_regTail]

omit [Fintype ν] in
/-- The tails of a good state on a set with a register beyond `l ≥ 1`. -/
lemma res_tails_good {M : ℝ} {v : En eta N} (hv : IsGood sys L 1 M v) (S : Cfg eta N → Prop) {l : ℝ}
    (hl : 1 ≤ l) (hS : ∀ q, S q → ∃ c, l < finitePlaneWaveKabs (2 * Real.pi / L) N (q c)) :
    ‖FSKernel.res S v‖ ≤ eta * M * l ^ (-(5 / 2 : ℝ)) ∧
      ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (FSKernel.res S v)‖ ≤
        eta * M * l ^ (-(1 / 2 : ℝ)) := by
  constructor
  · refine (norm_res_le_tails S hS v).trans ?_
    calc ∑ c : Fin eta, ‖regTail L c l v‖ ≤ ∑ _c : Fin eta, M * l ^ (-(5 / 2 : ℝ)) :=
          Finset.sum_le_sum fun c _ => by have := (hv.2 c l hl).1; rwa [one_mul] at this
      _ = eta * M * l ^ (-(5 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · refine (norm_wt_res_le_tails sys S hS v).trans ?_
    calc ∑ c : Fin eta, ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (regTail L c l v)‖
        ≤ ∑ _c : Fin eta, M * l ^ (-(1 / 2 : ℝ)) :=
          Finset.sum_le_sum fun c _ => by have := (hv.2 c l hl).2; rwa [one_mul] at this
      _ = eta * M * l ^ (-(1 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

omit [Fintype ν] in
/-- Restriction keeps a good state good. -/
lemma isGood_res {M : ℝ} {v : En eta N} (hv : IsGood sys L 1 M v) (S : Cfg eta N → Prop) :
    IsGood sys L 1 M (FSKernel.res S v) := by
  refine ⟨?_, fun a l hl => ⟨?_, ?_⟩⟩
  · rw [wt_res]
    have h1 := FSKernel.norm_res_le S v
    have h2 := FSKernel.norm_res_le S (FSSpectral.wt (sb eta N) (Asym sys L N) 1 v)
    linarith [hv.1]
  · rw [regTail_res]
    exact (FSKernel.norm_res_le S _).trans (hv.2 a l hl).1
  · rw [regTail_res, wt_res]
    exact (FSKernel.norm_res_le S _).trans (hv.2 a l hl).2

omit [Fintype ν] in
/-- A configuration outside the cube `s` has a register with `|k_c| > s`. -/
lemma exists_reg_of_not_inP {s : ℝ} (hs : 0 ≤ s) {k : Cf eta} (h : ¬ InP s k) :
    ∃ c, s ^ 2 < FSLattice.lsq (k c) := by
  simp only [InP, not_forall, not_le] at h
  obtain ⟨c, i, hci⟩ := h
  refine ⟨c, ?_⟩
  have h1 := sq_coord_le_lsq (k c) i
  have h2 : s ^ 2 < ((k c i : ℤ) : ℝ) ^ 2 := by
    rw [← sq_abs (((k c i : ℤ) : ℝ))]
    exact pow_lt_pow_left₀ hci hs two_ne_zero
  linarith

omit [Fintype ν] in
/-- A configuration outside the bulk ball `s/4` has a register with `|k_c| > s/4`. -/
lemma exists_reg_of_not_inQ {s : ℝ} {k : Cf eta} (h : ¬ InQ s k) :
    ∃ c, (s / 4) ^ 2 < FSLattice.lsq (k c) := by
  simp only [InQ, not_forall, not_le] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc⟩

omit [Fintype ν] in
/-- `|k_c| > r ≥ 0` in lattice units means `g |k_c| > g r` in physical units. -/
lemma kabs_gt_of_lsq_gt (hL : 0 < L) {r : ℝ} (_hr : 0 ≤ r) (q : Cfg eta N) (c : Fin eta)
    (h : r ^ 2 < FSLattice.lsq (cidx N q c)) :
    gF L * r < finitePlaneWaveKabs (2 * Real.pi / L) N (q c) := by
  have hg := gF_pos hL
  have e := kabs_sq_eq (n := N) L (q c)
  have hk0 := kabs_nonneg (n := N) hL (q c)
  have hgl : gL L = gF L := rfl
  rw [hgl] at e
  have : (gF L * r) ^ 2 < finitePlaneWaveKabs (2 * Real.pi / L) N (q c) ^ 2 := by
    rw [e, mul_pow]
    exact mul_lt_mul_of_pos_left h (by positivity)
  exact lt_of_pow_lt_pow_left₀ 2 hk0 this

end Tails

/-! ## The flat identity -/

section FlatId

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) {N : ℕ} (n : ℕ)

/-- The complement of the cube inside the box. -/
noncomputable abbrev RN (N n : ℕ) : En eta N →ₗ[ℂ] En eta N :=
  FSKernel.res fun q : Cfg eta N => ¬ InP (n : ℝ) (cidx N q)

/-- The boundary flat potential `Ŵ_c = Ŵ - P Ŵ P`. -/
noncomputable def Whc : En eta N →ₗ[ℂ] En eta N :=
  WhN sys L p₀ N - PN N n ∘ₗ WhN sys L p₀ N ∘ₗ PN N n

/-- The flat second-order remainder `n^fl(u) = 2 Im⟨W δ, P Ŵ φ⟩ - 2 Im⟨R W φ, R Ŵ φ⟩`. -/
noncomputable def nfl (u : En eta N) : ℝ :=
  2 * (⟪WN sys L N (u - PN N n u), PN N n (WhN sys L p₀ N (PN N n u))⟫_ℂ).im -
    2 * (⟪RN N n (WN sys L N (PN N n u)), RN N n (WhN sys L p₀ N (PN N n u))⟫_ℂ).im

variable {sys L p₀}

lemma whK_conj (hL : 0 < L) (q p : Cfg eta N) : whK sys L p₀ N p q = conj (whK sys L p₀ N q p) := by
  unfold whK chPart
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  by_cases h : OnCh j (cidx N q) (cidx N p)
  · rw [if_pos (onCh_symm h), if_pos h]
    unfold wNK
    exact potKernel_conj' hL _ _
  · rw [if_neg (fun h' => h (onCh_symm h')), if_neg h, map_zero]

lemma WhN_symm (hL : 0 < L) : (WhN sys L p₀ N).IsSymmetric :=
  FSKernel.kop_symm _ fun q p => whK_conj hL q p

omit [Fintype ν] in
lemma RN_eq (v : En eta N) : RN N n v = v - PN N n v := by
  classical
  ext q
  simp only [FSKernel.res_apply, PiLp.sub_apply]
  split_ifs <;> simp_all

omit [Fintype ν] in
lemma RN_symm : (RN N n : En eta N →ₗ[ℂ] En eta N).IsSymmetric := by
  classical
  intro u v
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [FSKernel.res_apply, Pi.star_apply, RCLike.star_def]
  split_ifs <;> simp

omit [Fintype ν] in
lemma RN_idem (v : En eta N) : RN N n (RN N n v) = RN N n v := by
  classical
  ext q
  simp only [FSKernel.res_apply]
  split_ifs <;> simp

omit [Fintype ν] in
lemma PN_idem (v : En eta N) : PN N n (PN N n v) = PN N n v := by
  classical
  ext q
  simp only [FSKernel.res_apply]
  split_ifs <;> simp

lemma re_I_sub (z : ℂ) : (Complex.I * z - Complex.I * conj z).re = -2 * z.im := by
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma ebd_re (hL : 0 < L) (v : En eta N) :
    (ebd sys L p₀ v).re = -2 * (⟪WN sys L N v, WhN sys L p₀ N v⟫_ℂ).im := by
  unfold ebd
  rw [LinearMap.smul_apply, inner_smul_right, LinearMap.sub_apply, inner_sub_right,
    LinearMap.comp_apply, LinearMap.comp_apply, ← WN_symm v (WhN sys L p₀ N v),
    ← WhN_symm hL v (WN sys L N v), ← inner_conj_symm (WhN sys L p₀ N v) (WN sys L N v), mul_sub]
  exact re_I_sub _

/-- **The flat identity**:
`Re⟨u, i[W_N, Ŵ_c] u⟩ = Re e_bd(u) - Re e_bd(φ) + n^fl(u)`. -/
theorem flat_comm_eq (hL : 0 < L) (u : En eta N) :
    (⟪u, (Complex.I • (WN sys L N ∘ₗ Whc sys L p₀ n - Whc sys L p₀ n ∘ₗ WN sys L N)) u⟫_ℂ).re =
      (ebd sys L p₀ u).re - (ebd sys L p₀ (PN N n u)).re + nfl sys L p₀ n u := by
  set W := WN sys L N
  set Wh := WhN sys L p₀ N
  set P := PN N n
  set R := RN N n
  set φ := P u
  set δ := u - φ
  have hW := (WN_symm : W.IsSymmetric)
  have hWh : Wh.IsSymmetric := WhN_symm hL
  have hP : P.IsSymmetric := PN_symm n
  -- step 1: split off `[W, Ŵ]`
  have h1 : (⟪u, (Complex.I • (W ∘ₗ Whc sys L p₀ n - Whc sys L p₀ n ∘ₗ W)) u⟫_ℂ).re =
      (ebd sys L p₀ u).re - (Complex.I * ⟪W u, P (Wh φ)⟫_ℂ -
        Complex.I * conj ⟪W u, P (Wh φ)⟫_ℂ).re := by
    unfold Whc ebd
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
      inner_smul_right, inner_sub_right, mul_sub, Complex.sub_re]
    have e1 : ⟪u, W (P (Wh (P u)))⟫_ℂ = ⟪W u, P (Wh φ)⟫_ℂ := by rw [← hW]
    have e2 : ⟪u, P (Wh (P (W u)))⟫_ℂ = conj ⟪W u, P (Wh φ)⟫_ℂ := by
      rw [inner_conj_symm, ← hP u, ← hWh (P u), ← hP]
    rw [e1, e2]
    ring
  rw [h1, re_I_sub]
  -- step 2: `u = φ + δ`
  have hu : u = φ + δ := by simp only [δ]; abel
  have h2 : ⟪W u, P (Wh φ)⟫_ℂ = ⟪W φ, Wh φ⟫_ℂ - ⟪R (W φ), R (Wh φ)⟫_ℂ + ⟪W δ, P (Wh φ)⟫_ℂ := by
    have e3 : ⟪W φ, P (Wh φ)⟫_ℂ = ⟪W φ, Wh φ⟫_ℂ - ⟪R (W φ), R (Wh φ)⟫_ℂ := by
      have e4 : P (Wh φ) = Wh φ - R (Wh φ) := by rw [RN_eq]; abel
      rw [e4, inner_sub_right]
      congr 1
      rw [RN_symm n (W φ) (R (Wh φ)), RN_idem]
    conv_lhs => rw [hu]
    rw [map_add, inner_add_left, e3]
  rw [h2, ebd_re hL u, ebd_re hL φ]
  show _ = _ - _ + (2 * (⟪W δ, P (Wh φ)⟫_ℂ).im - 2 * (⟪R (W φ), R (Wh φ)⟫_ℂ).im)
  simp only [Complex.add_im, Complex.sub_im]
  ring

end FlatId

end FSFlux
