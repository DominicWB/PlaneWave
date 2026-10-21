import PlaneWave.FluxBox.FarColdHops

/-!
# Flux route, stage 3, part 28: the first hops from cold, and line squares of hops

A Coulomb hop of `j` from a cold configuration is split by its length at `τ₀ = c_* n`:
`|w_j(d,b)| ≤ W^L_j(d,b) + W^S_j(d,b)` (`norm_wj_le_split`).

* the long part is dominated on the `j`-lines by `κ^L(d) = c_j c_*⁻²/max(n², |ζ(d)|²)`
  (`WL_le_kappa`), with line sums `Σ (κ^L)² ≤ (c_j/c_*²)² 277/n` (`sum_kappaL_sq_le`);
* the short part lives on the short ball (`WS_supp`) and has columns `≤ 26 c_* n c_j`
  (`sum_WS_col_le`), so `L²_j(W^S_j x) ≤ (26 c_* n c_j)² L²_j(x)` on its own lines
  (`lineSq_WS_same_le`), and `L²_{j'}(W^S_j x) ≤ c_j² H² L²_{j'}(x; 1 + |ξ|²)` across (TH,
  `lineSq_WS_cross_le`);
* line squares are monotone and quadratic (`lineSq_mono`, `lineSq_smul`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Line squares: monotone and quadratic -/

section LineSqBasic

variable {N : ℕ}

omit [Fintype ν] in
open Classical in
lemma lineSum_mono (j : Ch eta) {v v' : Cfg eta N → ℝ} (h : ∀ p, v p ≤ v' p) (t : Cf eta) :
    lineSum j v t ≤ lineSum j v' t := by
  unfold lineSum
  exact Finset.sum_le_sum fun p _ => h p

omit [Fintype ν] in
lemma lineSq_mono (j : Ch eta) {Ω : Cf eta → ℝ} (hΩ : ∀ t, 0 ≤ Ω t) {v v' : Cfg eta N → ℝ}
    (hv : ∀ p, 0 ≤ v p) (h : ∀ p, v p ≤ v' p) : lineSq j Ω v ≤ lineSq j Ω v' := by
  unfold lineSq
  refine Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_ (hΩ t)
  exact pow_le_pow_left₀ (lineSum_nonneg j hv t) (lineSum_mono j h t) 2

omit [Fintype ν] in
open Classical in
lemma lineSq_smul (j : Ch eta) (Ω : Cf eta → ℝ) (c : ℝ) (v : Cfg eta N → ℝ) :
    lineSq j Ω (fun p => c * v p) = c ^ 2 * lineSq j Ω v := by
  unfold lineSq lineSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum]
  ring

omit [Fintype ν] in
lemma lineSq_weight_mono (j : Ch eta) {Ω Ω' : Cf eta → ℝ} (h : ∀ t, Ω t ≤ Ω' t)
    (v : Cfg eta N → ℝ) : lineSq j Ω v ≤ lineSq j Ω' v := by
  unfold lineSq
  exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_right (h t) (sq_nonneg _)

end LineSqBasic

/-! ## The first hops from cold -/

section FirstHops

variable (sys : CoulombSystem eta ν) (L : ℝ) (N n : ℕ)

open Classical in
/-- The long part (`|θ| ≥ c_* n`) of a Coulomb hop of `j` from cold. -/
noncomputable def WL (j : Ch eta) (d b : Cfg eta N) : ℝ :=
  if OnCh j (cidx N d) (cidx N b) ∧ InC (n : ℝ) (cst sys) (cidx N b) ∧
    (cst sys * n) ^ 2 ≤ FSLattice.lsq (chT N j d b) then
    chC sys L j / FSLattice.lsq (chT N j d b) else 0

open Classical in
/-- The short part (`|θ| < c_* n`) of a Coulomb hop of `j` from cold. -/
noncomputable def WS (j : Ch eta) (d b : Cfg eta N) : ℝ :=
  if OnCh j (cidx N d) (cidx N b) ∧ InC (n : ℝ) (cst sys) (cidx N b) ∧
    FSLattice.lsq (chT N j d b) < (cst sys * n) ^ 2 then
    chC sys L j / FSLattice.lsq (chT N j d b) else 0

/-- The line majorant of the long part: `κ^L(d) = c_j c_*⁻²/max(n², |ζ(d)|²)`. -/
noncomputable def kappaL (A : Finset (Fin eta)) (j : Ch eta) (d : Cfg eta N) : ℝ :=
  chC sys L j * (1 / cst sys ^ 2) / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d)))

variable {sys L N n}

lemma WL_nonneg (hL : 0 < L) (j : Ch eta) (d b : Cfg eta N) : 0 ≤ WL sys L N n j d b := by
  unfold WL
  split_ifs
  · exact div_nonneg (chC_nonneg sys hL j) (FSLattice.lsq_nonneg _)
  · exact le_rfl

lemma WS_nonneg (hL : 0 < L) (j : Ch eta) (d b : Cfg eta N) : 0 ≤ WS sys L N n j d b := by
  unfold WS
  split_ifs
  · exact div_nonneg (chC_nonneg sys hL j) (FSLattice.lsq_nonneg _)
  · exact le_rfl

/-- **The split of a Coulomb hop from cold**: `|w_j(d,b)| ≤ W^L_j(d,b) + W^S_j(d,b)`. -/
lemma norm_wj_le_split (hL : 0 < L) (j : Ch eta) {d b : Cfg eta N}
    (hb : InC (n : ℝ) (cst sys) (cidx N b)) :
    ‖wj sys L N j d b‖ ≤ WL sys L N n j d b + WS sys L N n j d b := by
  have h := norm_wj_le (sys := sys) hL j d b
  unfold WL WS
  by_cases hj : OnCh j (cidx N d) (cidx N b)
  · rw [if_pos hj] at h
    by_cases hl : (cst sys * n) ^ 2 ≤ FSLattice.lsq (chT N j d b)
    · rw [if_pos ⟨hj, hb, hl⟩, if_neg (fun h => absurd h.2.2 (not_lt.mpr hl)), add_zero]
      exact h
    · rw [if_neg (fun h => hl h.2.2), if_pos ⟨hj, hb, not_le.mp hl⟩, zero_add]
      exact h
  · rw [if_neg hj] at h
    have : ‖wj sys L N j d b‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [this]
    have h1 := WL_nonneg (sys := sys) (N := N) (n := n) hL j d b
    have h2 := WS_nonneg (sys := sys) (N := N) (n := n) hL j d b
    unfold WL at h1
    unfold WS at h2
    linarith

lemma kappaL_nonneg (hL : 0 < L) (A : Finset (Fin eta)) (j : Ch eta) (d : Cfg eta N) :
    0 ≤ kappaL sys L N n A j d := by
  unfold kappaL
  have := chC_nonneg sys hL j
  have := FSLattice.lsq_nonneg (regSum A (cidx N d))
  apply div_nonneg (by positivity)
  exact le_trans (sq_nonneg _) (le_max_left _ _)

/-- **The long part on the lines**: `W^L_j(d,b) ≤ κ^L(d)` on the `j`-lines. -/
lemma WL_le_kappa (hL : 0 < L) (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ}
    (hA : IsCoord j A ε) (d b : Cfg eta N) :
    WL sys L N n j d b ≤ if lab N j d = lab N j b then kappaL sys L N n A j d else 0 := by
  unfold WL
  split_ifs with h1 h2 h2
  · have hk := kappa_long hn hA h1.2.1 h1.1 h1.2.2
    unfold kappaL
    have hc := chC_nonneg sys hL j
    calc chC sys L j / FSLattice.lsq (chT N j d b) = chC sys L j * (1 / FSLattice.lsq (chT N j d b)) := by
          ring
      _ ≤ chC sys L j * ((1 / cst sys ^ 2) / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d)))) :=
          mul_le_mul_of_nonneg_left hk hc
      _ = _ := by ring
  · exact absurd (lab_eq_iff.mpr h1.1) h2
  · exact kappaL_nonneg hL A j d
  · exact le_rfl

open Classical in
/-- **The line sums of `(κ^L)²`**: `≤ (c_j/c_*²)² 277/n`. -/
lemma sum_kappaL_sq_le (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    (q : Cfg eta N) :
    ∑ d ∈ Finset.univ.filter (fun d => lab N j d = lab N j q), kappaL sys L N n A j d ^ 2 ≤
      (chC sys L j * (1 / cst sys ^ 2)) ^ 2 * (277 / n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := lineSum_inv_max_sq_le hA q hn1 0
  simp only [sub_zero] at h
  unfold kappaL
  have e : ∀ d ∈ Finset.univ.filter (fun d => lab N j d = lab N j q),
      (chC sys L j * (1 / cst sys ^ 2) / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d)))) ^ 2 =
      (chC sys L j * (1 / cst sys ^ 2)) ^ 2 *
        (1 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N d))) ^ 2) := by
    intro d _; ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- The short part lives on the short ball and on the `j`-lines. -/
lemma WS_supp {j : Ch eta} {d b : Cfg eta N} (h : WS sys L N n j d b ≠ 0) :
    SB sys N n d ∧ lab N j d = lab N j b := by
  unfold WS at h
  by_contra hc
  apply h
  rw [if_neg]
  intro h'
  exact hc ⟨SB_of_short h'.2.1 h'.1 h'.2.2, lab_eq_iff.mpr h'.1⟩

open Classical in
/-- **The columns of the short part**: `Σ_d W^S_j(d,b) ≤ 26 c_* n c_j`. -/
lemma sum_WS_col_le (hL : 0 < L) (j : Ch eta) (b : Cfg eta N) :
    ∑ d, WS sys L N n j d b ≤ 26 * (cst sys * n) * chC sys L j := by
  classical
  set T := Finset.univ.filter (fun d : Cfg eta N => OnCh j (cidx N d) (cidx N b) ∧
    InC (n : ℝ) (cst sys) (cidx N b) ∧ FSLattice.lsq (chT N j d b) < (cst sys * n) ^ 2)
  have e : ∑ d, WS sys L N n j d b = ∑ d ∈ T, chC sys L j / FSLattice.lsq (chT N j d b) := by
    rw [Finset.sum_filter]; rfl
  rw [e]
  have hinj : Set.InjOn (fun d => chT N j d b) T := fun d hd d' hd' h =>
    chT_injOn j b (Finset.mem_filter.mp hd).2.1 (Finset.mem_filter.mp hd').2.1 h
  rw [← Finset.sum_image (f := fun θ => chC sys L j / FSLattice.lsq θ) hinj]
  have hc := chC_nonneg sys hL j
  have h1 : ∑ θ ∈ T.image (fun d => chT N j d b), chC sys L j / FSLattice.lsq θ =
      chC sys L j * ∑ θ ∈ T.image (fun d => chT N j d b), 1 / FSLattice.lsq θ := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun θ _ => ?_; ring
  rw [h1, mul_comm (26 * (cst sys * n))]
  apply mul_le_mul_of_nonneg_left _ hc
  -- the image is in the ball of radius `c_* n`; zero contributes nothing
  obtain ⟨M, hM⟩ := FSLattice.exists_box (T.image fun d => chT N j d b)
  have hR : (0 : ℝ) ≤ cst sys * n := cst_mul_nonneg
  calc ∑ θ ∈ T.image (fun d => chT N j d b), 1 / FSLattice.lsq θ ≤
      ∑ θ ∈ (FSLattice.box M).filter (fun θ => θ ≠ 0 ∧ FSLattice.lsq θ ≤ (cst sys * n) ^ 2),
        1 / FSLattice.lsq θ := by
        have e2 : ∑ θ ∈ T.image (fun d => chT N j d b), 1 / FSLattice.lsq θ =
            ∑ θ ∈ (T.image (fun d => chT N j d b)).filter (fun θ => θ ≠ 0), 1 / FSLattice.lsq θ := by
          refine (Finset.sum_filter_of_ne fun θ _ h => ?_).symm
          intro h0; apply h; rw [h0]; simp [FSLattice.lsq]
        rw [e2]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro θ hθ
          rw [Finset.mem_filter] at hθ ⊢
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hθ.1
          exact ⟨hM hθ.1, hθ.2, ((Finset.mem_filter.mp hd).2.2.2).le⟩
        · intro θ _ _; exact div_nonneg zero_le_one (FSLattice.lsq_nonneg θ)
    _ ≤ 26 * (cst sys * n) := FSLattice.sum_inv_lsq_ball_le' hR M

end FirstHops

/-! ## Line squares of the short hops -/

section ShortLines

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

/-- **The short hop on its own lines**: `L²_j(W^S_j x; Ω) ≤ (26 c_* n c_j)² L²_j(x; Ω)`. -/
lemma lineSq_WS_same_le (hL : 0 < L) (j : Ch eta) {Ω : Cf eta → ℝ} (hΩ : ∀ t, 0 ≤ Ω t)
    (x : Cfg eta N → ℝ) (hx : ∀ p, 0 ≤ x p) :
    lineSq j Ω (fun d => ∑ b, WS sys L N n j d b * x b) ≤
      (26 * (cst sys * n) * chC sys L j) ^ 2 * lineSq j Ω x :=
  lineSq_conv_le j hΩ _ (WS_nonneg hL j) x hx (fun _ _ h => (WS_supp h).2)
    (sum_WS_col_le hL j)

/-- **The short hop across the lines** (transverse Hardy):
`L²_{j'}(W^S_j x) ≤ c_j² H² L²_{j'}(x; 1 + |ξ|²)`, `ξ` a coordinate of `j` killed by `j'`. -/
lemma lineSq_WS_cross_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) {j j' : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    (hAj' : ∀ σ, regSum A (tr j' σ) = 0) (x : Cfg eta N → ℝ) (hx : ∀ p, 0 ≤ x p) :
    lineSq j' (fun _ => 1) (fun d => ∑ b, WS sys L N n j d b * x b) ≤
      chC sys L j ^ 2 * (Hunit ^ 2 * lineSq j' (fun s => 1 + FSLattice.lsq (regSum A s)) x) := by
  classical
  have hc := chC_nonneg sys hL j
  have hpt : ∀ d, ∑ b, WS sys L N n j d b * x b ≤
      chC sys L j * ∑ b, (if OnCh j (cidx N d) (cidx N b) then
        x b / FSLattice.lsq (chT N j d b) else 0) := by
    intro d
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    unfold WS
    split_ifs with h1 h2
    · rw [div_mul_eq_mul_div, mul_div_assoc]
    · exact absurd h1.1 h2
    · rw [zero_mul]; exact mul_nonneg hc (div_nonneg (hx b) (FSLattice.lsq_nonneg _))
    · rw [zero_mul, mul_zero]
  have hv0 : ∀ d, 0 ≤ ∑ b, WS sys L N n j d b * x b := fun d =>
    Finset.sum_nonneg fun b _ => mul_nonneg (WS_nonneg hL j d b) (hx b)
  have h1 := lineSq_mono j' (fun _ => zero_le_one) hv0 hpt
  rw [lineSq_smul] at h1
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left (lineSq_hop_le hH hA hAj' x hx) (sq_nonneg _)

omit [Fintype ν] in
open Classical in
/-- `Σ_{p on the j-line of q} 1/max(n², |ζ_p|²)⁴ ≤ 277/n⁵`. -/
lemma lineSum_inv_max_four_le (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ}
    (hA : IsCoord j A ε) (q : Cfg eta N) :
    ∑ p ∈ Finset.univ.filter (fun p => lab N j p = lab N j q),
      1 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N p))) ^ 4 ≤ 277 / (n : ℝ) ^ 5 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := lineSum_inv_max_sq_le hA q hn1 0
  simp only [sub_zero] at h
  have hpt : ∀ p ∈ Finset.univ.filter (fun p => lab N j p = lab N j q),
      1 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N p))) ^ 4 ≤
        1 / (n : ℝ) ^ 4 * (1 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N p))) ^ 2) := by
    intro p _
    set M := max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N p)))
    have hM : (n : ℝ) ^ 2 ≤ M := le_max_left _ _
    have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
    rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    have : (n : ℝ) ^ 4 ≤ M ^ 2 := by
      rw [show (n : ℝ) ^ 4 = ((n : ℝ) ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ (by positivity) hM 2
    nlinarith [sq_nonneg M]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  calc 1 / (n : ℝ) ^ 4 * ∑ p ∈ Finset.univ.filter (fun p => lab N j p = lab N j q),
        1 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N p))) ^ 2 ≤ 1 / (n : ℝ) ^ 4 * (277 / n) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 277 / (n : ℝ) ^ 5 := by field_simp

end ShortLines

end FSFlux
