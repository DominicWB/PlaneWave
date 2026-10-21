import PlaneWave.FluxBox.FlatLedger

/-!
# Flux route, stage 2, part 8: long hops and the flat endpoint

* `ub_good`: the box state along the trajectory is good, with budget `2 c_tr Ξ`;
* `sum_longhop_le`: Young on fibres for hops of length `> R`:
  `Σ_{y ∈ T} (Σ_{x ∈ D} a(x) M(y, x))² ≤ #Ch Σ_j c_j² (250/R) Z₂ Σ_x (1 + |x_{lead}|²)² a(x)²`;
* `norm_R_kop_Q_le`: a majorant-dominated kernel from the bulk ball `Q` out of the cube has
  `‖R κ Q v‖² ≤ (C/n) ‖(1+A) v‖²` (hops of length `> 3n/4`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Good

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hL hKernel in
/-- The box state along the trajectory is good, with budget `2 c_tr Ξ`. -/
lemma ub_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (N : ℕ) (s : ℝ) :
    IsGood sys L 1 (2 * (cTr sys L Hunit * D.Xi)) (ub H D N s) := by
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D s
  have hw : traj H D s = w := traj_eq H D s w hw1
  rw [ub_eq, hw]
  exact ext_good sys hF

end Good

section LongHop

variable (sys : CoulombSystem eta ν) {L : ℝ}

open Classical in
/-- **Young on fibres for long hops.** -/
theorem sum_longhop_le (hL : 0 < L) {R : ℝ} (hR : 1 ≤ R) (D T : Finset (Cf eta)) (a : Cf eta → ℝ)
    (hlong : ∀ y ∈ T, ∀ x ∈ D, ∀ j, OnCh j y x → a x ≠ 0 →
      R ^ 2 < FSLattice.lsq (y (lead j) - x (lead j))) :
    ∑ y ∈ T, (∑ x ∈ D, a x * potMaj sys L y x) ^ 2 ≤
      Fintype.card (Ch eta) * ∑ j, chC sys L j ^ 2 * (250 / R) * FSChannel.Zs 2 *
        ∑ x ∈ D, (1 + FSLattice.lsq (x (lead j))) ^ 2 * a x ^ 2 := by
  set kt : Ch eta → Lattice3 → ℝ := fun j θ =>
    if R ^ 2 < FSLattice.lsq θ then chC sys L j / FSLattice.lsq θ else 0
  set b : Ch eta → Cf eta → ℝ := fun j y =>
    ∑ x ∈ D, a x * (if OnCh j y x then kt j (y (lead j) - x (lead j)) else 0)
  have hdec : ∀ y ∈ T, ∑ x ∈ D, a x * potMaj sys L y x = ∑ j, b j y := by
    intro y hy
    unfold potMaj
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x hx => ?_
    unfold chMaj
    by_cases ha : a x = 0
    · rw [ha, zero_mul, zero_mul]
    by_cases h : OnCh j y x
    · rw [if_pos h, if_pos h]
      simp only [kt]
      rw [if_pos (hlong y hy x hx j h ha)]
      rfl
    · rw [if_neg h, if_neg h]
  have hcs : ∀ y ∈ T, (∑ x ∈ D, a x * potMaj sys L y x) ^ 2 ≤
      (Fintype.card (Ch eta) : ℝ) * ∑ j, b j y ^ 2 := by
    intro y hy
    rw [hdec y hy]
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => b j y)
    rwa [Finset.card_univ] at h1
  have hkt0 : ∀ j θ, 0 ≤ kt j θ := fun j θ => by
    simp only [kt]; split_ifs
    · exact div_nonneg (chC_nonneg sys hL j) (FSLattice.lsq_nonneg θ)
    · exact le_rfl
  have hY : ∀ j, ∑ y ∈ T, b j y ^ 2 ≤ chC sys L j ^ 2 * (250 / R) * FSChannel.Zs 2 *
      ∑ x ∈ D, (1 + FSLattice.lsq (x (lead j))) ^ 2 * a x ^ 2 := fun j =>
    lattice_fibre_sq_le j (kt j) (hkt0 j) (fun S => sum_coul_sq_tail_le (chC sys L j) hR S) D T a
  calc ∑ y ∈ T, (∑ x ∈ D, a x * potMaj sys L y x) ^ 2
      ≤ ∑ y ∈ T, (Fintype.card (Ch eta) : ℝ) * ∑ j, b j y ^ 2 := Finset.sum_le_sum hcs
    _ = (Fintype.card (Ch eta) : ℝ) * ∑ j, ∑ y ∈ T, b j y ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := by
        gcongr with j
        exact hY j

end LongHop

/-! ## Hop lengths, weights, the bulk-to-outside output -/

section Box

variable (sys : CoulombSystem eta ν) {L : ℝ} {N : ℕ}

/-- The bulk ball `Q` inside the box. -/
noncomputable abbrev QN (N n : ℕ) : En eta N →ₗ[ℂ] En eta N :=
  FSKernel.res fun q : Cfg eta N => InQ (n : ℝ) (cidx N q)

omit [Fintype ν] in
lemma abs_coord_le_of_lsq_le {k : Lattice3} {a : ℝ} (ha : 0 ≤ a) (h : FSLattice.lsq k ≤ a ^ 2)
    (i : Fin 3) : |((k i : ℤ) : ℝ)| ≤ a := by
  have h1 := sq_coord_le_lsq k i
  rw [← Real.sqrt_sq (abs_nonneg _), sq_abs, ← Real.sqrt_sq ha]
  exact Real.sqrt_le_sqrt (h1.trans h)

omit [Fintype ν] in
/-- A hop from a configuration with all coordinates `≤ a` to one with a coordinate `> b ≥ a` has
`|θ| > b - a`. -/
lemma hop_lsq_gt {j : Ch eta} {x y : Cf eta} {a b : ℝ} (hab : a ≤ b)
    (hx : ∀ c i, |((x c i : ℤ) : ℝ)| ≤ a) (hy : ∃ c i, b < |((y c i : ℤ) : ℝ)|) (h : OnCh j y x) :
    (b - a) ^ 2 < FSLattice.lsq (y (lead j) - x (lead j)) := by
  obtain ⟨c, i, hci⟩ := hy
  have e : y = x + tr j (y (lead j) - x (lead j)) := h
  set θ := y (lead j) - x (lead j)
  have h1 : y c i = x c i + tr j θ c i := by rw [e]; simp
  have h2 := abs_tr_le j θ c i
  have h3 := sq_coord_le_lsq θ i
  have h5 := hx c i
  rw [h1, Int.cast_add] at hci
  have h6 : b - a < |((θ i : ℤ) : ℝ)| := by
    have := abs_add_le ((x c i : ℤ) : ℝ) ((tr j θ c i : ℤ) : ℝ)
    linarith
  have h7 : (b - a) ^ 2 < ((θ i : ℤ) : ℝ) ^ 2 := by
    rw [← sq_abs (((θ i : ℤ) : ℝ))]
    exact pow_lt_pow_left₀ h6 (by linarith) two_ne_zero
  linarith

omit [Fintype ν] in
lemma lprof_ne_zero {v : En eta N} {x : Cf eta} (h : lprof v x ≠ 0) :
    ∃ q, cidx N q = x ∧ v.ofLp q ≠ 0 := by
  unfold lprof at h
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  by_cases hc : cidx N q = x
  · rw [if_pos hc] at hq
    exact ⟨q, hc, norm_ne_zero_iff.mp hq⟩
  · rw [if_neg hc] at hq; exact absurd rfl hq

omit [Fintype ν] in
open Classical in
/-- `‖R κ Q v‖²` as a lattice sum. -/
lemma norm_sq_R_kop_le (n : ℕ) (κ : Cfg eta N → Cfg eta N → ℂ) (M : Cf eta → Cf eta → ℝ)
    (hκ : ∀ q p, ‖κ q p‖ ≤ M (cidx N q) (cidx N p)) (v : En eta N) :
    ‖RN N n (FSKernel.kop κ v)‖ ^ 2 ≤
      ∑ y ∈ (fourierConfigCube eta N).filter (fun y => ¬ InP (n : ℝ) y),
        (∑ x ∈ fourierConfigCube eta N, lprof v x * M y x) ^ 2 := by
  classical
  rw [FSKernel.norm_sq_eq, Finset.sum_filter]
  rw [← sum_cfg_eq_sum_cube N (fun y => if ¬ InP (n : ℝ) y then
    (∑ x ∈ fourierConfigCube eta N, lprof v x * M y x) ^ 2 else 0)]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [FSKernel.res_apply]
  by_cases h : InP (n : ℝ) (cidx N q)
  · simp only [h, not_true_eq_false, if_false, norm_zero]
    norm_num
  · simp only [h, not_false_eq_true, if_true]
    rw [FSKernel.kop_apply, ← sum_cfg_eq_sum_cube N (fun x => lprof v x * M (cidx N q) x)]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_mul, lprof_cidx]
    exact mul_le_mul_of_nonneg_left (hκ q p) (norm_nonneg _)

open Classical in
/-- **Bulk-to-outside output**: for a majorant-dominated kernel and `n ≥ 2`,
`‖R κ Q v‖² ≤ #Ch Σ_j c_j² (1000/(3n)) Z₂ c_E² ‖(1+A) v‖²`. -/
theorem norm_sq_R_kop_Q_le (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n) (κ : Cfg eta N → Cfg eta N → ℂ)
    (hκ : ∀ q p, ‖κ q p‖ ≤ potMaj sys L (cidx N q) (cidx N p)) (v : En eta N) :
    ‖RN N n (FSKernel.kop κ (QN N n v))‖ ^ 2 ≤
      Fintype.card (Ch eta) * ∑ j : Ch eta, chC sys L j ^ 2 * (1000 / (3 * n)) * FSChannel.Zs 2 *
        (FSNormal.cE sys L ^ 2 * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 v‖ ^ 2) := by
  classical
  have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : (1 : ℝ) ≤ 3 * n / 4 := by linarith
  refine (norm_sq_R_kop_le n κ (potMaj sys L) hκ (QN N n v)).trans ?_
  have hlong : ∀ y ∈ (fourierConfigCube eta N).filter (fun y => ¬ InP (n : ℝ) y),
      ∀ x ∈ fourierConfigCube eta N, ∀ j, OnCh j y x → lprof (QN N n v) x ≠ 0 →
        (3 * n / 4) ^ 2 < FSLattice.lsq (y (lead j) - x (lead j)) := by
    intro y hy x _ j hj hx
    obtain ⟨q, rfl, hq⟩ := lprof_ne_zero hx
    rw [FSKernel.res_apply] at hq
    split_ifs at hq with hQ
    · have hyP : ¬ InP (n : ℝ) y := (Finset.mem_filter.mp hy).2
      simp only [InP, not_forall, not_le] at hyP
      have hxa : ∀ c i, |((cidx N q c i : ℤ) : ℝ)| ≤ (n : ℝ) / 4 := fun c i =>
        abs_coord_le_of_lsq_le (by positivity) (hQ c) i
      have := hop_lsq_gt (by linarith : (n : ℝ) / 4 ≤ n) hxa hyP hj
      have e : (n : ℝ) - n / 4 = 3 * n / 4 := by ring
      rwa [e] at this
    · exact absurd rfl hq
  refine (sum_longhop_le sys hL hR _ _ _ hlong).trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity)
  have e : (250 : ℝ) / (3 * n / 4) = 1000 / (3 * n) := by field_simp; ring
  rw [e]
  have hZ : 0 ≤ FSChannel.Zs 2 := (FSChannel.Zs_pos (by norm_num)).le
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← sum_cfg_eq_sum_cube N (fun x => (1 + FSLattice.lsq (x (lead j))) ^ 2 * lprof (QN N n v) x ^ 2)]
  refine le_trans (Finset.sum_le_sum fun q _ => ?_) (sum_lead_weight_le sys hL j v)
  rw [lprof_cidx, FSKernel.res_apply]
  split_ifs
  · exact le_rfl
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

end Box

end FSFlux
