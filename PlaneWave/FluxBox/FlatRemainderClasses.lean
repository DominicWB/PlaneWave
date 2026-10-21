import PlaneWave.FluxBox.FlatEndpoint

/-!
# Flux route, stage 2, part 10: the classes of the flat remainder

Regions inside the box (all registers): the cube `P`, the bulk ball `Q`, the **cold ball**
`C` (every register at most `c_* n`, `c_*² = 1/(64 (η+1) m_max)`, so `C ⊂ Q`), the warm shell
`Wm = Q ∖ C`, and `F' = P ∖ Q`.

* `whK_eq_lam`: on a channel `j`, `ŵ = λ_j w`;
* `wNK_whK_comm` (the `Q × Q` structure, via `same_channel`): for `q, q' ∈ Q` and `r ∉ P`,
  `w(q, r) ŵ(r, q') = ŵ(q, r) w(r, q')`; hence `⟨R W v, R Ŵ v⟩` is real for `v = Q u`
  (`inner_RW_RWh_Q`);
* **`nfl_split`**: `n^fl(u) = n^{FC}(u) + n^{rr}(u)`, with the far–cold part
  `n^{FC} = 2 Im⟨W δ, P Ŵ u_C⟩ - 2 Im⟨R W u_C, R Ŵ u_{F'}⟩ - 2 Im⟨R W u_{F'}, R Ŵ u_C⟩`
  (to the third elimination round) and the restricted part `n^{rr}`;
* **`norm_nflRR_le`**: `|n^{rr}(u)| ≤ 16 C_H² η² c_*⁻³ M² K⁻³` for a good box state
  (every factor carries a register beyond `c_* n`: Hardy with the tails at `c_* K`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The cold ball -/

section Cold

/-- The cold ball of radius `c s`: every register of Euclidean length at most `c s`. -/
def InC (s c : ℝ) (k : Cf eta) : Prop := ∀ a, FSLattice.lsq (k a) ≤ (c * s) ^ 2

variable (sys : CoulombSystem eta ν)

/-- The cold radius `c_* = 1/(32 √((η+1) m_max))`. -/
noncomputable def cst : ℝ := 1 / (32 * Real.sqrt ((eta + 1) * mmax sys))

omit [Fintype ν] in
lemma one_le_etam : 1 ≤ ((eta : ℝ) + 1) * mmax sys := by
  have h1 := one_le_mmax sys
  have h2 : (1 : ℝ) ≤ eta + 1 := by have := Nat.cast_nonneg (α := ℝ) eta; linarith
  nlinarith

omit [Fintype ν] in
lemma cst_pos : 0 < cst sys := by
  unfold cst
  have := one_le_etam sys
  have : 0 < Real.sqrt ((eta + 1) * mmax sys) := Real.sqrt_pos.mpr (by linarith)
  positivity

omit [Fintype ν] in
lemma cst_le : cst sys ≤ 1 / 8 := by
  unfold cst
  have h1 := one_le_etam sys
  have h2 : 1 ≤ Real.sqrt ((eta + 1) * mmax sys) := by
    have := Real.sqrt_le_sqrt h1; rwa [Real.sqrt_one] at this
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

omit [Fintype ν] in
lemma cst_le32 : cst sys ≤ 1 / 32 := by
  unfold cst
  have h1 := one_le_etam sys
  have h2 : 1 ≤ Real.sqrt ((eta + 1) * mmax sys) := by
    have := Real.sqrt_le_sqrt h1; rwa [Real.sqrt_one] at this
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

omit [Fintype ν] in
lemma cst_sq : cst sys ^ 2 = 1 / (1024 * ((eta + 1) * mmax sys)) := by
  unfold cst
  have h := one_le_etam sys
  rw [div_pow, mul_pow, Real.sq_sqrt (by linarith)]
  norm_num

omit [Fintype ν] in
lemma inC_imp_inQ {s c : ℝ} (hs : 0 ≤ s) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 4) {k : Cf eta}
    (h : InC s c k) : InQ s k := by
  intro a
  have h1 : c * s ≤ s / 4 := by nlinarith
  have h2 : (c * s) ^ 2 ≤ (s / 4) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  exact (h a).trans h2

omit [Fintype ν] in
/-- A configuration outside the cold ball has a register beyond `c s`. -/
lemma exists_reg_of_not_inC {s c : ℝ} {k : Cf eta} (h : ¬ InC s c k) :
    ∃ a, (c * s) ^ 2 < FSLattice.lsq (k a) := by
  simp only [InC, not_forall, not_le] at h
  exact h

end Cold

/-! ## Regions on the box -/

section BoxRegions

variable (sys : CoulombSystem eta ν) (N n : ℕ)

/-- The cold ball on the box. -/
noncomputable abbrev CN : En eta N →ₗ[ℂ] En eta N :=
  FSKernel.res fun q : Cfg eta N => InC (n : ℝ) (cst sys) (cidx N q)

/-- The warm shell `Q ∖ C` on the box. -/
noncomputable abbrev WmN : En eta N →ₗ[ℂ] En eta N :=
  FSKernel.res fun q : Cfg eta N => InQ (n : ℝ) (cidx N q) ∧ ¬ InC (n : ℝ) (cst sys) (cidx N q)

/-- The near-cutoff band `P ∖ Q` on the box. -/
noncomputable abbrev FpN : En eta N →ₗ[ℂ] En eta N :=
  FSKernel.res fun q : Cfg eta N => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)

variable {sys N n}

omit [Fintype ν] in
lemma QN_eq_CN_add (u : En eta N) : QN N n u = CN sys N n u + WmN sys N n u := by
  classical
  ext q
  simp only [FSKernel.res_apply, PiLp.add_apply]
  have hc := cst_pos sys
  have hc4 : cst sys ≤ 1 / 4 := (cst_le sys).trans (by norm_num)
  by_cases hC : InC (n : ℝ) (cst sys) (cidx N q)
  · have hQ := inC_imp_inQ (Nat.cast_nonneg n) hc.le hc4 hC
    simp [hC, hQ]
  · by_cases hQ : InQ (n : ℝ) (cidx N q)
    · simp [hC, hQ]
    · simp [hC, hQ]

omit [Fintype ν] in
lemma PN_eq_CWF (u : En eta N) :
    PN N n u = CN sys N n u + (WmN sys N n u + FpN N n u) := by
  rw [PN_eq_QN_add, QN_eq_CN_add, add_assoc]

end BoxRegions

/-! ## The flat potential on a channel -/

section Lam

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

lemma whK_eq_zero_of_wNK {q p : Cfg eta N} (h : wNK sys L N q p = 0) : whK sys L p₀ N q p = 0 := by
  unfold whK
  refine Finset.sum_eq_zero fun j _ => ?_
  unfold chPart
  split_ifs <;> simp [h]

lemma wNK_self (hL : 0 < L) (q : Cfg eta N) : wNK sys L N q q = 0 := by
  unfold wNK; exact potKernel_self_eq_zero hL _

/-- **`ŵ = λ_j w` on a channel.** -/
lemma whK_eq_lam (hL : 0 < L) {j : Ch eta} {q p : Cfg eta N} (h : OnCh j (cidx N q) (cidx N p)) :
    whK sys L p₀ N q p = (lamC sys p₀ j : ℂ) * wNK sys L N q p := by
  classical
  by_cases hqp : cidx N q = cidx N p
  · have h0 : wNK sys L N q p = 0 := by unfold wNK; rw [hqp]; exact potKernel_self_eq_zero hL _
    rw [whK_eq_zero_of_wNK h0, h0, mul_zero]
  unfold whK
  rw [Finset.sum_eq_single j]
  · unfold chPart; rw [if_pos h]
  · intro j' _ hj'
    unfold chPart
    rw [if_neg (fun h' => hj' (onCh_unique h' h hqp)), mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- **The `Q × Q` structure of the flat remainder**: for `q, q' ∈ Q` and `r ∉ P`, both hops
`q ↔ r ↔ q'` use one channel (`same_channel`), so `w(q, r) ŵ(r, q') = ŵ(q, r) w(r, q')`. -/
lemma wNK_whK_comm (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n) {q q' r : Cfg eta N}
    (hq : InQ (n : ℝ) (cidx N q)) (hq' : InQ (n : ℝ) (cidx N q')) (hr : ¬ InP (n : ℝ) (cidx N r)) :
    wNK sys L N q r * whK sys L p₀ N r q' = whK sys L p₀ N q r * wNK sys L N r q' := by
  by_cases h1 : wNK sys L N q r = 0
  · rw [h1, whK_eq_zero_of_wNK h1]; ring
  by_cases h2 : wNK sys L N r q' = 0
  · rw [h2, whK_eq_zero_of_wNK h2]; ring
  obtain ⟨j₁, hj₁⟩ := exists_onCh_of_ne_zero (sys := sys) hL (show potKernel sys L (cidx N q) (cidx N r) ≠ 0 from h1)
  obtain ⟨j₂, hj₂⟩ := exists_onCh_of_ne_zero (sys := sys) hL (show potKernel sys L (cidx N r) (cidx N q') ≠ 0 from h2)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj : j₁ = j₂ := same_channel hn0 hq hq' hr hj₁ hj₂
  subst hj
  rw [whK_eq_lam hL hj₁, whK_eq_lam hL hj₂]
  ring

lemma wNK_conj (hL : 0 < L) (q p : Cfg eta N) : wNK sys L N p q = conj (wNK sys L N q p) := by
  unfold wNK; exact potKernel_conj' hL _ _

omit [Fintype ν] in
/-- The coordinate form of `⟨res S (κ₁ v), res S (κ₂ v)⟩`. -/
lemma inner_res_kop (S : Cfg eta N → Prop) [DecidablePred S] (κ₁ κ₂ : Cfg eta N → Cfg eta N → ℂ)
    (v : En eta N) :
    ⟪FSKernel.res S (FSKernel.kop κ₁ v), FSKernel.res S (FSKernel.kop κ₂ v)⟫_ℂ =
      ∑ r, ∑ q, ∑ p, (if S r then conj (v.ofLp q) * conj (κ₁ r q) * (v.ofLp p * κ₂ r p) else 0) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [FSKernel.res_apply, FSKernel.kop_apply, Pi.star_apply, RCLike.star_def]
  by_cases hr : S r
  · simp only [hr, if_true, map_sum, map_mul]
    rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
    ring
  · simp [hr]

/-- `⟨R W v, R Ŵ v⟩ = ⟨R Ŵ v, R W v⟩` for `v = Q u`; in particular it is real. -/
lemma inner_RW_RWh_Q (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {n : ℕ} (hn : 1 ≤ n) (u : En eta N) :
    ⟪RN N n (WN sys L N (QN N n u)), RN N n (WhN sys L p₀ N (QN N n u))⟫_ℂ =
      ⟪RN N n (WhN sys L p₀ N (QN N n u)), RN N n (WN sys L N (QN N n u))⟫_ℂ := by
  classical
  have hW : WN sys L N = FSKernel.kop (wNK sys L N) := VN_eq_kop sys hL H hKernel
  rw [hW, inner_res_kop, inner_res_kop]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun p _ => ?_
  by_cases hr : InP (n : ℝ) (cidx N r)
  · simp [hr]
  rw [if_pos hr, if_pos hr]
  simp only [FSKernel.res_apply]
  by_cases hq : InQ (n : ℝ) (cidx N q)
  swap
  · simp [hq]
  by_cases hp : InQ (n : ℝ) (cidx N p)
  swap
  · simp [hp]
  rw [if_pos hq, if_pos hp]
  have hc := wNK_whK_comm (sys := sys) (p₀ := p₀) hL hn hq hp hr
  rw [← wNK_conj hL r q, ← whK_conj hL r q]
  linear_combination (conj (u.ofLp q) * u.ofLp p) * hc

lemma im_inner_RW_RWh_Q (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {n : ℕ} (hn : 1 ≤ n) (u : En eta N) :
    (⟪RN N n (WN sys L N (QN N n u)), RN N n (WhN sys L p₀ N (QN N n u))⟫_ℂ).im = 0 := by
  have h := inner_RW_RWh_Q (p₀ := p₀) hL H hKernel hn u
  have h2 : ⟪RN N n (WN sys L N (QN N n u)), RN N n (WhN sys L p₀ N (QN N n u))⟫_ℂ =
      conj ⟪RN N n (WN sys L N (QN N n u)), RN N n (WhN sys L p₀ N (QN N n u))⟫_ℂ := by
    rw [inner_conj_symm]; exact h
  have := congrArg Complex.im h2
  rw [Complex.conj_im] at this
  linarith

end Lam

/-! ## The split of the flat remainder -/

section Split

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) {N : ℕ} (n : ℕ)

/-- The far–cold part of the flat remainder (to the third elimination round):
`2 Im⟨W δ, P Ŵ u_C⟩ - 2 Im⟨R W u_C, R Ŵ u_{F'}⟩ - 2 Im⟨R W u_{F'}, R Ŵ u_C⟩`. -/
noncomputable def nflFC (u : En eta N) : ℝ :=
  2 * (⟪WN sys L N (RN N n u), PN N n (WhN sys L p₀ N (CN sys N n u))⟫_ℂ).im -
    2 * (⟪RN N n (WN sys L N (CN sys N n u)), RN N n (WhN sys L p₀ N (FpN N n u))⟫_ℂ).im -
    2 * (⟪RN N n (WN sys L N (FpN N n u)), RN N n (WhN sys L p₀ N (CN sys N n u))⟫_ℂ).im

/-- The restricted part of the flat remainder: every factor carries a register beyond `c_* n`. -/
noncomputable def nflRR (u : En eta N) : ℝ :=
  2 * (⟪WN sys L N (RN N n u), PN N n (WhN sys L p₀ N (WmN sys N n u + FpN N n u))⟫_ℂ).im -
    2 * (⟪RN N n (WN sys L N (WmN sys N n u)), RN N n (WhN sys L p₀ N (FpN N n u))⟫_ℂ).im -
    2 * (⟪RN N n (WN sys L N (FpN N n u)), RN N n (WhN sys L p₀ N (WmN sys N n u))⟫_ℂ).im -
    2 * (⟪RN N n (WN sys L N (FpN N n u)), RN N n (WhN sys L p₀ N (FpN N n u))⟫_ℂ).im

variable {sys L p₀}

/-- **The split of the flat remainder**: `n^fl = n^{FC} + n^{rr}` (the `Q × Q` block vanishes). -/
theorem nfl_split (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {n : ℕ} (hn : 1 ≤ n) (u : En eta N) :
    nfl sys L p₀ n u = nflFC sys L p₀ n u + nflRR sys L p₀ n u := by
  have h0 := im_inner_RW_RWh_Q (sys := sys) (p₀ := p₀) hL H hKernel hn u
  set c := CN sys N n u
  set w := WmN sys N n u
  set f := FpN N n u
  have hP : PN N n u = c + (w + f) := PN_eq_CWF u
  have hQ : QN N n u = c + w := QN_eq_CN_add u
  have hδ : u - PN N n u = RN N n u := (RN_eq n u).symm
  unfold nfl nflFC nflRR
  rw [hδ]
  have hφ : PN N n u = QN N n u + f := by rw [hQ, hP, add_assoc]
  -- term 1
  have t1 : ⟪WN sys L N (RN N n u), PN N n (WhN sys L p₀ N (PN N n u))⟫_ℂ =
      ⟪WN sys L N (RN N n u), PN N n (WhN sys L p₀ N c)⟫_ℂ +
        ⟪WN sys L N (RN N n u), PN N n (WhN sys L p₀ N (w + f))⟫_ℂ := by
    rw [hP, map_add, map_add, inner_add_right]
  -- term 2
  have t2 : ⟪RN N n (WN sys L N (PN N n u)), RN N n (WhN sys L p₀ N (PN N n u))⟫_ℂ =
      ⟪RN N n (WN sys L N (QN N n u)), RN N n (WhN sys L p₀ N (QN N n u))⟫_ℂ +
        (⟪RN N n (WN sys L N c), RN N n (WhN sys L p₀ N f)⟫_ℂ +
          ⟪RN N n (WN sys L N w), RN N n (WhN sys L p₀ N f)⟫_ℂ) +
        (⟪RN N n (WN sys L N f), RN N n (WhN sys L p₀ N c)⟫_ℂ +
          ⟪RN N n (WN sys L N f), RN N n (WhN sys L p₀ N w)⟫_ℂ) +
        ⟪RN N n (WN sys L N f), RN N n (WhN sys L p₀ N f)⟫_ℂ := by
    rw [hφ]
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hQ]
    simp only [map_add, inner_add_left, inner_add_right]
    ring
  rw [t1, t2]
  simp only [Complex.add_im]
  rw [h0]
  ring

end Split

/-! ## The restricted part is at target -/

section Restricted

variable (sys : CoulombSystem eta ν) {L : ℝ} {N : ℕ}

omit [Fintype ν] in
/-- A configuration outside the cold ball has a register with `|k| > c_* K` (physical). -/
lemma kabs_gt_of_not_inC (hL : 0 < L) {n : ℕ} {q : Cfg eta N}
    (h : ¬ InC (n : ℝ) (cst sys) (cidx N q)) :
    ∃ c, gF L * (cst sys * n) < finitePlaneWaveKabs (2 * Real.pi / L) N (q c) := by
  obtain ⟨c, hc⟩ := exists_reg_of_not_inC h
  have h0 : 0 ≤ cst sys * n := by have := cst_pos sys; positivity
  exact ⟨c, kabs_gt_of_lsq_gt hL h0 q c hc⟩

/-- **Hardy with the tails beyond the cold ball**: for a kernel dominated by `potMaj` and a
restriction `S` to configurations outside the cold ball,
`‖kop κ (res S u)‖ ≤ C_H √2 η M l^{-3/2}`, `l = c_* K ≥ 1`. -/
lemma norm_kop_res_cold_le (hL : 0 < L) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {n : ℕ}
    (hl : 1 ≤ gF L * (cst sys * n)) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u)
    (κ : Cfg eta N → Cfg eta N → ℂ)
    (hκ : ∀ q p, ‖κ q p‖ ≤ potMaj sys L (cidx N q) (cidx N p))
    (S : Cfg eta N → Prop) (hS : ∀ q, S q → ¬ InC (n : ℝ) (cst sys) (cidx N q)) :
    ‖FSKernel.kop κ (FSKernel.res S u)‖ ≤
      CH sys L Hunit * (Real.sqrt 2 * eta * M * (gF L * (cst sys * n)) ^ (-(3 / 2 : ℝ))) := by
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  set l := gF L * (cst sys * n)
  have hl0 : 0 < l := by linarith
  obtain ⟨h1, h2⟩ := res_tails_good sys hu S hl (fun q hq => kabs_gt_of_not_inC sys hL (hS q hq))
  have hCH := CH_nonneg sys hL Hunit
  refine (norm_kop_le_potMaj sys hL Hunit hPeriodic κ hκ _).trans ?_
  refine mul_le_mul_of_nonneg_left ((sqrt_wns_le sys _).trans ?_) hCH
  have e : Real.sqrt 2 * eta * M * l ^ (-(3 / 2 : ℝ)) =
      Real.sqrt (2 * (eta * M * l ^ (-(5 / 2 : ℝ))) * (eta * M * l ^ (-(1 / 2 : ℝ)))) := by
    have hp : l ^ (-(5 / 2 : ℝ)) * l ^ (-(1 / 2 : ℝ)) = (l ^ (-(3 / 2 : ℝ))) ^ 2 := by
      rw [← Real.rpow_add hl0, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
      norm_num
    rw [show 2 * (eta * M * l ^ (-(5 / 2 : ℝ))) * (eta * M * l ^ (-(1 / 2 : ℝ))) =
        2 * (eta * M * l ^ (-(3 / 2 : ℝ))) ^ 2 by rw [mul_pow, mul_pow, ← hp]; ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    ring
  rw [e]
  apply Real.sqrt_le_sqrt
  have ha := norm_nonneg (FSKernel.res S u)
  have hb := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 (FSKernel.res S u))
  have hc : 0 ≤ eta * M * l ^ (-(1 / 2 : ℝ)) := by positivity
  calc 2 * ‖FSKernel.res S u‖ * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (FSKernel.res S u)‖
      ≤ 2 * (eta * M * l ^ (-(5 / 2 : ℝ))) *
          ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (FSKernel.res S u)‖ := by gcongr
    _ ≤ _ := by gcongr

variable (p₀ : Fin eta)

/-- The restriction constant `C_H √2 η`. -/
noncomputable def Hrs (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ := CH sys L Hunit * (Real.sqrt 2 * eta)

/-- **The restricted part of the flat remainder is at target**:
`|n^{rr}(u)| ≤ 8 H_rs² M² (c_* K)⁻³` for a good box state, `c_* K ≥ 1`. -/
theorem norm_nflRR_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {n : ℕ}
    (hl : 1 ≤ gF L * (cst sys * n)) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    |nflRR sys L p₀ n u| ≤ 8 * Hrs sys L Hunit ^ 2 * M ^ 2 * (gF L * (cst sys * n)) ^ (-(3 : ℝ)) := by
  classical
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  set l := gF L * (cst sys * n)
  have hl0 : 0 < l := by linarith
  set h₀ := CH sys L Hunit * (Real.sqrt 2 * eta * M * l ^ (-(3 / 2 : ℝ)))
  have hW : WN sys L N = FSKernel.kop (wNK sys L N) := VN_eq_kop sys hL H hKernel
  have hκW : ∀ q p, ‖wNK sys L N q p‖ ≤ potMaj sys L (cidx N q) (cidx N p) := fun q p =>
    norm_potKernel_le sys hL _ _
  have hκH : ∀ q p, ‖whK sys L p₀ N q p‖ ≤ potMaj sys L (cidx N q) (cidx N p) := norm_whK_le sys hL p₀
  have hc4 : cst sys ≤ 1 / 4 := (cst_le sys).trans (by norm_num)
  have hc0 := cst_pos sys
  -- the supports
  have sR : ∀ q : Cfg eta N, ¬ InP (n : ℝ) (cidx N q) → ¬ InC (n : ℝ) (cst sys) (cidx N q) := by
    intro q hq hC
    exact hq (inQ_imp_inP (Nat.cast_nonneg n) (inC_imp_inQ (Nat.cast_nonneg n) hc0.le hc4 hC))
  have sW : ∀ q : Cfg eta N, (InQ (n : ℝ) (cidx N q) ∧ ¬ InC (n : ℝ) (cst sys) (cidx N q)) →
      ¬ InC (n : ℝ) (cst sys) (cidx N q) := fun q hq => hq.2
  have sF : ∀ q : Cfg eta N, (InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)) →
      ¬ InC (n : ℝ) (cst sys) (cidx N q) := fun q hq hC =>
    hq.2 (inC_imp_inQ (Nat.cast_nonneg n) hc0.le hc4 hC)
  have sWF : ∀ q : Cfg eta N, ((InQ (n : ℝ) (cidx N q) ∧ ¬ InC (n : ℝ) (cst sys) (cidx N q)) ∨
      (InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))) → ¬ InC (n : ℝ) (cst sys) (cidx N q) := by
    intro q hq
    rcases hq with hq | hq
    · exact sW q hq
    · exact sF q hq
  have eWF : WmN sys N n u + FpN N n u = FSKernel.res (fun q : Cfg eta N =>
      (InQ (n : ℝ) (cidx N q) ∧ ¬ InC (n : ℝ) (cst sys) (cidx N q)) ∨
        (InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))) u := by
    ext q
    simp only [FSKernel.res_apply, PiLp.add_apply]
    by_cases h1 : InQ (n : ℝ) (cidx N q) <;> by_cases h2 : InC (n : ℝ) (cst sys) (cidx N q) <;>
      by_cases h3 : InP (n : ℝ) (cidx N q) <;> simp [h1, h2, h3]
  -- the factors
  have bR : ‖WN sys L N (RN N n u)‖ ≤ h₀ := by
    rw [hW]; exact norm_kop_res_cold_le sys hL Hunit hPeriodic hl hu _ hκW _ sR
  have bRW : ‖WN sys L N (WmN sys N n u)‖ ≤ h₀ := by
    rw [hW]; exact norm_kop_res_cold_le sys hL Hunit hPeriodic hl hu _ hκW _ sW
  have bRF : ‖WN sys L N (FpN N n u)‖ ≤ h₀ := by
    rw [hW]; exact norm_kop_res_cold_le sys hL Hunit hPeriodic hl hu _ hκW _ sF
  have bHW : ‖WhN sys L p₀ N (WmN sys N n u)‖ ≤ h₀ :=
    norm_kop_res_cold_le sys hL Hunit hPeriodic hl hu _ hκH _ sW
  have bHF : ‖WhN sys L p₀ N (FpN N n u)‖ ≤ h₀ :=
    norm_kop_res_cold_le sys hL Hunit hPeriodic hl hu _ hκH _ sF
  have bHWF : ‖WhN sys L p₀ N (WmN sys N n u + FpN N n u)‖ ≤ h₀ := by
    rw [eWF]; exact norm_kop_res_cold_le sys hL Hunit hPeriodic hl hu _ hκH _ sWF
  have h0 : 0 ≤ h₀ := by have := CH_nonneg sys hL Hunit; positivity
  -- products
  have pr : ∀ a b : En eta N, ‖a‖ ≤ h₀ → ‖b‖ ≤ h₀ → ∀ (A B : En eta N →ₗ[ℂ] En eta N),
      (∀ x, ‖A x‖ ≤ ‖x‖) → (∀ x, ‖B x‖ ≤ ‖x‖) → |(⟪A a, B b⟫_ℂ).im| ≤ h₀ ^ 2 := by
    intro a b ha hb A B hA hB
    refine (Complex.abs_im_le_norm _).trans ((norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_)
    rw [sq]
    exact mul_le_mul ((hA a).trans ha) ((hB b).trans hb) (norm_nonneg _) h0
  have hRc : ∀ x : En eta N, ‖RN N n x‖ ≤ ‖x‖ := fun x => FSKernel.norm_res_le _ x
  have hPc : ∀ x : En eta N, ‖PN N n x‖ ≤ ‖x‖ := fun x => FSKernel.norm_res_le _ x
  have hIc : ∀ x : En eta N, ‖(LinearMap.id : En eta N →ₗ[ℂ] En eta N) x‖ ≤ ‖x‖ := fun x => le_rfl
  have p1 := pr _ _ bR bHWF LinearMap.id (PN N n) hIc hPc
  have p2 := pr _ _ bRW bHF (RN N n) (RN N n) hRc hRc
  have p3 := pr _ _ bRF bHW (RN N n) (RN N n) hRc hRc
  have p4 := pr _ _ bRF bHF (RN N n) (RN N n) hRc hRc
  simp only [LinearMap.id_apply] at p1
  have htot : |nflRR sys L p₀ n u| ≤ 8 * h₀ ^ 2 := by
    unfold nflRR
    have := abs_sub (2 * (⟪WN sys L N (RN N n u), PN N n (WhN sys L p₀ N (WmN sys N n u +
      FpN N n u))⟫_ℂ).im - 2 * (⟪RN N n (WN sys L N (WmN sys N n u)),
        RN N n (WhN sys L p₀ N (FpN N n u))⟫_ℂ).im - 2 * (⟪RN N n (WN sys L N (FpN N n u)),
          RN N n (WhN sys L p₀ N (WmN sys N n u))⟫_ℂ).im)
      (2 * (⟪RN N n (WN sys L N (FpN N n u)), RN N n (WhN sys L p₀ N (FpN N n u))⟫_ℂ).im)
    have := abs_sub (2 * (⟪WN sys L N (RN N n u), PN N n (WhN sys L p₀ N (WmN sys N n u +
      FpN N n u))⟫_ℂ).im - 2 * (⟪RN N n (WN sys L N (WmN sys N n u)),
        RN N n (WhN sys L p₀ N (FpN N n u))⟫_ℂ).im)
      (2 * (⟪RN N n (WN sys L N (FpN N n u)), RN N n (WhN sys L p₀ N (WmN sys N n u))⟫_ℂ).im)
    have := abs_sub (2 * (⟪WN sys L N (RN N n u), PN N n (WhN sys L p₀ N (WmN sys N n u +
      FpN N n u))⟫_ℂ).im) (2 * (⟪RN N n (WN sys L N (WmN sys N n u)),
        RN N n (WhN sys L p₀ N (FpN N n u))⟫_ℂ).im)
    simp only [abs_mul, abs_two] at *
    linarith
  have hh : h₀ ^ 2 = Hrs sys L Hunit ^ 2 * M ^ 2 * l ^ (-(3 : ℝ)) := by
    have hp : (l ^ (-(3 / 2 : ℝ))) ^ 2 = l ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
    simp only [h₀, Hrs]
    rw [show (CH sys L Hunit * (Real.sqrt 2 * eta * M * l ^ (-(3 / 2 : ℝ)))) ^ 2 =
      (CH sys L Hunit * (Real.sqrt 2 * eta)) ^ 2 * M ^ 2 * (l ^ (-(3 / 2 : ℝ))) ^ 2 by ring, hp]
  rw [hh] at htot
  linarith

end Restricted

end FSFlux
