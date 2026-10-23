import PlaneWave.KineticLog.OpenDuhamel

/-!
# Logarithmic kinetic bound, part 21: trajectory shells in the physical weight

The observable step of the cell-to-grid comparison needs, uniformly in `L ≥ 2π`, the first
physical weight `‖w_g φ‖` and the shells `‖1_{|q_p|_∞ > T} w_g φ‖` of the exact and grid
trajectories on the register, `w_g = 1 + 2 A` (`A` the register kinetic multiplier, kinetic scale
`1/2`):

* the register kinetic multiplier `A_p ≤ w_g/2` and its crude register bounds
  (`norm_regKin_le_wPhys`, `norm_regKin_le_polyU`, `norm_wPhys_regKin_le_polyU`);
* **the layer cake for any weight** (`norm_w_regKin_shells`): if `‖w φ‖ ≤ B₀` and
  `‖1_{|q_p|_∞ > T} w φ‖ ≤ B/√T` for `T₀ ≤ T ≤ m`, then
  `‖w A_p φ‖ ≤ 3 g² (T₀² B₀ + 4 m √m B)`; the low shells cost `T₀⁴ B₀²` in square (not
  `m T₀³ B₀²`), so in physical units `3 (g T₀)² B₀ + 12 K^{3/2} B'` with `B = B'/√g`;
* the exact trajectory of `H_L` (`traj_tails_gL`, `exact_traj_shells_gL`): first graph bound and
  Fourier tails `c_tr^U Ξ λ^{-1/2}`, `2 m̄ c_tr^U Ξ λ^{-5/2}` beyond every `λ ≥ 1`
  (`tails_at_time_gL` with the `L`-free constants);
* the first physical weight of the grid trajectory (`grid_traj_weight_gL`,
  `norm_wPhys_gridFlow_le_gL`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The kinetic multiplier in the physical weight -/

section KinPhys

variable (sys : CoulombSystem eta ν) (g : ℝ) {m : ℕ}

omit [Fintype ν] in
lemma wPhys_eq_kinT (q : RCfg eta m) :
    FreeBoundary.wPhys (regParticlesOf sys) g q = 1 + 2 * kinT eta m (regParticlesOf sys) g q := by
  rw [FreeBoundary.wPhys_eq_wM]
  unfold kinT
  ring

omit [Fintype ν] in
lemma regKinSym_nonneg (p : Fin eta) (q : RCfg eta m) : 0 ≤ regKinSym sys g p q := by
  rw [regKinSym_eq]
  have := nsq_nonneg (gl (q p))
  have := sys.mass_pos p
  positivity

omit [Fintype ν] in
lemma regKinSym_le_half_wPhys (p : Fin eta) (q : RCfg eta m) :
    regKinSym sys g p q ≤ 1 / 2 * FreeBoundary.wPhys (regParticlesOf sys) g q := by
  rw [regKinSym_eq]
  unfold FreeBoundary.wPhys
  have hterm : nsq (gl (q p)) / (regParticlesOf sys).mass p ≤
      ∑ b, nsq (gl (q b)) / (regParticlesOf sys).mass b :=
    Finset.single_le_sum (f := fun b => nsq (gl (q b)) / (regParticlesOf sys).mass b)
      (fun b _ => div_nonneg (nsq_nonneg _) (sys.mass_pos b).le) (Finset.mem_univ p)
  have hm : (regParticlesOf sys).mass p = sys.mass p := rfl
  rw [hm] at hterm
  have := mul_le_mul_of_nonneg_left hterm (sq_nonneg g)
  nlinarith

omit [Fintype ν] in
/-- `‖A_p v‖ ≤ (1/2) ‖w_g v‖`. -/
lemma norm_regKin_le_wPhys (p : Fin eta) (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (regKinSym sys g p) v‖ ≤
        1 / 2 * ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) g) v‖ := by
  have h := norm_wMul_mono (w := regKinSym sys g p)
    (w' := fun q => 1 / 2 * FreeBoundary.wPhys (regParticlesOf sys) g q)
    (regKinSym_nonneg sys g p) (regKinSym_le_half_wPhys sys g p) v
  have e : wMul (fun q => 1 / 2 * FreeBoundary.wPhys (regParticlesOf sys) g q) v =
      ((1 / 2 : ℝ) : ℂ) • wMul (FreeBoundary.wPhys (regParticlesOf sys) g) v := by
    ext q
    simp only [wMul_apply, PiLp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)] at h
  exact h

omit [Fintype ν] in
lemma wPhys_le_reg (q : RCfg eta m) :
    FreeBoundary.wPhys (regParticlesOf sys) g q ≤ 1 + 12 * eta * (g * m) ^ 2 :=
  (FreeBoundary.wPhys_le_wTotPh (regParticlesOf sys) g q).trans (wTotPh_le_reg g q)

omit [Fintype ν] in
/-- `‖A_p v‖ ≤ (1/2)(1 + 12 η K²) ‖v‖`, `K = g m`. -/
lemma norm_regKin_le_polyU (p : Fin eta) (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (regKinSym sys g p) v‖ ≤ 1 / 2 * (1 + 12 * eta * (g * m) ^ 2) * ‖v‖ := by
  have hc : (0 : ℝ) ≤ 1 / 2 * (1 + 12 * eta * (g * m) ^ 2) := by positivity
  refine (norm_le_of_pointwise (Y := ((1 / 2 * (1 + 12 * eta * (g * m) ^ 2) : ℝ) : ℂ) • v)
    fun q => ?_).trans ?_
  · rw [wMul_apply, PiLp.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (regKinSym_nonneg sys g p q), Real.norm_of_nonneg hc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 := regKinSym_le_half_wPhys sys g p q
    have h2 := wPhys_le_reg sys g q
    linarith
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]

omit [Fintype ν] in
/-- `‖w_g A_p v‖ ≤ (1/2)(1 + 12 η K²)² ‖v‖`. -/
lemma norm_wPhys_regKin_le_polyU (p : Fin eta) (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) g) (wMul (regKinSym sys g p) v)‖ ≤
      1 / 2 * (1 + 12 * eta * (g * m) ^ 2) ^ 2 * ‖v‖ := by
  have hc : (0 : ℝ) ≤ 1 / 2 * (1 + 12 * eta * (g * m) ^ 2) ^ 2 := by positivity
  refine (norm_le_of_pointwise
    (Y := ((1 / 2 * (1 + 12 * eta * (g * m) ^ 2) ^ 2 : ℝ) : ℂ) • v) fun q => ?_).trans ?_
  · have hw1 : 1 ≤ FreeBoundary.wPhys (regParticlesOf sys) g q :=
      FreeBoundary.wPhys_ge_one (regParticlesOf sys) g q
    rw [wMul_apply, wMul_apply, PiLp.smul_apply, smul_eq_mul, norm_mul, norm_mul, norm_mul,
      Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (regKinSym_nonneg sys g p q),
      Real.norm_of_nonneg hc, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 := regKinSym_le_half_wPhys sys g p q
    have h2 := wPhys_le_reg sys g q
    have h0 := regKinSym_nonneg sys g p q
    calc FreeBoundary.wPhys (regParticlesOf sys) g q * regKinSym sys g p q
        ≤ (1 + 12 * eta * (g * m) ^ 2) * (1 / 2 * (1 + 12 * eta * (g * m) ^ 2)) :=
          mul_le_mul h2 (h1.trans (by linarith)) h0 (by positivity)
      _ = _ := by ring
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]

omit [Fintype ν] in
/-- `w_g P' S y = P' (S y + 2 T y)` on the register. -/
lemma wPhys_regCoeff_eq {g : ℝ} (y : MolecularFourierH2 eta) :
    wMul (FreeBoundary.wPhys (regParticlesOf sys) g) (regCoeff m (molecularH2StateMap eta g y)) =
      regCoeff m (molecularH2StateMap eta g y + (2 : ℂ) • coulombFourierKineticH2 sys g y) := by
  rw [map_add, map_smul, regCoeff_kinetic]
  ext q
  simp only [wMul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, wPhys_eq_kinT]
  push_cast
  ring

end KinPhys

/-! ## The layer cake for any weight -/

omit [Fintype ν] in
/-- **The second weighted moment from the first weighted shells, for any weight** (layer cake):
if `‖w φ‖ ≤ B₀` and `‖1_{|q_p|_∞ > T} w φ‖ ≤ B/√T` for `T₀ ≤ T ≤ m`, then
`‖w A_p φ‖ ≤ 3 g² (T₀² B₀ + 4 m √m B)`. -/
theorem norm_w_regKin_shells (sys : CoulombSystem eta ν) (g : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (w : RCfg eta m → ℝ) (p : Fin eta) (φ : EuclideanSpace ℂ (RCfg eta m)) {T₀ : ℕ}
    (hT₀ : 1 ≤ T₀) (hT₀m : T₀ ≤ m) {B₀ B : ℝ} (hB₀ : ‖wMul w φ‖ ≤ B₀) (hB : 0 ≤ B)
    (htail : ∀ T : ℕ, T₀ ≤ T → T ≤ m → ‖maskOp (High T p) (wMul w φ)‖ ≤ B / Real.sqrt T) :
    ‖wMul w (wMul (regKinSym sys g p) φ)‖ ≤
      3 * g ^ 2 * ((T₀ : ℝ) ^ 2 * B₀ + 4 * ((m : ℝ) * Real.sqrt m) * B) := by
  classical
  set z := wMul w φ with hz
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans hB₀
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT₀r : (1 : ℝ) ≤ T₀ := by exact_mod_cast hT₀
  have hcomm : wMul w (wMul (regKinSym sys g p) φ) = wMul (regKinSym sys g p) z := by
    ext q
    simp only [hz, wMul_apply]
    ring
  rw [hcomm]
  have hsq : ‖wMul (regKinSym sys g p) z‖ ^ 2 ≤
      9 * g ^ 4 * ∑ T ∈ Finset.range (2 * m), ((T : ℝ) + 1) ^ 3 * ‖maskOp (High T p) z‖ ^ 2 := by
    rw [norm_sq_eq_sum]
    have hpt : ∀ q, ‖(wMul (regKinSym sys g p) z) q‖ ^ 2 ≤ 9 * g ^ 4 *
        ∑ T ∈ Finset.range (2 * m), ((T : ℝ) + 1) ^ 3 * (if High T p q then 1 else 0) *
          ‖z q‖ ^ 2 := by
      intro q
      rw [wMul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
        ← Finset.sum_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (regKinSym_sq_le_shells sys g p q) (sq_nonneg _)
    refine (Finset.sum_le_sum fun q _ => hpt q).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [norm_sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [maskOp_apply]
    split_ifs <;> simp
  have hterm : ∀ T ∈ Finset.range (2 * m), ((T : ℝ) + 1) ^ 3 * ‖maskOp (High T p) z‖ ^ 2 ≤
      (if T < T₀ then (T₀ : ℝ) ^ 3 * B₀ ^ 2 else 0) + 8 * (m : ℝ) ^ 2 * B ^ 2 := by
    intro T hT
    rw [Finset.mem_range] at hT
    have hTr : (T : ℝ) + 1 ≤ 2 * m := by
      have : T + 1 ≤ 2 * m := hT
      exact_mod_cast this
    have hmask0 := norm_nonneg (maskOp (High T p) z)
    have h8 : 0 ≤ 8 * (m : ℝ) ^ 2 * B ^ 2 := by positivity
    rcases lt_or_ge T T₀ with h1 | h1
    · rw [if_pos h1]
      have hT1 : (T : ℝ) + 1 ≤ T₀ := by exact_mod_cast h1
      have hmk : ‖maskOp (High T p) z‖ ≤ B₀ := (norm_maskOp_le _ z).trans hB₀
      have a1 : ((T : ℝ) + 1) ^ 3 ≤ (T₀ : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hT1 3
      have a2 : ‖maskOp (High T p) z‖ ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ hmask0 hmk 2
      have := mul_le_mul a1 a2 (sq_nonneg _) (by positivity)
      linarith
    · rw [if_neg (not_lt.mpr h1), zero_add]
      rcases le_or_gt T m with h2 | h2
      · have hT1 : (1 : ℝ) ≤ T := hT₀r.trans (by exact_mod_cast h1)
        have hmk := htail T h1 h2
        have a2 : ‖maskOp (High T p) z‖ ^ 2 ≤ B ^ 2 / T := by
          have := pow_le_pow_left₀ hmask0 hmk 2
          rwa [div_pow, Real.sq_sqrt (by linarith)] at this
        have hTm : (T : ℝ) ≤ m := by exact_mod_cast h2
        have a1 : ((T : ℝ) + 1) ^ 3 ≤ 8 * (T : ℝ) ^ 3 := by
          calc ((T : ℝ) + 1) ^ 3 ≤ (2 * (T : ℝ)) ^ 3 :=
                pow_le_pow_left₀ (by positivity) (by linarith) 3
            _ = 8 * (T : ℝ) ^ 3 := by ring
        have a3 : ((T : ℝ) + 1) ^ 3 * ‖maskOp (High T p) z‖ ^ 2 ≤ 8 * (T : ℝ) ^ 3 * (B ^ 2 / T) :=
          mul_le_mul a1 a2 (sq_nonneg _) (by positivity)
        have a4 : 8 * (T : ℝ) ^ 3 * (B ^ 2 / T) = 8 * (T : ℝ) ^ 2 * B ^ 2 := by
          field_simp
        have a5 : 8 * (T : ℝ) ^ 2 * B ^ 2 ≤ 8 * (m : ℝ) ^ 2 * B ^ 2 := by
          have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ T) hTm 2
          have hB2 := sq_nonneg B
          nlinarith
        linarith
      · have hmk : ‖maskOp (High T p) z‖ ≤ B / Real.sqrt m :=
          (norm_maskOp_mono (fun q hq => High.mono h2.le hq) z).trans (htail m hT₀m le_rfl)
        have a2 : ‖maskOp (High T p) z‖ ^ 2 ≤ B ^ 2 / m := by
          have := pow_le_pow_left₀ hmask0 hmk 2
          rwa [div_pow, Real.sq_sqrt (by linarith)] at this
        have a1 : ((T : ℝ) + 1) ^ 3 ≤ (2 * m) ^ 3 := pow_le_pow_left₀ (by positivity) hTr 3
        have a3 : ((T : ℝ) + 1) ^ 3 * ‖maskOp (High T p) z‖ ^ 2 ≤ (2 * m) ^ 3 * (B ^ 2 / m) :=
          mul_le_mul a1 a2 (sq_nonneg _) (by positivity)
        have a4 : (2 * (m : ℝ)) ^ 3 * (B ^ 2 / m) = 8 * (m : ℝ) ^ 2 * B ^ 2 := by
          field_simp
          ring
        linarith
  have hlow : ∑ T ∈ Finset.range (2 * m), (if T < T₀ then (T₀ : ℝ) ^ 3 * B₀ ^ 2 else 0) ≤
      (T₀ : ℝ) ^ 4 * B₀ ^ 2 := by
    rw [← Finset.sum_filter]
    have hsub : (Finset.range (2 * m)).filter (fun T => T < T₀) ⊆ Finset.range T₀ := by
      intro T hT
      rw [Finset.mem_filter] at hT
      exact Finset.mem_range.mpr hT.2
    calc ∑ T ∈ (Finset.range (2 * m)).filter (fun T => T < T₀), (T₀ : ℝ) ^ 3 * B₀ ^ 2
        ≤ ∑ T ∈ Finset.range T₀, (T₀ : ℝ) ^ 3 * B₀ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = (T₀ : ℝ) ^ 4 * B₀ ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hsum : ∑ T ∈ Finset.range (2 * m), ((T : ℝ) + 1) ^ 3 * ‖maskOp (High T p) z‖ ^ 2 ≤
      (T₀ : ℝ) ^ 4 * B₀ ^ 2 + 16 * (m : ℝ) ^ 3 * B ^ 2 := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have e : ((2 * m : ℕ) : ℝ) * (8 * (m : ℝ) ^ 2 * B ^ 2) = 16 * (m : ℝ) ^ 3 * B ^ 2 := by
      push_cast
      ring
    rw [e]
    linarith
  have hR0 : 0 ≤ 3 * g ^ 2 * ((T₀ : ℝ) ^ 2 * B₀ + 4 * ((m : ℝ) * Real.sqrt m) * B) := by
    positivity
  have hsqm : Real.sqrt m ^ 2 = m := Real.sq_sqrt (by linarith)
  have hfin : ‖wMul (regKinSym sys g p) z‖ ^ 2 ≤
      (3 * g ^ 2 * ((T₀ : ℝ) ^ 2 * B₀ + 4 * ((m : ℝ) * Real.sqrt m) * B)) ^ 2 := by
    refine hsq.trans ?_
    have e : (3 * g ^ 2 * ((T₀ : ℝ) ^ 2 * B₀ + 4 * ((m : ℝ) * Real.sqrt m) * B)) ^ 2 =
        9 * g ^ 4 * (((T₀ : ℝ) ^ 2 * B₀) ^ 2 + 16 * (m : ℝ) ^ 3 * B ^ 2 +
          8 * (T₀ : ℝ) ^ 2 * B₀ * ((m : ℝ) * Real.sqrt m) * B) := by
      have : ((m : ℝ) * Real.sqrt m) ^ 2 = (m : ℝ) ^ 3 := by
        rw [mul_pow, hsqm]
        ring
      have e2 : (4 * ((m : ℝ) * Real.sqrt m) * B) ^ 2 =
          16 * ((m : ℝ) * Real.sqrt m) ^ 2 * B ^ 2 := by
        ring
      rw [mul_pow, mul_pow, add_sq, e2, this]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (by positivity)
    have h0 : 0 ≤ 8 * (T₀ : ℝ) ^ 2 * B₀ * ((m : ℝ) * Real.sqrt m) * B := by positivity
    have e3 : ((T₀ : ℝ) ^ 2 * B₀) ^ 2 = (T₀ : ℝ) ^ 4 * B₀ ^ 2 := by ring
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR0 two_ne_zero).mp hfin

/-! ## The exact trajectory of `H_L` -/

section ExactGL

variable (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (FreeBoundary.gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 2 * Real.pi ≤ L) (hθ : FreeBoundary.Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hH : 0 ≤ Hunit)

/-- The first graph constant of `H_L` trajectories, `b_e = 5 + 4 b_U`. -/
noncomputable def b0eU (sys : CoulombSystem eta ν) (V Hunit : ℝ) : ℝ :=
  5 + 4 * FreeBoundary.relBU sys V Hunit

/-- The tail constant of `H_L` trajectories,
`c_tr^U = 2 m̄ (2 + 2 b_U) + C_t^U(1) m̄ (5 + 4 b_U)`. -/
noncomputable def cTrU (sys : CoulombSystem eta ν) (V Hunit : ℝ) : ℝ :=
  2 * sys.maxMass * (2 + 2 * FreeBoundary.relBU sys V Hunit) +
    FreeBoundary.gLtailMU sys V Hunit 1 * (sys.maxMass * b0eU sys V Hunit)

lemma b0eU_nonneg {V Hunit : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ b0eU sys V Hunit := by
  unfold b0eU
  have := FreeBoundary.relBU_nonneg sys hV hH
  positivity

lemma cTrU_nonneg {V Hunit : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ cTrU sys V Hunit := by
  unfold cTrU
  have := FreeBoundary.relBU_nonneg sys hV hH
  have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
  have := b0eU_nonneg sys hV hH
  have := sys.maxMass_pos
  positivity

omit [Fintype ν] in
lemma Xi_parts {L : ℝ}
    {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}
    (D : EvoData L H) :
    ‖Sm eta L D.u₀‖ ≤ D.Xi ∧ ‖H D.u₀‖ ≤ D.Xi ∧ ‖H D.v₀‖ ≤ D.Xi ∧ ‖Sm eta L D.v₀‖ ≤ D.Xi := by
  have h1 := norm_nonneg (Sm eta L D.u₀)
  have h2 := norm_nonneg (H D.u₀)
  have h3 := norm_nonneg (H D.v₀)
  have hv : Sm eta L D.v₀ = H D.u₀ := D.uv.symm
  unfold EvoData.Xi
  refine ⟨by linarith, by linarith, by linarith, by rw [hv]; linarith⟩

set_option maxHeartbeats 400000 in
include hKernel hL hθ hPeriodic hH in
/-- **The exact trajectory of `H_L`** (uniform in `L ≥ 2π`): the `H²` lift `w` of `ψ(t)` has
`‖S w‖ + 2 ‖T w‖ ≤ b_e Ξ` and Fourier tails `‖1_{|k_a| > λ} T w‖ ≤ c_tr^U Ξ/√λ`,
`‖1_{|k_a| > λ} S w‖ ≤ 2 m̄ c_tr^U Ξ/(λ² √λ)` beyond every `λ ≥ 1`. -/
theorem traj_tails_gL (D : EvoData L H) (t : ℝ) :
    ∃ w : MolecularFourierH2 eta, Sm eta L w = D.U t (Sm eta L D.u₀) ∧
      ‖Sm eta L w‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) w‖ ≤
        b0eU sys (FreeBoundary.tv R θ) Hunit * D.Xi ∧
      ∀ (a : Fin eta) (lam : ℝ), 1 ≤ lam →
        ‖tailMask (gF L) lam a (coulombFourierKineticH2 sys (gF L) w)‖ ≤
            cTrU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt lam ∧
          ‖tailMask (gF L) lam a (Sm eta L w)‖ ≤
            2 * sys.maxMass * (cTrU sys (FreeBoundary.tv R θ) Hunit * D.Xi) /
              (lam ^ 2 * Real.sqrt lam) := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  have hM := sys.one_le_maxMass
  obtain ⟨w, hw1, hw2⟩ := D.graph t D.u₀
  obtain ⟨hX1, hX2, hX3, hX4⟩ := Xi_parts D
  have hΞ := D.Xi_nonneg
  set b := FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit with hb
  have hb0 : 0 ≤ b := FreeBoundary.relBU_nonneg sys hV hH
  have hC : 0 ≤ FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit :=
    gLmassConst_nonneg' sys (L := L) Hunit hθ
  have hrelB : FreeBoundary.relB_gL sys L (FreeBoundary.tv R θ) Hunit = b :=
    FreeBoundary.relB_gL_eq_U sys hL _ hH
  have hSw : ‖Sm eta L w‖ = ‖Sm eta L D.u₀‖ := by
    rw [hw1, LinearIsometryEquiv.norm_map]
  have hHw : ‖H w‖ = ‖H D.u₀‖ := by rw [hw2, LinearIsometryEquiv.norm_map]
  have hTw : ‖coulombFourierKineticH2 sys (gF L) w‖ ≤ 2 * ‖H D.u₀‖ + 2 * b * ‖Sm eta L D.u₀‖ := by
    have h := FreeBoundary.kinetic_le_elliptic_gL sys L H hKernel Hunit hL0 hθ hPeriodic hC w
    rw [hrelB] at h
    change ‖coulombFourierKineticH2 sys (gF L) w‖ ≤ 2 * ‖H w‖ + 2 * b * ‖Sm eta L w‖ at h
    rw [hHw, hSw] at h
    exact h
  refine ⟨w, hw1, ?_, fun a lam hl => ?_⟩
  · rw [hSw]
    unfold b0eU
    rw [← hb]
    have : 2 * b * ‖Sm eta L D.u₀‖ ≤ 2 * b * D.Xi := mul_le_mul_of_nonneg_left hX1 (by positivity)
    linarith
  · have hl0 : 0 < lam := by linarith
    have hρ : Real.sqrt (1 / lam) ^ 2 * lam = 1 := by
      rw [Real.sq_sqrt (by positivity)]
      field_simp
    have h := FreeBoundary.tails_at_time_gL sys L H hKernel Hunit hL0 hθ hPeriodic hC D.U D.graph
      a lam (Real.sqrt (1 / lam)) hl (Real.sqrt_nonneg _) hρ D.u₀ D.v₀ D.uv t w hw1 hw2
    simp only at h
    obtain ⟨hT1, hS1⟩ := h
    rw [hrelB] at hT1 hS1
    set M0 := sys.maxMass * (‖molecularH2StateMap eta (2 * Real.pi / L) D.u₀‖ +
      2 * (2 * ‖H D.u₀‖ + 2 * b * ‖molecularH2StateMap eta (2 * Real.pi / L) D.u₀‖)) with hM0
    have hM00 : 0 ≤ M0 := by positivity
    have hM0le : M0 ≤ sys.maxMass * (b0eU sys (FreeBoundary.tv R θ) Hunit * D.Xi) := by
      rw [hM0]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      unfold b0eU
      rw [← hb]
      change ‖Sm eta L D.u₀‖ + 2 * (2 * ‖H D.u₀‖ + 2 * b * ‖Sm eta L D.u₀‖) ≤ _
      have : 2 * b * ‖Sm eta L D.u₀‖ ≤ 2 * b * D.Xi := mul_le_mul_of_nonneg_left hX1 (by positivity)
      linarith
    have htl : FreeBoundary.gLtailM sys L (FreeBoundary.tv R θ) Hunit M0 ≤
        FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit 1 *
          (sys.maxMass * (b0eU sys (FreeBoundary.tv R θ) Hunit * D.Xi)) := by
      refine (FreeBoundary.gLtailM_le_U sys hL hV hH hM00).trans ?_
      rw [gLtailMU_linear]
      exact mul_le_mul_of_nonneg_left hM0le (gLtailMU_nonneg hV hH zero_le_one)
    have hsl : Real.sqrt (1 / lam) = 1 / Real.sqrt lam := by
      rw [Real.sqrt_div' 1 hl0.le, Real.sqrt_one]
    have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hl0
    have hsl1 : 1 ≤ Real.sqrt lam := Real.one_le_sqrt.mpr hl
    have hl2 : 1 ≤ lam ^ 2 := one_le_pow₀ hl
    -- the kinetic data term
    have hdat : 2 * ‖H D.v₀‖ + 2 * b * ‖molecularH2StateMap eta (2 * Real.pi / L) D.v₀‖ ≤
        (2 + 2 * b) * D.Xi := by
      change 2 * ‖H D.v₀‖ + 2 * b * ‖Sm eta L D.v₀‖ ≤ _
      have : 2 * b * ‖Sm eta L D.v₀‖ ≤ 2 * b * D.Xi := mul_le_mul_of_nonneg_left hX4 (by positivity)
      linarith
    have hBle : (2 * sys.maxMass / lam ^ 2) *
        (2 * ‖H D.v₀‖ + 2 * b * ‖molecularH2StateMap eta (2 * Real.pi / L) D.v₀‖) +
        FreeBoundary.gLtailM sys L (FreeBoundary.tv R θ) Hunit M0 * Real.sqrt (1 / lam) ≤
        cTrU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt lam := by
      have hlsl : lam ^ 2 ≥ Real.sqrt lam := by
        have h1 : lam ≤ lam ^ 2 := le_self_pow₀ hl two_ne_zero
        have h2 : Real.sqrt lam ≤ lam := by
          rw [Real.sqrt_le_left hl0.le]
          exact h1
        linarith
      have k1 : (2 * sys.maxMass / lam ^ 2) *
          (2 * ‖H D.v₀‖ + 2 * b * ‖molecularH2StateMap eta (2 * Real.pi / L) D.v₀‖) ≤
          2 * sys.maxMass * ((2 + 2 * b) * D.Xi) / Real.sqrt lam := by
        calc (2 * sys.maxMass / lam ^ 2) *
              (2 * ‖H D.v₀‖ + 2 * b * ‖molecularH2StateMap eta (2 * Real.pi / L) D.v₀‖)
            ≤ (2 * sys.maxMass / lam ^ 2) * ((2 + 2 * b) * D.Xi) :=
              mul_le_mul_of_nonneg_left hdat (by positivity)
          _ ≤ (2 * sys.maxMass / Real.sqrt lam) * ((2 + 2 * b) * D.Xi) := by
              gcongr
          _ = _ := by ring
      have k2 : FreeBoundary.gLtailM sys L (FreeBoundary.tv R θ) Hunit M0 * Real.sqrt (1 / lam) ≤
          FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit 1 *
            (sys.maxMass * (b0eU sys (FreeBoundary.tv R θ) Hunit * D.Xi)) / Real.sqrt lam := by
        rw [hsl, mul_one_div]
        exact div_le_div_of_nonneg_right htl hsl0.le
      unfold cTrU
      rw [← hb]
      have e : (2 * sys.maxMass * (2 + 2 * b) + FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ)
          Hunit 1 * (sys.maxMass * b0eU sys (FreeBoundary.tv R θ) Hunit)) * D.Xi /
            Real.sqrt lam = 2 * sys.maxMass * ((2 + 2 * b) * D.Xi) / Real.sqrt lam +
          FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit 1 *
            (sys.maxMass * (b0eU sys (FreeBoundary.tv R θ) Hunit * D.Xi)) / Real.sqrt lam := by
        ring
      rw [e]
      linarith
    refine ⟨hT1.trans hBle, hS1.trans ?_⟩
    have hct0 : 0 ≤ cTrU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt lam := by
      have := cTrU_nonneg sys hV hH
      positivity
    calc 2 * sys.maxMass / lam ^ 2 * ((2 * sys.maxMass / lam ^ 2) *
          (2 * ‖H D.v₀‖ + 2 * b * ‖molecularH2StateMap eta (2 * Real.pi / L) D.v₀‖) +
          FreeBoundary.gLtailM sys L (FreeBoundary.tv R θ) Hunit M0 * Real.sqrt (1 / lam))
        ≤ 2 * sys.maxMass / lam ^ 2 * (cTrU sys (FreeBoundary.tv R θ) Hunit * D.Xi /
            Real.sqrt lam) := mul_le_mul_of_nonneg_left hBle (by positivity)
      _ = _ := by
          field_simp

include hKernel hL hθ hPeriodic hH in
/-- **The shells of the exact trajectory of `H_L` on the register** (physical weight): with
`B₀ = b_e Ξ`, `‖w_g P' ψ(t)‖ ≤ B₀` and `‖1_{|q_p|_∞ > T} w_g P' ψ(t)‖ ≤ (2 m̄ + 2) c_tr^U Ξ/√(g T)`
for `g T ≥ 1`. -/
theorem exact_traj_shells_gL (D : EvoData L H) (t : ℝ) (m : ℕ) (p : Fin eta) :
    ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L)) (regCoeff m (D.U t (Sm eta L D.u₀)))‖ ≤
        b0eU sys (FreeBoundary.tv R θ) Hunit * D.Xi ∧
      ∀ T : ℕ, 1 ≤ gF L * T →
        ‖maskOp (High T p) (wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
            (regCoeff m (D.U t (Sm eta L D.u₀))))‖ ≤
          (2 * sys.maxMass + 2) * (cTrU sys (FreeBoundary.tv R θ) Hunit * D.Xi) /
            Real.sqrt (gF L * T) := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  have hg : 0 < gF L := gF_pos hL0
  obtain ⟨w, hw1, hw2, hw3⟩ := traj_tails_gL sys H hKernel Hunit hL hθ hPeriodic hH D t
  have hS : regCoeff m (D.U t (Sm eta L D.u₀)) = regCoeff m (molecularH2StateMap eta (gF L) w) := by
    rw [← hw1]
  rw [hS, wPhys_regCoeff_eq sys w]
  refine ⟨?_, fun T hT => ?_⟩
  · refine (norm_regCoeff_le _).trans ((norm_add_le _ _).trans ?_)
    rw [norm_smul]
    have : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [this]
    exact hw2
  · refine (norm_high_regCoeff_le hg T p _).trans ?_
    rw [map_add, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    obtain ⟨h1, h3⟩ := hw3 p (gF L * T) hT
    have hsT : 0 < Real.sqrt (gF L * T) := Real.sqrt_pos.mpr (by linarith)
    have hl2 : 1 ≤ (gF L * T) ^ 2 := one_le_pow₀ hT
    have hct0 : 0 ≤ cTrU sys (FreeBoundary.tv R θ) Hunit * D.Xi := by
      have := cTrU_nonneg sys hV hH
      have := D.Xi_nonneg
      positivity
    have k1 : ‖tailMask (gF L) (gF L * T) p (molecularH2StateMap eta (gF L) w)‖ ≤
        2 * sys.maxMass * (cTrU sys (FreeBoundary.tv R θ) Hunit * D.Xi) / Real.sqrt (gF L * T) := by
      refine h3.trans ?_
      apply div_le_div_of_nonneg_left (by have := sys.maxMass_pos; positivity) hsT
      calc Real.sqrt (gF L * T) = 1 * Real.sqrt (gF L * T) := by ring
        _ ≤ (gF L * T) ^ 2 * Real.sqrt (gF L * T) := by gcongr
    calc ‖tailMask (gF L) (gF L * T) p (molecularH2StateMap eta (gF L) w)‖ +
          2 * ‖tailMask (gF L) (gF L * T) p (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ 2 * sys.maxMass * (cTrU sys (FreeBoundary.tv R θ) Hunit * D.Xi) / Real.sqrt (gF L * T) +
            2 * (cTrU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt (gF L * T)) :=
          add_le_add k1 (mul_le_mul_of_nonneg_left h1 (by norm_num))
      _ = _ := by ring

end ExactGL

/-! ## The first physical weight of grid trajectories -/

section GridWeight

variable (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (FreeBoundary.gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 2 * Real.pi ≤ L) (hθ : FreeBoundary.Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hH : 0 ≤ Hunit)

/-- The first physical weight constant of grid trajectories,
`b_g = (5/3) m̄ b_e + (4/3)(1 + 4A)`. -/
noncomputable def b0gU (sys : CoulombSystem eta ν) (V Hunit : ℝ) : ℝ :=
  5 / 3 * (sys.maxMass * b0eU sys V Hunit) + FreeBoundary.gridFlowConstU sys V

lemma b0gU_nonneg {V Hunit : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ b0gU sys V Hunit := by
  unfold b0gU
  have := b0eU_nonneg sys hV hH
  have := FreeBoundary.gridFlowConstU_nonneg sys hV
  have := sys.maxMass_pos
  positivity

include hKernel hL hθ hPeriodic hH in
/-- **The weight of an `H²` datum on the register**: `‖w_g P' S u₀‖ ≤ m̄ b_e Ξ`. -/
lemma datum_weight_gL (D : EvoData L H) (m : ℕ) :
    ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L)) (regCoeff m (Sm eta L D.u₀))‖ ≤
      sys.maxMass * (b0eU sys (FreeBoundary.tv R θ) Hunit * D.Xi) := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  obtain ⟨hX1, hX2, -, -⟩ := Xi_parts D
  have hC : 0 ≤ FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit :=
    gLmassConst_nonneg' sys (L := L) Hunit hθ
  have hb0 := FreeBoundary.relBU_nonneg sys hV hH
  have h1 := FreeBoundary.norm_wPhys_regCoeff_stateMap_le (m := m) (regParticlesOf sys) (gF L) D.u₀
  have h2 := h2norm_le sys L D.u₀
  have hT := FreeBoundary.kinetic_le_elliptic_gL sys L H hKernel Hunit hL0 hθ hPeriodic hC D.u₀
  rw [FreeBoundary.relB_gL_eq_U sys hL _ hH] at hT
  change ‖coulombFourierKineticH2 sys (gF L) D.u₀‖ ≤
    2 * ‖H D.u₀‖ + 2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * ‖Sm eta L D.u₀‖ at hT
  change ‖D.u₀‖ ≤ sys.maxMass * (‖Sm eta L D.u₀‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) D.u₀‖)
    at h2
  refine h1.trans (h2.trans (mul_le_mul_of_nonneg_left ?_ sys.maxMass_pos.le))
  unfold b0eU
  have : 2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * ‖Sm eta L D.u₀‖ ≤
      2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * D.Xi :=
    mul_le_mul_of_nonneg_left hX1 (by positivity)
  linarith

include hKernel hL hθ hPeriodic hH in
/-- **The first physical weight of the grid trajectory** (uniform in `L ≥ 2π`, over the kernel
class and the time): `‖w_g U_g(t) P' ψ₀‖ ≤ b_g Ξ`. -/
theorem grid_traj_weight_gL (D : EvoData L H) (m : ℕ) {κ : Lat3 → ℝ}
    (hκb : ∀ x, |κ x| ≤ PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ) * coul x)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (t : ℝ) :
    ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L)) (Ug t (regCoeff m (Sm eta L D.u₀)))‖ ≤
      b0gU sys (FreeBoundary.tv R θ) Hunit * D.Xi := by
  have hV := hθ.tv_nonneg
  have h := FreeBoundary.norm_wPhys_gridFlow_le_gL sys hL hV hκb (Ug t) (hgcomm t)
    (regCoeff m (Sm eta L D.u₀))
  refine h.trans ?_
  have hw := datum_weight_gL sys H hKernel Hunit hL hθ hPeriodic hH D m
  obtain ⟨hX1, -, -, -⟩ := Xi_parts D
  have hx : ‖regCoeff m (Sm eta L D.u₀)‖ ≤ D.Xi := (norm_regCoeff_le _).trans hX1
  have hJ := FreeBoundary.gridFlowConstU_nonneg sys hV
  unfold b0gU
  have e1 := mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 5 / 3)
  have e2 := mul_le_mul_of_nonneg_left hx hJ
  change ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (2 * Real.pi / L))
    (regCoeff m (Sm eta L D.u₀))‖ ≤ _ at hw
  linarith

end GridWeight

end KineticLog
