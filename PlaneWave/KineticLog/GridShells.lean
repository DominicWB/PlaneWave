import PlaneWave.KineticLog.GridDuhamel

/-!
# Logarithmic kinetic bound, part 12: momentum shells of the trajectories

The observable step of the grid comparison pairs the separated (high grid energy) part of the
difference with `T_p` applied to the trajectories, through `‖(G + c) T_p φ‖`.  This needs the
second weighted moment `‖W T_p φ‖` of a register vector `φ`, which is controlled by its first
weighted tails at every sup-norm shell:

* **layer cake** (`norm_wM_regKin_shells`): if `‖W φ‖ ≤ B₀` and the shells satisfy
  `‖1_{|q_p|_∞ > T} W φ‖ ≤ B/√T` for `T₀ ≤ T ≤ m`, then
  `‖W T_p φ‖ ≤ 3 g² m √m (2 T₀² B₀ + 4 B)`, i.e. `O(B K^{3/2})`.  The proof writes
  `|q_p|⁴ ≤ 36 Σ_T (T+1)³ 1_{|q_p|_∞ > T}` (`nsq_sq_le_shells`) and sums the shells; the top
  shells `m < T < 2m` use the tail at `m` (no tail estimate above `K` is assumed).

This replaces the quarter-power estimate `‖G_s^{1/4} T_p l‖ ≤ C 𝒟 √log(2+K)` of
`lem:kinetic-high` by the full-power estimate `‖G_s T_p φ‖ ≤ C 𝒟 K^{3/2}`, which together with the
spectral factor `(2Λ)^{-1}` gives the same `K^{-3}` without the `√log` (a slightly stronger
intermediate bound).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Layer cake -/

/-- `n⁴ ≤ 4 Σ_{T < n} (T+1)³`. -/
lemma pow_four_le_sum_cubes (n : ℕ) :
    ((n : ℝ)) ^ 4 ≤ 4 * ∑ T ∈ Finset.range n, ((T : ℝ) + 1) ^ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [sq_nonneg (n : ℝ), mul_nonneg h0 (sq_nonneg (n : ℝ))]

open Classical in
/-- **The shell decomposition of the fourth power of a register momentum**:
`|q_p|⁴ ≤ 36 Σ_{T < 2m} (T+1)³ 1_{|q_p|_∞ > T}`. -/
lemma nsq_sq_le_shells {m : ℕ} (p : Fin eta) (q : RCfg eta m) :
    nsq (gl (q p)) ^ 2 ≤
      36 * ∑ T ∈ Finset.range (2 * m), ((T : ℝ) + 1) ^ 3 * (if High T p q then 1 else 0) := by
  classical
  set S := ∑ T ∈ Finset.range (2 * m), ((T : ℝ) + 1) ^ 3 * (if High T p q then 1 else 0) with hS
  have hbox := gl_inBox (q p)
  have hc : ∀ c : Fin 3, (((gl (q p) c : ℤ) : ℝ) ^ 2) ^ 2 ≤ 4 * S := by
    intro c
    set x := gl (q p) c with hx
    set n := x.natAbs with hn
    have hnx : ((n : ℕ) : ℝ) = |((x : ℤ) : ℝ)| := by
      rw [← Int.cast_natCast, hn, Int.natCast_natAbs, Int.cast_abs]
    have h4 : (((x : ℤ) : ℝ) ^ 2) ^ 2 = ((n : ℝ)) ^ 4 := by
      rw [hnx, ← sq_abs ((x : ℤ) : ℝ)]
      ring
    have hn2m : n ≤ 2 * m := by
      have h1 : |x| ≤ ((2 * m : ℕ) : ℤ) := hbox c
      rw [← Int.natCast_natAbs] at h1
      exact_mod_cast h1
    rw [h4]
    refine (pow_four_le_sum_cubes n).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hfilter : ∑ T ∈ Finset.range (2 * m), ((T : ℝ) + 1) ^ 3 * (if High T p q then 1 else 0) =
        ∑ T ∈ (Finset.range (2 * m)).filter (fun T => High T p q), ((T : ℝ) + 1) ^ 3 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun T _ => ?_
      split_ifs <;> simp
    rw [hS, hfilter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => ?_) (fun T _ _ => by positivity)
    rw [Finset.mem_range] at hT
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), fun hb => ?_⟩
    have h1 : |x| ≤ (T : ℤ) := hb c
    rw [← Int.natCast_natAbs] at h1
    have h2 : n ≤ T := by exact_mod_cast h1
    omega
  have hsum : nsq (gl (q p)) = ∑ c : Fin 3, ((gl (q p) c : ℤ) : ℝ) ^ 2 := nsq_eq_sum _
  rw [hsum, Fin.sum_univ_three]
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  set a := ((gl (q p) 0 : ℤ) : ℝ) ^ 2
  set b := ((gl (q p) 1 : ℤ) : ℝ) ^ 2
  set e := ((gl (q p) 2 : ℤ) : ℝ) ^ 2
  have h3 : (a + b + e) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + e ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - e), sq_nonneg (a - e)]
  linarith

omit [Fintype ν] in
/-- The register kinetic symbol in lattice units: `A_p(q) = (g²/2) |q_p|²/m_p`. -/
lemma regKinSym_eq (sys : CoulombSystem eta ν) (g : ℝ) {m : ℕ} (p : Fin eta) (q : RCfg eta m) :
    regKinSym sys g p q = g ^ 2 / 2 * (nsq (gl (q p)) / sys.mass p) := by
  unfold regKinSym regSymbol
  have : latticeNormSq (liftCfg q p) = nsq (gl (q p)) := rfl
  rw [this]
  ring

omit [Fintype ν] in
open Classical in
/-- `A_p(q)² ≤ 9 g⁴ Σ_{T < 2m} (T+1)³ 1_{|q_p|_∞ > T}`. -/
lemma regKinSym_sq_le_shells (sys : CoulombSystem eta ν) (g : ℝ) {m : ℕ} (p : Fin eta)
    (q : RCfg eta m) :
    regKinSym sys g p q ^ 2 ≤
      9 * g ^ 4 * ∑ T ∈ Finset.range (2 * m), ((T : ℝ) + 1) ^ 3 *
          (if High T p q then 1 else 0) := by
  have h := nsq_sq_le_shells p q
  have hn := nsq_nonneg (gl (q p))
  have hm := sys.one_le_mass p
  have h1 : nsq (gl (q p)) / sys.mass p ≤ nsq (gl (q p)) := div_le_self hn hm
  have h2 : 0 ≤ nsq (gl (q p)) / sys.mass p := div_nonneg hn (by linarith)
  rw [regKinSym_eq]
  have h3 : (g ^ 2 / 2 * (nsq (gl (q p)) / sys.mass p)) ^ 2 ≤
      (g ^ 2 / 2) ^ 2 * nsq (gl (q p)) ^ 2 :=
    by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) (by positivity)
  refine h3.trans ?_
  have h4 : (g ^ 2 / 2) ^ 2 * nsq (gl (q p)) ^ 2 ≤ (g ^ 2 / 2) ^ 2 * (36 *
      ∑ T ∈ Finset.range (2 * m), ((T : ℝ) + 1) ^ 3 * (if High T p q then 1 else 0)) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  refine h4.trans (le_of_eq ?_)
  ring

/-! ## The second weighted moment from the shells -/

omit [Fintype ν] in
/-- **The second weighted moment from the first weighted shells** (layer cake): if
`‖W φ‖ ≤ B₀` and `‖1_{|q_p|_∞ > T} W φ‖ ≤ B/√T` for `T₀ ≤ T ≤ m`, then
`‖W A_p φ‖ ≤ 3 g² m √m (2 T₀² B₀ + 4 B)`. -/
theorem norm_wM_regKin_shells (sys : CoulombSystem eta ν) (g : ℝ) (m : ℕ) (hm : 1 ≤ m)
    (p : Fin eta) (φ : EuclideanSpace ℂ (RCfg eta m)) {T₀ : ℕ} (hT₀ : 1 ≤ T₀) (hT₀m : T₀ ≤ m)
    {B₀ B : ℝ} (hB₀ : ‖wMul (wM (regParticlesOf sys)) φ‖ ≤ B₀) (hB : 0 ≤ B)
    (htail : ∀ T : ℕ, T₀ ≤ T → T ≤ m →
      ‖maskOp (High T p) (wMul (wM (regParticlesOf sys)) φ)‖ ≤ B / Real.sqrt T) :
    ‖wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys g p) φ)‖ ≤
      3 * g ^ 2 * ((m : ℝ) * Real.sqrt m) * (2 * (T₀ : ℝ) ^ 2 * B₀ + 4 * B) := by
  classical
  set z := wMul (wM (regParticlesOf sys)) φ with hz
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans hB₀
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hT₀r : (1 : ℝ) ≤ T₀ := by exact_mod_cast hT₀
  have hT₀mr : (T₀ : ℝ) ≤ m := by exact_mod_cast hT₀m
  have hcomm : wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys g p) φ) =
      wMul (regKinSym sys g p) z := by
    ext q
    simp only [hz, wMul_apply]
    ring
  rw [hcomm]
  -- the square as a shell sum
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
  -- each shell term
  have hterm : ∀ T ∈ Finset.range (2 * m), ((T : ℝ) + 1) ^ 3 * ‖maskOp (High T p) z‖ ^ 2 ≤
      (T₀ : ℝ) ^ 3 * B₀ ^ 2 + 8 * (m : ℝ) ^ 2 * B ^ 2 := by
    intro T hT
    rw [Finset.mem_range] at hT
    have hTr : (T : ℝ) + 1 ≤ 2 * m := by
      have : T + 1 ≤ 2 * m := hT
      exact_mod_cast this
    have hmask0 := norm_nonneg (maskOp (High T p) z)
    rcases lt_or_ge T T₀ with h1 | h1
    · -- low shells: the first weighted norm
      have hT1 : (T : ℝ) + 1 ≤ T₀ := by exact_mod_cast h1
      have hmk : ‖maskOp (High T p) z‖ ≤ B₀ := (norm_maskOp_le _ z).trans hB₀
      have a1 : ((T : ℝ) + 1) ^ 3 ≤ (T₀ : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hT1 3
      have a2 : ‖maskOp (High T p) z‖ ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ hmask0 hmk 2
      have := mul_le_mul a1 a2 (sq_nonneg _) (by positivity)
      have : 0 ≤ 8 * (m : ℝ) ^ 2 * B ^ 2 := by positivity
      linarith
    · rcases le_or_gt T m with h2 | h2
      · -- middle shells: the tail at `T`
        have hT1 : (1 : ℝ) ≤ T := hT₀r.trans (by exact_mod_cast h1)
        have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
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
          nlinarith [sq_nonneg B]
        nlinarith [sq_nonneg B₀, pow_nonneg (by linarith : (0 : ℝ) ≤ T₀) 3]
      · -- top shells: the tail at `m`
        have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
        have hmk : ‖maskOp (High T p) z‖ ≤ B / Real.sqrt m :=
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
        nlinarith [sq_nonneg B₀, pow_nonneg (by linarith : (0 : ℝ) ≤ T₀) 3]
  have hsum : ∑ T ∈ Finset.range (2 * m), ((T : ℝ) + 1) ^ 3 * ‖maskOp (High T p) z‖ ^ 2 ≤
      2 * m * ((T₀ : ℝ) ^ 3 * B₀ ^ 2 + 8 * (m : ℝ) ^ 2 * B ^ 2) := by
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  -- the final square comparison
  have hR0 : 0 ≤ 3 * g ^ 2 * ((m : ℝ) * Real.sqrt m) * (2 * (T₀ : ℝ) ^ 2 * B₀ + 4 * B) := by
    positivity
  have hsqm : Real.sqrt m ^ 2 = m := Real.sq_sqrt (by linarith)
  have hfin : ‖wMul (regKinSym sys g p) z‖ ^ 2 ≤
      (3 * g ^ 2 * ((m : ℝ) * Real.sqrt m) * (2 * (T₀ : ℝ) ^ 2 * B₀ + 4 * B)) ^ 2 := by
    refine hsq.trans ?_
    have e : (3 * g ^ 2 * ((m : ℝ) * Real.sqrt m) * (2 * (T₀ : ℝ) ^ 2 * B₀ + 4 * B)) ^ 2 =
        9 * g ^ 4 * ((m : ℝ) ^ 3 * (2 * (T₀ : ℝ) ^ 2 * B₀ + 4 * B) ^ 2) := by
      have : ((m : ℝ) * Real.sqrt m) ^ 2 = (m : ℝ) ^ 3 := by
        rw [mul_pow, hsqm]
        ring
      rw [mul_pow, mul_pow, this]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (by positivity)
    have hm3 : (m : ℝ) ≤ (m : ℝ) ^ 3 := by nlinarith
    have hT4 : (T₀ : ℝ) ^ 3 ≤
        (T₀ : ℝ) ^ 4 := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ T₀) 3]
    have k1 : 2 * (m : ℝ) * ((T₀ : ℝ) ^ 3 * B₀ ^ 2) ≤
        (m : ℝ) ^ 3 * (4 * (T₀ : ℝ) ^ 4 * B₀ ^ 2) := by
      have hB2 := sq_nonneg B₀
      calc 2 * (m : ℝ) * ((T₀ : ℝ) ^ 3 * B₀ ^ 2) ≤ 2 * (m : ℝ) ^ 3 * ((T₀ : ℝ) ^ 4 * B₀ ^ 2) := by
            gcongr
        _ ≤ (m : ℝ) ^ 3 * (4 * (T₀ : ℝ) ^ 4 * B₀ ^ 2) := by
            have : 0 ≤ (m : ℝ) ^ 3 * ((T₀ : ℝ) ^ 4 * B₀ ^ 2) := by positivity
            nlinarith
    have k2 : 0 ≤ (m : ℝ) ^ 3 * (16 * (T₀ : ℝ) ^ 2 * B₀ * B) := by positivity
    calc 2 * (m : ℝ) * ((T₀ : ℝ) ^ 3 * B₀ ^ 2 + 8 * (m : ℝ) ^ 2 * B ^ 2)
        = 2 * (m : ℝ) * ((T₀ : ℝ) ^ 3 * B₀ ^ 2) + 16 * (m : ℝ) ^ 3 * B ^ 2 := by ring
      _ ≤ (m : ℝ) ^ 3 * (4 * (T₀ : ℝ) ^ 4 * B₀ ^ 2) + 16 * (m : ℝ) ^ 3 * B ^ 2 +
            (m : ℝ) ^ 3 * (16 * (T₀ : ℝ) ^ 2 * B₀ * B) := by linarith
      _ = (m : ℝ) ^ 3 * (2 * (T₀ : ℝ) ^ 2 * B₀ + 4 * B) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR0 two_ne_zero).mp hfin

end KineticLog
