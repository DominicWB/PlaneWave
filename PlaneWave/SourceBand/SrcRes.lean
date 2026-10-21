import PlaneWave.SourceBand.MovingRegister

/-!
# Source band block, part 6: `prop:src-res`

The resonant part of the near-cutoff coupling `V_nc = R W (P - Q)`: per channel `j` and dyadic
scale `k`, the hops `2^k ≤ |ν| < 2^{k+1}` (lattice units) whose mismatch polynomial satisfies
`|F_c(ν)| ≤ κ 2^k` (`c` the drift of the input; the text's `|Ω| ≤ ϱ/μ` is `κ = 2/g`).

* `slabF_swap`: the mismatch seen from the output, `F_{c(p)}(ν) = -F_{c(q)}(-ν)`;
* `resK_schur` (eq:twoside): rows and columns `≤ 11000 (1 + κ) c_j`, by `lem:slab` (i);
* **`resK_eq_zero_of_large`** (the missing step of review S1 §2.K): a resonant hop from the cube
  has `|ν| ≤ 2√3 n + κ` (physical: `‖ν‖ ≤ 2√3 K + 2`), so only `K_res = ⌊log₂(2√3 n + κ)⌋ + 1`
  scales occur;
* **`prop_src_res`**: `|⟨ψ(s), V_nc^res φ_v(s)⟩| ≤ C Ξ M K^{-3} log K` for `K ≥ 2`, every good
  datum `v` (`φ_v = e^{iH_N τ} A_{p₀} v`) and all times.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal FSFlux

namespace FSBand

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The resonant kernel -/

section Res

omit [Fintype ν] in
lemma tr_neg (j : Ch eta) (x : Lattice3) : tr j (-x) = -tr j x := by
  have h := tr_sub j 0 x
  have h0 : tr j (0 : Lattice3) = 0 := by cases j <;> simp [tr]
  rw [zero_sub, h0, zero_sub] at h
  exact h

omit [Fintype ν] in
/-- **The mismatch seen from the output**: on a hop `q = p + τ_j(ν)`,
`F_{c(p)}(ν) = -F_{c(q)}(-ν)`. -/
lemma slabF_swap (sys : CoulombSystem eta ν) {j : Ch eta} {q p : Cf eta} (h : OnCh j q p) :
    slabF (cCh sys j p) (q (lead j) - p (lead j)) =
      -slabF (cCh sys j q) (-(q (lead j) - p (lead j))) := by
  set x := q (lead j) - p (lead j)
  have e1 : q = p + tr j x := h
  have e2 : p = q + tr j (-x) := by rw [tr_neg, e1]; abel
  have h1 := E_hop sys 1 j p x
  have h2 := E_hop sys 1 j q (-x)
  rw [← e1] at h1
  rw [← e2] at h2
  have hμ := muCh_pos sys j
  have hsum : 1 ^ 2 / (2 * muCh sys j) * (slabF (cCh sys j p) x + slabF (cCh sys j q) (-x)) = 0 := by
    rw [mul_add]; linarith
  have hne : (1 : ℝ) ^ 2 / (2 * muCh sys j) ≠ 0 := by positivity
  have := (mul_eq_zero.mp hsum).resolve_left hne
  linarith

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (κ : ℝ)

open Classical in
/-- **The resonant near-cutoff kernel** of channel `j` at scale `k` (`prop:src-res`): output
outside the cube, input in the cube but not in `Q`, a hop `2^k ≤ |ν| < 2^{k+1}` with
`|F_{c(p)}(ν)| ≤ κ 2^k`. -/
noncomputable def resK (j : Ch eta) (k : ℕ) (q p : Cf eta) : ℂ :=
  if q ∉ fourierConfigCube eta n ∧ p ∈ fourierConfigCube eta n ∧ ¬ InQ (n : ℝ) p ∧ OnCh j q p ∧
      (4 : ℝ) ^ k ≤ nsq (q (lead j) - p (lead j)) ∧ nsq (q (lead j) - p (lead j)) < 4 ^ (k + 1) ∧
      |slabF (cCh sys j p) (q (lead j) - p (lead j))| ≤ κ * 2 ^ k
  then potKernel (sysCh sys j) L q p else 0

variable {sys L n κ}

open Classical in
lemma resK_ne_zero {j : Ch eta} {k : ℕ} {q p : Cf eta} (h : resK sys L n κ j k q p ≠ 0) :
    q ∉ fourierConfigCube eta n ∧ p ∈ fourierConfigCube eta n ∧ ¬ InQ (n : ℝ) p ∧ OnCh j q p ∧
      (4 : ℝ) ^ k ≤ nsq (q (lead j) - p (lead j)) ∧ nsq (q (lead j) - p (lead j)) < 4 ^ (k + 1) ∧
      |slabF (cCh sys j p) (q (lead j) - p (lead j))| ≤ κ * 2 ^ k := by
  unfold resK at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

open Classical in
/-- The pointwise majorant of the resonant kernel. -/
lemma norm_resK_le {L : ℝ} (hL : 0 < L) (j : Ch eta) (k : ℕ) (q p : Cf eta) :
    ‖resK sys L n κ j k q p‖ ≤
      if OnCh j q p ∧ (4 : ℝ) ^ k ≤ nsq (q (lead j) - p (lead j)) ∧
          nsq (q (lead j) - p (lead j)) < 4 ^ (k + 1) ∧
          |slabF (cCh sys j p) (q (lead j) - p (lead j))| ≤ κ * 2 ^ k
      then chC sys L j / 4 ^ k else 0 := by
  by_cases h : resK sys L n κ j k q p = 0
  · rw [h, norm_zero]; split_ifs <;> [exact div_nonneg (chC_nonneg sys hL j) (by positivity); rfl]
  · obtain ⟨-, -, -, hon, h1, h2, h3⟩ := resK_ne_zero h
    rw [if_pos ⟨hon, h1, h2, h3⟩]
    unfold resK
    rw [if_pos (by obtain ⟨a1, a2, a3, a4⟩ := resK_ne_zero h; exact ⟨a1, a2, a3, a4⟩)]
    refine (potKernel_sysCh_le sys hL j q p).trans ?_
    unfold chMaj
    rw [if_pos hon]
    exact div_le_div_of_nonneg_left (chC_nonneg sys hL j) (by positivity)
      (by rw [← nsq_eq_latticeNormSq]; exact h1)

/-- The slab set of a drift `c` at scale `k`. -/
def slabSet (c : Fin 3 → ℝ) (κ : ℝ) (k : ℕ) (x : Lattice3) : Prop :=
  (4 : ℝ) ^ k ≤ nsq x ∧ nsq x < 4 ^ (k + 1) ∧ |slabF c x| ≤ κ * 2 ^ k

lemma slabSet_count (c : Fin 3 → ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (k : ℕ) (T : Finset Lattice3)
    (hT : ∀ x ∈ T, slabSet c κ k x) : (T.card : ℝ) ≤ 11000 * 4 ^ k * (1 + κ) := by
  have hr : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h := FSLattice.slab_count c (ρ := (2 : ℝ) ^ k) (δ := κ * 2 ^ k) hr (by positivity) T
    (fun x hx => by
      obtain ⟨h1, h2, h3⟩ := hT x hx
      refine ⟨by rw [two_pow_sq, lsq_eq_nsq]; exact h1, ?_, h3⟩
      rw [two_pow_sq, lsq_eq_nsq]
      have : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by ring
      linarith)
  rw [two_pow_sq] at h
  have e : κ * 2 ^ k / 2 ^ k = κ := by field_simp
  rwa [e] at h

open Classical in
/-- **eq:twoside**: the resonant kernel at one scale is Schur bounded by `11000 (1 + κ) c_j`. -/
theorem resK_schur {L : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ) (j : Ch eta) (k : ℕ) :
    SchurBound (resK sys L n κ j k) (11000 * (1 + κ) * chC sys L j)
      (11000 * (1 + κ) * chC sys L j) := by
  have hc := chC_nonneg sys hL j
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  -- rows
  have hrow : ∀ q, (Summable fun p => ‖resK sys L n κ j k q p‖) ∧
      ∑' p, ‖resK sys L n κ j k q p‖ ≤ 11000 * (1 + κ) * chC sys L j := by
    intro q
    set F : Cf eta → ℝ := fun p =>
      if (4 : ℝ) ^ k ≤ nsq (q (lead j) - p (lead j)) ∧ nsq (q (lead j) - p (lead j)) < 4 ^ (k + 1) ∧
          |slabF (cCh sys j p) (q (lead j) - p (lead j))| ≤ κ * 2 ^ k
      then chC sys L j / 4 ^ k else 0
    have hmaj : ∀ p, ‖resK sys L n κ j k q p‖ ≤ if OnCh j q p then F p else 0 := by
      intro p
      refine (norm_resK_le hL j k q p).trans (le_of_eq ?_)
      by_cases hon : OnCh j q p
      · simp only [F, if_pos hon]
        by_cases hh : (4 : ℝ) ^ k ≤ nsq (q (lead j) - p (lead j)) ∧
            nsq (q (lead j) - p (lead j)) < 4 ^ (k + 1) ∧
            |slabF (cCh sys j p) (q (lead j) - p (lead j))| ≤ κ * 2 ^ k
        · rw [if_pos ⟨hon, hh⟩, if_pos hh]
        · rw [if_neg (fun h => hh h.2), if_neg hh]
      · rw [if_neg (fun h => hon h.1), if_neg hon]
    -- along the row the slab set is the output's, reflected
    have hF : ∀ x : Lattice3, F (q - tr j x) =
        chC sys L j / 4 ^ k * (if slabSet (cCh sys j q) κ k (0 + -x) then 1 else 0) := by
      intro x
      have hon : OnCh j q (q - tr j x) := onCh_of_eq (ν := x) (by abel)
      have hl : q (lead j) - (q - tr j x) (lead j) = x := lead_sub_tr j q x
      simp only [F]
      rw [slabF_swap sys hon, hl, zero_add]
      unfold slabSet
      rw [nsq_neg, abs_neg]
      split_ifs <;> simp
    have hs := tsum_shell_shift_le (sh := slabSet (cCh sys j q) κ k)
      (slabSet_count (cCh sys j q) hκ k) 0 Neg.neg (Or.inr rfl)
    have hsF : Summable fun x : Lattice3 => F (q - tr j x) := by
      simp only [hF]; exact hs.1.mul_left _
    have hsum : Summable fun p => if OnCh j q p then F p else 0 := (summable_row_iff j q F).mpr hsF
    refine ⟨hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hmaj, ?_⟩
    calc ∑' p, ‖resK sys L n κ j k q p‖ ≤ ∑' p, (if OnCh j q p then F p else 0) :=
          (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hmaj).tsum_le_tsum hmaj hsum
      _ = ∑' x, F (q - tr j x) := tsum_row j q F
      _ = chC sys L j / 4 ^ k * ∑' x : Lattice3, (if slabSet (cCh sys j q) κ k (0 + -x) then 1 else 0) := by
          simp only [hF]; exact tsum_mul_left
      _ ≤ chC sys L j / 4 ^ k * (11000 * 4 ^ k * (1 + κ)) :=
          mul_le_mul_of_nonneg_left hs.2 (by positivity)
      _ = 11000 * (1 + κ) * chC sys L j := by field_simp
  -- columns
  have hcol : ∀ p, (Summable fun q => ‖resK sys L n κ j k q p‖) ∧
      ∑' q, ‖resK sys L n κ j k q p‖ ≤ 11000 * (1 + κ) * chC sys L j := by
    intro p
    set F : Cf eta → ℝ := fun q =>
      if (4 : ℝ) ^ k ≤ nsq (q (lead j) - p (lead j)) ∧ nsq (q (lead j) - p (lead j)) < 4 ^ (k + 1) ∧
          |slabF (cCh sys j p) (q (lead j) - p (lead j))| ≤ κ * 2 ^ k
      then chC sys L j / 4 ^ k else 0
    have hmaj : ∀ q, ‖resK sys L n κ j k q p‖ ≤ if OnCh j q p then F q else 0 := by
      intro q
      refine (norm_resK_le hL j k q p).trans (le_of_eq ?_)
      by_cases hon : OnCh j q p
      · simp only [F, if_pos hon]
        by_cases hh : (4 : ℝ) ^ k ≤ nsq (q (lead j) - p (lead j)) ∧
            nsq (q (lead j) - p (lead j)) < 4 ^ (k + 1) ∧
            |slabF (cCh sys j p) (q (lead j) - p (lead j))| ≤ κ * 2 ^ k
        · rw [if_pos ⟨hon, hh⟩, if_pos hh]
        · rw [if_neg (fun h => hh h.2), if_neg hh]
      · rw [if_neg (fun h => hon h.1), if_neg hon]
    have hF : ∀ x : Lattice3, F (p + tr j x) =
        chC sys L j / 4 ^ k * (if slabSet (cCh sys j p) κ k (0 + id x) then 1 else 0) := by
      intro x
      have hl : (p + tr j x) (lead j) - p (lead j) = x := lead_add_tr j p x
      simp only [F]
      rw [hl, zero_add, id]
      unfold slabSet
      split_ifs <;> simp
    have hs := tsum_shell_shift_le (sh := slabSet (cCh sys j p) κ k)
      (slabSet_count (cCh sys j p) hκ k) 0 id (Or.inl rfl)
    have hsF : Summable fun x : Lattice3 => F (p + tr j x) := by
      simp only [hF]; exact hs.1.mul_left _
    have hsum : Summable fun q => if OnCh j q p then F q else 0 := (summable_col_iff j p F).mpr hsF
    refine ⟨hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hmaj, ?_⟩
    calc ∑' q, ‖resK sys L n κ j k q p‖ ≤ ∑' q, (if OnCh j q p then F q else 0) :=
          (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hmaj).tsum_le_tsum hmaj hsum
      _ = ∑' x, F (p + tr j x) := tsum_col j p F
      _ = chC sys L j / 4 ^ k * ∑' x : Lattice3, (if slabSet (cCh sys j p) κ k (0 + id x) then 1 else 0) := by
          simp only [hF]; exact tsum_mul_left
      _ ≤ chC sys L j / 4 ^ k * (11000 * 4 ^ k * (1 + κ)) :=
          mul_le_mul_of_nonneg_left hs.2 (by positivity)
      _ = 11000 * (1 + κ) * chC sys L j := by field_simp
  exact ⟨fun q => (hrow q).1, fun q => (hrow q).2, fun p => (hcol p).1, fun p => (hcol p).2⟩

/-- **A resonant hop from the cube is short**: `2^k ≤ |ν| ≤ 2√3 n + κ` (the missing step of
review S1 §2.K; physically `‖ν‖ ≤ 2√3 K + 2`). -/
lemma resK_short {j : Ch eta} {k : ℕ} {q p : Cf eta} (hκ : 0 ≤ κ)
    (h : resK sys L n κ j k q p ≠ 0) : (2 : ℝ) ^ k ≤ 2 * Real.sqrt 3 * n + κ := by
  obtain ⟨-, hp, -, hon, h1, -, h3⟩ := resK_ne_zero h
  set x := q (lead j) - p (lead j)
  set c := cCh sys j p
  have hc2 : ∑ i, c i ^ 2 ≤ 3 * (n : ℝ) ^ 2 := by
    refine cCh_sq_le sys j p fun b _ => ?_
    have := rho_le_of_mem_cube hp b
    rw [mem_fourierConfigCube_iff] at hp
    have hcoord : ∀ i : Fin 3, ((p b i : ℤ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := fun i => by
      have h := hp b i
      have h1 : (-(n : ℝ)) ≤ (p b i : ℝ) := by exact_mod_cast h.1
      have h2 : ((p b i : ℤ) : ℝ) ≤ n := by exact_mod_cast h.2
      nlinarith
    unfold nsq; linarith [hcoord 0, hcoord 1, hcoord 2]
  have hr : (2 : ℝ) ^ k ≤ rho x := by
    unfold rho
    exact Real.le_sqrt_of_sq_le (by rw [two_pow_sq, lsq_eq_nsq]; exact h1)
  have hcn : Real.sqrt (∑ i, c i ^ 2) ≤ Real.sqrt 3 * n := by
    rw [show Real.sqrt 3 * (n : ℝ) = Real.sqrt (3 * (n : ℝ) ^ 2) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (Nat.cast_nonneg n)]]
    exact Real.sqrt_le_sqrt hc2
  have hdot : -(rho x * Real.sqrt (∑ i, c i ^ 2)) ≤ ∑ i, (x i : ℝ) * c i := by
    have h := dot_sq_le c x
    have h' : |∑ i, (x i : ℝ) * c i| ≤ rho x * Real.sqrt (∑ i, c i ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs, rho, ← Real.sqrt_mul (lsq_nonneg x)]
      exact Real.sqrt_le_sqrt h
    linarith [neg_abs_le (∑ i, (x i : ℝ) * c i)]
  have hF : rho x ^ 2 - 2 * (rho x * (Real.sqrt 3 * n)) ≤ slabF c x := by
    unfold slabF
    rw [rho_sq]
    have := mul_le_mul_of_nonneg_left hcn (rho_nonneg x)
    linarith
  have hFk : slabF c x ≤ κ * rho x := by
    have := (le_abs_self _).trans h3
    have := mul_le_mul_of_nonneg_left hr hκ
    linarith
  have hρ0 : 0 < rho x := lt_of_lt_of_le (by positivity) hr
  have : rho x ≤ 2 * Real.sqrt 3 * n + κ := by
    by_contra hc; push Not at hc
    nlinarith
  linarith

lemma resK_eq_zero_of_large {j : Ch eta} {k : ℕ} (hκ : 0 ≤ κ)
    (hk : 2 * Real.sqrt 3 * n + κ < (2 : ℝ) ^ k) (q p : Cf eta) : resK sys L n κ j k q p = 0 := by
  by_contra h
  exact absurd (resK_short hκ h) (not_le.mpr hk)

/-- The number of resonant scales: `K_res = log₂ ⌈2√3 n + κ⌉ + 1`. -/
noncomputable def Kres (n : ℕ) (κ : ℝ) : ℕ := Nat.log 2 ⌈2 * Real.sqrt 3 * n + κ⌉₊ + 1

lemma resK_eq_zero_of_ge {j : Ch eta} {k : ℕ} (hκ : 0 ≤ κ) (hk : Kres n κ ≤ k) (q p : Cf eta) :
    resK sys L n κ j k q p = 0 := by
  refine resK_eq_zero_of_large hκ ?_ q p
  set X := 2 * Real.sqrt 3 * n + κ
  set m := ⌈X⌉₊
  have h1 : (m : ℝ) < 2 ^ (Nat.log 2 m + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
  have h2 : X ≤ m := Nat.le_ceil X
  have h3 : (2 : ℝ) ^ (Nat.log 2 m + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  linarith

end Res

/-! ## The number of resonant scales -/

/-- The constant of `K_res ≤ C_K log K`. -/
noncomputable def CKres (g κ : ℝ) : ℝ :=
  2 / Real.log 2 + |Real.log (2 * Real.sqrt 3 / g + (κ + 1) / 2)| / Real.log 2 ^ 2

lemma Kres_le_log {g κ : ℝ} (hg : 0 < g) (hκ : 0 ≤ κ) {n : ℕ} (hK : 2 ≤ g * n) :
    (Kres n κ : ℝ) ≤ CKres g κ * Real.log (g * n) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K := g * (n : ℝ) with hK_def
  have hn1 : (1 : ℝ) ≤ n := by
    by_contra h; push Not at h
    have : (n : ℝ) = 0 := by
      have : n = 0 := by exact_mod_cast (Nat.lt_one_iff.mp (by exact_mod_cast h))
      exact_mod_cast this
    rw [hK_def, this, mul_zero] at hK; linarith
  set X := 2 * Real.sqrt 3 * n + κ
  set m := ⌈X⌉₊
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hX : 0 < X := by simp only [X]; nlinarith
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hX)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
  have hpow : (2 : ℝ) ^ (Nat.log 2 m) ≤ m := by exact_mod_cast Nat.pow_log_le_self 2 hm0
  have hlog1 : (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  set B₀ := 2 * Real.sqrt 3 / g + (κ + 1) / 2
  have hB₀ : 0 < B₀ := by positivity
  have hmK : (m : ℝ) ≤ K * B₀ := by
    have h1 : (m : ℝ) < X + 1 := Nat.ceil_lt_add_one hX.le
    have e : K * B₀ = 2 * Real.sqrt 3 * n + K * ((κ + 1) / 2) := by
      simp only [B₀, hK_def]; field_simp
    rw [e]
    have : κ + 1 ≤ K * ((κ + 1) / 2) := by nlinarith
    simp only [X] at h1; linarith
  have hlogm : Real.log m ≤ Real.log K + Real.log B₀ := by
    rw [← Real.log_mul (by positivity) hB₀.ne']
    exact Real.log_le_log (by positivity) hmK
  have hlogK : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hK
  have hnat : (Nat.log 2 m : ℝ) ≤ (Real.log K + Real.log B₀) / Real.log 2 := by
    rw [le_div_iff₀ hl2]; linarith
  have hb : Real.log B₀ ≤ |Real.log B₀| * (Real.log K / Real.log 2) := by
    have h1 : 1 ≤ Real.log K / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
    calc Real.log B₀ ≤ |Real.log B₀| := le_abs_self _
      _ = |Real.log B₀| * 1 := (mul_one _).symm
      _ ≤ |Real.log B₀| * (Real.log K / Real.log 2) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h1' : (1 : ℝ) ≤ Real.log K / Real.log 2 := by rw [le_div_iff₀ hl2]; linarith
  unfold Kres CKres
  push_cast
  calc (Nat.log 2 m : ℝ) + 1 ≤ (Real.log K + Real.log B₀) / Real.log 2 + Real.log K / Real.log 2 :=
        add_le_add hnat h1'
    _ ≤ (Real.log K + |Real.log B₀| * (Real.log K / Real.log 2)) / Real.log 2 +
          Real.log K / Real.log 2 := by
        gcongr
    _ = (2 / Real.log 2 + |Real.log B₀| / Real.log 2 ^ 2) * Real.log K := by
        field_simp; ring

/-! ## `prop:src-res` -/

section SrcRes

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- **The resonant near-cutoff coupling** `V_nc^res`: all channels, all resonant scales. -/
noncomputable def Vres {κ : ℝ} (hκ : 0 ≤ κ) : L2 eta →L[ℂ] L2 eta :=
  ∑ j : Ch eta, ∑ k ∈ Finset.range (Kres n κ), (resK_schur (sys := sys) (n := n) hL hκ j k).toCLM

omit [Fintype ν] in
/-- A vector vanishing on the cube is orthogonal to the cube part. -/
lemma inner_trunc_eq_zero (y z : L2 eta) (hz : ∀ q ∈ fourierConfigCube eta n, z q = 0) :
    ⟪molecularH2Truncate n y, z⟫_ℂ = 0 := by
  rw [lp.inner_eq_tsum]
  refine (tsum_congr fun q => ?_).trans tsum_zero
  by_cases hq : q ∈ fourierConfigCube eta n
  · rw [hz q hq]; simp
  · rw [molecularH2Truncate_apply, cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq]; simp

open Classical in
include hL in
/-- **`prop:src-res`, the structural bound**: for every `x ∈ ℓ²`,
`|⟨ψ, V_nc^res x⟩| ≤ K_res · 11000 (1 + κ) c_tot · ‖(1 - P) ψ‖ ‖(1 - Q) x‖`. -/
theorem src_res_le {κ : ℝ} (hκ : 0 ≤ κ) (ψ x : L2 eta) :
    ‖⟪ψ, Vres sys hL (n := n) hκ x⟫_ℂ‖ ≤ Kres n κ * (11000 * (1 + κ) * ctot sys L) *
      (‖ψ - molecularH2Truncate n ψ‖ * ‖x - lpTruncate (Qs eta n) x‖) := by
  set δ := ψ - molecularH2Truncate n ψ
  set x' := x - lpTruncate (Qs eta n) x
  have hterm : ∀ (j : Ch eta) (k : ℕ),
      ‖⟪ψ, (resK_schur (sys := sys) (n := n) hL hκ j k).toCLM x⟫_ℂ‖ ≤
        11000 * (1 + κ) * chC sys L j * (‖δ‖ * ‖x'‖) := by
    intro j k
    set S := resK_schur (sys := sys) (n := n) hL hκ j k
    -- the output lies outside the cube
    have hout : ∀ q ∈ fourierConfigCube eta n, S.toCLM x q = 0 := by
      intro q hq
      rw [SchurBound.toCLM_apply]
      unfold kerApply
      refine (tsum_congr fun p => ?_).trans tsum_zero
      have : resK sys L n κ j k q p = 0 := by
        by_contra h; exact (resK_ne_zero h).1 hq
      rw [this, zero_mul]
    have hψ : ⟪ψ, S.toCLM x⟫_ℂ = ⟪δ, S.toCLM x⟫_ℂ := by
      rw [inner_sub_left, inner_trunc_eq_zero ψ _ hout, sub_zero]
    -- the input lies outside `Q`
    have hagree : ∀ q p, resK sys L n κ j k q p ≠ 0 → x' p = x p := by
      intro q p h
      have hQ := (resK_ne_zero h).2.2.1
      simp only [x', lp.coeFn_sub, Pi.sub_apply, lpTruncate_apply]
      rw [if_neg (fun hp => hQ (mem_Qs.mp hp)), sub_zero]
    have hS := toCLM_norm_le_of_agree S S x x' hagree
    have hc := chC_nonneg sys hL j
    rw [show Real.sqrt (11000 * (1 + κ) * chC sys L j * (11000 * (1 + κ) * chC sys L j)) =
      11000 * (1 + κ) * chC sys L j from Real.sqrt_mul_self (by positivity)] at hS
    rw [hψ]
    refine (norm_inner_le_norm _ _).trans ?_
    calc ‖δ‖ * ‖S.toCLM x‖ ≤ ‖δ‖ * (11000 * (1 + κ) * chC sys L j * ‖x'‖) :=
          mul_le_mul_of_nonneg_left hS (norm_nonneg _)
      _ = _ := by ring
  unfold Vres
  rw [sum_apply, inner_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Ch eta, ‖⟪ψ, (∑ k ∈ Finset.range (Kres n κ),
        (resK_schur (sys := sys) (n := n) hL hκ j k).toCLM) x⟫_ℂ‖
      ≤ ∑ j : Ch eta, ∑ _k ∈ Finset.range (Kres n κ), 11000 * (1 + κ) * chC sys L j * (‖δ‖ * ‖x'‖) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [sum_apply, inner_sum]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => hterm j k)
    _ = Kres n κ * (11000 * (1 + κ) * ctot sys L) * (‖δ‖ * ‖x'‖) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        unfold ctot
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring

/-- The constant of `prop:src-res` (per unit `Ξ M`, times `K^{-3} log K`). -/
noncomputable def Cres (sys : CoulombSystem eta ν) (L Hunit κ : ℝ) : ℝ :=
  CKres (gF L) κ * (11000 * (1 + κ) * ctot sys L) * (eta * cTr sys L Hunit) *
    (4 * eta * Real.sqrt (2 * sys.maxMass) * FSSrc1.cPhi sys L Hunit 0 *
      Real.sqrt (Real.sqrt (3 * eta * mmax sys)))

lemma rpow_half_div_sq {x l : ℝ} (_hx : 0 ≤ x) (hl : 0 < l) :
    (x / l ^ 2) ^ (1 / 2 : ℝ) = Real.sqrt x / l := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_div' x (sq_nonneg l), Real.sqrt_sq hl.le]

include hKernel hL in
/-- **`prop:src-res`** (restated, review S1 §2.K): for every datum, every good cube state `v`
(`IsGood 1 M v`), all times and every cutoff with `K = g n ≥ 2`,
`|⟨ψ(s), V_nc^res e^{iH_N τ} A_{p₀} v⟩| ≤ C Ξ M K^{-3} log K`, where `V_nc^res` collects the
resonant hops `|F_c(ν)| ≤ κ 2^k` of every channel at every scale (`resK_eq_zero_of_ge`: no
resonant hop beyond `K_res` scales). -/
theorem prop_src_res (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) {κ : ℝ} (hκ : 0 ≤ κ) (hK : 2 ≤ gF L * n) (D : EvoData L H) (s τ : ℝ) {M : ℝ}
    {v : En eta n} (hv : IsGood sys L 1 M v) :
    ‖⟪Sm eta L (traj H D s), Vres sys hL (n := n) hκ
        (emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) τ (FSSrc1.bdatum sys L p₀ v)))⟫_ℂ‖ ≤
      Cres sys L Hunit κ * D.Xi * M * (gF L * n) ^ (-(3 : ℝ)) * Real.log (gF L * n) := by
  have hg := gF_pos hL
  have heta : 0 < eta := Fin.pos p₀
  have hK1 : 1 ≤ gF L * n := by linarith
  have hK0 : 0 < gF L * n := by linarith
  have hΞ := D.Xi_nonneg
  have hM : 0 ≤ M := good_nonneg hv
  have hm := sys.one_le_maxMass
  have hct := ctot_nonneg sys hL
  have hcT := cTr_nonneg sys hL Hunit
  have hcphi : 0 ≤ FSSrc1.cPhi sys L Hunit 0 := by
    unfold FSSrc1.cPhi
    have := CflS_nonneg sys (L := L) Hunit le_rfl (1 / 2)
    positivity
  set K := gF L * n with hK_def
  set φ := retFlow sys L n (zero_isSymmetric (n := n)) τ (FSSrc1.bdatum sys L p₀ v)
  set x := emb eta n φ
  have h0 := src_res_le sys hL (n := n) hκ (Sm eta L (traj H D s)) x
  -- `‖(1 - P) ψ‖`
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D s
  have hw : traj H D s = w := traj_eq H D s w hw1
  have hδ : ‖Sm eta L (traj H D s) - molecularH2Truncate n (Sm eta L (traj H D s))‖ ≤
      eta * (cTr sys L Hunit * D.Xi) * K ^ (-(5 / 2 : ℝ)) := by
    rw [hw]; exact fgood_R hF hL hK1
  -- `‖(1 - Q) x‖`
  have hΛ := FSSrc1.one_le_LamN sys L hL heta hK1
  have htail : ∀ a : Fin eta, ‖tailMask (gF L) (gF L * n / 4) a x‖ ≤
      4 * Real.sqrt (2 * sys.maxMass) * FSSrc1.cPhi sys L Hunit 0 * M *
        Real.sqrt (Real.sqrt (3 * eta * mmax sys)) * (Real.sqrt K / K) := by
    intro a
    rw [tailMask_emb, norm_emb]
    have hl : 0 < gF L * n / 4 := by positivity
    have h := (FSSrc1.phi_tail sys L p₀ hL Hunit hPeriodic (zero_isSymmetric (n := n)) le_rfl
      (fun _ => by simp) hv hΛ τ a hl).1
    refine h.trans ?_
    have hma := sys.mass_le_maxMass a
    have hma0 := sys.mass_pos a
    rw [rpow_half_div_sq (by positivity) hl, ← Real.sqrt_eq_rpow, FSSrc1.LamN_eq sys L hL]
    have hs1 : Real.sqrt (2 * sys.mass a) ≤ Real.sqrt (2 * sys.maxMass) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsK : Real.sqrt (Real.sqrt (3 * eta * mmax sys) * K) =
        Real.sqrt (Real.sqrt (3 * eta * mmax sys)) * Real.sqrt K :=
      Real.sqrt_mul (Real.sqrt_nonneg _) K
    rw [← hK_def, hsK]
    have e : Real.sqrt (2 * sys.mass a) / (K / 4) *
        (FSSrc1.cPhi sys L Hunit 0 * M * (Real.sqrt (Real.sqrt (3 * eta * mmax sys)) * Real.sqrt K)) =
        4 * Real.sqrt (2 * sys.mass a) * FSSrc1.cPhi sys L Hunit 0 * M *
          Real.sqrt (Real.sqrt (3 * eta * mmax sys)) * (Real.sqrt K / K) := by
      field_simp
    rw [e]
    have : 0 ≤ FSSrc1.cPhi sys L Hunit 0 * M * Real.sqrt (Real.sqrt (3 * eta * mmax sys)) *
        (Real.sqrt K / K) := by positivity
    have h4 : 4 * Real.sqrt (2 * sys.mass a) ≤ 4 * Real.sqrt (2 * sys.maxMass) := by linarith
    calc 4 * Real.sqrt (2 * sys.mass a) * FSSrc1.cPhi sys L Hunit 0 * M *
          Real.sqrt (Real.sqrt (3 * eta * mmax sys)) * (Real.sqrt K / K)
        = (4 * Real.sqrt (2 * sys.mass a)) * (FSSrc1.cPhi sys L Hunit 0 * M *
            Real.sqrt (Real.sqrt (3 * eta * mmax sys)) * (Real.sqrt K / K)) := by ring
      _ ≤ (4 * Real.sqrt (2 * sys.maxMass)) * (FSSrc1.cPhi sys L Hunit 0 * M *
            Real.sqrt (Real.sqrt (3 * eta * mmax sys)) * (Real.sqrt K / K)) :=
          mul_le_mul_of_nonneg_right h4 this
      _ = _ := by ring
  have hx' : ‖x - lpTruncate (Qs eta n) x‖ ≤ eta * (4 * Real.sqrt (2 * sys.maxMass) *
      FSSrc1.cPhi sys L Hunit 0 * M * Real.sqrt (Real.sqrt (3 * eta * mmax sys)) *
        (Real.sqrt K / K)) := by
    refine (norm_sub_truncQ_le hL n x).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n / 4) a x‖
        ≤ ∑ _a : Fin eta, 4 * Real.sqrt (2 * sys.maxMass) * FSSrc1.cPhi sys L Hunit 0 * M *
            Real.sqrt (Real.sqrt (3 * eta * mmax sys)) * (Real.sqrt K / K) :=
          Finset.sum_le_sum fun a _ => htail a
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- `K_res ≤ C log K`
  have hKres := Kres_le_log hg hκ (n := n) hK
  rw [← hK_def] at hKres
  -- assemble
  have hpow : K ^ (-(5 / 2 : ℝ)) * (Real.sqrt K / K) = K ^ (-(3 : ℝ)) := by
    rw [FSNormal.rpow_neg_five_half_eq hK0, rpow_neg_three_eq hK0]
    have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
    field_simp
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hA : 0 ≤ 11000 * (1 + κ) * ctot sys L := by positivity
  have hCK : 0 ≤ CKres (gF L) κ := by
    unfold CKres
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hCKl : 0 ≤ CKres (gF L) κ * Real.log K * (11000 * (1 + κ) * ctot sys L) := by positivity
  refine h0.trans ?_
  have hp5 : 0 ≤ K ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hK0.le _
  calc (Kres n κ : ℝ) * (11000 * (1 + κ) * ctot sys L) *
        (‖Sm eta L (traj H D s) - molecularH2Truncate n (Sm eta L (traj H D s))‖ *
          ‖x - lpTruncate (Qs eta n) x‖)
      ≤ (CKres (gF L) κ * Real.log K) * (11000 * (1 + κ) * ctot sys L) *
          ((eta * (cTr sys L Hunit * D.Xi) * K ^ (-(5 / 2 : ℝ))) *
            (eta * (4 * Real.sqrt (2 * sys.maxMass) * FSSrc1.cPhi sys L Hunit 0 * M *
              Real.sqrt (Real.sqrt (3 * eta * mmax sys)) * (Real.sqrt K / K)))) := by
        gcongr
    _ = Cres sys L Hunit κ * D.Xi * M * (K ^ (-(5 / 2 : ℝ)) * (Real.sqrt K / K)) * Real.log K := by
        unfold Cres; ring
    _ = Cres sys L Hunit κ * D.Xi * M * K ^ (-(3 : ℝ)) * Real.log K := by rw [hpow]

end SrcRes

end FSBand
