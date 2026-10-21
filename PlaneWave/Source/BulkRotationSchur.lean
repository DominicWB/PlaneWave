import PlaneWave.Source.BulkRotation

/-!
# Flux/source build, block 5: Schur bounds for the bulk rotation

* `onCh_unique`: distinct configurations are joined by at most one channel.
* `Asym_hop`: on the cube, `E(q) - E(p) = (g²/2μ_j) F_c(θ)` for `q` one hop of `j` from `p`.
* `channel_row_le` (the row engine): for a fixed input `p ∈ Q` and channel `j`, the gapped
  outputs `q ∈ Q` (floor `|E(q) - E(p)| ≥ g²|θ|/μ_j`) have
  `Σ_q 1/|E(q) - E(p)| ≤ (2μ_j/g²) · 11000 (2J + 3) · 2n`, by dyadic shells in `|θ|` and the
  slab-weighted sum (`lem:slab`).
* `norm_Sig2bb_le`: `‖Σ₂^bb u‖ ≤ C (2J_n + 3)/n² ‖u‖`, `J_n = ⌊log₂ ⌈m_top η n²⌉⌋`
  (the text's `‖Σ₂^bb‖ ≤ CK^{-2} log(2+K)`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Uniqueness of the channel -/

omit [Fintype ν] in
lemma tr_ne_zero_iff_moved (j : Ch eta) {θ : Lattice3} (hθ : θ ≠ 0) (c : Fin eta) :
    tr j θ c ≠ 0 ↔ c ∈ moved j := by
  constructor
  · intro h
    by_contra hc
    exact h (tr_apply_not_moved j θ hc)
  · intro hc
    rcases tr_apply_moved j θ hc with h | h
    · rw [h]; exact hθ
    · rw [h]; exact neg_ne_zero.mpr hθ

omit [Fintype ν] in
/-- **Distinct configurations are joined by at most one channel.** -/
theorem onCh_unique {j j' : Ch eta} {k k' : Cf eta} (h : OnCh j k k') (h' : OnCh j' k k')
    (hne : k ≠ k') : j = j' := by
  set θ := k (lead j) - k' (lead j)
  set θ' := k (lead j') - k' (lead j')
  have e1 : k = k' + tr j θ := h
  have e2 : k = k' + tr j' θ' := h'
  have htr : tr j θ = tr j' θ' := add_left_cancel (e1.symm.trans e2)
  have hθ : θ ≠ 0 := by
    intro h0
    apply hne
    rw [e1, h0]
    cases j with
    | inl a => simp [tr]
    | inr pr => simp [tr]
  have hθ' : θ' ≠ 0 := by
    intro h0
    apply hne
    rw [e2, h0]
    cases j' with
    | inl a => simp [tr]
    | inr pr => simp [tr]
  apply moved_inj
  ext c
  rw [← tr_ne_zero_iff_moved j hθ c, ← tr_ne_zero_iff_moved j' hθ' c, htr]

/-! ## Cube kinematics -/

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

omit [Fintype ν] in
/-- The mismatch on the cube. -/
lemma Asym_hop {j : Ch eta} {q p : Cfg eta n} (hj : OnCh j (cidx n q) (cidx n p)) :
    Asym sys L n q - Asym sys L n p =
      gF L ^ 2 / (2 * muCh sys j) * FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p) := by
  rw [Asym_eq_Ek, Asym_eq_Ek]
  have e : finiteConfigLatticeIndex eta n q = cidx n p + tr j (chT n j q p) := hj
  rw [e]
  exact E_hop sys (gF L) j _ _

omit [Fintype ν] in
lemma chT_injOn (j : Ch eta) (p : Cfg eta n) :
    Set.InjOn (fun q => chT n j q p) {q | OnCh j (cidx n q) (cidx n p)} := by
  intro q hq q' hq' h
  apply finiteConfigLatticeIndex_injective eta n
  have e1 : finiteConfigLatticeIndex eta n q = cidx n p + tr j (chT n j q p) := hq
  have e2 : finiteConfigLatticeIndex eta n q' = cidx n p + tr j (chT n j q' p) := hq'
  have h' : chT n j q p = chT n j q' p := h
  rw [e1, e2, h']

omit [Fintype ν] in
open FSChannel in
lemma lsq_chT_le (hn : 0 ≤ (n : ℝ)) {j : Ch eta} {q p : Cfg eta n} (hq : InQ (n : ℝ) (cidx n q))
    (hp : InQ (n : ℝ) (cidx n p)) : FSLattice.lsq (chT n j q p) ≤ (n : ℝ) ^ 2 / 4 := by
  have h1 : rho (chT n j q p) ≤ rho (cidx n q (lead j)) + rho (cidx n p (lead j)) := by
    have := rho_add_le (cidx n q (lead j)) (-(cidx n p (lead j)))
    rw [rho_neg'] at this
    unfold chT
    rwa [sub_eq_add_neg]
  have h2 := rho_le_of_inQ hn hq (lead j)
  have h3 := rho_le_of_inQ hn hp (lead j)
  have h4 : rho (chT n j q p) ≤ n / 2 := by linarith
  rw [← rho_sq]
  have := rho_nonneg (chT n j q p)
  nlinarith

omit [Fintype ν] in
lemma one_le_lsq_chT {j : Ch eta} {q p : Cfg eta n} (hj : OnCh j (cidx n q) (cidx n p))
    (hne : q ≠ p) : 1 ≤ FSLattice.lsq (chT n j q p) := by
  have hθ : chT n j q p ≠ 0 := by
    intro h0
    apply hne
    apply finiteConfigLatticeIndex_injective eta n
    have e : finiteConfigLatticeIndex eta n q = cidx n p + tr j (chT n j q p) := hj
    rw [e, h0]
    cases j with
    | inl a => simp [tr]
    | inr pr => simp [tr]
  exact one_le_latticeNormSq hθ

/-! ## Dyadic shells -/

/-- Every real `x ∈ [1, X]` lies in a dyadic shell `4^i ≤ x ≤ 4^{i+1}` with `2^i ≤ √X`. -/
lemma exists_shell {x : ℝ} (hx : 1 ≤ x) : ∃ i : ℕ, (4 : ℝ) ^ i ≤ x ∧ x ≤ 4 ^ (i + 1) := by
  set m := ⌊x⌋₊
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hx)
  refine ⟨Nat.log 4 m, ?_, ?_⟩
  · have h1 : 4 ^ Nat.log 4 m ≤ m := Nat.pow_log_le_self 4 (by omega)
    have h2 : ((4 ^ Nat.log 4 m : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by linarith))
  · have h1 : m < 4 ^ (Nat.log 4 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    have h2 : m + 1 ≤ 4 ^ (Nat.log 4 m + 1) := h1
    have h3 : ((m + 1 : ℕ) : ℝ) ≤ ((4 ^ (Nat.log 4 m + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h3
    have := Nat.lt_floor_add_one x
    linarith

lemma shell_index_le {x : ℝ} {i n : ℕ} (hi : (4 : ℝ) ^ i ≤ x) (hx : x ≤ (n : ℝ) ^ 2 / 4)
    (hn : 1 ≤ n) : i ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by norm_num)
  have e : ((2 : ℝ) ^ i) ^ 2 = 4 ^ i := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h1 : ((2 : ℝ) ^ i) ^ 2 ≤ (n : ℝ) ^ 2 := by
    rw [e]; nlinarith [sq_nonneg (n : ℝ)]
  have h2 : (2 : ℝ) ^ i ≤ n :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
  exact_mod_cast h2

omit [Fintype ν] in
open FSChannel in
/-- **The row engine.** For a fixed input `p` and channel `j`, gapped outputs `q ∈ Q` with
`|F_c(θ)| < 2^{J+1}·2` have `Σ_q 1/|E(q) - E(p)| ≤ (2μ_j/g²) · 11000 (2J+3) · 2n`. -/
theorem channel_row_le (hL : 0 < L) (hn : 1 ≤ n) (j : Ch eta) (p : Cfg eta n) {J : ℕ}
    (T : Finset (Cfg eta n))
    (hT : ∀ q ∈ T, OnCh j (cidx n q) (cidx n p) ∧ q ≠ p ∧ InQ (n : ℝ) (cidx n q) ∧
      InQ (n : ℝ) (cidx n p) ∧
      gF L ^ 2 * rho (chT n j q p) / muCh sys j ≤ |Asym sys L n q - Asym sys L n p| ∧
      |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| < 2 ^ (J + 1) * 2) :
    ∑ q ∈ T, 1 / |Asym sys L n q - Asym sys L n p| ≤
      2 * muCh sys j / gF L ^ 2 * (11000 * (2 * J + 3) * (2 * n)) := by
  classical
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set c := cCh sys j (cidx n p)
  set F : Lattice3 → ℝ := fun θ => FSLattice.slabF c θ
  -- step 1: the mismatch in terms of `F`
  have h1 : ∀ q ∈ T, 1 / |Asym sys L n q - Asym sys L n p| =
      2 * muCh sys j / gF L ^ 2 * (1 / |F (chT n j q p)|) := by
    intro q hq
    rw [Asym_hop (hT q hq).1, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))]
    show 1 / (gF L ^ 2 / (2 * muCh sys j) * |F (chT n j q p)|) =
      2 * muCh sys j / gF L ^ 2 * (1 / |F (chT n j q p)|)
    rw [one_div, mul_inv, inv_div, ← one_div]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  -- step 2: pass to the transfers
  have hinj : Set.InjOn (fun q => chT n j q p) T := fun q hq q' hq' h =>
    chT_injOn j p (hT q hq).1 (hT q' hq').1 h
  rw [← Finset.sum_image (f := fun θ => 1 / |F θ|) hinj]
  set T' := T.image fun q => chT n j q p
  have hT' : ∀ θ ∈ T', 1 ≤ FSLattice.lsq θ ∧ FSLattice.lsq θ ≤ (n : ℝ) ^ 2 / 4 ∧
      2 * rho θ ≤ |F θ| ∧ |F θ| < 2 ^ (J + 1) * 2 := by
    intro θ hθ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨hon, hne, hiq, hip, hfl, hcap⟩ := hT q hq
    refine ⟨one_le_lsq_chT hon hne, lsq_chT_le hn0 hiq hip, ?_, hcap⟩
    rw [Asym_hop hon, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))] at hfl
    have e : gF L ^ 2 * rho (chT n j q p) / muCh sys j =
        gF L ^ 2 / (2 * muCh sys j) * (2 * rho (chT n j q p)) := by field_simp
    rw [e] at hfl
    exact le_of_mul_le_mul_left hfl (by positivity)
  -- step 3: shells
  set I := Nat.log 2 n
  have hshell : ∀ θ ∈ T', 1 / |F θ| ≤ ∑ i ∈ Finset.range (I + 1),
      if (4 : ℝ) ^ i ≤ FSLattice.lsq θ ∧ FSLattice.lsq θ ≤ 4 ^ (i + 1) then 1 / |F θ| else 0 := by
    intro θ hθ
    obtain ⟨h1', h2', -, -⟩ := hT' θ hθ
    obtain ⟨i, hi1, hi2⟩ := exists_shell h1'
    have hiI : i ≤ I := shell_index_le hi1 h2' hn
    have hterm : (if (4 : ℝ) ^ i ≤ FSLattice.lsq θ ∧ FSLattice.lsq θ ≤ 4 ^ (i + 1) then 1 / |F θ|
        else 0) = 1 / |F θ| := if_pos ⟨hi1, hi2⟩
    calc 1 / |F θ| = (if (4 : ℝ) ^ i ≤ FSLattice.lsq θ ∧ FSLattice.lsq θ ≤ 4 ^ (i + 1)
          then 1 / |F θ| else 0) := hterm.symm
      _ ≤ _ := by
        apply Finset.single_le_sum (f := fun i => if (4 : ℝ) ^ i ≤ FSLattice.lsq θ ∧
          FSLattice.lsq θ ≤ 4 ^ (i + 1) then 1 / |F θ| else 0)
        · intro i _; split_ifs
          · positivity
          · exact le_rfl
        · exact Finset.mem_range.mpr (by omega)
  have hsum := Finset.sum_le_sum hshell
  rw [Finset.sum_comm] at hsum
  -- step 4: each shell by the slab-weighted sum
  have hpiece : ∀ i ∈ Finset.range (I + 1), ∑ θ ∈ T', (if (4 : ℝ) ^ i ≤ FSLattice.lsq θ ∧
      FSLattice.lsq θ ≤ 4 ^ (i + 1) then 1 / |F θ| else 0) ≤ 11000 * (2 * J + 3) * 2 ^ i := by
    intro i _
    rw [← Finset.sum_filter]
    have hρ : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have h := FSLattice.slab_inv_sum_le c hρ (by positivity : (0 : ℝ) < 2 ^ (i + 1)) (J := J)
      (T'.filter fun θ => (4 : ℝ) ^ i ≤ FSLattice.lsq θ ∧ FSLattice.lsq θ ≤ 4 ^ (i + 1)) (by
        intro θ hθ
        obtain ⟨hθT, hs1, hs2⟩ := Finset.mem_filter.mp hθ
        obtain ⟨-, -, hfl, hcap⟩ := hT' θ hθT
        have e4 : ((2 : ℝ) ^ i) ^ 2 = 4 ^ i := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        refine ⟨by rw [e4]; exact hs1, by rw [e4, ← pow_succ']; linarith [hs2], ?_, ?_⟩
        · have hr : (2 : ℝ) ^ i ≤ rho θ := by
            unfold rho
            apply Real.le_sqrt_of_sq_le
            rw [e4]; exact hs1
          have : (2 : ℝ) ^ (i + 1) = 2 * 2 ^ i := by ring
          rw [this]
          exact le_trans (by linarith) hfl
        · calc |F θ| < 2 ^ (J + 1) * 2 := hcap
            _ ≤ 2 ^ (J + 1) * 2 ^ (i + 1) := by
                gcongr
                calc (2 : ℝ) = 2 ^ 1 := by norm_num
                  _ ≤ 2 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega))
    have e : 11000 * ((2 : ℝ) ^ i) ^ 2 * (2 / 2 ^ (i + 1) + 2 * (J + 1) / 2 ^ i) =
        11000 * (2 * J + 3) * 2 ^ i := by
      field_simp
      ring
    rw [e] at h
    exact h
  have hgeom : ∑ i ∈ Finset.range (I + 1), (2 : ℝ) ^ i ≤ 2 * n := by
    have h1 : ∑ i ∈ Finset.range (I + 1), (2 : ℝ) ^ i = 2 ^ (I + 1) - 1 := by
      have := geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) (I + 1)
      rw [this]; ring
    have h2 : 2 ^ I ≤ n := Nat.pow_log_le_self 2 (by omega)
    have h3 : (2 : ℝ) ^ I ≤ n := by exact_mod_cast h2
    rw [h1, pow_succ]
    linarith
  calc 2 * muCh sys j / gF L ^ 2 * ∑ θ ∈ T', 1 / |F θ|
      ≤ 2 * muCh sys j / gF L ^ 2 * ∑ i ∈ Finset.range (I + 1), ∑ θ ∈ T',
          (if (4 : ℝ) ^ i ≤ FSLattice.lsq θ ∧ FSLattice.lsq θ ≤ 4 ^ (i + 1) then 1 / |F θ| else 0) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 2 * muCh sys j / gF L ^ 2 * ∑ i ∈ Finset.range (I + 1),
          (11000 : ℝ) * (2 * (J : ℝ) + 3) * (2 : ℝ) ^ i :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpiece) (by positivity)
    _ = 2 * muCh sys j / gF L ^ 2 * ((11000 : ℝ) * (2 * (J : ℝ) + 3) *
          ∑ i ∈ Finset.range (I + 1), (2 : ℝ) ^ i) := by
        congr 1; rw [Finset.mul_sum]
    _ ≤ 2 * muCh sys j / gF L ^ 2 * (11000 * (2 * J + 3) * (2 * n)) := by
        gcongr

/-! ## The operator norm of `Σ₂^bb` -/

variable (sys) in
/-- The total bulk kernel constant `Σ_j chb_j`. -/
noncomputable def chbT (L : ℝ) : ℝ := ∑ j : Ch eta, chb sys L j

lemma chbT_nonneg (hL : 0 < L) : 0 ≤ chbT sys L :=
  Finset.sum_nonneg fun j _ => chb_nonneg hL j

omit [Fintype ν] in
lemma inP_cidx (q : Cfg eta n) : InP (n : ℝ) (cidx n q) :=
  (inP_iff_mem_cube n _).mpr (finiteConfigLatticeIndex_mem_cube eta n q)

lemma hbC_eq_zero_of_not_inQ {q p : Cfg eta n}
    (h : ¬ (InQ (n : ℝ) (cidx n q) ∧ InQ (n : ℝ) (cidx n p))) : hbC sys L n q p = 0 :=
  hbK_eq_zero_of_not_inQ (inP_cidx q) (inP_cidx p) h

open Classical in
lemma norm_hbC_le (hL : 0 < L) (hn : 2 ≤ n) (q p : Cfg eta n) :
    ‖hbC sys L n q p‖ ≤ chbT sys L / (n : ℝ) ^ 3 := by
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  by_cases hQ : InQ (n : ℝ) (cidx n q) ∧ InQ (n : ℝ) (cidx n p)
  · refine (norm_hbK_le hL hn hQ.1 hQ.2).trans ?_
    unfold chbT
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    apply div_le_div_of_nonneg_right _ hn3.le
    split_ifs
    · exact le_rfl
    · exact chb_nonneg hL j
  · rw [hbC_eq_zero_of_not_inQ hQ, norm_zero]
    exact div_nonneg (chbT_nonneg hL) hn3.le

omit [Fintype ν] in
lemma muCh_le_mtop (j : Ch eta) : muCh sys j ≤ mtop sys := by
  cases j with
  | inl a => exact mass_le_mtop sys a
  | inr pr =>
    have ha := sys.mass_pos pr.1.1
    have hb := sys.mass_pos pr.1.2
    have h1 : muCh sys (.inr pr) ≤ sys.mass pr.1.1 := by
      simp only [muCh]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    exact h1.trans (mass_le_mtop sys _)

variable (sys) in
/-- The number of dyadic mismatch layers, `J_n = ⌊log₂ ⌈m_top η n²⌉⌋`. -/
noncomputable def Jn (n : ℕ) : ℕ := Nat.log 2 ⌈mtop sys * eta * (n : ℝ) ^ 2⌉₊

omit [Fintype ν] in
lemma Asym_nonneg (q : Cfg eta n) : 0 ≤ Asym sys L n q := by
  rw [Asym_eq_Ek]
  unfold Ek E
  exact Finset.sum_nonneg fun c _ => by
    have := sys.mass_pos c
    have := nsq_nonneg (cidx n q c)
    positivity

omit [Fintype ν] in
/-- **The mismatch cap** on `Q × Q`: `|F_c(θ)| < 2^{J_n + 1} · 2`. -/
lemma slabF_cap (hL : 0 < L) {j : Ch eta} {q p : Cfg eta n} (hj : OnCh j (cidx n q) (cidx n p))
    (hq : InQ (n : ℝ) (cidx n q)) (hp : InQ (n : ℝ) (cidx n p)) :
    |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| < 2 ^ (Jn sys n + 1) * 2 := by
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hE := Asym_hop (sys := sys) (L := L) hj
  have hq' : Asym sys L n q ≤ eta * gF L ^ 2 * n ^ 2 / 32 := by
    rw [Asym_eq_Ek]; exact Ek_le_of_inQ hq
  have hp' : Asym sys L n p ≤ eta * gF L ^ 2 * n ^ 2 / 32 := by
    rw [Asym_eq_Ek]; exact Ek_le_of_inQ hp
  have hq0 := Asym_nonneg (sys := sys) (L := L) q
  have hp0 := Asym_nonneg (sys := sys) (L := L) p
  set F := FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)
  have habs : |F| = 2 * muCh sys j / gF L ^ 2 * |Asym sys L n q - Asym sys L n p| := by
    rw [hE, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))]
    field_simp
  have hdiff : |Asym sys L n q - Asym sys L n p| ≤ eta * gF L ^ 2 * n ^ 2 / 16 := by
    rw [abs_le]; constructor <;> linarith
  have hF : |F| ≤ mtop sys * eta * (n : ℝ) ^ 2 / 8 := by
    rw [habs]
    have hm := muCh_le_mtop (sys := sys) j
    calc 2 * muCh sys j / gF L ^ 2 * |Asym sys L n q - Asym sys L n p|
        ≤ 2 * muCh sys j / gF L ^ 2 * (eta * gF L ^ 2 * n ^ 2 / 16) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = muCh sys j * eta * (n : ℝ) ^ 2 / 8 := by field_simp; ring
      _ ≤ mtop sys * eta * (n : ℝ) ^ 2 / 8 := by gcongr
  have hx0 : 0 ≤ mtop sys * eta * (n : ℝ) ^ 2 := by
    have := one_le_mtop sys
    positivity
  have hlog : ⌈mtop sys * eta * (n : ℝ) ^ 2⌉₊ < 2 ^ (Jn sys n + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hlog' : mtop sys * eta * (n : ℝ) ^ 2 < 2 ^ (Jn sys n + 1) := by
    have h1 := Nat.le_ceil (mtop sys * eta * (n : ℝ) ^ 2)
    have h2 : ((⌈mtop sys * eta * (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ) < ((2 ^ (Jn sys n + 1) : ℕ) : ℝ) := by
      exact_mod_cast hlog
    push_cast at h2
    linarith
  have h2pos : (0 : ℝ) < 2 ^ (Jn sys n + 1) := by positivity
  nlinarith

variable (sys) in
/-- The Schur constant of `Σ₂^bb`: `C_Σ = chbT · Σ_j (2μ_j/g²) · 11000 · 2`. -/
noncomputable def CS1 (L : ℝ) : ℝ :=
  chbT sys L * ∑ j : Ch eta, 2 * muCh sys j / gF L ^ 2 * (11000 * 2)

lemma CS1_nonneg (hL : 0 < L) : 0 ≤ CS1 sys L := by
  unfold CS1
  have := chbT_nonneg (sys := sys) hL
  have hg := gF_pos hL
  exact mul_nonneg this (Finset.sum_nonneg fun j _ => by have := muCh_pos sys j; positivity)

open Classical in
/-- The column sums of `Σ₂^bb`. -/
lemma col_Sig2bb_le (hL : 0 < L) (hn : 2 ≤ n) (p : Cfg eta n) :
    ∑ q, ‖FSKernel.divK (Asym sys L n) (hgapK sys L n) q p‖ ≤
      CS1 sys L * (2 * Jn sys n + 3) / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  set T : Ch eta → Finset (Cfg eta n) := fun j => Finset.univ.filter fun q =>
    OnCh j (cidx n q) (cidx n p) ∧ q ≠ p ∧ InQ (n : ℝ) (cidx n q) ∧ InQ (n : ℝ) (cidx n p) ∧
      gF L ^ 2 * FSChannel.rho (chT n j q p) / muCh sys j ≤ |Asym sys L n q - Asym sys L n p| ∧
      |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| < 2 ^ (Jn sys n + 1) * 2
  have hpt : ∀ q, ‖FSKernel.divK (Asym sys L n) (hgapK sys L n) q p‖ ≤
      ∑ j, if q ∈ T j then chbT sys L / (n : ℝ) ^ 3 * (1 / |Asym sys L n q - Asym sys L n p|)
        else 0 := by
    intro q
    have hsum0 : 0 ≤ ∑ j, if q ∈ T j then chbT sys L / (n : ℝ) ^ 3 *
        (1 / |Asym sys L n q - Asym sys L n p|) else 0 :=
      Finset.sum_nonneg fun j _ => by
        split_ifs
        · have := chbT_nonneg (sys := sys) hL; positivity
        · exact le_rfl
    unfold FSKernel.divK hgapK
    by_cases hd : Asym sys L n q = Asym sys L n p
    · rw [if_pos hd, norm_zero]; exact hsum0
    rw [if_neg hd]
    by_cases hg : gapC sys L n q p
    · rw [if_pos hg]
      by_cases h0 : hbC sys L n q p = 0
      · rw [h0, zero_div, norm_zero]; exact hsum0
      have hQ : InQ (n : ℝ) (cidx n q) ∧ InQ (n : ℝ) (cidx n p) := by
        by_contra h; exact h0 (hbC_eq_zero_of_not_inQ h)
      obtain ⟨hne, j, hj, hfl⟩ := hg
      have hmem : q ∈ T j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hne, hQ.1, hQ.2, hfl,
        slabF_cap hL hj hQ.1 hQ.2⟩
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => if q ∈ T j then chbT sys L /
        (n : ℝ) ^ 3 * (1 / |Asym sys L n q - Asym sys L n p|) else 0) (fun j _ => by
          split_ifs
          · have := chbT_nonneg (sys := sys) hL; positivity
          · exact le_rfl) (Finset.mem_univ j))
      simp only [if_pos hmem]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (norm_hbC_le hL hn q p) (by positivity)
    · rw [if_neg hg, zero_div, norm_zero]; exact hsum0
  calc ∑ q, ‖FSKernel.divK (Asym sys L n) (hgapK sys L n) q p‖
      ≤ ∑ q, ∑ j, (if q ∈ T j then chbT sys L / (n : ℝ) ^ 3 *
          (1 / |Asym sys L n q - Asym sys L n p|) else 0) := Finset.sum_le_sum fun q _ => hpt q
    _ = ∑ j, chbT sys L / (n : ℝ) ^ 3 * ∑ q ∈ T j, 1 / |Asym sys L n q - Asym sys L n p| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    _ ≤ ∑ j, chbT sys L / (n : ℝ) ^ 3 *
          (2 * muCh sys j / gF L ^ 2 * (11000 * (2 * Jn sys n + 3) * (2 * n))) := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (by
          have := chbT_nonneg (sys := sys) hL; positivity)
        apply channel_row_le hL hn1 j p
        intro q hq
        exact (Finset.mem_filter.mp hq).2
    _ = CS1 sys L * (2 * Jn sys n + 3) / (n : ℝ) ^ 2 := by
        unfold CS1
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        field_simp

/-- **`‖Σ₂^bb‖ ≤ C_Σ (2J_n + 3)/n²`** (the text's `‖Σ₂^bb‖ ≤ CK^{-2} log(2+K)`). -/
theorem norm_Sig2bb_le (hL : 0 < L) (hn : 2 ≤ n) (u : En eta n) :
    ‖Sig2bb sys L n u‖ ≤ CS1 sys L * (2 * Jn sys n + 3) / (n : ℝ) ^ 2 * ‖u‖ := by
  have hR : 0 ≤ CS1 sys L * (2 * Jn sys n + 3) / (n : ℝ) ^ 2 := by
    have := CS1_nonneg (sys := sys) hL; positivity
  apply FSKernel.norm_kop_le' _ hR _ (col_Sig2bb_le hL hn)
  intro q
  calc ∑ p, ‖FSKernel.divK (Asym sys L n) (hgapK sys L n) q p‖
      = ∑ p, ‖FSKernel.divK (Asym sys L n) (hgapK sys L n) p q‖ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [sig2bbK_skew hL q p, norm_neg, Complex.norm_conj]
    _ ≤ _ := col_Sig2bb_le hL hn q

end FSNormal
