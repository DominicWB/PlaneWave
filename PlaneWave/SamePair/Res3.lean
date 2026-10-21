import PlaneWave.SamePair.RetainedThirdOrder

/-!
# Same-pair third order, part 6: `lem:res3` for the same-pair component

The same-pair component `H₃^sp` is split by the formal floor `gapC`
(`|E(q) - E(p)| ≥ g² |θ|/μ_j`, the floor of `lem:res2`) into `H₃^{gap,sp}` and `H₃^{res,sp}`
(`H3sp_split`; both Hermitian).

**`norm_H3resSp_good`** (`lem:res3`, same-pair case, restated as in review F4 Q-2/Q-3): for every
good state `u` (`IsGood 1 M u`), `‖H₃^{res,sp} u‖ ≤ C_R3(n) M` with
`C_R3(n) = D(n) + 10 (440000/c₀² + 3520000) Σ_j B_j(n) = O(n⁻³ log n)`.

The proof is that of `lem:res2` with the shell value of eq:h3: on the resonant elements of the
dyadic shell `i` the kernel is at most `B_j (i + 3)/2^i` (`norm_h3spK_le`), the shell holds at
most `55000 · 4^i` resonant transfers per configuration (`shell_count_le`, both orientations by
`r3Maj_symm`), and for `i ≥ 3` the input is pinned beyond `g (3/8) 2^i` (`pin_register`), where
a good state has the tail `8M/(c₀² 4^i)`; the shells sum geometrically. The diagonal is bounded by
`D(n)` (`norm_h3spK_diag_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The split of `H₃^sp` -/

section Split

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

open Classical in
/-- The gapped part of the same-pair kernel. -/
noncomputable def h3gK (q p : Cfg eta n) : ℂ := if gapC sys L n q p then h3spK sys L n q p else 0

open Classical in
/-- The resonant part of the same-pair kernel. -/
noncomputable def h3rK (q p : Cfg eta n) : ℂ := if gapC sys L n q p then 0 else h3spK sys L n q p

/-- `H₃^{gap,sp}`. -/
noncomputable def H3gapSp : En eta n →ₗ[ℂ] En eta n := FSKernel.kop (h3gK sys L n)

/-- `H₃^{res,sp}`. -/
noncomputable def H3resSp : En eta n →ₗ[ℂ] En eta n := FSKernel.kop (h3rK sys L n)

variable {sys L n}

theorem H3sp_split : H3sp sys L n = H3gapSp sys L n + H3resSp sys L n := by
  rw [H3sp, H3gapSp, H3resSp, ← FSKernel.kop_add]
  congr 1
  funext q p
  simp only [Pi.add_apply, h3gK, h3rK]
  split_ifs <;> simp

lemma h3gK_conj (hL : 0 < L) (q p : Cfg eta n) : h3gK sys L n p q = conj (h3gK sys L n q p) := by
  unfold h3gK
  rw [gapC_comm p q]
  split_ifs
  · exact h3spK_conj hL q p
  · simp

lemma h3rK_conj (hL : 0 < L) (q p : Cfg eta n) : h3rK sys L n p q = conj (h3rK sys L n q p) := by
  unfold h3rK
  rw [gapC_comm p q]
  split_ifs
  · simp
  · exact h3spK_conj hL q p

theorem H3gapSp_symm (hL : 0 < L) : (H3gapSp sys L n).IsSymmetric :=
  FSKernel.kop_symm _ fun q p => h3gK_conj hL q p

theorem H3resSp_symm (hL : 0 < L) : (H3resSp sys L n).IsSymmetric :=
  FSKernel.kop_symm _ fun q p => h3rK_conj hL q p

end Split

/-! ## The resonant shells -/

section Shells

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

variable (sys L n) in
open Classical in
/-- The majorant of the same-pair resonant residual on channel `m.1`, dyadic shell `m.2`. -/
noncomputable def r3Maj (m : Ch eta × ℕ) (q p : Cfg eta n) : ℝ :=
  if OnCh m.1 (cidx n q) (cidx n p) ∧ q ≠ p ∧
      ¬ (gF L ^ 2 * FSChannel.rho (chT n m.1 q p) / muCh sys m.1 ≤
        |Asym sys L n q - Asym sys L n p|) ∧
      (4 : ℝ) ^ m.2 ≤ FSLattice.lsq (chT n m.1 q p) ∧ FSLattice.lsq (chT n m.1 q p) ≤ 4 ^ (m.2 + 1)
  then Bh3 sys L n m.1 * ((m.2 + 3) * (1 / 2) ^ m.2) else 0

lemma r3Maj_nonneg (hL : 0 < L) (m : Ch eta × ℕ) (q p : Cfg eta n) : 0 ≤ r3Maj sys L n m q p := by
  unfold r3Maj
  have := Bh3_nonneg (sys := sys) (n := n) hL m.1
  split_ifs
  · positivity
  · exact le_rfl

lemma r3Maj_symm (m : Ch eta × ℕ) (q p : Cfg eta n) : r3Maj sys L n m q p = r3Maj sys L n m p q := by
  unfold r3Maj
  rw [lsq_chT_swap m.1 q p, chT_swap m.1 q p, abs_sub_comm (Asym sys L n p)]
  have h1 : OnCh m.1 (cidx n q) (cidx n p) ↔ OnCh m.1 (cidx n p) (cidx n q) :=
    ⟨onCh_symm, onCh_symm⟩
  by_cases hc : OnCh m.1 (cidx n q) (cidx n p) ∧ q ≠ p ∧
      ¬ (gF L ^ 2 * FSChannel.rho (chT n m.1 q p) / muCh sys m.1 ≤
        |Asym sys L n q - Asym sys L n p|) ∧
      (4 : ℝ) ^ m.2 ≤ FSLattice.lsq (chT n m.1 q p) ∧ FSLattice.lsq (chT n m.1 q p) ≤ 4 ^ (m.2 + 1)
  · rw [if_pos hc, if_pos ⟨h1.mp hc.1, Ne.symm hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2⟩]
  · rw [if_neg hc, if_neg]
    intro h
    exact hc ⟨h1.mpr h.1, Ne.symm h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

open Classical in
lemma col_r3Maj_le (hL : 0 < L) (m : Ch eta × ℕ) (p : Cfg eta n) :
    ∑ q, r3Maj sys L n m q p ≤ Bh3 sys L n m.1 * ((m.2 + 3) * (1 / 2) ^ m.2) * (55000 * 4 ^ m.2) := by
  obtain ⟨j, i⟩ := m
  set P : Cfg eta n → Prop := fun q => OnCh j (cidx n q) (cidx n p) ∧ q ≠ p ∧
      ¬ (gF L ^ 2 * FSChannel.rho (chT n j q p) / muCh sys j ≤ |Asym sys L n q - Asym sys L n p|) ∧
      (4 : ℝ) ^ i ≤ FSLattice.lsq (chT n j q p) ∧ FSLattice.lsq (chT n j q p) ≤ 4 ^ (i + 1)
  have hB := Bh3_nonneg (sys := sys) (n := n) hL j
  have e : ∑ q, r3Maj sys L n (j, i) q p =
      Bh3 sys L n j * ((i + 3) * (1 / 2) ^ i) * ((Finset.univ.filter P).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold r3Maj
    split_ifs <;> simp
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hc := shell_count_le (sys := sys) j p (i := i) (δ := 2 ^ (i + 2)) (by positivity)
    (Finset.univ.filter P) (by
      intro q hq
      obtain ⟨hon, -, hres, hs1, hs2⟩ := (Finset.mem_filter.mp hq).2
      refine ⟨hon, hs1, hs2, ?_⟩
      have h1 := resonant_slab hL hon hres
      have h2 := rho_le_of_shell hs2
      rw [pow_succ 2 (i + 1)]
      linarith)
  calc ((Finset.univ.filter P).card : ℝ) ≤ 11000 * 4 ^ i * (1 + 2 ^ (i + 2) / 2 ^ i) := hc
    _ = 55000 * 4 ^ i := by
        rw [pow_add]; field_simp; ring

/-- The pinned support of a resonant element in a shell `i ≥ 3`. -/
lemma r3Maj_pin (hL : 0 < L) {m : Ch eta × ℕ} (hm : 3 ≤ m.2) {q p : Cfg eta n}
    (h : r3Maj sys L n m q p ≠ 0) :
    ∃ c ∈ moved m.1, gF L * (3 / 8 * 2 ^ m.2) < finitePlaneWaveKabs (2 * Real.pi / L) n (p c) := by
  obtain ⟨j, i⟩ := m
  simp only at hm ⊢
  unfold r3Maj at h
  split_ifs at h with hc
  · obtain ⟨hon, -, hres, hs1, -⟩ := hc
    have h1 := resonant_slab hL hon hres
    have h64 : (64 : ℝ) ≤ FSLattice.lsq (chT n j q p) := by
      have : (4 : ℝ) ^ 3 ≤ 4 ^ i := pow_le_pow_right₀ (by norm_num) hm
      norm_num at this; linarith
    have hr8 : 8 ≤ FSChannel.rho (chT n j q p) := by
      unfold FSChannel.rho
      apply Real.le_sqrt_of_sq_le; norm_num; exact h64
    have hlow : |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| <
        FSLattice.lsq (chT n j q p) / 4 := by
      have := FSChannel.rho_sq (chT n j q p)
      nlinarith
    obtain ⟨c, hc, hcn⟩ := pin_register sys j (cidx n p) (chT n j q p) hlow
    refine ⟨c, hc, kabs_gt_of_nsq hL ?_⟩
    have e4 : (3 / 8 * (2 : ℝ) ^ i) ^ 2 = 9 / 64 * 4 ^ i := by
      rw [mul_pow, ← pow_mul, mul_comm i 2, pow_mul]; norm_num
    rw [e4]
    linarith
  · exact absurd rfl h

/-- One resonant shell of `H₃^{res,sp}`. -/
theorem norm_r3_shell_le (hL : 0 < L) (m : Ch eta × ℕ) {M : ℝ} {u : En eta n}
    (hu : IsGood sys L 1 M u) :
    ‖FSKernel.kop (fun q p => (r3Maj sys L n m q p : ℂ)) (FSKernel.absv u)‖ ≤
      Bh3 sys L n m.1 * ((m.2 + 3) * (1 / 2) ^ m.2) * M * (440000 / c0 L ^ 2 + 3520000) := by
  classical
  have hM := good_nonneg hu
  have hc0 := c0_pos hL
  set V := Bh3 sys L n m.1 * ((m.2 + 3) * (1 / 2) ^ m.2) with hV
  have hV0 : 0 ≤ V := by have := Bh3_nonneg (sys := sys) (n := n) hL m.1; positivity
  have hSchur : ∀ v : En eta n, ‖FSKernel.kop (fun q p => (r3Maj sys L n m q p : ℂ)) v‖ ≤
      V * (55000 * 4 ^ m.2) * ‖v‖ := fun v =>
    FSKernel.norm_kop_real_le _ (r3Maj_nonneg hL m) (by positivity)
      (fun q => by
        calc ∑ p, r3Maj sys L n m q p = ∑ p, r3Maj sys L n m p q :=
              Finset.sum_congr rfl fun p _ => r3Maj_symm m q p
          _ ≤ _ := col_r3Maj_le hL m q)
      (col_r3Maj_le hL m) v
  by_cases hm : 3 ≤ m.2
  · set P : Cfg eta n → Prop := fun p => ∃ c ∈ moved m.1,
      gF L * (3 / 8 * 2 ^ m.2) < finitePlaneWaveKabs (2 * Real.pi / L) n (p c)
    rw [FSKernel.kop_res_of_cols _ P (fun q p h => r3Maj_pin hL hm (by intro h0; apply h; rw [h0]; simp))]
    refine (hSchur _).trans ?_
    rw [FSKernel.norm_res_absv]
    have hl : 0 ≤ gF L * (3 / 8 * 2 ^ m.2) := by have := gF_pos hL; positivity
    have h1 : ‖FSKernel.res P u‖ ≤ ∑ c ∈ moved m.1, ‖regTail L c (gF L * (3 / 8 * 2 ^ m.2)) u‖ :=
      norm_res_pin_le (L := L) m.1 (gF L * (3 / 8 * 2 ^ m.2)) u
    have h2 : ∑ c ∈ moved m.1, ‖regTail L c (gF L * (3 / 8 * 2 ^ m.2)) u‖ ≤
        ∑ c ∈ moved m.1, 4 * M / (1 + gF L * (3 / 8 * 2 ^ m.2)) ^ 2 :=
      Finset.sum_le_sum fun c _ => regTail_le_good hu c hl
    have hcard : (moved m.1).card ≤ 2 := by
      cases m.1 with
      | inl a => simp [moved]
      | inr pr => exact Finset.card_le_two
    have h3 : ∑ c ∈ moved m.1, 4 * M / (1 + gF L * (3 / 8 * 2 ^ m.2)) ^ 2 ≤
        2 * (4 * M / (c0 L ^ 2 * 4 ^ m.2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have : ((moved m.1).card : ℝ) ≤ 2 := by exact_mod_cast hcard
      have h4 : 4 * M / (1 + gF L * (3 / 8 * 2 ^ m.2)) ^ 2 ≤ 4 * M / (c0 L ^ 2 * 4 ^ m.2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have := one_add_l_ge (L := L) m.2
        have e : c0 L ^ 2 * 4 ^ m.2 = (c0 L * 2 ^ m.2) ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm m.2 2, pow_mul]; norm_num
        rw [e]
        exact pow_le_pow_left₀ (by positivity) this 2
      exact mul_le_mul this h4 (by positivity) (by norm_num)
    have hres : ‖FSKernel.res P u‖ ≤ 8 * M / (c0 L ^ 2 * 4 ^ m.2) :=
      h1.trans (h2.trans (h3.trans (le_of_eq (by ring))))
    calc V * (55000 * 4 ^ m.2) * ‖FSKernel.res P u‖
        ≤ V * (55000 * 4 ^ m.2) * (8 * M / (c0 L ^ 2 * 4 ^ m.2)) :=
          mul_le_mul_of_nonneg_left hres (by positivity)
      _ = V * M * (440000 / c0 L ^ 2) := by field_simp; ring
      _ ≤ V * M * (440000 / c0 L ^ 2 + 3520000) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · push Not at hm
    refine (hSchur _).trans ?_
    rw [FSKernel.norm_absv]
    have h4 : (4 : ℝ) ^ m.2 ≤ 64 := by
      have : (4 : ℝ) ^ m.2 ≤ 4 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this; linarith
    have hu' := norm_le_good hu
    calc V * (55000 * 4 ^ m.2) * ‖u‖ ≤ V * (55000 * 64) * M := by gcongr
      _ = V * M * 3520000 := by ring
      _ ≤ V * M * (440000 / c0 L ^ 2 + 3520000) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : 0 ≤ 440000 / c0 L ^ 2 := by positivity
          linarith

/-- The shell index of a cube transfer: `4^i ≤ |θ|² ≤ 12 n²` forces `i ≤ ⌊log₂ n⌋ + 2`. -/
lemma shell_index_le_cube {x : ℝ} {i : ℕ} (hi : (4 : ℝ) ^ i ≤ x) (hx : x ≤ 12 * (n : ℝ) ^ 2) :
    i ≤ Nat.log 2 n + 2 := by
  by_contra h
  push Not at h
  have hk : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hk' : (n : ℝ) < 2 ^ (Nat.log 2 n + 1) := by exact_mod_cast hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (n : ℝ) ^ 2 < 4 ^ (Nat.log 2 n + 1) := by
    rw [← FSBand.two_pow_sq]; exact pow_lt_pow_left₀ hk' hn0 two_ne_zero
  have h2 : (4 : ℝ) ^ (Nat.log 2 n + 3) ≤ 4 ^ i := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (4 : ℝ) ^ (Nat.log 2 n + 3) = 16 * 4 ^ (Nat.log 2 n + 1) := by
    rw [show Nat.log 2 n + 3 = (Nat.log 2 n + 1) + 2 by ring, pow_add]; norm_num; ring
  nlinarith

end Shells

/-! ## `lem:res3` -/

section Res3

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

variable (sys L) in
/-- The constant of `lem:res3` (same-pair): `C_R3 = D + 10 (440000/c₀² + 3520000) Σ_j B_j`. -/
noncomputable def CR3 (n : ℕ) : ℝ :=
  Dh3 sys L n + 10 * (440000 / c0 L ^ 2 + 3520000) * ∑ j : Ch eta, Bh3 sys L n j

lemma sum_i_three_le (N : ℕ) : ∑ i ∈ Finset.range N, ((i : ℝ) + 3) * (1 / 2) ^ i ≤ 10 := by
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_two_i_three_le N)
  have : (0 : ℝ) ≤ (1 / 2) ^ i := by positivity
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  nlinarith

/-- **`lem:res3`, same-pair case**: `‖H₃^{res,sp} u‖ ≤ C_R3(n) M` for every good state
(`IsGood 1 M u`), `C_R3(n) = O(n⁻³ log n)`. -/
theorem norm_H3resSp_good (hL : 0 < L) (hn : 2 ≤ n) {M : ℝ} {u : En eta n}
    (hu : IsGood sys L 1 M u) : ‖H3resSp sys L n u‖ ≤ CR3 sys L n * M := by
  classical
  have hM := good_nonneg hu
  have hc0 := c0_pos hL
  set K := (440000 / c0 L ^ 2 + 3520000 : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hD0 : 0 ≤ Dh3 sys L n := le_trans (norm_nonneg _) (norm_h3spK_diag_le (sys := sys) hL hn
    (Classical.arbitrary _))
  set N := Nat.log 2 n + 3
  -- diagonal and off-diagonal parts
  set dK : Cfg eta n → Cfg eta n → ℂ := fun q p => if q = p then h3rK sys L n q p else 0
  set oK : Cfg eta n → Cfg eta n → ℂ := fun q p => if q = p then 0 else h3rK sys L n q p
  have hsplit : H3resSp sys L n = FSKernel.kop dK + FSKernel.kop oK := by
    rw [H3resSp, ← FSKernel.kop_add]
    congr 1
    funext q p
    simp only [Pi.add_apply, dK, oK]
    split_ifs <;> simp
  rw [hsplit, LinearMap.add_apply]
  have hdiag : ‖FSKernel.kop dK u‖ ≤ Dh3 sys L n * ‖u‖ := by
    have hent : ∀ q p, ‖dK q p‖ ≤ if q = p then Dh3 sys L n else 0 := by
      intro q p
      simp only [dK]
      split_ifs with h
      · subst h
        unfold h3rK
        split_ifs with hg
        · exact absurd rfl hg.1
        · exact norm_h3spK_diag_le hL hn q
      · simp
    apply FSKernel.norm_kop_le' _ hD0
    · intro q
      calc ∑ p, ‖dK q p‖ ≤ ∑ p, (if q = p then Dh3 sys L n else 0) :=
            Finset.sum_le_sum fun p _ => hent q p
        _ = Dh3 sys L n := by rw [Finset.sum_ite_eq]; simp
    · intro p
      calc ∑ q, ‖dK q p‖ ≤ ∑ q, (if q = p then Dh3 sys L n else 0) :=
            Finset.sum_le_sum fun q _ => hent q p
        _ = Dh3 sys L n := by rw [Finset.sum_ite_eq']; simp
  -- the off-diagonal majorants
  have hdom : ∀ q p, ‖oK q p‖ ≤ ∑ m ∈ (Finset.univ : Finset (Ch eta)) ×ˢ Finset.range N,
      r3Maj sys L n m q p := by
    intro q p
    have hsum0 : 0 ≤ ∑ m ∈ (Finset.univ : Finset (Ch eta)) ×ˢ Finset.range N,
        r3Maj sys L n m q p := Finset.sum_nonneg fun m _ => r3Maj_nonneg hL m q p
    simp only [oK]
    split_ifs with hqp
    · rw [norm_zero]; exact hsum0
    unfold h3rK
    split_ifs with hgp
    · rw [norm_zero]; exact hsum0
    by_cases hj : ∃ j, OnCh j (cidx n q) (cidx n p)
    swap
    · push Not at hj
      rw [h3spK_eq_zero hj, norm_zero]; exact hsum0
    obtain ⟨j, hj⟩ := hj
    have hfl : ¬ (gF L ^ 2 * FSChannel.rho (chT n j q p) / muCh sys j ≤
        |Asym sys L n q - Asym sys L n p|) := fun h => hgp ⟨hqp, j, hj, h⟩
    obtain ⟨i, hi1, hi2⟩ := exists_shell (one_le_lsq_chT hj hqp)
    have hiI : i ≤ Nat.log 2 n + 2 :=
      shell_index_le_cube hi1 (lsq_chT_le_cube j q p)
    have hval : r3Maj sys L n (j, i) q p = Bh3 sys L n j * ((i + 3) * (1 / 2) ^ i) := by
      unfold r3Maj; rw [if_pos ⟨hj, hqp, hfl, hi1, hi2⟩]
    have hm : ((j, i) : Ch eta × ℕ) ∈ (Finset.univ : Finset (Ch eta)) ×ˢ Finset.range N := by
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and, N]; omega
    -- the shell value of eq:h3
    have hρ1 : (2 : ℝ) ^ i ≤ FSChannel.rho (chT n j q p) := by
      unfold FSChannel.rho; apply Real.le_sqrt_of_sq_le; rw [FSBand.two_pow_sq]; exact hi1
    have hρ2 := rho_le_of_shell hi2
    have hlog : Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ ≤ i + 1 := by
      have h1 : ⌈FSChannel.rho (chT n j q p)⌉₊ ≤ 2 ^ (i + 1) := by
        rw [Nat.ceil_le]; push_cast; exact hρ2
      calc Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ ≤ Nat.log 2 (2 ^ (i + 1)) :=
            Nat.log_mono_right h1
        _ = i + 1 := Nat.log_pow (by norm_num) _
    have hX : ((Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ : ℕ) + 2 : ℝ) /
        FSChannel.rho (chT n j q p) ≤ (i + 3) * (1 / 2) ^ i := by
      have h2i : (0 : ℝ) < 2 ^ i := by positivity
      have hl : ((Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ : ℕ) : ℝ) ≤ i + 1 := by
        exact_mod_cast hlog
      rw [div_le_iff₀ (by linarith), one_div_pow]
      calc ((Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ : ℕ) + 2 : ℝ) ≤ i + 3 := by linarith
        _ = (i + 3) * (1 / 2 ^ i) * 2 ^ i := by field_simp
        _ ≤ (i + 3) * (1 / 2 ^ i) * FSChannel.rho (chT n j q p) :=
            mul_le_mul_of_nonneg_left hρ1 (by positivity)
    have hB := Bh3_nonneg (sys := sys) (n := n) hL j
    refine (norm_h3spK_le hL hn hj hqp).trans ?_
    calc Bh3 sys L n j * (((Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ : ℕ) + 2 : ℝ) /
          FSChannel.rho (chT n j q p))
        ≤ Bh3 sys L n j * ((i + 3) * (1 / 2) ^ i) := mul_le_mul_of_nonneg_left hX hB
      _ = r3Maj sys L n (j, i) q p := hval.symm
      _ ≤ _ := Finset.single_le_sum (f := fun m => r3Maj sys L n m q p)
          (fun m _ => r3Maj_nonneg hL m q p) hm
  have hoff := FSKernel.norm_kop_le_of_maj _ oK (r3Maj sys L n) (r3Maj_nonneg hL) hdom u
  have hoff2 : ∑ m ∈ (Finset.univ : Finset (Ch eta)) ×ˢ Finset.range N,
      ‖FSKernel.kop (fun q p => (r3Maj sys L n m q p : ℂ)) (FSKernel.absv u)‖ ≤
      10 * K * (∑ j : Ch eta, Bh3 sys L n j) * M := by
    refine (Finset.sum_le_sum fun m _ => norm_r3_shell_le hL m hu).trans ?_
    rw [Finset.sum_product]
    have hj : ∀ j : Ch eta, ∑ i ∈ Finset.range N,
        Bh3 sys L n (j, i).1 * (((j, i).2 + 3) * (1 / 2) ^ (j, i).2) * M * K ≤
        10 * K * Bh3 sys L n j * M := by
      intro j
      simp only
      have hB := Bh3_nonneg (sys := sys) (n := n) hL j
      calc ∑ i ∈ Finset.range N, Bh3 sys L n j * (((i : ℝ) + 3) * (1 / 2) ^ i) * M * K
          = Bh3 sys L n j * M * K * ∑ i ∈ Finset.range N, ((i : ℝ) + 3) * (1 / 2) ^ i := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ ≤ Bh3 sys L n j * M * K * 10 :=
            mul_le_mul_of_nonneg_left (sum_i_three_le N) (by positivity)
        _ = 10 * K * Bh3 sys L n j * M := by ring
    calc ∑ j : Ch eta, ∑ i ∈ Finset.range N,
          Bh3 sys L n (j, i).1 * (((j, i).2 + 3) * (1 / 2) ^ (j, i).2) * M * K
        ≤ ∑ j : Ch eta, 10 * K * Bh3 sys L n j * M := Finset.sum_le_sum fun j _ => hj j
      _ = 10 * K * (∑ j : Ch eta, Bh3 sys L n j) * M := by
          rw [Finset.mul_sum, Finset.sum_mul]
  have hu' := norm_le_good hu
  refine (norm_add_le _ _).trans ?_
  calc ‖FSKernel.kop dK u‖ + ‖FSKernel.kop oK u‖
      ≤ Dh3 sys L n * M + 10 * K * (∑ j : Ch eta, Bh3 sys L n j) * M :=
        add_le_add (hdiag.trans (mul_le_mul_of_nonneg_left hu' hD0)) (hoff.trans hoff2)
    _ = CR3 sys L n * M := by unfold CR3; rw [← hK]; ring

end Res3

end FSNormal
