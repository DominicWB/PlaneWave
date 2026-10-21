import PlaneWave.SamePair.Res3

/-!
# Same-pair third order, part 7: the same-pair third generator `Σ₃^sp`

`Σ₃^sp = H₃^{gap,sp}/ω` (the kernel `h₃/(E(q) - E(p))` on the gapped same-pair elements):

* **`comm_Sig3sp`**: the homological equation `[A, Σ₃^sp] = H₃^{gap,sp}`, equivalently
  `[Σ₃^sp, A] = -(H₃^sp - H₃^{res,sp})` (`comm_Sig3sp'`, the form of the formal hypothesis of
  `thm:src3` restricted to the same-pair class);
* **`inner_Sig3sp`**: `Σ₃^sp` is skew-adjoint (Hermitian kernel over an antisymmetric mismatch);
* **`norm_Sig3sp_le`**: the Schur bound `‖Σ₃^sp‖ ≤ C_Σ3(n) = O(n⁻³ log⁴ n)` (review F4 H-2:
  of order `μ³ K⁻³ log⁴ K`, not the text's `K⁻²`), from `lem:h3` (`norm_h3spK_le`), the cube cap
  `|F_c(θ)| < 2^{J_n + 3}` (`slabF_cap_cube`) and the lattice sum `sig3_core`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Gen

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

/-- **The same-pair third generator** `Σ₃^sp = H₃^{gap,sp}/ω`. -/
noncomputable def Sig3sp : En eta n →ₗ[ℂ] En eta n :=
  FSKernel.kop (FSKernel.divK (Asym sys L n) (h3gK sys L n))

end Gen

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

/-! ## The homological equation and skewness -/

/-- **The homological equation** `[A, Σ₃^sp] = H₃^{gap,sp}`. -/
theorem comm_Sig3sp (hL : 0 < L) :
    FSKernel.dg (fun q => (Asym sys L n q : ℂ)) ∘ₗ Sig3sp sys L n -
      Sig3sp sys L n ∘ₗ FSKernel.dg (fun q => (Asym sys L n q : ℂ)) = H3gapSp sys L n := by
  unfold Sig3sp H3gapSp
  apply FSKernel.comm_divK
  intro q p hqp
  unfold h3gK
  split_ifs with h
  · exact absurd hqp (gapC_ne hL h)
  · rfl

/-- The homological equation in the form of the formal hypothesis of `thm:src3`:
`[Σ₃^sp, A] = -(H₃^sp - H₃^{res,sp})`. -/
theorem comm_Sig3sp' (hL : 0 < L) :
    Sig3sp sys L n ∘ₗ FSKernel.dg (fun q => (Asym sys L n q : ℂ)) -
      FSKernel.dg (fun q => (Asym sys L n q : ℂ)) ∘ₗ Sig3sp sys L n =
      -(H3sp sys L n - H3resSp sys L n) := by
  rw [H3sp_split, add_sub_cancel_right, ← comm_Sig3sp hL, neg_sub]

/-- The kernel of `Σ₃^sp` is skew-Hermitian. -/
lemma sig3K_skew (hL : 0 < L) (q p : Cfg eta n) :
    FSKernel.divK (Asym sys L n) (h3gK sys L n) p q =
      -conj (FSKernel.divK (Asym sys L n) (h3gK sys L n) q p) := by
  unfold FSKernel.divK
  by_cases h : Asym sys L n q = Asym sys L n p
  · rw [if_pos h.symm, if_pos h]; simp
  · rw [if_neg (Ne.symm h), if_neg h, h3gK_conj hL q p, map_div₀, Complex.conj_ofReal,
      ← div_neg, ← Complex.ofReal_neg, neg_sub]

/-- **`Σ₃^sp` is skew-adjoint**: `⟪Σ u, v⟫ = -⟪u, Σ v⟫`. -/
theorem inner_Sig3sp (hL : 0 < L) (u v : En eta n) :
    ⟪Sig3sp sys L n u, v⟫_ℂ = -⟪u, Sig3sp sys L n v⟫_ℂ :=
  FSKernel.kop_skew _ (fun q p => sig3K_skew hL q p) u v

/-! ## The cube cap -/

omit [Fintype ν] in
/-- The kinetic energy on the cube is at most `3 η g² n²/2`. -/
lemma Asym_le_cube (q : Cfg eta n) : Asym sys L n q ≤ 3 * eta * gF L ^ 2 * n ^ 2 / 2 := by
  rw [Asym_eq_Ek]
  have hq : InP (n : ℝ) (cidx n q) := inP_of_mem_cube (finiteConfigLatticeIndex_mem_cube eta n q)
  unfold Ek E
  have hterm : ∀ c ∈ (Finset.univ : Finset (Fin eta)),
      gF L ^ 2 / (2 * sys.mass c) * nsq (cidx n q c) ≤ 3 * gF L ^ 2 * n ^ 2 / 2 := by
    intro c _
    have hm := sys.one_le_mass c
    have hg := sq_nonneg (gF L)
    have h0 := nsq_nonneg (cidx n q c)
    have hns : nsq (cidx n q c) ≤ 3 * (n : ℝ) ^ 2 := by
      have hc : ∀ i, ((cidx n q c i : ℤ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := fun i => by
        have h1 := hq c i
        have h2 := sq_abs ((cidx n q c i : ℤ) : ℝ)
        have h3 : |((cidx n q c i : ℤ) : ℝ)| ^ 2 ≤ (n : ℝ) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
        linarith
      unfold nsq
      linarith [hc 0, hc 1, hc 2]
    calc gF L ^ 2 / (2 * sys.mass c) * nsq (cidx n q c) ≤ gF L ^ 2 / 2 * nsq (cidx n q c) := by
          gcongr; linarith
      _ ≤ gF L ^ 2 / 2 * (3 * (n : ℝ) ^ 2) := by gcongr
      _ = 3 * gF L ^ 2 * n ^ 2 / 2 := by ring
  calc ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (cidx n q c) ≤
        ∑ _c : Fin eta, 3 * gF L ^ 2 * n ^ 2 / 2 := Finset.sum_le_sum hterm
    _ = 3 * eta * gF L ^ 2 * n ^ 2 / 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

omit [Fintype ν] in
/-- **The mismatch cap on the cube**: `|F_c(θ)| < 2^{J_n + 2} · 2`. -/
lemma slabF_cap_cube (hL : 0 < L) {j : Ch eta} {q p : Cfg eta n}
    (hj : OnCh j (cidx n q) (cidx n p)) :
    |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| < 2 ^ (Jn sys n + 1 + 1) * 2 := by
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hE := Asym_hop (sys := sys) (L := L) hj
  have hq' := Asym_le_cube (sys := sys) (L := L) q
  have hp' := Asym_le_cube (sys := sys) (L := L) p
  have hq0 := Asym_nonneg (sys := sys) (L := L) q
  have hp0 := Asym_nonneg (sys := sys) (L := L) p
  set F := FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)
  have habs : |F| = 2 * muCh sys j / gF L ^ 2 * |Asym sys L n q - Asym sys L n p| := by
    rw [hE, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))]
    field_simp
  have hdiff : |Asym sys L n q - Asym sys L n p| ≤ 3 * eta * gF L ^ 2 * n ^ 2 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hF : |F| ≤ 3 * (mtop sys * eta * (n : ℝ) ^ 2) := by
    rw [habs]
    have hm := muCh_le_mtop (sys := sys) j
    calc 2 * muCh sys j / gF L ^ 2 * |Asym sys L n q - Asym sys L n p|
        ≤ 2 * muCh sys j / gF L ^ 2 * (3 * eta * gF L ^ 2 * n ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = 3 * (muCh sys j * eta * (n : ℝ) ^ 2) := by field_simp
      _ ≤ 3 * (mtop sys * eta * (n : ℝ) ^ 2) := by gcongr
  have hlog : ⌈mtop sys * eta * (n : ℝ) ^ 2⌉₊ < 2 ^ (Jn sys n + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hlog' : mtop sys * eta * (n : ℝ) ^ 2 < 2 ^ (Jn sys n + 1) := by
    have h1 := Nat.le_ceil (mtop sys * eta * (n : ℝ) ^ 2)
    have h2 : ((⌈mtop sys * eta * (n : ℝ) ^ 2⌉₊ : ℕ) : ℝ) < ((2 ^ (Jn sys n + 1) : ℕ) : ℝ) := by
      exact_mod_cast hlog
    push_cast at h2
    linarith
  have e : (2 : ℝ) ^ (Jn sys n + 1 + 1) * 2 = 4 * 2 ^ (Jn sys n + 1) := by ring
  rw [e]
  have h2pos : (0 : ℝ) < 2 ^ (Jn sys n + 1) := by positivity
  linarith

/-! ## The Schur bound -/

variable (sys L n) in
/-- The Schur constant of `Σ₃^sp`:
`C_Σ3 = Σ_j B_j (J_n + 4)(2μ_j/g²) · 11000 (2J_n + 5)(J_n + 2)`, `O(n⁻³ log⁴ n)`. -/
noncomputable def CS3 : ℝ :=
  ∑ j : Ch eta, Bh3 sys L n j * (Jn sys n + 4) * (2 * muCh sys j / gF L ^ 2) *
    (11000 * (2 * (Jn sys n + 1 : ℕ) + 3) * ((Jn sys n + 1 : ℕ) + 1))

lemma CS3_nonneg (hL : 0 < L) : 0 ≤ CS3 sys L n := by
  unfold CS3
  refine Finset.sum_nonneg fun j _ => ?_
  have := Bh3_nonneg (sys := sys) (n := n) hL j
  have := muCh_pos sys j
  have := gF_pos hL
  positivity

open Classical in
/-- One channel of a column of `Σ₃^sp`. -/
lemma col_sig3_chan_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (p : Cfg eta n) :
    ∑ q ∈ Finset.univ.filter (fun q => OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p),
      ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| ≤
      Bh3 sys L n j * (Jn sys n + 4) * (2 * muCh sys j / gF L ^ 2) *
        (11000 * (2 * (Jn sys n + 1 : ℕ) + 3) * ((Jn sys n + 1 : ℕ) + 1)) := by
  classical
  set T := Finset.univ.filter (fun q => OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p)
  set c := cCh sys j (cidx n p)
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hB := Bh3_nonneg (sys := sys) (n := n) hL j
  have hterm : ∀ q ∈ T, ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| ≤
      Bh3 sys L n j * (Jn sys n + 4) * (2 * muCh sys j / gF L ^ 2) *
        (1 / |FSLattice.slabF c (chT n j q p)| * (1 / FSChannel.rho (chT n j q p))) := by
    intro q hq
    obtain ⟨hj, hg'⟩ := (Finset.mem_filter.mp hq).2
    have hqp : q ≠ p := hg'.1
    have hfl := floor_of_gapC hL hj hg'
    have hcap := slabF_cap_cube (sys := sys) hL hj
    have hρ1 : 1 ≤ FSChannel.rho (chT n j q p) := FSLattice.one_le_rho (one_le_lsq_chT hj hqp)
    have hF0 : 0 < |FSLattice.slabF c (chT n j q p)| := by linarith
    -- the logarithmic factor below the cap
    have hρc : FSChannel.rho (chT n j q p) < 2 ^ (Jn sys n + 1 + 1) := by
      have : 2 * FSChannel.rho (chT n j q p) < 2 ^ (Jn sys n + 1 + 1) * 2 := lt_of_le_of_lt hfl hcap
      linarith
    have hlog := FSLattice.log_ceil_le hρc
    have hlog' : ((Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ : ℕ) : ℝ) + 2 ≤ Jn sys n + 4 := by
      have : ((Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ : ℕ) : ℝ) ≤ Jn sys n + 1 + 1 := by
        exact_mod_cast hlog
      linarith
    have hh := norm_h3spK_le (sys := sys) hL hn hj hqp
    rw [mismatch_eq (sys := sys) hL hj]
    have e1 : ‖h3spK sys L n q p‖ / (gF L ^ 2 / (2 * muCh sys j) *
        |FSLattice.slabF c (chT n j q p)|) =
        (2 * muCh sys j / gF L ^ 2) * (‖h3spK sys L n q p‖ * (1 / |FSLattice.slabF c (chT n j q p)|)) := by
      field_simp
    rw [e1]
    have hX : ‖h3spK sys L n q p‖ ≤ Bh3 sys L n j * (Jn sys n + 4) *
        (1 / FSChannel.rho (chT n j q p)) := by
      refine hh.trans ?_
      rw [div_eq_mul_one_div _ (FSChannel.rho (chT n j q p)), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog' hB) (by positivity)
    calc 2 * muCh sys j / gF L ^ 2 * (‖h3spK sys L n q p‖ * (1 / |FSLattice.slabF c (chT n j q p)|))
        ≤ 2 * muCh sys j / gF L ^ 2 * (Bh3 sys L n j * (Jn sys n + 4) *
            (1 / FSChannel.rho (chT n j q p)) * (1 / |FSLattice.slabF c (chT n j q p)|)) := by
          gcongr
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hinj : Set.InjOn (fun q => chT n j q p) T := fun q hq q' hq' h =>
    chT_injOn j p (Finset.mem_filter.mp hq).2.1 (Finset.mem_filter.mp hq').2.1 h
  rw [← Finset.sum_image (f := fun θ => 1 / |FSLattice.slabF c θ| * (1 / FSChannel.rho θ)) hinj]
  apply FSLattice.sig3_core c (J := Jn sys n + 1)
  intro θ hθ
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hθ
  obtain ⟨hj, hg'⟩ := (Finset.mem_filter.mp hq).2
  exact ⟨one_le_lsq_chT hj hg'.1, floor_of_gapC hL hj hg', slabF_cap_cube hL hj⟩

/-- The columns of `Σ₃^sp`. -/
lemma col_sig3_le (hL : 0 < L) (hn : 2 ≤ n) (p : Cfg eta n) :
    ∑ q, ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) q p‖ ≤ CS3 sys L n := by
  classical
  have hent : ∀ q, ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) q p‖ ≤
      ∑ j : Ch eta, if OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p then
        ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| else 0 := by
    intro q
    have hnn : 0 ≤ ∑ j : Ch eta, if OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p then
        ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| else 0 :=
      Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
    unfold FSKernel.divK h3gK
    split_ifs with hA hg
    · rw [norm_zero]; exact hnn
    · obtain ⟨j, hj, -⟩ := hg.2
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun j : Ch eta =>
        if OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p then
          ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| else 0)
        (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ j))
      exact (if_pos ⟨hj, hg⟩).symm
    · rw [zero_div, norm_zero]; exact hnn
  calc ∑ q, ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) q p‖
      ≤ ∑ q, ∑ j : Ch eta, (if OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p then
          ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| else 0) :=
        Finset.sum_le_sum fun q _ => hent q
    _ = ∑ j : Ch eta, ∑ q ∈ Finset.univ.filter
          (fun q => OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p),
          ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.sum_filter _ _).symm
    _ ≤ CS3 sys L n := Finset.sum_le_sum fun j _ => col_sig3_chan_le hL hn j p

/-- **The Schur bound for the same-pair third generator**: `‖Σ₃^sp u‖ ≤ C_Σ3(n) ‖u‖`,
`C_Σ3(n) = O(n⁻³ log⁴ n)`. -/
theorem norm_Sig3sp_le (hL : 0 < L) (hn : 2 ≤ n) (u : En eta n) :
    ‖Sig3sp sys L n u‖ ≤ CS3 sys L n * ‖u‖ := by
  apply FSKernel.norm_kop_le' _ (CS3_nonneg hL)
  · intro q
    calc ∑ p, ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) q p‖
        = ∑ p, ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) p q‖ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [sig3K_skew hL q p, norm_neg, Complex.norm_conj]
      _ ≤ CS3 sys L n := col_sig3_le hL hn q
  · exact col_sig3_le hL hn

end FSNormal
