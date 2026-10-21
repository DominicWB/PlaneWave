import PlaneWave.SamePair.ThirdOrderKernel

/-!
# Same-pair third order, part 5: the same-pair component of `H₃^ret` and `lem:h3`

On the cube `E_n`:

* `VN_eq_kop` (`W_N` is the kernel operator of `w`), `Z2b_eq_kop`, the channel decompositions
  `sgK_eq_sum_chPart`, `wNK_eq_sum_chPart`, and `cm_eq_kop` (`[Σ₂^bb, W_N]` is the kernel operator
  of `σ w - w σ`);
* **`H3ret_decomp`**: `H₃^ret = H₃^sp + H₃^mp` with `H₃^sp` the kernel operator of the
  same-channel words (`h3spK`: `[Σ₂^{bb,j}, W^j]` and `½ P[Σ_b^j, [Σ_b^j, W^j]] P`, summed over the
  channels, one-body channels included) and `H₃^mp` that of all words with at least two channels
  (`h3mpK`);
* the same-pair kernel joins only single-channel elements (`h3spK_eq_single`, `h3spK_eq_zero`),
  is Hermitian (`h3spK_conj`), and satisfies **`lem:h3`** in the improved form
  `|h₃(q, p)| ≤ B_j(n) (⌊log₂⌈|θ|⌉⌋ + 2)/|θ|` for `q ≠ p` on channel `j` with transfer `θ`
  (`norm_h3spK_le`; `B_j(n) = O(n⁻³ log n)`, review F4 H-1/H-2/H-3), and
  `|h₃(q, q)| ≤ D(n) = O(n⁻³ log n)` on the diagonal (`norm_h3spK_diag_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Preliminaries -/

section Prelim

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

omit [Fintype ν] in
lemma onCh_refl (j : Ch eta) (k : Cf eta) : OnCh j k k := by
  apply onCh_of_eq (ν := 0)
  cases j with
  | inl a => simp [tr]
  | inr pr => simp [tr]

omit [Fintype ν] in
/-- Transfers between cube configurations: `|θ|² ≤ 12 n²`. -/
lemma lsq_chT_le_cube (j : Ch eta) (q p : Cfg eta n) :
    FSLattice.lsq (chT n j q p) ≤ 12 * (n : ℝ) ^ 2 := by
  have hq : InP (n : ℝ) (cidx n q) := inP_of_mem_cube (finiteConfigLatticeIndex_mem_cube eta n q)
  have hp : InP (n : ℝ) (cidx n p) := inP_of_mem_cube (finiteConfigLatticeIndex_mem_cube eta n p)
  have hc : ∀ i, ((chT n j q p i : ℤ) : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ 2 := by
    intro i
    have h1 := hq (lead j) i
    have h2 := hp (lead j) i
    have e : ((chT n j q p i : ℤ) : ℝ) =
        ((cidx n q (lead j) i : ℤ) : ℝ) - ((cidx n p (lead j) i : ℤ) : ℝ) := by
      show (((cidx n q (lead j) - cidx n p (lead j)) i : ℤ) : ℝ) = _
      rw [Pi.sub_apply, Int.cast_sub]
    have h3 : |((chT n j q p i : ℤ) : ℝ)| ≤ 2 * n := by
      rw [e]; exact (abs_sub _ _).trans (by linarith)
    have h4 := sq_abs ((chT n j q p i : ℤ) : ℝ)
    have h5 : |((chT n j q p i : ℤ) : ℝ)| ^ 2 ≤ (2 * n) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h3 2
    nlinarith
  unfold FSLattice.lsq
  linarith [hc 0, hc 1, hc 2]

omit [Fintype ν] in
lemma rho_chT_le_cube (j : Ch eta) (q p : Cfg eta n) : FSChannel.rho (chT n j q p) ≤ 4 * n := by
  unfold FSChannel.rho
  rw [Real.sqrt_le_left (by positivity)]
  have := lsq_chT_le_cube j q p
  nlinarith

/-- **The diagonal of the commutator words**: `|h₃(q, q)| ≤ 2 C_j n⁻³ · 22000 (2J_n + 3)`. -/
theorem norm_h3cK_diag_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (q : Cfg eta n) :
    ‖h3cK sys L n j q q‖ ≤ 2 * C3c sys L n j * (22000 * (2 * Jn sys n + 3)) := by
  unfold h3cK kmul
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖∑ r, chPart n j (sgK sys L n) q r * chPart n j (wNK sys L n) r q‖ ≤
      C3c sys L n j * (22000 * (2 * Jn sys n + 3)) := by
    refine (norm_sum_le _ _).trans ?_
    obtain ⟨T, hT, hle⟩ := sum_sg_w_img (sys := sys) hL hn j q q
    refine hle.trans (mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_
      (FSLattice.h3_diag_core _ T hT)) (C3c_nonneg sys hL j))
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [chT_self, neg_zero, zero_sub, lsq_neg]
  have h2 : ‖∑ r, chPart n j (wNK sys L n) q r * chPart n j (sgK sys L n) r q‖ ≤
      C3c sys L n j * (22000 * (2 * Jn sys n + 3)) := by
    refine (norm_sum_le _ _).trans ?_
    obtain ⟨T, hT, hle⟩ := sum_w_sg_img (sys := sys) hL hn j q q
    refine hle.trans (mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_
      (FSLattice.h3_diag_core _ T hT)) (C3c_nonneg sys hL j))
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [chT_self, zero_sub, lsq_neg]
  linarith

omit [Fintype ν] in
lemma matK_kop (κ : Cfg eta n → Cfg eta n → ℂ) (q p : Cfg eta n) :
    FSKernel.matK (FSKernel.kop κ) q p = κ q p := by
  classical
  rw [FSKernel.matK_apply, FSKernel.kop_apply, Finset.sum_eq_single p]
  · rw [PiLp.ofLp_single, Pi.single_eq_same, one_mul]
  · intro r _ hr
    rw [PiLp.ofLp_single, Pi.single_eq_of_ne hr, zero_mul]
  · intro h; exact absurd (Finset.mem_univ p) h

omit [Fintype ν] in
lemma matK_add (T T' : En eta n →ₗ[ℂ] En eta n) (q p : Cfg eta n) :
    FSKernel.matK (T + T') q p = FSKernel.matK T q p + FSKernel.matK T' q p := by
  simp only [FSKernel.matK_apply, LinearMap.add_apply, PiLp.add_apply]

omit [Fintype ν] in
lemma kmul_sum_sum {ι : Type*} [Fintype ι] (κ κ' : ι → Cfg eta n → Cfg eta n → ℂ)
    (q p : Cfg eta n) :
    kmul n (fun q r => ∑ j, κ j q r) (fun r p => ∑ k, κ' k r p) q p =
      ∑ j, ∑ k, kmul n (κ j) (κ' k) q p := by
  unfold kmul
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

end Prelim

/-! ## The cube kernels -/

section CubeKernels

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel hL in
/-- **`W_N` is the kernel operator of `w`.** -/
theorem VN_eq_kop : (VN sys L n : En eta n →ₗ[ℂ] En eta n) = FSKernel.kop (wNK sys L n) := by
  classical
  ext v q
  rw [FSKernel.kop_apply]
  change (finiteCoulombPotential sys (coulombCellAmplitude L) n v).ofLp q = _
  rw [← ext_W_cubeLift sys H hKernel v, extractCLM_apply]
  change coulombFourierPotentialH2 sys (2 * Real.pi / L) H _ _ = _
  rw [potential_apply sys L H hKernel hL]
  have e : ∀ S, molecularH2Coeff (2 * Real.pi / L) (cubeLift (gF L) n v) S =
      emb eta n v S := fun S => by
    rw [← stateMap_cubeLift' (L := L) v, molecularH2StateMap_apply]; rfl
  simp_rw [e]
  rw [emb_eq_sum]
  have e2 : ∀ S, (∑ p, v.ofLp p • ev (finiteConfigLatticeIndex eta n p) : L2 eta) S *
      potKernel sys L (finiteConfigLatticeIndex eta n q) S =
      ∑ p, v.ofLp p * (if S = finiteConfigLatticeIndex eta n p then
        potKernel sys L (finiteConfigLatticeIndex eta n q) S else 0) := fun S => by
    rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ev_apply]
    split_ifs <;> ring
  simp_rw [e2]
  rw [Summable.tsum_finsetSum (fun p _ => (summable_of_ne_finset_zero (s := {cidx n p})
    (fun S hS => by
      rw [Finset.mem_singleton] at hS
      rw [if_neg hS, mul_zero])))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [tsum_mul_left, tsum_ite_eq]
  rfl

lemma Z2b_eq_kop : (Z2b sys L n : En eta n →ₗ[ℂ] En eta n) = FSKernel.kop (sgK sys L n) := rfl

variable {sys} in
lemma sgK_eq_sum_chPart (q p : Cfg eta n) :
    sgK sys L n q p = ∑ j, chPart n j (sgK sys L n) q p := by
  classical
  by_cases h0 : sgK sys L n q p = 0
  · rw [h0]; symm
    exact Finset.sum_eq_zero fun j _ => by unfold chPart; split_ifs <;> simp [h0]
  obtain ⟨hg, -, -⟩ := sgK_ne_zero h0
  obtain ⟨hne, j, hj, -⟩ := hg
  have hne' : cidx n q ≠ cidx n p := fun h => hne (finiteConfigLatticeIndex_injective eta n h)
  rw [Finset.sum_eq_single j (fun j' _ hj' => by
      unfold chPart; rw [if_neg]; intro h; exact hj' (onCh_unique h hj hne'))
    (fun h => absurd (Finset.mem_univ j) h)]
  unfold chPart; rw [if_pos hj]

variable {sys} in
include hL in
lemma wNK_eq_sum_chPart (q p : Cfg eta n) :
    wNK sys L n q p = ∑ j, chPart n j (wNK sys L n) q p := by
  have := potKernel_eq_sum_lcp (sys := sys) hL (cidx n q) (cidx n p)
  exact this

include hKernel hL in
/-- **`[Σ₂^bb, W_N]` is the kernel operator of `σ w - w σ`.** -/
theorem cm_eq_kop : (FSConj.cm (Z2b sys L n) (VN sys L n) : En eta n →ₗ[ℂ] En eta n) =
    FSKernel.kop (kmul n (sgK sys L n) (wNK sys L n) - kmul n (wNK sys L n) (sgK sys L n)) := by
  unfold FSConj.cm
  rw [FSKernel.kop_sub, ← kop_kmul, ← kop_kmul, ← Z2b_eq_kop, ← VN_eq_kop sys hL H hKernel]
  rfl

end CubeKernels

/-! ## The decomposition `H₃^ret = H₃^sp + H₃^mp` -/

section Decomp

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

/-- **The same-pair (same-channel) kernel of `H₃^ret`**: the words of `[Σ₂^bb, W_N]` and of
`P H^{(3)} P` whose hops all lie on one channel, summed over the channels. -/
noncomputable def h3spK (q p : Cfg eta n) : ℂ :=
  ∑ j, (h3cK sys L n j q p + h3fW sys L n j j j (cidx n q) (cidx n p))

open Classical in
/-- The multi-channel words of `H₃^ret` (at least two different channels). -/
noncomputable def h3mpK (q p : Cfg eta n) : ℂ :=
  (∑ j, ∑ k, if j = k then 0 else
    (kmul n (chPart n j (sgK sys L n)) (chPart n k (wNK sys L n)) q p -
      kmul n (chPart n j (wNK sys L n)) (chPart n k (sgK sys L n)) q p)) +
  ∑ j, ∑ k, ∑ l, if j = k ∧ k = l then 0 else h3fW sys L n j k l (cidx n q) (cidx n p)

/-- `H₃^sp`, the same-pair component of `H₃^ret`. -/
noncomputable def H3sp : En eta n →ₗ[ℂ] En eta n := FSKernel.kop (h3spK sys L n)

/-- `H₃^mp`, the multi-channel component of `H₃^ret`. -/
noncomputable def H3mp : En eta n →ₗ[ℂ] En eta n := FSKernel.kop (h3mpK sys L n)

omit [Fintype ν] in
lemma sum_sum_split {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ι → ℂ) :
    ∑ j, ∑ k, f j k = ∑ j, f j j + ∑ j, ∑ k, (if j = k then 0 else f j k) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ k, f j k = (if j = k then f j k else 0) + (if j = k then 0 else f j k) := fun k => by
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ j)]

omit [Fintype ν] in
lemma sum_sum_sum_split {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ι → ι → ℂ) :
    ∑ j, ∑ k, ∑ l, g j k l =
      ∑ j, g j j j + ∑ j, ∑ k, ∑ l, (if j = k ∧ k = l then 0 else g j k l) := by
  have e : ∀ j k l, g j k l = (if j = k ∧ k = l then g j k l else 0) +
      (if j = k ∧ k = l then 0 else g j k l) := fun j k l => by split_ifs <;> simp
  have h1 : ∀ j, ∑ k, ∑ l, (if j = k ∧ k = l then g j k l else 0) = g j j j := fun j => by
    have e2 : ∀ k, ∑ l, (if j = k ∧ k = l then g j k l else 0) =
        if j = k then g j k k else 0 := fun k => by
      by_cases hjk : j = k
      · simp only [hjk, true_and, if_true]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ k)]
      · simp [hjk]
    rw [Finset.sum_congr rfl fun k _ => e2 k, Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]
  calc ∑ j, ∑ k, ∑ l, g j k l
      = ∑ j, ∑ k, ∑ l, ((if j = k ∧ k = l then g j k l else 0) +
          (if j = k ∧ k = l then 0 else g j k l)) := by
        simp only [← e]
    _ = _ := by
        simp only [Finset.sum_add_distrib, h1]

variable {sys L n}

include sys in
theorem H3ret_decomp (hL : 0 < L) (hn : 2 ≤ n)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    (H3ret sys hL hn H : En eta n →ₗ[ℂ] En eta n) = H3sp sys L n + H3mp sys L n := by
  classical
  rw [H3sp, H3mp, ← FSKernel.kop_add, ← FSKernel.kop_matK (H3ret sys hL hn H : En eta n →ₗ[ℂ] En eta n)]
  congr 1
  funext q p
  rw [Pi.add_apply, Pi.add_apply]
  have e1 : FSKernel.matK (H3ret sys hL hn H : En eta n →ₗ[ℂ] En eta n) q p =
      (kmul n (sgK sys L n) (wNK sys L n) q p - kmul n (wNK sys L n) (sgK sys L n) q p) +
        h3fL sys L n (cidx n q) (cidx n p) := by
    unfold H3ret
    rw [ContinuousLinearMap.toLinearMap_add, matK_add, cm_eq_kop sys hL H hKernel, matK_kop,
      H3first_matK sys hL hn H hKernel]
    rfl
  rw [e1]
  have e2 : kmul n (sgK sys L n) (wNK sys L n) q p =
      ∑ j, ∑ k, kmul n (chPart n j (sgK sys L n)) (chPart n k (wNK sys L n)) q p := by
    rw [← kmul_sum_sum]
    unfold kmul
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [sgK_eq_sum_chPart q r, wNK_eq_sum_chPart hL r p]
  have e3 : kmul n (wNK sys L n) (sgK sys L n) q p =
      ∑ j, ∑ k, kmul n (chPart n j (wNK sys L n)) (chPart n k (sgK sys L n)) q p := by
    rw [← kmul_sum_sum]
    unfold kmul
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [wNK_eq_sum_chPart hL q r, sgK_eq_sum_chPart r p]
  rw [e2, e3, h3fL_eq_sum hL hn, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [sum_sum_split (fun j k => kmul n (chPart n j (sgK sys L n)) (chPart n k (wNK sys L n)) q p -
      kmul n (chPart n j (wNK sys L n)) (chPart n k (sgK sys L n)) q p),
    sum_sum_sum_split (fun j k l => h3fW sys L n j k l (cidx n q) (cidx n p))]
  unfold h3spK h3mpK h3cK
  rw [Finset.sum_add_distrib]
  ring

end Decomp

/-! ## `lem:h3` for the same-pair component -/

section Bounds

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

/-- On a single-channel element only the words of that channel survive. -/
lemma h3spK_eq_single {j : Ch eta} {q p : Cfg eta n} (hj : OnCh j (cidx n q) (cidx n p))
    (hqp : q ≠ p) :
    h3spK sys L n q p = h3cK sys L n j q p + h3fW sys L n j j j (cidx n q) (cidx n p) := by
  have hne : cidx n q ≠ cidx n p := fun h => hqp (finiteConfigLatticeIndex_injective eta n h)
  unfold h3spK
  rw [Finset.sum_eq_single j (fun j' _ hj' => by
      have hn' : ¬ OnCh j' (cidx n q) (cidx n p) := fun h => hj' (onCh_unique h hj hne)
      rw [h3cK_eq_zero j' hn', h3fW_diag_eq_zero j' hn', add_zero])
    (fun h => absurd (Finset.mem_univ j) h)]

/-- Off the single-channel elements the same-pair kernel vanishes. -/
lemma h3spK_eq_zero {q p : Cfg eta n} (h : ∀ j : Ch eta, ¬ OnCh j (cidx n q) (cidx n p)) :
    h3spK sys L n q p = 0 := by
  unfold h3spK
  exact Finset.sum_eq_zero fun j _ => by rw [h3cK_eq_zero j (h j), h3fW_diag_eq_zero j (h j),
    add_zero]

lemma sgK_conj (hL : 0 < L) (q p : Cfg eta n) : conj (sgK sys L n q p) = -sgK sys L n p q := by
  unfold sgK
  rw [sig2bbK_skew hL q p, neg_neg]

lemma chPart_sgK_conj (hL : 0 < L) (j : Ch eta) (q p : Cfg eta n) :
    conj (chPart n j (sgK sys L n) q p) = -chPart n j (sgK sys L n) p q := by
  classical
  unfold chPart
  by_cases h : OnCh j (cidx n q) (cidx n p)
  · rw [if_pos h, if_pos (onCh_symm h), sgK_conj hL]
  · rw [if_neg h, if_neg (fun h' => h (onCh_symm h')), map_zero, neg_zero]

lemma chPart_wNK_conj (hL : 0 < L) (j : Ch eta) (q p : Cfg eta n) :
    conj (chPart n j (wNK sys L n) q p) = chPart n j (wNK sys L n) p q := by
  classical
  unfold chPart wNK
  by_cases h : OnCh j (cidx n q) (cidx n p)
  · rw [if_pos h, if_pos (onCh_symm h), ← potKernel_conj' hL]
  · rw [if_neg h, if_neg (fun h' => h (onCh_symm h')), map_zero]

lemma h3cK_conj (hL : 0 < L) (j : Ch eta) (q p : Cfg eta n) :
    conj (h3cK sys L n j q p) = h3cK sys L n j p q := by
  unfold h3cK kmul
  rw [map_sub, map_sum, map_sum]
  simp_rw [map_mul, chPart_sgK_conj hL, chPart_wNK_conj hL]
  simp only [neg_mul, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  rw [neg_add_eq_sub]
  congr 1
  · exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  · exact Finset.sum_congr rfl fun r _ => mul_comm _ _

/-- **The same-pair kernel is Hermitian.** -/
theorem h3spK_conj (hL : 0 < L) (q p : Cfg eta n) :
    h3spK sys L n p q = conj (h3spK sys L n q p) := by
  unfold h3spK
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, h3cK_conj hL, h3fW_diag_conj hL]

theorem H3sp_symm (hL : 0 < L) : (H3sp sys L n).IsSymmetric :=
  FSKernel.kop_symm _ fun q p => h3spK_conj hL q p

variable (sys L n) in
/-- The constant of `lem:h3` for channel `j`: `B_j = 2 C_j C_h3 (J_n + 2) + 4 n A_j chb_j n⁻³`,
`O(n⁻³ log n)`. -/
noncomputable def Bh3 (j : Ch eta) : ℝ :=
  2 * C3c sys L n j * (FSLattice.Ch3 * (Jn sys n + 2)) +
    4 * n * Asj sys L n j * (chb sys L j / (n : ℝ) ^ 3)

lemma Bh3_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ Bh3 sys L n j := by
  unfold Bh3
  have := C3c_nonneg sys (n := n) hL j
  have := Asj_nonneg (sys := sys) (n := n) hL j
  have := chb_nonneg (sys := sys) hL j
  have : (0 : ℝ) ≤ FSLattice.Ch3 := by unfold FSLattice.Ch3; norm_num
  positivity

/-- **`lem:h3`** (same-pair component, improved): for `q ≠ p` joined by channel `j` with transfer
`θ`, `|h₃(q, p)| ≤ B_j(n) (⌊log₂⌈|θ|⌉⌋ + 2)/|θ|` with `B_j(n) = O(n⁻³ log n)`. -/
theorem norm_h3spK_le (hL : 0 < L) (hn : 2 ≤ n) {j : Ch eta} {q p : Cfg eta n}
    (hj : OnCh j (cidx n q) (cidx n p)) (hqp : q ≠ p) :
    ‖h3spK sys L n q p‖ ≤ Bh3 sys L n j *
      ((Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ + 2) / FSChannel.rho (chT n j q p)) := by
  rw [h3spK_eq_single hj hqp]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_h3cK_le (sys := sys) hL hn j hj hqp
  have h2 := norm_h3fW_le (sys := sys) hL hn j (cidx n q) (cidx n p)
  set ρ := FSChannel.rho (chT n j q p)
  set X := ((Nat.log 2 ⌈ρ⌉₊ : ℕ) + 2 : ℝ) / ρ
  have hρ1 : 1 ≤ ρ := FSLattice.one_le_rho (one_le_lsq_chT hj hqp)
  have hρn : ρ ≤ 4 * n := rho_chT_le_cube j q p
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hX : 1 / (2 * (n : ℝ)) ≤ X := by
    have h2X : 2 / ρ ≤ X := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      have : (0 : ℝ) ≤ (Nat.log 2 ⌈ρ⌉₊ : ℕ) := Nat.cast_nonneg _
      linarith
    refine le_trans ?_ h2X
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    linarith
  have hA0 := Asj_nonneg (sys := sys) (n := n) hL j
  have hb0 : 0 ≤ chb sys L j / (n : ℝ) ^ 3 := by have := chb_nonneg (sys := sys) hL j; positivity
  have h2' : 2 * Asj sys L n j * (chb sys L j / (n : ℝ) ^ 3) ≤
      4 * n * Asj sys L n j * (chb sys L j / (n : ℝ) ^ 3) * X := by
    have e : 2 * Asj sys L n j * (chb sys L j / (n : ℝ) ^ 3) =
        4 * n * Asj sys L n j * (chb sys L j / (n : ℝ) ^ 3) * (1 / (2 * (n : ℝ))) := by
      field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hX (by positivity)
  have h1' : ‖h3cK sys L n j q p‖ ≤ 2 * C3c sys L n j * (FSLattice.Ch3 * (Jn sys n + 2)) * X := by
    refine h1.trans (le_of_eq ?_)
    simp only [X]
    ring
  calc ‖h3cK sys L n j q p‖ + ‖h3fW sys L n j j j (cidx n q) (cidx n p)‖
      ≤ 2 * C3c sys L n j * (FSLattice.Ch3 * (Jn sys n + 2)) * X +
          4 * n * Asj sys L n j * (chb sys L j / (n : ℝ) ^ 3) * X := add_le_add h1' (h2.trans h2')
    _ = Bh3 sys L n j * X := by unfold Bh3; ring

variable (sys L n) in
/-- The diagonal constant of `lem:h3`: `D = Σ_j (2 C_j · 22000 (2J_n + 3) + 2 A_j chb_j n⁻³)`. -/
noncomputable def Dh3 : ℝ :=
  ∑ j : Ch eta, (2 * C3c sys L n j * (22000 * (2 * Jn sys n + 3)) +
    2 * Asj sys L n j * (chb sys L j / (n : ℝ) ^ 3))

/-- **The diagonal of the same-pair kernel**: `|h₃(q, q)| ≤ D(n) = O(n⁻³ log n)`. -/
theorem norm_h3spK_diag_le (hL : 0 < L) (hn : 2 ≤ n) (q : Cfg eta n) :
    ‖h3spK sys L n q q‖ ≤ Dh3 sys L n := by
  unfold h3spK Dh3
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact (norm_add_le _ _).trans (add_le_add (norm_h3cK_diag_le hL hn j q)
    (norm_h3fW_le hL hn j _ _))

end Bounds

end FSNormal
