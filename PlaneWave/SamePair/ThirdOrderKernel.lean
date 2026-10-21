import PlaneWave.SamePair.LatticeSums

/-!
# Same-pair third order, part 4: the kernel of `P H^{(3)} P` and its channel words

On the lattice `ℤ^{3η}`:

* `zK`, the kernel of `Z = W Σ_D + (W Σ_D)† = -[Σ_b, W]` (`Zsym_ev`, `Zsym_apply`), and
  `h3fL = -½ (σ z - z σ)`; **`H3first_matK`**: the matrix of `P H^{(3)} P = -½ P [Σ_b, Z] P`
  between cube configurations is `h3fL`;
* the channel parts `lcp j κ` of a lattice kernel, with `sigK_eq_sum_lcp`,
  `potKernel_eq_sum_lcp` (each element of `σ` and `w` lies on one channel);
* the channel words `zJ k l` (two hops) and `h3fW j k l` (three hops, output to input), with
  `zK_eq_sum` and **`h3fL_eq_sum`**: the kernel of `P H^{(3)} P` is the sum of its words;
* the same-channel words `h3fW j j j`: supported on channel-`j` elements (`h3fW_diag_eq_zero`),
  Hermitian (`h3fW_diag_conj`), and **`norm_h3fW_le`**: `|h3fW j j j| ≤ 2 A_j chb_j n⁻³`
  with `A_j = (c_j/c_gap) 416/(3n)`, i.e. `O(n⁻⁴)`: the closed and open excursions of `lem:h3`,
  by eq:flatbd (`tsum_sigMaj_chMaj_le`, `tsum_chMaj_sigMaj_le`) and the Schur rows of `Σ_b`
  (review F4, H-3).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Lattice kernels and channel words -/

section Defs

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

open Classical in
/-- The channel-`j` part of a lattice kernel. -/
noncomputable def lcp (j : Ch eta) (κ : Cf eta → Cf eta → ℂ) (k k' : Cf eta) : ℂ :=
  if OnCh j k k' then κ k k' else 0

/-- The kernel of `Z = -[Σ_b, W]`: `z(R, P) = Σ_S w(R,S) σ(S,P) - Σ_S σ(R,S) w(S,P)`. -/
noncomputable def zK (R P : Cf eta) : ℂ :=
  (∑' S, potKernel sys L R S * sigK sys L n S P) - ∑' S, sigK sys L n R S * potKernel sys L S P

/-- The kernel of `P H^{(3)} P = -½ P [Σ_b, Z] P` on the lattice. -/
noncomputable def h3fL (Q P : Cf eta) : ℂ :=
  -(1 / 2 : ℂ) * ((∑' R, sigK sys L n Q R * zK sys L n R P) -
    ∑' R, zK sys L n Q R * sigK sys L n R P)

/-- The channel words of `z`: the hop on channel `k` after the hop on channel `l`. -/
noncomputable def zJ (k l : Ch eta) (R P : Cf eta) : ℂ :=
  (∑' S, lcp k (potKernel sys L) R S * lcp l (sigK sys L n) S P) -
    ∑' S, lcp k (sigK sys L n) R S * lcp l (potKernel sys L) S P

/-- The channel words of `P H^{(3)} P`: hops on channels `j`, `k`, `l` (output to input). -/
noncomputable def h3fW (j k l : Ch eta) (Q P : Cf eta) : ℂ :=
  -(1 / 2 : ℂ) * ((∑' R, lcp j (sigK sys L n) Q R * zJ sys L n k l R P) -
    ∑' R, zJ sys L n j k Q R * lcp l (sigK sys L n) R P)

/-- The Schur row constant of the channel-`j` part of `Σ_b`, `A_j = (c_j/c_gap) 416/(3n)`. -/
noncomputable def Asj (j : Ch eta) : ℝ := chC sys L j / cgap sys (gF L) * (416 / (3 * n))

end Defs

/-! ## Channel parts -/

section ChannelParts

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

lemma lcp_eq_zero {j : Ch eta} {κ : Cf eta → Cf eta → ℂ} {k k' : Cf eta} (h : ¬ OnCh j k k') :
    lcp j κ k k' = 0 := by
  unfold lcp; rw [if_neg h]

lemma lcp_of_onCh {j : Ch eta} {κ : Cf eta → Cf eta → ℂ} {k k' : Cf eta} (h : OnCh j k k') :
    lcp j κ k k' = κ k k' := by
  unfold lcp; rw [if_pos h]

lemma Asj_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ Asj sys L n j := by
  unfold Asj
  have := cgap_pos sys (gF_pos hL).ne'
  have := chC_nonneg sys hL j
  positivity

/-- The potential kernel vanishes on the diagonal. -/
lemma potKernel_self (hL : 0 < L) (k : Cf eta) : potKernel sys L k k = 0 := by
  classical
  have h := norm_potKernel_le sys hL k k
  have h0 : potMaj sys L k k = 0 := by
    unfold potMaj
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold chMaj
    split_ifs
    · rw [sub_self]; simp [latticeNormSq]
    · rfl
  rw [h0] at h
  exact norm_le_zero_iff.mp h

/-- `σ` vanishes on the diagonal (a crossing joins `Q` to the outside of `P`). -/
lemma sigK_self (k : Cf eta) : sigK sys L n k k = 0 := by
  apply sigK_eq_zero_of_not_cross
  rintro (⟨hq, hp⟩ | ⟨hp, hq⟩)
  · exact hp (hq.inP (Nat.cast_nonneg n))
  · exact hp (hq.inP (Nat.cast_nonneg n))

lemma sigK_eq_sum_lcp (hL : 0 < L) (k k' : Cf eta) :
    sigK sys L n k k' = ∑ j, lcp j (sigK sys L n) k k' := by
  classical
  by_cases h0 : sigK sys L n k k' = 0
  · rw [h0]; symm
    exact Finset.sum_eq_zero fun j _ => by unfold lcp; split_ifs <;> simp [h0]
  have hne : k ≠ k' := by rintro rfl; exact h0 (sigK_self k)
  have hw : potKernel sys L k k' ≠ 0 := by
    intro hw; apply h0; unfold sigK; split_ifs <;> simp [hw]
  obtain ⟨j, hj⟩ := exists_onCh_of_ne_zero hL hw
  rw [Finset.sum_eq_single j (fun j' _ hj' => lcp_eq_zero fun h => hj' (onCh_unique h hj hne))
    (fun h => absurd (Finset.mem_univ j) h), lcp_of_onCh hj]

lemma potKernel_eq_sum_lcp (hL : 0 < L) (k k' : Cf eta) :
    potKernel sys L k k' = ∑ j, lcp j (potKernel sys L) k k' := by
  classical
  by_cases h0 : potKernel sys L k k' = 0
  · rw [h0]; symm
    exact Finset.sum_eq_zero fun j _ => by unfold lcp; split_ifs <;> simp [h0]
  have hne : k ≠ k' := by rintro rfl; exact h0 (potKernel_self hL k)
  obtain ⟨j, hj⟩ := exists_onCh_of_ne_zero hL h0
  rw [Finset.sum_eq_single j (fun j' _ hj' => lcp_eq_zero fun h => hj' (onCh_unique h hj hne))
    (fun h => absurd (Finset.mem_univ j) h), lcp_of_onCh hj]

lemma norm_lcp_sig_le (hL : 0 < L) (hn : 0 < n) (j : Ch eta) (k k' : Cf eta) :
    ‖lcp j (sigK sys L n) k k'‖ ≤ sigMaj sys L n j k k' := by
  classical
  by_cases hj : OnCh j k k'
  · rw [lcp_of_onCh hj]
    by_cases hne : k = k'
    · subst hne; rw [sigK_self, norm_zero]; exact sigMaj_nonneg hL j k k
    refine (norm_sigK_le hL hn k k').trans (le_of_eq ?_)
    exact Finset.sum_eq_single j (fun j' _ hj' => by
        unfold sigMaj; rw [if_neg]; intro h; exact hj' (onCh_unique h hj hne))
      (fun h => absurd (Finset.mem_univ j) h)
  · rw [lcp_eq_zero hj, norm_zero]; exact sigMaj_nonneg hL j k k'

lemma norm_lcp_pot_le (hL : 0 < L) (j : Ch eta) (k k' : Cf eta) :
    ‖lcp j (potKernel sys L) k k'‖ ≤ chMaj j (chC sys L j) k k' := by
  classical
  by_cases hj : OnCh j k k'
  · rw [lcp_of_onCh hj]
    by_cases hne : k = k'
    · subst hne; rw [potKernel_self hL, norm_zero]; exact chMaj_nonneg j (chC_nonneg sys hL j) k k
    refine (norm_potKernel_le sys hL k k').trans (le_of_eq ?_)
    unfold potMaj
    exact Finset.sum_eq_single j (fun j' _ hj' => by
        unfold chMaj; rw [if_neg]; intro h; exact hj' (onCh_unique h hj hne))
      (fun h => absurd (Finset.mem_univ j) h)
  · rw [lcp_eq_zero hj, norm_zero]; exact chMaj_nonneg j (chC_nonneg sys hL j) k k'

lemma lcp_sig_conj (hL : 0 < L) (j : Ch eta) (k k' : Cf eta) :
    conj (lcp j (sigK sys L n) k k') = -lcp j (sigK sys L n) k' k := by
  by_cases h : OnCh j k k'
  · rw [lcp_of_onCh h, lcp_of_onCh (onCh_symm h), sigK_anti hL]
  · rw [lcp_eq_zero h, lcp_eq_zero (fun h' => h (onCh_symm h')), map_zero, neg_zero]

lemma lcp_pot_conj (hL : 0 < L) (j : Ch eta) (k k' : Cf eta) :
    conj (lcp j (potKernel sys L) k k') = lcp j (potKernel sys L) k' k := by
  by_cases h : OnCh j k k'
  · rw [lcp_of_onCh h, lcp_of_onCh (onCh_symm h), ← potKernel_conj' hL]
  · rw [lcp_eq_zero h, lcp_eq_zero (fun h' => h (onCh_symm h')), map_zero]

end ChannelParts

/-! ## The kernel of `P H^{(3)} P` -/

section Kernel

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

omit [Fintype ν] in
/-- The entries of an adjoint on basis vectors. -/
lemma adj_ev_apply (A : L2 eta →L[ℂ] L2 eta) (P R : Cf eta) :
    ContinuousLinearMap.adjoint A (ev P) R = conj (A (ev R) P) := by
  rw [← inner_ev_left R, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_ev_left]

include hKernel in
/-- `(W Σ_b e_P)(R) = Σ_S σ(S, P) w(R, S)`. -/
lemma Zw_ev (P R : Cf eta) :
    Zw sys hL hn H (ev P) R = ∑' S, sigK sys L n S P * potKernel sys L R S := by
  rw [Zw, ContinuousLinearMap.comp_apply]
  change coulombFourierPotentialH2 sys (2 * Real.pi / L) H _ R = _
  rw [potential_apply sys L H hKernel hL]
  refine tsum_congr fun S => ?_
  congr 1
  rw [← molecularH2StateMap_apply]
  change molecularH2StateMap eta (gF L) (SigD sys L n hL (by omega) (ev P)) S = _
  rw [stateMap_SigD hL hn, Sig_ev hL hn]

include hL in
lemma zK_conj (R P : Cf eta) : conj (zK sys L n R P) = zK sys L n P R := by
  unfold zK
  rw [map_sub, Complex.conj_tsum, Complex.conj_tsum]
  have h1 : ∀ S, conj (potKernel sys L R S * sigK sys L n S P) =
      -(sigK sys L n P S * potKernel sys L S R) := fun S => by
    rw [map_mul, ← potKernel_conj' hL, sigK_anti hL]; ring
  have h2 : ∀ S, conj (sigK sys L n R S * potKernel sys L S P) =
      -(potKernel sys L P S * sigK sys L n S R) := fun S => by
    rw [map_mul, sigK_anti hL, ← potKernel_conj' hL]; ring
  simp_rw [h1, h2, tsum_neg]
  ring

include hKernel in
/-- **The columns of `Z`**: `(Z e_P)(R) = z(R, P)`. -/
lemma Zsym_ev (P R : Cf eta) : Zsym sys hL hn H (ev P) R = zK sys L n R P := by
  unfold Zsym zK
  rw [add_apply, lp.coeFn_add, Pi.add_apply, Zw_ev sys hL hn H hKernel,
    adj_ev_apply, Zw_ev sys hL hn H hKernel, Complex.conj_tsum, sub_eq_add_neg, ← tsum_neg]
  congr 1
  · exact tsum_congr fun S => mul_comm _ _
  · refine tsum_congr fun S => ?_
    rw [map_mul, sigK_anti hL, ← potKernel_conj' hL]
    ring

lemma adjoint_Zsym : ContinuousLinearMap.adjoint (Zsym sys hL hn H) = Zsym sys hL hn H := by
  unfold Zsym
  rw [map_add, ContinuousLinearMap.adjoint_adjoint, add_comm]

include hKernel in
/-- **The rows of `Z`**: `(Z y)(Q) = Σ_R z(Q, R) y(R)`. -/
lemma Zsym_apply (y : L2 eta) (Q : Cf eta) :
    Zsym sys hL hn H y Q = ∑' R, zK sys L n Q R * y R := by
  have e : Zsym sys hL hn H y Q = ⟪Zsym sys hL hn H (ev Q), y⟫_ℂ := by
    rw [← inner_ev_left Q (Zsym sys hL hn H y), ← ContinuousLinearMap.adjoint_inner_left,
      adjoint_Zsym]
  rw [e, lp.inner_eq_tsum]
  refine tsum_congr fun R => ?_
  rw [Zsym_ev sys hL hn H hKernel, RCLike.inner_apply, zK_conj sys hL, mul_comm]

include hKernel in
/-- **The matrix of `P H^{(3)} P`** between cube configurations is `h3fL`. -/
theorem H3first_matK (q p : Cfg eta n) :
    FSKernel.matK (H3first sys hL hn H : En eta n →ₗ[ℂ] En eta n) q p =
      h3fL sys L n (cidx n q) (cidx n p) := by
  rw [FSKernel.matK_apply]
  have e : ((H3first sys hL hn H : En eta n →ₗ[ℂ] En eta n) (EuclideanSpace.single p 1)).ofLp q =
      -(1 / 2 : ℂ) * (FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H)
        (emb eta n (EuclideanSpace.single p 1)) (cidx n q)) := rfl
  rw [e, emb_single]
  unfold FSConj.cm h3fL
  rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
    lp.coeFn_sub, Pi.sub_apply, Sig_apply, Zsym_apply sys hL hn H hKernel]
  congr 2
  · exact tsum_congr fun R => by rw [Zsym_ev sys hL hn H hKernel]
  · exact tsum_congr fun R => by rw [Sig_ev hL hn]

end Kernel

/-! ## The decomposition into channel words -/

section Words

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

lemma summable_lcp_pot_sig (hL : 0 < L) (hn : 2 ≤ n) (k l : Ch eta) (R P : Cf eta) :
    Summable fun S => lcp k (potKernel sys L) R S * lcp l (sigK sys L n) S P := by
  refine Summable.of_norm_bounded ((summable_sigMaj_col (sys := sys) (L := L) hn l P).mul_left
    (chC sys L k)) fun S => ?_
  rw [norm_mul]
  exact mul_le_mul ((norm_lcp_pot_le hL k R S).trans (chMaj_le k (chC_nonneg sys hL k) R S))
    (norm_lcp_sig_le hL (by omega) l S P) (norm_nonneg _) (chC_nonneg sys hL k)

lemma summable_lcp_sig_pot (hL : 0 < L) (hn : 2 ≤ n) (k l : Ch eta) (R P : Cf eta) :
    Summable fun S => lcp k (sigK sys L n) R S * lcp l (potKernel sys L) S P := by
  refine Summable.of_norm_bounded ((summable_sigMaj_row (sys := sys) (L := L) hn k R).mul_right
    (chC sys L l)) fun S => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_lcp_sig_le hL (by omega) k R S)
    ((norm_lcp_pot_le hL l S P).trans (chMaj_le l (chC_nonneg sys hL l) S P)) (norm_nonneg _)
    (sigMaj_nonneg hL k R S)

/-- The two-hop words are uniformly bounded. -/
lemma norm_zJ_le_crude (hL : 0 < L) (hn : 2 ≤ n) (k l : Ch eta) (R P : Cf eta) :
    ‖zJ sys L n k l R P‖ ≤ chC sys L k * Asj sys L n l + Asj sys L n k * chC sys L l := by
  unfold zJ
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_tsum_le_tsum_norm (summable_lcp_pot_sig hL hn k l R P).norm).trans ?_
    calc ∑' S, ‖lcp k (potKernel sys L) R S * lcp l (sigK sys L n) S P‖
        ≤ ∑' S, chC sys L k * sigMaj sys L n l S P :=
          (summable_lcp_pot_sig hL hn k l R P).norm.tsum_le_tsum (fun S => by
            rw [norm_mul]
            exact mul_le_mul ((norm_lcp_pot_le hL k R S).trans
              (chMaj_le k (chC_nonneg sys hL k) R S)) (norm_lcp_sig_le hL (by omega) l S P)
              (norm_nonneg _) (chC_nonneg sys hL k))
            ((summable_sigMaj_col (sys := sys) (L := L) hn l P).mul_left _)
      _ = chC sys L k * ∑' S, sigMaj sys L n l S P := tsum_mul_left
      _ ≤ chC sys L k * Asj sys L n l :=
          mul_le_mul_of_nonneg_left (tsum_sigMaj_col hL hn l P) (chC_nonneg sys hL k)
  · refine (norm_tsum_le_tsum_norm (summable_lcp_sig_pot hL hn k l R P).norm).trans ?_
    calc ∑' S, ‖lcp k (sigK sys L n) R S * lcp l (potKernel sys L) S P‖
        ≤ ∑' S, sigMaj sys L n k R S * chC sys L l :=
          (summable_lcp_sig_pot hL hn k l R P).norm.tsum_le_tsum (fun S => by
            rw [norm_mul]
            exact mul_le_mul (norm_lcp_sig_le hL (by omega) k R S)
              ((norm_lcp_pot_le hL l S P).trans (chMaj_le l (chC_nonneg sys hL l) S P))
              (norm_nonneg _) (sigMaj_nonneg hL k R S))
            ((summable_sigMaj_row (sys := sys) (L := L) hn k R).mul_right _)
      _ = (∑' S, sigMaj sys L n k R S) * chC sys L l := tsum_mul_right
      _ ≤ Asj sys L n k * chC sys L l :=
          mul_le_mul_of_nonneg_right (tsum_sigMaj_row hL hn k R) (chC_nonneg sys hL l)

lemma summable_lcp_sig_zJ (hL : 0 < L) (hn : 2 ≤ n) (j k l : Ch eta) (Q P : Cf eta) :
    Summable fun R => lcp j (sigK sys L n) Q R * zJ sys L n k l R P := by
  refine Summable.of_norm_bounded ((summable_sigMaj_row (sys := sys) (L := L) hn j Q).mul_right
    (chC sys L k * Asj sys L n l + Asj sys L n k * chC sys L l)) fun R => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_lcp_sig_le hL (by omega) j Q R) (norm_zJ_le_crude hL hn k l R P)
    (norm_nonneg _) (sigMaj_nonneg hL j Q R)

lemma summable_zJ_lcp_sig (hL : 0 < L) (hn : 2 ≤ n) (j k l : Ch eta) (Q P : Cf eta) :
    Summable fun R => zJ sys L n j k Q R * lcp l (sigK sys L n) R P := by
  refine Summable.of_norm_bounded ((summable_sigMaj_col (sys := sys) (L := L) hn l P).mul_left
    (chC sys L j * Asj sys L n k + Asj sys L n j * chC sys L k)) fun R => ?_
  rw [norm_mul]
  exact mul_le_mul (norm_zJ_le_crude hL hn j k Q R) (norm_lcp_sig_le hL (by omega) l R P)
    (norm_nonneg _) (by
      have := Asj_nonneg (sys := sys) (n := n) hL j
      have := Asj_nonneg (sys := sys) (n := n) hL k
      have := chC_nonneg sys hL j
      have := chC_nonneg sys hL k
      positivity)

/-- `z` is the sum of its two-hop channel words. -/
theorem zK_eq_sum (hL : 0 < L) (hn : 2 ≤ n) (R P : Cf eta) :
    zK sys L n R P = ∑ k, ∑ l, zJ sys L n k l R P := by
  unfold zK zJ
  have h1 : ∑' S, potKernel sys L R S * sigK sys L n S P =
      ∑ k, ∑ l, ∑' S, lcp k (potKernel sys L) R S * lcp l (sigK sys L n) S P := by
    have e : ∀ S, potKernel sys L R S * sigK sys L n S P =
        ∑ k, ∑ l, lcp k (potKernel sys L) R S * lcp l (sigK sys L n) S P := fun S => by
      rw [potKernel_eq_sum_lcp hL R S, sigK_eq_sum_lcp hL S P, Finset.sum_mul_sum]
    rw [tsum_congr e, Summable.tsum_finsetSum (fun k _ => summable_sum fun l _ =>
      summable_lcp_pot_sig hL hn k l R P)]
    exact Finset.sum_congr rfl fun k _ => Summable.tsum_finsetSum fun l _ =>
      summable_lcp_pot_sig hL hn k l R P
  have h2 : ∑' S, sigK sys L n R S * potKernel sys L S P =
      ∑ k, ∑ l, ∑' S, lcp k (sigK sys L n) R S * lcp l (potKernel sys L) S P := by
    have e : ∀ S, sigK sys L n R S * potKernel sys L S P =
        ∑ k, ∑ l, lcp k (sigK sys L n) R S * lcp l (potKernel sys L) S P := fun S => by
      rw [sigK_eq_sum_lcp hL R S, potKernel_eq_sum_lcp hL S P, Finset.sum_mul_sum]
    rw [tsum_congr e, Summable.tsum_finsetSum (fun k _ => summable_sum fun l _ =>
      summable_lcp_sig_pot hL hn k l R P)]
    exact Finset.sum_congr rfl fun k _ => Summable.tsum_finsetSum fun l _ =>
      summable_lcp_sig_pot hL hn k l R P
  rw [h1, h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [← Finset.sum_sub_distrib]

/-- **The kernel of `P H^{(3)} P` is the sum of its three-hop channel words.** -/
theorem h3fL_eq_sum (hL : 0 < L) (hn : 2 ≤ n) (Q P : Cf eta) :
    h3fL sys L n Q P = ∑ j, ∑ k, ∑ l, h3fW sys L n j k l Q P := by
  unfold h3fL h3fW
  have h1 : ∑' R, sigK sys L n Q R * zK sys L n R P =
      ∑ j, ∑ k, ∑ l, ∑' R, lcp j (sigK sys L n) Q R * zJ sys L n k l R P := by
    have e : ∀ R, sigK sys L n Q R * zK sys L n R P =
        ∑ j, ∑ k, ∑ l, lcp j (sigK sys L n) Q R * zJ sys L n k l R P := fun R => by
      rw [sigK_eq_sum_lcp hL Q R, zK_eq_sum hL hn R P, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
    rw [tsum_congr e, Summable.tsum_finsetSum (fun j _ => summable_sum fun k _ =>
      summable_sum fun l _ => summable_lcp_sig_zJ hL hn j k l Q P)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Summable.tsum_finsetSum (fun k _ => summable_sum fun l _ =>
      summable_lcp_sig_zJ hL hn j k l Q P)]
    exact Finset.sum_congr rfl fun k _ => Summable.tsum_finsetSum fun l _ =>
      summable_lcp_sig_zJ hL hn j k l Q P
  have h2 : ∑' R, zK sys L n Q R * sigK sys L n R P =
      ∑ j, ∑ k, ∑ l, ∑' R, zJ sys L n j k Q R * lcp l (sigK sys L n) R P := by
    have e : ∀ R, zK sys L n Q R * sigK sys L n R P =
        ∑ j, ∑ k, ∑ l, zJ sys L n j k Q R * lcp l (sigK sys L n) R P := fun R => by
      rw [zK_eq_sum hL hn Q R, sigK_eq_sum_lcp hL R P, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
    rw [tsum_congr e, Summable.tsum_finsetSum (fun j _ => summable_sum fun k _ =>
      summable_sum fun l _ => summable_zJ_lcp_sig hL hn j k l Q P)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Summable.tsum_finsetSum (fun k _ => summable_sum fun l _ =>
      summable_zJ_lcp_sig hL hn j k l Q P)]
    exact Finset.sum_congr rfl fun k _ => Summable.tsum_finsetSum fun l _ =>
      summable_zJ_lcp_sig hL hn j k l Q P
  rw [h1, h2]
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]

/-! ## The same-channel words -/

lemma zJ_diag_eq_zero (j : Ch eta) {R P : Cf eta} (h : ¬ OnCh j R P) : zJ sys L n j j R P = 0 := by
  unfold zJ
  have h1 : ∀ S, lcp j (potKernel sys L) R S * lcp j (sigK sys L n) S P = 0 := fun S => by
    by_cases ha : OnCh j R S
    · rw [lcp_eq_zero (fun hb => h (onCh_comp ha hb)), mul_zero]
    · rw [lcp_eq_zero ha, zero_mul]
  have h2 : ∀ S, lcp j (sigK sys L n) R S * lcp j (potKernel sys L) S P = 0 := fun S => by
    by_cases ha : OnCh j R S
    · rw [lcp_eq_zero (fun hb => h (onCh_comp ha hb)), mul_zero]
    · rw [lcp_eq_zero ha, zero_mul]
  simp [h1, h2]

/-- A same-channel word joins only configurations on that channel. -/
lemma h3fW_diag_eq_zero (j : Ch eta) {Q P : Cf eta} (h : ¬ OnCh j Q P) :
    h3fW sys L n j j j Q P = 0 := by
  unfold h3fW
  have h1 : ∀ R, lcp j (sigK sys L n) Q R * zJ sys L n j j R P = 0 := fun R => by
    by_cases ha : OnCh j Q R
    · rw [zJ_diag_eq_zero j (fun hb => h (onCh_comp ha hb)), mul_zero]
    · rw [lcp_eq_zero ha, zero_mul]
  have h2 : ∀ R, zJ sys L n j j Q R * lcp j (sigK sys L n) R P = 0 := fun R => by
    by_cases hb : OnCh j R P
    · rw [zJ_diag_eq_zero j (fun ha => h (onCh_comp ha hb)), zero_mul]
    · rw [lcp_eq_zero hb, mul_zero]
  simp [h1, h2]

lemma zJ_diag_conj (hL : 0 < L) (j : Ch eta) (R P : Cf eta) :
    conj (zJ sys L n j j R P) = zJ sys L n j j P R := by
  unfold zJ
  rw [map_sub, Complex.conj_tsum, Complex.conj_tsum]
  have h1 : ∀ S, conj (lcp j (potKernel sys L) R S * lcp j (sigK sys L n) S P) =
      -(lcp j (sigK sys L n) P S * lcp j (potKernel sys L) S R) := fun S => by
    rw [map_mul, lcp_pot_conj hL, lcp_sig_conj hL]; ring
  have h2 : ∀ S, conj (lcp j (sigK sys L n) R S * lcp j (potKernel sys L) S P) =
      -(lcp j (potKernel sys L) P S * lcp j (sigK sys L n) S R) := fun S => by
    rw [map_mul, lcp_sig_conj hL, lcp_pot_conj hL]; ring
  simp_rw [h1, h2, tsum_neg]
  ring

/-- **The same-channel words are Hermitian.** -/
theorem h3fW_diag_conj (hL : 0 < L) (j : Ch eta) (Q P : Cf eta) :
    conj (h3fW sys L n j j j Q P) = h3fW sys L n j j j P Q := by
  unfold h3fW
  rw [map_mul, map_sub, Complex.conj_tsum, Complex.conj_tsum]
  have h1 : ∀ R, conj (lcp j (sigK sys L n) Q R * zJ sys L n j j R P) =
      -(zJ sys L n j j P R * lcp j (sigK sys L n) R Q) := fun R => by
    rw [map_mul, lcp_sig_conj hL, zJ_diag_conj hL]; ring
  have h2 : ∀ R, conj (zJ sys L n j j Q R * lcp j (sigK sys L n) R P) =
      -(lcp j (sigK sys L n) P R * zJ sys L n j j R Q) := fun R => by
    rw [map_mul, zJ_diag_conj hL, lcp_sig_conj hL]; ring
  simp_rw [h1, h2, tsum_neg]
  have hc : conj (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by
    rw [map_neg, map_div₀, map_one, map_ofNat]
  rw [hc]
  ring

/-- The flat bound of a same-channel two-hop word: `|z_jj(R, P)| ≤ 2 chb_j n⁻³`. -/
lemma norm_zJ_diag_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (R P : Cf eta) :
    ‖zJ sys L n j j R P‖ ≤ 2 * (chb sys L j / (n : ℝ) ^ 3) := by
  classical
  have hflat : ∀ x : ℝ, x ≤ (if OnCh j R P then chC sys L j ^ 2 / cgap sys (gF L) *
      (611 / (3 * (n : ℝ) / 4) ^ 3) else 0) → x ≤ chb sys L j / (n : ℝ) ^ 3 := by
    intro x hx
    refine hx.trans ?_
    have hb : chC sys L j ^ 2 / cgap sys (gF L) * (611 / (3 * (n : ℝ) / 4) ^ 3) =
        chb sys L j / (n : ℝ) ^ 3 := by rw [flat_const_eq hn]; rfl
    split_ifs
    · exact le_of_eq hb
    · have := chb_nonneg (sys := sys) hL j; positivity
  unfold zJ
  refine (norm_sub_le _ _).trans ?_
  rw [two_mul]
  refine add_le_add ?_ ?_
  · refine (norm_tsum_le_tsum_norm (summable_lcp_pot_sig hL hn j j R P).norm).trans (hflat _ ?_)
    refine le_trans ?_ (tsum_chMaj_sigMaj_le hL hn j R P)
    exact (summable_lcp_pot_sig hL hn j j R P).norm.tsum_le_tsum (fun S => by
        rw [norm_mul]
        exact mul_le_mul (norm_lcp_pot_le hL j R S) (norm_lcp_sig_le hL (by omega) j S P)
          (norm_nonneg _) (chMaj_nonneg j (chC_nonneg sys hL j) R S))
      (summable_chMaj_sigMaj hL hn j R P)
  · refine (norm_tsum_le_tsum_norm (summable_lcp_sig_pot hL hn j j R P).norm).trans (hflat _ ?_)
    refine le_trans ?_ (tsum_sigMaj_chMaj_le hL hn j R P)
    exact (summable_lcp_sig_pot hL hn j j R P).norm.tsum_le_tsum (fun S => by
        rw [norm_mul]
        exact mul_le_mul (norm_lcp_sig_le hL (by omega) j R S) (norm_lcp_pot_le hL j S P)
          (norm_nonneg _) (sigMaj_nonneg hL j R S))
      (summable_sigMaj_chMaj hL hn j R P)

/-- **The same-channel words of `P H^{(3)} P` are `O(n⁻⁴)`**:
`|h3fW j j j (Q, P)| ≤ 2 A_j chb_j n⁻³`, `A_j = (c_j/c_gap) 416/(3n)`. -/
theorem norm_h3fW_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (Q P : Cf eta) :
    ‖h3fW sys L n j j j Q P‖ ≤ 2 * Asj sys L n j * (chb sys L j / (n : ℝ) ^ 3) := by
  have hb0 : 0 ≤ chb sys L j / (n : ℝ) ^ 3 := by
    have := chb_nonneg (sys := sys) hL j; positivity
  have hA0 := Asj_nonneg (sys := sys) (n := n) hL j
  have hA : ‖∑' R, lcp j (sigK sys L n) Q R * zJ sys L n j j R P‖ ≤
      Asj sys L n j * (2 * (chb sys L j / (n : ℝ) ^ 3)) := by
    refine (norm_tsum_le_tsum_norm (summable_lcp_sig_zJ hL hn j j j Q P).norm).trans ?_
    calc ∑' R, ‖lcp j (sigK sys L n) Q R * zJ sys L n j j R P‖
        ≤ ∑' R, sigMaj sys L n j Q R * (2 * (chb sys L j / (n : ℝ) ^ 3)) :=
          (summable_lcp_sig_zJ hL hn j j j Q P).norm.tsum_le_tsum (fun R => by
            rw [norm_mul]
            exact mul_le_mul (norm_lcp_sig_le hL (by omega) j Q R) (norm_zJ_diag_le hL hn j R P)
              (norm_nonneg _) (sigMaj_nonneg hL j Q R))
            ((summable_sigMaj_row (sys := sys) (L := L) hn j Q).mul_right _)
      _ = (∑' R, sigMaj sys L n j Q R) * (2 * (chb sys L j / (n : ℝ) ^ 3)) := tsum_mul_right
      _ ≤ _ := mul_le_mul_of_nonneg_right (tsum_sigMaj_row hL hn j Q) (by positivity)
  have hB : ‖∑' R, zJ sys L n j j Q R * lcp j (sigK sys L n) R P‖ ≤
      Asj sys L n j * (2 * (chb sys L j / (n : ℝ) ^ 3)) := by
    refine (norm_tsum_le_tsum_norm (summable_zJ_lcp_sig hL hn j j j Q P).norm).trans ?_
    calc ∑' R, ‖zJ sys L n j j Q R * lcp j (sigK sys L n) R P‖
        ≤ ∑' R, (2 * (chb sys L j / (n : ℝ) ^ 3)) * sigMaj sys L n j R P :=
          (summable_zJ_lcp_sig hL hn j j j Q P).norm.tsum_le_tsum (fun R => by
            rw [norm_mul]
            exact mul_le_mul (norm_zJ_diag_le hL hn j Q R) (norm_lcp_sig_le hL (by omega) j R P)
              (norm_nonneg _) (by positivity))
            ((summable_sigMaj_col (sys := sys) (L := L) hn j P).mul_left _)
      _ = (2 * (chb sys L j / (n : ℝ) ^ 3)) * ∑' R, sigMaj sys L n j R P := tsum_mul_left
      _ ≤ (2 * (chb sys L j / (n : ℝ) ^ 3)) * Asj sys L n j :=
          mul_le_mul_of_nonneg_left (tsum_sigMaj_col hL hn j P) (by positivity)
      _ = _ := by ring
  unfold h3fW
  rw [norm_mul, show ‖-(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  calc 1 / 2 * ‖(∑' R, lcp j (sigK sys L n) Q R * zJ sys L n j j R P) -
        ∑' R, zJ sys L n j j Q R * lcp j (sigK sys L n) R P‖
      ≤ 1 / 2 * (Asj sys L n j * (2 * (chb sys L j / (n : ℝ) ^ 3)) +
          Asj sys L n j * (2 * (chb sys L j / (n : ℝ) ^ 3))) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hA hB)) (by norm_num)
    _ = _ := by ring

end Words

end FSNormal
