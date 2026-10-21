import PlaneWave.KineticCompletion.CrossCommutators

/-!
# Kinetic completion, part 3: the multi-channel first-rotation words

The words of `P H^{(3)} P = ½ P[Σ_b, [Σ_b, W]] P` (`h3fW j k l`, three hops output to input)
expand as `h3fW = -A + ½ B + ½ C` (`h3fW_eq`), with the pair sums over intermediate
configurations `(R, S)`

* `A = Σ σ_j(Q,R) w_k(R,S) σ_l(S,P)` (the closed word `S_j^* R W_k R S_l`; the fourth word of the
  definition equals `A` after exchanging `R` and `S`),
* `B = Σ σ_j(Q,R) σ_k(R,S) w_l(S,P)` (the open word `S_j^* S_k W_l`),
* `C = Σ w_j(Q,S) σ_k(S,R) σ_l(R,P)` (the open word `W_j S_k^* S_l`).

**Exterior channel separation** (`sep_inP`, `lem:separation`): a configuration reached from the
bulk block `Q` along two different channels lies in the cube. Hence (`fA_eq_zero`, `fB_eq_zero`,
`fC_eq_zero`) `A = 0` if `k = l ≠ j`, `B = 0` if `j ≠ k`, `C = 0` if `k ≠ l`: every multi-channel
word is either zero or has a transverse pair of channels. The remaining words are bounded on the
cube (`prop:mp`) by `‖·u‖ ≤ C n⁻³ ‖(1 + A)u‖`:

* the weighted rows of `Σ_b` (`row_sig_lam`): `Σ_P |σ_l(S,P)| Λ_d(P)⁻² ≤ α_l = O(n⁻³)` for
  `d · ℓ_l = 1` and `P` in the bulk (eq:Sdirection, `‖S_l Λ_d⁻¹‖ ≤ C K⁻²`);
* the transverse Hardy inequality `dir_hardy` with `Λ_e` (`e · ℓ` one on the potential's channel
  and zero on the generator's channel), and `Λ_d Λ_e ≤ c_Λ (1 + A)`;
* truncation of the intermediate configurations to boxes (`cbox`), where all sums are finite, and
  the limit (`norm_kop_le_of_tendsto`).

With the cross commutators of `PlaneWave.KineticCompletion.CrossCommutators`: **`norm_H3mp_le`** (eq:mpbound),
`‖H₃^mp u‖ ≤ (C_X(n) + C_Y(n)) ‖(1 + A) u‖`, `C_X(n) + C_Y(n) = O(n⁻³ log² n)`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSKernel

lemma norm_sq_eq_kop {X : Type*} [Fintype X] (κ : X → X → ℂ) (u : EuclideanSpace ℂ X) :
    ‖kop κ u‖ ^ 2 = ∑ q, ‖∑ p, u.ofLp p * κ q p‖ ^ 2 := by
  rw [norm_sq_eq]; rfl

end FSKernel

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

/-! ## Supports of `Σ_b` -/

lemma sig_ne_zero {j : Ch eta} {R S : Cf eta} (h : lcp j (sigK sys L n) R S ≠ 0) :
    OnCh j R S ∧ Cross (n : ℝ) R S := by
  unfold lcp at h
  split_ifs at h with hj
  · refine ⟨hj, ?_⟩
    by_contra hc
    exact h (sigK_eq_zero_of_not_cross hc)
  · exact absurd rfl h

lemma cross_left_inP {R S : Cf eta} (hR : InP (n : ℝ) R) (h : Cross (n : ℝ) R S) :
    InQ (n : ℝ) R ∧ ¬ InP (n : ℝ) S := by
  rcases h with h | h
  · exact h
  · exact absurd hR h.1

lemma cross_right_inP {R S : Cf eta} (hS : InP (n : ℝ) S) (h : Cross (n : ℝ) R S) :
    ¬ InP (n : ℝ) R ∧ InQ (n : ℝ) S := by
  rcases h with h | h
  · exact absurd hS h.2
  · exact h

lemma cross_left_out {R S : Cf eta} (hR : ¬ InP (n : ℝ) R) (h : Cross (n : ℝ) R S) :
    InQ (n : ℝ) S := by
  rcases h with h | h
  · exact absurd (h.1.inP (Nat.cast_nonneg n)) hR
  · exact h.2

lemma cross_right_out {R S : Cf eta} (hS : ¬ InP (n : ℝ) S) (h : Cross (n : ℝ) R S) :
    InQ (n : ℝ) R := by
  rcases h with h | h
  · exact h.1
  · exact absurd (h.2.inP (Nat.cast_nonneg n)) hS

/-! ## Exterior channel separation -/

lemma pair_eq_of_mem (pr pr' : FiniteElectronPair eta)
    (h1 : pr.1.1 = pr'.1.1 ∨ pr.1.1 = pr'.1.2) (h2 : pr.1.2 = pr'.1.1 ∨ pr.1.2 = pr'.1.2) :
    pr = pr' := by
  have hlt := pr.2
  have hlt' := pr'.2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) (ne_of_lt hlt)
  · exact Subtype.ext (Prod.ext h1 h2)
  · exfalso
    have : pr.1.2 < pr.1.1 := by rw [h1, h2]; exact hlt'
    exact absurd hlt (not_lt.mpr this.le)
  · exact absurd (h1.trans h2.symm) (ne_of_lt hlt)

lemma rho_three_le {x y z : Lattice3} {r : ℝ} (hx : FSChannel.rho x ≤ r) (hy : FSChannel.rho y ≤ r)
    (hz : FSChannel.rho z ≤ r) : FSChannel.rho (x + y - z) ≤ 3 * r := by
  have h1 := FSChannel.rho_add_le (x + y) (-z)
  have h2 := FSChannel.rho_add_le x y
  rw [rho_neg', ← sub_eq_add_neg] at h1
  linarith

/-- **Exterior channel separation** (`lem:separation`): if `R` is reached from bulk
configurations `Q` and `S` along two different channels `j ≠ k`, then `R` lies in the cube. -/
theorem sep_inP {j k : Ch eta} (hjk : j ≠ k) {R Q S : Cf eta} (hj : OnCh j R Q)
    (hk : OnCh k R S) (hQ : InQ (n : ℝ) Q) (hS : InQ (n : ℝ) S) : InP (n : ℝ) R := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hQb : ∀ c, FSChannel.rho (Q c) ≤ n / 4 := fun c => rho_le_of_inQ hn0 hQ c
  have hSb : ∀ c, FSChannel.rho (S c) ≤ n / 4 := fun c => rho_le_of_inQ hn0 hS c
  suffices hR : ∀ c, FSChannel.rho (R c) ≤ 3 * (n / 4) by
    intro c i
    have h1 : |((R c i : ℤ) : ℝ)| ≤ FSChannel.rho (R c) := by
      unfold FSChannel.rho
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (FSLattice.sq_le_lsq _ i)
    linarith [hR c]
  have hle : ∀ c, FSChannel.rho (Q c) ≤ 3 * (n / 4) := fun c => by linarith [hQb c]
  have hle' : ∀ c, FSChannel.rho (S c) ≤ 3 * (n / 4) := fun c => by linarith [hSb c]
  intro c
  cases j with
  | inl a =>
    have hjR := (FSFlux.onCh_inl_iff a R Q).mp hj
    by_cases hca : c = a
    · subst hca
      cases k with
      | inl b =>
        have hcb : c ≠ b := fun h => hjk (by rw [h])
        rw [(FSFlux.onCh_inl_iff b R S).mp hk c hcb]; exact hle' c
      | inr pr =>
        obtain ⟨hk1, hk2⟩ := (FSFlux.onCh_inr_iff pr R S).mp hk
        have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
        by_cases h1 : c = pr.1.1
        · subst h1
          have e : R pr.1.1 = S pr.1.1 + S pr.1.2 - Q pr.1.2 := by
            rw [← hjR pr.1.2 hne.symm]; rw [← hk2]; abel
          rw [e]; exact rho_three_le (hSb _) (hSb _) (hQb _)
        · by_cases h2 : c = pr.1.2
          · subst h2
            have e : R pr.1.2 = S pr.1.1 + S pr.1.2 - Q pr.1.1 := by
              rw [← hjR pr.1.1 hne]; rw [← hk2]; abel
            rw [e]; exact rho_three_le (hSb _) (hSb _) (hQb _)
          · rw [hk1 c h1 h2]; exact hle' c
    · rw [hjR c hca]; exact hle c
  | inr pr =>
    obtain ⟨hj1, hj2⟩ := (FSFlux.onCh_inr_iff pr R Q).mp hj
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    by_cases hc1 : c = pr.1.1 ∨ c = pr.1.2
    · cases k with
      | inl b =>
        have hkR := (FSFlux.onCh_inl_iff b R S).mp hk
        by_cases hcb : c = b
        · subst hcb
          rcases hc1 with h1 | h1
          · subst h1
            have e : R pr.1.1 = Q pr.1.1 + Q pr.1.2 - S pr.1.2 := by
              rw [← hkR pr.1.2 hne.symm]; rw [← hj2]; abel
            rw [e]; exact rho_three_le (hQb _) (hQb _) (hSb _)
          · subst h1
            have e : R pr.1.2 = Q pr.1.1 + Q pr.1.2 - S pr.1.1 := by
              rw [← hkR pr.1.1 hne]; rw [← hj2]; abel
            rw [e]; exact rho_three_le (hQb _) (hQb _) (hSb _)
        · rw [hkR c hcb]; exact hle' c
      | inr pr' =>
        obtain ⟨hk1, hk2⟩ := (FSFlux.onCh_inr_iff pr' R S).mp hk
        by_cases hc2 : c = pr'.1.1 ∨ c = pr'.1.2
        · -- the common register: the other register of `pr` is not moved by `pr'`
          rcases hc1 with h1 | h1
          · subst h1
            have hb : ¬ (pr.1.2 = pr'.1.1 ∨ pr.1.2 = pr'.1.2) := fun hb =>
              hjk (by rw [pair_eq_of_mem pr pr' hc2 hb])
            push Not at hb
            have e : R pr.1.1 = Q pr.1.1 + Q pr.1.2 - S pr.1.2 := by
              rw [← hk1 pr.1.2 hb.1 hb.2]; rw [← hj2]; abel
            rw [e]; exact rho_three_le (hQb _) (hQb _) (hSb _)
          · subst h1
            have hb : ¬ (pr.1.1 = pr'.1.1 ∨ pr.1.1 = pr'.1.2) := fun hb =>
              hjk (by rw [pair_eq_of_mem pr pr' hb hc2])
            push Not at hb
            have e : R pr.1.2 = Q pr.1.1 + Q pr.1.2 - S pr.1.1 := by
              rw [← hk1 pr.1.1 hb.1 hb.2]; rw [← hj2]; abel
            rw [e]; exact rho_three_le (hQb _) (hQb _) (hSb _)
        · push Not at hc2
          rw [hk1 c hc2.1 hc2.2]; exact hle' c
    · push Not at hc1
      rw [hj1 c hc1.1 hc1.2]; exact hle c

/-! ## Rows and columns of `Σ_b` on finite sets -/

lemma sum_norm_sig_row_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (Q : Cf eta)
    (G : Finset (Cf eta)) : ∑ R ∈ G, ‖lcp j (sigK sys L n) Q R‖ ≤ Asj sys L n j := by
  calc ∑ R ∈ G, ‖lcp j (sigK sys L n) Q R‖ ≤ ∑ R ∈ G, sigMaj sys L n j Q R :=
        Finset.sum_le_sum fun R _ => norm_lcp_sig_le hL (by omega) j Q R
    _ ≤ ∑' R, sigMaj sys L n j Q R :=
        (summable_sigMaj_row (sys := sys) (L := L) hn j Q).sum_le_tsum G (fun R _ => sigMaj_nonneg hL j Q R)
    _ ≤ Asj sys L n j := tsum_sigMaj_row hL hn j Q

lemma sum_norm_sig_col_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (R : Cf eta)
    (G : Finset (Cf eta)) : ∑ Q ∈ G, ‖lcp j (sigK sys L n) Q R‖ ≤ Asj sys L n j := by
  calc ∑ Q ∈ G, ‖lcp j (sigK sys L n) Q R‖ ≤ ∑ Q ∈ G, sigMaj sys L n j Q R :=
        Finset.sum_le_sum fun Q _ => norm_lcp_sig_le hL (by omega) j Q R
    _ ≤ ∑' Q, sigMaj sys L n j Q R :=
        (summable_sigMaj_col (sys := sys) (L := L) hn j R).sum_le_tsum G (fun Q _ => sigMaj_nonneg hL j Q R)
    _ ≤ Asj sys L n j := tsum_sigMaj_col hL hn j R

variable (sys L n) in
/-- The weighted row constant `α_l = (c_l/c_gap)(4/(3n))⁴ (1 + 13 n) = O(n⁻³)`. -/
noncomputable def alS (l : Ch eta) : ℝ :=
  chC sys L l / cgap sys (gF L) * (4 / (3 * n)) ^ 4 * (1 + 13 * n)

lemma alS_nonneg (hL : 0 < L) (l : Ch eta) : 0 ≤ alS sys L n l := by
  unfold alS
  have := chC_nonneg sys hL l
  have := cgap_pos sys (gF_pos hL).ne'
  positivity

lemma tailFn_le_pow {R : ℝ} (hR : 0 < R) (μ : FSLattice.L3) : tailFn R μ ≤ (1 / R) ^ 4 := by
  unfold tailFn
  split_ifs with h
  · have hR2 : 0 < R ^ 2 := by positivity
    have h1 : (nsq μ)⁻¹ ≤ (R ^ 2)⁻¹ := inv_anti₀ hR2 h.le
    calc (nsq μ)⁻¹ ^ 2 ≤ ((R ^ 2)⁻¹) ^ 2 :=
          pow_le_pow_left₀ (inv_nonneg.mpr (by linarith)) h1 2
      _ = (1 / R) ^ 4 := by field_simp
  · positivity

/-- **The weighted rows of `Σ_b`** (eq:Sdirection): for `d · ℓ_l = 1`, `Σ_P |σ_l(S,P)| Λ_d(P)⁻²
≤ α_l` over bulk configurations `P`. -/
lemma row_sig_lam (hL : 0 < L) (hn : 2 ≤ n) (l : Ch eta) {d : Fin eta → ℤ} (hdl : dl d l = 1)
    (hd1 : l1 d ≤ 2) (S : Cf eta) (G : Finset (Cf eta))
    (hG : ∀ P ∈ G, lcp l (sigK sys L n) S P ≠ 0 → InQ (n : ℝ) P) :
    ∑ P ∈ G, ‖lcp l (sigK sys L n) S P‖ / lam d P ^ 2 ≤ alS sys L n l := by
  classical
  set G' := G.filter (fun P => lcp l (sigK sys L n) S P ≠ 0)
  have hsub : ∑ P ∈ G, ‖lcp l (sigK sys L n) S P‖ / lam d P ^ 2 =
      ∑ P ∈ G', ‖lcp l (sigK sys L n) S P‖ / lam d P ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun P _ => ?_
    split_ifs with h
    · rfl
    · push Not at h; rw [h, norm_zero, zero_div]
  rw [hsub]
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hR : (0 : ℝ) < 3 * n / 4 := by positivity
  set c := chC sys L l / cgap sys (gF L)
  have hc : 0 ≤ c := div_nonneg (chC_nonneg sys hL l) (cgap_pos sys (gF_pos hL).ne').le
  have hterm : ∀ P ∈ G', ‖lcp l (sigK sys L n) S P‖ / lam d P ^ 2 ≤
      c * (4 / (3 * n)) ^ 4 * (1 / (1 + FSLattice.lsq (dsum d P))) := by
    intro P hP
    have hne := (Finset.mem_filter.mp hP).2
    obtain ⟨hon, -⟩ := sig_ne_zero hne
    have h1 := norm_lcp_sig_le (sys := sys) (n := n) hL (by omega) l S P
    have h2 : sigMaj sys L n l S P ≤ c * (4 / (3 * n)) ^ 4 := by
      unfold sigMaj
      rw [if_pos hon]
      apply mul_le_mul_of_nonneg_left _ hc
      refine (tailFn_le_pow hR _).trans (le_of_eq ?_)
      field_simp
    rw [lam_sq, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (h1.trans h2) (by
      have := FSLattice.lsq_nonneg (dsum d P); positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  unfold alS
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  -- the directional coordinates are distinct points of a box
  have hinj : Set.InjOn (fun P => dsum d P) G' := by
    intro P hP P' hP' h
    have h1 := (sig_ne_zero (Finset.mem_filter.mp hP).2).1
    have h2 := (sig_ne_zero (Finset.mem_filter.mp hP').2).1
    have e1 := dsum_onCh_one hdl h1
    have e2 := dsum_onCh_one hdl h2
    have h' : dsum d P = dsum d P' := h
    have ht : S (lead l) - P (lead l) = S (lead l) - P' (lead l) := by
      have h3 : dsum d P + (S (lead l) - P (lead l)) = dsum d P' + (S (lead l) - P' (lead l)) :=
        e1.symm.trans e2
      rw [h'] at h3
      exact add_left_cancel h3
    rw [eq_sub_of_onCh h1, eq_sub_of_onCh h2, ht]
  have hbox : ∀ P ∈ G', dsum d P ∈ FSLattice.box ⌊(n : ℝ) / 2⌋₊ := by
    intro P hP
    have hQ := hG P (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2
    exact FSLattice.mem_box_floor_of_lsq_le (by positivity) (lsq_dsum_le_of_inQ hd1 hQ)
  calc ∑ P ∈ G', 1 / (1 + FSLattice.lsq (dsum d P))
      = ∑ w ∈ G'.image (fun P => dsum d P), 1 / (1 + FSLattice.lsq w) :=
        (Finset.sum_image (f := fun w => 1 / (1 + FSLattice.lsq w)) hinj).symm
    _ ≤ ∑ w ∈ FSLattice.box ⌊(n : ℝ) / 2⌋₊, 1 / (1 + FSLattice.lsq w) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => by
          obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hw; exact hbox P hP)
          (fun w _ _ => by have := FSLattice.lsq_nonneg w; positivity)
    _ ≤ 1 + 26 * (⌊(n : ℝ) / 2⌋₊ : ℝ) := FSLattice.sum_box_inv_le _
    _ ≤ 1 + 13 * n := by
        have : (⌊(n : ℝ) / 2⌋₊ : ℝ) ≤ (n : ℝ) / 2 := Nat.floor_le (by positivity)
        linarith

/-! ## The words as sums over intermediate pairs -/

variable (sys L n) in
/-- The closed word `σ_j w_k σ_l` on intermediate pairs `(R, S)`. -/
noncomputable def wdA (j k l : Ch eta) (Q P : Cf eta) (x : Cf eta × Cf eta) : ℂ :=
  lcp j (sigK sys L n) Q x.1 * (lcp k (potKernel sys L) x.1 x.2 * lcp l (sigK sys L n) x.2 P)

variable (sys L n) in
/-- The open word `σ_j σ_k w_l`. -/
noncomputable def wdB (j k l : Ch eta) (Q P : Cf eta) (x : Cf eta × Cf eta) : ℂ :=
  lcp j (sigK sys L n) Q x.1 * (lcp k (sigK sys L n) x.1 x.2 * lcp l (potKernel sys L) x.2 P)

variable (sys L n) in
/-- The open word `w_j σ_k σ_l` (outer variable `R = x.1`, inner `S = x.2`). -/
noncomputable def wdC (j k l : Ch eta) (Q P : Cf eta) (x : Cf eta × Cf eta) : ℂ :=
  lcp j (potKernel sys L) Q x.2 * lcp k (sigK sys L n) x.2 x.1 * lcp l (sigK sys L n) x.1 P

lemma summable_wdA (hL : 0 < L) (hn : 2 ≤ n) (j k l : Ch eta) (Q P : Cf eta) :
    Summable (wdA sys L n j k l Q P) := by
  have hg : Summable fun x : Cf eta × Cf eta =>
      sigMaj sys L n j Q x.1 * (chC sys L k * sigMaj sys L n l x.2 P) :=
    Summable.mul_of_nonneg (summable_sigMaj_row (sys := sys) (L := L) hn j Q)
      ((summable_sigMaj_col (sys := sys) (L := L) hn l P).mul_left _) (fun R => sigMaj_nonneg hL j Q R)
      (fun S => mul_nonneg (chC_nonneg sys hL k) (sigMaj_nonneg hL l S P))
  refine Summable.of_norm_bounded hg fun x => ?_
  unfold wdA
  rw [norm_mul, norm_mul]
  exact mul_le_mul (norm_lcp_sig_le hL (by omega) j Q x.1)
    (mul_le_mul ((norm_lcp_pot_le hL k _ _).trans (chMaj_le k (chC_nonneg sys hL k) _ _))
      (norm_lcp_sig_le hL (by omega) l _ P) (norm_nonneg _) (chC_nonneg sys hL k))
    (by positivity) (sigMaj_nonneg hL j Q x.1)

lemma summable_wdB (hL : 0 < L) (hn : 2 ≤ n) (j k l : Ch eta) (Q P : Cf eta) :
    Summable (wdB sys L n j k l Q P) := by
  have hg0 : ∀ x : Cf eta × Cf eta,
      0 ≤ sigMaj sys L n j Q x.1 * (sigMaj sys L n k x.1 x.2 * chC sys L l) := fun x =>
    mul_nonneg (sigMaj_nonneg hL j Q x.1)
      (mul_nonneg (sigMaj_nonneg hL k x.1 x.2) (chC_nonneg sys hL l))
  have hg : Summable fun x : Cf eta × Cf eta =>
      sigMaj sys L n j Q x.1 * (sigMaj sys L n k x.1 x.2 * chC sys L l) := by
    rw [summable_prod_of_nonneg (fun x => hg0 x)]
    refine ⟨fun R => ?_, ?_⟩
    · exact ((summable_sigMaj_row (sys := sys) (L := L) hn k R).mul_right (chC sys L l)).mul_left
        (sigMaj sys L n j Q R)
    · refine Summable.of_nonneg_of_le (fun R => tsum_nonneg fun S => hg0 (R, S)) (fun R => ?_)
        ((summable_sigMaj_row (sys := sys) (L := L) hn j Q).mul_right (Asj sys L n k * chC sys L l))
      show ∑' S, sigMaj sys L n j Q R * (sigMaj sys L n k R S * chC sys L l) ≤
        sigMaj sys L n j Q R * (Asj sys L n k * chC sys L l)
      rw [tsum_mul_left, tsum_mul_right]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (tsum_sigMaj_row (sys := sys) hL hn k R) (chC_nonneg sys hL l)) (sigMaj_nonneg hL j Q R)
  refine Summable.of_norm_bounded hg fun x => ?_
  unfold wdB
  rw [norm_mul, norm_mul]
  exact mul_le_mul (norm_lcp_sig_le hL (by omega) j Q x.1)
    (mul_le_mul (norm_lcp_sig_le hL (by omega) k _ _)
      ((norm_lcp_pot_le hL l _ _).trans (chMaj_le l (chC_nonneg sys hL l) _ _)) (norm_nonneg _)
      (sigMaj_nonneg hL k _ _))
    (by positivity) (sigMaj_nonneg hL j Q x.1)

lemma summable_wdC (hL : 0 < L) (hn : 2 ≤ n) (j k l : Ch eta) (Q P : Cf eta) :
    Summable (wdC sys L n j k l Q P) := by
  have hg0 : ∀ x : Cf eta × Cf eta,
      0 ≤ chC sys L j * sigMaj sys L n k x.2 x.1 * sigMaj sys L n l x.1 P := fun x =>
    mul_nonneg (mul_nonneg (chC_nonneg sys hL j) (sigMaj_nonneg hL k x.2 x.1))
      (sigMaj_nonneg hL l x.1 P)
  have hg : Summable fun x : Cf eta × Cf eta =>
      chC sys L j * sigMaj sys L n k x.2 x.1 * sigMaj sys L n l x.1 P := by
    rw [summable_prod_of_nonneg (fun x => hg0 x)]
    refine ⟨fun R => ?_, ?_⟩
    · exact ((summable_sigMaj_col (sys := sys) (L := L) hn k R).mul_left (chC sys L j)).mul_right
        (sigMaj sys L n l R P)
    · refine Summable.of_nonneg_of_le (fun R => tsum_nonneg fun S => hg0 (R, S)) (fun R => ?_)
        ((summable_sigMaj_col (sys := sys) (L := L) hn l P).mul_left (chC sys L j * Asj sys L n k))
      show ∑' S, chC sys L j * sigMaj sys L n k S R * sigMaj sys L n l R P ≤
        chC sys L j * Asj sys L n k * sigMaj sys L n l R P
      rw [tsum_mul_right, tsum_mul_left]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (tsum_sigMaj_col (sys := sys) hL hn k R) (chC_nonneg sys hL j)) (sigMaj_nonneg hL l R P)
  refine Summable.of_norm_bounded hg fun x => ?_
  unfold wdC
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul ((norm_lcp_pot_le hL j _ _).trans
      (chMaj_le j (chC_nonneg sys hL j) _ _))
      (norm_lcp_sig_le hL (by omega) k _ _) (norm_nonneg _) (chC_nonneg sys hL j))
    (norm_lcp_sig_le hL (by omega) l _ P) (norm_nonneg _) (by
      have := sigMaj_nonneg (sys := sys) (n := n) hL k x.2 x.1
      have := chC_nonneg sys hL j; positivity)

/-- **The words of `P H^{(3)} P`**: `h3fW_{jkl} = -A + ½ B + ½ C`. -/
theorem h3fW_eq (hL : 0 < L) (hn : 2 ≤ n) (j k l : Ch eta) (Q P : Cf eta) :
    h3fW sys L n j k l Q P = -(∑' x, wdA sys L n j k l Q P x) +
      (1 / 2 : ℂ) * (∑' x, wdB sys L n j k l Q P x) + (1 / 2 : ℂ) * (∑' x, wdC sys L n j k l Q P x) := by
  have hA := summable_wdA (sys := sys) hL hn j k l Q P
  have hB := summable_wdB (sys := sys) hL hn j k l Q P
  have hC := summable_wdC (sys := sys) hL hn j k l Q P
  -- the fourth word is the first with exchanged variables
  set fD : Cf eta × Cf eta → ℂ := fun x => lcp j (sigK sys L n) Q x.2 *
    lcp k (potKernel sys L) x.2 x.1 * lcp l (sigK sys L n) x.1 P with hfD
  have hDA : ∀ x, fD x = wdA sys L n j k l Q P x.swap := fun x => by
    simp only [hfD, wdA, Prod.fst_swap, Prod.snd_swap]; ring
  have hD : Summable fD := by
    have := hA.comp_injective Prod.swap_injective
    exact this.congr fun x => (hDA x).symm
  have hDsum : ∑' x, fD x = ∑' x, wdA sys L n j k l Q P x := by
    rw [tsum_congr hDA]
    exact (Equiv.prodComm _ _).tsum_eq (wdA sys L n j k l Q P)
  -- the four nested sums
  have e1 : ∑' R, lcp j (sigK sys L n) Q R * (∑' S, lcp k (potKernel sys L) R S *
      lcp l (sigK sys L n) S P) = ∑' x, wdA sys L n j k l Q P x := by
    rw [hA.tsum_prod]
    exact tsum_congr fun R => by simp only [wdA, tsum_mul_left]
  have e2 : ∑' R, lcp j (sigK sys L n) Q R * (∑' S, lcp k (sigK sys L n) R S *
      lcp l (potKernel sys L) S P) = ∑' x, wdB sys L n j k l Q P x := by
    rw [hB.tsum_prod]
    exact tsum_congr fun R => by simp only [wdB, tsum_mul_left]
  have e3 : ∑' R, (∑' S, lcp j (potKernel sys L) Q S * lcp k (sigK sys L n) S R) *
      lcp l (sigK sys L n) R P = ∑' x, wdC sys L n j k l Q P x := by
    rw [hC.tsum_prod]
    exact tsum_congr fun R => by simp only [wdC, tsum_mul_right]
  have e4 : ∑' R, (∑' S, lcp j (sigK sys L n) Q S * lcp k (potKernel sys L) S R) *
      lcp l (sigK sys L n) R P = ∑' x, fD x := by
    rw [hD.tsum_prod]
    exact tsum_congr fun R => by simp only [hfD, tsum_mul_right]
  have s1 : Summable fun R => lcp j (sigK sys L n) Q R * (∑' S, lcp k (potKernel sys L) R S *
      lcp l (sigK sys L n) S P) :=
    hA.prod.congr fun R => by simp only [wdA, tsum_mul_left]
  have s2 : Summable fun R => lcp j (sigK sys L n) Q R * (∑' S, lcp k (sigK sys L n) R S *
      lcp l (potKernel sys L) S P) :=
    hB.prod.congr fun R => by simp only [wdB, tsum_mul_left]
  have s3 : Summable fun R => (∑' S, lcp j (potKernel sys L) Q S * lcp k (sigK sys L n) S R) *
      lcp l (sigK sys L n) R P :=
    hC.prod.congr fun R => by simp only [wdC, tsum_mul_right]
  have s4 : Summable fun R => (∑' S, lcp j (sigK sys L n) Q S * lcp k (potKernel sys L) S R) *
      lcp l (sigK sys L n) R P :=
    hD.prod.congr fun R => by simp only [hfD, tsum_mul_right]
  unfold h3fW zJ
  simp_rw [mul_sub, sub_mul]
  rw [s1.tsum_sub s2, s3.tsum_sub s4, e1, e2, e3, e4, hDsum]
  ring

/-! ## Vanishing words -/

/-- `A = 0` for `k = l ≠ j` (closed separation). -/
lemma fA_eq_zero {j k : Ch eta} (hjk : j ≠ k) {Q P : Cf eta} (hQ : InP (n : ℝ) Q)
    (hP : InP (n : ℝ) P) (x : Cf eta × Cf eta) : wdA sys L n j k k Q P x = 0 := by
  by_contra h
  unfold wdA at h
  have h1 : lcp j (sigK sys L n) Q x.1 ≠ 0 := left_ne_zero_of_mul h
  have h23 := right_ne_zero_of_mul h
  have h2 : lcp k (potKernel sys L) x.1 x.2 ≠ 0 := left_ne_zero_of_mul h23
  have h3 : lcp k (sigK sys L n) x.2 P ≠ 0 := right_ne_zero_of_mul h23
  obtain ⟨on1, cr1⟩ := sig_ne_zero h1
  obtain ⟨hQb, hR⟩ := cross_left_inP hQ cr1
  have on2 : OnCh k x.1 x.2 := by
    unfold lcp at h2; by_contra hc; exact h2 (if_neg hc)
  obtain ⟨on3, cr3⟩ := sig_ne_zero h3
  obtain ⟨-, hPb⟩ := cross_right_inP hP cr3
  exact hR (sep_inP hjk (onCh_symm on1) (onCh_comp on2 on3) hQb hPb)

/-- `B = 0` for `j ≠ k`. -/
lemma fB_eq_zero {j k : Ch eta} (hjk : j ≠ k) (l : Ch eta) {Q P : Cf eta} (hQ : InP (n : ℝ) Q)
    (x : Cf eta × Cf eta) : wdB sys L n j k l Q P x = 0 := by
  by_contra h
  unfold wdB at h
  have h1 : lcp j (sigK sys L n) Q x.1 ≠ 0 := left_ne_zero_of_mul h
  have h2 : lcp k (sigK sys L n) x.1 x.2 ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul h)
  obtain ⟨on1, cr1⟩ := sig_ne_zero h1
  obtain ⟨hQb, hR⟩ := cross_left_inP hQ cr1
  obtain ⟨on2, cr2⟩ := sig_ne_zero h2
  have hSb := cross_left_out hR cr2
  exact hR (sep_inP hjk (onCh_symm on1) on2 hQb hSb)

/-- `C = 0` for `k ≠ l`. -/
lemma fC_eq_zero (j : Ch eta) {k l : Ch eta} (hkl : k ≠ l) {Q P : Cf eta} (hP : InP (n : ℝ) P)
    (x : Cf eta × Cf eta) : wdC sys L n j k l Q P x = 0 := by
  by_contra h
  unfold wdC at h
  have h3 : lcp l (sigK sys L n) x.1 P ≠ 0 := right_ne_zero_of_mul h
  have h2 : lcp k (sigK sys L n) x.2 x.1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  obtain ⟨on3, cr3⟩ := sig_ne_zero h3
  obtain ⟨hR, hPb⟩ := cross_right_inP hP cr3
  obtain ⟨on2, cr2⟩ := sig_ne_zero h2
  have hSb := cross_right_out hR cr2
  exact hR (sep_inP hkl (onCh_symm on2) on3 hSb hPb)

/-! ## Boxes of configurations -/

/-- The configuration box `max_{a,i} |k_{a,i}| ≤ N`. -/
noncomputable def cbox (N : ℕ) : Finset (Cf eta) := Fintype.piFinset fun _ => FSLattice.box N

lemma cbox_mono : Monotone (cbox (eta := eta)) := fun _ _ h =>
  Fintype.piFinset_subset _ _ fun _ => FSLattice.box_mono h

lemma exists_cbox (x : Cf eta) : ∃ N, x ∈ cbox N := by
  refine ⟨∑ a, ∑ i, (x a i).natAbs, ?_⟩
  rw [cbox, Fintype.mem_piFinset]
  intro a
  rw [FSLattice.mem_box]
  intro i
  have h1 : (x a i).natAbs ≤ ∑ i', (x a i').natAbs :=
    Finset.single_le_sum (f := fun i' => (x a i').natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2 : ∑ i', (x a i').natAbs ≤ ∑ a', ∑ i', (x a' i').natAbs :=
    Finset.single_le_sum (f := fun a' => ∑ i', (x a' i').natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ a)
  omega

lemma tendsto_cbox2 :
    Tendsto (fun N => cbox (eta := eta) N ×ˢ cbox (eta := eta) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro _ _ h
    exact Finset.product_subset_product (cbox_mono h) (cbox_mono h)
  · intro x
    obtain ⟨N₁, h₁⟩ := exists_cbox x.1
    obtain ⟨N₂, h₂⟩ := exists_cbox x.2
    exact ⟨max N₁ N₂, Finset.mem_product.mpr
      ⟨cbox_mono (le_max_left _ _) h₁, cbox_mono (le_max_right _ _) h₂⟩⟩

lemma tendsto_pair_sum {f : Cf eta × Cf eta → ℂ} (hf : Summable f) :
    Tendsto (fun N => ∑ x ∈ cbox N ×ˢ cbox N, f x) atTop (𝓝 (∑' x, f x)) :=
  hf.hasSum.comp tendsto_cbox2

/-- Bounds pass to the limit of the truncated kernels. -/
lemma norm_kop_le_of_tendsto {X : Type*} [Fintype X] (T : X → X → ℂ) (TN : ℕ → X → X → ℂ)
    (h : ∀ q p, Tendsto (fun N => TN N q p) atTop (𝓝 (T q p))) {B : ℝ} (u : EuclideanSpace ℂ X)
    (hB : ∀ N, ‖FSKernel.kop (TN N) u‖ ≤ B) : ‖FSKernel.kop T u‖ ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hlim : Tendsto (fun N => ∑ q, ‖∑ p, u.ofLp p * TN N q p‖ ^ 2) atTop
      (𝓝 (∑ q, ‖∑ p, u.ofLp p * T q p‖ ^ 2)) :=
    tendsto_finsetSum _ fun q _ =>
      ((tendsto_finsetSum _ fun p _ => (h q p).const_mul (u.ofLp p)).norm).pow 2
  have hle : ∑ q, ‖∑ p, u.ofLp p * T q p‖ ^ 2 ≤ B ^ 2 := by
    refine le_of_tendsto' hlim fun N => ?_
    have := hB N
    rw [← FSKernel.norm_sq_eq_kop (TN N) u]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have h2 : ‖FSKernel.kop T u‖ ^ 2 ≤ B ^ 2 := by
    rw [FSKernel.norm_sq_eq_kop]; exact hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 two_ne_zero).mp h2

/-! ## Sums over the cube -/

variable (n) in
/-- The cube as a finite set of lattice configurations. -/
noncomputable def cubeImg : Finset (Cf eta) := (Finset.univ : Finset (Cfg eta n)).image (cidx n)

omit [Fintype ν] in
lemma sum_cube_eq {M : Type*} [AddCommMonoid M] (φ : Cf eta → M) :
    ∑ P : Cfg eta n, φ (cidx n P) = ∑ T ∈ cubeImg n, φ T := by
  rw [cubeImg, Finset.sum_image (fun x _ y _ h => finiteConfigLatticeIndex_injective eta n h)]

omit [Fintype ν] in
lemma mem_cubeImg_inP {T : Cf eta} (hT : T ∈ cubeImg n) : InP (n : ℝ) T := by
  obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hT
  exact inP_cidx P

lemma sum_norm_sig_col_cube_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (R : Cf eta) :
    ∑ Q : Cfg eta n, ‖lcp j (sigK sys L n) (cidx n Q) R‖ ≤ Asj sys L n j := by
  rw [sum_cube_eq (fun T => ‖lcp j (sigK sys L n) T R‖)]
  exact sum_norm_sig_col_le hL hn j R _

/-- A lattice function from a cube vector. -/
noncomputable def liftU (u : En eta n) (T : Cf eta) : ℂ :=
  if h : ∃ P, cidx n P = T then u.ofLp h.choose else 0

omit [Fintype ν] in
lemma liftU_cidx (u : En eta n) (P : Cfg eta n) : liftU u (cidx n P) = u.ofLp P := by
  have h : ∃ P', cidx n P' = cidx n P := ⟨P, rfl⟩
  unfold liftU
  rw [dif_pos h, finiteConfigLatticeIndex_injective eta n h.choose_spec]

omit [Fintype ν] in
lemma liftU_eq_zero (u : En eta n) {T : Cf eta} (hT : T ∉ cubeImg n) : liftU u T = 0 := by
  unfold liftU
  rw [dif_neg]
  rintro ⟨P, rfl⟩
  exact hT (Finset.mem_image_of_mem _ (Finset.mem_univ P))

/-- **Hardy with inputs on the cube** (outputs on any finite set). -/
lemma hardy_cube_in (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (k : Ch eta) {e : Fin eta → ℤ} (he : dl e k = 1) (c : ℝ) (X : Finset (Cf eta))
    (v : En eta n) :
    ∑ S ∈ X, (∑ P : Cfg eta n, chMaj k c S (cidx n P) * ‖v.ofLp P‖) ^ 2 ≤
      c ^ 2 * Hunit ^ 2 * ∑ P : Cfg eta n, (1 + FSLattice.lsq (dsum e (cidx n P))) * ‖v.ofLp P‖ ^ 2 := by
  classical
  set F := X ∪ cubeImg n
  set f : Cf eta → ℝ := fun T => ‖liftU v T‖ with hf
  have hin : ∀ S, ∑ P : Cfg eta n, chMaj k c S (cidx n P) * ‖v.ofLp P‖ =
      ∑ T ∈ F, chMaj k c S T * f T := by
    intro S
    rw [show (∑ P : Cfg eta n, chMaj k c S (cidx n P) * ‖v.ofLp P‖) =
      ∑ P : Cfg eta n, chMaj k c S (cidx n P) * f (cidx n P) by
        simp only [hf, liftU_cidx], sum_cube_eq (fun T => chMaj k c S T * f T)]
    refine Finset.sum_subset Finset.subset_union_right fun T _ hT => ?_
    simp only [hf, liftU_eq_zero v hT, norm_zero, mul_zero]
  have hout : ∑ P : Cfg eta n, (1 + FSLattice.lsq (dsum e (cidx n P))) * ‖v.ofLp P‖ ^ 2 =
      ∑ T ∈ F, (1 + FSLattice.lsq (dsum e T)) * f T ^ 2 := by
    rw [show (∑ P : Cfg eta n, (1 + FSLattice.lsq (dsum e (cidx n P))) * ‖v.ofLp P‖ ^ 2) =
      ∑ P : Cfg eta n, (1 + FSLattice.lsq (dsum e (cidx n P))) * f (cidx n P) ^ 2 by
        simp only [hf, liftU_cidx], sum_cube_eq (fun T => (1 + FSLattice.lsq (dsum e T)) * f T ^ 2)]
    refine Finset.sum_subset Finset.subset_union_right fun T _ hT => ?_
    simp only [hf, liftU_eq_zero v hT, norm_zero]; ring
  simp_rw [hin]
  rw [hout]
  refine le_trans ?_ (dir_hardy Hunit hPeriodic k he c F f (fun T => norm_nonneg _))
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun _ _ _ => sq_nonneg _)

/-- **Hardy with outputs on the cube** (inputs on any finite set). -/
lemma hardy_cube_out (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (k : Ch eta) {e : Fin eta → ℤ} (he : dl e k = 1) (c : ℝ) (X : Finset (Cf eta))
    (f : Cf eta → ℝ) (hf : ∀ S, 0 ≤ f S) :
    ∑ Q : Cfg eta n, (∑ S ∈ X, chMaj k c (cidx n Q) S * f S) ^ 2 ≤
      c ^ 2 * Hunit ^ 2 * ∑ S ∈ X, (1 + FSLattice.lsq (dsum e S)) * f S ^ 2 := by
  classical
  set F := cubeImg n ∪ X
  set f' : Cf eta → ℝ := fun T => if T ∈ X then f T else 0 with hf'
  have hf'0 : ∀ T, 0 ≤ f' T := fun T => by simp only [hf']; split_ifs <;> simp [hf T]
  have hin : ∀ R, ∑ S ∈ X, chMaj k c R S * f S = ∑ S ∈ F, chMaj k c R S * f' S := by
    intro R
    rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := cubeImg n)) (fun T _ hT => by
      simp only [hf', if_neg hT, mul_zero])]
    exact Finset.sum_congr rfl fun S hS => by simp only [hf', if_pos hS]
  have hout : ∑ S ∈ X, (1 + FSLattice.lsq (dsum e S)) * f S ^ 2 =
      ∑ S ∈ F, (1 + FSLattice.lsq (dsum e S)) * f' S ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := cubeImg n)) (fun T _ hT => by
      simp only [hf', if_neg hT]; ring)]
    exact Finset.sum_congr rfl fun S hS => by simp only [hf', if_pos hS]
  rw [hout]
  refine le_trans ?_ (dir_hardy Hunit hPeriodic k he c F f' hf'0)
  rw [sum_cube_eq (fun R => (∑ S ∈ X, chMaj k c R S * f S) ^ 2)]
  simp_rw [hin]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
    (fun _ _ _ => sq_nonneg _)

/-- The weighted Schur step for `σ_l` from the cube: with `d · ℓ_l = 1`,
`Σ_{S ∈ X} |Σ_P σ_l(S,P) v_P|² ≤ α_l A_l Σ_P Λ_d(P)² |v_P|²`. -/
lemma wschur_sig_cube (hL : 0 < L) (hn : 2 ≤ n) (l : Ch eta) {d : Fin eta → ℤ} (hdl : dl d l = 1)
    (hd1 : l1 d ≤ 2) (X : Finset (Cf eta)) (v : Cfg eta n → ℂ) :
    ∑ S ∈ X, ‖∑ P : Cfg eta n, lcp l (sigK sys L n) S (cidx n P) * v P‖ ^ 2 ≤
      alS sys L n l * Asj sys L n l *
        ∑ P : Cfg eta n, ‖(lam d (cidx n P) : ℂ) * v P‖ ^ 2 := by
  have h := FSLattice.wschur X Finset.univ
    (fun S P => lcp l (sigK sys L n) S (cidx n P) * ((lam d (cidx n P))⁻¹ : ℂ))
    (fun _ => 1) (fun P => (lam d (cidx n P))⁻¹) (fun P _ => inv_pos.mpr (lam_pos _ _))
    (alS_nonneg hL l)
    (fun S _ => by
      have e : ∑ P : Cfg eta n, ‖lcp l (sigK sys L n) S (cidx n P) * ((lam d (cidx n P))⁻¹ : ℂ)‖ *
          (lam d (cidx n P))⁻¹ = ∑ P : Cfg eta n, ‖lcp l (sigK sys L n) S (cidx n P)‖ /
            lam d (cidx n P) ^ 2 := by
        refine Finset.sum_congr rfl fun P _ => ?_
        have hp := lam_pos d (cidx n P)
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        field_simp
      rw [e, mul_one, sum_cube_eq (fun T => ‖lcp l (sigK sys L n) S T‖ / lam d T ^ 2)]
      exact row_sig_lam hL hn l hdl hd1 S _ (fun T hT hne =>
        (cross_right_inP (mem_cubeImg_inP hT) (sig_ne_zero hne).2).2))
    (fun P _ => by
      have hp := lam_pos d (cidx n P)
      have e : ∑ S ∈ X, ‖lcp l (sigK sys L n) S (cidx n P) * ((lam d (cidx n P))⁻¹ : ℂ)‖ * 1 =
          (lam d (cidx n P))⁻¹ * ∑ S ∈ X, ‖lcp l (sigK sys L n) S (cidx n P)‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        ring
      rw [e, mul_comm (Asj sys L n l)]
      exact mul_le_mul_of_nonneg_left (sum_norm_sig_col_le hL hn l _ X) (inv_nonneg.mpr hp.le))
    (fun P => (lam d (cidx n P) : ℂ) * v P)
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 2
  refine Finset.sum_congr rfl fun P _ => ?_
  have hp : (lam d (cidx n P) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lam_pos _ _).ne'
  field_simp

/-! ## The truncated words -/

variable (sys L n) in
/-- The truncated closed word `σ_j w_k σ_l` on the cube. -/
noncomputable def TA (j k l : Ch eta) (N : ℕ) (Q P : Cfg eta n) : ℂ :=
  ∑ x ∈ cbox N ×ˢ cbox N, wdA sys L n j k l (cidx n Q) (cidx n P) x

variable (sys L n) in
/-- The truncated open word `σ_j σ_j w_l` on the cube. -/
noncomputable def TB (j l : Ch eta) (N : ℕ) (Q P : Cfg eta n) : ℂ :=
  ∑ x ∈ cbox N ×ˢ cbox N, wdB sys L n j j l (cidx n Q) (cidx n P) x

variable (sys L n) in
/-- The truncated open word `w_j σ_k σ_k` on the cube. -/
noncomputable def TC (j k : Ch eta) (N : ℕ) (Q P : Cfg eta n) : ℂ :=
  ∑ x ∈ cbox N ×ˢ cbox N, wdC sys L n j k k (cidx n Q) (cidx n P) x

/-- The weight is constant along a hop of a channel with `d · ℓ = 0`: moving it inside. -/
lemma lam_mul_sum_sig {l : Ch eta} {e : Fin eta → ℤ} (hel : dl e l = 0) (S : Cf eta)
    (v : Cfg eta n → ℂ) :
    (lam e S : ℂ) * ∑ P : Cfg eta n, lcp l (sigK sys L n) S (cidx n P) * v P =
      ∑ P : Cfg eta n, lcp l (sigK sys L n) S (cidx n P) * ((lam e (cidx n P) : ℂ) * v P) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  by_cases h0 : lcp l (sigK sys L n) S (cidx n P) = 0
  · rw [h0]; ring
  · rw [lam_onCh_zero hel (sig_ne_zero h0).1]; ring

lemma lam_mul_sum_sig' {l : Ch eta} {e : Fin eta → ℤ} (hel : dl e l = 0) (S : Cf eta)
    (X : Finset (Cf eta)) (v : Cf eta → ℂ) :
    (lam e S : ℂ) * ∑ R ∈ X, lcp l (sigK sys L n) S R * v R =
      ∑ R ∈ X, lcp l (sigK sys L n) S R * ((lam e R : ℂ) * v R) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  by_cases h0 : lcp l (sigK sys L n) S R = 0
  · rw [h0]; ring
  · rw [lam_onCh_zero hel (sig_ne_zero h0).1]; ring

lemma lam_mul_sum_pot {l : Ch eta} {e : Fin eta → ℤ} (hel : dl e l = 0) (S : Cf eta)
    (v : Cfg eta n → ℂ) :
    (lam e S : ℂ) * ∑ P : Cfg eta n, lcp l (potKernel sys L) S (cidx n P) * v P =
      ∑ P : Cfg eta n, lcp l (potKernel sys L) S (cidx n P) * ((lam e (cidx n P) : ℂ) * v P) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  by_cases h0 : OnCh l S (cidx n P)
  · rw [lam_onCh_zero hel h0]; ring
  · rw [lcp_eq_zero h0]; ring

omit [Fintype ν] in
lemma norm_lam_mul_sq (e : Fin eta → ℤ) (S : Cf eta) (z : ℂ) :
    ‖(lam e S : ℂ) * z‖ ^ 2 = (1 + FSLattice.lsq (dsum e S)) * ‖z‖ ^ 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lam_pos _ _), mul_pow, lam_sq]

omit [Fintype ν] in
lemma norm_dg2_sq (d e : Fin eta → ℤ) (u : En eta n) :
    ‖FSKernel.dg (fun q => (lam e (cidx n q) : ℂ)) (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)‖ ^ 2
      = ∑ P : Cfg eta n, ‖(lam d (cidx n P) : ℂ) * ((lam e (cidx n P) : ℂ) * u.ofLp P)‖ ^ 2 := by
  rw [FSKernel.norm_sq_eq]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [FSKernel.dg_apply, FSKernel.dg_apply]
  congr 1; ring_nf

/-- **The closed multi-channel words** (`k ≠ l`, eq:closedzero excluded):
`‖A_N u‖ ≤ A_j c_k |H| √(α_l A_l) c_Λ ‖(1 + A) u‖`. -/
theorem norm_TA_le (hL : 0 < L) (hn : 2 ≤ n) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (j : Ch eta) {k l : Ch eta}
    (hkl : k ≠ l) (N : ℕ) (u : En eta n) :
    ‖FSKernel.kop (TA sys L n j k l N) u‖ ≤
      Asj sys L n j * (chC sys L k * |Hunit|) * Real.sqrt (alS sys L n l * Asj sys L n l) *
        cLam sys L * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
  classical
  obtain ⟨e, hek, hel, he1⟩ := exists_dir k l hkl
  obtain ⟨d, hdl, -, hd1⟩ := exists_dir l k (Ne.symm hkl)
  have hrep : ∀ Q, (FSKernel.kop (TA sys L n j k l N) u).ofLp Q =
      ∑ R ∈ cbox N, lcp j (sigK sys L n) (cidx n Q) R *
        ∑ S ∈ cbox N, lcp k (potKernel sys L) R S *
          ∑ P : Cfg eta n, lcp l (sigK sys L n) S (cidx n P) * u.ofLp P := by
    intro Q
    rw [FSKernel.kop_apply]
    simp only [TA, wdA, Finset.sum_product, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun P _ => ?_
    ring
  set B := cbox (eta := eta) N
  set f : Cf eta → ℂ := fun S => ∑ P : Cfg eta n, lcp l (sigK sys L n) S (cidx n P) * u.ofLp P
    with hf
  set g : Cf eta → ℂ := fun R => ∑ S ∈ B, lcp k (potKernel sys L) R S * f S with hg
  have h1 : ‖FSKernel.kop (TA sys L n j k l N) u‖ ^ 2 ≤
      Asj sys L n j * Asj sys L n j * ∑ R ∈ B, ‖g R‖ ^ 2 := by
    rw [FSKernel.norm_sq_eq]
    simp_rw [hrep]
    exact FSLattice.wschur Finset.univ B (fun Q R => lcp j (sigK sys L n) (cidx n Q) R)
      (fun _ => 1) (fun _ => 1) (fun _ _ => one_pos) (Asj_nonneg hL j)
      (fun Q _ => by simp only [mul_one]; exact sum_norm_sig_row_le hL hn j _ B)
      (fun R _ => by simp only [mul_one]; exact sum_norm_sig_col_cube_le hL hn j R) g
  have h2 : ∑ R ∈ B, ‖g R‖ ^ 2 ≤ chC sys L k ^ 2 * Hunit ^ 2 *
      ∑ S ∈ B, (1 + FSLattice.lsq (dsum e S)) * ‖f S‖ ^ 2 := by
    refine le_trans ?_ (dir_hardy Hunit hPeriodic k hek (chC sys L k) B (fun S => ‖f S‖)
      (fun _ => norm_nonneg _))
    refine Finset.sum_le_sum fun R _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simp only [hg]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun S _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_lcp_pot_le hL k R S) (norm_nonneg _)
  have h3 : ∑ S ∈ B, (1 + FSLattice.lsq (dsum e S)) * ‖f S‖ ^ 2 ≤
      alS sys L n l * Asj sys L n l * ‖FSKernel.dg (fun q => (lam e (cidx n q) : ℂ))
        (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)‖ ^ 2 := by
    have e1 : ∀ S, (1 + FSLattice.lsq (dsum e S)) * ‖f S‖ ^ 2 =
        ‖∑ P : Cfg eta n, lcp l (sigK sys L n) S (cidx n P) *
          ((lam e (cidx n P) : ℂ) * u.ofLp P)‖ ^ 2 := by
      intro S
      rw [← norm_lam_mul_sq e S (f S)]
      simp only [hf]
      rw [lam_mul_sum_sig hel S (fun P => u.ofLp P)]
    simp_rw [e1]
    refine (wschur_sig_cube hL hn l hdl hd1 B _).trans (le_of_eq ?_)
    rw [norm_dg2_sq]
  have hD := norm_lam2_le (sys := sys) hL hd1 he1 u
  set D := ‖FSKernel.dg (fun q => (lam e (cidx n q) : ℂ))
    (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)‖
  set W := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖
  have hα := alS_nonneg (sys := sys) (n := n) hL l
  have hAl := Asj_nonneg (sys := sys) (n := n) hL l
  have hAj := Asj_nonneg (sys := sys) (n := n) hL j
  have hck := chC_nonneg sys hL k
  have hsq : Real.sqrt (alS sys L n l * Asj sys L n l) ^ 2 = alS sys L n l * Asj sys L n l :=
    Real.sq_sqrt (mul_nonneg hα hAl)
  have hfin : ‖FSKernel.kop (TA sys L n j k l N) u‖ ^ 2 ≤
      (Asj sys L n j * (chC sys L k * |Hunit|) * Real.sqrt (alS sys L n l * Asj sys L n l) * D) ^ 2 := by
    calc ‖FSKernel.kop (TA sys L n j k l N) u‖ ^ 2
        ≤ Asj sys L n j * Asj sys L n j * ∑ R ∈ B, ‖g R‖ ^ 2 := h1
      _ ≤ Asj sys L n j * Asj sys L n j * (chC sys L k ^ 2 * Hunit ^ 2 *
            (alS sys L n l * Asj sys L n l * D ^ 2)) := by
          apply mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
          positivity
      _ = _ := by rw [mul_pow, mul_pow, mul_pow, mul_pow, hsq, sq_abs]; ring
  have hfin' := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hfin
  calc ‖FSKernel.kop (TA sys L n j k l N) u‖
      ≤ Asj sys L n j * (chC sys L k * |Hunit|) * Real.sqrt (alS sys L n l * Asj sys L n l) * D := hfin'
    _ ≤ Asj sys L n j * (chC sys L k * |Hunit|) * Real.sqrt (alS sys L n l * Asj sys L n l) *
          (cLam sys L * W) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring

/-- **The open words `S_j^* S_j W_l`** (`j ≠ l`):
`‖B_N u‖ ≤ A_j √(α_j A_j) c_l |H| c_Λ ‖(1 + A) u‖`. -/
theorem norm_TB_le (hL : 0 < L) (hn : 2 ≤ n) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {j l : Ch eta} (hjl : j ≠ l)
    (N : ℕ) (u : En eta n) :
    ‖FSKernel.kop (TB sys L n j l N) u‖ ≤
      Asj sys L n j * Real.sqrt (alS sys L n j * Asj sys L n j) * (chC sys L l * |Hunit|) *
        cLam sys L * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
  classical
  obtain ⟨d, hdj, hdl, hd1⟩ := exists_dir j l hjl
  obtain ⟨e, hel, -, he1⟩ := exists_dir l j (Ne.symm hjl)
  set B := cbox (eta := eta) N
  set Bx := B.filter (fun R => ¬ InP (n : ℝ) R)
  have hrep : ∀ Q, (FSKernel.kop (TB sys L n j l N) u).ofLp Q =
      ∑ R ∈ Bx, lcp j (sigK sys L n) (cidx n Q) R *
        ∑ S ∈ B, lcp j (sigK sys L n) R S *
          ∑ P : Cfg eta n, lcp l (potKernel sys L) S (cidx n P) * u.ofLp P := by
    intro Q
    have h0 : (FSKernel.kop (TB sys L n j l N) u).ofLp Q =
        ∑ R ∈ B, lcp j (sigK sys L n) (cidx n Q) R *
          ∑ S ∈ B, lcp j (sigK sys L n) R S *
            ∑ P : Cfg eta n, lcp l (potKernel sys L) S (cidx n P) * u.ofLp P := by
      rw [FSKernel.kop_apply]
      simp only [TB, wdB, Finset.sum_product, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun R _ => ?_
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun P _ => ?_
      ring
    rw [h0, Finset.sum_filter]
    refine Finset.sum_congr rfl fun R _ => ?_
    by_cases hR : InP (n : ℝ) R
    · have h00 : lcp j (sigK sys L n) (cidx n Q) R = 0 := by
        by_contra hne
        exact (cross_left_inP (inP_cidx Q) (sig_ne_zero hne).2).2 hR
      simp [hR, h00]
    · simp [hR]
  set g : Cf eta → ℂ := fun S => ∑ P : Cfg eta n, lcp l (potKernel sys L) S (cidx n P) * u.ofLp P
    with hg
  set m : Cf eta → ℂ := fun R => ∑ S ∈ B, lcp j (sigK sys L n) R S * g S with hm
  have h1 : ‖FSKernel.kop (TB sys L n j l N) u‖ ^ 2 ≤
      Asj sys L n j * Asj sys L n j * ∑ R ∈ Bx, ‖m R‖ ^ 2 := by
    rw [FSKernel.norm_sq_eq]
    simp_rw [hrep]
    exact FSLattice.wschur Finset.univ Bx (fun Q R => lcp j (sigK sys L n) (cidx n Q) R)
      (fun _ => 1) (fun _ => 1) (fun _ _ => one_pos) (Asj_nonneg hL j)
      (fun Q _ => by simp only [mul_one]; exact sum_norm_sig_row_le hL hn j _ Bx)
      (fun R _ => by simp only [mul_one]; exact sum_norm_sig_col_cube_le hL hn j R) m
  have h2 : ∑ R ∈ Bx, ‖m R‖ ^ 2 ≤
      alS sys L n j * Asj sys L n j * ∑ S ∈ B, ‖(lam d S : ℂ) * g S‖ ^ 2 := by
    have h := FSLattice.wschur Bx B (fun R S => lcp j (sigK sys L n) R S * ((lam d S)⁻¹ : ℂ))
      (fun _ => 1) (fun S => (lam d S)⁻¹) (fun S _ => inv_pos.mpr (lam_pos _ _))
      (alS_nonneg hL j)
      (fun R hR => by
        have e : ∑ S ∈ B, ‖lcp j (sigK sys L n) R S * ((lam d S)⁻¹ : ℂ)‖ * (lam d S)⁻¹ =
            ∑ S ∈ B, ‖lcp j (sigK sys L n) R S‖ / lam d S ^ 2 := by
          refine Finset.sum_congr rfl fun S _ => ?_
          have hp := lam_pos d S
          rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
          field_simp
        rw [e, mul_one]
        have hRx := (Finset.mem_filter.mp hR).2
        exact row_sig_lam hL hn j hdj hd1 R B (fun S _ hne =>
          cross_left_out hRx (sig_ne_zero hne).2))
      (fun S _ => by
        have hp := lam_pos d S
        have e : ∑ R ∈ Bx, ‖lcp j (sigK sys L n) R S * ((lam d S)⁻¹ : ℂ)‖ * 1 =
            (lam d S)⁻¹ * ∑ R ∈ Bx, ‖lcp j (sigK sys L n) R S‖ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun R _ => ?_
          rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
          ring
        rw [e, mul_comm (Asj sys L n j)]
        exact mul_le_mul_of_nonneg_left (sum_norm_sig_col_le hL hn j S Bx) (inv_nonneg.mpr hp.le))
      (fun S => (lam d S : ℂ) * g S)
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun R _ => ?_
    congr 2
    refine Finset.sum_congr rfl fun S _ => ?_
    have hp : (lam d S : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lam_pos _ _).ne'
    field_simp
  have h3 : ∑ S ∈ B, ‖(lam d S : ℂ) * g S‖ ^ 2 ≤ chC sys L l ^ 2 * Hunit ^ 2 *
      ‖FSKernel.dg (fun q => (lam e (cidx n q) : ℂ))
        (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)‖ ^ 2 := by
    have e1 : ∀ S, (lam d S : ℂ) * g S = ∑ P : Cfg eta n, lcp l (potKernel sys L) S (cidx n P) *
        ((lam d (cidx n P) : ℂ) * u.ofLp P) := fun S => by
      simp only [hg]; exact lam_mul_sum_pot hdl S (fun P => u.ofLp P)
    simp_rw [e1]
    have hH := hardy_cube_in Hunit hPeriodic l hel (chC sys L l) B
      (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)
    refine le_trans ?_ (hH.trans (le_of_eq ?_))
    · refine Finset.sum_le_sum fun S _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun P _ => ?_)
      rw [norm_mul, FSKernel.dg_apply]
      exact mul_le_mul_of_nonneg_right (norm_lcp_pot_le hL l S _) (norm_nonneg _)
    · rw [norm_dg2_sq]
      congr 1
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [FSKernel.dg_apply, mul_comm (lam d (cidx n P) : ℂ), ← norm_lam_mul_sq e (cidx n P)]
      congr 1; ring_nf
  have hD := norm_lam2_le (sys := sys) hL hd1 he1 u
  set D := ‖FSKernel.dg (fun q => (lam e (cidx n q) : ℂ))
    (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)‖
  set W := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖
  have hα := alS_nonneg (sys := sys) (n := n) hL j
  have hAj := Asj_nonneg (sys := sys) (n := n) hL j
  have hcl := chC_nonneg sys hL l
  have hsq : Real.sqrt (alS sys L n j * Asj sys L n j) ^ 2 = alS sys L n j * Asj sys L n j :=
    Real.sq_sqrt (mul_nonneg hα hAj)
  have hfin : ‖FSKernel.kop (TB sys L n j l N) u‖ ^ 2 ≤
      (Asj sys L n j * Real.sqrt (alS sys L n j * Asj sys L n j) * (chC sys L l * |Hunit|) * D) ^ 2 := by
    calc ‖FSKernel.kop (TB sys L n j l N) u‖ ^ 2
        ≤ Asj sys L n j * Asj sys L n j * ∑ R ∈ Bx, ‖m R‖ ^ 2 := h1
      _ ≤ Asj sys L n j * Asj sys L n j * (alS sys L n j * Asj sys L n j *
            (chC sys L l ^ 2 * Hunit ^ 2 * D ^ 2)) := by
          apply mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
          positivity
      _ = _ := by rw [mul_pow, mul_pow, mul_pow, mul_pow, hsq, sq_abs]; ring
  have hfin' := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hfin
  calc ‖FSKernel.kop (TB sys L n j l N) u‖
      ≤ Asj sys L n j * Real.sqrt (alS sys L n j * Asj sys L n j) * (chC sys L l * |Hunit|) * D := hfin'
    _ ≤ Asj sys L n j * Real.sqrt (alS sys L n j * Asj sys L n j) * (chC sys L l * |Hunit|) *
          (cLam sys L * W) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring

/-- **The open words `W_j S_k^* S_k`** (`j ≠ k`):
`‖C_N u‖ ≤ c_j |H| A_k √(α_k A_k) c_Λ ‖(1 + A) u‖`. -/
theorem norm_TC_le (hL : 0 < L) (hn : 2 ≤ n) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {j k : Ch eta} (hjk : j ≠ k)
    (N : ℕ) (u : En eta n) :
    ‖FSKernel.kop (TC sys L n j k N) u‖ ≤
      chC sys L j * |Hunit| * Asj sys L n k * Real.sqrt (alS sys L n k * Asj sys L n k) *
        cLam sys L * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
  classical
  obtain ⟨e, hej, hek, he1⟩ := exists_dir j k hjk
  obtain ⟨d, hdk, -, hd1⟩ := exists_dir k j (Ne.symm hjk)
  set B := cbox (eta := eta) N
  have hrep : ∀ Q, (FSKernel.kop (TC sys L n j k N) u).ofLp Q =
      ∑ S ∈ B, lcp j (potKernel sys L) (cidx n Q) S *
        ∑ R ∈ B, lcp k (sigK sys L n) S R *
          ∑ P : Cfg eta n, lcp k (sigK sys L n) R (cidx n P) * u.ofLp P := by
    intro Q
    rw [FSKernel.kop_apply]
    simp only [TC, wdC, Finset.sum_product, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun P _ => ?_
    ring
  set f : Cf eta → ℂ := fun R => ∑ P : Cfg eta n, lcp k (sigK sys L n) R (cidx n P) * u.ofLp P
    with hf
  set m : Cf eta → ℂ := fun S => ∑ R ∈ B, lcp k (sigK sys L n) S R * f R with hm
  have h1 : ‖FSKernel.kop (TC sys L n j k N) u‖ ^ 2 ≤
      chC sys L j ^ 2 * Hunit ^ 2 * ∑ S ∈ B, (1 + FSLattice.lsq (dsum e S)) * ‖m S‖ ^ 2 := by
    rw [FSKernel.norm_sq_eq]
    simp_rw [hrep]
    refine le_trans ?_ (hardy_cube_out (n := n) Hunit hPeriodic j hej (chC sys L j) B
      (fun S => ‖m S‖) (fun _ => norm_nonneg _))
    refine Finset.sum_le_sum fun Q _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun S _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_lcp_pot_le hL j _ S) (norm_nonneg _)
  have h2 : ∑ S ∈ B, (1 + FSLattice.lsq (dsum e S)) * ‖m S‖ ^ 2 ≤
      Asj sys L n k * Asj sys L n k * ∑ R ∈ B, ‖(lam e R : ℂ) * f R‖ ^ 2 := by
    have e1 : ∀ S, (1 + FSLattice.lsq (dsum e S)) * ‖m S‖ ^ 2 =
        ‖∑ R ∈ B, lcp k (sigK sys L n) S R * ((lam e R : ℂ) * f R)‖ ^ 2 := by
      intro S
      rw [← norm_lam_mul_sq e S (m S)]
      simp only [hm]
      rw [lam_mul_sum_sig' hek S B f]
    simp_rw [e1]
    exact FSLattice.wschur B B (fun S R => lcp k (sigK sys L n) S R)
      (fun _ => 1) (fun _ => 1) (fun _ _ => one_pos) (Asj_nonneg hL k)
      (fun S _ => by simp only [mul_one]; exact sum_norm_sig_row_le hL hn k S B)
      (fun R _ => by simp only [mul_one]; exact sum_norm_sig_col_le hL hn k R B)
      (fun R => (lam e R : ℂ) * f R)
  have h3 : ∑ R ∈ B, ‖(lam e R : ℂ) * f R‖ ^ 2 ≤ alS sys L n k * Asj sys L n k *
      ‖FSKernel.dg (fun q => (lam e (cidx n q) : ℂ))
        (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)‖ ^ 2 := by
    have e1 : ∀ R, (lam e R : ℂ) * f R = ∑ P : Cfg eta n, lcp k (sigK sys L n) R (cidx n P) *
        ((lam e (cidx n P) : ℂ) * u.ofLp P) := fun R => by
      simp only [hf]; exact lam_mul_sum_sig hek R (fun P => u.ofLp P)
    simp_rw [e1]
    refine (wschur_sig_cube hL hn k hdk hd1 B _).trans (le_of_eq ?_)
    rw [norm_dg2_sq]
  have hD := norm_lam2_le (sys := sys) hL hd1 he1 u
  set D := ‖FSKernel.dg (fun q => (lam e (cidx n q) : ℂ))
    (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)‖
  set W := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖
  have hα := alS_nonneg (sys := sys) (n := n) hL k
  have hAk := Asj_nonneg (sys := sys) (n := n) hL k
  have hcj := chC_nonneg sys hL j
  have hsq : Real.sqrt (alS sys L n k * Asj sys L n k) ^ 2 = alS sys L n k * Asj sys L n k :=
    Real.sq_sqrt (mul_nonneg hα hAk)
  have hfin : ‖FSKernel.kop (TC sys L n j k N) u‖ ^ 2 ≤
      (chC sys L j * |Hunit| * Asj sys L n k * Real.sqrt (alS sys L n k * Asj sys L n k) * D) ^ 2 := by
    calc ‖FSKernel.kop (TC sys L n j k N) u‖ ^ 2
        ≤ chC sys L j ^ 2 * Hunit ^ 2 * ∑ S ∈ B, (1 + FSLattice.lsq (dsum e S)) * ‖m S‖ ^ 2 := h1
      _ ≤ chC sys L j ^ 2 * Hunit ^ 2 * (Asj sys L n k * Asj sys L n k *
            (alS sys L n k * Asj sys L n k * D ^ 2)) := by
          apply mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
          positivity
      _ = _ := by rw [mul_pow, mul_pow, mul_pow, mul_pow, hsq, sq_abs]; ring
  have hfin' := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hfin
  calc ‖FSKernel.kop (TC sys L n j k N) u‖
      ≤ chC sys L j * |Hunit| * Asj sys L n k * Real.sqrt (alS sys L n k * Asj sys L n k) * D :=
        hfin'
    _ ≤ chC sys L j * |Hunit| * Asj sys L n k * Real.sqrt (alS sys L n k * Asj sys L n k) *
          (cLam sys L * W) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring

/-! ## The multi-channel words on the cube -/

variable (sys L n) in
/-- The per-word constant. -/
noncomputable def bW (Hunit : ℝ) (j k l : Ch eta) : ℝ :=
  (Asj sys L n j * (chC sys L k * |Hunit|) * Real.sqrt (alS sys L n l * Asj sys L n l) +
    Asj sys L n j * Real.sqrt (alS sys L n j * Asj sys L n j) * (chC sys L l * |Hunit|) +
    chC sys L j * |Hunit| * Asj sys L n k * Real.sqrt (alS sys L n k * Asj sys L n k)) *
  cLam sys L

lemma bW_terms_nonneg (hL : 0 < L) (Hunit : ℝ) (j k l : Ch eta) :
    0 ≤ Asj sys L n j * (chC sys L k * |Hunit|) * Real.sqrt (alS sys L n l * Asj sys L n l) ∧
    0 ≤ Asj sys L n j * Real.sqrt (alS sys L n j * Asj sys L n j) * (chC sys L l * |Hunit|) ∧
    0 ≤ chC sys L j * |Hunit| * Asj sys L n k * Real.sqrt (alS sys L n k * Asj sys L n k) := by
  have := Asj_nonneg (sys := sys) (n := n) hL j
  have := Asj_nonneg (sys := sys) (n := n) hL k
  have := chC_nonneg sys hL j
  have := chC_nonneg sys hL k
  have := chC_nonneg sys hL l
  refine ⟨by positivity, by positivity, by positivity⟩

lemma kop_tsum_zero {f : Cfg eta n → Cfg eta n → Cf eta × Cf eta → ℂ}
    (h : ∀ Q P x, f Q P x = 0) (u : En eta n) :
    FSKernel.kop (fun Q P => ∑' x, f Q P x) u = 0 := by
  ext Q
  simp [h]

/-- **One multi-channel word** (`prop:mp`): for `(j, k, l)` not all equal,
`‖h3fW_{jkl} u‖ ≤ b_W ‖(1 + A) u‖`. -/
theorem norm_word_le (hL : 0 < L) (hn : 2 ≤ n) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (j k l : Ch eta)
    (hjkl : ¬ (j = k ∧ k = l)) (u : En eta n) :
    ‖FSKernel.kop (fun Q P => h3fW sys L n j k l (cidx n Q) (cidx n P)) u‖ ≤
      bW sys L n Hunit j k l * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
  classical
  set W := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖
  have hW : 0 ≤ W := norm_nonneg _
  obtain ⟨t1, t2, t3⟩ := bW_terms_nonneg (sys := sys) (n := n) hL Hunit j k l
  have hcl := cLam_pos (sys := sys) L
  set KA : Cfg eta n → Cfg eta n → ℂ := fun Q P => ∑' x, wdA sys L n j k l (cidx n Q) (cidx n P) x
  set KB : Cfg eta n → Cfg eta n → ℂ := fun Q P => ∑' x, wdB sys L n j k l (cidx n Q) (cidx n P) x
  set KC : Cfg eta n → Cfg eta n → ℂ := fun Q P => ∑' x, wdC sys L n j k l (cidx n Q) (cidx n P) x
  have hsplit : FSKernel.kop (fun Q P => h3fW sys L n j k l (cidx n Q) (cidx n P)) u =
      -FSKernel.kop KA u + (1 / 2 : ℂ) • FSKernel.kop KB u + (1 / 2 : ℂ) • FSKernel.kop KC u := by
    ext Q
    simp only [FSKernel.kop_apply, h3fW_eq hL hn, WithLp.ofLp_add, WithLp.ofLp_neg,
      WithLp.ofLp_smul, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, KA, KB, KC]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun P _ => ?_
    ring
  -- the closed word
  have hA : ‖FSKernel.kop KA u‖ ≤ Asj sys L n j * (chC sys L k * |Hunit|) *
      Real.sqrt (alS sys L n l * Asj sys L n l) * cLam sys L * W := by
    by_cases hkl : k = l
    · subst hkl
      have hjk : j ≠ k := fun h => hjkl ⟨h, rfl⟩
      rw [kop_tsum_zero (fun Q P x => fA_eq_zero hjk (inP_cidx Q) (inP_cidx P) x), norm_zero]
      positivity
    · exact norm_kop_le_of_tendsto KA (TA sys L n j k l)
        (fun Q P => tendsto_pair_sum (summable_wdA hL hn j k l _ _)) u
        (fun N => norm_TA_le hL hn Hunit hPeriodic j hkl N u)
  have hB : ‖FSKernel.kop KB u‖ ≤ Asj sys L n j * Real.sqrt (alS sys L n j * Asj sys L n j) *
      (chC sys L l * |Hunit|) * cLam sys L * W := by
    by_cases hjk : j = k
    · subst hjk
      have hjl : j ≠ l := fun h => hjkl ⟨rfl, h⟩
      exact norm_kop_le_of_tendsto KB (TB sys L n j l)
        (fun Q P => tendsto_pair_sum (summable_wdB hL hn j j l _ _)) u
        (fun N => norm_TB_le hL hn Hunit hPeriodic hjl N u)
    · rw [kop_tsum_zero (fun Q P x => fB_eq_zero hjk l (inP_cidx Q) x), norm_zero]
      positivity
  have hC : ‖FSKernel.kop KC u‖ ≤ chC sys L j * |Hunit| * Asj sys L n k *
      Real.sqrt (alS sys L n k * Asj sys L n k) * cLam sys L * W := by
    by_cases hkl : k = l
    · subst hkl
      have hjk : j ≠ k := fun h => hjkl ⟨h, rfl⟩
      exact norm_kop_le_of_tendsto KC (TC sys L n j k)
        (fun Q P => tendsto_pair_sum (summable_wdC hL hn j k k _ _)) u
        (fun N => norm_TC_le hL hn Hunit hPeriodic hjk N u)
    · rw [kop_tsum_zero (fun Q P x => fC_eq_zero j hkl (inP_cidx P) x), norm_zero]
      positivity
  rw [hsplit]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  calc ‖-FSKernel.kop KA u + (1 / 2 : ℂ) • FSKernel.kop KB u + (1 / 2 : ℂ) • FSKernel.kop KC u‖
      ≤ ‖FSKernel.kop KA u‖ + 1 / 2 * ‖FSKernel.kop KB u‖ + 1 / 2 * ‖FSKernel.kop KC u‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          (le_of_eq (norm_neg _)) (le_of_eq ?_))) (le_of_eq ?_))
        · rw [norm_smul, hhalf]
        · rw [norm_smul, hhalf]
    _ ≤ Asj sys L n j * (chC sys L k * |Hunit|) * Real.sqrt (alS sys L n l * Asj sys L n l) *
          cLam sys L * W +
        1 / 2 * (Asj sys L n j * Real.sqrt (alS sys L n j * Asj sys L n j) *
          (chC sys L l * |Hunit|) * cLam sys L * W) +
        1 / 2 * (chC sys L j * |Hunit| * Asj sys L n k *
          Real.sqrt (alS sys L n k * Asj sys L n k) * cLam sys L * W) := by
        gcongr
    _ ≤ bW sys L n Hunit j k l * W := by
        unfold bW
        have h1 : 0 ≤ Asj sys L n j * Real.sqrt (alS sys L n j * Asj sys L n j) *
            (chC sys L l * |Hunit|) * cLam sys L * W := by positivity
        have h2 : 0 ≤ chC sys L j * |Hunit| * Asj sys L n k *
            Real.sqrt (alS sys L n k * Asj sys L n k) * cLam sys L * W := by positivity
        nlinarith

variable (sys L n) in
/-- The kernel of the multi-channel words of `P H^{(3)} P`. -/
noncomputable def wordK (Q P : Cfg eta n) : ℂ :=
  ∑ j, ∑ k, ∑ l, if j = k ∧ k = l then 0 else h3fW sys L n j k l (cidx n Q) (cidx n P)

variable (sys L n) in
/-- `C_Y(n) = Σ_{j,k,l} b_W(j,k,l)`. -/
noncomputable def kcCY (Hunit : ℝ) : ℝ := ∑ j : Ch eta, ∑ k : Ch eta, ∑ l : Ch eta, bW sys L n Hunit j k l

omit [Fintype ν] in
lemma kop_sum3 {ι : Type*} [Fintype ι] (F : ι → ι → ι → Cfg eta n → Cfg eta n → ℂ)
    (u : En eta n) :
    FSKernel.kop (fun q p => ∑ j, ∑ k, ∑ l, F j k l q p) u =
      ∑ j, ∑ k, ∑ l, FSKernel.kop (F j k l) u := by
  ext q
  simp only [FSKernel.kop_apply, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

/-- **The multi-channel words of `P H^{(3)} P`**: `‖Σ_{(j,k,l) not all equal} h3fW u‖ ≤
C_Y(n) ‖(1 + A) u‖`. -/
theorem norm_wordK_le (hL : 0 < L) (hn : 2 ≤ n) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (u : En eta n) :
    ‖FSKernel.kop (wordK sys L n) u‖ ≤
      kcCY sys L n Hunit * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
  classical
  have e := kop_sum3 (fun j k l Q P => if j = k ∧ k = l then (0 : ℂ) else
    h3fW sys L n j k l (cidx n Q) (cidx n P)) u
  rw [show wordK sys L n = fun q p => ∑ j, ∑ k, ∑ l, (if j = k ∧ k = l then (0 : ℂ) else
    h3fW sys L n j k l (cidx n q) (cidx n p)) from rfl, e]
  unfold kcCY
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  by_cases h : j = k ∧ k = l
  · have h0 : FSKernel.kop (fun Q P => if j = k ∧ k = l then (0 : ℂ) else
        h3fW sys L n j k l (cidx n Q) (cidx n P)) u = 0 := by
      ext Q; simp [h]
    rw [h0, norm_zero]
    obtain ⟨t1, t2, t3⟩ := bW_terms_nonneg (sys := sys) (n := n) hL Hunit j k l
    have := cLam_pos (sys := sys) L
    unfold bW
    positivity
  · have h0 : (fun Q P => if j = k ∧ k = l then (0 : ℂ) else
        h3fW sys L n j k l (cidx n Q) (cidx n P)) =
        fun Q P => h3fW sys L n j k l (cidx n Q) (cidx n P) := by
      funext Q P; rw [if_neg h]
    rw [h0]
    exact norm_word_le hL hn Hunit hPeriodic j k l h u

/-- **The multi-channel residual** (`prop:mp`, eq:mpbound): `‖H₃^mp u‖ ≤ (C_X(n) + C_Y(n)) ‖(1+A)u‖`. -/
theorem norm_H3mp_le (hL : 0 < L) (hn : 2 ≤ n) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (u : En eta n) :
    ‖H3mp sys L n u‖ ≤
      (kcCX sys L n Hunit + kcCY sys L n Hunit) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
  have e : H3mp sys L n = FSKernel.kop (crossK sys L n) + FSKernel.kop (wordK sys L n) := by
    rw [H3mp, ← FSKernel.kop_add]
    rfl
  rw [e, LinearMap.add_apply, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (norm_crossX_le hL hn Hunit hPeriodic u)
    (norm_wordK_le hL hn Hunit hPeriodic u))

end FSNormal
