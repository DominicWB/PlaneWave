import PlaneWave.SamePair.LatticeCounts

/-!
# Same-pair third order, part 2: the same-channel kernel of `[Σ₂^bb, W_N]`

On the cube `E_n`:

* `wNK` (the kernel of `W_N`, `VN_eq_kop`), `sgK` (the kernel of `Σ₂^bb`), `chPart j κ` (the
  channel-`j` part of a kernel), `kmul` (the kernel of a product), `kop_kmul`;
* `sgK_eq_sum_chPart`, `wNK_eq_sum_chPart`: both kernels are sums of their channel parts (each
  element joins its configurations through a single channel);
* `h3cK j` = the same-channel kernel `Σ_r σ_j(q,r) w_j(r,p) - Σ_r w_j(q,r) σ_j(r,p)` of
  `[Σ₂^bb, W_N]` (both hops on channel `j`), supported on channel-`j` elements (`h3cK_eq_zero`);
* **`norm_h3cK_le`** (eq:h3 for the commutator words, improved): for `q ≠ p` on channel `j` with
  transfer `θ`, `|h₃(q,p)| ≤ C_j n⁻³ (J_n + 2)(log₂⌈|θ|⌉ + 2)/|θ|`, by `h3_core` twice: the word
  `w σ` from the input's drift `c(p)`, the word `σ w` from the output's drift `c(q)` (the dressed
  element reversed, `|E(q) - E(r)| = (g²/2μ)|F_{c(q)}(r - q)|`); `norm_h3cK_diag_le` for `q = p`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Cube kernels -/

section Kernels

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

/-- The kernel of `W_N` on the cube. -/
noncomputable def wNK (q p : Cfg eta n) : ℂ := potKernel sys L (cidx n q) (cidx n p)

/-- The kernel of `Σ₂^bb`. -/
noncomputable def sgK (q p : Cfg eta n) : ℂ := FSKernel.divK (Asym sys L n) (hgapK sys L n) q p

open Classical in
/-- The channel-`j` part of a cube kernel. -/
noncomputable def chPart (j : Ch eta) (κ : Cfg eta n → Cfg eta n → ℂ) (q p : Cfg eta n) : ℂ :=
  if OnCh j (cidx n q) (cidx n p) then κ q p else 0

/-- The kernel of a product of kernel operators. -/
noncomputable def kmul (κ κ' : Cfg eta n → Cfg eta n → ℂ) (q p : Cfg eta n) : ℂ :=
  ∑ r, κ q r * κ' r p

/-- **The same-channel kernel of `[Σ₂^bb, W_N]`** on channel `j`. -/
noncomputable def h3cK (j : Ch eta) (q p : Cfg eta n) : ℂ :=
  kmul n (chPart n j (sgK sys L n)) (chPart n j (wNK sys L n)) q p -
    kmul n (chPart n j (wNK sys L n)) (chPart n j (sgK sys L n)) q p

variable {n}

omit [Fintype ν] in
lemma kop_kmul (κ κ' : Cfg eta n → Cfg eta n → ℂ) :
    FSKernel.kop κ ∘ₗ FSKernel.kop κ' = FSKernel.kop (kmul n κ κ') := by
  ext u q
  simp only [LinearMap.coe_comp, Function.comp_apply, FSKernel.kop_apply, kmul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  ring

end Kernels

/-! ## The two kernels channel by channel -/

section Channels

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

/-- The potential kernel on a channel-`j` element: `|w(k, k')| ≤ c_j/|k_a - k'_a|²`. -/
lemma norm_potKernel_onCh_le (hL : 0 < L) {j : Ch eta} {k k' : Cf eta} (hj : OnCh j k k') :
    ‖potKernel sys L k k'‖ ≤ chC sys L j / FSLattice.lsq (k (lead j) - k' (lead j)) := by
  classical
  refine (norm_potKernel_le sys hL k k').trans (le_of_eq ?_)
  unfold potMaj
  by_cases hkk : k = k'
  · subst hkk
    rw [sub_self, FSLattice.lsq_zero, div_zero]
    refine Finset.sum_eq_zero fun j' _ => ?_
    unfold chMaj
    split_ifs
    · rw [sub_self]; simp [latticeNormSq]
    · rfl
  · rw [Finset.sum_eq_single j]
    · unfold chMaj; rw [if_pos hj]; rfl
    · intro j' _ hj'
      unfold chMaj
      rw [if_neg]
      intro h
      exact hj' (onCh_unique h hj hkk)
    · intro h; exact absurd (Finset.mem_univ j) h

lemma norm_sgK_le (hL : 0 < L) (hn : 2 ≤ n) (q p : Cfg eta n) :
    ‖sgK sys L n q p‖ ≤ chbT sys L / (n : ℝ) ^ 3 * (1 / |Asym sys L n q - Asym sys L n p|) := by
  unfold sgK FSKernel.divK
  have hcb := chbT_nonneg (sys := sys) hL
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  by_cases hd : Asym sys L n q = Asym sys L n p
  · rw [if_pos hd, norm_zero]; positivity
  rw [if_neg hd, norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_one_div]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  unfold hgapK
  split_ifs
  · exact norm_hbC_le hL hn q p
  · rw [norm_zero]; positivity

lemma sgK_ne_zero {q p : Cfg eta n} (h : sgK sys L n q p ≠ 0) :
    gapC sys L n q p ∧ InQ (n : ℝ) (cidx n q) ∧ InQ (n : ℝ) (cidx n p) := by
  unfold sgK FSKernel.divK at h
  split_ifs at h with hd
  · exact absurd rfl h
  unfold hgapK at h
  split_ifs at h with hg
  · refine ⟨hg, ?_⟩
    by_contra hQ
    exact (div_ne_zero_iff.mp h).1 (hbC_eq_zero_of_not_inQ hQ)
  · rw [zero_div] at h; exact absurd rfl h

omit [Fintype ν] in
/-- On a gapped channel-`j` element the mismatch polynomial lies above the floor `2|θ|`. -/
lemma floor_of_gapC (hL : 0 < L) {j : Ch eta} {q p : Cfg eta n}
    (hj : OnCh j (cidx n q) (cidx n p)) (hg : gapC sys L n q p) :
    2 * FSChannel.rho (chT n j q p) ≤ |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| := by
  obtain ⟨hne, j', hj', hfl⟩ := hg
  have hjj : j' = j := onCh_unique hj' hj (fun h => hne (finiteConfigLatticeIndex_injective eta n h))
  subst hjj
  rw [mismatch_eq (sys := sys) hL hj'] at hfl
  have hgL := gF_pos hL
  have hμ := muCh_pos sys j'
  have e2 : gF L ^ 2 * FSChannel.rho (chT n j' q p) / muCh sys j' =
      gF L ^ 2 / (2 * muCh sys j') * (2 * FSChannel.rho (chT n j' q p)) := by field_simp
  rw [e2] at hfl
  exact le_of_mul_le_mul_left hfl (by positivity)

lemma sgK_self (q : Cfg eta n) : sgK sys L n q q = 0 := by
  unfold sgK FSKernel.divK; rw [if_pos rfl]

lemma lsq_neg (x : Fin 3 → ℤ) : FSLattice.lsq (-x) = FSLattice.lsq x := by
  simp only [FSLattice.lsq, Pi.neg_apply, Int.cast_neg, neg_sq]

omit [Fintype ν] in
lemma chT_comp (j : Ch eta) (q r p : Cfg eta n) : chT n j q r = chT n j q p - chT n j r p := by
  unfold chT; abel

end Channels

/-! ## The kernel bound -/

section Bound

variable (sys : CoulombSystem eta ν) {L : ℝ} {n : ℕ}

/-- The constant of eq:h3 for the commutator words of channel `j`. -/
noncomputable def C3c (L : ℝ) (n : ℕ) (j : Ch eta) : ℝ :=
  chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) * chC sys L j

lemma C3c_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ C3c sys L n j := by
  unfold C3c
  have := chbT_nonneg (sys := sys) hL
  have := muCh_pos sys j
  have := chC_nonneg sys hL j
  have := gF_pos hL
  positivity

variable {sys}

lemma h3cK_eq_zero (j : Ch eta) {q p : Cfg eta n} (h : ¬ OnCh j (cidx n q) (cidx n p)) :
    h3cK sys L n j q p = 0 := by
  classical
  unfold h3cK kmul chPart
  have h1 : ∀ r : Cfg eta n, (if OnCh j (cidx n q) (cidx n r) then sgK sys L n q r else 0) *
      (if OnCh j (cidx n r) (cidx n p) then wNK sys L n r p else 0) = 0 := fun r => by
    split_ifs with ha hb
    · exact absurd (onCh_comp ha hb) h
    all_goals simp
  have h2 : ∀ r : Cfg eta n, (if OnCh j (cidx n q) (cidx n r) then wNK sys L n q r else 0) *
      (if OnCh j (cidx n r) (cidx n p) then sgK sys L n r p else 0) = 0 := fun r => by
    split_ifs with ha hb
    · exact absurd (onCh_comp ha hb) h
    all_goals simp
  simp only [h1, h2, Finset.sum_const_zero, sub_self]

omit [Fintype ν] in
lemma chT_self (j : Ch eta) (q : Cfg eta n) : chT n j q q = 0 := by
  unfold chT; exact sub_self _

/-- The word `w σ`, reduced to a lattice sum: `Σ_r |w_j(q,r)| |σ_j(r,p)| ≤
C₃ Σ_{τ ∈ T} |F_{c(p)}(τ)|⁻¹ |θ - τ|⁻²` over a set `T` of transfers above the floor and below the
cap. -/
lemma sum_w_sg_img (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (q p : Cfg eta n) :
    ∃ T : Finset Lattice3, (∀ τ ∈ T, 1 ≤ FSLattice.lsq τ ∧
        2 * FSChannel.rho τ ≤ |FSLattice.slabF (cCh sys j (cidx n p)) τ| ∧
        |FSLattice.slabF (cCh sys j (cidx n p)) τ| < 2 ^ (Jn sys n + 1) * 2) ∧
      ∑ r, ‖chPart n j (wNK sys L n) q r * chPart n j (sgK sys L n) r p‖ ≤
        C3c sys L n j * ∑ τ ∈ T, 1 / |FSLattice.slabF (cCh sys j (cidx n p)) τ| *
          (1 / FSLattice.lsq (chT n j q p - τ)) := by
  classical
  set θ := chT n j q p
  set c := cCh sys j (cidx n p)
  set R := Finset.univ.filter fun r : Cfg eta n =>
    OnCh j (cidx n r) (cidx n p) ∧ sgK sys L n r p ≠ 0
  refine ⟨R.image fun r => chT n j r p, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hτ
    obtain ⟨-, hrp, hsg⟩ := Finset.mem_filter.mp hr
    obtain ⟨hg, hrQ, hpQ⟩ := sgK_ne_zero hsg
    have hrne : r ≠ p := hg.1
    exact ⟨one_le_lsq_chT hrp hrne, floor_of_gapC hL hrp hg, slabF_cap hL hrp hrQ hpQ⟩
  have hterm : ∀ r, ‖chPart n j (wNK sys L n) q r * chPart n j (sgK sys L n) r p‖ ≤
      if r ∈ R then C3c sys L n j *
        (1 / |FSLattice.slabF c (chT n j r p)| * (1 / FSLattice.lsq (θ - chT n j r p))) else 0 := by
    intro r
    by_cases hr : r ∈ R
    · rw [if_pos hr]
      obtain ⟨-, hrp, hsg⟩ := Finset.mem_filter.mp hr
      unfold chPart
      by_cases hqr : OnCh j (cidx n q) (cidx n r)
      · rw [if_pos hqr, if_pos hrp, norm_mul]
        have hw : ‖wNK sys L n q r‖ ≤ chC sys L j / FSLattice.lsq (θ - chT n j r p) := by
          have := norm_potKernel_onCh_le (sys := sys) hL hqr
          rwa [show cidx n q (lead j) - cidx n r (lead j) = θ - chT n j r p from chT_comp j q r p]
            at this
        have hs := norm_sgK_le (sys := sys) hL hn r p
        rw [mismatch_eq (sys := sys) hL hrp] at hs
        have hμ := muCh_pos sys j
        have hgL := gF_pos hL
        have e : chbT sys L / (n : ℝ) ^ 3 * (1 / (gF L ^ 2 / (2 * muCh sys j) *
            |FSLattice.slabF c (chT n j r p)|)) =
            chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) *
              (1 / |FSLattice.slabF c (chT n j r p)|) := by
          rw [← one_div_mul_one_div, one_div_div]; ring
        rw [e] at hs
        have hcC := chC_nonneg sys hL j
        calc ‖wNK sys L n q r‖ * ‖sgK sys L n r p‖
            ≤ chC sys L j / FSLattice.lsq (θ - chT n j r p) *
                (chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) *
                  (1 / |FSLattice.slabF c (chT n j r p)|)) :=
              mul_le_mul hw hs (norm_nonneg _) (by
                have := FSLattice.lsq_nonneg (θ - chT n j r p); positivity)
          _ = _ := by unfold C3c; ring
      · rw [if_neg hqr, zero_mul, norm_zero]
        have := C3c_nonneg sys (n := n) hL j
        have := FSLattice.lsq_nonneg (θ - chT n j r p)
        positivity
    · rw [if_neg hr]
      unfold chPart
      by_cases hrp : OnCh j (cidx n r) (cidx n p)
      · have hsg : sgK sys L n r p = 0 := by
          by_contra h; exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrp, h⟩)
        rw [if_pos hrp, hsg, mul_zero, norm_zero]
      · rw [if_neg hrp, mul_zero, norm_zero]
  refine (Finset.sum_le_sum fun r _ => hterm r).trans ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (C3c_nonneg sys hL j)
  have hinj : Set.InjOn (fun r => chT n j r p) R := fun r hr r' hr' h =>
    chT_injOn j p (Finset.mem_filter.mp hr).2.1 (Finset.mem_filter.mp hr').2.1 h
  rw [Finset.sum_image (f := fun τ => 1 / |FSLattice.slabF c τ| * (1 / FSLattice.lsq (θ - τ)))
    hinj]

/-- The word `σ w`, reduced to a lattice sum: the dressed element reversed, from the output's drift
`c(q)`, with the transfer `-θ`. -/
lemma sum_sg_w_img (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (q p : Cfg eta n) :
    ∃ T : Finset Lattice3, (∀ τ ∈ T, 1 ≤ FSLattice.lsq τ ∧
        2 * FSChannel.rho τ ≤ |FSLattice.slabF (cCh sys j (cidx n q)) τ| ∧
        |FSLattice.slabF (cCh sys j (cidx n q)) τ| < 2 ^ (Jn sys n + 1) * 2) ∧
      ∑ r, ‖chPart n j (sgK sys L n) q r * chPart n j (wNK sys L n) r p‖ ≤
        C3c sys L n j * ∑ τ ∈ T, 1 / |FSLattice.slabF (cCh sys j (cidx n q)) τ| *
          (1 / FSLattice.lsq (-chT n j q p - τ)) := by
  classical
  set θ := chT n j q p
  set c := cCh sys j (cidx n q)
  set R := Finset.univ.filter fun r : Cfg eta n =>
    OnCh j (cidx n r) (cidx n q) ∧ sgK sys L n q r ≠ 0
  refine ⟨R.image fun r => chT n j r q, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hτ
    obtain ⟨-, hrq, hsg⟩ := Finset.mem_filter.mp hr
    obtain ⟨hg, hqQ, hrQ⟩ := sgK_ne_zero hsg
    have hrne : r ≠ q := fun h => hg.1 h.symm
    exact ⟨one_le_lsq_chT hrq hrne, floor_of_gapC hL hrq (gapC_symm hg), slabF_cap hL hrq hrQ hqQ⟩
  have hterm : ∀ r, ‖chPart n j (sgK sys L n) q r * chPart n j (wNK sys L n) r p‖ ≤
      if r ∈ R then C3c sys L n j *
        (1 / |FSLattice.slabF c (chT n j r q)| * (1 / FSLattice.lsq (-θ - chT n j r q))) else 0 := by
    intro r
    by_cases hr : r ∈ R
    · rw [if_pos hr]
      obtain ⟨-, hrq, hsg⟩ := Finset.mem_filter.mp hr
      unfold chPart
      have hqr : OnCh j (cidx n q) (cidx n r) := onCh_symm hrq
      by_cases hrp : OnCh j (cidx n r) (cidx n p)
      · rw [if_pos hqr, if_pos hrp, norm_mul]
        have hw : ‖wNK sys L n r p‖ ≤ chC sys L j / FSLattice.lsq (-θ - chT n j r q) := by
          have := norm_potKernel_onCh_le (sys := sys) hL hrp
          have e : cidx n r (lead j) - cidx n p (lead j) = -(-θ - chT n j r q) := by
            have h1 : chT n j r q = chT n j r p - θ := chT_comp j r q p
            have h2 : cidx n r (lead j) - cidx n p (lead j) = chT n j r p := rfl
            rw [h2, h1]; abel
          rw [e, lsq_neg] at this
          exact this
        have hs := norm_sgK_le (sys := sys) hL hn q r
        rw [abs_sub_comm, mismatch_eq (sys := sys) hL hrq] at hs
        have hμ := muCh_pos sys j
        have hgL := gF_pos hL
        have e : chbT sys L / (n : ℝ) ^ 3 * (1 / (gF L ^ 2 / (2 * muCh sys j) *
            |FSLattice.slabF c (chT n j r q)|)) =
            chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) *
              (1 / |FSLattice.slabF c (chT n j r q)|) := by
          rw [← one_div_mul_one_div, one_div_div]; ring
        rw [e] at hs
        have hcC := chC_nonneg sys hL j
        calc ‖sgK sys L n q r‖ * ‖wNK sys L n r p‖
            ≤ (chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) *
                  (1 / |FSLattice.slabF c (chT n j r q)|)) *
                (chC sys L j / FSLattice.lsq (-θ - chT n j r q)) :=
              mul_le_mul hs hw (norm_nonneg _) (by
                have := chbT_nonneg (sys := sys) hL; positivity)
          _ = _ := by unfold C3c; ring
      · rw [if_neg hrp, mul_zero, norm_zero]
        have := C3c_nonneg sys (n := n) hL j
        have := FSLattice.lsq_nonneg (-θ - chT n j r q)
        positivity
    · rw [if_neg hr]
      unfold chPart
      by_cases hqr : OnCh j (cidx n q) (cidx n r)
      · have hsg : sgK sys L n q r = 0 := by
          by_contra h; exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, onCh_symm hqr, h⟩)
        rw [if_pos hqr, hsg, zero_mul, norm_zero]
      · rw [if_neg hqr, zero_mul, norm_zero]
  refine (Finset.sum_le_sum fun r _ => hterm r).trans ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (C3c_nonneg sys hL j)
  have hinj : Set.InjOn (fun r => chT n j r q) R := fun r hr r' hr' h =>
    chT_injOn j q (Finset.mem_filter.mp hr).2.1 (Finset.mem_filter.mp hr').2.1 h
  rw [Finset.sum_image (f := fun τ => 1 / |FSLattice.slabF c τ| * (1 / FSLattice.lsq (-θ - τ)))
    hinj]

/-- The word `w σ`: `Σ_r |w_j(q,r)| |σ_j(r,p)| ≤ C₃ C_h3 (J_n + 2)(log₂⌈|θ|⌉ + 2)/|θ|`. -/
lemma sum_w_sg_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) {q p : Cfg eta n}
    (hj : OnCh j (cidx n q) (cidx n p)) (hqp : q ≠ p) :
    ∑ r, ‖chPart n j (wNK sys L n) q r * chPart n j (sgK sys L n) r p‖ ≤
      C3c sys L n j * (FSLattice.Ch3 * (Jn sys n + 2) *
        (Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ + 2) / FSChannel.rho (chT n j q p)) := by
  obtain ⟨T, hT, hle⟩ := sum_w_sg_img (sys := sys) hL hn j q p
  exact hle.trans (mul_le_mul_of_nonneg_left
    (FSLattice.h3_core _ _ (one_le_lsq_chT hj hqp) T hT) (C3c_nonneg sys hL j))

/-- The word `σ w`: the dressed element reversed, from the output's drift `c(q)`. -/
lemma sum_sg_w_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) {q p : Cfg eta n}
    (hj : OnCh j (cidx n q) (cidx n p)) (hqp : q ≠ p) :
    ∑ r, ‖chPart n j (sgK sys L n) q r * chPart n j (wNK sys L n) r p‖ ≤
      C3c sys L n j * (FSLattice.Ch3 * (Jn sys n + 2) *
        (Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ + 2) / FSChannel.rho (chT n j q p)) := by
  obtain ⟨T, hT, hle⟩ := sum_sg_w_img (sys := sys) hL hn j q p
  have hθ : 1 ≤ FSLattice.lsq (-chT n j q p) := by
    rw [lsq_neg]; exact one_le_lsq_chT hj hqp
  have hρ : FSChannel.rho (-chT n j q p) = FSChannel.rho (chT n j q p) := rho_neg' _
  have h := FSLattice.h3_core _ _ hθ T hT
  rw [hρ] at h
  exact hle.trans (mul_le_mul_of_nonneg_left h (C3c_nonneg sys hL j))

/-- **eq:h3 for the commutator words** (improved, review F4 H-1/H-2): for `q ≠ p` joined by
channel `j` with transfer `θ`,
`|h₃(q,p)| ≤ 2 C_j n⁻³ C_h3 (J_n + 2)(log₂⌈|θ|⌉ + 2)/|θ|`. -/
theorem norm_h3cK_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) {q p : Cfg eta n}
    (hj : OnCh j (cidx n q) (cidx n p)) (hqp : q ≠ p) :
    ‖h3cK sys L n j q p‖ ≤ 2 * C3c sys L n j * (FSLattice.Ch3 * (Jn sys n + 2) *
      (Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ + 2) / FSChannel.rho (chT n j q p)) := by
  unfold h3cK kmul
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖∑ r, chPart n j (sgK sys L n) q r * chPart n j (wNK sys L n) r p‖ ≤ _ :=
    (norm_sum_le _ _).trans (sum_sg_w_le hL hn j hj hqp)
  have h2 : ‖∑ r, chPart n j (wNK sys L n) q r * chPart n j (sgK sys L n) r p‖ ≤ _ :=
    (norm_sum_le _ _).trans (sum_w_sg_le hL hn j hj hqp)
  linarith

end Bound

end FSNormal
