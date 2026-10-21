import PlaneWave.Source.BulkRotationSchur

/-!
# Flux/source build, block 5: good-state bounds for the bulk class

* `FSKernel.norm_kop_le_of_maj` (majorants): `‖κ(q,p)‖ ≤ Σ_m κ_m(q,p)` with real `κ_m ≥ 0`
  gives `‖kop κ u‖ ≤ Σ_m ‖kop κ_m |u|‖` (`|u|` the entrywise modulus).  This replaces exact
  decompositions by channels, layers and shells by coverings.
* `regTail_le_good`: for a good state `‖1{|k_a| > l} u‖ ≤ 4M/(1+l)²` (`l ≥ 0`).
* `shell_col_le`, `shell_count_le`: the slab estimates on one dyadic shell, for a fixed input.
* `norm_Sig2bb_good` (the state bound after the text's `‖Σ₂^bb‖` estimate):
  `‖Σ₂^bb u‖ ≤ C_kin M/n³ + C_low M/n³` for `IsGood 1 M u`: the kinetic layers
  `|ω| ≥ g²|θ|²/(8μ)` by Young's inequality on pair fibres (`|σ₂| ≤ C n⁻³ |θ|⁻²`), the low layers by
  the two-sided slab count on dyadic shells and pinning (`lem:pin`) with the good tails.
* `norm_Hres_good` (`lem:res2`): `‖H₂^{bb,res} u‖ ≤ C (log₂ n + 1) M/n³`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSKernel

variable {X : Type*} [Fintype X]

/-- The entrywise modulus of a vector. -/
noncomputable def absv (u : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun p => ((‖u.ofLp p‖ : ℝ) : ℂ))

omit [Fintype X] in
@[simp] lemma absv_apply (u : EuclideanSpace ℂ X) (p : X) :
    (absv u).ofLp p = ((‖u.ofLp p‖ : ℝ) : ℂ) := rfl

lemma norm_absv (u : EuclideanSpace ℂ X) : ‖absv u‖ = ‖u‖ := by
  have h : ‖absv u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_eq, norm_sq_eq]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [absv_apply, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

lemma norm_res_absv (P : X → Prop) (u : EuclideanSpace ℂ X) : ‖res P (absv u)‖ = ‖res P u‖ := by
  classical
  have h : ‖res P (absv u)‖ ^ 2 = ‖res P u‖ ^ 2 := by
    rw [norm_sq_eq, norm_sq_eq]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [res_apply, res_apply]
    split_ifs
    · rw [absv_apply, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    · rfl
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- Coordinatewise domination gives domination of norms. -/
lemma norm_le_of_coord_le {x y : EuclideanSpace ℂ X} (h : ∀ q, ‖x.ofLp q‖ ≤ ‖y.ofLp q‖) :
    ‖x‖ ≤ ‖y‖ := by
  have h2 : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [norm_sq_eq, norm_sq_eq]
    exact Finset.sum_le_sum fun q _ => pow_le_pow_left₀ (norm_nonneg _) (h q) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- **Majorant bound.** If `‖κ(q,p)‖ ≤ Σ_{m ∈ s} κ_m(q,p)` with real `κ_m ≥ 0`, then
`‖kop κ u‖ ≤ Σ_{m ∈ s} ‖kop κ_m |u|‖`. -/
theorem norm_kop_le_of_maj {ι : Type*} (s : Finset ι) (κ : X → X → ℂ) (κs : ι → X → X → ℝ)
    (hκs : ∀ m q p, 0 ≤ κs m q p) (h : ∀ q p, ‖κ q p‖ ≤ ∑ m ∈ s, κs m q p)
    (u : EuclideanSpace ℂ X) :
    ‖kop κ u‖ ≤ ∑ m ∈ s, ‖kop (fun q p => (κs m q p : ℂ)) (absv u)‖ := by
  refine le_trans ?_ (norm_sum_le _ _)
  apply norm_le_of_coord_le
  intro q
  have hy : (∑ m ∈ s, kop (fun q p => (κs m q p : ℂ)) (absv u)).ofLp q =
      ((∑ m ∈ s, ∑ p, ‖u.ofLp p‖ * κs m q p : ℝ) : ℂ) := by
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [kop_apply]
    simp only [absv_apply]
  have hnn : 0 ≤ ∑ m ∈ s, ∑ p, ‖u.ofLp p‖ * κs m q p :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (hκs m q p)
  rw [hy, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn, kop_apply]
  calc ‖∑ p, u.ofLp p * κ q p‖ ≤ ∑ p, ‖u.ofLp p‖ * ‖κ q p‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun p _ => norm_mul _ _
    _ ≤ ∑ p, ‖u.ofLp p‖ * ∑ m ∈ s, κs m q p :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (h q p) (norm_nonneg _)
    _ = ∑ m ∈ s, ∑ p, ‖u.ofLp p‖ * κs m q p := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm

/-- Schur's test for a real nonnegative kernel. -/
theorem norm_kop_real_le (κ : X → X → ℝ) (hκ : ∀ q p, 0 ≤ κ q p) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ q, ∑ p, κ q p ≤ R) (hcol : ∀ p, ∑ q, κ q p ≤ R) (u : EuclideanSpace ℂ X) :
    ‖kop (fun q p => (κ q p : ℂ)) u‖ ≤ R * ‖u‖ := by
  have e : ∀ q p, ‖((κ q p : ℝ) : ℂ)‖ = κ q p := fun q p => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hκ q p)]
  exact norm_kop_le' _ hR (fun q => by simp only [e]; exact hrow q)
    (fun p => by simp only [e]; exact hcol p) u

end FSKernel

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

/-! ## Tails of good states -/

omit [Fintype ν] in
lemma good_nonneg {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) : 0 ≤ M := by
  have := hu.1
  have h1 := norm_nonneg u
  have h2 := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) 1 u)
  linarith

omit [Fintype ν] in
lemma norm_le_good {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) : ‖u‖ ≤ M := by
  have := hu.1
  have h2 := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) 1 u)
  linarith

omit [Fintype ν] in
/-- **Tails of a good state**, uniform form: `‖1{|k_a| > l} u‖ ≤ 4M/(1+l)²` for `l ≥ 0`. -/
lemma regTail_le_good {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) (a : Fin eta) {l : ℝ}
    (hl : 0 ≤ l) : ‖regTail L a l u‖ ≤ 4 * M / (1 + l) ^ 2 := by
  have hM := good_nonneg hu
  have hpos : 0 < (1 + l) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  by_cases h1 : 1 ≤ l
  · have ht := (hu.2 a l h1).1
    rw [one_mul] at ht
    have hl0 : 0 < l := by linarith
    have hr : l ^ (-(5 / 2 : ℝ)) ≤ l ^ (-(2 : ℝ)) := rpow_le_of_le_one h1 (by norm_num)
    have hr2 : l ^ (-(2 : ℝ)) = 1 / l ^ 2 := by
      rw [Real.rpow_neg hl0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        one_div]
    have h3 : ‖regTail L a l u‖ ≤ M * (1 / l ^ 2) := by
      calc ‖regTail L a l u‖ ≤ M * l ^ (-(5 / 2 : ℝ)) := ht
        _ ≤ M * l ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_left hr hM
        _ = M * (1 / l ^ 2) := by rw [hr2]
    have h4 : (1 + l) ^ 2 ≤ 4 * l ^ 2 := by nlinarith
    calc ‖regTail L a l u‖ * (1 + l) ^ 2 ≤ M * (1 / l ^ 2) * (4 * l ^ 2) :=
          mul_le_mul h3 h4 (by positivity) (by positivity)
      _ = 4 * M := by field_simp
  · push Not at h1
    have h3 : ‖regTail L a l u‖ ≤ M := (norm_regTail_le L a l u).trans (norm_le_good hu)
    have h4 : (1 + l) ^ 2 ≤ 4 := by nlinarith
    calc ‖regTail L a l u‖ * (1 + l) ^ 2 ≤ M * 4 :=
          mul_le_mul h3 h4 (by positivity) hM
      _ = 4 * M := by ring

omit [Fintype ν] in
/-- A restriction to configurations with a moved register beyond `l` is controlled by the
register tails. -/
lemma norm_res_pin_le (j : Ch eta) (l : ℝ) (u : En eta n) :
    ‖FSKernel.res (fun p : Cfg eta n => ∃ c ∈ moved j,
        l < finitePlaneWaveKabs (2 * Real.pi / L) n (p c)) u‖ ≤
      ∑ c ∈ moved j, ‖regTail L c l u‖ := by
  classical
  have h2 : ‖FSKernel.res (fun p : Cfg eta n => ∃ c ∈ moved j,
      l < finitePlaneWaveKabs (2 * Real.pi / L) n (p c)) u‖ ^ 2 ≤
      ∑ c ∈ moved j, ‖regTail L c l u‖ ^ 2 := by
    rw [FSKernel.norm_sq_eq]
    simp_rw [norm_sq_regTail]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [FSKernel.res_apply]
    split_ifs with h
    · obtain ⟨c, hc, hlc⟩ := h
      refine le_trans ?_ (Finset.single_le_sum (f := fun c => if l < finitePlaneWaveKabs
        (2 * Real.pi / L) n (p c) then ‖u.ofLp p‖ ^ 2 else 0) (fun c _ => by
          split_ifs
          · exact sq_nonneg _
          · exact le_rfl) hc)
      rw [if_pos hlc]
    · rw [norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact Finset.sum_nonneg fun c _ => by split_ifs
                                            · exact sq_nonneg _
                                            · exact le_rfl
  have h3 := Finset.sum_sq_le_sq_sum_of_nonneg (s := moved j)
    (f := fun c => ‖regTail L c l u‖) (fun c _ => norm_nonneg _)
  have h4 := h2.trans h3
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.sum_nonneg fun c _ => norm_nonneg _)
    two_ne_zero).mp h4

/-! ## The geometric sums -/

lemma sum_two_i_three (N : ℕ) :
    ∑ i ∈ Finset.range N, (2 * (i : ℝ) + 3) * (1 / 2) ^ i = 10 - (4 * N + 10) * (1 / 2) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

lemma sum_two_i_three_le (N : ℕ) : ∑ i ∈ Finset.range N, (2 * (i : ℝ) + 3) * (1 / 2) ^ i ≤ 10 := by
  rw [sum_two_i_three]
  have : 0 ≤ (4 * (N : ℝ) + 10) * (1 / 2) ^ N := by positivity
  linarith

/-! ## One dyadic shell -/

omit [Fintype ν] in
/-- The slab-weighted sum on one dyadic shell, for a fixed input. -/
lemma shell_col_le (hL : 0 < L) (j : Ch eta) (p : Cfg eta n) {i J : ℕ} {F : ℝ} (hF : 0 < F)
    (T : Finset (Cfg eta n))
    (hT : ∀ q ∈ T, OnCh j (cidx n q) (cidx n p) ∧ (4 : ℝ) ^ i ≤ FSLattice.lsq (chT n j q p) ∧
      FSLattice.lsq (chT n j q p) ≤ 4 ^ (i + 1) ∧
      F ≤ |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| ∧
      |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| < 2 ^ (J + 1) * F) :
    ∑ q ∈ T, 1 / |Asym sys L n q - Asym sys L n p| ≤
      2 * muCh sys j / gF L ^ 2 * (11000 * 4 ^ i * (2 / F + 2 * (J + 1) / 2 ^ i)) := by
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have h1 : ∀ q ∈ T, 1 / |Asym sys L n q - Asym sys L n p| = 2 * muCh sys j / gF L ^ 2 *
      (1 / |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)|) := by
    intro q hq
    rw [Asym_hop (hT q hq).1, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j)),
      one_div, mul_inv, inv_div, ← one_div]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun q => chT n j q p) T := fun q hq q' hq' h =>
    chT_injOn j p (hT q hq).1 (hT q' hq').1 h
  rw [← Finset.sum_image (f := fun θ => 1 / |FSLattice.slabF (cCh sys j (cidx n p)) θ|) hinj]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have e4 : ((2 : ℝ) ^ i) ^ 2 = 4 ^ i := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h := FSLattice.slab_inv_sum_le (cCh sys j (cidx n p)) (one_le_pow₀ (by norm_num :
    (1 : ℝ) ≤ 2) (n := i)) hF (J := J) (T.image fun q => chT n j q p) (by
      intro θ hθ
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hθ
      obtain ⟨-, h2, h3, h4, h5⟩ := hT q hq
      refine ⟨by rw [e4]; exact h2, by rw [e4, ← pow_succ']; linarith, h4, h5⟩)
  rw [e4] at h
  exact h

omit [Fintype ν] in
/-- The slab count on one dyadic shell, for a fixed input. -/
lemma shell_count_le (j : Ch eta) (p : Cfg eta n) {i : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (T : Finset (Cfg eta n))
    (hT : ∀ q ∈ T, OnCh j (cidx n q) (cidx n p) ∧ (4 : ℝ) ^ i ≤ FSLattice.lsq (chT n j q p) ∧
      FSLattice.lsq (chT n j q p) ≤ 4 ^ (i + 1) ∧
      |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| ≤ δ) :
    (T.card : ℝ) ≤ 11000 * 4 ^ i * (1 + δ / 2 ^ i) := by
  have hinj : Set.InjOn (fun q => chT n j q p) T := fun q hq q' hq' h =>
    chT_injOn j p (hT q hq).1 (hT q' hq').1 h
  rw [← Finset.card_image_of_injOn hinj]
  have e4 : ((2 : ℝ) ^ i) ^ 2 = 4 ^ i := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h := FSLattice.slab_count (cCh sys j (cidx n p)) (one_le_pow₀ (by norm_num :
    (1 : ℝ) ≤ 2) (n := i)) hδ (T.image fun q => chT n j q p) (by
      intro θ hθ
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hθ
      obtain ⟨-, h2, h3, h4⟩ := hT q hq
      exact ⟨by rw [e4]; exact h2, by rw [e4, ← pow_succ']; linarith, h4⟩)
  rw [e4] at h
  exact h

/-! ## Fibre labels of a channel -/

/-- The fibre label of a channel: the unmoved registers, and the total momentum of a pair. -/
def labC : Ch eta → Cf eta → (Fin eta → Lattice3) × Lattice3
  | .inl a, k => (fun c => if c = a then 0 else k c, 0)
  | .inr pr, k => (fun c => if c = pr.1.1 ∨ c = pr.1.2 then 0 else k c, k pr.1.1 + k pr.1.2)

omit [Fintype ν] in
lemma labC_eq_of_onCh {j : Ch eta} {k k' : Cf eta} (h : OnCh j k k') : labC j k = labC j k' := by
  have e : k = k' + tr j (k (lead j) - k' (lead j)) := h
  cases j with
  | inl a =>
    simp only [labC, Prod.mk.injEq, and_true]
    funext c
    split_ifs with hc
    · rfl
    · rw [e]
      simp [tr, Pi.single_eq_of_ne hc]
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    simp only [labC, Prod.mk.injEq]
    constructor
    · funext c
      split_ifs with hc
      · rfl
      · push Not at hc
        rw [e]
        simp [tr, Pi.single_eq_of_ne hc.1, Pi.single_eq_of_ne hc.2]
    · rw [e]
      simp [tr, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
      abel

omit [Fintype ν] in
lemma eq_of_labC_lead {j : Ch eta} {k k' : Cf eta} (h1 : labC j k = labC j k')
    (h2 : k (lead j) = k' (lead j)) : k = k' := by
  cases j with
  | inl a =>
    simp only [labC, Prod.mk.injEq, and_true] at h1
    funext c
    by_cases hc : c = a
    · subst hc; exact h2
    · have := congrFun h1 c
      simp only [if_neg hc] at this
      exact this
  | inr pr =>
    simp only [labC, Prod.mk.injEq] at h1
    obtain ⟨h1a, h1b⟩ := h1
    simp only [lead] at h2
    funext c
    by_cases hca : c = pr.1.1
    · subst hca; exact h2
    · by_cases hcb : c = pr.1.2
      · subst hcb
        have : k pr.1.1 + k pr.1.2 = k' pr.1.1 + k' pr.1.2 := h1b
        rw [h2] at this
        exact add_left_cancel this
      · have := congrFun h1a c
        simp only [hca, hcb, or_self, if_false] at this
        exact this

/-! ## The kinetic layers: Young's inequality on pair fibres -/

variable (sys L n) in
open Classical in
/-- The majorant of `Σ₂^bb` on the kinetic layers of channel `j`:
`n⁻³ chbT · (8μ_j/g²)/|θ|²` on `|E(q) - E(p)| ≥ g²|θ|²/(8μ_j)`. -/
noncomputable def kinMaj (j : Ch eta) (q p : Cfg eta n) : ℝ :=
  if OnCh j (cidx n q) (cidx n p) ∧ q ≠ p ∧
      gF L ^ 2 * FSLattice.lsq (chT n j q p) / (8 * muCh sys j) ≤ |Asym sys L n q - Asym sys L n p|
  then chbT sys L / (n : ℝ) ^ 3 * (8 * muCh sys j / gF L ^ 2) * (1 / FSLattice.lsq (chT n j q p))
  else 0

lemma kinMaj_nonneg (hL : 0 < L) (j : Ch eta) (q p : Cfg eta n) : 0 ≤ kinMaj sys L n j q p := by
  unfold kinMaj
  have := chbT_nonneg (sys := sys) hL
  have := gF_pos hL
  have := muCh_pos sys j
  split_ifs
  · have := FSLattice.lsq_nonneg (chT n j q p); positivity
  · exact le_rfl

/-- **The kinetic layers**: `‖kop κ_kin |u|‖ ≤ n⁻³ chbT (8μ_j/g²) 2 Z₂ c_E Θ(u)`. -/
theorem norm_kin_le (hL : 0 < L) (j : Ch eta) (u : En eta n) :
    ‖FSKernel.kop (fun q p => (kinMaj sys L n j q p : ℂ)) (FSKernel.absv u)‖ ≤
      chbT sys L / (n : ℝ) ^ 3 * (8 * muCh sys j / gF L ^ 2) * (2 * FSChannel.Zs 2) * cE sys L *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
  classical
  set c0 := chbT sys L / (n : ℝ) ^ 3 * (8 * muCh sys j / gF L ^ 2)
  have hc0 : 0 ≤ c0 := by
    have := chbT_nonneg (sys := sys) hL
    have := gF_pos hL
    have := muCh_pos sys j
    positivity
  set k₀ : Lattice3 → ℝ := fun θ => c0 * (1 / FSLattice.lsq θ)
  have hk₀ : ∀ θ, 0 ≤ k₀ θ := fun θ => by have := FSLattice.lsq_nonneg θ; positivity
  have hZ : (0 : ℝ) < FSChannel.Zs 2 := FSChannel.Zs_pos (by norm_num)
  have hK₂ : ∀ S : Finset Lattice3, ∑ θ ∈ S, k₀ θ ^ 2 ≤ c0 ^ 2 * 4 * FSChannel.Zs 2 := by
    intro S
    have hw := FSLattice.sum_weight_le (by norm_num : (3 : ℝ) / 2 < 2) S
    have hterm : ∀ θ ∈ S, k₀ θ ^ 2 ≤ c0 ^ 2 * 4 * (1 + FSLattice.lsq θ) ^ (-(2 : ℝ)) := by
      intro θ _
      have hpos : 0 < 1 + FSLattice.lsq θ := by have := FSLattice.lsq_nonneg θ; linarith
      rw [Real.rpow_neg hpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      by_cases h0 : FSLattice.lsq θ = 0
      · simp only [k₀, h0, div_zero, mul_zero]; norm_num; positivity
      · have hl1 : 1 ≤ FSLattice.lsq θ := by
          by_contra hlt
          push Not at hlt
          have hθ : θ ≠ 0 := by intro h; rw [h, FSLattice.lsq_zero] at h0; exact h0 rfl
          exact absurd (one_le_latticeNormSq hθ) (by
            have : latticeNormSq θ = FSLattice.lsq θ := rfl
            rw [this]; linarith)
        simp only [k₀]
        rw [mul_pow, div_pow, one_pow]
        have h2 : 1 / FSLattice.lsq θ ^ 2 ≤ 4 * ((1 + FSLattice.lsq θ) ^ 2)⁻¹ := by
          rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        calc c0 ^ 2 * (1 / FSLattice.lsq θ ^ 2) ≤ c0 ^ 2 * (4 * ((1 + FSLattice.lsq θ) ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
          _ = _ := by ring
    calc ∑ θ ∈ S, k₀ θ ^ 2 ≤ ∑ θ ∈ S, c0 ^ 2 * 4 * (1 + FSLattice.lsq θ) ^ (-(2 : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = c0 ^ 2 * 4 * ∑ θ ∈ S, (1 + FSLattice.lsq θ) ^ (-(2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ c0 ^ 2 * 4 * FSChannel.Zs 2 := by
          gcongr
          simpa [FSChannel.Zs] using hw
  have hY := FSKernel.norm_kop_fibre_sq_le (fun q : Cfg eta n => labC j (cidx n q))
    (fun q => cidx n q (lead j))
    (fun x y h1 h2 => finiteConfigLatticeIndex_injective eta n (eq_of_labC_lead h1 h2))
    (fun q p => (kinMaj sys L n j q p : ℂ)) k₀ hk₀ hK₂ (by
      intro q p
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kinMaj_nonneg hL j q p)]
      unfold kinMaj
      split_ifs with h1 h2
      · rfl
      · exact absurd (labC_eq_of_onCh h1.1) h2
      · exact hk₀ _
      · exact le_rfl) (FSKernel.absv u)
  -- the lattice weight by the kinetic weight
  have hW : ∑ p, (1 + FSLattice.lsq (cidx n p (lead j))) ^ 2 * ‖(FSKernel.absv u).ofLp p‖ ^ 2 ≤
      cE sys L ^ 2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 := by
    rw [FSKernel.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [FSKernel.absv_apply, Complex.norm_real, Real.norm_eq_abs, abs_norm, wt_one_apply,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have h1 := one_add_lsqC_le sys hL (cidx n p)
    have h2 : FSLattice.lsq (cidx n p (lead j)) ≤ lsqC (cidx n p) := by
      unfold lsqC
      exact Finset.single_le_sum (f := fun c => nsq (cidx n p c)) (fun c _ => nsq_nonneg _)
        (Finset.mem_univ (lead j))
    have h3 : 1 + FSLattice.lsq (cidx n p (lead j)) ≤ cE sys L * (1 + Asym sys L n p) := by
      rw [Asym_eq_Ek]; linarith
    have h0 : 0 ≤ 1 + FSLattice.lsq (cidx n p (lead j)) := by
      have := FSLattice.lsq_nonneg (cidx n p (lead j)); linarith
    have h4 := pow_le_pow_left₀ h0 h3 2
    rw [mul_pow] at h4
    nlinarith [sq_nonneg ‖u.ofLp p‖]
  have hcomb : ‖FSKernel.kop (fun q p => (kinMaj sys L n j q p : ℂ)) (FSKernel.absv u)‖ ^ 2 ≤
      (c0 * (2 * FSChannel.Zs 2) * cE sys L * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) ^ 2 := by
    calc _ ≤ c0 ^ 2 * 4 * FSChannel.Zs 2 * FSChannel.Zs 2 *
          ∑ p, (1 + FSLattice.lsq (cidx n p (lead j))) ^ 2 * ‖(FSKernel.absv u).ofLp p‖ ^ 2 := hY
      _ ≤ c0 ^ 2 * 4 * FSChannel.Zs 2 * FSChannel.Zs 2 *
          (cE sys L ^ 2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hW (by positivity)
      _ = _ := by ring
  have := one_le_cE (sys := sys) (L := L)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hcomb

/-! ## The low layers: slab counts, pinning and the good tails -/

variable (sys L n) in
open Classical in
/-- The majorant of `Σ₂^bb` on the low layers of channel `j`, dyadic shell `i`. -/
noncomputable def lowMaj (j : Ch eta) (i : ℕ) (q p : Cfg eta n) : ℝ :=
  if OnCh j (cidx n q) (cidx n p) ∧ q ≠ p ∧ InQ (n : ℝ) (cidx n q) ∧ InQ (n : ℝ) (cidx n p) ∧
      gF L ^ 2 * FSChannel.rho (chT n j q p) / muCh sys j ≤ |Asym sys L n q - Asym sys L n p| ∧
      ¬ (gF L ^ 2 * FSLattice.lsq (chT n j q p) / (8 * muCh sys j) ≤
        |Asym sys L n q - Asym sys L n p|) ∧
      (4 : ℝ) ^ i ≤ FSLattice.lsq (chT n j q p) ∧ FSLattice.lsq (chT n j q p) ≤ 4 ^ (i + 1)
  then chbT sys L / (n : ℝ) ^ 3 * (1 / |Asym sys L n q - Asym sys L n p|) else 0

lemma lowMaj_nonneg (hL : 0 < L) (j : Ch eta) (i : ℕ) (q p : Cfg eta n) :
    0 ≤ lowMaj sys L n j i q p := by
  unfold lowMaj
  have := chbT_nonneg (sys := sys) hL
  split_ifs
  · positivity
  · exact le_rfl

omit [Fintype ν] in
lemma lsq_chT_swap (j : Ch eta) (q p : Cfg eta n) :
    FSLattice.lsq (chT n j p q) = FSLattice.lsq (chT n j q p) := by
  unfold chT
  simp only [FSLattice.lsq, Pi.sub_apply, Int.cast_sub]
  ring

lemma lowMaj_symm (j : Ch eta) (i : ℕ) (q p : Cfg eta n) :
    lowMaj sys L n j i q p = lowMaj sys L n j i p q := by
  unfold lowMaj
  rw [lsq_chT_swap j q p, chT_swap j q p, abs_sub_comm (Asym sys L n p)]
  have h1 : OnCh j (cidx n q) (cidx n p) ↔ OnCh j (cidx n p) (cidx n q) := ⟨onCh_symm, onCh_symm⟩
  by_cases hc : OnCh j (cidx n q) (cidx n p) ∧ q ≠ p ∧ InQ (n : ℝ) (cidx n q) ∧
      InQ (n : ℝ) (cidx n p) ∧
      gF L ^ 2 * FSChannel.rho (chT n j q p) / muCh sys j ≤ |Asym sys L n q - Asym sys L n p| ∧
      ¬ (gF L ^ 2 * FSLattice.lsq (chT n j q p) / (8 * muCh sys j) ≤
        |Asym sys L n q - Asym sys L n p|) ∧
      (4 : ℝ) ^ i ≤ FSLattice.lsq (chT n j q p) ∧ FSLattice.lsq (chT n j q p) ≤ 4 ^ (i + 1)
  · rw [if_pos hc, if_pos ⟨h1.mp hc.1, Ne.symm hc.2.1, hc.2.2.2.1, hc.2.2.1, hc.2.2.2.2⟩]
  · rw [if_neg hc, if_neg]
    intro h
    exact hc ⟨h1.mpr h.1, Ne.symm h.2.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2⟩

omit [Fintype ν] in
lemma mismatch_eq (hL : 0 < L) {j : Ch eta} {q p : Cfg eta n} (hj : OnCh j (cidx n q) (cidx n p)) :
    |Asym sys L n q - Asym sys L n p| =
      gF L ^ 2 / (2 * muCh sys j) * |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| := by
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  rw [Asym_hop hj, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))]

/-- The low-layer Schur constant of shell `i`. -/
noncomputable def Blow (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (j : Ch eta) (i : ℕ) : ℝ :=
  chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2 *
    (11000 * 4 ^ i * (2 / 2 ^ (i + 1) + 2 * (i + 1) / 2 ^ i)))

lemma Blow_nonneg (hL : 0 < L) (j : Ch eta) (i : ℕ) : 0 ≤ Blow sys L n j i := by
  unfold Blow
  have := chbT_nonneg (sys := sys) hL
  have := gF_pos hL
  have := muCh_pos sys j
  positivity

open Classical in
lemma col_lowMaj_le (hL : 0 < L) (j : Ch eta) (i : ℕ) (p : Cfg eta n) :
    ∑ q, lowMaj sys L n j i q p ≤ Blow sys L n j i := by
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  set P : Cfg eta n → Prop := fun q => OnCh j (cidx n q) (cidx n p) ∧ q ≠ p ∧
      InQ (n : ℝ) (cidx n q) ∧ InQ (n : ℝ) (cidx n p) ∧
      gF L ^ 2 * FSChannel.rho (chT n j q p) / muCh sys j ≤ |Asym sys L n q - Asym sys L n p| ∧
      ¬ (gF L ^ 2 * FSLattice.lsq (chT n j q p) / (8 * muCh sys j) ≤
        |Asym sys L n q - Asym sys L n p|) ∧
      (4 : ℝ) ^ i ≤ FSLattice.lsq (chT n j q p) ∧ FSLattice.lsq (chT n j q p) ≤ 4 ^ (i + 1)
  have e : ∑ q, lowMaj sys L n j i q p = chbT sys L / (n : ℝ) ^ 3 *
      ∑ q ∈ Finset.univ.filter P, 1 / |Asym sys L n q - Asym sys L n p| := by
    rw [Finset.mul_sum, Finset.sum_filter]
    rfl
  rw [e]
  unfold Blow
  apply mul_le_mul_of_nonneg_left _ (by have := chbT_nonneg (sys := sys) hL; positivity)
  apply shell_col_le hL j p (J := i) (by positivity)
  intro q hq
  obtain ⟨hon, hne, hiq, hip, hfl, hkin, hs1, hs2⟩ := (Finset.mem_filter.mp hq).2
  have hE := mismatch_eq (sys := sys) hL hon
  rw [hE] at hfl hkin
  refine ⟨hon, hs1, hs2, ?_, ?_⟩
  · have hr : (2 : ℝ) ^ i ≤ FSChannel.rho (chT n j q p) := by
      unfold FSChannel.rho
      apply Real.le_sqrt_of_sq_le
      rw [← pow_mul, mul_comm, pow_mul]; norm_num; exact hs1
    have e2 : gF L ^ 2 * FSChannel.rho (chT n j q p) / muCh sys j =
        gF L ^ 2 / (2 * muCh sys j) * (2 * FSChannel.rho (chT n j q p)) := by field_simp
    rw [e2] at hfl
    have h3 := le_of_mul_le_mul_left hfl (by positivity)
    rw [pow_succ]; linarith
  · push Not at hkin
    have e2 : gF L ^ 2 * FSLattice.lsq (chT n j q p) / (8 * muCh sys j) =
        gF L ^ 2 / (2 * muCh sys j) * (FSLattice.lsq (chT n j q p) / 4) := by field_simp; ring
    rw [e2] at hkin
    have h3 := lt_of_mul_lt_mul_left hkin (by positivity)
    have h4 : (4 : ℝ) ^ (i + 1) / 4 < 2 ^ (i + 1) * 2 ^ (i + 1) := by
      rw [← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num]
      have : (0 : ℝ) < 4 ^ (i + 1) := by positivity
      linarith
    linarith

lemma kabs_gt_of_nsq {q : Cfg eta n} {c : Fin eta} {X : ℝ} (hL : 0 < L)
    (h : X ^ 2 < nsq (cidx n q c)) : gF L * X < finitePlaneWaveKabs (2 * Real.pi / L) n (q c) := by
  rw [kabs_eq_lattice]
  have hg := gF_pos hL
  have hsq : X < Real.sqrt (latticeNormSq (finitePlaneWaveLatticeIndex n (q c))) := by
    apply Real.lt_sqrt_of_sq_lt
    exact h
  have e : gF L = 2 * Real.pi / L := rfl
  rw [← e]
  exact mul_lt_mul_of_pos_left hsq hg

/-- The pinned support of a low-layer majorant: some moved register of the input beyond
`l_i = g (3/8) 2^i`. -/
lemma lowMaj_pin (hL : 0 < L) {j : Ch eta} {i : ℕ} {q p : Cfg eta n}
    (h : lowMaj sys L n j i q p ≠ 0) :
    ∃ c ∈ moved j, gF L * (3 / 8 * 2 ^ i) < finitePlaneWaveKabs (2 * Real.pi / L) n (p c) := by
  unfold lowMaj at h
  split_ifs at h with hc
  · obtain ⟨hon, -, -, -, -, hkin, hs1, -⟩ := hc
    push Not at hkin
    rw [mismatch_eq (sys := sys) hL hon] at hkin
    have hg := gF_pos hL
    have hμ := muCh_pos sys j
    have e2 : gF L ^ 2 * FSLattice.lsq (chT n j q p) / (8 * muCh sys j) =
        gF L ^ 2 / (2 * muCh sys j) * (FSLattice.lsq (chT n j q p) / 4) := by field_simp; ring
    rw [e2] at hkin
    have h3 := lt_of_mul_lt_mul_left hkin (by positivity)
    obtain ⟨c, hc, hcn⟩ := pin_register sys j (cidx n p) (chT n j q p) h3
    refine ⟨c, hc, kabs_gt_of_nsq hL ?_⟩
    have e4 : (3 / 8 * (2 : ℝ) ^ i) ^ 2 = 9 / 64 * 4 ^ i := by
      rw [mul_pow, ← pow_mul, mul_comm i 2, pow_mul]; norm_num
    rw [e4]
    linarith
  · exact absurd rfl h

/-- The constant `c₀ = min(1, 3g/8)`. -/
noncomputable def c0 (L : ℝ) : ℝ := min 1 (3 * gF L / 8)

lemma c0_pos (hL : 0 < L) : 0 < c0 L := lt_min one_pos (by have := gF_pos hL; positivity)

lemma one_add_l_ge (i : ℕ) : c0 L * 2 ^ i ≤ 1 + gF L * (3 / 8 * 2 ^ i) := by
  have h1 : c0 L ≤ 3 * gF L / 8 := min_le_right _ _
  have h2 : c0 L * 2 ^ i ≤ 3 * gF L / 8 * 2 ^ i := mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith

/-- **One low shell**: `‖kop κ_low |u|‖ ≤ B_low · 8M/(c₀² 4^i)`. -/
theorem norm_low_le (hL : 0 < L) (j : Ch eta) (i : ℕ) {M : ℝ} {u : En eta n}
    (hu : IsGood sys L 1 M u) :
    ‖FSKernel.kop (fun q p => (lowMaj sys L n j i q p : ℂ)) (FSKernel.absv u)‖ ≤
      Blow sys L n j i * (8 * M / (c0 L ^ 2 * 4 ^ i)) := by
  classical
  have hM := good_nonneg hu
  have hc0 := c0_pos hL
  set P : Cfg eta n → Prop := fun p => ∃ c ∈ moved j,
    gF L * (3 / 8 * 2 ^ i) < finitePlaneWaveKabs (2 * Real.pi / L) n (p c)
  have hres := FSKernel.kop_res_of_cols (fun q p => (lowMaj sys L n j i q p : ℂ)) P
    (fun q p h => lowMaj_pin hL (by intro h0; apply h; rw [h0]; simp)) (FSKernel.absv u)
  rw [hres]
  refine (FSKernel.norm_kop_real_le _ (lowMaj_nonneg hL j i) (Blow_nonneg hL j i)
    (fun q => by
      calc ∑ p, lowMaj sys L n j i q p = ∑ p, lowMaj sys L n j i p q :=
            Finset.sum_congr rfl fun p _ => lowMaj_symm j i q p
        _ ≤ Blow sys L n j i := col_lowMaj_le hL j i q)
    (col_lowMaj_le hL j i) _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Blow_nonneg hL j i)
  rw [FSKernel.norm_res_absv]
  have hl : 0 ≤ gF L * (3 / 8 * 2 ^ i) := by have := gF_pos hL; positivity
  have h1 := norm_res_pin_le (L := L) j (gF L * (3 / 8 * 2 ^ i)) u
  have h2 : ∑ c ∈ moved j, ‖regTail L c (gF L * (3 / 8 * 2 ^ i)) u‖ ≤
      ∑ c ∈ moved j, 4 * M / (1 + gF L * (3 / 8 * 2 ^ i)) ^ 2 :=
    Finset.sum_le_sum fun c _ => regTail_le_good hu c hl
  have hcard : (moved j).card ≤ 2 := by
    cases j with
    | inl a => simp [moved]
    | inr pr => exact Finset.card_le_two
  have h3 : ∑ c ∈ moved j, 4 * M / (1 + gF L * (3 / 8 * 2 ^ i)) ^ 2 ≤
      2 * (4 * M / (1 + gF L * (3 / 8 * 2 ^ i)) ^ 2) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have : ((moved j).card : ℝ) ≤ 2 := by exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h4 : 4 * M / (1 + gF L * (3 / 8 * 2 ^ i)) ^ 2 ≤ 4 * M / (c0 L ^ 2 * 4 ^ i) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have := one_add_l_ge (L := L) i
    have e : c0 L ^ 2 * 4 ^ i = (c0 L * 2 ^ i) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm i 2, pow_mul]; norm_num
    rw [e]
    exact pow_le_pow_left₀ (by positivity) this 2
  calc ‖FSKernel.res P u‖ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ ≤ 2 * (4 * M / (c0 L ^ 2 * 4 ^ i)) := by linarith
    _ = 8 * M / (c0 L ^ 2 * 4 ^ i) := by ring

/-! ## The good-state bound for `Σ₂^bb` -/

variable (sys L n) in
/-- The majorant family of `Σ₂^bb`: `(j, 0)` the kinetic layers of `j`, `(j, i+1)` its low
shell `i`. -/
noncomputable def sbMaj (m : Ch eta × ℕ) (q p : Cfg eta n) : ℝ :=
  match m.2 with
  | 0 => kinMaj sys L n m.1 q p
  | i + 1 => lowMaj sys L n m.1 i q p

lemma sbMaj_nonneg (hL : 0 < L) (m : Ch eta × ℕ) (q p : Cfg eta n) : 0 ≤ sbMaj sys L n m q p := by
  obtain ⟨j, i⟩ := m
  cases i with
  | zero => exact kinMaj_nonneg hL j q p
  | succ i => exact lowMaj_nonneg hL j i q p

open Classical in
/-- Every entry of `Σ₂^bb` is covered by a kinetic layer or a low shell. -/
lemma sig2K_le_maj (hL : 0 < L) (hn : 2 ≤ n) (q p : Cfg eta n) :
    ‖FSKernel.divK (Asym sys L n) (hgapK sys L n) q p‖ ≤
      ∑ m ∈ (Finset.univ : Finset (Ch eta)) ×ˢ Finset.range (Nat.log 2 n + 2), sbMaj sys L n m q p := by
  have hsum0 : 0 ≤ ∑ m ∈ (Finset.univ : Finset (Ch eta)) ×ˢ Finset.range (Nat.log 2 n + 2),
      sbMaj sys L n m q p := Finset.sum_nonneg fun m _ => sbMaj_nonneg hL m q p
  have hg := gF_pos hL
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  unfold FSKernel.divK hgapK
  by_cases hd : Asym sys L n q = Asym sys L n p
  · rw [if_pos hd, norm_zero]; exact hsum0
  rw [if_neg hd]
  by_cases hgp : gapC sys L n q p
  swap
  · rw [if_neg hgp, zero_div, norm_zero]; exact hsum0
  rw [if_pos hgp]
  by_cases h0 : hbC sys L n q p = 0
  · rw [h0, zero_div, norm_zero]; exact hsum0
  have hQ : InQ (n : ℝ) (cidx n q) ∧ InQ (n : ℝ) (cidx n p) := by
    by_contra h; exact h0 (hbC_eq_zero_of_not_inQ h)
  obtain ⟨hne, j, hj, hfl⟩ := hgp
  have hdpos : 0 < |Asym sys L n q - Asym sys L n p| := abs_pos.mpr (sub_ne_zero.mpr hd)
  have hval : ‖hbC sys L n q p / ((Asym sys L n q - Asym sys L n p : ℝ) : ℂ)‖ ≤
      chbT sys L / (n : ℝ) ^ 3 * (1 / |Asym sys L n q - Asym sys L n p|) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (norm_hbC_le hL hn q p) (by positivity)
  have hl1 := one_le_lsq_chT hj hne
  by_cases hk : gF L ^ 2 * FSLattice.lsq (chT n j q p) / (8 * muCh sys j) ≤
      |Asym sys L n q - Asym sys L n p|
  · have hkm : kinMaj sys L n j q p = chbT sys L / (n : ℝ) ^ 3 * (8 * muCh sys j / gF L ^ 2) *
        (1 / FSLattice.lsq (chT n j q p)) := by
      unfold kinMaj; rw [if_pos ⟨hj, hne, hk⟩]
    have hμ := muCh_pos sys j
    have hb : chbT sys L / (n : ℝ) ^ 3 * (1 / |Asym sys L n q - Asym sys L n p|) ≤
        kinMaj sys L n j q p := by
      rw [hkm, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by have := chbT_nonneg (sys := sys) hL; positivity)
      have hpos : 0 < gF L ^ 2 * FSLattice.lsq (chT n j q p) / (8 * muCh sys j) := by positivity
      calc 1 / |Asym sys L n q - Asym sys L n p| ≤
            1 / (gF L ^ 2 * FSLattice.lsq (chT n j q p) / (8 * muCh sys j)) :=
            one_div_le_one_div_of_le hpos hk
        _ = 8 * muCh sys j / gF L ^ 2 * (1 / FSLattice.lsq (chT n j q p)) := by field_simp
    refine hval.trans (hb.trans ?_)
    have hm : ((j, 0) : Ch eta × ℕ) ∈ (Finset.univ : Finset (Ch eta)) ×ˢ
        Finset.range (Nat.log 2 n + 2) := by simp
    exact Finset.single_le_sum (f := fun m => sbMaj sys L n m q p)
      (fun m _ => sbMaj_nonneg hL m q p) hm
  · obtain ⟨i, hi1, hi2⟩ := exists_shell hl1
    have hiI : i ≤ Nat.log 2 n :=
      shell_index_le hi1 (lsq_chT_le (Nat.cast_nonneg n) hQ.1 hQ.2) (by omega)
    have hlm : lowMaj sys L n j i q p =
        chbT sys L / (n : ℝ) ^ 3 * (1 / |Asym sys L n q - Asym sys L n p|) := by
      unfold lowMaj; rw [if_pos ⟨hj, hne, hQ.1, hQ.2, hfl, hk, hi1, hi2⟩]
    refine hval.trans (le_of_eq hlm.symm |>.trans ?_)
    have hm : ((j, i + 1) : Ch eta × ℕ) ∈ (Finset.univ : Finset (Ch eta)) ×ˢ
        Finset.range (Nat.log 2 n + 2) := by
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]; omega
    exact Finset.single_le_sum (f := fun m => sbMaj sys L n m q p)
      (fun m _ => sbMaj_nonneg hL m q p) hm

variable (sys L) in
/-- The good-state constant of `Σ₂^bb`. -/
noncomputable def CSg : ℝ :=
  chbT sys L * ∑ j : Ch eta, (8 * muCh sys j / gF L ^ 2 * (2 * FSChannel.Zs 2) * cE sys L +
    2 * muCh sys j / gF L ^ 2 * (880000 / c0 L ^ 2))

/-- **The good-state bound for the bulk rotation**: `‖Σ₂^bb u‖ ≤ C_Σg M/n³` for `IsGood 1 M u`
(the text's `‖Σ₂^bb u‖ ≤ CΞK^{-3} log(2+K)`, here without the logarithm). -/
theorem norm_Sig2bb_good (hL : 0 < L) (hn : 2 ≤ n) {M : ℝ} {u : En eta n}
    (hu : IsGood sys L 1 M u) : ‖Sig2bb sys L n u‖ ≤ CSg sys L * M / (n : ℝ) ^ 3 := by
  have hM := good_nonneg hu
  have hg := gF_pos hL
  have hc0 := c0_pos hL
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  have hΘ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ≤ M := by
    have := hu.1; have := norm_nonneg u; linarith
  have h1 := FSKernel.norm_kop_le_of_maj _ (FSKernel.divK (Asym sys L n) (hgapK sys L n))
    (sbMaj sys L n) (sbMaj_nonneg hL) (sig2K_le_maj hL hn) u
  have hS : (Sig2bb sys L n : En eta n →ₗ[ℂ] En eta n) =
      FSKernel.kop (FSKernel.divK (Asym sys L n) (hgapK sys L n)) := rfl
  rw [hS]
  refine h1.trans ?_
  rw [Finset.sum_product]
  unfold CSg
  rw [mul_comm (chbT sys L), Finset.sum_mul, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.sum_range_succ']
  have hkin : ‖FSKernel.kop (fun q p => (sbMaj sys L n (j, 0) q p : ℂ)) (FSKernel.absv u)‖ ≤
      chbT sys L / (n : ℝ) ^ 3 * (8 * muCh sys j / gF L ^ 2) * (2 * FSChannel.Zs 2) * cE sys L * M := by
    have := norm_kin_le (sys := sys) (n := n) hL j u
    refine this.trans (mul_le_mul_of_nonneg_left hΘ ?_)
    have := chbT_nonneg (sys := sys) hL
    have := muCh_pos sys j
    have := FSChannel.Zs_pos (by norm_num : (3 : ℝ) / 2 < 2)
    have := one_le_cE (sys := sys) (L := L)
    positivity
  have hlow : ∀ i ∈ Finset.range (Nat.log 2 n + 1),
      ‖FSKernel.kop (fun q p => (sbMaj sys L n (j, i + 1) q p : ℂ)) (FSKernel.absv u)‖ ≤
        chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) * (88000 * M / c0 L ^ 2) *
          ((2 * (i : ℝ) + 3) * (1 / 2) ^ i) := by
    intro i _
    refine (norm_low_le hL j i hu).trans (le_of_eq ?_)
    unfold Blow
    rw [one_div_pow, pow_succ]
    field_simp
    ring
  have hlow_sum : ∑ i ∈ Finset.range (Nat.log 2 n + 1),
      ‖FSKernel.kop (fun q p => (sbMaj sys L n (j, i + 1) q p : ℂ)) (FSKernel.absv u)‖ ≤
        chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) * (88000 * M / c0 L ^ 2) * 10 := by
    refine (Finset.sum_le_sum hlow).trans ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left (sum_two_i_three_le _)
    have := chbT_nonneg (sys := sys) hL
    have := muCh_pos sys j
    positivity
  rw [add_comm]
  calc ‖FSKernel.kop (fun q p => (sbMaj sys L n (j, 0) q p : ℂ)) (FSKernel.absv u)‖ +
        ∑ i ∈ Finset.range (Nat.log 2 n + 1),
          ‖FSKernel.kop (fun q p => (sbMaj sys L n (j, i + 1) q p : ℂ)) (FSKernel.absv u)‖
      ≤ chbT sys L / (n : ℝ) ^ 3 * (8 * muCh sys j / gF L ^ 2) * (2 * FSChannel.Zs 2) * cE sys L * M +
        chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) * (88000 * M / c0 L ^ 2) * 10 :=
        add_le_add hkin hlow_sum
    _ = (8 * muCh sys j / gF L ^ 2 * (2 * FSChannel.Zs 2) * cE sys L +
          2 * muCh sys j / gF L ^ 2 * (880000 / c0 L ^ 2)) * chbT sys L * M / (n : ℝ) ^ 3 := by
        field_simp
        ring

/-! ## The resonant residual `H₂^{bb,res}` (`lem:res2`) -/

variable (sys L n) in
open Classical in
/-- The majorant of the resonant residual on channel `j`, dyadic shell `i`. -/
noncomputable def resMaj (m : Ch eta × ℕ) (q p : Cfg eta n) : ℝ :=
  if OnCh m.1 (cidx n q) (cidx n p) ∧ q ≠ p ∧ InQ (n : ℝ) (cidx n q) ∧ InQ (n : ℝ) (cidx n p) ∧
      ¬ (gF L ^ 2 * FSChannel.rho (chT n m.1 q p) / muCh sys m.1 ≤
        |Asym sys L n q - Asym sys L n p|) ∧
      (4 : ℝ) ^ m.2 ≤ FSLattice.lsq (chT n m.1 q p) ∧ FSLattice.lsq (chT n m.1 q p) ≤ 4 ^ (m.2 + 1)
  then chbT sys L / (n : ℝ) ^ 3 else 0

lemma resMaj_nonneg (hL : 0 < L) (m : Ch eta × ℕ) (q p : Cfg eta n) :
    0 ≤ resMaj sys L n m q p := by
  unfold resMaj
  have := chbT_nonneg (sys := sys) hL
  split_ifs
  · positivity
  · exact le_rfl

lemma resMaj_symm (m : Ch eta × ℕ) (q p : Cfg eta n) :
    resMaj sys L n m q p = resMaj sys L n m p q := by
  unfold resMaj
  rw [lsq_chT_swap m.1 q p, chT_swap m.1 q p, abs_sub_comm (Asym sys L n p)]
  have h1 : OnCh m.1 (cidx n q) (cidx n p) ↔ OnCh m.1 (cidx n p) (cidx n q) :=
    ⟨onCh_symm, onCh_symm⟩
  by_cases hc : OnCh m.1 (cidx n q) (cidx n p) ∧ q ≠ p ∧ InQ (n : ℝ) (cidx n q) ∧
      InQ (n : ℝ) (cidx n p) ∧
      ¬ (gF L ^ 2 * FSChannel.rho (chT n m.1 q p) / muCh sys m.1 ≤
        |Asym sys L n q - Asym sys L n p|) ∧
      (4 : ℝ) ^ m.2 ≤ FSLattice.lsq (chT n m.1 q p) ∧ FSLattice.lsq (chT n m.1 q p) ≤ 4 ^ (m.2 + 1)
  · rw [if_pos hc, if_pos ⟨h1.mp hc.1, Ne.symm hc.2.1, hc.2.2.2.1, hc.2.2.1, hc.2.2.2.2⟩]
  · rw [if_neg hc, if_neg]
    intro h
    exact hc ⟨h1.mpr h.1, Ne.symm h.2.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2⟩

open FSChannel in
omit [Fintype ν] in
/-- On a resonant element, `|F_c(θ)| < 2|θ|`. -/
lemma resonant_slab (hL : 0 < L) {j : Ch eta} {q p : Cfg eta n}
    (hj : OnCh j (cidx n q) (cidx n p))
    (h : ¬ (gF L ^ 2 * rho (chT n j q p) / muCh sys j ≤ |Asym sys L n q - Asym sys L n p|)) :
    |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| < 2 * rho (chT n j q p) := by
  push Not at h
  rw [mismatch_eq (sys := sys) hL hj] at h
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have e2 : gF L ^ 2 * rho (chT n j q p) / muCh sys j =
      gF L ^ 2 / (2 * muCh sys j) * (2 * rho (chT n j q p)) := by field_simp
  rw [e2] at h
  exact lt_of_mul_lt_mul_left h (by positivity)

open FSChannel in
omit [Fintype ν] in
lemma rho_le_of_shell {θ : Lattice3} {i : ℕ} (h : FSLattice.lsq θ ≤ 4 ^ (i + 1)) :
    rho θ ≤ 2 ^ (i + 1) := by
  unfold rho
  rw [Real.sqrt_le_left (by positivity)]
  rw [← pow_mul, mul_comm, pow_mul]; norm_num; exact h

open Classical in
lemma col_resMaj_le (hL : 0 < L) (m : Ch eta × ℕ) (p : Cfg eta n) :
    ∑ q, resMaj sys L n m q p ≤ chbT sys L / (n : ℝ) ^ 3 * (55000 * 4 ^ m.2) := by
  obtain ⟨j, i⟩ := m
  set P : Cfg eta n → Prop := fun q => OnCh j (cidx n q) (cidx n p) ∧ q ≠ p ∧
      InQ (n : ℝ) (cidx n q) ∧ InQ (n : ℝ) (cidx n p) ∧
      ¬ (gF L ^ 2 * FSChannel.rho (chT n j q p) / muCh sys j ≤ |Asym sys L n q - Asym sys L n p|) ∧
      (4 : ℝ) ^ i ≤ FSLattice.lsq (chT n j q p) ∧ FSLattice.lsq (chT n j q p) ≤ 4 ^ (i + 1)
  have e : ∑ q, resMaj sys L n (j, i) q p =
      chbT sys L / (n : ℝ) ^ 3 * ((Finset.univ.filter P).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold resMaj
    split_ifs <;> simp
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (by have := chbT_nonneg (sys := sys) hL; positivity)
  have hc := shell_count_le (sys := sys) j p (i := i) (δ := 2 ^ (i + 2)) (by positivity)
    (Finset.univ.filter P) (by
      intro q hq
      obtain ⟨hon, -, -, -, hres, hs1, hs2⟩ := (Finset.mem_filter.mp hq).2
      refine ⟨hon, hs1, hs2, ?_⟩
      have h1 := resonant_slab hL hon hres
      have h2 := rho_le_of_shell hs2
      rw [pow_succ 2 (i + 1)]
      linarith)
  calc ((Finset.univ.filter P).card : ℝ) ≤ 11000 * 4 ^ i * (1 + 2 ^ (i + 2) / 2 ^ i) := hc
    _ = 55000 * 4 ^ i := by
        rw [pow_add]; field_simp; ring

/-- The pinned support of a resonant element in a shell `i ≥ 3`. -/
lemma resMaj_pin (hL : 0 < L) {m : Ch eta × ℕ} (hm : 3 ≤ m.2) {q p : Cfg eta n}
    (h : resMaj sys L n m q p ≠ 0) :
    ∃ c ∈ moved m.1, gF L * (3 / 8 * 2 ^ m.2) < finitePlaneWaveKabs (2 * Real.pi / L) n (p c) := by
  obtain ⟨j, i⟩ := m
  simp only at hm ⊢
  unfold resMaj at h
  split_ifs at h with hc
  · obtain ⟨hon, -, -, -, hres, hs1, -⟩ := hc
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

/-- One resonant shell. -/
theorem norm_res_shell_le (hL : 0 < L) (m : Ch eta × ℕ) {M : ℝ} {u : En eta n}
    (hu : IsGood sys L 1 M u) :
    ‖FSKernel.kop (fun q p => (resMaj sys L n m q p : ℂ)) (FSKernel.absv u)‖ ≤
      chbT sys L / (n : ℝ) ^ 3 * M * (440000 / c0 L ^ 2 + 3520000) := by
  classical
  have hM := good_nonneg hu
  have hc0 := c0_pos hL
  have hcb := chbT_nonneg (sys := sys) hL
  have hn3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hSchur : ∀ v : En eta n, ‖FSKernel.kop (fun q p => (resMaj sys L n m q p : ℂ)) v‖ ≤
      chbT sys L / (n : ℝ) ^ 3 * (55000 * 4 ^ m.2) * ‖v‖ := fun v =>
    FSKernel.norm_kop_real_le _ (resMaj_nonneg hL m) (by positivity)
      (fun q => by
        calc ∑ p, resMaj sys L n m q p = ∑ p, resMaj sys L n m p q :=
              Finset.sum_congr rfl fun p _ => resMaj_symm m q p
          _ ≤ _ := col_resMaj_le hL m q)
      (col_resMaj_le hL m) v
  by_cases hm : 3 ≤ m.2
  · set P : Cfg eta n → Prop := fun p => ∃ c ∈ moved m.1,
      gF L * (3 / 8 * 2 ^ m.2) < finitePlaneWaveKabs (2 * Real.pi / L) n (p c)
    rw [FSKernel.kop_res_of_cols _ P (fun q p h => resMaj_pin hL hm (by intro h0; apply h; rw [h0]; simp))]
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
    have e1 : chbT sys L / (n : ℝ) ^ 3 * (55000 * 4 ^ m.2) * (8 * M / (c0 L ^ 2 * 4 ^ m.2)) =
        chbT sys L / (n : ℝ) ^ 3 * M * (440000 / c0 L ^ 2) := by
      field_simp
      ring
    have e2 : chbT sys L / (n : ℝ) ^ 3 * M * (440000 / c0 L ^ 2) ≤
        chbT sys L / (n : ℝ) ^ 3 * M * (440000 / c0 L ^ 2 + 3520000) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e3 : chbT sys L / (n : ℝ) ^ 3 * (55000 * 4 ^ m.2) * ‖FSKernel.res P u‖ ≤
        chbT sys L / (n : ℝ) ^ 3 * (55000 * 4 ^ m.2) * (8 * M / (c0 L ^ 2 * 4 ^ m.2)) := by
      exact mul_le_mul_of_nonneg_left hres (by positivity)
    exact le_trans e3 (le_trans (le_of_eq e1) e2)
  · push Not at hm
    refine (hSchur _).trans ?_
    rw [FSKernel.norm_absv]
    have h4 : (4 : ℝ) ^ m.2 ≤ 64 := by
      have : (4 : ℝ) ^ m.2 ≤ 4 ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
      norm_num at this; linarith
    have hu' := norm_le_good hu
    calc chbT sys L / (n : ℝ) ^ 3 * (55000 * 4 ^ m.2) * ‖u‖
        ≤ chbT sys L / (n : ℝ) ^ 3 * (55000 * 64) * M := by gcongr
      _ = chbT sys L / (n : ℝ) ^ 3 * M * 3520000 := by ring
      _ ≤ chbT sys L / (n : ℝ) ^ 3 * M * (440000 / c0 L ^ 2 + 3520000) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : 0 ≤ 440000 / c0 L ^ 2 := by positivity
          linarith

variable (sys L) in
/-- The constant of `lem:res2`. -/
noncomputable def CRes (n : ℕ) : ℝ :=
  chbT sys L * (1 + Fintype.card (Ch eta) * (Nat.log 2 n + 1) * (440000 / c0 L ^ 2 + 3520000))

open Classical in
/-- **`lem:res2`**: `‖H₂^{bb,res} u‖ ≤ C_res(n) M/n³` for `IsGood 1 M u`, with
`C_res(n) = chbT (1 + #Ch (log₂ n + 1)(440000/c₀² + 3520000))`. -/
theorem norm_Hres_good (hL : 0 < L) (hn : 2 ≤ n) {M : ℝ} {u : En eta n}
    (hu : IsGood sys L 1 M u) : ‖Hres sys L n u‖ ≤ CRes sys L n * M / (n : ℝ) ^ 3 := by
  have hM := good_nonneg hu
  have hc0 := c0_pos hL
  have hcb := chbT_nonneg (sys := sys) hL
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  -- diagonal and off-diagonal parts
  set dK : Cfg eta n → Cfg eta n → ℂ := fun q p => if q = p then hresK sys L n q p else 0
  set oK : Cfg eta n → Cfg eta n → ℂ := fun q p => if q = p then 0 else hresK sys L n q p
  have hsplit : Hres sys L n = FSKernel.kop dK + FSKernel.kop oK := by
    rw [Hres, ← FSKernel.kop_add]
    congr 1
    funext q p
    simp only [Pi.add_apply, dK, oK]
    split_ifs <;> simp
  rw [hsplit, LinearMap.add_apply]
  have hdiag : ‖FSKernel.kop dK u‖ ≤ chbT sys L / (n : ℝ) ^ 3 * ‖u‖ := by
    have hent : ∀ q p, ‖dK q p‖ ≤ if q = p then chbT sys L / (n : ℝ) ^ 3 else 0 := by
      intro q p
      simp only [dK]
      split_ifs with h
      · unfold hresK
        split_ifs
        · rw [norm_zero]; positivity
        · exact norm_hbC_le hL hn q p
      · simp
    apply FSKernel.norm_kop_le' _ (by positivity)
    · intro q
      calc ∑ p, ‖dK q p‖ ≤ ∑ p, (if q = p then chbT sys L / (n : ℝ) ^ 3 else 0) :=
            Finset.sum_le_sum fun p _ => hent q p
        _ = chbT sys L / (n : ℝ) ^ 3 := by rw [Finset.sum_ite_eq]; simp
    · intro p
      calc ∑ q, ‖dK q p‖ ≤ ∑ q, (if q = p then chbT sys L / (n : ℝ) ^ 3 else 0) :=
            Finset.sum_le_sum fun q _ => hent q p
        _ = chbT sys L / (n : ℝ) ^ 3 := by rw [Finset.sum_ite_eq']; simp
  -- the off-diagonal majorants
  have hdom : ∀ q p, ‖oK q p‖ ≤ ∑ m ∈ (Finset.univ : Finset (Ch eta)) ×ˢ
      Finset.range (Nat.log 2 n + 1), resMaj sys L n m q p := by
    intro q p
    have hsum0 : 0 ≤ ∑ m ∈ (Finset.univ : Finset (Ch eta)) ×ˢ Finset.range (Nat.log 2 n + 1),
        resMaj sys L n m q p := Finset.sum_nonneg fun m _ => resMaj_nonneg hL m q p
    simp only [oK]
    split_ifs with hqp
    · rw [norm_zero]; exact hsum0
    unfold hresK
    split_ifs with hgp
    · rw [norm_zero]; exact hsum0
    by_cases h0 : hbC sys L n q p = 0
    · rw [h0, norm_zero]; exact hsum0
    have hQ : InQ (n : ℝ) (cidx n q) ∧ InQ (n : ℝ) (cidx n p) := by
      by_contra h; exact h0 (hbC_eq_zero_of_not_inQ h)
    have hj : ∃ j, OnCh j (cidx n q) (cidx n p) := by
      by_contra hno
      push Not at hno
      have hb := norm_hbK_le (sys := sys) (L := L) hL hn hQ.1 hQ.2
      simp only [if_neg (hno _), zero_div, Finset.sum_const_zero] at hb
      exact h0 (norm_le_zero_iff.mp hb)
    obtain ⟨j, hj⟩ := hj
    have hfl : ¬ (gF L ^ 2 * FSChannel.rho (chT n j q p) / muCh sys j ≤
        |Asym sys L n q - Asym sys L n p|) := fun h => hgp ⟨hqp, j, hj, h⟩
    obtain ⟨i, hi1, hi2⟩ := exists_shell (one_le_lsq_chT hj hqp)
    have hiI : i ≤ Nat.log 2 n :=
      shell_index_le hi1 (lsq_chT_le (Nat.cast_nonneg n) hQ.1 hQ.2) (by omega)
    have hval : resMaj sys L n (j, i) q p = chbT sys L / (n : ℝ) ^ 3 := by
      unfold resMaj; rw [if_pos ⟨hj, hqp, hQ.1, hQ.2, hfl, hi1, hi2⟩]
    have hm : ((j, i) : Ch eta × ℕ) ∈ (Finset.univ : Finset (Ch eta)) ×ˢ
        Finset.range (Nat.log 2 n + 1) := by
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]; omega
    refine (norm_hbC_le hL hn q p).trans (le_of_eq hval.symm |>.trans ?_)
    exact Finset.single_le_sum (f := fun m => resMaj sys L n m q p)
      (fun m _ => resMaj_nonneg hL m q p) hm
  have hoff := FSKernel.norm_kop_le_of_maj _ oK (resMaj sys L n) (resMaj_nonneg hL) hdom u
  have hoff2 : ∑ m ∈ (Finset.univ : Finset (Ch eta)) ×ˢ Finset.range (Nat.log 2 n + 1),
      ‖FSKernel.kop (fun q p => (resMaj sys L n m q p : ℂ)) (FSKernel.absv u)‖ ≤
      Fintype.card (Ch eta) * (Nat.log 2 n + 1) *
        (chbT sys L / (n : ℝ) ^ 3 * M * (440000 / c0 L ^ 2 + 3520000)) := by
    refine (Finset.sum_le_sum fun m _ => norm_res_shell_le hL m hu).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hu' := norm_le_good hu
  refine (norm_add_le _ _).trans ?_
  calc ‖FSKernel.kop dK u‖ + ‖FSKernel.kop oK u‖
      ≤ chbT sys L / (n : ℝ) ^ 3 * M + Fintype.card (Ch eta) * (Nat.log 2 n + 1) *
          (chbT sys L / (n : ℝ) ^ 3 * M * (440000 / c0 L ^ 2 + 3520000)) := by
        refine add_le_add (hdiag.trans (mul_le_mul_of_nonneg_left hu' (by positivity)))
          (hoff.trans hoff2)
    _ = CRes sys L n * M / (n : ℝ) ^ 3 := by
        unfold CRes
        field_simp

end FSNormal
