import PlaneWave.Auxiliary.FourierDomination

/-!
# Auxiliary claims, part 6: the alias bound and the grid operator (`lem:grid-KR` (ii), (iv))

The register zone has half-width `M` (`n' = 2M + 1` grid points per direction): `inZone M x`
says that every momentum component of the configuration `x` lies in `[-M, M]`. The centred
representative modulo `n'` (`cfold`) folds every lattice configuration into the zone (`foldC`).
On a cube `n` (containing the zone and the outputs of the kernels):

* `aliasOp M v`, the alias `R`: the exterior coefficients of `v` folded onto the zone;
* `gridDiag M κ u = P'(κ u) + R(κ u)`, the collocation `Diag[g]` in momentum coordinates (the fold
  identity, `lem:fold`, `GridFold.fold_pair`); `gridDiag_apply`: `(Diag[g] u)(p) = Σ_{t ≡ p} (g u)(t)`;
* **`alias_bound`** (eq:alias-mult): for an output supported in the region of a kernel acting on the
  registers `S` (transfers at most `M`), `‖R v‖² ≤ (27^{|S|} - 1) ‖(1 - P') v‖²`; for a pair term
  `C_alias = √728 ≤ 27` (`sqrt728_le`);
* **`alias_bound_restricted`** (eq:alias-restricted): the same with the restriction
  `Q_{a,J} = 1{‖k_{p_a}‖_∞ > J}` on both sides (centred folding never increases a component);
* `norm_gridDiag_le`, `tail_gridDiag_le`: `‖Diag[g] u‖ ≤ 28 ‖g u‖`, `‖Q_{a,J} Diag[g] u‖ ≤ 28 ‖Q_{a,J} g u‖`;
* **`grid_graph_equivalence`**, **`grid_form_lower`** (`lem:grid-KR` (iv), eq:grid-graph-equivalence,
  eq:grid-form-lower): for a grid potential `V = Σ_t c_t Diag[g_t]` whose terms have the weighted
  bounds of `PlaneWave.Auxiliary.FourierDomination` (`‖g_t u‖² ≤ X_t² Σ (1 + |k_{p_{r_t}}|²)|u_p|²`), with `Y = 28 Σ_t |c_t| X_t`:
  `‖H u‖ ≤ (3/2) Θ(u) + (Y + Y²) m̄ ‖u‖`, `Θ(u) ≤ 2 ‖H u‖ + (1 + 2Y + 2Y²) m̄ ‖u‖` and
  `|⟨u, V u⟩| ≤ ε ⟨u, T u⟩ + (Y + Y²/(2ε)) m̄ ‖u‖²` for zone states, `H = T + V`; hence the
  `K`-uniform lower bound `Re ⟨u, H u⟩ ≥ -(Y + 2Y²) m̄ ‖u‖²` (`grid_lower_bound`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators
open PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν] {n : ℕ}

/-! ## The centred fold -/

/-- The centred representative of `t` modulo `n' = 2M + 1`, in `[-M, M]`. -/
def cfold (M : ℕ) (t : ℤ) : ℤ := (t + M) % (2 * M + 1) - M

lemma cfold_bounds (M : ℕ) (t : ℤ) : -(M : ℤ) ≤ cfold M t ∧ cfold M t ≤ M := by
  unfold cfold
  have h1 := Int.emod_nonneg (t + M) (by omega : (2 * (M : ℤ) + 1) ≠ 0)
  have h2 := Int.emod_lt_of_pos (t + M) (by omega : (0 : ℤ) < 2 * M + 1)
  constructor <;> omega

lemma abs_cfold_le_M (M : ℕ) (t : ℤ) : |cfold M t| ≤ M := abs_le.mpr (cfold_bounds M t)

lemma dvd_sub_cfold (M : ℕ) (t : ℤ) : (2 * (M : ℤ) + 1) ∣ t - cfold M t := by
  refine ⟨(t + M) / (2 * M + 1), ?_⟩
  have h := Int.emod_add_mul_ediv (t + M) (2 * M + 1)
  unfold cfold
  linarith

lemma cfold_of_abs_le (M : ℕ) {t : ℤ} (h : |t| ≤ M) : cfold M t = t := by
  unfold cfold
  have h' := abs_le.mp h
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  ring

/-- Centred folding never increases the modulus of a component. -/
lemma abs_cfold_le (M : ℕ) (t : ℤ) : |cfold M t| ≤ |t| := by
  by_cases h : |t| ≤ M
  · rw [cfold_of_abs_le M h]
  · push Not at h
    exact (abs_cfold_le_M M t).trans h.le

/-- On `[-2M, 2M]` the fold index is `-1`, `0` or `1`. -/
lemma fold_index_mem (M : ℕ) {t : ℤ} (h : |t| ≤ 2 * M) :
    (t - cfold M t) / (2 * M + 1) ∈ ({-1, 0, 1} : Finset ℤ) := by
  obtain ⟨ℓ, hℓ⟩ := dvd_sub_cfold M t
  have hpos : (0 : ℤ) < 2 * M + 1 := by omega
  rw [hℓ, Int.mul_ediv_cancel_left _ hpos.ne']
  have hb := cfold_bounds M t
  have ht := abs_le.mp h
  have h1 : (2 * (M : ℤ) + 1) * ℓ ≤ 3 * M := by rw [← hℓ]; omega
  have h2 : -(3 * (M : ℤ)) ≤ (2 * (M : ℤ) + 1) * ℓ := by rw [← hℓ]; omega
  have hl1 : ℓ ≤ 1 := by nlinarith
  have hl2 : -1 ≤ ℓ := by nlinarith
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- The register zone: every momentum component in `[-M, M]`. -/
def inZone (M : ℕ) (x : Cf eta) : Prop := ∀ a c, |x a c| ≤ M

instance (M : ℕ) (x : Cf eta) : Decidable (inZone M x) := by
  unfold inZone; infer_instance

/-- The configuration fold. -/
def foldC (M : ℕ) (x : Cf eta) : Cf eta := fun a c => cfold M (x a c)

lemma foldC_inZone (M : ℕ) (x : Cf eta) : inZone M (foldC M x) := fun _ _ => abs_cfold_le_M M _

/-- The output region of a kernel acting on the registers `S` with transfers at most `M`. -/
def OutReg (M : ℕ) (S : Finset (Fin eta)) (x : Cf eta) : Prop :=
  (∀ a, a ∉ S → ∀ c, |x a c| ≤ M) ∧ ∀ a, a ∈ S → ∀ c, |x a c| ≤ 2 * M

instance (M : ℕ) (S : Finset (Fin eta)) (x : Cf eta) : Decidable (OutReg M S x) := by
  unfold OutReg; infer_instance

/-! ## The alias and the grid operator -/

/-- The zone projector `P'`. -/
noncomputable def zoneProj (M : ℕ) (v : En eta n) : En eta n :=
  WithLp.toLp 2 (fun p => if inZone M (cidx n p) then v.ofLp p else 0)

/-- The exterior fibre of a zone configuration. -/
noncomputable def aliasFib (M : ℕ) (p : Cfg eta n) : Finset (Cfg eta n) :=
  Finset.univ.filter fun q => ¬ inZone M (cidx n q) ∧ foldC M (cidx n q) = cidx n p

/-- **The alias** `R`: the exterior coefficients folded onto the zone. -/
noncomputable def aliasOp (M : ℕ) (v : En eta n) : En eta n :=
  WithLp.toLp 2 (fun p => if inZone M (cidx n p) then ∑ q ∈ aliasFib M p, v.ofLp q else 0)

/-- **The collocation** `Diag[g] u = P'(g u) + R(g u)` in momentum coordinates. -/
noncomputable def gridDiag (M : ℕ) (κ : Cfg eta n → Cfg eta n → ℂ) (u : En eta n) : En eta n :=
  zoneProj M (finiteCoefficientKernelOperator κ u) + aliasOp M (finiteCoefficientKernelOperator κ u)

/-- A coordinate mask. -/
noncomputable def maskV (P : Cfg eta n → Prop) [DecidablePred P] (v : En eta n) : En eta n :=
  WithLp.toLp 2 (fun p => if P p then v.ofLp p else 0)

omit [Fintype ν] in
lemma norm_maskV_sq (P : Cfg eta n → Prop) [DecidablePred P] (v : En eta n) :
    ‖maskV P v‖ ^ 2 = ∑ p ∈ Finset.univ.filter P, ‖v.ofLp p‖ ^ 2 := by
  rw [FSKernel.norm_sq_eq, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  change ‖(if P p then v.ofLp p else 0)‖ ^ 2 = _
  by_cases h : P p <;> simp [h]

omit [Fintype ν] in
lemma norm_maskV_le (P : Cfg eta n → Prop) [DecidablePred P] (v : En eta n) :
    ‖maskV P v‖ ≤ ‖v‖ := by
  have h1 := norm_maskV_sq P v
  have h2 : ∑ p ∈ Finset.univ.filter P, ‖v.ofLp p‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [FSKernel.norm_sq_eq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (h1 ▸ h2)

omit [Fintype ν] in
lemma maskV_true (v : En eta n) : maskV (fun _ => True) v = v := by
  ext p; simp [maskV]

/-- The number of fold-index vectors of a kernel acting on the registers `S`. -/
noncomputable def foldIdx (S : Finset (Fin eta)) : Finset (Fin eta → Fin 3 → ℤ) :=
  (Fintype.piFinset fun a : Fin eta =>
    Fintype.piFinset fun _ : Fin 3 => if a ∈ S then ({-1, 0, 1} : Finset ℤ) else {0}).erase 0

lemma card_foldIdx (S : Finset (Fin eta)) : (foldIdx S).card = 27 ^ S.card - 1 := by
  classical
  unfold foldIdx
  rw [Finset.card_erase_of_mem]
  · rw [Fintype.card_piFinset]
    simp_rw [Fintype.card_piFinset]
    have e : ∀ a : Fin eta, (∏ _c : Fin 3, (if a ∈ S then ({-1, 0, 1} : Finset ℤ) else {0}).card) =
        if a ∈ S then 27 else 1 := by
      intro a
      split_ifs
      · simp
      · simp
    simp_rw [e]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  · rw [Fintype.mem_piFinset]
    intro a
    rw [Fintype.mem_piFinset]
    intro c
    split_ifs <;> simp

omit [Fintype ν] in
/-- At most `27^{|S|} - 1` exterior preimages lie in the output region. -/
lemma card_aliasFib_le (M : ℕ) (S : Finset (Fin eta)) (p : Cfg eta n)
    (hp : inZone M (cidx n p)) :
    ((aliasFib M p).filter fun q => OutReg M S (cidx n q)).card ≤ 27 ^ S.card - 1 := by
  classical
  rw [← card_foldIdx S]
  set ℓ : Cfg eta n → Fin eta → Fin 3 → ℤ :=
    fun q a c => (cidx n q a c - cfold M (cidx n q a c)) / (2 * M + 1) with hℓ
  have hpos : (0 : ℤ) < 2 * M + 1 := by omega
  have hrep : ∀ q ∈ (aliasFib M p).filter (fun q => OutReg M S (cidx n q)), ∀ a c,
      cidx n q a c = cidx n p a c + (2 * M + 1) * ℓ q a c := by
    intro q hq a c
    obtain ⟨hq1, -⟩ := Finset.mem_filter.mp hq
    obtain ⟨-, -, hf⟩ := Finset.mem_filter.mp hq1
    obtain ⟨k, hk⟩ := dvd_sub_cfold M (cidx n q a c)
    have hpc : cfold M (cidx n q a c) = cidx n p a c := congrFun (congrFun hf a) c
    simp only [hℓ]
    rw [hk, Int.mul_ediv_cancel_left _ hpos.ne', ← hk, hpc]
    ring
  refine Finset.card_le_card_of_injOn ℓ (fun q hq => ?_) (fun q hq q' hq' h => ?_)
  · obtain ⟨hq1, hout⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    obtain ⟨-, hz, hf⟩ := Finset.mem_filter.mp hq1
    rw [Finset.mem_coe, foldIdx, Finset.mem_erase]
    constructor
    · intro h0
      apply hz
      have : cidx n q = cidx n p := by
        funext a c
        rw [hrep q (Finset.mem_coe.mp hq) a c, show ℓ q a c = 0 from congrFun (congrFun h0 a) c]
        ring
      rw [this]; exact hp
    · rw [Fintype.mem_piFinset]
      intro a
      rw [Fintype.mem_piFinset]
      intro c
      split_ifs with ha
      · exact fold_index_mem M (hout.2 a ha c)
      · simp only [Finset.mem_singleton, hℓ]
        rw [cfold_of_abs_le M (hout.1 a ha c), sub_self, Int.zero_ediv]
  · have hq0 := Finset.mem_coe.mp hq
    have hq0' := Finset.mem_coe.mp hq'
    apply finiteConfigLatticeIndex_injective eta n
    change cidx n q = cidx n q'
    funext a c
    rw [hrep q hq0 a c, hrep q' hq0' a c, show ℓ q a c = ℓ q' a c from congrFun (congrFun h a) c]

omit [Fintype ν] in
/-- Every exterior configuration lies in at most one fibre. -/
lemma sum_fibres_le (M : ℕ) (f : Cfg eta n → ℝ) (hf : ∀ q, 0 ≤ f q)
    (P : Cfg eta n → Prop) [DecidablePred P] (Q : Cfg eta n → Prop) [DecidablePred Q] :
    ∑ p ∈ Finset.univ.filter P, ∑ q ∈ (aliasFib M p).filter Q, f q ≤
      ∑ q ∈ Finset.univ.filter (fun q => ¬ inZone M (cidx n q) ∧ Q q), f q := by
  classical
  have h1 : ∀ p, ∑ q ∈ (aliasFib M p).filter Q, f q =
      ∑ q, if ¬ inZone M (cidx n q) ∧ foldC M (cidx n q) = cidx n p ∧ Q q then f q else 0 := by
    intro p
    rw [aliasFib, Finset.filter_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [and_assoc]
  simp_rw [h1]
  calc ∑ p ∈ Finset.univ.filter P, ∑ q,
        (if ¬ inZone M (cidx n q) ∧ foldC M (cidx n q) = cidx n p ∧ Q q then f q else 0)
      ≤ ∑ p, ∑ q,
        (if ¬ inZone M (cidx n q) ∧ foldC M (cidx n q) = cidx n p ∧ Q q then f q else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p _ _ =>
          Finset.sum_nonneg fun q _ => by split_ifs <;> simp [hf])
    _ = ∑ q, ∑ p,
        (if ¬ inZone M (cidx n q) ∧ foldC M (cidx n q) = cidx n p ∧ Q q then f q else 0) :=
        Finset.sum_comm
    _ ≤ ∑ q, if ¬ inZone M (cidx n q) ∧ Q q then f q else 0 := by
        refine Finset.sum_le_sum fun q _ => ?_
        by_cases hq : ¬ inZone M (cidx n q) ∧ Q q
        · rw [if_pos hq]
          have hcard : (Finset.univ.filter fun p : Cfg eta n =>
              foldC M (cidx n q) = cidx n p).card ≤ 1 := by
            refine Finset.card_le_one.mpr fun p hp p' hp' => ?_
            apply finiteConfigLatticeIndex_injective eta n
            exact (Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hp').2
          calc ∑ p, (if ¬ inZone M (cidx n q) ∧ foldC M (cidx n q) = cidx n p ∧ Q q
                then f q else 0)
              = ∑ p ∈ Finset.univ.filter (fun p => foldC M (cidx n q) = cidx n p), f q := by
                rw [Finset.sum_filter]
                refine Finset.sum_congr rfl fun p _ => ?_
                by_cases hp : foldC M (cidx n q) = cidx n p
                · rw [if_pos ⟨hq.1, hp, hq.2⟩, if_pos hp]
                · rw [if_neg (fun h => hp h.2.1), if_neg hp]
            _ = (Finset.univ.filter fun p : Cfg eta n => foldC M (cidx n q) = cidx n p).card *
                f q := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 1 * f q := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hf q)
            _ = f q := one_mul _
        · rw [if_neg hq]
          refine le_of_eq (Finset.sum_eq_zero fun p _ => ?_)
          rw [if_neg]
          exact fun h => hq ⟨h.1, h.2.2⟩
    _ = ∑ q ∈ Finset.univ.filter (fun q => ¬ inZone M (cidx n q) ∧ Q q), f q :=
        (Finset.sum_filter _ _).symm

omit [Fintype ν] in
/-- The general alias estimate with an output restriction `Q` that folding can only increase
(`Q (fold q) → Q q`). -/
theorem alias_bound_gen (M : ℕ) (S : Finset (Fin eta)) (v : En eta n)
    (hv : ∀ q, v.ofLp q ≠ 0 → OutReg M S (cidx n q))
    (Q : Cfg eta n → Prop) [DecidablePred Q]
    (hQ : ∀ p q, q ∈ aliasFib M p → Q p → Q q) :
    ∑ p ∈ Finset.univ.filter Q, ‖(aliasOp M v).ofLp p‖ ^ 2 ≤
      (27 ^ S.card - 1 : ℕ) *
        ∑ q ∈ Finset.univ.filter (fun q => ¬ inZone M (cidx n q) ∧ Q q), ‖v.ofLp q‖ ^ 2 := by
  classical
  have hpt : ∀ p ∈ Finset.univ.filter Q, ‖(aliasOp M v).ofLp p‖ ^ 2 ≤
      (27 ^ S.card - 1 : ℕ) *
        ∑ q ∈ (aliasFib M p).filter (fun q => OutReg M S (cidx n q) ∧ Q q), ‖v.ofLp q‖ ^ 2 := by
    intro p hpQ
    have hQp := (Finset.mem_filter.mp hpQ).2
    unfold aliasOp
    simp only []
    split_ifs with hp
    · have hsum : ∑ q ∈ aliasFib M p, v.ofLp q =
          ∑ q ∈ (aliasFib M p).filter (fun q => OutReg M S (cidx n q) ∧ Q q), v.ofLp q := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun q hq => ?_
        by_cases hvq : v.ofLp q = 0
        · simp [hvq]
        · rw [if_pos ⟨hv q hvq, hQ p q hq hQp⟩]
      rw [hsum]
      have hsub : (aliasFib M p).filter (fun q => OutReg M S (cidx n q) ∧ Q q) ⊆
          (aliasFib M p).filter (fun q => OutReg M S (cidx n q)) := by
        intro q hq
        obtain ⟨h1, h2, -⟩ := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr ⟨h1, h2⟩
      have hcard : ((aliasFib M p).filter (fun q => OutReg M S (cidx n q) ∧ Q q)).card ≤
          27 ^ S.card - 1 := (Finset.card_le_card hsub).trans (card_aliasFib_le M S p hp)
      have hcs := (norm_sum_le _ _).trans (le_refl (∑ q ∈ (aliasFib M p).filter
        (fun q => OutReg M S (cidx n q) ∧ Q q), ‖v.ofLp q‖))
      have h2 : (∑ q ∈ (aliasFib M p).filter (fun q => OutReg M S (cidx n q) ∧ Q q),
          ‖v.ofLp q‖) ^ 2 ≤ ((aliasFib M p).filter (fun q => OutReg M S (cidx n q) ∧ Q q)).card *
            ∑ q ∈ (aliasFib M p).filter (fun q => OutReg M S (cidx n q) ∧ Q q), ‖v.ofLp q‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      calc ‖∑ q ∈ (aliasFib M p).filter (fun q => OutReg M S (cidx n q) ∧ Q q), v.ofLp q‖ ^ 2
          ≤ (∑ q ∈ (aliasFib M p).filter (fun q => OutReg M S (cidx n q) ∧ Q q),
              ‖v.ofLp q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hcs 2
        _ ≤ _ := h2
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have h := sum_fibres_le M (fun q => ‖v.ofLp q‖ ^ 2) (fun q => sq_nonneg _) Q
    (fun q => OutReg M S (cidx n q) ∧ Q q)
  refine h.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => sq_nonneg _))
  intro q hq
  obtain ⟨-, h1, -, h3⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h3⟩

omit [Fintype ν] in
/-- **eq:alias-mult**: `‖R v‖² ≤ (27^{|S|} - 1) ‖(1 - P') v‖²` for an output in the region of a
kernel acting on the registers `S`. -/
theorem alias_bound (M : ℕ) (S : Finset (Fin eta)) (v : En eta n)
    (hv : ∀ q, v.ofLp q ≠ 0 → OutReg M S (cidx n q)) :
    ‖aliasOp M v‖ ^ 2 ≤ (27 ^ S.card - 1 : ℕ) *
      ∑ q ∈ Finset.univ.filter (fun q => ¬ inZone M (cidx n q)), ‖v.ofLp q‖ ^ 2 := by
  classical
  have h := alias_bound_gen M S v hv (fun _ => True) (fun _ _ _ _ => trivial)
  rw [Finset.filter_true_of_mem (fun _ _ => trivial)] at h
  simp only [and_true] at h
  rw [FSKernel.norm_sq_eq]
  exact h

/-- The restriction `Q_{a,J} = 1{‖k_{p_a}‖_∞ > J}` (lattice units). -/
def supTail (a : Fin eta) (J : ℝ) (x : Cf eta) : Prop := ∃ c, J < |(x a c : ℝ)|

noncomputable instance (a : Fin eta) (J : ℝ) (x : Cf eta) : Decidable (supTail a J x) := by
  unfold supTail; infer_instance

omit [Fintype ν] in
/-- **eq:alias-restricted**: `‖Q_{a,J} R v‖² ≤ (27^{|S|} - 1) ‖Q_{a,J}(1 - P') v‖²`, because the
centred representative has no larger component than the unfolded index. -/
theorem alias_bound_restricted (M : ℕ) (S : Finset (Fin eta)) (v : En eta n)
    (hv : ∀ q, v.ofLp q ≠ 0 → OutReg M S (cidx n q)) (a : Fin eta) (J : ℝ) :
    ∑ p ∈ Finset.univ.filter (fun p => supTail a J (cidx n p)), ‖(aliasOp M v).ofLp p‖ ^ 2 ≤
      (27 ^ S.card - 1 : ℕ) * ∑ q ∈ Finset.univ.filter
        (fun q => ¬ inZone M (cidx n q) ∧ supTail a J (cidx n q)), ‖v.ofLp q‖ ^ 2 := by
  refine alias_bound_gen M S v hv _ fun p q hq hp => ?_
  obtain ⟨-, -, hf⟩ := Finset.mem_filter.mp hq
  obtain ⟨c, hc⟩ := hp
  refine ⟨c, lt_of_lt_of_le hc ?_⟩
  have h : cfold M (cidx n q a c) = cidx n p a c := congrFun (congrFun hf a) c
  rw [← h]
  exact_mod_cast abs_cfold_le M _

lemma sqrt728_le : Real.sqrt 728 ≤ 27 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

lemma card_pair (b c : Fin eta) (hbc : b ≠ c) : ({b, c} : Finset (Fin eta)).card = 2 := by
  rw [Finset.card_pair hbc]

/-! ## The collocation bounds -/

omit [Fintype ν] in
lemma zoneProj_eq_maskV (M : ℕ) (v : En eta n) :
    zoneProj M v = maskV (fun p => inZone M (cidx n p)) v := rfl

omit [Fintype ν] in
/-- `‖(1 - P') v‖ ≤ ‖v‖` in the form of a sum. -/
lemma sum_ext_le (M : ℕ) (v : En eta n) (Q : Cfg eta n → Prop) [DecidablePred Q] :
    ∑ q ∈ Finset.univ.filter (fun q => ¬ inZone M (cidx n q) ∧ Q q), ‖v.ofLp q‖ ^ 2 ≤
      ∑ q ∈ Finset.univ.filter Q, ‖v.ofLp q‖ ^ 2 :=
  Finset.sum_le_sum_of_subset_of_nonneg (fun _ hq => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2.2⟩) (fun _ _ _ => sq_nonneg _)

omit [Fintype ν] in
/-- `‖Q (Diag[g] u)‖ ≤ (1 + (27^{|S|} - 1)^{1/2}) ‖Q (g u)‖` for a restriction `Q` that folding can only
increase, when the output `g u` lies in the region of `S`. -/
theorem mask_gridDiag_le (M : ℕ) (S : Finset (Fin eta)) (κ : Cfg eta n → Cfg eta n → ℂ)
    (u : En eta n)
    (hv : ∀ q, (finiteCoefficientKernelOperator κ u).ofLp q ≠ 0 → OutReg M S (cidx n q))
    (Q : Cfg eta n → Prop) [DecidablePred Q] (hQ : ∀ p q, q ∈ aliasFib M p → Q p → Q q) :
    ‖maskV Q (gridDiag M κ u)‖ ≤
      (1 + Real.sqrt (27 ^ S.card - 1 : ℕ)) * ‖maskV Q (finiteCoefficientKernelOperator κ u)‖ := by
  set v := finiteCoefficientKernelOperator κ u
  have hsplit : maskV Q (gridDiag M κ u) = maskV Q (zoneProj M v) + maskV Q (aliasOp M v) := by
    ext p; simp [maskV, gridDiag, v]
    split_ifs <;> simp
  have h1 : ‖maskV Q (zoneProj M v)‖ ≤ ‖maskV Q v‖ := by
    have e1 := norm_maskV_sq Q (zoneProj M v)
    have e2 := norm_maskV_sq Q v
    have h : ∑ p ∈ Finset.univ.filter Q, ‖(zoneProj M v).ofLp p‖ ^ 2 ≤
        ∑ p ∈ Finset.univ.filter Q, ‖v.ofLp p‖ ^ 2 := by
      refine Finset.sum_le_sum fun p _ => ?_
      change ‖(if inZone M (cidx n p) then v.ofLp p else 0)‖ ^ 2 ≤ _
      split_ifs <;> simp
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
      (by rw [e1, e2]; exact h)
  have h2 : ‖maskV Q (aliasOp M v)‖ ≤ Real.sqrt (27 ^ S.card - 1 : ℕ) * ‖maskV Q v‖ := by
    have e1 := norm_maskV_sq Q (aliasOp M v)
    have e2 := norm_maskV_sq Q v
    have h := (alias_bound_gen M S v hv Q hQ).trans
      (mul_le_mul_of_nonneg_left (sum_ext_le M v Q) (Nat.cast_nonneg _))
    rw [← e1, ← e2] at h
    have h' : ‖maskV Q (aliasOp M v)‖ ^ 2 ≤
        (Real.sqrt (27 ^ S.card - 1 : ℕ) * ‖maskV Q v‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; exact h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'
  rw [hsplit]
  calc ‖maskV Q (zoneProj M v) + maskV Q (aliasOp M v)‖
      ≤ ‖maskV Q (zoneProj M v)‖ + ‖maskV Q (aliasOp M v)‖ := norm_add_le _ _
    _ ≤ ‖maskV Q v‖ + Real.sqrt (27 ^ S.card - 1 : ℕ) * ‖maskV Q v‖ := add_le_add h1 h2
    _ = _ := by ring

omit [Fintype ν] in
/-- **`‖Diag[g] u‖ ≤ 28 ‖g u‖`** for a pair term (`C_alias ≤ 27`), and for a single-register term. -/
theorem norm_gridDiag_le (M : ℕ) (S : Finset (Fin eta)) (hS : S.card ≤ 2)
    (κ : Cfg eta n → Cfg eta n → ℂ) (u : En eta n)
    (hv : ∀ q, (finiteCoefficientKernelOperator κ u).ofLp q ≠ 0 → OutReg M S (cidx n q)) :
    ‖gridDiag M κ u‖ ≤ 28 * ‖finiteCoefficientKernelOperator κ u‖ := by
  classical
  have h := mask_gridDiag_le M S κ u hv (fun _ => True) (fun _ _ _ _ => trivial)
  rw [maskV_true, maskV_true] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hc : ((27 ^ S.card - 1 : ℕ) : ℝ) ≤ 728 := by
    have : 27 ^ S.card ≤ 27 ^ 2 := Nat.pow_le_pow_right (by norm_num) hS
    have : 27 ^ S.card - 1 ≤ 728 := by omega
    exact_mod_cast this
  have := (Real.sqrt_le_sqrt hc).trans sqrt728_le
  linarith

omit [Fintype ν] in
/-- **The restricted collocation bound**: `‖Q_{a,J} Diag[g] u‖ ≤ 28 ‖Q_{a,J} g u‖`
(the step from eq:grid-tail to eq:grid-potential-tail). -/
theorem tail_gridDiag_le (M : ℕ) (S : Finset (Fin eta)) (hS : S.card ≤ 2)
    (κ : Cfg eta n → Cfg eta n → ℂ) (u : En eta n)
    (hv : ∀ q, (finiteCoefficientKernelOperator κ u).ofLp q ≠ 0 → OutReg M S (cidx n q))
    (a : Fin eta) (J : ℝ) :
    ‖maskV (fun p => supTail a J (cidx n p)) (gridDiag M κ u)‖ ≤
      28 * ‖maskV (fun p => supTail a J (cidx n p)) (finiteCoefficientKernelOperator κ u)‖ := by
  classical
  have h := mask_gridDiag_le M S κ u hv (fun p => supTail a J (cidx n p)) (fun p q hq hp => by
    obtain ⟨-, -, hf⟩ := Finset.mem_filter.mp hq
    obtain ⟨c, hc⟩ := hp
    refine ⟨c, lt_of_lt_of_le hc ?_⟩
    have h : cfold M (cidx n q a c) = cidx n p a c := congrFun (congrFun hf a) c
    rw [← h]
    exact_mod_cast abs_cfold_le M _)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hc : ((27 ^ S.card - 1 : ℕ) : ℝ) ≤ 728 := by
    have : 27 ^ S.card ≤ 27 ^ 2 := Nat.pow_le_pow_right (by norm_num) hS
    have : 27 ^ S.card - 1 ≤ 728 := by omega
    exact_mod_cast this
  have := (Real.sqrt_le_sqrt hc).trans sqrt728_le
  linarith

omit [Fintype ν] in
/-- The output of a kernel acting on the registers `S` with transfers at most `M` (`|k|_∞`) on a
zone state lies in the output region of `S`. -/
lemma outReg_of_kernel (M : ℕ) (S : Finset (Fin eta)) (κ : Cfg eta n → Cfg eta n → ℂ)
    (hκ : ∀ q p, κ q p ≠ 0 → (∀ a, a ∉ S → cidx n q a = cidx n p a) ∧
      ∀ a, a ∈ S → ∀ c, |cidx n q a c - cidx n p a c| ≤ M)
    (u : En eta n) (hu : ∀ p, u.ofLp p ≠ 0 → inZone M (cidx n p)) (q : Cfg eta n)
    (hq : (finiteCoefficientKernelOperator κ u).ofLp q ≠ 0) : OutReg M S (cidx n q) := by
  rw [fcko_apply] at hq
  obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
  have hu0 : u.ofLp p ≠ 0 := left_ne_zero_of_mul hp
  have hκ0 : κ q p ≠ 0 := right_ne_zero_of_mul hp
  obtain ⟨h1, h2⟩ := hκ q p hκ0
  have hz := hu p hu0
  refine ⟨fun a ha c => ?_, fun a ha c => ?_⟩
  · rw [h1 a ha]; exact hz a c
  · have h := h2 a ha c
    have hz' := hz a c
    calc |cidx n q a c| = |(cidx n q a c - cidx n p a c) + cidx n p a c| := by ring_nf
      _ ≤ |cidx n q a c - cidx n p a c| + |cidx n p a c| := abs_add_le _ _
      _ ≤ M + M := add_le_add h hz'
      _ = 2 * M := by ring

omit [Fintype ν] in
lemma foldC_of_inZone (M : ℕ) {x : Cf eta} (h : inZone M x) : foldC M x = x := by
  funext a c; exact cfold_of_abs_le M (h a c)

omit [Fintype ν] in
/-- **`Diag[g]` is the fold of the multiplication**: on a zone configuration `p`,
`(Diag[g] u)(p) = Σ_{t ≡ p (mod n')} (g u)(t)`, the sum over every configuration of the cube that
folds onto `p` (the momentum form of the collocation given by `lem:fold`). -/
theorem gridDiag_apply (M : ℕ) (κ : Cfg eta n → Cfg eta n → ℂ) (u : En eta n) (p : Cfg eta n)
    (hp : inZone M (cidx n p)) :
    (gridDiag M κ u).ofLp p = ∑ t ∈ Finset.univ.filter (fun t => foldC M (cidx n t) = cidx n p),
      (finiteCoefficientKernelOperator κ u).ofLp t := by
  classical
  set v := finiteCoefficientKernelOperator κ u
  have hsplit : Finset.univ.filter (fun t => foldC M (cidx n t) = cidx n p) =
      insert p (aliasFib M p) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, aliasFib]
    constructor
    · intro h
      by_cases ht : inZone M (cidx n t)
      · left
        apply finiteConfigLatticeIndex_injective eta n
        change cidx n t = cidx n p
        rw [← foldC_of_inZone M ht, h]
      · right; exact ⟨ht, h⟩
    · rintro (rfl | ⟨-, h⟩)
      · exact foldC_of_inZone M hp
      · exact h
  have hnot : p ∉ aliasFib M p := fun h => (Finset.mem_filter.mp h).2.1 hp
  rw [hsplit, Finset.sum_insert hnot]
  change (if inZone M (cidx n p) then v.ofLp p else 0) +
    (if inZone M (cidx n p) then ∑ q ∈ aliasFib M p, v.ofLp q else 0) = _
  rw [if_pos hp, if_pos hp]

/-! ## The grid Hamiltonian: graph norms and the lower bound -/

section GridHam

variable (sys : CoulombSystem eta ν) (L : ℝ)
variable {ι : Type*} [Fintype ι] (M : ℕ) (cpl : ι → ℝ) (κ : ι → Cfg eta n → Cfg eta n → ℂ)
  (S : ι → Finset (Fin eta)) (rr : ι → Fin eta) (X : ι → ℝ)

/-- The grid potential `V_grid = Σ_t c_t Diag[g_t]`. -/
noncomputable def gridV (u : En eta n) : En eta n := ∑ t, (cpl t : ℂ) • gridDiag M (κ t) u

/-- The grid Hamiltonian `H_grid = T + V_grid` on zone states. -/
noncomputable def gridH (u : En eta n) : En eta n :=
  FSSpectral.kin (sb eta n) (Asym sys L n) u + gridV M cpl κ u

/-- The coupling `Y = 28 Σ_t |c_t| X_t`. -/
noncomputable def gridY : ℝ := 28 * ∑ t, |cpl t| * X t

omit [Fintype ν] in
lemma gridY_nonneg (hX : ∀ t, 0 ≤ X t) : 0 ≤ gridY cpl X := by
  unfold gridY; have := Finset.sum_nonneg fun t (_ : t ∈ Finset.univ) =>
    mul_nonneg (abs_nonneg (cpl t)) (hX t)
  positivity

omit [Fintype ν] in
/-- `⟨u, T u⟩ = Σ_p A(p) |u_p|²`. -/
lemma re_inner_kin (u : En eta n) :
    (⟪u, FSSpectral.kin (sb eta n) (Asym sys L n) u⟫_ℂ).re = ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [kin_apply', Pi.star_apply, RCLike.star_def]
  have e : (Asym sys L n p : ℂ) * u.ofLp p * (starRingEnd ℂ) (u.ofLp p) =
      ((Asym sys L n p * ‖u.ofLp p‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, Complex.mul_conj']; push_cast; ring
  rw [e, Complex.ofReal_re]

omit [Fintype ν] in
lemma Asym_nonneg' (p : Cfg eta n) : 0 ≤ Asym sys L n p := by
  unfold Asym; have := massKineticSymbol_nonneg sys L n p; positivity

omit [Fintype ν] in
/-- The grid potential on a zone state: `‖V u‖ ≤ Y (‖u‖² + 2 m̄ ⟨u, T u⟩)^{1/2}`. -/
theorem norm_gridV_le (hS : ∀ t, (S t).card ≤ 2) (hX : ∀ t, 0 ≤ X t)
    (hA : ∀ t, HasWeightedOperatorBound
      (fun p => 1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p (rr t)) ^ 2)
      (finiteCoefficientKernelOperator (κ t)) (X t))
    (u : En eta n)
    (hv : ∀ t q, (finiteCoefficientKernelOperator (κ t) u).ofLp q ≠ 0 →
      OutReg M (S t) (cidx n q)) :
    ‖gridV M cpl κ u‖ ≤ gridY cpl X *
      Real.sqrt (‖u‖ ^ 2 + 2 * sys.maxMass * ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2) := by
  obtain ⟨R, hR⟩ : ∃ R, R = Real.sqrt (‖u‖ ^ 2 + 2 * sys.maxMass *
      ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2) := ⟨_, rfl⟩
  rw [← hR]
  have hT0 : 0 ≤ ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (Asym_nonneg' sys L p) (sq_nonneg _)
  have hm := sys.one_le_maxMass
  have hR0 : 0 ≤ R := by rw [hR]; exact Real.sqrt_nonneg _
  have hterm : ∀ t, ‖finiteCoefficientKernelOperator (κ t) u‖ ≤ X t * R := by
    intro t
    have h := hA t u
    have hw : weightedNormSq (fun p => 1 + finitePlaneWaveKabs (2 * Real.pi / L) n
        (p (rr t)) ^ 2) u ≤ ‖u‖ ^ 2 + 2 * sys.maxMass * ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2 := by
      unfold weightedNormSq
      rw [FSKernel.norm_sq_eq u, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun p _ => ?_
      have h1 := register_weight_le sys L (rr t) p
      have h2 := sys.mass_le_maxMass (rr t)
      have h3 := Asym_nonneg' sys L p
      have h4 : 1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p (rr t)) ^ 2 ≤
          1 + 2 * sys.maxMass * Asym sys L n p := by nlinarith
      nlinarith [sq_nonneg ‖u.ofLp p‖]
    have h' : ‖finiteCoefficientKernelOperator (κ t) u‖ ^ 2 ≤ (X t * R) ^ 2 := by
      rw [mul_pow, hR, Real.sq_sqrt (by positivity)]
      exact h.trans (mul_le_mul_of_nonneg_left hw (sq_nonneg _))
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by have := hX t; positivity) two_ne_zero).mp h'
  unfold gridV gridY
  calc ‖∑ t, (cpl t : ℂ) • gridDiag M (κ t) u‖
      ≤ ∑ t, ‖(cpl t : ℂ) • gridDiag M (κ t) u‖ := norm_sum_le _ _
    _ ≤ ∑ t, |cpl t| * (28 * (X t * R)) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact (norm_gridDiag_le M (S t) (hS t) (κ t) u (hv t)).trans
          (mul_le_mul_of_nonneg_left (hterm t) (by norm_num))
    _ = (28 * ∑ t, |cpl t| * X t) * R := by
        rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring

omit [Fintype ν] in
/-- `x y ≤ ε a + b/(4ε)·…`: the arithmetic–geometric step `Y s ≤ c + Y² s²/(4c)` in squared form. -/
lemma amgm_sq {x s c d : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : (x * s) ^ 2 ≤ 4 * c * d) : x * s ≤ c + d := by
  have h1 : (x * s) ^ 2 ≤ (c + d) ^ 2 := by nlinarith [sq_nonneg (c - d)]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1

omit [Fintype ν] in
/-- **eq:grid-form-lower**: `|⟨u, V u⟩| ≤ ε ⟨u, T u⟩ + (Y + Y²/(2ε)) m̄ ‖u‖²` for zone states. -/
theorem grid_form_lower (hS : ∀ t, (S t).card ≤ 2) (hX : ∀ t, 0 ≤ X t)
    (hA : ∀ t, HasWeightedOperatorBound
      (fun p => 1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p (rr t)) ^ 2)
      (finiteCoefficientKernelOperator (κ t)) (X t))
    (u : En eta n)
    (hv : ∀ t q, (finiteCoefficientKernelOperator (κ t) u).ofLp q ≠ 0 →
      OutReg M (S t) (cidx n q))
    {ε : ℝ} (hε : 0 < ε) :
    ‖⟪u, gridV M cpl κ u⟫_ℂ‖ ≤ ε * ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2 +
      (gridY cpl X + gridY cpl X ^ 2 / (2 * ε)) * sys.maxMass * ‖u‖ ^ 2 := by
  obtain ⟨T, hT⟩ : ∃ T, T = ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2 := ⟨_, rfl⟩
  rw [← hT]
  have hT0 : 0 ≤ T := by
    rw [hT]; exact Finset.sum_nonneg fun p _ => mul_nonneg (Asym_nonneg' sys L p) (sq_nonneg _)
  have hm : 1 ≤ sys.maxMass := sys.one_le_maxMass
  have hY := gridY_nonneg cpl X hX
  have ha := norm_nonneg u
  have hV := norm_gridV_le sys L M cpl κ S rr X hS hX hA u hv
  rw [← hT] at hV
  set Y := gridY cpl X
  set m := sys.maxMass
  have hs2 : Real.sqrt (2 * m * T) ^ 2 = 2 * m * T := Real.sq_sqrt (by positivity)
  have hs0 := Real.sqrt_nonneg (2 * m * T)
  have hsq : Real.sqrt (‖u‖ ^ 2 + 2 * m * T) ≤ ‖u‖ + Real.sqrt (2 * m * T) := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have key : ‖u‖ * Y * Real.sqrt (2 * m * T) ≤ ε * T + Y ^ 2 / (2 * ε) * m * ‖u‖ ^ 2 := by
    have e : ‖u‖ * Y * Real.sqrt (2 * m * T) = (‖u‖ * Y) * Real.sqrt (2 * m * T) := rfl
    refine amgm_sq (by positivity) hs0 (by positivity) (by positivity) ?_
    rw [mul_pow, hs2]
    have : 4 * (ε * T) * (Y ^ 2 / (2 * ε) * m * ‖u‖ ^ 2) = 2 * T * Y ^ 2 * m * ‖u‖ ^ 2 := by
      field_simp; ring
    rw [this]
    nlinarith
  have h2 : ‖u‖ * (Y * ‖u‖) ≤ Y * m * ‖u‖ ^ 2 := by
    have := mul_nonneg (mul_nonneg hY (sub_nonneg.mpr hm)) (sq_nonneg ‖u‖)
    nlinarith
  calc ‖⟪u, gridV M cpl κ u⟫_ℂ‖ ≤ ‖u‖ * ‖gridV M cpl κ u‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (Y * (‖u‖ + Real.sqrt (2 * m * T))) :=
        mul_le_mul_of_nonneg_left (hV.trans (mul_le_mul_of_nonneg_left hsq hY)) ha
    _ = ‖u‖ * (Y * ‖u‖) + ‖u‖ * Y * Real.sqrt (2 * m * T) := by ring
    _ ≤ Y * m * ‖u‖ ^ 2 + (ε * T + Y ^ 2 / (2 * ε) * m * ‖u‖ ^ 2) := add_le_add h2 key
    _ = ε * T + (Y + Y ^ 2 / (2 * ε)) * m * ‖u‖ ^ 2 := by ring

omit [Fintype ν] in
/-- **The `K`-uniform lower bound**: `Re ⟨u, H_grid u⟩ ≥ -(Y + Y²) m̄ ‖u‖²` for zone states
(`ε = 1/2` in eq:grid-form-lower). -/
theorem grid_lower_bound (hS : ∀ t, (S t).card ≤ 2) (hX : ∀ t, 0 ≤ X t)
    (hA : ∀ t, HasWeightedOperatorBound
      (fun p => 1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p (rr t)) ^ 2)
      (finiteCoefficientKernelOperator (κ t)) (X t))
    (u : En eta n)
    (hv : ∀ t q, (finiteCoefficientKernelOperator (κ t) u).ofLp q ≠ 0 →
      OutReg M (S t) (cidx n q)) :
    -((gridY cpl X + gridY cpl X ^ 2) * sys.maxMass * ‖u‖ ^ 2) ≤
      (⟪u, gridH sys L M cpl κ u⟫_ℂ).re := by
  have h := grid_form_lower sys L M cpl κ S rr X hS hX hA u hv (ε := 1 / 2) (by norm_num)
  have hre : (⟪u, gridH sys L M cpl κ u⟫_ℂ).re =
      ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2 + (⟪u, gridV M cpl κ u⟫_ℂ).re := by
    unfold gridH
    rw [inner_add_right, Complex.add_re, re_inner_kin]
  have hV : -‖⟪u, gridV M cpl κ u⟫_ℂ‖ ≤ (⟪u, gridV M cpl κ u⟫_ℂ).re := by
    have := Complex.abs_re_le_norm (⟪u, gridV M cpl κ u⟫_ℂ)
    linarith [neg_abs_le (⟪u, gridV M cpl κ u⟫_ℂ).re]
  have hT0 : 0 ≤ ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2 := Finset.sum_nonneg fun p _ =>
    mul_nonneg (Asym_nonneg' sys L p) (sq_nonneg _)
  have hY := gridY_nonneg cpl X hX
  have hm := sys.one_le_maxMass
  rw [hre]
  have e : gridY cpl X ^ 2 / (2 * (1 / 2)) = gridY cpl X ^ 2 := by ring
  rw [e] at h
  nlinarith [sq_nonneg ‖u‖]

omit [Fintype ν] in
/-- **eq:grid-graph-equivalence**: for zone states,
`‖H u‖ ≤ (3/2) Θ(u) + (Y + Y²) m̄ ‖u‖` and `Θ(u) ≤ 2 ‖H u‖ + (1 + 2Y + 2Y²) m̄ ‖u‖`, with
`Θ(u) = ‖(1 + A) u‖`. -/
theorem grid_graph_equivalence (hS : ∀ t, (S t).card ≤ 2) (hX : ∀ t, 0 ≤ X t)
    (hA : ∀ t, HasWeightedOperatorBound
      (fun p => 1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p (rr t)) ^ 2)
      (finiteCoefficientKernelOperator (κ t)) (X t))
    (u : En eta n)
    (hv : ∀ t q, (finiteCoefficientKernelOperator (κ t) u).ofLp q ≠ 0 →
      OutReg M (S t) (cidx n q)) :
    ‖gridH sys L M cpl κ u‖ ≤ 3 / 2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ +
        (gridY cpl X + gridY cpl X ^ 2) * sys.maxMass * ‖u‖ ∧
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ≤ 2 * ‖gridH sys L M cpl κ u‖ +
        (1 + 2 * gridY cpl X + 2 * gridY cpl X ^ 2) * sys.maxMass * ‖u‖ := by
  have hm : 1 ≤ sys.maxMass := sys.one_le_maxMass
  have hY := gridY_nonneg cpl X hX
  have ha := norm_nonneg u
  have hk0 := norm_nonneg (FSSpectral.kin (sb eta n) (Asym sys L n) u)
  -- `‖V u‖ ≤ k/2 + (Y + Y² m) ‖u‖`
  have hV := norm_gridV_le sys L M cpl κ S rr X hS hX hA u hv
  have hTk := sum_Asym_le sys L u
  obtain ⟨k, hk⟩ : ∃ k, k = ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖ := ⟨_, rfl⟩
  rw [← hk] at hTk hk0
  set Y := gridY cpl X
  set m := sys.maxMass
  have hV2 : ‖gridV M cpl κ u‖ ≤ k / 2 + (Y + Y ^ 2 * m) * ‖u‖ := by
    have hs2 : Real.sqrt (2 * m * (‖u‖ * k)) ^ 2 = 2 * m * (‖u‖ * k) :=
      Real.sq_sqrt (by positivity)
    have hs0 := Real.sqrt_nonneg (2 * m * (‖u‖ * k))
    have hsq : Real.sqrt (‖u‖ ^ 2 + 2 * m * ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2) ≤
        ‖u‖ + Real.sqrt (2 * m * (‖u‖ * k)) := by
      rw [Real.sqrt_le_left (by positivity)]
      have h2 : 2 * m * ∑ p, Asym sys L n p * ‖u.ofLp p‖ ^ 2 ≤ 2 * m * (‖u‖ * k) :=
        mul_le_mul_of_nonneg_left hTk (by positivity)
      nlinarith
    have hamgm : Y * Real.sqrt (2 * m * (‖u‖ * k)) ≤ k / 2 + Y ^ 2 * m * ‖u‖ := by
      refine amgm_sq hY hs0 (by positivity) (by positivity) ?_
      rw [mul_pow, hs2]
      nlinarith
    calc ‖gridV M cpl κ u‖ ≤ Y * (‖u‖ + Real.sqrt (2 * m * (‖u‖ * k))) :=
          hV.trans (mul_le_mul_of_nonneg_left hsq hY)
      _ = Y * ‖u‖ + Y * Real.sqrt (2 * m * (‖u‖ * k)) := by ring
      _ ≤ Y * ‖u‖ + (k / 2 + Y ^ 2 * m * ‖u‖) := add_le_add le_rfl hamgm
      _ = k / 2 + (Y + Y ^ 2 * m) * ‖u‖ := by ring
  -- `k ≤ Θ ≤ ‖u‖ + k`
  have hwt : FSSpectral.wt (sb eta n) (Asym sys L n) 1 u =
      u + FSSpectral.kin (sb eta n) (Asym sys L n) u := by
    ext q; rw [wt_one_apply, PiLp.add_apply, kin_apply']; push_cast; ring
  have hkΘ : k ≤ ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
    have e1 := FSKernel.norm_sq_eq (FSSpectral.kin (sb eta n) (Asym sys L n) u)
    have e2 := FSKernel.norm_sq_eq (FSSpectral.wt (sb eta n) (Asym sys L n) 1 u)
    have h : ∑ q, ‖(FSSpectral.kin (sb eta n) (Asym sys L n) u).ofLp q‖ ^ 2 ≤
        ∑ q, ‖(FSSpectral.wt (sb eta n) (Asym sys L n) 1 u).ofLp q‖ ^ 2 := by
      refine Finset.sum_le_sum fun q _ => ?_
      have hq := Asym_nonneg' sys L q
      rw [kin_apply', wt_one_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq, abs_of_nonneg (by linarith)]
      have : Asym sys L n q ≤ 1 + Asym sys L n q := by linarith
      gcongr
    rw [← e1, ← e2] at h
    rw [hk]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  have hΘk : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ≤ ‖u‖ + k := by
    rw [hwt, hk]; exact norm_add_le _ _
  have hH : gridH sys L M cpl κ u =
      FSSpectral.kin (sb eta n) (Asym sys L n) u + gridV M cpl κ u := rfl
  constructor
  · rw [hH]
    calc ‖FSSpectral.kin (sb eta n) (Asym sys L n) u + gridV M cpl κ u‖
        ≤ k + ‖gridV M cpl κ u‖ := by rw [hk]; exact norm_add_le _ _
      _ ≤ k + (k / 2 + (Y + Y ^ 2 * m) * ‖u‖) := add_le_add le_rfl hV2
      _ ≤ 3 / 2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ + (Y + Y ^ 2) * m * ‖u‖ := by
          nlinarith [mul_nonneg hY ha, mul_nonneg (sq_nonneg Y) ha]
  · have h1 : k ≤ ‖gridH sys L M cpl κ u‖ + ‖gridV M cpl κ u‖ := by
      have e : FSSpectral.kin (sb eta n) (Asym sys L n) u =
          gridH sys L M cpl κ u - gridV M cpl κ u := by rw [hH]; abel
      calc k = ‖gridH sys L M cpl κ u - gridV M cpl κ u‖ := by rw [hk, ← e]
        _ ≤ _ := norm_sub_le _ _
    nlinarith [mul_nonneg hY ha, mul_nonneg (sq_nonneg Y) ha]

end GridHam

end FSNormal
