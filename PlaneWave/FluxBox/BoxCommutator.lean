import PlaneWave.FluxBox.BoxHardy

/-!
# Flux route, stage 2, part 5: the box commutator on good states

* `lattice_fibre_sq_le`: Young's inequality on channel fibres for finitely supported lattice
  functions (`FSKernel.norm_kop_fibre_sq_le` on the subtype of a finite set);
* `sum_out_le`: the out-of-box potential output `Σ_{y ∈ B_{3N} ∖ B_N} (Σ_q |v_q| M(q - y))²` is at
  most `C (N⁻¹ ‖(1+A)v‖² + Σ_a ‖(1+A) Q_{a, gN/2} v‖²)`: hops from `B_{N/2}` out of `B_N` have
  `|θ| > N/2` (`Σ_{|θ|>R} |θ|⁻⁴ ≤ 250/R`), the rest carries a register tail at `gN/2`;
* **`norm_ebd_good`**: `|e_bd(v)| ≤ C_bd M² (1/N + 1/(gN))` for a good box state.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section LatticeYoung

omit [Fintype ν] in
open Classical in
/-- **Young's inequality on channel fibres for finitely supported lattice functions.** -/
theorem lattice_fibre_sq_le (j : Ch eta) (k₀ : Lattice3 → ℝ) (hk₀ : ∀ θ, 0 ≤ k₀ θ) {K₂ : ℝ}
    (hK₂ : ∀ S : Finset Lattice3, ∑ θ ∈ S, k₀ θ ^ 2 ≤ K₂)
    (D T : Finset (Cf eta)) (a : Cf eta → ℝ) :
    ∑ y ∈ T, (∑ x ∈ D, a x * (if OnCh j y x then k₀ (y (lead j) - x (lead j)) else 0)) ^ 2 ≤
      K₂ * FSChannel.Zs 2 * ∑ x ∈ D, (1 + FSLattice.lsq (x (lead j))) ^ 2 * a x ^ 2 := by
  classical
  set U := D ∪ T
  let u : EuclideanSpace ℂ U := WithLp.toLp 2 (fun x => if x.1 ∈ D then (a x.1 : ℂ) else 0)
  let κ : U → U → ℂ := fun y x => if OnCh j y.1 x.1 then (k₀ (y.1 (lead j) - x.1 (lead j)) : ℂ) else 0
  have hY := FSKernel.norm_kop_fibre_sq_le (fun x : U => labC j x.1) (fun x : U => x.1 (lead j))
    (fun x y h1 h2 => Subtype.ext (eq_of_labC_lead h1 h2)) κ k₀ hk₀ hK₂ (by
      intro y x
      simp only [κ]
      split_ifs with h1 h2
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk₀ _)]
      · exact absurd (labC_eq_of_onCh h1) h2
      · rw [norm_zero]; exact hk₀ _
      · rw [norm_zero]) u
  -- the output at `y`
  have hout : ∀ y : U, (FSKernel.kop κ u).ofLp y =
      ((∑ x ∈ D, a x * (if OnCh j y.1 x then k₀ (y.1 (lead j) - x (lead j)) else 0) : ℝ) : ℂ) := by
    intro y
    rw [FSKernel.kop_apply]
    have e1 : ∑ x : U, u.ofLp x * κ y x =
        ∑ x ∈ U, (if x ∈ D then ((a x * (if OnCh j y.1 x then k₀ (y.1 (lead j) - x (lead j))
          else 0) : ℝ) : ℂ) else 0) := by
      rw [← Finset.sum_coe_sort U]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [u, κ]
      split_ifs <;> push_cast <;> ring
    rw [e1, ← Finset.sum_filter]
    have e2 : U.filter (fun x => x ∈ D) = D := by
      ext x; simp only [Finset.mem_filter, U, Finset.mem_union]; tauto
    rw [e2]
    push_cast
    rfl
  have hlhs : ∑ y ∈ T, (∑ x ∈ D, a x * (if OnCh j y x then k₀ (y (lead j) - x (lead j)) else 0)) ^ 2 ≤
      ‖FSKernel.kop κ u‖ ^ 2 := by
    rw [FSKernel.norm_sq_eq]
    have hT : T ⊆ U := Finset.subset_union_right
    have e3 : ∑ y : U, ‖(FSKernel.kop κ u).ofLp y‖ ^ 2 = ∑ y ∈ U,
        (∑ x ∈ D, a x * (if OnCh j y x then k₀ (y (lead j) - x (lead j)) else 0)) ^ 2 := by
      rw [← Finset.sum_coe_sort U]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hout y, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [e3]
    exact Finset.sum_le_sum_of_subset_of_nonneg hT fun y _ _ => sq_nonneg _
  have hrhs : ∑ x : U, (1 + FSLattice.lsq (x.1 (lead j))) ^ 2 * ‖u.ofLp x‖ ^ 2 =
      ∑ x ∈ D, (1 + FSLattice.lsq (x (lead j))) ^ 2 * a x ^ 2 := by
    have e4 : ∑ x : U, (1 + FSLattice.lsq (x.1 (lead j))) ^ 2 * ‖u.ofLp x‖ ^ 2 =
        ∑ x ∈ U, (if x ∈ D then (1 + FSLattice.lsq (x (lead j))) ^ 2 * a x ^ 2 else 0) := by
      rw [← Finset.sum_coe_sort U]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [u]
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      · rw [norm_zero]; ring
    rw [e4, ← Finset.sum_filter]
    have e2 : U.filter (fun x => x ∈ D) = D := by
      ext x; simp only [Finset.mem_filter, U, Finset.mem_union]; tauto
    rw [e2]
  rw [hrhs] at hY
  exact hlhs.trans hY

end LatticeYoung

/-! ## Coulomb sums -/

section CoulSums

/-- `Σ_θ (c/|θ|²)² ≤ 4 c² Z₂`. -/
lemma sum_coul_sq_le (c : ℝ) (S : Finset Lattice3) :
    ∑ θ ∈ S, (c / FSLattice.lsq θ) ^ 2 ≤ c ^ 2 * 4 * FSChannel.Zs 2 := by
  have hw := FSLattice.sum_weight_le (by norm_num : (3 : ℝ) / 2 < 2) S
  have hterm : ∀ θ ∈ S, (c / FSLattice.lsq θ) ^ 2 ≤ c ^ 2 * 4 * (1 + FSLattice.lsq θ) ^ (-(2 : ℝ)) := by
    intro θ _
    have hpos : 0 < 1 + FSLattice.lsq θ := by have := FSLattice.lsq_nonneg θ; linarith
    rw [Real.rpow_neg hpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    by_cases h0 : FSLattice.lsq θ = 0
    · rw [h0, div_zero]; norm_num; positivity
    · have hl1 : 1 ≤ FSLattice.lsq θ := by
        have hθ : θ ≠ 0 := by intro h; rw [h, FSLattice.lsq_zero] at h0; exact h0 rfl
        exact one_le_latticeNormSq hθ
      rw [div_pow]
      have h2 : 1 / FSLattice.lsq θ ^ 2 ≤ 4 * ((1 + FSLattice.lsq θ) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc c ^ 2 / FSLattice.lsq θ ^ 2 = c ^ 2 * (1 / FSLattice.lsq θ ^ 2) := by ring
        _ ≤ c ^ 2 * (4 * ((1 + FSLattice.lsq θ) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = _ := by ring
  calc ∑ θ ∈ S, (c / FSLattice.lsq θ) ^ 2 ≤ ∑ θ ∈ S, c ^ 2 * 4 * (1 + FSLattice.lsq θ) ^ (-(2 : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = c ^ 2 * 4 * ∑ θ ∈ S, (1 + FSLattice.lsq θ) ^ (-(2 : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ c ^ 2 * 4 * FSChannel.Zs 2 := by
        gcongr
        simpa [FSChannel.Zs] using hw

open Classical in
/-- `Σ_{|θ| > R} (c/|θ|²)² ≤ 250 c²/R` (`R ≥ 1`). -/
lemma sum_coul_sq_tail_le (c : ℝ) {R : ℝ} (hR : 1 ≤ R) (S : Finset Lattice3) :
    ∑ θ ∈ S, (if R ^ 2 < FSLattice.lsq θ then c / FSLattice.lsq θ else 0) ^ 2 ≤ c ^ 2 * (250 / R) := by
  have h := FSLattice.sum_tail_inv_sq_le S hR
  calc ∑ θ ∈ S, (if R ^ 2 < FSLattice.lsq θ then c / FSLattice.lsq θ else 0) ^ 2
      = ∑ θ ∈ S.filter (fun θ => R ^ 2 < FSLattice.lsq θ), c ^ 2 * (1 / FSLattice.lsq θ ^ 2) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun θ _ => ?_
        split_ifs
        · ring
        · ring
    _ = c ^ 2 * ∑ θ ∈ S.filter (fun θ => R ^ 2 < FSLattice.lsq θ), 1 / FSLattice.lsq θ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ c ^ 2 * (250 / R) := mul_le_mul_of_nonneg_left h (sq_nonneg _)

end CoulSums

/-! ## The out-of-box output of a box vector -/

section OutBox

variable (sys : CoulombSystem eta ν) {L : ℝ} {N : ℕ}

/-- The lattice profile of a box vector: `a(cidx q) = |v_q|`, `0` off the box. -/
noncomputable def lprof (v : En eta N) (x : Cf eta) : ℝ :=
  ∑ q, if cidx N q = x then ‖v.ofLp q‖ else 0

omit [Fintype ν] in
lemma lprof_cidx (v : En eta N) (q : Cfg eta N) : lprof v (cidx N q) = ‖v.ofLp q‖ := by
  unfold lprof
  rw [Finset.sum_eq_single q]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    exact fun h => hb (finiteConfigLatticeIndex_injective eta N h)
  · intro h; exact absurd (Finset.mem_univ q) h

omit [Fintype ν] in
lemma lprof_nonneg (v : En eta N) (x : Cf eta) : 0 ≤ lprof v x :=
  Finset.sum_nonneg fun q _ => by
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl

omit [Fintype ν] in
lemma abs_tr_le (j : Ch eta) (θ : Lattice3) (c : Fin eta) (i : Fin 3) :
    |((tr j θ c i : ℤ) : ℝ)| ≤ |((θ i : ℤ) : ℝ)| := by
  by_cases hc : c ∈ moved j
  · rcases tr_apply_moved j θ hc with h | h
    · rw [h]
    · rw [h, Pi.neg_apply, Int.cast_neg, abs_neg]
  · rw [tr_apply_not_moved j θ hc]; simp

omit [Fintype ν] in
lemma sq_coord_le_lsq (θ : Lattice3) (i : Fin 3) : ((θ i : ℤ) : ℝ) ^ 2 ≤ FSLattice.lsq θ := by
  unfold FSLattice.lsq
  fin_cases i <;> simp <;> nlinarith [sq_nonneg ((θ 0 : ℤ) : ℝ), sq_nonneg ((θ 1 : ℤ) : ℝ),
    sq_nonneg ((θ 2 : ℤ) : ℝ)]

omit [Fintype ν] in
/-- A hop from `B_{N/2}` out of `B_N` has `|θ| > N/2`. -/
lemma out_hop_large {j : Ch eta} {x y : Cf eta} (hy : y ∉ fourierConfigCube eta N)
    (hx : InP ((N : ℝ) / 2) x) (h : OnCh j y x) :
    ((N : ℝ) / 2) ^ 2 < FSLattice.lsq (y (lead j) - x (lead j)) := by
  by_contra hle
  push Not at hle
  apply hy
  rw [← inP_iff_mem_cube]
  intro c i
  have e : y = x + tr j (y (lead j) - x (lead j)) := h
  set θ := y (lead j) - x (lead j)
  have h1 : y c i = x c i + tr j θ c i := by rw [e]; simp
  have h2 := abs_tr_le j θ c i
  have h3 := sq_coord_le_lsq θ i
  have hN0 : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have h4 : |((θ i : ℤ) : ℝ)| ≤ (N : ℝ) / 2 := by
    rw [← Real.sqrt_sq (abs_nonneg _), sq_abs, ← Real.sqrt_sq hN0]
    exact Real.sqrt_le_sqrt (h3.trans hle)
  have h5 := hx c i
  rw [h1, Int.cast_add]
  calc |((x c i : ℤ) : ℝ) + ((tr j θ c i : ℤ) : ℝ)| ≤ |((x c i : ℤ) : ℝ)| + |((tr j θ c i : ℤ) : ℝ)| :=
        abs_add_le _ _
    _ ≤ (N : ℝ) / 2 + (N : ℝ) / 2 := add_le_add h5 (h2.trans h4)
    _ = N := by ring

end OutBox

section OutBox2

variable (sys : CoulombSystem eta ν) {L : ℝ} {N : ℕ}

open Classical in
/-- **The out-of-box potential output** of a box vector: hops from `B_{N/2}` out of `B_N` are
long, the rest carries the tail beyond `B_{N/2}`. -/
theorem sum_out_le (hL : 0 < L) (hN : 2 ≤ N) (v : En eta N) :
    ∑ y ∈ fourierConfigCube eta (3 * N) \ fourierConfigCube eta N,
        (∑ q, ‖v.ofLp q‖ * Mp sys L (cidx N q - y)) ^ 2 ≤
      2 * (Fintype.card (Ch eta) : ℝ) * ∑ j : Ch eta, chC sys L j ^ 2 * FSChannel.Zs 2 *
        ((500 / N) * ∑ q, (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2 +
          4 * FSChannel.Zs 2 * ∑ q, (if InP ((N : ℝ) / 2) (cidx N q) then 0 else
            (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2)) := by
  set C := fourierConfigCube eta N
  set T := fourierConfigCube eta (3 * N) \ C
  set a := lprof v
  have ha : ∀ q, a (cidx N q) = ‖v.ofLp q‖ := fun q => lprof_cidx v q
  set ain : Cf eta → ℝ := fun x => if InP ((N : ℝ) / 2) x then a x else 0
  set aout : Cf eta → ℝ := fun x => if InP ((N : ℝ) / 2) x then 0 else a x
  set kf : Ch eta → Lattice3 → ℝ := fun j θ => chC sys L j / FSLattice.lsq θ
  set kt : Ch eta → Lattice3 → ℝ := fun j θ =>
    if ((N : ℝ) / 2) ^ 2 < FSLattice.lsq θ then chC sys L j / FSLattice.lsq θ else 0
  set bin : Ch eta → Cf eta → ℝ := fun j y =>
    ∑ x ∈ C, ain x * (if OnCh j y x then kt j (y (lead j) - x (lead j)) else 0)
  set bout : Ch eta → Cf eta → ℝ := fun j y =>
    ∑ x ∈ C, aout x * (if OnCh j y x then kf j (y (lead j) - x (lead j)) else 0)
  have hN2 : (1 : ℝ) ≤ (N : ℝ) / 2 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  -- step 1: the decomposition on `T`
  have hdec : ∀ y ∈ T, ∑ q, ‖v.ofLp q‖ * Mp sys L (cidx N q - y) = ∑ j, (bin j y + bout j y) := by
    intro y hy
    have hyC : y ∉ C := (Finset.mem_sdiff.mp hy).2
    have e1 : ∀ q : Cfg eta N, ‖v.ofLp q‖ * Mp sys L (cidx N q - y) =
        ∑ j, a (cidx N q) * (if OnCh j y (cidx N q) then kf j (y (lead j) - cidx N q (lead j)) else 0) := by
      intro q
      unfold Mp
      rw [potMaj_sub, ha]
      unfold potMaj
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold chMaj
      congr 1
      by_cases h : OnCh j (cidx N q) y
      · rw [if_pos h, if_pos (onCh_symm h)]
        simp only [kf]
        congr 1
        have : cidx N q (lead j) - y (lead j) = -(y (lead j) - cidx N q (lead j)) := by abel
        rw [this]
        show latticeNormSq _ = latticeNormSq _
        simp only [latticeNormSq, Pi.neg_apply, Pi.sub_apply, Int.cast_neg, Int.cast_sub]
        ring
      · rw [if_neg h, if_neg (fun h' => h (onCh_symm h'))]
    rw [Finset.sum_congr rfl fun q _ => e1 q, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sum_cfg_eq_sum_cube N (fun x => a x * (if OnCh j y x then kf j (y (lead j) - x (lead j)) else 0))]
    simp only [bin, bout]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [ain, aout]
    by_cases hx : InP ((N : ℝ) / 2) x
    · rw [if_pos hx, if_pos hx, zero_mul, add_zero]
      congr 1
      by_cases h : OnCh j y x
      · rw [if_pos h, if_pos h]
        simp only [kt, kf]
        rw [if_pos (out_hop_large hyC hx h)]
      · rw [if_neg h, if_neg h]
    · rw [if_neg hx, if_neg hx, zero_mul, zero_add]
  -- step 2: Cauchy–Schwarz over channels and `(u + w)² ≤ 2u² + 2w²`
  have hcs : ∀ y ∈ T, (∑ q, ‖v.ofLp q‖ * Mp sys L (cidx N q - y)) ^ 2 ≤
      (Fintype.card (Ch eta) : ℝ) * ∑ j, (2 * bin j y ^ 2 + 2 * bout j y ^ 2) := by
    intro y hy
    rw [hdec y hy]
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => bin j y + bout j y)
    rw [Finset.card_univ] at h1
    refine h1.trans ?_
    gcongr with j
    nlinarith [sq_nonneg (bin j y - bout j y)]
  -- step 3: Young on fibres, channel by channel
  have hkt0 : ∀ j θ, 0 ≤ kt j θ := fun j θ => by
    simp only [kt]; split_ifs
    · exact div_nonneg (chC_nonneg sys hL j) (FSLattice.lsq_nonneg θ)
    · exact le_rfl
  have hkf0 : ∀ j θ, 0 ≤ kf j θ := fun j θ =>
    div_nonneg (chC_nonneg sys hL j) (FSLattice.lsq_nonneg θ)
  have hYin : ∀ j, ∑ y ∈ T, bin j y ^ 2 ≤
      chC sys L j ^ 2 * (250 / ((N : ℝ) / 2)) * FSChannel.Zs 2 *
        ∑ x ∈ C, (1 + FSLattice.lsq (x (lead j))) ^ 2 * ain x ^ 2 := fun j =>
    lattice_fibre_sq_le j (kt j) (hkt0 j) (fun S => sum_coul_sq_tail_le (chC sys L j) hN2 S) C T ain
  have hYout : ∀ j, ∑ y ∈ T, bout j y ^ 2 ≤
      chC sys L j ^ 2 * 4 * FSChannel.Zs 2 * FSChannel.Zs 2 *
        ∑ x ∈ C, (1 + FSLattice.lsq (x (lead j))) ^ 2 * aout x ^ 2 := fun j =>
    lattice_fibre_sq_le j (kf j) (hkf0 j) (fun S => sum_coul_sq_le (chC sys L j) S) C T aout
  -- step 4: back to the box
  have hin : ∀ j, ∑ x ∈ C, (1 + FSLattice.lsq (x (lead j))) ^ 2 * ain x ^ 2 ≤
      ∑ q, (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2 := by
    intro j
    rw [← sum_cfg_eq_sum_cube N (fun x => (1 + FSLattice.lsq (x (lead j))) ^ 2 * ain x ^ 2)]
    refine Finset.sum_le_sum fun q _ => ?_
    simp only [ain]
    split_ifs
    · rw [ha]
    · rw [sq (0 : ℝ), mul_zero, mul_zero]; positivity
  have hout : ∀ j, ∑ x ∈ C, (1 + FSLattice.lsq (x (lead j))) ^ 2 * aout x ^ 2 =
      ∑ q, (if InP ((N : ℝ) / 2) (cidx N q) then 0 else
        (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2) := by
    intro j
    rw [← sum_cfg_eq_sum_cube N (fun x => (1 + FSLattice.lsq (x (lead j))) ^ 2 * aout x ^ 2)]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [aout]
    split_ifs
    · ring
    · rw [ha]
  -- assemble
  have hZ : 0 ≤ FSChannel.Zs 2 := (FSChannel.Zs_pos (by norm_num)).le
  calc ∑ y ∈ T, (∑ q, ‖v.ofLp q‖ * Mp sys L (cidx N q - y)) ^ 2
      ≤ ∑ y ∈ T, (Fintype.card (Ch eta) : ℝ) * ∑ j, (2 * bin j y ^ 2 + 2 * bout j y ^ 2) :=
        Finset.sum_le_sum hcs
    _ = ∑ y ∈ T, ∑ j, (Fintype.card (Ch eta) : ℝ) * (2 * bin j y ^ 2 + 2 * bout j y ^ 2) :=
        Finset.sum_congr rfl fun y _ => Finset.mul_sum _ _ _
    _ = ∑ j, ∑ y ∈ T, (Fintype.card (Ch eta) : ℝ) * (2 * bin j y ^ 2 + 2 * bout j y ^ 2) :=
        Finset.sum_comm
    _ = 2 * (Fintype.card (Ch eta) : ℝ) * ∑ j, (∑ y ∈ T, bin j y ^ 2 + ∑ y ∈ T, bout j y ^ 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ _ := by
        gcongr with j
        have h1 := hYin j
        have h2 := hYout j
        have h3 := hin j
        have h4 := hout j
        have hc2 : 0 ≤ chC sys L j ^ 2 := sq_nonneg _
        have e250 : (250 : ℝ) / ((N : ℝ) / 2) = 500 / N := by field_simp; ring
        rw [e250] at h1
        rw [h4] at h2
        have h5 : chC sys L j ^ 2 * (500 / N) * FSChannel.Zs 2 *
            ∑ x ∈ C, (1 + FSLattice.lsq (x (lead j))) ^ 2 * ain x ^ 2 ≤
            chC sys L j ^ 2 * (500 / N) * FSChannel.Zs 2 *
            ∑ q, (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        nlinarith

end OutBox2

/-! ## The box commutator on good states -/

section EbdGood

variable (sys : CoulombSystem eta ν) {L : ℝ} {N : ℕ}

/-- The constant of `norm_ebd_good`. -/
noncomputable def Cbd (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  4 * Fintype.card (Ch eta) * (∑ j : Ch eta, chC sys L j ^ 2) * FSChannel.Zs 2 * FSNormal.cE sys L ^ 2 *
    (500 + 8 * eta * FSChannel.Zs 2)

omit [Fintype ν] in
lemma lead_weight_le (hL : 0 < L) (j : Ch eta) (q : Cfg eta N) :
    1 + FSLattice.lsq (cidx N q (lead j)) ≤ FSNormal.cE sys L * (1 + Asym sys L N q) := by
  have h1 := FSNormal.one_add_lsqC_le sys hL (cidx N q)
  have h2 : FSLattice.lsq (cidx N q (lead j)) ≤ lsqC (cidx N q) := by
    unfold lsqC
    exact Finset.single_le_sum (f := fun c => nsq (cidx N q c)) (fun c _ => nsq_nonneg _)
      (Finset.mem_univ (lead j))
  rw [Asym_eq_Ek]
  linarith

omit [Fintype ν] in
lemma sum_lead_weight_le (hL : 0 < L) (j : Ch eta) (v : En eta N) :
    ∑ q, (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2 ≤
      FSNormal.cE sys L ^ 2 * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 v‖ ^ 2 := by
  rw [FSKernel.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [wt_one_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by have := Asym_nonneg sys L N q; linarith), mul_pow]
  have h0 : 0 ≤ 1 + FSLattice.lsq (cidx N q (lead j)) := by
    have := FSLattice.lsq_nonneg (cidx N q (lead j)); linarith
  have h4 := pow_le_pow_left₀ h0 (lead_weight_le sys hL j q) 2
  rw [mul_pow] at h4
  nlinarith [sq_nonneg ‖v.ofLp q‖]

omit [Fintype ν] in
open Classical in
lemma sum_out_weight_le (hL : 0 < L) (j : Ch eta) (v : En eta N) :
    ∑ q, (if InP ((N : ℝ) / 2) (cidx N q) then 0 else
        (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2) ≤
      FSNormal.cE sys L ^ 2 * ∑ c : Fin eta,
        ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (regTail L c (gF L * N / 2) v)‖ ^ 2 := by
  have hg := gF_pos hL
  rw [Finset.mul_sum]
  simp_rw [FSKernel.norm_sq_eq]
  rw [← Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun q _ => ?_
  split_ifs with hq
  · exact Finset.sum_nonneg fun c _ => by positivity
  · -- a register beyond `N/2`
    simp only [InP, not_forall, not_le] at hq
    obtain ⟨c, i, hci⟩ := hq
    have hlsq : ((N : ℝ) / 2) ^ 2 < FSLattice.lsq (cidx N q c) := by
      have h1 := sq_coord_le_lsq (cidx N q c) i
      have h2 : ((N : ℝ) / 2) ^ 2 < ((cidx N q c i : ℤ) : ℝ) ^ 2 := by
        have : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
        rw [← sq_abs (((cidx N q c i : ℤ) : ℝ))]
        exact pow_lt_pow_left₀ hci this two_ne_zero
      linarith
    have hk : gF L * N / 2 < finitePlaneWaveKabs (2 * Real.pi / L) N (q c) := by
      have e := kabs_sq_eq (n := N) L (q c)
      have hk0 := kabs_nonneg (n := N) hL (q c)
      have hgl : gL L = gF L := rfl
      rw [hgl] at e
      have : (gF L * N / 2) ^ 2 < finitePlaneWaveKabs (2 * Real.pi / L) N (q c) ^ 2 := by
        rw [e, show gF L * N / 2 = gF L * (N / 2) by ring, mul_pow]
        exact mul_lt_mul_of_pos_left hlsq (by positivity)
      have h0 : 0 ≤ gF L * N / 2 := by positivity
      exact lt_of_pow_lt_pow_left₀ 2 hk0 this
    have hterm : (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2 ≤
        FSNormal.cE sys L ^ 2 * ‖(FSSpectral.wt (sb eta N) (Asym sys L N) 1
          (regTail L c (gF L * N / 2) v)).ofLp q‖ ^ 2 := by
      rw [wt_regTail, regTail_apply, if_pos hk, wt_one_apply, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by have := Asym_nonneg sys L N q; linarith), mul_pow]
      have h0 : 0 ≤ 1 + FSLattice.lsq (cidx N q (lead j)) := by
        have := FSLattice.lsq_nonneg (cidx N q (lead j)); linarith
      have h4 := pow_le_pow_left₀ h0 (lead_weight_le sys hL j q) 2
      rw [mul_pow] at h4
      nlinarith [sq_nonneg ‖v.ofLp q‖]
    refine hterm.trans ?_
    exact Finset.single_le_sum (f := fun c => FSNormal.cE sys L ^ 2 * ‖(FSSpectral.wt (sb eta N) (Asym sys L N) 1
      (regTail L c (gF L * N / 2) v)).ofLp q‖ ^ 2) (fun c _ => by positivity) (Finset.mem_univ c)

/-- **The box commutator on good states**: `|e_bd(v)| ≤ C_bd M² (1/N + 1/(gN))`. -/
theorem norm_ebd_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (p₀ : Fin eta) (hN : 2 ≤ N) (hgN : 2 ≤ gF L * N) {M : ℝ} {v : En eta N}
    (hv : IsGood sys L 1 M v) :
    ‖ebd sys L p₀ v‖ ≤ Cbd sys L * M ^ 2 * (1 / N + 1 / (gF L * N)) := by
  classical
  have hg := gF_pos hL
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hM : 0 ≤ M := by
    have h := hv.1
    have := norm_nonneg v
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 v)
    linarith
  have hZ : 0 ≤ FSChannel.Zs 2 := (FSChannel.Zs_pos (by norm_num)).le
  have hcE := FSNormal.one_le_cE (sys := sys) (L := L)
  set l := gF L * N / 2
  have hl1 : 1 ≤ l := by simp only [l]; linarith
  have hl0 : 0 < l := by linarith
  -- the tails
  have hW : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 v‖ ≤ M := by
    have := hv.1; have := norm_nonneg v; linarith
  have hT : ∀ c, ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (regTail L c l v)‖ ^ 2 ≤ M ^ 2 * (2 / (gF L * N)) := by
    intro c
    have h := (hv.2 c l hl1).2
    rw [one_mul] at h
    have h' : M * l ^ (-(1 / 2 : ℝ)) ≥ 0 := by positivity
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    have e1 : (l ^ (-(1 / 2 : ℝ))) ^ 2 = l⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
      norm_num
      exact Real.rpow_neg_one l
    have e2 : l⁻¹ = 2 / (gF L * N) := by
      simp only [l]
      field_simp
    have e : (M * l ^ (-(1 / 2 : ℝ))) ^ 2 = M ^ 2 * (2 / (gF L * N)) := by
      rw [mul_pow, e1, e2]
    linarith
  have hsum := sum_out_le sys hL hN v
  have hE := norm_ebd_le (sys := sys) (p₀ := p₀) hL H hKernel v
  -- bound each channel term
  have hj : ∀ j : Ch eta, chC sys L j ^ 2 * FSChannel.Zs 2 *
      ((500 / N) * ∑ q, (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2 +
        4 * FSChannel.Zs 2 * ∑ q, (if InP ((N : ℝ) / 2) (cidx N q) then 0 else
          (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2)) ≤
      chC sys L j ^ 2 * FSChannel.Zs 2 * FSNormal.cE sys L ^ 2 * M ^ 2 *
        (500 / N + 8 * eta * FSChannel.Zs 2 / (gF L * N)) := by
    intro j
    have h1 := sum_lead_weight_le sys hL j v
    have h2 := sum_out_weight_le sys hL j v
    have h3 : ∑ c : Fin eta, ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (regTail L c l v)‖ ^ 2 ≤
        eta * (M ^ 2 * (2 / (gF L * N))) := by
      calc _ ≤ ∑ _c : Fin eta, M ^ 2 * (2 / (gF L * N)) := Finset.sum_le_sum fun c _ => hT c
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hW2 : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 v‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hW 2
    have hc2 : 0 ≤ chC sys L j ^ 2 := sq_nonneg _
    have hA : (500 / N) * ∑ q, (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2 ≤
        (500 / N) * (FSNormal.cE sys L ^ 2 * M ^ 2) :=
      mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)))
        (by positivity)
    have hB : 4 * FSChannel.Zs 2 * ∑ q, (if InP ((N : ℝ) / 2) (cidx N q) then 0 else
          (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2) ≤
        4 * FSChannel.Zs 2 * (FSNormal.cE sys L ^ 2 * (eta * (M ^ 2 * (2 / (gF L * N))))) :=
      mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))) (by positivity)
    have e : chC sys L j ^ 2 * FSChannel.Zs 2 * FSNormal.cE sys L ^ 2 * M ^ 2 *
        (500 / N + 8 * eta * FSChannel.Zs 2 / (gF L * N)) =
        chC sys L j ^ 2 * FSChannel.Zs 2 * ((500 / N) * (FSNormal.cE sys L ^ 2 * M ^ 2) +
          4 * FSChannel.Zs 2 * (FSNormal.cE sys L ^ 2 * (eta * (M ^ 2 * (2 / (gF L * N)))))) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
  have hsum2 : ∑ j : Ch eta, chC sys L j ^ 2 * FSChannel.Zs 2 *
      ((500 / N) * ∑ q, (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2 +
        4 * FSChannel.Zs 2 * ∑ q, (if InP ((N : ℝ) / 2) (cidx N q) then 0 else
          (1 + FSLattice.lsq (cidx N q (lead j))) ^ 2 * ‖v.ofLp q‖ ^ 2)) ≤
      (∑ j : Ch eta, chC sys L j ^ 2) * FSChannel.Zs 2 * FSNormal.cE sys L ^ 2 * M ^ 2 *
        (500 / N + 8 * eta * FSChannel.Zs 2 / (gF L * N)) := by
    refine (Finset.sum_le_sum fun j _ => hj j).trans (le_of_eq ?_)
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  have hfin : 500 / (N : ℝ) + 8 * eta * FSChannel.Zs 2 / (gF L * N) ≤
      (500 + 8 * eta * FSChannel.Zs 2) * (1 / N + 1 / (gF L * N)) := by
    have hgN0 : 0 < gF L * N := by positivity
    have e1 : (500 + 8 * eta * FSChannel.Zs 2) * (1 / N + 1 / (gF L * N)) =
        500 / N + 8 * eta * FSChannel.Zs 2 / (gF L * N) +
          (500 / (gF L * N) + 8 * eta * FSChannel.Zs 2 / N) := by ring
    rw [e1]
    have : 0 ≤ 500 / (gF L * N) + 8 * eta * FSChannel.Zs 2 / N := by positivity
    linarith
  have hcard : (0 : ℝ) ≤ Fintype.card (Ch eta) := by positivity
  have hcsum : 0 ≤ ∑ j : Ch eta, chC sys L j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  calc ‖ebd sys L p₀ v‖ ≤ 2 * ∑ y ∈ fourierConfigCube eta (3 * N) \ fourierConfigCube eta N,
        (∑ q, ‖v.ofLp q‖ * Mp sys L (cidx N q - y)) ^ 2 := hE
    _ ≤ 2 * (2 * (Fintype.card (Ch eta) : ℝ) * ((∑ j : Ch eta, chC sys L j ^ 2) * FSChannel.Zs 2 *
          FSNormal.cE sys L ^ 2 * M ^ 2 * (500 / N + 8 * eta * FSChannel.Zs 2 / (gF L * N)))) := by
        gcongr
        exact hsum.trans (mul_le_mul_of_nonneg_left hsum2 (by positivity))
    _ ≤ 2 * (2 * (Fintype.card (Ch eta) : ℝ) * ((∑ j : Ch eta, chC sys L j ^ 2) * FSChannel.Zs 2 *
          FSNormal.cE sys L ^ 2 * M ^ 2 * ((500 + 8 * eta * FSChannel.Zs 2) * (1 / N + 1 / (gF L * N))))) := by
        gcongr
    _ = Cbd sys L * M ^ 2 * (1 / N + 1 / (gF L * N)) := by unfold Cbd; ring

end EbdGood

end FSFlux
