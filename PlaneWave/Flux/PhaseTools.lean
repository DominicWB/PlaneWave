import PlaneWave.Flux.Flux2Split

/-!
# Flux route, part 4: tools for `prop:phase`

* `flat_sum2_le` (eq:flatbd): `Σ_{|μ| > R} |μ|⁻² |θ - μ|⁻² ≤ 455/R` for `R ≥ 1`, uniformly in `θ`
  (finite sums; `flat_tsum2_le` for the series);
* `fibre_amgm`: the fibre Cauchy–Schwarz of `lem:paird` on a finite set, in the AM–GM form
  `Σ_{k' ~ k} f(k') g(k) ≤ (N/2) (Σ W f² + Σ W g²)` when the fibre sums of `1/W` are at most `N`;
* `moment_Q`: weighted moments on the bulk block from register tails (eq:nrm-a/eq:nrm-b and the
  weighted potential tail): `Σ_{p ∈ Q} (1 + |p|²)^{2r} |v_p|² ≤ C T² (K/4)^{4r-1}`, `r > 1/4`;
* `norm_YQ_sq_le_s`: the fibre Gram bound for `Y 1_Q` with the weight `(1 + |p|²)^{2s}`, `s > 3/4`;
* the dressed symbol `s(q, p) = (A(p) - A(q))/(E(q) - E(p))` (`yK_eq`: `Y = w s` on crossings) and
  **`sY_diff_le`** (eq:asymbd, the symbol difference without `lem:com`): for `k, k' ∈ Q` on one
  fibre and an intermediate `k'' ∉ P`, `|s(k'', k) - s(k'', k')| ≤ C_Δ |τ|/n`, `τ` the transfer
  `k → k'`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

open FSLattice FSChannel

/-! ## The flat sum eq:flatbd -/

/-- **eq:flatbd**: `Σ_{μ ∈ S, |μ| > R} |μ|⁻² |θ - μ|⁻² ≤ 455/R` for `R ≥ 1`, uniformly in `θ`
(the term `μ = θ` vanishes, `1/0 = 0`). -/
theorem flat_sum2_le (S : Finset Lattice3) (θ : Lattice3) {R : ℝ} (hR : 1 ≤ R) :
    ∑ μ ∈ S.filter (fun μ => R ^ 2 < lsq μ), 1 / lsq μ * (1 / lsq (θ - μ)) ≤ 455 / R := by
  classical
  have hR0 : 0 < R := by linarith
  set S' := S.filter (fun μ => R ^ 2 < lsq μ)
  set f := fun μ : Lattice3 => 1 / lsq μ * (1 / lsq (θ - μ))
  rw [← Finset.sum_filter_add_sum_filter_not S' (fun μ => lsq μ ≤ 4 * lsq (θ - μ))]
  -- far terms
  have hfar : ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), f μ ≤ 4 * (104 / R) := by
    have hterm : ∀ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), f μ ≤ 4 * tailFn R μ := by
      intro μ hμ
      obtain ⟨hμ1, hμ2⟩ := Finset.mem_filter.mp hμ
      have hR2 := (Finset.mem_filter.mp hμ1).2
      have hl : 0 < lsq μ := lt_of_le_of_lt (sq_nonneg R) hR2
      have hd : 0 < lsq (θ - μ) := by linarith
      have h1 : 1 / lsq (θ - μ) ≤ 4 / lsq μ := by
        rw [div_le_div_iff₀ hd hl]; linarith
      have ht : tailFn R μ = (lsq μ)⁻¹ ^ 2 := by
        unfold tailFn; rw [if_pos (by exact hR2)]; rfl
      calc f μ = 1 / lsq μ * (1 / lsq (θ - μ)) := rfl
        _ ≤ 1 / lsq μ * (4 / lsq μ) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 4 * tailFn R μ := by rw [ht]; field_simp
    calc ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), f μ
        ≤ ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), 4 * tailFn R μ :=
          Finset.sum_le_sum hterm
      _ = 4 * ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), tailFn R μ := by
          rw [Finset.mul_sum]
      _ ≤ 4 * ∑' μ, tailFn R μ := by
          gcongr
          exact (tailFn_summable_and_le hR).1.sum_le_tsum _ fun μ _ => tailFn_nonneg R μ
      _ ≤ 4 * (104 / R) := by gcongr; exact (tailFn_summable_and_le hR).2
  -- near terms
  set Nr := S'.filter (fun μ => ¬ lsq μ ≤ 4 * lsq (θ - μ))
  set M := max (R ^ 2) (4 / 9 * lsq θ)
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hnear_geom : ∀ μ ∈ Nr, M ≤ lsq μ ∧ lsq (θ - μ) ≤ lsq θ := by
    intro μ hμ
    obtain ⟨hμ1, hμ2⟩ := Finset.mem_filter.mp hμ
    have hR2 := (Finset.mem_filter.mp hμ1).2
    push Not at hμ2
    have h4 : 4 * lsq (μ - θ) < lsq μ := by rw [lsq_sub_comm]; exact hμ2
    obtain ⟨g1, g2⟩ := near_geom h4
    refine ⟨max_le hR2.le (by linarith), ?_⟩
    linarith [lsq_nonneg (θ - μ)]
  set s := Real.sqrt (lsq θ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = lsq θ := Real.sq_sqrt (lsq_nonneg θ)
  have hball : ∑ μ ∈ Nr, 1 / lsq (θ - μ) ≤ 26 * s := by
    rw [← Finset.sum_filter_add_sum_filter_not Nr (fun μ => θ - μ = 0)]
    have hz : ∑ μ ∈ Nr.filter (fun μ => θ - μ = 0), 1 / lsq (θ - μ) = 0 := by
      refine Finset.sum_eq_zero fun μ hμ => ?_
      rw [(Finset.mem_filter.mp hμ).2, lsq_zero, div_zero]
    rw [hz, zero_add]
    apply sum_inv_lsq_image_le _ (fun μ => θ - μ) _ hs0
    · intro μ hμ; exact (Finset.mem_filter.mp hμ).2
    · intro μ hμ
      rw [hs2]
      exact (hnear_geom μ (Finset.mem_filter.mp hμ).1).2
    · intro μ _ μ' _ h
      have h' : θ - μ = θ - μ' := h
      exact sub_right_injective h'
  have hnear : ∑ μ ∈ Nr, f μ ≤ 39 / R := by
    have h1 : ∑ μ ∈ Nr, f μ ≤ ∑ μ ∈ Nr, 1 / M * (1 / lsq (θ - μ)) := by
      apply Finset.sum_le_sum
      intro μ hμ
      have hM := (hnear_geom μ hμ).1
      have hd : 0 ≤ 1 / lsq (θ - μ) := by have := lsq_nonneg (θ - μ); positivity
      exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hM0 hM) hd
    rw [← Finset.mul_sum] at h1
    have h2 : 1 / M * ∑ μ ∈ Nr, 1 / lsq (θ - μ) ≤ 1 / M * (26 * s) :=
      mul_le_mul_of_nonneg_left hball (by positivity)
    have hkey : s * R ≤ 3 / 2 * M := by
      have hθM : lsq θ ≤ 9 / 4 * M := by
        have := le_max_right (R ^ 2) (4 / 9 * lsq θ); linarith
      have hRM : R ^ 2 ≤ M := le_max_left _ _
      have hsq : (s * R) ^ 2 ≤ (3 / 2 * M) ^ 2 := by
        have e1 : (s * R) ^ 2 = s ^ 2 * R ^ 2 := by ring
        have e2 : (3 / 2 * M) ^ 2 = 9 / 4 * M * M := by ring
        rw [e1, e2, hs2]
        exact mul_le_mul hθM hRM (by positivity) (by positivity)
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    have h3 : 1 / M * (26 * s) ≤ 39 / R := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hM0 hR0]
      nlinarith
    linarith
  calc ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), 1 / lsq μ * (1 / lsq (θ - μ)) +
        ∑ μ ∈ S'.filter (fun μ => ¬ lsq μ ≤ 4 * lsq (θ - μ)), 1 / lsq μ * (1 / lsq (θ - μ))
      = ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), f μ + ∑ μ ∈ Nr, f μ := rfl
    _ ≤ 4 * (104 / R) + 39 / R := add_le_add hfar hnear
    _ = 455 / R := by ring

/-- The flat series: `Σ_{|μ| > R} |μ|⁻² |θ - μ|⁻² ≤ 455/R`. -/
theorem flat_tsum2_le (θ : Lattice3) {R : ℝ} (hR : 1 ≤ R) :
    Summable (fun μ : Lattice3 => if R ^ 2 < lsq μ then 1 / lsq μ * (1 / lsq (θ - μ)) else 0) ∧
      ∑' μ : Lattice3, (if R ^ 2 < lsq μ then 1 / lsq μ * (1 / lsq (θ - μ)) else 0) ≤ 455 / R := by
  classical
  have hnn : ∀ μ : Lattice3, 0 ≤ (if R ^ 2 < lsq μ then 1 / lsq μ * (1 / lsq (θ - μ)) else 0) := by
    intro μ; split_ifs
    · have := lsq_nonneg μ; have := lsq_nonneg (θ - μ); positivity
    · exact le_rfl
  have hfin : ∀ S : Finset Lattice3,
      ∑ μ ∈ S, (if R ^ 2 < lsq μ then 1 / lsq μ * (1 / lsq (θ - μ)) else 0) ≤ 455 / R := by
    intro S
    rw [← Finset.sum_filter]
    exact flat_sum2_le S θ hR
  have hs := summable_of_sum_le hnn hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

/-! ## The fibre AM–GM bound -/

/-- **The fibre Cauchy–Schwarz of `lem:paird`** on a finite set, AM–GM form: if the fibre sums of
`1/W` are at most `N` in both directions, then
`Σ_{k' ~ k} f(k') g(k) ≤ (N/2) (Σ W f² + Σ W g²)`. -/
lemma fibre_amgm {ι : Type*} (F : Finset ι) (R : ι → ι → Prop) [DecidableRel R] (W : ι → ℝ)
    (hW : ∀ p, 0 < W p) {N : ℝ}
    (hN1 : ∀ k' ∈ F, ∑ k ∈ F.filter (fun k => R k' k), (W k)⁻¹ ≤ N)
    (hN2 : ∀ k ∈ F, ∑ k' ∈ F.filter (fun k' => R k' k), (W k')⁻¹ ≤ N)
    (f g : ι → ℝ) :
    ∑ k' ∈ F, ∑ k ∈ F, (if R k' k then f k' * g k else 0) ≤
      N / 2 * (∑ p ∈ F, W p * f p ^ 2 + ∑ p ∈ F, W p * g p ^ 2) := by
  have hpt : ∀ k' k, (if R k' k then f k' * g k else 0) ≤
      1 / 2 * (if R k' k then W k' * f k' ^ 2 * (W k)⁻¹ else 0) +
        1 / 2 * (if R k' k then W k * g k ^ 2 * (W k')⁻¹ else 0) := by
    intro k' k
    split_ifs
    · have h1 := hW k'
      have h2 := hW k
      have key : 2 * (f k' * g k) ≤ W k' * f k' ^ 2 * (W k)⁻¹ + W k * g k ^ 2 * (W k')⁻¹ := by
        have := FSKernel.two_mul_le_ratio (x := f k') (y := g k) (t := W k' / W k) (by positivity)
        have e1 : f k' ^ 2 * (W k' / W k) = W k' * f k' ^ 2 * (W k)⁻¹ := by ring
        have e2 : g k ^ 2 / (W k' / W k) = W k * g k ^ 2 * (W k')⁻¹ := by
          field_simp
        linarith
      linarith
    · simp
  have hA : ∑ k' ∈ F, ∑ k ∈ F, (if R k' k then W k' * f k' ^ 2 * (W k)⁻¹ else 0) ≤
      N * ∑ p ∈ F, W p * f p ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k' hk' => ?_
    have e : ∑ k ∈ F, (if R k' k then W k' * f k' ^ 2 * (W k)⁻¹ else 0) =
        W k' * f k' ^ 2 * ∑ k ∈ F.filter (fun k => R k' k), (W k)⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [e]
    have h0 : 0 ≤ W k' * f k' ^ 2 := mul_nonneg (hW k').le (sq_nonneg _)
    calc W k' * f k' ^ 2 * ∑ k ∈ F.filter (fun k => R k' k), (W k)⁻¹
        ≤ W k' * f k' ^ 2 * N := mul_le_mul_of_nonneg_left (hN1 k' hk') h0
      _ = N * (W k' * f k' ^ 2) := by ring
  have hB : ∑ k' ∈ F, ∑ k ∈ F, (if R k' k then W k * g k ^ 2 * (W k')⁻¹ else 0) ≤
      N * ∑ p ∈ F, W p * g p ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have e : ∑ k' ∈ F, (if R k' k then W k * g k ^ 2 * (W k')⁻¹ else 0) =
        W k * g k ^ 2 * ∑ k' ∈ F.filter (fun k' => R k' k), (W k')⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [e]
    have h0 : 0 ≤ W k * g k ^ 2 := mul_nonneg (hW k).le (sq_nonneg _)
    calc W k * g k ^ 2 * ∑ k' ∈ F.filter (fun k' => R k' k), (W k')⁻¹
        ≤ W k * g k ^ 2 * N := mul_le_mul_of_nonneg_left (hN2 k hk) h0
      _ = N * (W k * g k ^ 2) := by ring
  calc ∑ k' ∈ F, ∑ k ∈ F, (if R k' k then f k' * g k else 0)
      ≤ ∑ k' ∈ F, ∑ k ∈ F, (1 / 2 * (if R k' k then W k' * f k' ^ 2 * (W k)⁻¹ else 0) +
          1 / 2 * (if R k' k then W k * g k ^ 2 * (W k')⁻¹ else 0)) :=
        Finset.sum_le_sum fun k' _ => Finset.sum_le_sum fun k _ => hpt k' k
    _ = 1 / 2 * ∑ k' ∈ F, ∑ k ∈ F, (if R k' k then W k' * f k' ^ 2 * (W k)⁻¹ else 0) +
          1 / 2 * ∑ k' ∈ F, ∑ k ∈ F, (if R k' k then W k * g k ^ 2 * (W k')⁻¹ else 0) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 1 / 2 * (N * ∑ p ∈ F, W p * f p ^ 2) + 1 / 2 * (N * ∑ p ∈ F, W p * g p ^ 2) := by
        gcongr
    _ = N / 2 * (∑ p ∈ F, W p * f p ^ 2 + ∑ p ∈ F, W p * g p ^ 2) := by ring

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Moments on the bulk block -/

omit [Fintype ν] in
/-- On the bulk block every register momentum is at most `g n/4`. -/
lemma kreg_le_of_mem_Qs {L : ℝ} (hL : 0 < L) {n : ℕ} {p : Cf eta} (hp : p ∈ Qs eta n)
    (a : Fin eta) : gF L * Real.sqrt (nsq (p a)) ≤ gF L * n / 4 := by
  have h := (mem_Qs.mp hp) a
  have hs : Real.sqrt (nsq (p a)) ≤ n / 4 := Real.sqrt_le_iff.mpr ⟨by positivity, h⟩
  have := gF_pos hL
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hs this.le

omit [Fintype ν] in
/-- **Moments on the bulk block** from register tails: if `‖v‖ ≤ T` and
`‖1_{a, > l} v‖² ≤ T²/l` for every register and every `l ≥ 1`, then for `r > 1/4`
`Σ_{p ∈ Q} (1 + |p|²)^{2r} |v_p|² ≤ C_r T² (g n/4)^{4r-1}` when `g n/4 ≥ 1`. -/
theorem moment_Q {L : ℝ} (hL : 0 < L) {n : ℕ} (hΛ : 1 ≤ gF L * n / 4) (v : L2 eta) {T r : ℝ}
    (hr : 1 / 4 < r) (hT : 0 ≤ T) (hv : ‖v‖ ≤ T)
    (htail : ∀ (a : Fin eta) (l : ℝ), 1 ≤ l → ‖tailMask (gF L) l a v‖ ^ 2 ≤ T ^ 2 / l) :
    ∑ p ∈ Qs eta n, (1 + lsqC p) ^ (2 * r) * ‖v p‖ ^ 2 ≤
      FSDatum.momentConst1 eta r ((eta : ℝ) / gF L ^ 2) * T ^ 2 * (gF L * n / 4) ^ (4 * r - 1) := by
  classical
  have hg := gF_pos hL
  set X := { p // p ∈ Qs eta n }
  have key := FSDatum.moment_le_of_tails1 (X := X) (η := eta) (fun x => lsqC x.1)
    (fun a x => gF L * Real.sqrt (nsq (x.1 a))) (fun x => v x.1) (cA := (eta : ℝ) / gF L ^ 2)
    (E₀ := lsqC (0 : Cf eta) + ∑ p ∈ Qs eta n, lsqC p) (Λ := gF L * n / 4) (T := T) (r := r)
    (by positivity) (fun x => lsqC_nonneg x.1) hΛ hr hT ?_ ?_ ?_ ?_
  · -- the sum over `Q`
    have e : ∑ x : X, (if lsqC x.1 ≤ lsqC (0 : Cf eta) + ∑ p ∈ Qs eta n, lsqC p then
        (1 + lsqC x.1) ^ (2 * r) * ‖v x.1‖ ^ 2 else 0) =
        ∑ p ∈ Qs eta n, (1 + lsqC p) ^ (2 * r) * ‖v p‖ ^ 2 := by
      rw [← Finset.sum_coe_sort (Qs eta n) (fun p => (1 + lsqC p) ^ (2 * r) * ‖v p‖ ^ 2)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [if_pos]
      have h1 : lsqC x.1 ≤ ∑ p ∈ Qs eta n, lsqC p :=
        Finset.single_le_sum (f := lsqC) (fun p _ => lsqC_nonneg p) x.2
      have h2 := lsqC_nonneg (0 : Cf eta)
      linarith
    rw [e] at key
    exact key
  · -- `lsqC ≤ (η/g²) R²` when every register momentum is at most `R`
    intro x R hR hx
    unfold lsqC
    have hR' : ∀ a, nsq (x.1 a) ≤ R ^ 2 / gF L ^ 2 := by
      intro a
      have h1 := hx a
      have h2 : Real.sqrt (nsq (x.1 a)) ≤ R / gF L := by rw [le_div_iff₀ hg]; linarith
      have h3 := Real.sqrt_le_sqrt (le_refl (nsq (x.1 a)))
      calc nsq (x.1 a) = Real.sqrt (nsq (x.1 a)) ^ 2 := (Real.sq_sqrt (nsq_nonneg _)).symm
        _ ≤ (R / gF L) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
        _ = R ^ 2 / gF L ^ 2 := by rw [div_pow]
    calc ∑ c, nsq (x.1 c) ≤ ∑ _c : Fin eta, R ^ 2 / gF L ^ 2 := Finset.sum_le_sum fun c _ => hR' c
      _ = (eta : ℝ) / gF L ^ 2 * R ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · intro x _ a
    exact kreg_le_of_mem_Qs hL x.2 a
  · -- `Σ_Q |v|² ≤ T²`
    rw [Finset.sum_coe_sort (Qs eta n) (fun p => ‖v p‖ ^ 2)]
    calc ∑ p ∈ Qs eta n, ‖v p‖ ^ 2 ≤ ‖v‖ ^ 2 := sum_Qs_sq_le n v
      _ ≤ T ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
  · intro a l hl
    rw [Finset.sum_coe_sort (Qs eta n)
      (fun p => if l < gF L * Real.sqrt (nsq (p a)) then ‖v p‖ ^ 2 else 0)]
    refine le_trans ?_ (htail a l hl)
    have e : ∀ p, (if l < gF L * Real.sqrt (nsq (p a)) then ‖v p‖ ^ 2 else 0) =
        ‖tailMask (gF L) l a v p‖ ^ 2 := by
      intro p
      rw [tailMask_apply]
      split_ifs with h1 h2 h2
      · rw [one_mul]
      · exact absurd h1 h2
      · exact absurd h2 h1
      · rw [zero_mul, norm_zero]; ring
    simp_rw [e]
    calc ∑ p ∈ Qs eta n, ‖tailMask (gF L) l a v p‖ ^ 2 ≤ ‖tailMask (gF L) l a v‖ ^ 2 :=
          sum_Qs_sq_le n _
      _ = _ := rfl

/-! ## The Gram bound with fractional weights -/

section GramS

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ} (p₀ : Fin eta)

open Classical in
/-- **The fibre Gram bound for `Y 1_Q` with the weight `(1 + |p|²)^{2s}`**, `s > 3/4`:
`‖Y 1_Q x‖² ≤ #Ch² M_Y Z_{2s} Σ_{p ∈ Q} (1 + |p|²)^{2s} |x_p|²`. -/
theorem norm_YQ_sq_le_s (hL : 0 < L) (hn : 2 ≤ n) {s : ℝ} (hs : 3 / 4 < s) (x : L2 eta) :
    ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)‖ ^ 2 ≤
      Fintype.card (Ch eta) ^ 2 * MY sys L n p₀ * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3))) *
        ∑ p ∈ Qs eta n, Ws s p * ‖x p‖ ^ 2 := by
  classical
  set F := Qs eta n
  set G : Ch eta → Cf eta → ℝ := fun j q => ∑ p ∈ F, ‖x p‖ * kapY (sys := sys) (L := L) (n := n) p₀ j q p
  set N : ℝ := 1 + 26 * (1 + 1 / (2 * (2 * s) - 3))
  have hj : ∀ j : Ch eta, (Summable fun q => (1 : ℝ) * G j q ^ 2) ∧
      ∑' q, (1 : ℝ) * G j q ^ 2 ≤ MY sys L n p₀ * N * ∑ p ∈ F, Ws s p * ‖x p‖ ^ 2 := by
    intro j
    refine fibre_gram F (kapY (sys := sys) (L := L) (n := n) p₀ j)
      (fun q p => kapY_nonneg p₀ j q p) (fun _ => 1) (fun _ => zero_le_one)
      (fun p p' => OnCh j p' p) (fun p p' h => onCh_symm h) ?_ (fun p _ => ?_) (fun p _ => ?_)
      (Ws s) (Ws_pos s) (fun p _ => fibre_weight_le n j p hs) (fun p => ‖x p‖)
      (fun p => norm_nonneg _)
    · intro q p _ p' _ h1 h2
      have o1 : OnCh j q p := by by_contra h; exact h1 (by unfold kapY; rw [if_neg h])
      have o2 : OnCh j q p' := by by_contra h; exact h2 (by unfold kapY; rw [if_neg h])
      exact onCh_trans o1 o2
    · simpa only [one_mul] using (col_kapY p₀ hL hn j p).1
    · simpa only [one_mul] using col_kapY_le_MY p₀ hL hn j p
  have hpt : ∀ q, ‖Yop sys hL hn p₀ (lpTruncate F x) q‖ ^ 2 ≤
      Fintype.card (Ch eta) * ∑ j : Ch eta, (1 : ℝ) * G j q ^ 2 := by
    intro q
    rw [Yop_truncQ_apply p₀ hL hn x q]
    have h1 : ‖∑ p ∈ F, yK sys L n p₀ q p * x p‖ ≤ ∑ j : Ch eta, G j q := by
      refine (norm_sum_le _ _).trans ?_
      simp only [G]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [norm_mul, ← Finset.mul_sum, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_yK_le_kapY p₀ hL q p) (norm_nonneg _)
    have h2 : (∑ j : Ch eta, G j q) ^ 2 ≤ Fintype.card (Ch eta) * ∑ j : Ch eta, G j q ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h0 : 0 ≤ ∑ j : Ch eta, G j q :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun p _ =>
        mul_nonneg (norm_nonneg _) (kapY_nonneg p₀ j q p)
    simp only [one_mul]
    calc ‖∑ p ∈ F, yK sys L n p₀ q p * x p‖ ^ 2 ≤ (∑ j : Ch eta, G j q) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hs' : Summable fun q => (Fintype.card (Ch eta) : ℝ) * ∑ j : Ch eta, (1 : ℝ) * G j q ^ 2 :=
    (summable_sum fun j _ => (hj j).1).mul_left _
  rw [← tsum_sq_coord]
  calc ∑' q, ‖Yop sys hL hn p₀ (lpTruncate F x) q‖ ^ 2
      ≤ ∑' q, (Fintype.card (Ch eta) : ℝ) * ∑ j : Ch eta, (1 : ℝ) * G j q ^ 2 :=
        (summable_sq_coord _).tsum_le_tsum hpt hs'
    _ = Fintype.card (Ch eta) * ∑ j : Ch eta, ∑' q, (1 : ℝ) * G j q ^ 2 := by
        rw [tsum_mul_left, Summable.tsum_finsetSum fun j _ => (hj j).1]
    _ ≤ Fintype.card (Ch eta) * ∑ _j : Ch eta, MY sys L n p₀ * N * ∑ p ∈ F, Ws s p * ‖x p‖ ^ 2 := by
        gcongr with j
        exact (hj j).2
    _ = Fintype.card (Ch eta) ^ 2 * MY sys L n p₀ * N * ∑ p ∈ F, Ws s p * ‖x p‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end GramS

/-! ## The dressed symbol and its difference -/

section Symbol

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta)

/-- **The dressed symbol** `s(q, p) = (A(p) - A(q))/(E(q) - E(p))`. -/
noncomputable def sY (q p : Cf eta) : ℝ :=
  (regSymbol sys (gF L) p₀ p - regSymbol sys (gF L) p₀ q) / (Ek sys L q - Ek sys L p)

variable {sys L}

open Classical in
/-- `Y = w s` on the crossings. -/
lemma yK_eq (n : ℕ) (q p : Cf eta) :
    yK sys L n p₀ q p = if Cross (n : ℝ) q p then potKernel sys L q p * (sY sys L p₀ q p : ℂ)
      else 0 := by
  unfold yK sigK sY
  split_ifs
  · push_cast; ring
  · rw [zero_mul]

omit [Fintype ν] in
/-- `|nsq(b + d) - nsq b| ≤ n |d|` when `|b|, |b + d| ≤ n/4`. -/
lemma nsq_diff_le {n : ℝ} (hn : 0 ≤ n) {b d : Lattice3} (hb : nsq b ≤ (n / 4) ^ 2)
    (hbd : nsq (b + d) ≤ (n / 4) ^ 2) :
    |nsq (b + d) - nsq b| ≤ n * Real.sqrt (nsq d) := by
  set D := Real.sqrt (nsq d)
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hD2 : D ^ 2 = nsq d := Real.sq_sqrt (nsq_nonneg d)
  have hb' : Real.sqrt (nsq b) ≤ n / 4 := Real.sqrt_le_iff.mpr ⟨by positivity, hb⟩
  have hbd' : Real.sqrt (nsq (b + d)) ≤ n / 4 := Real.sqrt_le_iff.mpr ⟨by positivity, hbd⟩
  -- `|d| ≤ |b + d| + |b|`
  have hD : D ≤ n / 2 := by
    have h := rho_add_le (b + d) (-b)
    have e : b + d + -b = d := by abel
    rw [e, rho_neg'] at h
    change D ≤ _
    have : D ≤ Real.sqrt (nsq (b + d)) + Real.sqrt (nsq b) := h
    linarith
  have hl := abs_ldot_le b d
  have hexp : nsq (b + d) - nsq b = 2 * ldot b d + nsq d := by rw [nsq_add]; ring
  rw [hexp, abs_le]
  have h1 : |ldot b d| ≤ n / 4 * D := hl.trans (mul_le_mul_of_nonneg_right hb' hD0)
  rw [abs_le] at h1
  have h2 : nsq d ≤ n / 2 * D := by rw [← hD2]; nlinarith
  have h3 : 0 ≤ nsq d := nsq_nonneg d
  constructor <;> nlinarith

omit [Fintype ν] in
/-- On a fibre of `Q`: `|A(k') - A(k)| ≤ (g²/(2m_{p₀})) n |τ|`. -/
lemma regSymbol_diff_le {n : ℕ} {j : Ch eta} {k k' : Cf eta} (hk : InQ (n : ℝ) k)
    (hk' : InQ (n : ℝ) k') (hj : OnCh j k' k) :
    |regSymbol sys (gF L) p₀ k' - regSymbol sys (gF L) p₀ k| ≤
      gF L ^ 2 / (2 * sys.mass p₀) * n * Real.sqrt (nsq (k' (lead j) - k (lead j))) := by
  set τ := k' (lead j) - k (lead j)
  have hq : k' = k + tr j τ := hj
  set d := tr j τ p₀
  have hkd : k' p₀ = k p₀ + d := congrFun hq p₀
  have hd : Real.sqrt (nsq d) ≤ Real.sqrt (nsq τ) := by
    apply Real.sqrt_le_sqrt
    by_cases hm : p₀ ∈ moved j
    · rcases tr_apply_moved j τ hm with h | h
      · rw [show d = τ from h]
      · rw [show d = -τ from h, nsq_neg]
    · rw [show d = 0 from tr_apply_not_moved j τ hm]
      have : nsq (0 : Lattice3) = 0 := by simp [nsq]
      rw [this]; exact nsq_nonneg τ
  have h := nsq_diff_le (n := (n : ℝ)) (Nat.cast_nonneg n) (hk p₀) (by rw [← hkd]; exact hk' p₀)
  have hm := sys.mass_pos p₀
  have e : regSymbol sys (gF L) p₀ k' - regSymbol sys (gF L) p₀ k =
      gF L ^ 2 / (2 * sys.mass p₀) * (nsq (k p₀ + d) - nsq (k p₀)) := by
    unfold regSymbol
    rw [hkd, ← nsq_eq_latticeNormSq]
    field_simp
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  calc gF L ^ 2 / (2 * sys.mass p₀) * |nsq (k p₀ + d) - nsq (k p₀)|
      ≤ gF L ^ 2 / (2 * sys.mass p₀) * (n * Real.sqrt (nsq d)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ gF L ^ 2 / (2 * sys.mass p₀) * (n * Real.sqrt (nsq τ)) := by gcongr
    _ = _ := by ring

variable (sys L) in
/-- `c_E = Σ_c g²/(2 m_c)`. -/
noncomputable def cE : ℝ := ∑ c : Fin eta, gF L ^ 2 / (2 * sys.mass c)

omit [Fintype ν] in
/-- On a fibre of `Q`: `|E(k') - E(k)| ≤ c_E n |τ|`. -/
lemma Ek_diff_le {n : ℕ} {j : Ch eta} {k k' : Cf eta} (hk : InQ (n : ℝ) k)
    (hk' : InQ (n : ℝ) k') (hj : OnCh j k' k) :
    |Ek sys L k' - Ek sys L k| ≤ cE sys L * n * Real.sqrt (nsq (k' (lead j) - k (lead j))) := by
  set τ := k' (lead j) - k (lead j)
  have hq : k' = k + tr j τ := hj
  rw [Ek, Ek, E, E, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold cE
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun c _ => ?_
  set d := tr j τ c
  have hkd : k' c = k c + d := congrFun hq c
  have hd : Real.sqrt (nsq d) ≤ Real.sqrt (nsq τ) := by
    apply Real.sqrt_le_sqrt
    by_cases hm : c ∈ moved j
    · rcases tr_apply_moved j τ hm with h | h
      · rw [show d = τ from h]
      · rw [show d = -τ from h, nsq_neg]
    · rw [show d = 0 from tr_apply_not_moved j τ hm]
      have : nsq (0 : Lattice3) = 0 := by simp [nsq]
      rw [this]; exact nsq_nonneg τ
  have h := nsq_diff_le (n := (n : ℝ)) (Nat.cast_nonneg n) (hk c) (by rw [← hkd]; exact hk' c)
  have hm := sys.mass_pos c
  rw [← mul_sub, hkd, abs_mul, abs_of_nonneg (by positivity)]
  calc gF L ^ 2 / (2 * sys.mass c) * |nsq (k c + d) - nsq (k c)|
      ≤ gF L ^ 2 / (2 * sys.mass c) * (n * Real.sqrt (nsq d)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ gF L ^ 2 / (2 * sys.mass c) * (n * Real.sqrt (nsq τ)) := by gcongr
    _ = _ := by ring

variable (sys L) in
/-- The symbol-difference constant
`C_Δ = ((5/6)(g²/m_{p₀})/c_gap · c_E + g²/(2 m_{p₀})) · 16/(9 c_gap)`. -/
noncomputable def cDel : ℝ :=
  (5 / 6 * (gF L ^ 2 / sys.mass p₀) / cgap sys (gF L) * cE sys L + gF L ^ 2 / (2 * sys.mass p₀)) *
    (16 / (9 * cgap sys (gF L)))

omit [Fintype ν] in
/-- **The symbol difference** (eq:asymbd without the exact identity of `lem:com`): for `k, k' ∈ Q`
and `k'' ∉ P` with `k''` one hop of channel `j` from both,
`|s(k'', k) - s(k'', k')| ≤ C_Δ |τ|/n`, `τ = k'_j - k_j`. -/
theorem sY_diff_le (hL : 0 < L) {n : ℕ} (hn0 : 0 < n) {j : Ch eta} {k k' k'' : Cf eta}
    (hk : InQ (n : ℝ) k) (hk' : InQ (n : ℝ) k') (hr : ¬ InP (n : ℝ) k'')
    (h1 : OnCh j k'' k) (h2 : OnCh j k'' k') :
    |sY sys L p₀ k'' k - sY sys L p₀ k'' k'| ≤
      cDel sys L p₀ * Real.sqrt (nsq (k' (lead j) - k (lead j))) / n := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hc1 : Cross (n : ℝ) k'' k := Or.inr ⟨hr, hk⟩
  have hc2 : Cross (n : ℝ) k'' k' := Or.inr ⟨hr, hk'⟩
  obtain ⟨g1, g2⟩ := channel_gap sys (gF_pos hL).ne' hnr h1 hc1
  obtain ⟨g1', g2'⟩ := channel_gap sys (gF_pos hL).ne' hnr h2 hc2
  have hkk : OnCh j k' k := onCh_trans h1 h2
  have hFA := force_symbol_le sys p₀ (gF L) h1 hc1 g1
  have hdA := regSymbol_diff_le (sys := sys) (L := L) p₀ hk hk' hkk
  have hdE := Ek_diff_le (sys := sys) (L := L) hk hk' hkk
  set N := nsq (k'' (lead j) - k (lead j))
  set N' := nsq (k'' (lead j) - k' (lead j))
  set τ := Real.sqrt (nsq (k' (lead j) - k (lead j)))
  have hτ0 : 0 ≤ τ := Real.sqrt_nonneg _
  set A0 := regSymbol sys (gF L) p₀ k
  set A1 := regSymbol sys (gF L) p₀ k'
  set A2 := regSymbol sys (gF L) p₀ k''
  set E0 := Ek sys L k
  set E1 := Ek sys L k'
  set E2 := Ek sys L k''
  have hcg := cgap_pos sys (gF_pos hL).ne'
  have hm := sys.mass_pos p₀
  have hg2 : 0 < gF L ^ 2 := by have := gF_pos hL; positivity
  have hN0 : 0 < N := lt_of_le_of_lt (sq_nonneg _) g1
  have hN'0 : (3 * n / 4) ^ 2 < N' := g1'
  have hD : 0 < |E2 - E0| := lt_of_lt_of_le (by positivity) g2
  have hD' : cgap sys (gF L) * (3 * n / 4) ^ 2 < |E2 - E1| :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left hN'0 hcg) g2'
  have hD'0 : 0 < |E2 - E1| := lt_trans (by positivity) hD'
  have hne : E2 - E0 ≠ 0 := abs_pos.mp hD
  have hne' : E2 - E1 ≠ 0 := abs_pos.mp hD'0
  -- the algebraic identity
  have hid : sY sys L p₀ k'' k - sY sys L p₀ k'' k' =
      ((A2 - A0) * (E1 - E0) - (A1 - A0) * (E2 - E0)) / ((E2 - E0) * (E2 - E1)) := by
    have e1 : sY sys L p₀ k'' k = (A0 - A2) / (E2 - E0) := rfl
    have e2 : sY sys L p₀ k'' k' = (A1 - A2) / (E2 - E1) := rfl
    rw [e1, e2]
    field_simp
    ring
  rw [hid, abs_div, abs_mul]
  have hnum : |(A2 - A0) * (E1 - E0) - (A1 - A0) * (E2 - E0)| ≤
      |A2 - A0| * |E1 - E0| + |A1 - A0| * |E2 - E0| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
  have hratio : |A2 - A0| ≤ 5 / 6 * (gF L ^ 2 / sys.mass p₀) / cgap sys (gF L) * |E2 - E0| := by
    have h := hFA
    rw [abs_sub_comm] at h
    calc |A2 - A0| ≤ 5 / 6 * (gF L ^ 2 / sys.mass p₀) * N := h
      _ = 5 / 6 * (gF L ^ 2 / sys.mass p₀) / cgap sys (gF L) * (cgap sys (gF L) * N) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left g2 (by positivity)
  have hdA' : |A1 - A0| ≤ gF L ^ 2 / (2 * sys.mass p₀) * n * τ := hdA
  have hdE' : |E1 - E0| ≤ cE sys L * n * τ := hdE
  have hcE : 0 ≤ cE sys L := Finset.sum_nonneg fun c _ => by have := sys.mass_pos c; positivity
  have hfrac : |(A2 - A0) * (E1 - E0) - (A1 - A0) * (E2 - E0)| / (|E2 - E0| * |E2 - E1|) ≤
      (5 / 6 * (gF L ^ 2 / sys.mass p₀) / cgap sys (gF L) * (cE sys L * n * τ) +
        gF L ^ 2 / (2 * sys.mass p₀) * n * τ) / |E2 - E1| := by
    rw [div_le_div_iff₀ (by positivity) hD'0]
    have h1' : |A2 - A0| * |E1 - E0| ≤
        5 / 6 * (gF L ^ 2 / sys.mass p₀) / cgap sys (gF L) * |E2 - E0| * (cE sys L * n * τ) :=
      mul_le_mul hratio hdE' (abs_nonneg _) (by positivity)
    have h2' : |A1 - A0| * |E2 - E0| ≤ gF L ^ 2 / (2 * sys.mass p₀) * n * τ * |E2 - E0| :=
      mul_le_mul_of_nonneg_right hdA' (abs_nonneg _)
    have := mul_le_mul_of_nonneg_right (hnum.trans (add_le_add h1' h2')) hD'0.le
    nlinarith [abs_nonneg (E2 - E0), abs_nonneg (E2 - E1)]
  refine hfrac.trans ?_
  have hpos : 0 ≤ 5 / 6 * (gF L ^ 2 / sys.mass p₀) / cgap sys (gF L) * (cE sys L * n * τ) +
      gF L ^ 2 / (2 * sys.mass p₀) * n * τ := by positivity
  calc (5 / 6 * (gF L ^ 2 / sys.mass p₀) / cgap sys (gF L) * (cE sys L * n * τ) +
        gF L ^ 2 / (2 * sys.mass p₀) * n * τ) / |E2 - E1|
      ≤ (5 / 6 * (gF L ^ 2 / sys.mass p₀) / cgap sys (gF L) * (cE sys L * n * τ) +
        gF L ^ 2 / (2 * sys.mass p₀) * n * τ) / (cgap sys (gF L) * (3 * n / 4) ^ 2) :=
        div_le_div_of_nonneg_left hpos (by positivity) hD'.le
    _ = cDel sys L p₀ * τ / n := by
        unfold cDel
        field_simp
        ring

end Symbol

end FSFlux
