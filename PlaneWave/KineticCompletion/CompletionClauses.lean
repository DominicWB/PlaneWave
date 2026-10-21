import PlaneWave.KineticCompletion.Completion

/-!
# Kinetic completion, part 6: the remaining clauses of `comp:thm:completion`

* **`FSLattice.relativeD`**, **`relativeD_log`** (`comp:lem:relativeD` in its general form): for
  every finite set `X` of lattice points with `|x| ≤ M` (`M ≥ 2`), every centre `c` and every complex
  matrix with `|B(x,y)| ≤ b₀ D_c(x,y)` (eq:D), `‖B Λ⁻¹‖ ≤ b₀ C_rel (J + 2)²` whenever `M² ≤ 2^J`,
  hence `‖B Λ⁻¹‖ ≤ 49 b₀ C_rel log²(2 + M)`; by the weighted Schur test with `Λ⁻¹` on both sides,
  the core sums of `PlaneWave.KineticCompletion.InverseMismatch` for the small mismatches, and a crude count for `|F_c| ≥ 4M²`;
* `FSLattice.kato_sum_le` (the lattice Kato sum): for every finite set `T` of nonzero transfers,
  `Σ_{θ ∈ T} |θ|⁻² (1 + |y + θ|²)⁻¹ ≤ C_K (1 + |y|²)^{-1/2}`, `C_K = 1500`, uniformly in `y`;
* `schur_bilinear`, `dir_kato` (directional Kato on a finite set of configurations): for
  `e · ℓ_k = 1`, `Σ_{R,S} f(R) chMaj_k(R,S) g(S) ≤ c C_K ‖Λ_e^{1/2} f‖ ‖Λ_e^{1/2} g‖`, by Schur's
  test with the test function `Λ_e⁻²` and the Cauchy–Schwarz inequality;
* **`form_VN_le`**, **`norm_formW_le`** (eq:formW): `|⟨u, W_N v⟩| ≤ C_F ‖E^{1/4} u‖ ‖E^{1/4} v‖`,
  hence `‖E^{-1/4} W_N E^{-1/4}‖ ≤ C_F`, with `C_F = Σ_k c_k C_K √c_Λ` independent of the cutoff;
* **`weighted_Sig3sp_E14`** (eq:completionweighted in the form of the manuscript):
  `‖E^{-1/4} Σ₃^sp W_N u‖ + ‖E^{1/4} Σ₃^sp u‖ ≤ C_W (C_F + 1) ‖E^{1/4} u‖` for every `u`;
* **`inner_R3`** (`R₃^* = R₃`): the residual is symmetric, since `R₃ = H₃^ret + [Σ₃^sp, A]`;
* **`norm_Sj_le`**, **`norm_Sj_lam_le`**, **`FSAsymp.Sdirection_orders`** (eq:Sdirection as
  operator norms, for every matrix dominated entrywise by `S_j = R Σ_{b,j} Q`):
  `‖S_j‖ ≤ A_j ≤ C K⁻¹` and `‖S_j Λ_d⁻¹‖ ≤ (α_j A_j)^{1/2} ≤ C K⁻²`;
* **`FSAsymp.completion_full`** (`comp:thm:completion` with every clause): the homological
  equation, `Σ₃^* = -Σ₃`, `R₃^* = R₃`, `‖Σ₃‖ ≤ C log^q(2+K) K⁻³`, the weighted bound for every `u`,
  and `‖R₃ u‖ ≤ C log^q(2+K) K⁻³ B` on good states of budget `B`.
-/
set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace

namespace FSLattice

open Finset FSChannel

/-! ## Lattice sums -/

/-- One dyadic shell of the `|ν|⁻⁴` sum: `Σ_{ν ∈ S, lam < |ν| ≤ 2 lam} |ν|⁻⁴ ≤ 125 lam⁻¹`. -/
lemma sum_shell_inv_sq_sq_le (S : Finset L3) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∑ ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lsq ν ^ 2 ≤
      125 / lam := by
  have hlam0 : 0 < lam := by linarith
  have hsub : S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2) ⊆
      (box ⌈2 * lam⌉₊).filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2) := by
    intro ν hν
    rw [mem_filter] at hν ⊢
    exact ⟨box_mono (Nat.floor_le_ceil _) (mem_box_floor_of_lsq_le (by linarith) hν.2.2), hν.2⟩
  have hcard : ((S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2)).card : ℝ) ≤
      125 * lam ^ 3 :=
    (Nat.cast_le.mpr (card_le_card hsub)).trans (card_euclid_shell_le hlam)
  calc ∑ ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lsq ν ^ 2
      ≤ ∑ _ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lam ^ 4 := by
        apply sum_le_sum
        intro ν hν
        rw [mem_filter] at hν
        have h1 : lam ^ 4 ≤ lsq ν ^ 2 := by
          rw [show lam ^ 4 = (lam ^ 2) ^ 2 by ring]
          exact pow_le_pow_left₀ (by positivity) hν.2.1.le 2
        exact one_div_le_one_div_of_le (by positivity) h1
    _ = (S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2)).card * (1 / lam ^ 4) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 125 * lam ^ 3 * (1 / lam ^ 4) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 125 / lam := by field_simp

/-- The dyadic shells `R < |ν| ≤ 2^J R` of the `|ν|⁻⁴` sum: `≤ 250 R⁻¹`. -/
lemma sum_dyadic_inv_sq_sq_le (S : Finset L3) (J : ℕ) :
    ∀ R : ℝ, 1 ≤ R →
      ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * R) ^ 2), 1 / lsq ν ^ 2 ≤
        250 / R := by
  induction J with
  | zero =>
    intro R hR
    have hR0 : 0 < R := by linarith
    have : S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ 0 * R) ^ 2) = ∅ := by
      apply filter_false_of_mem
      intro ν _ h
      rw [pow_zero, one_mul] at h
      exact absurd h.2 (not_le.mpr h.1)
    rw [this, sum_empty]
    positivity
  | succ J ih =>
    intro R hR
    have hR0 : 0 < R := by linarith
    have h1 := sum_shell_inv_sq_sq_le S hR
    have h2 := ih (2 * R) (by linarith)
    have e : (2 : ℝ) ^ (J + 1) * R = 2 ^ J * (2 * R) := by ring
    have hsplit :
        ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ (J + 1) * R) ^ 2), 1 / lsq ν ^ 2 ≤
          ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 * R) ^ 2), 1 / lsq ν ^ 2 +
            ∑ ν ∈ S.filter (fun ν => (2 * R) ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * (2 * R)) ^ 2),
              1 / lsq ν ^ 2 := by
      rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib, e]
      apply sum_le_sum
      intro ν _
      have hnn : 0 ≤ 1 / lsq ν ^ 2 := by have := lsq_nonneg ν; positivity
      by_cases hc1 : R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * (2 * R)) ^ 2
      · by_cases hc2 : lsq ν ≤ (2 * R) ^ 2
        · rw [if_pos hc1, if_pos ⟨hc1.1, hc2⟩]
          split_ifs <;> linarith
        · rw [if_pos hc1, if_neg (fun h => hc2 h.2), if_pos ⟨not_le.mp hc2, hc1.2⟩]
          linarith
      · rw [if_neg hc1]
        split_ifs <;> linarith
    calc _ ≤ _ := hsplit
      _ ≤ 125 / R + 250 / (2 * R) := add_le_add h1 h2
      _ = 250 / R := by field_simp; ring

/-- **Lattice tail of the `|ν|⁻⁴` sum**: `Σ_{ν ∈ S, |ν| > R} |ν|⁻⁴ ≤ 250 R⁻¹` for `R ≥ 1`. -/
theorem sum_tail_inv_sq_sq_le (S : Finset L3) {R : ℝ} (hR : 1 ≤ R) :
    ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν), 1 / lsq ν ^ 2 ≤ 250 / R := by
  obtain ⟨N, hN⟩ := exists_box S
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, 3 * (N : ℝ) ^ 2 < 2 ^ J := pow_unbounded_of_one_lt _ (by norm_num)
  have hfilt : S.filter (fun ν => R ^ 2 < lsq ν) =
      S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * R) ^ 2) := by
    apply filter_congr
    intro ν hν
    refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
    have h1 := lsq_le_of_mem_box (hN hν)
    have h2 : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    have h3 : (2 : ℝ) ^ J ≤ 2 ^ J * R := le_mul_of_one_le_right (by positivity) hR
    have h4 : (1 : ℝ) ≤ 2 ^ J * R := h2.trans h3
    have h5 : 2 ^ J * R ≤ (2 ^ J * R) ^ 2 := by nlinarith
    linarith
  rw [hfilt]
  exact sum_dyadic_inv_sq_sq_le S J R hR

/-- The constant of the lattice Kato sum. -/
def CKato : ℝ := 1500

lemma CKato_pos : 0 < CKato := by norm_num [CKato]

/-- **The lattice Kato sum**: for every finite set `T` of nonzero transfers,
`Σ_{θ ∈ T} |θ|⁻² (1 + |y + θ|²)⁻¹ ≤ C_K (1 + |y|²)^{-1/2}`, uniformly in `y`. Three regions:
`|θ| ≤ |y|/2` (the Coulomb sum `≤ 13 |y|`), `|y|/2 < |θ| ≤ 3|y|` (`|θ|⁻² ≤ 4|y|⁻²` and the box sum
`Σ_{|w| ≤ 5|y|} (1 + |w|²)⁻¹`), and `|θ| > 3|y|` (`|y + θ|² ≥ (7/18)|θ|²` and the tail of
`|θ|⁻⁴`). -/
theorem kato_sum_le (y : L3) (T : Finset L3) (hT : ∀ θ ∈ T, θ ≠ 0) :
    ∑ θ ∈ T, 1 / lsq θ * (1 / (1 + lsq (y + θ))) ≤ CKato / Real.sqrt (1 + lsq y) := by
  classical
  have hpos : ∀ θ ∈ T, 1 ≤ lsq θ := fun θ hθ => one_le_lsq_of_ne_zero (hT θ hθ)
  by_cases hy : y = 0
  · -- the centre `y = 0`
    subst hy
    simp only [zero_add, lsq_zero, add_zero, Real.sqrt_one, div_one]
    have hle : ∀ θ ∈ T, 1 / lsq θ * (1 / (1 + lsq θ)) ≤ 1 / lsq θ ^ 2 := by
      intro θ hθ
      have h1 := hpos θ hθ
      rw [div_mul_div_comm, one_mul, sq]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have hlow : ∑ θ ∈ T.filter (fun θ => ¬ ((1 : ℝ) ^ 2 < lsq θ)), 1 / lsq θ ^ 2 ≤ 26 * 1 := by
      calc ∑ θ ∈ T.filter (fun θ => ¬ ((1 : ℝ) ^ 2 < lsq θ)), 1 / lsq θ ^ 2
          ≤ ∑ θ ∈ T.filter (fun θ => ¬ ((1 : ℝ) ^ 2 < lsq θ)), 1 / lsq θ := by
            refine sum_le_sum fun θ hθ => ?_
            have h1 := hpos θ (mem_filter.mp hθ).1
            exact one_div_le_one_div_of_le (by linarith) (by nlinarith)
        _ ≤ 26 * 1 := sum_inv_lsq_image_le _ (fun θ => θ) (Set.injOn_id _) zero_le_one
            (fun θ hθ => hT θ (mem_filter.mp hθ).1)
            (fun θ hθ => by
              have := (mem_filter.mp hθ).2
              push Not at this
              exact this)
    calc ∑ θ ∈ T, 1 / lsq θ * (1 / (1 + lsq θ)) ≤ ∑ θ ∈ T, 1 / lsq θ ^ 2 := sum_le_sum hle
      _ = ∑ θ ∈ T.filter (fun θ => (1 : ℝ) ^ 2 < lsq θ), 1 / lsq θ ^ 2 +
            ∑ θ ∈ T.filter (fun θ => ¬ ((1 : ℝ) ^ 2 < lsq θ)), 1 / lsq θ ^ 2 :=
          (sum_filter_add_sum_filter_not _ _ _).symm
      _ ≤ 250 / 1 + 26 * 1 := add_le_add (sum_tail_inv_sq_sq_le T le_rfl) hlow
      _ ≤ CKato := by norm_num [CKato]
  · -- `y ≠ 0`
    have hy1 : 1 ≤ lsq y := one_le_lsq_of_ne_zero hy
    set s := Real.sqrt (lsq y) with hs
    have hss : s ^ 2 = lsq y := Real.sq_sqrt (lsq_nonneg y)
    have hs1 : 1 ≤ s := by
      rw [hs, show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt hy1
    have hs0 : 0 < s := by linarith
    set w := Real.sqrt (1 + lsq y) with hw
    have hw0 : 0 < w := Real.sqrt_pos.mpr (by linarith)
    have hww : w ^ 2 = 1 + lsq y := Real.sq_sqrt (by linarith)
    have hsw : s ≤ w := Real.sqrt_le_sqrt (by linarith)
    have hws : w ≤ Real.sqrt 2 * s := by
      rw [hw, hs, ← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hnn : ∀ θ, 0 ≤ 1 / lsq θ * (1 / (1 + lsq (y + θ))) := fun θ => by
      have := lsq_nonneg θ; have := lsq_nonneg (y + θ); positivity
    -- the three regions
    set F : L3 → ℝ := fun θ => 1 / lsq θ * (1 / (1 + lsq (y + θ))) with hF
    have hsplit : ∑ θ ∈ T, F θ =
        ∑ θ ∈ T.filter (fun θ => 4 * lsq θ ≤ lsq y), F θ +
          (∑ θ ∈ T.filter (fun θ => ¬ (4 * lsq θ ≤ lsq y) ∧ lsq θ ≤ 9 * lsq y), F θ +
            ∑ θ ∈ T.filter (fun θ => ¬ (4 * lsq θ ≤ lsq y) ∧ ¬ (lsq θ ≤ 9 * lsq y)), F θ) := by
      rw [← sum_filter_add_sum_filter_not T (fun θ => 4 * lsq θ ≤ lsq y),
        ← sum_filter_add_sum_filter_not (T.filter (fun θ => ¬ (4 * lsq θ ≤ lsq y)))
          (fun θ => lsq θ ≤ 9 * lsq y), filter_filter, filter_filter]
    -- the inner region
    have hA : ∑ θ ∈ T.filter (fun θ => 4 * lsq θ ≤ lsq y), F θ ≤ 52 / w := by
      have hrow : ∀ θ ∈ T.filter (fun θ => 4 * lsq θ ≤ lsq y),
          F θ ≤ 1 / lsq θ * (4 / (1 + lsq y)) := by
        intro θ hθ
        obtain ⟨hθT, h4⟩ := mem_filter.mp hθ
        have hl := lsq_add_le (y + θ) (-θ)
        rw [add_neg_cancel_right, lsq_neg'] at hl
        have h1 : lsq y / 4 ≤ lsq (y + θ) := by linarith
        have hθ1 := hpos θ hθT
        simp only [hF]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_div_iff₀ (by have := lsq_nonneg (y + θ); linarith) (by linarith)]
        linarith
      calc ∑ θ ∈ T.filter (fun θ => 4 * lsq θ ≤ lsq y), F θ
          ≤ ∑ θ ∈ T.filter (fun θ => 4 * lsq θ ≤ lsq y), 1 / lsq θ * (4 / (1 + lsq y)) :=
            sum_le_sum hrow
        _ = (∑ θ ∈ T.filter (fun θ => 4 * lsq θ ≤ lsq y), 1 / lsq θ) * (4 / (1 + lsq y)) := by
            rw [sum_mul]
        _ ≤ (26 * (s / 2)) * (4 / (1 + lsq y)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact sum_inv_lsq_image_le _ (fun θ => θ) (Set.injOn_id _) (by positivity)
              (fun θ hθ => hT θ (mem_filter.mp hθ).1)
              (fun θ hθ => by
                have := (mem_filter.mp hθ).2
                rw [div_pow, hss]
                linarith)
        _ = 52 * s / w ^ 2 := by rw [hww]; ring
        _ ≤ 52 * w / w ^ 2 := by gcongr
        _ = 52 / w := by rw [sq, mul_div_mul_right _ _ hw0.ne']
    -- the comparable region
    have hB : ∑ θ ∈ T.filter (fun θ => ¬ (4 * lsq θ ≤ lsq y) ∧ lsq θ ≤ 9 * lsq y), F θ ≤
        524 / s := by
      set TB := T.filter (fun θ => ¬ (4 * lsq θ ≤ lsq y) ∧ lsq θ ≤ 9 * lsq y) with hTB
      have hrow : ∀ θ ∈ TB, F θ ≤ (4 / lsq y) * (1 / (1 + lsq (y + θ))) := by
        intro θ hθ
        obtain ⟨hθT, h4, _⟩ := mem_filter.mp hθ
        push Not at h4
        have hθ1 := hpos θ hθT
        simp only [hF]
        apply mul_le_mul_of_nonneg_right _ (by have := lsq_nonneg (y + θ); positivity)
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      have hsub : TB.image (fun θ => y + θ) ⊆ box ⌊5 * s⌋₊ := by
        intro x hx
        obtain ⟨θ, hθ, rfl⟩ := mem_image.mp hx
        have h9 := (mem_filter.mp hθ).2.2
        apply mem_box_floor_of_lsq_le (by positivity)
        have hl := lsq_add_le y θ
        rw [mul_pow, hss]
        nlinarith
      calc ∑ θ ∈ TB, F θ
          ≤ ∑ θ ∈ TB, (4 / lsq y) * (1 / (1 + lsq (y + θ))) := sum_le_sum hrow
        _ = (4 / lsq y) * ∑ θ ∈ TB, 1 / (1 + lsq (y + θ)) := by rw [mul_sum]
        _ = (4 / lsq y) * ∑ x ∈ TB.image (fun θ => y + θ), 1 / (1 + lsq x) := by
            rw [sum_image (fun a _ b _ h => add_left_cancel h)]
        _ ≤ (4 / lsq y) * ∑ x ∈ box ⌊5 * s⌋₊, 1 / (1 + lsq x) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by
              have := lsq_nonneg x; positivity)
        _ ≤ (4 / lsq y) * (1 + 26 * (⌊5 * s⌋₊ : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_box_inv_le _) (by positivity)
        _ ≤ (4 / lsq y) * (131 * s) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 5 * s)
            linarith
        _ = 524 / s := by rw [← hss]; field_simp; ring
    -- the far region
    have hC : ∑ θ ∈ T.filter (fun θ => ¬ (4 * lsq θ ≤ lsq y) ∧ ¬ (lsq θ ≤ 9 * lsq y)), F θ ≤
        18 / 7 * (250 / (3 * s)) := by
      set TC := T.filter (fun θ => ¬ (4 * lsq θ ≤ lsq y) ∧ ¬ (lsq θ ≤ 9 * lsq y)) with hTC
      have hrow : ∀ θ ∈ TC, F θ ≤ 18 / 7 * (1 / lsq θ ^ 2) := by
        intro θ hθ
        obtain ⟨hθT, _, h9⟩ := mem_filter.mp hθ
        push Not at h9
        have hl := lsq_add_le (y + θ) (-y)
        have e : y + θ + -y = θ := by abel
        rw [e, lsq_neg'] at hl
        have h1 : 7 * lsq θ / 18 ≤ lsq (y + θ) := by linarith
        have hθ1 := hpos θ hθT
        simp only [hF]
        calc 1 / lsq θ * (1 / (1 + lsq (y + θ))) ≤ 1 / lsq θ * (18 / (7 * lsq θ)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [div_le_div_iff₀ (by have := lsq_nonneg (y + θ); linarith) (by positivity)]
              linarith
          _ = 18 / 7 * (1 / lsq θ ^ 2) := by field_simp
      calc ∑ θ ∈ TC, F θ ≤ ∑ θ ∈ TC, 18 / 7 * (1 / lsq θ ^ 2) := sum_le_sum hrow
        _ = 18 / 7 * ∑ θ ∈ TC, 1 / lsq θ ^ 2 := by rw [mul_sum]
        _ ≤ 18 / 7 * (250 / (3 * s)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            calc ∑ θ ∈ TC, 1 / lsq θ ^ 2
                ≤ ∑ θ ∈ T.filter (fun θ => (3 * s) ^ 2 < lsq θ), 1 / lsq θ ^ 2 := by
                  apply sum_le_sum_of_subset_of_nonneg
                  · intro θ hθ
                    rw [mem_filter] at hθ ⊢
                    refine ⟨hθ.1, ?_⟩
                    have := hθ.2.2
                    push Not at this
                    rw [mul_pow, hss]
                    linarith
                  · intro θ _ _
                    have := lsq_nonneg θ
                    positivity
              _ ≤ 250 / (3 * s) := sum_tail_inv_sq_sq_le T (by linarith)
    -- assembly
    have hsw' : 1 / s ≤ Real.sqrt 2 / w := by
      rw [div_le_div_iff₀ hs0 hw0]
      linarith
    have hsqrt2 : Real.sqrt 2 < 1.415 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hBC : 524 / s + 18 / 7 * (250 / (3 * s)) ≤ 1146 / w := by
      have e : 524 / s + 18 / 7 * (250 / (3 * s)) = 15504 / 21 * (1 / s) := by
        field_simp
        ring
      rw [e]
      calc 15504 / 21 * (1 / s) ≤ 15504 / 21 * (Real.sqrt 2 / w) :=
            mul_le_mul_of_nonneg_left hsw' (by norm_num)
        _ ≤ 15504 / 21 * (1.415 / w) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact div_le_div_of_nonneg_right hsqrt2.le hw0.le
        _ ≤ 1146 / w := by
            rw [← mul_div_assoc]
            exact div_le_div_of_nonneg_right (by norm_num) hw0.le
    change ∑ θ ∈ T, F θ ≤ CKato / w
    rw [hsplit]
    calc _ ≤ 52 / w + (524 / s + 18 / 7 * (250 / (3 * s))) := add_le_add hA (add_le_add hB hC)
      _ ≤ 52 / w + 1146 / w := by linarith
      _ ≤ CKato / w := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by norm_num [CKato]) hw0.le

/-! ## The inverse mismatch on a ball (`comp:lem:relativeD`) -/

/-- The real vector of a lattice point. -/
def toR (x : L3) : Fin 3 → ℝ := fun i => (x i : ℝ)

/-- The mismatch `F_c(x, y) = |x - c|² - |y - c|²`. -/
noncomputable def Fc (c : Fin 3 → ℝ) (x y : L3) : ℝ :=
  ∑ i, ((x i : ℝ) - c i) ^ 2 - ∑ i, ((y i : ℝ) - c i) ^ 2

lemma Fc_eq_slabF (c : Fin 3 → ℝ) (x y : L3) : Fc c x y = -slabF (toR x - c) (y - x) := by
  unfold Fc slabF toR
  rw [lsq_eq_sum]
  simp only [Fin.sum_univ_three, Pi.sub_apply, Int.cast_sub]
  ring

lemma Fc_eq_slabF' (c : Fin 3 → ℝ) (x y : L3) : Fc c x y = slabF (toR y - c) (x - y) := by
  unfold Fc slabF toR
  rw [lsq_eq_sum]
  simp only [Fin.sum_univ_three, Pi.sub_apply, Int.cast_sub]
  ring

/-- The inverse-mismatch matrix `D_c(x,y) = |F_c(x,y)|⁻¹` for `x ≠ y` above the floor
`|F_c(x,y)| ≥ 2|x - y|` (eq:D). -/
noncomputable def Dc (c : Fin 3 → ℝ) (x y : L3) : ℝ :=
  if x ≠ y ∧ 2 * rho (x - y) ≤ |Fc c x y| then 1 / |Fc c x y| else 0

lemma Dc_nonneg (c : Fin 3 → ℝ) (x y : L3) : 0 ≤ Dc c x y := by
  unfold Dc
  split_ifs
  · positivity
  · exact le_rfl

lemma rho_sub_comm (x y : L3) : rho (x - y) = rho (y - x) := by
  unfold rho
  rw [lsq_sub_comm]

/-- `Σ_{w ∈ box N} (1 + |w|²)^{-1/2} ≤ 1 + 26 N²`. -/
lemma sum_box_inv_sqrt_le (N : ℕ) :
    ∑ w ∈ box N, 1 / Real.sqrt (1 + lsq w) ≤ 1 + 26 * (N : ℝ) ^ 2 := by
  have key := sum_box_le_shells (fun w => 1 / Real.sqrt (1 + lsq w)) (fun n => 1 / (n : ℝ))
    (fun n _ => by positivity)
    (fun n hn w hw => by
      have hl := lsq_ge_of_not_mem (Finset.mem_sdiff.mp hw).2 hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      apply one_div_le_one_div_of_le hn'
      rw [show (n : ℝ) = Real.sqrt ((n : ℝ) ^ 2) from (Real.sqrt_sq hn'.le).symm]
      exact Real.sqrt_le_sqrt (by linarith)) N
  have h0 : 1 / Real.sqrt (1 + lsq (0 : L3)) = 1 := by simp [lsq_zero]
  rw [h0] at key
  have hsum : ∑ n ∈ Icc 1 N, 26 * (n : ℝ) ^ 2 * (1 / (n : ℝ)) ≤ 26 * (N : ℝ) ^ 2 := by
    calc ∑ n ∈ Icc 1 N, 26 * (n : ℝ) ^ 2 * (1 / (n : ℝ)) ≤ ∑ _n ∈ Icc 1 N, 26 * (N : ℝ) := by
          refine sum_le_sum fun n hn => ?_
          have h1 := (mem_Icc.mp hn)
          have hn' : (0 : ℝ) < n := by exact_mod_cast h1.1
          have hnN : (n : ℝ) ≤ N := by exact_mod_cast h1.2
          have e : 26 * (n : ℝ) ^ 2 * (1 / (n : ℝ)) = 26 * n * (n / n) := by ring
          rw [e, div_self hn'.ne', mul_one]
          linarith
      _ = 26 * (N : ℝ) ^ 2 := by
          rw [sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
          ring
  linarith

/-- The constant of `comp:lem:relativeD`. -/
noncomputable def Crel : ℝ := CD + 44014

lemma Crel_pos : 0 < Crel := by unfold Crel CD; norm_num

/-- The rows of `D_c Λ⁻¹`: `Σ_{y ∈ X} D_c(x,y) (1 + |y|²)⁻¹ ≤ (C_D (J+2)² + 14) ⟨x⟩⁻¹`. -/
lemma Dc_row (c : Fin 3 → ℝ) {M : ℝ} (hM : 2 ≤ M) (X : Finset L3) (hX : ∀ x ∈ X, lsq x ≤ M ^ 2)
    {J : ℕ} (hJ : M ^ 2 ≤ 2 ^ J) (x : L3) (hx : x ∈ X) :
    ∑ y ∈ X, Dc c x y * (1 / (1 + lsq y)) ≤ (CD * (J + 2) ^ 2 + 14) / Real.sqrt (1 + lsq x) := by
  classical
  have hw0 : 0 < Real.sqrt (1 + lsq x) := Real.sqrt_pos.mpr (by have := lsq_nonneg x; linarith)
  set Xs := X.filter (fun y => Dc c x y ≠ 0 ∧ |Fc c x y| < 2 ^ (J + 1) * 2) with hXs
  set Xl := X.filter (fun y => ¬ (Dc c x y ≠ 0 ∧ |Fc c x y| < 2 ^ (J + 1) * 2)) with hXl
  have hsplit : ∑ y ∈ X, Dc c x y * (1 / (1 + lsq y)) =
      ∑ y ∈ Xs, Dc c x y * (1 / (1 + lsq y)) + ∑ y ∈ Xl, Dc c x y * (1 / (1 + lsq y)) :=
    (sum_filter_add_sum_filter_not X _ _).symm
  -- the small mismatches
  have hS : ∑ y ∈ Xs, Dc c x y * (1 / (1 + lsq y)) ≤ CD * (J + 2) ^ 2 / Real.sqrt (1 + lsq x) := by
    have hinj : Set.InjOn (fun y => y - x) Xs := fun a _ b _ h => sub_left_injective h
    have hT : ∀ τ ∈ Xs.image (fun y => y - x), CoreHyp (toR x - c) J τ := by
      intro τ hτ
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hτ
      obtain ⟨_, hD, hcap⟩ := mem_filter.mp hy
      unfold Dc at hD
      split_ifs at hD with hcond
      · obtain ⟨hne, hfloor⟩ := hcond
        rw [Fc_eq_slabF, abs_neg] at hfloor hcap
        refine ⟨one_le_lsq_of_ne_zero (sub_ne_zero.mpr (Ne.symm hne)), ?_, hcap⟩
        rw [← rho_sub_comm]
        exact hfloor
      · exact absurd rfl hD
    have hrow := inv_mismatch_row (toR x - c) x (Xs.image (fun y => y - x)) hT
    rw [sum_image hinj] at hrow
    have e : ∀ y ∈ Xs, Dc c x y * (1 / (1 + lsq y)) =
        1 / |slabF (toR x - c) (y - x)| * (1 / (1 + lsq (x + (y - x)))) := by
      intro y hy
      obtain ⟨_, hD, _⟩ := mem_filter.mp hy
      unfold Dc at hD ⊢
      split_ifs at hD ⊢ with hcond
      · rw [Fc_eq_slabF, abs_neg, add_sub_cancel]
      · exact absurd rfl hD
    rw [sum_congr rfl e, le_div_iff₀ hw0]
    exact (le_of_eq (mul_comm _ _)).trans hrow
  -- the large mismatches
  have hL' : ∑ y ∈ Xl, Dc c x y * (1 / (1 + lsq y)) ≤ 14 / Real.sqrt (1 + lsq x) := by
    have hM0 : 0 < M := by linarith
    have hterm : ∀ y ∈ Xl, Dc c x y * (1 / (1 + lsq y)) ≤ 1 / (4 * M ^ 2) * (1 / (1 + lsq y)) := by
      intro y hy
      have hy' := (mem_filter.mp hy).2
      apply mul_le_mul_of_nonneg_right _ (by have := lsq_nonneg y; positivity)
      by_cases hD : Dc c x y = 0
      · rw [hD]; positivity
      · have hbig : 2 ^ (J + 1) * 2 ≤ |Fc c x y| := by
          by_contra h
          exact hy' ⟨hD, not_le.mp h⟩
        have h4 : 4 * M ^ 2 ≤ |Fc c x y| := by
          have : (2 : ℝ) ^ (J + 1) * 2 = 4 * 2 ^ J := by ring
          linarith
        unfold Dc
        split_ifs
        · exact one_div_le_one_div_of_le (by positivity) h4
        · positivity
    have hbox : Xl ⊆ box ⌊M⌋₊ := fun y hy =>
      mem_box_floor_of_lsq_le hM0.le (hX y (mem_filter.mp hy).1)
    have hsum : ∑ y ∈ Xl, 1 / (1 + lsq y) ≤ 1 + 26 * M := by
      calc ∑ y ∈ Xl, 1 / (1 + lsq y) ≤ ∑ y ∈ box ⌊M⌋₊, 1 / (1 + lsq y) :=
            sum_le_sum_of_subset_of_nonneg hbox (fun y _ _ => by have := lsq_nonneg y; positivity)
        _ ≤ 1 + 26 * (⌊M⌋₊ : ℝ) := sum_box_inv_le _
        _ ≤ 1 + 26 * M := by have := Nat.floor_le hM0.le; linarith
    have hxM : Real.sqrt (1 + lsq x) ≤ 2 * M := by
      rw [show 2 * M = Real.sqrt ((2 * M) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
      exact Real.sqrt_le_sqrt (by have := hX x hx; nlinarith)
    calc ∑ y ∈ Xl, Dc c x y * (1 / (1 + lsq y))
        ≤ ∑ y ∈ Xl, 1 / (4 * M ^ 2) * (1 / (1 + lsq y)) := sum_le_sum hterm
      _ = 1 / (4 * M ^ 2) * ∑ y ∈ Xl, 1 / (1 + lsq y) := by rw [mul_sum]
      _ ≤ 1 / (4 * M ^ 2) * (1 + 26 * M) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 14 / Real.sqrt (1 + lsq x) := by
          rw [le_div_iff₀ hw0]
          calc 1 / (4 * M ^ 2) * (1 + 26 * M) * Real.sqrt (1 + lsq x)
              ≤ 1 / (4 * M ^ 2) * (1 + 26 * M) * (2 * M) :=
                mul_le_mul_of_nonneg_left hxM (by positivity)
            _ ≤ 14 := by
                rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
                nlinarith
  rw [hsplit]
  calc _ ≤ CD * (J + 2) ^ 2 / Real.sqrt (1 + lsq x) + 14 / Real.sqrt (1 + lsq x) := add_le_add hS hL'
    _ = _ := by rw [← add_div]

/-- The columns of `D_c Λ⁻¹`: `Σ_{x ∈ X} D_c(x,y) ⟨x⟩⁻¹ ≤ (C_D + 44000)(J+2)² + 7`. -/
lemma Dc_col (c : Fin 3 → ℝ) {M : ℝ} (hM : 2 ≤ M) (X : Finset L3) (hX : ∀ x ∈ X, lsq x ≤ M ^ 2)
    {J : ℕ} (hJ : M ^ 2 ≤ 2 ^ J) (y : L3) :
    ∑ x ∈ X, Dc c x y * (1 / Real.sqrt (1 + lsq x)) ≤ (CD + 44000) * (J + 2) ^ 2 + 7 := by
  classical
  set Xs := X.filter (fun x => Dc c x y ≠ 0 ∧ |Fc c x y| < 2 ^ (J + 1) * 2) with hXs
  set Xl := X.filter (fun x => ¬ (Dc c x y ≠ 0 ∧ |Fc c x y| < 2 ^ (J + 1) * 2)) with hXl
  have hsplit : ∑ x ∈ X, Dc c x y * (1 / Real.sqrt (1 + lsq x)) =
      ∑ x ∈ Xs, Dc c x y * (1 / Real.sqrt (1 + lsq x)) +
        ∑ x ∈ Xl, Dc c x y * (1 / Real.sqrt (1 + lsq x)) :=
    (sum_filter_add_sum_filter_not X _ _).symm
  have hS : ∑ x ∈ Xs, Dc c x y * (1 / Real.sqrt (1 + lsq x)) ≤ (CD + 44000) * (J + 2) ^ 2 := by
    have hinj : Set.InjOn (fun x => x - y) Xs := fun a _ b _ h => sub_left_injective h
    have hT : ∀ τ ∈ Xs.image (fun x => x - y), CoreHyp (toR y - c) J τ := by
      intro τ hτ
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hτ
      obtain ⟨_, hD, hcap⟩ := mem_filter.mp hx
      unfold Dc at hD
      split_ifs at hD with hcond
      · obtain ⟨hne, hfloor⟩ := hcond
        rw [Fc_eq_slabF'] at hfloor hcap
        exact ⟨one_le_lsq_of_ne_zero (sub_ne_zero.mpr hne), hfloor, hcap⟩
      · exact absurd rfl hD
    have hcol := inv_mismatch_col (toR y - c) y (Xs.image (fun x => x - y)) hT
    rw [sum_image hinj] at hcol
    have e : ∀ x ∈ Xs, Dc c x y * (1 / Real.sqrt (1 + lsq x)) =
        1 / |slabF (toR y - c) (x - y)| * (1 / Real.sqrt (1 + lsq (y + (x - y)))) := by
      intro x hx
      obtain ⟨_, hD, _⟩ := mem_filter.mp hx
      unfold Dc at hD ⊢
      split_ifs at hD ⊢ with hcond
      · rw [Fc_eq_slabF', add_sub_cancel]
      · exact absurd rfl hD
    rw [sum_congr rfl e]
    exact hcol
  have hL' : ∑ x ∈ Xl, Dc c x y * (1 / Real.sqrt (1 + lsq x)) ≤ 7 := by
    have hM0 : 0 < M := by linarith
    have hterm : ∀ x ∈ Xl, Dc c x y * (1 / Real.sqrt (1 + lsq x)) ≤
        1 / (4 * M ^ 2) * (1 / Real.sqrt (1 + lsq x)) := by
      intro x hx
      have hx' := (mem_filter.mp hx).2
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      by_cases hD : Dc c x y = 0
      · rw [hD]; positivity
      · have hbig : 2 ^ (J + 1) * 2 ≤ |Fc c x y| := by
          by_contra h
          exact hx' ⟨hD, not_le.mp h⟩
        have h4 : 4 * M ^ 2 ≤ |Fc c x y| := by
          have : (2 : ℝ) ^ (J + 1) * 2 = 4 * 2 ^ J := by ring
          linarith
        unfold Dc
        split_ifs
        · exact one_div_le_one_div_of_le (by positivity) h4
        · positivity
    have hbox : Xl ⊆ box ⌊M⌋₊ := fun x hx =>
      mem_box_floor_of_lsq_le hM0.le (hX x (mem_filter.mp hx).1)
    have hsum : ∑ x ∈ Xl, 1 / Real.sqrt (1 + lsq x) ≤ 1 + 26 * M ^ 2 := by
      calc ∑ x ∈ Xl, 1 / Real.sqrt (1 + lsq x) ≤ ∑ x ∈ box ⌊M⌋₊, 1 / Real.sqrt (1 + lsq x) :=
            sum_le_sum_of_subset_of_nonneg hbox (fun x _ _ => by positivity)
        _ ≤ 1 + 26 * (⌊M⌋₊ : ℝ) ^ 2 := sum_box_inv_sqrt_le _
        _ ≤ 1 + 26 * M ^ 2 := by
            have := Nat.floor_le hM0.le
            have h0 : (0 : ℝ) ≤ ⌊M⌋₊ := Nat.cast_nonneg _
            nlinarith
    calc ∑ x ∈ Xl, Dc c x y * (1 / Real.sqrt (1 + lsq x))
        ≤ ∑ x ∈ Xl, 1 / (4 * M ^ 2) * (1 / Real.sqrt (1 + lsq x)) := sum_le_sum hterm
      _ = 1 / (4 * M ^ 2) * ∑ x ∈ Xl, 1 / Real.sqrt (1 + lsq x) := by rw [mul_sum]
      _ ≤ 1 / (4 * M ^ 2) * (1 + 26 * M ^ 2) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 7 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  rw [hsplit]
  linarith

/-- **`comp:lem:relativeD`** (eq:Drelative): for a finite set `X` of lattice points in the ball
`|x| ≤ M` (`M ≥ 2`), every centre `c` and every `J` with `M² ≤ 2^J`, and every complex matrix
with `|B(x,y)| ≤ b₀ D_c(x,y)`: `‖B Λ⁻¹ v‖ ≤ b₀ C_rel (J + 2)² ‖v‖`, `Λ(y) = (1 + |y|²)^{1/2}`. -/
theorem relativeD (c : Fin 3 → ℝ) {M : ℝ} (hM : 2 ≤ M) (X : Finset L3)
    (hX : ∀ x ∈ X, lsq x ≤ M ^ 2) {J : ℕ} (hJ : M ^ 2 ≤ 2 ^ J) (B : L3 → L3 → ℂ) {b₀ : ℝ}
    (hb₀ : 0 ≤ b₀) (hB : ∀ x y, ‖B x y‖ ≤ b₀ * Dc c x y) (v : L3 → ℂ) :
    ∑ x ∈ X, ‖∑ y ∈ X, B x y * ((1 / Real.sqrt (1 + lsq y) : ℝ) : ℂ) * v y‖ ^ 2 ≤
      (b₀ * Crel * (J + 2) ^ 2) ^ 2 * ∑ y ∈ X, ‖v y‖ ^ 2 := by
  have hJ2 : (4 : ℝ) ≤ (J + 2) ^ 2 := by
    have : (2 : ℝ) ≤ J + 2 := by have := Nat.cast_nonneg (α := ℝ) J; linarith
    nlinarith
  have hCD : 0 ≤ CD := by unfold CD; norm_num
  set a := b₀ * (CD * (J + 2) ^ 2 + 14) with ha
  set b := b₀ * ((CD + 44000) * (J + 2) ^ 2 + 7) with hb
  have hw : ∀ y : L3, 0 < Real.sqrt (1 + lsq y) := fun y =>
    Real.sqrt_pos.mpr (by have := lsq_nonneg y; linarith)
  have h := wschur X X (fun x y => B x y * ((1 / Real.sqrt (1 + lsq y) : ℝ) : ℂ))
    (fun x => 1 / Real.sqrt (1 + lsq x)) (fun y => 1 / Real.sqrt (1 + lsq y))
    (fun y _ => by have := hw y; positivity) ((by rw [ha]; positivity) : 0 ≤ a)
    (fun x hx => by
      have hrow := Dc_row c hM X hX hJ x hx
      calc ∑ y ∈ X, ‖B x y * ((1 / Real.sqrt (1 + lsq y) : ℝ) : ℂ)‖ * (1 / Real.sqrt (1 + lsq y))
          ≤ ∑ y ∈ X, b₀ * (Dc c x y * (1 / (1 + lsq y))) := by
            refine sum_le_sum fun y _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by have := hw y; positivity)]
            have e : 1 / Real.sqrt (1 + lsq y) * (1 / Real.sqrt (1 + lsq y)) = 1 / (1 + lsq y) := by
              rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by have := lsq_nonneg y; linarith)]
            calc ‖B x y‖ * (1 / Real.sqrt (1 + lsq y)) * (1 / Real.sqrt (1 + lsq y))
                = ‖B x y‖ * (1 / (1 + lsq y)) := by rw [mul_assoc, e]
              _ ≤ b₀ * Dc c x y * (1 / (1 + lsq y)) :=
                  mul_le_mul_of_nonneg_right (hB x y) (by have := lsq_nonneg y; positivity)
              _ = b₀ * (Dc c x y * (1 / (1 + lsq y))) := by ring
        _ = b₀ * ∑ y ∈ X, Dc c x y * (1 / (1 + lsq y)) := by rw [mul_sum]
        _ ≤ b₀ * ((CD * (J + 2) ^ 2 + 14) / Real.sqrt (1 + lsq x)) :=
            mul_le_mul_of_nonneg_left hrow hb₀
        _ = a * (1 / Real.sqrt (1 + lsq x)) := by rw [ha]; ring)
    (fun y _ => by
      have hcol := Dc_col c hM X hX hJ y
      calc ∑ x ∈ X, ‖B x y * ((1 / Real.sqrt (1 + lsq y) : ℝ) : ℂ)‖ * (1 / Real.sqrt (1 + lsq x))
          ≤ ∑ x ∈ X, b₀ * (1 / Real.sqrt (1 + lsq y)) *
              (Dc c x y * (1 / Real.sqrt (1 + lsq x))) := by
            refine sum_le_sum fun x _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by have := hw y; positivity)]
            have h1 := hB x y
            have h2 : 0 ≤ 1 / Real.sqrt (1 + lsq y) := by have := hw y; positivity
            have h3 : 0 ≤ 1 / Real.sqrt (1 + lsq x) := by have := hw x; positivity
            calc ‖B x y‖ * (1 / Real.sqrt (1 + lsq y)) * (1 / Real.sqrt (1 + lsq x))
                ≤ b₀ * Dc c x y * (1 / Real.sqrt (1 + lsq y)) * (1 / Real.sqrt (1 + lsq x)) := by
                  gcongr
              _ = _ := by ring
        _ = b₀ * (1 / Real.sqrt (1 + lsq y)) * ∑ x ∈ X, Dc c x y * (1 / Real.sqrt (1 + lsq x)) := by
            rw [mul_sum]
        _ ≤ b₀ * (1 / Real.sqrt (1 + lsq y)) * ((CD + 44000) * (J + 2) ^ 2 + 7) :=
            mul_le_mul_of_nonneg_left hcol (by have := hw y; positivity)
        _ = b * (1 / Real.sqrt (1 + lsq y)) := by rw [hb]; ring) v
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _))
  have hCrel : Crel = CD + 44014 := rfl
  have ha' : a ≤ b₀ * Crel * (J + 2) ^ 2 := by
    rw [ha, hCrel, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hb₀
    nlinarith
  have hb' : b ≤ b₀ * Crel * (J + 2) ^ 2 := by
    rw [hb, hCrel, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hb₀
    nlinarith
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hC0 : 0 ≤ b₀ * Crel * (J + 2) ^ 2 := by have := Crel_pos; positivity
  calc a * b ≤ (b₀ * Crel * (J + 2) ^ 2) * (b₀ * Crel * (J + 2) ^ 2) :=
        mul_le_mul ha' hb' hb0 hC0
    _ = _ := (sq _).symm

/-- **`comp:lem:relativeD` with the logarithm**: `‖B Λ⁻¹ v‖ ≤ 49 b₀ C_rel log²(2 + M) ‖v‖`. -/
theorem relativeD_log (c : Fin 3 → ℝ) {M : ℝ} (hM : 2 ≤ M) (X : Finset L3)
    (hX : ∀ x ∈ X, lsq x ≤ M ^ 2) (B : L3 → L3 → ℂ) {b₀ : ℝ} (hb₀ : 0 ≤ b₀)
    (hB : ∀ x y, ‖B x y‖ ≤ b₀ * Dc c x y) (v : L3 → ℂ) :
    ∑ x ∈ X, ‖∑ y ∈ X, B x y * ((1 / Real.sqrt (1 + lsq y) : ℝ) : ℂ) * v y‖ ^ 2 ≤
      (49 * b₀ * Crel * Real.log (2 + M) ^ 2) ^ 2 * ∑ y ∈ X, ‖v y‖ ^ 2 := by
  have hM0 : 0 < M := by linarith
  have hl2h := FSAsymp.half_le_log_two
  have hl2 : 0 < Real.log 2 := by linarith
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hJc : 2 * Real.log M / Real.log 2 ≤ (⌈2 * Real.log M / Real.log 2⌉₊ : ℝ) := Nat.le_ceil _
  have hJ : M ^ 2 ≤ 2 ^ ⌈2 * Real.log M / Real.log 2⌉₊ := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    rw [div_le_iff₀ hl2] at hJc
    push_cast
    linarith
  have hJ1 : (⌈2 * Real.log M / Real.log 2⌉₊ : ℝ) < 2 * Real.log M / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by linarith) hl2.le)
  generalize ⌈2 * Real.log M / Real.log 2⌉₊ = J at hJ hJ1
  have h := relativeD c hM X hX hJ B hb₀ hB v
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun _ _ => sq_nonneg _))
  -- `J + 2 ≤ 7 log(2 + M)`
  have hlog1 : 1 ≤ Real.log (2 + M) := FSAsymp.one_le_log_two_add hM
  have hlogb : 2 * Real.log M / Real.log 2 ≤ 4 * Real.log (2 + M) := by
    rw [div_le_iff₀ hl2]
    have : Real.log M ≤ Real.log (2 + M) := Real.log_le_log hM0 (by linarith)
    nlinarith
  have hJ7 : (J : ℝ) + 2 ≤ 7 * Real.log (2 + M) := by linarith
  have hCrel := Crel_pos
  have hJ0 : (0 : ℝ) ≤ J + 2 := by have := Nat.cast_nonneg (α := ℝ) J; linarith
  have hsq : ((J : ℝ) + 2) ^ 2 ≤ 49 * Real.log (2 + M) ^ 2 := by nlinarith
  have hpos : 0 ≤ b₀ * Crel * ((J : ℝ) + 2) ^ 2 := by positivity
  apply pow_le_pow_left₀ hpos
  calc b₀ * Crel * ((J : ℝ) + 2) ^ 2 ≤ b₀ * Crel * (49 * Real.log (2 + M) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 49 * b₀ * Crel * Real.log (2 + M) ^ 2 := by ring

end FSLattice

namespace FSNormal

open Finset

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Directional Kato on finite sets -/

omit [Fintype ν] in
lemma chMaj_symm (k : Ch eta) (c : ℝ) (R S : Cf eta) : chMaj k c R S = chMaj k c S R := by
  unfold chMaj
  by_cases h : OnCh k R S
  · rw [if_pos h, if_pos (onCh_symm h), ← neg_sub, latticeNormSq_neg]
  · rw [if_neg h, if_neg (fun h' => h (onCh_symm h'))]

omit [Fintype ν] in
/-- **The Kato row**: `Σ_{S ∈ F} chMaj_k(R,S) Λ_e(S)⁻² ≤ c C_K Λ_e(R)⁻¹` for `e · ℓ_k = 1`. -/
lemma kato_row (k : Ch eta) {e : Fin eta → ℤ} (he : dl e k = 1) {c : ℝ} (hc : 0 ≤ c)
    (F : Finset (Cf eta)) (R : Cf eta) :
    ∑ S ∈ F, chMaj k c R S * (1 / (1 + FSLattice.lsq (dsum e S))) ≤
      c * FSLattice.CKato / lam e R := by
  classical
  set G := F.filter (fun S => OnCh k R S ∧ S ≠ R) with hG
  set y := dsum e R with hy
  have hred : ∑ S ∈ F, chMaj k c R S * (1 / (1 + FSLattice.lsq (dsum e S))) =
      ∑ S ∈ G, c * (1 / FSLattice.lsq (dsum e S - y) *
        (1 / (1 + FSLattice.lsq (y + (dsum e S - y))))) := by
    rw [sum_filter]
    refine sum_congr rfl fun S _ => ?_
    unfold chMaj
    by_cases h : OnCh k R S
    · have htr := (onCh_of_fkey_eq (fkey_eq_of_onCh he h)).2
      by_cases hSR : S = R
      · subst hSR
        rw [if_pos h, if_neg (fun h' => h'.2 rfl), sub_self]
        simp [latticeNormSq]
      · rw [if_pos h, if_pos ⟨h, hSR⟩, htr]
        have e1 : y + (dsum e S - y) = dsum e S := by abel
        have e2 : latticeNormSq (dsum e R - dsum e S) = FSLattice.lsq (dsum e S - y) := by
          rw [← neg_sub, latticeNormSq_neg]
          rfl
        rw [e1, e2]
        ring
    · rw [if_neg h, if_neg (fun h' => h h'.1), zero_mul]
  rw [hred, ← mul_sum]
  have hinj : Set.InjOn (fun S => dsum e S - y) G := by
    intro S hS S' hS' hSS'
    have h1 := (mem_filter.mp hS).2.1
    have h2 := (mem_filter.mp hS').2.1
    have hk : fkey k e S = fkey k e S' :=
      (fkey_eq_of_onCh he h1).symm.trans (fkey_eq_of_onCh he h2)
    exact dsum_inj_of_fkey hk (sub_left_injective hSS')
  have hne : ∀ θ ∈ G.image (fun S => dsum e S - y), θ ≠ 0 := by
    intro θ hθ
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hθ
    obtain ⟨_, h1, hSR⟩ := mem_filter.mp hS
    intro h0
    have hk : fkey k e S = fkey k e R := (fkey_eq_of_onCh he h1).symm
    exact hSR (dsum_inj_of_fkey hk (sub_eq_zero.mp h0))
  have hsum := FSLattice.kato_sum_le y (G.image (fun S => dsum e S - y)) hne
  rw [sum_image hinj] at hsum
  calc c * ∑ S ∈ G, 1 / FSLattice.lsq (dsum e S - y) *
        (1 / (1 + FSLattice.lsq (y + (dsum e S - y))))
      ≤ c * (FSLattice.CKato / Real.sqrt (1 + FSLattice.lsq y)) :=
        mul_le_mul_of_nonneg_left hsum hc
    _ = c * FSLattice.CKato / lam e R := by unfold lam; rw [hy]; ring

omit [Fintype ν] in
/-- **Schur's test as a bilinear bound**: for a nonnegative symmetric kernel `K`, a positive test
function `h` and a weight `w` with `Σ_S K(R,S) h(S) ≤ A w(R) h(R)`,
`Σ_{R,S} f(R) K(R,S) g(S) ≤ A (Σ_R w f²)^{1/2} (Σ_S w g²)^{1/2}`. -/
theorem schur_bilinear {α : Type*} (F : Finset α) (K : α → α → ℝ) (h w : α → ℝ) {A : ℝ}
    (hK0 : ∀ R S, 0 ≤ K R S) (hsym : ∀ R S, K R S = K S R) (hh0 : ∀ S, 0 < h S) (hA : 0 ≤ A)
    (hw0 : ∀ R, 0 ≤ w R) (hrow : ∀ R ∈ F, ∑ S ∈ F, K R S * h S ≤ A * (w R * h R))
    (f g : α → ℝ) :
    ∑ R ∈ F, ∑ S ∈ F, f R * K R S * g S ≤
      A * (Real.sqrt (∑ R ∈ F, w R * f R ^ 2) * Real.sqrt (∑ S ∈ F, w S * g S ^ 2)) := by
  obtain ⟨a, ha⟩ : ∃ a : α × α → ℝ, a = fun x => f x.1 * Real.sqrt (K x.1 x.2 * h x.2 / h x.1) :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : α × α → ℝ, b = fun x => g x.2 * Real.sqrt (K x.1 x.2 * h x.1 / h x.2) :=
    ⟨_, rfl⟩
  have hab : ∀ R S, a (R, S) * b (R, S) = f R * K R S * g S := by
    intro R S
    rw [ha, hb]
    dsimp only
    have h1 := hh0 R
    have h2 := hh0 S
    have hk := hK0 R S
    have e : Real.sqrt (K R S * h S / h R) * Real.sqrt (K R S * h R / h S) = K R S := by
      rw [← Real.sqrt_mul (by positivity)]
      have : K R S * h S / h R * (K R S * h R / h S) = K R S ^ 2 := by
        rw [div_mul_div_comm, div_eq_iff (by positivity)]
        ring
      rw [this, Real.sqrt_sq hk]
    calc f R * Real.sqrt (K R S * h S / h R) * (g S * Real.sqrt (K R S * h R / h S))
        = f R * (Real.sqrt (K R S * h S / h R) * Real.sqrt (K R S * h R / h S)) * g S := by ring
      _ = f R * K R S * g S := by rw [e]
  have hA' : ∑ x ∈ F ×ˢ F, a x ^ 2 ≤ A * ∑ R ∈ F, w R * f R ^ 2 := by
    rw [sum_product, mul_sum]
    refine sum_le_sum fun R hR => ?_
    have e : ∀ S ∈ F, a (R, S) ^ 2 = f R ^ 2 / h R * (K R S * h S) := by
      intro S _
      rw [ha]
      dsimp only
      have h1 := hh0 R
      have h2 := hh0 S
      have hk := hK0 R S
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [sum_congr rfl e, ← mul_sum]
    have h1 := hh0 R
    calc f R ^ 2 / h R * ∑ S ∈ F, K R S * h S ≤ f R ^ 2 / h R * (A * (w R * h R)) :=
          mul_le_mul_of_nonneg_left (hrow R hR) (by positivity)
      _ = A * (w R * f R ^ 2) := by
          rw [div_mul_eq_mul_div, div_eq_iff h1.ne']
          ring
  have hB' : ∑ x ∈ F ×ˢ F, b x ^ 2 ≤ A * ∑ S ∈ F, w S * g S ^ 2 := by
    rw [sum_product_right, mul_sum]
    refine sum_le_sum fun S hS => ?_
    have e : ∀ R ∈ F, b (R, S) ^ 2 = g S ^ 2 / h S * (K S R * h R) := by
      intro R _
      rw [hb]
      dsimp only
      have h1 := hh0 R
      have h2 := hh0 S
      have hk := hK0 R S
      rw [mul_pow, Real.sq_sqrt (by positivity), hsym R S]
      ring
    rw [sum_congr rfl e, ← mul_sum]
    have h2 := hh0 S
    calc g S ^ 2 / h S * ∑ R ∈ F, K S R * h R ≤ g S ^ 2 / h S * (A * (w S * h S)) :=
          mul_le_mul_of_nonneg_left (hrow S hS) (by positivity)
      _ = A * (w S * g S ^ 2) := by
          rw [div_mul_eq_mul_div, div_eq_iff h2.ne']
          ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (F ×ˢ F) a b
  have hsum : ∑ R ∈ F, ∑ S ∈ F, f R * K R S * g S = ∑ x ∈ F ×ˢ F, a x * b x := by
    rw [sum_product]
    exact sum_congr rfl fun R _ => sum_congr rfl fun S _ => (hab R S).symm
  rw [hsum]
  have hA0 : 0 ≤ ∑ R ∈ F, w R * f R ^ 2 := sum_nonneg fun R _ => mul_nonneg (hw0 R) (sq_nonneg _)
  have hB0 : 0 ≤ ∑ S ∈ F, w S * g S ^ 2 := sum_nonneg fun S _ => mul_nonneg (hw0 S) (sq_nonneg _)
  calc ∑ x ∈ F ×ˢ F, a x * b x ≤ |∑ x ∈ F ×ˢ F, a x * b x| := le_abs_self _
    _ = Real.sqrt ((∑ x ∈ F ×ˢ F, a x * b x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ x ∈ F ×ˢ F, a x ^ 2) * ∑ x ∈ F ×ˢ F, b x ^ 2) := Real.sqrt_le_sqrt hCS
    _ ≤ Real.sqrt ((A * ∑ R ∈ F, w R * f R ^ 2) * (A * ∑ S ∈ F, w S * g S ^ 2)) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul hA' hB' (sum_nonneg fun x _ => sq_nonneg _) (mul_nonneg hA hA0)
    _ = A * (Real.sqrt (∑ R ∈ F, w R * f R ^ 2) * Real.sqrt (∑ S ∈ F, w S * g S ^ 2)) := by
        rw [show (A * ∑ R ∈ F, w R * f R ^ 2) * (A * ∑ S ∈ F, w S * g S ^ 2) =
            A ^ 2 * ((∑ R ∈ F, w R * f R ^ 2) * ∑ S ∈ F, w S * g S ^ 2) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA, Real.sqrt_mul hA0]

omit [Fintype ν] in
/-- **Directional Kato on a finite set of configurations**: for `e · ℓ_k = 1`,
`Σ_{R,S ∈ F} f(R) chMaj_k(R,S) g(S) ≤ c C_K (Σ_R Λ_e(R) f(R)²)^{1/2} (Σ_S Λ_e(S) g(S)²)^{1/2}`. -/
theorem dir_kato (k : Ch eta) {e : Fin eta → ℤ} (he : dl e k = 1) {c : ℝ} (hc : 0 ≤ c)
    (F : Finset (Cf eta)) (f g : Cf eta → ℝ) :
    ∑ R ∈ F, ∑ S ∈ F, f R * chMaj k c R S * g S ≤
      c * FSLattice.CKato *
        (Real.sqrt (∑ R ∈ F, lam e R * f R ^ 2) * Real.sqrt (∑ S ∈ F, lam e S * g S ^ 2)) := by
  have hrow : ∀ R ∈ F, ∑ S ∈ F, chMaj k c R S * (1 / (1 + FSLattice.lsq (dsum e S))) ≤
      c * FSLattice.CKato * (lam e R * (1 / (1 + FSLattice.lsq (dsum e R)))) := by
    intro R _
    have h := kato_row k he hc F R
    have hl := lam_pos e R
    have e2 : lam e R * (1 / (1 + FSLattice.lsq (dsum e R))) = 1 / lam e R := by
      rw [← lam_sq, mul_one_div, div_eq_div_iff (pow_ne_zero 2 hl.ne') hl.ne']
      ring
    refine h.trans_eq ?_
    rw [e2]
    ring
  exact schur_bilinear F (chMaj k c) (fun S => 1 / (1 + FSLattice.lsq (dsum e S))) (lam e)
    (fun R S => chMaj_nonneg k hc R S) (fun R S => chMaj_symm k c R S)
    (fun S => by have := FSLattice.lsq_nonneg (dsum e S); positivity)
    (mul_nonneg hc FSLattice.CKato_pos.le) (fun R => (lam_pos e R).le) hrow f g

/-! ## The Coulomb form bound on the cube (eq:formW) -/

omit [Fintype ν] in
lemma dl_single_lead (k : Ch eta) : dl (Pi.single (lead k) 1 : Fin eta → ℤ) k = 1 := by
  cases k with
  | inl a => simp [dl, lead]
  | inr pr =>
    have h : pr.1.2 ≠ pr.1.1 := (ne_of_lt pr.2).symm
    simp [dl, lead, h]

omit [Fintype ν] in
lemma l1_single_lead (k : Ch eta) : l1 (Pi.single (lead k) 1 : Fin eta → ℤ) ≤ 2 := by
  rw [l1_single]; norm_num

omit [Fintype ν] in
/-- Directional Kato on the cube:
`Σ_{q,p} f(q) chMaj_k(q,p) g(p) ≤ c C_K (Σ_q Λ_e f²)^{1/2} (Σ_p Λ_e g²)^{1/2}`. -/
lemma dir_kato_cube {n : ℕ} (k : Ch eta) {e : Fin eta → ℤ} (he : dl e k = 1) {c : ℝ}
    (hc : 0 ≤ c) (f g : Cfg eta n → ℝ) :
    ∑ q, ∑ p, f q * chMaj k c (cidx n q) (cidx n p) * g p ≤
      c * FSLattice.CKato * (Real.sqrt (∑ q, lam e (cidx n q) * f q ^ 2) *
        Real.sqrt (∑ p, lam e (cidx n p) * g p ^ 2)) := by
  classical
  set F := (Finset.univ : Finset (Cfg eta n)).image (cidx n) with hF
  have hinj : Function.Injective (cidx n : Cfg eta n → Cf eta) :=
    finiteConfigLatticeIndex_injective eta n
  set f' : Cf eta → ℝ := fun S => if h : ∃ p, cidx n p = S then f h.choose else 0 with hf'def
  set g' : Cf eta → ℝ := fun S => if h : ∃ p, cidx n p = S then g h.choose else 0 with hg'def
  have hf' : ∀ p, f' (cidx n p) = f p := by
    intro p
    have h : ∃ p', cidx n p' = cidx n p := ⟨p, rfl⟩
    simp only [hf'def, dif_pos h]
    rw [hinj h.choose_spec]
  have hg' : ∀ p, g' (cidx n p) = g p := by
    intro p
    have h : ∃ p', cidx n p' = cidx n p := ⟨p, rfl⟩
    simp only [hg'def, dif_pos h]
    rw [hinj h.choose_spec]
  have h := dir_kato k he hc F f' g'
  have hconv1 : ∑ R ∈ F, ∑ S ∈ F, f' R * chMaj k c R S * g' S =
      ∑ q, ∑ p, f q * chMaj k c (cidx n q) (cidx n p) * g p := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    simp only [hf', hg']
  have hconv2 : ∀ φ : Cf eta → ℝ, ∑ R ∈ F, lam e R * φ R ^ 2 =
      ∑ q, lam e (cidx n q) * φ (cidx n q) ^ 2 := fun φ => by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
  rw [hconv1, hconv2, hconv2] at h
  simpa only [hf', hg'] using h

omit [Fintype ν] in
lemma wt_wt {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ} (s t : ℝ) (v : En eta n) :
    FSSpectral.wt (sb eta n) (Asym sys L n) s (FSSpectral.wt (sb eta n) (Asym sys L n) t v) =
      FSSpectral.wt (sb eta n) (Asym sys L n) (s + t) v := by
  rw [wt_eq_dg (sys := sys) (L := L) s, wt_eq_dg (sys := sys) (L := L) t,
    wt_eq_dg (sys := sys) (L := L) (s + t)]
  ext q
  simp only [FSKernel.dg_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add (one_add_asym_pos (sys := sys) (L := L) q)]

omit [Fintype ν] in
lemma wt_zero' {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ} (v : En eta n) :
    FSSpectral.wt (sb eta n) (Asym sys L n) 0 v = v := by
  rw [wt_eq_dg (sys := sys) (L := L)]
  ext q
  simp

omit [Fintype ν] in
lemma wt_wt_neg {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ} (s : ℝ) (v : En eta n) :
    FSSpectral.wt (sb eta n) (Asym sys L n) s (FSSpectral.wt (sb eta n) (Asym sys L n) (-s) v) =
      v := by
  rw [wt_wt, add_neg_cancel, wt_zero']

omit [Fintype ν] in
lemma wt_neg_wt {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ} (s : ℝ) (v : En eta n) :
    FSSpectral.wt (sb eta n) (Asym sys L n) (-s) (FSSpectral.wt (sb eta n) (Asym sys L n) s v) =
      v := by
  rw [wt_wt, neg_add_cancel, wt_zero']

section Cube

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

variable (sys) in
/-- `C_F = Σ_k c_k C_K √c_Λ`, the constant of the Coulomb form bound (independent of the
cutoff). -/
noncomputable def CF (L : ℝ) : ℝ :=
  ∑ k : Ch eta, chC sys L k * FSLattice.CKato * Real.sqrt (cLam sys L)

lemma CF_nonneg (hL : 0 < L) : 0 ≤ CF sys L := by
  unfold CF
  refine Finset.sum_nonneg fun k _ => ?_
  have := chC_nonneg sys hL k
  have := FSLattice.CKato_pos
  positivity

omit [Fintype ν] in
lemma sum_lam_le_wt (hL : 0 < L) (k : Ch eta) (u : En eta n) :
    ∑ q, lam (Pi.single (lead k) 1) (cidx n q) * ‖u.ofLp q‖ ^ 2 ≤
      Real.sqrt (cLam sys L) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) u‖ ^ 2 := by
  rw [wt_eq_dg (sys := sys) (L := L), FSKernel.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have hA := one_add_asym_pos (sys := sys) (L := L) q
  rw [FSKernel.dg_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hA _), mul_pow]
  have hm := lam_mul_le (sys := sys) hL (l1_single_lead k) (l1_single_lead k) q
  have hlam : lam (Pi.single (lead k) 1) (cidx n q) ≤
      Real.sqrt (cLam sys L) * Real.sqrt (1 + Asym sys L n q) := by
    rw [← Real.sqrt_mul (cLam_pos (sys := sys) L).le]
    calc lam (Pi.single (lead k) 1) (cidx n q)
        = Real.sqrt (lam (Pi.single (lead k) 1) (cidx n q) *
            lam (Pi.single (lead k) 1) (cidx n q)) :=
          (Real.sqrt_mul_self (lam_pos _ _).le).symm
      _ ≤ Real.sqrt (cLam sys L * (1 + Asym sys L n q)) := Real.sqrt_le_sqrt hm
  have hq : ((1 + Asym sys L n q) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (1 + Asym sys L n q) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le, Real.sqrt_eq_rpow]
    norm_num
  rw [hq]
  calc lam (Pi.single (lead k) 1) (cidx n q) * ‖u.ofLp q‖ ^ 2
      ≤ (Real.sqrt (cLam sys L) * Real.sqrt (1 + Asym sys L n q)) * ‖u.ofLp q‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hlam (sq_nonneg _)
    _ = Real.sqrt (cLam sys L) * (Real.sqrt (1 + Asym sys L n q) * ‖u.ofLp q‖ ^ 2) := by ring

/-- **The Coulomb form bound** (eq:formW, bilinear form): `|⟨u, W_N v⟩| ≤ C_F ‖E^{1/4} u‖ ‖E^{1/4} v‖`,
by directional Kato in each channel. -/
theorem form_VN_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (u v : En eta n) :
    ‖⟪u, VN sys L n v⟫_ℂ‖ ≤ CF sys L * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) u‖ *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) v‖ := by
  classical
  set Wu := ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) u‖ with hWu
  set Wv := ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) v‖ with hWv
  have hV : VN sys L n v = FSKernel.kop (wNK sys L n) v := by
    rw [← VN_eq_kop sys hL H hKernel]
    rfl
  have h1 : ‖⟪u, VN sys L n v⟫_ℂ‖ ≤
      ∑ q, ∑ p, ‖u.ofLp q‖ * ‖wNK sys L n q p‖ * ‖v.ofLp p‖ := by
    rw [hV, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_mul, Pi.star_apply, norm_star, FSKernel.kop_apply]
    calc ‖∑ p, v.ofLp p * wNK sys L n q p‖ * ‖u.ofLp q‖
        ≤ (∑ p, ‖v.ofLp p‖ * ‖wNK sys L n q p‖) * ‖u.ofLp q‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp only [norm_mul]
      _ = ∑ p, ‖u.ofLp q‖ * ‖wNK sys L n q p‖ * ‖v.ofLp p‖ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun p _ => by ring
  have h2 : ∀ q p, ‖wNK sys L n q p‖ ≤ ∑ k, chMaj k (chC sys L k) (cidx n q) (cidx n p) := by
    intro q p
    rw [wNK_eq_sum_chPart hL q p]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    unfold chPart wNK
    split_ifs with h
    · rw [← lcp_of_onCh (κ := potKernel sys L) h]
      exact norm_lcp_pot_le hL k _ _
    · rw [norm_zero]
      exact chMaj_nonneg k (chC_nonneg sys hL k) _ _
  have hcL := cLam_pos (sys := sys) L
  have hcK := FSLattice.CKato_pos
  have h3 : ∀ k : Ch eta, ∑ q, ∑ p, ‖u.ofLp q‖ * chMaj k (chC sys L k) (cidx n q) (cidx n p) *
      ‖v.ofLp p‖ ≤ chC sys L k * FSLattice.CKato * Real.sqrt (cLam sys L) * Wu * Wv := by
    intro k
    have hk := dir_kato_cube (n := n) k (dl_single_lead k) (chC_nonneg sys hL k)
      (fun q => ‖u.ofLp q‖) (fun p => ‖v.ofLp p‖)
    have hu := sum_lam_le_wt (sys := sys) hL k u
    have hv := sum_lam_le_wt (sys := sys) hL k v
    have hc := chC_nonneg sys hL k
    refine hk.trans ?_
    have e1 : Real.sqrt (Real.sqrt (cLam sys L) * Wu ^ 2) = Real.sqrt (Real.sqrt (cLam sys L)) * Wu := by
      rw [Real.sqrt_mul (Real.sqrt_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have e2 : Real.sqrt (Real.sqrt (cLam sys L) * Wv ^ 2) = Real.sqrt (Real.sqrt (cLam sys L)) * Wv := by
      rw [Real.sqrt_mul (Real.sqrt_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have e3 : Real.sqrt (Real.sqrt (cLam sys L)) * Real.sqrt (Real.sqrt (cLam sys L)) =
        Real.sqrt (cLam sys L) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
    calc chC sys L k * FSLattice.CKato *
          (Real.sqrt (∑ q, lam (Pi.single (lead k) 1) (cidx n q) * ‖u.ofLp q‖ ^ 2) *
            Real.sqrt (∑ p, lam (Pi.single (lead k) 1) (cidx n p) * ‖v.ofLp p‖ ^ 2))
        ≤ chC sys L k * FSLattice.CKato *
          (Real.sqrt (Real.sqrt (cLam sys L) * Wu ^ 2) *
            Real.sqrt (Real.sqrt (cLam sys L) * Wv ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul (Real.sqrt_le_sqrt hu) (Real.sqrt_le_sqrt hv) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = chC sys L k * FSLattice.CKato * (Real.sqrt (Real.sqrt (cLam sys L)) *
            Real.sqrt (Real.sqrt (cLam sys L))) * Wu * Wv := by
          rw [e1, e2]
          ring
      _ = chC sys L k * FSLattice.CKato * Real.sqrt (cLam sys L) * Wu * Wv := by rw [e3]
  calc ‖⟪u, VN sys L n v⟫_ℂ‖ ≤ ∑ q, ∑ p, ‖u.ofLp q‖ * ‖wNK sys L n q p‖ * ‖v.ofLp p‖ := h1
    _ ≤ ∑ q, ∑ p, ‖u.ofLp q‖ * (∑ k, chMaj k (chC sys L k) (cidx n q) (cidx n p)) *
          ‖v.ofLp p‖ := by
        refine Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun p _ => ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (h2 q p) (norm_nonneg _))
          (norm_nonneg _)
    _ = ∑ k, ∑ q, ∑ p, ‖u.ofLp q‖ * chMaj k (chC sys L k) (cidx n q) (cidx n p) *
          ‖v.ofLp p‖ := by
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => ?_
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ k, chC sys L k * FSLattice.CKato * Real.sqrt (cLam sys L) * Wu * Wv :=
        Finset.sum_le_sum fun k _ => h3 k
    _ = CF sys L * Wu * Wv := by
        unfold CF
        rw [Finset.sum_mul, Finset.sum_mul]

/-- **eq:formW**: `‖E^{-1/4} W_N E^{-1/4}‖ ≤ C_F`. -/
theorem norm_formW_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (w : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4))
        (VN sys L n (FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) w))‖ ≤ CF sys L * ‖w‖ := by
  set x := FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4))
    (VN sys L n (FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) w)) with hx
  have hCF := CF_nonneg (sys := sys) hL
  have key : ‖x‖ ^ 2 ≤ CF sys L * ‖x‖ * ‖w‖ := by
    have e1 : ‖x‖ ^ 2 = ‖⟪x, x⟫_ℂ‖ := by
      rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
    have e2 : ⟪x, x⟫_ℂ = ⟪FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) x,
        VN sys L n (FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) w)⟫_ℂ := by
      rw [inner_wt_shift sys L n (1 / 4) x x]
      congr 1
      rw [hx, wt_wt_neg]
    rw [e1, e2]
    refine (form_VN_le hL H hKernel _ _).trans (le_of_eq ?_)
    rw [wt_wt_neg (1 / 4) x, wt_wt_neg (1 / 4) w]
  rcases (norm_nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hCF (norm_nonneg _)
  · have : ‖x‖ * ‖x‖ ≤ ‖x‖ * (CF sys L * ‖w‖) := by nlinarith
    exact le_of_mul_le_mul_left this hpos

/-- **eq:completionweighted** in the form of the manuscript: for every `u`,
`‖E^{-1/4} Σ₃^sp W_N u‖ + ‖E^{1/4} Σ₃^sp u‖ ≤ C_W (C_F + 1) ‖E^{1/4} u‖`. -/
theorem weighted_Sig3sp_E14 (hL : 0 < L) (hn : 2 ≤ n)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (u : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (Sig3sp sys L n (VN sys L n u))‖ +
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (Sig3sp sys L n u)‖ ≤
      CW sys L n * (CF sys L + 1) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) u‖ := by
  have hW := CW_nonneg (sys := sys) (n := n) hL
  have h1 := norm_wt_Sig3sp_le (sys := sys) hL hn (α := -(1 / 4)) (by norm_num) (by norm_num)
    (VN sys L n u)
  have h2 := norm_wt_Sig3sp_le (sys := sys) hL hn (α := 1 / 4) (by norm_num) (by norm_num) u
  have h3 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (VN sys L n u)‖ ≤
      CF sys L * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) u‖ := by
    have := norm_formW_le hL H hKernel (FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) u)
    rwa [wt_neg_wt] at this
  calc _ ≤ CW sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (VN sys L n u)‖ +
        CW sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) u‖ := add_le_add h1 h2
    _ ≤ CW sys L n * (CF sys L * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) u‖) +
        CW sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) u‖ := by gcongr
    _ = _ := by ring

end Cube

/-! ## The residual is self-adjoint -/

section Residual

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

omit [Fintype ν] in
lemma inner_Akin (u v : En eta n) : ⟪Akin sys L n u, v⟫_ℂ = ⟪u, Akin sys L n v⟫_ℂ := by
  simp only [Akin, toC, LinearMap.coe_toContinuousLinearMap',
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, FSKernel.dg_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [star_mul', Complex.star_def, Complex.conj_ofReal]
  ring

lemma inner_VN (u v : En eta n) : ⟪VN sys L n u, v⟫_ℂ = ⟪u, VN sys L n v⟫_ℂ := by
  simp only [VN, toC, LinearMap.coe_toContinuousLinearMap']
  exact finiteCoulombPotential_isSymmetric sys (coulombCellAmplitude L) n u v

include hL in
lemma inner_Z2b (u v : En eta n) : ⟪Z2b sys L n u, v⟫_ℂ = -⟪u, Z2b sys L n v⟫_ℂ := by
  simp only [Z2b, toC, LinearMap.coe_toContinuousLinearMap']
  exact inner_Sig2bb hL u v

lemma inner_H3first (u v : En eta n) :
    ⟪H3first sys hL hn H u, v⟫_ℂ = ⟪u, H3first sys hL hn H v⟫_ℂ := by
  have hS : ∀ x y : L2 eta, ⟪Sig sys L n hL hn x, y⟫_ℂ = -⟪x, Sig sys L n hL hn y⟫_ℂ :=
    fun x y => by
      rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_Sig, neg_apply, inner_neg_right]
  have hZ : ∀ x y : L2 eta, ⟪Zsym sys hL hn H x, y⟫_ℂ = ⟪x, Zsym sys hL hn H y⟫_ℂ :=
    fun x y => by rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_Zsym]
  have hsa : ∀ x y : L2 eta, ⟪FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) x, y⟫_ℂ =
      ⟪x, FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) y⟫_ℂ := by
    intro x y
    simp only [FSConj.cm, sub_apply, mul_apply_eq_comp, inner_sub_left, inner_sub_right]
    rw [hS, hZ, hZ, hS]
    ring
  simp only [H3first, smul_apply, ContinuousLinearMap.comp_apply,
    inner_smul_left, inner_smul_right]
  rw [inner_ext, hsa, ← inner_ext']
  congr 1
  rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

lemma inner_H3ret (u v : En eta n) :
    ⟪H3ret sys hL hn H u, v⟫_ℂ = ⟪u, H3ret sys hL hn H v⟫_ℂ := by
  simp only [H3ret, add_apply, inner_add_left, inner_add_right]
  rw [inner_H3first sys hL hn H]
  congr 1
  simp only [FSConj.cm, sub_apply, mul_apply_eq_comp, inner_sub_left, inner_sub_right]
  rw [inner_Z2b sys hL, inner_VN, inner_VN, inner_Z2b sys hL]
  ring

include hL hn hKernel in
/-- **`R₃^* = R₃`** (`comp:thm:completion`): the residual `R₃ = H₃^{res,sp} + H₃^mp` is
self-adjoint, since `R₃ = H₃^ret + [Σ₃^sp, A]` with both terms self-adjoint. -/
theorem inner_R3 (u v : En eta n) :
    ⟪(H3resSp sys L n + H3mp sys L n) u, v⟫_ℂ = ⟪u, (H3resSp sys L n + H3mp sys L n) v⟫_ℂ := by
  obtain ⟨hdec, hsplit, hskew, hcomm, -, -⟩ := same_pair_package sys hL hn H hKernel
  have hR : ∀ x, (H3resSp sys L n + H3mp sys L n) x = H3ret sys hL hn H x +
      (Sig3sp sys L n (Akin sys L n x) - Akin sys L n (Sig3sp sys L n x)) := by
    intro x
    have h1 := LinearMap.congr_fun hcomm x
    have h2 := LinearMap.congr_fun hdec x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.add_apply,
      ContinuousLinearMap.coe_coe] at h1 h2
    simp only [Akin, toC, LinearMap.coe_toContinuousLinearMap', LinearMap.add_apply]
    rw [h2]
    have h3 : Sig3sp sys L n (FSKernel.dg (fun q => (Asym sys L n q : ℂ)) x) -
        FSKernel.dg (fun q => (Asym sys L n q : ℂ)) (Sig3sp sys L n x) =
        -(H3sp sys L n x - H3resSp sys L n x) := h1
    rw [h3]
    abel
  rw [hR, hR, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_H3ret sys hL hn H, hskew, inner_Akin, inner_Akin, hskew]
  ring

end Residual


/-! ## The directional generator bounds as operator norms (eq:Sdirection) -/

section Sdirection

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

/-- **eq:Sdirection, first bound, as an operator norm**: for every complex matrix `κ` dominated
entrywise by `σ_j` (`S_j = R Σ_{b,j} Q` itself, or its absolute majorant) and every finite set `X`
of output configurations, `Σ_{S ∈ X} |Σ_P κ(S,P) v_P|² ≤ A_j² Σ_P |v_P|²`, i.e. `‖S_j‖ ≤ A_j`. -/
theorem norm_Sj_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (κ : Cf eta → Cfg eta n → ℂ)
    (hκ : ∀ S P, ‖κ S P‖ ≤ ‖lcp j (sigK sys L n) S (cidx n P)‖) (X : Finset (Cf eta))
    (v : Cfg eta n → ℂ) :
    ∑ S ∈ X, ‖∑ P, κ S P * v P‖ ^ 2 ≤ Asj sys L n j ^ 2 * ∑ P, ‖v P‖ ^ 2 := by
  have h := FSLattice.wschur X Finset.univ κ (fun _ => 1) (fun _ => 1) (fun _ _ => one_pos)
    (Asj_nonneg hL j)
    (fun S _ => by
      rw [mul_one]
      calc ∑ P : Cfg eta n, ‖κ S P‖ * 1 ≤ ∑ P : Cfg eta n, ‖lcp j (sigK sys L n) S (cidx n P)‖ :=
            Finset.sum_le_sum fun P _ => by rw [mul_one]; exact hκ S P
        _ = ∑ T ∈ cubeImg n, ‖lcp j (sigK sys L n) S T‖ :=
            sum_cube_eq (fun T => ‖lcp j (sigK sys L n) S T‖)
        _ ≤ Asj sys L n j := sum_norm_sig_row_le hL hn j S _)
    (fun P _ => by
      rw [mul_one]
      calc ∑ S ∈ X, ‖κ S P‖ * 1 ≤ ∑ S ∈ X, ‖lcp j (sigK sys L n) S (cidx n P)‖ :=
            Finset.sum_le_sum fun S _ => by rw [mul_one]; exact hκ S P
        _ ≤ Asj sys L n j := sum_norm_sig_col_le hL hn j _ X) v
  rwa [← sq] at h

/-- **eq:Sdirection, second bound, as an operator norm**: for `d · ℓ_j = 1` (`|d|₁ ≤ 2`) and every
matrix `κ` dominated entrywise by `σ_j`, `Σ_{S ∈ X} |Σ_P κ(S,P) Λ_d(P)⁻¹ v_P|² ≤ α_j A_j Σ_P |v_P|²`,
i.e. `‖S_j Λ_d⁻¹‖ ≤ (α_j A_j)^{1/2}`. -/
theorem norm_Sj_lam_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) {d : Fin eta → ℤ}
    (hdl : dl d j = 1) (hd1 : l1 d ≤ 2) (κ : Cf eta → Cfg eta n → ℂ)
    (hκ : ∀ S P, ‖κ S P‖ ≤ ‖lcp j (sigK sys L n) S (cidx n P)‖) (X : Finset (Cf eta))
    (v : Cfg eta n → ℂ) :
    ∑ S ∈ X, ‖∑ P, κ S P * ((lam d (cidx n P))⁻¹ : ℂ) * v P‖ ^ 2 ≤
      alS sys L n j * Asj sys L n j * ∑ P, ‖v P‖ ^ 2 := by
  have h := FSLattice.wschur X Finset.univ
    (fun S P => κ S P * ((lam d (cidx n P))⁻¹ : ℂ))
    (fun _ => 1) (fun P => (lam d (cidx n P))⁻¹) (fun P _ => inv_pos.mpr (lam_pos _ _))
    (alS_nonneg hL j)
    (fun S _ => by
      have e : ∀ P : Cfg eta n, ‖κ S P * ((lam d (cidx n P))⁻¹ : ℂ)‖ * (lam d (cidx n P))⁻¹ =
          ‖κ S P‖ / lam d (cidx n P) ^ 2 := by
        intro P
        have hp := lam_pos d (cidx n P)
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        field_simp
      rw [Finset.sum_congr rfl (fun P _ => e P), mul_one]
      calc ∑ P : Cfg eta n, ‖κ S P‖ / lam d (cidx n P) ^ 2
          ≤ ∑ P : Cfg eta n, ‖lcp j (sigK sys L n) S (cidx n P)‖ / lam d (cidx n P) ^ 2 :=
            Finset.sum_le_sum fun P _ => div_le_div_of_nonneg_right (hκ S P)
              (by have := lam_pos d (cidx n P); positivity)
        _ = ∑ T ∈ cubeImg n, ‖lcp j (sigK sys L n) S T‖ / lam d T ^ 2 :=
            sum_cube_eq (fun T => ‖lcp j (sigK sys L n) S T‖ / lam d T ^ 2)
        _ ≤ alS sys L n j := row_sig_lam hL hn j hdl hd1 S _ (fun T hT hne =>
              (cross_right_inP (mem_cubeImg_inP hT) (sig_ne_zero hne).2).2))
    (fun P _ => by
      have hp := lam_pos d (cidx n P)
      have e : ∑ S ∈ X, ‖κ S P * ((lam d (cidx n P))⁻¹ : ℂ)‖ * 1 =
          (lam d (cidx n P))⁻¹ * ∑ S ∈ X, ‖κ S P‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        ring
      rw [e, mul_comm (Asj sys L n j)]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hp.le)
      exact (Finset.sum_le_sum fun S _ => hκ S P).trans (sum_norm_sig_col_le hL hn j _ X)) v
  exact h

end Sdirection

end FSNormal

namespace FSAsymp

open FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ}

/-- **The orders in eq:Sdirection**: there is `C` with `A_j ≤ C K⁻¹` and `(α_j A_j)^{1/2} ≤ C K⁻²`
for every cutoff `n ≥ 1` (no logarithm), so `‖S_j‖ ≤ C K⁻¹` and `‖S_j Λ_d⁻¹‖ ≤ C K⁻²`. -/
theorem Sdirection_orders (hL : 0 < L) (j : Ch eta) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
    Asj sys L n j ≤ C / Kc L n ∧
      Real.sqrt (alS sys L n j * Asj sys L n j) ≤ C / Kc L n ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = chC sys L j / cgap sys (gF L) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [ha]; exact div_nonneg (chC_nonneg sys hL j) (cgap_pos sys (gF_pos hL).ne').le
  have hg := gL_pos hL
  refine ⟨a * (139 * gL L + 79 * gL L ^ 2), by positivity, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK : Kc L n = gL L * n := rfl
  have hK0 : 0 < Kc L n := by rw [hK]; positivity
  have hA : Asj sys L n j = a * (416 / 3) / n := by
    unfold Asj
    rw [← ha]
    ring
  have hal : alS sys L n j = a * (256 / 81) * (1 + 13 * n) / n ^ 4 := by
    unfold alS
    rw [← ha]
    ring
  constructor
  · rw [hA, hK, div_le_div_iff₀ hn0 (by positivity)]
    have h1 : (416 / 3 : ℝ) * gL L ≤ 139 * gL L + 79 * gL L ^ 2 := by
      nlinarith [sq_nonneg (gL L)]
    calc a * (416 / 3) * (gL L * n) = a * ((416 / 3) * gL L) * n := by ring
      _ ≤ a * (139 * gL L + 79 * gL L ^ 2) * n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 ha0) hn0.le
  · have hC0 : 0 ≤ a * (139 * gL L + 79 * gL L ^ 2) := by positivity
    have hprod : alS sys L n j * Asj sys L n j ≤
        (a * (139 * gL L + 79 * gL L ^ 2) / Kc L n ^ 2) ^ 2 := by
      have hbound : alS sys L n j * Asj sys L n j ≤ a ^ 2 * 6136 / n ^ 4 := by
        rw [hal, hA, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        have e : a * (256 / 81) * (1 + 13 * n) * (a * (416 / 3)) =
            a ^ 2 * (106496 / 243) * (1 + 13 * n) := by ring
        rw [e]
        have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
        have h1 : a ^ 2 * (106496 / 243) * (1 + 13 * n) ≤ a ^ 2 * 6136 * n := by
          nlinarith [mul_nonneg ha2 hn0.le, mul_nonneg ha2 (sub_nonneg.mpr hn1)]
        calc a ^ 2 * (106496 / 243) * (1 + 13 * (n : ℝ)) * (n : ℝ) ^ 4
            ≤ a ^ 2 * 6136 * n * n ^ 4 := mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = a ^ 2 * 6136 * (n ^ 4 * n) := by ring
      have eR : a ^ 2 * (139 * gL L + 79 * gL L ^ 2) ^ 2 / (gL L ^ 4 * n ^ 4) =
          (a * (139 * gL L + 79 * gL L ^ 2) / Kc L n ^ 2) ^ 2 := by
        rw [hK]; ring
      refine hbound.trans (le_of_le_of_eq ?_ eR)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have key : (6136 : ℝ) * gL L ^ 4 ≤ (139 * gL L + 79 * gL L ^ 2) ^ 2 := by
        nlinarith [pow_pos hg 3, pow_pos hg 2, pow_pos hg 4]
      calc a ^ 2 * 6136 * (gL L ^ 4 * n ^ 4) = (a ^ 2 * n ^ 4) * (6136 * gL L ^ 4) := by ring
        _ ≤ (a ^ 2 * n ^ 4) * (139 * gL L + 79 * gL L ^ 2) ^ 2 :=
            mul_le_mul_of_nonneg_left key (by positivity)
        _ = a ^ 2 * (139 * gL L + 79 * gL L ^ 2) ^ 2 * n ^ 4 := by ring
    calc Real.sqrt (alS sys L n j * Asj sys L n j)
        ≤ Real.sqrt ((a * (139 * gL L + 79 * gL L ^ 2) / Kc L n ^ 2) ^ 2) :=
          Real.sqrt_le_sqrt hprod
      _ = a * (139 * gL L + 79 * gL L ^ 2) / Kc L n ^ 2 := Real.sqrt_sq (by positivity)

/-- **`comp:thm:completion` in full.** There are `C ≥ 0`, `q` and `N₁` such that for every cutoff
`n ≥ N₁` the choice `Σ₃ = Σ₃^sp`, `R₃ = H₃^{res,sp} + H₃^mp` (eq:choice) satisfies
`[Σ₃, A] = -(H₃^ret - R₃)`, `Σ₃^* = -Σ₃`, `R₃^* = R₃`, `‖Σ₃‖ ≤ C log^q(2+K)/K³`
(eq:completionnorm), `‖E^{-1/4} Σ₃ W_N u‖ + ‖E^{1/4} Σ₃ u‖ ≤ C log^q(2+K)/K³ ‖E^{1/4} u‖` for every
`u` (eq:completionweighted, `E = 1 + A`), and `‖R₃ u‖ ≤ C log^q(2+K)/K³ B` for every good `u` of
budget `B` (eq:completionres). -/
theorem completion_full (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (heta : 0 < eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℕ, ∃ N₁ : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N₁ ≤ n →
      FSConj.cm (toC (Sig3sp sys L n)) (Akin sys L n) =
        -(H3ret sys hL hn H - toC (H3resSp sys L n + H3mp sys L n)) ∧
      toC (Sig3sp sys L n) ∈ skewAdjoint (En eta n →L[ℂ] En eta n) ∧
      IsSelfAdjoint (toC (H3resSp sys L n + H3mp sys L n)) ∧
      ‖toC (Sig3sp sys L n)‖ ≤ betaF L C q n ∧
      (∀ u : En eta n,
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (Sig3sp sys L n (VN sys L n u))‖ +
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (Sig3sp sys L n u)‖ ≤
        betaF L C q n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) u‖) ∧
      (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u →
        ‖(H3resSp sys L n + H3mp sys L n) u‖ ≤ betaF L C q n * M) := by
  obtain ⟨Ca, hCa, qa, Na, ha⟩ := exists_logK_bound hL 3
    ((pl_CS3 sys (L := L) heta).mono (by norm_num : (-3 : ℝ) ≤ -((3 : ℕ) : ℝ)))
  obtain ⟨Cb, hCb, qb, Nb, hb⟩ := exists_logK_bound hL 3
    (((pl_CW sys (L := L) heta).mul_const (CF sys L + 1)).mono
      (by norm_num : (-3 : ℝ) ≤ -((3 : ℕ) : ℝ)))
  obtain ⟨Cc, hCc, qc, Nc, hc⟩ := exists_logK_bound hL 3
    (((pl_CR3 sys (L := L) heta).add ((pl_kcCX sys (L := L) heta Hunit).add
      (pl_kcCY sys (L := L) Hunit))).mono (by norm_num : (-3 : ℝ) ≤ -((3 : ℕ) : ℝ)))
  have hg := gL_pos hL
  refine ⟨max Ca (max Cb Cc), le_max_of_le_left hCa, max qa (max qb qc),
    max (max Na (max Nb Nc)) ⌈2 / gL L⌉₊, fun n hn hN => ?_⟩
  have hNa : Na ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNb : Nb ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hN
  have hNc : Nc ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hN
  have hK2 : 2 ≤ Kc L n := by
    have h1 : 2 / gL L ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
    rw [div_le_iff₀ hg] at h1
    calc (2 : ℝ) ≤ n * gL L := h1
      _ = Kc L n := by rw [Kc, mul_comm]
  obtain ⟨hdec, -, hskew, hcomm, hS, hR⟩ := same_pair_package sys hL hn H hKernel
  have hza : CS3 sys L n ≤ betaF L (max Ca (max Cb Cc)) (max qa (max qb qc)) n :=
    (le_abs_self _).trans ((ha n hNa).trans
      (logK_mono hK2 hCa (le_max_left _ _) (le_max_left _ _) 3))
  have hzb : CW sys L n * (CF sys L + 1) ≤ betaF L (max Ca (max Cb Cc)) (max qa (max qb qc)) n :=
    (le_abs_self _).trans ((hb n hNb).trans
      (logK_mono hK2 hCb ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_left _ _).trans (le_max_right _ _)) 3))
  have hzc : CR3 sys L n + (kcCX sys L n Hunit + kcCY sys L n Hunit) ≤
      betaF L (max Ca (max Cb Cc)) (max qa (max qb qc)) n :=
    (le_abs_self _).trans ((hc n hNc).trans
      (logK_mono hK2 hCc ((le_max_right _ _).trans (le_max_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _)) 3))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the homological equation
    ext1 u
    have h1 := LinearMap.congr_fun hcomm u
    have h2 := LinearMap.congr_fun hdec u
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.add_apply,
      ContinuousLinearMap.coe_coe] at h1 h2
    simp only [FSConj.cm, Akin, toC, sub_apply, mul_apply_eq_comp, neg_apply,
      LinearMap.coe_toContinuousLinearMap', LinearMap.add_apply]
    rw [h1, h2]
    abel
  · -- skew-adjointness
    refine mem_skewAdjoint_of_inner _ fun u v => ?_
    simp only [toC, LinearMap.coe_toContinuousLinearMap']
    exact hskew u v
  · -- self-adjointness of the residual
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro u v
    simp only [toC, LinearMap.coe_toContinuousLinearMap]
    exact inner_R3 sys hL hn H hKernel u v
  · -- `‖Σ₃‖`
    refine le_trans (ContinuousLinearMap.opNorm_le_bound _ (CS3_nonneg (sys := sys) (n := n) hL)
      fun u => ?_) hza
    simp only [toC, LinearMap.coe_toContinuousLinearMap']
    exact hS u
  · -- the weighted bound for every state
    intro u
    exact (weighted_Sig3sp_E14 hL hn H hKernel u).trans
      (mul_le_mul_of_nonneg_right hzb (norm_nonneg _))
  · -- the residual bound
    intro M u hu
    have hM := good_nonneg hu
    have hw1 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ≤ M := by
      have := hu.1
      have := norm_nonneg u
      linarith
    have h1 := hR M u hu
    have h2 := norm_H3mp_le (sys := sys) hL hn Hunit hPeriodic u
    have hX := kcCX_nonneg (sys := sys) (n := n) hL Hunit
    have hY := kcCY_nonneg sys (n := n) hL Hunit
    rw [LinearMap.add_apply]
    calc ‖H3resSp sys L n u + H3mp sys L n u‖ ≤ ‖H3resSp sys L n u‖ + ‖H3mp sys L n u‖ :=
          norm_add_le _ _
      _ ≤ CR3 sys L n * M + (kcCX sys L n Hunit + kcCY sys L n Hunit) * M :=
          add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hw1 (by positivity)))
      _ = (CR3 sys L n + (kcCX sys L n Hunit + kcCY sys L n Hunit)) * M := by ring
      _ ≤ betaF L (max Ca (max Cb Cc)) (max qa (max qb qc)) n * M :=
          mul_le_mul_of_nonneg_right hzc hM

end FSAsymp
