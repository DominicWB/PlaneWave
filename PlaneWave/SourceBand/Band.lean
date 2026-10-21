import PlaneWave.SourceBand.ThinShellCounts

/-!
# Source band block, part 2: `lem:band`

Physical shells of a register `a` are written in lattice units: `S = {q : sh (q a)}` with
`sh = shE (λ/g) (ρ/g)` (Euclidean, `λ ≤ g|k_a| < λ + ρ`) or `sh = shC (λ/g) (ρ/g)` (cube,
`λ ≤ g‖k_a‖_∞ < λ + ρ`).

* Shell counts: `shE_count` (`≤ 750 Λ² max(R, 1)`), `shC_count` (`≤ 2250 Λ² max(R, 1)`), for
  `Λ ≥ 1`, `0 ≤ R ≤ Λ` (lattice units); `tsum_shell_shift_le` (the count as a series over a fibre).
* `fibre_weight_two_le`: fibre sums of `(1 + |p|²)^{-2}` are at most `53`.
* **`far_band_finite`** (the far-input step of `lem:band`): on a finite input set with
  `|p_a| ≤ r₀` and outputs in a shell beyond `r₁ > r₀`,
  `Σ_q 1_S(q) |Σ_p x_p w(q,p)|² ≤ (c_tot/(r₁-r₀)²)² · 53 N₀ · Σ_p (1+|p|²)² |x_p|²`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal FSFlux

namespace FSBand

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Shell counts -/

lemma lsq_eq_nsq (y : Lattice3) : lsq y = nsq y := rfl

lemma lsq_le_three_supn_sq (y : Lattice3) : lsq y ≤ 3 * supn y ^ 2 := by
  have h0 := abs_le_supn y 0
  have h1 := abs_le_supn y 1
  have h2 := abs_le_supn y 2
  have hs : 0 ≤ supn y := (abs_nonneg _).trans h0
  have e0 : (y 0 : ℝ) ^ 2 ≤ supn y ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have e1 : (y 1 : ℝ) ^ 2 ≤ supn y ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 : (y 2 : ℝ) ^ 2 ≤ supn y ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  unfold lsq; linarith

lemma supn_sq_le_lsq (y : Lattice3) : supn y ^ 2 ≤ lsq y := by
  obtain ⟨i, hi⟩ := exists_supn_coord y
  rw [← hi, sq_abs]
  have : (y i : ℝ) ^ 2 ≤ lsq y := by
    unfold lsq
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (y 0 : ℝ), sq_nonneg (y 1 : ℝ), sq_nonneg (y 2 : ℝ)]
  exact this

/-- **The Euclidean shell count**: `Λ ≤ |y| < Λ + R` holds for at most `750 Λ² max(R, 1)` lattice
points (`Λ ≥ 1`, `0 ≤ R ≤ Λ`). -/
lemma shE_count {Λ R : ℝ} (hΛ : 1 ≤ Λ) (hR : 0 ≤ R) (hRΛ : R ≤ Λ) (T : Finset Lattice3)
    (hT : ∀ y ∈ T, shE Λ R y) : (T.card : ℝ) ≤ 750 * Λ ^ 2 * max R 1 := by
  have hm1 : (1 : ℝ) ≤ max R 1 := le_max_right _ _
  have hmΛ : max R 1 ≤ Λ := max_le hRΛ hΛ
  have h := thin_count_le 0 (lam := Λ) (ρ := max R 1) (ρ' := Λ) hm1 hmΛ hΛ T (fun θ hθ => by
    obtain ⟨h1, h2⟩ := hT θ hθ
    rw [zero_add]
    have hl := lsq_nonneg θ
    refine ⟨?_, h1, ?_⟩
    · have : (Λ + R) ^ 2 ≤ (2 * Λ) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      linarith
    · have : (Λ + R) ^ 2 ≤ (Λ + max R 1) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith [le_max_left R 1]) 2
      linarith)
  calc (T.card : ℝ) ≤ 750 * Λ ^ 2 * min (max R 1) Λ := h
    _ ≤ 750 * Λ ^ 2 * max R 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)

/-- **The cube shell count**: `Λ ≤ ‖y‖_∞ < Λ + R` holds for at most `2250 Λ² max(R, 1)` lattice
points (`Λ ≥ 1`, `0 ≤ R ≤ Λ`). -/
lemma shC_count {Λ R : ℝ} (hΛ : 1 ≤ Λ) (_hR : 0 ≤ R) (hRΛ : R ≤ Λ) (T : Finset Lattice3)
    (hT : ∀ y ∈ T, shC Λ R y) : (T.card : ℝ) ≤ 2250 * Λ ^ 2 * max R 1 := by
  have hm1 : (1 : ℝ) ≤ max R 1 := le_max_right _ _
  have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h3Λ : (1 : ℝ) ≤ Real.sqrt 3 * Λ := by nlinarith
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h := thin_count_cube_le 0 (lam := Λ) (ρ := max R 1) (ρ' := Real.sqrt 3 * Λ) hm1 h3Λ T
    (fun θ hθ => by
      obtain ⟨h1, h2⟩ := hT θ hθ
      rw [zero_add]
      refine ⟨?_, h1, by linarith [le_max_left R 1]⟩
      have hs := lsq_le_three_supn_sq θ
      have hs0 : 0 ≤ supn θ := (abs_nonneg _).trans (abs_le_supn θ 0)
      have : supn θ ^ 2 ≤ (2 * Λ) ^ 2 := pow_le_pow_left₀ hs0 (by linarith) 2
      have e : (2 * (Real.sqrt 3 * Λ)) ^ 2 = 3 * (2 * Λ) ^ 2 := by
        rw [mul_pow, mul_pow, hs3]; ring
      rw [e]; linarith)
  have e : (Real.sqrt 3 * Λ) ^ 2 = 3 * Λ ^ 2 := by rw [mul_pow, hs3]
  calc (T.card : ℝ) ≤ 750 * (Real.sqrt 3 * Λ) ^ 2 * min (max R 1) (Real.sqrt 3 * Λ) := h
    _ ≤ 750 * (Real.sqrt 3 * Λ) ^ 2 * max R 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    _ = 2250 * Λ ^ 2 * max R 1 := by rw [e]; ring

/-- A predicate with a uniform bound on its finite subsets holds on a finite set. -/
lemma finite_of_count {sh : Lattice3 → Prop} {N₀ : ℝ}
    (hcnt : ∀ T : Finset Lattice3, (∀ y ∈ T, sh y) → (T.card : ℝ) ≤ N₀) : {y | sh y}.Finite := by
  by_contra hinf
  obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊N₀⌋₊ + 1)
  have h := hcnt t (fun y hy => ht hy)
  rw [hcard] at h
  push_cast at h
  have := Nat.lt_floor_add_one N₀
  linarith

open Classical in
/-- The count of a shell as a series: `Σ_y 1_sh(y) ≤ N₀`. -/
lemma tsum_shell_le {sh : Lattice3 → Prop} {N₀ : ℝ}
    (hcnt : ∀ T : Finset Lattice3, (∀ y ∈ T, sh y) → (T.card : ℝ) ≤ N₀) :
    Summable (fun y : Lattice3 => if sh y then (1 : ℝ) else 0) ∧
      ∑' y : Lattice3, (if sh y then (1 : ℝ) else 0) ≤ N₀ := by
  set Sf := (finite_of_count hcnt).toFinset
  have hmem : ∀ y, y ∈ Sf ↔ sh y := fun y => Set.Finite.mem_toFinset _
  have hsupp : ∀ y ∉ Sf, (if sh y then (1 : ℝ) else 0) = 0 := by
    intro y hy
    rw [if_neg]; intro h; exact hy ((hmem y).mpr h)
  refine ⟨summable_of_ne_finset_zero hsupp, ?_⟩
  rw [tsum_eq_sum hsupp]
  have e : ∑ y ∈ Sf, (if sh y then (1 : ℝ) else 0) = Sf.card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [if_pos ((hmem y).mp hy)]; simp
  rw [e]
  exact hcnt Sf fun y hy => (hmem y).mp hy

open Classical in
/-- The count of a shell along a fibre `ν ↦ c ± ν`. -/
lemma tsum_shell_shift_le {sh : Lattice3 → Prop} {N₀ : ℝ}
    (hcnt : ∀ T : Finset Lattice3, (∀ y ∈ T, sh y) → (T.card : ℝ) ≤ N₀) (c : Lattice3)
    (σ : Lattice3 → Lattice3) (hσ : σ = id ∨ σ = Neg.neg) :
    Summable (fun ν : Lattice3 => if sh (c + σ ν) then (1 : ℝ) else 0) ∧
      ∑' ν : Lattice3, (if sh (c + σ ν) then (1 : ℝ) else 0) ≤ N₀ := by
  obtain ⟨hs, ht⟩ := tsum_shell_le hcnt
  obtain ⟨e, he⟩ : ∃ e : Lattice3 ≃ Lattice3, ∀ ν, e ν = c + σ ν := by
    rcases hσ with rfl | rfl
    · exact ⟨Equiv.addLeft c, fun ν => rfl⟩
    · exact ⟨(Equiv.neg Lattice3).trans (Equiv.addLeft c), fun ν => rfl⟩
  have hf : (fun ν : Lattice3 => if sh (c + σ ν) then (1 : ℝ) else 0) =
      (fun y : Lattice3 => if sh y then (1 : ℝ) else 0) ∘ e := by
    funext ν; simp only [Function.comp, he]
  rw [hf]
  refine ⟨(e.summable_iff).mpr hs, ?_⟩
  calc ∑' ν, ((fun y : Lattice3 => if sh y then (1 : ℝ) else 0) ∘ e) ν =
        ∑' y : Lattice3, (if sh y then (1 : ℝ) else 0) :=
        e.tsum_eq (fun y : Lattice3 => if sh y then (1 : ℝ) else 0)
    _ ≤ N₀ := ht

/-! ## Fibre weights -/

open Classical in
/-- The fibre sums of `(1 + |p|²)^{-2}` over any finite set are at most `53`. -/
lemma fibre_weight_two_le (F : Finset (Cf eta)) (j : Ch eta) (p : Cf eta) :
    ∑ p' ∈ F.filter (fun p' => OnCh j p' p), ((1 + lsqC p') ^ 2)⁻¹ ≤ 53 := by
  have hinj : Set.InjOn (fun p' : Cf eta => p' (lead j)) (F.filter fun p' => OnCh j p' p) := by
    intro x hx y hy hxy
    exact lead_inj_on_fibre (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  have hterm : ∀ p' ∈ F.filter (fun p' => OnCh j p' p),
      ((1 + lsqC p') ^ 2)⁻¹ ≤ (1 + lsq (p' (lead j))) ^ (-(2 : ℝ)) := by
    intro p' _
    have h0 := lsq_nonneg (p' (lead j))
    have hle : lsq (p' (lead j)) ≤ lsqC p' := by
      unfold lsqC
      exact Finset.single_le_sum (f := fun c => nsq (p' c)) (fun _ _ => nsq_nonneg _)
        (Finset.mem_univ (lead j))
    rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  calc ∑ p' ∈ F.filter (fun p' => OnCh j p' p), ((1 + lsqC p') ^ 2)⁻¹
      ≤ ∑ p' ∈ F.filter (fun p' => OnCh j p' p), (1 + lsq (p' (lead j))) ^ (-(2 : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = ∑ μ ∈ (F.filter (fun p' => OnCh j p' p)).image (fun p' => p' (lead j)),
          (1 + lsq μ) ^ (-(2 : ℝ)) :=
        (Finset.sum_image (f := fun μ => (1 + lsq μ) ^ (-(2 : ℝ))) hinj).symm
    _ ≤ 1 + 26 * (1 + 1 / (2 * 2 - 3)) := sum_weight_le (by norm_num) _
    _ = 53 := by norm_num

/-- Weighted Cauchy–Schwarz on a finite sum: `(Σ b G)² ≤ (Σ b)(Σ b G²)` for `b ≥ 0`. -/
lemma sq_sum_le_weighted {ι : Type*} (s : Finset ι) (b G : ι → ℝ) (hb : ∀ i, 0 ≤ b i) :
    (∑ i ∈ s, b i * G i) ^ 2 ≤ (∑ i ∈ s, b i) * ∑ i ∈ s, b i * G i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (b i))
    (fun i => Real.sqrt (b i) * G i)
  have e1 : ∀ i, Real.sqrt (b i) * (Real.sqrt (b i) * G i) = b i * G i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (hb i)]
  have e2 : ∀ i, Real.sqrt (b i) ^ 2 = b i := fun i => Real.sq_sqrt (hb i)
  have e3 : ∀ i, (Real.sqrt (b i) * G i) ^ 2 = b i * G i ^ 2 := fun i => by rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  exact h

/-! ## The far-input bound -/

section Far

variable (sys : CoulombSystem eta ν) (L : ℝ)

/-- The total channel constant `c_tot = Σ_j c_j`. -/
noncomputable def ctot : ℝ := ∑ j : Ch eta, chC sys L j

lemma ctot_nonneg {L : ℝ} (hL : 0 < L) : 0 ≤ ctot sys L :=
  Finset.sum_nonneg fun j _ => chC_nonneg sys hL j

variable {sys L}

/-- A hop of channel `j` between a configuration with `|p_a| ≤ r₀` and one with `|q_a| ≥ r₁`
moves `a` and has length at least `r₁ - r₀`. -/
lemma hop_far {j : Ch eta} {q p : Cf eta} (hon : OnCh j q p) (a : Fin eta) {r₀ r₁ : ℝ}
    (hr₀ : 0 ≤ r₀) (hr : r₀ < r₁) (hq : r₁ ^ 2 ≤ nsq (q a)) (hp : nsq (p a) ≤ r₀ ^ 2) :
    (r₁ - r₀) ^ 2 ≤ latticeNormSq (q (lead j) - p (lead j)) := by
  set x := q (lead j) - p (lead j)
  have hqe : q = p + tr j x := hon
  have hqa : q a = p a + tr j x a := by rw [hqe]; rfl
  by_cases hm : a ∈ moved j
  · have hn : nsq (tr j x a) = nsq x := by
      rcases tr_apply_moved j x hm with h | h
      · rw [h]
      · rw [h, nsq_neg]
    have hd : q a - p a = tr j x a := by rw [hqa]; abel
    -- `|q_a| ≤ |p_a| + |q_a - p_a|`
    have htri := rho_le_add_rho_sub (q a) (p a)
    have hrq : r₁ ≤ rho (q a) := by
      unfold rho
      exact Real.le_sqrt_of_sq_le (by rw [lsq_eq_nsq]; exact hq)
    have hrp : rho (p a) ≤ r₀ := by
      unfold rho
      rw [Real.sqrt_le_left (by linarith)]
      rw [lsq_eq_nsq]; exact hp
    have hrd : r₁ - r₀ ≤ rho (q a - p a) := by linarith
    have h0 : 0 ≤ r₁ - r₀ := by linarith
    have hsq : (r₁ - r₀) ^ 2 ≤ rho (q a - p a) ^ 2 := pow_le_pow_left₀ h0 hrd 2
    rw [rho_sq, hd, lsq_eq_nsq, hn] at hsq
    exact hsq
  · exfalso
    have h0 : tr j x a = 0 := tr_apply_not_moved j x hm
    rw [h0, add_zero] at hqa
    rw [hqa] at hq
    have : r₀ ^ 2 < r₁ ^ 2 := pow_lt_pow_left₀ hr hr₀ two_ne_zero
    linarith

open Classical in
/-- **The far-input bound of `lem:band`** on a finite input set (lattice units). -/
theorem far_band_finite (hL : 0 < L) (a : Fin eta) (sh : Lattice3 → Prop) {N₀ r₀ r₁ : ℝ}
    (hN₀ : 0 ≤ N₀) (hr₀ : 0 ≤ r₀) (hr : r₀ < r₁)
    (hsh : ∀ y, sh y → r₁ ^ 2 ≤ nsq y)
    (hcnt : ∀ T : Finset Lattice3, (∀ y ∈ T, sh y) → (T.card : ℝ) ≤ N₀)
    (F : Finset (Cf eta)) (hF : ∀ p ∈ F, nsq (p a) ≤ r₀ ^ 2) (x : Cf eta → ℂ) :
    Summable (fun q => if sh (q a) then ‖∑ p ∈ F, x p * potKernel sys L q p‖ ^ 2 else 0) ∧
    ∑' q, (if sh (q a) then ‖∑ p ∈ F, x p * potKernel sys L q p‖ ^ 2 else 0) ≤
      (ctot sys L / (r₁ - r₀) ^ 2) ^ 2 * (53 * N₀) * ∑ p ∈ F, (1 + lsqC p) ^ 2 * ‖x p‖ ^ 2 := by
  set d := (r₁ - r₀) ^ 2 with hd
  have hd0 : 0 < d := by have : 0 < r₁ - r₀ := by linarith
                         positivity
  set b : Ch eta → ℝ := fun j => chC sys L j / d
  have hb : ∀ j, 0 ≤ b j := fun j => div_nonneg (chC_nonneg sys hL j) hd0.le
  set κ : Ch eta → Cf eta → Cf eta → ℝ := fun j q p => if OnCh j q p then 1 else 0
  have hκ0 : ∀ j q p, 0 ≤ κ j q p := fun j q p => by simp only [κ]; split_ifs <;> norm_num
  set w : Cf eta → ℝ := fun q => if sh (q a) then 1 else 0
  have hw0 : ∀ q, 0 ≤ w q := fun q => by simp only [w]; split_ifs <;> norm_num
  set G : Ch eta → Cf eta → ℝ := fun j q => ∑ p ∈ F, ‖x p‖ * κ j q p
  set Sx := ∑ p ∈ F, (1 + lsqC p) ^ 2 * ‖x p‖ ^ 2
  -- the fibre Gram bound, channel by channel
  have hgram : ∀ j, (Summable fun q => w q * G j q ^ 2) ∧
      ∑' q, w q * G j q ^ 2 ≤ N₀ * 53 * Sx := by
    intro j
    have hcs : ∀ p ∈ F, Summable fun q => w q * κ j q p ^ 2 := by
      intro p hp
      have e : (fun q => w q * κ j q p ^ 2) = fun q => if OnCh j q p then w q else 0 := by
        funext q; simp only [κ]; split_ifs <;> simp
      rw [e, summable_col_iff]
      by_cases hm : a ∈ moved j
      · obtain ⟨σ, hσ, htr⟩ : ∃ σ : Lattice3 → Lattice3, (σ = id ∨ σ = Neg.neg) ∧
            ∀ y, tr j y a = σ y := by
          rcases tr_moved_uniform hm with h | h
          · exact ⟨id, Or.inl rfl, fun y => h y⟩
          · exact ⟨Neg.neg, Or.inr rfl, fun y => h y⟩
        refine (tsum_shell_shift_le hcnt (p a) σ hσ).1.congr fun y => ?_
        simp only [w, Pi.add_apply, htr]
      · have hz : ∀ y : Lattice3, w (p + tr j y) = 0 := by
          intro y
          simp only [w, Pi.add_apply, tr_apply_not_moved j y hm, add_zero]
          rw [if_neg]
          intro hs
          have h1 := hsh _ hs
          have h2 := hF p hp
          have : r₀ ^ 2 < r₁ ^ 2 := pow_lt_pow_left₀ hr hr₀ two_ne_zero
          linarith
        simp only [hz]
        exact summable_zero
    have hcol : ∀ p ∈ F, ∑' q, w q * κ j q p ^ 2 ≤ N₀ := by
      intro p hp
      have e : (fun q => w q * κ j q p ^ 2) = fun q => if OnCh j q p then w q else 0 := by
        funext q; simp only [κ]; split_ifs <;> simp
      rw [e, tsum_col]
      by_cases hm : a ∈ moved j
      · obtain ⟨σ, hσ, htr⟩ : ∃ σ : Lattice3 → Lattice3, (σ = id ∨ σ = Neg.neg) ∧
            ∀ y, tr j y a = σ y := by
          rcases tr_moved_uniform hm with h | h
          · exact ⟨id, Or.inl rfl, fun y => h y⟩
          · exact ⟨Neg.neg, Or.inr rfl, fun y => h y⟩
        refine le_of_eq_of_le (tsum_congr fun y => ?_) (tsum_shell_shift_le hcnt (p a) σ hσ).2
        simp only [w, Pi.add_apply, htr]
      · have hz : ∀ y : Lattice3, w (p + tr j y) = 0 := by
          intro y
          simp only [w, Pi.add_apply, tr_apply_not_moved j y hm, add_zero]
          rw [if_neg]
          intro hs
          have h1 := hsh _ hs
          have h2 := hF p hp
          have : r₀ ^ 2 < r₁ ^ 2 := pow_lt_pow_left₀ hr hr₀ two_ne_zero
          linarith
        simp only [hz, tsum_zero]
        exact hN₀
    have h := fibre_gram F (κ j) (hκ0 j) w hw0 (fun p p' => OnCh j p' p)
      (fun p p' h => onCh_symm h)
      (fun q p _ p' _ h1 h2 => by
        simp only [κ, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h1 h2
        exact onCh_trans h1 h2)
      hcs hcol (fun p => (1 + lsqC p) ^ 2) (fun p => by have := lsqC_nonneg p; positivity)
      (N := 53) (fun p _ => fibre_weight_two_le F j p) (fun p => ‖x p‖) (fun p => norm_nonneg _)
    exact h
  -- the pointwise bound
  have hpt : ∀ q, sh (q a) → ‖∑ p ∈ F, x p * potKernel sys L q p‖ ≤ ∑ j, b j * G j q := by
    intro q hq
    have hq2 := hsh _ hq
    have hK : ∀ p ∈ F, ‖potKernel sys L q p‖ ≤ ∑ j, b j * κ j q p := by
      intro p hp
      refine (norm_potKernel_le sys hL q p).trans ?_
      unfold potMaj
      refine Finset.sum_le_sum fun j _ => ?_
      unfold chMaj
      simp only [κ, b]
      split_ifs with hon
      · have hfar := hop_far hon a hr₀ hr hq2 (hF p hp)
        rw [mul_one]
        exact div_le_div_of_nonneg_left (chC_nonneg sys hL j) hd0 hfar
      · simp
    calc ‖∑ p ∈ F, x p * potKernel sys L q p‖
        ≤ ∑ p ∈ F, ‖x p‖ * ‖potKernel sys L q p‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun p _ => norm_mul _ _
      _ ≤ ∑ p ∈ F, ‖x p‖ * ∑ j, b j * κ j q p :=
          Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hK p hp) (norm_nonneg _)
      _ = ∑ j, b j * G j q := by
          simp only [G, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => by ring
  -- the majorant
  have hmaj : ∀ q, (if sh (q a) then ‖∑ p ∈ F, x p * potKernel sys L q p‖ ^ 2 else 0) ≤
      (∑ j, b j) * ∑ j, b j * (w q * G j q ^ 2) := by
    intro q
    by_cases hq : sh (q a)
    · rw [if_pos hq]
      have hw1 : w q = 1 := by simp only [w]; rw [if_pos hq]
      have hG0 : 0 ≤ ∑ j, b j * G j q := Finset.sum_nonneg fun j _ =>
        mul_nonneg (hb j) (Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (hκ0 j q p))
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hpt q hq) 2
      have h2 := sq_sum_le_weighted Finset.univ b (fun j => G j q) hb
      simp only [hw1, one_mul]
      exact h1.trans h2
    · rw [if_neg hq]
      have hw1 : w q = 0 := by simp only [w]; rw [if_neg hq]
      simp [hw1]
  have hsum_maj : Summable fun q => (∑ j, b j) * ∑ j, b j * (w q * G j q ^ 2) :=
    (summable_sum fun j _ => ((hgram j).1.mul_left (b j))).mul_left _
  have hLHS : Summable (fun q => if sh (q a) then ‖∑ p ∈ F, x p * potKernel sys L q p‖ ^ 2 else 0) :=
    hsum_maj.of_nonneg_of_le (fun q => by split_ifs <;> positivity) hmaj
  refine ⟨hLHS, ?_⟩
  have hSx : 0 ≤ Sx := Finset.sum_nonneg fun p _ => by have := lsqC_nonneg p; positivity
  have hbsum : ∑ j, b j = ctot sys L / d := by
    simp only [b, ctot]; rw [Finset.sum_div]
  calc ∑' q, (if sh (q a) then ‖∑ p ∈ F, x p * potKernel sys L q p‖ ^ 2 else 0)
      ≤ ∑' q, (∑ j, b j) * ∑ j, b j * (w q * G j q ^ 2) := hLHS.tsum_le_tsum hmaj hsum_maj
    _ = (∑ j, b j) * ∑ j, b j * ∑' q, w q * G j q ^ 2 := by
        rw [tsum_mul_left, Summable.tsum_finsetSum (fun j _ => (hgram j).1.mul_left (b j))]
        congr 1
        refine Finset.sum_congr rfl fun j _ => tsum_mul_left
    _ ≤ (∑ j, b j) * ∑ j, b j * (N₀ * 53 * Sx) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hgram j).2 (hb j)) (Finset.sum_nonneg fun j _ => hb j)
    _ = (ctot sys L / d) ^ 2 * (53 * N₀) * Sx := by
        rw [← Finset.sum_mul, hbsum]; ring

end Far

/-! ## Register-shell masks on `ℓ²` -/

section Mask

open Classical in
/-- The mask `1_S` of the configurations whose register `a` lies in the lattice set `sh`. -/
noncomputable def shMask (a : Fin eta) (sh : Lattice3 → Prop) : L2 eta →L[ℂ] L2 eta :=
  diagCLM (fun q => if sh (q a) then (1 : ℂ) else 0) 1 zero_le_one (fun q => by split_ifs <;> simp)

open Classical in
lemma shMask_apply (a : Fin eta) (sh : Lattice3 → Prop) (x : L2 eta) (q : Cf eta) :
    shMask a sh x q = (if sh (q a) then (1 : ℂ) else 0) * x q := rfl

lemma norm_shMask_le (a : Fin eta) (sh : Lattice3 → Prop) (x : L2 eta) : ‖shMask a sh x‖ ≤ ‖x‖ := by
  have := l2_norm_le_of_le (shMask a sh x) x zero_le_one fun q => by
    rw [shMask_apply, one_mul]; split_ifs <;> simp
  rwa [one_mul] at this

open Classical in
lemma norm_shMask_sq (a : Fin eta) (sh : Lattice3 → Prop) (x : L2 eta) :
    ‖shMask a sh x‖ ^ 2 = ∑' q, (if sh (q a) then ‖x q‖ ^ 2 else 0) := by
  rw [l2_norm_sq]
  refine tsum_congr fun q => ?_
  rw [shMask_apply]; split_ifs <;> simp

/-- A shell beyond the threshold `l` (physical units) is dominated by the tail mask. -/
lemma norm_shMask_le_tail {g l : ℝ} (hg : 0 < g) (a : Fin eta)
    (sh : Lattice3 → Prop) (hsh : ∀ y, sh y → (l / g) ^ 2 < nsq y) (x : L2 eta) :
    ‖shMask a sh x‖ ≤ ‖tailMask g l a x‖ := by
  have := l2_norm_le_of_le (shMask a sh x) (tailMask g l a x) zero_le_one fun q => by
    rw [shMask_apply, tailMask_apply, one_mul]
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso; apply h2
      have h3 := hsh _ h1
      have h4 : l / g < Real.sqrt (latticeNormSq (q a)) :=
        Real.lt_sqrt_of_sq_lt (by rw [← nsq_eq_latticeNormSq]; exact h3)
      rw [div_lt_iff₀ hg] at h4
      linarith
    · simp
    · simp
  rwa [one_mul] at this

omit [Fintype ν] in
lemma shMask_add_kin_apply (sys : CoulombSystem eta ν) (L : ℝ) (w : MolecularFourierH2 eta)
    (q : Cf eta) :
    (Sm eta L w + coulombFourierKineticH2 sys (gF L) w) q =
      ((1 + Ek sys L q : ℝ) : ℂ) * Sm eta L w q := by
  rw [lp.coeFn_add, Pi.add_apply, kinetic_apply']
  push_cast; ring

omit [Fintype ν] in
/-- **`ℰ ≥ λ²/(2m̄)` on a shell beyond `λ`**: `‖1_S û‖ ≤ (2m̄/λ²) ‖1_S ℰ û‖`. -/
lemma shell_state_le (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {lam : ℝ} (hlam : 0 < lam)
    (a : Fin eta) (sh : Lattice3 → Prop) (hsh : ∀ y, sh y → (lam / gF L) ^ 2 ≤ nsq y)
    (w : MolecularFourierH2 eta) :
    ‖shMask a sh (Sm eta L w)‖ ≤
      2 * sys.maxMass / lam ^ 2 * ‖shMask a sh (Sm eta L w + coulombFourierKineticH2 sys (gF L) w)‖ := by
  have hg := gF_pos hL
  have hm := sys.one_le_maxMass
  refine l2_norm_le_of_le _ _ (by positivity) fun q => ?_
  rw [shMask_apply, shMask_apply, shMask_add_kin_apply]
  split_ifs with h
  · have hq := hsh _ h
    have hE0 : 0 ≤ Ek sys L q := by
      rw [Ek, E]
      exact Finset.sum_nonneg fun c _ => by
        have := sys.mass_pos c; have := nsq_nonneg (q c); positivity
    have hEa : gF L ^ 2 / (2 * sys.mass a) * nsq (q a) ≤ Ek sys L q := by
      rw [Ek, E]
      exact Finset.single_le_sum (f := fun c => gF L ^ 2 / (2 * sys.mass c) * nsq (q c))
        (fun c _ => by have := sys.mass_pos c; have := nsq_nonneg (q c); positivity)
        (Finset.mem_univ a)
    have hma := sys.mass_pos a
    have hmam : sys.mass a ≤ sys.maxMass := sys.mass_le_maxMass a
    have hkey : 1 ≤ 2 * sys.maxMass / lam ^ 2 * (1 + Ek sys L q) := by
      have h1 : lam ^ 2 / (2 * sys.maxMass) ≤ Ek sys L q := by
        refine le_trans ?_ hEa
        have e : lam ^ 2 = gF L ^ 2 * (lam / gF L) ^ 2 := by field_simp
        rw [e]
        calc gF L ^ 2 * (lam / gF L) ^ 2 / (2 * sys.maxMass)
            ≤ gF L ^ 2 * (lam / gF L) ^ 2 / (2 * sys.mass a) := by
              apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
          _ ≤ gF L ^ 2 / (2 * sys.mass a) * nsq (q a) := by
              rw [div_mul_eq_mul_div]
              apply div_le_div_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hq (by positivity)
      have h2 : 1 ≤ 2 * sys.maxMass / lam ^ 2 * Ek sys L q := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        rw [div_le_iff₀ (by positivity)] at h1
        linarith
      nlinarith [show 0 ≤ 2 * sys.maxMass / lam ^ 2 by positivity]
    rw [one_mul, one_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), ← mul_assoc]
    calc ‖Sm eta L w q‖ = 1 * ‖Sm eta L w q‖ := (one_mul _).symm
      _ ≤ 2 * sys.maxMass / lam ^ 2 * (1 + Ek sys L q) * ‖Sm eta L w q‖ :=
          mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
  · simp

lemma stateMap_tailMask (L : ℝ) (l : ℝ) (a : Fin eta) (w : MolecularFourierH2 eta) :
    Sm eta L (tailMask (gF L) l a w) = tailMask (gF L) l a (Sm eta L w) := by
  ext p
  rw [Sm, molecularH2StateMap_apply, tailMask_apply, molecularH2StateMap_apply]
  unfold molecularH2Coeff
  rw [tailMask_apply, mul_div_assoc]

omit [Fintype ν] in
lemma kinetic_tailMask (sys : CoulombSystem eta ν) (L : ℝ) (l : ℝ) (a : Fin eta)
    (w : MolecularFourierH2 eta) :
    coulombFourierKineticH2 sys (gF L) (tailMask (gF L) l a w) =
      tailMask (gF L) l a (coulombFourierKineticH2 sys (gF L) w) := by
  ext p
  rw [kinetic_apply', tailMask_apply, kinetic_apply']
  change ((Ek sys L p : ℝ) : ℂ) * Sm eta L (tailMask (gF L) l a w) p = _
  rw [stateMap_tailMask, tailMask_apply]
  ring

omit [Fintype ν] in
lemma shMask_truncate (a : Fin eta) (sh : Lattice3 → Prop) (n : ℕ) (x : L2 eta) :
    shMask a sh (molecularH2Truncate n x) = molecularH2Truncate n (shMask a sh x) := by
  classical
  ext q
  rw [shMask_apply, molecularH2Truncate_apply, molecularH2Truncate_apply]
  by_cases hq : q ∈ fourierConfigCube eta n
  · rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hq, cubicLatticeCoeffTruncate_eq_of_mem n _ q hq,
      shMask_apply]
  · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq,
      cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq, mul_zero]

omit [Fintype ν] in
/-- `(λ/2)^{-5/2} ≤ 2^{5/2} λ^{-1} ρ^{1/2}` for `λ ≥ 2`, `ρ ≥ 1`. -/
lemma tail52_arith {lam ρ : ℝ} (hlam : 2 ≤ lam) (hρ : 1 ≤ ρ) :
    (lam / 2) ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * lam⁻¹ * Real.sqrt ρ := by
  have hl0 : 0 < lam := by linarith
  have e : (lam / 2) ^ (-(5 / 2 : ℝ)) = 2 ^ (5 / 2 : ℝ) * lam ^ (-(5 / 2 : ℝ)) := by
    rw [Real.div_rpow hl0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have h1 : lam ^ (-(5 / 2 : ℝ)) ≤ lam⁻¹ := by
    have := rpow_le_of_le_one (show 1 ≤ lam by linarith) (show -(5 / 2 : ℝ) ≤ -1 by norm_num)
    rwa [Real.rpow_neg_one] at this
  have h2 : 1 ≤ Real.sqrt ρ := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  rw [e]
  have h3 : (0 : ℝ) ≤ 2 ^ (5 / 2 : ℝ) := by positivity
  calc 2 ^ (5 / 2 : ℝ) * lam ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * lam⁻¹ :=
        mul_le_mul_of_nonneg_left h1 h3
    _ ≤ 2 ^ (5 / 2 : ℝ) * lam⁻¹ * Real.sqrt ρ := by
        have : 0 ≤ 2 ^ (5 / 2 : ℝ) * lam⁻¹ := by positivity
        nlinarith

omit [Fintype ν] in
/-- `λ^{-2} ≤ λ^{-1} ρ^{1/2}` for `λ, ρ ≥ 1`. -/
lemma inv_sq_arith {lam ρ : ℝ} (hlam : 1 ≤ lam) (hρ : 1 ≤ ρ) : 1 / lam ^ 2 ≤ lam⁻¹ * Real.sqrt ρ := by
  have hl0 : 0 < lam := by linarith
  have h2 : 1 ≤ Real.sqrt ρ := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have h1 : 1 / lam ^ 2 ≤ lam⁻¹ := by
    rw [one_div, inv_le_inv₀ (by positivity) hl0]; nlinarith
  have : 0 ≤ lam⁻¹ := by positivity
  nlinarith

omit [Fintype ν] in
lemma rpow_neg_three_eq {lam : ℝ} (hl : 0 < lam) : lam ^ (-(3 : ℝ)) = 1 / lam ^ 2 * lam⁻¹ := by
  rw [Real.rpow_neg hl.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

end Mask

/-! ## `lem:band`: the potential on a shell -/

section BandW

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel hL in
/-- **The near input** (`lem:band`): Hardy on the `l`-tail of a good state,
`‖W 1_{a,>l} u‖ ≤ C_m √3 M l^{-3/2}`. -/
theorem near_band (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {M : ℝ}
    {w : MolecularFourierH2 eta} (hF : FGood sys L M w) (a : Fin eta) {l : ℝ} (hl : 1 ≤ l) :
    ‖Wp sys L H (tailMask (gF L) l a w)‖ ≤
      finiteCoulombPhysicalMassConstant sys L Hunit * (Real.sqrt 3 * M * l ^ (-(3 / 2 : ℝ))) := by
  have hM := hF.nonneg
  have hl0 : 0 < l := by linarith
  have h1 : ‖Sm eta L (tailMask (gF L) l a w)‖ ≤ M * l ^ (-(5 / 2 : ℝ)) := by
    rw [stateMap_tailMask]; exact (hF.2 a l hl).1
  have h2 : ‖coulombFourierKineticH2 sys (gF L) (tailMask (gF L) l a w)‖ ≤ M * l ^ (-(1 / 2 : ℝ)) := by
    rw [kinetic_tailMask]; exact (hF.2 a l hl).2
  have hab : M * l ^ (-(5 / 2 : ℝ)) ≤ M * l ^ (-(1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left (rpow_le_of_le_one hl (by norm_num)) hM
  have h := norm_W_le_of sys hL H hKernel Hunit hPeriodic (tailMask (gF L) l a w) h1 h2 hab
  rwa [sqrt_three_tail hM hl0] at h

open Classical in
include hKernel hL in
/-- **The far input** (`lem:band`): inputs with `|p_a| ≤ r₀`, outputs in a shell `sh` beyond
`r₁ > r₀` (lattice units) with at most `N₀` points:
`‖1_S W (1 - 1_{a,>g r₀}) u‖ ≤ (c_tot/(r₁-r₀)²) (53 N₀)^{1/2} c_L M` when `‖S u‖ + ‖T u‖ ≤ M`. -/
theorem far_band {M : ℝ} {w : MolecularFourierH2 eta}
    (hw : ‖Sm eta L w‖ + ‖coulombFourierKineticH2 sys (gF L) w‖ ≤ M)
    (a : Fin eta) (sh : Lattice3 → Prop) {N₀ r₀ r₁ : ℝ} (hN₀ : 0 ≤ N₀) (hr₀ : 0 ≤ r₀)
    (hr : r₀ < r₁) (hsh : ∀ y, sh y → r₁ ^ 2 ≤ nsq y)
    (hcnt : ∀ T : Finset Lattice3, (∀ y ∈ T, sh y) → (T.card : ℝ) ≤ N₀) :
    ‖shMask a sh (Wp sys L H (w - tailMask (gF L) (gF L * r₀) a w))‖ ≤
      ctot sys L / (r₁ - r₀) ^ 2 * Real.sqrt (53 * N₀) * (cL sys L * M) := by
  have hg := gF_pos hL
  set y := w - tailMask (gF L) (gF L * r₀) a w with hy
  -- the far input vanishes beyond `r₀`
  have hSy : ∀ p, Sm eta L y p = if nsq (p a) ≤ r₀ ^ 2 then Sm eta L w p else 0 := by
    intro p
    rw [hy, map_sub, stateMap_tailMask, lp.coeFn_sub, Pi.sub_apply, tailMask_apply]
    by_cases hp : nsq (p a) ≤ r₀ ^ 2
    · rw [if_pos hp, if_neg]
      · simp
      · intro hlt
        have h1 : r₀ < Real.sqrt (latticeNormSq (p a)) := by
          have := (mul_lt_mul_iff_of_pos_left hg).mp hlt
          exact this
        have h2 : Real.sqrt (latticeNormSq (p a)) ≤ r₀ := by
          rw [Real.sqrt_le_left hr₀, ← nsq_eq_latticeNormSq]; exact hp
        linarith
    · rw [if_neg hp, if_pos]
      · simp
      · push Not at hp
        have h1 : r₀ < Real.sqrt (latticeNormSq (p a)) :=
          Real.lt_sqrt_of_sq_lt (by rw [← nsq_eq_latticeNormSq]; exact hp)
        exact mul_lt_mul_of_pos_left h1 hg
  -- the budget of the far input
  have hyM : ‖Sm eta L y‖ + ‖coulombFourierKineticH2 sys (gF L) y‖ ≤ M := by
    have h1 : ‖Sm eta L y‖ ≤ ‖Sm eta L w‖ := by
      have := l2_norm_le_of_le (Sm eta L y) (Sm eta L w) zero_le_one fun p => by
        rw [hSy, one_mul]; split_ifs <;> simp
      rwa [one_mul] at this
    have h2 : ‖coulombFourierKineticH2 sys (gF L) y‖ ≤ ‖coulombFourierKineticH2 sys (gF L) w‖ := by
      have := l2_norm_le_of_le (coulombFourierKineticH2 sys (gF L) y)
        (coulombFourierKineticH2 sys (gF L) w) zero_le_one fun p => by
        rw [kinetic_apply', kinetic_apply', one_mul]
        change ‖((Ek sys L p : ℝ) : ℂ) * Sm eta L y p‖ ≤ ‖((Ek sys L p : ℝ) : ℂ) * Sm eta L w p‖
        rw [hSy]
        split_ifs
        · exact le_rfl
        · rw [mul_zero, norm_zero]; exact norm_nonneg _
      rwa [one_mul] at this
    linarith
  have hM : 0 ≤ M := le_trans (by positivity) hw
  have hcL : 0 ≤ cL sys L := by
    unfold cL; have := one_le_mtop sys; have : 0 < gF L ^ 2 := by positivity
    positivity
  have hct := ctot_nonneg sys hL
  set B := ctot sys L / (r₁ - r₀) ^ 2 * Real.sqrt (53 * N₀) * (cL sys L * M) with hB
  have hB0 : 0 ≤ B := by
    have : 0 < r₁ - r₀ := by linarith
    positivity
  -- the truncations
  have hN : ∀ N : ℕ, ‖shMask a sh (Wp sys L H (molecularH2Truncate N y))‖ ≤ B := by
    intro N
    set F := (fourierConfigCube eta N).filter (fun p => nsq (p a) ≤ r₀ ^ 2)
    have hF : ∀ p ∈ F, nsq (p a) ≤ r₀ ^ 2 := fun p hp => (Finset.mem_filter.mp hp).2
    have hWq : ∀ q, Wp sys L H (molecularH2Truncate N y) q =
        ∑ p ∈ F, Sm eta L y p * potKernel sys L q p := by
      intro q
      have h := potential_apply sys L H hKernel hL (molecularH2Truncate N y) q
      change Wp sys L H (molecularH2Truncate N y) q = _ at h
      rw [h]
      have hz : ∀ p ∉ F, molecularH2Coeff (2 * Real.pi / L) (molecularH2Truncate N y) p *
          potKernel sys L q p = 0 := by
        intro p hp
        rw [molecularH2Coeff_truncate]
        by_cases hc : p ∈ fourierConfigCube eta N
        · rw [cubicLatticeCoeffTruncate_eq_of_mem N _ p hc]
          have hnp : ¬ nsq (p a) ≤ r₀ ^ 2 := fun h => hp (Finset.mem_filter.mpr ⟨hc, h⟩)
          have e : molecularH2Coeff (2 * Real.pi / L) y p = Sm eta L y p :=
            (molecularH2StateMap_apply _ _ _).symm
          rw [e, hSy, if_neg hnp, zero_mul]
        · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem N _ p hc, zero_mul]
      rw [tsum_eq_sum hz]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [molecularH2Coeff_truncate,
        cubicLatticeCoeffTruncate_eq_of_mem N _ p (Finset.mem_filter.mp hp).1]
      have e : molecularH2Coeff (2 * Real.pi / L) y p = Sm eta L y p :=
        (molecularH2StateMap_apply _ _ _).symm
      rw [e]
    have hfar := far_band_finite (sys := sys) hL a sh hN₀ hr₀ hr hsh hcnt F hF (Sm eta L y)
    have hsq : ‖shMask a sh (Wp sys L H (molecularH2Truncate N y))‖ ^ 2 ≤ B ^ 2 := by
      rw [norm_shMask_sq]
      have e : (fun q => if sh (q a) then ‖Wp sys L H (molecularH2Truncate N y) q‖ ^ 2 else 0) =
          fun q => if sh (q a) then ‖∑ p ∈ F, Sm eta L y p * potKernel sys L q p‖ ^ 2 else 0 := by
        funext q; rw [hWq]
      rw [e]
      refine hfar.2.trans ?_
      -- the weighted sum of the input
      have hS : ∑ p ∈ F, (1 + lsqC p) ^ 2 * ‖Sm eta L y p‖ ^ 2 ≤ (cL sys L * M) ^ 2 := by
        set v := Sm eta L y + coulombFourierKineticH2 sys (gF L) y
        have hv : ‖v‖ ≤ M := (norm_add_le _ _).trans hyM
        calc ∑ p ∈ F, (1 + lsqC p) ^ 2 * ‖Sm eta L y p‖ ^ 2
            ≤ ∑ p ∈ F, cL sys L ^ 2 * ‖v p‖ ^ 2 := by
              refine Finset.sum_le_sum fun p _ => ?_
              have h1 := FSFlux.one_add_lsqC_le (sys := sys) hL p
              have hl := lsqC_nonneg p
              have hE0 : 0 ≤ Ek sys L p := by
                rw [Ek, E]
                exact Finset.sum_nonneg fun c _ => by
                  have := sys.mass_pos c; have := nsq_nonneg (p c); positivity
              have hvp : v p = ((1 + Ek sys L p : ℝ) : ℂ) * Sm eta L y p := shMask_add_kin_apply sys L y p
              rw [hvp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
              have h2 : (1 + lsqC p) ^ 2 ≤ (cL sys L * (1 + Ek sys L p)) ^ 2 :=
                pow_le_pow_left₀ (by linarith) h1 2
              calc (1 + lsqC p) ^ 2 * ‖Sm eta L y p‖ ^ 2
                  ≤ (cL sys L * (1 + Ek sys L p)) ^ 2 * ‖Sm eta L y p‖ ^ 2 :=
                    mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
                _ = cL sys L ^ 2 * ((1 + Ek sys L p) * ‖Sm eta L y p‖) ^ 2 := by ring
          _ = cL sys L ^ 2 * ∑ p ∈ F, ‖v p‖ ^ 2 := by rw [Finset.mul_sum]
          _ ≤ cL sys L ^ 2 * ‖v‖ ^ 2 := by
              refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
              rw [l2_norm_sq]
              exact (l2_summable_sq v).sum_le_tsum _ fun _ _ => sq_nonneg _
          _ ≤ cL sys L ^ 2 * M ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hv 2) (sq_nonneg _)
          _ = (cL sys L * M) ^ 2 := by ring
      have hd : 0 < r₁ - r₀ := by linarith
      have e2 : B ^ 2 = (ctot sys L / (r₁ - r₀) ^ 2) ^ 2 * (53 * N₀) * (cL sys L * M) ^ 2 := by
        rw [hB, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      rw [e2]
      exact mul_le_mul_of_nonneg_left hS (by positivity)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 two_ne_zero).mp hsq
  -- the limit
  have ht : Tendsto (fun N => ‖shMask a sh (Wp sys L H (molecularH2Truncate N y))‖) atTop
      (𝓝 ‖shMask a sh (Wp sys L H y)‖) :=
    ((continuous_norm.comp ((shMask a sh).continuous.comp (Wp sys L H).continuous)).tendsto y).comp
      (molecularH2Truncate_tendsto y)
  exact le_of_tendsto' ht hN

/-! ### Physical shells and the constant of `lem:band` -/

/-- The physical shell of a register momentum in lattice units: `λ ≤ g|y| < λ + ρ`
(`cube = false`) or `λ ≤ g‖y‖_∞ < λ + ρ` (`cube = true`). -/
def physSh : Bool → ℝ → ℝ → ℝ → Lattice3 → Prop
  | false, g, lam, ρ => shE (lam / g) (ρ / g)
  | true, g, lam, ρ => shC (lam / g) (ρ / g)

omit [Fintype ν] in
lemma physSh_ge {cube : Bool} {g lam ρ : ℝ} (hg : 0 < g) (hlam : 0 ≤ lam) {y : Lattice3}
    (hy : physSh cube g lam ρ y) : (lam / g) ^ 2 ≤ nsq y := by
  cases cube
  · exact hy.1
  · have h1 : lam / g ≤ supn y := hy.1
    have h0 : 0 ≤ lam / g := div_nonneg hlam hg.le
    calc (lam / g) ^ 2 ≤ supn y ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ ≤ lsq y := supn_sq_le_lsq y

omit [Fintype ν] in
lemma physSh_count {cube : Bool} {g lam ρ : ℝ} (hg : 0 < g) (hlamg : g ≤ lam) (hρ : 0 ≤ ρ)
    (hρl : ρ ≤ lam) (T : Finset Lattice3) (hT : ∀ y ∈ T, physSh cube g lam ρ y) :
    (T.card : ℝ) ≤ 2250 * (lam / g) ^ 2 * max (ρ / g) 1 := by
  have hΛ : 1 ≤ lam / g := by rw [le_div_iff₀ hg]; linarith
  have hR : 0 ≤ ρ / g := div_nonneg hρ hg.le
  have hRΛ : ρ / g ≤ lam / g := div_le_div_of_nonneg_right hρl hg.le
  cases cube
  · have h := shE_count hΛ hR hRΛ T hT
    have : 0 ≤ (lam / g) ^ 2 * max (ρ / g) 1 := by positivity
    linarith
  · exact shC_count hΛ hR hRΛ T hT

omit [Fintype ν] in
lemma near_arith {C M lam ρ : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hlam : 2 ≤ lam) (hρ : 1 ≤ ρ) :
    C * (Real.sqrt 3 * M * (lam / 2) ^ (-(3 / 2 : ℝ))) ≤
      Real.sqrt 3 * 2 ^ (3 / 2 : ℝ) * C * M * lam⁻¹ * Real.sqrt ρ := by
  have hl0 : 0 < lam := by linarith
  have e : (lam / 2) ^ (-(3 / 2 : ℝ)) = 2 ^ (3 / 2 : ℝ) * lam ^ (-(3 / 2 : ℝ)) := by
    rw [Real.div_rpow hl0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have h1 : lam ^ (-(3 / 2 : ℝ)) ≤ lam⁻¹ := by
    have := rpow_le_of_le_one (show 1 ≤ lam by linarith) (show -(3 / 2 : ℝ) ≤ -1 by norm_num)
    rwa [Real.rpow_neg_one] at this
  have h2 : 1 ≤ Real.sqrt ρ := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  rw [e]
  have h3 : 0 ≤ Real.sqrt 3 * 2 ^ (3 / 2 : ℝ) * C * M := by positivity
  calc C * (Real.sqrt 3 * M * (2 ^ (3 / 2 : ℝ) * lam ^ (-(3 / 2 : ℝ))))
      = Real.sqrt 3 * 2 ^ (3 / 2 : ℝ) * C * M * lam ^ (-(3 / 2 : ℝ)) := by ring
    _ ≤ Real.sqrt 3 * 2 ^ (3 / 2 : ℝ) * C * M * lam⁻¹ := mul_le_mul_of_nonneg_left h1 h3
    _ ≤ Real.sqrt 3 * 2 ^ (3 / 2 : ℝ) * C * M * lam⁻¹ * Real.sqrt ρ := by
        have : 0 ≤ Real.sqrt 3 * 2 ^ (3 / 2 : ℝ) * C * M * lam⁻¹ := by positivity
        nlinarith

omit [Fintype ν] in
lemma far_arith {g c κ M lam ρ : ℝ} (hg : 0 < g) (hc : 0 ≤ c) (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hlam : 0 < lam) (hρ : 1 ≤ ρ) :
    c / (lam / g - lam / (2 * g)) ^ 2 * Real.sqrt (53 * (2250 * (lam / g) ^ 2 * max (ρ / g) 1)) *
        (κ * M) ≤
      4 * g * c * κ * Real.sqrt (53 * 2250 * max 1 (1 / g)) * M * lam⁻¹ * Real.sqrt ρ := by
  have hg2 : lam / g - lam / (2 * g) = lam / (2 * g) := by field_simp; ring
  rw [hg2]
  set m := max (ρ / g) 1 with hm_def
  have hm : m ≤ max 1 (1 / g) * ρ := by
    rcases le_total (ρ / g) 1 with h | h
    · rw [hm_def, max_eq_right h]
      calc (1 : ℝ) ≤ 1 * ρ := by linarith
        _ ≤ max 1 (1 / g) * ρ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    · rw [hm_def, max_eq_left h]
      calc ρ / g = (1 / g) * ρ := by ring
        _ ≤ max 1 (1 / g) * ρ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  have hm0 : 0 ≤ m := le_trans zero_le_one (le_max_right _ _)
  have hsq : Real.sqrt (53 * (2250 * (lam / g) ^ 2 * m)) = lam / g * Real.sqrt (53 * 2250 * m) := by
    rw [show 53 * (2250 * (lam / g) ^ 2 * m) = (lam / g) ^ 2 * (53 * 2250 * m) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hlam.le hg.le)]
  have hsq2 : Real.sqrt (53 * 2250 * m) ≤ Real.sqrt (53 * 2250 * max 1 (1 / g)) * Real.sqrt ρ := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have : 0 ≤ (53 * 2250 : ℝ) := by norm_num
    nlinarith
  rw [hsq]
  have e : c / (lam / (2 * g)) ^ 2 * (lam / g * Real.sqrt (53 * 2250 * m)) * (κ * M) =
      4 * g * c * κ * M * lam⁻¹ * Real.sqrt (53 * 2250 * m) := by
    field_simp; ring
  rw [e]
  have h0 : 0 ≤ 4 * g * c * κ * M * lam⁻¹ := by positivity
  calc 4 * g * c * κ * M * lam⁻¹ * Real.sqrt (53 * 2250 * m)
      ≤ 4 * g * c * κ * M * lam⁻¹ * (Real.sqrt (53 * 2250 * max 1 (1 / g)) * Real.sqrt ρ) :=
        mul_le_mul_of_nonneg_left hsq2 h0
    _ = _ := by ring

/-- The constant of the shell bound of `W`. -/
noncomputable def bandK1 (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  Real.sqrt 3 * 2 ^ (3 / 2 : ℝ) * finiteCoulombPhysicalMassConstant sys L Hunit +
    4 * gF L * ctot sys L * cL sys L * Real.sqrt (53 * 2250 * max 1 (1 / gF L))

lemma bandK1_nonneg {L : ℝ} (hL : 0 < L) (Hunit : ℝ) : 0 ≤ bandK1 sys L Hunit := by
  have hg := gF_pos hL
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hct := ctot_nonneg sys hL
  have hcL : 0 ≤ cL sys L := by
    unfold cL; have := one_le_mtop sys; have : 0 < gF L ^ 2 := by positivity
    positivity
  unfold bandK1; positivity

include hKernel hL in
/-- **The potential on a shell** (the paragraph after `lem:thinschur`, K1, for every good state):
for `λ ≥ max(2, g)` and `1 ≤ ρ ≤ λ`, `‖1_S (W u)^‖ ≤ C M λ^{-1} ρ^{1/2}`, Euclidean or cube
shell. -/
theorem band_W (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {M : ℝ}
    {w : MolecularFourierH2 eta} (hF : FGood sys L M w) (a : Fin eta) (cube : Bool) {lam ρ : ℝ}
    (hlam2 : 2 ≤ lam) (hlamg : gF L ≤ lam) (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam) :
    ‖shMask a (physSh cube (gF L) lam ρ) (Wp sys L H w)‖ ≤
      bandK1 sys L Hunit * M * lam⁻¹ * Real.sqrt ρ := by
  have hg := gF_pos hL
  have hM := hF.nonneg
  have hlam0 : 0 < lam := by linarith
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hct := ctot_nonneg sys hL
  have hcL : 0 ≤ cL sys L := by
    unfold cL; have := one_le_mtop sys; have : 0 < gF L ^ 2 := by positivity
    positivity
  set sh := physSh cube (gF L) lam ρ
  set r₀ := lam / (2 * gF L)
  have hthr : gF L * r₀ = lam / 2 := by simp only [r₀]; field_simp
  have hsplit : Wp sys L H w = Wp sys L H (tailMask (gF L) (lam / 2) a w) +
      Wp sys L H (w - tailMask (gF L) (gF L * r₀) a w) := by
    rw [hthr, ← map_add, add_sub_cancel]
  have hnear := near_band sys hL H hKernel Hunit hPeriodic hF a (l := lam / 2) (by linarith)
  have hr : r₀ < lam / gF L := by
    simp only [r₀]
    rw [div_lt_div_iff₀ (by positivity) hg]
    nlinarith
  have hfar := far_band sys hL H hKernel hF.1 a sh (N₀ := 2250 * (lam / gF L) ^ 2 * max (ρ / gF L) 1)
    (r₀ := r₀) (r₁ := lam / gF L) (by positivity) (by positivity) hr
    (fun y hy => physSh_ge hg hlam0.le hy) (physSh_count hg hlamg (by linarith) hρl)
  have hfar' := hfar.trans (far_arith (c := ctot sys L) (κ := cL sys L) hg hct hcL hM hlam0 hρ)
  have hnear' := (norm_shMask_le a sh _).trans (hnear.trans (near_arith hCm hM hlam2 hρ))
  rw [hsplit, map_add]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ Real.sqrt 3 * 2 ^ (3 / 2 : ℝ) * finiteCoulombPhysicalMassConstant sys L Hunit * M *
          lam⁻¹ * Real.sqrt ρ +
        4 * gF L * ctot sys L * cL sys L * Real.sqrt (53 * 2250 * max 1 (1 / gF L)) * M * lam⁻¹ *
          Real.sqrt ρ := add_le_add hnear' hfar'
    _ = _ := by unfold bandK1; ring

/-! ### `lem:band` for the exact and the truncated state -/

/-- The constant of `lem:band` for `ψ(t)` and `P ψ(t)` (per unit `Ξ`). -/
noncomputable def bandEx (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  2 ^ (5 / 2 : ℝ) * cTr sys L Hunit + 16 * sys.maxMass * (1 + relB sys L Hunit) +
    bandK1 sys L Hunit * cTr sys L Hunit

include hKernel hL in
/-- **`lem:band` for the exact state** `ψ(t)`: for `λ ≥ max(2, g)` and `1 ≤ ρ ≤ λ`,
`‖1_S ℰ ψ̂(t)‖ ≤ C Ξ λ^{-1} ρ^{1/2}` and `‖1_S ψ̂(t)‖ ≤ 2m̄ C Ξ λ^{-3} ρ^{1/2}`, uniformly in `t`,
for the Euclidean and the cube shell. -/
theorem band_exact (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (t : ℝ) (a : Fin eta) (cube : Bool) {lam ρ : ℝ}
    (hlam2 : 2 ≤ lam) (hlamg : gF L ≤ lam) (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam) :
    ‖shMask a (physSh cube (gF L) lam ρ)
        (Sm eta L (traj H D t) + coulombFourierKineticH2 sys (gF L) (traj H D t))‖ ≤
        bandEx sys L Hunit * D.Xi * lam⁻¹ * Real.sqrt ρ ∧
      ‖shMask a (physSh cube (gF L) lam ρ) (Sm eta L (traj H D t))‖ ≤
        2 * sys.maxMass * bandEx sys L Hunit * D.Xi * lam ^ (-(3 : ℝ)) * Real.sqrt ρ := by
  have hg := gF_pos hL
  have hlam0 : 0 < lam := by linarith
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hb := relB_nonneg sys L Hunit hC
  have hΞ := D.Xi_nonneg
  have hc := cTr_nonneg sys hL Hunit
  have hm := sys.one_le_maxMass
  have hK1 := bandK1_nonneg sys hL Hunit
  set sh := physSh cube (gF L) lam ρ
  obtain ⟨w, hw1, hw2, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D t
  have hw : traj H D t = w := traj_eq H D t w hw1
  rw [hw]
  set M := cTr sys L Hunit * D.Xi
  have hM : 0 ≤ M := by positivity
  have hsh2 : ∀ y, sh y → ((lam / 2) / gF L) ^ 2 < nsq y := by
    intro y hy
    have h1 := physSh_ge hg hlam0.le hy
    have h2 : ((lam / 2) / gF L) ^ 2 < (lam / gF L) ^ 2 := by
      apply pow_lt_pow_left₀ _ (by positivity) two_ne_zero
      rw [div_lt_div_iff_of_pos_right hg]; linarith
    linarith
  -- `T w = H w - W w`, `H w = S v'`
  have hT : coulombFourierKineticH2 sys (gF L) w = H w - Wp sys L H w := by
    simp only [Wp, coulombFourierPotentialH2, sub_apply]; abel
  obtain ⟨v', hv1, hv2⟩ := D.graph t D.v₀
  have hHw : H w = Sm eta L v' := by rw [hw2, D.uv, hv1]
  -- the three pieces
  have h1 : ‖shMask a sh (Sm eta L w)‖ ≤ M * (lam / 2) ^ (-(5 / 2 : ℝ)) :=
    (norm_shMask_le_tail hg a sh hsh2 _).trans (hF.2 a (lam / 2) (by linarith)).1
  have h2 : ‖shMask a sh (Sm eta L v')‖ ≤ 16 * sys.maxMass * (1 + relB sys L Hunit) * D.Xi *
      (1 / lam ^ 2) := by
    refine (norm_shMask_le_tail hg a sh hsh2 _).trans ?_
    have hl2 : (0 : ℝ) < lam / 2 := by linarith
    have ht := tail_stateMap_le sys L hl2 a v'
    have hTv : ‖coulombFourierKineticH2 sys (2 * Real.pi / L) v'‖ ≤
        2 * ‖H v'‖ + 2 * relB sys L Hunit * ‖molecularH2StateMap eta (2 * Real.pi / L) v'‖ :=
      kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC v'
    have hHv : ‖H v'‖ = ‖H D.v₀‖ := by rw [hv2, LinearIsometryEquiv.norm_map]
    have hSv : ‖molecularH2StateMap eta (2 * Real.pi / L) v'‖ = ‖H D.u₀‖ := by
      change ‖Sm eta L v'‖ = _
      rw [hv1, LinearIsometryEquiv.norm_map, ← D.uv]
    rw [hHv, hSv] at hTv
    have hXi : ‖H D.v₀‖ ≤ D.Xi ∧ ‖H D.u₀‖ ≤ D.Xi := by
      unfold EvoData.Xi
      have := norm_nonneg (Sm eta L D.u₀); have := norm_nonneg (H D.u₀)
      have := norm_nonneg (H D.v₀)
      constructor <;> linarith
    have hTv' : ‖coulombFourierKineticH2 sys (2 * Real.pi / L) v'‖ ≤
        2 * (1 + relB sys L Hunit) * D.Xi := by
      have := mul_le_mul_of_nonneg_left hXi.2 hb
      nlinarith [hXi.1]
    change ‖tailMask (2 * Real.pi / L) (lam / 2) a (molecularH2StateMap eta (2 * Real.pi / L) v')‖ ≤ _
    refine ht.trans ?_
    have e : 2 * sys.maxMass / (lam / 2) ^ 2 = 8 * sys.maxMass * (1 / lam ^ 2) := by
      field_simp; ring
    rw [e]
    calc 8 * sys.maxMass * (1 / lam ^ 2) *
          ‖tailMask (2 * Real.pi / L) (lam / 2) a (coulombFourierKineticH2 sys (2 * Real.pi / L) v')‖
        ≤ 8 * sys.maxMass * (1 / lam ^ 2) * (2 * (1 + relB sys L Hunit) * D.Xi) :=
          mul_le_mul_of_nonneg_left ((norm_tailMask_le _ _ _ _).trans hTv') (by positivity)
      _ = 16 * sys.maxMass * (1 + relB sys L Hunit) * D.Xi * (1 / lam ^ 2) := by ring
  have h3 := band_W sys hL H hKernel Hunit hPeriodic hF a cube hlam2 hlamg hρ hρl
  have hA : ‖shMask a sh (Sm eta L w + coulombFourierKineticH2 sys (gF L) w)‖ ≤
      bandEx sys L Hunit * D.Xi * lam⁻¹ * Real.sqrt ρ := by
    rw [hT, hHw, map_add, map_sub]
    have hn : ‖shMask a sh (Sm eta L w) + (shMask a sh (Sm eta L v') - shMask a sh (Wp sys L H w))‖ ≤
        ‖shMask a sh (Sm eta L w)‖ + ‖shMask a sh (Sm eta L v')‖ + ‖shMask a sh (Wp sys L H w)‖ := by
      refine (norm_add_le _ _).trans ?_
      have := norm_sub_le (shMask a sh (Sm eta L v')) (shMask a sh (Wp sys L H w))
      linarith
    refine hn.trans ?_
    have k1 := mul_le_mul_of_nonneg_left (tail52_arith hlam2 hρ) hM
    have k2 := mul_le_mul_of_nonneg_left (inv_sq_arith (by linarith : (1 : ℝ) ≤ lam) hρ)
      (by positivity : (0 : ℝ) ≤ 16 * sys.maxMass * (1 + relB sys L Hunit) * D.Xi)
    have e : bandEx sys L Hunit * D.Xi * lam⁻¹ * Real.sqrt ρ =
        M * (2 ^ (5 / 2 : ℝ) * lam⁻¹ * Real.sqrt ρ) +
          16 * sys.maxMass * (1 + relB sys L Hunit) * D.Xi * (lam⁻¹ * Real.sqrt ρ) +
          bandK1 sys L Hunit * M * lam⁻¹ * Real.sqrt ρ := by
      unfold bandEx; ring
    rw [e]
    linarith
  refine ⟨hA, ?_⟩
  refine (shell_state_le sys hL hlam0 a sh (fun y hy => physSh_ge hg hlam0.le hy) w).trans ?_
  have hm0 : 0 ≤ 2 * sys.maxMass / lam ^ 2 := by positivity
  calc 2 * sys.maxMass / lam ^ 2 *
        ‖shMask a sh (Sm eta L w + coulombFourierKineticH2 sys (gF L) w)‖
      ≤ 2 * sys.maxMass / lam ^ 2 * (bandEx sys L Hunit * D.Xi * lam⁻¹ * Real.sqrt ρ) :=
        mul_le_mul_of_nonneg_left hA hm0
    _ = 2 * sys.maxMass * bandEx sys L Hunit * D.Xi * lam ^ (-(3 : ℝ)) * Real.sqrt ρ := by
        rw [rpow_neg_three_eq hlam0]; ring

include hKernel hL in
/-- **`lem:band` for the truncated state** `P ψ(t)`: the same bounds (`1_S` commutes with `P`). -/
theorem band_trunc (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (t : ℝ) (n : ℕ) (a : Fin eta) (cube : Bool) {lam ρ : ℝ}
    (hlam2 : 2 ≤ lam) (hlamg : gF L ≤ lam) (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam) :
    ‖shMask a (physSh cube (gF L) lam ρ) (Sm eta L (molecularH2Truncate n (traj H D t)) +
        coulombFourierKineticH2 sys (gF L) (molecularH2Truncate n (traj H D t)))‖ ≤
        bandEx sys L Hunit * D.Xi * lam⁻¹ * Real.sqrt ρ ∧
      ‖shMask a (physSh cube (gF L) lam ρ) (Sm eta L (molecularH2Truncate n (traj H D t)))‖ ≤
        2 * sys.maxMass * bandEx sys L Hunit * D.Xi * lam ^ (-(3 : ℝ)) * Real.sqrt ρ := by
  obtain ⟨h1, h2⟩ := band_exact sys hL H hKernel Hunit hPeriodic D t a cube hlam2 hlamg hρ hρl
  have e1 : Sm eta L (molecularH2Truncate n (traj H D t)) +
      coulombFourierKineticH2 sys (gF L) (molecularH2Truncate n (traj H D t)) =
      molecularH2Truncate n (Sm eta L (traj H D t) +
        coulombFourierKineticH2 sys (gF L) (traj H D t)) := by
    rw [Sm, stateMap_truncate, kinetic_truncate, molecularH2Truncate_add]
  have e2 : Sm eta L (molecularH2Truncate n (traj H D t)) =
      molecularH2Truncate n (Sm eta L (traj H D t)) := by rw [Sm, stateMap_truncate]
  rw [e1, e2, shMask_truncate, shMask_truncate]
  exact ⟨(molecularH2Truncate_norm_le n _).trans h1, (molecularH2Truncate_norm_le n _).trans h2⟩

end BandW

end FSBand
