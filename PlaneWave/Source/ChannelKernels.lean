import PlaneWave.Source.LatticeSums
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Flux/source build, block 1b: output-weighted Coulomb channel kernels

The near/far hop estimates of `lem:qtail`, on an abstract finite configuration set `X` with a
register momentum `π : X → ℤ³`.  A *channel* is a kernel `κ : X → X → ℂ` with

* the Coulomb bound `‖κ q p‖ ≤ c_w / |π q - π p|²` (so `κ q p = 0` when `π q = π p`, since
  `c_w / 0 = 0`);
* row and column injectivity: for fixed output `q` the inputs `p` with `κ q p ≠ 0` are determined
  by `π p`, and for fixed input `p` the outputs are determined by `π q` (the nuclear term of a
  register and the pair terms containing it all have this form: the other momenta are fixed or
  determined by momentum conservation).

The output is weighted by `θ` with `|θ q| ≤ c_θ / |π q|²`, supported in `|π q| > R₀` (the
resolvent weight `1/(A_a + H_ā - E)` of the register shell).  The hops are split at
`|π q - π p| = |π q|/2`:

* `near_sum_le`: the near hops see only inputs with `|π p| > R₀/2`, and a weighted Schur test
  (row sums `≤ 13 c_θ c_w / R₀`, column sums `≤ 117 c_θ c_w / R₀`) gives the factor
  `39 c_θ c_w / R₀` (the recursion term `C m_a λ⁻¹ h(λ/2)` of eq:qtail-rec);
* `far_sum_le`: on far hops `|κ| ≤ 4 c_w/|π q|²`; Cauchy–Schwarz along the input fibre with the
  weight `(1 + |π p|²)^{-s}`, `s > 3/2`, and the lattice tail `Σ_{|ν| > R₀} |ν|⁻⁸ ≤ 130 R₀⁻⁵`
  give `‖far‖² ≤ 2080 Z_s (c_θ c_w)² R₀⁻⁵ Σ_p (1 + |π p|²)^s |u_p|²` (the term
  `C λ^{-5/2} ‖(1+A)^{3/4+ε} q‖` of eq:qtail-rec);
* `norm_wop_le`: the two together, for the output-weighted operator `wop κ θ`.

Auxiliary results: `sum_tail_inv_pow_four_le` (the lattice tail, from the dyadic Euclidean shells
`2^j R < |ν| ≤ 2^{j+1} R` and `card_euclid_shell_le`: `125 Σ_j 32^{-j} < 130`), `schur_sum_sq`
(the finite Schur test), and the triangle inequality `rho_add_le` for `|ν| = √(lsq ν)`, which
gives the near-hop geometry `|π q|/2 < |π p| < 3|π q|/2` (`near_geom`).
-/

set_option autoImplicit false

open Finset

namespace FSChannel

open FSLattice

variable {X : Type*} [Fintype X]

/-- A Coulomb-type channel kernel on configurations `X` with register momentum `π`. -/
structure IsChannel (π : X → L3) (κ : X → X → ℂ) (cw : ℝ) : Prop where
  bound : ∀ q p, ‖κ q p‖ ≤ cw / lsq (π q - π p)
  row : ∀ q p p', κ q p ≠ 0 → κ q p' ≠ 0 → π p = π p' → p = p'
  col : ∀ p q q', κ q p ≠ 0 → κ q' p ≠ 0 → π q = π q' → q = q'

/-- The weight constant `Z_s = 1 + 26 (1 + 1/(2s - 3))` of `Σ_ν (1 + |ν|²)^{-s}`. -/
noncomputable def Zs (s : ℝ) : ℝ := 1 + 26 * (1 + 1 / (2 * s - 3))

/-! ## Euclidean length and the triangle inequality on `ℤ³` -/

/-- Euclidean length `|ν| = √(lsq ν)` of a lattice vector. -/
noncomputable def rho (ν : L3) : ℝ := Real.sqrt (lsq ν)

lemma rho_nonneg (ν : L3) : 0 ≤ rho ν := Real.sqrt_nonneg _

lemma rho_sq (ν : L3) : rho ν ^ 2 = lsq ν := Real.sq_sqrt (lsq_nonneg ν)

/-- Triangle inequality `|a + b| ≤ |a| + |b|` on `ℤ³` (Cauchy–Schwarz via Lagrange's identity). -/
lemma rho_add_le (a b : L3) : rho (a + b) ≤ rho a + rho b := by
  unfold rho
  rw [Real.sqrt_le_left (by positivity)]
  have hdot : (a 0 : ℝ) * b 0 + (a 1 : ℝ) * b 1 + (a 2 : ℝ) * b 2 ≤
      Real.sqrt (lsq a) * Real.sqrt (lsq b) := by
    rw [← Real.sqrt_mul (lsq_nonneg a)]
    apply Real.le_sqrt_of_sq_le
    have hL : lsq a * lsq b - ((a 0 : ℝ) * b 0 + (a 1 : ℝ) * b 1 + (a 2 : ℝ) * b 2) ^ 2 =
        ((a 0 : ℝ) * b 1 - (a 1 : ℝ) * b 0) ^ 2 + ((a 0 : ℝ) * b 2 - (a 2 : ℝ) * b 0) ^ 2 +
          ((a 1 : ℝ) * b 2 - (a 2 : ℝ) * b 1) ^ 2 := by
      unfold lsq; ring
    nlinarith [sq_nonneg ((a 0 : ℝ) * b 1 - (a 1 : ℝ) * b 0),
      sq_nonneg ((a 0 : ℝ) * b 2 - (a 2 : ℝ) * b 0), sq_nonneg ((a 1 : ℝ) * b 2 - (a 2 : ℝ) * b 1)]
  have hab : lsq (a + b) =
      lsq a + lsq b + 2 * ((a 0 : ℝ) * b 0 + (a 1 : ℝ) * b 1 + (a 2 : ℝ) * b 2) := by
    simp only [lsq, Pi.add_apply, Int.cast_add]; ring
  rw [hab, add_sq, Real.sq_sqrt (lsq_nonneg a), Real.sq_sqrt (lsq_nonneg b)]
  linarith

lemma lsq_sub_comm (a b : L3) : lsq (a - b) = lsq (b - a) := by
  simp only [lsq, Pi.sub_apply, Int.cast_sub]; ring

/-- `|a| ≤ |b| + |a - b|`. -/
lemma rho_le_add_rho_sub (a b : L3) : rho a ≤ rho b + rho (a - b) := by
  have h := rho_add_le b (a - b)
  rwa [show b + (a - b) = a by abel] at h

/-- **Near-hop geometry.** If `|a - b| < |a|/2` then `|a|/2 < |b| < 3|a|/2`, in squared form. -/
lemma near_geom {a b : L3} (h : 4 * lsq (a - b) < lsq a) :
    lsq a < 4 * lsq b ∧ 4 * lsq b < 9 * lsq a := by
  have ha := rho_nonneg a
  have hb := rho_nonneg b
  have hd := rho_nonneg (a - b)
  have h1 := rho_le_add_rho_sub a b
  have h2 : rho b ≤ rho a + rho (a - b) := by
    have := rho_le_add_rho_sub b a
    unfold rho at this ⊢
    rwa [lsq_sub_comm b a] at this
  rw [← rho_sq a, ← rho_sq b]
  rw [← rho_sq a, ← rho_sq (a - b)] at h
  have h3 : 2 * rho (a - b) < rho a := by nlinarith
  constructor <;> nlinarith

/-! ## Lattice sums -/

/-- Points of `box N` have `|ν|² ≤ 3 N²`. -/
lemma lsq_le_of_mem_box {N : ℕ} {ν : L3} (h : ν ∈ box N) : lsq ν ≤ 3 * (N : ℝ) ^ 2 := by
  rw [mem_box] at h
  have hi : ∀ i, (ν i : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    intro i
    obtain ⟨h1, h2⟩ := h i
    have h1' : -(N : ℝ) ≤ ν i := by exact_mod_cast h1
    have h2' : (ν i : ℝ) ≤ N := by exact_mod_cast h2
    nlinarith
  unfold lsq
  linarith [hi 0, hi 1, hi 2]

/-- One dyadic Euclidean shell: `Σ_{ν ∈ S, lam < |ν| ≤ 2 lam} |ν|⁻⁸ ≤ 125 lam⁻⁵` (`lam ≥ 1`). -/
lemma sum_shell_inv_pow_four_le (S : Finset L3) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∑ ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lsq ν ^ 4 ≤
      125 / lam ^ 5 := by
  have hlam0 : 0 < lam := by linarith
  have hsub : S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2) ⊆
      (box ⌈2 * lam⌉₊).filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2) := by
    intro ν hν
    rw [mem_filter] at hν ⊢
    exact ⟨box_mono (Nat.floor_le_ceil _) (mem_box_floor_of_lsq_le (by linarith) hν.2.2), hν.2⟩
  have hcard : ((S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2)).card : ℝ) ≤
      125 * lam ^ 3 :=
    (Nat.cast_le.mpr (card_le_card hsub)).trans (card_euclid_shell_le hlam)
  calc ∑ ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lsq ν ^ 4
      ≤ ∑ _ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lam ^ 8 := by
        apply sum_le_sum
        intro ν hν
        rw [mem_filter] at hν
        have h1 : lam ^ 8 ≤ lsq ν ^ 4 := by
          rw [show lam ^ 8 = (lam ^ 2) ^ 4 by ring]
          exact pow_le_pow_left₀ (by positivity) hν.2.1.le 4
        exact one_div_le_one_div_of_le (by positivity) h1
    _ = (S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2)).card * (1 / lam ^ 8) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 125 * lam ^ 3 * (1 / lam ^ 8) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 125 / lam ^ 5 := by field_simp

/-- The dyadic shells `R < |ν| ≤ 2^J R`, by induction on `J` (for all `R ≥ 1` at once):
`125 R⁻⁵ + 130 (2R)⁻⁵ ≤ 130 R⁻⁵`. -/
lemma sum_dyadic_inv_pow_four_le (S : Finset L3) (J : ℕ) :
    ∀ R : ℝ, 1 ≤ R →
      ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * R) ^ 2), 1 / lsq ν ^ 4 ≤
        130 / R ^ 5 := by
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
    have h1 := sum_shell_inv_pow_four_le S hR
    have h2 := ih (2 * R) (by linarith)
    have e : (2 : ℝ) ^ (J + 1) * R = 2 ^ J * (2 * R) := by ring
    have hsplit :
        ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ (J + 1) * R) ^ 2), 1 / lsq ν ^ 4 ≤
          ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 * R) ^ 2), 1 / lsq ν ^ 4 +
            ∑ ν ∈ S.filter (fun ν => (2 * R) ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * (2 * R)) ^ 2),
              1 / lsq ν ^ 4 := by
      rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib, e]
      apply sum_le_sum
      intro ν _
      have hnn : 0 ≤ 1 / lsq ν ^ 4 := by have := lsq_nonneg ν; positivity
      by_cases hc1 : R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * (2 * R)) ^ 2
      · by_cases hc2 : lsq ν ≤ (2 * R) ^ 2
        · rw [if_pos hc1, if_pos ⟨hc1.1, hc2⟩]
          split_ifs <;> linarith
        · rw [if_pos hc1, if_neg (fun h => hc2 h.2), if_pos ⟨not_le.mp hc2, hc1.2⟩]
          linarith
      · rw [if_neg hc1]
        split_ifs <;> linarith
    have h5 : (2 * R) ^ 5 = 32 * R ^ 5 := by ring
    rw [h5] at h2
    calc _ ≤ _ := hsplit
      _ ≤ 125 / R ^ 5 + 130 / (32 * R ^ 5) := add_le_add h1 h2
      _ = (125 + 130 / 32) / R ^ 5 := by field_simp
      _ ≤ 130 / R ^ 5 := by gcongr; norm_num

/-- **Lattice tail sum.** `Σ_{ν ∈ S, |ν| > R} |ν|⁻⁸ ≤ 130 R⁻⁵` for `R ≥ 1`. -/
theorem sum_tail_inv_pow_four_le (S : Finset L3) {R : ℝ} (hR : 1 ≤ R) :
    ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν), 1 / lsq ν ^ 4 ≤ 130 / R ^ 5 := by
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
  exact sum_dyadic_inv_pow_four_le S J R hR

/-- **The finite Schur test**, output-first kernel convention. -/
theorem schur_sum_sq (K : X → X → ℂ) (x : X → ℂ) {R C : ℝ} (hR : 0 ≤ R) (_hC : 0 ≤ C)
    (hrow : ∀ q, ∑ p, ‖K q p‖ ≤ R) (hcol : ∀ p, ∑ q, ‖K q p‖ ≤ C) :
    ∑ q, ‖∑ p, x p * K q p‖ ^ 2 ≤ R * C * ∑ p, ‖x p‖ ^ 2 := by
  have hq : ∀ q, ‖∑ p, x p * K q p‖ ^ 2 ≤ R * ∑ p, ‖K q p‖ * ‖x p‖ ^ 2 := by
    intro q
    have h1 : ‖∑ p, x p * K q p‖ ≤ ∑ p, ‖K q p‖ * ‖x p‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine sum_congr rfl fun p _ => ?_
      rw [norm_mul, mul_comm]
    have h2 : (∑ p, ‖K q p‖ * ‖x p‖) ^ 2 ≤ (∑ p, ‖K q p‖) * ∑ p, ‖K q p‖ * ‖x p‖ ^ 2 :=
      sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => norm_nonneg _)
        (fun p _ => by positivity) (fun p _ => le_of_eq (by ring))
    calc ‖∑ p, x p * K q p‖ ^ 2 ≤ (∑ p, ‖K q p‖ * ‖x p‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ p, ‖K q p‖) * ∑ p, ‖K q p‖ * ‖x p‖ ^ 2 := h2
      _ ≤ R * ∑ p, ‖K q p‖ * ‖x p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hrow q) (sum_nonneg fun p _ => by positivity)
  calc ∑ q, ‖∑ p, x p * K q p‖ ^ 2 ≤ ∑ q, R * ∑ p, ‖K q p‖ * ‖x p‖ ^ 2 :=
        sum_le_sum fun q _ => hq q
    _ = R * ∑ p, ‖x p‖ ^ 2 * ∑ q, ‖K q p‖ := by
        rw [← mul_sum, sum_comm]
        congr 1
        refine sum_congr rfl fun p _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun q _ => mul_comm _ _
    _ ≤ R * ∑ p, ‖x p‖ ^ 2 * C := by
        gcongr with p
        exact hcol p
    _ = R * C * ∑ p, ‖x p‖ ^ 2 := by rw [← sum_mul]; ring

/-! ## Sums over injective images -/

/-- Coulomb sum over an injective image inside the ball `|ν| ≤ R`: `≤ 26 R`. -/
lemma sum_inv_lsq_image_le {ι : Type*} (F : Finset ι) (f : ι → L3) (hf : Set.InjOn f F)
    {R : ℝ} (hR : 0 ≤ R) (h0 : ∀ i ∈ F, f i ≠ 0) (hle : ∀ i ∈ F, lsq (f i) ≤ R ^ 2) :
    ∑ i ∈ F, 1 / lsq (f i) ≤ 26 * R := by
  rw [← sum_image (f := fun ν => 1 / lsq ν) hf]
  obtain ⟨N, hN⟩ := exists_box (F.image f)
  refine le_trans ?_ (sum_inv_lsq_ball_le' hR N)
  apply sum_le_sum_of_subset_of_nonneg
  · intro ν hν
    rw [mem_filter]
    refine ⟨hN hν, ?_⟩
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hν
    exact ⟨h0 i hi, hle i hi⟩
  · intro ν _ _
    exact div_nonneg zero_le_one (lsq_nonneg ν)

/-- Weight sum over an injective image: `≤ Z_s`. -/
lemma sum_weight_image_le {ι : Type*} (F : Finset ι) (f : ι → L3) (hf : Set.InjOn f F)
    {s : ℝ} (hs : 3 / 2 < s) : ∑ i ∈ F, (1 + lsq (f i)) ^ (-s) ≤ Zs s := by
  rw [← sum_image (f := fun ν => (1 + lsq ν) ^ (-s)) hf]
  exact sum_weight_le hs _

/-- Lattice tail sum over an injective image outside the ball `|ν| ≤ R`: `≤ 130 R⁻⁵`. -/
lemma sum_tail_image_le {ι : Type*} (G : Finset ι) (f : ι → L3) (hf : Set.InjOn f G)
    {R : ℝ} (hR : 1 ≤ R) (hG : ∀ i ∈ G, R ^ 2 < lsq (f i)) :
    ∑ i ∈ G, 1 / lsq (f i) ^ 4 ≤ 130 / R ^ 5 := by
  rw [← sum_image (f := fun ν => 1 / lsq ν ^ 4) hf]
  have h := sum_tail_inv_pow_four_le (G.image f) hR
  rwa [filter_true_of_mem] at h
  intro ν hν
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hν
  exact hG i hi

lemma Zs_pos {s : ℝ} (hs : 3 / 2 < s) : 0 < Zs s := by
  unfold Zs
  have : 0 < 2 * s - 3 := by linarith
  positivity

omit [Fintype X] in
/-- A nonzero channel entry has nonzero momentum transfer (`c_w / 0 = 0`). -/
lemma IsChannel.sub_ne_zero {π : X → L3} {κ : X → X → ℂ} {cw : ℝ} (hch : IsChannel π κ cw)
    {q p : X} (h : κ q p ≠ 0) : π q - π p ≠ 0 := by
  intro h0
  have hb := hch.bound q p
  rw [h0, lsq_zero, div_zero] at hb
  exact h (norm_le_zero_iff.mp hb)

variable (π : X → L3) (κ : X → X → ℂ) {cw : ℝ}

/-! ## Near hops -/

/-- Row sums of the near kernel `θ_q 1[near] κ_{qp}`: `≤ 13 c_θ c_w / R₀`. -/
lemma near_row_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R₀ : ℝ}
    (hcθ : 0 ≤ cθ) (hR₀ : 0 < R₀) (hθ : ∀ q, |θ q| ≤ cθ / lsq (π q))
    (hθ0 : ∀ q, lsq (π q) ≤ R₀ ^ 2 → θ q = 0) (q : X) :
    ∑ p, ‖(θ q : ℂ) * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0)‖ ≤
      13 * cθ * cw / R₀ := by
  by_cases hθq : θ q = 0
  · simp only [hθq, Complex.ofReal_zero, zero_mul, norm_zero, sum_const_zero]
    positivity
  have hL : R₀ ^ 2 < lsq (π q) := lt_of_not_ge (fun h => hθq (hθ0 q h))
  have hL0 : 0 < lsq (π q) := lt_trans (by positivity) hL
  have hr : R₀ < Real.sqrt (lsq (π q)) := (Real.lt_sqrt hR₀.le).mpr hL
  have hr0 : 0 < Real.sqrt (lsq (π q)) := hR₀.trans hr
  have hrr : Real.sqrt (lsq (π q)) ^ 2 = lsq (π q) := Real.sq_sqrt hL0.le
  have hpt : ∀ p, ‖(θ q : ℂ) * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0)‖ ≤
      cθ / lsq (π q) * cw *
        (if 4 * lsq (π q - π p) < lsq (π q) ∧ κ q p ≠ 0 then 1 / lsq (π q - π p) else 0) := by
    intro p
    by_cases hc : 4 * lsq (π q - π p) < lsq (π q) ∧ κ q p ≠ 0
    · rw [if_pos hc.1, if_pos hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |θ q| * ‖κ q p‖ ≤ cθ / lsq (π q) * (cw / lsq (π q - π p)) :=
            mul_le_mul (hθ q) (hch.bound q p) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · rw [if_neg hc]
      have h0 : (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0) = 0 := by
        split_ifs with h
        · by_contra hk
          exact hc ⟨h, hk⟩
        · rfl
      rw [h0, mul_zero, norm_zero, mul_zero]
  calc ∑ p, ‖(θ q : ℂ) * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0)‖
      ≤ ∑ p, cθ / lsq (π q) * cw *
          (if 4 * lsq (π q - π p) < lsq (π q) ∧ κ q p ≠ 0 then 1 / lsq (π q - π p) else 0) :=
        sum_le_sum fun p _ => hpt p
    _ = cθ / lsq (π q) * cw * ∑ p ∈ univ.filter
          (fun p => 4 * lsq (π q - π p) < lsq (π q) ∧ κ q p ≠ 0), 1 / lsq (π q - π p) := by
        rw [sum_filter, mul_sum]
    _ ≤ cθ / lsq (π q) * cw * (26 * (Real.sqrt (lsq (π q)) / 2)) := by
        gcongr
        refine sum_inv_lsq_image_le _ (fun p => π q - π p) ?_ (by positivity) ?_ ?_
        · intro p hp p' hp' h
          have hp1 := (mem_filter.mp (mem_coe.mp hp)).2
          have hp2 := (mem_filter.mp (mem_coe.mp hp')).2
          exact hch.row q p p' hp1.2 hp2.2 (sub_right_injective h)
        · intro p hp
          exact hch.sub_ne_zero (mem_filter.mp hp).2.2
        · intro p hp
          rw [div_pow, hrr]
          linarith [(mem_filter.mp hp).2.1]
    _ = 13 * cθ * cw / Real.sqrt (lsq (π q)) := by
        set r := Real.sqrt (lsq (π q))
        have hrne : r ≠ 0 := hr0.ne'
        rw [← hrr]
        field_simp
        ring
    _ ≤ 13 * cθ * cw / R₀ := div_le_div_of_nonneg_left (by positivity) hR₀ hr.le

/-- Column sums of the near kernel: `≤ 117 c_θ c_w / R₀`. -/
lemma near_col_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R₀ : ℝ}
    (hcθ : 0 ≤ cθ) (hR₀ : 0 < R₀) (hθ : ∀ q, |θ q| ≤ cθ / lsq (π q))
    (hθ0 : ∀ q, lsq (π q) ≤ R₀ ^ 2 → θ q = 0) (p : X) :
    ∑ q, ‖(θ q : ℂ) * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0)‖ ≤
      117 * cθ * cw / R₀ := by
  by_cases hp : R₀ ^ 2 < 4 * lsq (π p)
  swap
  · have h0 : ∀ q, (θ q : ℂ) * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0) = 0 := by
      intro q
      by_cases hθq : θ q = 0
      · rw [hθq, Complex.ofReal_zero, zero_mul]
      · have hL : R₀ ^ 2 < lsq (π q) := lt_of_not_ge (fun h => hθq (hθ0 q h))
        rw [if_neg, mul_zero]
        intro hn
        exact hp (lt_trans hL (near_geom hn).1)
    simp only [h0, norm_zero, sum_const_zero]
    positivity
  have hM0 : 0 < lsq (π p) := by nlinarith
  have hr0 : 0 < Real.sqrt (lsq (π p)) := Real.sqrt_pos.mpr hM0
  have hrr : Real.sqrt (lsq (π p)) ^ 2 = lsq (π p) := Real.sq_sqrt hM0.le
  have hr : R₀ < 2 * Real.sqrt (lsq (π p)) := by nlinarith
  have hpt : ∀ q, ‖(θ q : ℂ) * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0)‖ ≤
      9 * cθ / (4 * lsq (π p)) * cw *
        (if κ q p ≠ 0 ∧ lsq (π q - π p) ≤ lsq (π p) then 1 / lsq (π q - π p) else 0) := by
    intro q
    have hrhs : 0 ≤ 9 * cθ / (4 * lsq (π p)) * cw *
        (if κ q p ≠ 0 ∧ lsq (π q - π p) ≤ lsq (π p) then 1 / lsq (π q - π p) else 0) := by
      apply mul_nonneg (by positivity)
      split_ifs
      · exact div_nonneg zero_le_one (lsq_nonneg _)
      · exact le_rfl
    by_cases hθq : θ q = 0
    · rw [hθq, Complex.ofReal_zero, zero_mul, norm_zero]
      exact hrhs
    have hL : R₀ ^ 2 < lsq (π q) := lt_of_not_ge (fun h => hθq (hθ0 q h))
    by_cases hn : 4 * lsq (π q - π p) < lsq (π q)
    · by_cases hk : κ q p = 0
      · have hz : (θ q : ℂ) * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0) = 0 := by
          rw [if_pos hn, hk, mul_zero]
        rw [hz, norm_zero]
        exact hrhs
      have hg := near_geom hn
      have hc : κ q p ≠ 0 ∧ lsq (π q - π p) ≤ lsq (π p) := ⟨hk, by linarith [hg.1]⟩
      rw [if_pos hn, if_pos hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hθ' : |θ q| ≤ 9 * cθ / (4 * lsq (π p)) := by
        refine (hθ q).trans ?_
        rw [div_le_div_iff₀ (by linarith) (by positivity)]
        nlinarith [hg.2]
      calc |θ q| * ‖κ q p‖ ≤ 9 * cθ / (4 * lsq (π p)) * (cw / lsq (π q - π p)) :=
            mul_le_mul hθ' (hch.bound q p) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · rw [if_neg hn, mul_zero, norm_zero]
      exact hrhs
  calc ∑ q, ‖(θ q : ℂ) * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0)‖
      ≤ ∑ q, 9 * cθ / (4 * lsq (π p)) * cw *
          (if κ q p ≠ 0 ∧ lsq (π q - π p) ≤ lsq (π p) then 1 / lsq (π q - π p) else 0) :=
        sum_le_sum fun q _ => hpt q
    _ = 9 * cθ / (4 * lsq (π p)) * cw * ∑ q ∈ univ.filter
          (fun q => κ q p ≠ 0 ∧ lsq (π q - π p) ≤ lsq (π p)), 1 / lsq (π q - π p) := by
        rw [sum_filter, mul_sum]
    _ ≤ 9 * cθ / (4 * lsq (π p)) * cw * (26 * Real.sqrt (lsq (π p))) := by
        gcongr
        refine sum_inv_lsq_image_le _ (fun q => π q - π p) ?_ hr0.le ?_ ?_
        · intro q hq q' hq' h
          have hq1 := (mem_filter.mp (mem_coe.mp hq)).2
          have hq2 := (mem_filter.mp (mem_coe.mp hq')).2
          exact hch.col p q q' hq1.1 hq2.1 (sub_left_injective h)
        · intro q hq
          exact hch.sub_ne_zero (mem_filter.mp hq).2.1
        · intro q hq
          rw [hrr]
          exact (mem_filter.mp hq).2.2
    _ = 117 / 2 * cθ * cw / Real.sqrt (lsq (π p)) := by
        set r := Real.sqrt (lsq (π p))
        have hrne : r ≠ 0 := hr0.ne'
        rw [← hrr]
        field_simp
        ring
    _ ≤ 117 * cθ * cw / R₀ := by
        rw [div_le_div_iff₀ hr0 hR₀]
        nlinarith [mul_nonneg hcθ hcw]

/-- **Near hops.** -/
theorem near_sum_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R₀ : ℝ}
    (hcθ : 0 ≤ cθ) (hR₀ : 0 < R₀) (hθ : ∀ q, |θ q| ≤ cθ / lsq (π q))
    (hθ0 : ∀ q, lsq (π q) ≤ R₀ ^ 2 → θ q = 0) (u : X → ℂ) :
    ∑ q, ‖(θ q : ℂ) * ∑ p, u p * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0)‖ ^ 2 ≤
      (39 * cθ * cw / R₀) ^ 2 * ∑ p, (if R₀ ^ 2 < 4 * lsq (π p) then ‖u p‖ ^ 2 else 0) := by
  have hS := schur_sum_sq
    (fun q p => (θ q : ℂ) * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0))
    (fun p => if R₀ ^ 2 < 4 * lsq (π p) then u p else 0)
    (R := 13 * cθ * cw / R₀) (C := 117 * cθ * cw / R₀) (by positivity) (by positivity)
    (near_row_le π κ hch hcw θ hcθ hR₀ hθ hθ0) (near_col_le π κ hch hcw θ hcθ hR₀ hθ hθ0)
  have hLHS : ∀ q,
      (θ q : ℂ) * ∑ p, u p * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0) =
        ∑ p, (if R₀ ^ 2 < 4 * lsq (π p) then u p else 0) *
          ((θ q : ℂ) * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0)) := by
    intro q
    rw [mul_sum]
    refine sum_congr rfl fun p _ => ?_
    by_cases hθq : θ q = 0
    · rw [hθq, Complex.ofReal_zero]; ring
    · have hL : R₀ ^ 2 < lsq (π q) := lt_of_not_ge (fun h => hθq (hθ0 q h))
      by_cases hn : 4 * lsq (π q - π p) < lsq (π q)
      · rw [if_pos (lt_trans hL (near_geom hn).1)]; ring
      · rw [if_neg hn]; ring
  have hRHS : ∑ p, ‖(if R₀ ^ 2 < 4 * lsq (π p) then u p else 0)‖ ^ 2 =
      ∑ p, (if R₀ ^ 2 < 4 * lsq (π p) then ‖u p‖ ^ 2 else 0) := by
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  calc ∑ q, ‖(θ q : ℂ) * ∑ p, u p * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0)‖ ^ 2
      = ∑ q, ‖∑ p, (if R₀ ^ 2 < 4 * lsq (π p) then u p else 0) *
          ((θ q : ℂ) * (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0))‖ ^ 2 :=
        sum_congr rfl fun q _ => by rw [hLHS q]
    _ ≤ 13 * cθ * cw / R₀ * (117 * cθ * cw / R₀) *
          ∑ p, ‖(if R₀ ^ 2 < 4 * lsq (π p) then u p else 0)‖ ^ 2 := hS
    _ = (39 * cθ * cw / R₀) ^ 2 * ∑ p, (if R₀ ^ 2 < 4 * lsq (π p) then ‖u p‖ ^ 2 else 0) := by
        rw [hRHS]; ring

/-! ## Far hops -/

/-- Far hops, one output `q`: `‖θ_q Σ_p u_p 1[far] κ_{qp}‖² ≤ 16 (c_θ c_w)² Z_s |π q|⁻⁸ Σ_{p ∈ F_q}
(1 + |π p|²)^s ‖u_p‖²`, written as a sum over all `p`. -/
lemma far_row_sq_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R₀ s : ℝ}
    (hcθ : 0 ≤ cθ) (hR₀ : 1 ≤ R₀) (hs : 3 / 2 < s) (hθ : ∀ q, |θ q| ≤ cθ / lsq (π q))
    (hθ0 : ∀ q, lsq (π q) ≤ R₀ ^ 2 → θ q = 0) (u : X → ℂ) (q : X) :
    ‖(θ q : ℂ) * ∑ p, u p * (if 4 * lsq (π q - π p) < lsq (π q) then 0 else κ q p)‖ ^ 2 ≤
      16 * (cθ * cw) ^ 2 * Zs s * ∑ p, (if κ q p ≠ 0 ∧ R₀ ^ 2 < lsq (π q) then
        1 / lsq (π q) ^ 4 * ((1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) else 0) := by
  have hZ := Zs_pos hs
  have hw : ∀ p, 0 ≤ (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := fun p =>
    mul_nonneg (Real.rpow_nonneg (by linarith [lsq_nonneg (π p)]) s) (sq_nonneg _)
  have hrhs : 0 ≤ 16 * (cθ * cw) ^ 2 * Zs s * ∑ p, (if κ q p ≠ 0 ∧ R₀ ^ 2 < lsq (π q) then
      1 / lsq (π q) ^ 4 * ((1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) else 0) := by
    apply mul_nonneg (by positivity)
    apply sum_nonneg
    intro p _
    split_ifs
    · exact mul_nonneg (div_nonneg zero_le_one (pow_nonneg (lsq_nonneg _) 4)) (hw p)
    · exact le_rfl
  by_cases hθq : θ q = 0
  · rw [hθq, Complex.ofReal_zero, zero_mul, norm_zero]
    simpa using hrhs
  have hL : R₀ ^ 2 < lsq (π q) := lt_of_not_ge (fun h => hθq (hθ0 q h))
  have hL1 : 1 < lsq (π q) := by nlinarith
  have hL0 : 0 < lsq (π q) := by linarith
  have h1 : ‖∑ p, u p * (if 4 * lsq (π q - π p) < lsq (π q) then 0 else κ q p)‖ ≤
      4 * cw / lsq (π q) * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [sum_filter, mul_sum]
    refine sum_le_sum fun p _ => ?_
    rw [norm_mul]
    by_cases hn : 4 * lsq (π q - π p) < lsq (π q)
    · rw [if_pos hn, norm_zero, mul_zero]
      split_ifs <;> positivity
    · rw [if_neg hn]
      by_cases hk : κ q p = 0
      · rw [if_neg (not_not.mpr hk), hk, norm_zero, mul_zero, mul_zero]
      · rw [if_pos hk]
        have hD : lsq (π q) ≤ 4 * lsq (π q - π p) := not_lt.mp hn
        have hb : ‖κ q p‖ ≤ 4 * cw / lsq (π q) := by
          refine (hch.bound q p).trans ?_
          rw [div_le_div_iff₀ (by linarith) hL0]
          nlinarith
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  have h2 : ‖(θ q : ℂ) * ∑ p, u p * (if 4 * lsq (π q - π p) < lsq (π q) then 0 else κ q p)‖ ≤
      4 * cθ * cw / lsq (π q) ^ 2 * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |θ q| * ‖∑ p, u p * (if 4 * lsq (π q - π p) < lsq (π q) then 0 else κ q p)‖
        ≤ cθ / lsq (π q) * (4 * cw / lsq (π q) * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖) :=
          mul_le_mul (hθ q) h1 (norm_nonneg _) (by positivity)
      _ = 4 * cθ * cw / lsq (π q) ^ 2 * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖ := by
          field_simp
  have hCS : (∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖) ^ 2 ≤
      Zs s * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := by
    calc (∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖) ^ 2
        ≤ (∑ p ∈ univ.filter (fun p => κ q p ≠ 0), (1 + lsq (π p)) ^ (-s)) *
            ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := by
          apply sum_sq_le_sum_mul_sum_of_sq_le_mul
          · intro p _
            exact Real.rpow_nonneg (by linarith [lsq_nonneg (π p)]) _
          · intro p _
            exact hw p
          · intro p _
            have hpos : 0 < 1 + lsq (π p) := by linarith [lsq_nonneg (π p)]
            rw [← mul_assoc, ← Real.rpow_add hpos, neg_add_cancel, Real.rpow_zero, one_mul]
      _ ≤ Zs s * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun p _ => hw p)
          apply sum_weight_image_le _ π _ hs
          intro p hp p' hp' h
          exact hch.row q p p' (mem_filter.mp (mem_coe.mp hp)).2
            (mem_filter.mp (mem_coe.mp hp')).2 h
  calc ‖(θ q : ℂ) * ∑ p, u p * (if 4 * lsq (π q - π p) < lsq (π q) then 0 else κ q p)‖ ^ 2
      ≤ (4 * cθ * cw / lsq (π q) ^ 2 * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = 16 * (cθ * cw) ^ 2 / lsq (π q) ^ 4 *
          (∑ p ∈ univ.filter (fun p => κ q p ≠ 0), ‖u p‖) ^ 2 := by ring
    _ ≤ 16 * (cθ * cw) ^ 2 / lsq (π q) ^ 4 *
          (Zs s * ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = 16 * (cθ * cw) ^ 2 * Zs s * ∑ p, (if κ q p ≠ 0 ∧ R₀ ^ 2 < lsq (π q) then
          1 / lsq (π q) ^ 4 * ((1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) else 0) := by
        have e : ∑ p, (if κ q p ≠ 0 ∧ R₀ ^ 2 < lsq (π q) then
            1 / lsq (π q) ^ 4 * ((1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) else 0) =
            1 / lsq (π q) ^ 4 *
              ∑ p ∈ univ.filter (fun p => κ q p ≠ 0), (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := by
          rw [mul_sum, sum_filter]
          refine sum_congr rfl fun p _ => ?_
          simp only [hL, and_true]
        rw [e]
        ring

/-- **Far hops.** -/
theorem far_sum_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R₀ s : ℝ}
    (hcθ : 0 ≤ cθ) (hR₀ : 1 ≤ R₀) (hs : 3 / 2 < s) (hθ : ∀ q, |θ q| ≤ cθ / lsq (π q))
    (hθ0 : ∀ q, lsq (π q) ≤ R₀ ^ 2 → θ q = 0) (u : X → ℂ) :
    ∑ q, ‖(θ q : ℂ) * ∑ p, u p * (if 4 * lsq (π q - π p) < lsq (π q) then 0 else κ q p)‖ ^ 2 ≤
      2080 * Zs s * (cθ * cw) ^ 2 / R₀ ^ 5 * ∑ p, (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := by
  have hZ := Zs_pos hs
  have hw : ∀ p, 0 ≤ (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := fun p =>
    mul_nonneg (Real.rpow_nonneg (by linarith [lsq_nonneg (π p)]) s) (sq_nonneg _)
  calc ∑ q, ‖(θ q : ℂ) * ∑ p, u p * (if 4 * lsq (π q - π p) < lsq (π q) then 0 else κ q p)‖ ^ 2
      ≤ ∑ q, 16 * (cθ * cw) ^ 2 * Zs s * ∑ p, (if κ q p ≠ 0 ∧ R₀ ^ 2 < lsq (π q) then
          1 / lsq (π q) ^ 4 * ((1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) else 0) :=
        sum_le_sum fun q _ => far_row_sq_le π κ hch hcw θ hcθ hR₀ hs hθ hθ0 u q
    _ = 16 * (cθ * cw) ^ 2 * Zs s * ∑ p, ∑ q, (if κ q p ≠ 0 ∧ R₀ ^ 2 < lsq (π q) then
          1 / lsq (π q) ^ 4 * ((1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) else 0) := by
        rw [← mul_sum, sum_comm]
    _ ≤ 16 * (cθ * cw) ^ 2 * Zs s * ∑ p, 130 / R₀ ^ 5 * ((1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum
        intro p _
        have e : ∑ q, (if κ q p ≠ 0 ∧ R₀ ^ 2 < lsq (π q) then
            1 / lsq (π q) ^ 4 * ((1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) else 0) =
            (∑ q ∈ univ.filter (fun q => κ q p ≠ 0 ∧ R₀ ^ 2 < lsq (π q)), 1 / lsq (π q) ^ 4) *
              ((1 + lsq (π p)) ^ s * ‖u p‖ ^ 2) := by
          rw [sum_mul, sum_filter]
        rw [e]
        apply mul_le_mul_of_nonneg_right _ (hw p)
        apply sum_tail_image_le _ π _ hR₀
        · intro q hq
          exact (mem_filter.mp hq).2.2
        · intro q hq q' hq' h
          exact hch.col p q q' (mem_filter.mp (mem_coe.mp hq)).2.1
            (mem_filter.mp (mem_coe.mp hq')).2.1 h
    _ = 2080 * Zs s * (cθ * cw) ^ 2 / R₀ ^ 5 * ∑ p, (1 + lsq (π p)) ^ s * ‖u p‖ ^ 2 := by
        rw [← mul_sum]; ring

/-- The output-weighted channel operator `(θ ⊙ T_κ u)_q = θ_q Σ_p u_p κ_{qp}`. -/
noncomputable def wop (θ : X → ℝ) (u : EuclideanSpace ℂ X) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 (fun q => (θ q : ℂ) * ∑ p, u.ofLp p * κ q p)

/-- **The output-weighted channel bound**: near plus far. -/
theorem norm_wop_le (hch : IsChannel π κ cw) (hcw : 0 ≤ cw) (θ : X → ℝ) {cθ R₀ s : ℝ}
    (hcθ : 0 ≤ cθ) (hR₀ : 1 ≤ R₀) (hs : 3 / 2 < s) (hθ : ∀ q, |θ q| ≤ cθ / lsq (π q))
    (hθ0 : ∀ q, lsq (π q) ≤ R₀ ^ 2 → θ q = 0) (u : EuclideanSpace ℂ X) :
    ‖wop κ θ u‖ ≤
      39 * cθ * cw / R₀ *
          Real.sqrt (∑ p, if R₀ ^ 2 < 4 * lsq (π p) then ‖u.ofLp p‖ ^ 2 else 0) +
        Real.sqrt (2080 * Zs s) * (cθ * cw) / R₀ ^ (5 / 2 : ℝ) *
          Real.sqrt (∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2) := by
  have hZ := Zs_pos hs
  have hR0 : (0 : ℝ) < R₀ := by linarith
  have hsplit : wop κ θ u =
      WithLp.toLp 2 (fun q => (θ q : ℂ) * ∑ p, u.ofLp p *
        (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0)) +
      WithLp.toLp 2 (fun q => (θ q : ℂ) * ∑ p, u.ofLp p *
        (if 4 * lsq (π q - π p) < lsq (π q) then 0 else κ q p)) := by
    rw [← WithLp.toLp_add]
    unfold wop
    congr 1
    funext q
    simp only [Pi.add_apply]
    rw [← mul_add, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  have hnear := near_sum_le π κ hch hcw θ hcθ hR0 hθ hθ0 u.ofLp
  have hfar := far_sum_le π κ hch hcw θ hcθ hR₀ hs hθ hθ0 u.ofLp
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [EuclideanSpace.norm_eq]
    dsimp only
    calc Real.sqrt (∑ q, ‖(θ q : ℂ) * ∑ p, u.ofLp p *
            (if 4 * lsq (π q - π p) < lsq (π q) then κ q p else 0)‖ ^ 2)
        ≤ Real.sqrt ((39 * cθ * cw / R₀) ^ 2 *
            ∑ p, (if R₀ ^ 2 < 4 * lsq (π p) then ‖u.ofLp p‖ ^ 2 else 0)) :=
          Real.sqrt_le_sqrt hnear
      _ = 39 * cθ * cw / R₀ *
            Real.sqrt (∑ p, if R₀ ^ 2 < 4 * lsq (π p) then ‖u.ofLp p‖ ^ 2 else 0) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  · rw [EuclideanSpace.norm_eq]
    dsimp only
    have hS2 : 0 ≤ ∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2 := sum_nonneg fun p _ =>
      mul_nonneg (Real.rpow_nonneg (by linarith [lsq_nonneg (π p)]) s) (sq_nonneg _)
    have hR5 : (R₀ ^ (5 / 2 : ℝ)) ^ 2 = R₀ ^ 5 := by
      rw [← Real.rpow_natCast (R₀ ^ (5 / 2 : ℝ)) 2, ← Real.rpow_mul hR0.le]
      norm_num
    have heq : 2080 * Zs s * (cθ * cw) ^ 2 / R₀ ^ 5 *
          ∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2 =
        (Real.sqrt (2080 * Zs s) * (cθ * cw) / R₀ ^ (5 / 2 : ℝ) *
          Real.sqrt (∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2)) ^ 2 := by
      have e1 : (Real.sqrt (2080 * Zs s) * (cθ * cw) / R₀ ^ (5 / 2 : ℝ) *
          Real.sqrt (∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2)) ^ 2 =
          Real.sqrt (2080 * Zs s) ^ 2 * (cθ * cw) ^ 2 / (R₀ ^ (5 / 2 : ℝ)) ^ 2 *
            Real.sqrt (∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2) ^ 2 := by ring
      rw [e1, Real.sq_sqrt (by positivity), Real.sq_sqrt hS2, hR5]
    calc Real.sqrt (∑ q, ‖(θ q : ℂ) * ∑ p, u.ofLp p *
            (if 4 * lsq (π q - π p) < lsq (π q) then 0 else κ q p)‖ ^ 2)
        ≤ Real.sqrt (2080 * Zs s * (cθ * cw) ^ 2 / R₀ ^ 5 *
            ∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2) :=
          Real.sqrt_le_sqrt hfar
      _ = Real.sqrt (2080 * Zs s) * (cθ * cw) / R₀ ^ (5 / 2 : ℝ) *
            Real.sqrt (∑ p, (1 + lsq (π p)) ^ s * ‖u.ofLp p‖ ^ 2) := by
          rw [heq, Real.sqrt_sq (by positivity)]

end FSChannel
