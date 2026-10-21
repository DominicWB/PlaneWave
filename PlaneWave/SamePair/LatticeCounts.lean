import PlaneWave.SourceBand.BandTails

/-!
# Same-pair third order, part 1: lattice counts

Mathlib-level estimates on `ℤ³` behind `lem:h3` and `lem:res3` (review F4, repairs H-1 and H-2).
With the mismatch polynomial `F_c(τ) = |τ|² + 2τ·c` and `Q_c(τ) = |τ + c|² = F_c(τ) + |c|²`:

* `pin_two_sided` (`lem:pin`, both ends): `|F_c(τ)| < |τ|²/4` gives `|c|² > (9/64)|τ|²` and
  `|τ + c|² > (9/64)|τ|²`;
* `card_shifted_piece_le`, **`window_box_count`** (the counting core of `lem:slab2`): the points
  `τ` with `τ - x₀ ∈ box N`, `a ≤ F_c(τ) ≤ b` and `|τ + c| ≥ r₀` number at most
  `6 (2N+1)² ((b-a)√3/(2r₀) + 1)` (columns along the largest coordinate of `τ + c`);
* **`h3_core`** (the lattice part of eq:h3, improved): for transfers `τ` above the floor
  `|F_c(τ)| ≥ 2|τ|` and below the cap `|F_c(τ)| < 2^{J+2}`,
  `Σ_τ |F_c(τ)|⁻¹ |θ - τ|⁻² ≤ C_h3 (J + 2)(log₂⌈|θ|⌉ + 2)/|θ|`. Far transfers by the slab-weighted
  shell sums; near transfers above resonance by the Coulomb ball sum; near low transfers by the
  layer-cake, two-sided pinning and the window–ball count (no flat third term: review F4, H-2).
-/

set_option autoImplicit false

open Finset

namespace FSLattice

open FSChannel

/-! ## Two-sided pinning -/

/-- `Q_c(τ) = Σ_i (τ_i + c_i)²`. -/
noncomputable def qd (c : Fin 3 → ℝ) (τ : L3) : ℝ := ∑ i, ((τ i : ℝ) + c i) ^ 2

lemma qd_nonneg (c : Fin 3 → ℝ) (τ : L3) : 0 ≤ qd c τ := sum_nonneg fun _ _ => sq_nonneg _

lemma qd_eq (c : Fin 3 → ℝ) (τ : L3) : qd c τ = slabF c τ + ∑ i, c i ^ 2 := sum_sq_add_eq c τ

/-- **Two-sided pinning** (`lem:pin`): near resonance `|F_c(τ)| < |τ|²/4` pins both ends,
`|c|² > (9/64)|τ|²` and `|τ + c|² > (9/64)|τ|²`. -/
theorem pin_two_sided (c : Fin 3 → ℝ) (τ : L3) (h : |slabF c τ| < lsq τ / 4) :
    9 / 64 * lsq τ < ∑ i, c i ^ 2 ∧ 9 / 64 * lsq τ < qd c τ := by
  refine ⟨pin_core c τ h, ?_⟩
  set c' : Fin 3 → ℝ := fun i => c i + τ i with hc'
  have hF : slabF c' (-τ) = -slabF c τ := by
    simp only [slabF, lsq, c', Pi.neg_apply, Int.cast_neg, Fin.sum_univ_three]; ring
  have hl : lsq (-τ) = lsq τ := by simp [lsq]
  have h' : |slabF c' (-τ)| < lsq (-τ) / 4 := by rw [hF, abs_neg, hl]; exact h
  have h2 := pin_core c' (-τ) h'
  rw [hl] at h2
  have e : ∑ i, c' i ^ 2 = qd c τ := by
    unfold qd; refine sum_congr rfl fun i _ => ?_; simp only [c']; ring
  linarith [e]

/-! ## The window–ball count -/

lemma exists_big_coord (y : Fin 3 → ℝ) {r : ℝ} (_hr : 0 ≤ r) (h : r ^ 2 ≤ ∑ i, y i ^ 2) :
    ∃ i, r / Real.sqrt 3 ≤ |y i| := by
  by_contra hno
  push Not at hno
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hb : ∀ i, y i ^ 2 < r ^ 2 / 3 := fun i => by
    have h1 := hno i
    have h2 : |y i| ^ 2 < (r / Real.sqrt 3) ^ 2 := pow_lt_pow_left₀ h1 (abs_nonneg _) two_ne_zero
    rw [sq_abs, div_pow, hs3] at h2
    exact h2
  rw [Fin.sum_univ_three] at h
  linarith [hb 0, hb 1, hb 2]

/-- A one-signed piece of a shifted window, in a box about `x₀`. -/
lemma card_shifted_piece_le (c : Fin 3 → ℝ) (x₀ : L3) (N : ℕ) (i : Fin 3) {a b s : ℝ}
    (hs : 0 < s) (hab : a ≤ b) (P : Finset L3)
    (hP : ∀ τ ∈ P, τ - x₀ ∈ box N ∧ a ≤ slabF c τ ∧ slabF c τ ≤ b)
    (hsign : ∀ τ ∈ P, ∀ τ' ∈ P, s ≤ |((τ i : ℝ) + c i) + ((τ' i : ℝ) + c i)|) :
    (P.card : ℝ) ≤ (2 * N + 1) ^ 2 * ((b - a) / s + 1) := by
  classical
  set c' : Fin 3 → ℝ := fun l => c l + (x₀ l : ℝ) with hc'
  set P' := P.image (fun τ => τ - x₀)
  have hinj : Set.InjOn (fun τ : L3 => τ - x₀) P := fun τ _ τ' _ h => sub_left_injective h
  have hcard : P'.card = P.card := card_image_of_injOn hinj
  have hbox : P' ⊆ box N := by
    intro τ' hτ'
    obtain ⟨τ, hτ, rfl⟩ := mem_image.mp hτ'
    exact (hP τ hτ).1
  have hshift : ∀ τ : L3, slabF c' (τ - x₀) = slabF c τ + ∑ l, c l ^ 2 - ∑ l, c' l ^ 2 := by
    intro τ
    have h1 := sum_sq_add_eq c' (τ - x₀)
    have h2 := sum_sq_add_eq c τ
    have h3 : ∑ l, (((τ - x₀) l : ℝ) + c' l) ^ 2 = ∑ l, ((τ l : ℝ) + c l) ^ 2 := by
      refine sum_congr rfl fun l _ => ?_
      simp only [c', Pi.sub_apply, Int.cast_sub]; ring
    linarith
  have hcoord : ∀ τ : L3, (((τ - x₀) i : ℤ) : ℝ) + c' i = (τ i : ℝ) + c i := by
    intro τ; simp only [c', Pi.sub_apply, Int.cast_sub]; ring
  have h := FSBand.card_piece_le' c' i hs (by linarith : (0 : ℝ) ≤ b - a) N P' hbox (by
    intro τ₁' h₁ τ₂' h₂
    obtain ⟨τ₁, hτ₁, rfl⟩ := mem_image.mp h₁
    obtain ⟨τ₂, hτ₂, rfl⟩ := mem_image.mp h₂
    rw [hshift, hshift]
    obtain ⟨-, ha1, hb1⟩ := hP τ₁ hτ₁
    obtain ⟨-, ha2, hb2⟩ := hP τ₂ hτ₂
    rw [abs_le]; constructor <;> linarith) (by
    intro τ₁' h₁ τ₂' h₂
    obtain ⟨τ₁, hτ₁, rfl⟩ := mem_image.mp h₁
    obtain ⟨τ₂, hτ₂, rfl⟩ := mem_image.mp h₂
    rw [hcoord, hcoord]
    exact hsign τ₁ hτ₁ τ₂ hτ₂)
  rw [hcard] at h
  calc (P.card : ℝ) ≤ (2 * N + 1) ^ 2 * (min ((b - a) / s) (2 * N) + 1) := h
    _ ≤ (2 * N + 1) ^ 2 * ((b - a) / s + 1) := by gcongr; exact min_le_left _ _

/-- **The window–ball count** (`lem:slab2`, its counting core): the lattice points `τ` with
`τ - x₀ ∈ box N`, `a ≤ F_c(τ) ≤ b` and `|τ + c|² ≥ r₀² > 0` number at most
`6 (2N+1)² ((b - a)√3/(2r₀) + 1)`. -/
theorem window_box_count (c : Fin 3 → ℝ) (x₀ : L3) (N : ℕ) {a b r₀ : ℝ} (hr₀ : 0 < r₀)
    (hab : a ≤ b) (S : Finset L3)
    (hS : ∀ τ ∈ S, τ - x₀ ∈ box N ∧ a ≤ slabF c τ ∧ slabF c τ ≤ b ∧ r₀ ^ 2 ≤ qd c τ) :
    (S.card : ℝ) ≤ 6 * (2 * N + 1) ^ 2 * ((b - a) * Real.sqrt 3 / (2 * r₀) + 1) := by
  classical
  have hs3 : 0 < Real.sqrt 3 := by positivity
  set s := 2 * r₀ / Real.sqrt 3 with hs_def
  have hs : 0 < s := by positivity
  set t := r₀ / Real.sqrt 3 with ht_def
  have ht : 0 < t := by positivity
  have hst : s = 2 * t := by rw [hs_def, ht_def]; ring
  let pos : Fin 3 → Finset L3 := fun i => S.filter fun τ => t ≤ (τ i : ℝ) + c i
  let neg : Fin 3 → Finset L3 := fun i => S.filter fun τ => (τ i : ℝ) + c i ≤ -t
  have hcover : S ⊆ (univ : Finset (Fin 3)).biUnion (fun i => pos i ∪ neg i) := by
    intro τ hτ
    obtain ⟨-, -, -, hq⟩ := hS τ hτ
    obtain ⟨i, hi⟩ := exists_big_coord (fun i => (τ i : ℝ) + c i) hr₀.le hq
    rw [mem_biUnion]
    refine ⟨i, mem_univ _, ?_⟩
    rcases le_abs.mp hi with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hτ, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hτ, by linarith⟩)
  have hpiece : ∀ i, ((pos i).card : ℝ) ≤ (2 * N + 1) ^ 2 * ((b - a) / s + 1) ∧
      ((neg i).card : ℝ) ≤ (2 * N + 1) ^ 2 * ((b - a) / s + 1) := by
    intro i
    constructor
    · refine card_shifted_piece_le c x₀ N i hs hab (pos i)
        (fun τ hτ => ⟨(hS τ (mem_filter.mp hτ).1).1, (hS τ (mem_filter.mp hτ).1).2.1,
          (hS τ (mem_filter.mp hτ).1).2.2.1⟩) ?_
      intro τ hτ τ' hτ'
      have e1 := (mem_filter.mp hτ).2
      have e2 := (mem_filter.mp hτ').2
      rw [abs_of_nonneg (by linarith)]
      linarith
    · refine card_shifted_piece_le c x₀ N i hs hab (neg i)
        (fun τ hτ => ⟨(hS τ (mem_filter.mp hτ).1).1, (hS τ (mem_filter.mp hτ).1).2.1,
          (hS τ (mem_filter.mp hτ).1).2.2.1⟩) ?_
      intro τ hτ τ' hτ'
      have e1 := (mem_filter.mp hτ).2
      have e2 := (mem_filter.mp hτ').2
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hc1 : (S.card : ℝ) ≤ ∑ i : Fin 3, (((pos i).card : ℝ) + ((neg i).card : ℝ)) := by
    have h1 := card_le_card hcover
    have h2 := card_biUnion_le (s := (univ : Finset (Fin 3))) (t := fun i => pos i ∪ neg i)
    have h3 : ∀ i ∈ (univ : Finset (Fin 3)), (pos i ∪ neg i).card ≤ (pos i).card + (neg i).card :=
      fun i _ => card_union_le _ _
    have h4 := sum_le_sum h3
    have h5 : S.card ≤ ∑ i : Fin 3, ((pos i).card + (neg i).card) := h1.trans (h2.trans h4)
    exact_mod_cast h5
  have hc2 : ∑ i : Fin 3, (((pos i).card : ℝ) + ((neg i).card : ℝ)) ≤
      ∑ _i : Fin 3, 2 * ((2 * N + 1) ^ 2 * ((b - a) / s + 1)) :=
    sum_le_sum fun i _ => by linarith [(hpiece i).1, (hpiece i).2]
  have e : (b - a) / s = (b - a) * Real.sqrt 3 / (2 * r₀) := by
    rw [hs_def]; field_simp
  calc (S.card : ℝ) ≤ _ := hc1.trans hc2
    _ = 6 * (2 * N + 1) ^ 2 * ((b - a) / s + 1) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
    _ = _ := by rw [e]

/-! ## The core sum of eq:h3 -/

/-- Splitting a sum along a (possibly overlapping) cover by finitely many pieces. -/
lemma sum_le_sum_shells {α : Type*} (T : Finset α) (f : α → ℝ) (hf : ∀ x ∈ T, 0 ≤ f x)
    (P : ℕ → α → Prop) [∀ i, DecidablePred (P i)] (I : ℕ) (hP : ∀ x ∈ T, ∃ i ≤ I, P i x) :
    ∑ x ∈ T, f x ≤ ∑ i ∈ range (I + 1), ∑ x ∈ T.filter (P i), f x := by
  rw [show ∑ i ∈ range (I + 1), ∑ x ∈ T.filter (P i), f x =
      ∑ i ∈ range (I + 1), ∑ x ∈ T, (if P i x then f x else 0) from
      sum_congr rfl fun i _ => sum_filter _ _, sum_comm]
  refine sum_le_sum fun x hx => ?_
  obtain ⟨i, hiI, hi⟩ := hP x hx
  calc f x = (if P i x then f x else 0) := (if_pos hi).symm
    _ ≤ ∑ j ∈ range (I + 1), (if P j x then f x else 0) :=
        single_le_sum (f := fun j => if P j x then f x else 0)
          (fun j _ => by split_ifs; exacts [hf x hx, le_rfl]) (mem_range.mpr (by omega))

lemma one_le_rho {θ : L3} (h : 1 ≤ lsq θ) : 1 ≤ rho θ := by
  unfold rho
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt h

/-- `Σ_{i<K} 2^i/max(x², 4^i) ≤ 4/x` for `x ≥ 1`. -/
lemma sum_geom_max_le {x : ℝ} (hx : 1 ≤ x) (K : ℕ) :
    ∑ i ∈ range K, (2 : ℝ) ^ i / max (x ^ 2) (4 ^ i) ≤ 4 / x := by
  have hx0 : 0 < x := by linarith
  rw [← sum_filter_add_sum_filter_not (range K) (fun i => (2 : ℝ) ^ i ≤ x),
    show (4 : ℝ) / x = 2 / x + 2 / x by ring]
  refine add_le_add ?_ ?_
  · calc _ ≤ ∑ i ∈ (range K).filter (fun i => (2 : ℝ) ^ i ≤ x), (2 : ℝ) ^ i * (1 / x ^ 2) := by
          refine sum_le_sum fun i _ => ?_
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity)
            (le_max_left _ _)) (by positivity)
      _ = (∑ i ∈ (range K).filter (fun i => (2 : ℝ) ^ i ≤ x), (2 : ℝ) ^ i) * (1 / x ^ 2) := by
          rw [sum_mul]
      _ ≤ 2 * x * (1 / x ^ 2) := by
          gcongr; exact FSBand.sum_pow_two_le hx0.le K
      _ = 2 / x := by field_simp
  · calc _ ≤ ∑ i ∈ (range K).filter (fun i => ¬ (2 : ℝ) ^ i ≤ x), ((2 : ℝ) ^ i)⁻¹ := by
          refine sum_le_sum fun i _ => ?_
          have h4 : (4 : ℝ) ^ i = (2 ^ i) ^ 2 := (FSBand.two_pow_sq i).symm
          have h0 : (0 : ℝ) < 2 ^ i := by positivity
          calc (2 : ℝ) ^ i / max (x ^ 2) (4 ^ i) ≤ 2 ^ i / 4 ^ i :=
                div_le_div_of_nonneg_left h0.le (by positivity) (le_max_right _ _)
            _ = (2 ^ i)⁻¹ := by rw [h4]; field_simp
      _ = ∑ i ∈ (range K).filter (fun i => x < (2 : ℝ) ^ i), ((2 : ℝ) ^ i)⁻¹ := by
          congr 1; ext i; simp [not_le]
      _ ≤ 2 / x := FSBand.sum_inv_pow_two_le hx0 K

/-- Far transfers: `|θ - τ|⁻² ≤ 64/max(|θ|², |τ|²)` when `|θ|² ≤ 4|θ - τ|²`. -/
lemma far_inv_le {θ τ : L3} (hθ : 1 ≤ lsq θ) (h : lsq θ ≤ 4 * lsq (θ - τ)) :
    1 / lsq (θ - τ) ≤ 64 / max (lsq θ) (lsq τ) := by
  have hd : 0 < lsq (θ - τ) := by linarith
  have hm0 : 0 < max (lsq θ) (lsq τ) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  rw [div_le_div_iff₀ hd hm0, one_mul]
  rcases le_or_gt (lsq τ) (16 * lsq θ) with h1 | h1
  · have : max (lsq θ) (lsq τ) ≤ 16 * lsq θ := max_le (by linarith) h1
    linarith
  · have hmax : max (lsq θ) (lsq τ) = lsq τ := max_eq_right (by linarith)
    rw [hmax]
    have hr1 := rho_le_add_rho_sub τ θ
    have hr2 : rho (τ - θ) = rho (θ - τ) := by unfold rho; rw [lsq_sub_comm]
    have hθ0 := rho_nonneg θ
    have hτ0 := rho_nonneg τ
    have hsq : (4 * rho θ) ^ 2 < rho τ ^ 2 := by rw [mul_pow, rho_sq, rho_sq]; linarith
    have hτθ : 4 * rho θ < rho τ := (pow_lt_pow_iff_left₀ (by positivity) hτ0 two_ne_zero).mp hsq
    have h3 : 3 / 4 * rho τ ≤ rho (θ - τ) := by linarith
    have h4 : (3 / 4 * rho τ) ^ 2 ≤ rho (θ - τ) ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    rw [mul_pow, rho_sq, rho_sq] at h4
    nlinarith

/-- **The far part** of the core sum. -/
lemma h3_far_le (c : Fin 3 → ℝ) (θ : L3) (hθ : 1 ≤ lsq θ) {J : ℕ} (T : Finset L3)
    (hT : ∀ τ ∈ T, 1 ≤ lsq τ ∧ 2 * rho τ ≤ |slabF c τ| ∧ |slabF c τ| < 2 ^ (J + 1) * 2)
    (hfar : ∀ τ ∈ T, lsq θ ≤ 4 * lsq (θ - τ)) :
    ∑ τ ∈ T, 1 / |slabF c τ| * (1 / lsq (θ - τ)) ≤
      64 * (11000 * (2 * J + 3)) * (4 / rho θ) := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ τ ∈ T, lsq τ ≤ B :=
    ⟨∑ τ ∈ T, lsq τ, fun τ hτ => single_le_sum (fun x _ => lsq_nonneg x) hτ⟩
  set I := Nat.log 2 ⌈B⌉₊
  have hshell : ∀ τ ∈ T, ∃ i ≤ I, (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1) := by
    intro τ hτ
    obtain ⟨i, hi1, hi2⟩ := FSNormal.exists_shell (hT τ hτ).1
    refine ⟨i, ?_, hi1, hi2⟩
    have h2 : (2 : ℝ) ^ i ≤ 4 ^ i := pow_le_pow_left₀ (by norm_num) (by norm_num) i
    have h3 : ((2 ^ i : ℕ) : ℝ) ≤ (⌈B⌉₊ : ℝ) := by
      push_cast; linarith [Nat.le_ceil B, hB τ hτ]
    exact Nat.le_log_of_pow_le (by norm_num) (by exact_mod_cast h3)
  have hnn : ∀ τ ∈ T, 0 ≤ 1 / |slabF c τ| * (1 / lsq (θ - τ)) := fun τ _ => by
    have := lsq_nonneg (θ - τ); positivity
  refine (sum_le_sum_shells T _ hnn (fun i τ => (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1)) I
    hshell).trans ?_
  have hper : ∀ i ∈ range (I + 1),
      ∑ τ ∈ T.filter (fun τ => (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1)),
        1 / |slabF c τ| * (1 / lsq (θ - τ)) ≤
      64 * (11000 * (2 * J + 3)) * ((2 : ℝ) ^ i / max (rho θ ^ 2) (4 ^ i)) := by
    intro i _
    set Ti := T.filter (fun τ => (4 : ℝ) ^ i ≤ lsq τ ∧ lsq τ ≤ 4 ^ (i + 1))
    rw [rho_sq]
    have hm : 0 < max (lsq θ) (4 ^ i) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have h1 : ∀ τ ∈ Ti, 1 / |slabF c τ| * (1 / lsq (θ - τ)) ≤
        64 / max (lsq θ) (4 ^ i) * (1 / |slabF c τ|) := by
      intro τ hτ
      obtain ⟨hτT, hs1, -⟩ := mem_filter.mp hτ
      have hf := far_inv_le hθ (hfar τ hτT)
      have hmm : max (lsq θ) (4 ^ i) ≤ max (lsq θ) (lsq τ) := max_le_max le_rfl hs1
      have h64 : 64 / max (lsq θ) (lsq τ) ≤ 64 / max (lsq θ) (4 ^ i) :=
        div_le_div_of_nonneg_left (by norm_num) hm hmm
      have hF : 0 ≤ 1 / |slabF c τ| := by positivity
      calc 1 / |slabF c τ| * (1 / lsq (θ - τ)) ≤ 1 / |slabF c τ| * (64 / max (lsq θ) (4 ^ i)) :=
            mul_le_mul_of_nonneg_left (hf.trans h64) hF
        _ = _ := by ring
    refine (sum_le_sum h1).trans ?_
    rw [← mul_sum]
    have hρ : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have h := slab_inv_sum_le c hρ (by positivity : (0 : ℝ) < 2 ^ (i + 1)) (J := J) Ti (by
      intro τ hτ
      obtain ⟨hτT, hs1, hs2⟩ := mem_filter.mp hτ
      obtain ⟨-, hfl, hcap⟩ := hT τ hτT
      have e4 : ((2 : ℝ) ^ i) ^ 2 = 4 ^ i := FSBand.two_pow_sq i
      refine ⟨by rw [e4]; exact hs1, by rw [e4, ← pow_succ']; exact hs2, ?_, ?_⟩
      · have hr : (2 : ℝ) ^ i ≤ rho τ := by
          unfold rho; apply Real.le_sqrt_of_sq_le; rw [e4]; exact hs1
        rw [pow_succ]; linarith
      · calc |slabF c τ| < 2 ^ (J + 1) * 2 := hcap
          _ ≤ 2 ^ (J + 1) * 2 ^ (i + 1) := by
              gcongr
              calc (2 : ℝ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega))
    have e : 11000 * ((2 : ℝ) ^ i) ^ 2 * (2 / 2 ^ (i + 1) + 2 * (J + 1) / 2 ^ i) =
        11000 * (2 * J + 3) * 2 ^ i := by
      field_simp; ring
    rw [e] at h
    calc 64 / max (lsq θ) (4 ^ i) * ∑ τ ∈ Ti, 1 / |slabF c τ|
        ≤ 64 / max (lsq θ) (4 ^ i) * (11000 * (2 * J + 3) * 2 ^ i) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by ring
  refine (sum_le_sum hper).trans ?_
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_geom_max_le (one_le_rho hθ) (I + 1)) (by positivity)

/-- **The near part above resonance** of the core sum (Coulomb ball sum). -/
lemma h3_kin_le (c : Fin 3 → ℝ) (θ : L3) (hθ : 1 ≤ lsq θ) (T : Finset L3)
    (h1 : ∀ τ ∈ T, 1 ≤ lsq τ) (hnear : ∀ τ ∈ T, 4 * lsq (θ - τ) < lsq θ)
    (hkin : ∀ τ ∈ T, lsq τ ≤ 4 * |slabF c τ|) :
    ∑ τ ∈ T, 1 / |slabF c τ| * (1 / lsq (θ - τ)) ≤ 208 / rho θ := by
  classical
  have hρ := one_le_rho hθ
  have hρ2 : rho θ ^ 2 = lsq θ := rho_sq θ
  have hterm : ∀ τ ∈ T, 1 / |slabF c τ| * (1 / lsq (θ - τ)) ≤ 16 / lsq θ * (1 / lsq (θ - τ)) := by
    intro τ hτ
    have hg := near_geom (hnear τ hτ)
    have hτ1 := h1 τ hτ
    have hF : 0 < |slabF c τ| := by linarith [hkin τ hτ]
    have hd : 0 ≤ 1 / lsq (θ - τ) := by have := lsq_nonneg (θ - τ); positivity
    have : 1 / |slabF c τ| ≤ 16 / lsq θ := by
      rw [div_le_div_iff₀ hF (by linarith)]; linarith [hkin τ hτ, hg.1]
    exact mul_le_mul_of_nonneg_right this hd
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have hball : ∑ τ ∈ T, 1 / lsq (θ - τ) ≤ 26 * (rho θ / 2) := by
    rw [← sum_filter_add_sum_filter_not T (fun τ => θ - τ = 0)]
    have hz : ∑ τ ∈ T.filter (fun τ => θ - τ = 0), 1 / lsq (θ - τ) = 0 :=
      sum_eq_zero fun τ hτ => by rw [(mem_filter.mp hτ).2, lsq_zero, div_zero]
    rw [hz, zero_add]
    apply sum_inv_lsq_image_le _ (fun τ => θ - τ) _ (by positivity)
    · intro τ hτ; exact (mem_filter.mp hτ).2
    · intro τ hτ
      have := hnear τ (mem_filter.mp hτ).1
      rw [div_pow, hρ2]; linarith
    · intro τ _ τ' _ h
      exact sub_right_injective h
  calc 16 / lsq θ * ∑ τ ∈ T, 1 / lsq (θ - τ) ≤ 16 / lsq θ * (26 * (rho θ / 2)) :=
        mul_le_mul_of_nonneg_left hball (by positivity)
    _ = 208 / rho θ := by rw [← hρ2]; field_simp; ring

/-- **The near low part** of the core sum: layer-cake in `|F_c|`, two-sided pinning and the
window–ball count on dyadic distance shells about `θ`. -/
lemma h3_low_le (c : Fin 3 → ℝ) (θ : L3) (hθ : 1 ≤ lsq θ) {J : ℕ} (T : Finset L3)
    (hT : ∀ τ ∈ T, 1 ≤ lsq τ ∧ 2 * rho τ ≤ |slabF c τ| ∧ |slabF c τ| < 2 ^ (J + 1) * 2)
    (hnear : ∀ τ ∈ T, 4 * lsq (θ - τ) < lsq θ) (hlow : ∀ τ ∈ T, 4 * |slabF c τ| < lsq τ) :
    ∑ τ ∈ T, 1 / |slabF c τ| * (1 / lsq (θ - τ)) ≤
      3000 * (J + 2) * (Nat.log 2 ⌈rho θ⌉₊ + 1) / rho θ := by
  classical
  have hρ := one_le_rho hθ
  have hρ0 : 0 < rho θ := by linarith
  have hρ2 : rho θ ^ 2 = lsq θ := rho_sq θ
  set Kθ := Nat.log 2 ⌈rho θ⌉₊
  -- step 1: the layer-cake in `|F_c|` with floor `|θ|`
  have hlayer : ∀ τ ∈ T, 1 / |slabF c τ| ≤ 1 / rho θ * ∑ l ∈ range (J + 2),
      (1 / 2 : ℝ) ^ l * (if |slabF c τ| < 2 ^ (l + 1) * rho θ then 1 else 0) := by
    intro τ hτ
    obtain ⟨hτ1, hfl, hcap⟩ := hT τ hτ
    have hg := near_geom (hnear τ hτ)
    have hρτ : rho θ < 2 * rho τ := by
      have h1 : rho θ ^ 2 < (2 * rho τ) ^ 2 := by rw [mul_pow, rho_sq, rho_sq]; linarith [hg.1]
      exact (pow_lt_pow_iff_left₀ (rho_nonneg θ) (by have := rho_nonneg τ; positivity)
        two_ne_zero).mp h1
    refine inv_le_layer_sum hρ0 (by linarith) (J := J + 1) ?_
    calc |slabF c τ| < 2 ^ (J + 1) * 2 := hcap
      _ = 2 ^ (J + 1 + 1) * 1 := by ring
      _ ≤ 2 ^ (J + 1 + 1) * rho θ := by gcongr
  have hnn : ∀ τ ∈ T, 0 ≤ 1 / lsq (θ - τ) := fun τ _ => by have := lsq_nonneg (θ - τ); positivity
  have hstep1 : ∑ τ ∈ T, 1 / |slabF c τ| * (1 / lsq (θ - τ)) ≤
      1 / rho θ * ∑ l ∈ range (J + 2), (1 / 2 : ℝ) ^ l *
        ∑ τ ∈ T.filter (fun τ => |slabF c τ| < 2 ^ (l + 1) * rho θ), 1 / lsq (θ - τ) := by
    calc ∑ τ ∈ T, 1 / |slabF c τ| * (1 / lsq (θ - τ))
        ≤ ∑ τ ∈ T, (1 / rho θ * ∑ l ∈ range (J + 2),
            (1 / 2 : ℝ) ^ l * (if |slabF c τ| < 2 ^ (l + 1) * rho θ then 1 else 0)) *
              (1 / lsq (θ - τ)) :=
          sum_le_sum fun τ hτ => mul_le_mul_of_nonneg_right (hlayer τ hτ) (hnn τ hτ)
      _ = _ := by
          simp_rw [mul_assoc (1 / rho θ)]
          rw [← mul_sum]
          congr 1
          simp_rw [sum_mul]
          rw [sum_comm]
          refine sum_congr rfl fun l _ => ?_
          rw [mul_sum, sum_filter]
          refine sum_congr rfl fun τ _ => ?_
          split_ifs <;> ring
  refine hstep1.trans ?_
  -- step 2: each layer by dyadic distance shells and the window–ball count
  have hinner : ∀ l ∈ range (J + 2),
      ∑ τ ∈ T.filter (fun τ => |slabF c τ| < 2 ^ (l + 1) * rho θ), 1 / lsq (θ - τ) ≤
        3000 * 2 ^ l * (Kθ + 1) := by
    intro l _
    set Tl := T.filter (fun τ => |slabF c τ| < 2 ^ (l + 1) * rho θ)
    rw [← sum_filter_add_sum_filter_not Tl (fun τ => θ - τ = 0)]
    have hz : ∑ τ ∈ Tl.filter (fun τ => θ - τ = 0), 1 / lsq (θ - τ) = 0 :=
      sum_eq_zero fun τ hτ => by rw [(mem_filter.mp hτ).2, lsq_zero, div_zero]
    rw [hz, zero_add]
    set Tl' := Tl.filter (fun τ => ¬ θ - τ = 0)
    have hshell : ∀ τ ∈ Tl', ∃ k ≤ Kθ, (4 : ℝ) ^ k ≤ lsq (θ - τ) ∧ lsq (θ - τ) ≤ 4 ^ (k + 1) := by
      intro τ hτ
      obtain ⟨hτl, hne⟩ := mem_filter.mp hτ
      have hτT := (mem_filter.mp hτl).1
      have h1 : 1 ≤ lsq (θ - τ) := FSNormal.one_le_latticeNormSq hne
      obtain ⟨k, hk1, hk2⟩ := FSNormal.exists_shell h1
      refine ⟨k, ?_, hk1, hk2⟩
      have h4 : ((2 : ℝ) ^ k) ^ 2 < rho θ ^ 2 := by
        rw [FSBand.two_pow_sq, hρ2]; linarith [hnear τ hτT]
      have h2 : (2 : ℝ) ^ k < rho θ :=
        (pow_lt_pow_iff_left₀ (by positivity) (rho_nonneg θ) two_ne_zero).mp h4
      have h3 : ((2 ^ k : ℕ) : ℝ) ≤ (⌈rho θ⌉₊ : ℝ) := by
        push_cast; linarith [Nat.le_ceil (rho θ)]
      exact Nat.le_log_of_pow_le (by norm_num) (by exact_mod_cast h3)
    refine (sum_le_sum_shells Tl' _ (fun τ hτ => hnn τ (mem_filter.mp (mem_filter.mp hτ).1).1)
      (fun k τ => (4 : ℝ) ^ k ≤ lsq (θ - τ) ∧ lsq (θ - τ) ≤ 4 ^ (k + 1)) Kθ hshell).trans ?_
    have hper : ∀ k ∈ range (Kθ + 1),
        ∑ τ ∈ Tl'.filter (fun τ => (4 : ℝ) ^ k ≤ lsq (θ - τ) ∧ lsq (θ - τ) ≤ 4 ^ (k + 1)),
          1 / lsq (θ - τ) ≤ 3000 * 2 ^ l := by
      intro k _
      set S := Tl'.filter (fun τ => (4 : ℝ) ^ k ≤ lsq (θ - τ) ∧ lsq (θ - τ) ≤ 4 ^ (k + 1))
      have h1 : ∑ τ ∈ S, 1 / lsq (θ - τ) ≤ ∑ _τ ∈ S, 1 / (4 : ℝ) ^ k :=
        sum_le_sum fun τ hτ => one_div_le_one_div_of_le (by positivity) (mem_filter.mp hτ).2.1
      rw [sum_const, nsmul_eq_mul] at h1
      have hr₀ : 0 < 3 * rho θ / 16 := by positivity
      have hcount := window_box_count c θ (2 ^ (k + 1)) hr₀
        (by have : (0 : ℝ) ≤ 2 ^ (l + 1) * rho θ := by positivity
            linarith : -(2 ^ (l + 1) * rho θ) ≤ 2 ^ (l + 1) * rho θ) S (by
        intro τ hτ
        obtain ⟨hτl', hs1, hs2⟩ := mem_filter.mp hτ
        obtain ⟨hτl, -⟩ := mem_filter.mp hτl'
        obtain ⟨hτT, hFl⟩ := mem_filter.mp hτl
        refine ⟨?_, ?_, ?_, ?_⟩
        · apply mem_box_of_lsq_le
          rw [lsq_sub_comm]
          push_cast
          rw [FSBand.two_pow_sq]
          exact hs2
        · linarith [neg_abs_le (slabF c τ)]
        · linarith [le_abs_self (slabF c τ)]
        · have hg := near_geom (hnear τ hτT)
          have hp := (pin_two_sided c τ (by linarith [hlow τ hτT])).2
          rw [div_pow, mul_pow, hρ2]
          nlinarith)
      have hs3 : Real.sqrt 3 ≤ 7 / 4 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      have hratio : (2 ^ (l + 1) * rho θ - -(2 ^ (l + 1) * rho θ)) * Real.sqrt 3 /
          (2 * (3 * rho θ / 16)) ≤ 19 * 2 ^ l := by
        rw [div_le_iff₀ (by positivity)]
        have : (2 : ℝ) ^ (l + 1) = 2 * 2 ^ l := by ring
        rw [this]
        have h2l : (0 : ℝ) < 2 ^ l := by positivity
        nlinarith [mul_pos h2l hρ0]
      have hbox : (2 * ((2 ^ (k + 1) : ℕ) : ℝ) + 1) ^ 2 ≤ 25 * 4 ^ k := by
        push_cast
        have h1k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        have : 2 * (2 : ℝ) ^ (k + 1) + 1 ≤ 5 * 2 ^ k := by rw [pow_succ]; linarith
        calc (2 * (2 : ℝ) ^ (k + 1) + 1) ^ 2 ≤ (5 * 2 ^ k) ^ 2 :=
              pow_le_pow_left₀ (by positivity) this 2
          _ = 25 * 4 ^ k := by rw [mul_pow, FSBand.two_pow_sq]; ring
      have hrat0 : 0 ≤ (2 ^ (l + 1) * rho θ - -(2 ^ (l + 1) * rho θ)) * Real.sqrt 3 /
          (2 * (3 * rho θ / 16)) := by
        apply div_nonneg _ (by positivity)
        apply mul_nonneg _ (Real.sqrt_nonneg _)
        have : (0 : ℝ) ≤ 2 ^ (l + 1) * rho θ := by positivity
        linarith
      have hcard : (S.card : ℝ) ≤ 6 * (25 * 4 ^ k) * (19 * 2 ^ l + 1) := by
        refine hcount.trans ?_
        gcongr
      calc ∑ τ ∈ S, 1 / lsq (θ - τ) ≤ (S.card : ℝ) * (1 / 4 ^ k) := h1
        _ ≤ 6 * (25 * 4 ^ k) * (19 * 2 ^ l + 1) * (1 / 4 ^ k) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 150 * (19 * 2 ^ l + 1) := by field_simp; ring
        _ ≤ 3000 * 2 ^ l := by
            have : (1 : ℝ) ≤ 2 ^ l := one_le_pow₀ (by norm_num)
            nlinarith
    calc ∑ k ∈ range (Kθ + 1), ∑ τ ∈ Tl'.filter
          (fun τ => (4 : ℝ) ^ k ≤ lsq (θ - τ) ∧ lsq (θ - τ) ≤ 4 ^ (k + 1)), 1 / lsq (θ - τ)
        ≤ ∑ _k ∈ range (Kθ + 1), (3000 : ℝ) * 2 ^ l := sum_le_sum hper
      _ = 3000 * 2 ^ l * (Kθ + 1) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  calc 1 / rho θ * ∑ l ∈ range (J + 2), (1 / 2 : ℝ) ^ l *
        ∑ τ ∈ T.filter (fun τ => |slabF c τ| < 2 ^ (l + 1) * rho θ), 1 / lsq (θ - τ)
      ≤ 1 / rho θ * ∑ l ∈ range (J + 2), (1 / 2 : ℝ) ^ l * (3000 * 2 ^ l * (Kθ + 1)) := by
        gcongr with l hl
        exact hinner l hl
    _ = 1 / rho θ * ∑ _l ∈ range (J + 2), (3000 : ℝ) * (Kθ + 1) := by
        congr 1
        refine sum_congr rfl fun l _ => ?_
        rw [show (1 / 2 : ℝ) ^ l * (3000 * 2 ^ l * (Kθ + 1)) =
          ((1 / 2 : ℝ) ^ l * 2 ^ l) * (3000 * (Kθ + 1)) by ring, ← mul_pow]
        norm_num
    _ = 3000 * (J + 2) * (Kθ + 1) / rho θ := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; field_simp

/-- The numerical constant of eq:h3's core sum. -/
def Ch3 : ℝ := 3000000

/-- **The core sum of eq:h3** (improved: no flat third term). For transfers above the floor
`|F_c(τ)| ≥ 2|τ|` and below the cap `|F_c(τ)| < 2^{J+2}`,
`Σ_τ |F_c(τ)|⁻¹ |θ - τ|⁻² ≤ C_h3 (J + 2)(⌊log₂⌈|θ|⌉⌋ + 2)/|θ|` (`τ = θ` contributes `0`). -/
theorem h3_core (c : Fin 3 → ℝ) (θ : L3) (hθ : 1 ≤ lsq θ) {J : ℕ} (T : Finset L3)
    (hT : ∀ τ ∈ T, 1 ≤ lsq τ ∧ 2 * rho τ ≤ |slabF c τ| ∧ |slabF c τ| < 2 ^ (J + 1) * 2) :
    ∑ τ ∈ T, 1 / |slabF c τ| * (1 / lsq (θ - τ)) ≤
      Ch3 * (J + 2) * (Nat.log 2 ⌈rho θ⌉₊ + 2) / rho θ := by
  classical
  have hρ := one_le_rho hθ
  have hρ0 : 0 < rho θ := by linarith
  rw [← sum_filter_add_sum_filter_not T (fun τ => lsq θ ≤ 4 * lsq (θ - τ))]
  have hA := h3_far_le c θ hθ (T.filter (fun τ => lsq θ ≤ 4 * lsq (θ - τ)))
    (fun τ hτ => hT τ (mem_filter.mp hτ).1) (fun τ hτ => (mem_filter.mp hτ).2)
  set Tn := T.filter (fun τ => ¬ lsq θ ≤ 4 * lsq (θ - τ))
  have hTn : ∀ τ ∈ Tn, 4 * lsq (θ - τ) < lsq θ := fun τ hτ => not_le.mp (mem_filter.mp hτ).2
  rw [← sum_filter_add_sum_filter_not Tn (fun τ => lsq τ ≤ 4 * |slabF c τ|)]
  have hB1 := h3_kin_le c θ hθ (Tn.filter (fun τ => lsq τ ≤ 4 * |slabF c τ|))
    (fun τ hτ => (hT τ (mem_filter.mp (mem_filter.mp hτ).1).1).1)
    (fun τ hτ => hTn τ (mem_filter.mp hτ).1) (fun τ hτ => (mem_filter.mp hτ).2)
  have hB2 := h3_low_le c θ hθ (Tn.filter (fun τ => ¬ lsq τ ≤ 4 * |slabF c τ|))
    (fun τ hτ => hT τ (mem_filter.mp (mem_filter.mp hτ).1).1)
    (fun τ hτ => hTn τ (mem_filter.mp hτ).1) (fun τ hτ => not_le.mp (mem_filter.mp hτ).2)
  set K := (Nat.log 2 ⌈rho θ⌉₊ : ℝ)
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have e1 : 64 * (11000 * (2 * (J : ℝ) + 3)) * (4 / rho θ) = 2816000 * (2 * J + 3) / rho θ := by
    ring
  rw [e1] at hA
  have hsum : 2816000 * (2 * (J : ℝ) + 3) / rho θ + 208 / rho θ +
      3000 * (J + 2) * (K + 1) / rho θ ≤ Ch3 * (J + 2) * (K + 2) / rho θ := by
    rw [← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hρ0.le
    unfold Ch3
    nlinarith [mul_nonneg hJ0 hK0]
  linarith

/-! ## `lem:slab2` -/

/-- The radial thickness of the window `F₋ ≤ F_c ≤ F₊` (`lem:slab2`): `t_W = √(R₊)₊ - √(R₋)₊`,
`R± = |c|² + F±` (`Real.sqrt` vanishes on negatives). -/
noncomputable def slabT (c : Fin 3 → ℝ) (Fm Fp : ℝ) : ℝ :=
  Real.sqrt (∑ i, c i ^ 2 + Fp) - Real.sqrt (∑ i, c i ^ 2 + Fm)

lemma slabT_nonneg (c : Fin 3 → ℝ) {Fm Fp : ℝ} (hF : Fm ≤ Fp) : 0 ≤ slabT c Fm Fp := by
  unfold slabT
  have := Real.sqrt_le_sqrt (by linarith : ∑ i, c i ^ 2 + Fm ≤ ∑ i, c i ^ 2 + Fp)
  linarith

/-- `t_W ≤ √|W|` (`|W| = F₊ - F₋`). -/
lemma slabT_le_sqrt (c : Fin 3 → ℝ) {Fm Fp : ℝ} (hF : Fm ≤ Fp) :
    slabT c Fm Fp ≤ Real.sqrt (Fp - Fm) := by
  unfold slabT
  set C := ∑ i, c i ^ 2
  have hw : 0 ≤ Fp - Fm := by linarith
  have hgoal : Real.sqrt (C + Fp) ≤ Real.sqrt (C + Fm) + Real.sqrt (Fp - Fm) := by
    rw [Real.sqrt_le_left (by positivity)]
    have hs := Real.sq_sqrt hw
    have h0 := Real.sqrt_nonneg (C + Fm)
    have h1 := Real.sqrt_nonneg (Fp - Fm)
    rcases le_or_gt 0 (C + Fm) with h | h
    · have hm := Real.sq_sqrt h
      nlinarith
    · rw [Real.sqrt_eq_zero_of_nonpos h.le]
      nlinarith
  linarith

/-- `t_W ≤ |W|/√R₊` when `R₊ > 0`. -/
lemma slabT_le_div (c : Fin 3 → ℝ) {Fm Fp : ℝ} (hF : Fm ≤ Fp) (hR : 0 < ∑ i, c i ^ 2 + Fp) :
    slabT c Fm Fp ≤ (Fp - Fm) / Real.sqrt (∑ i, c i ^ 2 + Fp) := by
  unfold slabT
  set C := ∑ i, c i ^ 2
  have hsp : 0 < Real.sqrt (C + Fp) := Real.sqrt_pos.mpr hR
  rw [le_div_iff₀ hsp]
  have hp := Real.sq_sqrt hR.le
  rcases le_or_gt 0 (C + Fm) with h | h
  · have hm := Real.sq_sqrt h
    have h0 := Real.sqrt_nonneg (C + Fm)
    have hle : Real.sqrt (C + Fm) ≤ Real.sqrt (C + Fp) := Real.sqrt_le_sqrt (by linarith)
    nlinarith
  · rw [Real.sqrt_eq_zero_of_nonpos h.le, sub_zero]
    nlinarith

/-- **`lem:slab2`** (eq:ballcount, normalised units): the lattice points `ν` with
`ν - x₀ ∈ box N` and `F₋ ≤ F_c(ν) ≤ F₊` number at most `8 + 22 (2N+1)² (t_W + 2)`. The window
set is the annulus `√(R₋)₊ ≤ |ν + c| ≤ √(R₊)₊`; it is covered by at most `t_W + 2` unit shells,
each counted by `window_box_count`, and the unit ball about `-c` (`≤ 8` points). -/
theorem slab2_count (c : Fin 3 → ℝ) (x₀ : L3) (N : ℕ) {Fm Fp : ℝ} (hF : Fm ≤ Fp)
    (S : Finset L3) (hS : ∀ ν ∈ S, ν - x₀ ∈ box N ∧ Fm ≤ slabF c ν ∧ slabF c ν ≤ Fp) :
    (S.card : ℝ) ≤ 8 + 22 * (2 * N + 1) ^ 2 * (slabT c Fm Fp + 2) := by
  classical
  set C := ∑ i, c i ^ 2 with hC
  rw [← card_filter_add_card_filter_not (fun ν => qd c ν < 1)]
  push_cast
  -- the unit ball about `-c`
  have h0 : ((S.filter (fun ν => qd c ν < 1)).card : ℝ) ≤ 8 := by
    have hsub : S.filter (fun ν => qd c ν < 1) ⊆
        Fintype.piFinset (fun i => Icc ⌊-c i⌋ (⌊-c i⌋ + 1)) := by
      intro ν hν
      have hq := (mem_filter.mp hν).2
      rw [Fintype.mem_piFinset]
      intro i
      have hi : ((ν i : ℝ) + c i) ^ 2 < 1 := by
        have hle : ((ν i : ℝ) + c i) ^ 2 ≤ qd c ν :=
          single_le_sum (f := fun l => ((ν l : ℝ) + c l) ^ 2) (fun l _ => sq_nonneg _)
            (mem_univ i)
        linarith
      have hab : |(ν i : ℝ) + c i| < 1 := by
        rw [← sq_lt_one_iff_abs_lt_one]; exact hi
      rw [abs_lt] at hab
      have f1 := Int.floor_le (-c i)
      have f2 := Int.lt_floor_add_one (-c i)
      rw [mem_Icc]
      constructor
      · have : ((⌊-c i⌋ : ℤ) : ℝ) - 1 < (ν i : ℝ) := by linarith
        have : ⌊-c i⌋ - 1 < ν i := by exact_mod_cast this
        omega
      · have : (ν i : ℝ) < ((⌊-c i⌋ : ℤ) : ℝ) + 2 := by linarith
        have : ν i < ⌊-c i⌋ + 2 := by exact_mod_cast this
        omega
    have hc := card_le_card hsub
    rw [Fintype.card_piFinset] at hc
    have e : ∀ i : Fin 3, (Icc ⌊-c i⌋ (⌊-c i⌋ + 1)).card = 2 := fun i => by
      rw [Int.card_Icc]; omega
    simp only [e, prod_const, card_univ, Fintype.card_fin] at hc
    exact_mod_cast hc
  -- the unit shells
  set S₁ := S.filter (fun ν => ¬ qd c ν < 1)
  set m₀ := ⌊Real.sqrt (C + Fm)⌋₊
  set m₁ := ⌊Real.sqrt (C + Fp)⌋₊
  have hmem : ∀ ν ∈ S₁, ⌊Real.sqrt (qd c ν)⌋₊ ∈ Icc m₀ m₁ := by
    intro ν hν
    obtain ⟨hνS, -⟩ := mem_filter.mp hν
    obtain ⟨-, hFm, hFp⟩ := hS ν hνS
    have hq : qd c ν = C + slabF c ν := by rw [qd_eq]; ring
    rw [mem_Icc]
    constructor
    · exact Nat.floor_le_floor (Real.sqrt_le_sqrt (by rw [hq]; linarith))
    · exact Nat.floor_le_floor (Real.sqrt_le_sqrt (by rw [hq]; linarith))
  have hpiece : ∀ m ∈ Icc m₀ m₁,
      ((S₁.filter (fun ν => ⌊Real.sqrt (qd c ν)⌋₊ = m)).card : ℝ) ≤ 22 * (2 * N + 1) ^ 2 := by
    intro m _
    set Sm := S₁.filter (fun ν => ⌊Real.sqrt (qd c ν)⌋₊ = m)
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · have : Sm = ∅ := by
        apply filter_false_of_mem
        intro ν hν heq
        have hq1 : 1 ≤ qd c ν := not_lt.mp (mem_filter.mp hν).2
        have : 1 ≤ ⌊Real.sqrt (qd c ν)⌋₊ :=
          Nat.le_floor (by rw [Nat.cast_one]; exact Real.one_le_sqrt.mpr hq1)
        omega
      rw [this, card_empty, Nat.cast_zero]; positivity
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
    have hcount := window_box_count c x₀ N (r₀ := m) (a := (m : ℝ) ^ 2 - C)
      (b := ((m : ℝ) + 1) ^ 2 - C) (by linarith) (by nlinarith) Sm (by
        intro ν hν
        obtain ⟨hν1, hfl⟩ := mem_filter.mp hν
        obtain ⟨hνS, hq1⟩ := mem_filter.mp hν1
        have hq0 := qd_nonneg c ν
        have hq : qd c ν = C + slabF c ν := by rw [qd_eq]; ring
        have hs := Real.sq_sqrt hq0
        have hfl1 : (m : ℝ) ≤ Real.sqrt (qd c ν) := by
          rw [← hfl]; exact Nat.floor_le (Real.sqrt_nonneg _)
        have hfl2 : Real.sqrt (qd c ν) < m + 1 := by
          rw [← hfl]; exact Nat.lt_floor_add_one _
        have h1 : (m : ℝ) ^ 2 ≤ qd c ν := by
          rw [← hs]; exact pow_le_pow_left₀ (by positivity) hfl1 2
        have h2 : qd c ν ≤ ((m : ℝ) + 1) ^ 2 := by
          rw [← hs]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hfl2.le 2
        exact ⟨(hS ν hνS).1, by linarith, by linarith, h1⟩)
    have hs3 : Real.sqrt 3 ≤ 7 / 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hrat : (((m : ℝ) + 1) ^ 2 - C - ((m : ℝ) ^ 2 - C)) * Real.sqrt 3 / (2 * m) ≤ 21 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.sqrt_nonneg 3]
    calc (Sm.card : ℝ) ≤ 6 * (2 * N + 1) ^ 2 *
          ((((m : ℝ) + 1) ^ 2 - C - ((m : ℝ) ^ 2 - C)) * Real.sqrt 3 / (2 * m) + 1) := hcount
      _ ≤ 6 * (2 * N + 1) ^ 2 * (21 / 8 + 1) := by gcongr
      _ ≤ 22 * (2 * N + 1) ^ 2 := by nlinarith [sq_nonneg (2 * (N : ℝ) + 1)]
  have hS₁ : (S₁.card : ℝ) ≤ ∑ m ∈ Icc m₀ m₁,
      ((S₁.filter (fun ν => ⌊Real.sqrt (qd c ν)⌋₊ = m)).card : ℝ) := by
    have := card_eq_sum_card_fiberwise (f := fun ν => ⌊Real.sqrt (qd c ν)⌋₊) (t := Icc m₀ m₁)
      (fun ν hν => hmem ν hν)
    rw [this]; push_cast; exact le_rfl
  have hcardI : ((Icc m₀ m₁).card : ℝ) ≤ slabT c Fm Fp + 2 := by
    rw [Nat.card_Icc]
    have f1 : (m₁ : ℝ) ≤ Real.sqrt (C + Fp) := Nat.floor_le (Real.sqrt_nonneg _)
    have f2 : Real.sqrt (C + Fm) < m₀ + 1 := Nat.lt_floor_add_one _
    have ht : slabT c Fm Fp = Real.sqrt (C + Fp) - Real.sqrt (C + Fm) := rfl
    rcases le_or_gt m₀ (m₁ + 1) with h | h
    · rw [Nat.cast_sub h]; push_cast; linarith
    · rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero]
      linarith [slabT_nonneg c hF]
  have hsum : ∑ m ∈ Icc m₀ m₁, ((S₁.filter (fun ν => ⌊Real.sqrt (qd c ν)⌋₊ = m)).card : ℝ) ≤
      22 * (2 * N + 1) ^ 2 * (slabT c Fm Fp + 2) := by
    calc _ ≤ ∑ _m ∈ Icc m₀ m₁, 22 * (2 * (N : ℝ) + 1) ^ 2 := sum_le_sum hpiece
      _ = ((Icc m₀ m₁).card : ℝ) * (22 * (2 * N + 1) ^ 2) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (slabT c Fm Fp + 2) * (22 * (2 * N + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right hcardI (by positivity)
      _ = _ := by ring
  linarith

end FSLattice
