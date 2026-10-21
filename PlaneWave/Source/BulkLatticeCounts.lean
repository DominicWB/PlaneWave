import PlaneWave.Source.ChannelKernels

/-!
# Flux/source build, block 5: lattice counts for the bulk hierarchy

Mathlib-only estimates on `ℤ³` used by the retained bulk hierarchy.  With the mismatch polynomial
`F_c(θ) = |θ|² + 2 θ·c` (for a pair hop on `(a, b)` with transfer `θ`,
`E(out) - E(in) = (g²/2μ) F_c(θ)` with `c = μ (k_a/m_a - k_b/m_b)`):

* `slab_count` (`lem:slab` (i)): for `ρ ≥ 1`, `δ ≥ 0` the transfers with `ρ ≤ |θ| ≤ 2ρ` and
  `|F_c(θ)| ≤ δ` number at most `11000 ρ² (1 + δ/ρ)`, uniformly in `c`.  The proof is
  combinatorial instead of the text's volume argument: a nonempty thin slab forces `|c| ≥ ρ/3`,
  every point of it has a coordinate `i` with `|θ_i + c_i| ≥ ρ/4`, and on a line in direction
  `e_i` the points with `θ_i + c_i` of one sign lie in an interval of length `4δ/ρ`.
* `pin_core` (`lem:pin`, the lattice part): `|F_c(θ)| < |θ|²/4` forces `|c|² > (9/64)|θ|²`.
* `flat_sum_le` (eq:flatbd in the form used by `lem:h2`):
  `Σ_{|μ| > R} |μ|⁻⁴ |θ - μ|⁻² ≤ 611/R³` for `R ≥ 1`, uniformly in `θ` (the term `μ = θ` is
  `0`, as `1/0 = 0`).
* `inv_le_layer_sum`, `slab_inv_sum_le`: the dyadic layer-cake bound `1/x ≤ (1/f) Σ_l 2^{-l}
  1{x < 2^{l+1} f}` and, with the slab count, `Σ_{θ ∈ T} 1/|F_c(θ)| ≤ 11000 ρ² (2/F + 2(J+1)/ρ)`
  for a shell `T` with floor `F ≤ |F_c| < 2^{J+1} F` (the Schur rows of `Σ₂^bb`).
* `sum_tail_inv_pow_three_le`: `Σ_{|ν| > R} |ν|⁻⁶ ≤ 143/R³`.
-/

set_option autoImplicit false

open Finset

namespace FSLattice

open FSChannel

/-! ## The mismatch polynomial -/

/-- The mismatch polynomial `F_c(θ) = |θ|² + 2 θ·c`. -/
noncomputable def slabF (c : Fin 3 → ℝ) (θ : L3) : ℝ := lsq θ + 2 * ∑ i, (θ i : ℝ) * c i

lemma lsq_eq_sum (θ : L3) : lsq θ = ∑ i, (θ i : ℝ) ^ 2 := by
  simp [lsq, Fin.sum_univ_three]

lemma slabF_eq_sum (c : Fin 3 → ℝ) (θ : L3) :
    slabF c θ = ∑ i, ((θ i : ℝ) ^ 2 + 2 * ((θ i : ℝ) * c i)) := by
  rw [slabF, lsq_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- Completing the square: `Σ_i (θ_i + c_i)² = F_c(θ) + |c|²`. -/
lemma sum_sq_add_eq (c : Fin 3 → ℝ) (θ : L3) :
    ∑ i, ((θ i : ℝ) + c i) ^ 2 = slabF c θ + ∑ i, c i ^ 2 := by
  rw [slabF_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Cauchy–Schwarz: `(θ·c)² ≤ |θ|² |c|²`. -/
lemma dot_sq_le (c : Fin 3 → ℝ) (θ : L3) :
    (∑ i, (θ i : ℝ) * c i) ^ 2 ≤ lsq θ * ∑ i, c i ^ 2 := by
  rw [lsq_eq_sum]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- **Pinning, the lattice part** (`lem:pin`): if `|F_c(θ)| < |θ|²/4` then `|c|² > (9/64)|θ|²`. -/
theorem pin_core (c : Fin 3 → ℝ) (θ : L3) (h : |slabF c θ| < lsq θ / 4) :
    9 / 64 * lsq θ < ∑ i, c i ^ 2 := by
  have hl : 0 < lsq θ := by
    have := abs_nonneg (slabF c θ)
    linarith
  set t := ∑ i, (θ i : ℝ) * c i
  have hF : slabF c θ = lsq θ + 2 * t := rfl
  rw [hF] at h
  have h1 : 3 / 4 * lsq θ < 2 * |t| := by
    have := abs_lt.mp h
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]; nlinarith
    · rw [abs_of_neg ht]; nlinarith
  have h2 : (3 / 8 * lsq θ) ^ 2 < t ^ 2 := by
    have h3 : 3 / 8 * lsq θ < |t| := by linarith
    have h4 : 0 ≤ 3 / 8 * lsq θ := by positivity
    calc (3 / 8 * lsq θ) ^ 2 < |t| ^ 2 := by gcongr
      _ = t ^ 2 := sq_abs t
  have h5 := dot_sq_le c θ
  nlinarith

/-! ## The two-sided slab count -/

/-- The three coordinates of `ℤ³` relative to `i`: every `l` is `i`, `i + 1` or `i + 2`. -/
lemma fin3_cases (i l : Fin 3) : l = i ∨ l = i + 1 ∨ l = i + 2 := by
  fin_cases i <;> fin_cases l <;> decide

/-- Sum over `Fin 3` relative to a coordinate `i`. -/
lemma sum_fin3_rel (i : Fin 3) (g : Fin 3 → ℝ) : ∑ l, g l = g i + g (i + 1) + g (i + 2) := by
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring_nf

/-- Two lattice points agreeing in the coordinates `i + 1`, `i + 2` differ in `F_c` by
`(θ_i - θ'_i)(θ_i + θ'_i + 2 c_i)`. -/
lemma slabF_sub_of_fiber (c : Fin 3 → ℝ) (i : Fin 3) {θ θ' : L3} (h1 : θ (i + 1) = θ' (i + 1))
    (h2 : θ (i + 2) = θ' (i + 2)) :
    slabF c θ - slabF c θ' =
      ((θ i : ℝ) - θ' i) * (((θ i : ℝ) + c i) + ((θ' i : ℝ) + c i)) := by
  rw [slabF_eq_sum, slabF_eq_sum, sum_fin3_rel i, sum_fin3_rel i, h1, h2]
  ring

/-- Integers with diameter at most `D` number at most `⌊D⌋₊ + 1`. -/
lemma card_int_le_of_diam (T : Finset ℤ) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ x ∈ T, ∀ y ∈ T, ((x : ℝ) - y) ≤ D) : (T.card : ℝ) ≤ D + 1 := by
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT, card_empty, Nat.cast_zero]; linarith
  set m := T.min' hT
  have hsub : T ⊆ Icc m (m + ⌊D⌋₊) := by
    intro x hx
    rw [mem_Icc]
    refine ⟨T.min'_le x hx, ?_⟩
    have hxm : ((x : ℝ) - m) ≤ D := h x hx m (T.min'_mem hT)
    have hxm' : x - m ≤ (⌊D⌋₊ : ℤ) := by
      have hnn : 0 ≤ x - m := by have := T.min'_le x hx; omega
      have : ((x - m).toNat : ℝ) ≤ D := by
        have e : ((x - m).toNat : ℝ) = ((x - m : ℤ) : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
        rw [e]; push_cast; exact hxm
      have := Nat.le_floor this
      omega
    omega
  have hc := card_le_card hsub
  rw [Int.card_Icc] at hc
  have e : m + (⌊D⌋₊ : ℤ) + 1 - m = ((⌊D⌋₊ + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, Int.toNat_natCast] at hc
  have hc' : (T.card : ℝ) ≤ ((⌊D⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at hc'
  linarith [Nat.floor_le hD]

/-- The fibres of a one-signed slab piece: on a line in direction `e_i` the points with
`|θ_i + c_i + θ'_i + c_i| ≥ ρ/2` number at most `4δ/ρ + 1`. -/
lemma card_line_le (c : Fin 3 → ℝ) (i : Fin 3) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ)
    (F : Finset L3) (hF : ∀ θ ∈ F, |slabF c θ| ≤ δ)
    (hfib : ∀ θ ∈ F, ∀ θ' ∈ F, θ (i + 1) = θ' (i + 1) ∧ θ (i + 2) = θ' (i + 2))
    (hsign : ∀ θ ∈ F, ∀ θ' ∈ F, ρ / 2 ≤ |((θ i : ℝ) + c i) + ((θ' i : ℝ) + c i)|) :
    (F.card : ℝ) ≤ 4 * δ / ρ + 1 := by
  have hinj : Set.InjOn (fun θ : L3 => θ i) F := by
    intro θ hθ θ' hθ' he
    obtain ⟨h1, h2⟩ := hfib θ hθ θ' hθ'
    funext l
    rcases fin3_cases i l with rfl | rfl | rfl
    · exact he
    · exact h1
    · exact h2
  rw [← card_image_of_injOn hinj]
  apply card_int_le_of_diam _ (by positivity)
  intro x hx y hy
  obtain ⟨θ, hθ, rfl⟩ := mem_image.mp hx
  obtain ⟨θ', hθ', rfl⟩ := mem_image.mp hy
  obtain ⟨h1, h2⟩ := hfib θ hθ θ' hθ'
  have he := slabF_sub_of_fiber c i h1 h2
  have hs := hsign θ hθ θ' hθ'
  have hd : |slabF c θ - slabF c θ'| ≤ 2 * δ := by
    have := abs_sub (slabF c θ) (slabF c θ')
    linarith [hF θ hθ, hF θ' hθ']
  rw [he, abs_mul] at hd
  have hprod : |(θ i : ℝ) - θ' i| * (ρ / 2) ≤ 2 * δ :=
    le_trans (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) hd
  have hle : |(θ i : ℝ) - θ' i| ≤ 4 * δ / ρ := by
    rw [le_div_iff₀ hρ]; linarith
  exact (le_abs_self _).trans hle

/-- The coordinate pairs of a box: the labels `(θ_{i+1}, θ_{i+2})` of the points of `box N`. -/
lemma card_labels_le (i : Fin 3) (N : ℕ) (S : Finset L3) (hS : S ⊆ box N) :
    ((S.image fun θ : L3 => (θ (i + 1), θ (i + 2))).card : ℝ) ≤ (2 * N + 1) ^ 2 := by
  have hsub : S.image (fun θ : L3 => (θ (i + 1), θ (i + 2))) ⊆
      Icc (-(N : ℤ)) N ×ˢ Icc (-(N : ℤ)) N := by
    intro x hx
    obtain ⟨θ, hθ, rfl⟩ := mem_image.mp hx
    have hb := mem_box.mp (hS hθ)
    rw [mem_product, mem_Icc, mem_Icc]
    exact ⟨hb (i + 1), hb (i + 2)⟩
  have hc := card_le_card hsub
  rw [card_product, Int.card_Icc] at hc
  have e : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, Int.toNat_natCast] at hc
  have : ((S.image fun θ : L3 => (θ (i + 1), θ (i + 2))).card : ℝ) ≤
      ((2 * N + 1 : ℕ) : ℝ) * ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at this
  nlinarith

/-- A one-signed slab piece in direction `i`: at most `(2N+1)² (4δ/ρ + 1)` points. -/
lemma card_piece_le (c : Fin 3 → ℝ) (i : Fin 3) {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ) (N : ℕ)
    (S : Finset L3) (hS : S ⊆ box N) (hF : ∀ θ ∈ S, |slabF c θ| ≤ δ)
    (hsign : ∀ θ ∈ S, ∀ θ' ∈ S, ρ / 2 ≤ |((θ i : ℝ) + c i) + ((θ' i : ℝ) + c i)|) :
    (S.card : ℝ) ≤ (2 * N + 1) ^ 2 * (4 * δ / ρ + 1) := by
  set lab := fun θ : L3 => (θ (i + 1), θ (i + 2))
  have hfib : ∀ b ∈ S.image lab, ((S.filter fun θ => lab θ = b).card : ℝ) ≤ 4 * δ / ρ + 1 := by
    intro b _
    apply card_line_le c i hρ hδ
    · intro θ hθ; exact hF θ (mem_filter.mp hθ).1
    · intro θ hθ θ' hθ'
      have e1 := (mem_filter.mp hθ).2
      have e2 := (mem_filter.mp hθ').2
      have e := e1.trans e2.symm
      exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
    · intro θ hθ θ' hθ'
      exact hsign θ (mem_filter.mp hθ).1 θ' (mem_filter.mp hθ').1
  have hn : ∀ b ∈ S.image lab, (S.filter fun θ => lab θ = b).card ≤ ⌊4 * δ / ρ + 1⌋₊ := by
    intro b hb
    exact Nat.le_floor (hfib b hb)
  have hc := card_le_mul_card_image S _ hn
  have hc' : (S.card : ℝ) ≤ (⌊4 * δ / ρ + 1⌋₊ : ℝ) * ((S.image lab).card : ℝ) := by
    exact_mod_cast hc
  have hfl : (⌊4 * δ / ρ + 1⌋₊ : ℝ) ≤ 4 * δ / ρ + 1 := Nat.floor_le (by positivity)
  have hl := card_labels_le i N S hS
  have h0 : (0 : ℝ) ≤ ((S.image lab).card : ℝ) := Nat.cast_nonneg _
  calc (S.card : ℝ) ≤ (⌊4 * δ / ρ + 1⌋₊ : ℝ) * ((S.image lab).card : ℝ) := hc'
    _ ≤ (4 * δ / ρ + 1) * ((2 * N + 1) ^ 2) := by
        apply mul_le_mul hfl hl h0 (by positivity)
    _ = _ := by ring

/-- **The two-sided slab count** (`lem:slab` (i)). For `c ∈ ℝ³`, `ρ ≥ 1` and `δ ≥ 0`, the lattice
transfers with `ρ ≤ |θ| ≤ 2ρ` and `|F_c(θ)| ≤ δ` number at most `11000 ρ² (1 + δ/ρ)`. -/
theorem slab_count (c : Fin 3 → ℝ) {ρ δ : ℝ} (hρ : 1 ≤ ρ) (hδ : 0 ≤ δ) (S : Finset L3)
    (hS : ∀ θ ∈ S, ρ ^ 2 ≤ lsq θ ∧ lsq θ ≤ 4 * ρ ^ 2 ∧ |slabF c θ| ≤ δ) :
    (S.card : ℝ) ≤ 11000 * ρ ^ 2 * (1 + δ / ρ) := by
  have hρ0 : 0 < ρ := by linarith
  set N := ⌊2 * ρ⌋₊
  have hN : (N : ℝ) ≤ 2 * ρ := Nat.floor_le (by linarith)
  have hbox : S ⊆ box N := by
    intro θ hθ
    apply mem_box_floor_of_lsq_le (by linarith)
    have := (hS θ hθ).2.1
    nlinarith
  have hlab : (2 * (N : ℝ) + 1) ^ 2 ≤ 25 * ρ ^ 2 := by
    have : 2 * (N : ℝ) + 1 ≤ 5 * ρ := by linarith
    have h0 : (0 : ℝ) ≤ 2 * N + 1 := by positivity
    nlinarith
  have hδρ : 0 ≤ δ / ρ := div_nonneg hδ hρ0.le
  by_cases hbig : ρ ^ 2 / 32 ≤ δ
  · -- the trivial count `125 ρ³`
    have hc := card_le_card hbox
    rw [card_box] at hc
    have hc' : (S.card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ 3 := by exact_mod_cast hc
    have h5 : 2 * (N : ℝ) + 1 ≤ 5 * ρ := by linarith
    have h125 : (2 * (N : ℝ) + 1) ^ 3 ≤ 125 * ρ ^ 3 := by
      have h0 : (0 : ℝ) ≤ 2 * N + 1 := by positivity
      calc (2 * (N : ℝ) + 1) ^ 3 ≤ (5 * ρ) ^ 3 := pow_le_pow_left₀ h0 h5 3
        _ = 125 * ρ ^ 3 := by ring
    have hρδ : ρ ^ 3 ≤ 32 * ρ ^ 2 * (δ / ρ) := by
      rw [show 32 * ρ ^ 2 * (δ / ρ) = 32 * ρ * δ by field_simp]
      nlinarith
    nlinarith
  push Not at hbig
  rcases S.eq_empty_or_nonempty with hS0 | ⟨θ₀, hθ₀⟩
  · rw [hS0, card_empty, Nat.cast_zero]; positivity
  -- a nonempty thin slab forces `|c|² ≥ (961/4096) ρ²`
  have hc2 : 961 / 4096 * ρ ^ 2 ≤ ∑ i, c i ^ 2 := by
    obtain ⟨h1, -, h3⟩ := hS θ₀ hθ₀
    set t := ∑ i, (θ₀ i : ℝ) * c i
    have hF : slabF c θ₀ = lsq θ₀ + 2 * t := rfl
    rw [hF] at h3
    have ht : 31 / 64 * lsq θ₀ ≤ -t := by
      have := (abs_le.mp h3).2
      nlinarith
    have hcs := dot_sq_le c θ₀
    have hl : 0 < lsq θ₀ := by nlinarith
    have h4 : (31 / 64 * lsq θ₀) ^ 2 ≤ t ^ 2 := by
      have h0 : 0 ≤ 31 / 64 * lsq θ₀ := by positivity
      nlinarith
    have h5 : (31 / 64) ^ 2 * lsq θ₀ ≤ ∑ i, c i ^ 2 := by
      by_contra hcon
      push Not at hcon
      have : t ^ 2 < (31 / 64) ^ 2 * lsq θ₀ ^ 2 := by nlinarith
      nlinarith
    nlinarith
  -- every point has a coordinate with `|θ_i + c_i| ≥ ρ/4`
  have hcov : ∀ θ ∈ S, ∃ i, ρ / 4 ≤ (θ i : ℝ) + c i ∨ (θ i : ℝ) + c i ≤ -(ρ / 4) := by
    intro θ hθ
    have hsum := sum_sq_add_eq c θ
    have h3 := (hS θ hθ).2.2
    have hlow : 3 * (ρ / 4) ^ 2 < ∑ i, ((θ i : ℝ) + c i) ^ 2 := by
      have := (abs_le.mp h3).1
      nlinarith
    by_contra hno
    push Not at hno
    have hlt : ∀ i, ((θ i : ℝ) + c i) ^ 2 < (ρ / 4) ^ 2 := by
      intro i
      obtain ⟨h1, h2⟩ := hno i
      have : |(θ i : ℝ) + c i| < ρ / 4 := abs_lt.mpr ⟨by linarith, h1⟩
      calc ((θ i : ℝ) + c i) ^ 2 = |(θ i : ℝ) + c i| ^ 2 := (sq_abs _).symm
        _ < (ρ / 4) ^ 2 := by gcongr
    rw [Fin.sum_univ_three] at hlow
    linarith [hlt 0, hlt 1, hlt 2]
  -- the six one-signed pieces
  set Sp := fun i : Fin 3 => S.filter fun θ => ρ / 4 ≤ (θ i : ℝ) + c i
  set Sm := fun i : Fin 3 => S.filter fun θ => (θ i : ℝ) + c i ≤ -(ρ / 4)
  have hpiece : ∀ i, ((Sp i).card : ℝ) ≤ 25 * ρ ^ 2 * (4 * δ / ρ + 1) ∧
      ((Sm i).card : ℝ) ≤ 25 * ρ ^ 2 * (4 * δ / ρ + 1) := by
    intro i
    have hfac : 0 ≤ 4 * δ / ρ + 1 := by positivity
    constructor
    · refine (card_piece_le c i hρ0 hδ N (Sp i) ((filter_subset _ _).trans hbox)
        (fun θ hθ => (hS θ (mem_filter.mp hθ).1).2.2) ?_).trans
        (mul_le_mul_of_nonneg_right hlab hfac)
      intro θ hθ θ' hθ'
      have h1 := (mem_filter.mp hθ).2
      have h2 := (mem_filter.mp hθ').2
      rw [abs_of_nonneg (by linarith)]
      linarith
    · refine (card_piece_le c i hρ0 hδ N (Sm i) ((filter_subset _ _).trans hbox)
        (fun θ hθ => (hS θ (mem_filter.mp hθ).1).2.2) ?_).trans
        (mul_le_mul_of_nonneg_right hlab hfac)
      intro θ hθ θ' hθ'
      have h1 := (mem_filter.mp hθ).2
      have h2 := (mem_filter.mp hθ').2
      rw [abs_of_nonpos (by linarith)]
      linarith
  have hsub : S ⊆ (univ : Finset (Fin 3)).biUnion fun i => Sp i ∪ Sm i := by
    intro θ hθ
    obtain ⟨i, hi⟩ := hcov θ hθ
    rw [mem_biUnion]
    refine ⟨i, mem_univ _, ?_⟩
    rcases hi with hi | hi
    · exact mem_union_left _ (mem_filter.mpr ⟨hθ, hi⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hθ, hi⟩)
  have hcard : (S.card : ℝ) ≤ ∑ i : Fin 3, (((Sp i).card : ℝ) + (Sm i).card) := by
    have h1 := card_le_card hsub
    have h2 := card_biUnion_le (s := (univ : Finset (Fin 3))) (t := fun i => Sp i ∪ Sm i)
    have h3 : ∀ i ∈ (univ : Finset (Fin 3)), (Sp i ∪ Sm i).card ≤ (Sp i).card + (Sm i).card :=
      fun i _ => card_union_le _ _
    have h4 := (h1.trans h2).trans (sum_le_sum h3)
    exact_mod_cast h4
  have htot : ∑ i : Fin 3, (((Sp i).card : ℝ) + (Sm i).card) ≤
      ∑ _i : Fin 3, 2 * (25 * ρ ^ 2 * (4 * δ / ρ + 1)) :=
    sum_le_sum fun i _ => by linarith [(hpiece i).1, (hpiece i).2]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at htot
  have hfin : (3 : ℝ) * (2 * (25 * ρ ^ 2 * (4 * δ / ρ + 1))) ≤ 11000 * ρ ^ 2 * (1 + δ / ρ) := by
    have e : 4 * δ / ρ = 4 * (δ / ρ) := by ring
    rw [e]
    have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
    nlinarith
  push_cast at htot
  linarith

/-! ## The dyadic layer-cake -/

/-- **Dyadic layer-cake**: for `0 < f ≤ x < 2^{J+1} f`,
`1/x ≤ (1/f) Σ_{l ≤ J} 2^{-l} 1{x < 2^{l+1} f}`. -/
lemma inv_le_layer_sum {f x : ℝ} (hf : 0 < f) (hx : f ≤ x) {J : ℕ} (hJ : x < 2 ^ (J + 1) * f) :
    1 / x ≤ 1 / f * ∑ l ∈ range (J + 1), (1 / 2 : ℝ) ^ l * (if x < 2 ^ (l + 1) * f then 1 else 0) := by
  classical
  have hex : ∃ l, x < 2 ^ (l + 1) * f := ⟨J, hJ⟩
  set i := Nat.find hex with hi
  have hiJ : i ≤ J := Nat.find_min' hex hJ
  have hix : x < 2 ^ (i + 1) * f := Nat.find_spec hex
  have hxi : 2 ^ i * f ≤ x := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0, pow_zero, one_mul]; exact hx
    · have hmin := Nat.find_min hex (show i - 1 < i by omega)
      push Not at hmin
      rwa [show i - 1 + 1 = i by omega] at hmin
  have hterm : (1 / 2 : ℝ) ^ i * (if x < 2 ^ (i + 1) * f then 1 else 0) = (1 / 2 : ℝ) ^ i := by
    rw [if_pos hix, mul_one]
  have hsingle : (1 / 2 : ℝ) ^ i ≤
      ∑ l ∈ range (J + 1), (1 / 2 : ℝ) ^ l * (if x < 2 ^ (l + 1) * f then 1 else 0) := by
    rw [← hterm]
    apply single_le_sum (f := fun l => (1 / 2 : ℝ) ^ l * (if x < 2 ^ (l + 1) * f then 1 else 0))
    · intro l _
      positivity
    · exact mem_range.mpr (by omega)
  have hx0 : 0 < x := lt_of_lt_of_le hf hx
  have h2 : (0 : ℝ) < 2 ^ i * f := by positivity
  calc 1 / x ≤ 1 / (2 ^ i * f) := one_div_le_one_div_of_le h2 hxi
    _ = 1 / f * (1 / 2 : ℝ) ^ i := by rw [one_div_pow]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hsingle (by positivity)

/-- **The slab-weighted sum** (the Schur rows of `Σ₂^bb`): for a shell `ρ ≤ |θ| ≤ 2ρ` with floor
`F ≤ |F_c(θ)| < 2^{J+1} F`, `Σ_θ 1/|F_c(θ)| ≤ 11000 ρ² (2/F + 2(J+1)/ρ)`. -/
theorem slab_inv_sum_le (c : Fin 3 → ℝ) {ρ F : ℝ} (hρ : 1 ≤ ρ) (hF : 0 < F) {J : ℕ}
    (T : Finset L3)
    (hT : ∀ θ ∈ T, ρ ^ 2 ≤ lsq θ ∧ lsq θ ≤ 4 * ρ ^ 2 ∧ F ≤ |slabF c θ| ∧
      |slabF c θ| < 2 ^ (J + 1) * F) :
    ∑ θ ∈ T, 1 / |slabF c θ| ≤ 11000 * ρ ^ 2 * (2 / F + 2 * (J + 1) / ρ) := by
  classical
  have hρ0 : 0 < ρ := by linarith
  have h1 : ∑ θ ∈ T, 1 / |slabF c θ| ≤ ∑ θ ∈ T, 1 / F * ∑ l ∈ range (J + 1),
      (1 / 2 : ℝ) ^ l * (if |slabF c θ| < 2 ^ (l + 1) * F then 1 else 0) :=
    sum_le_sum fun θ hθ => inv_le_layer_sum hF (hT θ hθ).2.2.1 (hT θ hθ).2.2.2
  have h2 : ∑ θ ∈ T, 1 / F * ∑ l ∈ range (J + 1),
      (1 / 2 : ℝ) ^ l * (if |slabF c θ| < 2 ^ (l + 1) * F then 1 else 0) =
      1 / F * ∑ l ∈ range (J + 1), (1 / 2 : ℝ) ^ l *
        ((T.filter fun θ => |slabF c θ| < 2 ^ (l + 1) * F).card : ℝ) := by
    rw [← mul_sum, sum_comm]
    congr 1
    refine sum_congr rfl fun l _ => ?_
    rw [← mul_sum, sum_boole]
  have h3 : ∀ l ∈ range (J + 1), (1 / 2 : ℝ) ^ l *
      ((T.filter fun θ => |slabF c θ| < 2 ^ (l + 1) * F).card : ℝ) ≤
      (1 / 2 : ℝ) ^ l * (11000 * ρ ^ 2) + 11000 * ρ ^ 2 * (2 * F / ρ) := by
    intro l _
    have hcount := slab_count c hρ (by positivity : (0 : ℝ) ≤ 2 ^ (l + 1) * F)
      (T.filter fun θ => |slabF c θ| < 2 ^ (l + 1) * F)
      (fun θ hθ => ⟨(hT θ (mem_filter.mp hθ).1).1, (hT θ (mem_filter.mp hθ).1).2.1,
        (mem_filter.mp hθ).2.le⟩)
    have hpow : (1 / 2 : ℝ) ^ l * 2 ^ (l + 1) = 2 := by
      rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
    calc (1 / 2 : ℝ) ^ l * ((T.filter fun θ => |slabF c θ| < 2 ^ (l + 1) * F).card : ℝ)
        ≤ (1 / 2 : ℝ) ^ l * (11000 * ρ ^ 2 * (1 + 2 ^ (l + 1) * F / ρ)) :=
          mul_le_mul_of_nonneg_left hcount (by positivity)
      _ = (1 / 2 : ℝ) ^ l * (11000 * ρ ^ 2) +
            11000 * ρ ^ 2 * (((1 / 2 : ℝ) ^ l * 2 ^ (l + 1)) * F / ρ) := by ring
      _ = (1 / 2 : ℝ) ^ l * (11000 * ρ ^ 2) + 11000 * ρ ^ 2 * (2 * F / ρ) := by rw [hpow]
  have hgeom : ∑ l ∈ range (J + 1), (1 / 2 : ℝ) ^ l ≤ 2 := by
    have := sum_geometric_two_le (J + 1)
    simpa using this
  have h4 := sum_le_sum h3
  rw [sum_add_distrib, ← sum_mul, sum_const, card_range, nsmul_eq_mul] at h4
  rw [h2] at h1
  have hF1 : 0 < 1 / F := by positivity
  calc ∑ θ ∈ T, 1 / |slabF c θ| ≤ _ := h1
    _ ≤ 1 / F * ((∑ l ∈ range (J + 1), (1 / 2 : ℝ) ^ l) * (11000 * ρ ^ 2) +
          ((J + 1 : ℕ) : ℝ) * (11000 * ρ ^ 2 * (2 * F / ρ))) :=
        mul_le_mul_of_nonneg_left h4 hF1.le
    _ ≤ 1 / F * (2 * (11000 * ρ ^ 2) + ((J + 1 : ℕ) : ℝ) * (11000 * ρ ^ 2 * (2 * F / ρ))) := by
        gcongr
    _ = 11000 * ρ ^ 2 * (2 / F + 2 * (J + 1) / ρ) := by
        push_cast; field_simp

/-! ## The lattice tail `Σ |ν|⁻⁶` -/

/-- One dyadic Euclidean shell: `Σ_{ν ∈ S, lam < |ν| ≤ 2 lam} |ν|⁻⁶ ≤ 125 lam⁻³` (`lam ≥ 1`). -/
lemma sum_shell_inv_pow_three_le (S : Finset L3) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∑ ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lsq ν ^ 3 ≤
      125 / lam ^ 3 := by
  have hlam0 : 0 < lam := by linarith
  have hsub : S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2) ⊆
      (box ⌈2 * lam⌉₊).filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2) := by
    intro ν hν
    rw [mem_filter] at hν ⊢
    exact ⟨box_mono (Nat.floor_le_ceil _) (mem_box_floor_of_lsq_le (by linarith) hν.2.2), hν.2⟩
  have hcard : ((S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2)).card : ℝ) ≤
      125 * lam ^ 3 :=
    (Nat.cast_le.mpr (card_le_card hsub)).trans (card_euclid_shell_le hlam)
  calc ∑ ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lsq ν ^ 3
      ≤ ∑ _ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lam ^ 6 := by
        apply sum_le_sum
        intro ν hν
        rw [mem_filter] at hν
        have h1 : lam ^ 6 ≤ lsq ν ^ 3 := by
          rw [show lam ^ 6 = (lam ^ 2) ^ 3 by ring]
          exact pow_le_pow_left₀ (by positivity) hν.2.1.le 3
        exact one_div_le_one_div_of_le (by positivity) h1
    _ = (S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2)).card * (1 / lam ^ 6) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 125 * lam ^ 3 * (1 / lam ^ 6) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 125 / lam ^ 3 := by field_simp

/-- The dyadic shells `R < |ν| ≤ 2^J R`: `125 R⁻³ + 143 (2R)⁻³ ≤ 143 R⁻³`. -/
lemma sum_dyadic_inv_pow_three_le (S : Finset L3) (J : ℕ) :
    ∀ R : ℝ, 1 ≤ R →
      ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * R) ^ 2), 1 / lsq ν ^ 3 ≤
        143 / R ^ 3 := by
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
    have h1 := sum_shell_inv_pow_three_le S hR
    have h2 := ih (2 * R) (by linarith)
    have e : (2 : ℝ) ^ (J + 1) * R = 2 ^ J * (2 * R) := by ring
    have hsplit :
        ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ (J + 1) * R) ^ 2), 1 / lsq ν ^ 3 ≤
          ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 * R) ^ 2), 1 / lsq ν ^ 3 +
            ∑ ν ∈ S.filter (fun ν => (2 * R) ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * (2 * R)) ^ 2),
              1 / lsq ν ^ 3 := by
      rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib, e]
      apply sum_le_sum
      intro ν _
      have hnn : 0 ≤ 1 / lsq ν ^ 3 := by have := lsq_nonneg ν; positivity
      by_cases hc1 : R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * (2 * R)) ^ 2
      · by_cases hc2 : lsq ν ≤ (2 * R) ^ 2
        · rw [if_pos hc1, if_pos ⟨hc1.1, hc2⟩]
          split_ifs <;> linarith
        · rw [if_pos hc1, if_neg (fun h => hc2 h.2), if_pos ⟨not_le.mp hc2, hc1.2⟩]
          linarith
      · rw [if_neg hc1]
        split_ifs <;> linarith
    have h5 : (2 * R) ^ 3 = 8 * R ^ 3 := by ring
    rw [h5] at h2
    calc _ ≤ _ := hsplit
      _ ≤ 125 / R ^ 3 + 143 / (8 * R ^ 3) := add_le_add h1 h2
      _ = (125 + 143 / 8) / R ^ 3 := by field_simp
      _ ≤ 143 / R ^ 3 := by gcongr; norm_num

/-- **Lattice tail sum.** `Σ_{ν ∈ S, |ν| > R} |ν|⁻⁶ ≤ 143 R⁻³` for `R ≥ 1`. -/
theorem sum_tail_inv_pow_three_le (S : Finset L3) {R : ℝ} (hR : 1 ≤ R) :
    ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν), 1 / lsq ν ^ 3 ≤ 143 / R ^ 3 := by
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
  exact sum_dyadic_inv_pow_three_le S J R hR

/-! ## The flat sum -/

/-- **The flat sum** (eq:flatbd): `Σ_{μ ∈ S, |μ| > R} |μ|⁻⁴ |θ - μ|⁻² ≤ 611/R³` for `R ≥ 1`,
uniformly in `θ`; the term `μ = θ` vanishes (`1/0 = 0`). Far terms (`|θ - μ| ≥ |μ|/2`) give the
lattice tail `4 · 143/R³`; near terms have `|μ| > max(R, 2|θ|/3)` and the Coulomb ball sum
`Σ_{0 < |x| ≤ |θ|} |x|⁻² ≤ 26|θ|`. -/
theorem flat_sum_le (S : Finset L3) (θ : L3) {R : ℝ} (hR : 1 ≤ R) :
    ∑ μ ∈ S.filter (fun μ => R ^ 2 < lsq μ), 1 / lsq μ ^ 2 * (1 / lsq (θ - μ)) ≤ 611 / R ^ 3 := by
  classical
  have hR0 : 0 < R := by linarith
  set S' := S.filter (fun μ => R ^ 2 < lsq μ)
  set f := fun μ : L3 => 1 / lsq μ ^ 2 * (1 / lsq (θ - μ))
  rw [← sum_filter_add_sum_filter_not S' (fun μ => lsq μ ≤ 4 * lsq (θ - μ))]
  -- far terms
  have hfar : ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), f μ ≤ 4 * (143 / R ^ 3) := by
    have hterm : ∀ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), f μ ≤ 4 * (1 / lsq μ ^ 3) := by
      intro μ hμ
      obtain ⟨hμ1, hμ2⟩ := mem_filter.mp hμ
      have hl : 0 < lsq μ := lt_of_le_of_lt (sq_nonneg R) (mem_filter.mp hμ1).2
      have hd : 0 < lsq (θ - μ) := by linarith
      have h1 : 1 / lsq (θ - μ) ≤ 4 / lsq μ := by
        rw [div_le_div_iff₀ hd hl]; linarith
      calc f μ = 1 / lsq μ ^ 2 * (1 / lsq (θ - μ)) := rfl
        _ ≤ 1 / lsq μ ^ 2 * (4 / lsq μ) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 4 * (1 / lsq μ ^ 3) := by field_simp
    calc ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), f μ
        ≤ ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), 4 * (1 / lsq μ ^ 3) :=
          sum_le_sum hterm
      _ = 4 * ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), 1 / lsq μ ^ 3 := by
          rw [mul_sum]
      _ ≤ 4 * ∑ μ ∈ S', 1 / lsq μ ^ 3 := by
          gcongr
          · intro μ _ _; have := lsq_nonneg μ; positivity
          · exact filter_subset _ _
      _ ≤ 4 * (143 / R ^ 3) := by gcongr; exact sum_tail_inv_pow_three_le S hR
  -- near terms
  set Nr := S'.filter (fun μ => ¬ lsq μ ≤ 4 * lsq (θ - μ))
  set M := max (R ^ 2) (4 / 9 * lsq θ)
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hnear_geom : ∀ μ ∈ Nr, M ≤ lsq μ ∧ lsq (θ - μ) ≤ lsq θ := by
    intro μ hμ
    obtain ⟨hμ1, hμ2⟩ := mem_filter.mp hμ
    have hR2 := (mem_filter.mp hμ1).2
    push Not at hμ2
    have h4 : 4 * lsq (μ - θ) < lsq μ := by rw [lsq_sub_comm]; exact hμ2
    obtain ⟨g1, g2⟩ := near_geom h4
    refine ⟨max_le hR2.le (by linarith), ?_⟩
    linarith [lsq_nonneg (θ - μ)]
  set s := Real.sqrt (lsq θ)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = lsq θ := Real.sq_sqrt (lsq_nonneg θ)
  have hball : ∑ μ ∈ Nr, 1 / lsq (θ - μ) ≤ 26 * s := by
    rw [← sum_filter_add_sum_filter_not Nr (fun μ => θ - μ = 0)]
    have hz : ∑ μ ∈ Nr.filter (fun μ => θ - μ = 0), 1 / lsq (θ - μ) = 0 := by
      refine sum_eq_zero fun μ hμ => ?_
      rw [(mem_filter.mp hμ).2, lsq_zero, div_zero]
    rw [hz, zero_add]
    apply sum_inv_lsq_image_le _ (fun μ => θ - μ) _ hs0
    · intro μ hμ; exact (mem_filter.mp hμ).2
    · intro μ hμ
      rw [hs2]
      exact (hnear_geom μ (mem_filter.mp hμ).1).2
    · intro μ _ μ' _ h
      have h' : θ - μ = θ - μ' := h
      exact sub_right_injective h'
  have hnear : ∑ μ ∈ Nr, f μ ≤ 39 / R ^ 3 := by
    have h1 : ∑ μ ∈ Nr, f μ ≤ ∑ μ ∈ Nr, 1 / M ^ 2 * (1 / lsq (θ - μ)) := by
      apply sum_le_sum
      intro μ hμ
      have hM := (hnear_geom μ hμ).1
      have hd : 0 ≤ 1 / lsq (θ - μ) := by have := lsq_nonneg (θ - μ); positivity
      have : 1 / lsq μ ^ 2 ≤ 1 / M ^ 2 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hM0.le hM 2)
      exact mul_le_mul_of_nonneg_right this hd
    rw [← mul_sum] at h1
    have h2 : 1 / M ^ 2 * ∑ μ ∈ Nr, 1 / lsq (θ - μ) ≤ 1 / M ^ 2 * (26 * s) :=
      mul_le_mul_of_nonneg_left hball (by positivity)
    have hkey : s * R ^ 3 ≤ 3 / 2 * M ^ 2 := by
      have hθM : lsq θ ≤ 9 / 4 * M := by
        have := le_max_right (R ^ 2) (4 / 9 * lsq θ); linarith
      have hRM : R ^ 6 ≤ M ^ 3 := by
        rw [show R ^ 6 = (R ^ 2) ^ 3 by ring]
        exact pow_le_pow_left₀ (by positivity) (le_max_left _ _) 3
      have hsq : (s * R ^ 3) ^ 2 ≤ (3 / 2 * M ^ 2) ^ 2 := by
        have e1 : (s * R ^ 3) ^ 2 = s ^ 2 * R ^ 6 := by ring
        have e2 : (3 / 2 * M ^ 2) ^ 2 = 9 / 4 * M * M ^ 3 := by ring
        rw [e1, e2, hs2]
        exact mul_le_mul hθM hRM (by positivity) (by positivity)
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    have h3 : 1 / M ^ 2 * (26 * s) ≤ 39 / R ^ 3 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  calc ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), 1 / lsq μ ^ 2 * (1 / lsq (θ - μ)) +
        ∑ μ ∈ S'.filter (fun μ => ¬ lsq μ ≤ 4 * lsq (θ - μ)), 1 / lsq μ ^ 2 * (1 / lsq (θ - μ))
      = ∑ μ ∈ S'.filter (fun μ => lsq μ ≤ 4 * lsq (θ - μ)), f μ + ∑ μ ∈ Nr, f μ := rfl
    _ ≤ 4 * (143 / R ^ 3) + 39 / R ^ 3 := add_le_add hfar hnear
    _ = 611 / R ^ 3 := by ring

end FSLattice
