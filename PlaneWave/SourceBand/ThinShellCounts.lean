import PlaneWave.Flux.Flux2

/-!
# Source band block, part 1: thin-shell lattice counts and `lem:thinschur`

* `card_line_le'`, `card_piece_le'`: the line counts of `PlaneWave.Source.BulkLatticeCounts` for a slab that is not centred
  at `0` (two points of a piece differ in `F_c` by at most `w`);
* **`thin_count`** (the count behind `lem:thinschur` and `lem:band`): the transfers `θ` with
  `|θ| ≤ R` and `p + θ` in the Euclidean shell `λ ≤ |y| < λ + ρ` (`1 ≤ ρ ≤ λ`) number at most
  `6 (2R+1)² (min(3√3 ρ/2, 2R) + 1)`; `thin_count_cube` for the cube shell
  `λ ≤ ‖y‖_∞ < λ + ρ` (`6 (2R+1)² (min(ρ, 2R) + 1)`). For `R = 2ρ'`, `ρ, ρ' ≥ 1`, both are
  `≤ 750 ρ'² min(ρ, ρ')` (`thin_count_le`, `thin_count_cube_le`).
  The text's hypothesis `λ ≥ 4ρ'` is not needed.
-/

open Finset

namespace FSBand

open FSLattice

/-! ## Lines in a shifted slab -/

/-- On a line in direction `e_i`, a set whose points differ pairwise in `F_c` by at most `w`, with
`|θ_i + c_i + θ'_i + c_i| ≥ s`, has at most `w/s + 1` points. -/
lemma card_line_le' (c : Fin 3 → ℝ) (i : Fin 3) {s w : ℝ} (hs : 0 < s) (hw : 0 ≤ w)
    (F : Finset L3) (hF : ∀ θ ∈ F, ∀ θ' ∈ F, |slabF c θ - slabF c θ'| ≤ w)
    (hfib : ∀ θ ∈ F, ∀ θ' ∈ F, θ (i + 1) = θ' (i + 1) ∧ θ (i + 2) = θ' (i + 2))
    (hsign : ∀ θ ∈ F, ∀ θ' ∈ F, s ≤ |((θ i : ℝ) + c i) + ((θ' i : ℝ) + c i)|) :
    (F.card : ℝ) ≤ w / s + 1 := by
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
  have hsn := hsign θ hθ θ' hθ'
  have hd := hF θ hθ θ' hθ'
  rw [he, abs_mul] at hd
  have hprod : |(θ i : ℝ) - θ' i| * s ≤ w :=
    le_trans (mul_le_mul_of_nonneg_left hsn (abs_nonneg _)) hd
  have hle : |(θ i : ℝ) - θ' i| ≤ w / s := by
    rw [le_div_iff₀ hs]; linarith
  exact (le_abs_self _).trans hle

/-- On a line in direction `e_i`, a set inside `box N` has at most `2N + 1` points. -/
lemma card_line_box_le (i : Fin 3) (N : ℕ) (F : Finset L3) (hF : F ⊆ FSLattice.box N)
    (hfib : ∀ θ ∈ F, ∀ θ' ∈ F, θ (i + 1) = θ' (i + 1) ∧ θ (i + 2) = θ' (i + 2)) :
    (F.card : ℝ) ≤ 2 * N + 1 := by
  have hinj : Set.InjOn (fun θ : L3 => θ i) F := by
    intro θ hθ θ' hθ' he
    obtain ⟨h1, h2⟩ := hfib θ hθ θ' hθ'
    funext l
    rcases fin3_cases i l with rfl | rfl | rfl
    · exact he
    · exact h1
    · exact h2
  rw [← card_image_of_injOn hinj]
  have hsub : F.image (fun θ : L3 => θ i) ⊆ Icc (-(N : ℤ)) N := by
    intro x hx
    obtain ⟨θ, hθ, rfl⟩ := mem_image.mp hx
    exact mem_Icc.mpr ((mem_box.mp (hF hθ)) i)
  have hc := card_le_card hsub
  rw [Int.card_Icc] at hc
  have e : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, Int.toNat_natCast] at hc
  have : ((F.image (fun θ : L3 => θ i)).card : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at this
  exact this

/-- A one-signed piece of a shifted slab in direction `i`, inside `box N`:
at most `(2N+1)² (min(w/s, 2N) + 1)` points. -/
lemma card_piece_le' (c : Fin 3 → ℝ) (i : Fin 3) {s w : ℝ} (hs : 0 < s) (hw : 0 ≤ w) (N : ℕ)
    (S : Finset L3) (hS : S ⊆ FSLattice.box N) (hF : ∀ θ ∈ S, ∀ θ' ∈ S, |slabF c θ - slabF c θ'| ≤ w)
    (hsign : ∀ θ ∈ S, ∀ θ' ∈ S, s ≤ |((θ i : ℝ) + c i) + ((θ' i : ℝ) + c i)|) :
    (S.card : ℝ) ≤ (2 * N + 1) ^ 2 * (min (w / s) (2 * N) + 1) := by
  set lab := fun θ : L3 => (θ (i + 1), θ (i + 2))
  have hline : ∀ b ∈ S.image lab, ((S.filter fun θ => lab θ = b).card : ℝ) ≤ min (w / s) (2 * N) + 1 := by
    intro b _
    have hfib : ∀ θ ∈ S.filter (fun θ => lab θ = b), ∀ θ' ∈ S.filter (fun θ => lab θ = b),
        θ (i + 1) = θ' (i + 1) ∧ θ (i + 2) = θ' (i + 2) := by
      intro θ hθ θ' hθ'
      have e := (mem_filter.mp hθ).2.trans (mem_filter.mp hθ').2.symm
      exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
    have h1 := card_line_le' c i hs hw _ (fun θ hθ θ' hθ' =>
      hF θ (mem_filter.mp hθ).1 θ' (mem_filter.mp hθ').1) hfib
      (fun θ hθ θ' hθ' => hsign θ (mem_filter.mp hθ).1 θ' (mem_filter.mp hθ').1)
    have h2 := card_line_box_le i N _ (fun θ hθ => hS (mem_filter.mp hθ).1) hfib
    rcases le_total (w / s) (2 * N) with h | h
    · rw [min_eq_left h]; exact h1
    · rw [min_eq_right h]; linarith
  have hn : ∀ b ∈ S.image lab, (S.filter fun θ => lab θ = b).card ≤
      ⌊min (w / s) (2 * N) + 1⌋₊ := fun b hb => Nat.le_floor (hline b hb)
  have hc := card_le_mul_card_image S _ hn
  have hc' : (S.card : ℝ) ≤ (⌊min (w / s) (2 * N) + 1⌋₊ : ℝ) * ((S.image lab).card : ℝ) := by
    exact_mod_cast hc
  have hm0 : 0 ≤ min (w / s) (2 * N) + 1 := by
    have : 0 ≤ min (w / s) (2 * N) := le_min (by positivity) (by positivity)
    linarith
  have hfl : (⌊min (w / s) (2 * N) + 1⌋₊ : ℝ) ≤ min (w / s) (2 * N) + 1 := Nat.floor_le hm0
  have hl := card_labels_le i N S hS
  have h0 : (0 : ℝ) ≤ ((S.image lab).card : ℝ) := Nat.cast_nonneg _
  calc (S.card : ℝ) ≤ (⌊min (w / s) (2 * N) + 1⌋₊ : ℝ) * ((S.image lab).card : ℝ) := hc'
    _ ≤ (min (w / s) (2 * N) + 1) * ((2 * N + 1) ^ 2) := mul_le_mul hfl hl h0 hm0
    _ = _ := by ring

/-! ## Thin Euclidean shells -/

/-- `slabF p θ = |p + θ|² - |p|²`. -/
lemma slabF_shift (p θ : L3) :
    slabF (fun i => (p i : ℝ)) θ = lsq (p + θ) - lsq p := by
  rw [slabF_eq_sum]
  simp only [lsq, Pi.add_apply, Int.cast_add, Fin.sum_univ_three]
  ring

/-- Every lattice vector has a coordinate carrying a third of its square. -/
lemma exists_big_coord (y : L3) : ∃ i : Fin 3, lsq y ≤ 3 * (y i : ℝ) ^ 2 := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have e : lsq y = (y 0 : ℝ) ^ 2 + (y 1 : ℝ) ^ 2 + (y 2 : ℝ) ^ 2 := rfl
  linarith

/-- **The thin-shell count** (Euclidean): the transfers `θ ∈ S` with `|θ| ≤ R` and
`λ ≤ |p + θ| < λ + ρ`, `1 ≤ ρ ≤ λ`, number at most `6 (2N+1)² (min(3√3 ρ/2, 2N) + 1)`,
`N = ⌊R⌋`. -/
theorem thin_count (p : L3) {lam ρ R : ℝ} (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam) (hR : 0 ≤ R)
    (S : Finset L3)
    (hS : ∀ θ ∈ S, lsq θ ≤ R ^ 2 ∧ lam ^ 2 ≤ lsq (p + θ) ∧ lsq (p + θ) < (lam + ρ) ^ 2) :
    (S.card : ℝ) ≤ 6 * (2 * ⌊R⌋₊ + 1) ^ 2 * (min (3 * Real.sqrt 3 / 2 * ρ) (2 * ⌊R⌋₊) + 1) := by
  classical
  have hl0 : 0 < lam := by linarith
  set N := ⌊R⌋₊
  set c : Fin 3 → ℝ := fun i => (p i : ℝ)
  have hbox : S ⊆ FSLattice.box N := fun θ hθ => mem_box_floor_of_lsq_le hR (hS θ hθ).1
  -- the six pieces
  set piece : Fin 3 → Bool → Finset L3 := fun i b => S.filter fun θ =>
    lsq (p + θ) ≤ 3 * (((p + θ) i : ℤ) : ℝ) ^ 2 ∧ (b = true ↔ 0 ≤ ((p + θ) i : ℤ))
  have hcover : S ⊆ (Finset.univ : Finset (Fin 3 × Bool)).biUnion fun ib => piece ib.1 ib.2 := by
    intro θ hθ
    obtain ⟨i, hi⟩ := exists_big_coord (p + θ)
    rw [mem_biUnion]
    refine ⟨(i, decide (0 ≤ ((p + θ) i : ℤ))), mem_univ _, ?_⟩
    simp only [piece, mem_filter]
    exact ⟨hθ, hi, by simp⟩
  have hw : (lam + ρ) ^ 2 - lam ^ 2 ≤ 3 * ρ * lam := by nlinarith
  have hs : 0 < 2 * lam / Real.sqrt 3 := by positivity
  have hpiece : ∀ i b, ((piece i b).card : ℝ) ≤
      (2 * N + 1) ^ 2 * (min (3 * Real.sqrt 3 / 2 * ρ) (2 * N) + 1) := by
    intro i b
    have hsub : piece i b ⊆ FSLattice.box N := fun θ hθ => hbox (mem_filter.mp hθ).1
    have h := card_piece_le' c i hs (by nlinarith : (0 : ℝ) ≤ (lam + ρ) ^ 2 - lam ^ 2) N
      (piece i b) hsub ?_ ?_
    · refine h.trans ?_
      have hq : ((lam + ρ) ^ 2 - lam ^ 2) / (2 * lam / Real.sqrt 3) ≤ 3 * Real.sqrt 3 / 2 * ρ := by
        rw [div_le_iff₀ hs]
        have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
        have : 3 * Real.sqrt 3 / 2 * ρ * (2 * lam / Real.sqrt 3) = 3 * ρ * lam := by
          field_simp
        linarith
      have hmin : min (((lam + ρ) ^ 2 - lam ^ 2) / (2 * lam / Real.sqrt 3)) (2 * (N : ℝ)) ≤
          min (3 * Real.sqrt 3 / 2 * ρ) (2 * (N : ℝ)) := min_le_min_right _ hq
      have : (0 : ℝ) ≤ (2 * N + 1) ^ 2 := by positivity
      nlinarith
    · intro θ hθ θ' hθ'
      have h1 := (hS θ (mem_filter.mp hθ).1)
      have h2 := (hS θ' (mem_filter.mp hθ').1)
      rw [slabF_shift, slabF_shift, abs_le]
      constructor <;> nlinarith
    · intro θ hθ θ' hθ'
      obtain ⟨hθS, hbig, hsgn⟩ := mem_filter.mp hθ
      obtain ⟨hθS', hbig', hsgn'⟩ := mem_filter.mp hθ'
      have h1 := (hS θ hθS).2.1
      have h2 := (hS θ' hθS').2.1
      have e1 : ((θ i : ℝ) + c i) = (((p + θ) i : ℤ) : ℝ) := by
        simp only [c, Pi.add_apply, Int.cast_add]; ring
      have e2 : ((θ' i : ℝ) + c i) = (((p + θ') i : ℤ) : ℝ) := by
        simp only [c, Pi.add_apply, Int.cast_add]; ring
      have hsame : (0 ≤ (((p + θ) i : ℤ) : ℝ) ∧ 0 ≤ (((p + θ') i : ℤ) : ℝ)) ∨
          ((((p + θ) i : ℤ) : ℝ) ≤ 0 ∧ (((p + θ') i : ℤ) : ℝ) ≤ 0) := by
        cases b
        · right
          have a1 : ¬ (0 ≤ ((p + θ) i : ℤ)) := fun h => by simpa using hsgn.mpr h
          have a2 : ¬ (0 ≤ ((p + θ') i : ℤ)) := fun h => by simpa using hsgn'.mpr h
          push Not at a1 a2
          exact ⟨by exact_mod_cast a1.le, by exact_mod_cast a2.le⟩
        · left
          have a1 := hsgn.mp rfl
          have a2 := hsgn'.mp rfl
          exact ⟨by exact_mod_cast a1, by exact_mod_cast a2⟩
      rw [e1, e2]
      set y := (((p + θ) i : ℤ) : ℝ)
      set y' := (((p + θ') i : ℤ) : ℝ)
      -- `|y| ≥ λ/√3` and `y`, `y'` have the same sign
      have hy : lam / Real.sqrt 3 ≤ |y| := by
        rw [div_le_iff₀ (by positivity)]
        have h3 : lam ^ 2 ≤ 3 * y ^ 2 := h1.trans hbig
        have : (lam) ^ 2 ≤ (|y| * Real.sqrt 3) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num), sq_abs]; linarith
        exact (pow_le_pow_iff_left₀ hl0.le (by positivity) two_ne_zero).mp this
      have hy' : lam / Real.sqrt 3 ≤ |y'| := by
        rw [div_le_iff₀ (by positivity)]
        have h3 : lam ^ 2 ≤ 3 * y' ^ 2 := h2.trans hbig'
        have : (lam) ^ 2 ≤ (|y'| * Real.sqrt 3) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num), sq_abs]; linarith
        exact (pow_le_pow_iff_left₀ hl0.le (by positivity) two_ne_zero).mp this
      have hpos : 0 < lam / Real.sqrt 3 := by positivity
      have e3 : 2 * lam / Real.sqrt 3 = lam / Real.sqrt 3 + lam / Real.sqrt 3 := by ring
      rw [e3]
      rcases hsame with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · rw [abs_of_nonneg a1] at hy
        rw [abs_of_nonneg a2] at hy'
        rw [abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos a1] at hy
        rw [abs_of_nonpos a2] at hy'
        rw [abs_of_nonpos (by linarith)]; linarith
  calc (S.card : ℝ) ≤ (((Finset.univ : Finset (Fin 3 × Bool)).biUnion
        fun ib => piece ib.1 ib.2).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ ∑ ib : Fin 3 × Bool, ((piece ib.1 ib.2).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _ib : Fin 3 × Bool, (2 * N + 1) ^ 2 * (min (3 * Real.sqrt 3 / 2 * ρ) (2 * N) + 1) :=
        sum_le_sum fun ib _ => hpiece ib.1 ib.2
    _ = 6 * (2 * N + 1) ^ 2 * (min (3 * Real.sqrt 3 / 2 * ρ) (2 * N) + 1) := by
        rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
        simp only [nsmul_eq_mul]
        push_cast; ring

/-- `thin_count` at `R = 2ρ'`: `≤ 750 ρ'² min(ρ, ρ')` for `ρ, ρ' ≥ 1`. -/
theorem thin_count_le (p : L3) {lam ρ ρ' : ℝ} (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam) (hρ' : 1 ≤ ρ')
    (S : Finset L3)
    (hS : ∀ θ ∈ S, lsq θ ≤ (2 * ρ') ^ 2 ∧ lam ^ 2 ≤ lsq (p + θ) ∧ lsq (p + θ) < (lam + ρ) ^ 2) :
    (S.card : ℝ) ≤ 750 * ρ' ^ 2 * min ρ ρ' := by
  have h := thin_count p hρ hρl (by linarith : (0 : ℝ) ≤ 2 * ρ') S hS
  set N := ⌊2 * ρ'⌋₊
  have hN : (N : ℝ) ≤ 2 * ρ' := Nat.floor_le (by linarith)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h3 : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hmin : min (3 * Real.sqrt 3 / 2 * ρ) (2 * N) + 1 ≤ 5 * min ρ ρ' := by
    rcases le_total ρ ρ' with hle | hle
    · rw [min_eq_left hle]
      have : min (3 * Real.sqrt 3 / 2 * ρ) (2 * N) ≤ 3 * Real.sqrt 3 / 2 * ρ := min_le_left _ _
      nlinarith
    · rw [min_eq_right hle]
      have : min (3 * Real.sqrt 3 / 2 * ρ) (2 * N) ≤ 2 * N := min_le_right _ _
      linarith
  have hbox : (2 * N + 1 : ℝ) ^ 2 ≤ 25 * ρ' ^ 2 := by nlinarith
  have hm0 : 0 ≤ min (3 * Real.sqrt 3 / 2 * ρ) (2 * N) + 1 := by
    have : 0 ≤ min (3 * Real.sqrt 3 / 2 * ρ) (2 * N) := le_min (by positivity) (by positivity)
    linarith
  calc (S.card : ℝ) ≤ 6 * (2 * N + 1) ^ 2 * (min (3 * Real.sqrt 3 / 2 * ρ) (2 * N) + 1) := h
    _ ≤ 6 * (25 * ρ' ^ 2) * (5 * min ρ ρ') := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hbox (by norm_num)) hmin hm0 (by positivity)
    _ = 750 * ρ' ^ 2 * min ρ ρ' := by ring

/-! ## Thin cube shells -/

/-- The sup norm of a lattice vector. -/
noncomputable def supn (y : L3) : ℝ := max |(y 0 : ℝ)| (max |(y 1 : ℝ)| |(y 2 : ℝ)|)

lemma abs_le_supn (y : L3) (i : Fin 3) : |(y i : ℝ)| ≤ supn y := by
  unfold supn
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

lemma exists_supn_coord (y : L3) : ∃ i : Fin 3, |(y i : ℝ)| = supn y := by
  unfold supn
  rcases le_total |(y 1 : ℝ)| |(y 2 : ℝ)| with h12 | h12
  · rw [max_eq_right h12]
    rcases le_total |(y 0 : ℝ)| |(y 2 : ℝ)| with h02 | h02
    · exact ⟨2, by rw [max_eq_right h02]⟩
    · exact ⟨0, by rw [max_eq_left h02]⟩
  · rw [max_eq_left h12]
    rcases le_total |(y 0 : ℝ)| |(y 1 : ℝ)| with h01 | h01
    · exact ⟨1, by rw [max_eq_right h01]⟩
    · exact ⟨0, by rw [max_eq_left h01]⟩

/-- **The thin-shell count** (cube): the transfers `θ ∈ S` with `|θ| ≤ R` and
`λ ≤ ‖p + θ‖_∞ < λ + ρ`, `ρ ≥ 0`, number at most `6 (2N+1)² (min(ρ, 2N) + 1)`. -/
theorem thin_count_cube (p : L3) {lam ρ R : ℝ} (hρ : 0 ≤ ρ) (hR : 0 ≤ R) (S : Finset L3)
    (hS : ∀ θ ∈ S, lsq θ ≤ R ^ 2 ∧ lam ≤ supn (p + θ) ∧ supn (p + θ) < lam + ρ) :
    (S.card : ℝ) ≤ 6 * (2 * ⌊R⌋₊ + 1) ^ 2 * (min ρ (2 * ⌊R⌋₊) + 1) := by
  classical
  set N := ⌊R⌋₊
  have hbox : S ⊆ FSLattice.box N := fun θ hθ => mem_box_floor_of_lsq_le hR (hS θ hθ).1
  set piece : Fin 3 → Bool → Finset L3 := fun i b => S.filter fun θ =>
    (b = true → lam ≤ (((p + θ) i : ℤ) : ℝ)) ∧ (b = false → lam ≤ -(((p + θ) i : ℤ) : ℝ))
  have hcover : S ⊆ (Finset.univ : Finset (Fin 3 × Bool)).biUnion fun ib => piece ib.1 ib.2 := by
    intro θ hθ
    obtain ⟨i, hi⟩ := exists_supn_coord (p + θ)
    have h1 := (hS θ hθ).2.1
    rw [mem_biUnion]
    rcases le_total 0 (((p + θ) i : ℤ) : ℝ) with h0 | h0
    · refine ⟨(i, true), mem_univ _, ?_⟩
      simp only [piece, mem_filter]
      refine ⟨hθ, fun _ => ?_, fun h => absurd h (by simp)⟩
      rw [abs_of_nonneg h0] at hi; linarith
    · refine ⟨(i, false), mem_univ _, ?_⟩
      simp only [piece, mem_filter]
      refine ⟨hθ, fun h => absurd h (by simp), fun _ => ?_⟩
      rw [abs_of_nonpos h0] at hi; linarith
  have hpiece : ∀ i b, ((piece i b).card : ℝ) ≤ (2 * N + 1) ^ 2 * (min ρ (2 * N) + 1) := by
    intro i b
    set lab := fun θ : L3 => (θ (i + 1), θ (i + 2))
    have hline : ∀ x ∈ (piece i b).image lab,
        (((piece i b).filter fun θ => lab θ = x).card : ℝ) ≤ min ρ (2 * N) + 1 := by
      intro x _
      have hfib : ∀ θ ∈ (piece i b).filter (fun θ => lab θ = x),
          ∀ θ' ∈ (piece i b).filter (fun θ => lab θ = x),
          θ (i + 1) = θ' (i + 1) ∧ θ (i + 2) = θ' (i + 2) := by
        intro θ hθ θ' hθ'
        have e := (mem_filter.mp hθ).2.trans (mem_filter.mp hθ').2.symm
        exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
      have hsubb : (piece i b).filter (fun θ => lab θ = x) ⊆ FSLattice.box N :=
        fun θ hθ => hbox (mem_filter.mp (mem_filter.mp hθ).1).1
      have h2 := card_line_box_le i N _ hsubb hfib
      -- the diameter `ρ`
      have hinj : Set.InjOn (fun θ : L3 => θ i) ((piece i b).filter (fun θ => lab θ = x)) := by
        intro θ hθ θ' hθ' he
        obtain ⟨h1, h2⟩ := hfib θ hθ θ' hθ'
        funext l
        rcases fin3_cases i l with rfl | rfl | rfl
        · exact he
        · exact h1
        · exact h2
      have h1 : ((((piece i b).filter fun θ => lab θ = x).card : ℕ) : ℝ) ≤ ρ + 1 := by
        rw [← card_image_of_injOn hinj]
        apply card_int_le_of_diam _ hρ
        intro u hu v hv
        obtain ⟨θ, hθ, rfl⟩ := mem_image.mp hu
        obtain ⟨θ', hθ', rfl⟩ := mem_image.mp hv
        have hθp := (mem_filter.mp hθ).1
        have hθp' := (mem_filter.mp hθ').1
        obtain ⟨hθS, hA, hB⟩ := mem_filter.mp hθp
        obtain ⟨hθS', hA', hB'⟩ := mem_filter.mp hθp'
        have hs1 := (hS θ hθS).2.2
        have hs2 := (hS θ' hθS').2.2
        have hb1 := abs_le_supn (p + θ) i
        have hb2 := abs_le_supn (p + θ') i
        have e1 : (((p + θ) i : ℤ) : ℝ) = (p i : ℝ) + θ i := by simp
        have e2 : (((p + θ') i : ℤ) : ℝ) = (p i : ℝ) + θ' i := by simp
        rw [e1] at hA hB hb1
        rw [e2] at hA' hB' hb2
        rw [abs_le] at hb1 hb2
        cases b
        · have a1 := hB rfl; have a2 := hB' rfl
          linarith
        · have a1 := hA rfl; have a2 := hA' rfl
          linarith
      rcases le_total ρ (2 * N) with h | h
      · rw [min_eq_left h]; exact h1
      · rw [min_eq_right h]; linarith
    have hn : ∀ x ∈ (piece i b).image lab, ((piece i b).filter fun θ => lab θ = x).card ≤
        ⌊min ρ (2 * N) + 1⌋₊ := fun x hx => Nat.le_floor (hline x hx)
    have hc := card_le_mul_card_image (piece i b) _ hn
    have hc' : ((piece i b).card : ℝ) ≤ (⌊min ρ (2 * N) + 1⌋₊ : ℝ) *
        (((piece i b).image lab).card : ℝ) := by exact_mod_cast hc
    have hm0 : 0 ≤ min ρ (2 * N) + 1 := by
      have : 0 ≤ min ρ (2 * N) := le_min hρ (by positivity)
      linarith
    have hfl : (⌊min ρ (2 * N) + 1⌋₊ : ℝ) ≤ min ρ (2 * N) + 1 := Nat.floor_le hm0
    have hl := card_labels_le i N (piece i b) (fun θ hθ => hbox (mem_filter.mp hθ).1)
    have h0 : (0 : ℝ) ≤ (((piece i b).image lab).card : ℝ) := Nat.cast_nonneg _
    calc ((piece i b).card : ℝ) ≤ (⌊min ρ (2 * N) + 1⌋₊ : ℝ) *
          (((piece i b).image lab).card : ℝ) := hc'
      _ ≤ (min ρ (2 * N) + 1) * ((2 * N + 1) ^ 2) := mul_le_mul hfl hl h0 hm0
      _ = _ := by ring
  calc (S.card : ℝ) ≤ (((Finset.univ : Finset (Fin 3 × Bool)).biUnion
        fun ib => piece ib.1 ib.2).card : ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ ∑ ib : Fin 3 × Bool, ((piece ib.1 ib.2).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _ib : Fin 3 × Bool, (2 * N + 1) ^ 2 * (min ρ (2 * N) + 1) :=
        sum_le_sum fun ib _ => hpiece ib.1 ib.2
    _ = 6 * (2 * N + 1) ^ 2 * (min ρ (2 * N) + 1) := by
        rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
        simp only [nsmul_eq_mul]
        push_cast; ring

/-- `thin_count_cube` at `R = 2ρ'`: `≤ 750 ρ'² min(ρ, ρ')` for `ρ, ρ' ≥ 1`. -/
theorem thin_count_cube_le (p : L3) {lam ρ ρ' : ℝ} (hρ : 1 ≤ ρ) (hρ' : 1 ≤ ρ') (S : Finset L3)
    (hS : ∀ θ ∈ S, lsq θ ≤ (2 * ρ') ^ 2 ∧ lam ≤ supn (p + θ) ∧ supn (p + θ) < lam + ρ) :
    (S.card : ℝ) ≤ 750 * ρ' ^ 2 * min ρ ρ' := by
  have h := thin_count_cube p (by linarith : (0 : ℝ) ≤ ρ) (by linarith : (0 : ℝ) ≤ 2 * ρ') S hS
  set N := ⌊2 * ρ'⌋₊
  have hN : (N : ℝ) ≤ 2 * ρ' := Nat.floor_le (by linarith)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hmin : min ρ (2 * N) + 1 ≤ 5 * min ρ ρ' := by
    rcases le_total ρ ρ' with hle | hle
    · rw [min_eq_left hle]
      have : min ρ (2 * N) ≤ ρ := min_le_left _ _
      linarith
    · rw [min_eq_right hle]
      have : min ρ (2 * N) ≤ 2 * N := min_le_right _ _
      linarith
  have hbox : (2 * N + 1 : ℝ) ^ 2 ≤ 25 * ρ' ^ 2 := by nlinarith
  have hm0 : 0 ≤ min ρ (2 * N) + 1 := by
    have : 0 ≤ min ρ (2 * N) := le_min (by linarith) (by positivity)
    linarith
  calc (S.card : ℝ) ≤ 6 * (2 * N + 1) ^ 2 * (min ρ (2 * N) + 1) := h
    _ ≤ 6 * (25 * ρ' ^ 2) * (5 * min ρ ρ') := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hbox (by norm_num)) hmin hm0 (by positivity)
    _ = 750 * ρ' ^ 2 * min ρ ρ' := by ring

end FSBand

/-! ## `lem:thinschur` on `ℓ²` -/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal FSFlux

namespace FSBand

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- On a moved register the transfer is `+ν` (the lead) or `-ν` (its partner), uniformly. -/
lemma tr_moved_uniform {j : Ch eta} {a : Fin eta} (ha : a ∈ moved j) :
    (∀ x : Lattice3, tr j x a = x) ∨ (∀ x : Lattice3, tr j x a = -x) := by
  cases j with
  | inl b =>
    simp only [moved, Finset.mem_singleton] at ha
    subst ha
    left; intro x; simp [tr]
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    simp only [moved, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · left; intro x; simp [tr, Pi.single_eq_of_ne hne]
    · right; intro x; simp [tr, Pi.single_eq_of_ne hne.symm]

variable (sys : CoulombSystem eta ν) (L : ℝ)

open Classical in
/-- **The thin-shell kernel** of `lem:thinschur`: the channel-`j` part of the potential with hops
`ρ' ≤ |θ| < 2ρ'`, restricted to outputs whose register `a` lies in the shell `sh` (lattice
units; `shE` Euclidean, `shC` cube). -/
noncomputable def tsK (j : Ch eta) (a : Fin eta) (sh : Lattice3 → Prop) (ρ' : ℝ) (q p : Cf eta) : ℂ :=
  if sh (q a) ∧ OnCh j q p ∧
      ρ' ^ 2 ≤ nsq (q (lead j) - p (lead j)) ∧ nsq (q (lead j) - p (lead j)) < (2 * ρ') ^ 2
  then potKernel sys L q p else 0

variable {sys L}

open Classical in
/-- The Coulomb sum over a hop shell: `Σ_{ρ' ≤ |θ| < 2ρ'} 1/|θ|² ≤ 52 ρ'`. -/
lemma hop_shell_sum_le {ρ' : ℝ} (hρ' : 1 ≤ ρ') :
    Summable (fun θ : Lattice3 => if ρ' ^ 2 ≤ nsq θ ∧ nsq θ < (2 * ρ') ^ 2 then 1 / nsq θ else 0) ∧
      ∑' θ : Lattice3, (if ρ' ^ 2 ≤ nsq θ ∧ nsq θ < (2 * ρ') ^ 2 then 1 / nsq θ else 0) ≤
        52 * ρ' := by
  set N := ⌊2 * ρ'⌋₊
  have hsupp : ∀ θ ∉ FSLattice.box N,
      (if ρ' ^ 2 ≤ nsq θ ∧ nsq θ < (2 * ρ') ^ 2 then 1 / nsq θ else 0) = 0 := by
    intro θ hθ
    rw [if_neg]
    rintro ⟨-, h2⟩
    exact hθ (mem_box_floor_of_lsq_le (by linarith) h2.le)
  refine ⟨summable_of_ne_finset_zero hsupp, ?_⟩
  rw [tsum_eq_sum hsupp, ← Finset.sum_filter]
  refine le_trans ?_ (le_of_le_of_eq (sum_inv_lsq_ball_le' (by linarith : (0 : ℝ) ≤ 2 * ρ') N)
    (by ring))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro θ hθ
    obtain ⟨hθb, h1, h2⟩ := Finset.mem_filter.mp hθ
    refine Finset.mem_filter.mpr ⟨hθb, ?_, h2.le⟩
    intro h0
    rw [h0] at h1
    have : nsq (0 : Lattice3) = 0 := by simp [nsq]
    rw [this] at h1
    nlinarith
  · intro θ _ _
    exact div_nonneg zero_le_one (lsq_nonneg θ)

open Classical in
/-- The hop-shell count in a thin shell, as a series of `1/|θ|²` weights: if the transfers
`|θ| ≤ 2ρ'` with `x + θ` in the shell number at most `N₀`, then
`Σ_{ρ' ≤ |θ| < 2ρ', x ± θ ∈ shell} 1/|θ|² ≤ N₀/ρ'²`. -/
lemma hop_shell_thin_sum_le (x : Lattice3) (sh : Lattice3 → Prop) [DecidablePred sh] {ρ' N₀ : ℝ}
    (hρ' : 1 ≤ ρ')
    (hcnt : ∀ T : Finset Lattice3, (∀ θ ∈ T, lsq θ ≤ (2 * ρ') ^ 2 ∧ sh (x + θ)) → (T.card : ℝ) ≤ N₀)
    (σ : Lattice3 → Lattice3) (hσ : σ = id ∨ σ = Neg.neg) :
    Summable (fun θ : Lattice3 => if sh (x + σ θ) ∧
        ρ' ^ 2 ≤ nsq θ ∧ nsq θ < (2 * ρ') ^ 2 then 1 / nsq θ else 0) ∧
      ∑' θ : Lattice3, (if sh (x + σ θ) ∧
        ρ' ^ 2 ≤ nsq θ ∧ nsq θ < (2 * ρ') ^ 2 then 1 / nsq θ else 0) ≤ N₀ / ρ' ^ 2 := by
  set N := ⌊2 * ρ'⌋₊
  set f : Lattice3 → ℝ := fun θ => if sh (x + σ θ) ∧
        ρ' ^ 2 ≤ nsq θ ∧ nsq θ < (2 * ρ') ^ 2 then 1 / nsq θ else 0
  have hsupp : ∀ θ ∉ FSLattice.box N, f θ = 0 := by
    intro θ hθ
    simp only [f]
    rw [if_neg]
    rintro ⟨-, -, h2⟩
    exact hθ (mem_box_floor_of_lsq_le (by linarith) h2.le)
  refine ⟨summable_of_ne_finset_zero hsupp, ?_⟩
  rw [tsum_eq_sum hsupp]
  set T := (FSLattice.box N).filter fun θ => sh (x + σ θ) ∧
        ρ' ^ 2 ≤ nsq θ ∧ nsq θ < (2 * ρ') ^ 2
  have hsum : ∑ θ ∈ FSLattice.box N, f θ = ∑ θ ∈ T, 1 / nsq θ := by
    simp only [f, T]; rw [Finset.sum_filter]
  rw [hsum]
  have hterm : ∀ θ ∈ T, 1 / nsq θ ≤ 1 / ρ' ^ 2 := by
    intro θ hθ
    have h1 := (Finset.mem_filter.mp hθ).2.2.1
    exact one_div_le_one_div_of_le (by positivity) h1
  have hcard : (T.card : ℝ) ≤ N₀ := by
    rcases hσ with rfl | rfl
    · apply hcnt T
      intro θ hθ
      obtain ⟨-, h1, -, h4⟩ := Finset.mem_filter.mp hθ
      exact ⟨h4.le, h1⟩
    · have hinj : Function.Injective (Neg.neg : Lattice3 → Lattice3) := neg_injective
      rw [← Finset.card_image_of_injective T hinj]
      apply hcnt _
      intro θ hθ
      obtain ⟨θ₀, hθ₀, rfl⟩ := Finset.mem_image.mp hθ
      obtain ⟨-, h1, -, h4⟩ := Finset.mem_filter.mp hθ₀
      refine ⟨?_, h1⟩
      have : lsq (-θ₀) = nsq θ₀ := by simp [lsq, nsq]
      rw [this]; exact h4.le
  calc ∑ θ ∈ T, 1 / nsq θ ≤ ∑ _θ ∈ T, 1 / ρ' ^ 2 := Finset.sum_le_sum hterm
    _ = T.card * (1 / ρ' ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N₀ * (1 / ρ' ^ 2) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = N₀ / ρ' ^ 2 := by ring

open Classical in
/-- **`lem:thinschur`, general shell**: for a register `a` moved by channel `j`, hop radius
`ρ' ≥ 1` and a shell `sh` whose `2ρ'`-ball pieces carry at most `N₀` lattice points, the
thin-shell kernel has Schur rows `≤ 52 c_j ρ'` and columns `≤ c_j N₀/ρ'²`. -/
theorem thinschur_gen (hL : 0 < L) {j : Ch eta} {a : Fin eta} (ha : a ∈ moved j)
    (sh : Lattice3 → Prop) [DecidablePred sh] {ρ' N₀ : ℝ} (hρ' : 1 ≤ ρ')
    (hcnt : ∀ (x : Lattice3) (T : Finset Lattice3),
      (∀ θ ∈ T, lsq θ ≤ (2 * ρ') ^ 2 ∧ sh (x + θ)) → (T.card : ℝ) ≤ N₀) :
    SchurBound (tsK sys L j a sh ρ') (52 * chC sys L j * ρ') (chC sys L j * (N₀ / ρ' ^ 2)) := by
  classical
  have hc := chC_nonneg sys hL j
  set c := chC sys L j
  set gR : Lattice3 → ℝ := fun θ =>
    if ρ' ^ 2 ≤ nsq θ ∧ nsq θ < (2 * ρ') ^ 2 then c * (1 / nsq θ) else 0
  set gC : Lattice3 → Lattice3 → ℝ := fun y θ =>
    if sh y ∧ ρ' ^ 2 ≤ nsq θ ∧ nsq θ < (2 * ρ') ^ 2
    then c * (1 / nsq θ) else 0
  have hgR0 : ∀ θ, 0 ≤ gR θ := fun θ => by
    simp only [gR]; split_ifs
    · exact mul_nonneg hc (div_nonneg zero_le_one (nsq_nonneg _))
    · exact le_rfl
  have hgC0 : ∀ y θ, 0 ≤ gC y θ := fun y θ => by
    simp only [gC]; split_ifs
    · exact mul_nonneg hc (div_nonneg zero_le_one (nsq_nonneg _))
    · exact le_rfl
  -- the pointwise bounds
  have hpt : ∀ q p, ‖tsK sys L j a sh ρ' q p‖ ≤
      (if OnCh j q p then gC (q a) (q (lead j) - p (lead j)) else 0) := by
    intro q p
    unfold tsK
    by_cases h : sh (q a) ∧ OnCh j q p ∧
        ρ' ^ 2 ≤ nsq (q (lead j) - p (lead j)) ∧ nsq (q (lead j) - p (lead j)) < (2 * ρ') ^ 2
    · obtain ⟨hs, hon, h1, h2⟩ := h
      rw [if_pos ⟨hs, hon, h1, h2⟩, if_pos hon]
      simp only [gC]
      rw [if_pos ⟨hs, h1, h2⟩]
      have hqp : q ≠ p := by
        intro hqp; rw [hqp, sub_self] at h1
        have : nsq (0 : Lattice3) = 0 := by simp [nsq]
        rw [this] at h1; nlinarith
      have := norm_potKernel_le_ch (sys := sys) hL hon hqp
      rw [mul_one_div]; exact this
    · rw [if_neg h, norm_zero]
      split_ifs
      · exact hgC0 _ _
      · exact le_rfl
  have hCR : ∀ y θ, gC y θ ≤ gR θ := by
    intro y θ
    simp only [gC, gR]
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd h1.2 h2
    · exact mul_nonneg hc (div_nonneg zero_le_one (nsq_nonneg _))
    · exact le_rfl
  have hptR : ∀ q p, ‖tsK sys L j a sh ρ' q p‖ ≤
      (if OnCh j q p then gR (q (lead j) - p (lead j)) else 0) := by
    intro q p
    refine (hpt q p).trans ?_
    split_ifs
    · exact hCR _ _
    · exact le_rfl
  have hR := hop_shell_sum_le hρ'
  have hgR_s : Summable gR := by
    refine (hR.1.mul_left c).congr fun θ => ?_
    simp only [gR]; split_ifs <;> simp
  have hgR_t : ∑' θ, gR θ ≤ 52 * c * ρ' := by
    have e : ∑' θ, gR θ = c * ∑' θ : Lattice3,
        (if ρ' ^ 2 ≤ nsq θ ∧ nsq θ < (2 * ρ') ^ 2 then 1 / nsq θ else 0) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun θ => ?_
      simp only [gR]; split_ifs <;> simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hR.2 hc
    linarith
  -- rows
  have hrow_s : ∀ q, Summable fun p => (if OnCh j q p then gR (q (lead j) - p (lead j)) else 0) := by
    intro q
    rw [summable_row_iff]
    simp only [lead_sub_tr]
    exact hgR_s
  -- columns: the uniform sign of the moved register
  obtain ⟨σ, hσ, htr⟩ : ∃ σ : Lattice3 → Lattice3, (σ = id ∨ σ = Neg.neg) ∧
      ∀ x, tr j x a = σ x := by
    rcases tr_moved_uniform ha with h | h
    · exact ⟨id, Or.inl rfl, fun x => h x⟩
    · exact ⟨Neg.neg, Or.inr rfl, fun x => h x⟩
  have hcol_eq : ∀ p (x : Lattice3), gC ((p + tr j x) a) x = c *
      (if sh (p a + σ x) ∧
        ρ' ^ 2 ≤ nsq x ∧ nsq x < (2 * ρ') ^ 2 then 1 / nsq x else 0) := by
    intro p x
    simp only [gC, Pi.add_apply, htr]
    split_ifs <;> simp
  have hT := fun p : Cf eta => hop_shell_thin_sum_le (p a) sh hρ' (hcnt (p a)) σ hσ
  have hcol_s : ∀ p, Summable fun q => (if OnCh j q p then gC (q a) (q (lead j) - p (lead j)) else 0) := by
    intro p
    rw [summable_col_iff]
    simp only [lead_add_tr]
    refine ((hT p).1.mul_left c).congr fun x => ?_
    rw [hcol_eq]
  refine ⟨fun q => ?_, fun q => ?_, fun p => ?_, fun p => ?_⟩
  · exact (hrow_s q).of_nonneg_of_le (fun _ => norm_nonneg _) (hptR q)
  · calc ∑' p, ‖tsK sys L j a sh ρ' q p‖
        ≤ ∑' p, (if OnCh j q p then gR (q (lead j) - p (lead j)) else 0) :=
          ((hrow_s q).of_nonneg_of_le (fun _ => norm_nonneg _) (hptR q)).tsum_le_tsum (hptR q)
            (hrow_s q)
      _ = ∑' x, gR (q (lead j) - (q - tr j x) (lead j)) := tsum_row j q _
      _ = ∑' x, gR x := by simp only [lead_sub_tr]
      _ ≤ 52 * c * ρ' := hgR_t
  · exact (hcol_s p).of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hpt q p)
  · calc ∑' q, ‖tsK sys L j a sh ρ' q p‖
        ≤ ∑' q, (if OnCh j q p then gC (q a) (q (lead j) - p (lead j)) else 0) :=
          ((hcol_s p).of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hpt q p)).tsum_le_tsum
            (fun q => hpt q p) (hcol_s p)
      _ = ∑' x, gC ((p + tr j x) a) ((p + tr j x) (lead j) - p (lead j)) := tsum_col j p _
      _ = ∑' x, c * (if sh (p a + σ x) ∧
            ρ' ^ 2 ≤ nsq x ∧ nsq x < (2 * ρ') ^ 2 then 1 / nsq x else 0) := by
          simp only [lead_add_tr, hcol_eq]
      _ = c * ∑' x : Lattice3, (if sh (p a + σ x) ∧
            ρ' ^ 2 ≤ nsq x ∧ nsq x < (2 * ρ') ^ 2 then 1 / nsq x else 0) := tsum_mul_left
      _ ≤ c * (N₀ / ρ' ^ 2) := mul_le_mul_of_nonneg_left (hT p).2 hc

/-- The Euclidean shell `λ ≤ |y| < λ + ρ`. -/
def shE (lam ρ : ℝ) (y : Lattice3) : Prop := lam ^ 2 ≤ lsq y ∧ lsq y < (lam + ρ) ^ 2

/-- The cube shell `λ ≤ ‖y‖_∞ < λ + ρ`. -/
def shC (lam ρ : ℝ) (y : Lattice3) : Prop := lam ≤ supn y ∧ supn y < lam + ρ

open Classical in
/-- **`lem:thinschur`** (Euclidean shell, `1 ≤ ρ ≤ λ`): rows `≤ 52 c_j ρ'`, columns
`≤ 750 c_j min(ρ, ρ')`, so `‖1_S W_{ρ'}‖ ≤ c_j (39000 ρ' min(ρ, ρ'))^{1/2}`. -/
theorem thinschur (hL : 0 < L) {j : Ch eta} {a : Fin eta} (ha : a ∈ moved j) {lam ρ ρ' : ℝ}
    (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam) (hρ' : 1 ≤ ρ') :
    SchurBound (tsK sys L j a (shE lam ρ) ρ') (52 * chC sys L j * ρ')
      (750 * chC sys L j * min ρ ρ') := by
  have h := thinschur_gen (sys := sys) hL ha (shE lam ρ) (N₀ := 750 * ρ' ^ 2 * min ρ ρ') hρ'
    (fun x T hT => thin_count_le x hρ hρl hρ' T fun θ hθ => ⟨(hT θ hθ).1, (hT θ hθ).2.1, (hT θ hθ).2.2⟩)
  have e : chC sys L j * (750 * ρ' ^ 2 * min ρ ρ' / ρ' ^ 2) = 750 * chC sys L j * min ρ ρ' := by
    have : ρ' ≠ 0 := by linarith
    field_simp
  rw [e] at h
  exact h

open Classical in
/-- **`lem:thinschur`** (cube shell, `ρ ≥ 1`): rows `≤ 52 c_j ρ'`, columns `≤ 750 c_j min(ρ, ρ')`. -/
theorem thinschur_cube (hL : 0 < L) {j : Ch eta} {a : Fin eta} (ha : a ∈ moved j) {lam ρ ρ' : ℝ}
    (hρ : 1 ≤ ρ) (hρ' : 1 ≤ ρ') :
    SchurBound (tsK sys L j a (shC lam ρ) ρ') (52 * chC sys L j * ρ')
      (750 * chC sys L j * min ρ ρ') := by
  have h := thinschur_gen (sys := sys) hL ha (shC lam ρ) (N₀ := 750 * ρ' ^ 2 * min ρ ρ') hρ'
    (fun x T hT => thin_count_cube_le x hρ hρ' T fun θ hθ =>
      ⟨(hT θ hθ).1, (hT θ hθ).2.1, (hT θ hθ).2.2⟩)
  have e : chC sys L j * (750 * ρ' ^ 2 * min ρ ρ' / ρ' ^ 2) = 750 * chC sys L j * min ρ ρ' := by
    have : ρ' ≠ 0 := by linarith
    field_simp
  rw [e] at h
  exact h

end FSBand
