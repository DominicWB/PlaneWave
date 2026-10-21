import PlaneWave.Certificate

/-!
# `lem:scaling` (Appendix `app:free`): the lattice estimates of the range-truncated kernel

`lem:scaling` states, for the range-truncated kernel `g_L` of eq:rangecut, four lattice estimates
and the slice-wise Sobolev embedding, uniformly in the cell size `L ≥ L₀`. Its proof uses only the
domination `|ĝ_L(ν)| ≤ C_ρ ŵ(ν)`, `ŵ(ν) = 4π / (Ω |k_ν|²)` (`ν ≠ 0`, `Ω = L³`, `k_ν = 2πν/L`),
which the manuscript derives from the radial Fourier integral of `g_L`. Here that domination is
the hypothesis `RangeCut L Cρ g`, for any coefficient function `g`. The constants are explicit
and do not depend on `L`; the four estimates hold for every `J > 0` and `K ≥ 0`, without the
restriction `J ≥ 2π/L₀`:

* `scaling_low`: `Σ_{0 < |k_ν| ≤ J} |ĝ(ν)| ≤ (27/π²) C_ρ J`;
* `scaling_tail`, `scaling_tail_tsum`: `Ω Σ_{|k_ν| > J} |ĝ(ν)|² ≤ (216√3/π) C_ρ² / J`;
* `scaling_moment2`: `Ω Σ_{0 < |k_ν| ≤ 2K} |k_ν|² |ĝ(ν)|² ≤ (216/π) C_ρ² K`;
* `scaling_moment4`: `Ω Σ_{0 < |k_ν| ≤ 2K} |k_ν|⁴ |ĝ(ν)|² ≤ (864/π) C_ρ² K³`;
* `slice_sobolev`: `Ω^{-1/2} Σ_ν |c_ν| ≤ C_S (Σ_ν (1 + |k_ν|²)² |c_ν|²)^{1/2}` for `L ≥ L₀`, with
  `C_S² = L₀^{-3} + 81/(4π³)`. A function on `T_L` with coefficients `c_ν` in the orthonormal
  basis `Ω^{-1/2} e^{i k_ν·x}` has sup norm at most `Ω^{-1/2} Σ_ν |c_ν|`, so this is the
  embedding `H²(T_L) ↪ L^∞(T_L)` of eq:sliceSobolev with an `L`-independent constant.

The manuscript's displays are the square roots of the second to fourth estimates. Finite sums are
taken over arbitrary finite sets of lattice points in the stated ranges. The lattice sums run over
the cubic shells `‖ν‖_∞ = m + 1` of the release file (`cubicSupShell`: at most `54 (m+1)²` points,
`(m+1)² ≤ |ν|² ≤ 3 (m+1)²`).

Not formalised: eq:rangecut itself (the Fourier coefficients of `g_L`), and `prop:free` and
`prop:free-dyn`. These rest on free-space spectral theory (Agmon decay, IMS localisation) and on
the energy and dynamics theorems for the `g_L` Hamiltonian; the development proves those
theorems for the periodic Coulomb interaction only.
-/

open scoped BigOperators
open Finset PlaneWaveCertificate

namespace FreeBoundary

/-! ## Lattice preliminaries -/

lemma latticeNormSq_eq_sum (ν : Lattice3) : latticeNormSq ν = ∑ i, (ν i : ℝ) ^ 2 := by
  simp [latticeNormSq, Fin.sum_univ_three]

lemma coord_sq_le (ν : Lattice3) (i : Fin 3) : (ν i : ℝ) ^ 2 ≤ latticeNormSq ν := by
  rw [latticeNormSq_eq_sum]
  exact single_le_sum (f := fun j => (ν j : ℝ) ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)

lemma latticeNormSq_zero : latticeNormSq (fun _ => (0 : ℤ)) = 0 := by
  simp [latticeNormSq]

lemma latticeNormSq_pos {ν : Lattice3} (h : ν ≠ (fun _ => 0)) : 0 < latticeNormSq ν := by
  rcases lt_or_eq_of_le (latticeNormSq_nonneg ν) with h' | h'
  · exact h'
  · exfalso
    apply h
    funext i
    have h1 := coord_sq_le ν i
    have h2 : (ν i : ℝ) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    exact_mod_cast (pow_eq_zero_iff two_ne_zero).1 h2

lemma ne_zero_of_normSq_pos {ν : Lattice3} (h : 0 < latticeNormSq ν) : ν ≠ (fun _ => 0) := by
  rintro rfl
  rw [latticeNormSq_zero] at h
  exact lt_irrefl _ h

/-- `|ν|² ≤ R²` bounds the coordinates by `⌊R⌋`. -/
lemma coord_bounds {ν : Lattice3} {R : ℝ} (hR : 0 ≤ R) (h : latticeNormSq ν ≤ R ^ 2) (i : Fin 3) :
    -((⌊R⌋₊ : ℕ) : ℤ) ≤ ν i ∧ ν i ≤ ((⌊R⌋₊ : ℕ) : ℤ) := by
  obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' ((coord_sq_le ν i).trans h) hR
  rw [Int.natCast_floor_eq_floor hR]
  constructor
  · have : -(ν i) ≤ ⌊R⌋ := Int.le_floor.2 (by push_cast; linarith)
    linarith
  · exact Int.le_floor.2 h2

/-- A finite set of lattice points has bounded coordinates. -/
lemma exists_coord_bound (F : Finset Lattice3) :
    ∃ M : ℕ, ∀ ν ∈ F, ∀ i, -(M : ℤ) ≤ ν i ∧ ν i ≤ (M : ℤ) := by
  refine ⟨F.sup fun ν => ∑ j, (ν j).natAbs, fun ν hν i => ?_⟩
  have h1 : (ν i).natAbs ≤ ∑ j, (ν j).natAbs :=
    single_le_sum (f := fun j => (ν j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have h2 : ∑ j, (ν j).natAbs ≤ F.sup fun ν => ∑ j, (ν j).natAbs :=
    le_sup (f := fun ν => ∑ j, (ν j).natAbs) hν
  have h3 : ((ν i).natAbs : ℤ) ≤ ((F.sup fun ν => ∑ j, (ν j).natAbs : ℕ) : ℤ) := by
    exact_mod_cast h1.trans h2
  have h4 : ν i ≤ ((ν i).natAbs : ℤ) := Int.le_natAbs
  have h5 : -(ν i) ≤ ((ν i).natAbs : ℤ) := by
    rw [← Int.natAbs_neg]; exact Int.le_natAbs
  constructor <;> linarith

/-! ## Sums over the cubic shells -/

/-- **Shell decomposition**: for `f ≥ 0` and a finite set of nonzero lattice points with
coordinates in `[-M, M]`, `Σ_F f ≤ Σ_{m < M} Σ_{‖ν‖_∞ = m+1} f`. -/
lemma sum_le_shells {f : Lattice3 → ℝ} (hf : ∀ ν, 0 ≤ f ν) (M : ℕ) (F : Finset Lattice3)
    (hF : ∀ ν ∈ F, ν ≠ (fun _ => 0) ∧ ∀ i, -(M : ℤ) ≤ ν i ∧ ν i ≤ (M : ℤ)) :
    ∑ ν ∈ F, f ν ≤ ∑ m ∈ range M, ∑ ν ∈ cubicSupShell m, f ν := by
  classical
  have hsub : F ⊆ (range M).biUnion cubicSupShell := by
    intro ν hν
    obtain ⟨hne, hb⟩ := hF ν hν
    obtain ⟨m, hm, hmem⟩ := exists_cubicSupShell_of_nonzero_coord_bounds M ν hne hb
    exact mem_biUnion.2 ⟨m, mem_range.2 hm, hmem⟩
  have hdisj : (↑(range M) : Set ℕ).PairwiseDisjoint cubicSupShell := by
    intro a _ b _ hab
    exact disjoint_left.2 fun ν ha hb => hab (cubicSupShell_index_unique ha hb)
  calc ∑ ν ∈ F, f ν ≤ ∑ ν ∈ (range M).biUnion cubicSupShell, f ν :=
        sum_le_sum_of_subset_of_nonneg hsub fun ν _ _ => hf ν
    _ = ∑ m ∈ range M, ∑ ν ∈ cubicSupShell m, f ν := sum_biUnion hdisj

/-- A shell has at most `54 (m+1)²` points. -/
lemma shell_sum_le {f : Lattice3 → ℝ} (m : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ ν ∈ cubicSupShell m, f ν ≤ b) :
    ∑ ν ∈ cubicSupShell m, f ν ≤ 54 * ((m : ℝ) + 1) ^ 2 * b := by
  calc ∑ ν ∈ cubicSupShell m, f ν ≤ ∑ _ν ∈ cubicSupShell m, b := sum_le_sum h
    _ = ((cubicSupShell m).card : ℝ) * b := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 54 * ((m : ℝ) + 1) ^ 2 * b := by
      have hc : ((cubicSupShell m).card : ℝ) ≤ 54 * ((m : ℝ) + 1) ^ 2 := by
        exact_mod_cast cubicSupShell_card_nat_bound m
      exact mul_le_mul_of_nonneg_right hc hb

/-- Shell decomposition with a bound `b m` on shell `m`. -/
lemma sum_le_shell_bound {f : Lattice3 → ℝ} (hf : ∀ ν, 0 ≤ f ν) (b : ℕ → ℝ)
    (hb : ∀ m, 0 ≤ b m) (hfb : ∀ m, ∀ ν ∈ cubicSupShell m, f ν ≤ b m) (M : ℕ)
    (F : Finset Lattice3)
    (hF : ∀ ν ∈ F, ν ≠ (fun _ => 0) ∧ ∀ i, -(M : ℤ) ≤ ν i ∧ ν i ≤ (M : ℤ)) :
    ∑ ν ∈ F, f ν ≤ ∑ m ∈ range M, 54 * ((m : ℝ) + 1) ^ 2 * b m :=
  (sum_le_shells hf M F hF).trans (sum_le_sum fun m _ => shell_sum_le m (hb m) (hfb m))

/-- The telescoping majorant of `sum_inv_sq_tail_le`. -/
noncomputable def telB (k m : ℕ) : ℝ := if k ≤ m then 2 / ((m : ℝ) + 1) else 2 / ((k : ℝ) + 1)

/-- `Σ_{m < M, m + 1 > x} (m + 1)^{-2} ≤ 2/x` for `x > 0`. -/
lemma sum_inv_sq_tail_le {x : ℝ} (hx : 0 < x) (M : ℕ) :
    ∑ m ∈ range M, (if x < (m : ℝ) + 1 then 1 / ((m : ℝ) + 1) ^ 2 else 0) ≤ 2 / x := by
  obtain ⟨k, hk⟩ : ∃ k, k = ⌊x⌋₊ := ⟨_, rfl⟩
  have hkx : x < (k : ℝ) + 1 := by rw [hk]; exact Nat.lt_floor_add_one x
  have hxk : (k : ℝ) ≤ x := by rw [hk]; exact Nat.floor_le hx.le
  have hstep : ∀ m : ℕ,
      (if x < (m : ℝ) + 1 then 1 / ((m : ℝ) + 1) ^ 2 else 0) ≤ telB k m - telB k (m + 1) := by
    intro m
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    by_cases hkm : k ≤ m
    · have e1 : telB k m = 2 / ((m : ℝ) + 1) := by rw [telB, if_pos hkm]
      have e2 : telB k (m + 1) = 2 / ((m : ℝ) + 1 + 1) := by
        rw [telB, if_pos (by omega), Nat.cast_add, Nat.cast_one]
      rw [e1, e2]
      have key : 1 / ((m : ℝ) + 1) ^ 2 ≤ 2 / ((m : ℝ) + 1) - 2 / ((m : ℝ) + 1 + 1) := by
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      by_cases hxm : x < (m : ℝ) + 1
      · rw [if_pos hxm]; exact key
      · rw [if_neg hxm]; exact le_trans (by positivity) key
    · have hlt : m + 1 ≤ k := by omega
      have hx' : (m : ℝ) + 1 ≤ x := by
        have : ((m + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlt
        push_cast at this
        linarith
      rw [if_neg (not_lt.2 hx')]
      have e1 : telB k m = 2 / ((k : ℝ) + 1) := by rw [telB, if_neg hkm]
      have e2 : telB k (m + 1) = 2 / ((k : ℝ) + 1) := by
        by_cases hk1 : k ≤ m + 1
        · have hkm1 : k = m + 1 := by omega
          rw [telB, if_pos hk1, hkm1]
        · rw [telB, if_neg hk1]
      simp only [e1, e2, sub_self, le_refl]
  have hb0 : telB k 0 = 2 / ((k : ℝ) + 1) := by
    by_cases h0 : k ≤ 0
    · rw [telB, if_pos h0, show k = 0 by omega]
    · rw [telB, if_neg h0]
  have hbM : 0 ≤ telB k M := by
    rw [telB]; split_ifs <;> positivity
  calc ∑ m ∈ range M, (if x < (m : ℝ) + 1 then 1 / ((m : ℝ) + 1) ^ 2 else 0)
      ≤ ∑ m ∈ range M, (telB k m - telB k (m + 1)) := sum_le_sum fun m _ => hstep m
    _ = telB k 0 - telB k M := sum_range_sub' (telB k) M
    _ ≤ 2 / ((k : ℝ) + 1) := by rw [hb0]; linarith
    _ ≤ 2 / x := div_le_div_of_nonneg_left (by norm_num) hx hkx.le

/-- `Σ_{m < M, m + 1 ≤ y} (m + 1)² ≤ y³` for `y ≥ 0`. -/
lemma sum_sq_head_le {y : ℝ} (hy : 0 ≤ y) (M : ℕ) :
    ∑ m ∈ range M, (if (m : ℝ) + 1 ≤ y then ((m : ℝ) + 1) ^ 2 else 0) ≤ y ^ 3 := by
  classical
  calc ∑ m ∈ range M, (if (m : ℝ) + 1 ≤ y then ((m : ℝ) + 1) ^ 2 else 0)
      ≤ ∑ m ∈ range M, (if (m : ℝ) + 1 ≤ y then y ^ 2 else 0) := by
        refine sum_le_sum fun m _ => ?_
        split_ifs with h
        · exact pow_le_pow_left₀ (by positivity) h 2
        · exact le_rfl
    _ = ∑ m ∈ (range M).filter (fun m : ℕ => (m : ℝ) + 1 ≤ y), y ^ 2 := (sum_filter _ _).symm
    _ ≤ ∑ _m ∈ range ⌊y⌋₊, y ^ 2 := by
        refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun _ _ _ => by positivity
        rw [mem_filter] at hm
        rw [mem_range]
        have : ((m + 1 : ℕ) : ℝ) ≤ y := by push_cast; exact hm.2
        have := Nat.le_floor this
        omega
    _ = (⌊y⌋₊ : ℝ) * y ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ y * y ^ 2 := mul_le_mul_of_nonneg_right (Nat.floor_le hy) (by positivity)
    _ = y ^ 3 := by ring

/-! ## The kernel hypothesis -/

/-- `|k_ν|² = (2π/L)² |ν|²`. -/
noncomputable def kSq (L : ℝ) (ν : Lattice3) : ℝ := (2 * Real.pi / L) ^ 2 * latticeNormSq ν

lemma kSq_nonneg (L : ℝ) (ν : Lattice3) : 0 ≤ kSq L ν :=
  mul_nonneg (sq_nonneg _) (latticeNormSq_nonneg ν)

lemma kSq_eq (L : ℝ) (ν : Lattice3) :
    kSq L ν = latticeNormSq ν / (L / (2 * Real.pi)) ^ 2 := by
  unfold kSq
  rw [div_pow, div_pow, div_div_eq_mul_div]
  ring

lemma normSq_le_of_kSq_le {L J : ℝ} (hL : 0 < L) {ν : Lattice3} (h : kSq L ν ≤ J ^ 2) :
    latticeNormSq ν ≤ (J * (L / (2 * Real.pi))) ^ 2 := by
  have hπ := Real.pi_pos
  rw [kSq_eq, div_le_iff₀ (by positivity)] at h
  rw [mul_pow]
  exact h

lemma normSq_gt_of_kSq_gt {L J : ℝ} (hL : 0 < L) {ν : Lattice3} (h : J ^ 2 < kSq L ν) :
    (J * (L / (2 * Real.pi))) ^ 2 < latticeNormSq ν := by
  have hπ := Real.pi_pos
  rw [kSq_eq, lt_div_iff₀ (by positivity)] at h
  rw [mul_pow]
  exact h

/-- **eq:rangecut**, the hypothesis of `lem:scaling`: `|ĝ(ν)| ≤ C_ρ ŵ(ν)` for `ν ≠ 0`, where
`ŵ(ν) = 4π / (Ω |k_ν|²)` is the periodic Coulomb coefficient and `Ω = L³`. -/
def RangeCut (L Cρ : ℝ) (g : Lattice3 → ℂ) : Prop :=
  ∀ ν : Lattice3, ν ≠ (fun _ => 0) → ‖g ν‖ ≤ Cρ * (4 * Real.pi / (L ^ 3 * kSq L ν))

/-- `ŵ(ν) = 4π/(Ω |k_ν|²) = 1/(π L |ν|²)`. -/
lemma what_eq {L : ℝ} (hL : 0 < L) (ν : Lattice3) :
    4 * Real.pi / (L ^ 3 * kSq L ν) = 1 / (Real.pi * L * latticeNormSq ν) := by
  have hπ := Real.pi_pos
  have hL' : L ≠ 0 := hL.ne'
  have e : L ^ 3 * kSq L ν = 4 * Real.pi * (Real.pi * L * latticeNormSq ν) := by
    unfold kSq
    rw [div_pow]
    field_simp
    ring
  rw [e, div_mul_eq_div_div, div_self (show 4 * Real.pi ≠ 0 by positivity)]

section Kernel

variable {L Cρ : ℝ} (hL : 0 < L) (hCρ : 0 ≤ Cρ) {g : Lattice3 → ℂ} (hg : RangeCut L Cρ g)
include hL hg

/-- `|ĝ(ν)| ≤ (C_ρ/(πL)) |ν|^{-2}`. -/
lemma norm_le {ν : Lattice3} (hν : ν ≠ (fun _ => 0)) :
    ‖g ν‖ ≤ Cρ / (Real.pi * L) * (1 / latticeNormSq ν) := by
  have h := hg ν hν
  rw [what_eq hL] at h
  refine h.trans_eq ?_
  ring

/-- `|ĝ(ν)|² ≤ (C_ρ²/(π²L²)) |ν|^{-4}`. -/
lemma norm_sq_le {ν : Lattice3} (hν : ν ≠ (fun _ => 0)) :
    ‖g ν‖ ^ 2 ≤ Cρ ^ 2 / (Real.pi ^ 2 * L ^ 2) * (1 / latticeNormSq ν ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_le hL hg hν) 2
  refine h.trans_eq ?_
  ring

include hCρ in
/-- **`lem:scaling`, first display**: `Σ_{0 < |k_ν| ≤ J} |ĝ(ν)| ≤ (27/π²) C_ρ J`. -/
theorem scaling_low {J : ℝ} (hJ : 0 ≤ J) (F : Finset Lattice3)
    (hF : ∀ ν ∈ F, ν ≠ (fun _ => 0) ∧ kSq L ν ≤ J ^ 2) :
    ∑ ν ∈ F, ‖g ν‖ ≤ 27 / Real.pi ^ 2 * Cρ * J := by
  have hπ := Real.pi_pos
  have hL' : L ≠ 0 := hL.ne'
  set R := J * (L / (2 * Real.pi)) with hR
  have hR0 : 0 ≤ R := by positivity
  have hcoord : ∀ ν ∈ F, ν ≠ (fun _ => 0) ∧
      ∀ i, -((⌊R⌋₊ : ℕ) : ℤ) ≤ ν i ∧ ν i ≤ ((⌊R⌋₊ : ℕ) : ℤ) :=
    fun ν hν => ⟨(hF ν hν).1, coord_bounds hR0 (normSq_le_of_kSq_le hL (hF ν hν).2)⟩
  have hshell : ∑ ν ∈ F, (1 / latticeNormSq ν) ≤
      ∑ m ∈ range ⌊R⌋₊, 54 * ((m : ℝ) + 1) ^ 2 * (1 / ((m : ℝ) + 1) ^ 2) :=
    sum_le_shell_bound (fun ν => one_div_nonneg.2 (latticeNormSq_nonneg ν))
      (fun m => 1 / ((m : ℝ) + 1) ^ 2) (fun m => by positivity)
      (fun m ν hν => one_div_le_one_div_of_le (by positivity) (cubicSupShell_normSq_lower m hν))
      ⌊R⌋₊ F hcoord
  have hsum : ∑ m ∈ range ⌊R⌋₊, 54 * ((m : ℝ) + 1) ^ 2 * (1 / ((m : ℝ) + 1) ^ 2) ≤ 54 * R := by
    have e : ∀ m : ℕ, 54 * ((m : ℝ) + 1) ^ 2 * (1 / ((m : ℝ) + 1) ^ 2) = 54 := fun m => by
      field_simp
    simp only [e, sum_const, card_range, nsmul_eq_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le hR0) (by norm_num)
  calc ∑ ν ∈ F, ‖g ν‖ ≤ ∑ ν ∈ F, Cρ / (Real.pi * L) * (1 / latticeNormSq ν) :=
        sum_le_sum fun ν hν => norm_le hL hg (hF ν hν).1
    _ = Cρ / (Real.pi * L) * ∑ ν ∈ F, (1 / latticeNormSq ν) := (mul_sum _ _ _).symm
    _ ≤ Cρ / (Real.pi * L) * (54 * R) :=
        mul_le_mul_of_nonneg_left (hshell.trans hsum) (by positivity)
    _ = 27 / Real.pi ^ 2 * Cρ * J := by
        rw [hR]
        field_simp
        ring

/-- **`lem:scaling`, second display**: `Ω Σ_{|k_ν| > J} |ĝ(ν)|² ≤ (216√3/π) C_ρ² / J`, for every
finite part of the sum. -/
theorem scaling_tail {J : ℝ} (hJ : 0 < J) (F : Finset Lattice3)
    (hF : ∀ ν ∈ F, J ^ 2 < kSq L ν) :
    L ^ 3 * ∑ ν ∈ F, ‖g ν‖ ^ 2 ≤ 216 * Real.sqrt 3 / Real.pi * Cρ ^ 2 / J := by
  classical
  have hπ := Real.pi_pos
  have hL' : L ≠ 0 := hL.ne'
  have h3 : 0 < Real.sqrt 3 := by positivity
  set R := J * (L / (2 * Real.pi)) with hR
  have hR0 : 0 < R := by positivity
  set x := R / Real.sqrt 3 with hx
  have hx0 : 0 < x := by positivity
  obtain ⟨M, hM⟩ := exists_coord_bound F
  have hgt : ∀ ν ∈ F, R ^ 2 < latticeNormSq ν := fun ν hν => normSq_gt_of_kSq_gt hL (hF ν hν)
  have hne : ∀ ν ∈ F, ν ≠ (fun _ => 0) := fun ν hν =>
    ne_zero_of_normSq_pos (lt_of_le_of_lt (sq_nonneg R) (hgt ν hν))
  set f : Lattice3 → ℝ := fun ν => if R ^ 2 < latticeNormSq ν then 1 / latticeNormSq ν ^ 2 else 0
    with hfdef
  have hf0 : ∀ ν, 0 ≤ f ν := fun ν => by
    simp only [hfdef]; split_ifs <;> positivity
  have hfb : ∀ m, ∀ ν ∈ cubicSupShell m,
      f ν ≤ (if x < (m : ℝ) + 1 then 1 / ((m : ℝ) + 1) ^ 4 else 0) := by
    intro m ν hν
    have hlo := cubicSupShell_normSq_lower m hν
    have hup := cubicSupShell_normSq_upper m hν
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    simp only [hfdef]
    split_ifs with h1 h2
    · rw [show ((m : ℝ) + 1) ^ 4 = (((m : ℝ) + 1) ^ 2) ^ 2 by ring]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hlo 2)
    · exfalso
      apply h2
      have hsq : x ^ 2 < ((m : ℝ) + 1) ^ 2 := by
        rw [hx, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), div_lt_iff₀ (by norm_num)]
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 hm1.le hsq
    · positivity
    · exact le_rfl
  have hshell := sum_le_shell_bound hf0 _ (fun m => by split_ifs <;> positivity) hfb M F
    (fun ν hν => ⟨hne ν hν, hM ν hν⟩)
  have hsum : ∑ m ∈ range M, 54 * ((m : ℝ) + 1) ^ 2 *
      (if x < (m : ℝ) + 1 then 1 / ((m : ℝ) + 1) ^ 4 else 0) ≤ 54 * (2 / x) := by
    have e : ∀ m : ℕ, 54 * ((m : ℝ) + 1) ^ 2 *
        (if x < (m : ℝ) + 1 then 1 / ((m : ℝ) + 1) ^ 4 else 0) =
        54 * (if x < (m : ℝ) + 1 then 1 / ((m : ℝ) + 1) ^ 2 else 0) := fun m => by
      have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      split_ifs
      · field_simp
      · simp
    simp only [e, ← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_inv_sq_tail_le hx0 M) (by norm_num)
  have hterm : ∀ ν ∈ F, ‖g ν‖ ^ 2 ≤ Cρ ^ 2 / (Real.pi ^ 2 * L ^ 2) * f ν := by
    intro ν hν
    have h := norm_sq_le hL hg (hne ν hν)
    simp only [hfdef, if_pos (hgt ν hν)]
    exact h
  calc L ^ 3 * ∑ ν ∈ F, ‖g ν‖ ^ 2
      ≤ L ^ 3 * ∑ ν ∈ F, Cρ ^ 2 / (Real.pi ^ 2 * L ^ 2) * f ν :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = L ^ 3 * (Cρ ^ 2 / (Real.pi ^ 2 * L ^ 2)) * ∑ ν ∈ F, f ν := by rw [← mul_sum]; ring
    _ ≤ L ^ 3 * (Cρ ^ 2 / (Real.pi ^ 2 * L ^ 2)) * (54 * (2 / x)) :=
        mul_le_mul_of_nonneg_left (hshell.trans hsum) (by positivity)
    _ = 216 * Real.sqrt 3 / Real.pi * Cρ ^ 2 / J := by
        rw [hx, hR]
        field_simp
        ring

/-- **`lem:scaling`, second display, for the series**: the tail series converges and
`Ω Σ'_{|k_ν| > J} |ĝ(ν)|² ≤ (216√3/π) C_ρ² / J`. -/
theorem scaling_tail_tsum {J : ℝ} (hJ : 0 < J) :
    Summable (fun ν : Lattice3 => if J ^ 2 < kSq L ν then ‖g ν‖ ^ 2 else 0) ∧
      L ^ 3 * ∑' ν : Lattice3, (if J ^ 2 < kSq L ν then ‖g ν‖ ^ 2 else 0) ≤
        216 * Real.sqrt 3 / Real.pi * Cρ ^ 2 / J := by
  classical
  have hL3 : 0 < L ^ 3 := by positivity
  set B := 216 * Real.sqrt 3 / Real.pi * Cρ ^ 2 / J
  have hfin : ∀ u : Finset Lattice3,
      ∑ ν ∈ u, (if J ^ 2 < kSq L ν then ‖g ν‖ ^ 2 else 0) ≤ B / L ^ 3 := by
    intro u
    rw [← sum_filter, le_div_iff₀ hL3, mul_comm]
    exact scaling_tail hL hg hJ _ fun ν hν => (mem_filter.1 hν).2
  have hnn : ∀ ν : Lattice3, 0 ≤ (if J ^ 2 < kSq L ν then ‖g ν‖ ^ 2 else 0) := fun ν => by
    split_ifs <;> positivity
  have hs := summable_of_sum_le hnn hfin
  refine ⟨hs, ?_⟩
  have ht := hs.tsum_le_of_sum_le hfin
  rw [le_div_iff₀ hL3] at ht
  linarith

/-- **`lem:scaling`, third display**: `Ω Σ_{0 < |k_ν| ≤ 2K} |k_ν|² |ĝ(ν)|² ≤ (216/π) C_ρ² K`. -/
theorem scaling_moment2 {K : ℝ} (hK : 0 ≤ K) (F : Finset Lattice3)
    (hF : ∀ ν ∈ F, ν ≠ (fun _ => 0) ∧ kSq L ν ≤ (2 * K) ^ 2) :
    L ^ 3 * ∑ ν ∈ F, kSq L ν * ‖g ν‖ ^ 2 ≤ 216 / Real.pi * Cρ ^ 2 * K := by
  have hπ := Real.pi_pos
  have hL' : L ≠ 0 := hL.ne'
  set R := 2 * K * (L / (2 * Real.pi)) with hR
  have hR0 : 0 ≤ R := by positivity
  have hcoord : ∀ ν ∈ F, ν ≠ (fun _ => 0) ∧
      ∀ i, -((⌊R⌋₊ : ℕ) : ℤ) ≤ ν i ∧ ν i ≤ ((⌊R⌋₊ : ℕ) : ℤ) :=
    fun ν hν => ⟨(hF ν hν).1, coord_bounds hR0 (normSq_le_of_kSq_le hL (hF ν hν).2)⟩
  have hshell : ∑ ν ∈ F, (1 / latticeNormSq ν) ≤
      ∑ m ∈ range ⌊R⌋₊, 54 * ((m : ℝ) + 1) ^ 2 * (1 / ((m : ℝ) + 1) ^ 2) :=
    sum_le_shell_bound (fun ν => one_div_nonneg.2 (latticeNormSq_nonneg ν))
      (fun m => 1 / ((m : ℝ) + 1) ^ 2) (fun m => by positivity)
      (fun m ν hν => one_div_le_one_div_of_le (by positivity) (cubicSupShell_normSq_lower m hν))
      ⌊R⌋₊ F hcoord
  have hsum : ∑ m ∈ range ⌊R⌋₊, 54 * ((m : ℝ) + 1) ^ 2 * (1 / ((m : ℝ) + 1) ^ 2) ≤ 54 * R := by
    have e : ∀ m : ℕ, 54 * ((m : ℝ) + 1) ^ 2 * (1 / ((m : ℝ) + 1) ^ 2) = 54 := fun m => by
      field_simp
    simp only [e, sum_const, card_range, nsmul_eq_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le hR0) (by norm_num)
  have hterm : ∀ ν ∈ F, kSq L ν * ‖g ν‖ ^ 2 ≤ 4 * Cρ ^ 2 / L ^ 4 * (1 / latticeNormSq ν) := by
    intro ν hν
    have hn := latticeNormSq_pos (hF ν hν).1
    have h := mul_le_mul_of_nonneg_left (norm_sq_le hL hg (hF ν hν).1) (kSq_nonneg L ν)
    refine h.trans_eq ?_
    unfold kSq
    field_simp
    ring
  calc L ^ 3 * ∑ ν ∈ F, kSq L ν * ‖g ν‖ ^ 2
      ≤ L ^ 3 * ∑ ν ∈ F, 4 * Cρ ^ 2 / L ^ 4 * (1 / latticeNormSq ν) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = L ^ 3 * (4 * Cρ ^ 2 / L ^ 4) * ∑ ν ∈ F, (1 / latticeNormSq ν) := by rw [← mul_sum]; ring
    _ ≤ L ^ 3 * (4 * Cρ ^ 2 / L ^ 4) * (54 * R) :=
        mul_le_mul_of_nonneg_left (hshell.trans hsum) (by positivity)
    _ = 216 / Real.pi * Cρ ^ 2 * K := by
        rw [hR]
        field_simp
        ring

/-- **`lem:scaling`, fourth display**: `Ω Σ_{0 < |k_ν| ≤ 2K} |k_ν|⁴ |ĝ(ν)|² ≤ (864/π) C_ρ² K³`. -/
theorem scaling_moment4 {K : ℝ} (hK : 0 ≤ K) (F : Finset Lattice3)
    (hF : ∀ ν ∈ F, ν ≠ (fun _ => 0) ∧ kSq L ν ≤ (2 * K) ^ 2) :
    L ^ 3 * ∑ ν ∈ F, kSq L ν ^ 2 * ‖g ν‖ ^ 2 ≤ 864 / Real.pi * Cρ ^ 2 * K ^ 3 := by
  have hπ := Real.pi_pos
  have hL' : L ≠ 0 := hL.ne'
  set R := 2 * K * (L / (2 * Real.pi)) with hR
  have hR0 : 0 ≤ R := by positivity
  have hcoord : ∀ ν ∈ F, ν ≠ (fun _ => 0) ∧
      ∀ i, -((⌊R⌋₊ : ℕ) : ℤ) ≤ ν i ∧ ν i ≤ ((⌊R⌋₊ : ℕ) : ℤ) :=
    fun ν hν => ⟨(hF ν hν).1, coord_bounds hR0 (normSq_le_of_kSq_le hL (hF ν hν).2)⟩
  have hshell : ∑ ν ∈ F, (1 : ℝ) ≤ ∑ m ∈ range ⌊R⌋₊, 54 * ((m : ℝ) + 1) ^ 2 * 1 :=
    sum_le_shell_bound (fun _ => zero_le_one) (fun _ => 1) (fun _ => zero_le_one)
      (fun _ _ _ => le_rfl) ⌊R⌋₊ F hcoord
  have hsum : ∑ m ∈ range ⌊R⌋₊, 54 * ((m : ℝ) + 1) ^ 2 * 1 ≤ 54 * R ^ 3 := by
    have hle : ∀ m ∈ range ⌊R⌋₊, 54 * ((m : ℝ) + 1) ^ 2 * 1 ≤ 54 * (⌊R⌋₊ : ℝ) ^ 2 := by
      intro m hm
      have hm' : ((m + 1 : ℕ) : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast mem_range.1 hm
      push_cast at hm'
      have := pow_le_pow_left₀ (by positivity) hm' 2
      linarith
    refine (sum_le_sum hle).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul]
    have hfl := Nat.floor_le hR0
    have hfl0 : (0 : ℝ) ≤ (⌊R⌋₊ : ℝ) := Nat.cast_nonneg _
    have : (⌊R⌋₊ : ℝ) * (54 * (⌊R⌋₊ : ℝ) ^ 2) = 54 * (⌊R⌋₊ : ℝ) ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hfl0 hfl 3) (by norm_num)
  have hterm : ∀ ν ∈ F, kSq L ν ^ 2 * ‖g ν‖ ^ 2 ≤ 16 * Real.pi ^ 2 * Cρ ^ 2 / L ^ 6 * 1 := by
    intro ν hν
    have hn := latticeNormSq_pos (hF ν hν).1
    have h := mul_le_mul_of_nonneg_left (norm_sq_le hL hg (hF ν hν).1)
      (sq_nonneg (kSq L ν))
    refine h.trans_eq ?_
    unfold kSq
    field_simp
    ring
  calc L ^ 3 * ∑ ν ∈ F, kSq L ν ^ 2 * ‖g ν‖ ^ 2
      ≤ L ^ 3 * ∑ ν ∈ F, 16 * Real.pi ^ 2 * Cρ ^ 2 / L ^ 6 * 1 :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = L ^ 3 * (16 * Real.pi ^ 2 * Cρ ^ 2 / L ^ 6) * ∑ ν ∈ F, (1 : ℝ) := by
        rw [← mul_sum]; ring
    _ ≤ L ^ 3 * (16 * Real.pi ^ 2 * Cρ ^ 2 / L ^ 6) * (54 * R ^ 3) :=
        mul_le_mul_of_nonneg_left (hshell.trans hsum) (by positivity)
    _ = 864 / Real.pi * Cρ ^ 2 * K ^ 3 := by
        rw [hR]
        field_simp
        ring

end Kernel

/-! ## The slice-wise Sobolev embedding with an `L`-independent constant -/

/-- `Ω^{-1} Σ_ν (1 + |k_ν|²)^{-2} ≤ L₀^{-3} + 81/(4π³)` for `L ≥ L₀`. -/
theorem sobolev_weight_sum {L₀ L : ℝ} (hL₀ : 0 < L₀) (hL : L₀ ≤ L) (F : Finset Lattice3) :
    1 / L ^ 3 * ∑ ν ∈ F, 1 / (1 + kSq L ν) ^ 2 ≤ 1 / L₀ ^ 3 + 81 / (4 * Real.pi ^ 3) := by
  classical
  have hπ := Real.pi_pos
  have hL0 : 0 < L := lt_of_lt_of_le hL₀ hL
  have hL' : L ≠ 0 := hL0.ne'
  set a := 2 * Real.pi / L with ha
  have ha0 : 0 < a := by positivity
  set y := 1 / a with hy
  have hy0 : 0 < y := by positivity
  set w : Lattice3 → ℝ := fun ν => 1 / (1 + kSq L ν) ^ 2 with hw
  have hw0 : ∀ ν, 0 ≤ w ν := fun ν => by
    have := kSq_nonneg L ν
    simp only [hw]; positivity
  have hw1 : ∀ ν, w ν ≤ 1 := fun ν => by
    have := kSq_nonneg L ν
    simp only [hw]
    rw [div_le_one (by positivity)]
    nlinarith
  -- the zero mode and the rest
  have hsplit := sum_filter_add_sum_filter_not F (fun ν => ν = (fun _ => (0 : ℤ))) w
  have hzero : ∑ ν ∈ F.filter (fun ν => ν = (fun _ => (0 : ℤ))), w ν ≤ 1 := by
    calc ∑ ν ∈ F.filter (fun ν => ν = (fun _ => (0 : ℤ))), w ν
        ≤ ∑ ν ∈ ({fun _ => (0 : ℤ)} : Finset Lattice3), w ν :=
          sum_le_sum_of_subset_of_nonneg
            (fun ν hν => mem_singleton.2 (mem_filter.1 hν).2) fun ν _ _ => hw0 ν
      _ ≤ 1 := by rw [sum_singleton]; exact hw1 _
  obtain ⟨M, hM⟩ := exists_coord_bound F
  have hfb : ∀ m, ∀ ν ∈ cubicSupShell m, w ν ≤ 1 / (1 + a ^ 2 * ((m : ℝ) + 1) ^ 2) ^ 2 := by
    intro m ν hν
    have hlo := cubicSupShell_normSq_lower m hν
    simp only [hw]
    refine one_div_le_one_div_of_le (by positivity) ?_
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    unfold kSq
    rw [← ha]
    have := mul_le_mul_of_nonneg_left hlo (sq_nonneg a)
    linarith
  have hshell := sum_le_shell_bound hw0 _ (fun m => by positivity) hfb M
    (F.filter fun ν => ¬ν = (fun _ => (0 : ℤ)))
    (fun ν hν => ⟨(mem_filter.1 hν).2, hM ν (mem_filter.1 hν).1⟩)
  -- each shell term splits into a head and a tail part
  have hterm : ∀ m : ℕ, 54 * ((m : ℝ) + 1) ^ 2 * (1 / (1 + a ^ 2 * ((m : ℝ) + 1) ^ 2) ^ 2) ≤
      54 * (if (m : ℝ) + 1 ≤ y then ((m : ℝ) + 1) ^ 2 else 0) +
        54 / a ^ 4 * (if y < (m : ℝ) + 1 then 1 / ((m : ℝ) + 1) ^ 2 else 0) := by
    intro m
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hden : 1 ≤ (1 + a ^ 2 * ((m : ℝ) + 1) ^ 2) ^ 2 := by
      have : 1 ≤ 1 + a ^ 2 * ((m : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (a * ((m : ℝ) + 1))]
      nlinarith
    by_cases h1 : (m : ℝ) + 1 ≤ y
    · -- head
      have h2 : ¬y < (m : ℝ) + 1 := not_lt.2 h1
      rw [if_pos h1, if_neg h2]
      have : ((m : ℝ) + 1) ^ 2 * (1 / (1 + a ^ 2 * ((m : ℝ) + 1) ^ 2) ^ 2) ≤ ((m : ℝ) + 1) ^ 2 := by
        rw [mul_one_div]
        exact div_le_self (by positivity) hden
      nlinarith
    · -- tail: `(1 + a²(m+1)²)² ≥ a⁴ (m+1)⁴`
      have h2 : y < (m : ℝ) + 1 := lt_of_not_ge h1
      rw [if_neg h1, if_pos h2]
      have hge : a ^ 4 * ((m : ℝ) + 1) ^ 4 ≤ (1 + a ^ 2 * ((m : ℝ) + 1) ^ 2) ^ 2 := by
        nlinarith [sq_nonneg (a ^ 2 * ((m : ℝ) + 1) ^ 2)]
      have hpos : 0 < a ^ 4 * ((m : ℝ) + 1) ^ 4 := by positivity
      have key : 54 * ((m : ℝ) + 1) ^ 2 * (1 / (1 + a ^ 2 * ((m : ℝ) + 1) ^ 2) ^ 2) ≤
          54 * ((m : ℝ) + 1) ^ 2 * (1 / (a ^ 4 * ((m : ℝ) + 1) ^ 4)) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpos hge) (by positivity)
      refine key.trans (le_of_eq ?_)
      field_simp
      ring
  have hsum : ∑ m ∈ range M,
      54 * ((m : ℝ) + 1) ^ 2 * (1 / (1 + a ^ 2 * ((m : ℝ) + 1) ^ 2) ^ 2) ≤
      54 * y ^ 3 + 54 / a ^ 4 * (2 / y) := by
    refine (sum_le_sum fun m _ => hterm m).trans ?_
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have h1 := sum_sq_head_le hy0.le M
    have h2 := sum_inv_sq_tail_le hy0 M
    have ha4 : 0 ≤ 54 / a ^ 4 := by positivity
    exact add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) (mul_le_mul_of_nonneg_left h2 ha4)
  have hrest : 54 * y ^ 3 + 54 / a ^ 4 * (2 / y) = 162 / a ^ 3 := by
    rw [hy]
    field_simp
    ring
  have htot : ∑ ν ∈ F, w ν ≤ 1 + 162 / a ^ 3 := by
    rw [← hsplit]
    have := hshell.trans (hsum.trans_eq hrest)
    linarith
  have hL3 : 0 < L ^ 3 := by positivity
  calc 1 / L ^ 3 * ∑ ν ∈ F, 1 / (1 + kSq L ν) ^ 2 = 1 / L ^ 3 * ∑ ν ∈ F, w ν := rfl
    _ ≤ 1 / L ^ 3 * (1 + 162 / a ^ 3) :=
        mul_le_mul_of_nonneg_left htot (by positivity)
    _ = 1 / L ^ 3 + 81 / (4 * Real.pi ^ 3) := by
        rw [ha]
        field_simp
        ring
    _ ≤ 1 / L₀ ^ 3 + 81 / (4 * Real.pi ^ 3) := by
        have : 1 / L ^ 3 ≤ 1 / L₀ ^ 3 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hL₀.le hL 3)
        linarith

/-- **`lem:scaling`, the slice-wise embedding `H²(T_L) ↪ L^∞(T_L)` with an `L`-independent
constant**: for `L ≥ L₀`, every finite family of coefficients satisfies
`Ω^{-1/2} Σ_ν |c_ν| ≤ C_S (Σ_ν (1 + |k_ν|²)² |c_ν|²)^{1/2}`, `C_S² = L₀^{-3} + 81/(4π³)`. -/
theorem slice_sobolev {L₀ L : ℝ} (hL₀ : 0 < L₀) (hL : L₀ ≤ L) (c : Lattice3 → ℂ)
    (F : Finset Lattice3) :
    Real.sqrt (1 / L ^ 3) * ∑ ν ∈ F, ‖c ν‖ ≤
      Real.sqrt (1 / L₀ ^ 3 + 81 / (4 * Real.pi ^ 3)) *
        Real.sqrt (∑ ν ∈ F, (1 + kSq L ν) ^ 2 * ‖c ν‖ ^ 2) := by
  have hL0 : 0 < L := lt_of_lt_of_le hL₀ hL
  have hpos : ∀ ν, 0 < 1 + kSq L ν := fun ν => by have := kSq_nonneg L ν; linarith
  -- Cauchy–Schwarz
  have hcs := sum_mul_sq_le_sq_mul_sq F (fun ν => 1 / (1 + kSq L ν))
    (fun ν => (1 + kSq L ν) * ‖c ν‖)
  have e1 : ∀ ν, 1 / (1 + kSq L ν) * ((1 + kSq L ν) * ‖c ν‖) = ‖c ν‖ := fun ν => by
    have := hpos ν
    field_simp
  have e2 : ∀ ν, (1 / (1 + kSq L ν)) ^ 2 = 1 / (1 + kSq L ν) ^ 2 := fun ν => by
    rw [div_pow, one_pow]
  have e3 : ∀ ν, ((1 + kSq L ν) * ‖c ν‖) ^ 2 = (1 + kSq L ν) ^ 2 * ‖c ν‖ ^ 2 := fun ν => by
    rw [mul_pow]
  simp only [e1, e2, e3] at hcs
  have hC : 0 ≤ 1 / L₀ ^ 3 + 81 / (4 * Real.pi ^ 3) := by positivity
  set S := ∑ ν ∈ F, ‖c ν‖
  set W := ∑ ν ∈ F, 1 / (1 + kSq L ν) ^ 2
  set H := ∑ ν ∈ F, (1 + kSq L ν) ^ 2 * ‖c ν‖ ^ 2
  set C := 1 / L₀ ^ 3 + 81 / (4 * Real.pi ^ 3)
  have hW := sobolev_weight_sum hL₀ hL F
  have hH : 0 ≤ H := sum_nonneg fun ν _ => by positivity
  have hS : 0 ≤ S := sum_nonneg fun ν _ => norm_nonneg _
  have hL3 : 0 ≤ 1 / L ^ 3 := by positivity
  have hsq : (Real.sqrt (1 / L ^ 3) * S) ^ 2 ≤ C * H := by
    rw [mul_pow, Real.sq_sqrt hL3]
    calc 1 / L ^ 3 * S ^ 2 ≤ 1 / L ^ 3 * (W * H) := mul_le_mul_of_nonneg_left hcs hL3
      _ = (1 / L ^ 3 * W) * H := by ring
      _ ≤ C * H := mul_le_mul_of_nonneg_right hW hH
  rw [← Real.sqrt_mul hC]
  exact (le_abs_self _).trans (Real.abs_le_sqrt hsq)

end FreeBoundary
