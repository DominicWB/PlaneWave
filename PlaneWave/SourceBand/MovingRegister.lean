import PlaneWave.SourceBand.SpectatorBound
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Source band block, part 5: K2 for a channel that moves the register

The paragraph after `lem:thinschur`: for a band-good state, the part of a channel `j` moving `a`
fed by the input beyond `λ/2` satisfies `‖1_S W_j 1_{a,>λ/2} u‖ ≤ C (B + M) λ^{-2} ρ^{1/2}`. The
hops are split dyadically, `2^k ≤ |ν| < 2^{k+1}` (lattice units, `Λ = λ/g`):

* `2^k < Λ/4`: `lem:thinschur` (rows `52 c r`, columns `750 c min(max(R,1), r)`) times the band
  mass of the feeding band `λ - 2gr ≤ |k_a| < λ + ρ + 2gr` (`wide_band`: bands up to four times
  their radius), `≤ C B λ^{-3} ρ^{1/2} r`, summed: `C B λ^{-2} ρ^{1/2}`;
* `Λ/4 ≤ 2^k ≤ 8Λ`: columns into the whole shell `≤ c N_S/r²`, times the tail `M (λ/2)^{-5/2}`;
* `2^k > 8Λ`: the input lies beyond `gr/2`; Schur `C Λ (max(R,1))^{1/2} r^{-1/2}` times the tail
  `M (gr/2)^{-5/2}`, summed: `C M λ^{-2} ρ^{1/2}`.

The decomposition is exact on truncated inputs (finitely many dyadic shells), and the bound passes
to the limit as in `far_band`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal FSFlux

namespace FSBand

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Dyadic bookkeeping -/

/-- Every `t ≥ 1` lies in a dyadic shell `4^k ≤ t < 4^{k+1}`. -/
lemma exists_dyadic {t : ℝ} (ht : 1 ≤ t) : ∃ k : ℕ, (4 : ℝ) ^ k ≤ t ∧ t < 4 ^ (k + 1) := by
  classical
  have hex : ∃ k : ℕ, t < (4 : ℝ) ^ (k + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt t (by norm_num : (1 : ℝ) < 4)
    exact ⟨n, hn.trans_le (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero]; exact ht
  · have := Nat.find_min hex (Nat.sub_lt hpos one_pos)
    push Not at this
    rwa [show Nat.find hex - 1 + 1 = Nat.find hex from by omega] at this

lemma dyadic_unique {t : ℝ} {k k' : ℕ} (h : (4 : ℝ) ^ k ≤ t ∧ t < 4 ^ (k + 1))
    (h' : (4 : ℝ) ^ k' ≤ t ∧ t < 4 ^ (k' + 1)) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : (4 : ℝ) ^ (k + 1) ≤ 4 ^ k' := pow_le_pow_right₀ (by norm_num) hlt
    linarith [h.2, h'.1]
  · have : (4 : ℝ) ^ (k' + 1) ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) hlt
    linarith [h'.2, h.1]

open Classical in
/-- `Σ_{k<K} [4^k ≤ t < 4^{k+1}] = 1` for `1 ≤ t < 4^K`. -/
lemma sum_dyadic_ind {t : ℝ} (ht : 1 ≤ t) {K : ℕ} (htK : t < 4 ^ K) :
    ∑ k ∈ Finset.range K, (if (4 : ℝ) ^ k ≤ t ∧ t < 4 ^ (k + 1) then (1 : ℂ) else 0) = 1 := by
  obtain ⟨k₀, hk₀⟩ := exists_dyadic ht
  have hk₀K : k₀ < K := by
    by_contra h; push Not at h
    have : (4 : ℝ) ^ K ≤ 4 ^ k₀ := pow_le_pow_right₀ (by norm_num) h
    linarith [hk₀.1]
  rw [Finset.sum_eq_single k₀]
  · rw [if_pos hk₀]
  · intro k _ hk; rw [if_neg]; intro h; exact hk (dyadic_unique h hk₀)
  · intro h; exact absurd (Finset.mem_range.mpr hk₀K) h

lemma two_pow_sq (k : ℕ) : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

lemma two_two_pow_sq (k : ℕ) : (2 * (2 : ℝ) ^ k) ^ 2 = 4 ^ (k + 1) := by
  rw [mul_pow, two_pow_sq, pow_succ]; ring

open Classical in
/-- `Σ_{k<K, 2^k ≤ Y} 2^k ≤ 2Y`. -/
lemma sum_pow_two_le {Y : ℝ} (hY : 0 ≤ Y) (K : ℕ) :
    ∑ k ∈ (Finset.range K).filter (fun k => (2 : ℝ) ^ k ≤ Y), (2 : ℝ) ^ k ≤ 2 * Y := by
  set S := (Finset.range K).filter (fun k => (2 : ℝ) ^ k ≤ Y)
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h, Finset.sum_empty]; linarith
  · set k₁ := S.max' h
    have hk₁ : (2 : ℝ) ^ k₁ ≤ Y := (Finset.mem_filter.mp (S.max'_mem h)).2
    have hsub : S ⊆ Finset.range (k₁ + 1) := fun k hk =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (S.le_max' k hk))
    calc ∑ k ∈ S, (2 : ℝ) ^ k ≤ ∑ k ∈ Finset.range (k₁ + 1), (2 : ℝ) ^ k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 2 ^ (k₁ + 1) - 1 := by rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]; norm_num
      _ ≤ 2 * Y := by rw [pow_succ]; linarith

open Classical in
/-- `Σ_{k<K, X < 2^k} 2^{-k} ≤ 2/X`. -/
lemma sum_inv_pow_two_le {X : ℝ} (hX : 0 < X) (K : ℕ) :
    ∑ k ∈ (Finset.range K).filter (fun k => X < (2 : ℝ) ^ k), ((2 : ℝ) ^ k)⁻¹ ≤ 2 / X := by
  set S := (Finset.range K).filter (fun k => X < (2 : ℝ) ^ k)
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h, Finset.sum_empty]; positivity
  · set k₀ := S.min' h
    have hk₀ : X < (2 : ℝ) ^ k₀ := (Finset.mem_filter.mp (S.min'_mem h)).2
    have hsub : S ⊆ Finset.Ico k₀ K := fun k hk => Finset.mem_Ico.mpr
      ⟨S.min'_le k hk, Finset.mem_range.mp (Finset.mem_filter.mp hk).1⟩
    have e : ∀ k : ℕ, ((2 : ℝ) ^ k)⁻¹ = (1 / 2 : ℝ) ^ k := fun k => by rw [one_div, inv_pow]
    calc ∑ k ∈ S, ((2 : ℝ) ^ k)⁻¹ ≤ ∑ k ∈ Finset.Ico k₀ K, ((2 : ℝ) ^ k)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ k ∈ Finset.Ico k₀ K, (1 / 2 : ℝ) ^ k := Finset.sum_congr rfl fun k _ => e k
      _ ≤ (1 / 2 : ℝ) ^ k₀ / (1 - 1 / 2) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
      _ = 2 * ((2 : ℝ) ^ k₀)⁻¹ := by rw [← e]; ring
      _ ≤ 2 / X := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ hX hk₀.le) (by norm_num)

/-! ## Radial shells -/

lemma supn_nonneg (y : Lattice3) : 0 ≤ supn y := (abs_nonneg _).trans (abs_le_supn y 0)

lemma supn_add_le (x y : Lattice3) : supn (x + y) ≤ supn x + supn y := by
  have h : ∀ i : Fin 3, |((x + y) i : ℝ)| ≤ supn x + supn y := fun i => by
    rw [Pi.add_apply, Int.cast_add]
    exact (abs_add_le _ _).trans (add_le_add (abs_le_supn x i) (abs_le_supn y i))
  unfold supn
  exact max_le (h 0) (max_le (h 1) (h 2))

lemma supn_neg (y : Lattice3) : supn (-y) = supn y := by
  unfold supn; simp [abs_neg]

lemma supn_le_rho (y : Lattice3) : supn y ≤ rho y := by
  unfold rho
  exact Real.le_sqrt_of_sq_le (supn_sq_le_lsq y)

/-- The radial function of a shell type: `|y|` (Euclidean) or `‖y‖_∞` (cube). -/
noncomputable def rad : Bool → Lattice3 → ℝ
  | false, y => rho y
  | true, y => supn y

lemma rad_nonneg (cube : Bool) (y : Lattice3) : 0 ≤ rad cube y := by
  cases cube
  · exact rho_nonneg y
  · exact supn_nonneg y

lemma rad_add_le (cube : Bool) (x y : Lattice3) : rad cube (x + y) ≤ rad cube x + rad cube y := by
  cases cube
  · exact rho_add_le x y
  · exact supn_add_le x y

lemma rad_neg (cube : Bool) (y : Lattice3) : rad cube (-y) = rad cube y := by
  cases cube
  · change rho (-y) = rho y
    unfold rho; congr 1; unfold lsq; push_cast [Pi.neg_apply]; ring
  · exact supn_neg y

lemma rad_le_rho (cube : Bool) (y : Lattice3) : rad cube y ≤ rho y := by
  cases cube
  · exact le_rfl
  · exact supn_le_rho y

/-- A physical shell in terms of the radial function: `λ/g ≤ rad < (λ + ρ)/g`. -/
lemma physSh_iff {cube : Bool} {g lam ρ : ℝ} (hg : 0 < g) (hlam : 0 ≤ lam) (hρ : 0 < ρ)
    (y : Lattice3) :
    physSh cube g lam ρ y ↔ lam / g ≤ rad cube y ∧ rad cube y < (lam + ρ) / g := by
  have hs : lam / g + ρ / g = (lam + ρ) / g := by ring
  cases cube
  · change shE (lam / g) (ρ / g) y ↔ lam / g ≤ rho y ∧ rho y < (lam + ρ) / g
    unfold shE rho
    have h1 : 0 ≤ lam / g := div_nonneg hlam hg.le
    have h2 : 0 < (lam + ρ) / g := div_pos (by linarith) hg
    rw [hs, Real.le_sqrt h1 (lsq_nonneg y), Real.sqrt_lt' h2]
  · change shC (lam / g) (ρ / g) y ↔ lam / g ≤ supn y ∧ supn y < (lam + ρ) / g
    unfold shC; rw [hs]

open Classical in
/-- Telescoping of interval indicators along a monotone sequence of radii. -/
lemma sum_interval_ind (u : ℕ → ℝ) (hu : Monotone u) (t : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (if u i ≤ t ∧ t < u (i + 1) then (1 : ℂ) else 0) =
      if u 0 ≤ t ∧ t < u n then 1 else 0 := by
  have hterm : ∀ i, (if u i ≤ t ∧ t < u (i + 1) then (1 : ℂ) else 0) =
      (if t < u (i + 1) then 1 else 0) - (if t < u i then 1 else 0) := by
    intro i
    have hmon : u i ≤ u (i + 1) := hu (Nat.le_succ i)
    by_cases h1 : t < u i
    · rw [if_neg (fun h => absurd h.1 (not_le.mpr h1)), if_pos (lt_of_lt_of_le h1 hmon), if_pos h1,
        sub_self]
    · rw [if_neg h1, sub_zero]
      push Not at h1
      by_cases h2 : t < u (i + 1)
      · rw [if_pos ⟨h1, h2⟩, if_pos h2]
      · rw [if_neg (fun h => h2 h.2), if_neg h2]
  simp only [hterm]
  rw [Finset.sum_range_sub (fun i => if t < u i then (1 : ℂ) else 0)]
  have hmon : u 0 ≤ u n := hu (Nat.zero_le n)
  by_cases h1 : t < u 0
  · rw [if_pos (lt_of_lt_of_le h1 hmon), if_pos h1, sub_self,
      if_neg (fun h => absurd h.1 (not_le.mpr h1))]
  · rw [if_neg h1, sub_zero]
    push Not at h1
    by_cases h2 : t < u n
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.2)]

/-- **Wide bands** (the text's "divide it into a bounded number of bands"): from eq:band for
`1 ≤ ρ ≤ λ` (`λ ≥ l₀`), a band of width up to `4λ` at radius `λ ≥ max(l₀, 4)` has mass at most
`2 B λ^{-3} ρ^{1/2}`. -/
lemma wide_band {g : ℝ} (hg : 0 < g) (a : Fin eta) (cube : Bool) (x : L2 eta) {l₀ B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ lam ρ : ℝ, l₀ ≤ lam → 1 ≤ ρ → ρ ≤ lam →
      ‖shMask a (physSh cube g lam ρ) x‖ ≤ B * lam ^ (-(3 : ℝ)) * Real.sqrt ρ)
    {lam ρ : ℝ} (hlam : l₀ ≤ lam) (hlam4 : 4 ≤ lam) (hρ : 1 ≤ ρ) (hρl : ρ ≤ 4 * lam) :
    ‖shMask a (physSh cube g lam ρ) x‖ ≤ 2 * B * lam ^ (-(3 : ℝ)) * Real.sqrt ρ := by
  have hl0 : 0 < lam := by linarith
  have hp : 0 ≤ lam ^ (-(3 : ℝ)) := Real.rpow_nonneg hl0.le _
  by_cases hsmall : ρ ≤ lam
  · refine (hB lam ρ hlam hρ hsmall).trans ?_
    have : 0 ≤ B * lam ^ (-(3 : ℝ)) * Real.sqrt ρ := by positivity
    linarith
  push Not at hsmall
  classical
  -- the four sub-bands
  set u : ℕ → ℝ := fun i => (lam + i * (ρ / 4)) / g
  have hu : Monotone u := by
    intro i i' hii'
    simp only [u]
    have : (i : ℝ) ≤ i' := by exact_mod_cast hii'
    exact div_le_div_of_nonneg_right (by nlinarith) hg.le
  have hdec : shMask a (physSh cube g lam ρ) x =
      ∑ i ∈ Finset.range 4, shMask a (physSh cube g (lam + i * (ρ / 4)) (ρ / 4)) x := by
    ext q
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp only [shMask_apply]
    rw [← Finset.sum_mul]
    congr 1
    have h1 : (if physSh cube g lam ρ (q a) then (1 : ℂ) else 0) =
        if u 0 ≤ rad cube (q a) ∧ rad cube (q a) < u 4 then 1 else 0 := by
      have e0 : u 0 = lam / g := by simp [u]
      have e4 : u 4 = (lam + ρ) / g := by simp only [u]; push_cast; ring
      rw [e0, e4]
      by_cases h : physSh cube g lam ρ (q a)
      · rw [if_pos h, if_pos ((physSh_iff hg hl0.le (by linarith) _).mp h)]
      · rw [if_neg h, if_neg (fun h' => h ((physSh_iff hg hl0.le (by linarith) _).mpr h'))]
    have h2 : ∀ i ∈ Finset.range 4,
        (if physSh cube g (lam + i * (ρ / 4)) (ρ / 4) (q a) then (1 : ℂ) else 0) =
        if u i ≤ rad cube (q a) ∧ rad cube (q a) < u (i + 1) then 1 else 0 := by
      intro i _
      have hi0 : 0 ≤ lam + i * (ρ / 4) := by positivity
      have ei : u (i + 1) = (lam + i * (ρ / 4) + ρ / 4) / g := by simp only [u]; push_cast; ring
      rw [ei]
      by_cases h : physSh cube g (lam + i * (ρ / 4)) (ρ / 4) (q a)
      · rw [if_pos h, if_pos ((physSh_iff hg hi0 (by linarith) _).mp h)]
      · rw [if_neg h, if_neg (fun h' => h ((physSh_iff hg hi0 (by linarith) _).mpr h'))]
    rw [h1, Finset.sum_congr rfl h2, sum_interval_ind u hu]
  rw [hdec]
  refine (norm_sum_le _ _).trans ?_
  have hpiece : ∀ i ∈ Finset.range 4,
      ‖shMask a (physSh cube g (lam + i * (ρ / 4)) (ρ / 4)) x‖ ≤ B * lam ^ (-(3 : ℝ)) * (Real.sqrt ρ / 2) := by
    intro i _
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hrad : lam ≤ lam + i * (ρ / 4) := by nlinarith
    have h1 := hB (lam + i * (ρ / 4)) (ρ / 4) (hlam.trans hrad) (by linarith) (by linarith)
    refine h1.trans ?_
    have hmono : (lam + i * (ρ / 4)) ^ (-(3 : ℝ)) ≤ lam ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hl0 hrad (by norm_num)
    have hs : Real.sqrt (ρ / 4) = Real.sqrt ρ / 2 := by
      rw [Real.sqrt_div' ρ (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hs]
    have : 0 ≤ Real.sqrt ρ / 2 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hB0) this
  calc ∑ i ∈ Finset.range 4, ‖shMask a (physSh cube g (lam + i * (ρ / 4)) (ρ / 4)) x‖
      ≤ ∑ _i ∈ Finset.range 4, B * lam ^ (-(3 : ℝ)) * (Real.sqrt ρ / 2) := Finset.sum_le_sum hpiece
    _ = 2 * B * lam ^ (-(3 : ℝ)) * Real.sqrt ρ := by
        rw [Finset.sum_const, Finset.card_range]; simp; ring

/-! ## Geometry of the dyadic kernels -/

lemma rad_sub_ge (cube : Bool) (x y : Lattice3) : rad cube x - rad cube y ≤ rad cube (x - y) := by
  have h := rad_add_le cube (x - y) y
  rw [sub_add_cancel] at h
  linarith

lemma rad_sub_le (cube : Bool) (x y : Lattice3) : rad cube (x - y) ≤ rad cube x + rad cube y := by
  have h := rad_add_le cube x (-y)
  rw [← sub_eq_add_neg, rad_neg] at h
  exact h

omit [Fintype ν] in
lemma rad_tr_moved (cube : Bool) {j : Ch eta} {a : Fin eta} (ha : a ∈ moved j) (x : Lattice3) :
    rad cube (tr j x a) = rad cube x := by
  rcases tr_apply_moved j x ha with h | h
  · rw [h]
  · rw [h, rad_neg]

omit [Fintype ν] in
lemma nsq_tr_moved {j : Ch eta} {a : Fin eta} (ha : a ∈ moved j) (x : Lattice3) :
    nsq (tr j x a) = nsq x := by
  rcases tr_apply_moved j x ha with h | h
  · rw [h]
  · rw [h, nsq_neg]

lemma rho_lt_of_nsq_lt {x : Lattice3} {r : ℝ} (hr : 0 ≤ r) (h : nsq x < r ^ 2) : rho x < r := by
  unfold rho
  rw [Real.sqrt_lt' (by
    rcases hr.lt_or_eq with h' | h'
    · exact h'
    · exfalso; rw [← h'] at h; have := nsq_nonneg x; nlinarith)]
  rw [lsq_eq_nsq]; exact h

omit [Fintype ν] in
lemma rho_le_of_mem_cube {N : ℕ} {p : Cf eta} (hp : p ∈ fourierConfigCube eta N) (a : Fin eta) :
    rho (p a) ≤ 2 * N := by
  rw [mem_fourierConfigCube_iff] at hp
  have hc : ∀ i : Fin 3, ((p a i : ℤ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := fun i => by
    have h := hp a i
    have h1 : (-(N : ℝ)) ≤ (p a i : ℝ) := by exact_mod_cast h.1
    have h2 : ((p a i : ℤ) : ℝ) ≤ N := by exact_mod_cast h.2
    nlinarith
  unfold rho
  rw [Real.sqrt_le_left (by positivity)]
  unfold lsq
  nlinarith [hc 0, hc 1, hc 2]

omit [Fintype ν] in
/-- A shell beyond the threshold `l` is unaffected by the tail mask at `l`. -/
lemma shMask_tailMask_eq {g l : ℝ} (hg : 0 < g) (a : Fin eta) (sh : Lattice3 → Prop)
    (hsh : ∀ y, sh y → (l / g) ^ 2 < nsq y) (x : L2 eta) :
    shMask a sh (tailMask g l a x) = shMask a sh x := by
  ext q
  rw [shMask_apply, shMask_apply, tailMask_apply]
  split_ifs with h1 h2
  · rw [one_mul]
  · exfalso; apply h2
    have h3 := hsh _ h1
    have h4 : l / g < Real.sqrt (latticeNormSq (q a)) :=
      Real.lt_sqrt_of_sq_lt (by rw [← nsq_eq_latticeNormSq]; exact h3)
    rw [div_lt_iff₀ hg] at h4
    linarith
  · simp
  · simp

omit [Fintype ν] in
lemma norm_tailMask_tailMask_le (g l₁ l₂ : ℝ) (a : Fin eta) (x : L2 eta) :
    ‖tailMask g l₁ a (tailMask g l₂ a x)‖ ≤ ‖tailMask g l₁ a x‖ := by
  have := l2_norm_le_of_le (tailMask g l₁ a (tailMask g l₂ a x)) (tailMask g l₁ a x) zero_le_one
    fun q => by
      rw [tailMask_apply, tailMask_apply, tailMask_apply, one_mul]
      split_ifs <;> simp
  rwa [one_mul] at this

/-- Two Schur bounds for one kernel give one operator; an input that agrees on the columns that
reach the output gives the same image, so the sharper bound applies to it. -/
lemma toCLM_norm_le_of_agree {κ : Cf eta → Cf eta → ℂ} {A' B' A B : ℝ} (hS : SchurBound κ A' B')
    (h : SchurBound κ A B) (z z' : L2 eta) (hz : ∀ q p, κ q p ≠ 0 → z' p = z p) :
    ‖hS.toCLM z‖ ≤ Real.sqrt (A * B) * ‖z'‖ := by
  have e : hS.toCLM z = h.toCLM z' := by
    ext q
    rw [SchurBound.toCLM_apply, SchurBound.toCLM_apply]
    unfold kerApply
    refine tsum_congr fun p => ?_
    by_cases hk : κ q p = 0
    · rw [hk, zero_mul, zero_mul]
    · rw [hz q p hk]
  rw [e]
  exact (h.toCLM.le_opNorm z').trans (mul_le_mul_of_nonneg_right h.norm_toCLM_le (norm_nonneg _))

/-! ## The dyadic kernels of a moved channel -/

section Moved

variable (sys : CoulombSystem eta ν) (L : ℝ)

/-- The dyadic kernel of channel `j` (its channel system): outputs with register `a` in `sh`, hops
`2^k ≤ |ν| < 2^{k+1}`. -/
noncomputable abbrev dyK (j : Ch eta) (a : Fin eta) (sh : Lattice3 → Prop) (k : ℕ) :
    Cf eta → Cf eta → ℂ :=
  tsK (sysCh sys j) L j a sh ((2 : ℝ) ^ k)

variable {sys L}

open Classical in
lemma dyK_ne_zero {j : Ch eta} {a : Fin eta} {sh : Lattice3 → Prop} {k : ℕ} {q p : Cf eta}
    (h : dyK sys L j a sh k q p ≠ 0) :
    sh (q a) ∧ OnCh j q p ∧ (4 : ℝ) ^ k ≤ nsq (q (lead j) - p (lead j)) ∧
      nsq (q (lead j) - p (lead j)) < 4 ^ (k + 1) := by
  unfold dyK tsK at h
  split_ifs at h with hc
  · rw [two_pow_sq, two_two_pow_sq] at hc; exact hc
  · exact absurd rfl h

open Classical in
/-- **The dyadic decomposition** on inputs supported in a cube: for outputs in `sh`,
`1_sh(q_a) (W_j z)(q) = Σ_{k<K} (D_k z)(q)` with `K` depending only on the cube and the shell. -/
theorem dyadic_decomp (hL : 0 < L) (j : Ch eta) {a : Fin eta} (ha : a ∈ moved j)
    (sh : Lattice3 → Prop) {Bd : ℝ} (hsh : ∀ y, sh y → rho y ≤ Bd) (N : ℕ) :
    ∃ K : ℕ, ∀ (z : Cf eta → ℂ), (∀ p ∉ fourierConfigCube eta N, z p = 0) → ∀ q : Cf eta,
      (if sh (q a) then (1 : ℂ) else 0) * ∑' p, z p * potKernel (sysCh sys j) L q p =
        ∑ k ∈ Finset.range K, ∑' p, dyK sys L j a sh k q p * z p := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((Bd + 2 * N) ^ 2) (by norm_num : (1 : ℝ) < 4)
  refine ⟨K, fun z hz q => ?_⟩
  have hfin : ∀ f : Cf eta → ℂ, ∑' p, f p * z p = ∑ p ∈ fourierConfigCube eta N, f p * z p :=
    fun f => tsum_eq_sum fun p hp => by rw [hz p hp, mul_zero]
  have hfin' : ∑' p, z p * potKernel (sysCh sys j) L q p =
      ∑ p ∈ fourierConfigCube eta N, z p * potKernel (sysCh sys j) L q p :=
    tsum_eq_sum fun p hp => by rw [hz p hp, zero_mul]
  rw [hfin', Finset.mul_sum]
  simp only [hfin]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_mul]
  by_cases hq : sh (q a)
  · rw [if_pos hq, one_mul]
    by_cases hon : OnCh j q p
    · set x := q (lead j) - p (lead j) with hx
      have hdy : ∀ k, dyK sys L j a sh k q p =
          (if (4 : ℝ) ^ k ≤ nsq x ∧ nsq x < 4 ^ (k + 1) then (1 : ℂ) else 0) *
            potKernel (sysCh sys j) L q p := by
        intro k
        unfold dyK tsK
        rw [two_pow_sq, two_two_pow_sq]
        by_cases hk : (4 : ℝ) ^ k ≤ nsq x ∧ nsq x < 4 ^ (k + 1)
        · rw [if_pos ⟨hq, hon, hk⟩, if_pos hk, one_mul]
        · rw [if_neg (fun h => hk h.2.2), if_neg hk, zero_mul]
      simp only [hdy]
      rw [← Finset.sum_mul]
      by_cases hx0 : x = 0
      · have hK0 : potKernel (sysCh sys j) L q p = 0 := by
          have h := potKernel_sysCh_le sys hL j q p
          unfold chMaj at h
          rw [if_pos hon, ← hx, hx0] at h
          have h0 : latticeNormSq (0 : Lattice3) = 0 := by simp [latticeNormSq]
          rw [h0, div_zero] at h
          exact norm_le_zero_iff.mp h
        rw [hK0]; ring
      · have h1 : 1 ≤ nsq x := one_le_latticeNormSq hx0
        have he : q a - p a = tr j x a := by
          have e : q = p + tr j x := hon
          rw [e, Pi.add_apply]; abel
        have hr : rho (q a - p a) ≤ Bd + 2 * N := by
          have h1 := rad_sub_le false (q a) (p a)
          change rho (q a - p a) ≤ rho (q a) + rho (p a) at h1
          have h2 := hsh _ hq
          have h3 := rho_le_of_mem_cube hp a
          linarith
        have h2 : nsq x < 4 ^ K := by
          have e : nsq x = rho (q a - p a) ^ 2 := by rw [rho_sq, lsq_eq_nsq, he, nsq_tr_moved ha]
          rw [e]
          have := pow_le_pow_left₀ (rho_nonneg _) hr 2
          linarith
        rw [sum_dyadic_ind h1 h2, one_mul, mul_comm]
    · have hK0 : potKernel (sysCh sys j) L q p = 0 := by
        by_contra h; exact hon (potKernel_sysCh_onCh sys hL h)
      have hdy : ∀ k, dyK sys L j a sh k q p = 0 := fun k => by
        unfold dyK tsK; rw [if_neg (fun h => hon h.2.1)]
      simp [hdy, hK0]
  · rw [if_neg hq, zero_mul]
    have hdy : ∀ k, dyK sys L j a sh k q p = 0 := fun k => by
      unfold dyK tsK; rw [if_neg (fun h => hq h.1)]
    simp [hdy]

end Moved

/-! ## The arithmetic of the three regimes -/

/-- The constant `D_g = 1 + 5 max(g,1) max(1,1/g)` of the thin regime. -/
noncomputable def Dg (g : ℝ) : ℝ := 1 + 5 * max g 1 * max 1 (1 / g)

lemma one_le_Dg (g : ℝ) : 1 ≤ Dg g := by
  unfold Dg
  have h1 : 1 ≤ max g 1 := le_max_right _ _
  have h2 : 1 ≤ max 1 (1 / g) := le_max_left _ _
  nlinarith

/-- The thin regime: `√(r min(m, r)) √(ρ + 4gr) ≤ √D_g r √ρ`, `m = max(ρ/g, 1)`. -/
lemma reg1_arith {g ρ r : ℝ} (hg : 0 < g) (hρ : 1 ≤ ρ) (hr : 0 ≤ r) :
    Real.sqrt (r * min (max (ρ / g) 1) r) * Real.sqrt (ρ + 4 * g * r) ≤
      Real.sqrt (Dg g) * r * Real.sqrt ρ := by
  set m := max (ρ / g) 1 with hm
  set G := max g 1
  set H := max 1 (1 / g)
  have hG1 : 1 ≤ G := le_max_right _ _
  have hH1 : 1 ≤ H := le_max_left _ _
  have hGg : g ≤ G := le_max_left _ _
  have hHg : 1 / g ≤ H := le_max_right _ _
  have hmρ : m ≤ H * ρ := by
    rcases le_total (ρ / g) 1 with h | h
    · rw [hm, max_eq_right h]; nlinarith
    · rw [hm, max_eq_left h]
      calc ρ / g = 1 / g * ρ := by ring
        _ ≤ H * ρ := mul_le_mul_of_nonneg_right hHg (by linarith)
  have hm1 : 1 ≤ m := le_max_right _ _
  have hD : Dg g = 1 + 5 * G * H := rfl
  have hsq : r * min m r * (ρ + 4 * g * r) ≤ Dg g * r ^ 2 * ρ := by
    rw [hD]
    rcases le_total r m with hrm | hrm
    · rw [min_eq_right hrm]
      -- `4 g r ≤ 4 G H ρ`
      have h4 : g * r ≤ G * H * ρ := by
        rcases le_total (ρ / g) 1 with h | h
        · have hr1 : r ≤ 1 := by rw [hm, max_eq_right h] at hrm; exact hrm
          have : g * r ≤ G := by nlinarith
          have : G ≤ G * H * ρ := by
            have : 1 ≤ H * ρ := by nlinarith
            nlinarith
          linarith
        · have hrr : r ≤ ρ / g := by rw [hm, max_eq_left h] at hrm; exact hrm
          have : g * r ≤ ρ := by rw [le_div_iff₀ hg] at hrr; linarith
          have : ρ ≤ G * H * ρ := by
            have : 1 ≤ G * H := by nlinarith
            nlinarith
          linarith
      have : r * r * (ρ + 4 * g * r) = r ^ 2 * ρ + 4 * r ^ 2 * (g * r) := by ring
      rw [this]
      have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
      have k1 := mul_le_mul_of_nonneg_left h4 hr2
      have k2 : 0 ≤ G * H * r ^ 2 * ρ := by positivity
      nlinarith
    · rw [min_eq_left hrm]
      have hρgr : ρ ≤ g * r := by
        have : ρ / g ≤ m := le_max_left _ _
        rw [div_le_iff₀ hg] at this; nlinarith
      have h1 : m * (ρ + 4 * g * r) ≤ H * ρ * (5 * (g * r)) := by
        have hm0 : 0 ≤ m := by linarith
        calc m * (ρ + 4 * g * r) ≤ m * (5 * (g * r)) := by nlinarith
          _ ≤ H * ρ * (5 * (g * r)) := mul_le_mul_of_nonneg_right hmρ (by positivity)
      have h2 : H * ρ * (5 * (g * r)) ≤ 5 * G * H * ρ * r := by
        have : H * ρ * (5 * (g * r)) = 5 * (H * ρ * r) * g := by ring
        rw [this]
        have : 0 ≤ 5 * (H * ρ * r) := by positivity
        nlinarith
      calc r * m * (ρ + 4 * g * r) = r * (m * (ρ + 4 * g * r)) := by ring
        _ ≤ r * (5 * G * H * ρ * r) := mul_le_mul_of_nonneg_left (h1.trans h2) hr
        _ ≤ (1 + 5 * G * H) * r ^ 2 * ρ := by nlinarith [sq_nonneg r]
  rw [← Real.sqrt_mul (by positivity)]
  have e : Real.sqrt (Dg g) * r * Real.sqrt ρ = Real.sqrt (Dg g * r ^ 2 * ρ) := by
    rw [Real.sqrt_mul (by have := one_le_Dg g; positivity), Real.sqrt_mul (by
      have := one_le_Dg g; positivity), Real.sqrt_sq hr]
  rw [e]
  exact Real.sqrt_le_sqrt hsq

lemma rpow_neg_three_le_of_half {lam d : ℝ} (hlam : 0 < lam) (hd2 : d ≤ lam / 2) :
    (lam - d) ^ (-(3 : ℝ)) ≤ 8 * lam ^ (-(3 : ℝ)) := by
  have h1 : lam / 2 ≤ lam - d := by linarith
  have h2 : (lam - d) ^ (-(3 : ℝ)) ≤ (lam / 2) ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  refine h2.trans (le_of_eq ?_)
  rw [Real.div_rpow hlam.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (2 : ℝ) ^ (3 : ℝ) = 8 by norm_num]
  field_simp

lemma rpow_neg_five_half_mul_sqrt {l : ℝ} (hl : 0 < l) :
    l ^ (-(5 / 2 : ℝ)) * Real.sqrt l = 1 / l ^ 2 := by
  rw [FSNormal.rpow_neg_five_half_eq hl]
  have hs : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  field_simp

lemma half_rpow_neg_five_half {l : ℝ} (hl : 0 < l) :
    (l / 2) ^ (-(5 / 2 : ℝ)) = 2 ^ (5 / 2 : ℝ) * l ^ (-(5 / 2 : ℝ)) := by
  rw [Real.div_rpow hl.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

/-- The middle regime: `c √(468000 Λ m) M (λ/2)^{-5/2} ≤ c √(468000 H/g) 2^{5/2} M λ^{-2} ρ^{1/2}`. -/
lemma reg2_arith {g c M lam ρ : ℝ} (hg : 0 < g) (hc : 0 ≤ c) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hρ : 1 ≤ ρ) :
    c * Real.sqrt (468000 * (lam / g) * max (ρ / g) 1) * (M * (lam / 2) ^ (-(5 / 2 : ℝ))) ≤
      c * Real.sqrt (468000 * max 1 (1 / g) / g) * 2 ^ (5 / 2 : ℝ) * M * (1 / lam ^ 2) *
        Real.sqrt ρ := by
  have hmρ : max (ρ / g) 1 ≤ max 1 (1 / g) * ρ := by
    rcases le_total (ρ / g) 1 with h | h
    · rw [max_eq_right h]
      calc (1 : ℝ) ≤ 1 * ρ := by linarith
        _ ≤ max 1 (1 / g) * ρ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
    · rw [max_eq_left h]
      calc ρ / g = 1 / g * ρ := by ring
        _ ≤ max 1 (1 / g) * ρ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  have hs : Real.sqrt (468000 * (lam / g) * max (ρ / g) 1) ≤
      Real.sqrt (468000 * max 1 (1 / g) / g) * Real.sqrt lam * Real.sqrt ρ := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have e : 468000 * max 1 (1 / g) / g * lam * ρ = 468000 * (lam / g) * (max 1 (1 / g) * ρ) := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hmρ (by positivity)
  rw [half_rpow_neg_five_half hlam]
  have hp : 0 ≤ lam ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hlam.le _
  calc c * Real.sqrt (468000 * (lam / g) * max (ρ / g) 1) * (M * (2 ^ (5 / 2 : ℝ) * lam ^ (-(5 / 2 : ℝ))))
      ≤ c * (Real.sqrt (468000 * max 1 (1 / g) / g) * Real.sqrt lam * Real.sqrt ρ) *
          (M * (2 ^ (5 / 2 : ℝ) * lam ^ (-(5 / 2 : ℝ)))) := by
        gcongr
    _ = c * Real.sqrt (468000 * max 1 (1 / g) / g) * 2 ^ (5 / 2 : ℝ) * M *
          (lam ^ (-(5 / 2 : ℝ)) * Real.sqrt lam) * Real.sqrt ρ := by ring
    _ = _ := by rw [rpow_neg_five_half_mul_sqrt hlam]

/-- The far regime, one shell: `c √(52 N/r) M (gr/2)^{-5/2} = c √(117000 m) Λ (2/g)^{5/2} M r^{-3}`
for `N = 2250 Λ² m`. -/
lemma reg3_term {g c M Λ m r : ℝ} (hg : 0 < g) (hΛ : 0 ≤ Λ) (hm : 0 ≤ m) (hr : 0 < r) :
    c * Real.sqrt (52 * (2250 * Λ ^ 2 * m) / r) * (M * (g * r / 2) ^ (-(5 / 2 : ℝ))) =
      c * Real.sqrt (117000 * m) * Λ * (2 / g) ^ (5 / 2 : ℝ) * M * (r⁻¹) ^ 3 := by
  have e1 : Real.sqrt (52 * (2250 * Λ ^ 2 * m) / r) = Λ * Real.sqrt (117000 * m) * Real.sqrt (1 / r) := by
    rw [show 52 * (2250 * Λ ^ 2 * m) / r = Λ ^ 2 * (117000 * m) * (1 / r) by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hΛ]
  have e2 : (g * r / 2) ^ (-(5 / 2 : ℝ)) = (2 / g) ^ (5 / 2 : ℝ) * r ^ (-(5 / 2 : ℝ)) := by
    rw [show g * r / 2 = r / (2 / g) by field_simp, Real.div_rpow hr.le (by positivity),
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 / g)]
    rw [div_eq_mul_inv, inv_inv, mul_comm]
  have e3 : Real.sqrt (1 / r) * r ^ (-(5 / 2 : ℝ)) = (r⁻¹) ^ 3 := by
    rw [FSNormal.rpow_neg_five_half_eq hr, Real.sqrt_div' 1 hr.le, Real.sqrt_one]
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    field_simp
    exact (Real.sq_sqrt hr.le).symm
  rw [e1, e2]
  calc c * (Λ * Real.sqrt (117000 * m) * Real.sqrt (1 / r)) *
        (M * ((2 / g) ^ (5 / 2 : ℝ) * r ^ (-(5 / 2 : ℝ))))
      = c * Real.sqrt (117000 * m) * Λ * (2 / g) ^ (5 / 2 : ℝ) * M *
          (Real.sqrt (1 / r) * r ^ (-(5 / 2 : ℝ))) := by ring
    _ = _ := by rw [e3]

lemma max_div_le {g ρ : ℝ} (hρ : 1 ≤ ρ) : max (ρ / g) 1 ≤ max 1 (1 / g) * ρ := by
  rcases le_total (ρ / g) 1 with h | h
  · rw [max_eq_right h]
    calc (1 : ℝ) ≤ 1 * ρ := by linarith
      _ ≤ max 1 (1 / g) * ρ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  · rw [max_eq_left h]
    calc ρ / g = 1 / g * ρ := by ring
      _ ≤ max 1 (1 / g) * ρ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

/-- The far regime, summed: `c √(117000 m) Λ (2/g)^{5/2} M (8Λ)^{-2} (2/(8Λ)) ≤
c √(117000 H) (2/g)^{5/2} g²/256 · M λ^{-2} ρ^{1/2}` (`Λ = λ/g`). -/
lemma reg3_sum_arith {g c M lam ρ : ℝ} (hg : 0 < g) (hc : 0 ≤ c) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hρ : 1 ≤ ρ) :
    c * Real.sqrt (117000 * max (ρ / g) 1) * (lam / g) * (2 / g) ^ (5 / 2 : ℝ) * M *
        ((1 / (8 * (lam / g))) ^ 2 * (2 / (8 * (lam / g)))) ≤
      c * Real.sqrt (117000 * max 1 (1 / g)) * (2 / g) ^ (5 / 2 : ℝ) * g ^ 2 / 256 * M *
        (1 / lam ^ 2) * Real.sqrt ρ := by
  have hs : Real.sqrt (117000 * max (ρ / g) 1) ≤
      Real.sqrt (117000 * max 1 (1 / g)) * Real.sqrt ρ := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have := max_div_le (g := g) hρ
    nlinarith
  have e : (lam / g) * ((1 / (8 * (lam / g))) ^ 2 * (2 / (8 * (lam / g)))) =
      g ^ 2 / 256 * (1 / lam ^ 2) := by
    field_simp; ring
  have hp : (0 : ℝ) ≤ (2 / g) ^ (5 / 2 : ℝ) := by positivity
  calc c * Real.sqrt (117000 * max (ρ / g) 1) * (lam / g) * (2 / g) ^ (5 / 2 : ℝ) * M *
        ((1 / (8 * (lam / g))) ^ 2 * (2 / (8 * (lam / g))))
      = c * Real.sqrt (117000 * max (ρ / g) 1) * (2 / g) ^ (5 / 2 : ℝ) * M *
          ((lam / g) * ((1 / (8 * (lam / g))) ^ 2 * (2 / (8 * (lam / g))))) := by ring
    _ = c * Real.sqrt (117000 * max (ρ / g) 1) * (2 / g) ^ (5 / 2 : ℝ) * M *
          (g ^ 2 / 256 * (1 / lam ^ 2)) := by rw [e]
    _ ≤ c * (Real.sqrt (117000 * max 1 (1 / g)) * Real.sqrt ρ) * (2 / g) ^ (5 / 2 : ℝ) * M *
          (g ^ 2 / 256 * (1 / lam ^ 2)) := by gcongr
    _ = _ := by ring

/-! ## K2 for a moved channel -/

lemma rho_le_two_rad (cube : Bool) (y : Lattice3) : rho y ≤ 2 * rad cube y := by
  cases cube
  · change rho y ≤ 2 * rho y; linarith [rho_nonneg y]
  · change rho y ≤ 2 * supn y
    unfold rho
    rw [Real.sqrt_le_left (by linarith [supn_nonneg y])]
    have := lsq_le_three_supn_sq y
    nlinarith [sq_nonneg (supn y)]

section K2

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)

/-- The whole-shell count of the physical shell `S_{a,λ,ρ}`. -/
noncomputable def Nsh (L lam ρ : ℝ) : ℝ := 2250 * (lam / gF L) ^ 2 * max (ρ / gF L) 1

open Classical in
include hL in
/-- The dyadic kernels are Schur bounded with the whole-shell count. -/
lemma dyK_schur (j : Ch eta) {a : Fin eta} (ha : a ∈ moved j) (cube : Bool) {lam ρ : ℝ}
    (hlamg : gF L ≤ lam) (hρ : 0 ≤ ρ) (hρl : ρ ≤ lam) (k : ℕ) :
    SchurBound (dyK sys L j a (physSh cube (gF L) lam ρ) k) (52 * chC sys L j * 2 ^ k)
      (chC sys L j * (Nsh L lam ρ / ((2 : ℝ) ^ k) ^ 2)) := by
  have hg := gF_pos hL
  have hcnt : ∀ (x : Lattice3) (T : Finset Lattice3),
      (∀ θ ∈ T, lsq θ ≤ (2 * (2 : ℝ) ^ k) ^ 2 ∧ physSh cube (gF L) lam ρ (x + θ)) →
        (T.card : ℝ) ≤ Nsh L lam ρ := by
    intro x T hT
    have hinj : Function.Injective (fun θ : Lattice3 => x + θ) := add_right_injective x
    rw [← Finset.card_image_of_injective T hinj]
    exact physSh_count hg hlamg hρ hρl _ fun y hy => by
      obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hy
      exact (hT θ hθ).2
  have h := thinschur_gen (sys := sysCh sys j) hL ha (physSh cube (gF L) lam ρ) (ρ' := (2 : ℝ) ^ k)
    (N₀ := Nsh L lam ρ) (one_le_pow₀ (by norm_num)) hcnt
  rw [chC_sysCh, if_pos rfl] at h
  exact h

open Classical in
include hL in
/-- The thin Schur bound of a dyadic kernel (`lem:thinschur` with thickness `max(ρ/g, 1)`). -/
lemma dyK_schur_thin (j : Ch eta) {a : Fin eta} (ha : a ∈ moved j) (cube : Bool) {lam ρ : ℝ}
    (hlamg : gF L ≤ lam) (hρ : 0 ≤ ρ) (hρl : ρ ≤ lam) (k : ℕ) :
    SchurBound (dyK sys L j a (physSh cube (gF L) lam ρ) k) (52 * chC sys L j * 2 ^ k)
      (chC sys L j * (750 * ((2 : ℝ) ^ k) ^ 2 * min (max (ρ / gF L) 1) ((2 : ℝ) ^ k) /
        ((2 : ℝ) ^ k) ^ 2)) := by
  have hg := gF_pos hL
  set Λ := lam / gF L
  set R := ρ / gF L
  set m := max R 1
  have hΛ : 1 ≤ Λ := by rw [le_div_iff₀ hg]; linarith
  have hm1 : 1 ≤ m := le_max_right _ _
  have hmΛ : m ≤ Λ := max_le (div_le_div_of_nonneg_right hρl hg.le) hΛ
  have hRm : R ≤ m := le_max_left _ _
  have hR0 : 0 ≤ R := div_nonneg hρ hg.le
  have hr : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hcnt : ∀ (x : Lattice3) (T : Finset Lattice3),
      (∀ θ ∈ T, lsq θ ≤ (2 * (2 : ℝ) ^ k) ^ 2 ∧ physSh cube (gF L) lam ρ (x + θ)) →
        (T.card : ℝ) ≤ 750 * ((2 : ℝ) ^ k) ^ 2 * min m ((2 : ℝ) ^ k) := by
    intro x T hT
    cases cube
    · refine thin_count_le x (lam := Λ) (ρ := m) (ρ' := (2 : ℝ) ^ k) hm1 hmΛ hr T fun θ hθ => ?_
      obtain ⟨h1, h2⟩ := hT θ hθ
      have h2' : shE Λ R (x + θ) := h2
      refine ⟨h1, h2'.1, lt_of_lt_of_le h2'.2 ?_⟩
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    · refine thin_count_cube_le x (lam := Λ) (ρ := m) (ρ' := (2 : ℝ) ^ k) hm1 hr T fun θ hθ => ?_
      obtain ⟨h1, h2⟩ := hT θ hθ
      have h2' : shC Λ R (x + θ) := h2
      exact ⟨h1, h2'.1, lt_of_lt_of_le h2'.2 (by linarith)⟩
  have h := thinschur_gen (sys := sysCh sys j) hL ha (physSh cube (gF L) lam ρ) (ρ' := (2 : ℝ) ^ k)
    (N₀ := 750 * ((2 : ℝ) ^ k) ^ 2 * min m ((2 : ℝ) ^ k)) hr hcnt
  rw [chC_sysCh, if_pos rfl] at h
  exact h

/-- The feeding band of a thin dyadic shell (`4 · 2^k < Λ`). -/
lemma dyK_feed {j : Ch eta} {a : Fin eta} {cube : Bool} {lam ρ : ℝ} {k : ℕ} {q p : Cf eta}
    (hg : 0 < gF L) (ha : a ∈ moved j) (hlam : 0 < lam) (hρ : 0 < ρ)
    (hk : 4 * (2 : ℝ) ^ k < lam / gF L) (h : dyK sys L j a (physSh cube (gF L) lam ρ) k q p ≠ 0) :
    physSh cube (gF L) (lam - 2 * gF L * 2 ^ k) (ρ + 4 * gF L * 2 ^ k) (p a) := by
  obtain ⟨hq, hon, h1, h2⟩ := dyK_ne_zero h
  set x := q (lead j) - p (lead j)
  set r := (2 : ℝ) ^ k with hr_def
  have hr0 : 0 < r := by positivity
  have hpa : p a = q a - tr j x a := by
    have e : q = p + tr j x := hon
    rw [e, Pi.add_apply]; abel
  have hrad : rad cube (tr j x a) < 2 * r := by
    rw [rad_tr_moved cube ha]
    refine (rad_le_rho cube x).trans_lt ?_
    exact rho_lt_of_nsq_lt (by positivity) (by rw [hr_def, two_two_pow_sq]; exact h2)
  have hq' := (physSh_iff hg hlam.le hρ (q a)).mp hq
  have hk' : 4 * r * gF L < lam := by rwa [lt_div_iff₀ hg] at hk
  have hlam' : 0 ≤ lam - 2 * gF L * r := by nlinarith
  rw [physSh_iff hg hlam' (by positivity) (p a), hpa]
  have hlow := rad_sub_ge cube (q a) (tr j x a)
  have hup := rad_sub_le cube (q a) (tr j x a)
  constructor
  · have e : (lam - 2 * gF L * r) / gF L = lam / gF L - 2 * r := by field_simp
    rw [e]; linarith [hq'.1]
  · have e : (lam - 2 * gF L * r + (ρ + 4 * gF L * r)) / gF L = (lam + ρ) / gF L + 2 * r := by
      field_simp; ring
    rw [e]; linarith [hq'.2]

/-- The input of a far dyadic shell (`2^k > 8Λ`) lies beyond `g 2^k/2`. -/
lemma dyK_tail {j : Ch eta} {a : Fin eta} {cube : Bool} {lam ρ : ℝ} {k : ℕ} {q p : Cf eta}
    (hg : 0 < gF L) (ha : a ∈ moved j) (hlam : 0 < lam) (hρ : 0 < ρ) (hρl : ρ ≤ lam)
    (hk : 8 * (lam / gF L) < (2 : ℝ) ^ k) (h : dyK sys L j a (physSh cube (gF L) lam ρ) k q p ≠ 0) :
    gF L * (2 : ℝ) ^ k / 2 < gF L * Real.sqrt (latticeNormSq (p a)) := by
  obtain ⟨hq, hon, h1, h2⟩ := dyK_ne_zero h
  set x := q (lead j) - p (lead j)
  set r := (2 : ℝ) ^ k with hr_def
  have hr0 : 0 < r := by positivity
  have hq' := (physSh_iff hg hlam.le hρ (q a)).mp hq
  have hrq : rho (q a) < 4 * (lam / gF L) := by
    have h3 := rho_le_two_rad cube (q a)
    have h4 : (lam + ρ) / gF L ≤ 2 * (lam / gF L) := by
      rw [div_le_iff₀ hg]; field_simp; linarith
    linarith [hq'.2]
  have hrx : r ≤ rho x := by
    unfold rho
    refine Real.le_sqrt_of_sq_le ?_
    rw [hr_def, two_pow_sq, lsq_eq_nsq]; exact h1
  have he : q a - p a = tr j x a := by
    have e : q = p + tr j x := hon
    rw [e, Pi.add_apply]; abel
  have htri := rad_sub_le false (q a) (p a)
  change rho (q a - p a) ≤ rho (q a) + rho (p a) at htri
  have hrt : rho (q a - p a) = rho x := by
    rw [he]; exact rad_tr_moved false ha x
  have hpa : r / 2 < rho (p a) := by linarith
  have : rho (p a) = Real.sqrt (latticeNormSq (p a)) := rfl
  rw [← this]
  have := mul_lt_mul_of_pos_left hpa hg
  linarith

/-- The constants of K2 for a moved channel. -/
noncomputable def K2a (sys : CoulombSystem eta ν) (L : ℝ) (j : Ch eta) : ℝ :=
  8 * chC sys L j * Real.sqrt 39000 * Real.sqrt (Dg (gF L)) / gF L

noncomputable def K2b (sys : CoulombSystem eta ν) (L : ℝ) (j : Ch eta) : ℝ :=
  64 * (chC sys L j * Real.sqrt (468000 * max 1 (1 / gF L) / gF L) * 2 ^ (5 / 2 : ℝ)) +
    chC sys L j * Real.sqrt (117000 * max 1 (1 / gF L)) * (2 / gF L) ^ (5 / 2 : ℝ) * gF L ^ 2 / 256

set_option maxHeartbeats 1000000 in
open Classical in
include hL in
/-- **K2 for a channel moving `a`** (the paragraph after `lem:thinschur`): for a good state (`M`)
whose register `a` satisfies eq:band with constant `B` for `λ' ≥ l₀`, the part of `W_j` fed by the
input beyond `λ/2` satisfies `‖1_S W_j 1_{a,>λ/2} u‖ ≤ (K2a B + K2b M) λ^{-2} ρ^{1/2}` for
`λ ≥ max(2 l₀, 8, g)`, `1 ≤ ρ ≤ λ`, either shell type. -/
theorem band_moved (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {M B l₀ : ℝ} {w : MolecularFourierH2 eta} (hF : FGood sys L M w) (hB0 : 0 ≤ B)
    (a : Fin eta) (cube : Bool)
    (hband : ∀ lam' ρ' : ℝ, l₀ ≤ lam' → 1 ≤ ρ' → ρ' ≤ lam' →
      ‖shMask a (physSh cube (gF L) lam' ρ') (Sm eta L w)‖ ≤ B * lam' ^ (-(3 : ℝ)) * Real.sqrt ρ')
    (j : Ch eta) (ha : a ∈ moved j) {lam ρ : ℝ} (hlam0 : 2 * l₀ ≤ lam) (hlam8 : 8 ≤ lam)
    (hlamg : gF L ≤ lam) (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam) :
    ‖shMask a (physSh cube (gF L) lam ρ)
        (Wch sys L Hunit hL hPeriodic j (tailMask (gF L) (lam / 2) a w))‖ ≤
      (K2a sys L j * B + K2b sys L j * M) * (1 / lam ^ 2) * Real.sqrt ρ := by
  have hg := gF_pos hL
  have hM := hF.nonneg
  have hlam : 0 < lam := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hc : 0 ≤ chC sys L j := chC_nonneg sys hL j
  have hΛ1 : 1 ≤ lam / gF L := by rw [le_div_iff₀ hg]; linarith
  have hm1 : (1 : ℝ) ≤ max (ρ / gF L) 1 := le_max_right _ _
  have hSy : Sm eta L (tailMask (gF L) (lam / 2) a w) = tailMask (gF L) (lam / 2) a (Sm eta L w) :=
    stateMap_tailMask L _ a w
  -- the shell is bounded
  have hshB : ∀ v, physSh cube (gF L) lam ρ v → rho v ≤ 4 * (lam / gF L) := by
    intro v hv
    have h1 := (physSh_iff hg hlam.le hρ0 v).mp hv
    have h2 := rho_le_two_rad cube v
    have h3 : (lam + ρ) / gF L ≤ 2 * (lam / gF L) := by
      rw [div_le_iff₀ hg]; field_simp; linarith
    linarith [h1.2]
  -- the shell bounds `b k`
  set Λ := lam / gF L with hΛ_def
  set m := max (ρ / gF L) 1 with hm_def
  set sh := physSh cube (gF L) lam ρ with hsh_def
  set c := chC sys L j with hc_def
  set y := tailMask (gF L) (lam / 2) a w with hy_def
  set b : ℕ → ℝ := fun k =>
    if 4 * (2 : ℝ) ^ k < Λ then
      c * Real.sqrt 39000 * Real.sqrt (Dg (gF L)) * 16 * B * lam ^ (-(3 : ℝ)) * Real.sqrt ρ * 2 ^ k
    else if (2 : ℝ) ^ k ≤ 8 * Λ then
      c * Real.sqrt (468000 * Λ * m) * (M * (lam / 2) ^ (-(5 / 2 : ℝ)))
    else c * Real.sqrt (117000 * m) * Λ * (2 / gF L) ^ (5 / 2 : ℝ) * M * (((2 : ℝ) ^ k)⁻¹) ^ 3
    with hb_def
  have hNn : Nsh L lam ρ = 2250 * Λ ^ 2 * m := rfl
  have hbk : ∀ (N k : ℕ), ‖(dyK_schur sys hL j ha cube hlamg hρ0.le hρl k).toCLM
      (molecularH2Truncate N (Sm eta L y))‖ ≤ b k := by
    intro N k
    set z := molecularH2Truncate N (Sm eta L y)
    have hzSy : ‖z‖ ≤ ‖Sm eta L y‖ := molecularH2Truncate_norm_le N _
    by_cases h1 : 4 * (2 : ℝ) ^ k < Λ
    · -- the thin regime
      have eb : b k = c * Real.sqrt 39000 * Real.sqrt (Dg (gF L)) * 16 * B * lam ^ (-(3 : ℝ)) *
          Real.sqrt ρ * 2 ^ k := by
        simp only [hb_def]; rw [if_pos h1]
      rw [eb]
      set r := (2 : ℝ) ^ k with hr_def
      have hr0 : 0 < r := by positivity
      have hr1 : 1 ≤ r := one_le_pow₀ (by norm_num)
      set feed := physSh cube (gF L) (lam - 2 * gF L * r) (ρ + 4 * gF L * r)
      have hagree : ∀ q p, dyK sys L j a sh k q p ≠ 0 → shMask a feed z p = z p := by
        intro q p hk
        rw [shMask_apply, if_pos (dyK_feed sys hg ha hlam hρ0 h1 hk), one_mul]
      have hT := toCLM_norm_le_of_agree (dyK_schur sys hL j ha cube hlamg hρ0.le hρl k)
        (dyK_schur_thin sys hL j ha cube hlamg hρ0.le hρl k) z (shMask a feed z) hagree
      have hAB : Real.sqrt (52 * c * r * (c * (750 * r ^ 2 * min m r / r ^ 2))) =
          c * Real.sqrt 39000 * Real.sqrt (r * min m r) := by
        rw [show 52 * c * r * (c * (750 * r ^ 2 * min m r / r ^ 2)) =
            c ^ 2 * (39000 * (r * min m r)) by field_simp; ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc,
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 39000)]
        ring
      rw [hAB] at hT
      have hgr : 4 * r * gF L < lam := by rwa [hΛ_def, lt_div_iff₀ hg] at h1
      have hrad : lam / 2 < lam - 2 * gF L * r := by nlinarith
      have hfeed_sub : ∀ v, feed v → ((lam / 2) / gF L) ^ 2 < nsq v := by
        intro v hv
        have h3 := physSh_ge hg (by linarith) hv
        have h4 : ((lam / 2) / gF L) ^ 2 < ((lam - 2 * gF L * r) / gF L) ^ 2 := by
          apply pow_lt_pow_left₀ _ (by positivity) two_ne_zero
          rw [div_lt_div_iff_of_pos_right hg]; exact hrad
        linarith
      have hfeed : ‖shMask a feed z‖ ≤
          2 * B * (lam - 2 * gF L * r) ^ (-(3 : ℝ)) * Real.sqrt (ρ + 4 * gF L * r) := by
        have k1 : ‖shMask a feed z‖ ≤ ‖shMask a feed (Sm eta L y)‖ := by
          rw [shMask_truncate]; exact molecularH2Truncate_norm_le N _
        have k2 : shMask a feed (Sm eta L y) = shMask a feed (Sm eta L w) := by
          rw [hSy, shMask_tailMask_eq hg a feed hfeed_sub]
        rw [k2] at k1
        refine k1.trans (wide_band hg a cube (Sm eta L w) hB0 hband (by linarith) (by linarith)
          (by nlinarith) (by nlinarith))
      have h8 := rpow_neg_three_le_of_half hlam (d := 2 * gF L * r) (by linarith)
      have hreg := reg1_arith hg hρ (le_of_lt hr0) (r := r)
      have hp0 : 0 ≤ (lam - 2 * gF L * r) ^ (-(3 : ℝ)) := Real.rpow_nonneg (by linarith) _
      have hs0 : 0 ≤ Real.sqrt (r * min m r) := Real.sqrt_nonneg _
      have hc39 : 0 ≤ c * Real.sqrt 39000 := by positivity
      calc ‖(dyK_schur sys hL j ha cube hlamg hρ0.le hρl k).toCLM z‖
          ≤ c * Real.sqrt 39000 * Real.sqrt (r * min m r) * ‖shMask a feed z‖ := hT
        _ ≤ c * Real.sqrt 39000 * Real.sqrt (r * min m r) *
              (2 * B * (8 * lam ^ (-(3 : ℝ))) * Real.sqrt (ρ + 4 * gF L * r)) := by
            refine mul_le_mul_of_nonneg_left (hfeed.trans ?_) (by positivity)
            have := Real.sqrt_nonneg (ρ + 4 * gF L * r)
            gcongr
        _ = c * Real.sqrt 39000 * 16 * B * lam ^ (-(3 : ℝ)) *
              (Real.sqrt (r * min m r) * Real.sqrt (ρ + 4 * gF L * r)) := by ring
        _ ≤ c * Real.sqrt 39000 * 16 * B * lam ^ (-(3 : ℝ)) *
              (Real.sqrt (Dg (gF L)) * r * Real.sqrt ρ) := by
            have : 0 ≤ c * Real.sqrt 39000 * 16 * B * lam ^ (-(3 : ℝ)) := by positivity
            exact mul_le_mul_of_nonneg_left hreg this
        _ = _ := by ring
    · by_cases h2 : (2 : ℝ) ^ k ≤ 8 * Λ
      · -- the middle regime
        have eb : b k = c * Real.sqrt (468000 * Λ * m) * (M * (lam / 2) ^ (-(5 / 2 : ℝ))) := by
          simp only [hb_def]; rw [if_neg h1, if_pos h2]
        rw [eb]
        set r := (2 : ℝ) ^ k with hr_def
        have hr0 : 0 < r := by positivity
        have hT := toCLM_norm_le_of_agree (dyK_schur sys hL j ha cube hlamg hρ0.le hρl k)
          (dyK_schur sys hL j ha cube hlamg hρ0.le hρl k) z z (fun _ _ _ => rfl)
        have hAB : Real.sqrt (52 * c * r * (c * (Nsh L lam ρ / r ^ 2))) ≤
            c * Real.sqrt (468000 * Λ * m) := by
          rw [show 52 * c * r * (c * (Nsh L lam ρ / r ^ 2)) = c ^ 2 * (52 * Nsh L lam ρ / r) by
              field_simp,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]
          refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hc
          rw [hNn, div_le_iff₀ hr0]
          push Not at h1
          have : 0 ≤ Λ * m := by positivity
          nlinarith
        have hz : ‖z‖ ≤ M * (lam / 2) ^ (-(5 / 2 : ℝ)) := by
          refine hzSy.trans ?_
          rw [hSy]
          exact (hF.2 a (lam / 2) (by linarith)).1
        calc _ ≤ Real.sqrt (52 * c * r * (c * (Nsh L lam ρ / r ^ 2))) * ‖z‖ := hT
          _ ≤ c * Real.sqrt (468000 * Λ * m) * (M * (lam / 2) ^ (-(5 / 2 : ℝ))) :=
              mul_le_mul hAB hz (norm_nonneg _) (by positivity)
      · -- the far regime
        have eb : b k = c * Real.sqrt (117000 * m) * Λ * (2 / gF L) ^ (5 / 2 : ℝ) * M *
            (((2 : ℝ) ^ k)⁻¹) ^ 3 := by
          simp only [hb_def]; rw [if_neg h1, if_neg h2]
        rw [eb]
        set r := (2 : ℝ) ^ k with hr_def
        have hr0 : 0 < r := by positivity
        push Not at h2
        have hagree : ∀ q p, dyK sys L j a sh k q p ≠ 0 →
            tailMask (gF L) (gF L * r / 2) a z p = z p := by
          intro q p hk
          rw [tailMask_apply, if_pos (dyK_tail sys hg ha hlam hρ0 hρl h2 hk), one_mul]
        have hT := toCLM_norm_le_of_agree (dyK_schur sys hL j ha cube hlamg hρ0.le hρl k)
          (dyK_schur sys hL j ha cube hlamg hρ0.le hρl k) z (tailMask (gF L) (gF L * r / 2) a z)
          hagree
        have hAB : Real.sqrt (52 * c * r * (c * (Nsh L lam ρ / r ^ 2))) =
            c * Real.sqrt (52 * (2250 * Λ ^ 2 * m) / r) := by
          rw [show 52 * c * r * (c * (Nsh L lam ρ / r ^ 2)) = c ^ 2 * (52 * (2250 * Λ ^ 2 * m) / r) by
              rw [hNn]; field_simp,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]
        have hl1 : 1 ≤ gF L * r / 2 := by
          have h2' : 8 * lam < r * gF L := by
            have := h2
            rw [hΛ_def, mul_div_assoc', div_lt_iff₀ hg] at this
            exact this
          linarith
        have hz : ‖tailMask (gF L) (gF L * r / 2) a z‖ ≤ M * (gF L * r / 2) ^ (-(5 / 2 : ℝ)) := by
          have k1 : ‖tailMask (gF L) (gF L * r / 2) a z‖ ≤
              ‖tailMask (gF L) (gF L * r / 2) a (Sm eta L y)‖ := by
            simp only [z]
            rw [← truncate_tailMask]; exact molecularH2Truncate_norm_le N _
          refine k1.trans ?_
          rw [hSy]
          exact (norm_tailMask_tailMask_le _ _ _ a _).trans (hF.2 a _ hl1).1
        calc _ ≤ Real.sqrt (52 * c * r * (c * (Nsh L lam ρ / r ^ 2))) *
              ‖tailMask (gF L) (gF L * r / 2) a z‖ := hT
          _ ≤ c * Real.sqrt (52 * (2250 * Λ ^ 2 * m) / r) * (M * (gF L * r / 2) ^ (-(5 / 2 : ℝ))) := by
              rw [hAB]; exact mul_le_mul_of_nonneg_left hz (by positivity)
          _ = _ := reg3_term hg (by positivity) (by positivity) hr0
  -- the limit over truncations
  have hlim : Tendsto (fun N => ‖shMask a sh (Wch sys L Hunit hL hPeriodic j
      (molecularH2Truncate N y))‖) atTop (𝓝 ‖shMask a sh (Wch sys L Hunit hL hPeriodic j y)‖) :=
    ((continuous_norm.comp ((shMask a sh).continuous.comp
      (Wch sys L Hunit hL hPeriodic j).continuous)).tendsto y).comp (molecularH2Truncate_tendsto y)
  refine le_of_tendsto' hlim fun N => ?_
  obtain ⟨K, hK⟩ := dyadic_decomp (sys := sys) hL j ha sh hshB N
  have hz : ∀ p ∉ fourierConfigCube eta N, molecularH2Truncate N (Sm eta L y) p = 0 :=
    fun p hp => by
      rw [molecularH2Truncate_apply, cubicLatticeCoeffTruncate_eq_zero_of_not_mem N _ p hp]
  have hdec : shMask a sh (Wch sys L Hunit hL hPeriodic j (molecularH2Truncate N y)) =
      ∑ k ∈ Finset.range K, (dyK_schur sys hL j ha cube hlamg hρ0.le hρl k).toCLM
        (molecularH2Truncate N (Sm eta L y)) := by
    ext q
    rw [shMask_apply, Wch_apply, lp.coeFn_sum, Finset.sum_apply]
    have e : Sm eta L (molecularH2Truncate N y) = molecularH2Truncate N (Sm eta L y) := by
      rw [Sm, stateMap_truncate]
    rw [e, hK _ hz q]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [SchurBound.toCLM_apply]
    rfl
  rw [hdec]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hbk N k).trans ?_)
  -- the three regimes
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨α₁, hα₁_def⟩ : ∃ x : ℝ, x = c * Real.sqrt 39000 * Real.sqrt (Dg (gF L)) * 16 * B *
      lam ^ (-(3 : ℝ)) * Real.sqrt ρ := ⟨_, rfl⟩
  have hα₁ : 0 ≤ α₁ := by
    rw [hα₁_def]; have := Real.rpow_nonneg hlam.le (-(3 : ℝ)); positivity
  obtain ⟨b₂, hb₂_def⟩ : ∃ x : ℝ, x = c * Real.sqrt (468000 * Λ * m) *
      (M * (lam / 2) ^ (-(5 / 2 : ℝ))) := ⟨_, rfl⟩
  have hb₂ : 0 ≤ b₂ := by
    rw [hb₂_def]
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ lam / 2 by linarith) (-(5 / 2 : ℝ)); positivity
  obtain ⟨α₃, hα₃_def⟩ : ∃ x : ℝ, x = c * Real.sqrt (117000 * m) * Λ * (2 / gF L) ^ (5 / 2 : ℝ) * M :=
    ⟨_, rfl⟩
  have hα₃ : 0 ≤ α₃ := by
    rw [hα₃_def]
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 / gF L by positivity) (5 / 2 : ℝ); positivity
  set S1 := (Finset.range K).filter (fun k => 4 * (2 : ℝ) ^ k < Λ)
  set S' := (Finset.range K).filter (fun k => ¬ 4 * (2 : ℝ) ^ k < Λ)
  set S2 := S'.filter (fun k => (2 : ℝ) ^ k ≤ 8 * Λ)
  set S3 := S'.filter (fun k => ¬ (2 : ℝ) ^ k ≤ 8 * Λ)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range K) (fun k => 4 * (2 : ℝ) ^ k < Λ) b,
    ← Finset.sum_filter_add_sum_filter_not S' (fun k => (2 : ℝ) ^ k ≤ 8 * Λ) b]
  -- regime 1
  have hS1 : ∑ k ∈ S1, b k ≤ K2a sys L j * B * (1 / lam ^ 2) * Real.sqrt ρ := by
    have e : ∀ k ∈ S1, b k = α₁ * 2 ^ k := by
      intro k hk; simp only [hb_def]; rw [if_pos (Finset.mem_filter.mp hk).2, hα₁_def]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    have hsub : S1 ⊆ (Finset.range K).filter (fun k => (2 : ℝ) ^ k ≤ Λ / 4) := by
      intro k hk
      rw [Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, by linarith [hk.2]⟩
    have hsum := (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (sum_pow_two_le (by positivity : 0 ≤ Λ / 4) K)
    calc α₁ * ∑ k ∈ S1, (2 : ℝ) ^ k ≤ α₁ * (2 * (Λ / 4)) := mul_le_mul_of_nonneg_left hsum hα₁
      _ = K2a sys L j * B * (1 / lam ^ 2) * Real.sqrt ρ := by
          rw [hα₁_def, hΛ_def]; unfold K2a; rw [rpow_neg_three_eq hlam]; field_simp; ring
  -- regime 2
  have hS2 : ∑ k ∈ S2, b k ≤ 64 * b₂ := by
    have e : ∀ k ∈ S2, b k = b₂ := by
      intro k hk
      have hk2 := (Finset.mem_filter.mp hk).2
      have hk1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
      simp only [hb_def]; rw [if_neg hk1, if_pos hk2, hb₂_def]
    rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hb₂
    have hc1 : (S2.card : ℝ) = ∑ _k ∈ S2, (1 : ℝ) := by simp
    rw [hc1]
    have h1 : ∑ _k ∈ S2, (1 : ℝ) ≤ ∑ k ∈ S2, 4 / Λ * (2 : ℝ) ^ k := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
      push Not at hk1
      rw [div_mul_eq_mul_div, le_div_iff₀ hΛ0]
      linarith
    have hsub : S2 ⊆ (Finset.range K).filter (fun k => (2 : ℝ) ^ k ≤ 8 * Λ) := by
      intro k hk
      rw [Finset.mem_filter] at hk ⊢
      exact ⟨(Finset.mem_filter.mp hk.1).1, hk.2⟩
    have h2 := (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (sum_pow_two_le (by positivity : 0 ≤ 8 * Λ) K)
    calc ∑ _k ∈ S2, (1 : ℝ) ≤ ∑ k ∈ S2, 4 / Λ * (2 : ℝ) ^ k := h1
      _ = 4 / Λ * ∑ k ∈ S2, (2 : ℝ) ^ k := by rw [Finset.mul_sum]
      _ ≤ 4 / Λ * (2 * (8 * Λ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 64 := by field_simp; ring
  -- regime 3
  have hS3 : ∑ k ∈ S3, b k ≤ α₃ * ((1 / (8 * Λ)) ^ 2 * (2 / (8 * Λ))) := by
    have e : ∀ k ∈ S3, b k = α₃ * (((2 : ℝ) ^ k)⁻¹) ^ 3 := by
      intro k hk
      have hk2 := (Finset.mem_filter.mp hk).2
      have hk1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
      simp only [hb_def]; rw [if_neg hk1, if_neg hk2, hα₃_def]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hα₃
    have h1 : ∀ k ∈ S3, (((2 : ℝ) ^ k)⁻¹) ^ 3 ≤ (1 / (8 * Λ)) ^ 2 * ((2 : ℝ) ^ k)⁻¹ := by
      intro k hk
      have hk2 := (Finset.mem_filter.mp hk).2
      push Not at hk2
      have hinv : ((2 : ℝ) ^ k)⁻¹ ≤ 1 / (8 * Λ) := by
        rw [one_div]; exact inv_anti₀ (by positivity) hk2.le
      have h0 : 0 ≤ ((2 : ℝ) ^ k)⁻¹ := by positivity
      calc (((2 : ℝ) ^ k)⁻¹) ^ 3 = (((2 : ℝ) ^ k)⁻¹) ^ 2 * ((2 : ℝ) ^ k)⁻¹ := by ring
        _ ≤ (1 / (8 * Λ)) ^ 2 * ((2 : ℝ) ^ k)⁻¹ :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hinv 2) h0
    have hsub : S3 ⊆ (Finset.range K).filter (fun k => 8 * Λ < (2 : ℝ) ^ k) := by
      intro k hk
      rw [Finset.mem_filter] at hk ⊢
      exact ⟨(Finset.mem_filter.mp hk.1).1, not_le.mp hk.2⟩
    have h2 := (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (sum_inv_pow_two_le (by positivity : 0 < 8 * Λ) K)
    calc ∑ k ∈ S3, (((2 : ℝ) ^ k)⁻¹) ^ 3 ≤ ∑ k ∈ S3, (1 / (8 * Λ)) ^ 2 * ((2 : ℝ) ^ k)⁻¹ :=
          Finset.sum_le_sum h1
      _ = (1 / (8 * Λ)) ^ 2 * ∑ k ∈ S3, ((2 : ℝ) ^ k)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (1 / (8 * Λ)) ^ 2 * (2 / (8 * Λ)) := mul_le_mul_of_nonneg_left h2 (by positivity)
  -- collect
  have h2' := reg2_arith hg hc hM hlam hρ (c := c) (M := M)
  have h3' := reg3_sum_arith hg hc hM hlam hρ (c := c) (M := M)
  rw [← hΛ_def, ← hm_def] at h2' h3'
  have e : (K2a sys L j * B + K2b sys L j * M) * (1 / lam ^ 2) * Real.sqrt ρ =
      K2a sys L j * B * (1 / lam ^ 2) * Real.sqrt ρ +
        (64 * (c * Real.sqrt (468000 * max 1 (1 / gF L) / gF L) * 2 ^ (5 / 2 : ℝ) * M *
          (1 / lam ^ 2) * Real.sqrt ρ) +
        c * Real.sqrt (117000 * max 1 (1 / gF L)) * (2 / gF L) ^ (5 / 2 : ℝ) * gF L ^ 2 / 256 *
          M * (1 / lam ^ 2) * Real.sqrt ρ) := by
    unfold K2b; ring
  rw [e]
  have k2 : 64 * b₂ ≤ 64 * (c * Real.sqrt (468000 * max 1 (1 / gF L) / gF L) * 2 ^ (5 / 2 : ℝ) * M *
      (1 / lam ^ 2) * Real.sqrt ρ) := by
    rw [hb₂_def]; exact mul_le_mul_of_nonneg_left h2' (by norm_num)
  have k3 : α₃ * ((1 / (8 * Λ)) ^ 2 * (2 / (8 * Λ))) ≤
      c * Real.sqrt (117000 * max 1 (1 / gF L)) * (2 / gF L) ^ (5 / 2 : ℝ) * gF L ^ 2 / 256 *
        M * (1 / lam ^ 2) * Real.sqrt ρ := by
    rw [hα₃_def]; exact h3'
  linarith

/-- The constant of the combined K2 bound. -/
noncomputable def K2tot (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  ∑ j : Ch eta, (K2a sys L j + K2b sys L j +
    Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit)

include hL in
lemma K2_nonneg (j : Ch eta) (Hunit : ℝ) :
    0 ≤ K2a sys L j ∧ 0 ≤ K2b sys L j ∧
      0 ≤ Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit := by
  have hg := gF_pos hL
  have hc := chC_nonneg sys hL j
  have := one_le_Dg (gF L)
  refine ⟨by unfold K2a; positivity, ?_, ?_⟩
  · unfold K2b
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 / gF L by positivity) (5 / 2 : ℝ)
    positivity
  · have := finiteCoulombPhysicalMassConstant_nonneg (sysCh sys j) L Hunit
    positivity

open Classical in
include hL in
/-- **K2** (the paragraph after `lem:thinschur`, combined): for a good, band-good state, the shell
image of `W u` minus the far-input parts of the channels moving `a` is
`≤ K2tot (B + M) λ^{-2} ρ^{1/2}`; so the `λ^{-1}` of K1 comes only from those far inputs. -/
theorem band_K2 (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {M B l₀ : ℝ} {w : MolecularFourierH2 eta} (hF : FGood sys L M w) (hB0 : 0 ≤ B)
    (a : Fin eta) (cube : Bool)
    (hband : ∀ lam' ρ' : ℝ, l₀ ≤ lam' → 1 ≤ ρ' → ρ' ≤ lam' →
      ‖shMask a (physSh cube (gF L) lam' ρ') (Sm eta L w)‖ ≤ B * lam' ^ (-(3 : ℝ)) * Real.sqrt ρ' ∧
      ‖shMask a (physSh cube (gF L) lam' ρ') (Sm eta L w + coulombFourierKineticH2 sys (gF L) w)‖ ≤
        B * lam'⁻¹ * Real.sqrt ρ')
    {lam ρ : ℝ} (hlam0 : 2 * l₀ ≤ lam) (hlam8 : 8 ≤ lam) (hlamg : gF L ≤ lam) (hρ : 1 ≤ ρ)
    (hρl : ρ ≤ lam) :
    ‖shMask a (physSh cube (gF L) lam ρ) (Wp sys L H w -
        ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∈ moved j),
          Wch sys L Hunit hL hPeriodic j (w - tailMask (gF L) (lam / 2) a w))‖ ≤
      K2tot sys L Hunit * (B + M) * (1 / lam ^ 2) * Real.sqrt ρ := by
  have hM := hF.nonneg
  have hlam : 0 < lam := by linarith
  have hl₀ : l₀ ≤ lam := by
    rcases le_or_gt 0 l₀ with h | h
    · linarith
    · linarith
  set sh := physSh cube (gF L) lam ρ
  set y := tailMask (gF L) (lam / 2) a w
  -- the decomposition
  have hdec : Wp sys L H w - ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∈ moved j),
      Wch sys L Hunit hL hPeriodic j (w - y) =
      ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∈ moved j), Wch sys L Hunit hL hPeriodic j y +
        ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∉ moved j), Wch sys L Hunit hL hPeriodic j w := by
    rw [W_eq_sum_Wch sys L Hunit hL hPeriodic H hKernel w,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Ch eta => a ∈ moved j)]
    have e1 : ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∈ moved j), Wch sys L Hunit hL hPeriodic j w =
        ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∈ moved j), Wch sys L Hunit hL hPeriodic j y +
          ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∈ moved j),
            Wch sys L Hunit hL hPeriodic j (w - y) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← map_add, add_sub_cancel]
    rw [e1]; abel
  set Wj := Wch sys L Hunit hL hPeriodic
  rw [hdec, map_add, map_sum, map_sum]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∈ moved j), shMask a sh (Wj j y)‖ ≤
      ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∈ moved j),
        (K2a sys L j * B + K2b sys L j * M) * (1 / lam ^ 2) * Real.sqrt ρ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    exact band_moved sys hL Hunit hPeriodic hF hB0 a cube (fun l' r' h1 h2 h3 => (hband l' r' h1 h2 h3).1)
      j (Finset.mem_filter.mp hj).2 hlam0 hlam8 hlamg hρ hρl
  have h2 : ‖∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∉ moved j), shMask a sh (Wj j w)‖ ≤
      ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∉ moved j),
        Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit * B * (1 / lam ^ 2) *
          Real.sqrt ρ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    obtain ⟨hb1, hb2⟩ := hband lam ρ hl₀ hρ hρl
    exact band_spectator sys L Hunit hL hPeriodic j (Finset.mem_filter.mp hj).2 sh
      (by linarith) hB0 w hb1 hb2
  refine (add_le_add h1 h2).trans ?_
  -- compare with the total constant
  have hs : 0 ≤ (1 / lam ^ 2) * Real.sqrt ρ := by positivity
  have hterm : ∀ j : Ch eta, 0 ≤ K2a sys L j + K2b sys L j +
      Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit := fun j => by
    obtain ⟨a1, a2, a3⟩ := K2_nonneg sys hL j Hunit; linarith
  have k1 : ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∈ moved j),
      (K2a sys L j * B + K2b sys L j * M) * (1 / lam ^ 2) * Real.sqrt ρ ≤
      ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∈ moved j),
        (K2a sys L j + K2b sys L j + Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit) *
          (B + M) * ((1 / lam ^ 2) * Real.sqrt ρ) := by
    refine Finset.sum_le_sum fun j _ => ?_
    obtain ⟨a1, a2, a3⟩ := K2_nonneg sys hL j Hunit
    have : K2a sys L j * B + K2b sys L j * M ≤ (K2a sys L j + K2b sys L j +
        Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit) * (B + M) := by
      nlinarith
    calc (K2a sys L j * B + K2b sys L j * M) * (1 / lam ^ 2) * Real.sqrt ρ
        = (K2a sys L j * B + K2b sys L j * M) * ((1 / lam ^ 2) * Real.sqrt ρ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hs
  have k2 : ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∉ moved j),
      Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit * B * (1 / lam ^ 2) *
        Real.sqrt ρ ≤
      ∑ j ∈ Finset.univ.filter (fun j : Ch eta => a ∉ moved j),
        (K2a sys L j + K2b sys L j + Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit) *
          (B + M) * ((1 / lam ^ 2) * Real.sqrt ρ) := by
    refine Finset.sum_le_sum fun j _ => ?_
    obtain ⟨a1, a2, a3⟩ := K2_nonneg sys hL j Hunit
    have : Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit * B ≤
        (K2a sys L j + K2b sys L j +
          Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit) * (B + M) := by
      nlinarith
    calc Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit * B * (1 / lam ^ 2) *
          Real.sqrt ρ
        = Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit * B *
            ((1 / lam ^ 2) * Real.sqrt ρ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this hs
  refine (add_le_add k1 k2).trans (le_of_eq ?_)
  rw [Finset.sum_filter_add_sum_filter_not, ← Finset.sum_mul, ← Finset.sum_mul]
  unfold K2tot; ring

end K2

end FSBand
