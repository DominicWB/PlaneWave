import PlaneWave.Source.BulkLatticeCounts

/-!
# Flux/source build, block 5: kernel operators on a finite configuration set

Mathlib-only.  For a finite type `X`, the kernel operator `kop κ` on `EuclideanSpace ℂ X`,
`(kop κ u)_q = Σ_p u_p κ(q, p)`, and the facts the retained hierarchy uses:

* `norm_kop_le` (Schur's test) and `norm_kop_sq_le`;
* `kop_comm_dg`: `[diag d, kop κ] = kop ((d q - d p) κ)`; `divK` (entrywise division by the
  mismatch `d q - d p`) solves the homological equation `[diag d, kop (divK d κ)] = kop κ` when
  `κ` vanishes on the diagonal `d q = d p`;
* `inner_kop`, `kop_skew`, `kop_symm`: adjoints, skew-adjoint and Hermitian kernels;
* `norm_divK_HL_le`, `norm_divK_LH_le` (the Laplace bound of `lem:mixed`, as a Sylvester-type
  estimate): if `κ` joins inputs of energy `≤ b` to outputs of energy `≥ a > b ≥ 0` (or the
  reverse), then `‖kop (divK d κ)‖ ≤ ‖kop κ‖ / (a - b)`;
* `norm_kop_fibre_sq_le` (Young's inequality on pair fibres): if `|κ(q, p)| ≤ k₀(π q - π p)` on
  fibres of a label `lab` on which `π` is injective and `0` across fibres, then
  `‖kop κ u‖² ≤ (Σ_θ k₀(θ)²) Z₂ Σ_p (1 + |π p|²)² |u_p|²`, `Z₂ = Zs 2`.
-/

set_option autoImplicit false

open Finset
open scoped InnerProductSpace ComplexConjugate

namespace FSKernel

open FSLattice FSChannel

variable {X : Type*} [Fintype X]

/-! ## Kernel and diagonal operators -/

/-- The kernel operator `(kop κ u)_q = Σ_p u_p κ(q, p)`. -/
noncomputable def kop (κ : X → X → ℂ) : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X where
  toFun u := WithLp.toLp 2 (fun q => ∑ p, u.ofLp p * κ q p)
  map_add' u v := by
    ext q
    simp [add_mul, sum_add_distrib]
  map_smul' c u := by
    ext q
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    ring

@[simp] lemma kop_apply (κ : X → X → ℂ) (u : EuclideanSpace ℂ X) (q : X) :
    (kop κ u).ofLp q = ∑ p, u.ofLp p * κ q p := rfl

lemma kop_add (κ κ' : X → X → ℂ) : kop (κ + κ') = kop κ + kop κ' := by
  ext u q
  simp [mul_add, sum_add_distrib]

lemma kop_sub (κ κ' : X → X → ℂ) : kop (κ - κ') = kop κ - kop κ' := by
  ext u q
  simp [mul_sub, sum_sub_distrib]

lemma kop_smul (c : ℂ) (κ : X → X → ℂ) : kop (c • κ) = c • kop κ := by
  ext u q
  simp only [kop_apply, Pi.smul_apply, smul_eq_mul, LinearMap.smul_apply, PiLp.smul_apply, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  ring

/-- The diagonal operator `(dg d u)_q = d q u_q`. -/
noncomputable def dg (d : X → ℂ) : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X where
  toFun u := WithLp.toLp 2 (fun q => d q * u.ofLp q)
  map_add' u v := by
    ext q
    simp [mul_add]
  map_smul' c u := by
    ext q
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype X] in
@[simp] lemma dg_apply (d : X → ℂ) (u : EuclideanSpace ℂ X) (q : X) :
    (dg d u).ofLp q = d q * u.ofLp q := rfl

lemma norm_sq_eq (u : EuclideanSpace ℂ X) : ‖u‖ ^ 2 = ∑ q, ‖u.ofLp q‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (sum_nonneg fun q _ => sq_nonneg _)]

/-- A diagonal operator with `|d| ≤ B` has norm at most `B`. -/
lemma norm_dg_le (d : X → ℂ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ q, ‖d q‖ ≤ B)
    (u : EuclideanSpace ℂ X) : ‖dg d u‖ ≤ B * ‖u‖ := by
  have h : ‖dg d u‖ ^ 2 ≤ (B * ‖u‖) ^ 2 := by
    rw [norm_sq_eq, mul_pow, norm_sq_eq, mul_sum]
    refine sum_le_sum fun q _ => ?_
    rw [dg_apply, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB q) 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-! ## Schur's test -/

/-- **Schur's test**: row sums `≤ R`, column sums `≤ C` give `‖kop κ u‖ ≤ √(RC) ‖u‖`. -/
theorem norm_kop_le (κ : X → X → ℂ) {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ q, ∑ p, ‖κ q p‖ ≤ R) (hcol : ∀ p, ∑ q, ‖κ q p‖ ≤ C) (u : EuclideanSpace ℂ X) :
    ‖kop κ u‖ ≤ Real.sqrt (R * C) * ‖u‖ := by
  have h := schur_sum_sq κ u.ofLp hR hC hrow hcol
  have h2 : ‖kop κ u‖ ^ 2 ≤ (Real.sqrt (R * C) * ‖u‖) ^ 2 := by
    rw [norm_sq_eq, mul_pow, Real.sq_sqrt (mul_nonneg hR hC), norm_sq_eq]
    simpa using h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- Schur's test with equal row and column bound. -/
theorem norm_kop_le' (κ : X → X → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ q, ∑ p, ‖κ q p‖ ≤ R) (hcol : ∀ p, ∑ q, ‖κ q p‖ ≤ R) (u : EuclideanSpace ℂ X) :
    ‖kop κ u‖ ≤ R * ‖u‖ := by
  have h := norm_kop_le κ hR hR hrow hcol u
  rwa [Real.sqrt_mul_self hR] at h

/-! ## Commutators with diagonal operators and the homological equation -/

lemma dg_kop (d : X → ℂ) (κ : X → X → ℂ) : dg d ∘ₗ kop κ = kop fun q p => d q * κ q p := by
  ext u q
  simp [mul_sum]
  refine sum_congr rfl fun p _ => ?_
  ring

lemma kop_dg (d : X → ℂ) (κ : X → X → ℂ) : kop κ ∘ₗ dg d = kop fun q p => κ q p * d p := by
  ext u q
  simp only [LinearMap.coe_comp, Function.comp_apply, kop_apply, dg_apply]
  refine sum_congr rfl fun p _ => ?_
  ring

/-- `[diag d, kop κ] = kop ((d q - d p) κ(q, p))`. -/
lemma kop_comm_dg (d : X → ℂ) (κ : X → X → ℂ) :
    dg d ∘ₗ kop κ - kop κ ∘ₗ dg d = kop fun q p => (d q - d p) * κ q p := by
  rw [dg_kop, kop_dg, ← kop_sub]
  congr 1
  funext q p
  simp only [Pi.sub_apply]
  ring

open Classical in
/-- Entrywise division by the mismatch: `divK d κ (q, p) = κ(q, p) / (d q - d p)` (`0` on the
diagonal `d q = d p`). -/
noncomputable def divK (d : X → ℝ) (κ : X → X → ℂ) (q p : X) : ℂ :=
  if d q = d p then 0 else κ q p / ((d q - d p : ℝ) : ℂ)

/-- **The homological equation**: if `κ` vanishes where `d q = d p`, then
`[diag d, kop (divK d κ)] = kop κ`. -/
theorem comm_divK (d : X → ℝ) (κ : X → X → ℂ) (hκ : ∀ q p, d q = d p → κ q p = 0) :
    dg (fun q => (d q : ℂ)) ∘ₗ kop (divK d κ) - kop (divK d κ) ∘ₗ dg (fun q => (d q : ℂ)) =
      kop κ := by
  rw [kop_comm_dg]
  congr 1
  funext q p
  unfold divK
  split_ifs with h
  · rw [mul_zero, hκ q p h]
  · have hne : ((d q - d p : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact sub_ne_zero.mpr h
    rw [← Complex.ofReal_sub] at *
    field_simp

omit [Fintype X] in
lemma divK_mul_right (d : X → ℝ) (κ : X → X → ℂ) (w : X → ℂ) (q p : X) :
    divK d (fun q p => κ q p * w p) q p = divK d κ q p * w p := by
  unfold divK
  split_ifs
  · rw [zero_mul]
  · ring

/-! ## Adjoints -/

/-- `⟪kop κ u, v⟫ = ⟪u, kop κ* v⟫` with `κ*(q, p) = conj κ(p, q)`. -/
theorem inner_kop (κ : X → X → ℂ) (u v : EuclideanSpace ℂ X) :
    ⟪kop κ u, v⟫_ℂ = ⟪u, kop (fun q p => conj (κ p q)) v⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, kop_apply, dotProduct, star_sum, star_mul',
    Pi.star_apply, RCLike.star_def]
  simp_rw [mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
  ring

/-- A skew-Hermitian kernel gives a skew-adjoint operator. -/
theorem kop_skew (κ : X → X → ℂ) (hκ : ∀ q p, κ p q = -conj (κ q p)) (u v : EuclideanSpace ℂ X) :
    ⟪kop κ u, v⟫_ℂ = -⟪u, kop κ v⟫_ℂ := by
  rw [inner_kop, ← inner_neg_right]
  congr 1
  ext q
  simp only [kop_apply, PiLp.neg_apply, ← sum_neg_distrib]
  refine sum_congr rfl fun p _ => ?_
  rw [hκ q p, map_neg, Complex.conj_conj]
  ring

/-- A Hermitian kernel gives a symmetric operator. -/
theorem kop_symm (κ : X → X → ℂ) (hκ : ∀ q p, κ p q = conj (κ q p)) : (kop κ).IsSymmetric := by
  intro u v
  have h : (fun q p => conj (κ p q)) = κ := by
    funext q p
    rw [hκ q p, Complex.conj_conj]
  rw [inner_kop, h]

/-! ## The Laplace (Sylvester) bound for energy-gapped blocks -/

open Classical in
/-- Restriction to a set of configurations. -/
noncomputable def res (P : X → Prop) : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X :=
  dg fun q => if P q then 1 else 0

omit [Fintype X] in
lemma res_apply (P : X → Prop) [DecidablePred P] (u : EuclideanSpace ℂ X) (q : X) :
    (res P u).ofLp q = if P q then u.ofLp q else 0 := by
  classical
  unfold res
  rw [dg_apply]
  split_ifs <;> simp_all

lemma norm_res_le (P : X → Prop) (u : EuclideanSpace ℂ X) : ‖res P u‖ ≤ ‖u‖ := by
  classical
  have := norm_dg_le (fun q => if P q then (1 : ℂ) else 0) (B := 1) zero_le_one (fun q => by
    split_ifs <;> simp) u
  rwa [one_mul] at this

/-- Columns supported in `P`: `kop κ u = kop κ (res P u)`. -/
lemma kop_res_of_cols (κ : X → X → ℂ) (P : X → Prop) (hκ : ∀ q p, κ q p ≠ 0 → P p)
    (u : EuclideanSpace ℂ X) : kop κ u = kop κ (res P u) := by
  classical
  ext q
  simp only [kop_apply, res_apply]
  refine sum_congr rfl fun p _ => ?_
  by_cases hp : P p
  · rw [if_pos hp]
  · rw [if_neg hp, zero_mul]
    have : κ q p = 0 := by by_contra h; exact hp (hκ q p h)
    rw [this, mul_zero]

/-- **The Laplace bound, cold-to-hot orientation.** Let `0 ≤ d`, `0 ≤ b < a`, and let `κ` join
inputs with `d ≤ b` to outputs with `d ≥ a`. If `‖kop κ u‖ ≤ B ‖u‖`, then
`‖kop (divK d κ) u‖ ≤ B/(a - b) ‖u‖`. -/
theorem norm_divK_HL_le (d : X → ℝ) (hd : ∀ q, 0 ≤ d q) {a b B : ℝ} (hb : 0 ≤ b) (hab : b < a)
    (hB0 : 0 ≤ B) (κ : X → X → ℂ) (hκ : ∀ q p, κ q p ≠ 0 → a ≤ d q ∧ d p ≤ b)
    (hB : ∀ u, ‖kop κ u‖ ≤ B * ‖u‖) (u : EuclideanSpace ℂ X) :
    ‖kop (divK d κ) u‖ ≤ B / (a - b) * ‖u‖ := by
  classical
  have ha : 0 < a := by linarith
  set S := kop (divK d κ)
  set Sc := LinearMap.toContinuousLinearMap S
  have hSc : ∀ x, Sc x = S x := fun x => rfl
  have hdiv0 : ∀ q p, divK d κ q p ≠ 0 → a ≤ d q ∧ d p ≤ b := by
    intro q p h
    unfold divK at h
    split_ifs at h with h1
    · exact absurd rfl h
    · have : κ q p ≠ 0 := by intro h0; rw [h0, zero_div] at h; exact h rfl
      exact hκ q p this
  have hdiag : ∀ q p, d q = d p → κ q p = 0 := by
    intro q p hqp
    by_contra h
    have := hκ q p h
    linarith [this.1, this.2]
  -- the homological identity `d (S u) = κ u + S (d u)`
  have hcomm := comm_divK d κ hdiag
  have hid : ∀ x, dg (fun q => (d q : ℂ)) (S x) = kop κ x + S (dg (fun q => (d q : ℂ)) x) := by
    intro x
    have := congrArg (fun T => T x) hcomm
    simp only [LinearMap.sub_apply, LinearMap.comp_apply] at this
    rw [← this]; abel
  -- `‖d (S x)‖ ≥ a ‖S x‖` (outputs in `d ≥ a`)
  have hlow : ∀ x, a * ‖S x‖ ≤ ‖dg (fun q => (d q : ℂ)) (S x)‖ := by
    intro x
    have h2 : (a * ‖S x‖) ^ 2 ≤ ‖dg (fun q => (d q : ℂ)) (S x)‖ ^ 2 := by
      rw [mul_pow, norm_sq_eq, norm_sq_eq, mul_sum]
      refine sum_le_sum fun q _ => ?_
      rw [dg_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      by_cases hq : (S x).ofLp q = 0
      · rw [hq, norm_zero]; simp
      · have : ∃ p, divK d κ q p ≠ 0 := by
          by_contra hno
          push Not at hno
          apply hq
          show (kop (divK d κ) x).ofLp q = 0
          rw [kop_apply]
          exact sum_eq_zero fun p _ => by rw [hno p, mul_zero]
        obtain ⟨p, hp⟩ := this
        have hq' := (hdiv0 q p hp).1
        have : a ^ 2 ≤ d q ^ 2 := pow_le_pow_left₀ ha.le hq' 2
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h2
  -- `‖S (d x)‖ ≤ b ‖S‖ ‖x‖` (inputs in `d ≤ b`)
  have hcols : ∀ q p, divK d κ q p ≠ 0 → d p ≤ b := fun q p h => (hdiv0 q p h).2
  have hupp : ∀ x, ‖S (dg (fun q => (d q : ℂ)) x)‖ ≤ ‖Sc‖ * (b * ‖x‖) := by
    intro x
    rw [kop_res_of_cols (divK d κ) (fun p => d p ≤ b) hcols]
    refine (Sc.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have : res (fun p => d p ≤ b) (dg (fun q => (d q : ℂ)) x) =
        dg (fun q => if d q ≤ b then (d q : ℂ) else 0) x := by
      ext q
      rw [res_apply, dg_apply, dg_apply]
      split_ifs <;> simp
    rw [this]
    refine norm_dg_le _ hb (fun q => ?_) x
    split_ifs with h
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd q)]; exact h
    · rw [norm_zero]; exact hb
  have hop : ‖Sc‖ ≤ B / (a - b) := by
    have hbound : ∀ x, ‖Sc x‖ ≤ (B + b * ‖Sc‖) / a * ‖x‖ := by
      intro x
      rw [hSc, div_mul_eq_mul_div, le_div_iff₀ ha]
      have h1 := hlow x
      rw [hid x] at h1
      have h2 := (norm_add_le _ _).trans (add_le_add (hB x) (hupp x))
      nlinarith [norm_nonneg x, norm_nonneg (S x)]
    have h3 := Sc.opNorm_le_bound (by positivity) hbound
    rw [le_div_iff₀ (by linarith)]
    rw [le_div_iff₀ ha] at h3
    linarith
  calc ‖kop (divK d κ) u‖ = ‖Sc u‖ := rfl
    _ ≤ ‖Sc‖ * ‖u‖ := Sc.le_opNorm u
    _ ≤ B / (a - b) * ‖u‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)

/-- **The Laplace bound, hot-to-cold orientation**: `κ` joins inputs with `d ≥ a` to outputs with
`d ≤ b`. -/
theorem norm_divK_LH_le (d : X → ℝ) (hd : ∀ q, 0 ≤ d q) {a b B : ℝ} (hb : 0 ≤ b) (hab : b < a)
    (hB0 : 0 ≤ B) (κ : X → X → ℂ) (hκ : ∀ q p, κ q p ≠ 0 → d q ≤ b ∧ a ≤ d p)
    (hB : ∀ u, ‖kop κ u‖ ≤ B * ‖u‖) (u : EuclideanSpace ℂ X) :
    ‖kop (divK d κ) u‖ ≤ B / (a - b) * ‖u‖ := by
  classical
  have ha : 0 < a := by linarith
  set S := kop (divK d κ)
  set Sc := LinearMap.toContinuousLinearMap S
  have hSc : ∀ x, Sc x = S x := fun x => rfl
  have hdiv0 : ∀ q p, divK d κ q p ≠ 0 → d q ≤ b ∧ a ≤ d p := by
    intro q p h
    unfold divK at h
    split_ifs at h with h1
    · exact absurd rfl h
    · have : κ q p ≠ 0 := by intro h0; rw [h0, zero_div] at h; exact h rfl
      exact hκ q p this
  have hdiag : ∀ q p, d q = d p → κ q p = 0 := by
    intro q p hqp
    by_contra h
    have := hκ q p h
    linarith [this.1, this.2]
  have hcomm := comm_divK d κ hdiag
  have hid : ∀ x, S (dg (fun q => (d q : ℂ)) x) = dg (fun q => (d q : ℂ)) (S x) - kop κ x := by
    intro x
    have := congrArg (fun T => T x) hcomm
    simp only [LinearMap.sub_apply, LinearMap.comp_apply] at this
    rw [← this]; abel
  -- outputs of `S` lie in `d ≤ b`
  have hrows : ∀ x, ‖dg (fun q => (d q : ℂ)) (S x)‖ ≤ b * ‖S x‖ := by
    intro x
    have e : dg (fun q => (d q : ℂ)) (S x) = dg (fun q => if d q ≤ b then (d q : ℂ) else 0) (S x) := by
      ext q
      rw [dg_apply, dg_apply]
      split_ifs with h
      · rfl
      · have : (S x).ofLp q = 0 := by
          show (kop (divK d κ) x).ofLp q = 0
          rw [kop_apply]
          refine sum_eq_zero fun p _ => ?_
          by_cases hp : divK d κ q p = 0
          · rw [hp, mul_zero]
          · exact absurd (hdiv0 q p hp).1 h
        rw [this, mul_zero, mul_zero]
    rw [e]
    refine norm_dg_le _ hb (fun q => ?_) _
    split_ifs with h
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd q)]; exact h
    · rw [norm_zero]; exact hb
  -- the rescaled input `y = d⁻¹ 1_{d ≥ a} x`
  have hcols : ∀ q p, divK d κ q p ≠ 0 → a ≤ d p := fun q p h => (hdiv0 q p h).2
  have hbound : ∀ x, ‖Sc x‖ ≤ (B + b * ‖Sc‖) / a * ‖x‖ := by
    intro x
    set y := dg (fun p => if a ≤ d p then ((1 / d p : ℝ) : ℂ) else 0) x
    have hy : dg (fun q => (d q : ℂ)) y = res (fun p => a ≤ d p) x := by
      ext p
      rw [dg_apply, dg_apply, res_apply]
      split_ifs with h
      · have : d p ≠ 0 := by linarith
        rw [← mul_assoc, ← Complex.ofReal_mul, mul_one_div_cancel this, Complex.ofReal_one, one_mul]
      · simp
    have hy_norm : ‖y‖ ≤ 1 / a * ‖x‖ := by
      refine norm_dg_le _ (by positivity) (fun p => ?_) x
      split_ifs with h
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by have := hd p; positivity)]
        exact one_div_le_one_div_of_le ha h
      · rw [norm_zero]; positivity
    have hSx : S x = S (dg (fun q => (d q : ℂ)) y) := by
      rw [hy]; exact kop_res_of_cols (divK d κ) (fun p => a ≤ d p) hcols x
    rw [hSc, hSx, hid y]
    calc ‖dg (fun q => (d q : ℂ)) (S y) - kop κ y‖
        ≤ ‖dg (fun q => (d q : ℂ)) (S y)‖ + ‖kop κ y‖ := norm_sub_le _ _
      _ ≤ b * ‖Sc y‖ + B * ‖y‖ := add_le_add (hrows y) (hB y)
      _ ≤ b * (‖Sc‖ * ‖y‖) + B * ‖y‖ := by gcongr; exact Sc.le_opNorm y
      _ = (B + b * ‖Sc‖) * ‖y‖ := by ring
      _ ≤ (B + b * ‖Sc‖) * (1 / a * ‖x‖) := by gcongr
      _ = (B + b * ‖Sc‖) / a * ‖x‖ := by ring
  have hop : ‖Sc‖ ≤ B / (a - b) := by
    have h3 := Sc.opNorm_le_bound (by positivity) hbound
    rw [le_div_iff₀ (by linarith)]
    rw [le_div_iff₀ ha] at h3
    linarith
  calc ‖kop (divK d κ) u‖ = ‖Sc u‖ := rfl
    _ ≤ ‖Sc‖ * ‖u‖ := Sc.le_opNorm u
    _ ≤ B / (a - b) * ‖u‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)

/-! ## Young's inequality on fibres -/

/-- AM–GM with a ratio: `2xy ≤ x² t + y²/t` for `t > 0`. -/
lemma two_mul_le_ratio {x y t : ℝ} (ht : 0 < t) : 2 * (x * y) ≤ x ^ 2 * t + y ^ 2 / t := by
  have h : 0 ≤ (x * t - y) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have e : (x * t - y) ^ 2 / t = x ^ 2 * t - 2 * (x * y) + y ^ 2 / t := by
    field_simp; ring
  linarith

/-- The fibre weight sum `Σ_{p' ~ p} (1 + |π p'|²)⁻² ≤ Z₂`. -/
lemma sum_fibre_weight_le {β : Type*} [DecidableEq β] (lab : X → β) (π : X → L3)
    (hπ : ∀ x y, lab x = lab y → π x = π y → x = y) (p : X) :
    ∑ p', (if lab p = lab p' then 1 / (1 + lsq (π p')) ^ 2 else 0) ≤ Zs 2 := by
  rw [← sum_filter]
  have hinj : Set.InjOn π (univ.filter fun p' => lab p = lab p') := by
    intro x hx y hy h
    exact hπ x y ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2) h
  have h := sum_weight_image_le (univ.filter fun p' => lab p = lab p') π hinj
    (by norm_num : (3 : ℝ) / 2 < 2)
  refine le_trans (le_of_eq (sum_congr rfl fun p' _ => ?_)) h
  have hpos : 0 < 1 + lsq (π p') := by have := lsq_nonneg (π p'); linarith
  rw [Real.rpow_neg hpos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    one_div]

/-- **Young's inequality on fibres.** If `|κ(q, p)| ≤ k₀(π q - π p)` when `lab q = lab p` and
`κ(q, p) = 0` otherwise, with `π` injective on each fibre and `Σ_{θ ∈ S} k₀(θ)² ≤ K₂` for every
finite `S`, then `‖kop κ u‖² ≤ K₂ Z₂ Σ_p (1 + |π p|²)² |u_p|²`. -/
theorem norm_kop_fibre_sq_le {β : Type*} [DecidableEq β] (lab : X → β) (π : X → L3)
    (hπ : ∀ x y, lab x = lab y → π x = π y → x = y)
    (κ : X → X → ℂ) (k₀ : L3 → ℝ) (hk₀ : ∀ θ, 0 ≤ k₀ θ) {K₂ : ℝ}
    (hK₂ : ∀ S : Finset L3, ∑ θ ∈ S, k₀ θ ^ 2 ≤ K₂)
    (hκ : ∀ q p, ‖κ q p‖ ≤ if lab q = lab p then k₀ (π q - π p) else 0)
    (u : EuclideanSpace ℂ X) :
    ‖kop κ u‖ ^ 2 ≤ K₂ * Zs 2 * ∑ p, (1 + lsq (π p)) ^ 2 * ‖u.ofLp p‖ ^ 2 := by
  classical
  set a : X → ℝ := fun p => ‖u.ofLp p‖
  set kb : X → X → ℝ := fun q p => if lab q = lab p then k₀ (π q - π p) else 0
  have hkb0 : ∀ q p, 0 ≤ kb q p := fun q p => by
    simp only [kb]; split_ifs
    · exact hk₀ _
    · exact le_rfl
  have ha0 : ∀ p, 0 ≤ a p := fun p => norm_nonneg _
  set F : X → ℝ := fun q => ∑ p, if lab q = lab p then a p else 0
  have hK0 : 0 ≤ K₂ := by
    have := hK₂ ∅; rwa [sum_empty] at this
  -- step 1–2: pointwise Cauchy–Schwarz along the fibre
  have hq : ∀ q, ‖(kop κ u).ofLp q‖ ^ 2 ≤ (∑ p, kb q p ^ 2 * a p) * F q := by
    intro q
    have h1 : ‖(kop κ u).ofLp q‖ ≤ ∑ p, a p * kb q p := by
      rw [kop_apply]
      refine (norm_sum_le _ _).trans (sum_le_sum fun p _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hκ q p) (ha0 p)
    have h2 : (∑ p, a p * kb q p) ^ 2 ≤ (∑ p, kb q p ^ 2 * a p) *
        ∑ p, (if lab q = lab p then a p else 0) := by
      apply sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro p _; exact mul_nonneg (sq_nonneg _) (ha0 p)
      · intro p _; split_ifs
        · exact ha0 p
        · exact le_rfl
      · intro p _
        simp only [kb]
        split_ifs
        · nlinarith [ha0 p]
        · simp
    calc ‖(kop κ u).ofLp q‖ ^ 2 ≤ (∑ p, a p * kb q p) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  -- step 3: sum over outputs
  have hF : ∀ q p, lab q = lab p → F q = F p := by
    intro q p h
    simp only [F, h]
  have hcol : ∀ p, ∑ q, kb q p ^ 2 * F q = F p * ∑ q, kb q p ^ 2 := by
    intro p
    rw [mul_sum]
    refine sum_congr rfl fun q _ => ?_
    simp only [kb]
    split_ifs with h
    · rw [hF q p h]; ring
    · ring
  have hcolsum : ∀ p, ∑ q, kb q p ^ 2 ≤ K₂ := by
    intro p
    have e : ∑ q, kb q p ^ 2 = ∑ q ∈ univ.filter (fun q => lab q = lab p), k₀ (π q - π p) ^ 2 := by
      rw [sum_filter]
      refine sum_congr rfl fun q _ => ?_
      simp only [kb]; split_ifs <;> simp
    rw [e]
    have hinj : Set.InjOn (fun q => π q - π p) (univ.filter (fun q => lab q = lab p)) := by
      intro x hx y hy h
      have h' : π x = π y := sub_left_injective h
      exact hπ x y ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) h'
    rw [← sum_image (f := fun θ => k₀ θ ^ 2) hinj]
    exact hK₂ _
  have hFnn : ∀ p, 0 ≤ F p := fun p => sum_nonneg fun p' _ => by
    split_ifs
    · exact ha0 p'
    · exact le_rfl
  have hstep3 : ∑ q, (∑ p, kb q p ^ 2 * a p) * F q ≤ K₂ * ∑ p, a p * F p := by
    have e : ∑ q, (∑ p, kb q p ^ 2 * a p) * F q = ∑ p, a p * ∑ q, kb q p ^ 2 * F q := by
      simp_rw [sum_mul, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
      ring
    rw [e, mul_sum]
    refine sum_le_sum fun p _ => ?_
    rw [hcol p]
    have := mul_le_mul_of_nonneg_left (hcolsum p) (mul_nonneg (ha0 p) (hFnn p))
    nlinarith [ha0 p, hFnn p]
  -- step 4: the fibre `ℓ¹` norms by the weights
  set W : X → ℝ := fun p => (1 + lsq (π p)) ^ 2
  have hW : ∀ p, 0 < W p := fun p => by have := lsq_nonneg (π p); positivity
  have hstep4 : ∑ p, a p * F p ≤ Zs 2 * ∑ p, W p * a p ^ 2 := by
    have e : ∑ p, a p * F p = ∑ p, ∑ p', if lab p = lab p' then a p * a p' else 0 := by
      refine sum_congr rfl fun p _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun p' _ => ?_
      split_ifs <;> ring
    rw [e]
    have hpt : ∀ p p', (if lab p = lab p' then a p * a p' else 0) ≤
        (1 / 2) * (if lab p = lab p' then a p ^ 2 * W p * (1 / W p') else 0) +
          (1 / 2) * (if lab p' = lab p then a p' ^ 2 * W p' * (1 / W p) else 0) := by
      intro p p'
      by_cases h : lab p = lab p'
      · simp only [if_pos h, if_pos h.symm]
        have := two_mul_le_ratio (x := a p) (y := a p') (div_pos (hW p) (hW p'))
        have e2 : a p' ^ 2 / (W p / W p') = a p' ^ 2 * W p' * (1 / W p) := by
          field_simp
        have e1 : a p ^ 2 * (W p / W p') = a p ^ 2 * W p * (1 / W p') := by ring
        rw [e1, e2] at this
        linarith
      · simp only [if_neg h, if_neg (Ne.symm h)]; simp
    have hsum := sum_le_sum fun p (_ : p ∈ univ) => sum_le_sum fun p' (_ : p' ∈ univ) => hpt p p'
    simp only [sum_add_distrib, ← mul_sum] at hsum
    rw [sum_comm (f := fun p p' => if lab p' = lab p then a p' ^ 2 * W p' * (1 / W p) else 0)]
      at hsum
    have hhalf : ∀ p, ∑ p', (if lab p = lab p' then a p ^ 2 * W p * (1 / W p') else 0) ≤
        W p * a p ^ 2 * Zs 2 := by
      intro p
      have e3 : ∑ p', (if lab p = lab p' then a p ^ 2 * W p * (1 / W p') else 0) =
          a p ^ 2 * W p * ∑ p', (if lab p = lab p' then 1 / (1 + lsq (π p')) ^ 2 else 0) := by
        rw [mul_sum]
        refine sum_congr rfl fun p' _ => ?_
        split_ifs <;> simp [W]
      rw [e3]
      have := sum_fibre_weight_le lab π hπ p
      have h0 : 0 ≤ a p ^ 2 * W p := mul_nonneg (sq_nonneg _) (hW p).le
      nlinarith
    have hs1 := sum_le_sum fun p (_ : p ∈ univ) => hhalf p
    rw [← sum_mul] at hs1
    linarith
  -- assemble
  rw [norm_sq_eq]
  calc ∑ q, ‖(kop κ u).ofLp q‖ ^ 2 ≤ ∑ q, (∑ p, kb q p ^ 2 * a p) * F q := sum_le_sum fun q _ => hq q
    _ ≤ K₂ * ∑ p, a p * F p := hstep3
    _ ≤ K₂ * (Zs 2 * ∑ p, W p * a p ^ 2) := mul_le_mul_of_nonneg_left hstep4 hK0
    _ = K₂ * Zs 2 * ∑ p, (1 + lsq (π p)) ^ 2 * ‖u.ofLp p‖ ^ 2 := by ring

end FSKernel
