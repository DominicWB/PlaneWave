import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Logarithmic kinetic bound, part 1: matrix operators and Sylvester absorption

The spectral proof of `thm:kinetic-log` (Appendix H, `app:source`) compares two evolutions on
finite-dimensional low-energy spectral subspaces.  In eigenbases of the two Hamiltonians every
operator of the proof is a finite matrix, and this file provides the matrix layer.

* `mop X`: the operator `c ↦ X c` of a matrix `X : ι → κ → ℂ` between Euclidean coordinate
  spaces, as a continuous linear map, so that its operator norm `‖mop X‖` is available;
* coordinatewise norm comparisons and unimodular diagonal factors;
* **Sylvester absorption** (`norm_sylvester_le`, `norm_sylvester_le'`): if
  `λ_i X_ik - X_ik μ_k = F_ik` and the nonzero entries of `X` have output labels at least `α`
  and input labels at most `β < α` (or the reverse), then `‖X‖ ≤ ‖F‖/(α - β)`.  This is the
  operator-norm bound for the ordered-spectrum Sylvester solution of `lem:kinetic-dyadic` and
  `lem:kinetic-leakage`; it is proved by absorbing `‖X‖` itself, never by dividing individual
  matrix entries by eigenvalue differences;
* the scalar Duhamel kernel `phiT t x = ∫_0^t e^{ixs} ds` and the **time-integration bound**
  `‖(φ_t(λ_i - μ_k) X_ik) c‖ ≤ t ‖X‖ ‖c‖` (`norm_mop_phiT_le`), proved with the mean value
  inequality for a scalar function.

Mathlib only.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators

namespace KineticLog

/-! ## Matrix operators on Euclidean coordinate spaces -/

section Mop

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The linear map `c ↦ X c` of a matrix. -/
noncomputable def mopL (X : ι → κ → ℂ) : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ ι where
  toFun c := WithLp.toLp 2 (fun i => ∑ k, X i k * c k)
  map_add' c d := by
    ext i
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- The matrix operator `c ↦ X c` as a continuous linear map. -/
noncomputable def mop (X : ι → κ → ℂ) : EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap (mopL X)

lemma mop_apply (X : ι → κ → ℂ) (c : EuclideanSpace ℂ κ) (i : ι) :
    mop X c i = ∑ k, X i k * c k := rfl

lemma norm_sq_eucl (x : EuclideanSpace ℂ ι) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq x

/-- Coordinatewise domination: `‖x_i‖ ≤ s ‖y_i‖` for all `i` gives `‖x‖ ≤ s ‖y‖`. -/
lemma norm_le_of_coord {x y : EuclideanSpace ℂ ι} {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ i, ‖x i‖ ≤ s * ‖y i‖) : ‖x‖ ≤ s * ‖y‖ := by
  have h2 : ‖x‖ ^ 2 ≤ (s * ‖y‖) ^ 2 := by
    rw [mul_pow, norm_sq_eucl, norm_sq_eucl, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- Coordinatewise lower bound: `s ‖y_i‖ ≤ ‖x_i‖` for all `i` gives `s ‖y‖ ≤ ‖x‖`. -/
lemma le_norm_of_coord {x y : EuclideanSpace ℂ ι} {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ i, s * ‖y i‖ ≤ ‖x i‖) : s * ‖y‖ ≤ ‖x‖ := by
  have h2 : (s * ‖y‖) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [mul_pow, norm_sq_eucl, norm_sq_eucl, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (h i) 2
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h2

/-- A diagonal factor of modulus one preserves the norm. -/
lemma norm_diag_unit (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) (y : EuclideanSpace ℂ ι) :
    ‖(WithLp.toLp 2 (fun i => z i * y i) : EuclideanSpace ℂ ι)‖ = ‖y‖ := by
  refine le_antisymm ?_ ?_
  · have := norm_le_of_coord (x := WithLp.toLp 2 (fun i => z i * y i)) (y := y) zero_le_one
      (fun i => by
        change ‖z i * y i‖ ≤ 1 * ‖y i‖
        rw [norm_mul, hz i])
    simpa using this
  · have := le_norm_of_coord (x := WithLp.toLp 2 (fun i => z i * y i)) (y := y) zero_le_one
      (fun i => by
        change 1 * ‖y i‖ ≤ ‖z i * y i‖
        rw [norm_mul, hz i])
    simpa using this

lemma norm_mop_apply_le (X : ι → κ → ℂ) (c : EuclideanSpace ℂ κ) :
    ‖mop X c‖ ≤ ‖mop X‖ * ‖c‖ :=
  (mop X).le_opNorm c

/-- An operator-norm bound from a bound on every vector. -/
lemma norm_mop_le {X : ι → κ → ℂ} {B : ℝ} (hB : 0 ≤ B) (h : ∀ c, ‖mop X c‖ ≤ B * ‖c‖) :
    ‖mop X‖ ≤ B :=
  ContinuousLinearMap.opNorm_le_bound _ hB h

/-- Columns where the matrix vanishes do not contribute. -/
lemma mop_restrict_cols (X : ι → κ → ℂ) (c c' : EuclideanSpace ℂ κ)
    (h : ∀ k, c k ≠ c' k → ∀ i, X i k = 0) : mop X c = mop X c' := by
  ext i
  rw [mop_apply, mop_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : c k = c' k
  · rw [hk]
  · rw [h k hk i, zero_mul, zero_mul]

end Mop

/-! ## Sylvester absorption -/

section Sylvester

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Sylvester absorption, output labels above input labels.** Suppose
`λ_i X_ik - X_ik μ_k = F_ik`, every nonzero entry of `X` has `α ≤ λ_i` and `|μ_k| ≤ β`, and
`0 ≤ β < α`.  Then `‖X‖ ≤ ‖F‖ / (α - β)`. -/
theorem norm_sylvester_le (lam : ι → ℝ) (mu : κ → ℝ) (X F : ι → κ → ℂ) {α β : ℝ}
    (hβ : 0 ≤ β) (hαβ : β < α)
    (hrow : ∀ i k, X i k ≠ 0 → α ≤ lam i) (hcol : ∀ i k, X i k ≠ 0 → |mu k| ≤ β)
    (hsyl : ∀ i k, (lam i : ℂ) * X i k - X i k * mu k = F i k) :
    ‖mop X‖ ≤ ‖mop F‖ / (α - β) := by
  classical
  have hα : 0 < α := lt_of_le_of_lt hβ hαβ
  have hab : 0 < α - β := sub_pos.mpr hαβ
  -- the identity `Λ (X c) = F c + X (M c)` with the column-restricted `M c`
  set cM : EuclideanSpace ℂ κ → EuclideanSpace ℂ κ := fun c =>
    WithLp.toLp 2 (fun k => if ∀ i, X i k = 0 then 0 else (mu k : ℂ) * c k) with hcM
  have hcMn : ∀ c, ‖cM c‖ ≤ β * ‖c‖ := by
    intro c
    refine norm_le_of_coord hβ fun k => ?_
    change ‖(if ∀ i, X i k = 0 then 0 else (mu k : ℂ) * c k)‖ ≤ β * ‖c k‖
    split_ifs with h0
    · rw [norm_zero]
      positivity
    · push Not at h0
      obtain ⟨i, hi⟩ := h0
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hcol i k hi) (norm_nonneg _)
  have hid : ∀ c i, (lam i : ℂ) * mop X c i = mop F c i + mop X (cM c) i := by
    intro c i
    rw [mop_apply, mop_apply, mop_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (lam i : ℂ) * (X i k * c k) =
      F i k * c k + X i k * (if ∀ i, X i k = 0 then 0 else (mu k : ℂ) * c k)
    rw [← hsyl i k]
    split_ifs with h0
    · rw [h0 i]
      ring
    · ring
  -- the output labels are at least `α` on the support
  have hlow : ∀ c, α * ‖mop X c‖ ≤ ‖mop F‖ * ‖c‖ + ‖mop X‖ * (β * ‖c‖) := by
    intro c
    have h1 : α * ‖mop X c‖ ≤ ‖mop F c + mop X (cM c)‖ := by
      refine le_norm_of_coord hα.le fun i => ?_
      change α * ‖mop X c i‖ ≤ ‖mop F c i + mop X (cM c) i‖
      rw [← hid c i]
      by_cases h0 : ∀ k, X i k = 0
      · have : mop X c i = 0 := by
          rw [mop_apply]
          exact Finset.sum_eq_zero fun k _ => by rw [h0 k, zero_mul]
        rw [this, norm_zero, mul_zero, mul_zero, norm_zero]
      · push Not at h0
        obtain ⟨k, hk⟩ := h0
        have hl := hrow i k hk
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hα hl)]
        exact mul_le_mul_of_nonneg_right hl (norm_nonneg _)
    calc α * ‖mop X c‖ ≤ ‖mop F c + mop X (cM c)‖ := h1
      _ ≤ ‖mop F c‖ + ‖mop X (cM c)‖ := norm_add_le _ _
      _ ≤ ‖mop F‖ * ‖c‖ + ‖mop X‖ * ‖cM c‖ :=
          add_le_add (norm_mop_apply_le F c) (norm_mop_apply_le X _)
      _ ≤ ‖mop F‖ * ‖c‖ + ‖mop X‖ * (β * ‖c‖) := by
          gcongr
          exact hcMn c
  have hXle : ‖mop X‖ ≤ (‖mop F‖ + β * ‖mop X‖) / α := by
    refine norm_mop_le (by positivity) fun c => ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hα]
    nlinarith [hlow c]
  rw [le_div_iff₀ hab]
  rw [le_div_iff₀ hα] at hXle
  nlinarith

/-- **Sylvester absorption, input labels above output labels.** Suppose
`λ_i X_ik - X_ik μ_k = F_ik`, every nonzero entry of `X` has `|λ_i| ≤ α` and `β ≤ μ_k`, and
`0 ≤ α < β`.  Then `‖X‖ ≤ ‖F‖ / (β - α)`. -/
theorem norm_sylvester_le' (lam : ι → ℝ) (mu : κ → ℝ) (X F : ι → κ → ℂ) {α β : ℝ}
    (hα : 0 ≤ α) (hαβ : α < β)
    (hrow : ∀ i k, X i k ≠ 0 → |lam i| ≤ α) (hcol : ∀ i k, X i k ≠ 0 → β ≤ mu k)
    (hsyl : ∀ i k, (lam i : ℂ) * X i k - X i k * mu k = F i k) :
    ‖mop X‖ ≤ ‖mop F‖ / (β - α) := by
  classical
  have hβ : 0 < β := lt_of_le_of_lt hα hαβ
  have hab : 0 < β - α := sub_pos.mpr hαβ
  -- divide the input by the column labels on the support
  set cD : EuclideanSpace ℂ κ → EuclideanSpace ℂ κ := fun c =>
    WithLp.toLp 2 (fun k => if ∀ i, X i k = 0 then 0 else c k / (mu k : ℂ)) with hcD
  have hcDn : ∀ c, ‖cD c‖ ≤ β⁻¹ * ‖c‖ := by
    intro c
    refine norm_le_of_coord (by positivity) fun k => ?_
    change ‖(if ∀ i, X i k = 0 then 0 else c k / (mu k : ℂ))‖ ≤ β⁻¹ * ‖c k‖
    split_ifs with h0
    · rw [norm_zero]
      positivity
    · push Not at h0
      obtain ⟨i, hi⟩ := h0
      have hm := hcol i k hi
      have hm0 : 0 < mu k := lt_of_lt_of_le hβ hm
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0, div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hβ hm) (norm_nonneg _)
  -- `X c = Λ (X (D c)) - F (D c)`
  have hid : ∀ c i, mop X c i = (lam i : ℂ) * mop X (cD c) i - mop F (cD c) i := by
    intro c i
    rw [mop_apply, mop_apply, mop_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    change X i k * c k = (lam i : ℂ) * (X i k * (if ∀ i, X i k = 0 then 0 else c k / (mu k : ℂ)))
      - F i k * (if ∀ i, X i k = 0 then 0 else c k / (mu k : ℂ))
    rw [← hsyl i k]
    split_ifs with h0
    · rw [h0 i]
      ring
    · push Not at h0
      obtain ⟨i', hi'⟩ := h0
      have hm0 : (mu k : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le hβ (hcol i' k hi')).ne'
      field_simp
      ring
  have hup : ∀ c, ‖mop X c‖ ≤ (α * ‖mop X‖ + ‖mop F‖) * (β⁻¹ * ‖c‖) := by
    intro c
    have h1 : ‖mop X c‖ ≤ α * ‖mop X (cD c)‖ + ‖mop F (cD c)‖ := by
      have e : mop X c = WithLp.toLp 2 (fun i => (lam i : ℂ) * mop X (cD c) i) - mop F (cD c) := by
        ext i
        rw [hid c i]
        rfl
      rw [e]
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      refine norm_le_of_coord hα fun i => ?_
      change ‖(lam i : ℂ) * mop X (cD c) i‖ ≤ α * ‖mop X (cD c) i‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases h0 : ∀ k, X i k = 0
      · have : mop X (cD c) i = 0 := by
          rw [mop_apply]
          exact Finset.sum_eq_zero fun k _ => by rw [h0 k, zero_mul]
        rw [this, norm_zero, mul_zero, mul_zero]
      · push Not at h0
        obtain ⟨k, hk⟩ := h0
        exact mul_le_mul_of_nonneg_right (hrow i k hk) (norm_nonneg _)
    calc ‖mop X c‖ ≤ α * ‖mop X (cD c)‖ + ‖mop F (cD c)‖ := h1
      _ ≤ α * (‖mop X‖ * ‖cD c‖) + ‖mop F‖ * ‖cD c‖ := by
          gcongr
          · exact norm_mop_apply_le X _
          · exact norm_mop_apply_le F _
      _ = (α * ‖mop X‖ + ‖mop F‖) * ‖cD c‖ := by ring
      _ ≤ (α * ‖mop X‖ + ‖mop F‖) * (β⁻¹ * ‖c‖) := by
          gcongr
          exact hcDn c
  have hXle : ‖mop X‖ ≤ (α * ‖mop X‖ + ‖mop F‖) * β⁻¹ := by
    refine norm_mop_le (by positivity) fun c => ?_
    rw [mul_assoc]
    exact hup c
  rw [le_div_iff₀ hab]
  have : ‖mop X‖ * β ≤ α * ‖mop X‖ + ‖mop F‖ := by
    have := mul_le_mul_of_nonneg_right hXle hβ.le
    rwa [mul_assoc, inv_mul_cancel₀ hβ.ne', mul_one] at this
  nlinarith

end Sylvester

/-! ## The Duhamel kernel and time integration -/

section Phi

/-- The Duhamel kernel `φ_t(x) = ∫_0^t e^{ixs} ds`. -/
noncomputable def phiT (t x : ℝ) : ℂ :=
  if x = 0 then (t : ℂ) else (Complex.exp (Complex.I * x * t) - 1) / (Complex.I * x)

lemma phiT_zero_left (x : ℝ) : phiT 0 x = 0 := by
  unfold phiT
  split_ifs <;> simp

lemma phiT_of_ne {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    phiT t x = (Complex.exp (Complex.I * x * t) - 1) / (Complex.I * x) := by
  unfold phiT
  rw [if_neg hx]

lemma hasDerivAt_phiT (x s : ℝ) :
    HasDerivAt (fun t => phiT t x) (Complex.exp (Complex.I * x * s)) s := by
  by_cases hx : x = 0
  · subst hx
    have h : (fun t : ℝ => phiT t 0) = fun t : ℝ => (t : ℂ) := by
      funext t
      unfold phiT
      rw [if_pos rfl]
    rw [h]
    simpa using HasDerivAt.ofReal_comp (hasDerivAt_id s)
  · have h : (fun t : ℝ => phiT t x) =
        fun t : ℝ => (Complex.exp (Complex.I * x * t) - 1) / (Complex.I * x) := by
      funext t
      exact phiT_of_ne hx t
    rw [h]
    have hIx : Complex.I * (x : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx)
    have h1 : HasDerivAt (fun t : ℝ => Complex.I * x * (t : ℂ)) (Complex.I * x * 1) s :=
      (HasDerivAt.ofReal_comp (hasDerivAt_id s)).const_mul (Complex.I * x)
    have h2 := ((h1.cexp).sub_const 1).div_const (Complex.I * x)
    have e : Complex.exp (Complex.I * x * s) * (Complex.I * x * 1) / (Complex.I * x) =
        Complex.exp (Complex.I * x * s) := by
      rw [mul_one, mul_div_assoc, div_self hIx, mul_one]
    rw [e] at h2
    exact h2

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The phase-conjugated pairing: `Σ_i conj(y_i) Σ_k e^{i(λ_i-μ_k)s} X_ik c_k` is an inner
product of unitary rotations of `y` and `c`. -/
lemma sum_phase_eq_inner (lam : ι → ℝ) (mu : κ → ℝ) (X : ι → κ → ℂ) (y : EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ κ) (s : ℝ) :
    ∑ i, conj (y i) * ∑ k, Complex.exp (Complex.I * ((lam i - mu k : ℝ) : ℂ) * s) * X i k * c k =
      ⟪(WithLp.toLp 2 (fun i => Complex.exp (-(Complex.I * lam i * s)) * y i) :
          EuclideanSpace ℂ ι),
        mop X (WithLp.toLp 2 (fun k => Complex.exp (-(Complex.I * mu k * s)) * c k))⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = ⟪Complex.exp (-(Complex.I * lam i * s)) * y i,
    ∑ k, X i k * (Complex.exp (-(Complex.I * mu k * s)) * c k)⟫_ℂ
  rw [RCLike.inner_apply, map_mul, ← Complex.exp_conj]
  have hc : (starRingEnd ℂ) (-(Complex.I * (lam i : ℂ) * (s : ℂ))) = Complex.I * lam i * s := by
    simp [Complex.conj_ofReal]
  rw [hc]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have he : Complex.exp (Complex.I * ((lam i - mu k : ℝ) : ℂ) * s) =
      Complex.exp (Complex.I * lam i * s) * Complex.exp (-(Complex.I * mu k * s)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- **Time integration.** For every matrix `X` and `t ≥ 0`,
`‖(φ_t(λ_i - μ_k) X_ik) c‖ ≤ t ‖X‖ ‖c‖`. -/
theorem norm_mop_phiT_le (lam : ι → ℝ) (mu : κ → ℝ) (X : ι → κ → ℂ) {t : ℝ} (ht : 0 ≤ t)
    (c : EuclideanSpace ℂ κ) :
    ‖mop (fun i k => phiT t (lam i - mu k) * X i k) c‖ ≤ t * ‖mop X‖ * ‖c‖ := by
  set y := mop (fun i k => phiT t (lam i - mu k) * X i k) c with hy
  set g : ℝ → ℂ := fun s => ∑ i, conj (y i) * ∑ k, phiT s (lam i - mu k) * X i k * c k with hg
  have hderiv : ∀ s : ℝ, HasDerivAt g (∑ i, conj (y i) *
      ∑ k, Complex.exp (Complex.I * ((lam i - mu k : ℝ) : ℂ) * (s : ℂ)) * X i k * c k) s := by
    intro s
    refine HasDerivAt.fun_sum fun i _ => ?_
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun k _ => ?_)
    exact ((hasDerivAt_phiT (lam i - mu k) s).mul_const (X i k)).mul_const (c k)
  have hbound : ∀ s : ℝ, ‖∑ i, conj (y i) *
      ∑ k, Complex.exp (Complex.I * ((lam i - mu k : ℝ) : ℂ) * (s : ℂ)) * X i k * c k‖ ≤
      ‖y‖ * (‖mop X‖ * ‖c‖) := by
    intro s
    rw [sum_phase_eq_inner]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_diag_unit _ (fun i => by
      rw [Complex.norm_exp]
      simp) y]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_mop_apply_le X _).trans ?_
    rw [norm_diag_unit _ (fun k => by
      rw [Complex.norm_exp]
      simp) c]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := g) (a := 0) (b := t) (C := ‖y‖ * (‖mop X‖ * ‖c‖))
    (fun s _ => (hderiv s).hasDerivWithinAt) (fun s _ => hbound s) t ⟨ht, le_rfl⟩
  have hg0 : g 0 = 0 := by
    simp only [hg, phiT_zero_left, zero_mul, Finset.sum_const_zero, mul_zero]
  have hgt : g t = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    have e : ∀ i, ∑ k, phiT t (lam i - mu k) * X i k * c k = y i := by
      intro i
      rw [hy, mop_apply]
    simp only [hg, e]
    rw [norm_sq_eucl]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.conj_mul']
  rw [hg0, sub_zero, hgt, sub_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)] at hmvt
  by_cases hy0 : ‖y‖ = 0
  · rw [hy0]
    have : 0 ≤ ‖mop X‖ := norm_nonneg _
    positivity
  · have hpos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
    have h2 : ‖y‖ * ‖y‖ ≤ ‖y‖ * (t * ‖mop X‖ * ‖c‖) := by
      nlinarith
    exact le_of_mul_le_mul_left h2 hpos

end Phi

end KineticLog
