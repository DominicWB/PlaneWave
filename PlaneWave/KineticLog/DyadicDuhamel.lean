import PlaneWave.KineticLog.Sylvester
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Logarithmic kinetic bound, part 2: the dyadic spectral Duhamel estimate

**`lem:kinetic-dyadic`** (`eq:kinetic-dyadic`) in eigenbasis coordinates.  Let `λ : ι → ℝ`
(output labels) and `μ : κ → ℝ` (input labels) take values in `[1, M]`, `M ≥ 2`, and let
`A : ι → κ → ℂ` be a matrix whose doubly inverse-weighted form `W_ik = A_ik/(λ_i μ_k)` has
operator norm at most `δ`.  In the eigenbases of `B₁, B₂` the Duhamel operator
`∫_0^t e^{-iB₁(t-s)} F e^{-iB₂ s} B₂^{-2} ds` has entries `e^{-iλ_i t} φ_t(λ_i - μ_k) A_ik/μ_k²`
with `φ_t(x) = ∫_0^t e^{ixs} ds`; up to the unimodular output phase, **`dyadic_duhamel`** gives

  `‖(φ_t(λ_i - μ_k) A_ik/μ_k²) c‖ ≤ 48 δ (t + log(2 + M)) ‖c‖`  for every `t ≥ 0`.

The proof is the manuscript's:
* dyadic bands `band x = ⌊log₂ x⌋`, with `band M + 1 ≤ 3 log(2 + M)` bands (`band_add_one_le`);
* the **row-band bound** `‖P_j L c‖ ≤ 2^{j+1} δ ‖μ⁻¹ c‖` for `L = A μ⁻²` (`rowband_le`);
* **neighbouring bands** (`|j - k| ≤ 1`): the near part has norm at most `7 δ`, because output
  bands are orthogonal and each input band meets at most three output bands
  (`norm_lnear_le`); time integration (`norm_mop_phiT_le`) then costs `7 t δ`, with no factor
  of the number of bands;
* **separated bands** (`|j - k| ≥ 2`): the ordered-spectrum Sylvester solution `X_jk` has
  `‖X_jk‖ ≤ 4 δ 2^{-k}` by absorption (`norm_xblk_le`, from `norm_sylvester_le` and
  `norm_sylvester_le'`), and the block of the Duhamel operator is a difference of two unitary
  rotations of `X_jk` (`norm_mop_phiT_mul_le`); summing `8 δ 2^{-k}` over all pairs costs
  `16 δ (J + 1)`, the source of the single logarithm.

Multiplicities, small spacings within a band and empty bands never enter.  Mathlib only.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators

namespace KineticLog

/-! ## Dyadic bands -/

/-- The dyadic band `⌊log₂ x⌋` of a label `x ≥ 1`. -/
noncomputable def band (x : ℝ) : ℕ := Nat.log 2 ⌊x⌋₊

lemma two_pow_band_le {x : ℝ} (hx : 1 ≤ x) : (2 : ℝ) ^ band x ≤ x := by
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff x |>.mpr hx
  have h2 : 2 ^ band x ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 (by omega)
  have h3 : ((2 ^ band x : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h2
  push_cast at h3
  exact h3.trans (Nat.floor_le (by linarith))

lemma lt_two_pow_band_succ {x : ℝ} (_hx : 0 ≤ x) : x < (2 : ℝ) ^ (band x + 1) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊x⌋₊
  have h2 : ⌊x⌋₊ + 1 ≤ 2 ^ (band x + 1) := by
    unfold band
    exact h
  have h3 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (band x + 1) : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  linarith [Nat.lt_floor_add_one x]

lemma band_mono {x y : ℝ} (h : x ≤ y) : band x ≤ band y :=
  Nat.log_mono_right (Nat.floor_mono h)

/-- The number of bands below `M ≥ 2` is at most `3 log(2 + M)`. -/
lemma band_add_one_le {M : ℝ} (hM : 2 ≤ M) : (band M : ℝ) + 1 ≤ 3 * Real.log (2 + M) := by
  have hl2 : 1 / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  have hl : 0 < Real.log 2 := by linarith
  have hb : (2 : ℝ) ^ band M ≤ 2 + M := (two_pow_band_le (by linarith)).trans (by linarith)
  have h1 : (band M : ℝ) * Real.log 2 ≤ Real.log (2 + M) := by
    have := Real.log_le_log (by positivity) hb
    rwa [Real.log_pow] at this
  have h4 : 2 * Real.log 2 ≤ Real.log (2 + M) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ 2 + M)
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hℓ : 0 ≤ Real.log (2 + M) := by linarith
  have h5 := mul_le_mul_of_nonneg_left hl2 hℓ
  have h6 : ((band M : ℝ) + 1) * Real.log 2 ≤ (3 * Real.log (2 + M)) * Real.log 2 := by
    nlinarith
  exact le_of_mul_le_mul_right h6 hl

/-! ## Restrictions, input weights and matrix linearity -/

section Aux

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
@[simp] lemma eucl_toLp_apply (f : ι → ℂ) (i : ι) :
    (WithLp.toLp 2 f : EuclideanSpace ℂ ι) i = f i := rfl

/-- Restriction of a coordinate vector to the coordinates satisfying `P`. -/
noncomputable def restr (P : ι → Prop) [DecidablePred P] (x : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => if P i then x i else 0)

lemma norm_sq_restr (P : ι → Prop) [DecidablePred P] (x : EuclideanSpace ℂ ι) :
    ‖restr P x‖ ^ 2 = ∑ i ∈ Finset.univ.filter P, ‖x i‖ ^ 2 := by
  rw [norm_sq_eucl, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ‖(if P i then x i else 0)‖ ^ 2 = _
  split_ifs <;> simp

lemma norm_restr_le (P : ι → Prop) [DecidablePred P] (x : EuclideanSpace ℂ ι) :
    ‖restr P x‖ ≤ ‖x‖ := by
  have := norm_le_of_coord (x := restr P x) (y := x) zero_le_one fun i => by
    change ‖(if P i then x i else 0)‖ ≤ 1 * ‖x i‖
    split_ifs <;> simp
  simpa using this

/-- The inverse-weighted input `c_k / μ_k`. -/
noncomputable def divIn (mu : κ → ℝ) (c : EuclideanSpace ℂ κ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => c k / (mu k : ℂ))

lemma norm_divIn_restr_le (mu : κ → ℝ) (P : κ → Prop) [DecidablePred P] {m : ℝ} (hm : 0 < m)
    (hP : ∀ k, P k → m ≤ mu k) (c : EuclideanSpace ℂ κ) :
    ‖divIn mu (restr P c)‖ ≤ m⁻¹ * ‖restr P c‖ := by
  refine norm_le_of_coord (by positivity) fun k => ?_
  change ‖(if P k then c k else 0) / (mu k : ℂ)‖ ≤ m⁻¹ * ‖(if P k then c k else 0)‖
  split_ifs with h
  · have hk := hP k h
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hm hk),
      div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hm hk) (norm_nonneg _)
  · simp

lemma mop_add (X Y : ι → κ → ℂ) : mop (X + Y) = mop X + mop Y := by
  ext c i
  simp [mop_apply, add_mul, Finset.sum_add_distrib]

lemma mop_zero : mop (0 : ι → κ → ℂ) = 0 := by
  ext c i
  simp [mop_apply]

lemma mop_sum {α : Type*} (s : Finset α) (X : α → ι → κ → ℂ) :
    mop (∑ a ∈ s, X a) = ∑ a ∈ s, mop (X a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mop_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mop_add, ih]

lemma mop_ite (p : Prop) [Decidable p] (X : ι → κ → ℂ) :
    mop (if p then X else 0) = if p then mop X else 0 := by
  split_ifs
  · rfl
  · exact mop_zero

end Aux

/-! ## The dyadic decomposition -/

section Dyadic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `L_ik = A_ik / μ_k²`. -/
noncomputable def lmat (mu : κ → ℝ) (A : ι → κ → ℂ) : ι → κ → ℂ :=
  fun i k => A i k / (mu k : ℂ) ^ 2

/-- The hypothesis matrix `W_ik = A_ik / (λ_i μ_k)`. -/
noncomputable def wmat (lam : ι → ℝ) (mu : κ → ℝ) (A : ι → κ → ℂ) : ι → κ → ℂ :=
  fun i k => A i k / ((lam i : ℂ) * mu k)

/-- Neighbouring bands. -/
def near (j k : ℕ) : Prop := j ≤ k + 1 ∧ k ≤ j + 1

instance (j k : ℕ) : Decidable (near j k) := by unfold near; infer_instance

/-- The part of `L` between neighbouring bands. -/
noncomputable def lnear (lam : ι → ℝ) (mu : κ → ℝ) (A : ι → κ → ℂ) : ι → κ → ℂ :=
  fun i k => if near (band (lam i)) (band (mu k)) then lmat mu A i k else 0

/-- The block of `L` from input band `k` to output band `j`. -/
noncomputable def lblk (lam : ι → ℝ) (mu : κ → ℝ) (A : ι → κ → ℂ) (j k : ℕ) : ι → κ → ℂ :=
  fun i l => if band (lam i) = j ∧ band (mu l) = k then lmat mu A i l else 0

/-- The Sylvester solution of a block: `X_il = L_il / (λ_i - μ_l)`. -/
noncomputable def xblk (lam : ι → ℝ) (mu : κ → ℝ) (A : ι → κ → ℂ) (j k : ℕ) : ι → κ → ℂ :=
  fun i l => lblk lam mu A j k i l / ((lam i : ℂ) - mu l)

variable (lam : ι → ℝ) (mu : κ → ℝ) (A : ι → κ → ℂ)

/-- **Row-band bound**: `‖P_j L c‖ ≤ 2^{j+1} δ ‖μ⁻¹ c‖`. -/
lemma rowband_le (hlam : ∀ i, 1 ≤ lam i) (hmu : ∀ k, 1 ≤ mu k) {δ : ℝ}
    (hA : ∀ c, ‖mop (wmat lam mu A) c‖ ≤ δ * ‖c‖) (j : ℕ) (c : EuclideanSpace ℂ κ) :
    ‖restr (fun i => band (lam i) = j) (mop (lmat mu A) c)‖ ≤ 2 ^ (j + 1) * (δ * ‖divIn mu c‖) := by
  refine (norm_le_of_coord (by positivity) fun i => ?_).trans
    (mul_le_mul_of_nonneg_left (hA _) (by positivity))
  change ‖(if band (lam i) = j then mop (lmat mu A) c i else 0)‖ ≤
    2 ^ (j + 1) * ‖mop (wmat lam mu A) (divIn mu c) i‖
  split_ifs with hj
  · have hl0 : (lam i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hlam i])
    have e : mop (lmat mu A) c i = (lam i : ℂ) * mop (wmat lam mu A) (divIn mu c) i := by
      rw [mop_apply, mop_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hm0 : (mu k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hmu k])
      simp only [lmat, wmat, divIn, eucl_toLp_apply]
      field_simp
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hlam i])]
    have hl := lt_two_pow_band_succ (le_trans zero_le_one (hlam i))
    rw [hj] at hl
    exact mul_le_mul_of_nonneg_right hl.le (norm_nonneg _)
  · rw [norm_zero]
    positivity

/-- **Neighbouring bands**: `‖L_near‖ ≤ 7 δ`. -/
lemma norm_lnear_le {M δ : ℝ} (hlam : ∀ i, 1 ≤ lam i ∧ lam i ≤ M) (hmu : ∀ k, 1 ≤ mu k)
    (hδ : 0 ≤ δ) (hA : ∀ c, ‖mop (wmat lam mu A) c‖ ≤ δ * ‖c‖) (c : EuclideanSpace ℂ κ) :
    ‖mop (lnear lam mu A) c‖ ≤ 7 * δ * ‖c‖ := by
  classical
  set J := band M
  have hJ : ∀ i ∈ (Finset.univ : Finset ι), band (lam i) ∈ Finset.range (J + 1) := fun i _ =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (band_mono (hlam i).2))
  set cj : ℕ → EuclideanSpace ℂ κ := fun j => restr (fun k => near j (band (mu k))) c with hcj
  -- the squared norm splits over output bands
  have hsq : ‖mop (lnear lam mu A) c‖ ^ 2 = ∑ j ∈ Finset.range (J + 1),
      ‖restr (fun i => band (lam i) = j) (mop (lmat mu A) (cj j))‖ ^ 2 := by
    rw [norm_sq_eucl, ← Finset.sum_fiberwise_of_maps_to hJ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_sq_restr]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : band (lam i) = j := (Finset.mem_filter.mp hi).2
    congr 2
    rw [mop_apply, mop_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [lnear, hcj, restr, eucl_toLp_apply, hij]
    split_ifs <;> simp
  -- each output band
  have hband : ∀ j, ‖restr (fun i => band (lam i) = j) (mop (lmat mu A) (cj j))‖ ≤
      4 * δ * ‖cj j‖ := by
    intro j
    refine (rowband_le lam mu A (fun i => (hlam i).1) hmu hA j _).trans ?_
    have hm : (0 : ℝ) < 2 ^ j / 2 := by positivity
    have hdiv := norm_divIn_restr_le mu (fun k => near j (band (mu k))) hm (fun k hk => by
      have h1 := two_pow_band_le (hmu k)
      have h2 : (2 : ℝ) ^ j ≤ 2 ^ (band (mu k) + 1) :=
        pow_le_pow_right₀ (by norm_num) hk.1
      rw [pow_succ] at h2
      linarith) c
    calc 2 ^ (j + 1) * (δ * ‖divIn mu (cj j)‖)
        ≤ 2 ^ (j + 1) * (δ * ((2 ^ j / 2)⁻¹ * ‖cj j‖)) := by gcongr
      _ = 4 * δ * ‖cj j‖ := by
          rw [pow_succ]
          field_simp
          ring
  -- each input coordinate meets at most three output bands
  have hcount : ∑ j ∈ Finset.range (J + 1), ‖cj j‖ ^ 2 ≤ 3 * ‖c‖ ^ 2 := by
    have e : ∀ j, ‖cj j‖ ^ 2 = ∑ k, if near j (band (mu k)) then ‖c k‖ ^ 2 else 0 := by
      intro j
      rw [hcj, norm_sq_restr, Finset.sum_filter]
    simp_rw [e]
    rw [Finset.sum_comm, norm_sq_eucl, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hsub : (Finset.range (J + 1)).filter (fun j => near j (band (mu k))) ⊆
        Finset.Icc (band (mu k) - 1) (band (mu k) + 1) := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_Icc]
      obtain ⟨-, h1, h2⟩ := hj
      omega
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    have : ((Finset.range (J + 1)).filter (fun j => near j (band (mu k)))).card ≤ 3 := by
      omega
    exact_mod_cast this
  have h2 : ‖mop (lnear lam mu A) c‖ ^ 2 ≤ (7 * δ * ‖c‖) ^ 2 := by
    rw [hsq]
    calc ∑ j ∈ Finset.range (J + 1),
          ‖restr (fun i => band (lam i) = j) (mop (lmat mu A) (cj j))‖ ^ 2
        ≤ ∑ j ∈ Finset.range (J + 1), (4 * δ) ^ 2 * ‖cj j‖ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hband j) 2
      _ = (4 * δ) ^ 2 * ∑ j ∈ Finset.range (J + 1), ‖cj j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (4 * δ) ^ 2 * (3 * ‖c‖ ^ 2) := by gcongr
      _ ≤ (7 * δ * ‖c‖) ^ 2 := by nlinarith [sq_nonneg (δ * ‖c‖)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- The norm of a block of `L`: `‖L_jk‖ ≤ 2^{j+1} δ / 2^k`. -/
lemma norm_lblk_le (hlam : ∀ i, 1 ≤ lam i) (hmu : ∀ k, 1 ≤ mu k) {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ∀ c, ‖mop (wmat lam mu A) c‖ ≤ δ * ‖c‖) (j k : ℕ) :
    ‖mop (lblk lam mu A j k)‖ ≤ 2 ^ (j + 1) * δ / 2 ^ k := by
  classical
  refine norm_mop_le (by positivity) fun c => ?_
  have e : mop (lblk lam mu A j k) c = restr (fun i => band (lam i) = j)
      (mop (lmat mu A) (restr (fun l => band (mu l) = k) c)) := by
    ext i
    simp only [restr, eucl_toLp_apply, mop_apply, lblk]
    split_ifs with h
    · refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h2 : band (mu l) = k <;> simp [h, h2]
    · refine Finset.sum_eq_zero fun l _ => ?_
      rw [if_neg (fun h' => h h'.1), zero_mul]
  rw [e]
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have hdiv := norm_divIn_restr_le mu (fun l => band (mu l) = k) hk
    (fun l hl => by rw [← hl]; exact two_pow_band_le (hmu l)) c
  calc ‖restr (fun i => band (lam i) = j) (mop (lmat mu A) (restr (fun l => band (mu l) = k) c))‖
      ≤ 2 ^ (j + 1) * (δ * ‖divIn mu (restr (fun l => band (mu l) = k) c)‖) :=
        rowband_le lam mu A hlam hmu hA j _
    _ ≤ 2 ^ (j + 1) * (δ * ((2 ^ k)⁻¹ * ‖c‖)) := by
        gcongr
        exact hdiv.trans (mul_le_mul_of_nonneg_left (norm_restr_le _ c) (by positivity))
    _ = 2 ^ (j + 1) * δ / 2 ^ k * ‖c‖ := by ring

omit [Fintype ι] [Fintype κ] in
lemma lblk_eq_mul {j k : ℕ} (hjk : j ≠ k) (i : ι) (l : κ) :
    lblk lam mu A j k i l = ((lam i : ℂ) - mu l) * xblk lam mu A j k i l := by
  unfold xblk
  by_cases h : band (lam i) = j ∧ band (mu l) = k
  · have hne : (lam i : ℂ) - mu l ≠ 0 := by
      intro h0
      have : lam i = mu l := by exact_mod_cast sub_eq_zero.mp h0
      apply hjk
      rw [← h.1, ← h.2, this]
    field_simp
  · simp [lblk, h]

/-- **Separated bands**: the Sylvester solution of a block has `‖X_jk‖ ≤ 4 δ / 2^k`. -/
lemma norm_xblk_le (hlam : ∀ i, 1 ≤ lam i) (hmu : ∀ k, 1 ≤ mu k) {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ∀ c, ‖mop (wmat lam mu A) c‖ ≤ δ * ‖c‖) {j k : ℕ} (hfar : ¬ near j k) :
    ‖mop (xblk lam mu A j k)‖ ≤ 4 * δ / 2 ^ k := by
  have hjk : j ≠ k := by
    intro h
    apply hfar
    unfold near
    omega
  have hsyl : ∀ i l, (lam i : ℂ) * xblk lam mu A j k i l - xblk lam mu A j k i l * mu l =
      lblk lam mu A j k i l := by
    intro i l
    rw [lblk_eq_mul lam mu A hjk]
    ring
  have hsupp : ∀ i l, xblk lam mu A j k i l ≠ 0 → band (lam i) = j ∧ band (mu l) = k := by
    intro i l h
    by_contra hc
    apply h
    simp [xblk, lblk, hc]
  have hL := norm_lblk_le lam mu A hlam hmu hδ hA j k
  have ha : (0 : ℝ) < 2 ^ j := by positivity
  have hb : (0 : ℝ) < 2 ^ k := by positivity
  rcases (show k + 2 ≤ j ∨ j + 2 ≤ k by unfold near at hfar; omega) with h | h
  · -- output bands above input bands
    have h4 : 4 * (2 : ℝ) ^ k ≤ 2 ^ j := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h
      rw [pow_add] at this
      linarith
    have hX := norm_sylvester_le lam mu (xblk lam mu A j k) (lblk lam mu A j k)
      (α := 2 ^ j) (β := 2 ^ (k + 1)) (by positivity)
      (by rw [pow_succ]; linarith)
      (fun i l hx => by rw [← (hsupp i l hx).1]; exact two_pow_band_le (hlam i))
      (fun i l hx => by
        rw [abs_of_pos (by linarith [hmu l]), ← (hsupp i l hx).2]
        exact (lt_two_pow_band_succ (by linarith [hmu l])).le)
      hsyl
    have hden : (0 : ℝ) < 2 ^ j - 2 ^ (k + 1) := by rw [pow_succ]; linarith
    refine hX.trans ?_
    rw [div_le_div_iff₀ hden hb]
    calc ‖mop (lblk lam mu A j k)‖ * 2 ^ k ≤ 2 ^ (j + 1) * δ / 2 ^ k * 2 ^ k := by gcongr
      _ = 2 * 2 ^ j * δ := by rw [pow_succ]; field_simp
      _ ≤ 4 * δ * (2 ^ j - 2 ^ (k + 1)) := by rw [pow_succ]; nlinarith
  · -- input bands above output bands
    have h4 : 4 * (2 : ℝ) ^ j ≤ 2 ^ k := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h
      rw [pow_add] at this
      linarith
    have hX := norm_sylvester_le' lam mu (xblk lam mu A j k) (lblk lam mu A j k)
      (α := 2 ^ (j + 1)) (β := 2 ^ k) (by positivity)
      (by rw [pow_succ]; linarith)
      (fun i l hx => by
        rw [abs_of_pos (by linarith [hlam i]), ← (hsupp i l hx).1]
        exact (lt_two_pow_band_succ (by linarith [hlam i])).le)
      (fun i l hx => by rw [← (hsupp i l hx).2]; exact two_pow_band_le (hmu l))
      hsyl
    have hden : (0 : ℝ) < 2 ^ k - 2 ^ (j + 1) := by rw [pow_succ]; linarith
    refine hX.trans ?_
    rw [div_le_div_iff₀ hden hb]
    calc ‖mop (lblk lam mu A j k)‖ * 2 ^ k ≤ 2 ^ (j + 1) * δ / 2 ^ k * 2 ^ k := by gcongr
      _ = 2 * 2 ^ j * δ := by rw [pow_succ]; field_simp
      _ ≤ 4 * δ * (2 ^ k - 2 ^ (j + 1)) := by rw [pow_succ]; nlinarith

/-- The Duhamel kernel times the label difference: `φ_t(x) x = -i (e^{ixt} - 1)`. -/
lemma phiT_mul_self (t x : ℝ) :
    phiT t x * (x : ℂ) = -Complex.I * (Complex.exp (Complex.I * x * t) - 1) := by
  by_cases hx : x = 0
  · subst hx
    simp [phiT]
  · rw [phiT_of_ne hx]
    have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

/-- **A block solved by Sylvester's equation** is a difference of two unitary rotations of the
solution: `‖(φ_t(λ_i - μ_l) (λ_i - μ_l) X_il) c‖ ≤ 2 ‖X‖ ‖c‖`. -/
lemma norm_mop_phiT_mul_le (X : ι → κ → ℂ) (t : ℝ) (c : EuclideanSpace ℂ κ) :
    ‖mop (fun i l => phiT t (lam i - mu l) * (((lam i : ℂ) - mu l) * X i l)) c‖ ≤
      2 * ‖mop X‖ * ‖c‖ := by
  set c' : EuclideanSpace ℂ κ :=
      WithLp.toLp 2 (fun l => Complex.exp (-(Complex.I * mu l * t)) * c l)
  set u : EuclideanSpace ℂ ι :=
    WithLp.toLp 2 (fun i => Complex.exp (Complex.I * lam i * t) * mop X c' i)
  have e : mop (fun i l => phiT t (lam i - mu l) * (((lam i : ℂ) - mu l) * X i l)) c =
      (-Complex.I) • (u - mop X c) := by
    ext i
    simp only [mop_apply, PiLp.smul_apply, PiLp.sub_apply, u, c', smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h1 : phiT t (lam i - mu l) * (((lam i : ℂ) - mu l) * X i l) =
        (phiT t (lam i - mu l) * ((lam i - mu l : ℝ) : ℂ)) * X i l := by
      push_cast
      ring
    rw [h1, phiT_mul_self]
    have h2 : Complex.exp (Complex.I * ((lam i - mu l : ℝ) : ℂ) * t) =
        Complex.exp (Complex.I * lam i * t) * Complex.exp (-(Complex.I * mu l * t)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [h2]
    ring
  rw [e, norm_smul, norm_neg, Complex.norm_I, one_mul]
  have hu : ‖u‖ = ‖mop X c'‖ := norm_diag_unit _ (fun i => by
    rw [Complex.norm_exp]
    simp) _
  have hc' : ‖c'‖ = ‖c‖ := norm_diag_unit _ (fun l => by
    rw [Complex.norm_exp]
    simp) _
  calc ‖u - mop X c‖ ≤ ‖u‖ + ‖mop X c‖ := norm_sub_le _ _
    _ ≤ ‖mop X‖ * ‖c'‖ + ‖mop X‖ * ‖c‖ := by
        rw [hu]
        exact add_le_add (norm_mop_apply_le X c') (norm_mop_apply_le X c)
    _ = 2 * ‖mop X‖ * ‖c‖ := by rw [hc']; ring

omit [Fintype ι] [Fintype κ] in
/-- The entrywise decomposition `L = L_near + Σ_{separated (j,k)} L_jk`. -/
lemma lmat_decomp {J : ℕ} (hlamJ : ∀ i, band (lam i) ≤ J) (hmuJ : ∀ k, band (mu k) ≤ J)
    (i : ι) (l : κ) :
    lmat mu A i l = lnear lam mu A i l + ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (J + 1),
      if ¬ near j k then lblk lam mu A j k i l else 0 := by
  have hj0 : band (lam i) ∈ Finset.range (J + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hlamJ i))
  have hk0 : band (mu l) ∈ Finset.range (J + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hmuJ l))
  rw [Finset.sum_eq_single (band (lam i)) (fun j _ hj => Finset.sum_eq_zero fun k _ => by
      simp [lblk, Ne.symm hj]) (fun h => absurd hj0 h)]
  rw [Finset.sum_eq_single (band (mu l)) (fun k _ hk => by simp [lblk, Ne.symm hk])
      (fun h => absurd hk0 h)]
  unfold lnear lblk
  split_ifs <;> simp_all

/-- **`lem:kinetic-dyadic`** (`eq:kinetic-dyadic`), in eigenbasis coordinates: if the labels lie
in `[1, M]` with `M ≥ 2` and the doubly inverse-weighted matrix has norm at most `δ`, then for
every `t ≥ 0`, `‖(φ_t(λ_i - μ_k) A_ik/μ_k²) c‖ ≤ 48 δ (t + log(2 + M)) ‖c‖`. -/
theorem dyadic_duhamel {M δ : ℝ} (hM : 2 ≤ M) (hδ : 0 ≤ δ)
    (hlam : ∀ i, 1 ≤ lam i ∧ lam i ≤ M) (hmu : ∀ k, 1 ≤ mu k ∧ mu k ≤ M)
    (hA : ∀ c, ‖mop (wmat lam mu A) c‖ ≤ δ * ‖c‖) {t : ℝ} (ht : 0 ≤ t)
    (c : EuclideanSpace ℂ κ) :
    ‖mop (fun i k => phiT t (lam i - mu k) * (A i k / (mu k : ℂ) ^ 2)) c‖ ≤
      48 * δ * (t + Real.log (2 + M)) * ‖c‖ := by
  classical
  set J := band M
  have hlamJ : ∀ i, band (lam i) ≤ J := fun i => band_mono (hlam i).2
  have hmuJ : ∀ k, band (mu k) ≤ J := fun k => band_mono (hmu k).2
  set phi : (ι → κ → ℂ) → ι → κ → ℂ := fun X i l => phiT t (lam i - mu l) * X i l with hphi
  -- the matrix identity
  have hmat : (fun i k => phiT t (lam i - mu k) * (A i k / (mu k : ℂ) ^ 2)) =
      phi (lnear lam mu A) + ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (J + 1),
        if ¬ near j k then phi (lblk lam mu A j k) else 0 := by
    funext i l
    have h := lmat_decomp lam mu A hlamJ hmuJ i l
    simp only [lmat] at h
    rw [h]
    simp only [hphi, Pi.add_apply, Finset.sum_apply, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [hmat, mop_add, mop_sum, add_apply]
  simp_rw [mop_sum, mop_ite]
  -- the near part
  have hnear : ‖mop (phi (lnear lam mu A)) c‖ ≤ 7 * t * δ * ‖c‖ := by
    have h1 := norm_mop_phiT_le lam mu (lnear lam mu A) ht c
    have h2 : ‖mop (lnear lam mu A)‖ ≤ 7 * δ :=
      norm_mop_le (by positivity) (norm_lnear_le lam mu A hlam (fun k => (hmu k).1) hδ hA)
    calc ‖mop (phi (lnear lam mu A)) c‖ ≤ t * ‖mop (lnear lam mu A)‖ * ‖c‖ := h1
      _ ≤ t * (7 * δ) * ‖c‖ := by gcongr
      _ = 7 * t * δ * ‖c‖ := by ring
  -- the separated blocks
  have hfar : ∀ j k, ¬ near j k → ‖mop (phi (lblk lam mu A j k)) c‖ ≤ 8 * δ * ‖c‖ / 2 ^ k := by
    intro j k hjk
    have hjk' : j ≠ k := by
      intro h
      apply hjk
      unfold near
      omega
    have e : phi (lblk lam mu A j k) = fun i l =>
        phiT t (lam i - mu l) * (((lam i : ℂ) - mu l) * xblk lam mu A j k i l) := by
      funext i l
      simp only [hphi]
      rw [lblk_eq_mul lam mu A hjk']
    rw [e]
    refine (norm_mop_phiT_mul_le lam mu (xblk lam mu A j k) t c).trans ?_
    have hX := norm_xblk_le lam mu A (fun i => (hlam i).1) (fun k => (hmu k).1) hδ hA hjk
    calc 2 * ‖mop (xblk lam mu A j k)‖ * ‖c‖ ≤ 2 * (4 * δ / 2 ^ k) * ‖c‖ := by gcongr
      _ = 8 * δ * ‖c‖ / 2 ^ k := by ring
  have hsum : ‖∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (J + 1),
      (if ¬ near j k then mop (phi (lblk lam mu A j k)) else 0) c‖ ≤
      16 * ((J : ℝ) + 1) * δ * ‖c‖ := by
    calc ‖∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (J + 1),
          (if ¬ near j k then mop (phi (lblk lam mu A j k)) else 0) c‖
        ≤ ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (J + 1),
          ‖(if ¬ near j k then mop (phi (lblk lam mu A j k)) else 0) c‖ := by
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
      _ ≤ ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (J + 1),
          8 * δ * ‖c‖ * (1 / 2) ^ k := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
          by_cases h : near j k
          · simp only [h, not_true_eq_false, if_false, zero_apply, norm_zero]
            positivity
          · simp only [h, not_false_eq_true, if_true]
            refine (hfar j k h).trans (le_of_eq ?_)
            rw [one_div_pow, div_eq_mul_inv, one_div]
      _ = ((J : ℝ) + 1) * (8 * δ * ‖c‖ * ∑ k ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ k) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
          push_cast
          ring
      _ ≤ ((J : ℝ) + 1) * (8 * δ * ‖c‖ * 2) := by
          gcongr
          exact sum_geometric_two_le (J + 1)
      _ = 16 * ((J : ℝ) + 1) * δ * ‖c‖ := by ring
  have hJlog := band_add_one_le hM
  calc ‖mop (phi (lnear lam mu A)) c + (∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (J + 1),
        if ¬ near j k then mop (phi (lblk lam mu A j k)) else 0) c‖
      ≤ ‖mop (phi (lnear lam mu A)) c‖ + ‖∑ j ∈ Finset.range (J + 1),
          ∑ k ∈ Finset.range (J + 1),
            (if ¬ near j k then mop (phi (lblk lam mu A j k)) else 0) c‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        congr 2
        rw [sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sum_apply]
    _ ≤ 7 * t * δ * ‖c‖ + 16 * ((J : ℝ) + 1) * δ * ‖c‖ := add_le_add hnear hsum
    _ ≤ 7 * t * δ * ‖c‖ + 16 * (3 * Real.log (2 + M)) * δ * ‖c‖ := by gcongr
    _ ≤ 48 * δ * (t + Real.log (2 + M)) * ‖c‖ := by
        have hc := norm_nonneg c
        have hlog : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
        nlinarith [mul_nonneg (mul_nonneg hδ hc) ht, mul_nonneg (mul_nonneg hδ hc) hlog]

end Dyadic

end KineticLog
