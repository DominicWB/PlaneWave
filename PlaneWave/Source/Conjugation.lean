import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Flux/source build, block 2c: conjugation by `e^{Σ}` (Mathlib only)

For a complex Hilbert space `E`, `𝔸 = E →L[ℂ] E` and a skew-adjoint `Z ∈ 𝔸` (the generator):

* `ex Z r = e^{rZ}` for real `r`: unitary, `e^{0} = 1`, `e^{-rZ} e^{rZ} = 1`,
  `∂_r e^{rZ} = e^{rZ} Z = Z e^{rZ}`;
* `cj Z r X = e^{rZ} X e^{-rZ}` and the commutator `cm Z X = Z X - X Z`:
  `∂_r cj = cj (cm Z X)`, `‖cj Z r X‖ = ‖X‖`, `‖cj Z r X - X‖ ≤ |r| ‖[Z, X]‖`,
  `‖cj Z r X - X - r [Z, X]‖ ≤ r ‖[Z, [Z, X]]‖` on `[0, 1]`;
* `Bi Z X = ∫₀¹ e^{rZ} X e^{-rZ} dr` with `‖Bi - X‖ ≤ ‖[Z, X]‖` and
  `‖Bi - X - ½[Z, X]‖ ≤ ‖[Z, [Z, X]]‖`;
* **`conj_unbounded`**: if `S G = Z S` and `H G - Z H = X S` (the commutator `[H, Z]` of an
  operator defined on `ran S` extends to the bounded `X`), then `e^{Z} H e^{-G} = H - Bi Z X · S`.
  With `S` the decoding map, `G = S⁻¹ Z S` and `H` the Hamiltonian, this is the conjugation
  `e^{Σ} H e^{-Σ} = H + B` on `D(T)`, `B = -∫₀¹ e^{rΣ}[H, Σ]e^{-rΣ} dr` bounded (`lem:bulk-weighted`:
  "the Hamiltonian conjugation is an identity on `D(A)`; its bounded correction has a
  norm-convergent expansion").
-/

set_option autoImplicit false

open scoped InnerProductSpace
open NormedSpace MeasureTheory intervalIntegral

namespace FSConj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The rational algebra structure used by the exponential lemmas. -/
@[reducible] noncomputable def ratAlg : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _

/-- `e^{rZ}` for real `r`. -/
noncomputable def ex (Z : E →L[ℂ] E) (r : ℝ) : E →L[ℂ] E := exp ((r : ℂ) • Z)

/-- The commutator `[Z, X] = Z X - X Z`. -/
def cm (Z X : E →L[ℂ] E) : E →L[ℂ] E := Z * X - X * Z

/-- The conjugate `e^{rZ} X e^{-rZ}`. -/
noncomputable def cj (Z : E →L[ℂ] E) (r : ℝ) (X : E →L[ℂ] E) : E →L[ℂ] E :=
  ex Z r * X * ex Z (-r)

variable (Z : E →L[ℂ] E)

omit [CompleteSpace E] in
lemma ex_zero : ex Z 0 = 1 := by simp [ex]

omit [CompleteSpace E] in
lemma ex_one : ex Z 1 = exp Z := by simp [ex]

omit [CompleteSpace E] in
lemma ex_neg_one : ex Z (-1) = exp (-Z) := by simp [ex]

omit [CompleteSpace E] in
lemma ex_commute (r s : ℝ) : Commute ((r : ℂ) • Z) ((s : ℂ) • Z) :=
  ((Commute.refl Z).smul_left _).smul_right _

lemma ex_add (r s : ℝ) : ex Z (r + s) = ex Z r * ex Z s := by
  letI := (ratAlg : NormedAlgebra ℚ (E →L[ℂ] E))
  unfold ex
  rw [← exp_add_of_commute (ex_commute Z r s), Complex.ofReal_add, add_smul]

lemma ex_neg_mul (r : ℝ) : ex Z (-r) * ex Z r = 1 := by
  rw [← ex_add, neg_add_cancel, ex_zero]

lemma ex_mul_neg (r : ℝ) : ex Z r * ex Z (-r) = 1 := by
  rw [← ex_add, add_neg_cancel, ex_zero]

omit [CompleteSpace E] in
lemma commute_ex' (r : ℝ) : Commute Z ((r : ℂ) • Z) := (Commute.refl Z).smul_right _

omit [CompleteSpace E] in
lemma commute_ex (r : ℝ) : Commute Z (ex Z r) :=
  ((Commute.refl Z).smul_right _).exp_right

lemma hasDerivAt_ex (r : ℝ) : HasDerivAt (ex Z) (ex Z r * Z) r := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℂ) Z (r : ℂ)
  have hr : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 r := by
    simpa using (hasDerivAt_id r).ofReal_comp
  have h2 := h.scomp r hr
  rw [one_smul] at h2
  exact h2

lemma hasDerivAt_ex_neg (r : ℝ) : HasDerivAt (fun s => ex Z (-s)) (-(ex Z (-r) * Z)) r := by
  have h := (hasDerivAt_ex Z (-r)).scomp r (hasDerivAt_neg r)
  simpa [Function.comp_def] using h

lemma ex_mem_unitary (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (r : ℝ) :
    ex Z r ∈ unitary (E →L[ℂ] E) := by
  letI := (ratAlg : NormedAlgebra ℚ (E →L[ℂ] E))
  apply exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff, star_smul, skewAdjoint.mem_iff.mp hZ, Complex.star_def,
    Complex.conj_ofReal, smul_neg]

/-! ## The conjugate -/

variable {Z}

omit [CompleteSpace E] in
lemma cj_zero (X : E →L[ℂ] E) : cj Z 0 X = X := by simp [cj, ex_zero]

omit [CompleteSpace E] in
lemma cj_one (X : E →L[ℂ] E) : cj Z 1 X = exp Z * X * exp (-Z) := by
  rw [cj, ex_one, ex_neg_one]

lemma hasDerivAt_cj (X : E →L[ℂ] E) (r : ℝ) :
    HasDerivAt (fun s => cj Z s X) (cj Z r (cm Z X)) r := by
  have h1 := (hasDerivAt_ex Z r).mul_const X
  have h2 := h1.mul (hasDerivAt_ex_neg Z r)
  have hc := (commute_ex Z (-r)).eq
  have e : ex Z r * Z * X * ex Z (-r) + ex Z r * X * -(ex Z (-r) * Z) = cj Z r (cm Z X) := by
    rw [← hc]; unfold cj cm; noncomm_ring
  exact h2.congr_deriv e

lemma continuous_cj (X : E →L[ℂ] E) : Continuous fun r => cj Z r X :=
  continuous_iff_continuousAt.mpr fun r => (hasDerivAt_cj X r).continuousAt

lemma norm_cj (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (r : ℝ) (X : E →L[ℂ] E) :
    ‖cj Z r X‖ = ‖X‖ := by
  unfold cj
  rw [CStarRing.norm_mul_mem_unitary _ (ex_mem_unitary Z hZ (-r)),
    CStarRing.norm_mem_unitary_mul _ (ex_mem_unitary Z hZ r)]

/-- `‖e^{rZ} X e^{-rZ} - X‖ ≤ |r| ‖[Z, X]‖`. -/
lemma norm_cj_sub_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (r : ℝ) (X : E →L[ℂ] E) :
    ‖cj Z r X - X‖ ≤ ‖cm Z X‖ * |r| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Set.univ)
    (f := fun s => cj Z s X) (f' := fun s => cj Z s (cm Z X)) (C := ‖cm Z X‖)
    (fun s _ => (hasDerivAt_cj X s).hasDerivWithinAt) (fun s _ => (norm_cj hZ s _).le)
    convex_univ (Set.mem_univ 0) (Set.mem_univ r)
  simpa [cj_zero, Real.norm_eq_abs] using h

/-- The second-order bound on `[0, 1]`: `‖cj Z r X - X - r [Z, X]‖ ≤ ‖[Z, [Z, X]]‖ r`. -/
lemma norm_cj_taylor_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (X : E →L[ℂ] E) :
    ‖cj Z r X - X - (r : ℂ) • cm Z X‖ ≤ ‖cm Z (cm Z X)‖ * r := by
  set φ : ℝ → E →L[ℂ] E := fun s => cj Z s X - X - (s : ℂ) • cm Z X
  have hφ : ∀ s, HasDerivAt φ (cj Z s (cm Z X) - cm Z X) s := by
    intro s
    have h1 := (hasDerivAt_cj (Z := Z) X s).sub_const X
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) • cm Z X) ((1 : ℂ) • cm Z X) s := by
      have := (Complex.ofRealCLM.hasDerivAt (x := s)).smul_const (cm Z X)
      simpa using this
    have h3 := h1.sub h2
    rw [one_smul] at h3
    exact h3
  have hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖cj Z s (cm Z X) - cm Z X‖ ≤ ‖cm Z (cm Z X)‖ := by
    intro s hs
    refine (norm_cj_sub_le hZ s _).trans ?_
    have : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
    exact mul_le_of_le_one_right (norm_nonneg _) this
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Set.Icc (0 : ℝ) 1)
    (f := φ) (f' := fun s => cj Z s (cm Z X) - cm Z X) (C := ‖cm Z (cm Z X)‖)
    (fun s _ => (hφ s).hasDerivWithinAt) hb (convex_Icc 0 1) ⟨le_rfl, zero_le_one⟩ hr
  have h0 : φ 0 = 0 := by simp [φ, cj_zero]
  rw [h0, sub_zero, Real.norm_eq_abs, sub_zero, abs_of_nonneg hr.1] at h
  exact h

/-! ## The averaged conjugate `∫₀¹ e^{rZ} X e^{-rZ} dr` -/

/-- `Bi Z X = ∫₀¹ e^{rZ} X e^{-rZ} dr`. -/
noncomputable def Bi (Z X : E →L[ℂ] E) : E →L[ℂ] E := ∫ r in (0 : ℝ)..1, cj Z r X

lemma intervalIntegrable_cj (X : E →L[ℂ] E) (a b : ℝ) :
    IntervalIntegrable (fun r => cj Z r X) volume a b :=
  (continuous_cj X).intervalIntegrable a b

lemma norm_Bi_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (X : E →L[ℂ] E) : ‖Bi Z X‖ ≤ ‖X‖ := by
  unfold Bi
  have := norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := ‖X‖)
    (f := fun r => cj Z r X) fun r _ => (norm_cj hZ r X).le
  simpa using this

/-- `‖Bi Z X - X‖ ≤ ‖[Z, X]‖`. -/
lemma norm_Bi_sub_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (X : E →L[ℂ] E) :
    ‖Bi Z X - X‖ ≤ ‖cm Z X‖ := by
  have e : Bi Z X - X = ∫ r in (0 : ℝ)..1, (cj Z r X - X) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_cj X 0 1) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp [Bi]
  rw [e]
  have := norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := ‖cm Z X‖)
    (f := fun r => cj Z r X - X) fun r hr => by
      refine (norm_cj_sub_le hZ r X).trans ?_
      have hr' : r ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hr
      have : |r| ≤ 1 := by rw [abs_of_pos hr'.1]; exact hr'.2
      exact mul_le_of_le_one_right (norm_nonneg _) this
  simpa using this

/-- **The second-order expansion of the averaged conjugate**:
`‖Bi Z X - X - ½[Z, X]‖ ≤ ‖[Z, [Z, X]]‖`. -/
lemma norm_Bi_taylor_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (X : E →L[ℂ] E) :
    ‖Bi Z X - X - (1 / 2 : ℂ) • cm Z X‖ ≤ ‖cm Z (cm Z X)‖ := by
  have hlin : IntervalIntegrable (fun r : ℝ => (r : ℂ) • cm Z X) volume 0 1 :=
    (Continuous.smul (Complex.continuous_ofReal) continuous_const).intervalIntegrable 0 1
  have hint : ∫ r in (0 : ℝ)..1, (r : ℂ) • cm Z X = (1 / 2 : ℂ) • cm Z X := by
    rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_ofReal, integral_id]
    norm_num
  have e : Bi Z X - X - (1 / 2 : ℂ) • cm Z X =
      ∫ r in (0 : ℝ)..1, (cj Z r X - X - (r : ℂ) • cm Z X) := by
    rw [intervalIntegral.integral_sub ((intervalIntegrable_cj X 0 1).sub intervalIntegrable_const)
      hlin, intervalIntegral.integral_sub (intervalIntegrable_cj X 0 1) intervalIntegrable_const,
      intervalIntegral.integral_const, hint]
    simp [Bi]
  rw [e]
  have := norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := ‖cm Z (cm Z X)‖)
    (f := fun r => cj Z r X - X - (r : ℂ) • cm Z X) fun r hr => by
      have hr' : r ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hr
      refine (norm_cj_taylor_le hZ ⟨hr'.1.le, hr'.2⟩ X).trans ?_
      exact mul_le_of_le_one_right (norm_nonneg _) hr'.2
  simpa using this

/-- The full conjugate to second order: `‖e^Z X e^{-Z} - X - [Z, X]‖ ≤ ‖[Z, [Z, X]]‖`. -/
lemma norm_conj_taylor_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (X : E →L[ℂ] E) :
    ‖exp Z * X * exp (-Z) - X - cm Z X‖ ≤ ‖cm Z (cm Z X)‖ := by
  have := norm_cj_taylor_le hZ (r := 1) ⟨zero_le_one, le_rfl⟩ X
  rwa [cj_one, Complex.ofReal_one, one_smul, mul_one] at this

/-- The full conjugate to first order: `‖e^Z X e^{-Z} - X‖ ≤ ‖[Z, X]‖`. -/
lemma norm_conj_sub_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (X : E →L[ℂ] E) :
    ‖exp Z * X * exp (-Z) - X‖ ≤ ‖cm Z X‖ := by
  have := norm_cj_sub_le hZ 1 X
  rwa [cj_one, abs_one, mul_one] at this

/-! ## Conjugation of an operator defined on a range -/

/-- **Conjugation on `ran S`.** If `S G = Z S` and `H G - Z H = X S`, then
`e^{Z} H e^{-G} = H - (∫₀¹ e^{rZ} X e^{-rZ} dr) S`. -/
theorem conj_unbounded {S H G X : E →L[ℂ] E} (hSG : S * G = Z * S) (hHG : H * G - Z * H = X * S) :
    exp Z * H * exp (-G) = H - Bi Z X * S := by
  letI := (ratAlg : NormedAlgebra ℚ (E →L[ℂ] E))
  -- `S e^{-rG} = e^{-rZ} S`
  have hsc : ∀ r : ℝ, S * ex G (-r) = ex Z (-r) * S := by
    intro r
    have h : SemiconjBy S (((-r : ℝ) : ℂ) • G) (((-r : ℝ) : ℂ) • Z) := by
      unfold SemiconjBy
      rw [mul_smul_comm, hSG, smul_mul_assoc]
    exact h.exp_right
  set F : ℝ → E →L[ℂ] E := fun r => ex Z r * H * ex G (-r)
  have hF : ∀ r, HasDerivAt F (-(cj Z r X * S)) r := by
    intro r
    have h1 := (hasDerivAt_ex Z r).mul_const H
    have h2 := h1.mul (hasDerivAt_ex_neg G r)
    have hc := (commute_ex G (-r)).eq
    have e : ex Z r * Z * H * ex G (-r) + ex Z r * H * -(ex G (-r) * G) = -(cj Z r X * S) := by
      unfold cj
      rw [mul_assoc (ex Z r * X), ← hsc r, ← hc]
      have : ex Z r * X * (S * ex G (-r)) = ex Z r * (H * G - Z * H) * ex G (-r) := by
        rw [hHG]; noncomm_ring
      rw [this]
      noncomm_ring
    exact h2.congr_deriv e
  have hcont : Continuous fun r => -(cj Z r X * S) :=
    ((continuous_cj X).mul continuous_const).neg
  have hftc := integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun r _ => hF r)
    (hcont.intervalIntegrable 0 1)
  have hF1 : F 1 = exp Z * H * exp (-G) := by simp only [F, ex_one, ex_neg_one]
  have hF0 : F 0 = H := by simp only [F, ex_zero, neg_zero, one_mul, mul_one]
  -- pull `S` out of the integral
  have hpull : ∫ r in (0 : ℝ)..1, -(cj Z r X * S) = -(Bi Z X * S) := by
    rw [intervalIntegral.integral_neg]
    congr 1
    have := ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip S).intervalIntegral_comp_comm
      (intervalIntegrable_cj (Z := Z) X 0 1)
    simpa [Bi] using this
  rw [hpull, hF1, hF0] at hftc
  have h := hftc.symm
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

end FSConj
