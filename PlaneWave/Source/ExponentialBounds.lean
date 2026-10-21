import PlaneWave.Source.Conjugation

/-!
# Flux/source build, block 3d: vector bounds for `e^{Z}` (Mathlib only)

For a skew-adjoint `Z` on a complex Hilbert space:

* `norm_exp_sub_one_apply_le`: `‖(e^{Z} - 1) x‖ ≤ ‖Z x‖`;
* `norm_exp_sub_one_sub_apply_le`: `‖(e^{Z} - 1 - Z) x‖ ≤ ‖Z (Z x)‖`;
* the same for `e^{-Z}` (`-Z` is skew-adjoint), and `‖e^{Z} x‖ = ‖x‖`.

These are the bounds `‖P d‖ ≤ C b ‖Σ_b ψ̃_P‖`, `‖P e‖ ≤ C b ‖ψ̃_R‖` of `prop:nf` and the exact
remainders of `lem:acorr`, by the mean value theorem along `r ↦ e^{rZ} x` (no power series).
-/

set_option autoImplicit false

open scoped InnerProductSpace
open NormedSpace

namespace FSConj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {Z : E →L[ℂ] E}

lemma neg_mem_skew (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) : -Z ∈ skewAdjoint (E →L[ℂ] E) :=
  (skewAdjoint (E →L[ℂ] E)).neg_mem hZ

lemma smul_mem_skew (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (r : ℝ) :
    (r : ℂ) • Z ∈ skewAdjoint (E →L[ℂ] E) := by
  rw [skewAdjoint.mem_iff, star_smul, skewAdjoint.mem_iff.mp hZ, Complex.star_def,
    Complex.conj_ofReal, smul_neg]

lemma norm_ex_apply (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (r : ℝ) (x : E) : ‖ex Z r x‖ = ‖x‖ := by
  have hu := ex_mem_unitary Z hZ r
  have h : ‖ex Z r x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ,
      ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← mul_apply_eq_comp, (Unitary.mem_iff.mp hu).1, one_apply_eq_self]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

lemma norm_exp_apply (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (x : E) : ‖exp Z x‖ = ‖x‖ := by
  rw [← ex_one]; exact norm_ex_apply hZ 1 x

lemma hasDerivAt_ex_apply (r : ℝ) (x : E) :
    HasDerivAt (fun s => ex Z s x) (ex Z r (Z x)) r := by
  have h := (hasDerivAt_ex Z r)
  have h2 := ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r h
  simpa [Function.comp_def, mul_apply_eq_comp] using h2

/-- **`‖(e^{Z} - 1) x‖ ≤ ‖Z x‖`.** -/
theorem norm_exp_sub_one_apply_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (x : E) :
    ‖exp Z x - x‖ ≤ ‖Z x‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Set.univ)
    (f := fun s => ex Z s x) (f' := fun s => ex Z s (Z x)) (C := ‖Z x‖)
    (fun s _ => (hasDerivAt_ex_apply s x).hasDerivWithinAt)
    (fun s _ => (norm_ex_apply hZ s _).le) convex_univ (Set.mem_univ 0) (Set.mem_univ 1)
  simpa [ex_one, ex_zero] using h

/-- The scaled version: `‖(e^{rZ} - 1) x‖ ≤ |r| ‖Z x‖`. -/
lemma norm_ex_sub_apply_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (r : ℝ) (x : E) :
    ‖ex Z r x - x‖ ≤ |r| * ‖Z x‖ := by
  have h := norm_exp_sub_one_apply_le (smul_mem_skew hZ r) x
  rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- **`‖(e^{Z} - 1 - Z) x‖ ≤ ‖Z (Z x)‖`.** -/
theorem norm_exp_sub_one_sub_apply_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (x : E) :
    ‖exp Z x - x - Z x‖ ≤ ‖Z (Z x)‖ := by
  set g : ℝ → E := fun s => ex Z s x - x - (s : ℂ) • Z x
  have hg : ∀ s, HasDerivAt g (ex Z s (Z x) - Z x) s := by
    intro s
    have h1 := (hasDerivAt_ex_apply (Z := Z) s x).sub_const x
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) • Z x) ((1 : ℂ) • Z x) s := by
      have := (Complex.ofRealCLM.hasDerivAt (x := s)).smul_const (Z x)
      simpa using this
    have h3 := h1.sub h2
    rw [one_smul] at h3
    exact h3
  have hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖ex Z s (Z x) - Z x‖ ≤ ‖Z (Z x)‖ := by
    intro s hs
    refine (norm_ex_sub_apply_le hZ s (Z x)).trans ?_
    have : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
    exact mul_le_of_le_one_left (norm_nonneg _) this
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := Set.Icc (0 : ℝ) 1)
    (f := g) (f' := fun s => ex Z s (Z x) - Z x) (C := ‖Z (Z x)‖)
    (fun s _ => (hg s).hasDerivWithinAt) hb (convex_Icc 0 1) ⟨le_rfl, zero_le_one⟩
    ⟨zero_le_one, le_rfl⟩
  have h0 : g 0 = 0 := by simp [g, ex_zero]
  have h1 : g 1 = exp Z x - x - Z x := by simp [g, ex_one]
  rw [h0, h1, sub_zero, sub_zero, norm_one, mul_one] at h
  exact h

/-- The same bounds for `e^{-Z}`. -/
theorem norm_exp_neg_sub_one_apply_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (x : E) :
    ‖exp (-Z) x - x‖ ≤ ‖Z x‖ := by
  have := norm_exp_sub_one_apply_le (neg_mem_skew hZ) x
  rwa [neg_apply, norm_neg] at this

theorem norm_exp_neg_sub_one_add_apply_le (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (x : E) :
    ‖exp (-Z) x - x + Z x‖ ≤ ‖Z (Z x)‖ := by
  have := norm_exp_sub_one_sub_apply_le (neg_mem_skew hZ) x
  simp only [neg_apply, map_neg, neg_neg, sub_neg_eq_add] at this
  exact this

/-- `(e^{Z})* = e^{-Z}` for skew-adjoint `Z`. -/
lemma adjoint_exp (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) :
    ContinuousLinearMap.adjoint (exp Z) = exp (-Z) := by
  letI := (ratAlg : NormedAlgebra ℚ (E →L[ℂ] E))
  rw [← ContinuousLinearMap.star_eq_adjoint, star_exp, skewAdjoint.mem_iff.mp hZ]

end FSConj
