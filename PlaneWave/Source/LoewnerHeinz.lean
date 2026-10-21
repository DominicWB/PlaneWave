import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Lagrange

/-!
# Löwner–Heinz comparison of fractional powers

Operators on a finite-dimensional complex inner product space `E`, viewed as elements of the
C⋆-algebra `E →L[ℂ] E` with the Loewner order, the real continuous functional calculus `cfc`
and the real powers `X ^ s = CFC.rpow X s`.

* `cfc_apply_eigen`: for self-adjoint `X` with `X v = μ v`, `cfc f X v = f μ • v` for every
  `f : ℝ → ℝ` (Lagrange interpolation on the finite set `spectrum ℝ X ∪ {μ}`, then
  `cfc_congr` and `cfc_polynomial`);
* `rpow_apply_eigen`, `rpow_apply_basis`: the same for `X ^ s` (`0 ≤ X`), and the expansion
  `X ^ s v = ∑ i, (lam i) ^ s ⟪b i, v⟫ b i` in an orthonormal eigenbasis;
* `norm_rpow_le_of_norm_le`: **Löwner–Heinz** in norm form: if `0 ≤ X`, `0 ≤ Y`, `C ≥ 0` and
  `‖X v‖ ≤ C ‖Y v‖` for all `v`, then `‖X ^ s v‖ ≤ C ^ s ‖Y ^ s v‖` for all `v` and
  `s ∈ [0, 1]`.  The hypothesis says `X * X ≤ (C Y) * (C Y)` in the Loewner order
  (`mul_self_le_mul_self_iff`); operator monotonicity of `t ↦ t ^ s` (`CFC.rpow_le_rpow`) gives
  `(X * X) ^ s ≤ ((C Y) * (C Y)) ^ s`, and the identities `(X * X) ^ s = X ^ s * X ^ s`
  (`mul_self_rpow`) and `(c Y) ^ s = c ^ s Y ^ s` (`ofReal_smul_rpow`), both checked on an
  eigenbasis, turn this back into the norm comparison;
* `ePow`, `ePowL`, `norm_ePow_le_of_norm_ePow_le`: the eigenbasis form
  `ePow b x s v = ∑ i, (x i) ^ s ⟪b i, v⟫ b i` used by the rest of the project, and the
  Löwner–Heinz comparison between two such families built on different orthonormal bases.
-/

set_option autoImplicit false

namespace FluxSourceTest

open scoped InnerProductSpace Polynomial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Preliminaries (no finite-dimensionality needed) -/

/-- Lagrange interpolation: a real function agrees with some real polynomial on a finite set. -/
lemma exists_poly_eqOn (S : Finset ℝ) (f : ℝ → ℝ) :
    ∃ p : ℝ[X], ∀ x ∈ S, p.eval x = f x := by
  classical
  exact ⟨Lagrange.interpolate S id f, fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) f (Set.injOn_id _) hx⟩

/-- Natural powers of an operator act on an eigenvector by powers of the eigenvalue. -/
lemma pow_apply_eigen (X : E →L[ℂ] E) {v : E} {μ : ℝ} (hv : X v = (μ : ℂ) • v) (n : ℕ) :
    (X ^ n) v = ((μ ^ n : ℝ) : ℂ) • v := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Complex.ofReal_one, one_smul, one_apply_eq_self]
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hv, smul_smul, pow_succ,
      Complex.ofReal_mul]

/-- A real polynomial in an operator acts on an eigenvector by the polynomial evaluated at the
eigenvalue. -/
lemma aeval_apply_eigen (X : E →L[ℂ] E) {v : E} {μ : ℝ} (hv : X v = (μ : ℂ) • v) (p : ℝ[X]) :
    (Polynomial.aeval X p) v = ((p.eval μ : ℝ) : ℂ) • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, add_apply, hp, hq, Polynomial.eval_add, Complex.ofReal_add, add_smul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, mul_apply_eq_comp, pow_apply_eigen X hv n,
      Polynomial.eval_monomial, ContinuousLinearMap.algebraMap_apply, ← Complex.coe_smul,
      smul_smul, Complex.ofReal_mul]

/-- Two operators that agree on an orthonormal basis are equal. -/
lemma ext_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E)
    {A B : E →L[ℂ] E} (h : ∀ i, A (b i) = B (b i)) : A = B := by
  ext v
  rw [← b.sum_repr' v, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, h i]

/-- A nonnegative real multiple of a nonnegative operator is nonnegative. -/
lemma ofReal_smul_nonneg {Y : E →L[ℂ] E} (hY : 0 ≤ Y) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ (c : ℂ) • Y := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hY ⊢
  exact hY.smul_of_nonneg (Complex.zero_le_real.mpr hc)

section FiniteDimensional

variable [FiniteDimensional ℂ E]

/-! ## Functional calculus on eigenvectors -/

/-- The real spectrum of an operator on a finite-dimensional complex inner product space is
finite. -/
lemma finite_spectrum_real (X : E →L[ℂ] E) : (spectrum ℝ X).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  have h : (spectrum ℂ X).Finite := by
    rw [← AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap (𝕜 := ℂ) E).symm X]
    exact Module.End.finite_spectrum _
  exact h.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

/-- **Functional calculus on an eigenvector.** If `X` is self-adjoint and `X v = μ v`, then
`cfc f X v = f μ • v` for every `f : ℝ → ℝ`. -/
theorem cfc_apply_eigen {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) {v : E} {μ : ℝ}
    (hv : X v = (μ : ℂ) • v) (f : ℝ → ℝ) : cfc f X v = ((f μ : ℝ) : ℂ) • v := by
  classical
  obtain ⟨p, hp⟩ := exists_poly_eqOn (insert μ (finite_spectrum_real X).toFinset) f
  have hcfc : cfc f X = cfc (fun x => p.eval x) X := cfc_congr fun x hx =>
    (hp x (Finset.mem_insert_of_mem ((finite_spectrum_real X).mem_toFinset.mpr hx))).symm
  rw [hcfc, cfc_polynomial p X hX, aeval_apply_eigen X hv p, hp μ (Finset.mem_insert_self _ _)]

/-- **Real powers on an eigenvector.** If `0 ≤ X` and `X v = μ v`, then
`X ^ s v = μ ^ s • v` for every real `s`. -/
theorem rpow_apply_eigen {X : E →L[ℂ] E} (hX : 0 ≤ X) {v : E} {μ : ℝ}
    (hv : X v = (μ : ℂ) • v) (s : ℝ) : (X ^ s) v = ((μ ^ s : ℝ) : ℂ) • v := by
  rw [CFC.rpow_eq_cfc_real hX]
  exact cfc_apply_eigen (IsSelfAdjoint.of_nonneg hX) hv _

/-- **Eigenbasis expansion of real powers.** If `0 ≤ X` has the orthonormal eigenbasis `b` with
eigenvalues `lam`, then `X ^ s v = ∑ i, (lam i) ^ s ⟪b i, v⟫ b i`. -/
theorem rpow_apply_basis {ι : Type*} [Fintype ι] {X : E →L[ℂ] E} (hX : 0 ≤ X)
    (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (hb : ∀ i, X (b i) = (lam i : ℂ) • b i)
    (s : ℝ) (v : E) :
    (X ^ s) v = ∑ i, ((lam i ^ s : ℝ) : ℂ) • (⟪b i, v⟫_ℂ • b i) := by
  conv_lhs => rw [← b.sum_repr' v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, rpow_apply_eigen hX (hb i) s, smul_comm]

/-! ## Algebraic identities for real powers, checked on an eigenbasis -/

/-- A nonnegative operator has an orthonormal eigenbasis with nonnegative eigenvalues. -/
lemma exists_eigenbasis_of_nonneg {X : E →L[ℂ] E} (hX : 0 ≤ X) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
      (lam : Fin (Module.finrank ℂ E) → ℝ),
      (∀ i, X (b i) = (lam i : ℂ) • b i) ∧ ∀ i, 0 ≤ lam i := by
  have hT : (X : E →ₗ[ℂ] E).IsPositive :=
    ((ContinuousLinearMap.nonneg_iff_isPositive X).mp hX).toLinearMap
  exact ⟨hT.isSymmetric.eigenvectorBasis rfl, hT.isSymmetric.eigenvalues rfl,
    fun i => hT.isSymmetric.apply_eigenvectorBasis rfl i, fun i => hT.nonneg_eigenvalues rfl i⟩

/-- `X * X` is nonnegative for nonnegative `X`. -/
lemma mul_self_nonneg_of_nonneg {X : E →L[ℂ] E} (hX : 0 ≤ X) : 0 ≤ X * X := by
  have h := star_mul_self_nonneg X
  rwa [(IsSelfAdjoint.of_nonneg hX).star_eq] at h

/-- `(X * X) ^ s = X ^ s * X ^ s` for nonnegative `X`. -/
lemma mul_self_rpow {X : E →L[ℂ] E} (hX : 0 ≤ X) (s : ℝ) : (X * X) ^ s = X ^ s * X ^ s := by
  obtain ⟨b, lam, hb, hlam⟩ := exists_eigenbasis_of_nonneg hX
  refine ext_orthonormalBasis b fun i => ?_
  have hbi : (X * X) (b i) = ((lam i * lam i : ℝ) : ℂ) • b i := by
    rw [mul_apply_eq_comp, hb i, map_smul, hb i, smul_smul, Complex.ofReal_mul]
  rw [rpow_apply_eigen (mul_self_nonneg_of_nonneg hX) hbi, mul_apply_eq_comp,
    rpow_apply_eigen hX (hb i), map_smul, rpow_apply_eigen hX (hb i), smul_smul,
    Real.mul_rpow (hlam i) (hlam i), Complex.ofReal_mul]

/-- `((c : ℂ) • Y) ^ s = c ^ s • Y ^ s` for `c ≥ 0` and nonnegative `Y`. -/
lemma ofReal_smul_rpow {Y : E →L[ℂ] E} (hY : 0 ≤ Y) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) :
    ((c : ℂ) • Y) ^ s = ((c ^ s : ℝ) : ℂ) • Y ^ s := by
  obtain ⟨b, lam, hb, hlam⟩ := exists_eigenbasis_of_nonneg hY
  refine ext_orthonormalBasis b fun i => ?_
  have hbi : ((c : ℂ) • Y) (b i) = ((c * lam i : ℝ) : ℂ) • b i := by
    rw [smul_apply, hb i, smul_smul, Complex.ofReal_mul]
  rw [rpow_apply_eigen (ofReal_smul_nonneg hY hc) hbi, smul_apply, rpow_apply_eigen hY (hb i),
    smul_smul, Real.mul_rpow hc (hlam i), Complex.ofReal_mul]

/-! ## Loewner order versus norm comparison -/

/-- For self-adjoint `A`, `re ⟪A * A v, v⟫ = ‖A v‖ ^ 2`. -/
lemma re_inner_mul_self_apply {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (v : E) :
    RCLike.re ⟪(A * A) v, v⟫_ℂ = ‖A v‖ ^ 2 := by
  rw [mul_apply_eq_comp, hA.isSymmetric.apply_clm (A v) v, inner_self_eq_norm_sq]

/-- The square of a self-adjoint operator is self-adjoint. -/
lemma isSelfAdjoint_mul_self {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) : IsSelfAdjoint (A * A) := by
  rw [IsSelfAdjoint, star_mul, hA.star_eq]

/-- For self-adjoint `A`, `B`: `A * A ≤ B * B` in the Loewner order iff `‖A v‖ ≤ ‖B v‖` for
all `v`. -/
lemma mul_self_le_mul_self_iff {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    A * A ≤ B * B ↔ ∀ v, ‖A v‖ ≤ ‖B v‖ := by
  have key : ∀ v, RCLike.re ⟪(B * B - A * A) v, v⟫_ℂ = ‖B v‖ ^ 2 - ‖A v‖ ^ 2 := fun v => by
    rw [sub_apply, inner_sub_left, map_sub, re_inner_mul_self_apply hB,
      re_inner_mul_self_apply hA]
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_def']
  constructor
  · rintro ⟨-, h⟩ v
    have hv := h v
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, key, sub_nonneg] at hv
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hv
  · intro h
    refine ⟨(isSelfAdjoint_mul_self hB).sub (isSelfAdjoint_mul_self hA), fun v => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, key, sub_nonneg]
    exact pow_le_pow_left₀ (norm_nonneg _) (h v) 2

/-! ## Löwner–Heinz -/

/-- **Löwner–Heinz, norm form.** If `0 ≤ X`, `0 ≤ Y`, `0 ≤ C` and `‖X v‖ ≤ C ‖Y v‖` for all `v`,
then `‖X ^ s v‖ ≤ C ^ s ‖Y ^ s v‖` for all `v` and all `s ∈ [0, 1]`. -/
theorem norm_rpow_le_of_norm_le {X Y : E →L[ℂ] E} (hX : 0 ≤ X) (hY : 0 ≤ Y) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ v, ‖X v‖ ≤ C * ‖Y v‖) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ v, ‖(X ^ s) v‖ ≤ C ^ s * ‖(Y ^ s) v‖ := by
  have hB : 0 ≤ (C : ℂ) • Y := ofReal_smul_nonneg hY hC
  have hXB : ∀ v, ‖X v‖ ≤ ‖((C : ℂ) • Y) v‖ := fun v => by
    rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]
    exact h v
  have hle : (X * X) ^ s ≤ ((C : ℂ) • Y * ((C : ℂ) • Y)) ^ s :=
    CFC.rpow_le_rpow hs ((mul_self_le_mul_self_iff (IsSelfAdjoint.of_nonneg hX)
      (IsSelfAdjoint.of_nonneg hB)).mpr hXB)
  rw [mul_self_rpow hX, mul_self_rpow hB, mul_self_le_mul_self_iff
    (IsSelfAdjoint.of_nonneg (CFC.rpow_nonneg (a := X) (y := s)))
    (IsSelfAdjoint.of_nonneg (CFC.rpow_nonneg (a := (C : ℂ) • Y) (y := s)))] at hle
  intro v
  have hv := hle v
  rwa [ofReal_smul_rpow hY hC, smul_apply, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hC s)] at hv

end FiniteDimensional

/-! ## Eigenbasis form -/

section EigenPow

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The eigenbasis power `ePow b x s v = ∑ i, (x i) ^ s ⟪b i, v⟫ b i`: the `s`-th power of the
operator with orthonormal eigenbasis `b` and eigenvalues `x`, applied to `v`. -/
noncomputable def ePow (b : OrthonormalBasis ι ℂ E) (x : ι → ℝ) (s : ℝ) (v : E) : E :=
  ∑ i, ((x i ^ s : ℝ) : ℂ) • (⟪b i, v⟫_ℂ • b i)

/-- At `s = 1`, `ePow` is the operator with eigenbasis `b` and eigenvalues `x` itself. -/
lemma ePow_one (b : OrthonormalBasis ι ℂ E) (x : ι → ℝ) (v : E) :
    ePow b x 1 v = ∑ i, (x i : ℂ) • (⟪b i, v⟫_ℂ • b i) := by
  simp only [ePow, Real.rpow_one]

/-- At `s = 0`, `ePow` is the identity. -/
lemma ePow_zero (b : OrthonormalBasis ι ℂ E) (x : ι → ℝ) (v : E) : ePow b x 0 v = v := by
  simp only [ePow, Real.rpow_zero, Complex.ofReal_one, one_smul]
  exact b.sum_repr' v

/-- The basis vectors are eigenvectors of `ePow b x s`, with eigenvalues `(x j) ^ s`. -/
lemma ePow_basis (b : OrthonormalBasis ι ℂ E) (x : ι → ℝ) (s : ℝ) (j : ι) :
    ePow b x s (b j) = ((x j ^ s : ℝ) : ℂ) • b j := by
  rw [ePow, Finset.sum_eq_single j]
  · rw [b.inner_eq_one, one_smul]
  · intro i _ hij
    rw [b.inner_eq_zero hij, zero_smul, smul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Coefficients of `ePow b x s v` in the basis `b`. -/
lemma inner_ePow (b : OrthonormalBasis ι ℂ E) (x : ι → ℝ) (s : ℝ) (v : E) (j : ι) :
    ⟪b j, ePow b x s v⟫_ℂ = ((x j ^ s : ℝ) : ℂ) * ⟪b j, v⟫_ℂ := by
  rw [ePow, inner_sum, Finset.sum_eq_single j]
  · rw [inner_smul_right, inner_smul_right, b.inner_eq_one, mul_one]
  · intro i _ hij
    rw [inner_smul_right, inner_smul_right, b.inner_eq_zero (Ne.symm hij), mul_zero, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- Norm-squared (Parseval) formula for `ePow`. -/
lemma norm_sq_ePow (b : OrthonormalBasis ι ℂ E) (x : ι → ℝ) (s : ℝ) (v : E) :
    ‖ePow b x s v‖ ^ 2 = ∑ i, (x i ^ s) ^ 2 * ‖⟪b i, v⟫_ℂ‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right (ePow b x s v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_ePow, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- `ePow b x s` as a continuous linear map (a combination of rank-one projections). -/
noncomputable def ePowL (b : OrthonormalBasis ι ℂ E) (x : ι → ℝ) (s : ℝ) : E →L[ℂ] E :=
  ∑ i, ((x i ^ s : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ (b i) (b i)

/-- `ePowL b x s` applies as `ePow b x s`. -/
lemma ePowL_apply (b : OrthonormalBasis ι ℂ E) (x : ι → ℝ) (s : ℝ) (v : E) :
    ePowL b x s v = ePow b x s v := by
  simp only [ePowL, ePow, sum_apply, smul_apply, InnerProductSpace.rankOne_apply]

/-- `ePowL b x s` is nonnegative (Loewner order) when all `x i ≥ 0`. -/
lemma ePowL_nonneg (b : OrthonormalBasis ι ℂ E) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (s : ℝ) :
    0 ≤ ePowL b x s := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ContinuousLinearMap.isPositive_sum _ fun i _ => ?_
  exact (InnerProductSpace.isPositive_rankOne_self (b i)).smul_of_nonneg
    (Complex.zero_le_real.mpr (Real.rpow_nonneg (hx i) s))

/-- The basis vectors are eigenvectors of `ePowL b x 1`, with eigenvalues `x j`. -/
lemma ePowL_one_apply_basis (b : OrthonormalBasis ι ℂ E) (x : ι → ℝ) (j : ι) :
    ePowL b x 1 (b j) = (x j : ℂ) • b j := by
  rw [ePowL_apply, ePow_basis, Real.rpow_one]

variable [FiniteDimensional ℂ E]

/-- `ePow b x s` is the real power `(ePowL b x 1) ^ s` (for `x ≥ 0`). -/
lemma ePowL_one_rpow_apply (b : OrthonormalBasis ι ℂ E) {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i)
    (s : ℝ) (v : E) : (ePowL b x 1 ^ s) v = ePow b x s v :=
  rpow_apply_basis (ePowL_nonneg b hx 1) b x (ePowL_one_apply_basis b x) s v

/-- **Löwner–Heinz, eigenbasis form.** For orthonormal bases `b`, `f` and nonnegative
eigenvalue families `x`, `y`: if `‖ePow b x 1 v‖ ≤ C ‖ePow f y 1 v‖` for all `v` (with
`C ≥ 0`), then `‖ePow b x s v‖ ≤ C ^ s ‖ePow f y s v‖` for all `v` and `s ∈ [0, 1]`. -/
theorem norm_ePow_le_of_norm_ePow_le (b : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    {x : ι → ℝ} {y : κ → ℝ} (hx : ∀ i, 0 ≤ x i) (hy : ∀ k, 0 ≤ y k) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v, ‖ePow b x 1 v‖ ≤ C * ‖ePow f y 1 v‖) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∀ v, ‖ePow b x s v‖ ≤ C ^ s * ‖ePow f y s v‖ := by
  intro v
  rw [← ePowL_one_rpow_apply b hx s v, ← ePowL_one_rpow_apply f hy s v]
  refine norm_rpow_le_of_norm_le (ePowL_nonneg b hx 1) (ePowL_nonneg f hy 1) hC
    (fun w => ?_) hs v
  rw [ePowL_apply, ePowL_apply]
  exact h w

end EigenPow

end FluxSourceTest
