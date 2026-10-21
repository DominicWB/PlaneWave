import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Flux/source build, block 1a: the abstract spectral layer

First file of the flux/source build against the revised manuscript
(`plane_wave_error_bounds_flux_source_review.tex`, kept as `scope/rev/manuscript_rev.tex`; see
`dev/propagator_plan.md`, section "Flux/source build").  Everything here lives on an abstract
finite-dimensional complex inner product space; the Galerkin space `ran P` is an instance.

* `fc b lam f`: the functional calculus `f(H) v = Σ_i f(λ_i) ⟪b_i, v⟫ b_i` along an orthonormal
  eigenbasis `b` with eigenvalues `λ`; norms, composition, linearity.
* `specleak`: `lem:specleak` (eq:specleak).  If `H' = T + V'` with `‖V' v‖ ≤ C_V ‖(1+A)^{1/2} v‖`
  and `u` has kinetic support in `A ≤ β`, then `‖1{H' ≥ a} u‖ ≤ C_V/(a-β) ‖(1+A)^{1/2} u‖`.

The proof is the manuscript's: the eigenvector identity `(λ - μ)⟪e_λ, f_μ⟫ = ⟪e_λ, V' f_μ⟫`
and `(λ - μ)⁻¹ = ∫_0^∞ e^{-s(λ-μ)} ds`, in the weak form (pairing with `1{H' ≥ a} u` itself), so
that only scalar integrals of finite exponential sums occur.

Mathlib only; no dependence on the release file.
-/

set_option autoImplicit false

open MeasureTheory Complex Set
open scoped InnerProductSpace Real ComplexConjugate

namespace FSSpectral

/-! ## The functional calculus along an orthonormal eigenbasis -/

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [Fintype ι]

/-- `f(H) v = Σ_i f(λ_i) ⟪b_i, v⟫ b_i` for an orthonormal eigenbasis `b` with eigenvalues `lam`. -/
noncomputable def fc (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (f : ℝ → ℂ) (v : E) : E :=
  ∑ i, (f (lam i) * ⟪b i, v⟫_ℂ) • b i

variable (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ)

lemma inner_basis_fc (f : ℝ → ℂ) (v : E) (j : ι) :
    ⟪b j, fc b lam f v⟫_ℂ = f (lam j) * ⟪b j, v⟫_ℂ := by
  classical
  unfold fc
  rw [inner_sum]
  simp_rw [inner_smul_right, b.inner_eq_ite]
  simp

lemma norm_sq_fc (f : ℝ → ℂ) (v : E) :
    ‖fc b lam f v‖ ^ 2 = ∑ i, ‖f (lam i)‖ ^ 2 * ‖⟪b i, v⟫_ℂ‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right (fc b lam f v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_basis_fc, norm_mul, mul_pow]

lemma fc_one (v : E) : fc b lam (fun _ => 1) v = v := by
  unfold fc
  simp only [one_mul]
  exact b.sum_repr' v

lemma fc_add (f : ℝ → ℂ) (v w : E) : fc b lam f (v + w) = fc b lam f v + fc b lam f w := by
  unfold fc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_add_right, mul_add, add_smul]

lemma fc_smul (f : ℝ → ℂ) (c : ℂ) (v : E) : fc b lam f (c • v) = c • fc b lam f v := by
  unfold fc
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, smul_smul]
  ring_nf

lemma fc_neg (f : ℝ → ℂ) (w : E) : fc b lam f (-w) = -fc b lam f w := by
  rw [← neg_one_smul ℂ w, fc_smul, neg_one_smul]

lemma fc_sub (f : ℝ → ℂ) (v w : E) : fc b lam f (v - w) = fc b lam f v - fc b lam f w := by
  rw [sub_eq_add_neg, fc_add, fc_neg, ← sub_eq_add_neg]

lemma fc_comp (f g : ℝ → ℂ) (v : E) :
    fc b lam f (fc b lam g v) = fc b lam (fun x => f x * g x) v := by
  unfold fc
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← fc, inner_basis_fc, mul_assoc]

lemma fc_congr {f g : ℝ → ℂ} (h : ∀ i, f (lam i) = g (lam i)) (v : E) :
    fc b lam f v = fc b lam g v := by
  unfold fc
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i]

/-- An operator with eigenbasis `b` acts by `x ↦ x` in the calculus. -/
lemma apply_fc_of_eigen (H : E →ₗ[ℂ] E) (hb : ∀ i, H (b i) = (lam i : ℂ) • b i) (f : ℝ → ℂ)
    (v : E) : H (fc b lam f v) = fc b lam (fun x => (x : ℂ) * f x) v := by
  unfold fc
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hb i, smul_smul]
  ring_nf

lemma eigen_fc_id (H : E →ₗ[ℂ] E) (hb : ∀ i, H (b i) = (lam i : ℂ) • b i) (v : E) :
    H v = fc b lam (fun x => (x : ℂ)) v := by
  conv_lhs => rw [← fc_one b lam v]
  rw [apply_fc_of_eigen b lam H hb]
  simp

/-- The basis vectors are eigenvectors of every function of the operator. -/
lemma fc_basis [DecidableEq ι] (f : ℝ → ℂ) (j : ι) : fc b lam f (b j) = f (lam j) • b j := by
  unfold fc
  simp_rw [b.inner_eq_ite]
  simp

lemma norm_fc_le {f : ℝ → ℂ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ i, ‖f (lam i)‖ ≤ M) (v : E) :
    ‖fc b lam f v‖ ≤ M * ‖v‖ := by
  have h2 : ‖fc b lam f v‖ ^ 2 ≤ (M * ‖v‖) ^ 2 := by
    rw [norm_sq_fc, mul_pow, ← b.sum_sq_norm_inner_right v, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hf i) 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

end Calculus


/-! ## Spectral leakage of a kinetically localised vector (`lem:specleak`) -/

section Specleak

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The kinetic operator `T v = Σ_k A_k ⟪f_k, v⟫ f_k`. -/
noncomputable def kin (f : OrthonormalBasis κ ℂ E) (A : κ → ℝ) (v : E) : E :=
  fc f A (fun x => (x : ℂ)) v

/-- The kinetic weight `(1 + A)^s`. -/
noncomputable def wt (f : OrthonormalBasis κ ℂ E) (A : κ → ℝ) (s : ℝ) (v : E) : E :=
  fc f A (fun x => (((1 + x) ^ s : ℝ) : ℂ)) v

/-- The spectral projection `1{H ≥ a}` of the operator with eigenbasis `(b, lam)`. -/
noncomputable def specGe (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (a : ℝ) (v : E) : E :=
  fc b lam (fun x => if a ≤ x then 1 else 0) v

/-- The eigenvector identity `⟪e_λ, V f_μ⟫ = (λ - μ) ⟪e_λ, f_μ⟫` for `H = T + V`. -/
lemma inner_V_basis [DecidableEq κ] (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (A : κ → ℝ) (H V : E →ₗ[ℂ] E) (hH : H.IsSymmetric)
    (hb : ∀ i, H (b i) = (lam i : ℂ) • b i) (hHV : ∀ v, H v = kin f A v + V v) (i : ι) (k : κ) :
    ⟪b i, V (f k)⟫_ℂ = ((lam i - A k : ℝ) : ℂ) * ⟪b i, f k⟫_ℂ := by
  have h1 : V (f k) = H (f k) - (A k : ℂ) • f k := by
    rw [hHV, kin, fc_basis]; abel
  have h2 : ⟪b i, H (f k)⟫_ℂ = (lam i : ℂ) * ⟪b i, f k⟫_ℂ := by
    rw [← hH (b i) (f k), hb i, inner_smul_left, Complex.conj_ofReal]
  rw [h1, inner_sub_right, h2, inner_smul_right]
  push_cast
  ring

/-- Pairing of two calculus vectors through `V`, expanded in the two bases. -/
lemma inner_fc_V_fc (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (f : OrthonormalBasis κ ℂ E)
    (A : κ → ℝ) (V : E →ₗ[ℂ] E) (g : ℝ → ℝ) (h : ℝ → ℂ) (u : E) :
    ⟪fc b lam (fun x => (g x : ℂ)) u, V (fc f A h u)⟫_ℂ =
      ∑ i, ∑ k, ((g (lam i) : ℂ) * conj ⟪b i, u⟫_ℂ) * (h (A k) * ⟪f k, u⟫_ℂ) *
        ⟪b i, V (f k)⟫_ℂ := by
  unfold fc
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, inner_smul_left, inner_smul_right, map_mul, Complex.conj_ofReal]
  ring

/-- `∫_0^∞ e^{-κ s} ds = 1/κ` in complex form. -/
lemma integral_cexp_neg_Ioi {κ : ℝ} (hκ : 0 < κ) :
    ∫ s in Ioi (0 : ℝ), Complex.exp (-(κ : ℂ) * s) = 1 / (κ : ℂ) := by
  have h := integral_exp_mul_complex_Ioi (a := -(κ : ℂ)) (by simpa using hκ) 0
  rw [h]
  have : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  field_simp
  simp

lemma integrableOn_cexp_neg_Ioi {κ : ℝ} (hκ : 0 < κ) :
    IntegrableOn (fun s : ℝ => Complex.exp (-(κ : ℂ) * s)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using hκ) 0

/-- **`lem:specleak`** (eq:specleak).  Let `H = T + V` be symmetric with orthonormal eigenbasis
`(b, lam)`, `T` the kinetic operator of the orthonormal basis `f` with symbol `A ≥ 0`, and
`‖V v‖ ≤ C_V ‖(1+A)^{1/2} v‖` for all `v`.  If `u` has kinetic support in `A ≤ β` and `β < a`,
then `‖1{H ≥ a} u‖ ≤ C_V/(a - β) ‖(1+A)^{1/2} u‖`. -/
theorem specleak [DecidableEq κ] (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (A : κ → ℝ) (H V : E →ₗ[ℂ] E)
    (hH : H.IsSymmetric) (hb : ∀ i, H (b i) = (lam i : ℂ) • b i)
    (hHV : ∀ v, H v = kin f A v + V v) {CV : ℝ} (hCV : 0 ≤ CV)
    (hV : ∀ v, ‖V v‖ ≤ CV * ‖wt f A (1 / 2) v‖) {a β : ℝ} (hab : β < a) (u : E)
    (hu : ∀ k, β < A k → ⟪f k, u⟫_ℂ = 0) :
    ‖specGe b lam a u‖ ≤ CV / (a - β) * ‖wt f A (1 / 2) u‖ := by
  set N := ‖specGe b lam a u‖ with hN
  set W := ‖wt f A (1 / 2) u‖ with hW
  have hδ : 0 < a - β := sub_pos.mpr hab
  -- the two auxiliary vectors
  let g : ℝ → ℝ → ℝ := fun s x => if a ≤ x then Real.exp (-(s * x)) else 0
  let h : ℝ → ℝ → ℂ := fun s x => if x ≤ β then ((Real.exp (s * x) : ℝ) : ℂ) else 0
  let G : ℝ → ℂ := fun s => ⟪fc b lam (fun x => (g s x : ℂ)) u, V (fc f A (h s) u)⟫_ℂ
  -- (1) the integral of `G` is `N²`
  have hcoef : ∀ i, ⟪b i, u⟫_ℂ = ∑ k, ⟪b i, f k⟫_ℂ * ⟪f k, u⟫_ℂ := by
    intro i
    conv_lhs => rw [← f.sum_repr' u]
    rw [inner_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_right, mul_comm]
  have hterm : ∀ i k, (fun s : ℝ => ((g s (lam i) : ℂ) * conj ⟪b i, u⟫_ℂ) *
      (h s (A k) * ⟪f k, u⟫_ℂ) * ⟪b i, V (f k)⟫_ℂ) =
      fun s : ℝ => (if a ≤ lam i ∧ A k ≤ β then
        conj ⟪b i, u⟫_ℂ * ⟪f k, u⟫_ℂ * ⟪b i, V (f k)⟫_ℂ else 0) *
        Complex.exp (-((lam i - A k : ℝ) : ℂ) * (s : ℂ)) := by
    intro i k
    funext s
    simp only [g, h]
    by_cases hi : a ≤ lam i
    · by_cases hk : A k ≤ β
      · rw [if_pos hi, if_pos hk, if_pos ⟨hi, hk⟩]
        have : ((Real.exp (-(s * lam i)) : ℝ) : ℂ) * ((Real.exp (s * A k) : ℝ) : ℂ) =
            Complex.exp (-((lam i - A k : ℝ) : ℂ) * s) := by
          rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
          congr 1; push_cast; ring
        rw [← this]; ring
      · rw [if_neg hk, if_neg (show ¬(a ≤ lam i ∧ A k ≤ β) from fun hh => hk hh.2)]; ring
    · rw [if_neg hi, if_neg (show ¬(a ≤ lam i ∧ A k ≤ β) from fun hh => hi hh.1)]
      push_cast; ring
  have hint : ∀ i k, IntegrableOn (fun s : ℝ => (if a ≤ lam i ∧ A k ≤ β then
        conj ⟪b i, u⟫_ℂ * ⟪f k, u⟫_ℂ * ⟪b i, V (f k)⟫_ℂ else 0) *
        Complex.exp (-((lam i - A k : ℝ) : ℂ) * s)) (Ioi 0) := by
    intro i k
    by_cases hik : a ≤ lam i ∧ A k ≤ β
    · have hκ : 0 < lam i - A k := by linarith [hik.1, hik.2]
      exact (integrableOn_cexp_neg_Ioi hκ).const_mul _
    · simp only [if_neg hik, zero_mul]
      exact integrableOn_zero
  have hGint : ∫ s in Ioi (0 : ℝ), G s = ((N ^ 2 : ℝ) : ℂ) := by
    have hGexp : G = fun s : ℝ => ∑ i, ∑ k, (if a ≤ lam i ∧ A k ≤ β then
        conj ⟪b i, u⟫_ℂ * ⟪f k, u⟫_ℂ * ⟪b i, V (f k)⟫_ℂ else 0) *
        Complex.exp (-((lam i - A k : ℝ) : ℂ) * (s : ℂ)) := by
      funext s
      simp only [G]
      rw [inner_fc_V_fc]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      exact congrFun (hterm i k) s
    rw [hGexp, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint i k]
    have hk_sum : ∀ i, ∫ s in Ioi (0 : ℝ), ∑ k, (if a ≤ lam i ∧ A k ≤ β then
        conj ⟪b i, u⟫_ℂ * ⟪f k, u⟫_ℂ * ⟪b i, V (f k)⟫_ℂ else 0) *
        Complex.exp (-((lam i - A k : ℝ) : ℂ) * s) =
        (if a ≤ lam i then conj ⟪b i, u⟫_ℂ * ∑ k, ⟪b i, f k⟫_ℂ * ⟪f k, u⟫_ℂ else 0) := by
      intro i
      rw [integral_finsetSum _ fun k _ => hint i k]
      by_cases hi : a ≤ lam i
      · rw [if_pos hi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : A k ≤ β
        · have hκ : 0 < lam i - A k := by linarith
          rw [if_pos ⟨hi, hk⟩, integral_const_mul, integral_cexp_neg_Ioi hκ,
            inner_V_basis b lam f A H V hH hb hHV i k]
          have hne : ((lam i - A k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
          field_simp
        · have hk' : β < A k := lt_of_not_ge hk
          rw [if_neg (show ¬(a ≤ lam i ∧ A k ≤ β) from fun hh => hk hh.2), hu k hk']
          simp
      · rw [if_neg hi]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [if_neg (show ¬(a ≤ lam i ∧ A k ≤ β) from fun hh => hi hh.1)]
        simp
    simp_rw [hk_sum]
    have hNsq : N ^ 2 = ∑ i, (if a ≤ lam i then ‖⟪b i, u⟫_ℂ‖ ^ 2 else 0) := by
      rw [hN, specGe, norm_sq_fc]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    rw [hNsq]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · rw [← hcoef i, Complex.conj_mul']
      norm_cast
    · simp
  -- (2) the pointwise bound `‖G s‖ ≤ N C_V W e^{-(a-β)s}` for `s ≥ 0`
  have hbound : ∀ s, 0 ≤ s → ‖G s‖ ≤ N * CV * W * Real.exp (-(a - β) * s) := by
    intro s hs
    have hw : ‖fc b lam (fun x => (g s x : ℂ)) u‖ ≤ Real.exp (-(s * a)) * N := by
      have h2 : ‖fc b lam (fun x => (g s x : ℂ)) u‖ ^ 2 ≤ (Real.exp (-(s * a)) * N) ^ 2 := by
        rw [mul_pow, hN, specGe, norm_sq_fc, norm_sq_fc, Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [g]
        by_cases hi : a ≤ lam i
        · rw [if_pos hi, if_pos hi, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _), norm_one, one_pow, one_mul]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact pow_le_pow_left₀ (Real.exp_pos _).le
            (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hi hs))) 2
        · rw [if_neg hi, if_neg hi]; simp
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
    have hus : ‖wt f A (1 / 2) (fc f A (h s) u)‖ ≤ Real.exp (s * β) * W := by
      have h2 : ‖wt f A (1 / 2) (fc f A (h s) u)‖ ^ 2 ≤ (Real.exp (s * β) * W) ^ 2 := by
        rw [wt, fc_comp, mul_pow, hW, wt, norm_sq_fc, norm_sq_fc, Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        simp only [h]
        by_cases hk : A k ≤ β
        · rw [if_pos hk, norm_mul, mul_pow, Complex.norm_real (Real.exp (s * A k)),
            Real.norm_of_nonneg (Real.exp_pos _).le]
          have hexp : Real.exp (s * A k) ^ 2 ≤ Real.exp (s * β) ^ 2 :=
            pow_le_pow_left₀ (Real.exp_pos _).le
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk hs)) 2
          calc _ = Real.exp (s * A k) ^ 2 *
                (‖(((1 + A k) ^ (1 / 2 : ℝ) : ℝ) : ℂ)‖ ^ 2 * ‖⟪f k, u⟫_ℂ‖ ^ 2) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hexp (by positivity)
        · rw [hu k (lt_of_not_ge hk)]; simp
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
    calc ‖G s‖ ≤ ‖fc b lam (fun x => (g s x : ℂ)) u‖ * ‖V (fc f A (h s) u)‖ :=
          norm_inner_le_norm _ _
      _ ≤ (Real.exp (-(s * a)) * N) * (CV * (Real.exp (s * β) * W)) := by
          refine mul_le_mul hw ((hV _).trans (mul_le_mul_of_nonneg_left hus hCV))
            (norm_nonneg _) (by positivity)
      _ = N * CV * W * (Real.exp (-(s * a)) * Real.exp (s * β)) := by ring
      _ = N * CV * W * Real.exp (-(a - β) * s) := by
          rw [← Real.exp_add]; congr 2; ring
  -- (3) integrate the bound
  have hexp_int : IntegrableOn (fun s : ℝ => N * CV * W * Real.exp (-(a - β) * s)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  have hval : ∫ s in Ioi (0 : ℝ), N * CV * W * Real.exp (-(a - β) * s) = N * CV * W / (a - β) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
    field_simp
    simp
  have hmain : N ^ 2 ≤ N * CV * W / (a - β) := by
    have h1 : ‖∫ s in Ioi (0 : ℝ), G s‖ ≤ ∫ s in Ioi (0 : ℝ), N * CV * W * Real.exp (-(a - β) * s) :=
      norm_integral_le_of_norm_le hexp_int
        ((ae_restrict_mem measurableSet_Ioi).mono fun s hs => hbound s (le_of_lt hs))
    rw [hGint, hval, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg N)] at h1
    exact h1
  rcases (norm_nonneg (specGe b lam a u)).eq_or_lt with h0 | hpos
  · rw [hN, ← h0]; positivity
  · have hpos' : 0 < N := hpos
    have : N ≤ CV * W / (a - β) := by
      have := hmain
      rw [pow_two, mul_assoc, mul_div_assoc] at this
      exact le_of_mul_le_mul_left (by linarith [this]) hpos' |>.trans_eq (by ring)
    calc N ≤ CV * W / (a - β) := this
      _ = CV / (a - β) * W := by ring

end Specleak


/-! ## Time averaging (`lem:tavg`)

Copied from the scoping prototype `dev/DevFS2.lean` (Mathlib-only part), generalised from `Fin n` to
an arbitrary finite index type, so that this layer does not depend on the release file.
-/

section Tavg

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι : Type*} [Fintype ι] (lam : ι → ℝ) (y : ι → F)

/-- `C e^{iHτ} u = Σ_k e^{iλ_k τ} y_k`. -/
noncomputable def flowVec (τ : ℝ) : F :=
  ∑ k, Complex.exp (Complex.I * (lam k : ℂ) * τ) • y k

/-- `C w_x = Σ_k e^{-t²(λ_k - x)²/2} y_k`. -/
noncomputable def gaussVec (t x : ℝ) : F :=
  ∑ k, ((Real.exp (-(t ^ 2 * (lam k - x) ^ 2) / 2) : ℝ) : ℂ) • y k

/-- The Gaussian Fourier integral in the form used: `∫ e^{-τ²/t²} e^{iξτ} dτ = √(π t²) e^{-t²ξ²/4}`. -/
lemma integral_gauss_phase {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    ∫ τ : ℝ, Complex.exp (-(1 / (t : ℂ) ^ 2) * (τ : ℂ) ^ 2 + (Complex.I * ξ) * τ + 0) =
      ((π * t ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(t ^ 2 * ξ ^ 2 / 4 : ℝ)) := by
  have hb : (-(1 / (t : ℂ) ^ 2)).re < 0 := by
    have : (1 / (t : ℂ) ^ 2) = ((1 / t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, neg_re, ofReal_re]
    have : 0 < 1 / t ^ 2 := by positivity
    linarith
  rw [integral_cexp_quadratic hb]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  congr 1
  · congr 1
    push_cast
    field_simp
  · congr 1
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring

/-- The overlap integral `∫ e^{-t²(a-x)²/2} e^{-t²(b-x)²/2} dx = √(π/t²) e^{-t²(a-b)²/4}`. -/
lemma integral_gauss_overlap {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    ∫ x : ℝ, Complex.exp (-((t : ℂ) ^ 2) * (x : ℂ) ^ 2 + ((t : ℂ) ^ 2 * (a + b)) * x +
        (-((t : ℂ) ^ 2 * (a ^ 2 + b ^ 2) / 2))) =
      ((π / t ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(t ^ 2 * (a - b) ^ 2 / 4 : ℝ)) := by
  have hb : (-((t : ℂ) ^ 2)).re < 0 := by
    have : ((t : ℂ) ^ 2) = ((t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, neg_re, ofReal_re]
    have : 0 < t ^ 2 := by positivity
    linarith
  rw [integral_cexp_quadratic hb]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    push_cast
    field_simp
    ring

/-! ### Expansions of the two squared norms -/

lemma inner_sum_smul (a b : ι → ℂ) :
    ⟪∑ k, a k • y k, ∑ l, b l • y l⟫_ℂ = ∑ k, ∑ l, (starRingEnd ℂ) (a k) * b l * ⟪y k, y l⟫_ℂ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inner_smul_right]
  ring

lemma flowVec_inner (t τ : ℝ) :
    ((Real.exp (-(τ ^ 2 / t ^ 2)) : ℝ) : ℂ) * ⟪flowVec lam y τ, flowVec lam y τ⟫_ℂ =
      ∑ k, ∑ l, ⟪y k, y l⟫_ℂ *
        Complex.exp (-(1 / (t : ℂ) ^ 2) * (τ : ℂ) ^ 2 + (Complex.I * ((lam l - lam k : ℝ) : ℂ)) * τ + 0) := by
  unfold flowVec
  rw [inner_sum_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Complex.exp_conj, Complex.ofReal_exp]
  have h : (starRingEnd ℂ) (Complex.I * (lam k : ℂ) * τ) = -(Complex.I * (lam k : ℂ) * τ) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [h]
  have e : Complex.exp (((-(τ ^ 2 / t ^ 2) : ℝ) : ℂ)) * (Complex.exp (-(Complex.I * (lam k : ℂ) * τ)) *
      Complex.exp (Complex.I * (lam l : ℂ) * τ)) =
      Complex.exp (-(1 / (t : ℂ) ^ 2) * (τ : ℂ) ^ 2 +
        (Complex.I * ((lam l - lam k : ℝ) : ℂ)) * τ + 0) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← e]
  ring

lemma gaussVec_inner (t x : ℝ) :
    ⟪gaussVec lam y t x, gaussVec lam y t x⟫_ℂ =
      ∑ k, ∑ l, ⟪y k, y l⟫_ℂ *
        Complex.exp (-((t : ℂ) ^ 2) * (x : ℂ) ^ 2 + ((t : ℂ) ^ 2 * ((lam k : ℂ) + lam l)) * x +
          (-((t : ℂ) ^ 2 * ((lam k : ℂ) ^ 2 + (lam l : ℂ) ^ 2) / 2))) := by
  unfold gaussVec
  rw [inner_sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.conj_ofReal, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
  have e : (((-(t ^ 2 * (lam k - x) ^ 2) / 2 : ℝ)) : ℂ) + (((-(t ^ 2 * (lam l - x) ^ 2) / 2 : ℝ)) : ℂ) =
      -((t : ℂ) ^ 2) * (x : ℂ) ^ 2 + ((t : ℂ) ^ 2 * ((lam k : ℂ) + lam l)) * x +
        (-((t : ℂ) ^ 2 * ((lam k : ℂ) ^ 2 + (lam l : ℂ) ^ 2) / 2)) := by
    push_cast; ring
  rw [e]
  ring

/-! ### The identity -/

lemma ofReal_norm_sq_eq_inner (v : F) : ((‖v‖ ^ 2 : ℝ) : ℂ) = ⟪v, v⟫_ℂ := by
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

lemma sqrt_cpow_mul {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ 2 * ((π / t ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((π * t ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
  have h1 : ((π / t ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (π / t ^ 2) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast; rfl
  have h2 : ((π * t ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (π * t ^ 2) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast; rfl
  rw [h1, h2]
  have h3 : Real.sqrt (π / t ^ 2) = Real.sqrt π / t := by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq ht.le]
  have h4 : Real.sqrt (π * t ^ 2) = Real.sqrt π * t := by
    rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_sq ht.le]
  rw [h3, h4]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast
  field_simp

/-- **`lem:tavg`, the identity**: `∫ e^{-τ²/t²} ‖C e^{iHτ}u‖² dτ = t² ∫ ‖C w_x‖² dx`. -/
theorem tavg_identity {t : ℝ} (ht : 0 < t) :
    ∫ τ : ℝ, Real.exp (-(τ ^ 2 / t ^ 2)) * ‖flowVec lam y τ‖ ^ 2 =
      t ^ 2 * ∫ x : ℝ, ‖gaussVec lam y t x‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, Complex.ofReal_mul, ← integral_complex_ofReal]
  have hL : (fun τ : ℝ => (((Real.exp (-(τ ^ 2 / t ^ 2)) * ‖flowVec lam y τ‖ ^ 2 : ℝ)) : ℂ)) =
      fun τ : ℝ => ∑ k, ∑ l, ⟪y k, y l⟫_ℂ *
        Complex.exp (-(1 / (t : ℂ) ^ 2) * (τ : ℂ) ^ 2 +
          (Complex.I * ((lam l - lam k : ℝ) : ℂ)) * τ + 0) := by
    funext τ
    rw [← flowVec_inner, Complex.ofReal_mul, ofReal_norm_sq_eq_inner]
  have hR : (fun x : ℝ => ((‖gaussVec lam y t x‖ ^ 2 : ℝ) : ℂ)) =
      fun x : ℝ => ∑ k, ∑ l, ⟪y k, y l⟫_ℂ *
        Complex.exp (-((t : ℂ) ^ 2) * (x : ℂ) ^ 2 + ((t : ℂ) ^ 2 * ((lam k : ℂ) + lam l)) * x +
          (-((t : ℂ) ^ 2 * ((lam k : ℂ) ^ 2 + (lam l : ℂ) ^ 2) / 2))) := by
    funext x
    rw [← gaussVec_inner, ofReal_norm_sq_eq_inner]
  rw [hL, hR]
  have hb1 : (-(1 / (t : ℂ) ^ 2)).re < 0 := by
    have : (1 / (t : ℂ) ^ 2) = ((1 / t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, neg_re, ofReal_re]
    have : 0 < 1 / t ^ 2 := by positivity
    linarith
  have hb2 : (-((t : ℂ) ^ 2)).re < 0 := by
    have : ((t : ℂ) ^ 2) = ((t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, neg_re, ofReal_re]
    have : 0 < t ^ 2 := by positivity
    linarith
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (integrable_cexp_quadratic' hb1 _ _).const_mul _]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (integrable_cexp_quadratic' hb2 _ _).const_mul _]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => (integrable_cexp_quadratic' hb1 _ _).const_mul _]
  rw [integral_finsetSum _ fun l _ => (integrable_cexp_quadratic' hb2 _ _).const_mul _]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_const_mul, integral_gauss_phase ht,
    integral_gauss_overlap ht]
  have hsq : t ^ 2 * (lam l - lam k) ^ 2 / 4 = t ^ 2 * (lam k - lam l) ^ 2 / 4 := by ring
  rw [hsq, Complex.ofReal_pow]
  have key := sqrt_cpow_mul ht
  linear_combination (-(⟪y k, y l⟫_ℂ *
    Complex.exp (-((t ^ 2 * (lam k - lam l) ^ 2 / 4 : ℝ) : ℂ)))) * key

/-! ### The time-averaged bound and the normalisation -/

lemma norm_flowVec_le (τ : ℝ) : ‖flowVec lam y τ‖ ≤ ∑ k, ‖y k‖ := by
  unfold flowVec
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul]
  have : ‖Complex.exp (Complex.I * (lam k : ℂ) * τ)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [this, one_mul]

lemma continuous_flowVec : Continuous (flowVec lam y) := by
  unfold flowVec
  refine continuous_finsetSum _ fun k _ => ?_
  exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul
    continuous_const

lemma integrable_weighted_flow {t : ℝ} (ht : 0 < t) :
    Integrable fun τ : ℝ => Real.exp (-(τ ^ 2 / t ^ 2)) * ‖flowVec lam y τ‖ ^ 2 := by
  have hb : (0 : ℝ) < 1 / t ^ 2 := by positivity
  have hg := (integrable_exp_neg_mul_sq hb).const_mul ((∑ k, ‖y k‖) ^ 2)
  refine hg.mono' ?_ (Filter.Eventually.of_forall fun τ => ?_)
  · exact ((Real.continuous_exp.comp ((continuous_pow 2).div_const _).neg).mul
      ((continuous_flowVec lam y).norm.pow 2)).aestronglyMeasurable
  · have h1 : 0 ≤ Real.exp (-(τ ^ 2 / t ^ 2)) := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 (sq_nonneg _))]
    have h2 : ‖flowVec lam y τ‖ ^ 2 ≤ (∑ k, ‖y k‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_flowVec_le lam y τ) 2
    have h3 : Real.exp (-(τ ^ 2 / t ^ 2)) = Real.exp (-(1 / t ^ 2) * τ ^ 2) := by
      congr 1; ring
    rw [h3] at h1 ⊢
    nlinarith

/-- **`lem:tavg`, the bound**: `(1/t) ∫_0^t ‖C e^{iHτ}u‖² dτ ≤ e t ∫ ‖C w_x‖² dx`. -/
theorem tavg_bound {t : ℝ} (ht : 0 < t) :
    (1 / t) * ∫ τ in (0 : ℝ)..t, ‖flowVec lam y τ‖ ^ 2 ≤
      Real.exp 1 * t * ∫ x : ℝ, ‖gaussVec lam y t x‖ ^ 2 := by
  have hint := integrable_weighted_flow lam y ht
  have hstep : ∫ τ in (0 : ℝ)..t, ‖flowVec lam y τ‖ ^ 2 ≤
      Real.exp 1 * ∫ τ : ℝ, Real.exp (-(τ ^ 2 / t ^ 2)) * ‖flowVec lam y τ‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le ht.le, ← integral_const_mul]
    have hpt : ∀ τ ∈ Set.Ioc (0 : ℝ) t, ‖flowVec lam y τ‖ ^ 2 ≤
        Real.exp 1 * (Real.exp (-(τ ^ 2 / t ^ 2)) * ‖flowVec lam y τ‖ ^ 2) := by
      intro τ hτ
      have hτ2 : τ ^ 2 / t ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact pow_le_pow_left₀ hτ.1.le hτ.2 2
      have he : 1 ≤ Real.exp 1 * Real.exp (-(τ ^ 2 / t ^ 2)) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp (by linarith)
      have := sq_nonneg ‖flowVec lam y τ‖
      nlinarith
    calc ∫ τ in Set.Ioc (0 : ℝ) t, ‖flowVec lam y τ‖ ^ 2
        ≤ ∫ τ in Set.Ioc (0 : ℝ) t,
            Real.exp 1 * (Real.exp (-(τ ^ 2 / t ^ 2)) * ‖flowVec lam y τ‖ ^ 2) :=
          setIntegral_mono_on
            (((continuous_flowVec lam y).norm.pow 2).integrableOn_Icc.mono_set
              Set.Ioc_subset_Icc_self)
            (hint.const_mul _).integrableOn measurableSet_Ioc hpt
      _ ≤ ∫ τ : ℝ, Real.exp 1 * (Real.exp (-(τ ^ 2 / t ^ 2)) * ‖flowVec lam y τ‖ ^ 2) :=
          setIntegral_le_integral (hint.const_mul _) (Filter.Eventually.of_forall fun τ =>
            mul_nonneg (Real.exp_pos 1).le (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
  rw [tavg_identity lam y ht] at hstep
  have ht' : 0 < 1 / t := by positivity
  calc (1 / t) * ∫ τ in (0 : ℝ)..t, ‖flowVec lam y τ‖ ^ 2
      ≤ (1 / t) * (Real.exp 1 * (t ^ 2 * ∫ x : ℝ, ‖gaussVec lam y t x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hstep ht'.le
    _ = Real.exp 1 * t * ∫ x : ℝ, ‖gaussVec lam y t x‖ ^ 2 := by
        field_simp

end Tavg


/-! ## Gaussian spectral windows and the time-averaged bound (skeleton of `prop:tavgU`)

For `w_x = e^{-t²(H-x)²/2} u` (the vector of `lem:tavg`), split `w_x = w'_x + e_x` into its part in
the spectral window `|H - x| ≤ Δ` and the Gaussian tail.  The window part is a quasi-eigenstate
(`quasi_eigen_of_support`); the tail has integrated mass `t ∫ ‖e_x‖² ≤ √(2π) e^{-t²Δ²/2} ‖u‖²`
(the revised manuscript's integrated form).  `tavg_window_bound` then turns any bound on the
`C`-content of quasi-eigenstates below an energy `X` into a bound on the time-averaged
`C`-content of the flow `e^{iHτ} u`.  Unlike the manuscript we do not integrate the Gaussian moment
`(1 + x + C₀)^p` directly: inside the window `1 + x + C₀ ≤ (1 + Δ)(1 + λ + C₀)`, which costs the
harmless factor `(1 + Δ)^p` and leaves the spectral moment `Σ_i (1 + λ_i + C₀)^p |⟪b_i, u⟫|²`.
-/

section Windows

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [Fintype ι]
variable (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ)

/-- The Gaussian window `e^{-t²(λ-x)²/2}`. -/
noncomputable def gw (t x : ℝ) (l : ℝ) : ℂ := ((Real.exp (-(t ^ 2 * (l - x) ^ 2) / 2) : ℝ) : ℂ)

/-- Its part in the spectral window `|λ - x| ≤ Δ`. -/
noncomputable def gwIn (t x Δ : ℝ) (l : ℝ) : ℂ := if |l - x| ≤ Δ then gw t x l else 0

/-- Its Gaussian tail outside the window. -/
noncomputable def gwOut (t x Δ : ℝ) (l : ℝ) : ℂ := if |l - x| ≤ Δ then 0 else gw t x l

lemma fc_gw_split (t x Δ : ℝ) (u : E) :
    fc b lam (gw t x) u = fc b lam (gwIn t x Δ) u + fc b lam (gwOut t x Δ) u := by
  unfold fc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← add_smul, ← add_mul]
  unfold gwIn gwOut
  split_ifs <;> simp

lemma norm_gw_sq (t x l : ℝ) : ‖gw t x l‖ ^ 2 = Real.exp (-(t ^ 2 * (l - x) ^ 2)) := by
  unfold gw
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, sq, ← Real.exp_add]
  congr 1; ring

/-- A vector supported in a spectral window around `E₀` of width `γ` is a quasi-eigenstate. -/
lemma quasi_eigen_of_support (H : E →ₗ[ℂ] E) (hb : ∀ i, H (b i) = (lam i : ℂ) • b i)
    (g : ℝ → ℂ) {E₀ γ : ℝ} (hγ : 0 ≤ γ) (hsupp : ∀ i, g (lam i) ≠ 0 → |lam i - E₀| ≤ γ)
    (u : E) : ‖H (fc b lam g u) - (E₀ : ℂ) • fc b lam g u‖ ≤ γ * ‖fc b lam g u‖ := by
  have h1 : H (fc b lam g u) - (E₀ : ℂ) • fc b lam g u =
      fc b lam (fun x => ((x - E₀ : ℝ) : ℂ) * g x) u := by
    rw [apply_fc_of_eigen b lam H hb]
    unfold fc
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← sub_smul]
    congr 1; push_cast; ring
  rw [h1]
  have h2 : ‖fc b lam (fun x => ((x - E₀ : ℝ) : ℂ) * g x) u‖ ^ 2 ≤ (γ * ‖fc b lam g u‖) ^ 2 := by
    rw [norm_sq_fc, mul_pow, norm_sq_fc, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hg : g (lam i) = 0
    · simp [hg]
    · have h3 : (lam i - E₀) ^ 2 ≤ γ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hsupp i hg) 2
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      calc (lam i - E₀) ^ 2 * ‖g (lam i)‖ ^ 2 * ‖⟪b i, u⟫_ℂ‖ ^ 2
          ≤ γ ^ 2 * ‖g (lam i)‖ ^ 2 * ‖⟪b i, u⟫_ℂ‖ ^ 2 := by gcongr
        _ = γ ^ 2 * (‖g (lam i)‖ ^ 2 * ‖⟪b i, u⟫_ℂ‖ ^ 2) := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

lemma integral_exp_sq_shift {c : ℝ} (_hc : 0 < c) (l : ℝ) :
    ∫ x : ℝ, Real.exp (-(c * (l - x) ^ 2)) = Real.sqrt (π / c) := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun y => Real.exp (-c * y ^ 2)) l
  have e : (fun x : ℝ => Real.exp (-(c * (l - x) ^ 2))) =
      fun x => (fun y => Real.exp (-c * y ^ 2)) (x - l) := by
    funext x; congr 1; ring
  rw [e, h, integral_gaussian]

lemma integrable_exp_sq_shift {c : ℝ} (hc : 0 < c) (l : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-(c * (l - x) ^ 2))) := by
  have := (integrable_exp_neg_mul_sq hc).comp_sub_right l
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  congr 1; ring

/-- The pointwise bound behind `tavg_window_bound`, for the window part. -/
lemma window_part_bound (H : E →ₗ[ℂ] E) (hb : ∀ i, H (b i) = (lam i : ℂ) • b i)
    {C₀ : ℝ} (hlow : ∀ i, -C₀ ≤ lam i) (Cop : E →ₗ[ℂ] E) (hCop : ∀ v, ‖Cop v‖ ≤ ‖v‖)
    {t Δ X p α β : ℝ} (hΔ : 0 ≤ Δ) (hX : -C₀ ≤ X) (hp : 0 ≤ p) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hq : ∀ E₀ : ℝ, -C₀ ≤ E₀ → E₀ ≤ X → ∀ q : E,
        ‖H q - (E₀ : ℂ) • q‖ ≤ Δ * ‖q‖ → ‖Cop q‖ ^ 2 ≤ (α + β * (1 + E₀ + C₀) ^ p) * ‖q‖ ^ 2)
    (u : E) (x : ℝ) :
    ‖Cop (fc b lam (gwIn t x Δ) u)‖ ^ 2 ≤
      ∑ i, (α + β * (1 + Δ) ^ p * (1 + lam i + C₀) ^ p + (if X - Δ ≤ lam i then 1 else 0)) *
        Real.exp (-(t ^ 2 * (lam i - x) ^ 2)) * ‖⟪b i, u⟫_ℂ‖ ^ 2 := by
  set q := fc b lam (gwIn t x Δ) u with hqdef
  have hm : ∀ i, 0 ≤ α + β * (1 + Δ) ^ p * (1 + lam i + C₀) ^ p := by
    intro i
    have h1 : 0 ≤ 1 + lam i + C₀ := by linarith [hlow i]
    positivity
  have hind : ∀ i, (0 : ℝ) ≤ (if X - Δ ≤ lam i then 1 else 0) := by
    intro i; split_ifs <;> norm_num
  have hwin : ∀ i, gwIn t x Δ (lam i) ≠ 0 → |lam i - x| ≤ Δ := by
    intro i hi
    by_contra hc
    exact hi (by unfold gwIn; rw [if_neg hc])
  have hnorm_in : ∀ i, ‖gwIn t x Δ (lam i)‖ ^ 2 ≤ Real.exp (-(t ^ 2 * (lam i - x) ^ 2)) := by
    intro i
    unfold gwIn
    split_ifs
    · rw [norm_gw_sq]
    · simp; positivity
  by_cases hx : x ≤ X
  · -- below the energy cut: the hypothesis applies with `E₀ = max x (-C₀)`
    set E₀ := max x (-C₀) with hE₀
    have hsupp : ∀ i, gwIn t x Δ (lam i) ≠ 0 → |lam i - E₀| ≤ Δ := by
      intro i hi
      have hw := hwin i hi
      rw [abs_le] at hw ⊢
      rcases le_total x (-C₀) with h | h
      · have hE : E₀ = -C₀ := by rw [hE₀]; exact max_eq_right h
        rw [hE]
        constructor <;> linarith [hlow i, hw.1, hw.2]
      · have hE : E₀ = x := by rw [hE₀]; exact max_eq_left h
        rw [hE]
        exact hw
    have hqe := quasi_eigen_of_support b lam H hb (gwIn t x Δ) hΔ hsupp u
    have h1 := hq E₀ (le_max_right _ _) (max_le hx hX) q hqe
    refine h1.trans ?_
    rw [hqdef, norm_sq_fc, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : gwIn t x Δ (lam i) = 0
    · rw [hi, norm_zero]
      have : 0 ≤ (α + β * (1 + Δ) ^ p * (1 + lam i + C₀) ^ p + (if X - Δ ≤ lam i then 1 else 0)) *
          Real.exp (-(t ^ 2 * (lam i - x) ^ 2)) * ‖⟪b i, u⟫_ℂ‖ ^ 2 := by
        have := hm i; have := hind i; positivity
      simpa using this
    · have hw := hwin i hi
      have hE1 : 1 ≤ 1 + E₀ + C₀ := by
        have : -C₀ ≤ E₀ := le_max_right _ _
        linarith
      have hE2 : 1 + E₀ + C₀ ≤ (1 + Δ) * (1 + lam i + C₀) := by
        have h3 : E₀ ≤ lam i + Δ := by
          rw [abs_le] at hw
          exact max_le (by linarith [hw.1]) (by linarith [hlow i])
        have h4 : 0 ≤ Δ * (lam i + C₀) := mul_nonneg hΔ (by linarith [hlow i])
        nlinarith
      have hpow : (1 + E₀ + C₀) ^ p ≤ (1 + Δ) ^ p * (1 + lam i + C₀) ^ p := by
        rw [← Real.mul_rpow (by linarith) (by linarith [hlow i])]
        exact Real.rpow_le_rpow (by linarith) hE2 hp
      have hcoef : α + β * (1 + E₀ + C₀) ^ p ≤
          α + β * (1 + Δ) ^ p * (1 + lam i + C₀) ^ p + (if X - Δ ≤ lam i then 1 else 0) := by
        have := hind i
        have : β * (1 + E₀ + C₀) ^ p ≤ β * ((1 + Δ) ^ p * (1 + lam i + C₀) ^ p) :=
          mul_le_mul_of_nonneg_left hpow hβ
        nlinarith
      have hc0 : 0 ≤ α + β * (1 + E₀ + C₀) ^ p := by
        have : 0 ≤ (1 + E₀ + C₀) ^ p := Real.rpow_nonneg (by linarith) _
        positivity
      calc (α + β * (1 + E₀ + C₀) ^ p) * (‖gwIn t x Δ (lam i)‖ ^ 2 * ‖⟪b i, u⟫_ℂ‖ ^ 2)
          ≤ (α + β * (1 + Δ) ^ p * (1 + lam i + C₀) ^ p + (if X - Δ ≤ lam i then 1 else 0)) *
            (Real.exp (-(t ^ 2 * (lam i - x) ^ 2)) * ‖⟪b i, u⟫_ℂ‖ ^ 2) := by
            gcongr
            · have := hm i; have := hind i; positivity
            · exact hnorm_in i
        _ = _ := by ring
  · -- above the energy cut: only the high spectral part contributes
    push Not at hx
    refine ((pow_le_pow_left₀ (norm_nonneg _) (hCop q) 2)).trans ?_
    rw [hqdef, norm_sq_fc]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : gwIn t x Δ (lam i) = 0
    · rw [hi, norm_zero]
      have : 0 ≤ (α + β * (1 + Δ) ^ p * (1 + lam i + C₀) ^ p + (if X - Δ ≤ lam i then 1 else 0)) *
          Real.exp (-(t ^ 2 * (lam i - x) ^ 2)) * ‖⟪b i, u⟫_ℂ‖ ^ 2 := by
        have := hm i; have := hind i; positivity
      simpa using this
    · have hw := hwin i hi
      have hhigh : X - Δ ≤ lam i := by rw [abs_le] at hw; linarith [hw.1]
      rw [if_pos hhigh]
      calc ‖gwIn t x Δ (lam i)‖ ^ 2 * ‖⟪b i, u⟫_ℂ‖ ^ 2
          ≤ 1 * (Real.exp (-(t ^ 2 * (lam i - x) ^ 2)) * ‖⟪b i, u⟫_ℂ‖ ^ 2) := by
            rw [one_mul]; gcongr; exact hnorm_in i
        _ ≤ (α + β * (1 + Δ) ^ p * (1 + lam i + C₀) ^ p + 1) *
            (Real.exp (-(t ^ 2 * (lam i - x) ^ 2)) * ‖⟪b i, u⟫_ℂ‖ ^ 2) := by
            gcongr; linarith [hm i]
        _ = _ := by ring

/-- The pointwise bound for the Gaussian tail. -/
lemma tail_part_bound (Cop : E →ₗ[ℂ] E) (hCop : ∀ v, ‖Cop v‖ ≤ ‖v‖) {t Δ : ℝ} (hΔ : 0 ≤ Δ)
    (u : E) (x : ℝ) :
    ‖Cop (fc b lam (gwOut t x Δ) u)‖ ^ 2 ≤
      Real.exp (-(t ^ 2 * Δ ^ 2) / 2) *
        ∑ i, Real.exp (-(t ^ 2 / 2 * (lam i - x) ^ 2)) * ‖⟪b i, u⟫_ℂ‖ ^ 2 := by
  refine ((pow_le_pow_left₀ (norm_nonneg _) (hCop _) 2)).trans ?_
  rw [norm_sq_fc, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold gwOut
  split_ifs with h
  · simp; positivity
  · rw [norm_gw_sq]
    push Not at h
    have hsq : Δ ^ 2 ≤ (lam i - x) ^ 2 := by
      rw [← sq_abs (lam i - x)]; exact pow_le_pow_left₀ hΔ h.le 2
    have : Real.exp (-(t ^ 2 * (lam i - x) ^ 2)) ≤
        Real.exp (-(t ^ 2 * Δ ^ 2) / 2) * Real.exp (-(t ^ 2 / 2 * (lam i - x) ^ 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : t ^ 2 * Δ ^ 2 ≤ t ^ 2 * (lam i - x) ^ 2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg t)
      nlinarith
    calc Real.exp (-(t ^ 2 * (lam i - x) ^ 2)) * ‖⟪b i, u⟫_ℂ‖ ^ 2
        ≤ Real.exp (-(t ^ 2 * Δ ^ 2) / 2) * Real.exp (-(t ^ 2 / 2 * (lam i - x) ^ 2)) *
          ‖⟪b i, u⟫_ℂ‖ ^ 2 := by gcongr
      _ = _ := by ring

/-- **The time-averaged bound** (skeleton of `prop:tavgU`).  Let `H` have orthonormal eigenbasis
`(b, lam)` with `H ≥ -C₀`, `C` a contraction, `t > 0`, `Δ ≥ 0`, and suppose every
quasi-eigenstate `q`, `‖(H - E₀) q‖ ≤ Δ ‖q‖`, of energy `-C₀ ≤ E₀ ≤ X` has
`‖C q‖² ≤ (α + β (1 + E₀ + C₀)^p) ‖q‖²`.  Then the time average of `‖C e^{iHτ} u‖²` over
`[0, t]` is at most
`2e [√π Σ_i (α + β (1+Δ)^p (1 + λ_i + C₀)^p + 1{λ_i ≥ X - Δ}) |⟪b_i, u⟫|² + √(2π) e^{-t²Δ²/2} ‖u‖²]`. -/
theorem tavg_window_bound (H : E →ₗ[ℂ] E) (hb : ∀ i, H (b i) = (lam i : ℂ) • b i)
    {C₀ : ℝ} (hlow : ∀ i, -C₀ ≤ lam i) (Cop : E →ₗ[ℂ] E) (hCop : ∀ v, ‖Cop v‖ ≤ ‖v‖)
    {t Δ X p α β : ℝ} (ht : 0 < t) (hΔ : 0 ≤ Δ) (hX : -C₀ ≤ X) (hp : 0 ≤ p) (hα : 0 ≤ α)
    (hβ : 0 ≤ β)
    (hq : ∀ E₀ : ℝ, -C₀ ≤ E₀ → E₀ ≤ X → ∀ q : E,
        ‖H q - (E₀ : ℂ) • q‖ ≤ Δ * ‖q‖ → ‖Cop q‖ ^ 2 ≤ (α + β * (1 + E₀ + C₀) ^ p) * ‖q‖ ^ 2)
    (u : E) :
    (1 / t) * ∫ τ in (0 : ℝ)..t,
        ‖Cop (fc b lam (fun x => Complex.exp (Complex.I * (x : ℂ) * τ)) u)‖ ^ 2 ≤
      2 * Real.exp 1 * (Real.sqrt π * ∑ i, (α + β * (1 + Δ) ^ p * (1 + lam i + C₀) ^ p +
          (if X - Δ ≤ lam i then 1 else 0)) * ‖⟪b i, u⟫_ℂ‖ ^ 2 +
        Real.sqrt (2 * π) * Real.exp (-(t ^ 2 * Δ ^ 2) / 2) * ‖u‖ ^ 2) := by
  set y : ι → E := fun k => Cop (⟪b k, u⟫_ℂ • b k) with hy
  have hflow : ∀ τ : ℝ, Cop (fc b lam (fun x => Complex.exp (Complex.I * (x : ℂ) * τ)) u) =
      flowVec lam y τ := by
    intro τ
    unfold fc flowVec
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hy, map_smul, smul_smul]
  have hgauss : ∀ x : ℝ, Cop (fc b lam (gw t x) u) = gaussVec lam y t x := by
    intro x
    unfold fc gaussVec gw
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hy, map_smul, smul_smul]
  have h1 := tavg_bound lam y ht
  simp_rw [← hflow, ← hgauss] at h1
  -- the pointwise bound and its integral
  set m : ι → ℝ := fun i => α + β * (1 + Δ) ^ p * (1 + lam i + C₀) ^ p +
    (if X - Δ ≤ lam i then 1 else 0) with hmdef
  have hm : ∀ i, 0 ≤ m i := by
    intro i
    have h1 : 0 ≤ 1 + lam i + C₀ := by linarith [hlow i]
    have : (0 : ℝ) ≤ (if X - Δ ≤ lam i then 1 else 0) := by split_ifs <;> norm_num
    simp only [hmdef]
    positivity
  set R : ℝ → ℝ := fun x => 2 * ∑ i, m i * Real.exp (-(t ^ 2 * (lam i - x) ^ 2)) *
      ‖⟪b i, u⟫_ℂ‖ ^ 2 + 2 * (Real.exp (-(t ^ 2 * Δ ^ 2) / 2) *
      ∑ i, Real.exp (-(t ^ 2 / 2 * (lam i - x) ^ 2)) * ‖⟪b i, u⟫_ℂ‖ ^ 2) with hR
  have hpt : ∀ x, ‖Cop (fc b lam (gw t x) u)‖ ^ 2 ≤ R x := by
    intro x
    rw [fc_gw_split b lam t x Δ u, map_add]
    have hA := window_part_bound b lam H hb hlow Cop hCop (t := t) hΔ hX hp hα hβ hq u x
    have hB := tail_part_bound b lam Cop hCop (t := t) hΔ u x
    have hsum : ‖Cop (fc b lam (gwIn t x Δ) u) + Cop (fc b lam (gwOut t x Δ) u)‖ ^ 2 ≤
        2 * ‖Cop (fc b lam (gwIn t x Δ) u)‖ ^ 2 + 2 * ‖Cop (fc b lam (gwOut t x Δ) u)‖ ^ 2 := by
      have := norm_add_le (Cop (fc b lam (gwIn t x Δ) u)) (Cop (fc b lam (gwOut t x Δ) u))
      nlinarith [norm_nonneg (Cop (fc b lam (gwIn t x Δ) u) + Cop (fc b lam (gwOut t x Δ) u)),
        norm_nonneg (Cop (fc b lam (gwIn t x Δ) u)), norm_nonneg (Cop (fc b lam (gwOut t x Δ) u)),
        sq_nonneg (‖Cop (fc b lam (gwIn t x Δ) u)‖ - ‖Cop (fc b lam (gwOut t x Δ) u)‖)]
    simp only [hR]
    linarith
  have ht2 : 0 < t ^ 2 := by positivity
  have hRint : Integrable R := by
    simp only [hR]
    refine (Integrable.const_mul (integrable_finsetSum _ fun i _ => ?_) _).add
      ((Integrable.const_mul (integrable_finsetSum _ fun i _ => ?_) _).const_mul _)
    · exact ((integrable_exp_sq_shift ht2 (lam i)).const_mul (m i)).mul_const _
    · exact (integrable_exp_sq_shift (by positivity : 0 < t ^ 2 / 2) (lam i)).mul_const _
  have hRval : t * ∫ x, R x = 2 * Real.sqrt π * ∑ i, m i * ‖⟪b i, u⟫_ℂ‖ ^ 2 +
      2 * Real.sqrt (2 * π) * Real.exp (-(t ^ 2 * Δ ^ 2) / 2) * ‖u‖ ^ 2 := by
    simp only [hR]
    rw [integral_add (Integrable.const_mul (integrable_finsetSum _ fun i _ =>
        ((integrable_exp_sq_shift ht2 (lam i)).const_mul (m i)).mul_const _) _)
      ((Integrable.const_mul (integrable_finsetSum _ fun i _ =>
        (integrable_exp_sq_shift (by positivity : 0 < t ^ 2 / 2) (lam i)).mul_const _) _).const_mul _)]
    rw [integral_const_mul, integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun i _ =>
        ((integrable_exp_sq_shift ht2 (lam i)).const_mul (m i)).mul_const _,
      integral_finsetSum _ fun i _ =>
        (integrable_exp_sq_shift (by positivity : 0 < t ^ 2 / 2) (lam i)).mul_const _]
    simp_rw [integral_mul_const, integral_const_mul, integral_exp_sq_shift ht2,
      integral_exp_sq_shift (by positivity : 0 < t ^ 2 / 2)]
    rw [← b.sum_sq_norm_inner_right u]
    have hs1 : Real.sqrt (π / t ^ 2) = Real.sqrt π / t := by
      rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq ht.le]
    have hs2 : Real.sqrt (π / (t ^ 2 / 2)) = Real.sqrt (2 * π) / t := by
      rw [show π / (t ^ 2 / 2) = 2 * π / t ^ 2 by field_simp, Real.sqrt_div' _ (by positivity),
        Real.sqrt_sq ht.le]
    rw [hs1, hs2]
    simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have hmono : ∫ x, ‖Cop (fc b lam (gw t x) u)‖ ^ 2 ≤ ∫ x, R x :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hRint
      (Filter.Eventually.of_forall hpt)
  calc (1 / t) * ∫ τ in (0 : ℝ)..t,
        ‖Cop (fc b lam (fun x => Complex.exp (Complex.I * (x : ℂ) * τ)) u)‖ ^ 2
      ≤ Real.exp 1 * t * ∫ x : ℝ, ‖Cop (fc b lam (gw t x) u)‖ ^ 2 := h1
    _ ≤ Real.exp 1 * (t * ∫ x, R x) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmono ht.le)
          (Real.exp_pos 1).le
    _ = _ := by rw [hRval]; ring

end Windows

end FSSpectral
