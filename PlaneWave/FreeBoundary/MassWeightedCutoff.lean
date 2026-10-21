import PlaneWave.FreeBoundary.DomainWeakCalculus

/-!
# The cut initial state in `D(H_L²)`, part 2: mass-weighted cutoffs

For the non-Born–Oppenheimer system (every particle quantum, arbitrary masses `m_i`, no clamped
nuclei), the singular part of the double commutator `[V, [K, χ]]` is controlled by the
**mass-weighted cancellation** of the cutoff,
`|∇_iχ/m_i - ∇_jχ/m_j| ≤ C |x_i - x_j|`
(for `χ = h(X) f(S)`, `X` the centre of mass and `S = Σ_i m_i |x_i - X|²`, the left side is
`2 |h(X) f'(S)| |x_i - x_j|`). `DomCutoff` records what the domain theorem uses: `C⁴`,
`0 ≤ χ ≤ 1`, support in the quarter box, a bound `D` for the coordinate derivatives of orders
`1` to `4`, and the cancellation constant `C`.

* `massGrad`: the mass-weighted gradient `∇_iχ/m_i ∈ ℝ³`;
* `DomCutoff`, `DomCutoff.toCutoff`: the cutoff, and the same cutoff as a `Cutoff` of the
  free-space step;
* `DomCutoff.chainW`: the coordinate derivatives of `χ` as weights in the quarter box.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

variable {eta : ℕ}

/-- The mass-weighted gradient `∇_iχ/m_i ∈ ℝ³` of particle `i`. -/
noncomputable def massGrad (m : Fin eta → ℝ) (χ : Rcfg eta → ℝ) (i : Fin eta) (r : Rcfg eta) :
    E3 :=
  WithLp.toLp 2 (fun c => (m i)⁻¹ * dirD (i, c) χ r)

lemma massGrad_apply (m : Fin eta → ℝ) (χ : Rcfg eta → ℝ) (i : Fin eta) (r : Rcfg eta)
    (c : Fin 3) : massGrad m χ i r c = (m i)⁻¹ * dirD (i, c) χ r := rfl

/-- **A cutoff for the domain theorem**: `C⁴`, `0 ≤ χ ≤ 1`, supported in the quarter box, with
the bound `D` for the coordinate derivatives of orders `1` to `4` and the mass-weighted
cancellation `|∇_iχ/m_i - ∇_jχ/m_j| ≤ C |x_i - x_j|`. -/
structure DomCutoff (eta : ℕ) (L : ℝ) (m : Fin eta → ℝ) where
  /-- The cutoff function. -/
  χ : Rcfg eta → ℝ
  smooth : ContDiff ℝ 4 χ
  nonneg : ∀ r, 0 ≤ χ r
  le_one : ∀ r, χ r ≤ 1
  box : ∀ r, χ r ≠ 0 → ∀ a, |r a| ≤ L / 4
  /-- The derivative bound. -/
  D : ℝ
  D_nonneg : 0 ≤ D
  d1 : ∀ a r, |dirD a χ r| ≤ D
  d2 : ∀ a b r, |dirD b (dirD a χ) r| ≤ D
  d3 : ∀ a b c r, |dirD c (dirD b (dirD a χ)) r| ≤ D
  d4 : ∀ a b c d r, |dirD d (dirD c (dirD b (dirD a χ))) r| ≤ D
  /-- The cancellation constant. -/
  C : ℝ
  C_nonneg : 0 ≤ C
  cancel : ∀ r (i j : Fin eta),
    ‖massGrad m χ i r - massGrad m χ j r‖ ≤ C * ‖particle r i - particle r j‖

namespace DomCutoff

variable {L : ℝ} {m : Fin eta → ℝ} (X : DomCutoff eta L m)

/-- The cutoff as a `Cutoff` of the free-space step (`D₁ = D₂ = D`). -/
def toCutoff : Cutoff eta L where
  χ := X.χ
  smooth := X.smooth.of_le (by norm_num)
  nonneg := X.nonneg
  le_one := X.le_one
  box := X.box
  D1 := X.D
  D2 := X.D
  d1 := fun r a => X.d1 a r
  d2 := fun r a => X.d2 a a r

@[simp] lemma toCutoff_χ : X.toCutoff.χ = X.χ := rfl

lemma hasCompactSupport (hL : 0 < L) : HasCompactSupport X.χ := X.toCutoff.hasCompactSupport hL

lemma c1 (a : Fin eta × Fin 3) : ContDiff ℝ 3 (dirD a X.χ) := contDiff_dirD_nat (n := 3) X.smooth a

lemma c2 (a b : Fin eta × Fin 3) : ContDiff ℝ 2 (dirD b (dirD a X.χ)) :=
  contDiff_dirD_nat (n := 2) (X.c1 a) b

lemma c3 (a b c : Fin eta × Fin 3) : ContDiff ℝ 1 (dirD c (dirD b (dirD a X.χ))) :=
  contDiff_dirD_nat (n := 1) (X.c2 a b) c

lemma cont4 (a b c d : Fin eta × Fin 3) :
    Continuous (dirD d (dirD c (dirD b (dirD a X.χ)))) :=
  continuous_dirD (X.c3 a b c) (by norm_num) d

lemma tsupport_dirD_sub {f : Rcfg eta → ℝ} (h : tsupport f ⊆ tsupport X.χ) (a : Fin eta × Fin 3) :
    tsupport (dirD a f) ⊆ tsupport X.χ :=
  (tsupport_dirD_subset a).trans h

lemma ts1 (a : Fin eta × Fin 3) : tsupport (dirD a X.χ) ⊆ tsupport X.χ :=
  X.tsupport_dirD_sub subset_rfl a

lemma ts2 (a b : Fin eta × Fin 3) : tsupport (dirD b (dirD a X.χ)) ⊆ tsupport X.χ :=
  X.tsupport_dirD_sub (X.ts1 a) b

lemma ts3 (a b c : Fin eta × Fin 3) :
    tsupport (dirD c (dirD b (dirD a X.χ))) ⊆ tsupport X.χ :=
  X.tsupport_dirD_sub (X.ts2 a b) c

lemma ts4 (a b c d : Fin eta × Fin 3) :
    tsupport (dirD d (dirD c (dirD b (dirD a X.χ)))) ⊆ tsupport X.χ :=
  X.tsupport_dirD_sub (X.ts3 a b c) d

lemma hcs_of_sub (hL : 0 < L) {f : Rcfg eta → ℝ} (h : tsupport f ⊆ tsupport X.χ) :
    HasCompactSupport f :=
  (X.hasCompactSupport hL).mono' ((subset_tsupport f).trans h)

/-- A continuous function supported in `tsupport χ`, bounded by `D`, as a weight in the quarter
box. -/
def chainW {f : Rcfg eta → ℝ} (hf : Continuous f) (hs : tsupport f ⊆ tsupport X.χ)
    (hb : ∀ r, |f r| ≤ X.D) : BoxWeight eta L :=
  BoxWeight.ofReal f hf.measurable X.D hb fun r hr =>
    box_of_tsupport X.box r (hs (subset_tsupport f hr))

lemma chainW_w {f : Rcfg eta → ℝ} (hf : Continuous f) (hs : tsupport f ⊆ tsupport X.χ)
    (hb : ∀ r, |f r| ≤ X.D) (r : Rcfg eta) : (X.chainW hf hs hb).w r = (f r : ℂ) := rfl

lemma chainW_B {f : Rcfg eta → ℝ} (hf : Continuous f) (hs : tsupport f ⊆ tsupport X.χ)
    (hb : ∀ r, |f r| ≤ X.D) : (X.chainW hf hs hb).B = X.D := rfl

/-- `∂_aχ` as a weight. -/
noncomputable def w1 (a : Fin eta × Fin 3) : BoxWeight eta L :=
  X.chainW (continuous_dirD X.smooth (by norm_num) a) (X.ts1 a) (X.d1 a)

/-- `∂_b∂_aχ` as a weight. -/
noncomputable def w2 (a b : Fin eta × Fin 3) : BoxWeight eta L :=
  X.chainW (continuous_dirD (X.c1 a) (by norm_num) b) (X.ts2 a b) (X.d2 a b)

/-- `∂_c∂_b∂_aχ` as a weight. -/
noncomputable def w3 (a b c : Fin eta × Fin 3) : BoxWeight eta L :=
  X.chainW (continuous_dirD (X.c2 a b) (by norm_num) c) (X.ts3 a b c) (X.d3 a b c)

/-- `∂_d∂_c∂_b∂_aχ` as a weight. -/
noncomputable def w4 (a b c d : Fin eta × Fin 3) : BoxWeight eta L :=
  X.chainW (X.cont4 a b c d) (X.ts4 a b c d) (X.d4 a b c d)

/-- The pair cancellation in scalar form:
`|⟨∇_iχ/m_i - ∇_jχ/m_j, x_i - x_j⟩| ≤ C |x_i - x_j|²`. -/
lemma abs_inner_cancel_le (r : Rcfg eta) (i j : Fin eta) :
    |⟪massGrad m X.χ i r - massGrad m X.χ j r, particle r i - particle r j⟫_ℝ| ≤
      X.C * ‖particle r i - particle r j‖ ^ 2 := by
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖massGrad m X.χ i r - massGrad m X.χ j r‖ * ‖particle r i - particle r j‖
      ≤ X.C * ‖particle r i - particle r j‖ * ‖particle r i - particle r j‖ :=
        mul_le_mul_of_nonneg_right (X.cancel r i j) (norm_nonneg _)
    _ = X.C * ‖particle r i - particle r j‖ ^ 2 := by ring

end DomCutoff

end FreeBoundary
