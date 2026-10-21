import PlaneWave.Source.LedgerGoodStates

/-!
# Flux/source build, block 5: the retained comparison (`thm:src3`, first term)

The first term of eq:nf-assembly is `⟪χ(t), O χ(t)⟫ - ⟪ψ_N(t), O ψ_N(t)⟫` with `O = A_{p₀}^E`,
`χ(t) = e^{-iH't} χ₀` (`H' = H_N + ΔH`) and `ψ_N(t) = e^{-iH_N t} P ψ₀`.  With the rotation
`U = e^{Σ₃} e^{Z₂}` and `H'' = U H' U⁻¹` (`Hpp_mul_U`), the rotated trajectory
`χ'(s) = U χ(s)` solves `iχ'' = H'' χ' = H_N χ' + ΔH'' χ'`, and with
`ψ_N^{r₀}(t) = e^{-iH_N t} U χ₀`:

`T₁ = [⟪χ, Oχ⟫ - ⟪χ', Oχ'⟫] + [⟪χ', Oχ'⟫ - ⟪ψ_N^{r₀}, Oψ_N^{r₀}⟫] + [⟪ψ_N^{r₀}, Oψ_N^{r₀}⟫ - ⟪ψ_N, Oψ_N⟫]`.

* `norm_quad_sub_le` (the midpoint identity): for a symmetric `T`,
  `|⟪a, T a⟫ - ⟪b, T b⟫| ≤ |⟪a - b, T (a + b)⟫|`;
* the first and third brackets: `‖U χ - χ‖ (Θ(χ) + Θ(Uχ))` and `‖U χ₀ - P ψ₀‖ (Θ(ψ_N^{r₀}) + Θ(ψ_N))`
  (`‖U v - v‖ ≤ ‖Z₂ v‖ + ‖Σ₃ v‖`, `norm_Urot_sub_le`);
* the second bracket by Duhamel for `χ'` against the `H_N` flow (`duhamel_rot`):
  `⟪χ'(t) - ψ_N^{r₀}(t), v⟫ = i ∫₀ᵗ ⟪ΔH'' χ'(s), e^{iH_N(t-s)} v⟫ ds` with
  `v = O (χ'(t) + ψ_N^{r₀}(t))`, bounded by `t B` when the integrand is bounded by `B`
  (`T1_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

/-! ## The midpoint identity -/

lemma norm_quad_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (a b : E) :
    ‖⟪a, T a⟫_ℂ - ⟪b, T b⟫_ℂ‖ ≤ ‖⟪a - b, T (a + b)⟫_ℂ‖ := by
  set x := ⟪a - b, T (a + b)⟫_ℂ
  have hc : (starRingEnd ℂ) x = ⟪a + b, T (a - b)⟫_ℂ := by
    simp only [x]
    rw [inner_conj_symm, hT]
  have e : ⟪a, T a⟫_ℂ - ⟪b, T b⟫_ℂ = (x + (starRingEnd ℂ) x) / 2 := by
    rw [hc]
    simp only [x, map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right]
    ring
  rw [e, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have := norm_add_le x ((starRingEnd ℂ) x)
  rw [Complex.norm_conj] at this
  linarith

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The datum as a symmetric operator -/

section Datum

variable (sys : CoulombSystem eta ν) (L : ℝ) {n : ℕ} (p₀ : Fin eta)

/-- `A_{p₀}^E` as a linear map. -/
noncomputable def datumL : En eta n →ₗ[ℂ] En eta n :=
  cfgMul (fun p => (datumSym sys L p₀ p : ℂ))

omit [Fintype ν] in
lemma datumL_apply (v : En eta n) : datumL sys L p₀ v = datum sys L p₀ v := rfl

omit [Fintype ν] in
lemma datumL_symm : (datumL sys L p₀ : En eta n →ₗ[ℂ] En eta n).IsSymmetric := by
  intro a b
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, datumL,
    cfgMul_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [star_mul', RCLike.star_def, Complex.conj_ofReal]
  ring

omit [Fintype ν] in
/-- **The midpoint bound for the datum**:
`|⟪a, O a⟫ - ⟪b, O b⟫| ≤ ‖a - b‖ (Θ(a) + Θ(b))`. -/
lemma norm_quad_datum_le (a b : En eta n) :
    ‖⟪a, datum sys L p₀ a⟫_ℂ - ⟪b, datum sys L p₀ b⟫_ℂ‖ ≤
      ‖a - b‖ * (‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 a‖ +
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 b‖) := by
  have h := norm_quad_sub_le (datumL sys L p₀) (datumL_symm sys L p₀) a b
  simp only [datumL_apply] at h
  refine h.trans ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)))
  rw [← datumL_apply, map_add, datumL_apply, datumL_apply]
  exact (norm_add_le _ _).trans (add_le_add (norm_datum_le sys L p₀ a) (norm_datum_le sys L p₀ b))

end Datum

/-! ## The rotation -/

section Rot

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

omit [Fintype ν] in
/-- `ΔH = 0` is symmetric: its flow is the Galerkin flow `e^{iH_N τ}`. -/
lemma zero_isSymmetric : (0 : En eta n →ₗ[ℂ] En eta n).IsSymmetric := fun x y => by simp

include hKernel in
lemma norm_Urot_apply (S3 : En eta n →L[ℂ] En eta n)
    (hS3 : S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n)) (v : En eta n) :
    ‖Urot sys hL hn H S3 v‖ = ‖v‖ := by
  simp only [Urot, mul_apply_eq_comp]
  rw [FSConj.norm_exp_apply hS3, FSConj.norm_exp_apply (Z2_skew sys hL hn H hKernel)]

include hKernel in
/-- `‖U v - v‖ ≤ ‖Z₂ v‖ + ‖Σ₃ v‖`. -/
lemma norm_Urot_sub_le (S3 : En eta n →L[ℂ] En eta n)
    (hS3 : S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n)) (v : En eta n) :
    ‖Urot sys hL hn H S3 v - v‖ ≤ ‖(Z2b sys L n + Z2m sys hL hn H) v‖ + ‖S3 v‖ := by
  simp only [Urot, mul_apply_eq_comp]
  have e : exp S3 (exp (Z2b sys L n + Z2m sys hL hn H) v) - v =
      exp S3 (exp (Z2b sys L n + Z2m sys hL hn H) v - v) + (exp S3 v - v) := by
    rw [map_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ (FSConj.norm_exp_sub_one_apply_le hS3 v))
  rw [FSConj.norm_exp_apply hS3]
  exact FSConj.norm_exp_sub_one_apply_le (Z2_skew sys hL hn H hKernel) v

lemma Hret_apply_eq (ΔH : En eta n →ₗ[ℂ] En eta n) (v : En eta n) :
    Hret sys L n ΔH v = (Akin sys L n + VN sys L n) v + ΔH v := by
  have h := congrArg (fun T : En eta n →L[ℂ] En eta n => T v) (HN_eq sys (L := L) (n := n))
  simp only [LinearMap.coe_toContinuousLinearMap'] at h
  unfold Hret
  rw [LinearMap.add_apply, h]

/-- The rotated trajectory `χ'(s) = U e^{-iH's} χ₀`. -/
noncomputable def rotT (S3 : En eta n →L[ℂ] En eta n) (χ₀ : En eta n) (s : ℝ) : En eta n :=
  Urot sys hL hn H S3 (retFlow sys L n (dH_symm sys hL hn H hKernel) (-s) χ₀)

include hKernel in
/-- **The rotated trajectory solves `iχ'' = H_N χ' + ΔH'' χ'`.** -/
lemma hasDerivAt_rotT (S3 : En eta n →L[ℂ] En eta n) (χ₀ : En eta n) (s : ℝ) :
    HasDerivAt (rotT sys hL hn H hKernel S3 χ₀)
      (-(Complex.I • (Hret sys L n 0 (rotT sys hL hn H hKernel S3 χ₀ s) +
        (Hpp sys hL hn H S3 - (Akin sys L n + VN sys L n)) (rotT sys hL hn H hKernel S3 χ₀ s)))) s := by
  set hΔ := dH_symm sys hL hn H hKernel
  set U := Urot sys hL hn H S3
  have h1 := hasDerivAt_retFlow sys L n hΔ (-s) χ₀
  have h2 : HasDerivAt (fun s : ℝ => -s) (-1) s := (hasDerivAt_id s).neg
  have h3 := h1.scomp s h2
  have h4 := ((U.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h3)
  set x := retFlow sys L n hΔ (-s) χ₀
  have hx : rotT sys hL hn H hKernel S3 χ₀ s = U x := rfl
  have e1 : U ((-1 : ℝ) • (Complex.I • Hret sys L n (dH sys hL hn H) x)) =
      -(Complex.I • (Hret sys L n 0 (rotT sys hL hn H hKernel S3 χ₀ s) +
        (Hpp sys hL hn H S3 - (Akin sys L n + VN sys L n)) (rotT sys hL hn H hKernel S3 χ₀ s))) := by
    have hU := congrArg (fun T : En eta n →L[ℂ] En eta n => T x) (Hpp_mul_U sys hL hn H S3)
    simp only [mul_apply_eq_comp] at hU
    have hH : Hret sys L n (dH sys hL hn H) x = (Akin sys L n + VN sys L n + dHc sys hL hn H) x := by
      rw [Hret_apply_eq]
      simp only [dHc, add_apply, LinearMap.coe_toContinuousLinearMap']
    have h0 : Hret sys L n 0 (U x) = (Akin sys L n + VN sys L n) (U x) := by
      rw [Hret_apply_eq, LinearMap.zero_apply, add_zero]
    rw [hx, hH, h0, neg_one_smul, map_neg, map_smul, ← hU, sub_apply]
    congr 2
    abel
  have h5 : HasDerivAt (rotT sys hL hn H hKernel S3 χ₀)
      (U ((-1 : ℝ) • (Complex.I • Hret sys L n (dH sys hL hn H) x))) s := h4
  rw [← e1]
  exact h5

include hKernel in
lemma continuous_rotT (S3 : En eta n →L[ℂ] En eta n) (χ₀ : En eta n) :
    Continuous (rotT sys hL hn H hKernel S3 χ₀) :=
  (Urot sys hL hn H S3).continuous.comp
    ((continuous_retFlow sys L n (dH_symm sys hL hn H hKernel) χ₀).comp continuous_neg)

include hKernel in
/-- **Duhamel for the rotated trajectory** against the Galerkin flow. -/
theorem duhamel_rot (S3 : En eta n →L[ℂ] En eta n) (χ₀ : En eta n) (t : ℝ) (v : En eta n) :
    ⟪rotT sys hL hn H hKernel S3 χ₀ t, v⟫_ℂ =
      ⟪retFlow sys L n (zero_isSymmetric (n := n)) (-t) (Urot sys hL hn H S3 χ₀), v⟫_ℂ +
      Complex.I * ∫ s in (0 : ℝ)..t,
        ⟪(Hpp sys hL hn H S3 - (Akin sys L n + VN sys L n)) (rotT sys hL hn H hKernel S3 χ₀ s),
          retFlow sys L n (zero_isSymmetric (n := n)) (t - s) v⟫_ℂ := by
  have h := duhamel_weak_of sys (zero_isSymmetric (n := n)) (rotT sys hL hn H hKernel S3 χ₀)
    (fun s => (Hpp sys hL hn H S3 - (Akin sys L n + VN sys L n)) (rotT sys hL hn H hKernel S3 χ₀ s))
    ((Hpp sys hL hn H S3 - (Akin sys L n + VN sys L n)).continuous.comp
      (continuous_rotT sys hL hn H hKernel S3 χ₀))
    (hasDerivAt_rotT sys hL hn H hKernel S3 χ₀) t v
  have h0 : rotT sys hL hn H hKernel S3 χ₀ 0 = Urot sys hL hn H S3 χ₀ := by
    simp only [rotT, neg_zero, retFlow_zero]
  rw [h0] at h
  exact h

/-! ## The retained comparison -/

include hKernel in
/-- **The retained comparison** (`thm:src3`, first term), given a bound `B` on the integrand. -/
theorem T1_le (S3 : En eta n →L[ℂ] En eta n) (p₀ : Fin eta) (χ₀ ψ₀P : En eta n) {t : ℝ} (ht : 0 ≤ t) {B : ℝ}
    (hB : ∀ s ∈ Set.Icc (0 : ℝ) t,
      ‖⟪(Hpp sys hL hn H S3 - (Akin sys L n + VN sys L n)) (rotT sys hL hn H hKernel S3 χ₀ s),
        retFlow sys L n (zero_isSymmetric (n := n)) (t - s)
          (datum sys L p₀ (rotT sys hL hn H hKernel S3 χ₀ t +
            retFlow sys L n (zero_isSymmetric (n := n)) (-t) (Urot sys hL hn H S3 χ₀)))⟫_ℂ‖ ≤ B) :
    ‖⟪retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) χ₀,
        datum sys L p₀ (retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) χ₀)⟫_ℂ -
      ⟪retFlow sys L n (zero_isSymmetric (n := n)) (-t) ψ₀P,
        datum sys L p₀ (retFlow sys L n (zero_isSymmetric (n := n)) (-t) ψ₀P)⟫_ℂ‖ ≤
      ‖rotT sys hL hn H hKernel S3 χ₀ t - retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) χ₀‖ *
          (‖FSSpectral.wt (sb eta n) (Asym sys L n) 1
              (retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) χ₀)‖ +
            ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (rotT sys hL hn H hKernel S3 χ₀ t)‖) +
        t * B +
        ‖Urot sys hL hn H S3 χ₀ - ψ₀P‖ *
          (‖FSSpectral.wt (sb eta n) (Asym sys L n) 1
              (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (Urot sys hL hn H S3 χ₀))‖ +
            ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1
              (retFlow sys L n (zero_isSymmetric (n := n)) (-t) ψ₀P)‖) := by
  set h0 := zero_isSymmetric (n := n)
  set χ := retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) χ₀
  set χ' := rotT sys hL hn H hKernel S3 χ₀ t
  set ψr := retFlow sys L n h0 (-t) (Urot sys hL hn H S3 χ₀)
  set ψN := retFlow sys L n h0 (-t) ψ₀P
  set O := datum sys L p₀
  have e : ⟪χ, O χ⟫_ℂ - ⟪ψN, O ψN⟫_ℂ = (⟪χ, O χ⟫_ℂ - ⟪χ', O χ'⟫_ℂ) +
      (⟪χ', O χ'⟫_ℂ - ⟪ψr, O ψr⟫_ℂ) + (⟪ψr, O ψr⟫_ℂ - ⟪ψN, O ψN⟫_ℂ) := by ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · -- the first rotation of the observable
    refine (norm_quad_datum_le sys L p₀ χ χ').trans ?_
    rw [norm_sub_rev]
  · -- Duhamel
    refine (norm_quad_sub_le (datumL sys L p₀) (datumL_symm sys L p₀) χ' ψr).trans ?_
    simp only [datumL_apply]
    have hd := duhamel_rot sys hL hn H hKernel S3 χ₀ t (O (χ' + ψr))
    have e2 : ⟪χ' - ψr, O (χ' + ψr)⟫_ℂ = Complex.I * ∫ s in (0 : ℝ)..t,
        ⟪(Hpp sys hL hn H S3 - (Akin sys L n + VN sys L n)) (rotT sys hL hn H hKernel S3 χ₀ s),
          retFlow sys L n h0 (t - s) (O (χ' + ψr))⟫_ℂ := by
      rw [inner_sub_left, hd]; ring
    rw [e2, norm_mul, Complex.norm_I, one_mul]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := B)
      (f := fun s => ⟪(Hpp sys hL hn H S3 - (Akin sys L n + VN sys L n))
          (rotT sys hL hn H hKernel S3 χ₀ s), retFlow sys L n h0 (t - s) (O (χ' + ψr))⟫_ℂ)
      (fun s hs => by
        rw [Set.uIoc_of_le ht] at hs
        exact hB s ⟨hs.1.le, hs.2⟩)
    rw [sub_zero, abs_of_nonneg ht] at hb
    linarith
  · -- the datum of the Galerkin comparison
    refine (norm_quad_datum_le sys L p₀ ψr ψN).trans ?_
    refine mul_le_mul_of_nonneg_right (le_of_eq ?_) (by positivity)
    simp only [ψr, ψN]
    rw [← retFlow_sub_apply, norm_retFlow]

end Rot

end FSNormal
