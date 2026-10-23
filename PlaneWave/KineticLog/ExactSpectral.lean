import PlaneWave.Source.TrajectoryBudgets
import PlaneWave.KineticLog.DyadicDuhamel

/-!
# Logarithmic kinetic bound, part 3: the spectral decomposition of the exact Hamiltonian

The spectral proof of `thm:kinetic-log` uses the low-energy spectral projector
`S = 1_{H + c ≤ Λ}` of the constructed periodic Coulomb Hamiltonian.  The Hamiltonian has
compact resolvent (`PlaneWaveDynamics.resolventR`), so this projector is a finite sum over an
orthonormal family of eigenvectors.  This file connects that finite family to the already
constructed physical Hamiltonian and to every propagator satisfying `FSNormal.EvoData`:

* `Hs_lower`: the form bound `‖S u‖² ≤ Re ⟪S u, (H + c) u⟫` with the resolvent shift
  `c = shiftC` (from the release's finite Galerkin lower bound and its limit);
* `finite_eigen_ge`: a compact operator has only finitely many orthonormal eigenvectors with
  eigenvalue at least `ε > 0` (total boundedness of the image of the unit ball);
* **`ExactEigen`** and **`exists_exactEigen`**: a Hilbert basis `b` of `ℓ²` of eigenvectors of
  `H + c`, with `H²` preimages `w` (`S w_i = b_i`, `H w_i = (ν_i - c) b_i`), eigenvalues
  `ν_i ≥ 1` and finitely many eigenvalues below every level.  It is built from the
  eigenbasis of the compact symmetric resolvent `R = S (H + c S)⁻¹`;
* `ExactEigen.inner_b_H`: `⟪b_i, H x⟫ = (ν_i - c) ⟪b_i, S x⟫` (symmetry of `H`);
* **`ExactEigen.evo_b`, `ExactEigen.inner_b_evo`**: every propagator of `EvoData` acts on the
  eigenvectors by the phases `e^{-i(ν_i - c)t}` (from its Schrödinger equation, without any
  uniqueness assumption);
* the finite spectral projectors `proj s` and the high-energy bound
  `‖x - proj s x‖ ≤ ‖y‖/Λ²` when `⟪b_i, y⟫ = ν_i² ⟪b_i, x⟫` and `ν_i > Λ` off `s`
  (`norm_sub_proj_le`), via Parseval in the Hilbert basis;
* the second graph vector `Hs2 D = (H + c)² ψ₀` of an `EvoData` datum, with
  `⟪b_i, (H + c)² ψ₀⟫ = ν_i² ⟪b_i, ψ₀⟫` and `‖(H + c)² ψ₀‖ ≤ (1 + c)² Ξ`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FSNormal

namespace KineticLog

/-! ## Compact operators have finitely many large eigenvalues -/

/-- An orthonormal family of eigenvectors of a compact operator has only finitely many members
with eigenvalue at least `ε > 0`. -/
lemma finite_eigen_ge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {R : E →L[ℂ] E} (hR : IsCompactOperator R) {ι : Type*} {b : ι → E} (hb : Orthonormal ℂ b)
    {m : ι → ℝ} (hRb : ∀ i, R (b i) = (m i : ℂ) • b i) {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ m i}.Finite := by
  obtain ⟨K, hK, hsub⟩ := hR.image_closedBall_subset_compact (f := (R : E →ₗ[ℂ] E)) 1
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (ε / 2)
    (by positivity)
  have hy : ∀ i, R (b i) ∈ K := fun i => hsub ⟨b i, by
    rw [Metric.mem_closedBall, dist_zero_right, hb.1 i], rfl⟩
  have hc : ∀ i, ∃ y ∈ t, dist (R (b i)) y < ε / 2 := by
    intro i
    have := hcover (hy i)
    rw [Set.mem_iUnion₂] at this
    obtain ⟨y, hyt, hyb⟩ := this
    exact ⟨y, hyt, Metric.mem_ball.mp hyb⟩
  choose f hft hfd using hc
  have hinj : Set.InjOn f {i | ε ≤ m i} := by
    intro i hi j hj hij
    by_contra hne
    have h1 : dist (R (b i)) (R (b j)) < ε := by
      calc dist (R (b i)) (R (b j)) ≤ dist (R (b i)) (f i) + dist (f i) (R (b j)) :=
            dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by
            refine add_lt_add (hfd i) ?_
            rw [hij, dist_comm]
            exact hfd j
        _ = ε := by ring
    have h2 : ε ≤ dist (R (b i)) (R (b j)) := by
      rw [dist_eq_norm, hRb, hRb]
      have hsq : ‖(m i : ℂ) • b i - (m j : ℂ) • b j‖ ^ 2 = m i ^ 2 + m j ^ 2 := by
        rw [@norm_sub_sq ℂ, inner_smul_left, inner_smul_right, hb.2 hne, norm_smul, norm_smul,
          hb.1 i, hb.1 j, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
        simp [sq_abs]
      have hmi : ε ≤ m i := hi
      have h3 : ε ^ 2 ≤ ‖(m i : ℂ) • b i - (m j : ℂ) • b j‖ ^ 2 := by
        rw [hsq]
        nlinarith [sq_nonneg (m j)]
      exact (pow_le_pow_iff_left₀ hε.le (norm_nonneg _) two_ne_zero).mp h3
    linarith
  refine Set.Finite.of_finite_image (htfin.subset ?_) hinj
  rintro y ⟨i, -, rfl⟩
  exact hft i

/-! ## The form lower bound of the shifted Hamiltonian -/

section Lower

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **`H + c ≥ 1`** in the form sense on `H²`, with the resolvent shift `c = shiftC`. -/
lemma Hs_lower (u : MolecularFourierH2 eta) :
    ‖Sm eta L u‖ ^ 2 ≤ (⟪Sm eta L u, H u + (shiftC sys L Hunit : ℂ) • Sm eta L u⟫_ℂ).re := by
  have h := coulombFourierDomainOperator_form_lower_bound sys L Hunit hL hPeriodic H hKernel
    (molecularFourierH2DomainEquiv eta (2 * Real.pi / L) u)
  rw [molecularFourierH2DomainEquiv_coe, molecularFourierDomainOperator_apply_equiv] at h
  have hS : Sm eta L u = molecularH2StateMap eta (2 * Real.pi / L) u := rfl
  have hC := sq_nonneg (finiteCoulombPhysicalMassConstant sys L Hunit)
  have e : (⟪molecularH2StateMap eta (2 * Real.pi / L) u, (shiftC sys L Hunit : ℂ) •
      molecularH2StateMap eta (2 * Real.pi / L) u⟫_ℂ).re =
      shiftC sys L Hunit * ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ ^ 2 := by
    rw [inner_smul_right, Complex.re_ofReal_mul]
    congr 1
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (molecularH2StateMap eta (2 * Real.pi / L) u)
    simpa using this
  rw [hS, inner_add_right, Complex.add_re, e]
  unfold shiftC
  nlinarith [sq_nonneg ‖molecularH2StateMap eta (2 * Real.pi / L) u‖,
    mul_nonneg hC (sq_nonneg ‖molecularH2StateMap eta (2 * Real.pi / L) u‖)]

end Lower

/-! ## The eigen-decomposition -/

section Eigen

variable {eta : ℕ}

/-- **An eigen-decomposition of the shifted exact Hamiltonian `H + c`**: a Hilbert basis `b` of
`ℓ²` consisting of eigenvectors, with `H²` preimages `w`, eigenvalues `ν ≥ 1` of `H + c`, and
finitely many eigenvalues below every level. -/
structure ExactEigen (L : ℝ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (c : ℝ) where
  /-- The index type. -/
  ι : Type
  /-- The eigenbasis. -/
  b : HilbertBasis ι ℂ (L2 eta)
  /-- The eigenvalues of `H + c`. -/
  nu : ι → ℝ
  /-- The `H²` preimages of the eigenvectors. -/
  w : ι → MolecularFourierH2 eta
  sm_w : ∀ i, Sm eta L (w i) = b i
  H_w : ∀ i, H (w i) = ((nu i - c : ℝ) : ℂ) • b i
  one_le : ∀ i, 1 ≤ nu i
  finite : ∀ Λ : ℝ, {i | nu i ≤ Λ}.Finite

variable {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **The exact Hamiltonian has an eigen-decomposition** with the resolvent shift `c = shiftC`. -/
theorem exists_exactEigen : Nonempty (ExactEigen L H (shiftC sys L Hunit)) := by
  set R := resolventR sys L H hKernel Hunit hL hPeriodic with hRdef
  set G := resolventG sys L H hKernel Hunit hL hPeriodic with hGdef
  set c := shiftC sys L Hunit with hc
  have hsymm := resolventR_symm sys L H hKernel Hunit hL hPeriodic
  obtain ⟨ι, b, μ, hb⟩ := exists_eigen_hilbertBasis
    (resolventR_compact sys L H hKernel Hunit hL hPeriodic) hsymm
  set m : ι → ℝ := fun i => (μ i).re with hmdef
  have hRb : ∀ i, R (b i) = (m i : ℂ) • b i := fun i => by
    rw [hb]
    simp only [hmdef]
    rw [eigen_real b μ hsymm hb i]
  have hSG : ∀ i, Sm eta L (G (b i)) = (m i : ℂ) • b i := hRb
  have hHG : ∀ i, H (G (b i)) + (c : ℂ) • Sm eta L (G (b i)) = b i := fun i =>
    H_add_shift_resolventG sys L H hKernel Hunit hL hPeriodic (b i)
  have hm : ∀ i, 0 < m i ∧ m i ≤ 1 := by
    intro i
    have hlow := Hs_lower sys H hKernel Hunit hL hPeriodic (G (b i))
    rw [hHG, hSG, norm_smul, b.orthonormal.1 i, inner_smul_left, inner_self_eq_norm_sq_to_K,
      b.orthonormal.1 i, Complex.norm_real, Real.norm_eq_abs, Complex.conj_ofReal] at hlow
    have hm0 : m i ≠ 0 := by
      intro h0
      have h1 : R (b i) = R 0 := by rw [hRb, h0, Complex.ofReal_zero, zero_smul, map_zero]
      have h2 := resolventR_injective sys L H hKernel Hunit hL hPeriodic h1
      have h3 := b.orthonormal.1 i
      rw [h2, norm_zero] at h3
      exact zero_ne_one h3
    have hsq : m i ^ 2 ≤ m i := by simpa using hlow
    have hpos : 0 < m i := by
      rcases lt_or_gt_of_ne hm0 with h | h
      · nlinarith
      · exact h
    exact ⟨hpos, by nlinarith⟩
  refine ⟨{
    ι := ι
    b := b
    nu := fun i => (m i)⁻¹
    w := fun i => (((m i)⁻¹ : ℝ) : ℂ) • G (b i)
    sm_w := fun i => ?_
    H_w := fun i => ?_
    one_le := fun i => ?_
    finite := fun Λ => ?_ }⟩
  · rw [map_smul, hSG, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (hm i).1.ne',
      Complex.ofReal_one, one_smul]
  · have h1 : H (G (b i)) = b i - (c : ℂ) • ((m i : ℂ) • b i) := by
      rw [← hSG]
      exact eq_sub_of_add_eq (hHG i)
    rw [map_smul, h1, smul_sub, smul_smul, smul_smul, ← sub_smul]
    congr 1
    have hmi : (m i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hm i).1.ne'
    push_cast
    field_simp
  · exact one_le_inv₀ (hm i).1 |>.mpr (hm i).2
  · by_cases hΛ : 0 < Λ
    · refine (finite_eigen_ge (resolventR_compact sys L H hKernel Hunit hL hPeriodic)
        b.orthonormal hRb (ε := Λ⁻¹) (by positivity)).subset ?_
      intro i hi
      have hi' : (m i)⁻¹ ≤ Λ := hi
      change Λ⁻¹ ≤ m i
      rw [inv_le_comm₀ hΛ (hm i).1]
      exact hi'
    · push Not at hΛ
      convert Set.finite_empty
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_le_of_lt hΛ (inv_pos.mpr (hm i).1)

end Eigen

/-! ## The eigenbasis API -/

namespace ExactEigen

variable {eta : ℕ} {L c : ℝ}
  {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}
  (E : ExactEigen L H c)

lemma nu_pos (i : E.ι) : 0 < E.nu i := lt_of_lt_of_le one_pos (E.one_le i)

open Classical in
lemma inner_b_b (i j : E.ι) : ⟪E.b i, E.b j⟫_ℂ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp E.b.orthonormal i j

section Symm

variable {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel in
/-- `⟪b_i, H x⟫ = (ν_i - c) ⟪b_i, S x⟫`. -/
lemma inner_b_H (i : E.ι) (x : MolecularFourierH2 eta) :
    ⟪E.b i, H x⟫_ℂ = ((E.nu i - c : ℝ) : ℂ) * ⟪E.b i, Sm eta L x⟫_ℂ := by
  have h := coulombH2_symm sys L H hKernel (E.w i) x
  have hS : molecularH2StateMap eta (2 * Real.pi / L) (E.w i) = E.b i := E.sm_w i
  rw [hS, E.H_w i, inner_smul_left, Complex.conj_ofReal] at h
  exact h

include hKernel in
/-- `⟪b_i, (H + c) x⟫ = ν_i ⟪b_i, S x⟫`. -/
lemma inner_b_Hs (i : E.ι) (x : MolecularFourierH2 eta) :
    ⟪E.b i, H x + (c : ℂ) • Sm eta L x⟫_ℂ = (E.nu i : ℂ) * ⟪E.b i, Sm eta L x⟫_ℂ := by
  rw [inner_add_right, inner_smul_right, E.inner_b_H sys hKernel]
  push_cast
  ring

end Symm

/-- **The propagator acts on the eigenvectors by phases**: for every `EvoData` propagator,
`U(t) b_i = e^{-i(ν_i - c)t} b_i`. -/
lemma evo_b (D : EvoData L H) (i : E.ι) (t : ℝ) :
    D.U t (E.b i) = Complex.exp (-(Complex.I * ((E.nu i - c : ℝ) : ℂ) * t)) • E.b i := by
  set a : ℂ := ((E.nu i - c : ℝ) : ℂ)
  set f : ℝ → L2 eta := fun s => D.U s (E.b i) with hf
  have hderiv : ∀ s, HasDerivAt f ((-(Complex.I * a)) • f s) s := by
    intro s
    have h := D.deriv s (E.w i)
    rw [E.sm_w i, E.H_w i, LinearIsometryEquiv.map_smul, smul_smul] at h
    refine h.congr_deriv ?_
    rw [neg_smul]
  set g : ℝ → L2 eta := fun s => Complex.exp (Complex.I * a * s) • f s with hg
  have hgd : ∀ s, HasDerivAt g 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * a * s))
        (Complex.exp (Complex.I * a * s) * (Complex.I * a)) s := by
      have h0 : HasDerivAt (fun s : ℝ => Complex.I * a * (s : ℂ)) (Complex.I * a * 1) s :=
        (HasDerivAt.ofReal_comp (hasDerivAt_id s)).const_mul (Complex.I * a)
      have := h0.cexp
      rw [mul_one] at this
      exact this
    have h2 := h1.smul (hderiv s)
    refine h2.congr_deriv ?_
    rw [smul_smul, ← add_smul]
    have : Complex.exp (Complex.I * a * s) * -(Complex.I * a) +
        Complex.exp (Complex.I * a * s) * (Complex.I * a) = 0 := by ring
    rw [this, zero_smul]
  have hconst : ∀ s, g s = g 0 := fun s =>
    is_const_of_deriv_eq_zero (fun s => (hgd s).differentiableAt) (fun s => (hgd s).deriv) s 0
  have hg0 : g 0 = E.b i := by
    simp only [hg, hf, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul, D.U0]
  have ht := hconst t
  rw [hg0] at ht
  have e : f t = Complex.exp (-(Complex.I * a * t)) • g t := by
    simp only [hg, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
  change f t = _
  rw [e, ht]

/-- **Eigen-coordinates of the evolution**: `⟪b_i, U(t) y⟫ = e^{-i(ν_i - c)t} ⟪b_i, y⟫`. -/
lemma inner_b_evo (D : EvoData L H) (i : E.ι) (t : ℝ) (y : L2 eta) :
    ⟪E.b i, D.U t y⟫_ℂ = Complex.exp (-(Complex.I * ((E.nu i - c : ℝ) : ℂ) * t)) *
      ⟪E.b i, y⟫_ℂ := by
  set a : ℂ := ((E.nu i - c : ℝ) : ℂ)
  have hz : D.U t (Complex.exp (Complex.I * a * t) • E.b i) = E.b i := by
    rw [LinearIsometryEquiv.map_smul, E.evo_b D i t, smul_smul, ← Complex.exp_add,
      add_neg_cancel, Complex.exp_zero, one_smul]
  calc ⟪E.b i, D.U t y⟫_ℂ = ⟪D.U t (Complex.exp (Complex.I * a * t) • E.b i), D.U t y⟫_ℂ := by
        rw [hz]
    _ = ⟪Complex.exp (Complex.I * a * t) • E.b i, y⟫_ℂ := LinearIsometryEquiv.inner_map_map _ _ _
    _ = _ := by
        rw [inner_smul_left, ← Complex.exp_conj]
        congr 2
        simp [a, Complex.conj_ofReal]

/-! ## Finite spectral projectors -/

/-- The projector `Σ_{i ∈ s} ⟪b_i, x⟫ b_i` onto a finite set of eigenvectors. -/
noncomputable def proj (s : Finset E.ι) (x : L2 eta) : L2 eta := ∑ i ∈ s, ⟪E.b i, x⟫_ℂ • E.b i

open Classical in
lemma inner_b_proj (s : Finset E.ι) (x : L2 eta) (i : E.ι) :
    ⟪E.b i, E.proj s x⟫_ℂ = if i ∈ s then ⟪E.b i, x⟫_ℂ else 0 := by
  classical
  unfold proj
  rw [inner_sum]
  simp_rw [inner_smul_right, E.inner_b_b]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-- **The high spectral part of a datum with two Hamiltonian derivatives.** If
`Λ² |⟪b_i, x⟫| ≤ |⟪b_i, y⟫|` for every `i ∉ s` (e.g. `y = (H + c)² x` and `ν_i > Λ` off `s`), then
`‖x - proj s x‖ ≤ ‖y‖ / Λ²`. -/
lemma norm_sub_proj_le (s : Finset E.ι) {Λ : ℝ} (hΛ : 0 < Λ) (x y : L2 eta)
    (hxy : ∀ i, i ∉ s → Λ ^ 2 * ‖⟪E.b i, x⟫_ℂ‖ ≤ ‖⟪E.b i, y⟫_ℂ‖) :
    ‖x - E.proj s x‖ ≤ ‖y‖ / Λ ^ 2 := by
  classical
  have hr : ∀ i, ‖E.b.repr (x - E.proj s x) i‖ ^ 2 ≤ (Λ ^ 2)⁻¹ ^ 2 * ‖E.b.repr y i‖ ^ 2 := by
    intro i
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, inner_sub_right,
      E.inner_b_proj]
    split_ifs with hi
    · rw [sub_self, norm_zero, zero_pow two_ne_zero]
      positivity
    · rw [sub_zero, ← mul_pow]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity), mul_comm]
      exact hxy i hi
  have h2 : ‖x - E.proj s x‖ ^ 2 ≤ (‖y‖ / Λ ^ 2) ^ 2 := by
    rw [norm_sq_eq_tsum_repr E.b, div_pow, div_eq_inv_mul, ← inv_pow, norm_sq_eq_tsum_repr E.b,
      ← tsum_mul_left]
    exact (summable_repr_sq E.b _).tsum_le_tsum hr ((summable_repr_sq E.b y).mul_left _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-! ## The datum and its second graph vector -/

/-- The second graph vector `(H + c)² ψ₀ = (H + c)(v₀ + c u₀)` of an `EvoData` datum
(`(H + c) u₀ = S (v₀ + c u₀)`). -/
noncomputable def Hs2 (D : EvoData L H) : L2 eta :=
  H (D.v₀ + (c : ℂ) • D.u₀) + (c : ℂ) • Sm eta L (D.v₀ + (c : ℂ) • D.u₀)

section Datum

variable {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel in
/-- `⟪b_i, (H + c)² ψ₀⟫ = ν_i² ⟪b_i, ψ₀⟫`. -/
lemma inner_b_Hs2 (D : EvoData L H) (i : E.ι) :
    ⟪E.b i, Hs2 (c := c) D⟫_ℂ = (E.nu i : ℂ) ^ 2 * ⟪E.b i, Sm eta L D.u₀⟫_ℂ := by
  unfold Hs2
  rw [E.inner_b_Hs sys hKernel]
  have hS : Sm eta L (D.v₀ + (c : ℂ) • D.u₀) = H D.u₀ + (c : ℂ) • Sm eta L D.u₀ := by
    rw [map_add, map_smul, ← D.uv]
  rw [hS, E.inner_b_Hs sys hKernel]
  ring

end Datum

/-- `‖(H + c)² ψ₀‖ ≤ (1 + |c|)² Ξ`. -/
lemma norm_Hs2_le (D : EvoData L H) : ‖Hs2 (c := c) D‖ ≤ (1 + |c|) ^ 2 * D.Xi := by
  unfold Hs2 EvoData.Xi
  have hS : Sm eta L (D.v₀ + (c : ℂ) • D.u₀) = H D.u₀ + (c : ℂ) • Sm eta L D.u₀ := by
    rw [map_add, map_smul, ← D.uv]
  rw [hS, map_add, map_smul]
  have hc : ‖(c : ℂ)‖ = |c| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 := norm_nonneg (Sm eta L D.u₀)
  have h2 := norm_nonneg (H D.u₀)
  have h3 := norm_nonneg (H D.v₀)
  have h4 := abs_nonneg c
  calc ‖H D.v₀ + (c : ℂ) • H D.u₀ + (c : ℂ) • (H D.u₀ + (c : ℂ) • Sm eta L D.u₀)‖
      ≤ ‖H D.v₀‖ + |c| * ‖H D.u₀‖ + |c| * (‖H D.u₀‖ + |c| * ‖Sm eta L D.u₀‖) := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
        · rw [norm_smul, hc]
        · rw [norm_smul, hc]
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) h4
          rw [norm_smul, hc]
    _ ≤ (1 + |c|) ^ 2 * (‖Sm eta L D.u₀‖ + ‖H D.u₀‖ + ‖H D.v₀‖) := by
        nlinarith [mul_nonneg h4 h1, mul_nonneg h4 h2, mul_nonneg h4 h3,
          mul_nonneg (mul_nonneg h4 h4) h1, mul_nonneg (mul_nonneg h4 h4) h2,
          mul_nonneg (mul_nonneg h4 h4) h3]

end ExactEigen

end KineticLog
