import PlaneWave.KineticLog.GalerkinConsistency

/-!
# Logarithmic kinetic bound, part 6: the Galerkin retained-state comparison

**`eq:kinetic-retained-galerkin`.**  For the Galerkin evolution
`ψ_N(t) = e^{-iH_N t} P ψ₀` (`retFlow` with `ΔH = 0`) and the exact evolution
`ψ(t) = U(t) ψ₀` of any `EvoData` datum `ψ₀ ∈ D(H²)`:

  `‖P ψ(t) - ψ_N(t)‖ ≤ C 𝒟 K^{-3} [1 + t + log(2 + K)]`  for all `t ≥ 0` and `n ≥ N₀`,

with `𝒟 = Ξ = ‖ψ₀‖ + ‖H ψ₀‖ + ‖H² ψ₀‖` and `K = 2π n/L` (`kinetic_retained_galerkin`).

The proof (`galerkin_retained_core`) follows `sec:kinetic-galerkin`:
* the initial filter `S = 1_{H + c ≤ Λ}` costs `‖(1 - S) ψ₀‖ ≤ ‖(H + c)² ψ₀‖/Λ²` twice;
* in the Galerkin eigenbasis the filtered difference `Δ(t) = P U(t) S ψ₀ - e^{-iH_N t} P S ψ₀` has
  coordinates `i e^{-i λ_a t} Σ_k φ_t(λ_a + c - ν_k) gcons_ak ⟪b_k, ψ₀⟫` on the low rows
  (`H_N + c ≤ 2Λ`) and two unitary rotations of the separated Sylvester solution on the high
  rows (`galerkin_coord`);
* the dyadic Duhamel estimate (`dyadic_duhamel` with `M = 2Λ`, `δ = δ_G/K³`) bounds the low
  rows by `48 δ (t + log(2 + 2Λ)) ‖(H + c)² ψ₀‖` and `galerkin_transfer` bounds the high rows by
  `2 ‖X‖ ‖(H + c) ψ₀‖`.

Then `Λ = K²/(8 m̄)`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FSNormal FSGalerkin

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- `(H + c) ψ₀ = H u₀ + c S u₀` for an `EvoData` datum. -/
noncomputable def Hs1 {L : ℝ}
    {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2} (c : ℝ)
    (D : EvoData L H) : L2 eta :=
  H D.u₀ + (c : ℂ) • Sm eta L D.u₀

omit [Fintype ν] in
lemma norm_Hs1_le {L : ℝ}
    {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2} {c : ℝ}
    (hc : 0 ≤ c) (D : EvoData L H) : ‖Hs1 c D‖ ≤ (1 + c) * D.Xi := by
  unfold Hs1 EvoData.Xi
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  have := norm_nonneg (Sm eta L D.u₀)
  have := norm_nonneg (H D.u₀)
  have := norm_nonneg (H D.v₀)
  nlinarith

omit [Fintype ν] in
/-- Bessel's inequality for the eigen-coordinates over a finite set. -/
lemma norm_coords_le {L c : ℝ}
    {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}
    (E : ExactEigen L H c) (s : Finset E.ι) (x : L2 eta) :
    ‖(WithLp.toLp 2 (fun k : s => ⟪E.b k, x⟫_ℂ) : EuclideanSpace ℂ s)‖ ≤ ‖x‖ := by
  have ho : Orthonormal ℂ (fun k : s => E.b k) := E.b.orthonormal.comp _ Subtype.val_injective
  have h := ho.sum_inner_products_le (s := Finset.univ) (x := x)
  have h2 : ‖(WithLp.toLp 2 (fun k : s => ⟪E.b k, x⟫_ℂ) : EuclideanSpace ℂ s)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eucl]
    exact h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

section Retained

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (n : ℕ)

include hKernel in
/-- **Eigen-coordinates of the filtered difference.** -/
lemma galerkin_coord {c : ℝ} (E : ExactEigen L H c) (Λ : ℝ) (s : Finset E.ι) (D : EvoData L H)
    (t : ℝ) (a : GIdx eta n) :
    let c2 : EuclideanSpace ℂ s := WithLp.toLp 2 (fun k => ⟪E.b k, ExactEigen.Hs2 (c := c) D⟫_ℂ)
    let d0 : EuclideanSpace ℂ s := WithLp.toLp 2 (fun k => ⟪E.b k, Hs1 c D⟫_ℂ)
    let dt : EuclideanSpace ℂ s := WithLp.toLp 2
      (fun k => Complex.exp (-(Complex.I * ((E.nu k - c : ℝ) : ℂ) * t)) * d0 k)
    ⟪gB sys L n a, ext eta n (D.U t (E.proj s (Sm eta L D.u₀))) -
        retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (E.proj s (Sm eta L D.u₀)))⟫_ℂ =
      Complex.I * Complex.exp (Complex.I * (gE sys L n a : ℂ) * (-t : ℝ)) *
          mop (fun a (k : s) => phiT t (lamC sys n L c Λ a - E.nu k) *
            (gA sys H n E Λ s a k / (E.nu k : ℂ) ^ 2)) c2 a +
        mop (gX sys H n E Λ s) dt a -
        Complex.exp (Complex.I * (gE sys L n a : ℂ) * (-t : ℝ)) * mop (gX sys H n E Λ s) d0 a := by
  intro c2 d0 dt
  classical
  set β : s → ℂ := fun k => ⟪E.b k, Sm eta L D.u₀⟫_ℂ with hβ
  set w : s → ℂ := fun k => ⟪gB sys L n a, ext eta n (E.b k)⟫_ℂ with hw
  set ε := Complex.exp (Complex.I * (gE sys L n a : ℂ) * (-t : ℝ)) with hε
  set e : s → ℂ := fun k => Complex.exp (-(Complex.I * ((E.nu k - c : ℝ) : ℂ) * t)) with he
  -- coordinates of the two evolutions
  have hUp : ⟪gB sys L n a, ext eta n (D.U t (E.proj s (Sm eta L D.u₀)))⟫_ℂ =
      ∑ k : s, β k * e k * w k := by
    unfold ExactEigen.proj
    rw [map_sum, map_sum, inner_sum, ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearIsometryEquiv.map_smul, E.evo_b D k t, smul_smul, map_smul, inner_smul_right]
  have hp : ⟪gB sys L n a, ext eta n (E.proj s (Sm eta L D.u₀))⟫_ℂ = ∑ k : s, β k * w k := by
    unfold ExactEigen.proj
    rw [map_sum, inner_sum, ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, inner_smul_right]
  have hflow := inner_gB_flow sys L n (-t) (ext eta n (E.proj s (Sm eta L D.u₀))) a
  rw [inner_sub_right, hUp, hflow, hp]
  -- the datum coordinates
  have hc2 : ∀ k : s, c2 k = (E.nu k : ℂ) ^ 2 * β k := fun k => by
    change ⟪E.b k, ExactEigen.Hs2 (c := c) D⟫_ℂ = _
    exact E.inner_b_Hs2 sys hKernel D k
  have hd0 : ∀ k : s, d0 k = (E.nu k : ℂ) * β k := fun k => by
    change ⟪E.b k, H D.u₀ + (c : ℂ) • Sm eta L D.u₀⟫_ℂ = _
    exact E.inner_b_Hs sys hKernel k D.u₀
  by_cases ha : gE sys L n a + c ≤ 2 * Λ
  · -- low row: the separated block vanishes
    have hX0 : ∀ v : EuclideanSpace ℂ s, mop (gX sys H n E Λ s) v a = 0 := fun v => by
      rw [mop_apply]
      exact Finset.sum_eq_zero fun k _ => by simp [gX, ha]
    rw [hX0, hX0, mul_zero, add_zero, sub_zero, mop_apply, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hlam : lamC sys n L c Λ a = gE sys L n a + c := min_eq_left ha
    have hn0 : (E.nu k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (E.nu_pos k).ne'
    simp only [gA, gcons, if_pos ha, hlam]
    rw [hc2 k]
    have hφ := phiT_mul_self t (gE sys L n a + c - E.nu k)
    have hexp : ε * Complex.exp (Complex.I * ((gE sys L n a + c - E.nu k : ℝ) : ℂ) * t) = e k := by
      rw [hε, he, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have key : Complex.I * ε * (phiT t (gE sys L n a + c - E.nu k) *
        (((gE sys L n a + c - E.nu k : ℝ) : ℂ) * w k / (E.nu k : ℂ) ^ 2) *
          ((E.nu k : ℂ) ^ 2 * β k)) =
        Complex.I * ε * (phiT t (gE sys L n a + c - E.nu k) *
          ((gE sys L n a + c - E.nu k : ℝ) : ℂ)) * w k * β k := by
      field_simp
    rw [key, hφ]
    have hI : Complex.I * ε * (-Complex.I * (Complex.exp (Complex.I *
        ((gE sys L n a + c - E.nu k : ℝ) : ℂ) * t) - 1)) * w k * β k =
        (ε * Complex.exp (Complex.I * ((gE sys L n a + c - E.nu k : ℝ) : ℂ) * t) - ε) *
          w k * β k := by
      have hII : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
      linear_combination (ε * (Complex.exp (Complex.I * ((gE sys L n a + c - E.nu k : ℝ) : ℂ) *
        t) - 1) * w k * β k) * hII
    rw [hI, hexp]
    ring
  · -- high row: the low block vanishes
    have hA0 : mop (fun a (k : s) => phiT t (lamC sys n L c Λ a - E.nu k) *
        (gA sys H n E Λ s a k / (E.nu k : ℂ) ^ 2)) c2 a = 0 := by
      rw [mop_apply]
      exact Finset.sum_eq_zero fun k _ => by simp [gA, ha]
    rw [hA0, mul_zero, zero_add, mop_apply, mop_apply]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hn0 : (E.nu k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (E.nu_pos k).ne'
    simp only [gX, if_neg ha]
    change β k * e k * w k - ε * (β k * w k) =
      w k / (E.nu k : ℂ) * (e k * d0 k) - ε * (w k / (E.nu k : ℂ) * d0 k)
    rw [hd0 k]
    field_simp

include hKernel hL hPeriodic in
/-- **The Galerkin retained-state comparison, finite form**: for `1 ≤ Λ` with
`Λ + c ≤ K²/(4 m̄)` and every `t ≥ 0`,
`‖P ψ(t) - ψ_N(t)‖ ≤ 2 ‖(H+c)²ψ₀‖/Λ² + 48 (δ_G/K³)(t + log(2 + 2Λ)) ‖(H+c)²ψ₀‖
  + 2 (C_F/(K Λ)) ‖(H+c)ψ₀‖`. -/
theorem galerkin_retained_core {c : ℝ} (E : ExactEigen L H c) (hcdef : c = shiftC sys L Hunit)
    (hK1 : 1 ≤ gF L * n) (hK2 : 2 * gF L ≤ gF L * n) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : Λ + c ≤ (gF L * n) ^ 2 / (4 * sys.maxMass)) (D : EvoData L H) {t : ℝ} (ht : 0 ≤ t) :
    ‖ext eta n (D.U t (Sm eta L D.u₀)) -
        retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀))‖ ≤
      2 * (‖ExactEigen.Hs2 (c := c) D‖ / Λ ^ 2) +
        48 * (dG sys L Hunit / (gF L * n) ^ 3) * (t + Real.log (2 + 2 * Λ)) *
            ‖ExactEigen.Hs2 (c := c) D‖ +
        2 * (cF sys L Hunit / (gF L * n * Λ)) * ‖Hs1 c D‖ := by
  classical
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  have hΛ0 : 0 < Λ := by linarith
  set ψ₀ := Sm eta L D.u₀ with hψ₀
  set s := (E.finite Λ).toFinset with hsdef
  have hs : ∀ k ∈ s, E.nu k ≤ Λ := fun k hk => by simpa [hsdef] using hk
  set p := E.proj s ψ₀ with hpdef
  -- the initial filter
  have hp : ‖ψ₀ - p‖ ≤ ‖ExactEigen.Hs2 (c := c) D‖ / Λ ^ 2 := by
    refine E.norm_sub_proj_le s hΛ0 ψ₀ (ExactEigen.Hs2 (c := c) D) fun i hi => ?_
    have hi' : Λ < E.nu i := by
      by_contra h
      exact hi (by simpa [hsdef] using not_lt.mp h)
    rw [E.inner_b_Hs2 sys hKernel D i, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (E.nu_pos i)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hΛ0.le hi'.le 2) (norm_nonneg _)
  -- the filtered difference
  set Δ := ext eta n (D.U t p) - retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n p)
    with hΔdef
  set c2 : EuclideanSpace ℂ s :=
      WithLp.toLp 2 (fun k => ⟪E.b k, ExactEigen.Hs2 (c := c) D⟫_ℂ) with hc2
  set d0 : EuclideanSpace ℂ s := WithLp.toLp 2 (fun k => ⟪E.b k, Hs1 c D⟫_ℂ) with hd0
  set dt : EuclideanSpace ℂ s := WithLp.toLp 2
    (fun k => Complex.exp (-(Complex.I * ((E.nu k - c : ℝ) : ℂ) * t)) * d0 k) with hdt
  set Φ := fun a (k : s) => phiT t (lamC sys n L c Λ a - E.nu k) *
    (gA sys H n E Λ s a k / (E.nu k : ℂ) ^ 2) with hΦ
  have hcoord := galerkin_coord sys H hKernel n E Λ s D t
  -- the coordinate vector of `Δ`
  set u1 : EuclideanSpace ℂ (GIdx eta n) := WithLp.toLp 2 (fun a => Complex.I *
    Complex.exp (Complex.I * (gE sys L n a : ℂ) * (-t : ℝ)) * mop Φ c2 a) with hu1
  set u3 : EuclideanSpace ℂ (GIdx eta n) := WithLp.toLp 2 (fun a =>
    Complex.exp (Complex.I * (gE sys L n a : ℂ) * (-t : ℝ)) * mop (gX sys H n E Λ s) d0 a) with hu3
  have hvec : (WithLp.toLp 2 (fun a => ⟪gB sys L n a, Δ⟫_ℂ) : EuclideanSpace ℂ (GIdx eta n)) =
      u1 + mop (gX sys H n E Λ s) dt - u3 := by
    ext a
    exact hcoord a
  have hΔn : ‖Δ‖ = ‖(WithLp.toLp 2 (fun a => ⟪gB sys L n a, Δ⟫_ℂ) :
      EuclideanSpace ℂ (GIdx eta n))‖ := by
    have h2 : ‖Δ‖ ^ 2 = ‖(WithLp.toLp 2 (fun a => ⟪gB sys L n a, Δ⟫_ℂ) :
        EuclideanSpace ℂ (GIdx eta n))‖ ^ 2 := by
      rw [← (gB sys L n).sum_sq_norm_inner_right Δ, norm_sq_eucl]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  have hu1n : ‖u1‖ = ‖mop Φ c2‖ := norm_diag_unit _ (fun a => by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_exp]
    simp) _
  have hu3n : ‖u3‖ = ‖mop (gX sys H n E Λ s) d0‖ := norm_diag_unit _ (fun a => by
    rw [Complex.norm_exp]
    simp) _
  have hdtn : ‖dt‖ = ‖d0‖ := norm_diag_unit _ (fun k => by
    rw [Complex.norm_exp]
    simp) _
  -- the dyadic estimate on the low rows
  have hδ := galerkin_delta sys H hKernel Hunit hL hPeriodic n E hcdef hK1 hK2 hΛ1 hΛ s hs
  have hlamC : ∀ a, 1 ≤ lamC sys n L c Λ a ∧ lamC sys n L c Λ a ≤ 2 * Λ := by
    intro a
    have h1 : 1 ≤ gE sys L n a + c := hcdef ▸ one_le_gE_add sys n Hunit hL hPeriodic a
    exact ⟨le_min h1 (by linarith), min_le_right _ _⟩
  have hdy := dyadic_duhamel (lamC sys n L c Λ) (fun k : s => E.nu k) (gA sys H n E Λ s)
    (M := 2 * Λ) (δ := dG sys L Hunit / K ^ 3) (by linarith)
    (by have := dG_nonneg sys Hunit hL; positivity) hlamC
    (fun k => ⟨E.one_le k, by linarith [hs k k.2]⟩) hδ ht c2
  -- the separated transfer on the high rows
  have hX := galerkin_transfer sys H hKernel Hunit hL hPeriodic n E hcdef hK1 hK2 hΛ1 hΛ s hs
  have hc2n : ‖c2‖ ≤ ‖ExactEigen.Hs2 (c := c) D‖ := norm_coords_le E s _
  have hd0n : ‖d0‖ ≤ ‖Hs1 c D‖ := norm_coords_le E s _
  have hΔb : ‖Δ‖ ≤ 48 * (dG sys L Hunit / K ^ 3) * (t + Real.log (2 + 2 * Λ)) *
      ‖ExactEigen.Hs2 (c := c) D‖ + 2 * (cF sys L Hunit / (K * Λ)) * ‖Hs1 c D‖ := by
    rw [hΔn, hvec]
    have hcF : 0 ≤ cF sys L Hunit / (K * Λ) := by
      have := cF_nonneg sys (L := L) Hunit
      positivity
    have hlog : 0 ≤ t + Real.log (2 + 2 * Λ) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 2 * Λ by linarith)
      linarith
    have hdG : 0 ≤ dG sys L Hunit / K ^ 3 := by
      have := dG_nonneg sys Hunit hL
      positivity
    calc ‖u1 + mop (gX sys H n E Λ s) dt - u3‖
        ≤ ‖u1‖ + ‖mop (gX sys H n E Λ s) dt‖ + ‖u3‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ 48 * (dG sys L Hunit / K ^ 3) * (t + Real.log (2 + 2 * Λ)) * ‖c2‖ +
          ‖mop (gX sys H n E Λ s)‖ * ‖dt‖ + ‖mop (gX sys H n E Λ s)‖ * ‖d0‖ := by
          rw [hu1n, hu3n]
          exact add_le_add (add_le_add hdy (norm_mop_apply_le _ _)) (norm_mop_apply_le _ _)
      _ ≤ 48 * (dG sys L Hunit / K ^ 3) * (t + Real.log (2 + 2 * Λ)) * ‖ExactEigen.Hs2 (c := c) D‖ +
          cF sys L Hunit / (K * Λ) * ‖Hs1 c D‖ + cF sys L Hunit / (K * Λ) * ‖Hs1 c D‖ := by
          rw [hdtn]
          gcongr
      _ = _ := by ring
  -- assemble
  have hsplit : ext eta n (D.U t ψ₀) -
      retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n ψ₀) =
      ext eta n (D.U t (ψ₀ - p)) + Δ -
        retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (ψ₀ - p)) := by
    rw [hΔdef, map_sub (D.U t), map_sub (ext eta n), map_sub (ext eta n), retFlow_sub_apply]
    abel
  have h1 : ‖ext eta n (D.U t (ψ₀ - p))‖ ≤ ‖ψ₀ - p‖ :=
    (norm_ext_le _).trans (le_of_eq (LinearIsometryEquiv.norm_map _ _))
  have h3 : ‖retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (ψ₀ - p))‖ ≤ ‖ψ₀ - p‖ := by
    rw [norm_retFlow]
    exact norm_ext_le _
  rw [hsplit]
  calc ‖ext eta n (D.U t (ψ₀ - p)) + Δ -
        retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (ψ₀ - p))‖
      ≤ ‖ψ₀ - p‖ + ‖Δ‖ + ‖ψ₀ - p‖ :=
        (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 le_rfl)) h3)
    _ ≤ _ := by linarith

end Retained

end KineticLog
