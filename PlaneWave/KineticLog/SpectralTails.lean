import PlaneWave.KineticLog.ExactSpectral
import PlaneWave.Source.PotentialTails

/-!
# Logarithmic kinetic bound, part 4: Fourier tails of inverse-weighted low-energy states

Inputs of `lem:kinetic-low` on the exact periodic side.  For the cube projector `P` of
half-width `n` (momenta `|k|_∞ ≤ K = g n`):

* `kin_ge_of_not_mem_cube`, `norm_sub_trunc_le_kin`: off the cube the kinetic energy is at least
  `g²(n+1)²/(2 m̄)`, so `‖(1 - P) S u‖ ≤ (2 m̄ / K²) ‖(1 - P) T u‖`;
* `W_tail_le` (`eq:kinetic-generic-tails` on the full space):
  `‖(1 - P) W u‖ ≤ η C_tail m̄ (‖S u‖ + 2 ‖T u‖) / √K` for every `u ∈ H²`;
* the low-energy combinations `zv s a = Σ_{k ∈ s} (a_k/ν_k) w_k`, i.e. `(H + c)⁻¹ Σ a_k b_k`,
  with `S zv = Σ (a_k/ν_k) b_k`, `H zv = Σ (a_k (ν_k - c)/ν_k) b_k` and `(H + c) zv = Σ a_k b_k`;
* **`norm_tail_zv_le`** (the first inequality of `eq:kinetic-spectral-momentum-tail`): if every
  `k ∈ s` has `ν_k ≤ Λ` and `Λ + c ≤ K²/(4 m̄)`, then
  `‖(1 - P) S zv s a‖ ≤ C_abs K^{-5/2} ‖a‖`.  The proof is the manuscript's absorption
  (`eq:kinetic-absorption`) at the level of the operator norm of `a ↦ (1 - P) S zv s a`, using
  `H zv s a = S zv s (ν - c) a` (that is, `H B = B H S`) and never `P H = H P`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FSNormal

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The kinetic energy off the cube -/

section Kinetic

variable (sys : CoulombSystem eta ν)

omit [Fintype ν] in
/-- Off the cube of half-width `n` the kinetic symbol is at least `g² (n+1)² / (2 m̄)`. -/
lemma kin_ge_of_not_mem_cube (g : ℝ) (n : ℕ) {p : FourierConfig eta Lattice3}
    (hp : p ∉ fourierConfigCube eta n) :
    g ^ 2 * ((n : ℝ) + 1) ^ 2 / (2 * sys.maxMass) ≤ coulombKineticEnergySymbol sys g p := by
  rw [mem_fourierConfigCube_iff] at hp
  push Not at hp
  obtain ⟨i, d, hid⟩ := hp
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ ((p i d : ℤ) : ℝ) ^ 2 := by
    have h1 : (n : ℤ) + 1 ≤ |p i d| := by
      by_cases h : -(n : ℤ) ≤ p i d
      · have := hid h
        rw [abs_of_pos (by omega)]
        omega
      · push Not at h
        rw [abs_of_neg (by omega)]
        omega
    have h2 : ((n : ℝ) + 1) ≤ |((p i d : ℤ) : ℝ)| := by
      have := (Int.cast_le (R := ℝ)).mpr h1
      push_cast at this
      exact this
    calc ((n : ℝ) + 1) ^ 2 ≤ |((p i d : ℤ) : ℝ)| ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      _ = ((p i d : ℤ) : ℝ) ^ 2 := sq_abs _
  have hlat : ((p i d : ℤ) : ℝ) ^ 2 ≤ latticeNormSq (p i) := by
    unfold latticeNormSq
    fin_cases d <;> simp <;> nlinarith [sq_nonneg ((p i 0 : ℤ) : ℝ), sq_nonneg ((p i 1 : ℤ) : ℝ),
      sq_nonneg ((p i 2 : ℤ) : ℝ)]
  have hm := sys.mass_le_maxMass i
  have hm0 := sys.mass_pos i
  have hterm : g ^ 2 * latticeNormSq (p i) / sys.mass i ≤
      ∑ j : Fin eta, g ^ 2 * latticeNormSq (p j) / sys.mass j :=
    Finset.single_le_sum (f := fun j => g ^ 2 * latticeNormSq (p j) / sys.mass j)
      (fun j _ => div_nonneg (mul_nonneg (sq_nonneg g) (latticeNormSq_nonneg _))
        (sys.mass_pos j).le) (Finset.mem_univ i)
  have hstep : g ^ 2 * ((n : ℝ) + 1) ^ 2 / sys.maxMass ≤
      g ^ 2 * latticeNormSq (p i) / sys.mass i := by
    have h1 : g ^ 2 * ((n : ℝ) + 1) ^ 2 ≤ g ^ 2 * latticeNormSq (p i) :=
      mul_le_mul_of_nonneg_left (hsq.trans hlat) (sq_nonneg g)
    calc g ^ 2 * ((n : ℝ) + 1) ^ 2 / sys.maxMass ≤ g ^ 2 * latticeNormSq (p i) / sys.maxMass :=
          div_le_div_of_nonneg_right h1 (by linarith)
      _ ≤ g ^ 2 * latticeNormSq (p i) / sys.mass i :=
          div_le_div_of_nonneg_left (by have := latticeNormSq_nonneg (p i); positivity) hm0 hm
  have key := hstep.trans hterm
  unfold coulombKineticEnergySymbol
  calc g ^ 2 * ((n : ℝ) + 1) ^ 2 / (2 * sys.maxMass) =
        (1 / 2 : ℝ) * (g ^ 2 * ((n : ℝ) + 1) ^ 2 / sys.maxMass) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key (by norm_num)

omit [Fintype ν] in
/-- The exterior part of a vector: `(x - P x)_p = 0` on the cube and `x_p` off it. -/
lemma sub_trunc_apply (n : ℕ) (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (p : FourierConfig eta Lattice3) :
    (x - molecularH2Truncate n x) p = if p ∈ fourierConfigCube eta n then 0 else x p := by
  classical
  rw [lp.coeFn_sub, Pi.sub_apply, molecularH2Truncate_apply]
  split_ifs with hp
  · rw [cubicLatticeCoeffTruncate_eq_of_mem n _ p hp, sub_self]
  · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ p hp, sub_zero]

omit [Fintype ν] in
/-- **The kinetic energy dominates the exterior norm**:
`‖(1 - P) S u‖ ≤ (2 m̄ / (g (n+1))²) ‖(1 - P) T u‖`. -/
lemma norm_sub_trunc_le_kin (g : ℝ) (hg : 0 < g) (n : ℕ) (u : MolecularFourierH2 eta) :
    ‖molecularH2StateMap eta g u - molecularH2Truncate n (molecularH2StateMap eta g u)‖ ≤
      2 * sys.maxMass / (g ^ 2 * ((n : ℝ) + 1) ^ 2) *
        ‖coulombFourierKineticH2 sys g u -
            molecularH2Truncate n (coulombFourierKineticH2 sys g u)‖ := by
  have hm := sys.one_le_maxMass
  have hκ : 0 < g ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
  refine l2_norm_le_of_le _ _ (by positivity) fun p => ?_
  rw [sub_trunc_apply, sub_trunc_apply]
  split_ifs with hp
  · simp
  · rw [molecularH2StateMap_apply, coulombFourierKineticH2_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (coulombKineticEnergySymbol_nonneg sys g p)]
    have hk := kin_ge_of_not_mem_cube sys g n hp
    have h1 : 1 ≤ 2 * sys.maxMass / (g ^ 2 * ((n : ℝ) + 1) ^ 2) *
        coulombKineticEnergySymbol sys g p := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
      rw [div_le_iff₀ (by linarith)] at hk
      linarith
    calc ‖molecularH2Coeff g u p‖ ≤ 2 * sys.maxMass / (g ^ 2 * ((n : ℝ) + 1) ^ 2) *
          coulombKineticEnergySymbol sys g p * ‖molecularH2Coeff g u p‖ :=
          le_mul_of_one_le_left (norm_nonneg _) h1
      _ = _ := by ring

end Kinetic

/-! ## The potential tail of an `H²` state -/

section PotentialTail

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

/-- The potential-tail constant per unit `H²` budget, `C_W = η C_tail(1) m̄`. -/
noncomputable def cWt (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  eta * CtW sys L Hunit 1 * sys.maxMass

lemma CtW_linear (M₂ : ℝ) : CtW sys L Hunit M₂ = CtW sys L Hunit 1 * M₂ := by
  unfold CtW finiteCoulombPhysicalTailConstant finiteCoulombTailConstant
  ring

include hL in
lemma cWt_nonneg : 0 ≤ cWt sys L Hunit := by
  unfold cWt
  have := CtW_nonneg sys hL Hunit zero_le_one
  have := sys.one_le_maxMass
  positivity

include hKernel hL hPeriodic in
/-- **Generic potential tail** (`eq:kinetic-generic-tails`): for `K = g n ≥ max(1, 2g)`,
`‖(1 - P) W u‖ ≤ C_W (‖S u‖ + 2 ‖T u‖) / √K`. -/
theorem W_tail_le (n : ℕ) (hK1 : 1 ≤ gF L * n) (hK2 : 2 * gF L ≤ gF L * n)
    (u : MolecularFourierH2 eta) :
    ‖Wp sys L H u - molecularH2Truncate n (Wp sys L H u)‖ ≤
      cWt sys L Hunit * (‖Sm eta L u‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) u‖) /
        Real.sqrt (gF L * n) := by
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  set M₂ := sys.maxMass * (‖Sm eta L u‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) u‖) with hM₂
  have hu : ‖u‖ ≤ M₂ := h2norm_le sys L u
  have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) hu
  have hρ : Real.sqrt (1 / K) ^ 2 * K = 1 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have ht : ∀ a, ‖tailMask (gF L) K a (Wp sys L H u)‖ ≤
      CtW sys L Hunit M₂ * Real.sqrt (1 / K) := by
    intro a
    have h := potential_tail_le sys L H hKernel Hunit hL hPeriodic a K (Real.sqrt (1 / K))
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) M₂ hK1 (Real.sqrt_nonneg _) hρ hBlow hCs hBker hM₂0
      hK2 hLow hKernelScale hSobolev u hu
    exact h
  have hsq : Real.sqrt (1 / K) = 1 / Real.sqrt K := by
    rw [Real.sqrt_div' 1 hK0.le, Real.sqrt_one]
  calc ‖Wp sys L H u - molecularH2Truncate n (Wp sys L H u)‖
      ≤ ∑ a : Fin eta, ‖tailMask (gF L) K a (Wp sys L H u)‖ :=
        PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) n _
    _ ≤ ∑ _a : Fin eta, CtW sys L Hunit M₂ * Real.sqrt (1 / K) := Finset.sum_le_sum fun a _ => ht a
    _ = cWt sys L Hunit * (‖Sm eta L u‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) u‖) /
          Real.sqrt K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, CtW_linear, hsq,
          hM₂]
        unfold cWt
        ring

end PotentialTail

/-! ## Low-energy combinations -/

namespace ExactEigen

variable {L c : ℝ}
  {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}
  (E : ExactEigen L H c)

omit [Fintype ν] in
/-- The orthonormal combination `Σ_{k ∈ s} a_k b_k` has norm `‖a‖`. -/
lemma norm_combo (s : Finset E.ι) (a : EuclideanSpace ℂ s) :
    ‖∑ k : s, a k • E.b k‖ = ‖a‖ := by
  have ho : Orthonormal ℂ (fun k : s => E.b k) :=
    E.b.orthonormal.comp _ Subtype.val_injective
  have h := ho.inner_sum (fun k => a k) (fun k => a k) (Finset.univ)
  have h2 : ‖∑ k : s, a k • E.b k‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, h, EuclideanSpace.norm_sq_eq, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

omit [Fintype ν] in
/-- A coordinatewise-dominated combination: if `‖d_k‖ ≤ C ‖a_k‖` then
`‖Σ d_k b_k‖ ≤ C ‖a‖`. -/
lemma norm_combo_le (s : Finset E.ι) (a : EuclideanSpace ℂ s) (d : s → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ k, ‖d k‖ ≤ C * ‖a k‖) : ‖∑ k : s, d k • E.b k‖ ≤ C * ‖a‖ := by
  have e := E.norm_combo s (WithLp.toLp 2 d)
  change ‖∑ k : s, d k • E.b k‖ = _ at e
  rw [e]
  exact norm_le_of_coord hC h

/-- The low-energy `H²` combination `zv s a = Σ_{k ∈ s} (a_k/ν_k) w_k = (H + c)⁻¹ Σ a_k b_k`. -/
noncomputable def zv (s : Finset E.ι) (a : EuclideanSpace ℂ s) : MolecularFourierH2 eta :=
  ∑ k : s, (a k / (E.nu k : ℂ)) • E.w k

omit [Fintype ν] in
lemma sm_zv (s : Finset E.ι) (a : EuclideanSpace ℂ s) :
    Sm eta L (E.zv s a) = ∑ k : s, (a k / (E.nu k : ℂ)) • E.b k := by
  unfold zv
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, E.sm_w]

omit [Fintype ν] in
lemma H_zv (s : Finset E.ι) (a : EuclideanSpace ℂ s) :
    H (E.zv s a) = ∑ k : s, (a k / (E.nu k : ℂ) * ((E.nu k - c : ℝ) : ℂ)) • E.b k := by
  unfold zv
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, E.H_w, smul_smul]

omit [Fintype ν] in
lemma Hs_zv (s : Finset E.ι) (a : EuclideanSpace ℂ s) :
    H (E.zv s a) + (c : ℂ) • Sm eta L (E.zv s a) = ∑ k : s, a k • E.b k := by
  rw [E.H_zv, E.sm_zv, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, ← add_smul]
  congr 1
  have hn : (E.nu k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (E.nu_pos k).ne'
  push_cast
  field_simp
  ring

omit [Fintype ν] in
lemma zv_add (s : Finset E.ι) (a a' : EuclideanSpace ℂ s) :
    E.zv s (a + a') = E.zv s a + E.zv s a' := by
  unfold zv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_smul]
  congr 1
  simp only [PiLp.add_apply]
  ring

omit [Fintype ν] in
lemma zv_smul (s : Finset E.ι) (r : ℂ) (a : EuclideanSpace ℂ s) :
    E.zv s (r • a) = r • E.zv s a := by
  unfold zv
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

/-- The exterior part `a ↦ (1 - P) S zv s a`, as a bounded operator on the coordinates. -/
noncomputable def tailOp (n : ℕ) (s : Finset E.ι) : EuclideanSpace ℂ s →L[ℂ] L2 eta :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => Sm eta L (E.zv s a) - molecularH2Truncate n (Sm eta L (E.zv s a))
      map_add' := fun a a' => by
        classical
        rw [E.zv_add, map_add]
        change _ = (Sm eta L (E.zv s a) - lpTruncateCLM (fourierConfigCube eta n)
          (Sm eta L (E.zv s a))) + (Sm eta L (E.zv s a') - lpTruncateCLM (fourierConfigCube eta n)
          (Sm eta L (E.zv s a')))
        change _ - lpTruncateCLM (fourierConfigCube eta n) _ = _
        rw [map_add]
        abel
      map_smul' := fun r a => by
        classical
        rw [E.zv_smul, map_smul]
        change _ - lpTruncateCLM (fourierConfigCube eta n) _ =
          r • (Sm eta L (E.zv s a) - lpTruncateCLM (fourierConfigCube eta n) (Sm eta L (E.zv s a)))
        rw [map_smul, smul_sub] }

omit [Fintype ν] in
lemma tailOp_apply (n : ℕ) (s : Finset E.ι) (a : EuclideanSpace ℂ s) :
    E.tailOp n s a = Sm eta L (E.zv s a) - molecularH2Truncate n (Sm eta L (E.zv s a)) := rfl

end ExactEigen

/-! ## Absorption: the momentum tail of inverse-weighted low-energy states -/

section Absorption

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

/-- The budget `‖S zv‖ + 2 ‖T zv‖ ≤ c_z ‖a‖`, `c_z = 1 + 2 (2 (1 + c) + 2 relB)`. -/
noncomputable def cZ (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  1 + 2 * (2 * (1 + shiftC sys L Hunit) + 2 * relB sys L Hunit)

/-- The absorption constant `C_abs = 4 m̄ C_W c_z`. -/
noncomputable def cAbs (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  4 * sys.maxMass * cWt sys L Hunit * cZ sys L Hunit

lemma cZ_nonneg : 0 ≤ cZ sys L Hunit := by
  unfold cZ
  have := two_le_shiftC sys L Hunit
  have := relB_nonneg sys L Hunit (finiteCoulombPhysicalMassConstant_nonneg sys L Hunit)
  positivity

include hL in
lemma cAbs_nonneg : 0 ≤ cAbs sys L Hunit := by
  unfold cAbs
  have := cWt_nonneg sys Hunit hL
  have := cZ_nonneg sys (L := L) Hunit
  have := sys.one_le_maxMass
  positivity

include hKernel hL hPeriodic in
/-- `‖S zv‖ + 2 ‖T zv‖ ≤ c_z ‖a‖` for low-energy combinations. -/
lemma zv_budget {c : ℝ} (E : ExactEigen L H c) (hcdef : c = shiftC sys L Hunit)
    (s : Finset E.ι) (a : EuclideanSpace ℂ s) :
    ‖Sm eta L (E.zv s a)‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) (E.zv s a)‖ ≤
      cZ sys L Hunit * ‖a‖ := by
  have hc : 2 ≤ c := hcdef ▸ two_le_shiftC sys L Hunit
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hb := relB_nonneg sys L Hunit hC
  have hS : ‖Sm eta L (E.zv s a)‖ ≤ 1 * ‖a‖ := by
    rw [E.sm_zv]
    refine E.norm_combo_le s a (fun k => a k / (E.nu k : ℂ)) zero_le_one fun k => ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (E.nu_pos k), one_mul]
    exact div_le_self (norm_nonneg _) (E.one_le k)
  have hH : ‖H (E.zv s a)‖ ≤ (1 + c) * ‖a‖ := by
    rw [E.H_zv]
    refine E.norm_combo_le s a (fun k => a k / (E.nu k : ℂ) * ((E.nu k - c : ℝ) : ℂ))
      (by linarith) fun k => ?_
    have hn := E.nu_pos k
    have h1 := E.one_le k
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hn]
    have h2 : |E.nu k - c| / E.nu k ≤ 1 + c := by
      rw [div_le_iff₀ hn]
      rcases le_total c (E.nu k) with h | h
      · rw [abs_of_nonneg (by linarith)]
        nlinarith
      · rw [abs_of_nonpos (by linarith)]
        nlinarith
    calc ‖a k‖ / E.nu k * |E.nu k - c| = |E.nu k - c| / E.nu k * ‖a k‖ := by ring
      _ ≤ (1 + c) * ‖a k‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have hT := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC (E.zv s a)
  change ‖coulombFourierKineticH2 sys (gF L) (E.zv s a)‖ ≤
    2 * ‖H (E.zv s a)‖ + 2 * relB sys L Hunit * ‖Sm eta L (E.zv s a)‖ at hT
  unfold cZ
  rw [← hcdef]
  nlinarith [norm_nonneg a]

include hKernel hL hPeriodic in
/-- **Inverse-weighted low-energy states have `K^{-5/2}` momentum tails**
(`eq:kinetic-spectral-momentum-tail`, exact side): if `ν_k ≤ Λ` on `s` and
`Λ + c ≤ K²/(4 m̄)` with `K = g n ≥ max(1, 2g)`, then
`‖(1 - P) S zv s a‖ ≤ C_abs / (K² √K) ‖a‖`. -/
theorem norm_tail_zv_le {c : ℝ} (E : ExactEigen L H c) (hcdef : c = shiftC sys L Hunit) (n : ℕ)
    (hK1 : 1 ≤ gF L * n) (hK2 : 2 * gF L ≤ gF L * n) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : Λ + c ≤ (gF L * n) ^ 2 / (4 * sys.maxMass))
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) (a : EuclideanSpace ℂ s) :
    ‖E.tailOp n s a‖ ≤ cAbs sys L Hunit / ((gF L * n) ^ 2 * Real.sqrt (gF L * n)) * ‖a‖ := by
  set K := gF L * n with hKdef
  set m := sys.maxMass
  have hm : 1 ≤ m := sys.one_le_maxMass
  have hc : 2 ≤ c := hcdef ▸ two_le_shiftC sys L Hunit
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hg := gF_pos hL
  set N := ‖E.tailOp n s‖ with hN
  have hCW := cWt_nonneg sys Hunit hL
  have hcz := cZ_nonneg sys (L := L) Hunit
  -- the kinetic lower bound off the cube: `(K²/(2m̄)) ‖(1-P) S z‖ ≤ ‖(1-P) T z‖`
  have hkin : ∀ b : EuclideanSpace ℂ s, K ^ 2 / (2 * m) * ‖E.tailOp n s b‖ ≤
      ‖coulombFourierKineticH2 sys (gF L) (E.zv s b) -
        molecularH2Truncate n (coulombFourierKineticH2 sys (gF L) (E.zv s b))‖ := by
    intro b
    have h := norm_sub_trunc_le_kin sys (gF L) hg n (E.zv s b)
    rw [E.tailOp_apply]
    have hκ : K ^ 2 ≤ gF L ^ 2 * ((n : ℝ) + 1) ^ 2 := by
      rw [hKdef, mul_pow]
      gcongr
      linarith
    have hpos : 0 < gF L ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
    have h2 : K ^ 2 / (2 * m) * ‖Sm eta L (E.zv s b) - molecularH2Truncate n
        (Sm eta L (E.zv s b))‖ ≤ gF L ^ 2 * ((n : ℝ) + 1) ^ 2 / (2 * m) *
          ‖Sm eta L (E.zv s b) - molecularH2Truncate n (Sm eta L (E.zv s b))‖ := by
      gcongr
    refine h2.trans ?_
    have e : gF L ^ 2 * ((n : ℝ) + 1) ^ 2 / (2 * m) * (2 * m / (gF L ^ 2 * ((n : ℝ) + 1) ^ 2)) =
        1 := by field_simp
    calc gF L ^ 2 * ((n : ℝ) + 1) ^ 2 / (2 * m) *
          ‖Sm eta L (E.zv s b) - molecularH2Truncate n (Sm eta L (E.zv s b))‖
        ≤ gF L ^ 2 * ((n : ℝ) + 1) ^ 2 / (2 * m) * (2 * m / (gF L ^ 2 * ((n : ℝ) + 1) ^ 2) *
          ‖coulombFourierKineticH2 sys (gF L) (E.zv s b) -
            molecularH2Truncate n (coulombFourierKineticH2 sys (gF L) (E.zv s b))‖) := by
          gcongr
      _ = _ := by rw [← mul_assoc, e, one_mul]
  -- `H z = S zv (ν - c) a`, so `(1 - P) H z = tailOp a''`
  have hHz : ∀ b : EuclideanSpace ℂ s, H (E.zv s b) = Sm eta L (E.zv s
      (WithLp.toLp 2 (fun k => ((E.nu k - c : ℝ) : ℂ) * b k))) := by
    intro b
    rw [E.H_zv, E.sm_zv]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    ring
  have hb'' : ∀ b : EuclideanSpace ℂ s,
      ‖(WithLp.toLp 2 (fun k => ((E.nu k - c : ℝ) : ℂ) * b k) : EuclideanSpace ℂ s)‖ ≤
        (Λ + c) * ‖b‖ := by
    intro b
    refine norm_le_of_coord (by linarith) fun k => ?_
    change ‖((E.nu k - c : ℝ) : ℂ) * b k‖ ≤ (Λ + c) * ‖b k‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have h1 := E.one_le k
    have h2 := hs k k.2
    rw [abs_le]
    constructor <;> linarith
  -- the potential tail
  have hW : ∀ b : EuclideanSpace ℂ s,
      ‖Wp sys L H (E.zv s b) - molecularH2Truncate n (Wp sys L H (E.zv s b))‖ ≤
        cWt sys L Hunit * cZ sys L Hunit / Real.sqrt K * ‖b‖ := by
    intro b
    refine (W_tail_le sys H hKernel Hunit hL hPeriodic n hK1 hK2 (E.zv s b)).trans ?_
    have hz := zv_budget sys H hKernel Hunit hL hPeriodic E hcdef s b
    rw [div_mul_eq_mul_div, mul_assoc]
    gcongr
  -- assemble: `(K²/(2m̄)) ‖tailOp b‖ ≤ N (Λ + c) ‖b‖ + C_W c_z/√K ‖b‖`
  have hstep : ∀ b : EuclideanSpace ℂ s, K ^ 2 / (2 * m) * ‖E.tailOp n s b‖ ≤
      (N * (Λ + c) + cWt sys L Hunit * cZ sys L Hunit / Real.sqrt K) * ‖b‖ := by
    intro b
    refine (hkin b).trans ?_
    have hT : coulombFourierKineticH2 sys (gF L) (E.zv s b) =
        H (E.zv s b) - Wp sys L H (E.zv s b) :=
      by
        have := coulombFourierHamiltonianH2_decomposition sys (gF L) H (E.zv s b)
        rw [this]
        abel
    have hsplit : coulombFourierKineticH2 sys (gF L) (E.zv s b) -
        molecularH2Truncate n (coulombFourierKineticH2 sys (gF L) (E.zv s b)) =
        E.tailOp n s (WithLp.toLp 2 (fun k => ((E.nu k - c : ℝ) : ℂ) * b k)) -
          (Wp sys L H (E.zv s b) - molecularH2Truncate n (Wp sys L H (E.zv s b))) := by
      classical
      rw [E.tailOp_apply, ← hHz, hT]
      change _ - lpTruncateCLM (fourierConfigCube eta n) _ =
        _ - lpTruncateCLM (fourierConfigCube eta n) _ -
          (_ - lpTruncateCLM (fourierConfigCube eta n) _)
      rw [map_sub]
      abel
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    have h1 := (E.tailOp n s).le_opNorm (WithLp.toLp 2 (fun k => ((E.nu k - c : ℝ) : ℂ) * b k))
    have h2 := hb'' b
    rw [add_mul]
    refine add_le_add ?_ (hW b)
    calc ‖E.tailOp n s (WithLp.toLp 2 (fun k => ((E.nu k - c : ℝ) : ℂ) * b k))‖
        ≤ N * ‖(WithLp.toLp 2 (fun k => ((E.nu k - c : ℝ) : ℂ) * b k) : EuclideanSpace ℂ s)‖ := h1
      _ ≤ N * ((Λ + c) * ‖b‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = N * (Λ + c) * ‖b‖ := by ring
  -- absorb
  have hΛc : 0 ≤ Λ + c := by linarith
  have hNle : N ≤ (2 * m / K ^ 2) * (N * (Λ + c) + cWt sys L Hunit * cZ sys L Hunit /
      Real.sqrt K) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b => ?_
    have h := hstep b
    have hpos : 0 < K ^ 2 / (2 * m) := by positivity
    calc ‖E.tailOp n s b‖ = (2 * m / K ^ 2) * (K ^ 2 / (2 * m) * ‖E.tailOp n s b‖) := by
          field_simp
      _ ≤ (2 * m / K ^ 2) * ((N * (Λ + c) + cWt sys L Hunit * cZ sys L Hunit /
            Real.sqrt K) * ‖b‖) := by gcongr
      _ = _ := by ring
  have hN0 : 0 ≤ N := norm_nonneg _
  have hfinal : N ≤ cAbs sys L Hunit / (K ^ 2 * Real.sqrt K) := by
    have hK2pos : 0 < K ^ 2 := by positivity
    have h1 : (2 * m / K ^ 2) * (N * (Λ + c)) ≤ N / 2 := by
      have : (2 * m / K ^ 2) * (Λ + c) ≤ 1 / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hK2pos]
        rw [le_div_iff₀ (by positivity)] at hΛ
        nlinarith
      nlinarith
    have hd : (2 * m / K ^ 2) * (N * (Λ + c) + cWt sys L Hunit * cZ sys L Hunit /
        Real.sqrt K) = (2 * m / K ^ 2) * (N * (Λ + c)) +
          (2 * m / K ^ 2) * (cWt sys L Hunit * cZ sys L Hunit / Real.sqrt K) := by ring
    have h2 : N / 2 ≤ (2 * m / K ^ 2) * (cWt sys L Hunit * cZ sys L Hunit / Real.sqrt K) := by
      linarith
    rw [le_div_iff₀ (by positivity)]
    have e : (2 * m / K ^ 2) * (cWt sys L Hunit * cZ sys L Hunit / Real.sqrt K) * 2 *
        (K ^ 2 * Real.sqrt K) = cAbs sys L Hunit := by
      unfold cAbs
      field_simp
      ring
    have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt (by positivity : (0 : ℝ) < 2 * (K ^ 2 *
      Real.sqrt K)))
    nlinarith
  calc ‖E.tailOp n s a‖ ≤ N * ‖a‖ := (E.tailOp n s).le_opNorm a
    _ ≤ cAbs sys L Hunit / (K ^ 2 * Real.sqrt K) * ‖a‖ :=
        mul_le_mul_of_nonneg_right hfinal (norm_nonneg _)

end Absorption

end KineticLog
