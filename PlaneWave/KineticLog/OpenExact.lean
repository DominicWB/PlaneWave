import PlaneWave.KineticLog.GridSpin
import PlaneWave.FreeBoundary.GridObservablePhysical

/-!
# Logarithmic kinetic bound, part 17: the exact side of the isolated (range-cut) cell

`prop:free-kinetic-log` compares the free-space evolution with the grid through the exact evolution
of the cell Hamiltonian `H_L` with the range-cut interaction `g_L` (`eq:rangecut`, zero mode
removed, `PlaneWave.FreeBoundary.CompletedHamiltonian`).  The proof of `thm:kinetic-log` is reused
on the cell, with every constant uniform in the cell side `L ≥ 2π` (`g = 2π/L ≤ 1`).  This file
supplies the exact-side inputs:

* **`gL_form_lower`**: `Re⟨S u, H_L u⟩ ≥ -(B² + 1/4) ‖S u‖²` on the whole `H²` domain, from the
  finite-cube bound (`gLpot_massBound`, mass-weighted `H¹` constant `B = gLmassConst`) and the
  limit of cubic truncations; **`Hs_lower_gL`**: `H_L + c ≥ 1` with the resolvent shift
  `c = 4K + 2`, `K = gLrelConst`;
* **`exists_exactEigen_gL`**: an eigen-decomposition `ExactEigen L H_L c` of `H_L + c`
  (Hilbert basis
  of eigenvectors with `H²` preimages, eigenvalues `≥ 1`, finitely many below every level), from
  the compact symmetric resolvent of `PlaneWave.FreeBoundary.Propagator`;
* the uniform constants: `cU = 4 K_U + 2` with `K_U = B_U²(4 B_U² + 2)`, `B_U = gLmassConstU`
  (`shift_gL_eq_U`: the shift does not depend on `L ≥ 2π`);
* the eigen-coordinate identities for a symmetric `H` (`inner_b_H_of_symm`, `inner_b_Hs2_of_symm`);
* **`W_tail_le_gL`** (`eq:kinetic-generic-tails` for `g_L`):
  `‖(1 - P) W u‖ ≤ C_W (‖S u‖ + 2‖T u‖)/√K`
  with the `L`-free `C_W = η C_tail^U m̄`;
* **`zv_budget_gL`**, **`norm_tail_zv_gL`** (`lem:kinetic-low`, exact side, uniform in `L`): the
  inverse-weighted low-energy states have `K^{-5/2}` momentum tails, with the `L`-free absorption
  constant `C_abs^U = 4 m̄ C_W c_z^U`; and the same for a larger common shift
  (`zv_budget_shift_gL`, `norm_tail_zv_shift_gL`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FSNormal

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The form lower bound and the eigen-decomposition of `H_L` -/

section GLExact

variable (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (FreeBoundary.gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hθ : FreeBoundary.Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

lemma gLmassConst_nonneg' (hθ : FreeBoundary.Profile R θ) :
    0 ≤ FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit := by
  unfold FreeBoundary.gLmassConst
  have := sys.massCouplingWeight_nonneg
  have := hθ.tv_nonneg
  have := tB_nonneg (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L)
  have : 0 ≤ 1 + FreeBoundary.tv R θ := by linarith
  positivity

include hKernel hL hθ hPeriodic in
/-- **The form lower bound of `H_L` on `H²`**: `Re⟨S u, H_L u⟩ ≥ -(B² + 1/4) ‖S u‖²`, with the
mass-weighted `H¹` constant `B = gLmassConst` of the `g_L` potential. -/
theorem gL_form_lower (u : MolecularFourierH2 eta) :
    -(FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit ^ 2 + 1 / 4) *
        ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ ^ 2 ≤
      (⟪molecularH2StateMap eta (2 * Real.pi / L) u, H u⟫_ℂ).re := by
  set g := 2 * Real.pi / L with hg
  have hB0 := gLmassConst_nonneg' sys (L := L) Hunit hθ
  have hfin : ∀ N : ℕ, -(FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit ^ 2 + 1 / 4) *
      ‖molecularH2StateMap eta g (molecularH2Truncate N u)‖ ^ 2 ≤
      (⟪molecularH2StateMap eta g (molecularH2Truncate N u),
          H (molecularH2Truncate N u)⟫_ℂ).re := by
    intro N
    have hmpos : ∀ a, 0 < sys.mass a := fun a => sys.mass_pos a
    have h := diagHamiltonian_form_lower_bound_of_weightedBound
      (massKineticSymbol sys.mass (finitePlaneWaveKabs g N))
      (fun p => massKineticSymbol_nonneg hmpos _ p) (FreeBoundary.gLpot sys L θ N) hB0
      (FreeBoundary.gLpot_massBound sys hL hθ Hunit hPeriodic N)
      (fullCoeffVector (finiteFourierCoeffExtract N (molecularH2Coeff g u)))
    rw [FreeBoundary.gL_truncation_norm_eq u g N,
      FreeBoundary.gL_truncation_inner_eq sys L θ H hKernel u N]
    exact h
  have hT := molecularH2Truncate_tendsto u
  have hS1 : Tendsto (fun N => molecularH2StateMap eta g (molecularH2Truncate N u)) atTop
      (𝓝 (molecularH2StateMap eta g u)) :=
    ((molecularH2StateMap eta g).continuous.tendsto u).comp hT
  have hH1 : Tendsto (fun N => H (molecularH2Truncate N u)) atTop (𝓝 (H u)) :=
    (H.continuous.tendsto u).comp hT
  have hlim : Tendsto (fun N => (⟪molecularH2StateMap eta g (molecularH2Truncate N u),
      H (molecularH2Truncate N u)⟫_ℂ).re +
        (FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit ^ 2 + 1 / 4) *
          ‖molecularH2StateMap eta g (molecularH2Truncate N u)‖ ^ 2) atTop
      (𝓝 ((⟪molecularH2StateMap eta g u, H u⟫_ℂ).re +
        (FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit ^ 2 + 1 / 4) *
          ‖molecularH2StateMap eta g u‖ ^ 2)) := by
    refine Tendsto.add (Complex.continuous_re.continuousAt.tendsto.comp (hS1.inner hH1)) ?_
    exact tendsto_const_nhds.mul ((continuous_norm.tendsto _).comp hS1 |>.pow 2)
  have h0 : (0 : ℝ) ≤ (⟪molecularH2StateMap eta g u, H u⟫_ℂ).re +
      (FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit ^ 2 + 1 / 4) *
        ‖molecularH2StateMap eta g u‖ ^ 2 :=
    ge_of_tendsto hlim (Eventually.of_forall fun N => by
      have := hfin N
      linarith)
  linarith

/-- The resolvent shift `c = 4K + 2`, `K = gLrelConst`, of the `g_L` Hamiltonian. -/
noncomputable def shiftGL (sys : CoulombSystem eta ν) (L V Hunit : ℝ) : ℝ :=
  FreeBoundary.relShift (FreeBoundary.gLrelConst sys L V Hunit)

lemma two_le_shiftGL (L V Hunit : ℝ) : 2 ≤ shiftGL sys L V Hunit :=
  FreeBoundary.two_le_relShift (FreeBoundary.gLrelConst_nonneg sys L V Hunit)

include hKernel hL hθ hPeriodic in
/-- **`H_L + c ≥ 1`** in the form sense on `H²`, with the resolvent shift `c = shiftGL`. -/
lemma Hs_lower_gL (u : MolecularFourierH2 eta) :
    ‖Sm eta L u‖ ^ 2 ≤
      (⟪Sm eta L u, H u + (shiftGL sys L (FreeBoundary.tv R θ) Hunit : ℂ) • Sm eta L u⟫_ℂ).re := by
  have h := gL_form_lower sys H hKernel Hunit hL hθ hPeriodic u
  have hS : Sm eta L u = molecularH2StateMap eta (2 * Real.pi / L) u := rfl
  set B := FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit with hB
  have hc : shiftGL sys L (FreeBoundary.tv R θ) Hunit = 4 * (B ^ 2 * (4 * B ^ 2 + 2)) + 2 := rfl
  have e : (⟪molecularH2StateMap eta (2 * Real.pi / L) u,
      (shiftGL sys L (FreeBoundary.tv R θ) Hunit : ℂ) •
        molecularH2StateMap eta (2 * Real.pi / L) u⟫_ℂ).re =
      shiftGL sys L (FreeBoundary.tv R θ) Hunit *
          ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ ^ 2 := by
    rw [inner_smul_right, Complex.re_ofReal_mul]
    congr 1
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (molecularH2StateMap eta (2 * Real.pi / L) u)
    simpa using this
  rw [hS, inner_add_right, Complex.add_re, e, hc]
  have hX := sq_nonneg ‖molecularH2StateMap eta (2 * Real.pi / L) u‖
  have hB2 := sq_nonneg B
  have hkey : (B ^ 2 + 1 / 4 + 1) * ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ ^ 2 ≤
      (4 * (B ^ 2 * (4 * B ^ 2 + 2)) + 2) * ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ hX
    nlinarith [sq_nonneg (B ^ 2)]
  linarith

include hKernel hL hθ hPeriodic in
/-- **The cell Hamiltonian `H_L` has an eigen-decomposition** with the resolvent shift
`c = shiftGL`: the eigenbasis of the compact symmetric resolvent `S (H_L + c S)⁻¹`. -/
theorem exists_exactEigen_gL :
    Nonempty (ExactEigen L H (shiftGL sys L (FreeBoundary.tv R θ) Hunit)) := by
  set K := FreeBoundary.gLrelConst sys L (FreeBoundary.tv R θ) Hunit with hKdef
  have hK0 : 0 ≤ K := FreeBoundary.gLrelConst_nonneg sys L _ Hunit
  have hrel : FreeBoundary.HasRelBound sys L H K :=
    FreeBoundary.gL_potential_sq_le_quarter sys hL hθ H hKernel Hunit hPeriodic
  have hsym := FreeBoundary.gLH2_symm sys L θ H hKernel hθ
  set R' := FreeBoundary.resolventRK sys L H hK0 hrel with hRdef
  set G := FreeBoundary.resolventGK sys L H hK0 hrel with hGdef
  set c := shiftGL sys L (FreeBoundary.tv R θ) Hunit with hc
  have hsymm := FreeBoundary.resolventRK_symm sys L H hK0 hrel hsym
  have hcomp := FreeBoundary.resolventRK_compact sys L H hK0 hL hrel
  obtain ⟨ι, b, μ, hb⟩ := exists_eigen_hilbertBasis hcomp hsymm
  set m : ι → ℝ := fun i => (μ i).re with hmdef
  have hRb : ∀ i, R' (b i) = (m i : ℂ) • b i := fun i => by
    rw [hb]
    simp only [hmdef]
    rw [eigen_real b μ hsymm hb i]
  have hSG : ∀ i, Sm eta L (G (b i)) = (m i : ℂ) • b i := hRb
  have hHG : ∀ i, H (G (b i)) + (c : ℂ) • Sm eta L (G (b i)) = b i := fun i =>
    FreeBoundary.H_add_shift_resolventGK sys L H hK0 hrel (b i)
  have hm : ∀ i, 0 < m i ∧ m i ≤ 1 := by
    intro i
    have hlow := Hs_lower_gL sys H hKernel Hunit hL hθ hPeriodic (G (b i))
    rw [hHG, hSG, norm_smul, b.orthonormal.1 i, inner_smul_left, inner_self_eq_norm_sq_to_K,
      b.orthonormal.1 i, Complex.norm_real, Real.norm_eq_abs, Complex.conj_ofReal] at hlow
    have hm0 : m i ≠ 0 := by
      intro h0
      have h1 : R' (b i) = R' 0 := by rw [hRb, h0, Complex.ofReal_zero, zero_smul, map_zero]
      have h2 := FreeBoundary.resolventRK_injective sys L H hK0 hrel h1
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
    · refine (finite_eigen_ge hcomp b.orthonormal hRb (ε := Λ⁻¹) (by positivity)).subset ?_
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

end GLExact

/-! ## The `L`-free constants of the exact side -/

section UConst

variable (sys : CoulombSystem eta ν) (V Hunit : ℝ)

/-- The `L`-free resolvent shift `c_U = 4 K_U + 2`, `K_U = B_U² (4 B_U² + 2)`,
`B_U = gLmassConstU`. -/
noncomputable def cU : ℝ :=
  4 * (PlaneWaveGridG.gLmassConstU sys V Hunit ^ 2 *
    (4 * PlaneWaveGridG.gLmassConstU sys V Hunit ^ 2 + 2)) + 2

lemma two_le_cU : 2 ≤ cU sys V Hunit := by
  unfold cU
  have := sq_nonneg (PlaneWaveGridG.gLmassConstU sys V Hunit)
  nlinarith

/-- The shift does not depend on `L ≥ 2π`. -/
lemma shift_gL_eq_U {L : ℝ} (hL : 2 * Real.pi ≤ L) (hH : 0 ≤ Hunit) :
    shiftGL sys L V Hunit = cU sys V Hunit := by
  unfold shiftGL FreeBoundary.relShift FreeBoundary.gLrelConst cU
  rw [FreeBoundary.gLmassConst_eq_U sys hL V hH]

/-- The potential-tail constant per unit `H²` budget, `C_W = η C_tail^U(1) m̄`. -/
noncomputable def cWtU : ℝ := eta * FreeBoundary.gLtailMU sys V Hunit 1 * sys.maxMass

/-- The budget constant `c_z = 1 + 2 (2 (1 + c_U) + 2 b_U)`. -/
noncomputable def cZU : ℝ := 1 + 2 * (2 * (1 + cU sys V Hunit) + 2 * FreeBoundary.relBU sys V Hunit)

/-- The absorption constant `C_abs^U = 4 m̄ C_W c_z`. -/
noncomputable def cAbsU : ℝ := 4 * sys.maxMass * cWtU sys V Hunit * cZU sys V Hunit

variable {sys V Hunit}

lemma gLtailMU_linear (M : ℝ) :
    FreeBoundary.gLtailMU sys V Hunit M = FreeBoundary.gLtailMU sys V Hunit 1 * M := by
  unfold FreeBoundary.gLtailMU
  ring

lemma gLtailMU_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ FreeBoundary.gLtailMU sys V Hunit M := by
  unfold FreeBoundary.gLtailMU
  have := sys.couplingWeight_nonneg
  have : 0 ≤ PlaneWaveGridG.ctailU Hunit := by
    unfold PlaneWaveGridG.ctailU PlaneWaveGridG.tBU
    positivity
  have : 0 ≤ 1 + V := by linarith
  positivity

lemma cWtU_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ cWtU sys V Hunit := by
  unfold cWtU
  have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
  have := sys.one_le_maxMass
  positivity

lemma cZU_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ cZU sys V Hunit := by
  unfold cZU
  have := two_le_cU sys V Hunit
  have := FreeBoundary.relBU_nonneg sys hV hH
  positivity

lemma cAbsU_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ cAbsU sys V Hunit := by
  unfold cAbsU
  have := cWtU_nonneg (sys := sys) hV hH
  have := cZU_nonneg (sys := sys) hV hH
  have := sys.one_le_maxMass
  positivity

end UConst

/-! ## Eigen-coordinates for a symmetric `H` -/

namespace ExactEigen

variable {L c : ℝ}
  {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}
  (E : ExactEigen L H c)
  (hsym : ∀ u u' : MolecularFourierH2 eta,
    ⟪molecularH2StateMap eta (2 * Real.pi / L) u, H u'⟫_ℂ =
      ⟪H u, molecularH2StateMap eta (2 * Real.pi / L) u'⟫_ℂ)

include hsym in
/-- `⟪b_i, H x⟫ = (ν_i - c) ⟪b_i, S x⟫` for a symmetric `H`. -/
lemma inner_b_H_of_symm (i : E.ι) (x : MolecularFourierH2 eta) :
    ⟪E.b i, H x⟫_ℂ = ((E.nu i - c : ℝ) : ℂ) * ⟪E.b i, Sm eta L x⟫_ℂ := by
  have h := hsym (E.w i) x
  have hS : molecularH2StateMap eta (2 * Real.pi / L) (E.w i) = E.b i := E.sm_w i
  rw [hS, E.H_w i, inner_smul_left, Complex.conj_ofReal] at h
  exact h

include hsym in
lemma inner_b_Hs_of_symm (i : E.ι) (x : MolecularFourierH2 eta) :
    ⟪E.b i, H x + (c : ℂ) • Sm eta L x⟫_ℂ = (E.nu i : ℂ) * ⟪E.b i, Sm eta L x⟫_ℂ := by
  rw [inner_add_right, inner_smul_right, E.inner_b_H_of_symm hsym]
  push_cast
  ring

include hsym in
/-- `⟪b_i, (H + c)² ψ₀⟫ = ν_i² ⟪b_i, ψ₀⟫` for a symmetric `H`. -/
lemma inner_b_Hs2_of_symm (D : EvoData L H) (i : E.ι) :
    ⟪E.b i, Hs2 (c := c) D⟫_ℂ = (E.nu i : ℂ) ^ 2 * ⟪E.b i, Sm eta L D.u₀⟫_ℂ := by
  unfold Hs2
  rw [E.inner_b_Hs_of_symm hsym]
  have hS : Sm eta L (D.v₀ + (c : ℂ) • D.u₀) = H D.u₀ + (c : ℂ) • Sm eta L D.u₀ := by
    rw [map_add, map_smul, ← D.uv]
  rw [hS, E.inner_b_Hs_of_symm hsym]
  ring

end ExactEigen

/-! ## Potential tails and absorption for `H_L`, uniform in `L` -/

section GLTails

variable (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (FreeBoundary.gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 2 * Real.pi ≤ L) (hθ : FreeBoundary.Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hH : 0 ≤ Hunit)

lemma pos_of_two_pi_le (hL : 2 * Real.pi ≤ L) : 0 < L := lt_of_lt_of_le (by positivity) hL

include hKernel hL hθ hPeriodic hH in
/-- **Generic potential tail of `H_L`** (`eq:kinetic-generic-tails`, uniform in `L ≥ 2π`): for
`K = g n ≥ 1`, `‖(1 - P) W u‖ ≤ C_W (‖S u‖ + 2 ‖T u‖) / √K`. -/
theorem W_tail_le_gL (n : ℕ) (hK1 : 1 ≤ gF L * n) (u : MolecularFourierH2 eta) :
    ‖Wp sys L H u - molecularH2Truncate n (Wp sys L H u)‖ ≤
      cWtU sys (FreeBoundary.tv R θ) Hunit *
        (‖Sm eta L u‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) u‖) / Real.sqrt (gF L * n) := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  set M₂ := sys.maxMass * (‖Sm eta L u‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) u‖) with hM₂
  have hu : ‖u‖ ≤ M₂ := h2norm_le sys L u
  have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) hu
  have hρ : Real.sqrt (1 / K) ^ 2 * K = 1 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have ht : ∀ a, ‖tailMask (gF L) K a (Wp sys L H u)‖ ≤
      FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit M₂ * Real.sqrt (1 / K) := by
    intro a
    have h := FreeBoundary.potential_tail_le_gL sys L H hKernel Hunit hL0 hθ hPeriodic a K
      (Real.sqrt (1 / K)) M₂ hK1 (Real.sqrt_nonneg _) hρ hM₂0 u hu
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    exact FreeBoundary.gLtailM_le_U sys hL hV hH hM₂0
  have hsq : Real.sqrt (1 / K) = 1 / Real.sqrt K := by
    rw [Real.sqrt_div' 1 hK0.le, Real.sqrt_one]
  calc ‖Wp sys L H u - molecularH2Truncate n (Wp sys L H u)‖
      ≤ ∑ a : Fin eta, ‖tailMask (gF L) K a (Wp sys L H u)‖ :=
        PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL0) n _
    _ ≤ ∑ _a : Fin eta, FreeBoundary.gLtailMU sys (FreeBoundary.tv R θ) Hunit M₂ *
          Real.sqrt (1 / K) := Finset.sum_le_sum fun a _ => ht a
    _ = cWtU sys (FreeBoundary.tv R θ) Hunit *
          (‖Sm eta L u‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) u‖) / Real.sqrt K := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, gLtailMU_linear,
          hsq, hM₂]
        unfold cWtU
        ring

include hKernel hL hθ hPeriodic hH in
/-- `‖S zv‖ + 2 ‖T zv‖ ≤ c_z ‖a‖` for the low-energy combinations of `H_L` (uniform in `L`). -/
lemma zv_budget_gL {c : ℝ} (E : ExactEigen L H c)
    (hcdef : c = cU sys (FreeBoundary.tv R θ) Hunit)
    (s : Finset E.ι) (a : EuclideanSpace ℂ s) :
    ‖Sm eta L (E.zv s a)‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) (E.zv s a)‖ ≤
      cZU sys (FreeBoundary.tv R θ) Hunit * ‖a‖ := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  have hc : 2 ≤ c := hcdef ▸ two_le_cU sys _ Hunit
  have hC : 0 ≤ FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit :=
    gLmassConst_nonneg' sys (L := L) Hunit hθ
  have hbU := FreeBoundary.relBU_nonneg sys hV hH
  have hS : ‖Sm eta L (E.zv s a)‖ ≤ 1 * ‖a‖ := by
    rw [E.sm_zv]
    refine E.norm_combo_le s a (fun k => a k / (E.nu k : ℂ)) zero_le_one fun k => ?_
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (E.nu_pos k), one_mul]
    exact div_le_self (norm_nonneg _) (E.one_le k)
  have hHz : ‖H (E.zv s a)‖ ≤ (1 + c) * ‖a‖ := by
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
  have hT := FreeBoundary.kinetic_le_elliptic_gL sys L H hKernel Hunit hL0 hθ hPeriodic hC
    (E.zv s a)
  rw [FreeBoundary.relB_gL_eq_U sys hL _ hH] at hT
  change ‖coulombFourierKineticH2 sys (gF L) (E.zv s a)‖ ≤
    2 * ‖H (E.zv s a)‖ + 2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit *
      ‖Sm eta L (E.zv s a)‖ at hT
  unfold cZU
  rw [← hcdef]
  have ha := norm_nonneg a
  have h1 : 2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * ‖Sm eta L (E.zv s a)‖ ≤
      2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * ‖a‖ := by
    have := mul_le_mul_of_nonneg_left hS (by positivity :
      (0 : ℝ) ≤ 2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit)
    linarith
  have e : (1 + 2 * (2 * (1 + c) + 2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit)) * ‖a‖ =
      1 * ‖a‖ + 2 * (2 * ((1 + c) * ‖a‖) +
        2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * ‖a‖) := by ring
  rw [e]
  linarith

include hKernel hL hθ hPeriodic hH in
/-- **Inverse-weighted low-energy states of `H_L` have `K^{-5/2}` momentum tails**
(`lem:kinetic-low`, exact side, uniform in `L ≥ 2π`): if `ν_k ≤ Λ` on `s` and
`Λ + c ≤ K²/(4 m̄)` with `K = g n ≥ 1`, then `‖(1 - P) S zv s a‖ ≤ C_abs^U / (K² √K) ‖a‖`. -/
theorem norm_tail_zv_gL {c : ℝ} (E : ExactEigen L H c)
    (hcdef : c = cU sys (FreeBoundary.tv R θ) Hunit) (n : ℕ)
    (hK1 : 1 ≤ gF L * n) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : Λ + c ≤ (gF L * n) ^ 2 / (4 * sys.maxMass))
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) (a : EuclideanSpace ℂ s) :
    ‖E.tailOp n s a‖ ≤
      cAbsU sys (FreeBoundary.tv R θ) Hunit / ((gF L * n) ^ 2 * Real.sqrt (gF L * n)) * ‖a‖ := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  set K := gF L * n with hKdef
  set m := sys.maxMass
  have hm : 1 ≤ m := sys.one_le_maxMass
  have hc : 2 ≤ c := hcdef ▸ two_le_cU sys _ Hunit
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hg := gF_pos hL0
  set N := ‖E.tailOp n s‖ with hN
  set CW := cWtU sys (FreeBoundary.tv R θ) Hunit with hCWdef
  set CZ := cZU sys (FreeBoundary.tv R θ) Hunit with hCZdef
  have hCW : 0 ≤ CW := cWtU_nonneg hV hH
  have hcz : 0 ≤ CZ := cZU_nonneg hV hH
  -- the kinetic lower bound off the cube
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
  have hW : ∀ b : EuclideanSpace ℂ s,
      ‖Wp sys L H (E.zv s b) - molecularH2Truncate n (Wp sys L H (E.zv s b))‖ ≤
        CW * CZ / Real.sqrt K * ‖b‖ := by
    intro b
    refine (W_tail_le_gL sys H hKernel Hunit hL hθ hPeriodic hH n hK1 (E.zv s b)).trans ?_
    have hz := zv_budget_gL sys H hKernel Hunit hL hθ hPeriodic hH E hcdef s b
    rw [div_mul_eq_mul_div, mul_assoc]
    gcongr
  have hstep : ∀ b : EuclideanSpace ℂ s, K ^ 2 / (2 * m) * ‖E.tailOp n s b‖ ≤
      (N * (Λ + c) + CW * CZ / Real.sqrt K) * ‖b‖ := by
    intro b
    refine (hkin b).trans ?_
    have hT : coulombFourierKineticH2 sys (gF L) (E.zv s b) =
        H (E.zv s b) - Wp sys L H (E.zv s b) := by
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
        ≤ N * ‖(WithLp.toLp 2 (fun k => ((E.nu k - c : ℝ) : ℂ) * b k) : EuclideanSpace ℂ s)‖ :=
          h1
      _ ≤ N * ((Λ + c) * ‖b‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = N * (Λ + c) * ‖b‖ := by ring
  have hΛc : 0 ≤ Λ + c := by linarith
  have hNle : N ≤ (2 * m / K ^ 2) * (N * (Λ + c) + CW * CZ / Real.sqrt K) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b => ?_
    have h := hstep b
    calc ‖E.tailOp n s b‖ = (2 * m / K ^ 2) * (K ^ 2 / (2 * m) * ‖E.tailOp n s b‖) := by
          field_simp
      _ ≤ (2 * m / K ^ 2) * ((N * (Λ + c) + CW * CZ / Real.sqrt K) * ‖b‖) := by gcongr
      _ = _ := by ring
  have hN0 : 0 ≤ N := norm_nonneg _
  have hfinal : N ≤ cAbsU sys (FreeBoundary.tv R θ) Hunit / (K ^ 2 * Real.sqrt K) := by
    have hK2pos : 0 < K ^ 2 := by positivity
    have hq : (2 * m / K ^ 2) * (Λ + c) ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hK2pos]
      rw [le_div_iff₀ (by positivity)] at hΛ
      linarith
    have h1 : (2 * m / K ^ 2) * (N * (Λ + c)) ≤ N / 2 := by
      have := mul_le_mul_of_nonneg_left hq hN0
      calc (2 * m / K ^ 2) * (N * (Λ + c)) = N * ((2 * m / K ^ 2) * (Λ + c)) := by ring
        _ ≤ N * (1 / 2) := this
        _ = N / 2 := by ring
    have hd : (2 * m / K ^ 2) * (N * (Λ + c) + CW * CZ / Real.sqrt K) =
        (2 * m / K ^ 2) * (N * (Λ + c)) + (2 * m / K ^ 2) * (CW * CZ / Real.sqrt K) := by ring
    have h2 : N / 2 ≤ (2 * m / K ^ 2) * (CW * CZ / Real.sqrt K) := by linarith
    have e : (2 * m / K ^ 2) * (CW * CZ / Real.sqrt K) * 2 = cAbsU sys (FreeBoundary.tv R θ) Hunit /
        (K ^ 2 * Real.sqrt K) := by
      unfold cAbsU
      rw [← hCWdef, ← hCZdef]
      field_simp
      ring
    linarith
  calc ‖E.tailOp n s a‖ ≤ N * ‖a‖ := (E.tailOp n s).le_opNorm a
    _ ≤ cAbsU sys (FreeBoundary.tv R θ) Hunit / (K ^ 2 * Real.sqrt K) * ‖a‖ :=
        mul_le_mul_of_nonneg_right hfinal (norm_nonneg _)

include hKernel hL hθ hPeriodic hH in
/-- The budget of the shifted combinations of `H_L`: `‖S zv'‖ + 2 ‖T zv'‖ ≤ c_z ‖a‖`. -/
lemma zv_budget_shift_gL {c : ℝ} (E : ExactEigen L H c)
    (hcdef : c = cU sys (FreeBoundary.tv R θ) Hunit) {d : ℝ}
    (hd : 0 ≤ d) (s : Finset E.ι) (a : EuclideanSpace ℂ s) :
    ‖Sm eta L ((E.shift d hd).zv s a)‖ +
        2 * ‖coulombFourierKineticH2 sys (gF L) ((E.shift d hd).zv s a)‖ ≤
      cZU sys (FreeBoundary.tv R θ) Hunit * ‖a‖ := by
  rw [E.shift_zv hd]
  refine (zv_budget_gL sys H hKernel Hunit hL hθ hPeriodic hH E hcdef s _).trans ?_
  exact mul_le_mul_of_nonneg_left (E.norm_resc_le hd s a) (cZU_nonneg hθ.tv_nonneg hH)

include hKernel hL hθ hPeriodic hH in
/-- The momentum-tail absorption for the shifted combinations of `H_L`. -/
theorem norm_tail_zv_shift_gL {c : ℝ} (E : ExactEigen L H c)
    (hcdef : c = cU sys (FreeBoundary.tv R θ) Hunit)
    {d : ℝ} (hd : 0 ≤ d) (n : ℕ) (hK1 : 1 ≤ gF L * n) {Λ : ℝ}
    (hΛ1 : 1 ≤ Λ) (hΛ : Λ + c ≤ (gF L * n) ^ 2 / (4 * sys.maxMass))
    (s : Finset E.ι) (hs : ∀ k ∈ s, E.nu k ≤ Λ) (a : EuclideanSpace ℂ s) :
    ‖Sm eta L ((E.shift d hd).zv s a) -
        molecularH2Truncate n (Sm eta L ((E.shift d hd).zv s a))‖ ≤
      cAbsU sys (FreeBoundary.tv R θ) Hunit / ((gF L * n) ^ 2 * Real.sqrt (gF L * n)) * ‖a‖ := by
  rw [E.shift_zv hd]
  have h := norm_tail_zv_gL sys H hKernel Hunit hL hθ hPeriodic hH E hcdef n hK1 hΛ1 hΛ s hs
    (E.resc d s a)
  rw [E.tailOp_apply] at h
  refine h.trans (mul_le_mul_of_nonneg_left (E.norm_resc_le hd s a) ?_)
  have := cAbsU_nonneg (sys := sys) hθ.tv_nonneg hH
  have hK0 : 0 < gF L * n := by linarith
  positivity

end GLTails

end KineticLog
