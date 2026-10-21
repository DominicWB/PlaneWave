import PlaneWave.Source.RetainedHamiltonian

/-!
# Flux/source build, block 1b: the register structure of the Galerkin Hamiltonian

For a register `a` the proof of `lem:qtail` writes `H' = A_a + H_ā + V_a + ΔH`, where `V_a`
collects the interactions containing `a` and `H_ā = H_N - V_a` acts on register `a` only through
its kinetic energy.  On the release's Galerkin space `E_n`:

* `regMul a φ`: multiplication by a function of register `a`'s mode; `RegLocal a T`: `T` commutes
  with every such multiplication (closed under sums and scalar multiples);
* `regLocal_of_kernel`: a kernel operator whose kernel only connects configurations with equal
  register-`a` mode is register-local; this covers the diagonal kinetic operator, the nuclear terms of
  the other registers and the pair terms not containing `a`;
* `Va`, `Hbar`: the interactions containing `a` (the nuclear term of `a` and the pairs containing
  `a`) and `H_ā = H_N - V_a`; `Hbar_regLocal`: `H_ā` is register-local;
* `Va_registerBound`: `‖V_a v‖² ≤ C_a² Σ_p (1 + |k_a|²) |v_p|²` with
  `C_a = (|q_a| Z_tot + Σ_{pairs ∋ a} |q_i q_j|) B_cell`;
* `Hbar_coercive`: for `v` supported in `|k_a| ≥ l`,
  `Re ⟪v, H_ā v⟫ ≥ (l²/(8 m_a) - C_sh) ‖v‖²`, with `C_sh = C_m² + 1/2 + 2 m_a C_a²`
  (coercivity of `H_N` from the release and the Hardy bound of `V_a`; the manuscript uses Coulomb
  stability of the subsystem instead, which gives the constant `1/2` in place of `1/8`);
* `norm_le_of_slice_coercive`: if a register-local `D` satisfies `Re ⟪x, D x⟫ ≥ w(ν) ‖x‖²` on
  every register-`a` slice `{p_a = ν}`, then `‖v‖ ≤ ‖(1/w) D v‖` for `v` supported where `w > 0`
  (the shell-by-shell denominator of the proof of `lem:qtail`, as one weighted estimate).
-/

set_option autoImplicit false

open scoped InnerProductSpace
open PlaneWaveCertificate

namespace FSGalerkin

variable {eta : ℕ} {ν : Type*}

/-! ## Register multipliers and register-local operators -/

section RegMul

variable {n : ℕ}

/-- Multiplication by a function of register `a`'s mode. -/
noncomputable def regMul (a : Fin eta) (φ : FinitePlaneWaveMode n → ℂ) :
    En eta n →ₗ[ℂ] En eta n where
  toFun u := WithLp.toLp 2 (fun p => φ (p a) * u.ofLp p)
  map_add' u v := by
    ext p
    simp [mul_add]
  map_smul' c u := by
    ext p
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] lemma regMul_apply (a : Fin eta) (φ : FinitePlaneWaveMode n → ℂ) (u : En eta n)
    (p : Cfg eta n) : (regMul a φ u).ofLp p = φ (p a) * u.ofLp p := rfl

/-- `T` commutes with every multiplier of register `a`. -/
def RegLocal (a : Fin eta) (T : En eta n →ₗ[ℂ] En eta n) : Prop :=
  ∀ (φ : FinitePlaneWaveMode n → ℂ) (u : En eta n), T (regMul a φ u) = regMul a φ (T u)

variable {a : Fin eta}

lemma RegLocal.add {S T : En eta n →ₗ[ℂ] En eta n} (hS : RegLocal a S) (hT : RegLocal a T) :
    RegLocal a (S + T) := by
  intro φ u
  simp only [LinearMap.add_apply, hS φ u, hT φ u, map_add]

lemma RegLocal.sub {S T : En eta n →ₗ[ℂ] En eta n} (hS : RegLocal a S) (hT : RegLocal a T) :
    RegLocal a (S - T) := by
  intro φ u
  simp only [LinearMap.sub_apply, hS φ u, hT φ u, map_sub]

lemma RegLocal.smul {T : En eta n →ₗ[ℂ] En eta n} (c : ℂ) (hT : RegLocal a T) :
    RegLocal a (c • T) := by
  intro φ u
  simp only [LinearMap.smul_apply, hT φ u, map_smul]

lemma RegLocal.sum {ι : Type*} (s : Finset ι) (T : ι → En eta n →ₗ[ℂ] En eta n)
    (h : ∀ i ∈ s, RegLocal a (T i)) : RegLocal a (∑ i ∈ s, T i) := by
  intro φ u
  simp only [LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi φ u

lemma regLocal_id : RegLocal a (LinearMap.id : En eta n →ₗ[ℂ] En eta n) := by
  intro φ u
  rfl

/-- **Kernel criterion**: a kernel operator whose kernel only connects configurations with the
same register-`a` mode is register-local. -/
lemma regLocal_of_kernel (T : En eta n →ₗ[ℂ] En eta n) (κ : Cfg eta n → Cfg eta n → ℂ)
    (hT : ∀ u q, (T u).ofLp q = ∑ p, u.ofLp p * κ q p)
    (hκ : ∀ q p, κ q p ≠ 0 → q a = p a) : RegLocal a T := by
  intro φ u
  ext q
  rw [hT, regMul_apply, hT, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [regMul_apply]
  by_cases h : κ q p = 0
  · simp [h]
  · rw [hκ q p h]
    ring

lemma regLocal_diagOperator (A : Cfg eta n → ℝ) : RegLocal a (diagOperator A) := by
  intro φ u
  ext p
  simp only [diagOperator_apply, regMul_apply]
  ring

/-- A reference convolution on another register is register-local. -/
lemma regLocal_referenceKernel {b : Fin eta} (hab : a ≠ b)
    (K : FinitePlaneWaveMode n → FinitePlaneWaveMode n → ℂ) :
    RegLocal a (referenceKernelConvolutionOperator b K :
      En eta n →ₗ[ℂ] En eta n) := by
  classical
  refine regLocal_of_kernel _ (referenceConfigurationKernel b K)
    (fun u q => referenceKernelConvolutionOperator_apply b K u q) (fun q p h => ?_)
  by_cases ho : outerConfigOf b q = outerConfigOf b p
  · exact congrFun ho ⟨a, hab⟩
  · exact absurd (referenceConfigurationKernel_of_outer_ne b K q p ho) h

/-- A pair term not containing `a` is register-local. -/
lemma regLocal_pair {i j : Fin eta} (hai : a ≠ i) (haj : a ≠ j) (C : ℝ) :
    RegLocal a (finiteElectronPairCoulombOperator i j C n :
      En eta n →ₗ[ℂ] En eta n) := by
  classical
  refine regLocal_of_kernel _ (finiteElectronPairConfigurationKernel i j C n)
    (fun u q => finiteElectronPairCoulombOperator_apply i j C n u q) (fun q p h => ?_)
  by_cases hl : finiteElectronPairSliceLabel i j n q = finiteElectronPairSliceLabel i j n p
  · exact ((finiteElectronPairSliceLabel_eq_iff i j n q p).mp hl).1 a hai haj
  · exact absurd (finiteElectronPairConfigurationKernel_of_other_fiber i j C n q p hl) h

end RegMul

/-! ## The interactions containing a register -/

section Split

variable [Fintype ν] (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (a : Fin eta)

/-- The unordered pairs containing register `a`. -/
def pairsWith (a : Fin eta) : Finset (FiniteElectronPair eta) :=
  Finset.univ.filter fun pr => pr.1.1 = a ∨ pr.1.2 = a

/-- The nuclear term of register `a`. -/
noncomputable def Vnuc : En eta n →ₗ[ℂ] En eta n :=
  ((-sys.charge a : ℝ) : ℂ) • ∑ ell : ν, referenceKernelConvolutionOperator a
    (finiteElectronNuclearKernel sys.nuclei (coulombCellAmplitude L) n ell)

/-- The pair terms containing register `a`. -/
noncomputable def Vpair : En eta n →ₗ[ℂ] En eta n :=
  ∑ pr ∈ pairsWith a, ((sys.charge pr.1.1 * sys.charge pr.1.2 : ℝ) : ℂ) •
    finiteElectronPairCoulombOperator pr.1.1 pr.1.2 ((coulombCellAmplitude L) ^ 2) n

/-- `V_a`: all interactions containing register `a`. -/
noncomputable def Va : En eta n →ₗ[ℂ] En eta n := Vnuc sys L n a + Vpair sys L n a

/-- `H_ā = H_N - V_a`. -/
noncomputable def Hbar : En eta n →ₗ[ℂ] En eta n := finiteCoulombHamiltonian sys L n - Va sys L n a

/-- `H_ā` is the kinetic operator plus the interactions not containing `a`. -/
lemma Hbar_eq : Hbar sys L n a =
    (1 / 2 : ℂ) • diagOperator (massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n)) +
      ∑ b ∈ Finset.univ.erase a, ((-sys.charge b : ℝ) : ℂ) • ∑ ell : ν,
        referenceKernelConvolutionOperator b
          (finiteElectronNuclearKernel sys.nuclei (coulombCellAmplitude L) n ell) +
      ∑ pr ∈ Finset.univ.filter (fun pr : FiniteElectronPair eta => ¬(pr.1.1 = a ∨ pr.1.2 = a)),
        ((sys.charge pr.1.1 * sys.charge pr.1.2 : ℝ) : ℂ) •
          finiteElectronPairCoulombOperator pr.1.1 pr.1.2 ((coulombCellAmplitude L) ^ 2) n := by
  classical
  unfold Hbar Va Vnuc Vpair pairsWith finiteCoulombHamiltonian diagHamiltonian finiteCoulombPotential
    finiteCoulombNuclearPotential finiteCoulombPairPotential
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun pr : FiniteElectronPair eta => pr.1.1 = a ∨ pr.1.2 = a)]
  abel

/-- **`H_ā` acts on register `a` only through its kinetic energy.** -/
theorem Hbar_regLocal : RegLocal a (Hbar sys L n a) := by
  classical
  rw [Hbar_eq]
  refine ((regLocal_diagOperator _).smul _).add ?_ |>.add ?_
  · refine RegLocal.sum _ _ fun b hb => RegLocal.smul _ (RegLocal.sum _ _ fun ell _ => ?_)
    exact regLocal_referenceKernel (Ne.symm (Finset.ne_of_mem_erase hb)) _
  · refine RegLocal.sum _ _ fun pr hpr => RegLocal.smul _ ?_
    rw [Finset.mem_filter, not_or] at hpr
    exact regLocal_pair (Ne.symm hpr.2.1) (Ne.symm hpr.2.2) _

lemma HN_eq_Hbar_add : finiteCoulombHamiltonian sys L n = Hbar sys L n a + Va sys L n a := by
  unfold Hbar
  abel

end Split

/-! ## The Hardy bound of `V_a` on the `H¹` space of register `a` -/

section Hardy

variable [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) (n : ℕ) (a : Fin eta)

/-- The charge weight of the interactions containing `a`. -/
noncomputable def chargeA (sys : CoulombSystem eta ν) (a : Fin eta) : ℝ :=
  |sys.charge a| * sys.nuclei.totalCharge +
    ∑ pr ∈ pairsWith a, |sys.charge pr.1.1 * sys.charge pr.1.2|

lemma chargeA_nonneg : 0 ≤ chargeA sys a := by
  unfold chargeA
  have h1 := mul_nonneg (abs_nonneg (sys.charge a)) sys.nuclei.totalCharge_nonneg
  have h2 : 0 ≤ ∑ pr ∈ pairsWith a, |sys.charge pr.1.1 * sys.charge pr.1.2| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

/-- The Hardy constant `C_a` of `V_a` on the `H¹` space of register `a`. -/
noncomputable def CVa (sys : CoulombSystem eta ν) (L Hunit : ℝ) (a : Fin eta) : ℝ :=
  chargeA sys a * coulombPhysicalCellConstant L Hunit

lemma CVa_nonneg (L : ℝ) : 0 ≤ CVa sys L Hunit a :=
  mul_nonneg (chargeA_nonneg sys a) (coulombPhysicalCellConstant_nonneg L Hunit)

/-- The register-`a` weight `1 + |k_a|²`. -/
noncomputable def regWeight (L : ℝ) (n : ℕ) (a : Fin eta) (p : Cfg eta n) : ℝ :=
  1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2

lemma regWeight_nonneg (L : ℝ) (p : Cfg eta n) : 0 ≤ regWeight L n a p := by
  unfold regWeight; positivity

/-- A pair containing `a` is bounded on the `H¹` space of register `a`. -/
lemma pair_registerBound (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (pr : FiniteElectronPair eta) (hpr : pr ∈ pairsWith a) :
    HasWeightedOperatorBound (regWeight L n a)
      (finiteElectronPairCoulombOperator pr.1.1 pr.1.2 ((coulombCellAmplitude L) ^ 2) n)
      (coulombPhysicalCellConstant L Hunit) := by
  rw [pairsWith, Finset.mem_filter] at hpr
  rcases hpr.2 with h | h
  · have hb := finiteElectronPairCoulombOperator_registerBound_first pr.1.1 pr.1.2 (ne_of_lt pr.2)
      (2 * Real.pi / L) ((coulombCellAmplitude L) ^ 2) (coulombPhysicalCellConstant L Hunit) Hunit n
      (sq_nonneg _) hPeriodic (coulombPhysicalCellConstant_scale L Hunit hL)
    have hw : (fun p : Cfg eta n => 1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p pr.1.1) ^ 2) =
        regWeight L n a := by
      funext p; rw [regWeight, h]
    rwa [hw] at hb
  · have hb := finiteElectronPairCoulombOperator_registerBound_second pr.1.1 pr.1.2 (ne_of_lt pr.2)
      (2 * Real.pi / L) ((coulombCellAmplitude L) ^ 2) (coulombPhysicalCellConstant L Hunit) Hunit n
      (sq_nonneg _) hPeriodic (coulombPhysicalCellConstant_scale L Hunit hL)
    have hw : (fun p : Cfg eta n => 1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p pr.1.2) ^ 2) =
        regWeight L n a := by
      funext p; rw [regWeight, h]
    rwa [hw] at hb

/-- **Hardy for `V_a`**: `‖V_a v‖² ≤ C_a² Σ_p (1 + |k_a|²) |v_p|²`. -/
theorem Va_registerBound (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    HasWeightedOperatorBound (regWeight L n a) (Va sys L n a) (CVa sys L Hunit a) := by
  classical
  have hw : ∀ p, 0 ≤ regWeight L n a p := regWeight_nonneg n a L
  have hB := coulombPhysicalCellConstant_nonneg L Hunit
  have hOne := oneParticleCoulombH1Bound_of_canonicalPeriodic (2 * Real.pi / L)
    ((coulombCellAmplitude L) ^ 2) (coulombPhysicalCellConstant L Hunit) Hunit n (sq_nonneg _)
    hPeriodic (coulombPhysicalCellConstant_scale L Hunit hL)
  -- the nuclear term
  have hNucTerm : ∀ ell : ν, HasWeightedOperatorBound (regWeight L n a)
      (referenceKernelConvolutionOperator a
        (finiteElectronNuclearKernel sys.nuclei (coulombCellAmplitude L) n ell))
      (sys.nuclei.charge ell * coulombPhysicalCellConstant L Hunit) := fun ell =>
    finiteElectronNuclearTerm_registerBound a sys.nuclei (2 * Real.pi / L) (coulombCellAmplitude L)
      (coulombPhysicalCellConstant L Hunit) n ell hOne
  have hNucSum := hasWeightedOperatorBound_finset_sum hw Finset.univ _ _
    (fun ell _ => mul_nonneg (sys.nuclei.charge_nonneg ell) hB) (fun ell _ => hNucTerm ell)
  have hNuc := hasWeightedOperatorBound_smul ((-sys.charge a : ℝ) : ℂ) hNucSum
  rw [norm_ofReal_neg] at hNuc
  -- the pair terms
  have hPair := hasWeightedOperatorBound_finset_sum hw (pairsWith a)
    (fun pr => ((sys.charge pr.1.1 * sys.charge pr.1.2 : ℝ) : ℂ) •
      finiteElectronPairCoulombOperator pr.1.1 pr.1.2 ((coulombCellAmplitude L) ^ 2) n)
    (fun pr => |sys.charge pr.1.1 * sys.charge pr.1.2| * coulombPhysicalCellConstant L Hunit)
    (fun pr _ => mul_nonneg (abs_nonneg _) hB)
    (fun pr hpr => by
      have h := hasWeightedOperatorBound_smul ((sys.charge pr.1.1 * sys.charge pr.1.2 : ℝ) : ℂ)
        (pair_registerBound Hunit n a hL hPeriodic pr hpr)
      rwa [norm_ofReal'] at h)
  have hN0 : 0 ≤ |sys.charge a| * ∑ ell : ν, sys.nuclei.charge ell * coulombPhysicalCellConstant L Hunit :=
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun ell _ =>
      mul_nonneg (sys.nuclei.charge_nonneg ell) hB)
  have hP0 : 0 ≤ ∑ pr ∈ pairsWith a,
      |sys.charge pr.1.1 * sys.charge pr.1.2| * coulombPhysicalCellConstant L Hunit :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) hB
  have hSum := hasWeightedOperatorBound_add hw hN0 hP0 hNuc hPair
  have hConst : |sys.charge a| * ∑ ell : ν, sys.nuclei.charge ell * coulombPhysicalCellConstant L Hunit +
      ∑ pr ∈ pairsWith a,
        |sys.charge pr.1.1 * sys.charge pr.1.2| * coulombPhysicalCellConstant L Hunit =
      CVa sys L Hunit a := by
    unfold CVa chargeA FiniteBONuclearData.totalCharge
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  rw [hConst] at hSum
  exact hSum

lemma norm_Va_le (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖Va sys L n a v‖ ≤ CVa sys L Hunit a * Real.sqrt (weightedNormSq (regWeight L n a) v) :=
  norm_le_of_weightedOperatorBound (regWeight_nonneg n a L) (CVa_nonneg sys Hunit a L)
    (Va_registerBound sys Hunit n a hL hPeriodic) v

end Hardy

/-! ## Coercivity of `H_ā` on high register momenta -/

section Coercive

variable [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) (n : ℕ) (a : Fin eta)

/-- The coercivity constant `C_sh = C_m² + 1/2 + 2 m_a C_a²`. -/
noncomputable def Csh (sys : CoulombSystem eta ν) (L Hunit : ℝ) (a : Fin eta) : ℝ :=
  (finiteCoulombPhysicalMassConstant sys L Hunit) ^ 2 + 1 / 2 +
    2 * sys.mass a * (CVa sys L Hunit a) ^ 2

/-- **Coercivity of `H_ā`**: for `v` supported in `|k_a| ≥ l`,
`Re ⟪v, H_ā v⟫ ≥ (l²/(8 m_a) - C_sh) ‖v‖²`. -/
theorem Hbar_coercive (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {l : ℝ} (v : En eta n)
    (hv : ∀ p, v.ofLp p ≠ 0 → l ^ 2 ≤ finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2) :
    (l ^ 2 / (8 * sys.mass a) - Csh sys L Hunit a) * ‖v‖ ^ 2 ≤ (⟪v, Hbar sys L n a v⟫_ℂ).re := by
  classical
  set mks := massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) with hmks
  set WN := weightedNormSq (fun p => 1 + mks p) v with hWN
  set Wa := weightedNormSq (regWeight L n a) v with hWa
  set Cm := finiteCoulombPhysicalMassConstant sys L Hunit with hCm
  set Ca := CVa sys L Hunit a with hCa
  have hm : 0 < sys.mass a := sys.mass_pos a
  have hmks0 : ∀ p, 0 ≤ mks p := fun p => massKineticSymbol_nonneg sys L n p
  -- coercivity of `H_N`
  have hcoer : (1 / 4 : ℝ) * WN ≤ (⟪v, finiteCoulombHamiltonian sys L n v⟫_ℂ).re +
      (Cm ^ 2 + 1 / 2) * ‖v‖ ^ 2 :=
    diagHamiltonian_coercive_of_weightedBound mks hmks0 _
      (finiteCoulombPhysicalMassConstant_nonneg sys L Hunit)
      (finiteCoulombPotential_physical_massBound sys L Hunit n hL hPeriodic) v
  -- the register weight is controlled by the mass-weighted one
  have hWa_le : Wa ≤ sys.mass a * WN := by
    rw [hWa, hWN, weightedNormSq, weightedNormSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have h := register_weight_le_mass_mul sys.one_le_mass
      (finitePlaneWaveKabs (2 * Real.pi / L) n) a p
    have : regWeight L n a p * ‖v.ofLp p‖ ^ 2 ≤
        sys.mass a * (1 + mks p) * ‖v.ofLp p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by rw [regWeight]; exact h) (sq_nonneg _)
    linarith
  -- `V_a` is form-bounded by the register weight
  have hWa0 : 0 ≤ Wa := weightedNormSq_nonneg (regWeight_nonneg n a L) v
  have hVa := norm_Va_le sys Hunit n a hL hPeriodic v
  have hform : (⟪v, Va sys L n a v⟫_ℂ).re ≤ WN / 8 + 2 * sys.mass a * Ca ^ 2 * ‖v‖ ^ 2 := by
    have h1 : (⟪v, Va sys L n a v⟫_ℂ).re ≤ ‖v‖ * (Ca * Real.sqrt Wa) :=
      (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left hVa (norm_nonneg _)))
    have hsq := Real.sq_sqrt hWa0
    have hs0 := Real.sqrt_nonneg Wa
    have hCa0 : 0 ≤ Ca := CVa_nonneg sys Hunit a L
    -- `‖v‖ C_a √W_a ≤ W_a/(8 m_a) + 2 m_a C_a² ‖v‖²`
    have h2 : ‖v‖ * (Ca * Real.sqrt Wa) ≤ Wa / (8 * sys.mass a) + 2 * sys.mass a * Ca ^ 2 * ‖v‖ ^ 2 := by
      have key : 0 ≤ (Real.sqrt Wa - 4 * sys.mass a * Ca * ‖v‖) ^ 2 := sq_nonneg _
      have h8 : Wa / (8 * sys.mass a) = (Real.sqrt Wa) ^ 2 / (8 * sys.mass a) := by rw [hsq]
      rw [h8, div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [key]
    have h3 : Wa / (8 * sys.mass a) ≤ WN / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have : WN / 8 * (8 * sys.mass a) = sys.mass a * WN := by ring
      rw [this]
      exact hWa_le
    linarith
  -- the kinetic lower bound on the support
  have hkin : l ^ 2 / sys.mass a * ‖v‖ ^ 2 ≤ WN := by
    rw [hWN, weightedNormSq, norm_sq_En, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases hp : v.ofLp p = 0
    · simp [hp]
    · have h1 := hv p hp
      have h2 := component_sq_le_mass_mul_massKineticSymbol (fun b => sys.mass_pos b)
        (finitePlaneWaveKabs (2 * Real.pi / L) n) p a
      have h3 : l ^ 2 / sys.mass a ≤ 1 + mks p := by
        rw [div_le_iff₀ hm]
        nlinarith [hmks0 p]
      exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
  -- assemble
  have hsplit : (⟪v, Hbar sys L n a v⟫_ℂ).re =
      (⟪v, finiteCoulombHamiltonian sys L n v⟫_ℂ).re - (⟪v, Va sys L n a v⟫_ℂ).re := by
    unfold Hbar
    rw [LinearMap.sub_apply, inner_sub_right, Complex.sub_re]
  rw [hsplit]
  have hl8 : l ^ 2 / (8 * sys.mass a) * ‖v‖ ^ 2 ≤ WN / 8 := by
    have : l ^ 2 / (8 * sys.mass a) * ‖v‖ ^ 2 = (l ^ 2 / sys.mass a * ‖v‖ ^ 2) / 8 := by
      field_simp
    rw [this]
    linarith
  unfold Csh
  rw [← hCm, ← hCa]
  nlinarith [hcoer, hform, hl8]

end Coercive

/-! ## Slices and the weighted resolvent bound -/

section Slices

variable {n : ℕ} (a : Fin eta)

/-- The register-`a` slice `{p_a = μ}`. -/
noncomputable def slice (μ : FinitePlaneWaveMode n) : En eta n →ₗ[ℂ] En eta n :=
  regMul a (fun μ' => if μ' = μ then 1 else 0)

lemma slice_apply (μ : FinitePlaneWaveMode n) (y : En eta n) (p : Cfg eta n) :
    (slice a μ y).ofLp p = if p a = μ then y.ofLp p else 0 := by
  unfold slice
  rw [regMul_apply]
  split_ifs <;> simp

lemma norm_sq_slice (μ : FinitePlaneWaveMode n) (y : En eta n) :
    ‖slice a μ y‖ ^ 2 = ∑ p, if p a = μ then ‖y.ofLp p‖ ^ 2 else 0 := by
  rw [norm_sq_En]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [slice_apply]
  split_ifs <;> simp

/-- The slices decompose the norm. -/
lemma norm_sq_eq_sum_slice (y : En eta n) : ‖y‖ ^ 2 = ∑ μ, ‖slice a μ y‖ ^ 2 := by
  classical
  simp_rw [norm_sq_slice]
  rw [Finset.sum_comm, norm_sq_En]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- **The weighted resolvent bound.**  Let `D` be register-local with
`Re ⟪x, D x⟫ ≥ w(μ) ‖x‖²` for every `x` supported on the slice `{p_a = μ}`.  Then every `v`
supported where `w > 0` satisfies `‖v‖ ≤ ‖w(p_a)⁻¹ (D v)‖`. -/
theorem norm_le_of_slice_coercive (D : En eta n →ₗ[ℂ] En eta n) (hD : RegLocal a D)
    (w : FinitePlaneWaveMode n → ℝ)
    (hco : ∀ (μ : FinitePlaneWaveMode n) (x : En eta n), (∀ p, x.ofLp p ≠ 0 → p a = μ) →
      w μ * ‖x‖ ^ 2 ≤ (⟪x, D x⟫_ℂ).re)
    (v : En eta n) (hv : ∀ p, v.ofLp p ≠ 0 → 0 < w (p a)) :
    ‖v‖ ≤ ‖regMul a (fun μ => (((w μ)⁻¹ : ℝ) : ℂ)) (D v)‖ := by
  classical
  suffices h : ‖v‖ ^ 2 ≤ ‖regMul a (fun μ => (((w μ)⁻¹ : ℝ) : ℂ)) (D v)‖ ^ 2 from
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  rw [norm_sq_eq_sum_slice a v, norm_sq_eq_sum_slice a (regMul a _ (D v))]
  refine Finset.sum_le_sum fun μ _ => ?_
  -- on the slice, the weighted vector is `w(μ)⁻¹ D (slice v)`
  have h1 : slice a μ (regMul a (fun μ => (((w μ)⁻¹ : ℝ) : ℂ)) (D v)) =
      (((w μ)⁻¹ : ℝ) : ℂ) • D (slice a μ v) := by
    unfold slice
    rw [hD]
    ext p
    simp only [regMul_apply, PiLp.smul_apply, smul_eq_mul]
    split_ifs with h
    · rw [h]; ring
    · ring
  rw [h1, norm_smul]
  set x := slice a μ v with hx
  by_cases hz : x = 0
  · rw [hz]; simp
  -- `x ≠ 0`, so the slice meets the support of `v` and `w(μ) > 0`
  obtain ⟨p, hp⟩ : ∃ p, x.ofLp p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hz (by ext p; simp [hcon p])
  have hpa : p a = μ := by
    by_contra hne
    exact hp (by rw [hx, slice_apply, if_neg hne])
  have hvp : v.ofLp p ≠ 0 := by
    rw [hx, slice_apply, if_pos hpa] at hp; exact hp
  have hw : 0 < w μ := hpa ▸ hv p hvp
  have hsupp : ∀ p', x.ofLp p' ≠ 0 → p' a = μ := by
    intro p' hp'
    by_contra hne
    exact hp' (by rw [hx, slice_apply, if_neg hne])
  have hc := hco μ x hsupp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hz
  -- `w(μ) ‖x‖ ≤ ‖D x‖`
  have h2 : w μ * ‖x‖ ≤ ‖D x‖ := by
    have h3 : (⟪x, D x⟫_ℂ).re ≤ ‖x‖ * ‖D x‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    have h4 : w μ * ‖x‖ ^ 2 ≤ ‖x‖ * ‖D x‖ := hc.trans h3
    have h5 : w μ * ‖x‖ * ‖x‖ ≤ ‖D x‖ * ‖x‖ := by nlinarith
    exact le_of_mul_le_mul_right h5 hxpos
  have h6 : ‖x‖ ≤ ‖(((w μ)⁻¹ : ℝ) : ℂ)‖ * ‖D x‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw)]
    rw [inv_mul_eq_div, le_div_iff₀ hw]
    linarith
  exact pow_le_pow_left₀ (norm_nonneg _) h6 2

end Slices

end FSGalerkin
