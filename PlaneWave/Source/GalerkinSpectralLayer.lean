import PlaneWave.Certificate
import PlaneWave.Source.HotContentAbstract

/-!
# Flux/source build, block 1b: the spectral layer on the release's Galerkin space

Instantiates the abstract spectral layer (`dev/PlaneWave.Source.SpectralLayer.lean`, `dev/PlaneWave.Source.HotContentAbstract.lean`) on the release
file's Galerkin space `E_n = EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n))`, whose mode
set is the sup-norm cube of radius `n`, with the release's Hamiltonian
`H_N = finiteCoulombHamiltonian sys L n = (1/2) diag(massKineticSymbol) + W_N`.

* `Asym`: the kinetic symbol `A = (1/2) massKineticSymbol = Σ_a g²|ν_a|²/(2 m_a)`; `sb`: the
  standard basis, along which `FSSpectral.kin` and `FSSpectral.wt` are `A` and `(1 + A)^s`;
* `HN_eq_kin_add`: `H_N v = A v + W_N v` (the hypothesis `H = T + V` of `lem:specleak`);
* `potential_le_wt`: `‖W_N v‖ ≤ √2 C_m ‖(1+A)^{1/2} v‖` (the release's uniform Hardy bound
  `finiteCoulombPotential_physical_massBound`), so `C_V = √2 C_m` in `lem:specleak`;
* `HN_lower`: `H_N ≥ -(C_m² + 1/4)` (`finiteCoulombHamiltonian_form_lower_bound`), the constant `C_low`.

Here `C_m = finiteCoulombPhysicalMassConstant sys L Hunit` is independent of `n`.
-/

set_option autoImplicit false

open scoped InnerProductSpace
open PlaneWaveCertificate

namespace FSGalerkin

variable {eta : ℕ} {ν : Type*}

/-- Configurations of the Galerkin space. -/
abbrev Cfg (eta n : ℕ) := FourierConfig eta (FinitePlaneWaveMode n)

/-- The Galerkin space `ran P`. -/
abbrev En (eta n : ℕ) := EuclideanSpace ℂ (Cfg eta n)

/-- The standard (kinetic) orthonormal basis. -/
noncomputable abbrev sb (eta n : ℕ) : OrthonormalBasis (Cfg eta n) ℂ (En eta n) :=
  EuclideanSpace.basisFun (Cfg eta n) ℂ

/-- The kinetic symbol `A = (1/2) massKineticSymbol`. -/
noncomputable def Asym (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (p : Cfg eta n) : ℝ :=
  (1 / 2) * massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) p

lemma massKineticSymbol_nonneg (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (p : Cfg eta n) :
    0 ≤ massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) p := by
  unfold massKineticSymbol
  refine Finset.sum_nonneg fun a _ => ?_
  have h1 : (0 : ℝ) < sys.mass a := lt_of_lt_of_le one_pos (sys.one_le_mass a)
  positivity

lemma Asym_nonneg (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (p : Cfg eta n) :
    0 ≤ Asym sys L n p := by
  unfold Asym; have := massKineticSymbol_nonneg sys L n p; positivity

lemma inner_sb (n : ℕ) (v : En eta n) (k : Cfg eta n) : ⟪sb eta n k, v⟫_ℂ = v.ofLp k := by
  rw [EuclideanSpace.basisFun_inner]

/-- Coordinates of the calculus along the standard basis. -/
lemma fc_sb_apply (n : ℕ) (A : Cfg eta n → ℝ) (f : ℝ → ℂ) (v : En eta n) (k : Cfg eta n) :
    (FSSpectral.fc (sb eta n) A f v).ofLp k = f (A k) * v.ofLp k := by
  classical
  have h := FSSpectral.inner_basis_fc (sb eta n) A f v k
  rwa [inner_sb, inner_sb] at h

lemma norm_sq_En (n : ℕ) (v : En eta n) : ‖v‖ ^ 2 = ∑ k, ‖v.ofLp k‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

lemma norm_sq_wt (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (s : ℝ) (v : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ ^ 2 =
      ∑ k, ((1 + Asym sys L n k) ^ s) ^ 2 * ‖v.ofLp k‖ ^ 2 := by
  rw [norm_sq_En]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [FSSpectral.wt, fc_sb_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- `‖(1+A)^{1/2} v‖² = Σ_k (1 + A_k) |v_k|²`. -/
lemma norm_sq_wt_half (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (v : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖ ^ 2 =
      ∑ k, (1 + Asym sys L n k) * ‖v.ofLp k‖ ^ 2 := by
  rw [norm_sq_wt]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h0 : 0 ≤ 1 + Asym sys L n k := by linarith [Asym_nonneg sys L n k]
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

/-- `H_N = A + W_N` (the kinetic operator plus the finite Coulomb potential). -/
lemma HN_eq_kin_add [Fintype ν] (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (v : En eta n) :
    finiteCoulombHamiltonian sys L n v =
      FSSpectral.kin (sb eta n) (Asym sys L n) v +
        finiteCoulombPotential sys (coulombCellAmplitude L) n v := by
  unfold finiteCoulombHamiltonian diagHamiltonian
  rw [LinearMap.add_apply, LinearMap.smul_apply]
  congr 1
  ext k
  rw [FSSpectral.kin, fc_sb_apply, PiLp.smul_apply, diagOperator_apply, Asym]
  push_cast
  ring

/-- **Hardy on the Galerkin space**: `‖W_N v‖ ≤ √2 C_m ‖(1+A)^{1/2} v‖`, uniformly in `n`. -/
lemma potential_le_wt [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) (n : ℕ) (hL : 0 < L)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (v : En eta n) :
    ‖finiteCoulombPotential sys (coulombCellAmplitude L) n v‖ ≤
      Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖ := by
  have hB := finiteCoulombPotential_physical_massBound sys L Hunit n hL hPeriodic v
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hw : weightedNormSq
      (fun p => 1 + massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) p) v ≤
      2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖ ^ 2 := by
    rw [norm_sq_wt_half, weightedNormSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have h1 := massKineticSymbol_nonneg sys L n k
    unfold Asym
    nlinarith [sq_nonneg ‖v.ofLp k‖]
  have h2 : ‖finiteCoulombPotential sys (coulombCellAmplitude L) n v‖ ^ 2 ≤
      (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc _ ≤ _ := hB
      _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          (2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hw (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- **The common lower bound** `H_N ≥ -(C_m² + 1/4)`. -/
lemma HN_lower [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) (n : ℕ) (hL : 0 < L)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (v : En eta n) :
    -((finiteCoulombPhysicalMassConstant sys L Hunit) ^ 2 + 1 / 4) * ‖v‖ ^ 2 ≤
      (⟪v, finiteCoulombHamiltonian sys L n v⟫_ℂ).re :=
  finiteCoulombHamiltonian_form_lower_bound sys L Hunit n hL hPeriodic v

/-- `‖v‖ ≤ ‖(1+A)^s v‖` for `s ≥ 0`. -/
lemma norm_le_wt (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) {s : ℝ} (hs : 0 ≤ s)
    (v : En eta n) : ‖v‖ ≤ ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ := by
  have h2 : ‖v‖ ^ 2 ≤ ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ ^ 2 := by
    rw [norm_sq_wt, norm_sq_En]
    refine Finset.sum_le_sum fun k _ => ?_
    have h0 : 1 ≤ 1 + Asym sys L n k := by linarith [Asym_nonneg sys L n k]
    have h1 : 1 ≤ (1 + Asym sys L n k) ^ s := Real.one_le_rpow h0 hs
    have : 1 ≤ ((1 + Asym sys L n k) ^ s) ^ 2 := by nlinarith
    nlinarith [sq_nonneg ‖v.ofLp k‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- Weights are monotone in the exponent. -/
lemma wt_mono (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) {s s' : ℝ} (hss : s ≤ s')
    (v : En eta n) : ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ ≤
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) s' v‖ := by
  have h2 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ ^ 2 ≤
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) s' v‖ ^ 2 := by
    rw [norm_sq_wt, norm_sq_wt]
    refine Finset.sum_le_sum fun k _ => ?_
    have h0 : 1 ≤ 1 + Asym sys L n k := by linarith [Asym_nonneg sys L n k]
    have h1 : (1 + Asym sys L n k) ^ s ≤ (1 + Asym sys L n k) ^ s' :=
      Real.rpow_le_rpow_of_exponent_le h0 hss
    have h2 : 0 ≤ (1 + Asym sys L n k) ^ s := Real.rpow_nonneg (by linarith) _
    have : ((1 + Asym sys L n k) ^ s) ^ 2 ≤ ((1 + Asym sys L n k) ^ s') ^ 2 :=
      pow_le_pow_left₀ h2 h1 2
    nlinarith [sq_nonneg ‖v.ofLp k‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

end FSGalerkin
