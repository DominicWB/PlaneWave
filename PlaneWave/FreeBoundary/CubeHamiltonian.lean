import PlaneWave.Auxiliary.PotentialTails
import PlaneWave.FreeBoundary.RangeCut

/-!
# `app:free`, part 3: the `g_L` Hamiltonian on the cube and its Galerkin energy bound

For a Coulomb system on the cell `T_L` (masses, charges, clamped nuclei) and the range-truncated
kernel `g_L = θ(|x|)/|x|` of `PlaneWave.FreeBoundary.RangeCut` (`Profile R θ`), the finite-cube Hamiltonian with the `g_L`
interaction (`gLham`). The zero mode `ĝ_L(0)` is a constant multiplication operator, a constant
shift of every energy (represented exactly by the Galerkin and grid methods), and is left out.

* `gLk`, `gLnuc`, `gLpot`: the pair coefficient `ĝ_L(k_v - k_u)`, the nuclear coefficient
  `-Z_ℓ φ_ℓ(v) conj φ_ℓ(u) ĝ_L(k_v - k_u)` (the phases of the release's nuclear terms), and the
  potential `Σ_{a<b} q_a q_b g_L(x_a - x_b) + Σ_{a,ℓ} q_a Z_ℓ g_L(x_a - R_ℓ)` in the layout of
  `finiteCoulombPotential`;
* `gLpot_isSymmetric`; `norm_gLk_le`, `norm_gLnuc_le`: domination by `(1 + V_θ)` times the
  Coulomb coefficients (eq:rangecut);
* `gLpot_h1Bound`, `gLpot_massBound`: the `H¹` and mass-weighted bounds by Fourier domination
  (constants `(1 + V_θ) B Q` and `(1 + V_θ) B Q_m`, `Q`, `Q_m` the coupling weights);
* `gLpot_tail_bound`: `‖1{|k_r| > K} W u‖ ≤ (1 + V_θ) c_tail Q M₂ K^{-1/2}` for every register and
  every `K ≥ 1`, under the `H²` budget `M₂`;
* **`gL_cubic_energy_bound`**: for a normalised sector eigenvector of `gLham` with energy `E`
  (`|E| ≤ E₀`) that is a ground state, and the cubic Galerkin ground energy `E_N`:
  `0 ≤ E_N - E` and `K³ (E_N - E) ≤ 64 (1/2 + C_pot + |E|) S₁ S₂ C_W²`, with
  `C_W = (1 + V_θ) c_tail Q m̄ (2 + 8E₀ + 16 B_m²)`; from the release's
  `mass_sector_cubic_energy_bound_of_tail_and_form`.

All constants are explicit. They depend on `L` through the Coulomb amplitude `1/(πL)`, the
momentum unit `2π/L` and the lattice-unit tail constants of the release, polynomially; the
`L`-uniform form of `lem:scaling` is not used here.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators
open PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin FSNormal

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν] {R : ℝ} {θ : ℝ → ℝ}

/-! ## The coefficients -/

lemma norm_kvec_neg (L : ℝ) (ν' : Lattice3) : ‖kvec L (-ν')‖ = ‖kvec L ν'‖ := by
  have h1 := norm_kvec_sq L (-ν')
  have h2 := norm_kvec_sq L ν'
  have hk : kSq L (-ν') = kSq L ν' := by
    unfold kSq
    congr 1
    simp [latticeNormSq]
  rw [hk, ← h2] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- `ĝ_L` is even. -/
lemma ghat_neg (L : ℝ) (θ : ℝ → ℝ) (ν' : Lattice3) : ghat L θ (-ν') = ghat L θ ν' := by
  unfold ghat
  rw [gFT_rot (kvec L (-ν')), gFT_rot (kvec L ν'), norm_kvec_neg]

/-- `ĝ_L` is real. -/
lemma ghat_conj (hθ : Profile R θ) (L : ℝ) (ν' : Lattice3) :
    starRingEnd ℂ (ghat L θ ν') = ghat L θ ν' := by
  have hreal : ∃ x : ℝ, gFT θ (kvec L ν') = (x : ℂ) := by
    by_cases hk : kvec L ν' = 0
    · rw [hk]; exact ⟨_, gFT_zero hθ⟩
    · exact ⟨_, gFT_eq_sin hθ hk⟩
  obtain ⟨x, hx⟩ := hreal
  unfold ghat
  rw [hx, map_div₀, Complex.conj_ofReal, Complex.conj_ofReal]

/-- The pair coefficient: `ĝ_L` of the transfer `v - u`, without the zero mode. -/
noncomputable def gLk (L : ℝ) (θ : ℝ → ℝ) (n : ℕ) (v u : FinitePlaneWaveMode n) : ℂ := by
  classical
  exact if finitePlaneWaveTransfer n v u = (fun _ => 0) then 0
    else ghat L θ (finitePlaneWaveTransfer n v u)

lemma transfer_swap (n : ℕ) (v u : FinitePlaneWaveMode n) :
    finitePlaneWaveTransfer n u v = -(finitePlaneWaveTransfer n v u) := by
  funext c
  simp [finitePlaneWaveTransfer, latticeSub]

lemma gLk_conj_swap (hθ : Profile R θ) (L : ℝ) (n : ℕ) (v u : FinitePlaneWaveMode n) :
    starRingEnd ℂ (gLk L θ n v u) = gLk L θ n u v := by
  classical
  unfold gLk
  rw [transfer_swap n v u]
  by_cases h : finitePlaneWaveTransfer n v u = (fun _ => 0)
  · have h' : -(finitePlaneWaveTransfer n v u) = (fun _ => 0) := by
      rw [h]; funext c; simp
    rw [if_pos h, if_pos h', map_zero]
  · have h' : -(finitePlaneWaveTransfer n v u) ≠ (fun _ => 0) := by
      intro h'
      apply h
      funext c
      have := congrFun h' c
      simpa using this
    rw [if_neg h, if_neg h', ghat_neg, ghat_conj hθ]

lemma norm_coulomb_eq {γ : ℝ} (hγ : 0 ≤ γ) (n : ℕ) (v u : FinitePlaneWaveMode n) :
    ‖finiteCoulombKernel (γ ^ 2) n v u‖ = γ / latticeNormSq (finitePlaneWaveTransfer n v u) := by
  unfold finiteCoulombKernel finiteCoulombDifferenceSquareWeight latticeCoulombSquareWeight
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), ← div_pow,
    Real.sqrt_sq (div_nonneg hγ (latticeNormSq_nonneg _))]

lemma cellAmp_nonneg (L : ℝ) (hL : 0 < L) : 0 ≤ coulombCellAmplitude L := by
  unfold coulombCellAmplitude; positivity

/-- **Domination of the pair coefficient** (eq:rangecut). -/
lemma norm_gLk_le {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (n : ℕ)
    (v u : FinitePlaneWaveMode n) :
    ‖gLk L θ n v u‖ ≤ (1 + tv R θ) * ‖finiteCoulombKernel (coulombCellAmplitude L ^ 2) n v u‖ := by
  classical
  have hV := hθ.tv_nonneg
  rw [norm_coulomb_eq (cellAmp_nonneg L hL)]
  unfold gLk
  split_ifs with h
  · rw [norm_zero]
    have := latticeNormSq_nonneg (finitePlaneWaveTransfer n v u)
    have := cellAmp_nonneg L hL
    positivity
  · have hb := rangecut hL hθ _ h
    have hpos := latticeNormSq_pos h
    rw [what_eq hL] at hb
    refine hb.trans (le_of_eq ?_)
    unfold coulombCellAmplitude
    field_simp

/-- The nuclear coefficient `-Z_ℓ φ_ℓ(v) conj φ_ℓ(u) ĝ_L(v - u)`. -/
noncomputable def gLnuc (data : FiniteBONuclearData ν) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ) (l : ν)
    (v u : FinitePlaneWaveMode n) : ℂ :=
  (-(data.charge l : ℂ)) * (finiteNuclearFourierPhase n (data.position l) v *
    starRingEnd ℂ (finiteNuclearFourierPhase n (data.position l) u)) * gLk L θ n v u

omit [Fintype ν] in
lemma gLnuc_conj_swap (hθ : Profile R θ) (data : FiniteBONuclearData ν) (L : ℝ) (n : ℕ)
    (l : ν) (v u : FinitePlaneWaveMode n) :
    starRingEnd ℂ (gLnuc data L θ n l v u) = gLnuc data L θ n l u v := by
  unfold gLnuc
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_conj, gLk_conj_swap hθ]
  ring

omit [Fintype ν] in
/-- **Domination of the nuclear coefficient**. -/
lemma norm_gLnuc_le {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (data : FiniteBONuclearData ν)
    (n : ℕ) (l : ν) (v u : FinitePlaneWaveMode n) :
    ‖gLnuc data L θ n l v u‖ ≤ (data.charge l * (1 + tv R θ)) *
      Real.sqrt (finiteCoulombDifferenceSquareWeight (coulombCellAmplitude L ^ 2) n v u) := by
  have h1 := finiteNuclearFourierPhase_norm_le_one n (data.position l) v
  have h2 := finiteNuclearFourierPhase_norm_le_one n (data.position l) u
  have h3 := norm_gLk_le hL hθ n v u
  have h4 : ‖finiteCoulombKernel (coulombCellAmplitude L ^ 2) n v u‖ =
      Real.sqrt (finiteCoulombDifferenceSquareWeight (coulombCellAmplitude L ^ 2) n v u) := by
    unfold finiteCoulombKernel
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [h4] at h3
  have hZ := data.charge_nonneg l
  unfold gLnuc
  rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hZ, RCLike.norm_conj]
  calc data.charge l * (‖finiteNuclearFourierPhase n (data.position l) v‖ *
        ‖finiteNuclearFourierPhase n (data.position l) u‖) * ‖gLk L θ n v u‖
      ≤ data.charge l * (1 * 1) * ((1 + tv R θ) *
          Real.sqrt (finiteCoulombDifferenceSquareWeight (coulombCellAmplitude L ^ 2) n v u)) := by
        gcongr
    _ = _ := by ring

/-- The lifted pair coefficient is dominated by the Coulomb pair kernel. -/
lemma norm_lift_gLk_le {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (i j : Fin eta) (n : ℕ)
    (q p : Cfg eta n) :
    ‖finiteElectronPairLiftKernel i j n (gLk L θ n) q p‖ ≤
      (1 + tv R θ) *
        ‖finiteElectronPairConfigurationKernel i j (coulombCellAmplitude L ^ 2) n q p‖ := by
  classical
  unfold finiteElectronPairLiftKernel finiteElectronPairConfigurationKernel
  split_ifs
  · exact norm_gLk_le hL hθ n _ _
  · simp

lemma lift_gLk_conj_swap (hθ : Profile R θ) (L : ℝ) (i j : Fin eta) (n : ℕ) (q p : Cfg eta n) :
    starRingEnd ℂ (finiteElectronPairLiftKernel i j n (gLk L θ n) q p) =
      finiteElectronPairLiftKernel i j n (gLk L θ n) p q := by
  classical
  unfold finiteElectronPairLiftKernel
  by_cases h : finiteElectronPairSliceLabel i j n q = finiteElectronPairSliceLabel i j n p
  · rw [if_pos h, if_pos h.symm, gLk_conj_swap hθ]
  · rw [if_neg h, if_neg (Ne.symm h), map_zero]

/-! ## The potential and the Hamiltonian -/

/-- **The `g_L` potential on the cube** (without the zero mode), in the layout of
`finiteCoulombPotential`. -/
noncomputable def gLpot (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ) :
    En eta n →ₗ[ℂ] En eta n :=
  (∑ a : Fin eta, ((-sys.charge a : ℝ) : ℂ) •
    ∑ l : ν, referenceKernelConvolutionOperator a (gLnuc sys.nuclei L θ n l)) +
  ∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) •
    finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n)

/-- **The `g_L` Hamiltonian on the cube**: `(1/2) Σ_a |k_a|²/m_a + W_L`. -/
noncomputable def gLham (sys : CoulombSystem eta ν) (L : ℝ) (θ : ℝ → ℝ) (n : ℕ) :
    En eta n →ₗ[ℂ] En eta n :=
  diagHamiltonian (massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n))
    (gLpot sys L θ n)

lemma gLpot_isSymmetric (hθ : Profile R θ) (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) :
    (gLpot sys L θ n).IsSymmetric := by
  unfold gLpot
  apply LinearMap.IsSymmetric.add
  · apply LinearMap.isSymmetric_sum
    intro a _
    apply real_smul_isSymmetric
    apply LinearMap.isSymmetric_sum
    intro l _
    exact referenceKernelConvolutionOperator_isSymmetric_of_conj a _
      (gLnuc_conj_swap hθ sys.nuclei L n l)
  · apply LinearMap.isSymmetric_sum
    intro pair _
    apply real_smul_isSymmetric
    exact finiteCoefficientKernelOperator_isSymmetric _
      (lift_gLk_conj_swap hθ L pair.1.1 pair.1.2 n)

/-! ## `H¹` and mass-weighted bounds -/

section Bounds

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ)
  (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (n : ℕ)

/-- The register weight is at most the `H¹` weight. -/
lemma register_le_h1 (kabs : FinitePlaneWaveMode n → ℝ) (r : Fin eta) (p : Cfg eta n) :
    1 + kabs (p r) ^ 2 ≤ 1 * (1 + boKineticSymbol kabs p) := by
  rw [one_mul]
  have : kabs (p r) ^ 2 ≤ boKineticSymbol kabs p := by
    unfold boKineticSymbol
    exact Finset.single_le_sum (f := fun a => kabs (p a) ^ 2) (fun a _ => sq_nonneg _)
      (Finset.mem_univ r)
  linarith

/-- The `g_L` potential on any weighted space on which every term has the stated bound. -/
lemma gLpot_weightedBound (w : Cfg eta n → ℝ) (hw : ∀ p, 0 ≤ w p) (Bn : Fin eta → ℝ)
    (Bpair : FiniteElectronPair eta → ℝ) (hBn : ∀ a, 0 ≤ Bn a) (hBpair : ∀ pair, 0 ≤ Bpair pair)
    (hN : ∀ a l, HasWeightedOperatorBound w
      (referenceKernelConvolutionOperator a (gLnuc sys.nuclei L θ n l))
      (sys.nuclei.charge l * Bn a))
    (hP : ∀ pair, HasWeightedOperatorBound w
      (finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n)) (Bpair pair)) :
    HasWeightedOperatorBound w (gLpot sys L θ n)
      ((∑ a, |sys.charge a| * Bn a) * sys.nuclei.totalCharge +
        ∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2| *
          Bpair pair) := by
  classical
  have hInner : ∀ a : Fin eta, HasWeightedOperatorBound w
      (∑ l : ν, referenceKernelConvolutionOperator a (gLnuc sys.nuclei L θ n l))
      (∑ l : ν, sys.nuclei.charge l * Bn a) := fun a =>
    hasWeightedOperatorBound_finset_sum hw Finset.univ _ _
      (fun l _ => mul_nonneg (sys.nuclei.charge_nonneg l) (hBn a)) (fun l _ => hN a l)
  have hScaled : ∀ a : Fin eta, HasWeightedOperatorBound w
      (((-sys.charge a : ℝ) : ℂ) • ∑ l : ν, referenceKernelConvolutionOperator a
        (gLnuc sys.nuclei L θ n l))
      (|sys.charge a| * (∑ l : ν, sys.nuclei.charge l * Bn a)) := by
    intro a
    have h := hasWeightedOperatorBound_smul ((-sys.charge a : ℝ) : ℂ) (hInner a)
    rwa [norm_ofReal_neg] at h
  have hNuc := hasWeightedOperatorBound_finset_sum hw Finset.univ _ _
    (fun a _ => mul_nonneg (abs_nonneg _)
      (Finset.sum_nonneg fun l _ => mul_nonneg (sys.nuclei.charge_nonneg l) (hBn a)))
    (fun a _ => hScaled a)
  have hPairS : ∀ pair : FiniteElectronPair eta, HasWeightedOperatorBound w
      (((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) •
        finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n))
      (|sys.charge pair.1.1 * sys.charge pair.1.2| * Bpair pair) := by
    intro pair
    have h := hasWeightedOperatorBound_smul
      ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) (hP pair)
    rwa [norm_ofReal'] at h
  have hPairT := hasWeightedOperatorBound_finset_sum hw Finset.univ _ _
    (fun pair _ => mul_nonneg (abs_nonneg _) (hBpair pair)) (fun pair _ => hPairS pair)
  have hN0 : 0 ≤ ∑ a : Fin eta, |sys.charge a| * ∑ l : ν, sys.nuclei.charge l * Bn a :=
    Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _)
      (Finset.sum_nonneg fun l _ => mul_nonneg (sys.nuclei.charge_nonneg l) (hBn a))
  have hP0 : 0 ≤ ∑ pair : FiniteElectronPair eta,
      |sys.charge pair.1.1 * sys.charge pair.1.2| * Bpair pair :=
    Finset.sum_nonneg fun pair _ => mul_nonneg (abs_nonneg _) (hBpair pair)
  have hSum := hasWeightedOperatorBound_add hw hN0 hP0 hNuc hPairT
  have hConst : (∑ a : Fin eta, |sys.charge a| * ∑ l : ν, sys.nuclei.charge l * Bn a) =
      (∑ a, |sys.charge a| * Bn a) * sys.nuclei.totalCharge := by
    unfold FiniteBONuclearData.totalCharge
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul, mul_assoc, mul_comm (∑ l : ν, sys.nuclei.charge l)]
  unfold gLpot
  rw [hConst] at hSum
  exact hSum

include hL hθ hPeriodic

omit [Fintype ν] in
/-- A nuclear term on register `a` has the register bound `Z_ℓ (1 + V_θ) B`. -/
lemma gLnuc_registerBound (a : Fin eta) (l : ν) :
    HasWeightedOperatorBound (fun p => 1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2)
      (referenceKernelConvolutionOperator a (gLnuc sys.nuclei L θ n l))
      (sys.nuclei.charge l * ((1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit
        (2 * Real.pi / L))) := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  have h := dominated_single_hardy a (2 * Real.pi / L) (coulombCellAmplitude L ^ 2)
    (tB (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L)) Hunit (sq_nonneg _) hPeriodic
    (tB_scale (sq_nonneg _) hg) (gLnuc sys.nuclei L θ n l)
    (mul_nonneg (sys.nuclei.charge_nonneg l) (by linarith [hθ.tv_nonneg]))
    (fun v w => norm_gLnuc_le hL hθ sys.nuclei n l v w)
  rwa [mul_assoc] at h

/-- A pair term has the register bound `(1 + V_θ) B` for either member. -/
lemma gLpair_registerBound (pair : FiniteElectronPair eta) {r : Fin eta}
    (hr : r = pair.1.1 ∨ r = pair.1.2) :
    HasWeightedOperatorBound (fun p => 1 + finitePlaneWaveKabs (2 * Real.pi / L) n (p r) ^ 2)
      (finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n))
      ((1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L)) := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  exact dominated_pair_hardy (ne_of_lt pair.2) (2 * Real.pi / L) (coulombCellAmplitude L ^ 2)
    (tB (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L)) Hunit (sq_nonneg _) hPeriodic
    (tB_scale (sq_nonneg _) hg) (finiteElectronPairLiftKernel pair.1.1 pair.1.2 n (gLk L θ n))
    (fun q p => norm_lift_gLk_le hL hθ pair.1.1 pair.1.2 n q p) hr

/-- **The `H¹` bound**: `‖W_L u‖ ≤ (1 + V_θ) B Q ‖u‖_{H¹}`. -/
theorem gLpot_h1Bound :
    HasH1OperatorBound (finitePlaneWaveKabs (2 * Real.pi / L) n) (gLpot sys L θ n)
      (sys.couplingWeight * ((1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit
        (2 * Real.pi / L))) := by
  rw [hasH1OperatorBound_iff_weighted]
  have hw : ∀ p : Cfg eta n, 0 ≤ 1 + boKineticSymbol (finitePlaneWaveKabs (2 * Real.pi / L) n) p :=
    fun p => by linarith [boKineticSymbol_nonneg (finitePlaneWaveKabs (2 * Real.pi / L) n) p]
  have hB0 : 0 ≤ (1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L) :=
    mul_nonneg (by linarith [hθ.tv_nonneg]) (tB_nonneg _ _ _)
  have h := gLpot_weightedBound sys n _ hw
    (fun _ => (1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L))
    (fun _ => (1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L))
    (fun _ => hB0) (fun _ => hB0)
    (fun a l => by
      have h1 := hasWeightedOperatorBound_mono zero_le_one
        (register_le_h1 n (finitePlaneWaveKabs (2 * Real.pi / L) n) a)
        (gLnuc_registerBound sys hL hθ Hunit hPeriodic n a l)
      rwa [Real.sqrt_one, one_mul] at h1)
    (fun pair => by
      have h1 := hasWeightedOperatorBound_mono zero_le_one
        (register_le_h1 n (finitePlaneWaveKabs (2 * Real.pi / L) n) pair.1.1)
        (gLpair_registerBound hL hθ Hunit hPeriodic n pair (Or.inl rfl))
      rwa [Real.sqrt_one, one_mul] at h1)
  have hConst : (∑ a, |sys.charge a| * ((1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit
      (2 * Real.pi / L))) * sys.nuclei.totalCharge +
      ∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2| *
        ((1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L)) =
      sys.couplingWeight * ((1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit
        (2 * Real.pi / L)) := by
    unfold CoulombSystem.couplingWeight
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  rw [hConst] at h
  exact h

/-- **The mass-weighted bound**: `‖W_L u‖² ≤ ((1 + V_θ) B Q_m)² Σ_p (1 + A_m(p)) |u_p|²`. -/
theorem gLpot_massBound :
    HasWeightedOperatorBound
      (fun p => 1 + massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) p)
      (gLpot sys L θ n)
      (sys.massCouplingWeight * ((1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit
        (2 * Real.pi / L))) := by
  have hmpos : ∀ a, 0 < sys.mass a := fun a => sys.mass_pos a
  have hw : ∀ p : Cfg eta n,
      0 ≤ 1 + massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) p :=
    fun p => by
      linarith [massKineticSymbol_nonneg hmpos (finitePlaneWaveKabs (2 * Real.pi / L) n) p]
  set X := (1 + tv R θ) * tB (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L) with hX
  have hX0 : 0 ≤ X := mul_nonneg (by linarith [hθ.tv_nonneg]) (tB_nonneg _ _ _)
  have h := gLpot_weightedBound sys n _ hw
    (fun a => Real.sqrt (sys.mass a) * X)
    (fun pair => Real.sqrt (min (sys.mass pair.1.1) (sys.mass pair.1.2)) * X)
    (fun a => mul_nonneg (Real.sqrt_nonneg _) hX0)
    (fun pair => mul_nonneg (Real.sqrt_nonneg _) hX0)
    (fun a l => by
      have h1 := registerBound_massBound sys.one_le_mass _ a
        (gLnuc_registerBound sys hL hθ Hunit hPeriodic n a l)
      have heq : Real.sqrt (sys.mass a) * (sys.nuclei.charge l * X) =
          sys.nuclei.charge l * (Real.sqrt (sys.mass a) * X) := by ring
      rwa [heq] at h1)
    (fun pair => by
      rcases le_total (sys.mass pair.1.1) (sys.mass pair.1.2) with hm | hm
      · rw [min_eq_left hm]
        exact registerBound_massBound sys.one_le_mass _ pair.1.1
          (gLpair_registerBound hL hθ Hunit hPeriodic n pair (Or.inl rfl))
      · rw [min_eq_right hm]
        exact registerBound_massBound sys.one_le_mass _ pair.1.2
          (gLpair_registerBound hL hθ Hunit hPeriodic n pair (Or.inr rfl)))
  have hConst : (∑ a, |sys.charge a| * (Real.sqrt (sys.mass a) * X)) * sys.nuclei.totalCharge +
      ∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2| *
        (Real.sqrt (min (sys.mass pair.1.1) (sys.mass pair.1.2)) * X) =
      sys.massCouplingWeight * X := by
    unfold CoulombSystem.massCouplingWeight
    have h1 : (∑ a, |sys.charge a| * (Real.sqrt (sys.mass a) * X)) =
        (∑ a, |sys.charge a| * Real.sqrt (sys.mass a)) * X := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    have h2 : (∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2| *
        (Real.sqrt (min (sys.mass pair.1.1) (sys.mass pair.1.2)) * X)) =
        (∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2| *
          Real.sqrt (min (sys.mass pair.1.1) (sys.mass pair.1.2))) * X := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun pair _ => by ring
    rw [h1, h2]
    ring
  rw [hConst] at h
  exact h

end Bounds

/-! ## The potential tail -/

section Tail

variable {n : ℕ}

omit [Fintype ν] in
/-- `tail_pair_dominated` (`PlaneWave.Auxiliary.PotentialTails`) under any `H²` budget `M₂`. -/
lemma tail_pair_M2 {L : ℝ} (hL : 0 < L) {i j : Fin eta} (hij : i ≠ j) (a : Fin eta) {C : ℝ}
    (hC : 0 ≤ C) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (κ : Cfg eta n → Cfg eta n → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hdom : ∀ q p, ‖κ q p‖ ≤ Cg * ‖finiteElectronPairConfigurationKernel i j C n q p‖)
    {Kt M2 : ℝ} (hK1 : 1 ≤ Kt) (hM2 : 0 ≤ M2) (u : En eta n)
    (hH2 : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) u.ofLp ≤ M2 ^ 2) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs (2 * Real.pi / L) n) a
        (finiteCoefficientKernelOperator κ u)‖ ≤
      Cg * ctail C Hunit (2 * Real.pi / L) * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hH2' : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) (umod u).ofLp ≤ M2 ^ 2 := by
    rw [fullH2Sq_umod]; exact hH2
  refine (tail_domination κ _ hCg (pairKernel_real i j C) hdom Kt _ a u).trans ?_
  unfold ctail
  rw [mul_assoc Cg, mul_assoc Cg]
  refine mul_le_mul_of_nonneg_left ?_ hCg
  have hfull := norm_le_of_h1 (tB_nonneg C Hunit _) hM2
    (finiteElectronPairCoulombOperator_h1Bound_of_periodic i j hij _ C _ Hunit n hC hPeriodic
      (tB_scale hC hg)) (umod u) hH2'
  exact tail_regimes hg (kabs_cube_le hL) a _ (tB_nonneg C Hunit _) (tZ_nonneg hg) hM2 hK1 hfull
    (fun h2g hn => pair_tail_release hij a hg hC Hunit hPeriodic hK1 h2g hn hM2 (umod u) hH2')

omit [Fintype ν] in
/-- `tail_single_dominated` (`PlaneWave.Auxiliary.PotentialTails`) under any `H²` budget `M₂`. -/
lemma tail_single_M2 {L : ℝ} (hL : 0 < L) (r a : Fin eta) {C : ℝ} (hC : 0 ≤ C) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (κ : Cfg eta n → Cfg eta n → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hdom : ∀ q p, ‖κ q p‖ ≤ Cg * ‖referenceConfigurationKernel r (finiteCoulombKernel C n) q p‖)
    {Kt M2 : ℝ} (hK1 : 1 ≤ Kt) (hM2 : 0 ≤ M2) (u : En eta n)
    (hH2 : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) u.ofLp ≤ M2 ^ 2) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs (2 * Real.pi / L) n) a
        (finiteCoefficientKernelOperator κ u)‖ ≤
      Cg * ctail C Hunit (2 * Real.pi / L) * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hH2' : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) (umod u).ofLp ≤ M2 ^ 2 := by
    rw [fullH2Sq_umod]; exact hH2
  refine (tail_domination κ _ hCg (refKernel_real r C) hdom Kt _ a u).trans ?_
  rw [fcko_refKernel]
  unfold ctail
  rw [mul_assoc Cg, mul_assoc Cg]
  refine mul_le_mul_of_nonneg_left ?_ hCg
  have hfull := norm_le_of_h1 (tB_nonneg C Hunit _) hM2
    (refCoulomb_h1 r hg hC Hunit hPeriodic n) (umod u) hH2'
  exact tail_regimes hg (kabs_cube_le hL) a _ (tB_nonneg C Hunit _) (tZ_nonneg hg) hM2 hK1 hfull
    (fun h2g hn => single_tail_release r a hg hC Hunit hPeriodic hK1 h2g hn hM2 (umod u) hH2')

/-- **The potential tail** (eq:grid-tail for the `g_L` potential): for every register `a`, every
`K ≥ 1` and every state with `H²` budget `M₂`,
`‖1{|k_{p_a}| > K} W_L u‖ ≤ Q (1 + V_θ) c_tail M₂ K^{-1/2}`. -/
theorem gLpot_tail_bound (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (a : Fin eta)
    {Kt M2 : ℝ} (hK1 : 1 ≤ Kt) (hM2 : 0 ≤ M2) (u : En eta n)
    (hH2 : fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) u.ofLp ≤ M2 ^ 2) :
    ‖referenceTailOperator Kt (finitePlaneWaveKabs (2 * Real.pi / L) n) a (gLpot sys L θ n u)‖ ≤
      sys.couplingWeight * ((1 + tv R θ) * ctail (coulombCellAmplitude L ^ 2) Hunit
        (2 * Real.pi / L)) * M2 * Kt ^ (-(1 / 2 : ℝ)) := by
  classical
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hV : 0 ≤ 1 + tv R θ := by linarith [hθ.tv_nonneg]
  have hC : 0 ≤ coulombCellAmplitude L ^ 2 := sq_nonneg _
  set T := (1 + tv R θ) * ctail (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L) * M2 *
    Kt ^ (-(1 / 2 : ℝ)) with hT
  have hK0 : 0 < Kt := by linarith
  have hT0 : 0 ≤ T := by
    have := ctail_nonneg (C := coulombCellAmplitude L ^ 2) (Hunit := Hunit) hg
    have := Real.rpow_pos_of_pos hK0 (-(1 / 2 : ℝ))
    positivity
  set kabs := finitePlaneWaveKabs (2 * Real.pi / L) n with hkabs
  have hN : ∀ (a' : Fin eta) (l : ν), ‖referenceTailOperator Kt kabs a
      (referenceKernelConvolutionOperator a' (gLnuc sys.nuclei L θ n l) u)‖ ≤
      sys.nuclei.charge l * T := by
    intro a' l
    have hZ := sys.nuclei.charge_nonneg l
    have h := tail_single_M2 hL a' a hC Hunit hPeriodic
      (referenceConfigurationKernel a' (gLnuc sys.nuclei L θ n l)) (mul_nonneg hZ hV)
      (refKernel_dom a' (gLnuc sys.nuclei L θ n l)
        (fun v w => norm_gLnuc_le hL hθ sys.nuclei n l v w)) hK1 hM2 u hH2
    rw [fcko_refKernel] at h
    refine h.trans (le_of_eq ?_)
    rw [hT]; ring
  have hP : ∀ pair : FiniteElectronPair eta, ‖referenceTailOperator Kt kabs a
      (finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n) u)‖ ≤ T := by
    intro pair
    have h := tail_pair_M2 hL (ne_of_lt pair.2) a hC Hunit hPeriodic
      (finiteElectronPairLiftKernel pair.1.1 pair.1.2 n (gLk L θ n)) hV
      (fun q p => norm_lift_gLk_le hL hθ pair.1.1 pair.1.2 n q p) hK1 hM2 u hH2
    exact h.trans (le_of_eq (by rw [hT]))
  have hExp : referenceTailOperator Kt kabs a (gLpot sys L θ n u) =
      (∑ a' : Fin eta, ((-sys.charge a' : ℝ) : ℂ) • ∑ l : ν, referenceTailOperator Kt kabs a
        (referenceKernelConvolutionOperator a' (gLnuc sys.nuclei L θ n l) u)) +
      ∑ pair : FiniteElectronPair eta, ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) •
        referenceTailOperator Kt kabs a
          (finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n) u) := by
    unfold gLpot
    simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_add, map_sum,
      map_smul]
  have h1 : ‖∑ a' : Fin eta, ((-sys.charge a' : ℝ) : ℂ) • ∑ l : ν, referenceTailOperator Kt kabs a
      (referenceKernelConvolutionOperator a' (gLnuc sys.nuclei L θ n l) u)‖ ≤
      ∑ a' : Fin eta, |sys.charge a'| * ∑ l : ν, sys.nuclei.charge l * T := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
    rw [norm_smul, norm_ofReal_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hN a' l)
  have h2 : ‖∑ pair : FiniteElectronPair eta,
      ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) • referenceTailOperator Kt kabs a
        (finiteElectronPairKernelOperator pair.1.1 pair.1.2 n (gLk L θ n) u)‖ ≤
      ∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2| * T := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun pair _ => ?_)
    rw [norm_smul, norm_ofReal']
    exact mul_le_mul_of_nonneg_left (hP pair) (abs_nonneg _)
  rw [hExp]
  refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  have e1 : ∑ a' : Fin eta, |sys.charge a'| * ∑ l : ν, sys.nuclei.charge l * T =
      (∑ a', |sys.charge a'|) * sys.nuclei.totalCharge * T := by
    unfold FiniteBONuclearData.totalCharge
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← Finset.sum_mul]
    ring
  have e2 : ∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2| * T =
      (∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2|) * T := by
    rw [Finset.sum_mul]
  rw [e1, e2, hT]
  unfold CoulombSystem.couplingWeight
  ring

end Tail

/-! ## The Galerkin energy bound -/

/-- The `H¹` constant `(1 + V) B Q` of the `g_L` potential (`V` the total variation of `θ`). -/
noncomputable def gLformConst (sys : CoulombSystem eta ν) (L V Hunit : ℝ) : ℝ :=
  sys.couplingWeight * ((1 + V) * tB (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L))

/-- The mass-weighted `H¹` constant `(1 + V) B Q_m`. -/
noncomputable def gLmassConst (sys : CoulombSystem eta ν) (L V Hunit : ℝ) : ℝ :=
  sys.massCouplingWeight * ((1 + V) * tB (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L))

/-- The `H²` budget `m̄ (2 + 8 E₀ + 16 B_m²)` of normalised eigenvectors with `|E| ≤ E₀`. -/
noncomputable def gLH2Const (sys : CoulombSystem eta ν) (L V Hunit E0 : ℝ) : ℝ :=
  sys.maxMass * uniformBOEigenH2Constant E0 (gLmassConst sys L V Hunit)

/-- The tail constant `C_W = Q (1 + V) c_tail M₂`. -/
noncomputable def gLtailConst (sys : CoulombSystem eta ν) (L V Hunit E0 : ℝ) : ℝ :=
  sys.couplingWeight * ((1 + V) * ctail (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L)) *
    gLH2Const sys L V Hunit E0

lemma gLformConst_nonneg (sys : CoulombSystem eta ν) (L : ℝ) {V : ℝ} (hV : 0 ≤ V) (Hunit : ℝ) :
    0 ≤ gLformConst sys L V Hunit :=
  mul_nonneg sys.couplingWeight_nonneg (mul_nonneg (by linarith) (tB_nonneg _ _ _))

lemma gLH2Const_nonneg (sys : CoulombSystem eta ν) (L V Hunit : ℝ) {E0 : ℝ} (hE0 : 0 ≤ E0) :
    0 ≤ gLH2Const sys L V Hunit E0 :=
  mul_nonneg (le_trans zero_le_one sys.one_le_maxMass) (uniformBOEigenH2Constant_nonneg hE0)

lemma gLham_isSymmetric (hθ : Profile R θ) (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) :
    (gLham sys L θ n).IsSymmetric :=
  diagHamiltonian_isSymmetric _ _ (gLpot_isSymmetric hθ sys L n)

/-- **The `H²` bound** of normalised eigenvectors of the `g_L` Hamiltonian with `|E| ≤ E₀`. -/
theorem gL_eigen_fullH2Sq_le (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (n : ℕ) (coeff : FourierConfig eta (FinitePlaneWaveMode n) → ℂ) (E E0 : ℝ) (hE0 : 0 ≤ E0)
    (hEnergy : |E| ≤ E0) (hNormalized : (∑ p, coeffMass coeff p) = 1)
    (hEigen : gLham sys L θ n (fullCoeffVector coeff) = (E : ℂ) • fullCoeffVector coeff) :
    fullH2Sq (finitePlaneWaveKabs (2 * Real.pi / L) n) coeff ≤
      (gLH2Const sys L (tv R θ) Hunit E0) ^ 2 := by
  have hTheta : massH2Sq sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) coeff ≤
      (uniformBOEigenH2Constant E0 (gLmassConst sys L (tv R θ) Hunit)) ^ 2 :=
    diag_eigen_h2_le_uniform _ coeff _ E E0 _ hE0 hEnergy
      (gLpot_massBound sys hL hθ Hunit hPeriodic n) hNormalized hEigen
  have hFull := fullH2Sq_le_mass_sq_mul_massH2Sq sys.one_le_mass sys.mass_le_maxMass
    sys.one_le_maxMass (finitePlaneWaveKabs (2 * Real.pi / L) n) coeff
  unfold gLH2Const
  rw [mul_pow]
  exact hFull.trans (mul_le_mul_of_nonneg_left hTheta (sq_nonneg _))

/-- **The Galerkin energy bound for the `g_L` Hamiltonian on the cube.** For a normalised sector
eigenvector of `gLham` with energy `E` (`|E| ≤ E₀`) which is the sector ground energy, and the
cubic Galerkin ground energy `E_N` at cutoff `K` (large: `4 m̄ |E| ≤ K²`,
`32 S₂ C_W² ≤ K⁵`): `0 ≤ E_N - E` and `K³ (E_N - E) ≤ 64 (1/2 + C_pot + |E|) S₁ S₂ C_W²`, with
`C_pot = (1 + V) B Q` and `C_W = Q (1 + V) c_tail m̄ (2 + 8E₀ + 16 B_m²)`. -/
theorem gL_cubic_energy_bound (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {sgn : Fin eta → ℂ} {lab : Fin eta → ℕ} (n : ℕ) (K E EN E0 : ℝ)
    (coeff : FourierConfig eta (FinitePlaneWaveMode n) → ℂ)
    (hK1 : 1 ≤ K) (hE0 : 0 ≤ E0) (hEnergy : |E| ≤ E0)
    (hAbsorb : 4 * sys.maxMass * |E| ≤ K ^ 2)
    (hLargeK : 32 * (∑ a, sys.mass a ^ 2) * (gLtailConst sys L (tv R θ) Hunit E0) ^ 2 ≤ K ^ 5)
    (hSector : IsSectorCoeff sgn lab coeff)
    (hNormalized : (∑ p, coeffMass coeff p) = 1)
    (hEigen : gLham sys L θ n (fullCoeffVector coeff) = (E : ℂ) • fullCoeffVector coeff)
    (hGround : IsSectorGroundEnergy sgn lab (gLham sys L θ n) E)
    (hGalerkin : IsSectorCubicGalerkinGroundEnergy eta sgn lab K (2 * Real.pi / L) n
      (gLham sys L θ n) EN) :
    0 ≤ EN - E ∧ K ^ 3 * (EN - E) ≤
      64 * ((1 / 2 : ℝ) + gLformConst sys L (tv R θ) Hunit + |E|) * (∑ a, sys.mass a) *
        (∑ a, sys.mass a ^ 2) * (gLtailConst sys L (tv R θ) Hunit E0) ^ 2 := by
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hK0 : 0 < K := by linarith
  have hV := hθ.tv_nonneg
  have hH2 := gL_eigen_fullH2Sq_le sys hL hθ Hunit hPeriodic n coeff E E0 hE0 hEnergy
    hNormalized hEigen
  have hM2 := gLH2Const_nonneg sys L (tv R θ) Hunit hE0
  have hPT : ∀ r : Fin eta, ‖referenceTailVector K (finitePlaneWaveKabs (2 * Real.pi / L) n) r
      (operatorPotentialCoeff (gLpot sys L θ n) coeff)‖ ≤
      gLtailConst sys L (tv R θ) Hunit E0 * K ^ (-(1 / 2 : ℝ)) := by
    intro r
    rw [← referenceTailOperator_potential]
    refine (gLpot_tail_bound sys hL hθ Hunit hPeriodic r hK1 hM2 (fullCoeffVector coeff)
      hH2).trans (le_of_eq ?_)
    unfold gLtailConst
    ring
  have hPotential := discarded_potential_form_of_h1OperatorBound K
    (finitePlaneWaveKabs (2 * Real.pi / L) n) coeff (gLpot sys L θ n)
    (gLformConst_nonneg sys L hV Hunit) (gLpot_h1Bound sys hL hθ Hunit hPeriodic n) le_rfl
  exact mass_sector_cubic_energy_bound_of_tail_and_form eta sys.mass sys.maxMass K
    (2 * Real.pi / L) E EN (gLtailConst sys L (tv R θ) Hunit E0) (K ^ (-(1 / 2 : ℝ)))
    (gLformConst sys L (tv R θ) Hunit) n coeff (gLpot sys L θ n) sys.one_le_mass
    sys.mass_le_maxMass hK1 hg.le (rho_scale hK0).le hPT hAbsorb hSector hNormalized hLargeK
    (gLpot_isSymmetric hθ sys L n) hEigen hGround hGalerkin
    (gLformConst_nonneg sys L hV Hunit) hPotential

end FreeBoundary
