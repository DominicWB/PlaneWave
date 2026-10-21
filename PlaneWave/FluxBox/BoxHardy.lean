import PlaneWave.FluxBox.BoxLatticeTools

/-!
# Flux route, stage 2, part 4: Hardy bounds for channel-dominated box kernels

The positive channel Coulomb kernels `couK j = γ/|θ|²` (on channel-`j` elements) are the kernels of
the release's pair operators and one-body convolutions (`pairOp_eq`, `oneOp_eq`), so the canonical
periodic Hardy bound gives (`couK_bound`)

  `‖kop couK_j v‖² ≤ B_j² Σ_p (1 + 2A(p)) |v_p|²`.

By domination (`norm_kop_le_potMaj`): **every box kernel dominated by the channel majorant
`potMaj` is Hardy-bounded**, with the constant `CH = Σ_j (c_j/γ) B_j`; in particular `W_N` and the
flat potential `Ŵ_N` (`norm_WhN_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Hardy

variable (sys : CoulombSystem eta ν) {L : ℝ} {N : ℕ}

/-- The positive Coulomb kernel of channel `j` on the box. -/
noncomputable def couK (L : ℝ) (N : ℕ) (j : Ch eta) (q p : Cfg eta N) : ℝ :=
  chMaj j (coulombCellAmplitude L) (cidx N q) (cidx N p)

omit [Fintype ν] in
lemma onCh_inl_iff (a : Fin eta) (x y : Cf eta) : OnCh (.inl a) x y ↔ ∀ k, k ≠ a → x k = y k := by
  constructor
  · intro h k hk
    have e : x = y + tr (.inl a) (x (lead (.inl a)) - y (lead (.inl a))) := h
    rw [e]
    simp [tr, Pi.single_eq_of_ne hk]
  · intro h
    apply onCh_of_eq (ν := x a - y a)
    funext k
    by_cases hk : k = a
    · subst hk; simp [tr]
    · simp [tr, Pi.single_eq_of_ne hk, h k hk]

omit [Fintype ν] in
lemma onCh_inr_iff (pr : FiniteElectronPair eta) (x y : Cf eta) :
    OnCh (.inr pr) x y ↔ (∀ k, k ≠ pr.1.1 → k ≠ pr.1.2 → x k = y k) ∧
      x pr.1.1 + x pr.1.2 = y pr.1.1 + y pr.1.2 := by
  have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
  constructor
  · intro h
    have e : x = y + tr (.inr pr) (x (lead (.inr pr)) - y (lead (.inr pr))) := h
    simp only [lead] at e
    refine ⟨fun k h1 h2 => ?_, ?_⟩
    · rw [e]; simp [tr, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
    · rw [e]
      simp [tr, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
      abel
  · rintro ⟨h1, h2⟩
    apply onCh_of_eq (ν := x pr.1.1 - y pr.1.1)
    funext k
    by_cases hk1 : k = pr.1.1
    · subst hk1; simp [tr, Pi.single_eq_of_ne hne]
    · by_cases hk2 : k = pr.1.2
      · subst hk2
        simp [tr, Pi.single_eq_of_ne hne.symm]
        linear_combination h2
      · simp [tr, Pi.single_eq_of_ne hk1, Pi.single_eq_of_ne hk2, h1 k hk1 hk2]

omit [Fintype ν] in
lemma latticeSub_eq_sub (a b : Lattice3) : latticeSub a b = a - b := by
  funext i; simp [latticeSub]

omit [Fintype ν] in
lemma latticeCoulombKernel_eq (hL : 0 < L) (x y : Lattice3) :
    latticeCoulombKernel (coulombCellAmplitude L ^ 2) x y =
      ((coulombCellAmplitude L / latticeNormSq (x - y) : ℝ) : ℂ) := by
  have hγ : 0 ≤ coulombCellAmplitude L := by unfold coulombCellAmplitude; positivity
  rw [latticeCoulombKernel_of_amplitude_sq _ hγ, latticeSub_eq_sub]

omit [Fintype ν] in
/-- The pair operator of the release has the positive channel kernel `couK`. -/
lemma pairOp_eq (hL : 0 < L) (pr : FiniteElectronPair eta) :
    finiteElectronPairCoulombOperator pr.1.1 pr.1.2 (coulombCellAmplitude L ^ 2) N =
      FSKernel.kop (fun q p => (couK L N (.inr pr) q p : ℂ)) := by
  classical
  ext u q
  rw [finiteElectronPairCoulombOperator_apply, FSKernel.kop_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [finiteElectronPairConfigurationKernel_eq_lattice]
  unfold latticeElectronPairConfigurationKernel couK chMaj
  by_cases h : OnCh (.inr pr) (cidx N q) (cidx N p)
  · rw [if_pos ((onCh_inr_iff pr _ _).mp h), if_pos h, latticeCoulombKernel_eq hL]
    rfl
  · rw [if_neg (fun h' => h ((onCh_inr_iff pr _ _).mpr h')), if_neg h]
    simp

omit [Fintype ν] in
/-- The one-body Coulomb convolution of the release has the positive channel kernel `couK`. -/
lemma oneOp_eq (hL : 0 < L) (a : Fin eta) :
    referenceKernelConvolutionOperator a (finiteCoulombKernel (coulombCellAmplitude L ^ 2) N) =
      FSKernel.kop (fun q p => (couK L N (.inl a) q p : ℂ)) := by
  classical
  ext u q
  rw [referenceKernelConvolutionOperator_apply, FSKernel.kop_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  have e1 : referenceConfigurationKernel a (finiteCoulombKernel (coulombCellAmplitude L ^ 2) N) q p =
      latticeReferenceConfigurationKernel a (latticeCoulombKernel (coulombCellAmplitude L ^ 2))
        (cidx N q) (cidx N p) :=
    referenceConfigurationKernel_eq_lattice a N (latticeCoulombKernel (coulombCellAmplitude L ^ 2)) q p
  rw [e1]
  unfold latticeReferenceConfigurationKernel couK chMaj
  by_cases h : OnCh (.inl a) (cidx N q) (cidx N p)
  · rw [if_pos ((onCh_inl_iff a _ _).mp h), if_pos h, latticeCoulombKernel_eq hL]
    rfl
  · rw [if_neg (fun h' => h ((onCh_inl_iff a _ _).mpr h')), if_neg h]
    simp

/-- The Hardy constant of channel `j`. -/
noncomputable def hB (L Hunit : ℝ) : Ch eta → ℝ
  | .inl a => Real.sqrt (sys.mass a) * coulombPhysicalCellConstant L Hunit
  | .inr pr => Real.sqrt (min (sys.mass pr.1.1) (sys.mass pr.1.2)) * coulombPhysicalCellConstant L Hunit

omit [Fintype ν] in
lemma hB_nonneg (L Hunit : ℝ) (j : Ch eta) : 0 ≤ hB sys L Hunit j := by
  have := coulombPhysicalCellConstant_nonneg L Hunit
  cases j with
  | inl a => simp only [hB]; positivity
  | inr pr => simp only [hB]; positivity

/-- The kinetic weight `1 + 2A`. -/
noncomputable abbrev hw (sys : CoulombSystem eta ν) (L : ℝ) (N : ℕ) : Cfg eta N → ℝ :=
  fun p => 1 + massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) N) p

omit [Fintype ν] in
/-- **Hardy for the positive channel Coulomb kernels.** -/
theorem couK_bound (hL : 0 < L) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (j : Ch eta) (v : En eta N) :
    ‖FSKernel.kop (fun q p => (couK L N j q p : ℂ)) v‖ ^ 2 ≤
      hB sys L Hunit j ^ 2 * weightedNormSq (hw sys L N) v := by
  have hScale := coulombPhysicalCellConstant_scale L Hunit hL
  set B := coulombPhysicalCellConstant L Hunit
  set g := 2 * Real.pi / L
  set γ := coulombCellAmplitude L
  cases j with
  | inl a =>
    rw [← oneOp_eq hL a]
    have hOne := oneParticleCoulombH1Bound_of_canonicalPeriodic g (γ ^ 2) B Hunit N (sq_nonneg γ)
      hPeriodic hScale
    have h1 := referenceKernelConvolutionOperator_registerBound a (finitePlaneWaveKabs g N)
      (finiteCoulombKernel (γ ^ 2) N) B (fun f =>
        coulomb_dominated_kernel_oneParticle_h1 g (γ ^ 2) B N (finiteCoulombKernel (γ ^ 2) N)
          (fun v w => by
            unfold finiteCoulombKernel
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)])
          hOne f)
    have h2 := registerBound_massBound sys.one_le_mass (finitePlaneWaveKabs g N) a h1
    exact h2 v
  | inr pr =>
    rw [← pairOp_eq hL pr]
    exact finiteElectronPairCoulombOperator_massBound sys.one_le_mass pr.1.1 pr.1.2 (ne_of_lt pr.2)
      g (γ ^ 2) B Hunit N (sq_nonneg γ) hPeriodic hScale v

/-- The Hardy constant of the channel majorant: `CH = Σ_j (c_j/γ) B_j`. -/
noncomputable def CH (L Hunit : ℝ) : ℝ := ∑ j : Ch eta, chC sys L j / coulombCellAmplitude L * hB sys L Hunit j

lemma CH_nonneg (hL : 0 < L) (Hunit : ℝ) : 0 ≤ CH sys L Hunit := by
  have hγ : 0 < coulombCellAmplitude L := by unfold coulombCellAmplitude; positivity
  exact Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg (chC_nonneg sys hL j) hγ.le)
    (hB_nonneg sys L Hunit j)

omit [Fintype ν] in
lemma weightedNormSq_absv (v : En eta N) :
    weightedNormSq (hw sys L N) (FSKernel.absv v) = weightedNormSq (hw sys L N) v := by
  unfold weightedNormSq
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [FSKernel.absv_apply, Complex.norm_real, Real.norm_eq_abs, abs_norm]

omit [Fintype ν] in
lemma weightedNormSq_hw_nonneg (v : En eta N) : 0 ≤ weightedNormSq (hw sys L N) v :=
  Finset.sum_nonneg fun p _ => mul_nonneg (by
    have := massKineticSymbol_nonneg sys L N p; simp only [hw]; linarith) (sq_nonneg _)

/-- **Hardy for majorant-dominated box kernels**: if `|κ(q, p)| ≤ potMaj(q, p)`, then
`‖kop κ v‖ ≤ CH (Σ_p (1 + 2A(p)) |v_p|²)^{1/2}`. -/
theorem norm_kop_le_potMaj (hL : 0 < L) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (κ : Cfg eta N → Cfg eta N → ℂ) (hκ : ∀ q p, ‖κ q p‖ ≤ potMaj sys L (cidx N q) (cidx N p))
    (v : En eta N) :
    ‖FSKernel.kop κ v‖ ≤ CH sys L Hunit * Real.sqrt (weightedNormSq (hw sys L N) v) := by
  have hγ : 0 < coulombCellAmplitude L := by unfold coulombCellAmplitude; positivity
  have hmaj : ∀ q p, ‖κ q p‖ ≤
      ∑ j ∈ Finset.univ, chC sys L j / coulombCellAmplitude L * couK L N j q p := by
    intro q p
    refine (hκ q p).trans (le_of_eq ?_)
    unfold potMaj couK chMaj
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · field_simp
    · simp
  have h1 := FSKernel.norm_kop_le_of_maj Finset.univ κ
    (fun j q p => chC sys L j / coulombCellAmplitude L * couK L N j q p)
    (fun j q p => mul_nonneg (div_nonneg (chC_nonneg sys hL j) hγ.le)
      (chMaj_nonneg j hγ.le _ _)) hmaj v
  refine h1.trans ?_
  unfold CH
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : (fun q p => ((chC sys L j / coulombCellAmplitude L * couK L N j q p : ℝ) : ℂ)) =
      ((chC sys L j / coulombCellAmplitude L : ℝ) : ℂ) • fun q p => (couK L N j q p : ℂ) := by
    funext q p; simp
  rw [e, FSKernel.kop_smul, LinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (chC_nonneg sys hL j) hγ.le), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (chC_nonneg sys hL j) hγ.le)
  have h2 := couK_bound sys hL Hunit hPeriodic j (FSKernel.absv v)
  rw [weightedNormSq_absv] at h2
  have h3 : ‖FSKernel.kop (fun q p => (couK L N j q p : ℂ)) (FSKernel.absv v)‖ ≤
      hB sys L Hunit j * Real.sqrt (weightedNormSq (hw sys L N) v) := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (hB_nonneg sys L Hunit j), ← Real.sqrt_mul
      (sq_nonneg _)]
    exact Real.sqrt_le_sqrt h2
  exact h3

lemma potMaj_sub (q p : Cf eta) : potMaj sys L (q - p) 0 = potMaj sys L q p := by
  unfold potMaj chMaj
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : OnCh j q p
  · rw [if_pos ((onCh_iff_sub j q p).mp h), if_pos h]
    simp
  · rw [if_neg (fun h' => h ((onCh_iff_sub j q p).mpr h')), if_neg h]

/-- `|whK(q, p)| ≤ potMaj(q, p)`. -/
lemma norm_whK_le (hL : 0 < L) (p₀ : Fin eta) (q p : Cfg eta N) :
    ‖whK sys L p₀ N q p‖ ≤ potMaj sys L (cidx N q) (cidx N p) := by
  rw [whK_eq_convK]
  unfold convK
  rw [← potMaj_sub]
  exact norm_whL_le hL _

/-- **Hardy for `W_N`** (through the majorant). -/
theorem norm_WN_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (v : En eta N) :
    ‖WN sys L N v‖ ≤ CH sys L Hunit * Real.sqrt (weightedNormSq (hw sys L N) v) := by
  have hW : WN sys L N = FSKernel.kop (wNK sys L N) := VN_eq_kop sys hL H hKernel
  rw [hW]
  exact norm_kop_le_potMaj sys hL Hunit hPeriodic _ (fun q p => norm_potKernel_le sys hL _ _) v

/-- **Hardy for the flat potential `Ŵ_N`.** -/
theorem norm_WhN_le (hL : 0 < L) (p₀ : Fin eta) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (v : En eta N) :
    ‖WhN sys L p₀ N v‖ ≤ CH sys L Hunit * Real.sqrt (weightedNormSq (hw sys L N) v) :=
  norm_kop_le_potMaj sys hL Hunit hPeriodic _ (norm_whK_le sys hL p₀) v

end Hardy

end FSFlux
