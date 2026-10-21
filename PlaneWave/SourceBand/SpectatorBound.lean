import PlaneWave.SourceBand.BandGalerkin

/-!
# Source band block, part 4: the channel potentials and the spectator bound

The paragraph after `lem:thinschur` bounds the channel parts of `W` separately. Here a channel `j`
(one-body `a`, or the pair `(a, b)`) gets its own potential through the **channel system**
`sysCh sys j`: the charges of the registers moved by `j` (and, for a one-body channel, the nuclei),
all other charges zero. Then

* `potKernel_eq_sum`: `w(q, p) = Σ_j w_j(q, p)`, `w_j` the kernel of the channel system;
* `potKernel_sysCh_le`: `|w_j(q, p)| ≤ [q = p + τ_j(ν)] c_j/|ν|²`;
* `Wch j` (the potential of the channel system, an operator on `H²` like `W`), `Wch_apply`,
  **`W_eq_sum_Wch`** (`W = Σ_j W_j`) and the Hardy bound `norm_Wch_sq_le` of each `W_j` (the
  release's relative bound for the channel system: no separate per-pair Hardy argument);
* `Wch_shMask`: a channel that does not move `a` commutes with the shell masks of `a`;
* **`band_spectator`** (K2, spectators): `‖1_S W_j u‖ ≤ √3 C_j B λ^{-2} ρ^{1/2}` when
  `‖1_S û‖ ≤ B λ^{-3} ρ^{1/2}` and `‖1_S ℰ û‖ ≤ B λ^{-1} ρ^{1/2}` (`a ∉ j`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal FSFlux

namespace FSBand

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The channel systems -/

section Reduced

/-- The nuclear data with all charges removed. -/
def nucZero (data : FiniteBONuclearData ν) : FiniteBONuclearData ν where
  charge := fun _ => 0
  charge_nonneg := fun _ => le_rfl
  position := data.position

/-- **The system of channel `j`**: the charges of the registers moved by `j` (with the nuclei for a
one-body channel); every other charge is zero and every register is its own species. -/
def sysCh (sys : CoulombSystem eta ν) (j : Ch eta) : CoulombSystem eta ν where
  mass := sys.mass
  one_le_mass := sys.one_le_mass
  charge := fun a => if a ∈ moved j then sys.charge a else 0
  species := fun a => a.val
  fermion := sys.fermion
  mass_eq := fun a b h => by rw [Fin.ext h]
  charge_eq := fun a b h => by rw [Fin.ext h]
  nuclei := match j with
    | .inl _ => sys.nuclei
    | .inr _ => nucZero sys.nuclei

variable (sys : CoulombSystem eta ν)

omit [Fintype ν] in
lemma sysCh_charge (j : Ch eta) (a : Fin eta) :
    (sysCh sys j).charge a = if a ∈ moved j then sys.charge a else 0 := rfl

omit [Fintype ν] in
lemma kinetic_sysCh (j : Ch eta) (g : ℝ) :
    coulombFourierKineticH2 (sysCh sys j) g = coulombFourierKineticH2 sys g := rfl

omit [Fintype ν] in
lemma sysCh_maxMass (j : Ch eta) : (sysCh sys j).maxMass = sys.maxMass := rfl

omit [Fintype ν] in
lemma pair_mem_moved {pr pr' : FiniteElectronPair eta} (h1 : pr'.1.1 ∈ moved (.inr pr : Ch eta))
    (h2 : pr'.1.2 ∈ moved (.inr pr : Ch eta)) : pr' = pr := by
  simp only [moved, Finset.mem_insert, Finset.mem_singleton] at h1 h2
  have hlt' := pr'.2
  have hlt := pr.2
  apply Subtype.ext
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exfalso; rw [h1, h2] at hlt'; exact lt_irrefl _ hlt'
  · exact Prod.ext h1 h2
  · exfalso; rw [h1, h2] at hlt'; exact lt_asymm hlt hlt'
  · exfalso; rw [h1, h2] at hlt'; exact lt_irrefl _ hlt'

/-- The channel constants of a channel system: `c_j` on `j`, zero elsewhere. -/
lemma chC_sysCh (L : ℝ) (j j' : Ch eta) :
    chC (sysCh sys j) L j' = if j' = j then chC sys L j else 0 := by
  cases j' with
  | inl a =>
    cases j with
    | inl b =>
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl]
        simp only [chC, sysCh_charge, moved, Finset.mem_singleton, if_true]
        rfl
      · rw [if_neg (fun h => hab (Sum.inl_injective h))]
        simp only [chC, sysCh_charge, moved, Finset.mem_singleton, hab, if_false, abs_zero,
          zero_mul]
    | inr pr =>
      rw [if_neg Sum.inl_ne_inr]
      simp only [chC]
      change |(sysCh sys (.inr pr)).charge a| * (∑ ell, (nucZero sys.nuclei).charge ell) *
        coulombCellAmplitude L = 0
      simp [nucZero]
  | inr pr' =>
    cases j with
    | inl b =>
      rw [if_neg Sum.inr_ne_inl]
      simp only [chC, sysCh_charge]
      have hne : pr'.1.1 ≠ pr'.1.2 := ne_of_lt pr'.2
      by_cases h1 : pr'.1.1 ∈ moved (.inl b : Ch eta)
      · have h2 : pr'.1.2 ∉ moved (.inl b : Ch eta) := by
          simp only [moved, Finset.mem_singleton] at h1 ⊢
          intro h2; exact hne (h1.trans h2.symm)
        rw [if_neg h2]; simp
      · rw [if_neg h1]; simp
    | inr pr =>
      by_cases hp : pr' = pr
      · subst hp
        rw [if_pos rfl]
        simp only [chC, sysCh_charge]
        have h1 : pr'.1.1 ∈ moved (.inr pr' : Ch eta) := by simp [moved]
        have h2 : pr'.1.2 ∈ moved (.inr pr' : Ch eta) := by simp [moved]
        rw [if_pos h1, if_pos h2]
      · rw [if_neg (fun h => hp (Sum.inr_injective h))]
        simp only [chC, sysCh_charge]
        by_cases h1 : pr'.1.1 ∈ moved (.inr pr : Ch eta)
        · have h2 : pr'.1.2 ∉ moved (.inr pr : Ch eta) := fun h2 => hp (pair_mem_moved h1 h2)
          rw [if_neg h2]; simp
        · rw [if_neg h1]; simp

/-- **The channel kernel bound**: `|w_j(q, p)| ≤ [q = p + τ_j(ν)] c_j/|ν|²`. -/
lemma potKernel_sysCh_le {L : ℝ} (hL : 0 < L) (j : Ch eta) (q p : Cf eta) :
    ‖potKernel (sysCh sys j) L q p‖ ≤ chMaj j (chC sys L j) q p := by
  refine (norm_potKernel_le (sysCh sys j) hL q p).trans (le_of_eq ?_)
  unfold potMaj
  rw [Finset.sum_eq_single j]
  · rw [chC_sysCh, if_pos rfl]
  · intro j' _ hj'
    rw [chC_sysCh, if_neg hj']
    unfold chMaj; split_ifs <;> simp
  · intro h; exact absurd (Finset.mem_univ j) h

lemma potKernel_sysCh_onCh {L : ℝ} (hL : 0 < L) {j : Ch eta} {q p : Cf eta}
    (h : potKernel (sysCh sys j) L q p ≠ 0) : OnCh j q p := by
  by_contra hon
  apply h
  have := potKernel_sysCh_le sys hL j q p
  unfold chMaj at this
  rw [if_neg hon] at this
  exact norm_le_zero_iff.mp this

omit [Fintype ν] in
lemma refKernel_zero (i : Fin eta) (q p : Cf eta) :
    latticeReferenceConfigurationKernel i (fun _ _ => (0 : ℂ)) q p = 0 := by
  unfold latticeReferenceConfigurationKernel; split_ifs <;> rfl

/-- **The channel decomposition of the kernel**: `w = Σ_j w_j`. -/
theorem potKernel_eq_sum (L : ℝ) (q p : Cf eta) :
    potKernel sys L q p = ∑ j : Ch eta, potKernel (sysCh sys j) L q p := by
  rw [Fintype.sum_sum_type]
  -- one-body channels
  have hnuc : ∀ b : Fin eta, potKernel (sysCh sys (.inl b)) L q p =
      ((-sys.charge b : ℝ) : ℂ) * ∑ ell : ν, latticeReferenceConfigurationKernel b
        (latticeElectronNuclearKernel sys.nuclei (coulombCellAmplitude L) ell) q p := by
    intro b
    unfold potKernel coulombLatticeNuclearKernel coulombLatticePairKernel
    have hpair : ∀ pr : FiniteElectronPair eta,
        (((sysCh sys (.inl b)).charge pr.1.1 * (sysCh sys (.inl b)).charge pr.1.2 : ℝ) : ℂ) = 0 := by
      intro pr
      have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
      simp only [sysCh_charge, moved, Finset.mem_singleton]
      by_cases h1 : pr.1.1 = b
      · have h2 : ¬ pr.1.2 = b := fun h2 => hne (h1.trans h2.symm)
        rw [if_neg h2]; simp
      · rw [if_neg h1]; simp
    simp only [hpair, zero_mul, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single b]
    · simp only [sysCh_charge, moved, Finset.mem_singleton, if_true]
      rfl
    · intro i _ hi
      simp only [sysCh_charge, moved, Finset.mem_singleton, hi, if_false]
      simp
    · intro h; exact absurd (Finset.mem_univ b) h
  -- pair channels
  have hpr : ∀ pr : FiniteElectronPair eta, potKernel (sysCh sys (.inr pr)) L q p =
      ((sys.charge pr.1.1 * sys.charge pr.1.2 : ℝ) : ℂ) *
        latticeElectronPairConfigurationKernel pr.1.1 pr.1.2 (coulombCellAmplitude L ^ 2) q p := by
    intro pr
    unfold potKernel coulombLatticeNuclearKernel coulombLatticePairKernel
    have hnz : ∀ (i : Fin eta) (ell : ν), latticeReferenceConfigurationKernel i
        (latticeElectronNuclearKernel (sysCh sys (.inr pr)).nuclei (coulombCellAmplitude L) ell)
          q p = 0 := by
      intro i ell
      have e : latticeElectronNuclearKernel (sysCh sys (.inr pr)).nuclei (coulombCellAmplitude L) ell =
          fun _ _ => (0 : ℂ) := by
        funext x y
        change latticeElectronNuclearKernel (nucZero sys.nuclei) (coulombCellAmplitude L) ell x y = 0
        unfold latticeElectronNuclearKernel nucZero
        simp
      rw [e, refKernel_zero]
    simp only [hnz, Finset.sum_const_zero, mul_zero, zero_add]
    rw [Finset.sum_eq_single pr]
    · have h1 : pr.1.1 ∈ moved (.inr pr : Ch eta) := by simp [moved]
      have h2 : pr.1.2 ∈ moved (.inr pr : Ch eta) := by simp [moved]
      simp only [sysCh_charge, if_pos h1, if_pos h2]
    · intro pr' _ hp
      by_cases h1 : pr'.1.1 ∈ moved (.inr pr : Ch eta)
      · have h2 : pr'.1.2 ∉ moved (.inr pr : Ch eta) := fun h2 => hp (pair_mem_moved h1 h2)
        simp only [sysCh_charge, if_neg h2]; simp
      · simp only [sysCh_charge, if_neg h1]; simp
    · intro h; exact absurd (Finset.mem_univ pr) h
  simp only [hnuc, hpr]
  unfold potKernel coulombLatticeNuclearKernel coulombLatticePairKernel
  rfl

end Reduced

/-! ## The channel potentials -/

section Channel

variable (sys : CoulombSystem eta ν) (L Hunit : ℝ) (hL : 0 < L)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

/-- The Hamiltonian of the channel system (the release's completed operator). -/
noncomputable def Hch (j : Ch eta) :
    MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
  Classical.choose (exists_coulombFourierH2Operator (sysCh sys j) L Hunit hL hPeriodic)

lemma Hch_kernel (j : Ch eta) : ∀ N u q, Hch sys L Hunit hL hPeriodic j (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel (sysCh sys j) L) N u q :=
  (Classical.choose_spec (exists_coulombFourierH2Operator (sysCh sys j) L Hunit hL hPeriodic)).1

/-- **The channel-`j` potential** `W_j` (the potential of the channel system). -/
noncomputable abbrev Wch (j : Ch eta) : MolecularFourierH2 eta →L[ℂ] L2 eta :=
  Wp (sysCh sys j) L (Hch sys L Hunit hL hPeriodic j)

lemma Wch_apply (j : Ch eta) (w : MolecularFourierH2 eta) (q : Cf eta) :
    Wch sys L Hunit hL hPeriodic j w q = ∑' p, Sm eta L w p * potKernel (sysCh sys j) L q p := by
  have h := potential_apply (sysCh sys j) L (Hch sys L Hunit hL hPeriodic j)
    (Hch_kernel sys L Hunit hL hPeriodic j) hL w q
  refine h.trans (tsum_congr fun p => ?_)
  rw [molecularH2StateMap_apply]
  rfl

variable (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel in
/-- **`W = Σ_j W_j`**. -/
theorem W_eq_sum_Wch (w : MolecularFourierH2 eta) :
    Wp sys L H w = ∑ j : Ch eta, Wch sys L Hunit hL hPeriodic j w := by
  ext q
  rw [lp.coeFn_sum, Finset.sum_apply]
  have h := potential_apply sys L H hKernel hL w q
  change Wp sys L H w q = _ at h
  rw [h]
  simp only [Wch_apply]
  have hs : ∀ j ∈ (Finset.univ : Finset (Ch eta)),
      Summable fun p => Sm eta L w p * potKernel (sysCh sys j) L q p := fun j _ =>
    (summable_coeff_potKernel (sysCh sys j) L hL w q).congr fun p => by
      rw [molecularH2StateMap_apply]; rfl
  rw [← Summable.tsum_finsetSum hs]
  refine tsum_congr fun p => ?_
  rw [potKernel_eq_sum sys L q p, Finset.mul_sum, molecularH2StateMap_apply]
  rfl

/-- **Hardy for a channel potential** (the release's relative bound for the channel system). -/
theorem norm_Wch_sq_le (j : Ch eta) {α : ℝ} (hα : 0 < α) (w : MolecularFourierH2 eta) :
    ‖Wch sys L Hunit hL hPeriodic j w‖ ^ 2 ≤
      finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit ^ 2 *
        (α * ‖coulombFourierKineticH2 sys (gF L) w‖ ^ 2 + (1 + 1 / α) * ‖Sm eta L w‖ ^ 2) :=
  potential_sq_le (sysCh sys j) L (Hch sys L Hunit hL hPeriodic j)
    (Hch_kernel sys L Hunit hL hPeriodic j) Hunit hL hPeriodic hα w

omit [Fintype ν] in
lemma stateMap_shMask (a : Fin eta) (sh : Lattice3 → Prop) (w : MolecularFourierH2 eta) :
    Sm eta L (shMask a sh w) = shMask a sh (Sm eta L w) := by
  ext p
  rw [Sm, molecularH2StateMap_apply, shMask_apply, molecularH2StateMap_apply]
  unfold molecularH2Coeff
  rw [shMask_apply, mul_div_assoc]

omit [Fintype ν] in
lemma kinetic_shMask (a : Fin eta) (sh : Lattice3 → Prop) (w : MolecularFourierH2 eta) :
    coulombFourierKineticH2 sys (gF L) (shMask a sh w) =
      shMask a sh (coulombFourierKineticH2 sys (gF L) w) := by
  ext p
  rw [kinetic_apply', shMask_apply, kinetic_apply']
  change ((Ek sys L p : ℝ) : ℂ) * Sm eta L (shMask a sh w) p = _
  rw [stateMap_shMask, shMask_apply]
  ring

omit [Fintype ν] in
lemma onCh_apply_not_moved {j : Ch eta} {q p : Cf eta} (h : OnCh j q p) {a : Fin eta}
    (ha : a ∉ moved j) : q a = p a := by
  have e : q = p + tr j (q (lead j) - p (lead j)) := h
  have := congrFun e a
  rw [Pi.add_apply, tr_apply_not_moved j _ ha, add_zero] at this
  exact this

open Classical in
/-- **A channel that does not move `a` commutes with the shell masks of `a`.** -/
theorem Wch_shMask (j : Ch eta) {a : Fin eta} (ha : a ∉ moved j) (sh : Lattice3 → Prop)
    (w : MolecularFourierH2 eta) :
    Wch sys L Hunit hL hPeriodic j (shMask a sh w) = shMask a sh (Wch sys L Hunit hL hPeriodic j w) := by
  ext q
  rw [Wch_apply, shMask_apply, Wch_apply, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [stateMap_shMask, shMask_apply]
  by_cases hK : potKernel (sysCh sys j) L q p = 0
  · rw [hK]; ring
  · have hon := potKernel_sysCh_onCh sys hL hK
    rw [onCh_apply_not_moved hon ha]
    ring

omit [Fintype ν] in
lemma norm_shMask_kin_le (a : Fin eta) (sh : Lattice3 → Prop) (w : MolecularFourierH2 eta) :
    ‖shMask a sh (coulombFourierKineticH2 sys (gF L) w)‖ ≤
      ‖shMask a sh (Sm eta L w + coulombFourierKineticH2 sys (gF L) w)‖ := by
  have := l2_norm_le_of_le (shMask a sh (coulombFourierKineticH2 sys (gF L) w))
    (shMask a sh (Sm eta L w + coulombFourierKineticH2 sys (gF L) w)) zero_le_one fun q => by
    rw [shMask_apply, shMask_apply, shMask_add_kin_apply, kinetic_apply', one_mul]
    have hE0 : 0 ≤ Ek sys L q := by
      rw [Ek, E]
      exact Finset.sum_nonneg fun c _ => by
        have := sys.mass_pos c; have := nsq_nonneg (q c); positivity
    split_ifs
    · rw [one_mul, one_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hE0, Real.norm_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    · simp
  rwa [one_mul] at this

/-- **K2, spectators** (the paragraph after `lem:thinschur`): a channel `j` that does not move `a`
satisfies `‖1_S W_j u‖ ≤ √3 C_j B λ^{-2} ρ^{1/2}` when `‖1_S û‖ ≤ B λ^{-3} ρ^{1/2}` and
`‖1_S ℰ û‖ ≤ B λ^{-1} ρ^{1/2}` (`C_j` the mass-weighted Hardy constant of the channel system). -/
theorem band_spectator (j : Ch eta) {a : Fin eta} (ha : a ∉ moved j) (sh : Lattice3 → Prop)
    {lam ρ B : ℝ} (hlam : 1 ≤ lam) (hB : 0 ≤ B) (w : MolecularFourierH2 eta)
    (h1 : ‖shMask a sh (Sm eta L w)‖ ≤ B * lam ^ (-(3 : ℝ)) * Real.sqrt ρ)
    (h2 : ‖shMask a sh (Sm eta L w + coulombFourierKineticH2 sys (gF L) w)‖ ≤
      B * lam⁻¹ * Real.sqrt ρ) :
    ‖shMask a sh (Wch sys L Hunit hL hPeriodic j w)‖ ≤
      Real.sqrt 3 * finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit * B * (1 / lam ^ 2) *
        Real.sqrt ρ := by
  have hlam0 : 0 < lam := by linarith
  set C := finiteCoulombPhysicalMassConstant (sysCh sys j) L Hunit
  have hC : 0 ≤ C := finiteCoulombPhysicalMassConstant_nonneg _ _ _
  rw [← Wch_shMask sys L Hunit hL hPeriodic j ha sh w]
  have hα : (0 : ℝ) < 1 / lam ^ 2 := by positivity
  have hW := norm_Wch_sq_le sys L Hunit hL hPeriodic j hα (shMask a sh w)
  rw [kinetic_shMask, stateMap_shMask] at hW
  have hT := (norm_shMask_kin_le sys L a sh w).trans h2
  rw [rpow_neg_three_eq hlam0] at h1
  set s := Real.sqrt ρ
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hT2 : ‖shMask a sh (coulombFourierKineticH2 sys (gF L) w)‖ ^ 2 ≤ (B * lam⁻¹ * s) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hT 2
  have hS2 : ‖shMask a sh (Sm eta L w)‖ ^ 2 ≤ (B * (1 / lam ^ 2 * lam⁻¹) * s) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hbound : 1 / lam ^ 2 * (B * lam⁻¹ * s) ^ 2 + (1 + 1 / (1 / lam ^ 2)) *
      (B * (1 / lam ^ 2 * lam⁻¹) * s) ^ 2 ≤ 3 * (B * (1 / lam ^ 2) * s) ^ 2 := by
    have e : 1 / lam ^ 2 * (B * lam⁻¹ * s) ^ 2 + (1 + 1 / (1 / lam ^ 2)) *
        (B * (1 / lam ^ 2 * lam⁻¹) * s) ^ 2 =
        (B * (1 / lam ^ 2) * s) ^ 2 * (2 + 1 / lam ^ 2) := by
      field_simp; ring
    rw [e]
    have : 1 / lam ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have : 0 ≤ (B * (1 / lam ^ 2) * s) ^ 2 := sq_nonneg _
    nlinarith
  have hsq : ‖Wch sys L Hunit hL hPeriodic j (shMask a sh w)‖ ^ 2 ≤
      (Real.sqrt 3 * C * B * (1 / lam ^ 2) * s) ^ 2 := by
    refine hW.trans ?_
    have e : (Real.sqrt 3 * C * B * (1 / lam ^ 2) * s) ^ 2 = C ^ 2 * (3 * (B * (1 / lam ^ 2) * s) ^ 2) := by
      rw [show Real.sqrt 3 * C * B * (1 / lam ^ 2) * s = C * (Real.sqrt 3 * (B * (1 / lam ^ 2) * s)) by
        ring, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    rw [e]
    refine mul_le_mul_of_nonneg_left ((add_le_add (mul_le_mul_of_nonneg_left hT2 hα.le)
      (mul_le_mul_of_nonneg_left hS2 (by positivity))).trans hbound) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end Channel

end FSBand
