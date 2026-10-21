import PlaneWave.Source.RegisterStructure
import PlaneWave.Source.QtailRecursion
import PlaneWave.Source.ChannelKernels

/-!
# Flux/source build, block 1b: tails of quasi-eigenstates, `lem:qtail`

The first bound of eq:qtail on the release's Galerkin space.  Let `H' = H_N + ΔH` with
`‖ΔH‖ ≤ C_Δ`, `q` a quasi-eigenstate `‖(H' - E) q‖ ≤ γ ‖q‖`, `a` a register and
`h(λ) = ‖1{|k_a| > λ} q‖`.

* `regTail`: the register tail `Q⁽²⁾_{a,λ} = 1{|k_a| > λ}`; `Wlat`: the lattice weighted norm
  `(Σ_p (1 + |ν_a|²)^s |q_p|²)^{1/2}` (`ν_a` the integer momentum of register `a`);
* `isChannel_nuc`, `isChannel_pair`: the nuclear term of `a` and the pair terms containing `a` are
  Coulomb channels in the sense of `dev/PlaneWave.Source.ChannelKernels.lean` for the register-`a` momentum;
* `norm_regMul_Va_le`: the output-weighted `V_a`, by the near/far channel bound;
* `qtail_rec` (eq:qtail-rec): `h(λ) ≤ (c/λ) h(λ/2) + F(λ)`,
  `F(λ) = (c₂/λ²)(λ^{-1/2} W + (γ + C_Δ)‖q‖)`, for `λ > λ₁`;
* `qtail` (eq:qtail, first bound): `h(λ) ≤ 4F(λ) + 2c²‖q‖/λ²` for `λ > 2λ₁`, by
  `FSQtail.qtail_recursion`.

The denominator is applied through the weighted resolvent bound `norm_le_of_slice_coercive`
(`dev/PlaneWave.Source.RegisterStructure.lean`) rather than shell by shell: on the slice `p_a = μ` the operator
`H_ā - E` is at least `w(μ) = |k_μ|²/(8 m_a) - C_sh - E`, and the output of `V_a` is weighted by
`1/w`.  The near hops then give the recursion term and the far hops the `λ^{-5/2}` term directly.
Constants: `c = 624 m_a Q_a γ_c / g`, `c₂ = 16 m_a (1 + Q_a γ_c √(2080 Z_s g))`, where
`Q_a = |q_a| Z_tot + Σ_{pairs ∋ a} |q_i q_j|`, `γ_c = 1/(πL)`, `g = 2π/L`; threshold
`λ₁ = max(8c, g, √(16 m_a (C_sh + E)))`.
-/

set_option autoImplicit false

open scoped InnerProductSpace
open PlaneWaveCertificate

namespace FSGalerkin

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type*}

/-! ## Register tails and lattice weights -/

section Tails

variable {n : ℕ}

/-- The integer momentum of register `a`. -/
def piA (a : Fin eta) (q : Cfg eta n) : L3 := finitePlaneWaveLatticeIndex n (q a)

/-- The reciprocal lattice spacing `g = 2π/L`. -/
noncomputable def gL (L : ℝ) : ℝ := 2 * Real.pi / L

lemma gL_pos {L : ℝ} (hL : 0 < L) : 0 < gL L := by
  unfold gL; positivity

lemma kabs_sq_eq (L : ℝ) (μ : FinitePlaneWaveMode n) :
    finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 =
      gL L ^ 2 * lsq (finitePlaneWaveLatticeIndex n μ) :=
  finitePlaneWaveKabs_sq_eq_g_sq_mul_latticeNormSq _ n μ

lemma kabs_nonneg {L : ℝ} (hL : 0 < L) (μ : FinitePlaneWaveMode n) :
    0 ≤ finitePlaneWaveKabs (2 * Real.pi / L) n μ :=
  finitePlaneWaveKabs_nonneg _ n (gL_pos hL).le μ

/-- The register tail `Q⁽²⁾_{a,λ} = 1{|k_a| > λ}`. -/
noncomputable def regTail (L : ℝ) (a : Fin eta) (l : ℝ) : En eta n →ₗ[ℂ] En eta n :=
  regMul a (fun μ => if l < finitePlaneWaveKabs (2 * Real.pi / L) n μ then 1 else 0)

lemma regTail_apply (L : ℝ) (a : Fin eta) (l : ℝ) (u : En eta n) (p : Cfg eta n) :
    (regTail L a l u).ofLp p =
      if l < finitePlaneWaveKabs (2 * Real.pi / L) n (p a) then u.ofLp p else 0 := by
  unfold regTail
  rw [regMul_apply]
  split_ifs <;> simp

lemma norm_sq_regTail (L : ℝ) (a : Fin eta) (l : ℝ) (u : En eta n) :
    ‖regTail L a l u‖ ^ 2 =
      ∑ p, if l < finitePlaneWaveKabs (2 * Real.pi / L) n (p a) then ‖u.ofLp p‖ ^ 2 else 0 := by
  rw [norm_sq_En]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [regTail_apply]
  split_ifs <;> simp

/-- A register multiplier with symbol bounded by `M` has norm at most `M`. -/
lemma norm_regMul_le (a : Fin eta) (φ : FinitePlaneWaveMode n → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hφ : ∀ μ, ‖φ μ‖ ≤ M) (u : En eta n) : ‖regMul a φ u‖ ≤ M * ‖u‖ := by
  have h2 : ‖regMul a φ u‖ ^ 2 ≤ (M * ‖u‖) ^ 2 := by
    rw [norm_sq_En, mul_pow, norm_sq_En, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [regMul_apply, norm_mul, mul_pow]
    have h := hφ (p a)
    have : ‖φ (p a)‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

lemma norm_regTail_le (L : ℝ) (a : Fin eta) (l : ℝ) (u : En eta n) : ‖regTail L a l u‖ ≤ ‖u‖ := by
  have h := norm_regMul_le a
    (fun μ => if l < finitePlaneWaveKabs (2 * Real.pi / L) n μ then (1 : ℂ) else 0)
    zero_le_one (fun μ => by split_ifs <;> simp) u
  rw [one_mul] at h
  exact h

lemma regMul_regMul (a : Fin eta) (φ ψ : FinitePlaneWaveMode n → ℂ) (u : En eta n) :
    regMul a φ (regMul a ψ u) = regMul a (fun μ => φ μ * ψ μ) u := by
  ext p
  simp only [regMul_apply]
  ring

/-- The lattice weighted norm `(Σ_p (1 + |ν_a|²)^s |u_p|²)^{1/2}`. -/
noncomputable def Wlat (a : Fin eta) (s : ℝ) (u : En eta n) : ℝ :=
  Real.sqrt (∑ p, (1 + lsq (piA a p)) ^ s * ‖u.ofLp p‖ ^ 2)

lemma Wlat_nonneg (a : Fin eta) (s : ℝ) (u : En eta n) : 0 ≤ Wlat a s u := Real.sqrt_nonneg _

end Tails

/-! ## The channels of `V_a` -/

section Channels

variable {n : ℕ} (a : Fin eta)

lemma transfer_eq (v u : FinitePlaneWaveMode n) :
    finitePlaneWaveTransfer n v u = finitePlaneWaveLatticeIndex n v - finitePlaneWaveLatticeIndex n u := by
  funext i
  simp [finitePlaneWaveTransfer, latticeSub]

/-- `√(C²/|Δν|⁴) = C/|Δν|²`. -/
lemma sqrt_weight_eq {C : ℝ} (hC : 0 ≤ C) (v u : FinitePlaneWaveMode n) :
    Real.sqrt (finiteCoulombDifferenceSquareWeight (C ^ 2) n v u) =
      C / lsq (finitePlaneWaveLatticeIndex n v - finitePlaneWaveLatticeIndex n u) := by
  unfold finiteCoulombDifferenceSquareWeight latticeCoulombSquareWeight
  rw [transfer_eq, ← div_pow]
  exact Real.sqrt_sq (div_nonneg hC (lsq_nonneg _))

lemma norm_finiteCoulombKernel_eq {C : ℝ} (hC : 0 ≤ C) (v u : FinitePlaneWaveMode n) :
    ‖finiteCoulombKernel (C ^ 2) n v u‖ =
      C / lsq (finitePlaneWaveLatticeIndex n v - finitePlaneWaveLatticeIndex n u) := by
  unfold finiteCoulombKernel
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), sqrt_weight_eq hC]

/-- **The nuclear channel** of register `a` and nucleus `ell`. -/
theorem isChannel_nuc [Fintype ν] (data : FiniteBONuclearData ν) {γ : ℝ} (hγ : 0 ≤ γ) (ell : ν) :
    IsChannel (piA (n := n) a)
      (referenceConfigurationKernel a (finiteElectronNuclearKernel data γ n ell))
      (data.charge ell * γ) where
  bound q p := by
    classical
    by_cases ho : outerConfigOf a q = outerConfigOf a p
    · rw [referenceConfigurationKernel_of_outer_eq a _ q p ho]
      unfold finiteElectronNuclearKernel
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (data.charge_nonneg ell)]
      have h := finiteTranslatedCoulombKernel_norm_le (γ ^ 2) n (data.position ell) (q a) (p a)
      rw [sqrt_weight_eq hγ] at h
      calc data.charge ell * ‖finiteTranslatedCoulombKernel (γ ^ 2) n (data.position ell) (q a) (p a)‖
          ≤ data.charge ell * (γ / lsq (finitePlaneWaveLatticeIndex n (q a) -
              finitePlaneWaveLatticeIndex n (p a))) :=
            mul_le_mul_of_nonneg_left h (data.charge_nonneg ell)
        _ = _ := by unfold piA; ring
    · rw [referenceConfigurationKernel_of_outer_ne a _ q p ho, norm_zero]
      exact div_nonneg (mul_nonneg (data.charge_nonneg ell) hγ) (lsq_nonneg _)
  row q p p' hp hp' hπ := by
    classical
    have h1 : outerConfigOf a q = outerConfigOf a p := by
      by_contra h; exact hp (referenceConfigurationKernel_of_outer_ne a _ q p h)
    have h2 : outerConfigOf a q = outerConfigOf a p' := by
      by_contra h; exact hp' (referenceConfigurationKernel_of_outer_ne a _ q p' h)
    have ha : p a = p' a := finitePlaneWaveLatticeIndex_injective n hπ
    funext b
    by_cases hb : b = a
    · subst hb; exact ha
    · exact congrFun (h1.symm.trans h2) ⟨b, hb⟩
  col p q q' hq hq' hπ := by
    classical
    have h1 : outerConfigOf a q = outerConfigOf a p := by
      by_contra h; exact hq (referenceConfigurationKernel_of_outer_ne a _ q p h)
    have h2 : outerConfigOf a q' = outerConfigOf a p := by
      by_contra h; exact hq' (referenceConfigurationKernel_of_outer_ne a _ q' p h)
    have ha : q a = q' a := finitePlaneWaveLatticeIndex_injective n hπ
    funext b
    by_cases hb : b = a
    · subst hb; exact ha
    · exact congrFun (h1.trans h2.symm) ⟨b, hb⟩

/-- **A pair channel** `(a, j)`, with `a` the first member. -/
theorem isChannel_pair {j : Fin eta} (haj : a ≠ j) {γ : ℝ} (hγ : 0 ≤ γ) :
    IsChannel (piA (n := n) a) (finiteElectronPairConfigurationKernel a j (γ ^ 2) n) γ where
  bound q p := by
    classical
    by_cases hl : finiteElectronPairSliceLabel a j n q = finiteElectronPairSliceLabel a j n p
    · rw [finiteElectronPairConfigurationKernel_of_same_fiber a j _ n q p hl,
        norm_finiteCoulombKernel_eq hγ]
      rfl
    · rw [finiteElectronPairConfigurationKernel_of_other_fiber a j _ n q p hl, norm_zero]
      exact div_nonneg hγ (lsq_nonneg _)
  row q p p' hp hp' hπ := by
    classical
    have h1 : finiteElectronPairSliceLabel a j n q = finiteElectronPairSliceLabel a j n p := by
      by_contra h; exact hp (finiteElectronPairConfigurationKernel_of_other_fiber a j _ n q p h)
    have h2 : finiteElectronPairSliceLabel a j n q = finiteElectronPairSliceLabel a j n p' := by
      by_contra h; exact hp' (finiteElectronPairConfigurationKernel_of_other_fiber a j _ n q p' h)
    have ha : p a = p' a := finitePlaneWaveLatticeIndex_injective n hπ
    exact finiteElectronPairSliceLabel_with_first_injective a j haj n
      (Prod.ext (h1.symm.trans h2) ha)
  col p q q' hq hq' hπ := by
    classical
    have h1 : finiteElectronPairSliceLabel a j n q = finiteElectronPairSliceLabel a j n p := by
      by_contra h; exact hq (finiteElectronPairConfigurationKernel_of_other_fiber a j _ n q p h)
    have h2 : finiteElectronPairSliceLabel a j n q' = finiteElectronPairSliceLabel a j n p := by
      by_contra h; exact hq' (finiteElectronPairConfigurationKernel_of_other_fiber a j _ n q' p h)
    have ha : q a = q' a := finitePlaneWaveLatticeIndex_injective n hπ
    exact finiteElectronPairSliceLabel_with_first_injective a j haj n
      (Prod.ext (h1.trans h2.symm) ha)

/-- The other member of a pair containing `a`. -/
def other (pr : FiniteElectronPair eta) : Fin eta := if pr.1.1 = a then pr.1.2 else pr.1.1

lemma ne_other (pr : FiniteElectronPair eta) (hpr : pr ∈ pairsWith a) : a ≠ other a pr := by
  unfold other
  rw [pairsWith, Finset.mem_filter] at hpr
  split_ifs with h
  · rw [← h]; exact ne_of_lt pr.2
  · rcases hpr.2 with h' | h'
    · exact absurd h' h
    · rw [← h']; exact ne_of_gt pr.2

lemma pairKernel_eq_other (pr : FiniteElectronPair eta) (hpr : pr ∈ pairsWith a) (C : ℝ) :
    finiteElectronPairConfigurationKernel pr.1.1 pr.1.2 C n =
      finiteElectronPairConfigurationKernel a (other a pr) C n := by
  unfold other
  rw [pairsWith, Finset.mem_filter] at hpr
  split_ifs with h
  · rw [h]
  · rcases hpr.2 with h' | h'
    · exact absurd h' h
    · funext q p
      rw [finiteElectronPairConfigurationKernel_swap_particles, h']

end Channels

/-! ## The output-weighted `V_a` -/

section WeightedVa

variable [Fintype ν] (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (a : Fin eta)

lemma regMul_kernel (θ : FinitePlaneWaveMode n → ℝ) (T : En eta n →ₗ[ℂ] En eta n)
    (κ : Cfg eta n → Cfg eta n → ℂ) (hT : ∀ u q, (T u).ofLp q = ∑ p, u.ofLp p * κ q p)
    (u : En eta n) :
    regMul a (fun μ => (θ μ : ℂ)) (T u) = wop κ (fun q => θ (q a)) u := by
  ext q
  rw [regMul_apply, hT]
  rfl

/-- **The output-weighted `V_a`.**  For an output weight `θ` of register `a` with
`|θ(μ)| ≤ c_θ/|ν_μ|²`, vanishing for `|ν_μ| ≤ R₀`, the weighted `V_a u` is at most
`Q_a γ_c [39 c_θ/R₀ · ‖1{|ν_a| > R₀/2} u‖ + √(2080 Z_s) c_θ/R₀^{5/2} · W_s(u)]`. -/
theorem norm_regMul_Va_le (θ : FinitePlaneWaveMode n → ℝ) {cθ R₀ s : ℝ} (hcθ : 0 ≤ cθ)
    (hR₀ : 1 ≤ R₀) (hs : 3 / 2 < s)
    (hθ : ∀ μ, |θ μ| ≤ cθ / lsq (finitePlaneWaveLatticeIndex n μ))
    (hθ0 : ∀ μ, lsq (finitePlaneWaveLatticeIndex n μ) ≤ R₀ ^ 2 → θ μ = 0) (hL : 0 < L)
    (u : En eta n) :
    ‖regMul a (fun μ => (θ μ : ℂ)) (Va sys L n a u)‖ ≤
      chargeA sys a * coulombCellAmplitude L *
        (39 * cθ / R₀ * Real.sqrt (∑ p, if R₀ ^ 2 < 4 * lsq (piA a p) then ‖u.ofLp p‖ ^ 2 else 0) +
          Real.sqrt (2080 * Zs s) * cθ / R₀ ^ (5 / 2 : ℝ) * Wlat a s u) := by
  classical
  set γc := coulombCellAmplitude L with hγc
  have hγ : 0 ≤ γc := (coulombCellAmplitude_pos hL).le
  set B1 := 39 * cθ / R₀ * Real.sqrt (∑ p, if R₀ ^ 2 < 4 * lsq (piA a p) then ‖u.ofLp p‖ ^ 2 else 0) +
    Real.sqrt (2080 * Zs s) * cθ / R₀ ^ (5 / 2 : ℝ) * Wlat a s u with hB1
  -- every channel contributes `c_w B1`
  have hch : ∀ (κ : Cfg eta n → Cfg eta n → ℂ) (cw : ℝ), IsChannel (piA (n := n) a) κ cw →
      0 ≤ cw → ‖wop κ (fun q => θ (q a)) u‖ ≤ cw * B1 := by
    intro κ cw hκ hcw
    have h := norm_wop_le (piA (n := n) a) κ hκ hcw (fun q => θ (q a)) hcθ hR₀ hs
      (fun q => hθ (q a)) (fun q hq => hθ0 (q a) hq) u
    refine h.trans (le_of_eq ?_)
    rw [hB1, Wlat]
    ring
  -- split `V_a`
  have hVa : regMul a (fun μ => (θ μ : ℂ)) (Va sys L n a u) =
      ((-sys.charge a : ℝ) : ℂ) • ∑ ell : ν,
        wop (referenceConfigurationKernel a (finiteElectronNuclearKernel sys.nuclei γc n ell))
          (fun q => θ (q a)) u +
      ∑ pr ∈ pairsWith a, ((sys.charge pr.1.1 * sys.charge pr.1.2 : ℝ) : ℂ) •
        wop (finiteElectronPairConfigurationKernel a (other a pr) (γc ^ 2) n)
          (fun q => θ (q a)) u := by
    unfold Va Vnuc Vpair
    rw [LinearMap.add_apply, map_add, LinearMap.smul_apply, map_smul, LinearMap.sum_apply, map_sum,
      LinearMap.sum_apply, map_sum]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun ell _ => ?_
      exact regMul_kernel n a θ _ _ (fun u q => referenceKernelConvolutionOperator_apply a _ u q) u
    · refine Finset.sum_congr rfl fun pr hpr => ?_
      rw [LinearMap.smul_apply, map_smul]
      congr 1
      rw [← pairKernel_eq_other a pr hpr]
      exact regMul_kernel n a θ _ _ (fun u q => finiteElectronPairCoulombOperator_apply _ _ _ n u q) u
  rw [hVa]
  -- bound the pieces
  have hNuc : ‖((-sys.charge a : ℝ) : ℂ) • ∑ ell : ν,
      wop (referenceConfigurationKernel a (finiteElectronNuclearKernel sys.nuclei γc n ell))
        (fun q => θ (q a)) u‖ ≤ |sys.charge a| * (sys.nuclei.totalCharge * γc * B1) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc _ ≤ ∑ ell : ν, ‖wop (referenceConfigurationKernel a
            (finiteElectronNuclearKernel sys.nuclei γc n ell)) (fun q => θ (q a)) u‖ :=
          norm_sum_le _ _
      _ ≤ ∑ ell : ν, sys.nuclei.charge ell * γc * B1 := Finset.sum_le_sum fun ell _ =>
          hch _ _ (isChannel_nuc a sys.nuclei hγ ell) (mul_nonneg (sys.nuclei.charge_nonneg ell) hγ)
      _ = sys.nuclei.totalCharge * γc * B1 := by
          unfold FiniteBONuclearData.totalCharge
          rw [Finset.sum_mul, Finset.sum_mul]
  have hPair : ‖∑ pr ∈ pairsWith a, ((sys.charge pr.1.1 * sys.charge pr.1.2 : ℝ) : ℂ) •
      wop (finiteElectronPairConfigurationKernel a (other a pr) (γc ^ 2) n)
        (fun q => θ (q a)) u‖ ≤
      (∑ pr ∈ pairsWith a, |sys.charge pr.1.1 * sys.charge pr.1.2|) * (γc * B1) := by
    calc _ ≤ ∑ pr ∈ pairsWith a, ‖((sys.charge pr.1.1 * sys.charge pr.1.2 : ℝ) : ℂ) •
            wop (finiteElectronPairConfigurationKernel a (other a pr) (γc ^ 2) n)
              (fun q => θ (q a)) u‖ := norm_sum_le _ _
      _ ≤ ∑ pr ∈ pairsWith a, |sys.charge pr.1.1 * sys.charge pr.1.2| * (γc * B1) := by
          refine Finset.sum_le_sum fun pr hpr => ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left
            (hch _ _ (isChannel_pair a (ne_other a pr hpr) hγ) hγ) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  have hB10 : 0 ≤ B1 := by
    rw [hB1]
    have h1 : 0 ≤ 39 * cθ / R₀ := by positivity
    have h2 : 0 ≤ Real.sqrt (2080 * Zs s) * cθ / R₀ ^ (5 / 2 : ℝ) := by
      have : 0 < R₀ ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    have h3 := Wlat_nonneg a s u
    have h4 := Real.sqrt_nonneg (∑ p, if R₀ ^ 2 < 4 * lsq (piA a p) then ‖u.ofLp p‖ ^ 2 else 0)
    positivity
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ |sys.charge a| * (sys.nuclei.totalCharge * γc * B1) +
        (∑ pr ∈ pairsWith a, |sys.charge pr.1.1 * sys.charge pr.1.2|) * (γc * B1) :=
        add_le_add hNuc hPair
    _ = chargeA sys a * γc * B1 := by unfold chargeA; ring

end WeightedVa

/-! ## The recursion -/

section Recursion

variable [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) (n : ℕ) (a : Fin eta)

/-- The recursion constant `c = 624 m_a Q_a γ_c / g`. -/
noncomputable def qtailC (sys : CoulombSystem eta ν) (L : ℝ) (a : Fin eta) : ℝ :=
  624 * sys.mass a * chargeA sys a * coulombCellAmplitude L / gL L

/-- The source constant `c₂ = 16 m_a (1 + Q_a γ_c √(2080 Z_s g))`. -/
noncomputable def qtailC2 (sys : CoulombSystem eta ν) (L : ℝ) (a : Fin eta) (s : ℝ) : ℝ :=
  16 * sys.mass a * (1 + chargeA sys a * coulombCellAmplitude L * Real.sqrt (2080 * Zs s * gL L))

/-- The threshold `λ₁ = max(8c, g, √(16 m_a (C_sh + E)))`. -/
noncomputable def qtailL1 (sys : CoulombSystem eta ν) (L Hunit : ℝ) (a : Fin eta) (E : ℝ) : ℝ :=
  max (max (8 * qtailC sys L a) (gL L)) (Real.sqrt (16 * sys.mass a * (Csh sys L Hunit a + E)))

lemma qtailC_nonneg (hL : 0 < L) : 0 ≤ qtailC sys L a := by
  unfold qtailC
  have := sys.mass_pos a
  have := chargeA_nonneg sys a
  have := (coulombCellAmplitude_pos hL).le
  have := gL_pos hL
  positivity

lemma qtailC2_nonneg (hL : 0 < L) (s : ℝ) : 0 ≤ qtailC2 sys L a s := by
  unfold qtailC2
  have := sys.mass_pos a
  have := chargeA_nonneg sys a
  have := (coulombCellAmplitude_pos hL).le
  have := Real.sqrt_nonneg (2080 * Zs s * gL L)
  positivity

/-- The slice weight `w(μ) = |k_μ|²/(8 m_a) - C_sh - E`. -/
noncomputable def sliceW (sys : CoulombSystem eta ν) (L Hunit : ℝ) (a : Fin eta) (E : ℝ)
    (μ : FinitePlaneWaveMode n) : ℝ :=
  finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 / (8 * sys.mass a) - Csh sys L Hunit a - E

/-- The output weight `θ(μ) = 1{λ < |k_μ|} / w(μ)`. -/
noncomputable def outW (sys : CoulombSystem eta ν) (L Hunit : ℝ) (a : Fin eta) (E l : ℝ)
    (μ : FinitePlaneWaveMode n) : ℝ :=
  if l < finitePlaneWaveKabs (2 * Real.pi / L) n μ then (sliceW n sys L Hunit a E μ)⁻¹ else 0

variable {n}

/-- Above the threshold the slice weight is at least `|k|²/(16 m_a)`. -/
lemma sliceW_gt (_hL : 0 < L) {E l : ℝ} (hl0 : 0 ≤ l)
    (hl2 : 16 * sys.mass a * (Csh sys L Hunit a + E) < l ^ 2) (μ : FinitePlaneWaveMode n)
    (hμ : l < finitePlaneWaveKabs (2 * Real.pi / L) n μ) :
    finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 / (16 * sys.mass a) <
      sliceW n sys L Hunit a E μ := by
  have hm := sys.mass_pos a
  have hk2 : l ^ 2 < finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 :=
    pow_lt_pow_left₀ hμ hl0 two_ne_zero
  unfold sliceW
  have : finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 / (8 * sys.mass a) - Csh sys L Hunit a - E -
      finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 / (16 * sys.mass a) =
      (finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 - 16 * sys.mass a * (Csh sys L Hunit a + E)) /
        (16 * sys.mass a) := by
    field_simp
    ring
  have h2 : 0 < (finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 -
      16 * sys.mass a * (Csh sys L Hunit a + E)) / (16 * sys.mass a) :=
    div_pos (by linarith) (by positivity)
  linarith

/-- `|θ(μ)| ≤ 16 m_a/λ²`. -/
lemma outW_le (hL : 0 < L) {E l : ℝ} (hl : 0 < l)
    (hl2 : 16 * sys.mass a * (Csh sys L Hunit a + E) < l ^ 2) (μ : FinitePlaneWaveMode n) :
    |outW n sys L Hunit a E l μ| ≤ 16 * sys.mass a / l ^ 2 := by
  have hm := sys.mass_pos a
  unfold outW
  split_ifs with h
  · have h1 := sliceW_gt sys Hunit a hL hl.le hl2 μ h
    have hk2 : l ^ 2 < finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 :=
      pow_lt_pow_left₀ h hl.le two_ne_zero
    have h2 : l ^ 2 / (16 * sys.mass a) < sliceW n sys L Hunit a E μ :=
      lt_trans (div_lt_div_of_pos_right hk2 (by positivity)) h1
    have hwpos : 0 < sliceW n sys L Hunit a E μ := lt_trans (by positivity) h2
    rw [abs_of_pos (inv_pos.mpr hwpos), inv_le_comm₀ hwpos (by positivity), inv_div]
    exact h2.le
  · rw [abs_zero]; positivity

/-- `|θ(μ)| ≤ (16 m_a/g²)/|ν_μ|²`. -/
lemma outW_le_lat (hL : 0 < L) {E l : ℝ} (hl : 0 < l)
    (hl2 : 16 * sys.mass a * (Csh sys L Hunit a + E) < l ^ 2) (μ : FinitePlaneWaveMode n) :
    |outW n sys L Hunit a E l μ| ≤
      16 * sys.mass a / gL L ^ 2 / lsq (finitePlaneWaveLatticeIndex n μ) := by
  have hm := sys.mass_pos a
  have hg0 := gL_pos hL
  have hk := kabs_sq_eq L μ
  unfold outW
  split_ifs with h
  · have h1 := sliceW_gt sys Hunit a hL hl.le hl2 μ h
    have hk0 : 0 < finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 :=
      pow_pos (lt_trans hl h) 2
    have hwpos : 0 < sliceW n sys L Hunit a E μ := lt_trans (by positivity) h1
    have hlsq : 0 < lsq (finitePlaneWaveLatticeIndex n μ) := by
      rw [hk] at hk0; exact pos_of_mul_pos_right hk0 (sq_nonneg _)
    rw [abs_of_pos (inv_pos.mpr hwpos), inv_le_comm₀ hwpos (by positivity)]
    have : (16 * sys.mass a / gL L ^ 2 / lsq (finitePlaneWaveLatticeIndex n μ))⁻¹ =
        finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 / (16 * sys.mass a) := by
      rw [hk]; field_simp
    rw [this]
    exact h1.le
  · rw [abs_zero]
    have := lsq_nonneg (finitePlaneWaveLatticeIndex n μ)
    positivity

/-- `θ(μ) = 0` for `|ν_μ| ≤ λ/g`. -/
lemma outW_eq_zero (hL : 0 < L) {E l : ℝ} (hl : 0 < l) (μ : FinitePlaneWaveMode n)
    (hμ : lsq (finitePlaneWaveLatticeIndex n μ) ≤ (l / gL L) ^ 2) :
    outW n sys L Hunit a E l μ = 0 := by
  have hg0 := gL_pos hL
  unfold outW
  rw [if_neg]
  intro h
  have hk := kabs_sq_eq L μ
  have hk2 : finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 ≤ l ^ 2 := by
    rw [hk]
    calc gL L ^ 2 * lsq (finitePlaneWaveLatticeIndex n μ) ≤ gL L ^ 2 * (l / gL L) ^ 2 :=
          mul_le_mul_of_nonneg_left hμ (sq_nonneg _)
      _ = l ^ 2 := by field_simp
  have h2 : l ^ 2 < finitePlaneWaveKabs (2 * Real.pi / L) n μ ^ 2 :=
    pow_lt_pow_left₀ h hl.le two_ne_zero
  linarith

/-- The near region of `dev/PlaneWave.Source.ChannelKernels.lean` is the tail at `λ/2`. -/
lemma near_iff (hL : 0 < L) {l : ℝ} (hl : 0 < l) (μ : FinitePlaneWaveMode n) :
    (l / gL L) ^ 2 < 4 * lsq (finitePlaneWaveLatticeIndex n μ) ↔
      l / 2 < finitePlaneWaveKabs (2 * Real.pi / L) n μ := by
  have hg0 := gL_pos hL
  have hk := kabs_sq_eq L μ
  have hk0 := kabs_nonneg hL μ
  have heq : 4 * lsq (finitePlaneWaveLatticeIndex n μ) =
      (2 * finitePlaneWaveKabs (2 * Real.pi / L) n μ / gL L) ^ 2 := by
    rw [div_pow, mul_pow, hk]; field_simp; ring
  rw [heq, pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero,
    div_lt_div_iff_of_pos_right hg0]
  constructor <;> intro h <;> linarith

lemma near_sum_eq (hL : 0 < L) {l : ℝ} (hl : 0 < l) (q : En eta n) :
    (∑ p, if (l / gL L) ^ 2 < 4 * lsq (piA a p) then ‖q.ofLp p‖ ^ 2 else 0) =
      ‖regTail L a (l / 2) q‖ ^ 2 := by
  rw [norm_sq_regTail]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold piA
  by_cases h : (l / gL L) ^ 2 < 4 * lsq (finitePlaneWaveLatticeIndex n (p a))
  · rw [if_pos h, if_pos ((near_iff hL hl (p a)).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((near_iff hL hl (p a)).mpr h'))]

/-- **The denominator**: `h(λ) ≤ ‖θ (H_ā - E) q‖`. -/
theorem tail_le_resolvent (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {E l : ℝ} (hl : 0 < l) (hl2 : 16 * sys.mass a * (Csh sys L Hunit a + E) < l ^ 2)
    (q : En eta n) :
    ‖regTail L a l q‖ ≤
      ‖regMul a (fun μ => (outW n sys L Hunit a E l μ : ℂ))
        (Hbar sys L n a q - (E : ℂ) • q)‖ := by
  classical
  set D : En eta n →ₗ[ℂ] En eta n := Hbar sys L n a - (E : ℂ) • LinearMap.id with hD
  have hDloc : RegLocal a D := (Hbar_regLocal sys L n a).sub (regLocal_id.smul _)
  have hDco : ∀ (μ : FinitePlaneWaveMode n) (x : En eta n), (∀ p, x.ofLp p ≠ 0 → p a = μ) →
      sliceW n sys L Hunit a E μ * ‖x‖ ^ 2 ≤ (⟪x, D x⟫_ℂ).re := by
    intro μ x hx
    have hc := Hbar_coercive sys Hunit n a hL hPeriodic
      (l := finitePlaneWaveKabs (2 * Real.pi / L) n μ) x (fun p hp => by rw [hx p hp])
    have hxx : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
      have := inner_self_eq_norm_sq (𝕜 := ℂ) x
      simpa using this
    have hre : (⟪x, D x⟫_ℂ).re = (⟪x, Hbar sys L n a x⟫_ℂ).re - E * ‖x‖ ^ 2 := by
      rw [hD, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right,
        inner_smul_right, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        hxx]
      ring
    rw [hre]
    unfold sliceW
    nlinarith [hc]
  have hsupp : ∀ p, (regTail L a l q).ofLp p ≠ 0 → 0 < sliceW n sys L Hunit a E (p a) := by
    intro p hp
    rw [regTail_apply] at hp
    split_ifs at hp with h
    · have := sliceW_gt sys Hunit a hL hl.le hl2 (p a) h
      have hm := sys.mass_pos a
      have : 0 ≤ finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2 / (16 * sys.mass a) := by
        positivity
      linarith
    · exact absurd rfl hp
  have hres := norm_le_of_slice_coercive a D hDloc _ hDco _ hsupp
  refine hres.trans (le_of_eq ?_)
  rw [regTail, hDloc, regMul_regMul]
  have hfun : (fun μ => (((sliceW n sys L Hunit a E μ)⁻¹ : ℝ) : ℂ) *
      (if l < finitePlaneWaveKabs (2 * Real.pi / L) n μ then (1 : ℂ) else 0)) =
      (fun μ => (outW n sys L Hunit a E l μ : ℂ)) := by
    funext μ
    unfold outW
    split_ifs <;> simp
  rw [hfun, hD, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]

/-- The near coefficient: `Q_a γ_c · 39 (16 m_a/g²)/(λ/g) = c/λ`. -/
lemma near_coeff (hL : 0 < L) {l : ℝ} (hl : 0 < l) :
    chargeA sys a * coulombCellAmplitude L * (39 * (16 * sys.mass a / gL L ^ 2) / (l / gL L)) =
      qtailC sys L a / l := by
  have hg0 := gL_pos hL
  unfold qtailC
  field_simp
  ring

omit [Fintype ν] in
/-- The far coefficient: `√(2080 Z) (16 m_a/g²)/(λ/g)^{5/2} = 16 m_a √(2080 Z g) λ^{-1/2}/λ²`. -/
lemma far_coeff (hL : 0 < L) {l s : ℝ} (hl : 0 < l) (hs : 3 / 2 < s) :
    Real.sqrt (2080 * Zs s) * (16 * sys.mass a / gL L ^ 2) / (l / gL L) ^ (5 / 2 : ℝ) =
      16 * sys.mass a * Real.sqrt (2080 * Zs s * gL L) * l ^ (-(1 / 2 : ℝ)) / l ^ 2 := by
  have hg0 := gL_pos hL
  have hZ : 0 ≤ 2080 * Zs s := by
    unfold Zs
    have : 0 < 2 * s - 3 := by linarith
    positivity
  have hl12 : 0 < l ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hl _
  have hg12 : 0 < gL L ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hg0 _
  have h52 : (5 / 2 : ℝ) = 2 + 1 / 2 := by norm_num
  have hR52 : (l / gL L) ^ (5 / 2 : ℝ) =
      l ^ 2 * l ^ (1 / 2 : ℝ) / (gL L ^ 2 * gL L ^ (1 / 2 : ℝ)) := by
    rw [Real.div_rpow hl.le hg0.le, h52, Real.rpow_add hl, Real.rpow_add hg0, Real.rpow_two,
      Real.rpow_two]
  have hSeq : Real.sqrt (2080 * Zs s * gL L) = Real.sqrt (2080 * Zs s) * gL L ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul hZ, Real.sqrt_eq_rpow (gL L)]
  have hPeq : l ^ (-(1 / 2 : ℝ)) = (l ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hl.le _
  rw [hR52, hSeq, hPeq]
  field_simp

/-- **eq:qtail-rec**: `h(λ) ≤ (c/λ) h(λ/2) + F(λ)` above the threshold `λ₁`. -/
theorem qtail_rec (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {E γr s : ℝ} (hγr : 0 ≤ γr) (hs : 3 / 2 < s) (q : En eta n)
    (hq : ‖Hret sys L n ΔH q - (E : ℂ) • q‖ ≤ γr * ‖q‖)
    (l : ℝ) (hl : qtailL1 sys L Hunit a E < l) :
    ‖regTail L a l q‖ ≤ qtailC sys L a / l * ‖regTail L a (l / 2) q‖ +
      FSQtail.F (qtailC2 sys L a s) (Wlat a s q) ((γr + CΔ) * ‖q‖) l := by
  classical
  have hg0 : 0 < gL L := gL_pos hL
  have hm : 0 < sys.mass a := sys.mass_pos a
  -- the threshold
  have hlg : gL L ≤ qtailL1 sys L Hunit a E := (le_max_right _ _).trans (le_max_left _ _)
  have hlsq : Real.sqrt (16 * sys.mass a * (Csh sys L Hunit a + E)) ≤ qtailL1 sys L Hunit a E :=
    le_max_right _ _
  have hlpos : 0 < l := by linarith
  have hl2 : 16 * sys.mass a * (Csh sys L Hunit a + E) < l ^ 2 := by
    by_cases h0 : 16 * sys.mass a * (Csh sys L Hunit a + E) < 0
    · nlinarith
    · push Not at h0
      have h1 : Real.sqrt (16 * sys.mass a * (Csh sys L Hunit a + E)) < l := by linarith
      exact (Real.sqrt_lt' hlpos).mp h1
  have hR₀1 : 1 ≤ l / gL L := by rw [le_div_iff₀ hg0]; linarith
  -- the denominator
  have hres := tail_le_resolvent sys Hunit a hL hPeriodic hlpos hl2 q
  set θ : FinitePlaneWaveMode n → ℝ := outW n sys L Hunit a E l with hθ
  -- `(H_ā - E) q = r - ΔH q - V_a q`
  have hDq : Hbar sys L n a q - (E : ℂ) • q =
      (Hret sys L n ΔH q - (E : ℂ) • q) - ΔH q - Va sys L n a q := by
    rw [Hbar, LinearMap.sub_apply, Hret, LinearMap.add_apply]
    abel
  rw [hDq, map_sub, map_sub] at hres
  have hθb : ∀ μ, ‖((θ μ : ℝ) : ℂ)‖ ≤ 16 * sys.mass a / l ^ 2 := fun μ => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact outW_le sys Hunit a hL hlpos hl2 μ
  have hθ0' : 0 ≤ 16 * sys.mass a / l ^ 2 := by positivity
  have hr := (norm_regMul_le a (fun μ => (θ μ : ℂ)) hθ0' hθb _).trans
    (mul_le_mul_of_nonneg_left hq hθ0')
  have hΔ := (norm_regMul_le a (fun μ => (θ μ : ℂ)) hθ0' hθb (ΔH q)).trans
    (mul_le_mul_of_nonneg_left (hΔb q) hθ0')
  -- the channel part
  have hVa := norm_regMul_Va_le sys L n a θ (by positivity) hR₀1 hs
    (outW_le_lat sys Hunit a hL hlpos hl2) (outW_eq_zero sys Hunit a hL hlpos) hL q
  rw [near_sum_eq a hL hlpos q, Real.sqrt_sq (norm_nonneg _), mul_add, ← mul_assoc,
    ← mul_div_assoc] at hVa
  set A := ‖regTail L a (l / 2) q‖ with hA
  set W := Wlat a s q with hWdef
  set N := ‖q‖ with hN
  have hW0 : 0 ≤ W := Wlat_nonneg a s q
  have hN0 : 0 ≤ N := norm_nonneg _
  set P := l ^ (-(1 / 2 : ℝ)) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hlpos.le _
  set S := Real.sqrt (2080 * Zs s * gL L) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  set Qγ := chargeA sys a * coulombCellAmplitude L with hQγ
  have hQγ0 : 0 ≤ Qγ := mul_nonneg (chargeA_nonneg sys a) (coulombCellAmplitude_pos hL).le
  have hVa' : ‖regMul a (fun μ => (θ μ : ℂ)) (Va sys L n a q)‖ ≤
      qtailC sys L a / l * A + Qγ * (16 * sys.mass a * S * P / l ^ 2) * W := by
    refine hVa.trans (le_of_eq ?_)
    rw [← near_coeff sys a hL hlpos, ← far_coeff sys a hL hlpos hs]
    ring
  have htri : ‖regTail L a l q‖ ≤ 16 * sys.mass a / l ^ 2 * (γr * N) +
      16 * sys.mass a / l ^ 2 * (CΔ * N) +
      (qtailC sys L a / l * A + Qγ * (16 * sys.mass a * S * P / l ^ 2) * W) := by
    refine hres.trans ?_
    calc _ ≤ ‖regMul a (fun μ => (θ μ : ℂ)) (Hret sys L n ΔH q - (E : ℂ) • q) -
            regMul a (fun μ => (θ μ : ℂ)) (ΔH q)‖ +
          ‖regMul a (fun μ => (θ μ : ℂ)) (Va sys L n a q)‖ := norm_sub_le _ _
      _ ≤ (‖regMul a (fun μ => (θ μ : ℂ)) (Hret sys L n ΔH q - (E : ℂ) • q)‖ +
            ‖regMul a (fun μ => (θ μ : ℂ)) (ΔH q)‖) +
          ‖regMul a (fun μ => (θ μ : ℂ)) (Va sys L n a q)‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add hr hΔ) hVa'
  refine htri.trans ?_
  -- compare with `F`
  have hF : FSQtail.F (qtailC2 sys L a s) W ((γr + CΔ) * N) l -
      (16 * sys.mass a / l ^ 2 * (γr * N) + 16 * sys.mass a / l ^ 2 * (CΔ * N) +
        Qγ * (16 * sys.mass a * S * P / l ^ 2) * W) =
      16 * sys.mass a / l ^ 2 * P * W + 16 * sys.mass a * Qγ * S / l ^ 2 * ((γr + CΔ) * N) := by
    unfold FSQtail.F qtailC2
    rw [← hS, ← hP, ← hQγ]
    ring
  have h1 : 0 ≤ 16 * sys.mass a / l ^ 2 * P * W := by positivity
  have h2 : 0 ≤ 16 * sys.mass a * Qγ * S / l ^ 2 * ((γr + CΔ) * N) := by
    have : 0 ≤ γr + CΔ := by linarith
    positivity
  linarith

/-- **`lem:qtail`, first bound**: `h(λ) ≤ 4 F(λ) + 2c² ‖q‖/λ²` for `λ > 2λ₁`. -/
theorem qtail (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {E γr s : ℝ} (hγr : 0 ≤ γr) (hs : 3 / 2 < s) (q : En eta n)
    (hq : ‖Hret sys L n ΔH q - (E : ℂ) • q‖ ≤ γr * ‖q‖)
    (l : ℝ) (hl : 2 * qtailL1 sys L Hunit a E < l) :
    ‖regTail L a l q‖ ≤
      4 * FSQtail.F (qtailC2 sys L a s) (Wlat a s q) ((γr + CΔ) * ‖q‖) l +
        2 * qtailC sys L a ^ 2 * ‖q‖ / l ^ 2 := by
  have hg0 := gL_pos hL
  have hl₁ : 0 < qtailL1 sys L Hunit a E :=
    lt_of_lt_of_le hg0 ((le_max_right _ _).trans (le_max_left _ _))
  exact FSQtail.qtail_recursion (h := fun l => ‖regTail L a l q‖) (qtailC_nonneg sys a hL)
    (qtailC2_nonneg sys a hL s) (Wlat_nonneg a s q) (mul_nonneg (by linarith) (norm_nonneg q))
    (norm_nonneg q) hl₁ ((le_max_left _ _).trans (le_max_left _ _))
    (fun l => norm_regTail_le L a l q)
    (fun l hl => qtail_rec sys Hunit a hL hPeriodic hCΔ hΔb hγr hs q hq l hl) l hl

end Recursion

/-! ## Kinetic weights and quasi-eigenstates -/

section Quasi

variable [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) {n : ℕ} (a : Fin eta)

/-- The conversion constant `κ_a = 2 m_a max(1, g⁻²)` of `1 + |ν_a|² ≤ κ_a (1 + A)`. -/
noncomputable def latConst (sys : CoulombSystem eta ν) (L : ℝ) (a : Fin eta) : ℝ :=
  2 * sys.mass a * max 1 (gL L ^ 2)⁻¹

omit [Fintype ν] in
lemma latConst_pos : 0 < latConst sys L a := by
  unfold latConst
  have := sys.mass_pos a
  have : 0 < max 1 (gL L ^ 2)⁻¹ := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

omit [Fintype ν] in
/-- `1 + |ν_a|² ≤ κ_a (1 + A)`. -/
lemma one_add_lsq_le (hL : 0 < L) (p : Cfg eta n) :
    1 + lsq (piA a p) ≤ latConst sys L a * (1 + Asym sys L n p) := by
  have hg0 := gL_pos hL
  have hk := kabs_sq_eq L (p a) (n := n)
  have hc := component_sq_le_mass_mul_massKineticSymbol (fun b => sys.mass_pos b)
    (finitePlaneWaveKabs (2 * Real.pi / L) n) p a
  have hm1 := sys.one_le_mass a
  set M := max 1 (gL L ^ 2)⁻¹ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMg : (gL L ^ 2)⁻¹ ≤ M := le_max_right _ _
  have hA : Asym sys L n p =
      (1 / 2) * massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) p := rfl
  have hmks := massKineticSymbol_nonneg sys L n p
  have hlsq : lsq (piA a p) = finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2 * (gL L ^ 2)⁻¹ := by
    unfold piA; rw [hk]; field_simp
  have h1 : lsq (piA a p) ≤ M * (sys.mass a *
      massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) p) := by
    rw [hlsq]
    calc finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2 * (gL L ^ 2)⁻¹
        ≤ finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2 * M :=
          mul_le_mul_of_nonneg_left hMg (sq_nonneg _)
      _ ≤ (sys.mass a * massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) p) * M :=
          mul_le_mul_of_nonneg_right hc (by linarith)
      _ = _ := by ring
  unfold latConst
  rw [← hM, hA]
  nlinarith

omit [Fintype ν] in
/-- `W_s(q) ≤ κ_a^{s/2} ‖(1+A)^{s/2} q‖`. -/
lemma Wlat_le_wt (hL : 0 < L) {s : ℝ} (hs : 0 ≤ s) (q : En eta n) :
    Wlat a s q ≤ latConst sys L a ^ (s / 2) *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (s / 2) q‖ := by
  have hκ := latConst_pos sys a (L := L)
  have hsq : (Wlat a s q) ^ 2 ≤
      (latConst sys L a ^ (s / 2) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (s / 2) q‖) ^ 2 := by
    rw [Wlat, Real.sq_sqrt (Finset.sum_nonneg fun p _ => mul_nonneg
      (Real.rpow_nonneg (by linarith [lsq_nonneg (piA a p)]) _) (sq_nonneg _)), mul_pow,
      norm_sq_wt, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have hA0 : 0 ≤ 1 + Asym sys L n p := by linarith [Asym_nonneg sys L n p]
    have h1 : (1 + lsq (piA a p)) ^ s ≤ (latConst sys L a * (1 + Asym sys L n p)) ^ s :=
      Real.rpow_le_rpow (by linarith [lsq_nonneg (piA a p)]) (one_add_lsq_le sys a hL p) hs
    have h2 : (latConst sys L a * (1 + Asym sys L n p)) ^ s =
        (latConst sys L a ^ (s / 2)) ^ 2 * ((1 + Asym sys L n p) ^ (s / 2)) ^ 2 := by
      rw [Real.mul_rpow hκ.le hA0, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hκ.le,
        ← Real.rpow_mul hA0]
      norm_num
    rw [h2] at h1
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖q.ofLp p‖)
    linarith
  exact (pow_le_pow_iff_left₀ (Wlat_nonneg a s q) (by positivity) two_ne_zero).mp hsq

/-- The Hardy constant of `V' = W_N + ΔH`: `C_V = √2 C_m + C_Δ`. -/
noncomputable def CVret (sys : CoulombSystem eta ν) (L Hunit CΔ : ℝ) : ℝ :=
  Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit + CΔ

/-- The common lower bound `C_low = C_m² + 1/4 + C_Δ`. -/
noncomputable def Clow (sys : CoulombSystem eta ν) (L Hunit CΔ : ℝ) : ℝ :=
  (finiteCoulombPhysicalMassConstant sys L Hunit) ^ 2 + 1 / 4 + CΔ

lemma CVret_nonneg {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) : 0 ≤ CVret sys L Hunit CΔ := by
  unfold CVret
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  positivity

lemma Clow_pos {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) : 0 < Clow sys L Hunit CΔ := by
  unfold Clow; positivity

/-- **Regularity of quasi-eigenstates**: `‖(1+A)^{s/2} q‖ ≤ (2(1 + |E| + γ + C_V²/2))^{s/2} ‖q‖`
for `0 ≤ s ≤ 2`. -/
lemma wt_le_of_quasi (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {E γ s : ℝ} (hγ : 0 ≤ γ) (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (q : En eta n)
    (hq : ‖Hret sys L n ΔH q - (E : ℂ) • q‖ ≤ γ * ‖q‖) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (s / 2) q‖ ≤
      (2 * (1 + |E| + γ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ (s / 2) * ‖q‖ := by
  have hW1 := wt_one_le_of_quasi sys L n (Hret sys L n ΔH) (Vret sys L n ΔH)
    (Hret_eq_kin_add sys L n ΔH) (CVret_nonneg sys Hunit hCΔ)
    (Vret_le_wt sys Hunit n hL hPeriodic hCΔ hΔb) q hq
  have hH := wt_le_holder sys L n (s := s / 2) (by positivity) (by linarith) q
  set B := 2 * (1 + |E| + γ + CVret sys L Hunit CΔ ^ 2 / 2) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]; have := abs_nonneg E; positivity
  rcases (norm_nonneg q).eq_or_lt with h0 | hpos
  · have hq0 : q = 0 := norm_eq_zero.mp h0.symm
    subst hq0
    have : FSSpectral.wt (sb eta n) (Asym sys L n) (s / 2) 0 = 0 := by
      ext k
      rw [FSSpectral.wt, fc_sb_apply]
      simp
    rw [this]; simp
  refine hH.trans ?_
  calc ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 q‖ ^ (s / 2) * ‖q‖ ^ (1 - s / 2)
      ≤ (B * ‖q‖) ^ (s / 2) * ‖q‖ ^ (1 - s / 2) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) hW1 (by positivity))
          (Real.rpow_nonneg (norm_nonneg _) _)
    _ = B ^ (s / 2) * ‖q‖ := by
        rw [Real.mul_rpow hB0 (norm_nonneg _), mul_assoc, ← Real.rpow_add hpos]
        norm_num

/-- The constant term `a₁ = 4 c₂ (γ + C_Δ)/λ² + 2c²/λ²` of the register bound. -/
noncomputable def regA (sys : CoulombSystem eta ν) (L : ℝ) (a : Fin eta) (s CΔ γ l : ℝ) : ℝ :=
  4 * qtailC2 sys L a s * (γ + CΔ) / l ^ 2 + 2 * qtailC sys L a ^ 2 / l ^ 2

/-- The energy term
`b₁ = 4 c₂ λ^{-1/2}/λ² · κ_a^{s/2} (2(1 + C_low + γ + C_V²/2))^{s/2}` of the register bound. -/
noncomputable def regB (sys : CoulombSystem eta ν) (L Hunit : ℝ) (a : Fin eta) (s CΔ γ l : ℝ) : ℝ :=
  4 * qtailC2 sys L a s * l ^ (-(1 / 2 : ℝ)) / l ^ 2 * latConst sys L a ^ (s / 2) *
    (2 * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ (s / 2)

/-- `1 + |E| + γ + C_V²/2 ≤ (1 + E + C_low)(1 + C_low + γ + C_V²/2)` for `E ≥ -C_low`. -/
lemma quasi_factor_le {E γ C₀ V : ℝ} (hγ : 0 ≤ γ) (hC₀ : 0 ≤ C₀) (hV : 0 ≤ V) (hE : -C₀ ≤ E) :
    1 + |E| + γ + V ≤ (1 + E + C₀) * (1 + C₀ + γ + V) := by
  have h1 : |E| ≤ E + 2 * C₀ := by
    rcases le_or_gt 0 E with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg h]; linarith
  have hx : 1 ≤ 1 + E + C₀ := by linarith
  nlinarith

/-- **The register tail of a quasi-eigenstate**:
`‖1{|k_a| > λ} q‖ ≤ (a₁ + b₁ (1 + E + C_low)^{s/2}) ‖q‖` for `λ > 2λ₁(E)`, `E ≥ -C_low`,
`3/2 < s ≤ 2`. -/
theorem regTail_le_of_quasi (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {E γ s l : ℝ} (hγ : 0 ≤ γ) (hs : 3 / 2 < s) (hs2 : s ≤ 2) (hE : -Clow sys L Hunit CΔ ≤ E)
    (q : En eta n) (hq : ‖Hret sys L n ΔH q - (E : ℂ) • q‖ ≤ γ * ‖q‖)
    (hl : 2 * qtailL1 sys L Hunit a E < l) :
    ‖regTail L a l q‖ ≤ (regA sys L a s CΔ γ l +
      regB sys L Hunit a s CΔ γ l * (1 + E + Clow sys L Hunit CΔ) ^ (s / 2)) * ‖q‖ := by
  have hqt := qtail sys Hunit a hL hPeriodic hCΔ hΔb hγ hs q hq l hl
  have hg0 := gL_pos hL
  have hlpos : 0 < l := by
    have : 0 < qtailL1 sys L Hunit a E :=
      lt_of_lt_of_le hg0 ((le_max_right _ _).trans (le_max_left _ _))
    linarith
  have hs0 : 0 ≤ s := by linarith
  have hC₀ := (Clow_pos sys Hunit hCΔ (L := L)).le
  have hV0 : 0 ≤ CVret sys L Hunit CΔ ^ 2 / 2 := by positivity
  set x := 1 + E + Clow sys L Hunit CΔ with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith
  -- the weighted norm
  have hW : Wlat a s q ≤ latConst sys L a ^ (s / 2) *
      ((2 * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ (s / 2) *
        x ^ (s / 2) * ‖q‖) := by
    refine (Wlat_le_wt sys a hL hs0 q).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (latConst_pos sys a).le _)
    refine (wt_le_of_quasi sys Hunit hL hPeriodic hCΔ hΔb hγ hs0 hs2 q hq).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hf := quasi_factor_le hγ hC₀ hV0 hE
    rw [← hx] at hf
    calc (2 * (1 + |E| + γ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ (s / 2)
        ≤ (2 * (x * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2))) ^ (s / 2) := by
          apply Real.rpow_le_rpow (by have := abs_nonneg E; positivity) _ (by positivity)
          rw [add_assoc (1 + |E|), add_assoc (1 + Clow sys L Hunit CΔ)] at *
          nlinarith
      _ = _ := by
          rw [show 2 * (x * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) =
              (2 * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) * x by ring,
            Real.mul_rpow (by positivity) (by linarith)]
  refine hqt.trans ?_
  have hc₂ := qtailC2_nonneg sys a hL s
  have hP0 : 0 ≤ l ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hlpos.le _
  have hF : FSQtail.F (qtailC2 sys L a s) (Wlat a s q) ((γ + CΔ) * ‖q‖) l ≤
      qtailC2 sys L a s / l ^ 2 * (l ^ (-(1 / 2 : ℝ)) * (latConst sys L a ^ (s / 2) *
        ((2 * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ (s / 2) *
          x ^ (s / 2) * ‖q‖)) + (γ + CΔ) * ‖q‖) := by
    unfold FSQtail.F
    gcongr
  unfold regA regB
  have hfinal : 4 * (qtailC2 sys L a s / l ^ 2 * (l ^ (-(1 / 2 : ℝ)) * (latConst sys L a ^ (s / 2) *
        ((2 * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ (s / 2) *
          x ^ (s / 2) * ‖q‖)) + (γ + CΔ) * ‖q‖)) + 2 * qtailC sys L a ^ 2 * ‖q‖ / l ^ 2 =
      (4 * qtailC2 sys L a s * (γ + CΔ) / l ^ 2 + 2 * qtailC sys L a ^ 2 / l ^ 2 +
        4 * qtailC2 sys L a s * l ^ (-(1 / 2 : ℝ)) / l ^ 2 * latConst sys L a ^ (s / 2) *
          (2 * (1 + Clow sys L Hunit CΔ + γ + CVret sys L Hunit CΔ ^ 2 / 2)) ^ (s / 2) *
            x ^ (s / 2)) * ‖q‖ := by
    ring
  linarith

end Quasi

end FSGalerkin
