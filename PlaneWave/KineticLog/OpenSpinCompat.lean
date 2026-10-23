import PlaneWave.KineticLog.OpenSpin

/-!
# Logarithmic kinetic bound, part 31: compatible cutoffs with spin

The compatible-cutoff corollaries of `prop:free-kinetic-log` in the spin-inclusive space. The
domain transfer is applied to each spin component; with `w_σ = C_sys (‖Ψ_σ‖ + ‖HΨ_σ‖ + ‖H²Ψ_σ‖)`
the componentwise bounds `‖φ_σ‖ ≤ w_σ`, `‖H_L φ_σ‖ ≤ Λ w_σ`, `‖H_L² φ_σ‖ ≤ Λ² w_σ` give, through
`Σ_σ (a_σ + b_σ + c_σ)² ≤ (‖a‖ + ‖b‖ + ‖c‖)²`,
`D_* ≤ (1 + Λ + Λ²) C_sys (‖Ψ₀‖ + ‖H_∞Ψ₀‖ + ‖H_∞²Ψ₀‖)` in the spin-inclusive Hilbert norms, with
no spin-dimension factor. The constants are those of the scalar corollaries.

* `spin_budget`: the spin-summed budget;
* **`free_kinetic_log_nbo_spin`**, **`free_kinetic_log_bo_spin`**: general compatible cutoffs;
* **`free_kinetic_log_nbo_spin_uniform`**, **`free_kinetic_log_bo_spin_uniform`**: the explicit
  cutoffs of `prop:free-dyn`, uniform in `L ≥ L₀`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter MeasureTheory Set PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic PlaneWaveGrid
  PlaneWaveGridDynamics FreeBoundary FSNormal

namespace KineticLog

attribute [local instance] FreeBoundary.unitAddCircleMeasureSpaceFB15
  FreeBoundary.unitAddCircleProbabilityMeasureFB15 FreeBoundary.molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The spin-summed budget -/

/-- `√(Σ a²) ≤ G W` from `0 ≤ a_σ ≤ G w_σ` and `Σ w² ≤ W²`. -/
lemma sqrt_sum_sq_le_of {ς : Type*} [Fintype ς] (a w : ς → ℝ) {G W : ℝ} (hG : 0 ≤ G)
    (hW : 0 ≤ W) (ha0 : ∀ σ, 0 ≤ a σ) (ha : ∀ σ, a σ ≤ G * w σ)
    (hw : ∑ σ, w σ ^ 2 ≤ W ^ 2) :
    Real.sqrt (∑ σ, a σ ^ 2) ≤ G * W := by
  refine Real.sqrt_le_iff.mpr ⟨mul_nonneg hG hW, ?_⟩
  calc ∑ σ, a σ ^ 2 ≤ ∑ σ, (G * w σ) ^ 2 :=
        Finset.sum_le_sum fun σ _ => pow_le_pow_left₀ (ha0 σ) (ha σ) 2
    _ = G ^ 2 * ∑ σ, w σ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
    _ ≤ G ^ 2 * W ^ 2 := mul_le_mul_of_nonneg_left hw (sq_nonneg G)
    _ = (G * W) ^ 2 := by ring

/-- **The spin-summed budget**: componentwise bounds `a_σ ≤ w_σ`, `b_σ ≤ Λ w_σ`, `c_σ ≤ Λ² w_σ`,
`w_σ = C (u_σ + h_σ + k_σ)`, with `Σ u² ≤ U²`, `Σ h² ≤ H²`, `Σ k² ≤ K²`, give
`√(Σ a²) + √(Σ b²) + √(Σ c²) ≤ (1 + Λ + Λ²) C (U + H + K)`. -/
lemma spin_budget {ς : Type*} [Fintype ς] (a b c u h k : ς → ℝ) {Λ C U H K : ℝ}
    (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (ha0 : ∀ σ, 0 ≤ a σ) (hb0 : ∀ σ, 0 ≤ b σ) (hc0 : ∀ σ, 0 ≤ c σ)
    (hU0 : 0 ≤ U) (hH0 : 0 ≤ H) (hK0 : 0 ≤ K)
    (hU : ∑ σ, u σ ^ 2 ≤ U ^ 2) (hH : ∑ σ, h σ ^ 2 ≤ H ^ 2) (hK : ∑ σ, k σ ^ 2 ≤ K ^ 2)
    (ha : ∀ σ, a σ ≤ C * (u σ + h σ + k σ)) (hb : ∀ σ, b σ ≤ Λ * (C * (u σ + h σ + k σ)))
    (hc : ∀ σ, c σ ≤ Λ ^ 2 * (C * (u σ + h σ + k σ))) :
    Real.sqrt (∑ σ, a σ ^ 2) + Real.sqrt (∑ σ, b σ ^ 2) + Real.sqrt (∑ σ, c σ ^ 2) ≤
      (1 + Λ + Λ ^ 2) * C * (U + H + K) := by
  have hw : ∑ σ, (u σ + h σ + k σ) ^ 2 ≤ (U + H + K) ^ 2 := by
    have h1 := sum_sq_add_le_of u h hU0 hH0 hU hH
    exact sum_sq_add_le_of (fun σ => u σ + h σ) k (add_nonneg hU0 hH0) hK0 h1 hK
  have hW0 : 0 ≤ U + H + K := by positivity
  have hwC : ∑ σ, (C * (u σ + h σ + k σ)) ^ 2 ≤ (C * (U + H + K)) ^ 2 := by
    have e : ∑ σ, (C * (u σ + h σ + k σ)) ^ 2 = C ^ 2 * ∑ σ, (u σ + h σ + k σ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    have e' : (C * (U + H + K)) ^ 2 = C ^ 2 * (U + H + K) ^ 2 := by ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_left hw (sq_nonneg C)
  have hCW : 0 ≤ C * (U + H + K) := mul_nonneg hC hW0
  have s1 := sqrt_sum_sq_le_of a (fun σ => C * (u σ + h σ + k σ)) zero_le_one hCW ha0
    (fun σ => by rw [one_mul]; exact ha σ) hwC
  have s2 := sqrt_sum_sq_le_of b (fun σ => C * (u σ + h σ + k σ)) hΛ hCW hb0 hb hwC
  have s3 := sqrt_sum_sq_le_of c (fun σ => C * (u σ + h σ + k σ)) (sq_nonneg Λ) hCW hc0 hc hwC
  have e : (1 + Λ + Λ ^ 2) * C * (U + H + K) =
      1 * (C * (U + H + K)) + Λ * (C * (U + H + K)) + Λ ^ 2 * (C * (U + H + K)) := by ring
  rw [e]
  linarith

/-- `Σ_σ ‖x_σ‖² = ‖x‖²` in the spin-inclusive space. -/
lemma sum_norm_sq_spin {ς : Type*} [Fintype ς] (x : FreeSpinL2 eta ς) :
    ∑ σ, ‖x σ‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]

/-! ## Compatible cutoffs -/

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with spin, mass-compatible cutoff (no clamped nuclei)**: the
cutoff-domain condition is proved for each spin component and the data enter through
`‖Ψ₀‖ + ‖H_∞Ψ₀‖ + ‖H_∞²Ψ₀‖ ≤ 𝒟` (spin-inclusive Hilbert norms):
`|Σ_σ ⟨Ψ_σ(t), T_p Ψ_σ(t)⟩ - Σ_σ ⟨Ψ_{g,σ}(t), T_p Ψ_{g,σ}(t)⟩|
  ≤ C 𝒟² [1 + t + log(2 + K)]/K³ + C 𝒟 (1 + t) ε`,
`C = freeKinConstNBO sys V_θ D̄ C̄` (the scalar constant). -/
theorem free_kinetic_log_nbo_spin [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ}
    {θ : ℝ → ℝ} (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0)
    (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Dbar Cbar : ℝ} (hDbar : X.D ≤ Dbar) (hCbar : X.C ≤ Cbar)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys (tv R θ) molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))| ≤
      freeKinConstNBO sys (tv R θ) Dbar Cbar * D ^ 2 *
          (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstNBO sys (tv R θ) Dbar Cbar * D * (1 + t) * ε := by
  have hL := pos_of_two_pi_le hL2
  have hV := hθ.tv_nonneg
  have hc₀ := norm_zeroModeShift_le sys hL2 hθ hR
  choose h₀ h₁ hd0 hd1 n0 n1 n2 using fun σ => cut_state_domain_reg sys hL hR0 hρ hone P hP
    hpos X hret (hHam 0 σ) (hH1 σ) hc₀
  have hQ0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have hD0 : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  set Λ := domConst sys.charge (zeroWeight sys / 4) Dbar Cbar with hΛ
  have hΛX : domConst sys.charge (zeroWeight sys / 4) X.D X.C ≤ Λ := domConst_mono _ hDbar hCbar
  have hΛX1 : 1 ≤ domConst sys.charge (zeroWeight sys / 4) X.D X.C :=
    one_le_domConst _ hQ0 X.D_nonneg X.C_nonneg
  have hΛ0 : 0 ≤ Λ := by linarith
  have hreg := one_le_regConst sys
  have hreg0 : 0 ≤ regConst sys := by linarith
  have hdat : 0 ≤ ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ := by positivity
  have hD00 : 0 ≤ D := hdat.trans hD
  have hw0 : ∀ σ, 0 ≤ regConst sys * (‖Ψ 0 σ‖ + ‖HΨ 0 σ‖ + ‖Kψ σ‖) := fun σ => by positivity
  have hb : ∀ σ, ‖h₀ σ‖ ≤ Λ * (regConst sys * (‖Ψ 0 σ‖ + ‖HΨ 0 σ‖ + ‖Kψ σ‖)) := fun σ =>
    (n1 σ).trans (mul_le_mul_of_nonneg_right hΛX (hw0 σ))
  have hc : ∀ σ, ‖h₁ σ‖ ≤ Λ ^ 2 * (regConst sys * (‖Ψ 0 σ‖ + ‖HΨ 0 σ‖ + ‖Kψ σ‖)) := fun σ =>
    (n2 σ).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hΛX 2) (hw0 σ))
  have hB := spin_budget (fun σ => ‖X.toCutoff.chiW.cutL2 hL (Ψ 0 σ)‖) (fun σ => ‖h₀ σ‖)
    (fun σ => ‖h₁ σ‖) (fun σ => ‖Ψ 0 σ‖) (fun σ => ‖HΨ 0 σ‖) (fun σ => ‖Kψ σ‖) hΛ0 hreg0
    (fun σ => norm_nonneg _) (fun σ => norm_nonneg _) (fun σ => norm_nonneg _) (norm_nonneg (Ψ 0))
    (norm_nonneg (HΨ 0)) (norm_nonneg Kψ) (sum_norm_sq_spin _) (sum_norm_sq_spin _)
    (sum_norm_sq_spin _) n0 hb hc
  have hDst : Real.sqrt (∑ σ, ‖X.toCutoff.chiW.cutL2 hL (Ψ 0 σ)‖ ^ 2) +
      Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤
      (1 + Λ + Λ ^ 2) * regConst sys * D := by
    refine hB.trans ?_
    exact mul_le_mul_of_nonneg_left hD (by positivity)
  have hDinf : ‖Ψ 0‖ + ‖HΨ 0‖ ≤ D := by linarith [norm_nonneg Kψ]
  have h := free_kinetic_log_spin sys hL2 hθ hR hR0 hρ hone P hP hpos X.toCutoff hret hDbar
    hDbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hd0 hd1 hDinf hDst p₀ m hm
    hK hκ Ug hg0 hgcomm hgderiv
  refine h.trans ?_
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hV hK).1
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hG : 0 ≤ (1 + Λ + Λ ^ 2) * regConst sys := by positivity
  have := transfer_arith (C := freeKinC sys (tv R θ) Dbar) (G := (1 + Λ + Λ ^ 2) * regConst sys)
    (q := 1 + t + Real.log (2 + 2 * Real.pi / L * m)) (K := 2 * Real.pi / L * m)
    (freeKinC_nonneg sys hV hD0) hG hD00 (by positivity) le_rfl (by positivity) (by linarith) ht hε
  unfold freeKinConstNBO
  rw [← hΛ]
  refine this.trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
/-- **`prop:free-kinetic-log` with spin, clamped nuclei, cutoff flat near the nuclei**: as
`free_kinetic_log_nbo_spin` with the nuclear domain transfer (`cut_state_domain_reg_nuc`),
`C = freeKinConstBO sys V_θ D̄ C̄ δ` (the scalar constant). -/
theorem free_kinetic_log_bo_spin (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ)
    {Dbar Cbar : ℝ} (hDbar : X.D ≤ Dbar) (hCbar : X.C ≤ Cbar)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys (tv R θ) molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (pos_of_two_pi_le hL2) (Ψ 0 σ)))))| ≤
      freeKinConstBO sys (tv R θ) Dbar Cbar δ * D ^ 2 *
          (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstBO sys (tv R θ) Dbar Cbar δ * D * (1 + t) * ε := by
  have hL := pos_of_two_pi_le hL2
  have hV := hθ.tv_nonneg
  have hc₀ := norm_zeroModeShift_le sys hL2 hθ hR
  choose h₀ h₁ hd0 hd1 n0 n1 n2 using fun σ => cut_state_domain_reg_nuc sys hL hR0 hρ hone P hP
    hpos X hret hδ hflat (hHam 0 σ) (hH1 σ) hc₀
  have hQ0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have hD0 : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  set Λ := domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) Dbar Cbar δ with hΛ
  have hΛX : domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) X.D X.C δ ≤ Λ :=
    domConstN_mono _ _ _ hDbar hCbar
  have hΛX1 : 1 ≤ domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) X.D X.C δ :=
    one_le_domConstN _ _ hQ0 X.D_nonneg X.C_nonneg
  have hΛ0 : 0 ≤ Λ := by linarith
  have hreg := one_le_regConstN sys
  have hreg0 : 0 ≤ regConstN sys := by linarith
  have hdat : 0 ≤ ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ := by positivity
  have hD00 : 0 ≤ D := hdat.trans hD
  have hw0 : ∀ σ, 0 ≤ regConstN sys * (‖Ψ 0 σ‖ + ‖HΨ 0 σ‖ + ‖Kψ σ‖) := fun σ => by positivity
  have hb : ∀ σ, ‖h₀ σ‖ ≤ Λ * (regConstN sys * (‖Ψ 0 σ‖ + ‖HΨ 0 σ‖ + ‖Kψ σ‖)) := fun σ =>
    (n1 σ).trans (mul_le_mul_of_nonneg_right hΛX (hw0 σ))
  have hc : ∀ σ, ‖h₁ σ‖ ≤ Λ ^ 2 * (regConstN sys * (‖Ψ 0 σ‖ + ‖HΨ 0 σ‖ + ‖Kψ σ‖)) := fun σ =>
    (n2 σ).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hΛX 2) (hw0 σ))
  have hB := spin_budget (fun σ => ‖X.toCutoff.chiW.cutL2 hL (Ψ 0 σ)‖) (fun σ => ‖h₀ σ‖)
    (fun σ => ‖h₁ σ‖) (fun σ => ‖Ψ 0 σ‖) (fun σ => ‖HΨ 0 σ‖) (fun σ => ‖Kψ σ‖) hΛ0 hreg0
    (fun σ => norm_nonneg _) (fun σ => norm_nonneg _) (fun σ => norm_nonneg _) (norm_nonneg (Ψ 0))
    (norm_nonneg (HΨ 0)) (norm_nonneg Kψ) (sum_norm_sq_spin _) (sum_norm_sq_spin _)
    (sum_norm_sq_spin _) n0 hb hc
  have hDst : Real.sqrt (∑ σ, ‖X.toCutoff.chiW.cutL2 hL (Ψ 0 σ)‖ ^ 2) +
      Real.sqrt (∑ σ, ‖h₀ σ‖ ^ 2) + Real.sqrt (∑ σ, ‖h₁ σ‖ ^ 2) ≤
      (1 + Λ + Λ ^ 2) * regConstN sys * D := by
    refine hB.trans ?_
    exact mul_le_mul_of_nonneg_left hD (by positivity)
  have hDinf : ‖Ψ 0‖ + ‖HΨ 0‖ ≤ D := by linarith [norm_nonneg Kψ]
  have h := free_kinetic_log_spin sys hL2 hθ hR hR0 hρ hone P hP hpos X.toCutoff hret hDbar
    hDbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hd0 hd1 hDinf hDst p₀ m hm
    hK hκ Ug hg0 hgcomm hgderiv
  refine h.trans ?_
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hV hK).1
  have hlog : 0 ≤ Real.log (2 + 2 * Real.pi / L * m) := Real.log_nonneg (by linarith)
  have hG : 0 ≤ (1 + Λ + Λ ^ 2) * regConstN sys := by positivity
  have := transfer_arith (C := freeKinC sys (tv R θ) Dbar) (G := (1 + Λ + Λ ^ 2) * regConstN sys)
    (q := 1 + t + Real.log (2 + 2 * Real.pi / L * m)) (K := 2 * Real.pi / L * m)
    (freeKinC_nonneg sys hV hD0) hG hD00 (by positivity) le_rfl (by positivity) (by linarith) ht hε
  unfold freeKinConstBO
  rw [← hΛ]
  refine this.trans (le_of_eq ?_)
  ring

/-! ## The explicit cutoffs, uniform in `L` -/

set_option maxHeartbeats 400000 in
/-- **`prop:free-kinetic-log` with spin, no clamped nuclei, uniform in `L`**: the explicit
mass-weighted cutoff `quadCutoffL` and its leakage regions, spin-summed leakage,
`‖Ψ₀‖ + ‖H_∞Ψ₀‖ + ‖H_∞²Ψ₀‖ ≤ 𝒟`:
`|Σ_σ ⟨Ψ_σ(t), T_p Ψ_σ(t)⟩ - Σ_σ ⟨Ψ_{g,σ}(t), T_p Ψ_{g,σ}(t)⟩|
  ≤ C 𝒟² [1 + t + log(2 + K)]/K³ + C 𝒟 (1 + t) ε`,
`C = freeKinConstNBO sys V D_s C_s` (the scalar constant), `K₀ = cellK0 sys V`. -/
theorem free_kinetic_log_nbo_spin_uniform [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ V : ℝ}
    (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) {L R : ℝ} {θ : ℝ → ℝ} (hL : freeKinL0 R0 ρ ≤ L)
    (hθ : Profile R θ) (hR : R ≤ L / 2) (hV : tv R θ = V)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t,
      ∑ σ, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r}, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2}, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm : 8 ≤ m)
    (hK : cellK0 sys V molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t) :
    |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          ((quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
            (pos_of_freeDynL0 hL) (Ψ 0 σ)))))| ≤
      freeKinConstNBO sys V (quadCutoff8 sys.one_le_mass).D (quadCutoff8 sys.one_le_mass).C *
          D ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstNBO sys V (quadCutoff8 sys.one_le_mass).D (quadCutoff8 sys.one_le_mass).C *
          D * (1 + t) * ε := by
  subst hV
  have h8 := eight_le_of_freeDynL0 hL
  have hL2 := two_pi_le_of_freeDynL0 hL
  have hS : MeasurableSet {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2} :=
    (measurableSet_le measurable_const
      (contDiff_massQ sys.mass (n := 0)).continuous.measurable).inter
      (measurableSet_le (contDiff_massQ sys.mass (n := 0)).continuous.measurable measurable_const)
  have hB : MeasurableSet {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2} :=
    measurableSet_lt (contDiff_massQ sys.mass (n := 0)).continuous.measurable measurable_const
  have hSB : {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r ∧ massQ sys.mass r ≤ 2 * (L / 8) ^ 2} ⊆
      {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2}ᶜ := fun r hr h => by
    simp only [Set.mem_setOf_eq] at hr h
    linarith [hr.1]
  have hc : {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2}ᶜ =
      {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r} := by
    ext r
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  have hret : ∀ r, (quadCutoffL sys.one_le_mass h8).χ r ≠ 0 →
      ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ := fun r hr i =>
    (quadCutoffL_ret sys.one_le_mass h8 r hr i).trans (ret_of_freeDynL0 hL)
  exact free_kinetic_log_nbo_spin sys hL2 hθ hR hR0 hρ hone P hP hpos
    (quadCutoffL sys.one_le_mass h8) hret (quadCutoffL_D_le sys.one_le_mass h8)
    (quadCutoffL_C_le sys.one_le_mass h8) hS hB (quadCutoffL_one sys.one_le_mass h8) hSB
    (fun r hr a => (quadCutoffL_derivs sys.one_le_mass h8 r hr a).1)
    (fun r hr a => (quadCutoffL_derivs sys.one_le_mass h8 r hr a).2) hψd hHam hgrad ht hε
    (fun s hs => by rw [hc]; exact hleak0 s hs) hleak1 hH1 hD p₀ m hm hK hκ Ug hg0 hgcomm hgderiv

set_option maxHeartbeats 400000 in
/-- **`prop:free-kinetic-log` with spin, clamped nuclei and equal moving masses, uniform in `L`**:
the explicit product cutoff `prodCutoffL` flat within `δ` of the nuclei, the molecule in the cell
of size `L ≥ L₀` (`sysAt sys P L`), spin-summed leakage,
`‖Ψ₀‖ + ‖H_∞Ψ₀‖ + ‖H_∞²Ψ₀‖ ≤ 𝒟`; `C = freeKinConstBO sys V D_s C_s δ` (the scalar constant). -/
theorem free_kinetic_log_bo_spin_uniform (sys : CoulombSystem eta ν) {m₀ : ℝ}
    (hmass : ∀ i, sys.mass i = m₀) (hm0 : 1 ≤ m₀) {V R0 ρ δ : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hδ : 0 < δ) (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0) {L R : ℝ} {θ : ℝ → ℝ}
    (hL : freeKinBOL0 R0 ρ δ ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hV : tv R θ = V)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t,
      ∑ σ, ∫ r in {r | ∃ i, L / 16 ≤ ‖particle r i‖}, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in {r | (∃ i, L / 16 ≤ ‖particle r i‖) ∧
      ∀ i, ‖particle r i‖ ≤ L / 8}, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (p₀ : Fin eta) (m : ℕ) (hm8 : 8 ≤ m)
    (hK : cellK0 sys V molecularCanonicalUnitHardyConstant ≤ 2 * Real.pi / L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (tv R θ))
      (PlaneWaveGridG.gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys)
      (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x) =
        Hgrid eta m (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei).toNucData
          κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys)
        (posNucleiOf (sysAt sys P L).nuclei).toNucData κ (2 * Real.pi / L) x))) t) :
    |freeKinQS sys p₀ (grad t) - ∑ σ, regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm
          ((prodCutoffL hmass hm0 (sixteen_le_of_freeDynBOL0 hL)).toCutoff.chiW.cutL2
            (pos_of_freeDynBOL0 hL) (Ψ 0 σ)))))| ≤
      freeKinConstBO sys V (prodCutoff16 hmass hm0).D (prodCutoff16 hmass hm0).C δ * D ^ 2 *
          (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 +
        freeKinConstBO sys V (prodCutoff16 hmass hm0).D (prodCutoff16 hmass hm0).C δ * D *
          (1 + t) * ε := by
  subst hV
  have h16 := sixteen_le_of_freeDynBOL0 hL
  have hL2 := two_pi_le_of_freeDynBOL0 hL
  have hS : MeasurableSet {r : Rcfg eta | (∃ i, L / 16 ≤ ‖particle r i‖) ∧
      ∀ i, ‖particle r i‖ ≤ L / 8} := by
    rw [Set.setOf_and, Set.setOf_exists, Set.setOf_forall]
    exact (MeasurableSet.iUnion fun i => measurableSet_le measurable_const
      (continuous_norm_particle i).measurable).inter
      (MeasurableSet.iInter fun i => measurableSet_le (continuous_norm_particle i).measurable
        measurable_const)
  have hB : MeasurableSet {r : Rcfg eta | ∀ i, ‖particle r i‖ < L / 16} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt (continuous_norm_particle i).measurable measurable_const
  have hSB : {r : Rcfg eta | (∃ i, L / 16 ≤ ‖particle r i‖) ∧ ∀ i, ‖particle r i‖ ≤ L / 8} ⊆
      {r : Rcfg eta | ∀ i, ‖particle r i‖ < L / 16}ᶜ := by
    rintro r ⟨⟨i, hi⟩, -⟩ h
    exact absurd (h i) (not_lt.mpr hi)
  have hc : {r : Rcfg eta | ∀ i, ‖particle r i‖ < L / 16}ᶜ =
      {r : Rcfg eta | ∃ i, L / 16 ≤ ‖particle r i‖} := by
    ext r
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_lt]
  have hret : ∀ r, (prodCutoffL hmass hm0 h16).χ r ≠ 0 →
      ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ := fun r hr i =>
    (prodCutoffL_ret hmass hm0 h16 r hr i).trans (ret_of_freeDynBOL0 hδ.le hL)
  have hflat : IsFlatNear (prodCutoffL hmass hm0 h16).χ P δ :=
    prodCutoffL_isFlatNear hmass hm0 h16 P (flat_of_freeDynBOL0 hρ hL hP)
  exact free_kinetic_log_bo_spin (sysAt sys P L) hL2 hθ hR hR0 hρ hone P hP (fun l => rfl)
    (prodCutoffL hmass hm0 h16) hret hδ hflat (prodCutoffL_D_le hmass hm0 h16)
    (prodCutoffL_C_le hmass hm0 h16) hS hB (prodCutoffL_one hmass hm0 h16) hSB
    (fun r hr a => (prodCutoffL_derivs hmass hm0 h16 r hr a).1)
    (fun r hr a => (prodCutoffL_derivs hmass hm0 h16 r hr a).2) hψd hHam hgrad ht hε
    (fun s hs => by rw [hc]; exact hleak0 s hs) hleak1 hH1 hD p₀ m hm8 hK hκ Ug hg0 hgcomm hgderiv

end KineticLog
