import PlaneWave.FreeBoundary.SpinFreeDynamicsGrid

/-!
# Spin, part 3: `prop:free-dyn` with internal spin in the form of the manuscript

The endpoints of `prop:free-dyn` for the spin-inclusive space `L²(ℝ^{3η}) ⊗ ℂ^ς`, with the
leakage summed over the spin components and the Hilbert norms of the spin-inclusive space: the
norm is conserved (`norm_conserved_spin`), the data norm `‖Ψ₀‖ + ‖H_∞Ψ₀‖ + ‖H_∞²Ψ₀‖ ≤ D` bounds
`Σ_σ N_σ²` by `(c′ D)²` (`sum_sq_add3_le`), and the bound takes the form
`C [K⁻⁵ + t K⁻³] + C (1 + t) ε` with `C = freeDynConstSpinNBO …` (no clamped nuclei) or
`C = freeDynConstSpinBO …` (clamped nuclei, a cutoff flat near them). The constants are those of
the grid step at the unit data, scaled by `(c′ D)²` (`spinScale`); they do not depend on the number
of spin components, nor on `L`.

* `norm_conserved_spin`, `sum_sq_add3_le`, `spinScale`, `le_spin_form`, `spin_final_le`;
* `freeDynConstSpinNBO`, `freeDynConstSpinBO`;
* **`free_dyn_nbo_spin_endpoint`**, **`free_dyn_bo_spin_endpoint`** (fixed `L`);
* **`free_dyn_nbo_spin_uniform`**, **`free_dyn_bo_spin_uniform`** (one constant for all
  `L ≥ L₀`, with the explicit cutoffs of `free_dyn_nbo_uniform` and `free_dyn_bo_uniform`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLref)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Norms, data and the form of the bound -/

section Form

/-- **The norm of the spin-inclusive state is conserved.** -/
theorem norm_conserved_spin (sys : CoulombSystem eta ν) (P : ν → E3) {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ)) (t : ℝ) : ‖Ψ t‖ = ‖Ψ 0‖ := by
  have hc : ∀ σ, ‖Ψ t σ‖ = ‖Ψ 0 σ‖ := fun σ =>
    norm_conserved sys P (ψ := fun s => Ψ s σ) (H := fun s => HΨ s σ)
      (fun s => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ς => FreeL2 eta) σ).hasFDerivAt.comp_hasDerivAt s
        (hψd s)) (fun s => hHam s σ) t
  rw [PiLp.norm_eq_of_L2 (Ψ t), PiLp.norm_eq_of_L2 (Ψ 0)]
  simp only [hc]

/-- `Σ (a + b + c)² ≤ (√(Σ a²) + √(Σ b²) + √(Σ c²))²`. -/
lemma sum_sq_add3_le {ς : Type*} [Fintype ς] (a b c : ς → ℝ) :
    ∑ σ, (a σ + b σ + c σ) ^ 2 ≤
      (Real.sqrt (∑ σ, a σ ^ 2) + Real.sqrt (∑ σ, b σ ^ 2) + Real.sqrt (∑ σ, c σ ^ 2)) ^ 2 := by
  have hab := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have hac := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a c
  have hbc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ b c
  have ha := Real.sq_sqrt (Finset.sum_nonneg fun σ (_ : σ ∈ Finset.univ) => sq_nonneg (a σ))
  have hb := Real.sq_sqrt (Finset.sum_nonneg fun σ (_ : σ ∈ Finset.univ) => sq_nonneg (b σ))
  have hc := Real.sq_sqrt (Finset.sum_nonneg fun σ (_ : σ ∈ Finset.univ) => sq_nonneg (c σ))
  have e : ∑ σ, (a σ + b σ + c σ) ^ 2 = ∑ σ, a σ ^ 2 + ∑ σ, b σ ^ 2 + ∑ σ, c σ ^ 2 +
      2 * ∑ σ, a σ * b σ + 2 * ∑ σ, a σ * c σ + 2 * ∑ σ, b σ * c σ := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [e]
  set A := Real.sqrt (∑ σ, a σ ^ 2)
  set B := Real.sqrt (∑ σ, b σ ^ 2)
  set C := Real.sqrt (∑ σ, c σ ^ 2)
  have e2 : (A + B + C) ^ 2 = A ^ 2 + B ^ 2 + C ^ 2 + 2 * (A * B) + 2 * (A * C) + 2 * (B * C) := by
    ring
  rw [e2, ha, hb, hc]
  linarith

/-- `(N² A₁, N² A₂, N² A₃)`. -/
def spinScale (N : ℝ) (A : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ := (N ^ 2 * A.1, N ^ 2 * A.2.1, N ^ 2 * A.2.2)

/-- The form of the bound with the constants at the unit data scaled by `N²`. -/
lemma le_spin_form {A : ℝ × ℝ × ℝ} {N T c n ε t K : ℝ} (hN : 0 ≤ N) (hc : 0 ≤ c)
    (hn : n ≤ 2 * N) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) (hK : 0 < K) :
    ε ^ 2 + n * (c * ε * t) + N ^ 2 * ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + 1) * T) * (1 / K) ^ 5 +
        A.2.1 * t * (1 / K) ^ 3) ≤
      dynConst (spinScale N A) N T c * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
        dynConst (spinScale N A) N T c * (1 + t) * ε := by
  have e : N ^ 2 * ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + 1) * T) * (1 / K) ^ 5 +
      A.2.1 * t * (1 / K) ^ 3) =
      ((spinScale N A).1 + ((spinScale N A).2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * T) * (1 / K) ^ 5 +
        (spinScale N A).2.1 * t * (1 / K) ^ 3 := by
    simp only [spinScale]
    ring
  rw [e]
  exact le_dynConst_form hN hc hn hε hε1 ht hK

/-- **The final step**: from the bound of `free_dyn_grid_spin` with `N_σ = c′(‖Ψ₀,σ‖ + ‖H₀,σ‖ +
‖K_σ‖)` to the form of the manuscript, for `‖Ψ₀‖ + ‖H₀‖ + ‖K‖ ≤ D`. -/
lemma spin_final_le {ς : Type*} [Fintype ς] {Ψt Ψ0 H0 K0 : FreeSpinL2 eta ς}
    (hcons : ‖Ψt‖ = ‖Ψ0‖) {ρc D : ℝ} (hρc : 1 ≤ ρc) (hD : ‖Ψ0‖ + ‖H0‖ + ‖K0‖ ≤ D)
    {A : ℝ × ℝ × ℝ} (hA1 : 0 ≤ A.1) (hA2 : 0 ≤ A.2.1) (hA3 : 0 ≤ A.2.2) {T c cbar ε t K : ℝ}
    (hT : 0 ≤ T) (hc0 : 0 ≤ c) (hcc : c ≤ cbar) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t)
    (hK : 0 < K) :
    ε ^ 2 + (‖Ψt‖ + ‖Ψ0‖) * (c * ε * t) +
        (∑ σ, (ρc * (‖Ψ0 σ‖ + ‖H0 σ‖ + ‖K0 σ‖)) ^ 2) *
          ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + 1) * T) * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3) ≤
      dynConst (spinScale (ρc * D) A) (ρc * D) T cbar * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
        dynConst (spinScale (ρc * D) A) (ρc * D) T cbar * (1 + t) * ε := by
  have hS0 : 0 ≤ ‖Ψ0‖ + ‖H0‖ + ‖K0‖ := by positivity
  have hD0 : 0 ≤ D := hS0.trans hD
  have hN0 : 0 ≤ ρc * D := by positivity
  have hB : 0 ≤ (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + 1) * T) * (1 / K) ^ 5 +
      A.2.1 * t * (1 / K) ^ 3 := by
    have : 0 ≤ 1 / K := div_nonneg zero_le_one hK.le
    positivity
  have hsum : ∑ σ, (ρc * (‖Ψ0 σ‖ + ‖H0 σ‖ + ‖K0 σ‖)) ^ 2 ≤ (ρc * D) ^ 2 := by
    have h1 : ∑ σ, (‖Ψ0 σ‖ + ‖H0 σ‖ + ‖K0 σ‖) ^ 2 ≤ (‖Ψ0‖ + ‖H0‖ + ‖K0‖) ^ 2 := by
      rw [PiLp.norm_eq_of_L2 Ψ0, PiLp.norm_eq_of_L2 H0, PiLp.norm_eq_of_L2 K0]
      exact sum_sq_add3_le _ _ _
    have h2 : (‖Ψ0‖ + ‖H0‖ + ‖K0‖) ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hS0 hD 2
    have e : ∑ σ, (ρc * (‖Ψ0 σ‖ + ‖H0 σ‖ + ‖K0 σ‖)) ^ 2 =
        ρc ^ 2 * ∑ σ, (‖Ψ0 σ‖ + ‖H0 σ‖ + ‖K0 σ‖) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by ring
    rw [e, mul_pow]
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (sq_nonneg ρc)
  have hcb : 0 ≤ cbar := hc0.trans hcc
  have hn : ‖Ψt‖ + ‖Ψ0‖ ≤ 2 * (ρc * D) := by
    rw [hcons]
    have h1 : ‖Ψ0‖ ≤ D := by linarith [norm_nonneg H0, norm_nonneg K0]
    have h2 : D ≤ ρc * D := by nlinarith
    linarith
  have hεt : 0 ≤ ε * t := mul_nonneg hε ht
  have step : ε ^ 2 + (‖Ψt‖ + ‖Ψ0‖) * (c * ε * t) +
      (∑ σ, (ρc * (‖Ψ0 σ‖ + ‖H0 σ‖ + ‖K0 σ‖)) ^ 2) *
        ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + 1) * T) * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3) ≤
      ε ^ 2 + (‖Ψt‖ + ‖Ψ0‖) * (cbar * ε * t) + (ρc * D) ^ 2 *
        ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + 1) * T) * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3) := by
    have h1 : (‖Ψt‖ + ‖Ψ0‖) * (c * ε * t) ≤ (‖Ψt‖ + ‖Ψ0‖) * (cbar * ε * t) := by
      have : c * ε * t ≤ cbar * ε * t := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right hcc hεt
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h2 := mul_le_mul_of_nonneg_right hsum hB
    linarith
  exact step.trans (le_spin_form hN0 hcb hn hε hε1 ht hK)

end Form

/-! ## The constants -/

section Constants

/-- The constant of `prop:free-dyn` with internal spin, without clamped nuclei: the constant of
`dynConst` with the grid constants at the unit data `(1, Λ, Λ, Λ²)` scaled by `(c′ D)²`
(`Λ = domConst`, `c′ = regConst`). -/
noncomputable def freeDynConstSpinNBO (sys : CoulombSystem eta ν) (V : ℝ) (F : 𝓢(E3, ℂ))
    (Dbar Cbar D : ℝ) : ℝ :=
  dynConst (spinScale (regConst sys * D) (gridConstsSharp_gLU sys V
    molecularCanonicalUnitHardyConstant (obsMomC (ftDecay F)) (obsMomC (ftDecay F))
    (obsMomD2 (ftDecay F)) (obsMomD4 (ftDecay F)) 1
    (domConst sys.charge (zeroWeight sys / 4) Dbar Cbar)
    (domConst sys.charge (zeroWeight sys / 4) Dbar Cbar)
    (domConst sys.charge (zeroWeight sys / 4) Dbar Cbar ^ 2)))
    (regConst sys * D) (obsTailC (ftDecay F) 5)
    ((Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2))

/-- The constant of `prop:free-dyn` with internal spin and clamped nuclei (a cutoff flat near the
nuclei at distance `δ`). -/
noncomputable def freeDynConstSpinBO (sys : CoulombSystem eta ν) (V : ℝ) (F : 𝓢(E3, ℂ))
    (Dbar Cbar δ D : ℝ) : ℝ :=
  dynConst (spinScale (regConstN sys * D) (gridConstsSharp_gLU sys V
    molecularCanonicalUnitHardyConstant (obsMomC (ftDecay F)) (obsMomC (ftDecay F))
    (obsMomD2 (ftDecay F)) (obsMomD4 (ftDecay F)) 1
    (domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) Dbar Cbar δ)
    (domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) Dbar Cbar δ)
    (domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) Dbar Cbar δ ^ 2)))
    (regConstN sys * D) (obsTailC (ftDecay F) 5)
    ((Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2))

lemma freeDynConstSpinBO_sysAt (sys : CoulombSystem eta ν) (P : ν → E3) (L V : ℝ)
    (F : 𝓢(E3, ℂ)) (Dbar Cbar δ D : ℝ) :
    freeDynConstSpinBO (sysAt sys P L) V F Dbar Cbar δ D =
      freeDynConstSpinBO sys V F Dbar Cbar δ D :=
  rfl

end Constants

/-! ## The endpoints at a fixed cell -/

section Endpoints

/-- **`prop:free-dyn` with internal spin, without clamped nuclei**, from the Hamiltonian relations
of each spin component: for a mass-weighted cutoff with bounds `D̄`, `C̄`, the leakages summed over
the spin components at most `ε² ≤ 1`, and `‖Ψ₀‖ + ‖H_∞Ψ₀‖ + ‖H_∞²Ψ₀‖ ≤ D` (Hilbert norms of the
spin-inclusive space),
`|Σ_σ ⟨Ψ_σ(t), f(x_a) Ψ_σ(t)⟩ - Σ_σ ⟨ψ_{g,σ}(t), O_g ψ_{g,σ}(t)⟩| ≤ C [K⁻⁵ + t K⁻³] + C (1 + t) ε`,
`C = freeDynConstSpinNBO sys V_θ F D̄ C̄ D`. -/
theorem free_dyn_nbo_spin_endpoint [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ}
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
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg : ς → EuclideanSpace ℂ (RCfg eta m) := fun σ => Ug t (idft (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (Ψ 0 σ)))))
      ‖((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
          ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ‖ ≤
        freeDynConstSpinNBO sys (tv R θ) F Dbar Cbar D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstSpinNBO sys (tv R θ) F Dbar Cbar D * (1 + t) * ε := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hc₀ := norm_zeroModeShift_le sys hL2 hθ hR
  have hdom := fun σ => cut_state_domain_reg sys hL hR0 hρ hone P hP hpos X hret (hHam 0 σ)
    (hH1 σ) hc₀
  choose h₀ h₁ hd0 hd1 n0 n1 n2 using hdom
  have hDb : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  have hCb : 0 ≤ Cbar := X.C_nonneg.trans hCbar
  have hc0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  set Λ := domConst sys.charge (zeroWeight sys / 4) Dbar Cbar with hΛ
  have hΛ1 : 1 ≤ Λ := one_le_domConst sys.charge hc0 hDb hCb
  have hΛX : domConst sys.charge (zeroWeight sys / 4) X.D X.C ≤ Λ :=
    domConst_mono sys.charge hDbar hCbar
  have hΛX0 : 0 ≤ domConst sys.charge (zeroWeight sys / 4) X.D X.C :=
    le_trans zero_le_one (one_le_domConst sys.charge hc0 X.D_nonneg X.C_nonneg)
  have hreg := one_le_regConst sys
  have hNσ : ∀ σ, 0 ≤ regConst sys * (‖Ψ 0 σ‖ + ‖HΨ 0 σ‖ + ‖Kψ σ‖) := fun σ => by positivity
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_grid_spin sys hL2 hθ hR
    hR0 hρ hone P hP hpos X.toCutoff hret hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0
    hleak1 hd0 hd1 (N := fun σ => regConst sys * (‖Ψ 0 σ‖ + ‖HΨ 0 σ‖ + ‖Kψ σ‖)) (Λ := Λ) hNσ n0
    (fun σ => (n1 σ).trans (mul_le_mul_of_nonneg_right hΛX (hNσ σ)))
    (fun σ => (n2 σ).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hΛX0 hΛX 2) (hNσ σ))) a hf0 hf1 F hFf hfR hRL m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ K ψg
  refine le_trans hbound ?_
  have hV := hθ.tv_nonneg
  obtain ⟨hC6, hD2, hD4, hT⟩ := obs_consts_nonneg F
  obtain ⟨hA1, hA2, hA3⟩ := gridConstsSharp_gLU_nonneg sys (V := tv R θ) (s0 := 1) (hu := Λ)
    (hs := Λ) (hv := Λ ^ 2) hV hardyUnit_nonneg hC6 hC6 hD2 hD4 zero_le_one (by linarith)
    (by linarith) (by positivity)
  have hcomm : X.toCutoff.commConst ≤ (Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2) := by
    unfold Cutoff.commConst
    have : X.toCutoff.D1 + X.toCutoff.D2 / 2 ≤ Dbar + Dbar / 2 := by
      have e1 : X.toCutoff.D1 = X.D := rfl
      have e2 : X.toCutoff.D2 = X.D := rfl
      rw [e1, e2]
      linarith
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have hcomm0 : 0 ≤ X.toCutoff.commConst := by
    unfold Cutoff.commConst
    have e1 : X.toCutoff.D1 = X.D := rfl
    have e2 : X.toCutoff.D2 = X.D := rfl
    rw [e1, e2]
    have := X.D_nonneg
    positivity
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  exact spin_final_le (norm_conserved_spin sys P hψd hHam t) hreg hD hA1 hA2 hA3 hT hcomm0 hcomm
    hε hε1 ht hKpos

/-- **`prop:free-dyn` with internal spin and clamped nuclei**, from the Hamiltonian relations of
each spin component: for a mass-weighted cutoff flat near the nuclei at distance `δ`, with bounds
`D̄`, `C̄`, the leakages summed over the spin components at most `ε² ≤ 1`, and
`‖Ψ₀‖ + ‖H_∞Ψ₀‖ + ‖H_∞²Ψ₀‖ ≤ D`: the bound `C [K⁻⁵ + t K⁻³] + C (1 + t) ε`,
`C = freeDynConstSpinBO sys V_θ F D̄ C̄ δ D`. -/
theorem free_dyn_bo_spin_endpoint (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg : ς → EuclideanSpace ℂ (RCfg eta m) := fun σ => Ug t (idft (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (Ψ 0 σ)))))
      ‖((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
          ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ‖ ≤
        freeDynConstSpinBO sys (tv R θ) F Dbar Cbar δ D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstSpinBO sys (tv R θ) F Dbar Cbar δ D * (1 + t) * ε := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hc₀ := norm_zeroModeShift_le sys hL2 hθ hR
  have hdom := fun σ => cut_state_domain_reg_nuc sys hL hR0 hρ hone P hP hpos X hret hδ hflat
    (hHam 0 σ) (hH1 σ) hc₀
  choose h₀ h₁ hd0 hd1 n0 n1 n2 using hdom
  have hDb : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  have hCb : 0 ≤ Cbar := X.C_nonneg.trans hCbar
  have hc0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  set Λ := domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) Dbar Cbar δ with hΛ
  have hΛ1 : 1 ≤ Λ := one_le_domConstN _ _ hc0 hDb hCb
  have hΛX : domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) X.D X.C δ ≤ Λ :=
    domConstN_mono _ _ _ hDbar hCbar
  have hΛX0 : 0 ≤ domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) X.D X.C δ :=
    le_trans zero_le_one (one_le_domConstN _ _ hc0 X.D_nonneg X.C_nonneg)
  have hreg := one_le_regConstN sys
  have hNσ : ∀ σ, 0 ≤ regConstN sys * (‖Ψ 0 σ‖ + ‖HΨ 0 σ‖ + ‖Kψ σ‖) := fun σ => by positivity
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_grid_spin sys hL2 hθ hR
    hR0 hρ hone P hP hpos X.toCutoff hret hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0
    hleak1 hd0 hd1 (N := fun σ => regConstN sys * (‖Ψ 0 σ‖ + ‖HΨ 0 σ‖ + ‖Kψ σ‖)) (Λ := Λ) hNσ n0
    (fun σ => (n1 σ).trans (mul_le_mul_of_nonneg_right hΛX (hNσ σ)))
    (fun σ => (n2 σ).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hΛX0 hΛX 2) (hNσ σ))) a hf0 hf1 F hFf hfR hRL m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ K ψg
  refine le_trans hbound ?_
  have hV := hθ.tv_nonneg
  obtain ⟨hC6, hD2, hD4, hT⟩ := obs_consts_nonneg F
  obtain ⟨hA1, hA2, hA3⟩ := gridConstsSharp_gLU_nonneg sys (V := tv R θ) (s0 := 1) (hu := Λ)
    (hs := Λ) (hv := Λ ^ 2) hV hardyUnit_nonneg hC6 hC6 hD2 hD4 zero_le_one (by linarith)
    (by linarith) (by positivity)
  have hcomm : X.toCutoff.commConst ≤ (Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2) := by
    unfold Cutoff.commConst
    have : X.toCutoff.D1 + X.toCutoff.D2 / 2 ≤ Dbar + Dbar / 2 := by
      have e1 : X.toCutoff.D1 = X.D := rfl
      have e2 : X.toCutoff.D2 = X.D := rfl
      rw [e1, e2]
      linarith
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have hcomm0 : 0 ≤ X.toCutoff.commConst := by
    unfold Cutoff.commConst
    have e1 : X.toCutoff.D1 = X.D := rfl
    have e2 : X.toCutoff.D2 = X.D := rfl
    rw [e1, e2]
    have := X.D_nonneg
    positivity
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  exact spin_final_le (norm_conserved_spin sys P hψd hHam t) hreg hD hA1 hA2 hA3 hT hcomm0 hcomm
    hε hε1 ht hKpos

end Endpoints

/-! ## One constant for all cells -/

section Uniform

/-- **`prop:free-dyn` with internal spin, without clamped nuclei, uniform in `L`**: the statement
of `free_dyn_nbo_uniform` for the spin-inclusive state, with the leakage summed over the spin
components and `‖Ψ₀‖ + ‖H_∞Ψ₀‖ + ‖H_∞²Ψ₀‖ ≤ D`; one constant
`C = freeDynConstSpinNBO sys V F D₈ C₈ D` for every `L ≥ L₀`. -/
theorem free_dyn_nbo_spin_uniform [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ Rf V : ℝ}
    (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) {L R : ℝ} {θ : ℝ → ℝ} (hL : freeDynL0 R0 ρ Rf ≤ L)
    (hθ : Profile R θ) (hR : R ≤ L / 2) (hV : tv R θ = V)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t,
      ∑ σ, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r}, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2}, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (pos_of_freeDynL0 hL) (continuous_of_schwartz F hFf) hfR
        (two_Rf_lt_of_freeDynL0 hL)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg : ς → EuclideanSpace ℂ (RCfg eta m) := fun σ => Ug t (idft (regCoeff m
        ((molecularPositionSynthesis eta).symm
          ((quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
            (pos_of_freeDynL0 hL) (Ψ 0 σ)))))
      ‖((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
          ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ‖ ≤
        freeDynConstSpinNBO sys V F (quadCutoff8 sys.one_le_mass).D
            (quadCutoff8 sys.one_le_mass).C D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstSpinNBO sys V F (quadCutoff8 sys.one_le_mass).D
            (quadCutoff8 sys.one_le_mass).C D * (1 + t) * ε := by
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
  have hSB : {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r ∧ massQ sys.mass r ≤ 2 * (L / 8) ^ 2}
      ⊆ {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2}ᶜ := fun r hr h => by
    simp only [Set.mem_setOf_eq] at hr h
    linarith [hr.1]
  have hc : {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2}ᶜ =
      {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r} := by
    ext r
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  have hret : ∀ r, (quadCutoffL sys.one_le_mass h8).χ r ≠ 0 →
      ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ := fun r hr i =>
    (quadCutoffL_ret sys.one_le_mass h8 r hr i).trans (ret_of_freeDynL0 hL)
  exact free_dyn_nbo_spin_endpoint sys hL2 hθ hR hR0 hρ hone P hP hpos
    (quadCutoffL sys.one_le_mass h8) hret (quadCutoffL_D_le sys.one_le_mass h8)
    (quadCutoffL_C_le sys.one_le_mass h8) hS hB (quadCutoffL_one sys.one_le_mass h8)
    hSB (fun r hr a => (quadCutoffL_derivs sys.one_le_mass h8 r hr a).1)
    (fun r hr a => (quadCutoffL_derivs sys.one_le_mass h8 r hr a).2) hψd hHam hgrad ht hε hε1
    (fun s hs => by rw [hc]; exact hleak0 s hs) hleak1 hH1 hD a hf0 hf1 F hFf hfR
    (two_Rf_lt_of_freeDynL0 hL) m hκ hm hK

/-- **`prop:free-dyn` with internal spin and clamped nuclei, uniform in `L`** (equal masses
`m_i = m₀ ≥ 1`): the statement of `free_dyn_bo_uniform` for the spin-inclusive state, with the
leakage summed over the spin components and `‖Ψ₀‖ + ‖H_∞Ψ₀‖ + ‖H_∞²Ψ₀‖ ≤ D`; one constant
`C = freeDynConstSpinBO sys V F D₁₆ C₁₆ δ D` for every
`L ≥ L₀ = max(16, 2R_f + 1, 16(R₀ + ρ + δ))`. -/
theorem free_dyn_bo_spin_uniform (sys : CoulombSystem eta ν) {m₀ : ℝ}
    (hm : ∀ i, sys.mass i = m₀) (hm0 : 1 ≤ m₀) {R0 ρ Rf δ L V : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hδ : 0 < δ) (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0) {R : ℝ} {θ : ℝ → ℝ}
    (hL : freeDynBOL0 R0 ρ Rf δ ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hV : tv R θ = V)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t,
      ∑ σ, ∫ r in {r | ∃ i, L / 16 ≤ ‖particle r i‖}, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in {r | (∃ i, L / 16 ≤ ‖particle r i‖) ∧
      ∀ i, ‖particle r i‖ ≤ L / 8}, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {Kψ : FreeSpinL2 eta ς} (hH1 : ∀ σ, HasFreeHamiltonian sys P (HΨ 0 σ) (Kψ σ)) {D : ℝ}
    (hD : ‖Ψ 0‖ + ‖HΨ 0‖ + ‖Kψ‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm8 : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (pos_of_freeDynBOL0 hL) (continuous_of_schwartz F hFf) hfR
        (two_Rf_lt_of_freeDynBOL0 hL)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg : ς → EuclideanSpace ℂ (RCfg eta m) := fun σ => Ug t (idft (regCoeff m
        ((molecularPositionSynthesis eta).symm
          ((prodCutoffL hm hm0 (sixteen_le_of_freeDynBOL0 hL)).toCutoff.chiW.cutL2
            (pos_of_freeDynBOL0 hL) (Ψ 0 σ)))))
      ‖((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
          ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ‖ ≤
        freeDynConstSpinBO sys V F (prodCutoff16 hm hm0).D (prodCutoff16 hm hm0).C δ D *
            ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstSpinBO sys V F (prodCutoff16 hm hm0).D (prodCutoff16 hm hm0).C δ D *
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
  have hret : ∀ r, (prodCutoffL hm hm0 h16).χ r ≠ 0 →
      ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ := fun r hr i =>
    (prodCutoffL_ret hm hm0 h16 r hr i).trans (ret_of_freeDynBOL0 hδ.le hL)
  have hflat : IsFlatNear (prodCutoffL hm hm0 h16).χ P δ :=
    prodCutoffL_isFlatNear hm hm0 h16 P (flat_of_freeDynBOL0 hρ hL hP)
  exact free_dyn_bo_spin_endpoint (sysAt sys P L) hL2 hθ hR hR0 hρ hone P hP (fun l => rfl)
    (prodCutoffL hm hm0 h16) hret hδ hflat (prodCutoffL_D_le hm hm0 h16)
    (prodCutoffL_C_le hm hm0 h16) hS hB (prodCutoffL_one hm hm0 h16) hSB
    (fun r hr a => (prodCutoffL_derivs hm hm0 h16 r hr a).1)
    (fun r hr a => (prodCutoffL_derivs hm hm0 h16 r hr a).2) hψd hHam hgrad ht hε hε1
    (fun s hs => by rw [hc]; exact hleak0 s hs) hleak1 hH1 hD a hf0 hf1 F hFf hfR
    (two_Rf_lt_of_freeDynBOL0 hL) m hκ hm8 hK

end Uniform

end FreeBoundary
