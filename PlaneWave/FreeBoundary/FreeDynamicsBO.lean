import PlaneWave.FreeBoundary.ProductCutoffRegions

/-!
# Clamped nuclei, part 10: `prop:free-dyn` with clamped nuclei

`prop:free-dyn` for a system with clamped nuclei, without the domain hypothesis: for a
mass-weighted cutoff in the retained region that is flat near the nuclei, the domain condition
(H_dom) follows from `H_∞ ψ(0) = H(0)`, `H_∞ H(0) = k` (`cut_state_domain_reg_nuc`), and
`free_dyn_endpoint` gives the bound `C [K⁻⁵ + t K⁻³] + C (1 + t) ε` with
`C = freeDynConstBO`, a function of the system, `V_θ`, the observable, the cutoff bounds
`D̄`, `C̄`, the flatness radius `δ` and the data bound `‖ψ₀‖ + ‖H_∞ψ₀‖ + ‖H_∞²ψ₀‖ ≤ D`.

* `one_le_regConstN`, `one_le_domConstN`, `domConstN_mono`;
* `freeDynConstBO`, **`free_dyn_grid_bo`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLref)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

lemma one_le_regConstN (sys : CoulombSystem eta ν) : 1 ≤ regConstN sys := by
  have h := relConstN_nonneg sys
  unfold regConstN
  have : 0 ≤ relConstN sys * (2 * (Fintype.card (Fin eta × Fin 3) : ℝ) +
      (Fintype.card (Fin eta × Fin 3) : ℝ) ^ 2 + (Fintype.card (FiniteElectronPair eta) : ℝ)) := by
    positivity
  linarith

lemma one_le_domConstN (q : Fin eta → ℝ) (Zc : ν → ℝ) {c₀ D C δ : ℝ} (hc₀ : 0 ≤ c₀)
    (hD : 0 ≤ D) (hC : 0 ≤ C) : 1 ≤ domConstN q Zc c₀ D C δ := by
  have h := domConstN_nonneg q Zc (δ := δ) (le_refl (0 : ℝ)) hD hC
  have e : domConstN q Zc c₀ D C δ = c₀ + domConstN q Zc 0 D C δ := by
    unfold domConstN
    ring
  have h1 : 1 ≤ domConstN q Zc 0 D C δ := by
    unfold domConstN
    have h2 : 0 ≤ pairWeight q * C := mul_nonneg (pairWeight_nonneg q) hC
    have h3 : 0 ≤ (∑ i : Fin eta, ∑ l : ν, |q i * Zc l|) * (D / δ ^ 2) :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (div_nonneg hD (sq_nonneg _))
    have h4 : (0 : ℝ) ≤ (Fintype.card (Fin eta × Fin 3) : ℝ) := Nat.cast_nonneg _
    have : 0 ≤ 6 * (1 + (Fintype.card (Fin eta × Fin 3) : ℝ)) ^ 2 * D := by positivity
    nlinarith [mul_nonneg h4 h3]
  linarith

lemma domConstN_mono (q : Fin eta → ℝ) (Zc : ν → ℝ) (c₀ : ℝ) {D D' C C' δ : ℝ} (hDD : D ≤ D')
    (hCC : C ≤ C') : domConstN q Zc c₀ D C δ ≤ domConstN q Zc c₀ D' C' δ := by
  unfold domConstN
  have h1 : 0 ≤ (∑ i : Fin eta, ∑ l : ν, |q i * Zc l|) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h4 : (0 : ℝ) ≤ (Fintype.card (Fin eta × Fin 3) : ℝ) := Nat.cast_nonneg _
  have hq : 0 ≤ pairWeight q := pairWeight_nonneg q
  have e1 : 6 * (1 + (Fintype.card (Fin eta × Fin 3) : ℝ)) ^ 2 * D ≤
      6 * (1 + (Fintype.card (Fin eta × Fin 3) : ℝ)) ^ 2 * D' :=
    mul_le_mul_of_nonneg_left hDD (by positivity)
  have e2 : pairWeight q * C ≤ pairWeight q * C' := mul_le_mul_of_nonneg_left hCC hq
  have e3 : D / δ ^ 2 ≤ D' / δ ^ 2 := div_le_div_of_nonneg_right hDD (sq_nonneg _)
  have e4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e3 h1) h4
  linarith

/-- The constant of `prop:free-dyn` with clamped nuclei. -/
noncomputable def freeDynConstBO (sys : CoulombSystem eta ν) (V : ℝ) (F : 𝓢(E3, ℂ))
    (Dbar Cbar δ D : ℝ) : ℝ :=
  freeDynConst sys V F Dbar
    (domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) Dbar Cbar δ ^ 2 *
      (regConstN sys * D))

/-- **`prop:free-dyn` with clamped nuclei, without the domain hypothesis.** For a mass-weighted
cutoff in the retained region, flat near the nuclei (`IsFlatNear`, radius `δ`), with derivative
and cancellation bounds `D̄`, `C̄`, and the free-space solution with `H_∞ H(0) = k`,
`‖ψ(0)‖ + ‖H(0)‖ + ‖k‖ ≤ D`, leakage `ε ≤ 1`:
`|⟨ψ(t), χ(x_a) ψ(t)⟩ - ⟨ψ_g(t), O_g ψ_g(t)⟩| ≤ C [K⁻⁵ + t K⁻³] + C (1 + t) ε`,
`C = freeDynConstBO sys V_θ F D̄ C̄ δ D`. -/
theorem free_dyn_grid_bo (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
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
      let φ₀ := X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConstBO sys (tv R θ) F Dbar Cbar δ D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstBO sys (tv R θ) F Dbar Cbar δ D * (1 + t) * ε := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hc₀ := norm_zeroModeShift_le sys hL2 hθ hR
  obtain ⟨h₀, h₁, hd0, hd1, n0, n1, n2⟩ := cut_state_domain_reg_nuc sys hL hR0 hρ hone P hP hpos X
    hret hδ hflat (hHam 0) hH1 hc₀
  -- the data bound `𝒟 = Λ̄² C′_sys D`
  have hc0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have hD0 : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  have hC0 : 0 ≤ Cbar := X.C_nonneg.trans hCbar
  set Λ := domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) X.D X.C δ with hΛ
  set Λb := domConstN sys.charge sys.nuclei.charge (zeroWeight sys / 4) Dbar Cbar δ with hΛb
  have hΛ1 : 1 ≤ Λ := one_le_domConstN _ _ hc0 X.D_nonneg X.C_nonneg
  have hΛΛ : Λ ≤ Λb := domConstN_mono _ _ _ hDbar hCbar
  have hR1 := one_le_regConstN sys
  set T := ‖ψ 0‖ + ‖H 0‖ + ‖k‖ with hT
  have hT0 : 0 ≤ T := by positivity
  have hRT : regConstN sys * T ≤ regConstN sys * D := mul_le_mul_of_nonneg_left hD (by linarith)
  have hRT0 : 0 ≤ regConstN sys * T := by positivity
  set 𝒟 := Λb ^ 2 * (regConstN sys * D) with h𝒟
  have hΛ2 : Λ ^ 2 ≤ Λb ^ 2 := pow_le_pow_left₀ (by linarith) hΛΛ 2
  have hb1 : 1 ≤ Λb ^ 2 := one_le_pow₀ (by linarith)
  have hRD0 : 0 ≤ regConstN sys * D := hRT0.trans hRT
  have key : regConstN sys * T ≤ 𝒟 := by
    calc regConstN sys * T ≤ regConstN sys * D := hRT
      _ = 1 * (regConstN sys * D) := (one_mul _).symm
      _ ≤ 𝒟 := mul_le_mul_of_nonneg_right hb1 hRD0
  have hψ0 : ‖ψ 0‖ ≤ 𝒟 := by
    have : ‖ψ 0‖ ≤ regConstN sys * T := by
      calc ‖ψ 0‖ ≤ T := by rw [hT]; linarith [norm_nonneg (H 0), norm_nonneg k]
        _ = 1 * T := (one_mul _).symm
        _ ≤ regConstN sys * T := mul_le_mul_of_nonneg_right hR1 hT0
    exact this.trans key
  have hn1 : ‖h₀‖ ≤ 𝒟 := by
    refine n1.trans (mul_le_mul ?_ hRT hRT0 (by positivity))
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Λb) (by linarith : (0 : ℝ) ≤ Λb - 1)]
  have hn2 : ‖h₁‖ ≤ 𝒟 := n2.trans (mul_le_mul hΛ2 hRT hRT0 (by positivity))
  exact free_dyn_endpoint sys hL2 hθ hR hR0 hρ hone P hP hpos X.toCutoff hret hDbar hDbar hSm hBm
    hχB hSB hdS hd2S hψd hHam hgrad ht hε hε1 hleak0 hleak1 hd0 hd1 hψ0 (n0.trans key) hn1 hn2 a
    hf0 hf1 F hFf hfR hRL m hκ hm hK

end FreeBoundary
