import PlaneWave.FreeBoundary.SpinFreeStep

/-!
# Spin, part 2: `prop:free-dyn` with internal spin, the two steps composed

The grid step acts on each spin component with one and the same grid flow `U_g(t)`
(`grid_dyn_sharp_gLU_of_propagator`). Its observable error is a quadratic form of the component:
scaling the component by `c` scales the error by `c²` and the data by `c` (`gridErr_smul`). So the
bound of the grid step at the unit data `(1, Λ, Λ²)` gives `N_σ² B₁` for a component with data
`(N_σ, Λ N_σ, Λ² N_σ)` (`norm_le_sq_mul_of_unit`), and the components add to `(Σ_σ N_σ²) B₁`.
With the free-space step with spin (`free_dyn_torus_spin`):
`|Σ_σ ⟨Ψ_σ(t), χ(x_a) Ψ_σ(t)⟩ - Σ_σ ⟨ψ_{g,σ}(t), O_g ψ_{g,σ}(t)⟩|
  ≤ ε² + (‖Ψ(t)‖ + ‖Ψ(0)‖) C ε t + (Σ_σ N_σ²) B₁`,
`B₁ = (A₁ + (A₃ 3^{5/2} + 1) C_{χ,5}) K⁻⁵ + A₂ t K⁻³` with `(A₁, A₂, A₃) = gridConstsSharp_gLU`
at the data `(1, Λ, Λ, Λ²)`. No factor depends on the number of spin components.

* `gridConstsSharp_gLU_nonneg`: the grid constants are nonnegative;
* `norm_le_sq_mul_of_unit`: from the unit data to `N²`;
* `gridErr_smul`: the grid observable error is quadratic;
* **`free_dyn_grid_spin`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLref)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The grid constants are nonnegative -/

lemma gridConstsSharp_gLU_zero (sys : CoulombSystem eta ν) (V Hunit Cχ CO D2 D4 : ℝ) :
    gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 0 0 0 0 = (0, 0, 0) := by
  simp [gridConstsSharp_gLU, gLtailMU]

lemma gridConstsSharp_gLU_nonneg (sys : CoulombSystem eta ν)
    {V Hunit Cχ CO D2 D4 s0 hu hs hv : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ Hunit) (hCχ : 0 ≤ Cχ)
    (hCO : 0 ≤ CO) (hD2 : 0 ≤ D2) (hD4 : 0 ≤ D4) (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) (h2 : 0 ≤ hs)
    (h3 : 0 ≤ hv) :
    0 ≤ (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).1 ∧
      0 ≤ (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).2.1 ∧
      0 ≤ (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).2.2 := by
  obtain ⟨m1, m2, m3⟩ := gridConstsSharp_gLU_mono_data sys hV hH hCχ hCO hD2 hD4 le_rfl le_rfl
    le_rfl le_rfl h0 h1 h2 h3
  rw [gridConstsSharp_gLU_zero] at m1 m2 m3
  exact ⟨m1, m2, m3⟩

/-! ## Homogeneity -/

/-- **From the unit data to `N²`.** Let `err` be quadratic under real scaling and `Rel` be
preserved by scaling. If `‖err f‖ ≤ B` whenever `Rel f h₀`, `Rel h₀ h₁`, `‖f‖ ≤ 1`, `‖h₀‖ ≤ Λ`,
`‖h₁‖ ≤ Λ²`, then `‖err f‖ ≤ N² B` whenever `‖f‖ ≤ N`, `‖h₀‖ ≤ Λ N`, `‖h₁‖ ≤ Λ² N`. -/
lemma norm_le_sq_mul_of_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Rel : E → E → Prop) (hRel : ∀ (c : ℂ) f h, Rel f h → Rel (c • f) (c • h))
    (err : E → ℂ) (hscale : ∀ (c : ℝ) f, err ((c : ℂ) • f) = ((c ^ 2 : ℝ) : ℂ) * err f)
    {Λ B : ℝ}
    (hunit : ∀ f h₀ h₁, Rel f h₀ → Rel h₀ h₁ → ‖f‖ ≤ 1 → ‖h₀‖ ≤ Λ → ‖h₁‖ ≤ Λ ^ 2 →
      ‖err f‖ ≤ B)
    {f h₀ h₁ : E} (hf : Rel f h₀) (hh : Rel h₀ h₁) {N : ℝ} (hN : 0 ≤ N) (n0 : ‖f‖ ≤ N)
    (n1 : ‖h₀‖ ≤ Λ * N) (n2 : ‖h₁‖ ≤ Λ ^ 2 * N) : ‖err f‖ ≤ N ^ 2 * B := by
  rcases hN.eq_or_lt with h0 | hpos
  · have hf0 : f = 0 := norm_le_zero_iff.mp (by rw [h0]; exact n0)
    have h := hscale 0 f
    have e1 : ((0 : ℝ) : ℂ) • f = 0 := by simp
    have e2 : (((0 : ℝ) ^ 2 : ℝ) : ℂ) * err f = 0 := by simp
    rw [e1, e2] at h
    rw [hf0, h, ← h0]
    simp
  · have hc : 0 < N⁻¹ := inv_pos.mpr hpos
    have hns : ∀ v : E, ‖((N⁻¹ : ℝ) : ℂ) • v‖ = N⁻¹ * ‖v‖ := fun v => by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    have h1 := hunit (((N⁻¹ : ℝ) : ℂ) • f) (((N⁻¹ : ℝ) : ℂ) • h₀) (((N⁻¹ : ℝ) : ℂ) • h₁)
      (hRel _ _ _ hf) (hRel _ _ _ hh)
      (by rw [hns, inv_mul_le_iff₀ hpos, mul_one]; exact n0)
      (by rw [hns, inv_mul_le_iff₀ hpos]; linarith)
      (by rw [hns, inv_mul_le_iff₀ hpos]; linarith)
    rw [hscale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    have e : ‖err f‖ = N ^ 2 * ((N⁻¹) ^ 2 * ‖err f‖) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg N)

/-- **The grid observable error is quadratic.** -/
lemma gridErr_smul {m : ℕ} (U : MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta)
    (Ug : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)) (a : Fin eta)
    (χ : C(UnitAddTorus (Fin 3), ℂ)) (c : ℝ) (φ : MolecularPositionL2 eta) :
    ⟪U ((c : ℂ) • φ), mulCLM (regFun a χ) (U ((c : ℂ) • φ))⟫_ℂ -
        ⟪Ug (idft (regCoeff m ((molecularPositionSynthesis eta).symm ((c : ℂ) • φ)))),
          posObs a (chiRefl χ)
            (Ug (idft (regCoeff m ((molecularPositionSynthesis eta).symm ((c : ℂ) • φ)))))⟫_ℂ =
      ((c ^ 2 : ℝ) : ℂ) * (⟪U φ, mulCLM (regFun a χ) (U φ)⟫_ℂ -
        ⟪Ug (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ))),
          posObs a (chiRefl χ)
            (Ug (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ))))⟫_ℂ) := by
  simp only [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  push_cast
  ring

/-! ## The two steps composed -/

/-- **`prop:free-dyn` with internal spin, the two steps composed** (`L ≥ 2π`, `L > 2R_f`; any
system, (H_dom) for each spin component). For a solution curve `Ψ` in `L²(ℝ^{3η}) ⊗ ℂ^ς` with the
leakages summed over the spin components at most `ε²`, and torus data
`H_L φ_σ = h₀,σ`, `H_L h₀,σ = h₁,σ` of the components `φ_σ = T(χ Ψ_σ(0))` with
`‖φ_σ‖ ≤ N_σ`, `‖h₀,σ‖ ≤ Λ N_σ`, `‖h₁,σ‖ ≤ Λ² N_σ`, the grid flow `U_g` (one for all components)
satisfies
`|Σ_σ ⟨Ψ_σ(t), f(x_a) Ψ_σ(t)⟩ - Σ_σ ⟨ψ_{g,σ}(t), O_g ψ_{g,σ}(t)⟩|
  ≤ ε² + (‖Ψ(t)‖ + ‖Ψ(0)‖) C ε t + (Σ_σ N_σ²) ((A₁ + (A₃ 3^{5/2} + 1) C_{χ,5}) K⁻⁵ + A₂ t K⁻³)`,
`(A₁, A₂, A₃)` the grid constants at the unit data `(1, Λ, Λ, Λ²)`. -/
theorem free_dyn_grid_spin (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
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
    {h₀ h₁ : ς → MolecularPositionL2 eta}
    (hdom0 : ∀ σ, HasGLHamiltonian sys L θ
      (X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (Ψ 0 σ)) (h₀ σ))
    (hdom1 : ∀ σ, HasGLHamiltonian sys L θ (h₀ σ) (h₁ σ))
    {N : ς → ℝ} {Λ : ℝ} (hN : ∀ σ, 0 ≤ N σ)
    (hn0 : ∀ σ, ‖X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (Ψ 0 σ)‖ ≤ N σ)
    (hn1 : ∀ σ, ‖h₀ σ‖ ≤ Λ * N σ) (hn2 : ∀ σ, ‖h₁ σ‖ ≤ Λ ^ 2 * N σ)
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
      let A := gridConstsSharp_gLU sys (tv R θ) molecularCanonicalUnitHardyConstant
        (obsMomC (ftDecay F)) (obsMomC (ftDecay F)) (obsMomD2 (ftDecay F)) (obsMomD4 (ftDecay F))
        1 Λ Λ (Λ ^ 2)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg : ς → EuclideanSpace ℂ (RCfg eta m) := fun σ => Ug t (idft (regCoeff m
        ((molecularPositionSynthesis eta).symm
          (X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (Ψ 0 σ)))))
      ‖((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
          ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ‖ ≤
        ε ^ 2 + (‖Ψ t‖ + ‖Ψ 0‖) * (X.commConst * ε * t) +
          (∑ σ, N σ ^ 2) * ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + 1) * obsTailC (ftDecay F) 5) *
            (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3) := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hL1 : 1 ≤ L := le_trans (by linarith [Real.two_le_pi]) hL2
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, -⟩ := exists_gLPropagator sys hL hθ hR
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ :=
    grid_dyn_sharp_gLU_of_propagator sys hL2 hθ hR U h0 hgraph hderiv m κ hκ
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ A K ψg
  have hχf : ∀ x : MolecularPositionTorus eta,
      χ (molecularPositionParticle a x) = (f (particle (cellCoord L x) a) : ℂ) :=
    cellObs_particle _ _ _ _ a
  have hreal := real_of_cell hχf
  have hfm : Measurable f := (continuous_of_schwartz F hFf).measurable
  have hχom : Measurable fun r : Rcfg eta => f (particle r a) :=
    hfm.comp (continuous_particle a).measurable
  have hG : ∀ x, regFun a χ x = ((fun r : Rcfg eta => f (particle r a)) (cellCoord L x) : ℂ) :=
    fun x => hχf x
  -- the free-space step with spin
  obtain ⟨-, hobs⟩ := free_dyn_torus_spin sys hL hθ hR0 hρ hone P hP hpos U h0 hadd hcont hderiv X
    hret hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1
    (χo := fun r => f (particle r a)) (fun r => hf0 _) (fun r => hf1 _) hχom (regFun a χ) hG
  -- the decay of the observable
  have hFe : (fun y => (f y : ℂ)) = (F : E3 → ℂ) := by
    funext y
    rw [hFf]
  have hcell : ∀ s, χ s = (fun y => (f y : ℂ)) (cellRep L s) := fun s => hχf (fun p => s p.2)
  have hsupp : ∀ y : E3, (fun y => (f y : ℂ)) y ≠ 0 → ∀ c, |y c| < L / 2 := by
    intro y hy c
    have hfy : f y ≠ 0 := fun h => hy (by simp [h])
    have := abs_coord_le_norm y c
    have := hfR y hfy
    linarith
  have hdec := cellDecay_of_fourier hL hsupp hcell (B := ftDecay F)
    (fun N ξ => by rw [hFe]; exact le_ftDecay F N ξ)
  have hc : HChi (2 * Real.pi / L) (mFourierCoeff χ) (obsTailC (ftDecay F)) := hdec.hChi hL1
  -- the grid step at the unit data
  have hV := hθ.tv_nonneg
  obtain ⟨hC6, hD2, hD4, hT⟩ := obs_consts_nonneg F
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have k5 : 0 ≤ (1 / K) ^ 5 := pow_nonneg (div_nonneg zero_le_one hKpos.le) 5
  have k3 : 0 ≤ (1 / K) ^ 3 := pow_nonneg (div_nonneg zero_le_one hKpos.le) 3
  have hunit : ∀ φ g₀ g₁ : MolecularPositionL2 eta, HasGLHamiltonian sys L θ φ g₀ →
      HasGLHamiltonian sys L θ g₀ g₁ → ‖φ‖ ≤ 1 → ‖g₀‖ ≤ Λ → ‖g₁‖ ≤ Λ ^ 2 →
      ‖⟪U t φ, mulCLM (regFun a χ) (U t φ)⟫_ℂ -
          ⟪Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ))),
            posObs a (chiRefl χ) (Ug t (idft (regCoeff m
              ((molecularPositionSynthesis eta).symm φ))))⟫_ℂ‖ ≤
        (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + 1) * obsTailC (ftDecay F) 5) * (1 / K) ^ 5 +
          A.2.1 * t * (1 / K) ^ 3 := by
    intro φ g₀ g₁ hφ hg hφ1 hg0 hg1
    have h := hbound φ g₀ g₁ hφ hg a χ (obsTailC (ftDecay F)) hc hreal hm hK t ht
    simp only at h
    set A' := gridConstsPosU sys L (tv R θ) a χ ‖φ‖ ‖g₀‖ ‖g₁‖ with hA'
    have h' : ‖⟪U t φ, mulCLM (regFun a χ) (U t φ)⟫_ℂ -
          ⟪Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ))),
            posObs a (chiRefl χ) (Ug t (idft (regCoeff m
              ((molecularPositionSynthesis eta).symm φ))))⟫_ℂ‖ ≤
        (A'.1 + (A'.2.2 * Real.sqrt 3 ^ 5 + ‖φ‖ ^ 2) * obsTailC (ftDecay F) 5) * (1 / K) ^ 5 +
          A'.2.1 * t * (1 / K) ^ 3 := h
    obtain ⟨hA1, hA2, hA3⟩ := gridConstsPosU_le_of_decay sys hL1 hV a hdec (norm_nonneg φ)
      (norm_nonneg g₀) (norm_nonneg g₁)
    obtain ⟨m1, m2, m3⟩ := gridConstsSharp_gLU_mono_data sys hV hardyUnit_nonneg hC6 hC6 hD2 hD4
      (norm_nonneg φ) (norm_nonneg g₀) (norm_nonneg g₀) (norm_nonneg g₁) hφ1 hg0 hg0 hg1
    have m1' : A'.1 ≤ A.1 := hA1.trans m1
    have m2' : A'.2.1 ≤ A.2.1 := hA2.trans m2
    have m3' : A'.2.2 ≤ A.2.2 := hA3.trans_le m3
    have hφ2 : ‖φ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg φ]
    have hs3 : 0 ≤ Real.sqrt 3 ^ 5 := by positivity
    have e1 : A'.1 + (A'.2.2 * Real.sqrt 3 ^ 5 + ‖φ‖ ^ 2) * obsTailC (ftDecay F) 5 ≤
        A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + 1) * obsTailC (ftDecay F) 5 := by
      have := mul_le_mul_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_right m3' hs3) hφ2) hT
      linarith
    have e2 : A'.2.1 * t ≤ A.2.1 * t := mul_le_mul_of_nonneg_right m2' ht
    refine h'.trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_right e1 k5) (mul_le_mul_of_nonneg_right e2 k3)
  -- the components
  have hsplit : ((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
      ∑ σ, ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ =
      (((∑ σ, ∫ r, f (particle r a) * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
        ∑ σ, ⟪U t (X.chiW.cutL2 hL (Ψ 0 σ)), mulCLM (regFun a χ)
          (U t (X.chiW.cutL2 hL (Ψ 0 σ)))⟫_ℂ) +
      ∑ σ, (⟪U t (X.chiW.cutL2 hL (Ψ 0 σ)), mulCLM (regFun a χ)
          (U t (X.chiW.cutL2 hL (Ψ 0 σ)))⟫_ℂ - ⟪ψg σ, posObs a (chiRefl χ) (ψg σ)⟫_ℂ) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add hobs ?_)
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun σ _ => ?_
  exact norm_le_sq_mul_of_unit (HasGLHamiltonian sys L θ) (fun c f h hf => hf.smul sys c)
    (fun φ => ⟪U t φ, mulCLM (regFun a χ) (U t φ)⟫_ℂ -
      ⟪Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ))),
        posObs a (chiRefl χ) (Ug t (idft (regCoeff m
          ((molecularPositionSynthesis eta).symm φ))))⟫_ℂ)
    (fun c φ => gridErr_smul (U t) (Ug t) a χ c φ) hunit (hdom0 σ) (hdom1 σ) (hN σ) (hn0 σ)
    (hn1 σ) (hn2 σ)

end FreeBoundary
