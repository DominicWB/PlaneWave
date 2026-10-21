import PlaneWave.FreeBoundary.GridDynamicsSharp

/-!
# `thm:grid-dyn-sharp` for the `g_L` kernel in position space

The release's `grid_observable_position_sharp` and `thm_grid_dyn_sharp` (`PlaneWave.Grid`, section
`DevGS6`) for the `g_L` Hamiltonian: the continuum side is the propagator `e^{-iH_L t}` of
`PlaneWave.FreeBoundary.Propagator` (`exists_gLPropagator`, the relation `HasGLHamiltonian` of
`PlaneWave.FreeBoundary.Dynamics`), the grid side is the release's padded collocation propagator
`e^{-iH_pos t}` with a kernel of the class `PlaneWaveGridG.IsGridKernel γ ρ_L m` (`γ ρ_L = ĝ_L` on
`|ν| ≤ m`).

The relation `HasGLHamiltonian` is the graph of the completed operator under the Fourier synthesis
`Φ` (`hasGLHamiltonian_iff_H2`), while the release's grid values are the values of the register in
the frame of `physMap = R ∘ Φ`, with the reflection `R : x ↦ -x`. So the grid point `x_j` represents
the physical position `-x_j`, and the collocated observable of `χ(x_a)` is `χ(-x_{j_a})`, the
collocation of `chiRefl χ = χ(-·)` (`synth_mulCLM`).

* `refl_mulCLM`, `synth_mulCLM`: multiplication operators under the reflection and the synthesis;
* `grid_observable_position_sharp_gL`: the observable error in position space;
* **`thm_grid_dyn_sharp_gL`**: `thm:grid-dyn-sharp` for `g_L`,
  `|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫|` is at most
  `(A₁ + (A₃ 3^{5/2} + ‖ψ₀‖²) C_{χ,5}) K⁻⁵ + A₂ t K⁻³`, with `(A₁, A₂, A₃) = gridConstsSharp_gL`
  independent of `K` and `t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLgamma_pos gLref gLNucData regParticlesOfG)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Reflection -/

section Reflection

/-- The reflection `y ↦ -y` of the unit torus. -/
def negT : C(UnitAddTorus (Fin 3), UnitAddTorus (Fin 3)) := ⟨fun y => -y, continuous_neg⟩

/-- The reflection `x ↦ -x` of the position torus. -/
def negM (eta : ℕ) : C(MolecularPositionTorus eta, MolecularPositionTorus eta) :=
  ⟨fun x => -x, continuous_neg⟩

/-- The reflected one-particle observable `χ(-·)`. -/
noncomputable def chiRefl (χ : C(UnitAddTorus (Fin 3), ℂ)) : C(UnitAddTorus (Fin 3), ℂ) := χ.comp
    negT

lemma chiRefl_apply (χ : C(UnitAddTorus (Fin 3), ℂ)) (y : UnitAddTorus (Fin 3)) :
    chiRefl χ y = χ (-y) := rfl

lemma mFourierCoeff_chiRefl (χ : C(UnitAddTorus (Fin 3), ℂ)) (n : Lattice3) :
    mFourierCoeff (chiRefl χ) n = mFourierCoeff χ (-n) :=
  unitTorus3_fourierCoeff_reflect χ n

lemma latticeSupNorm_neg (n : Lattice3) : latticeSupNorm (-n) = latticeSupNorm n := by
  simp [latticeSupNorm]

/-- `(Hχ)` passes to `χ(-·)` with the same constants. -/
lemma HChi_chiRefl {g : ℝ} {χ : C(UnitAddTorus (Fin 3), ℂ)} {CM : ℕ → ℝ}
    (h : HChi g (mFourierCoeff χ) CM) : HChi g (mFourierCoeff (chiRefl χ)) CM := by
  refine ⟨?_, fun M hM ρ hρ => ?_⟩
  · have h1 := (Equiv.neg Lattice3).summable_iff.mpr h.1
    refine h1.congr fun n => ?_
    simp [mFourierCoeff_chiRefl]
  · have h2 := h.2 M hM ρ hρ
    have e : (∑' n, if ρ < g * latticeSupNorm n then ‖mFourierCoeff (chiRefl χ) n‖ else 0) =
        ∑' n, if ρ < g * latticeSupNorm n then ‖mFourierCoeff χ n‖ else 0 := by
      rw [← (Equiv.neg Lattice3).tsum_eq]
      refine tsum_congr fun n => ?_
      simp [mFourierCoeff_chiRefl, latticeSupNorm_neg]
    rw [e]
    exact h2

lemma chiRefl_real {χ : C(UnitAddTorus (Fin 3), ℂ)} (hreal : ∀ y, conj (χ y) = χ y) :
    ∀ y, conj (chiRefl χ y) = chiRefl χ y := fun y => hreal (-y)

/-- Reflection commutes with multiplication operators: `R (G f) = (G ∘ (-·)) (R f)`. -/
lemma refl_mulCLM (G : C(MolecularPositionTorus eta, ℂ)) (f : MolecularPositionL2 eta) :
    molecularPositionReflection eta (mulCLM G f) =
      mulCLM (G.comp (negM eta)) (molecularPositionReflection eta f) := by
  apply Lp.ext
  filter_upwards [molecularPositionReflection_coeFn eta (mulCLM G f),
    (molecularPosition_neg_measurePreserving eta).quasiMeasurePreserving.ae (mulLp_ae G f),
    mulLp_ae (G.comp (negM eta)) (molecularPositionReflection eta f),
    molecularPositionReflection_coeFn eta f] with x h1 h2 h3 h4
  calc (molecularPositionReflection eta (mulCLM G f) : MolecularPositionTorus eta → ℂ) x
      = (mulLp G f : MolecularPositionTorus eta → ℂ) (-x) := h1
    _ = G (-x) * f (-x) := h2
    _ = (G.comp (negM eta)) x * (molecularPositionReflection eta f) x := by rw [h4]; rfl
    _ = _ := h3.symm

lemma regFun_chiRefl_comp (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) :
    (regFun a (chiRefl χ)).comp (negM eta) = regFun a χ := by
  ext x
  simp only [ContinuousMap.comp_apply, regFun, chiRefl, negT, negM, ContinuousMap.coe_mk, regPos]
  congr 1
  funext c
  simp [molecularPositionParticle]

/-- **The observable in the coordinates of the synthesis** `Φ`: `Φ⁻¹ χ(x_a) Φ` is the convolution
with the coefficients of `χ(-·)`. -/
theorem synth_mulCLM (a : Fin eta) {χ : C(UnitAddTorus (Fin 3), ℂ)}
    (hχ : Summable fun ν => ‖mFourierCoeff (chiRefl χ) ν‖)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    (molecularPositionSynthesis eta).symm
        (mulCLM (regFun a χ) (molecularPositionSynthesis eta x)) =
      convOp a (mFourierCoeff (chiRefl χ)) x := by
  have hΦ : molecularPositionSynthesis eta x =
      molecularPositionReflection eta (physMap eta x) := by
    show _ = molecularPositionReflection eta
      (molecularPositionReflection eta (molecularPositionSynthesis eta x))
    rw [molecularPositionReflection_involutive]
  have hsymm : ∀ z, (molecularPositionSynthesis eta).symm (molecularPositionReflection eta z) =
      (physMap eta).symm z := by
    intro z
    show _ = (molecularPositionSynthesis eta).symm ((molecularPositionReflection eta).symm z)
    rw [molecularPositionReflection_symm]
  rw [hΦ, ← regFun_chiRefl_comp a χ, ← refl_mulCLM, hsymm, physMap_mulCLM a hχ x]

end Reflection

/-! ## Constants -/

lemma gLmassConst_nonneg (sys : CoulombSystem eta ν) (L : ℝ) {V : ℝ} (hV : 0 ≤ V) (Hunit : ℝ) :
    0 ≤ gLmassConst sys L V Hunit :=
  mul_nonneg sys.massCouplingWeight_nonneg (mul_nonneg (by linarith) (FSNormal.tB_nonneg _ _ _))

lemma gridConstsSharp_gL_nonneg_three (sys : CoulombSystem eta ν) {L V : ℝ} (hL : 0 < L)
    (hV : 0 ≤ V) (Hunit : ℝ) (a : Fin eta) (χ : Lattice3 → ℂ)
    (hC : 0 ≤ gLmassConst sys L V Hunit) {s0 hu hs hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu)
    (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    0 ≤ (gridConstsSharp_gL sys L V Hunit a χ s0 hu hs hv).2.2 := by
  have hb := relB_gL_nonneg sys L V Hunit hC
  have hM := sys.one_le_maxMass
  have hκ : 0 ≤ gLtailM sys L V Hunit
      (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB_gL sys L V Hunit * s0))) :=
    gLtailM_nonneg sys hL hV Hunit (by positivity)
  simp only [gridConstsSharp_gL]
  positivity

/-! ## Position space -/

section PositionTheorem

/-- **Observable error on the grid, position space, sharp, `g_L`** (`thm:grid-dyn-sharp`): for
`m ≥ 8`, `K ≥ 8` and `t ≥ 0`,
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤
  A₁ K^{-5} + A₂ t K^{-3} + A₃ K^{-5/2} τ_χ(K) + ‖ψ₀‖² τ_χ^∞(m)`, with
`O_g = χ(-x_{j_a})` and `(A₁, A₂, A₃) = gridConstsSharp_gL` at the canonical Hardy constant,
independent of `K` and `t`. -/
theorem grid_observable_position_sharp_gL (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (hU0 : ∀ ψ, U 0 ψ = ψ)
    (hUgraph : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasGLHamiltonian sys L θ (U t f) (U t h))
    (hUderiv : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ))
      (gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (ψ₀ h₀ h₁ : MolecularPositionL2 eta) (hψ₀ : HasGLHamiltonian sys L θ ψ₀ h₀)
    (hh₀ : HasGLHamiltonian sys L θ h₀ h₁)
    (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχ1 : Summable fun ν => ‖mFourierCoeff (chiRefl χ) ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖mFourierCoeff (chiRefl χ) ν‖)
    (hχ4 : Summable fun ν => nsq ν ^ 2 * ‖mFourierCoeff (chiRefl χ) ν‖)
    (hreal : ∀ y, conj (χ y) = χ y) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridConstsSharp_gL sys L (tv R θ) molecularCanonicalUnitHardyConstant a
      (mFourierCoeff (chiRefl χ)) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then
      ‖mFourierCoeff (chiRefl χ) ν‖ else 0
    let ψg := posConj (Ug t) (idft (regCoeff m ((molecularPositionSynthesis eta).symm ψ₀)))
    ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖ψ₀‖ ^ 2 * supTail (mFourierCoeff (chiRefl χ)) m := by
  intro g K A τχ ψg
  have hPeriodic := canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨H, hKernel, -⟩ := exists_gLFourierH2Operator sys hL hθ
    molecularCanonicalUnitHardyConstant hPeriodic
  have hiff := hasGLHamiltonian_iff_H2 sys hL hθ hR H hKernel
  set Φ := molecularPositionSynthesis eta with hΦ
  -- the propagator on the Fourier side
  set UF : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
    fun s => (Φ.trans (U s)).trans Φ.symm with hUFdef
  have hUF : ∀ s x, UF s x = Φ.symm (U s (Φ x)) := fun s x => rfl
  have h0F : ∀ x, UF 0 x = x := by
    intro x
    rw [hUF, hU0, LinearIsometryEquiv.symm_apply_apply]
  have hgraphF : ∀ s u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        UF s (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = UF s (H u) := by
    intro s u
    obtain ⟨u', h1, h2⟩ := (hiff _ _).mp (hUgraph s _ _ ((hiff _ _).mpr ⟨u, rfl, rfl⟩))
    refine ⟨u', ?_, ?_⟩
    · rw [hUF, ← h1, LinearIsometryEquiv.symm_apply_apply]
    · rw [hUF, ← h2, LinearIsometryEquiv.symm_apply_apply]
  have hderivF : ∀ s u, HasDerivAt (fun r => UF r (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • UF s (H u))) s := by
    intro s u
    have h := hUderiv s _ _ ((hiff _ _).mpr ⟨u, rfl, rfl⟩)
    have h2 := ((Φ.symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt s h
    simp only [ContinuousLinearMap.coe_restrictScalars'] at h2
    rw [map_neg, map_smul] at h2
    exact h2
  -- the initial state in `D(H²)`
  obtain ⟨u₀, hu₀1, hu₀2⟩ := (hiff ψ₀ h₀).mp hψ₀
  obtain ⟨v₀, hv₀1, hv₀2⟩ := (hiff h₀ h₁).mp hh₀
  have huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀ :=
    Φ.injective (hu₀2.trans hv₀1.symm)
  have hx₀ : Φ.symm ψ₀ = molecularH2StateMap eta (2 * Real.pi / L) u₀ := by
    rw [← hu₀1, LinearIsometryEquiv.symm_apply_apply]
  -- the continuum expectation on the Fourier side
  have hO : ∀ x, ⟪Φ x, mulCLM (regFun a χ) (Φ x)⟫_ℂ =
      ⟪x, convOp a (mFourierCoeff (chiRefl χ)) x⟫_ℂ := by
    intro x
    rw [← synth_mulCLM a hχ1 x, ← LinearIsometryEquiv.inner_map_map Φ,
      LinearIsometryEquiv.apply_symm_apply]
  have hψt : U t ψ₀ = Φ (UF t (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    rw [hUF, LinearIsometryEquiv.apply_symm_apply, hu₀1]
  -- the grid expectation on the register
  have hdψ : dft ψg = Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    show dft (posConj (Ug t) (idft (regCoeff m (Φ.symm ψ₀)))) = _
    rw [dft_posConj, dft_idft, hx₀]
  have hψg : ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ =
      ⟪Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)),
        gridObs a (mFourierCoeff (chiRefl χ)) (Ug t
            (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)))⟫_ℂ := by
    rw [← inner_dft_dft ψg, dft_posObs a hχ1, hdψ]
  rw [hψt, hO, hψg]
  have h := grid_observable_rate_sharp_gL sys L H hKernel molecularCanonicalUnitHardyConstant hL hθ
    hPeriodic (gLmassConst_nonneg sys L hθ.tv_nonneg _) UF h0F hgraphF hderivF m hm hK hκ Ug hg0
    hgcomm hgderiv u₀ v₀ huv a (mFourierCoeff (chiRefl χ)) hχ1 hχ2 hχ4
    (fun ν => mFourierCoeff_neg_of_real (chiRefl_real hreal) ν) ht
  dsimp only at h
  have e1 : ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ = ‖ψ₀‖ := by
    rw [← hu₀1, LinearIsometryEquiv.norm_map]
  have e2 : ‖H u₀‖ = ‖h₀‖ := by rw [← hu₀2, LinearIsometryEquiv.norm_map]
  have e3 : ‖molecularH2StateMap eta (2 * Real.pi / L) v₀‖ = ‖h₀‖ := by
    rw [← hv₀1, LinearIsometryEquiv.norm_map]
  have e4 : ‖H v₀‖ = ‖h₁‖ := by rw [← hv₀2, LinearIsometryEquiv.norm_map]
  rw [e1, e2, e3, e4] at h
  exact h

end PositionTheorem

/-! ## `thm:grid-dyn-sharp` for `g_L` -/

section Final

/-- **`thm:grid-dyn-sharp` for `g_L`, for a given propagator.** The grid part of
`thm_grid_dyn_sharp_gL` for any `U` that preserves the graph of `H_L` and solves the Schrödinger
equation on it (in particular the propagator of `exists_gLPropagator`): a grid propagator `U_g`
and the bound `(A₁ + (A₃ 3^{5/2} + ‖ψ₀‖²) C_{χ,5}) K^{-5} + A₂ t K^{-3}`. -/
theorem grid_dyn_sharp_gL_of_propagator (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2)
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta) (h0 : ∀ ψ, U 0 ψ = ψ)
    (hgraph : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasGLHamiltonian sys L θ (U t f) (U t h))
    (hderiv : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (m : ℕ) (κ : Lat3 → ℝ)
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      ∀ ψ₀ h₀ h₁ : MolecularPositionL2 eta, HasGLHamiltonian sys L θ ψ₀ h₀ →
        HasGLHamiltonian sys L θ h₀ h₁ →
        ∀ (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (CM : ℕ → ℝ),
        HChi (2 * Real.pi / L) (mFourierCoeff χ) CM →
        (∀ y, conj (χ y) = χ y) →
        let A := gridConstsSharp_gL sys L (tv R θ) molecularCanonicalUnitHardyConstant a
          (mFourierCoeff (chiRefl χ)) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
        8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
          let K : ℝ := (2 * Real.pi / L) * m
          let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm ψ₀)))
          ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
            (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
              A.2.1 * t * (1 / K) ^ 3 := by
  obtain ⟨Ur, hr0, -, -, hrcomm, hrderiv, hp0, hpadd, hpcont, hpcomm, hpderiv⟩ :=
    exists_posPropagator (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) hκ.even
      (2 * Real.pi / L)
  refine ⟨fun t => posConj (Ur t), hp0, hpadd, hpcont, hpcomm, hpderiv, ?_⟩
  intro ψ₀ h₀ h₁ hψ₀ hh₀ a χ CM hc0 hreal A hm hK t ht K ψg
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hc := HChi_chiRefl hc0
  have hχ1 := hc.1
  have hχ2 := summable_nsq_of_HChi hg hc
  have hχ4 := summable_nsq_sq_of_HChi hg hc
  have h := grid_observable_position_sharp_gL sys hL hθ hR U h0 hgraph hderiv m hm hK hκ Ur hr0
    hrcomm hrderiv ψ₀ h₀ h₁ hψ₀ hh₀ a χ hχ1 hχ2 hχ4 hreal ht
  have hA₃ : 0 ≤ A.2.2 :=
    gridConstsSharp_gL_nonneg_three sys hL hθ.tv_nonneg molecularCanonicalUnitHardyConstant a
      (mFourierCoeff (chiRefl χ)) (gLmassConst_nonneg sys L hθ.tv_nonneg _)
      (norm_nonneg ψ₀) (norm_nonneg h₀) (norm_nonneg h₀) (norm_nonneg h₁)
  have hK' : (8 : ℝ) ≤ K := hK
  have hKpos : 0 < K := by linarith
  have hsqrt3 : Real.sqrt 3 ≤ K := by
    have : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    linarith
  have hC5 := CM_nonneg_of_HChi hc (M := 5) (by norm_num)
  have htail := tail_le_of_HChi hg hc (M := 5) (by norm_num) hsqrt3
  have hsup := supTail_le_of_HChi hg hc (M := 5) (by norm_num) (m := m) (by linarith)
  have hρ1 : Real.sqrt (1 / K) ^ 5 ≤ 1 := by
    have h1 : 1 / K ≤ 1 := by rw [div_le_one hKpos]; linarith
    have h2 : Real.sqrt (1 / K) ≤ 1 := by
      have := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_one] at this
    exact pow_le_one₀ (Real.sqrt_nonneg _) h2
  have hρ0 : 0 ≤ Real.sqrt (1 / K) ^ 5 := by positivity
  have hτ : A.2.2 * Real.sqrt (1 / K) ^ 5 *
      (∑' x, if K < (2 * Real.pi / L) * Real.sqrt (latticeNormSq x) then
        ‖mFourierCoeff (chiRefl χ) x‖ else 0) ≤ A.2.2 * Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left htail (mul_nonneg hA₃ hρ0)
    have h2 : A.2.2 * Real.sqrt (1 / K) ^ 5 * (Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5) ≤
        A.2.2 * 1 * (Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ1 hA₃)
      positivity
    have e : A.2.2 * 1 * (Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5) =
        A.2.2 * Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5 := by ring
    linarith
  have hs : ‖ψ₀‖ ^ 2 * supTail (mFourierCoeff (chiRefl χ)) m ≤
      ‖ψ₀‖ ^ 2 * (CM 5 * (1 / K) ^ 5) :=
    mul_le_mul_of_nonneg_left hsup (by positivity)
  have e : (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
      A.2.1 * t * (1 / K) ^ 3 = A.1 * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3 +
        A.2.2 * Real.sqrt 3 ^ 5 * CM 5 * (1 / K) ^ 5 + ‖ψ₀‖ ^ 2 * (CM 5 * (1 / K) ^ 5) := by ring
  rw [e]
  exact h.trans (by linarith)


/-- **`thm:grid-dyn-sharp` for the `g_L` kernel** (truncated-kernel grid method, energy-rate
secular bound). For the torus `g_L` Hamiltonian (zero mode removed) there is a propagator `U`
(`e^{-iH_L t}`) on `L²((T³)^η)` (unitary group, strongly continuous, preserving the graph of the
Hamiltonian, solving the Schrödinger equation on it, and the only evolution that does), and for
every register radius `2m` and every real, even kernel `κ` of the class
(`PlaneWaveGridG.IsGridKernel γ ρ_L m`: `|κ| ≤ γ/|ν|²`, `κ = ĝ_L` for `|ν| ≤ m`, zero outside the
zone) a grid propagator `U_g` (`e^{-iH_pos t}` on the grid values), such that: for every
`ψ₀ ∈ D(H_L²)` (`H_L ψ₀ = h₀`, `H_L h₀ = h₁`), register `a` and real continuous `χ` satisfying
`(Hχ)`, with the constants `(A₁, A₂, A₃) = gridConstsSharp_gL` at `(‖ψ₀‖, ‖h₀‖, ‖h₀‖, ‖h₁‖)`,
which do not depend on `m` or `t`: for `m ≥ 8`, `K ≥ 8` and `t ≥ 0`, the grid state
`ψ_g(t) = e^{-iH_pos t} P ψ₀` and the collocated observable `O_g = χ(-x_{j_a})` (the grid frame
is reflected, see the module docstring) satisfy
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤
  (A₁ + (A₃ 3^{5/2} + ‖ψ₀‖²) C_{χ,5}) K^{-5} + A₂ t K^{-3}`. -/
theorem thm_grid_dyn_sharp_gL (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (hR : R ≤ L / 2) :
    ∃ U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta,
      (∀ ψ, U 0 ψ = ψ) ∧
      (∀ s t ψ, U (s + t) ψ = U s (U t ψ)) ∧
      (∀ ψ, Continuous fun t => U t ψ) ∧
      (∀ t f h, HasGLHamiltonian sys L θ f h →
        HasGLHamiltonian sys L θ (U t f) (U t h)) ∧
      (∀ t f h, HasGLHamiltonian sys L θ f h →
        HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) ∧
      (∀ φ ζ : ℝ → MolecularPositionL2 eta, (∀ t, HasGLHamiltonian sys L θ (φ t) (ζ t)) →
        (∀ t, HasDerivAt φ (-(Complex.I • ζ t)) t) → ∀ t, φ t = U t (φ 0)) ∧
      ∀ (m : ℕ) (κ : Lat3 → ℝ), PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ))
          (gLref L θ (tv R θ)) m κ →
      ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
        (∀ x, Continuous fun t => Ug t x) ∧
        (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
          (2 * Real.pi / L) (Ug t x)) ∧
        (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
          (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
        ∀ ψ₀ h₀ h₁ : MolecularPositionL2 eta, HasGLHamiltonian sys L θ ψ₀ h₀ →
          HasGLHamiltonian sys L θ h₀ h₁ →
          ∀ (a : Fin eta) (χ : C(UnitAddTorus (Fin 3), ℂ)) (CM : ℕ → ℝ),
          HChi (2 * Real.pi / L) (mFourierCoeff χ) CM →
          (∀ y, conj (χ y) = χ y) →
          let A := gridConstsSharp_gL sys L (tv R θ) molecularCanonicalUnitHardyConstant a
            (mFourierCoeff (chiRefl χ)) ‖ψ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm ψ₀)))
            ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
              (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
                A.2.1 * t * (1 / K) ^ 3 := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq⟩ := exists_gLPropagator sys hL hθ hR
  exact ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, fun m κ hκ =>
    grid_dyn_sharp_gL_of_propagator sys hL hθ hR U h0 hgraph hderiv m κ hκ⟩

end Final

end FreeBoundary
