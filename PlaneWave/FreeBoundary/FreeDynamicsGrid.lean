import PlaneWave.FreeBoundary.GridDynamicsTheorem

/-!
# `prop:free-dyn`: the free-space evolution against the grid

The two steps of `prop:free-dyn` with one propagator `U = e^{-iH_L t}` of the torus `g_L`
Hamiltonian (`exists_gLPropagator`):

* the free-space step (`free_dyn_torus`, `PlaneWave.FreeBoundary.Dynamics`): the observable of
  the free-space evolution `ψ_∞(t)` against that of `U(t) φ(0)`, `φ(0) = T(χ_𝓑 ψ_∞(0))` the
  transplanted cut initial state;
* the grid step (`grid_dyn_sharp_gL_of_propagator`, `PlaneWave.FreeBoundary.GridDynamicsTheorem`):
  the observable of `U(t) φ(0)` against that of the grid state `ψ_g(t) = e^{-iH_pos t} P φ(0)`.

The text's domain condition `χ_𝓑 ψ₀ ∈ D(H_L²)` is a hypothesis (`H_L φ(0) = h₀`, `H_L h₀ = h₁`),
and the observable is one-particle: `f(r_a)` in free space, `χ(x_a)` on the torus, with
`χ(x_a) = f((L·rep x)_a)` (the torus version of `f` on the cell). As in
`PlaneWave.FreeBoundary.GridDynamicsTheorem`, the grid frame is the reflection of the torus frame,
so the collocated observable is `χ(-x_{j_a})`.

* **`free_dyn_grid_gL`**: `|∫ f(r_a) |ψ_∞(t, r)|² dr - ⟨ψ_g(t), O_g ψ_g(t)⟩| ≤
  ε² + (‖ψ_∞(t)‖ + ‖ψ_∞(0)‖) C ε t + (A₁ + (A₃ 3^{5/2} + ‖φ(0)‖²) C_{χ,5}) K⁻⁵ + A₂ t K⁻³`, with
  `C = 3η (D₁ + D₂/2)` of the cutoff and `(A₁, A₂, A₃) = gridConstsSharp_gL` at
  `(‖φ(0)‖, ‖h₀‖, ‖h₀‖, ‖h₁‖)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLref)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

lemma continuous_particle (a : Fin eta) : Continuous fun r : Rcfg eta => particle r a := by
  unfold particle
  fun_prop

/-- A torus observable that agrees on the cell with a real one-particle function is real. -/
lemma real_of_cell {a : Fin eta} {f : E3 → ℝ} {L : ℝ} {χ : C(UnitAddTorus (Fin 3), ℂ)}
    (hχf : ∀ x : MolecularPositionTorus eta,
      χ (molecularPositionParticle a x) = (f (particle (cellCoord L x) a) : ℂ)) :
    ∀ y, conj (χ y) = χ y := by
  intro y
  have h := hχf (fun p => y p.2)
  have hy : molecularPositionParticle a (fun p : Fin eta × Fin 3 => y p.2) = y := rfl
  rw [hy] at h
  rw [h, Complex.conj_ofReal]

/-- **`prop:free-dyn`: the free-space evolution against the grid.** Let `ψ_∞` solve the free-space
Schrödinger equation (`H_∞`, weak gradients `grad`), `X = χ_𝓑` a cutoff of the retained region
with the leak hypotheses (H_leak) up to time `t` (as in `free_dyn_torus`), and assume the text's
domain condition for the transplanted cut initial state `φ(0) = T(χ_𝓑 ψ_∞(0))`:
`H_L φ(0) = h₀`, `H_L h₀ = h₁` (`H_L` the torus `g_L` Hamiltonian, zero mode removed, `R ≤ L/2`).
Let `f` be a one-particle observable, `0 ≤ f ≤ 1` measurable, whose torus version on the cell is a
continuous `χ` with `(Hχ)` (`χ(x_a) = f((L·rep x)_a)`), and `κ` a kernel of the class with
reference `ĝ_L` at register radius `2m`, `m ≥ 8`, `K = 2πm/L ≥ 8`. Then the grid propagator
`U_g = e^{-iH_pos t}` and the grid state `ψ_g(t) = U_g(t) P φ(0)` satisfy
`|∫ f(r_a) |ψ_∞(t, r)|² dr - ⟨ψ_g(t), χ(-x_{j_a}) ψ_g(t)⟩| ≤
  ε² + (‖ψ_∞(t)‖ + ‖ψ_∞(0)‖) C ε t + (A₁ + (A₃ 3^{5/2} + ‖φ(0)‖²) C_{χ,5}) K⁻⁵ + A₂ t K⁻³`. -/
theorem free_dyn_grid_gL (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 hL (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1) (hfm : Measurable f)
    (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχf : ∀ x : MolecularPositionTorus eta,
      χ (molecularPositionParticle a x) = (f (particle (cellCoord L x) a) : ℂ))
    (CM : ℕ → ℝ) (hc : HChi (2 * Real.pi / L) (mFourierCoeff χ) CM)
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
      let φ₀ := X.chiW.cutL2 hL (ψ 0)
      let A := gridConstsSharp_gL sys L (tv R θ) molecularCanonicalUnitHardyConstant a
        (mFourierCoeff (chiRefl χ)) ‖φ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.commConst * ε * t) +
          ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖φ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
            A.2.1 * t * (1 / K) ^ 3) := by
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, -⟩ := exists_gLPropagator sys hL hθ hR
  have hreal := real_of_cell hχf
  have hχom : Measurable fun r : Rcfg eta => f (particle r a) :=
    hfm.comp (continuous_particle a).measurable
  have hG : ∀ x, regFun a χ x = ((fun r : Rcfg eta => f (particle r a)) (cellCoord L x) : ℂ) :=
    fun x => hχf x
  obtain ⟨-, hobs⟩ := free_dyn_torus sys hL hθ hR0 hρ hone P hP hpos U h0 hadd hcont hderiv X hret
    hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1
    (χo := fun r => f (particle r a)) (fun r => hf0 _) (fun r => hf1 _) hχom (regFun a χ) hG
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ :=
    grid_dyn_sharp_gL_of_propagator sys hL hθ hR U h0 hgraph hderiv m κ hκ
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro φ₀ A K ψg
  have hgrid := hbound φ₀ h₀ h₁ hdom0 hdom1 a χ CM hc hreal hm hK t ht
  simp only at hgrid hobs
  calc ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖
      ≤ ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) -
            ⟪U t φ₀, mulCLM (regFun a χ) (U t φ₀)⟫_ℂ‖ +
          ‖⟪U t φ₀, mulCLM (regFun a χ) (U t φ₀)⟫_ℂ - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hobs hgrid

end FreeBoundary
