import PlaneWave.FreeBoundary.CutoffScaling

/-!
# The torus version of a one-particle observable

`prop:free-dyn` compares `∫ f(r_a) |ψ_∞(t)|²` with the grid observable built from the torus
version `χ` of `f`, `χ(x_a) = f((L · rep x)_a)` (`rep x ∈ (-1/2, 1/2]³`), which the earlier
statements take as a hypothesis. It exists when `f` is continuous and vanishes outside a ball of
radius `R_f < L/2`: on the open set where every coordinate of `x_a` is away from `1/2 + ℤ` the
representative is continuous, and on the open set where some coordinate has `L ‖x_{a,c}‖ > R_f`
the function vanishes; the two sets cover the torus.

* `abs_equivIoc_eq_norm`: `|rep s| = ‖s‖` on the unit circle;
* `cellObs`: the torus version `χ` as a continuous function, `cellObs_particle`: the defining
  identity;
* `free_dyn_grid_gLU_schwartz_cell`, `free_dyn_grid_gLU_decay_cell`, **`free_dyn_grid_nbo_cell`**:
  `prop:free-dyn` without the hypothesis on `χ` (for the non-Born–Oppenheimer system also without
  the domain hypotheses).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap
open Finset Set MeasureTheory
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLgamma_pos gLref gLNucData regParticlesOfG gLzU gLzU_nonneg gLAU
  gLGridCoupling)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The torus version of `f` -/

section CellObservable

/-- `|rep s| = ‖s‖` for the representative `rep s ∈ (-1/2, 1/2]` of a point of the unit circle. -/
lemma abs_equivIoc_eq_norm (s : UnitAddCircle) :
    |(AddCircle.equivIoc 1 (-1 / 2) s : ℝ)| = ‖s‖ := by
  have hmem := (AddCircle.equivIoc 1 (-1 / 2 : ℝ) s).2
  have hle : |(AddCircle.equivIoc 1 (-1 / 2 : ℝ) s : ℝ)| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_one, abs_le]
    constructor <;> linarith [hmem.1, hmem.2]
  conv_rhs => rw [← AddCircle.coe_equivIoc (p := (1 : ℝ)) (a := -1 / 2) (y := s)]
  exact ((AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hle).symm

lemma norm_coe_neg_half : ‖((-1 / 2 : ℝ) : UnitAddCircle)‖ = 1 / 2 := by
  rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr (by norm_num)]
  norm_num

lemma abs_cellRep_eq {L : ℝ} (hL : 0 ≤ L) (t : UnitAddTorus (Fin 3)) (c : Fin 3) :
    |cellRep L t c| = L * ‖t c‖ := by
  change |L * (AddCircle.equivIoc 1 (-1 / 2) (t c) : ℝ)| = L * ‖t c‖
  rw [abs_mul, abs_of_nonneg hL, abs_equivIoc_eq_norm]

/-- **The torus version of `f` is continuous**: `t ↦ f(L · rep t)` is continuous on the unit torus
if `f` is continuous and vanishes outside a ball of radius `R_f < L/2`. -/
lemma continuous_cellRep_comp {L : ℝ} (hL : 0 < L) {f : E3 → ℝ} (hf : Continuous f) {Rf : ℝ}
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L) :
    Continuous fun t : UnitAddTorus (Fin 3) => f (cellRep L t) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases h : ∀ c, t c ≠ ((-1 / 2 : ℝ) : UnitAddCircle)
  · -- away from the boundary of the cell the representative is continuous
    have hv : ContinuousAt (fun s : UnitAddTorus (Fin 3) => fun c : Fin 3 =>
        L * (AddCircle.equivIoc 1 (-1 / 2) (s c) : ℝ)) t :=
      continuousAt_pi.mpr fun c => by
        have h1 : ContinuousAt (AddCircle.equivIoc 1 (-1 / 2 : ℝ)) (t c) :=
          AddCircle.continuousAt_equivIoc 1 (-1 / 2) (h c)
        have h2 : ContinuousAt (fun s : UnitAddTorus (Fin 3) => s c) t :=
          (continuous_apply c).continuousAt
        have h3 := ContinuousAt.comp (x := t) (f := fun s : UnitAddTorus (Fin 3) => s c) h1 h2
        exact continuousAt_const.mul (continuous_subtype_val.continuousAt.comp h3)
    have hrep : ContinuousAt (cellRep L) t := (PiLp.continuous_toLp 2 _).continuousAt.comp hv
    exact hf.continuousAt.comp hrep
  · -- near the boundary of the cell the function vanishes
    simp only [not_forall, not_not] at h
    obtain ⟨c, hc⟩ := h
    have hU : {s : UnitAddTorus (Fin 3) | Rf < L * ‖s c‖} ∈ 𝓝 t := by
      refine IsOpen.mem_nhds (isOpen_lt continuous_const
        (continuous_const.mul (continuous_apply c).norm)) ?_
      change Rf < L * ‖t c‖
      rw [hc, norm_coe_neg_half]
      linarith
    have hzero : ∀ s ∈ {s : UnitAddTorus (Fin 3) | Rf < L * ‖s c‖}, f (cellRep L s) = 0 := by
      intro s hs
      by_contra hne
      have h1 := hfR _ hne
      have h2 := abs_coord_le_norm (cellRep L s) c
      rw [abs_cellRep_eq hL.le] at h2
      simp only [Set.mem_setOf_eq] at hs
      linarith
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hU] with s hs
    exact (hzero s hs).symm

/-- **The torus version of a one-particle observable**: `χ(t) = f(L · rep t)`, `rep t ∈
(-1/2, 1/2]³`, as a continuous function on the unit torus (`f` continuous, vanishing outside a ball
of radius `R_f < L/2`). -/
noncomputable def cellObs {L : ℝ} (hL : 0 < L) {f : E3 → ℝ} (hf : Continuous f) {Rf : ℝ}
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L) : C(UnitAddTorus (Fin 3), ℂ) :=
  ⟨fun t => (f (cellRep L t) : ℂ),
    Complex.continuous_ofReal.comp (continuous_cellRep_comp hL hf hfR hRL)⟩

lemma cellObs_apply {L : ℝ} (hL : 0 < L) {f : E3 → ℝ} (hf : Continuous f) {Rf : ℝ}
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L) (t : UnitAddTorus (Fin 3)) :
    cellObs hL hf hfR hRL t = (f (cellRep L t) : ℂ) := rfl

/-- The defining identity `χ(x_a) = f((L · rep x)_a)`. -/
lemma cellObs_particle {L : ℝ} (hL : 0 < L) {f : E3 → ℝ} (hf : Continuous f) {Rf : ℝ}
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L) (a : Fin eta)
    (x : MolecularPositionTorus eta) :
    cellObs hL hf hfR hRL (molecularPositionParticle a x) =
      (f (particle (cellCoord L x) a) : ℂ) := rfl

lemma continuous_of_schwartz (F : 𝓢(E3, ℂ)) {f : E3 → ℝ} (hFf : ∀ y, F y = (f y : ℂ)) :
    Continuous f := by
  have e : f = fun y => (F y).re := by
    funext y
    rw [hFf, Complex.ofReal_re]
  rw [e]
  exact Complex.continuous_re.comp F.continuous

end CellObservable

/-! ## `prop:free-dyn` without the hypothesis on `χ` -/

section FreeDynCell

/-- **`prop:free-dyn` for a fixed Schwartz observable, with the torus observable constructed**:
`free_dyn_grid_gLU_schwartz` with `χ = cellObs`, the torus version of `f`. -/
theorem free_dyn_grid_gLU_schwartz_cell (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
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
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0))
      h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁)
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
      let φ₀ := X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let A := gridConstsSharp_gLU sys (tv R θ) molecularCanonicalUnitHardyConstant
        (obsMomC (ftDecay F)) (obsMomC (ftDecay F))
        (obsMomD2 (ftDecay F)) (obsMomD4 (ftDecay F)) ‖φ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.commConst * ε * t) +
          ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖φ₀‖ ^ 2) * obsTailC (ftDecay F) 5) * (1 / K) ^ 5 +
            A.2.1 * t * (1 / K) ^ 3) := by
  exact free_dyn_grid_gLU_schwartz sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hSm hBm hχB hSB hdS
    hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 a hf0 hf1 F hFf hfR hRL
    (cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL)
    (cellObs_particle _ _ _ _ a) m hκ hm hK

/-- `free_dyn_grid_gLU_decay` with `χ = cellObs`, for a continuous `f`. -/
theorem free_dyn_grid_gLU_decay_cell (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
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
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0))
      h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1) (hfc : Continuous f)
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (BB : ℕ → ℝ) (hB : ∀ (N : ℕ) (ξ : E3), (1 + ‖ξ‖) ^ N * ‖𝓕 (fun y => (f y : ℂ)) ξ‖ ≤ BB N)
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
      let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) hfc hfR hRL
      let φ₀ := X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let A := gridConstsSharp_gLU sys (tv R θ) molecularCanonicalUnitHardyConstant
        (obsMomC BB) (obsMomC BB) (obsMomD2 BB) (obsMomD4 BB) ‖φ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.commConst * ε * t) +
          ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖φ₀‖ ^ 2) * obsTailC BB 5) * (1 / K) ^ 5 +
            A.2.1 * t * (1 / K) ^ 3) := by
  exact free_dyn_grid_gLU_decay sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hSm hBm hχB hSB hdS hd2S
    hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 a hf0 hf1 hfc.measurable hfR hRL BB hB
    (cellObs (lt_of_lt_of_le (by positivity) hL2) hfc hfR hRL) (cellObs_particle _ _ _ _ a) m hκ
    hm hK

/-- **`prop:free-dyn`, non-Born–Oppenheimer, with no hypothesis on `χ` or on the domain**:
`free_dyn_grid_nbo` with `χ = cellObs`, the torus version of `f`. -/
theorem free_dyn_grid_nbo_cell [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Dbar Cbar : ℝ} (hDbar : X.D ≤ Dbar) (hCbar : X.C ≤ Cbar)
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
    {k : FreeL2 eta} {g' : Fin eta × Fin 3 → FreeL2 eta}
    {g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta}
    {Y : FiniteElectronPair eta → FreeL2 eta}
    {Z : FiniteElectronPair eta → Fin eta × Fin 3 → FreeL2 eta}
    (hH1 : HasFreeHamiltonian sys P (H 0) k) (hg' : HasWeakGrad (H 0) g')
    (hg2 : ∀ b, HasWeakGrad (grad 0 b) (g2 b))
    (hY : ∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * ψ 0 r)
    (hZ : ∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * grad 0 a r)
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
      let N := dataNorm (ψ 0) (H 0) k (grad 0) g' g2 Y
      let Λ := domConst sys.charge (zeroWeight sys / 4) Dbar Cbar
      let A := gridConstsSharp_gLU sys (tv R θ) molecularCanonicalUnitHardyConstant
        (obsMomC (ftDecay F)) (obsMomC (ftDecay F))
        (obsMomD2 (ftDecay F)) (obsMomD4 (ftDecay F)) N (Λ * N) (Λ * N) (Λ ^ 2 * N)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) *
          ((Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2) * ε * t) +
          ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * obsTailC (ftDecay F) 5) * (1 / K) ^ 5 +
            A.2.1 * t * (1 / K) ^ 3) := by
  exact free_dyn_grid_nbo sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hDbar hCbar hSm hBm hχB hSB
    hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hH1 hg' hg2 hY hZ a hf0 hf1 F hFf hfR hRL
    (cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL)
    (cellObs_particle _ _ _ _ a) m hκ hm hK

end FreeDynCell

end FreeBoundary
