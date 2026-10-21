import PlaneWave.FreeBoundary.FreeDynamicsBO

/-!
# Clamped nuclei, part 11: `prop:free-dyn` with clamped nuclei, uniform in `L`

For equal masses `m_i = m₀ ≥ 1` (the moving particles are electrons): the product cutoff at
`L = 16` (`prodCutoff16`), scaled by `L/16` (`prodCutoffL`, `χ_L(r) = Π_i q(16 x_i / L)`), is `1`
where every `|x_i| < L/16`, has derivatives only on the shell
`{some |x_i| ≥ L/16, every |x_i| ≤ L/8}`, is supported where every `|x_i| ≤ L/8 ≤ R_L`, and is
flat near nuclei in `B_{R₀}(0)` at distance `δ` once `L ≥ 16 (R₀ + δ)`. Its bounds are those of
the cutoff at `16`, so `prop:free-dyn` with clamped nuclei holds with one constant for all
`L ≥ L₀ = max(16, 2R_f + 1, 16(R₀ + ρ + δ))`.

* `prodCutoff16`, `prodCutoffL`, `prodCutoffL_one`, `prodCutoffL_derivs`, `prodCutoffL_ret`,
  `prodCutoffL_isFlatNear`;
* `freeDynBOL0`; **`free_dyn_bo_uniform`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLref)

namespace FreeBoundary

variable {eta : ℕ}

/-! ## The product cutoff at `L ≥ 16` -/

section ProdCutoff

lemma norm_particle_inv_smul {s : ℝ} (hs : 0 < s) (r : Rcfg eta) (i : Fin eta) :
    ‖particle (s⁻¹ • r) i‖ = ‖particle r i‖ / s := by
  rw [particle_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), inv_mul_eq_div]

/-- The product cutoff at `L = 16` (`exists_prodCutoff`). -/
noncomputable def prodCutoff16 {m : Fin eta → ℝ} {m₀ : ℝ} (hm : ∀ i, m i = m₀) (hm0 : 1 ≤ m₀) :
    DomCutoff eta 16 m :=
  Classical.choose (exists_prodCutoff m hm hm0 (show (8 : ℝ) ≤ 16 by norm_num))

lemma prodCutoff16_χ {m : Fin eta → ℝ} {m₀ : ℝ} (hm : ∀ i, m i = m₀) (hm0 : 1 ≤ m₀)
    (r : Rcfg eta) : (prodCutoff16 hm hm0).χ r = prodChi r :=
  Classical.choose_spec (exists_prodCutoff m hm hm0 (show (8 : ℝ) ≤ 16 by norm_num)) r

/-- **The cutoff at `L ≥ 16`**: `χ_L(r) = Π_i q(16 x_i / L)`, the cutoff at `16` scaled by
`L/16`; its bounds are those at `16` (`prodCutoffL_D_le`, `prodCutoffL_C_le`). -/
noncomputable def prodCutoffL {m : Fin eta → ℝ} {m₀ : ℝ} (hm : ∀ i, m i = m₀) (hm0 : 1 ≤ m₀)
    {L : ℝ} (hL : 16 ≤ L) : DomCutoff eta L m :=
  ((prodCutoff16 hm hm0).scale (s := L / 16) (by linarith)).congrL (by ring)

variable {m : Fin eta → ℝ} {m₀ : ℝ} (hm : ∀ i, m i = m₀) (hm0 : 1 ≤ m₀) {L : ℝ}

lemma prodCutoffL_χ (hL : 16 ≤ L) (r : Rcfg eta) :
    (prodCutoffL hm hm0 hL).χ r = prodChi ((L / 16)⁻¹ • r) := by
  unfold prodCutoffL
  rw [DomCutoff.congrL_χ]
  exact prodCutoff16_χ hm hm0 _

lemma prodCutoffL_eq (hL : 16 ≤ L) (hs1 : 1 ≤ L / 16) :
    (prodCutoffL hm hm0 hL).χ = ((prodCutoff16 hm hm0).scale hs1).χ := by
  unfold prodCutoffL
  exact DomCutoff.congrL_χ _ _

lemma prodCutoffL_D_le (hL : 16 ≤ L) : (prodCutoffL hm hm0 hL).D ≤ (prodCutoff16 hm hm0).D := by
  unfold prodCutoffL
  rw [DomCutoff.congrL_D]
  exact (prodCutoff16 hm hm0).scale_D_le _

lemma prodCutoffL_C_le (hL : 16 ≤ L) : (prodCutoffL hm hm0 hL).C ≤ (prodCutoff16 hm hm0).C := by
  unfold prodCutoffL
  rw [DomCutoff.congrL_C]
  exact (prodCutoff16 hm hm0).scale_C_le _

/-- `χ_L = 1` where every `|x_i| < L/16`. -/
lemma prodCutoffL_one (hL : 16 ≤ L) :
    ∀ r ∈ {r : Rcfg eta | ∀ i, ‖particle r i‖ < L / 16}, (prodCutoffL hm hm0 hL).χ r = 1 := by
  intro r hr
  have hs : 0 < L / 16 := by linarith
  rw [prodCutoffL_χ]
  apply prodChi_one
  intro i
  rw [norm_particle_inv_smul hs, div_lt_one hs]
  exact hr i

/-- The derivatives of `χ_L` vanish off the shell `{some |x_i| ≥ L/16, every |x_i| ≤ L/8}`. -/
lemma prodCutoffL_derivs (hL : 16 ≤ L) :
    ∀ r, r ∉ {r : Rcfg eta | (∃ i, L / 16 ≤ ‖particle r i‖) ∧ ∀ i, ‖particle r i‖ ≤ L / 8} →
      ∀ a, dirD a (prodCutoffL hm hm0 hL).χ r = 0 ∧
        dirD a (dirD a (prodCutoffL hm hm0 hL).χ) r = 0 := by
  intro r hr a
  have hs : 0 < L / 16 := by linarith
  have hs1 : 1 ≤ L / 16 := by linarith
  have hr' : r ∉ {r : Rcfg eta | (L / 16)⁻¹ • r ∈ prodShell (eta := eta)} := by
    rintro ⟨⟨i, hi⟩, h2⟩
    apply hr
    rw [norm_particle_inv_smul hs, le_div_iff₀ hs, one_mul] at hi
    refine ⟨⟨i, hi⟩, fun j => ?_⟩
    have h3 := h2 j
    rw [norm_particle_inv_smul hs, div_le_iff₀ hs] at h3
    linarith
  have hχ : (prodCutoff16 hm hm0).χ = prodChi := funext (prodCutoff16_χ hm hm0)
  have h1 : ∀ r, r ∉ prodShell (eta := eta) → ∀ a, dirD a (prodCutoff16 hm hm0).χ r = 0 := by
    intro r hr a
    rw [hχ]
    exact (prodChi_dS hr a).1
  have h2 : ∀ r, r ∉ prodShell (eta := eta) → ∀ a,
      dirD a (dirD a (prodCutoff16 hm hm0).χ) r = 0 := by
    intro r hr a
    rw [hχ]
    exact (prodChi_dS hr a).2
  rw [prodCutoffL_eq hm hm0 hL hs1]
  exact ⟨(prodCutoff16 hm hm0).scale_dS hs1 h1 r hr' a,
    (prodCutoff16 hm hm0).scale_d2S hs1 h2 r hr' a⟩

/-- `χ_L` is supported where every `|x_i| ≤ L/8`. -/
lemma prodCutoffL_ret (hL : 16 ≤ L) :
    ∀ r, (prodCutoffL hm hm0 hL).χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ L / 8 := by
  intro r hr i
  have hs : 0 < L / 16 := by linarith
  rw [prodCutoffL_χ] at hr
  have h := prodChi_ret hr i
  rw [norm_particle_inv_smul hs, div_le_iff₀ hs] at h
  linarith

/-- `χ_L` is flat near nuclei with `|P_ℓ| + δ ≤ L/16`. -/
lemma prodCutoffL_isFlatNear (hL : 16 ≤ L) {ν : Type} (P : ν → E3) {δ : ℝ}
    (hP : ∀ l, ‖P l‖ + δ ≤ L / 16) : IsFlatNear (prodCutoffL hm hm0 hL).χ P δ := by
  have hs1 : 1 ≤ L / 16 := by linarith
  rw [prodCutoffL_eq hm hm0 hL hs1]
  exact (prodCutoff16 hm hm0).scale_isFlatNear hs1 (prodCutoff16_χ hm hm0) P hP

end ProdCutoff

/-! ## One constant for all cells -/

section Uniform

/-- The cell size from which `prop:free-dyn` with clamped nuclei holds with one constant. -/
noncomputable def freeDynBOL0 (R0 ρ Rf δ : ℝ) : ℝ := max (max 16 (2 * Rf + 1)) (16 * (R0 + ρ + δ))

variable {R0 ρ Rf δ L : ℝ}

lemma sixteen_le_of_freeDynBOL0 (hL : freeDynBOL0 R0 ρ Rf δ ≤ L) : 16 ≤ L :=
  ((le_max_left _ _).trans (le_max_left _ _)).trans hL

lemma pos_of_freeDynBOL0 (hL : freeDynBOL0 R0 ρ Rf δ ≤ L) : 0 < L := by
  have := sixteen_le_of_freeDynBOL0 hL
  linarith

lemma two_pi_le_of_freeDynBOL0 (hL : freeDynBOL0 R0 ρ Rf δ ≤ L) : 2 * Real.pi ≤ L := by
  have := sixteen_le_of_freeDynBOL0 hL
  linarith [Real.pi_le_four]

lemma two_Rf_lt_of_freeDynBOL0 (hL : freeDynBOL0 R0 ρ Rf δ ≤ L) : 2 * Rf < L := by
  have : 2 * Rf + 1 ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  linarith

lemma ret_of_freeDynBOL0 (hδ : 0 ≤ δ) (hL : freeDynBOL0 R0 ρ Rf δ ≤ L) :
    L / 8 ≤ retainedRadius L R0 ρ := by
  have h1 : 16 * (R0 + ρ + δ) ≤ L := (le_max_right _ _).trans hL
  have h2 := sixteen_le_of_freeDynBOL0 hL
  unfold retainedRadius
  linarith

lemma flat_of_freeDynBOL0 (hρ : 0 ≤ ρ) (hL : freeDynBOL0 R0 ρ Rf δ ≤ L) {ν : Type}
    {P : ν → E3} (hP : ∀ l, ‖P l‖ ≤ R0) (l : ν) : ‖P l‖ + δ ≤ L / 16 := by
  have : 16 * (R0 + ρ + δ) ≤ L := (le_max_right _ _).trans hL
  linarith [hP l]

variable {ν : Type} [Fintype ν]

/-- **`prop:free-dyn` with clamped nuclei, uniform in `L`** (equal masses `m_i = m₀ ≥ 1`): for the
molecule with nuclei at `P_ℓ ∈ B_{R₀}(0)` in the cell of size
`L ≥ L₀ = max(16, 2R_f + 1, 16(R₀ + ρ + δ))` (`sysAt sys P L`), every profile with `V_θ = V`, the
cutoff `χ_L(r) = Π_i q(16 x_i / L)` (leakage measured where some `|x_i| ≥ L/16`, gradient leakage
on the shell where moreover every `|x_i| ≤ L/8`), and data with
`‖ψ₀‖ + ‖H_∞ψ₀‖ + ‖H_∞²ψ₀‖ ≤ D`: the bound of `free_dyn_grid_bo` with the one constant
`C = freeDynConstBO sys V F D₁₆ C₁₆ δ D` (`D₁₆`, `C₁₆` the bounds of the cutoff at `16`). -/
theorem free_dyn_bo_uniform (sys : CoulombSystem eta ν) {m₀ : ℝ} (hm : ∀ i, sys.mass i = m₀)
    (hm0 : 1 ≤ m₀) {V : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0) {R : ℝ} {θ : ℝ → ℝ}
    (hL : freeDynBOL0 R0 ρ Rf δ ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hV : tv R θ = V)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in {r | ∃ i, L / 16 ≤ ‖particle r i‖}, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in {r | (∃ i, L / 16 ≤ ‖particle r i‖) ∧
      ∀ i, ‖particle r i‖ ≤ L / 8}, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
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
      let φ₀ := (prodCutoffL hm hm0 (sixteen_le_of_freeDynBOL0 hL)).toCutoff.chiW.cutL2
        (pos_of_freeDynBOL0 hL) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConstBO sys V F (prodCutoff16 hm hm0).D (prodCutoff16 hm hm0).C δ D *
            ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstBO sys V F (prodCutoff16 hm hm0).D (prodCutoff16 hm hm0).C δ D *
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
  exact free_dyn_grid_bo (sysAt sys P L) hL2 hθ hR hR0 hρ hone P hP (fun l => rfl)
    (prodCutoffL hm hm0 h16) hret hδ hflat (prodCutoffL_D_le hm hm0 h16)
    (prodCutoffL_C_le hm hm0 h16) hS hB (prodCutoffL_one hm hm0 h16) hSB
    (fun r hr a => (prodCutoffL_derivs hm hm0 h16 r hr a).1)
    (fun r hr a => (prodCutoffL_derivs hm hm0 h16 r hr a).2) hψd hHam hgrad ht hε hε1
    (fun s hs => by rw [hc]; exact hleak0 s hs) hleak1 hH1 hD a hf0 hf1 F hFf hfR
    (two_Rf_lt_of_freeDynBOL0 hL) m hκ hm8 hK

end Uniform

end FreeBoundary
