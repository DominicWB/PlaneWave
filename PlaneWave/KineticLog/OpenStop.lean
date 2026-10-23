import PlaneWave.KineticLog.OpenUniform

/-!
# Logarithmic kinetic bound, part 29: `cor:free-stopping-log` and `eq:free-kinetic-N`

* **`free_stopping_log`** (`cor:free-stopping-log`): under the hypotheses of
  `prop:free-kinetic-log` with leakage on `[0, τ]`, `τ > 0`, and a reference speed `v_p > 0`, the
  signed secant `[⟨T_p⟩(τ) - ⟨T_p⟩(0)]/(v_p τ)` of the free-space and grid trajectories differs by
  at most
  `(2C D_*²/v_p) K⁻³ [1 + (1 + log(2 + K))/τ] + (2C (𝒟_∞ + D_*)/v_p)(1 + τ⁻¹) ε`
  (the endpoint bound at `τ` and at `0`);
* `basis_count_arith`, **`free_kinetic_log_N`** (`eq:free-kinetic-N`): with the padded register
  `N = (4m + 1)³`, `N^{1/3} = 4m + 1`, the basis term is at most
  `(125/(4π³)) C D_*² (L³/N) [1 + t + log(2 + N^{1/3}/L)]`; the factor `L³` is kept.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter MeasureTheory Set PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic PlaneWaveGrid
  PlaneWaveGridDynamics FreeBoundary FSNormal

namespace KineticLog

attribute [local instance] FreeBoundary.unitAddCircleMeasureSpaceFB15
  FreeBoundary.unitAddCircleProbabilityMeasureFB15 FreeBoundary.molecularTorusFiniteMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The stopping estimate -/

/-- The arithmetic of the secant with a leakage term. -/
lemma secant_arith_free {a1 a0 b1 b0 C X Y vp τ K lg ε : ℝ} (hC : 0 ≤ C) (hvp : 0 < vp)
    (hτ : 0 < τ) (hK : 0 < K) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hε : 0 ≤ ε)
    (h1 : |a1 - b1| ≤ C * X * (1 + τ + lg) / K ^ 3 + C * Y * (1 + τ) * ε)
    (h0 : |a0 - b0| ≤ C * X * (1 + 0 + lg) / K ^ 3 + C * Y * (1 + 0) * ε) :
    |(a1 - a0) / (vp * τ) - (b1 - b0) / (vp * τ)| ≤
      2 * C * X / vp * (1 + (1 + lg) / τ) / K ^ 3 + 2 * C * Y / vp * (1 + 1 / τ) * ε := by
  have hvt : 0 < vp * τ := mul_pos hvp hτ
  have hK3 : 0 < K ^ 3 := by positivity
  have e : (a1 - a0) / (vp * τ) - (b1 - b0) / (vp * τ) = ((a1 - b1) - (a0 - b0)) / (vp * τ) := by
    ring
  rw [e, abs_div, abs_of_pos hvt, div_le_iff₀ hvt]
  have htri := abs_sub (a1 - b1) (a0 - b0)
  have hsum : |a1 - b1 - (a0 - b0)| ≤ C * X * (2 + τ + 2 * lg) / K ^ 3 + C * Y * (2 + τ) * ε := by
    have e1 : C * X * (2 + τ + 2 * lg) / K ^ 3 =
        C * X * (1 + τ + lg) / K ^ 3 + C * X * (1 + 0 + lg) / K ^ 3 := by ring
    have e2 : C * Y * (2 + τ) * ε = C * Y * (1 + τ) * ε + C * Y * (1 + 0) * ε := by ring
    rw [e1, e2]
    linarith
  refine hsum.trans ?_
  · have e3 : (2 * C * X / vp * (1 + (1 + lg) / τ) / K ^ 3 + 2 * C * Y / vp * (1 + 1 / τ) * ε) *
        (vp * τ) = C * X * (2 * τ + 2 * (1 + lg)) / K ^ 3 + C * Y * (2 * τ + 2) * ε := by
      field_simp
    rw [e3]
    have f1 : C * X * (2 + τ + 2 * lg) / K ^ 3 ≤ C * X * (2 * τ + 2 * (1 + lg)) / K ^ 3 := by
      apply div_le_div_of_nonneg_right _ hK3.le
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hX)
      linarith
    have f2 : C * Y * (2 + τ) * ε ≤ C * Y * (2 * τ + 2) * ε := by
      apply mul_le_mul_of_nonneg_right _ hε
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hY)
      linarith
    linarith

set_option maxHeartbeats 400000 in
/-- **`cor:free-stopping-log`** (general cutoff, (H_dom)): with leakage on `[0, τ]`, `τ > 0`, and
`v_p > 0`, the secants `[⟨T_p⟩(τ) - ⟨T_p⟩(0)]/(v_p τ)` of the free-space solution and of the grid
trajectory differ by at most
`(2C D_*²/v_p)[1 + (1 + log(2 + K))/τ]/K³ + (2C(𝒟_∞ + D_*)/v_p)(1 + 1/τ) ε`,
`C = freeKinC sys V_θ D̄`. -/
theorem free_stopping_log (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Dbar : ℝ} (hD1 : X.D1 ≤ Dbar) (hD2 : X.D2 ≤ Dbar)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 τ, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 τ, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁)
    {Dinf Dst : ℝ} (hDinf : ‖ψ 0‖ + ‖H 0‖ ≤ Dinf)
    (hDst : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst)
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
        (2 * Real.pi / L) x))) t)
    {vp : ℝ} (hvp : 0 < vp) :
    |(freeKinQ sys p₀ (grad τ) - freeKinQ sys p₀ (grad 0)) / (vp * τ) -
        (regExpect sys (gF L) p₀ (Ug τ (regCoeff m ((molecularPositionSynthesis eta).symm
            (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0))))) -
          regExpect sys (gF L) p₀ (Ug 0 (regCoeff m ((molecularPositionSynthesis eta).symm
            (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))) / (vp * τ)| ≤
      2 * freeKinC sys (tv R θ) Dbar * Dst ^ 2 / vp *
          (1 + (1 + Real.log (2 + 2 * Real.pi / L * m)) / τ) / (2 * Real.pi / L * m) ^ 3 +
        2 * freeKinC sys (tv R θ) Dbar * (Dinf + Dst) / vp * (1 + 1 / τ) * ε := by
  have hV := hθ.tv_nonneg
  have hD10 : 0 ≤ X.D1 := (abs_nonneg _).trans (X.d1 0 (p₀, 0))
  have hDb : 0 ≤ Dbar := hD10.trans hD1
  have hK8 : (8 : ℝ) ≤ 2 * Real.pi / L * m := (cellK0_scales hV hK).1
  have h1 := free_kinetic_log_endpoint sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hD1 hD2 hSm hBm
    hχB hSB hdS hd2S hψd hHam hgrad hτ.le hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm hK hκ Ug
    hg0 hgcomm hgderiv
  have h0 := free_kinetic_log_endpoint sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hD1 hD2 hSm hBm
    hχB hSB hdS hd2S hψd hHam hgrad le_rfl hε
    (fun s hs => hleak0 s ⟨hs.1, hs.2.trans hτ.le⟩) (fun s hs => hleak1 s ⟨hs.1, hs.2.trans hτ.le⟩)
    hdom0 hdom1 hDinf hDst p₀ m hm hK hκ Ug hg0 hgcomm hgderiv
  have hDinf0 : 0 ≤ Dinf := by linarith [norm_nonneg (ψ 0), norm_nonneg (H 0)]
  have hDst0 : 0 ≤ Dst := by
    linarith [norm_nonneg (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)), norm_nonneg h₀,
      norm_nonneg h₁]
  exact secant_arith_free (freeKinC_nonneg sys hV hDb) hvp hτ (by linarith) (sq_nonneg Dst)
    (by linarith) hε h1 h0

/-! ## The basis count -/

/-- `(4m+1)³ = N` has `N^{1/3} = 4m + 1`. -/
lemma cube_rpow_third (x : ℝ) (hx : 0 ≤ x) : (x ^ 3) ^ (1 / 3 : ℝ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- **The basis count**: with `K = 2πm/L` and `N = (4m + 1)³`,
`[1 + t + log(2 + K)]/K³ ≤ (125/(4π³)) (L³/N) [1 + t + log(2 + N^{1/3}/L)]`. -/
lemma basis_count_arith {L : ℝ} (hL : 0 < L) {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3 ≤
      125 / (4 * Real.pi ^ 3) * (L ^ 3 / ((4 * m + 1 : ℝ) ^ 3)) *
        (1 + t + Real.log (2 + ((4 * m + 1 : ℝ) ^ 3) ^ (1 / 3 : ℝ) / L)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  rw [cube_rpow_third _ (by positivity)]
  set x : ℝ := (4 * m + 1) / L with hx
  have hx0 : 0 < x := by positivity
  have hK0 : 0 < 2 * Real.pi / L * m := by positivity
  -- `K ≤ 2x`
  have hKx : 2 * Real.pi / L * m ≤ 2 * x := by
    rw [hx, div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right hL]
    nlinarith
  -- `log(2 + K) ≤ 1 + log(2 + x)`
  have hlog : Real.log (2 + 2 * Real.pi / L * m) ≤ 1 + Real.log (2 + x) := by
    have h1 : 2 + 2 * Real.pi / L * m ≤ 2 * (2 + x) := by linarith
    have h2 : Real.log (2 + 2 * Real.pi / L * m) ≤ Real.log (2 * (2 + x)) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (by positivity)] at h2
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    linarith
  have hlx : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  have hQ : 1 + t + Real.log (2 + 2 * Real.pi / L * m) ≤ 2 * (1 + t + Real.log (2 + x)) := by
    linarith
  -- `1/K³ ≤ (125/(8π³)) L³/N`
  have hN0 : 0 < (4 * (m : ℝ) + 1) ^ 3 := by positivity
  have hcube : (4 * (m : ℝ) + 1) ^ 3 ≤ 125 * (m : ℝ) ^ 3 := by
    have h1 : 4 * (m : ℝ) + 1 ≤ 5 * m := by linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 3
    nlinarith
  have hK3 : 1 / (2 * Real.pi / L * m) ^ 3 ≤
      125 / (8 * Real.pi ^ 3) * (L ^ 3 / (4 * (m : ℝ) + 1) ^ 3) := by
    have e : 1 / (2 * Real.pi / L * m) ^ 3 = L ^ 3 / (8 * Real.pi ^ 3 * (m : ℝ) ^ 3) := by
      field_simp
      norm_num
    rw [e, div_le_iff₀ (by positivity)]
    have e2 : 125 / (8 * Real.pi ^ 3) * (L ^ 3 / (4 * (m : ℝ) + 1) ^ 3) *
        (8 * Real.pi ^ 3 * (m : ℝ) ^ 3) = L ^ 3 * (125 * (m : ℝ) ^ 3 / (4 * (m : ℝ) + 1) ^ 3) := by
      field_simp
    rw [e2]
    have h3 : 1 ≤ 125 * (m : ℝ) ^ 3 / (4 * (m : ℝ) + 1) ^ 3 := by
      rw [le_div_iff₀ hN0]
      linarith
    have hL3 : 0 < L ^ 3 := by positivity
    nlinarith
  have hQ0 : 0 ≤ 1 + t + Real.log (2 + 2 * Real.pi / L * m) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 2 * Real.pi / L * m by linarith)
    linarith
  calc (1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3
      = (1 + t + Real.log (2 + 2 * Real.pi / L * m)) * (1 / (2 * Real.pi / L * m) ^ 3) := by
        ring
    _ ≤ (2 * (1 + t + Real.log (2 + x))) *
          (125 / (8 * Real.pi ^ 3) * (L ^ 3 / (4 * (m : ℝ) + 1) ^ 3)) :=
        mul_le_mul hQ hK3 (by positivity) (by positivity)
    _ = 125 / (4 * Real.pi ^ 3) * (L ^ 3 / (4 * (m : ℝ) + 1) ^ 3) * (1 + t + Real.log (2 + x)) := by
        field_simp
        ring

set_option maxHeartbeats 400000 in
/-- **`eq:free-kinetic-N`**: with the padded register `N = (4m + 1)³` (`N^{1/3} = 4m + 1`), the
bound of `prop:free-kinetic-log` reads
`(125/(4π³)) C D_*² (L³/N) [1 + t + log(2 + N^{1/3}/L)] + C (𝒟_∞ + D_*) (1 + t) ε`:
at fixed budgets `O((L³/N)[1 + t + log(2 + N^{1/3}/L)] + (1 + t) ε)`; the factor `L³` is kept. -/
theorem free_kinetic_log_N (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Dbar : ℝ} (hD1 : X.D1 ≤ Dbar) (hD2 : X.D2 ≤ Dbar)
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
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁)
    {Dinf Dst : ℝ} (hDinf : ‖ψ 0‖ + ‖H 0‖ ≤ Dinf)
    (hDst : ‖X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)‖ + ‖h₀‖ + ‖h₁‖ ≤ Dst)
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
    |freeKinQ sys p₀ (grad t) - regExpect sys (gF L) p₀ (Ug t (regCoeff m
        ((molecularPositionSynthesis eta).symm (X.chiW.cutL2 (pos_of_two_pi_le hL2) (ψ 0)))))| ≤
      125 / (4 * Real.pi ^ 3) * freeKinC sys (tv R θ) Dbar * Dst ^ 2 *
          (L ^ 3 / ((4 * m + 1 : ℝ) ^ 3)) *
          (1 + t + Real.log (2 + ((4 * m + 1 : ℝ) ^ 3) ^ (1 / 3 : ℝ) / L)) +
        freeKinC sys (tv R θ) Dbar * (Dinf + Dst) * (1 + t) * ε := by
  have hL := pos_of_two_pi_le hL2
  have hV := hθ.tv_nonneg
  have hD10 : 0 ≤ X.D1 := (abs_nonneg _).trans (X.d1 0 (p₀, 0))
  have hDb : 0 ≤ Dbar := hD10.trans hD1
  have h := free_kinetic_log_endpoint sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hD1 hD2 hSm hBm
    hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 hDinf hDst p₀ m hm hK hκ Ug
    hg0 hgcomm hgderiv
  refine h.trans ?_
  have hb := basis_count_arith hL (by omega : 1 ≤ m) ht
  have hC := freeKinC_nonneg sys hV hDb
  have hCD : 0 ≤ freeKinC sys (tv R θ) Dbar * Dst ^ 2 := mul_nonneg hC (sq_nonneg _)
  have e1 : freeKinC sys (tv R θ) Dbar * Dst ^ 2 * (1 + t + Real.log (2 + 2 * Real.pi / L * m)) /
      (2 * Real.pi / L * m) ^ 3 = freeKinC sys (tv R θ) Dbar * Dst ^ 2 *
        ((1 + t + Real.log (2 + 2 * Real.pi / L * m)) / (2 * Real.pi / L * m) ^ 3) := by ring
  have e2 : 125 / (4 * Real.pi ^ 3) * freeKinC sys (tv R θ) Dbar * Dst ^ 2 *
      (L ^ 3 / ((4 * m + 1 : ℝ) ^ 3)) *
      (1 + t + Real.log (2 + ((4 * m + 1 : ℝ) ^ 3) ^ (1 / 3 : ℝ) / L)) =
      freeKinC sys (tv R θ) Dbar * Dst ^ 2 * (125 / (4 * Real.pi ^ 3) *
        (L ^ 3 / ((4 * m + 1 : ℝ) ^ 3)) *
        (1 + t + Real.log (2 + ((4 * m + 1 : ℝ) ^ 3) ^ (1 / 3 : ℝ) / L))) := by ring
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left hb hCD
  linarith

end KineticLog
