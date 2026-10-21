import PlaneWave.FreeBoundary.GridObservablePhysical
import PlaneWave.FreeBoundary.FreeDynamicsGrid

/-!
# `thm:grid-dyn-sharp` for `g_L` with `L`-uniform constants

Stage 4 of the `L`-uniform grid dynamics: the theorems of
`PlaneWave.FreeBoundary.GridDynamicsTheorem` (`thm_grid_dyn_sharp_gL`) and
`PlaneWave.FreeBoundary.FreeDynamicsGrid` (`free_dyn_grid_gL`) for `L ≥ 2π`, with constants
`(A₁, A₂, A₃) = gridConstsSharp_gLU` that do not depend on `L`, `m`, `K` or `t`:

* `gridPhiU`, `gridConstsSharp_gLU`: the constants, as functions of the system (masses, charges,
  the total variation `V_θ` of the range cut), the Hardy constant, the data
  `(‖ψ₀‖, ‖H ψ₀‖, ‖H² ψ₀‖)` and the physical moments of the observable: `C_χ = Σ |χ̂(ν)|`,
  `‖O‖` (the norm of the convolution with `χ̂`), `D₂ = Σ |gν|² |χ̂(ν)|`, `D₄ = Σ |gν|⁴ |χ̂(ν)|`;
* `grid_observable_rate_sharp_gLU`: the rates on the Fourier side,
  `A₁ K⁻⁵ + A₂ t K⁻³ + A₃ K^{-5/2} τ_χ(K) + ‖ψ₀‖² τ_χ^∞(m)`;
* `grid_observable_position_sharp_gLU`: the same four-term bound in position space;
* **`thm_grid_dyn_sharp_gLU`**: under `(Hχ)`, `(A₁ + (A₃ 3^{5/2} + ‖ψ₀‖²) C_{χ,5}) K⁻⁵ + A₂ t K⁻³`;
* **`free_dyn_grid_gLU`**: `prop:free-dyn`, the two steps composed, with the `L`-uniform grid
  constants.

The constants do not depend on `L` except through their inputs: the total variation `V_θ` of the
range cut, the data `(‖ψ₀‖, ‖H ψ₀‖, ‖H² ψ₀‖)` and the moments of `χ`. For `χ(x_a) = f((L·rep x)_a)`
these moments are Riemann sums of moments of `f̂`; their bounds uniform in `L`, for a fixed Schwartz
`f`, and the resulting form of `free_dyn_grid_gLU` are in
`PlaneWave.FreeBoundary.ObservableMomentsUniform`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLgamma_pos gLref gLNucData regParticlesOfG gLzU gLzU_nonneg gLAU
  gLGridCoupling)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The `L`-uniform constants -/

section Constants

/-- The second-moment constant `Φ_U` of the backward flows of the smeared states, `L`-free: a
function of the data `s0 = ‖ψ₀‖`, `hu = ‖H ψ₀‖`, `hs = ‖H ψ₀‖`, `hv = ‖H² ψ₀‖` and of the moments
`C_χ`, `D₂`, `D₄` of the observable. -/
noncomputable def gridPhiU (sys : CoulombSystem eta ν) (V Hunit Cχ D2 D4 s0 hu hs hv : ℝ) : ℝ :=
  let b : ℝ := relBU sys V Hunit
  let Ξ₀ : ℝ := 2 * hu + 2 * b * s0
  let Ξ₁ : ℝ := 2 * hv + 2 * b * hs
  let M₀ : ℝ := sys.maxMass * (s0 + 2 * Ξ₀)
  let C₀ : ℝ := gLtailMU sys V Hunit M₀
  let cJ : ℝ := gridFlowConstU sys V
  let A : ℝ := gLAU sys V
  let σ : ℝ := sigmaU sys V
  let Xb : ℝ := 5 / 3 * M₀ + cJ * s0
  let Wo : ℝ := (2 + 12 * sys.maxMass) * Cχ * Xb + ((3 + 12 * sys.maxMass) * Cχ + 14 * D2) * s0
  let Q : ℝ := 16 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 + 30 * C₀ ^ 2
  let ξ : ℝ := s0 + 4 * Ξ₀ + 2 * (eta * Real.sqrt Q)
  let F : ℝ := flow2 1 cJ A σ ξ M₀ s0
  let o : ℝ := 8 * Cχ * F + 8 * D4 * s0
  flow2 1 cJ A σ o Wo (Cχ * s0)

/-- **The constants `(A₁, A₂, A₃)` of `thm:grid-dyn-sharp` for `g_L`, `L`-free.** -/
noncomputable def gridConstsSharp_gLU (sys : CoulombSystem eta ν)
    (V Hunit Cχ CO D2 D4 s0 hu hs hv : ℝ) : ℝ × ℝ × ℝ :=
  let b : ℝ := relBU sys V Hunit
  let Ξ₀ : ℝ := 2 * hu + 2 * b * s0
  let Ξ₁ : ℝ := 2 * hv + 2 * b * hs
  let M₀ : ℝ := sys.maxMass * (s0 + 2 * Ξ₀)
  let Ct : ℝ → ℝ := fun M => gLtailMU sys V Hunit M
  let τ₁ : ℝ := 2 * sys.maxMass * (2 * sys.maxMass * Ξ₁ + Ct M₀)
  let β₄ : ℝ := 128 * sys.maxMass * (128 * sys.maxMass * Ξ₁ + 8 * Ct M₀)
  let δ₁ : ℝ := eta * τ₁
  let z : ℝ := gLzU sys V
  let cJ : ℝ := gridFlowConstU sys V
  let Xb : ℝ := 5 / 3 * M₀ + cJ * s0
  let Wo : ℝ := (2 + 12 * sys.maxMass) * Cχ * Xb + ((3 + 12 * sys.maxMass) * Cχ + 14 * D2) * s0
  let W : ℝ := 5 / 3 * Wo + cJ * (Cχ * s0)
  let cF : ℝ := 18 * Real.sqrt 8 * Real.sqrt 79 * z
  let T : ℝ := 3072 * sys.maxMass ^ 2 * gridPhiU sys V Hunit Cχ D2 D4 s0 hu hs hv * (1 + z)
  (2 * δ₁ * (Cχ * τ₁ + CO * δ₁) + CO * δ₁ ^ 2 + Cχ * τ₁ ^ 2,
    2 * (eta * δ₁ * Ct (sys.maxMass * W) +
      (cF * β₄ * (sys.maxMass * W) + cF * T * M₀ + 52 * T * β₄)),
    2 * δ₁ * s0)

lemma gridPhiU_nonneg (sys : CoulombSystem eta ν) {V Hunit Cχ D2 D4 s0 hu hs hv : ℝ}
    (hV : 0 ≤ V) (hH : 0 ≤ Hunit) (hCχ : 0 ≤ Cχ) (hD2 : 0 ≤ D2) (hD4 : 0 ≤ D4) (h0 : 0 ≤ s0)
    (h1 : 0 ≤ hu) : 0 ≤ gridPhiU sys V Hunit Cχ D2 D4 s0 hu hs hv := by
  have hb := relBU_nonneg sys hV hH
  have hM := sys.one_le_maxMass
  have hcJ := gridFlowConstU_nonneg sys hV
  have hA : 0 ≤ gLAU sys V := by
    unfold gLAU
    have := gLzU_nonneg sys hV
    positivity
  have hσ := sigmaU_nonneg sys hV
  have hΞ₀ : 0 ≤ 2 * hu + 2 * relBU sys V Hunit * s0 := by positivity
  have hM₀ : 0 ≤ sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0)) := by positivity
  have hXb : 0 ≤ 5 / 3 * (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0))) +
      gridFlowConstU sys V * s0 := by positivity
  show 0 ≤ flow2 _ _ _ _ _ _ _
  refine flow2_nonneg hcJ hA hσ ?_ ?_ (mul_nonneg hCχ h0)
  · refine add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCχ) ?_)
      (mul_nonneg (mul_nonneg (by norm_num) hD4) h0)
    refine flow2_nonneg hcJ hA hσ ?_ hM₀ h0
    have hQ : 0 ≤ 2 * (eta * Real.sqrt (16 * (2 * hu + 2 * relBU sys V Hunit * s0) ^ 2 +
        120 * sys.maxMass ^ 2 * (2 * hv + 2 * relBU sys V Hunit * hs) ^ 2 +
        30 * gLtailMU sys V Hunit
          (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0))) ^ 2)) :=
      mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    have hX0 : 0 ≤ 4 * (2 * hu + 2 * relBU sys V Hunit * s0) := by positivity
    exact add_nonneg (add_nonneg h0 hX0) hQ
  · exact add_nonneg (mul_nonneg (mul_nonneg (by linarith) hCχ) hXb)
      (mul_nonneg (add_nonneg (mul_nonneg (by linarith) hCχ) (by positivity)) h0)

lemma gridConstsSharp_gLU_nonneg_three (sys : CoulombSystem eta ν) {V Hunit : ℝ} (hV : 0 ≤ V)
    (hH : 0 ≤ Hunit) (Cχ CO D2 D4 : ℝ) {s0 hu hs hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu)
    (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    0 ≤ (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).2.2 := by
  have hb := relBU_nonneg sys hV hH
  have hM := sys.one_le_maxMass
  have hκ : 0 ≤ gLtailMU sys V Hunit
      (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0))) :=
    gLtailMU_nonneg sys hV hH (by positivity)
  simp only [gridConstsSharp_gLU]
  positivity

/-- `g k₀ ≤ 2` for the first threshold `k₀ = kZero g` and `0 < g ≤ 1`. -/
lemma mul_kZero_le_two {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) : g * (kZero g : ℝ) ≤ 2 := by
  unfold kZero
  rcases le_total 2 ⌈1 / g⌉₊ with h | h
  · rw [max_eq_right h]
    have h1 : (⌈1 / g⌉₊ : ℝ) < 1 / g + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : g * (⌈1 / g⌉₊ : ℝ) < g * (1 / g + 1) := mul_lt_mul_of_pos_left h1 hg
    have e : g * (1 / g + 1) = 1 + g := by field_simp
    linarith
  · rw [max_eq_left h]
    push_cast
    linarith

end Constants

/-! ## The rates on the Fourier side -/

section Rates

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  {θ : ℝ → ℝ} (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 0 < L) {R : ℝ} (hθ : Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hθ hPeriodic in
/-- **`thm:grid-dyn-sharp` for `g_L`, rates, `L`-uniform constants (Fourier side).** For
`L ≥ 2π`, `m ≥ 8` and `K = g m ≥ 8`, and `χ` with `D⁽⁴⁾_χ < ∞`,
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤ A₁ K^{-5} + A₂ t K^{-3} + A₃ K^{-5/2} τ_χ(K)
+ ‖ψ₀‖² τ_χ^∞(m)`, with `(A₁, A₂, A₃) = gridConstsSharp_gLU` at the physical moments
`(C_χ, ‖O‖, g² D'_χ, g⁴ D⁽⁴⁾_χ)` of `χ`; the constants do not depend on `L`, `K` or `t`. -/
theorem grid_observable_rate_sharp_gLU (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    (hL2 : 2 * Real.pi ≤ L) (hH : 0 ≤ Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (a : Fin eta) (χ : Lattice3 → ℂ) (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (hχ4 : Summable fun ν => nsq ν ^ 2 * ‖χ ν‖)
    (hreal : ∀ ν, χ (-ν) = conj (χ ν)) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let K : ℝ := g * m
    let A := gridConstsSharp_gLU sys (tv R θ) Hunit (∑' ν, ‖χ ν‖) ‖convOp (eta := eta) a χ‖
      (g ^ 2 * momTwo χ) (g ^ 4 * momFour χ) ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then ‖χ ν‖ else 0
    let ψg := Ug t (regCoeff m (molecularH2StateMap eta g u₀))
    ‖⟪U t (molecularH2StateMap eta g u₀), convOp a χ (U t (molecularH2StateMap eta g u₀))⟫_ℂ -
        ⟪ψg, gridObs a χ ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖molecularH2StateMap eta g u₀‖ ^ 2 * supTail χ m := by
  intro g K A τχ ψg
  have hM := sys.one_le_maxMass
  have hg : 0 < g := by positivity
  have hg1 : g ≤ 1 := PlaneWaveGridG.g_le_one hL2
  have hV := hθ.tv_nonneg
  have hγ : 0 ≤ gLgamma L (tv R θ) := (gLgamma_pos hL hV).le
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hK₄ : 1 ≤ g * ((m / 4 : ℕ) : ℝ) := by
    have : g * (m : ℝ) ≤ 8 * (g * ((m / 4 : ℕ) : ℝ)) := by nlinarith
    have hK' : (8 : ℝ) ≤ g * (m : ℝ) := hK
    linarith
  have hKpos : 0 < g * (m : ℝ) := by
    have hK' : (8 : ℝ) ≤ g * (m : ℝ) := hK
    linarith
  have hK₂pos : 0 < g * ((2 * m : ℕ) : ℝ) := by
    have : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    rw [this]
    linarith
  have hK₄pos : 0 < g * ((m / 4 : ℕ) : ℝ) := by linarith
  have hscale : ∀ X : ℝ, 0 < X → Real.sqrt (1 / X) ^ 2 * X = 1 := by
    intro X hX
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hS0 : 0 ≤ ‖molecularH2StateMap eta g u₀‖ := norm_nonneg _
  have hb := relBU_nonneg sys hV hH
  have hΞ₀ : 0 ≤ 2 * ‖H u₀‖ + 2 * relBU sys (tv R θ) Hunit * ‖molecularH2StateMap eta g u₀‖ := by
    positivity
  have hΞ₁ : 0 ≤ 2 * ‖H v₀‖ + 2 * relBU sys (tv R θ) Hunit * ‖molecularH2StateMap eta g v₀‖ := by
    positivity
  have hCt : ∀ M, 0 ≤ M → 0 ≤ gLtailMU sys (tv R θ) Hunit M :=
    fun M hM' => gLtailMU_nonneg sys hV hH hM'
  have hM₀ : 0 ≤ sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relBU sys (tv R θ) Hunit * ‖molecularH2StateMap eta g u₀‖)) := by
    positivity
  have hCχ : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hτχ : 0 ≤ τχ := tsum_nonneg fun ν => by split_ifs <;> simp
  have hZg : 0 ≤ Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (gLgamma L (tv R θ)) := Zc_nonneg hγ
  have hz := gLzU_nonneg sys hV
  have hZz : Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (gLgamma L (tv R θ)) ≤
      gLzU sys (tv R θ) * g := by
    have hcoup : sys.maxMass * Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (gLgamma L (tv R θ)) = gLGridCoupling sys L (tv R θ) := rfl
    rw [PlaneWaveGridG.gLGridCoupling_eq sys hL] at hcoup
    have := mul_le_mul_of_nonneg_right hM hZg
    linarith
  have hcJ := gridFlowConstU_nonneg sys hV
  have hD2 : 0 ≤ g ^ 2 * momTwo χ :=
    mul_nonneg (sq_nonneg g) (tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _))
  have hD4 : 0 ≤ g ^ 4 * momFour χ := mul_nonneg (by positivity) (momFour_nonneg χ)
  have hXb : 0 ≤ 5 / 3 * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
      2 * (2 * ‖H u₀‖ + 2 * relBU sys (tv R θ) Hunit * ‖molecularH2StateMap eta g u₀‖))) +
      gridFlowConstU sys (tv R θ) * ‖molecularH2StateMap eta g u₀‖ := by positivity
  have hW : 0 ≤ 5 / 3 * ((2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) *
      (5 / 3 * (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
        2 * (2 * ‖H u₀‖ + 2 * relBU sys (tv R θ) Hunit * ‖molecularH2StateMap eta g u₀‖))) +
        gridFlowConstU sys (tv R θ) * ‖molecularH2StateMap eta g u₀‖) +
      ((3 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) + 14 * (g ^ 2 * momTwo χ)) *
        ‖molecularH2StateMap eta g u₀‖) +
      gridFlowConstU sys (tv R θ) * ((∑' ν, ‖χ ν‖) * ‖molecularH2StateMap eta g u₀‖) := by
    positivity
  have hΦ := gridPhiU_nonneg sys (hs := ‖molecularH2StateMap eta g v₀‖) (hv := ‖H v₀‖) hV hH hCχ
    hD2 hD4 hS0 (norm_nonneg (H u₀))
  have hτφ0 : 0 ≤ sys.maxMass ^ 2 * (rPhys g m * gridPhiU sys (tv R θ) Hunit (∑' ν, ‖χ ν‖)
      (g ^ 2 * momTwo χ) (g ^ 4 * momFour χ) ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖) / (g * (((m / 4 : ℕ) : ℝ) + 1)) ^ 4 := by
    have : 0 ≤ rPhys g m := by unfold rPhys; positivity
    positivity
  have h := grid_observable_error_sharp_gLU sys L H hKernel Hunit hL hθ hPeriodic hC hL2 hH U h0
    hgraph hderiv m hm hκ Ug hg0 hgcomm hgderiv (Real.sqrt (1 / (g * (m : ℝ))))
    (Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))) (Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))) hK₄
    (Real.sqrt_nonneg _) (hscale _ hKpos) (Real.sqrt_nonneg _) (hscale _ hK₂pos)
    (Real.sqrt_nonneg _) (hscale _ hK₄pos) u₀ v₀ huv a χ hχ1 hχ2 hχ4 hreal (kZero g)
    (two_le_kZero g) (one_le_mul_kZero hg) (mul_kZero_le_two hg hg1) ht
  rw [relB_gL_eq_U sys hL2 (tv R θ) hH] at h
  refine h.trans ?_
  exact grid_rate_arith_sharpP (η := (eta : ℝ)) (mm := sys.maxMass)
    (Ξ₁ := 2 * ‖H v₀‖ + 2 * relBU sys (tv R θ) Hunit * ‖molecularH2StateMap eta g v₀‖)
    (C₀ := gLtailMU sys (tv R θ) Hunit
      (sys.maxMass * (‖molecularH2StateMap eta g u₀‖ +
        2 * (2 * ‖H u₀‖ + 2 * relBU sys (tv R θ) Hunit * ‖molecularH2StateMap eta g u₀‖))))
    (g := g) (t := t) (S0 := ‖molecularH2StateMap eta g u₀‖) (sT := supTail χ m)
    (Cχ := ∑' ν, ‖χ ν‖) (CO := ‖convOp (eta := eta) a χ‖) (τχ := τχ)
    (Zg := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (gLgamma L (tv R θ)))
    (Φ := gridPhiU sys (tv R θ) Hunit (∑' ν, ‖χ ν‖) (g ^ 2 * momTwo χ) (g ^ 4 * momFour χ)
      ‖molecularH2StateMap eta g u₀‖ ‖H u₀‖ ‖molecularH2StateMap eta g v₀‖ ‖H v₀‖)
    (z := gLzU sys (tv R θ)) (m := m) (Ct := fun M => gLtailMU sys (tv R θ) Hunit M)
    (Nat.cast_nonneg eta) hM hΞ₁ (hCt _ hM₀) hg hg1 hm hK ht hS0 hCχ (norm_nonneg _) hτχ hZg hZz
    hz hM₀ hW hCt hΦ hτφ0 le_rfl

end Rates


/-! ## Position space and `(Hχ)` -/

section PositionTheorem

/-- The `L`-uniform constants of `thm:grid-dyn-sharp` at a torus observable `χ` (in the reflected
grid frame) and the data `‖ψ₀‖`, `‖H ψ₀‖`, `‖H² ψ₀‖`: `gridConstsSharp_gLU` at the canonical
Hardy constant and the physical moments `C_χ`, `‖O‖`, `g² D'_χ`, `g⁴ D⁽⁴⁾_χ` of `χ(-·)`. -/
noncomputable def gridConstsPosU (sys : CoulombSystem eta ν) (L V : ℝ) (a : Fin eta)
    (χ : C(UnitAddTorus (Fin 3), ℂ)) (s0 hu hv : ℝ) : ℝ × ℝ × ℝ :=
  gridConstsSharp_gLU sys V molecularCanonicalUnitHardyConstant
    (∑' ν, ‖mFourierCoeff (chiRefl χ) ν‖) ‖convOp (eta := eta) a (mFourierCoeff (chiRefl χ))‖
    ((2 * Real.pi / L) ^ 2 * momTwo (mFourierCoeff (chiRefl χ)))
    ((2 * Real.pi / L) ^ 4 * momFour (mFourierCoeff (chiRefl χ))) s0 hu hu hv

/-- **Observable error on the grid, position space, sharp, `g_L`, `L`-uniform constants**
(`thm:grid-dyn-sharp`, `L ≥ 2π`): for `m ≥ 8`, `K ≥ 8` and `t ≥ 0`,
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤
  A₁ K^{-5} + A₂ t K^{-3} + A₃ K^{-5/2} τ_χ(K) + ‖ψ₀‖² τ_χ^∞(m)` with
`(A₁, A₂, A₃) = gridConstsPosU`, which do not depend on `K` or `t` and depend on `L` only through
`V_θ`, the data and the moments of `χ`. -/
theorem grid_observable_position_sharp_gLU (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2)
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
    let A := gridConstsPosU sys L (tv R θ) a χ ‖ψ₀‖ ‖h₀‖ ‖h₁‖
    let τχ : ℝ := ∑' ν, if K < g * Real.sqrt (latticeNormSq ν) then
      ‖mFourierCoeff (chiRefl χ) ν‖ else 0
    let ψg := posConj (Ug t) (idft (regCoeff m ((molecularPositionSynthesis eta).symm ψ₀)))
    ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
      A.1 * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3 + A.2.2 * Real.sqrt (1 / K) ^ 5 * τχ +
        ‖ψ₀‖ ^ 2 * supTail (mFourierCoeff (chiRefl χ)) m := by
  intro g K A τχ ψg
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hPeriodic := canonicalPeriodicCoulombHardyBound_explicit
  obtain ⟨H, hKernel, -⟩ := exists_gLFourierH2Operator sys hL hθ
    molecularCanonicalUnitHardyConstant hPeriodic
  have hiff := hasGLHamiltonian_iff_H2 sys hL hθ hR H hKernel
  set Φ := molecularPositionSynthesis eta with hΦ
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
  obtain ⟨u₀, hu₀1, hu₀2⟩ := (hiff ψ₀ h₀).mp hψ₀
  obtain ⟨v₀, hv₀1, hv₀2⟩ := (hiff h₀ h₁).mp hh₀
  have huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀ :=
    Φ.injective (hu₀2.trans hv₀1.symm)
  have hx₀ : Φ.symm ψ₀ = molecularH2StateMap eta (2 * Real.pi / L) u₀ := by
    rw [← hu₀1, LinearIsometryEquiv.symm_apply_apply]
  have hO : ∀ x, ⟪Φ x, mulCLM (regFun a χ) (Φ x)⟫_ℂ =
      ⟪x, convOp a (mFourierCoeff (chiRefl χ)) x⟫_ℂ := by
    intro x
    rw [← synth_mulCLM a hχ1 x, ← LinearIsometryEquiv.inner_map_map Φ,
      LinearIsometryEquiv.apply_symm_apply]
  have hψt : U t ψ₀ = Φ (UF t (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    rw [hUF, LinearIsometryEquiv.apply_symm_apply, hu₀1]
  have hdψ : dft ψg = Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)) := by
    show dft (posConj (Ug t) (idft (regCoeff m (Φ.symm ψ₀)))) = _
    rw [dft_posConj, dft_idft, hx₀]
  have hψg : ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ =
      ⟪Ug t (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)),
        gridObs a (mFourierCoeff (chiRefl χ)) (Ug t
            (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) u₀)))⟫_ℂ := by
    rw [← inner_dft_dft ψg, dft_posObs a hχ1, hdψ]
  rw [hψt, hO, hψg]
  have h := grid_observable_rate_sharp_gLU sys L H hKernel molecularCanonicalUnitHardyConstant hL hθ
    hPeriodic (gLmassConst_nonneg sys L hθ.tv_nonneg _) hL2
    molecularCanonicalUnitHardyConstant_nonneg
    UF h0F hgraphF hderivF m hm hK hκ Ug hg0 hgcomm hgderiv u₀ v₀ huv a (mFourierCoeff (chiRefl χ))
    hχ1 hχ2 hχ4 (fun ν => mFourierCoeff_neg_of_real (chiRefl_real hreal) ν) ht
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

/-! ## `thm:grid-dyn-sharp` for `g_L`, `L`-uniform -/

section Final

/-- **`thm:grid-dyn-sharp` for `g_L` with `L`-uniform constants, for a given propagator**
(`L ≥ 2π`): the grid part of `thm_grid_dyn_sharp_gLU` for any `U` that preserves the graph of
`H_L` and solves the Schrödinger equation on it. -/
theorem grid_dyn_sharp_gLU_of_propagator (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2)
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
        let A := gridConstsPosU sys L (tv R θ) a χ ‖ψ₀‖ ‖h₀‖ ‖h₁‖
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
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hc := HChi_chiRefl hc0
  have hχ1 := hc.1
  have hχ2 := summable_nsq_of_HChi hg hc
  have hχ4 := summable_nsq_sq_of_HChi hg hc
  have h := grid_observable_position_sharp_gLU sys hL2 hθ hR U h0 hgraph hderiv m hm hK hκ Ur hr0
    hrcomm hrderiv ψ₀ h₀ h₁ hψ₀ hh₀ a χ hχ1 hχ2 hχ4 hreal ht
  have hA₃ : 0 ≤ A.2.2 :=
    gridConstsSharp_gLU_nonneg_three sys hθ.tv_nonneg molecularCanonicalUnitHardyConstant_nonneg
      _ _ _ _ (norm_nonneg ψ₀) (norm_nonneg h₀) (norm_nonneg h₀) (norm_nonneg h₁)
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

/-- **`thm:grid-dyn-sharp` for the `g_L` kernel with `L`-uniform constants** (`L ≥ 2π`): the
statement of `thm_grid_dyn_sharp_gL` with `(A₁, A₂, A₃) = gridConstsPosU`, functions of the system,
of the total variation `V_θ` of the range cut, of `(‖ψ₀‖, ‖H ψ₀‖, ‖H² ψ₀‖)` and of the physical
moments `C_χ`, `‖O‖`, `g² D'_χ`, `g⁴ D⁽⁴⁾_χ` of the observable only:
`|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫| ≤
  (A₁ + (A₃ 3^{5/2} + ‖ψ₀‖²) C_{χ,5}) K^{-5} + A₂ t K^{-3}`. -/
theorem thm_grid_dyn_sharp_gLU (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) :
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
          let A := gridConstsPosU sys L (tv R θ) a χ ‖ψ₀‖ ‖h₀‖ ‖h₁‖
          8 ≤ m → 8 ≤ (2 * Real.pi / L) * m → ∀ t : ℝ, 0 ≤ t →
            let K : ℝ := (2 * Real.pi / L) * m
            let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm ψ₀)))
            ‖⟪U t ψ₀, mulCLM (regFun a χ) (U t ψ₀)⟫_ℂ - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
              (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖ψ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
                A.2.1 * t * (1 / K) ^ 3 := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  obtain ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq⟩ := exists_gLPropagator sys hL hθ hR
  exact ⟨U, h0, hadd, hcont, hgraph, hderiv, huniq, fun m κ hκ =>
    grid_dyn_sharp_gLU_of_propagator sys hL2 hθ hR U h0 hgraph hderiv m κ hκ⟩

end Final

/-! ## `prop:free-dyn` with the `L`-uniform grid constants -/

section FreeDyn

/-- **`prop:free-dyn`, the two steps composed, `L`-uniform grid constants** (`L ≥ 2π`): the
statement of `free_dyn_grid_gL` with `(A₁, A₂, A₃) = gridConstsPosU` at `(‖φ(0)‖, ‖h₀‖, ‖h₁‖)`:
`|∫ f(r_a) |ψ_∞(t, r)|² dr - ⟨ψ_g(t), O_g ψ_g(t)⟩| ≤ ε² + (‖ψ_∞(t)‖ + ‖ψ_∞(0)‖) C ε t +
  (A₁ + (A₃ 3^{5/2} + ‖φ(0)‖²) C_{χ,5}) K⁻⁵ + A₂ t K⁻³`. -/
theorem free_dyn_grid_gLU (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
      let φ₀ := X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let A := gridConstsPosU sys L (tv R θ) a χ ‖φ₀‖ ‖h₀‖ ‖h₁‖
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.commConst * ε * t) +
          ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖φ₀‖ ^ 2) * CM 5) * (1 / K) ^ 5 +
            A.2.1 * t * (1 / K) ^ 3) := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
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
    grid_dyn_sharp_gLU_of_propagator sys hL2 hθ hR U h0 hgraph hderiv m κ hκ
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

end FreeDyn

end FreeBoundary
