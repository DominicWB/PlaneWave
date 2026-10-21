import PlaneWave.FreeBoundary.CutStateDomain
import PlaneWave.FreeBoundary.Complexity

/-!
# `prop:free-dyn` without the domain hypotheses: the non-Born–Oppenheimer case

`free_dyn_grid_gLU_schwartz` assumes that the transplanted initial state `φ(0) = T(χ ψ_∞(0))` lies
in `D(H_L²)` (`hdom0`, `hdom1`), with constants depending on `(‖φ(0)‖, ‖H_L φ(0)‖, ‖H_L² φ(0)‖)`.
For the non-Born–Oppenheimer system (no clamped nuclei) and a mass-weighted cutoff, these
hypotheses follow from `cut_state_domain`, and the constants are bounded by `L`-free ones:

* `gridPhiU_mono_data`, `gridConstsSharp_gLU_mono_data`: the constants are monotone in the data
  `(‖ψ₀‖, ‖Hψ₀‖, ‖Hψ₀‖, ‖H²ψ₀‖)`;
* `norm_zeroModeShift_le`: `|C₀| ≤ Q/4` for `L ≥ 2π`, `R ≤ L/2` (`Q = zeroWeight`);
* **`free_dyn_grid_nbo`**: `prop:free-dyn` for a fixed Schwartz observable, without `hdom0`,
  `hdom1`: the constants are `gridConstsSharp_gLU` at the data `(N, Λ N, Λ N, Λ² N)`, `N` the
  free-space data norm of `ψ_∞(0)` and `Λ = domConst` at `c₀ = Q/4` and bounds `D̄ ≥ D`,
  `C̄ ≥ C` for the cutoff; the commutator constant is `3η (D̄ + D̄/2)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap
open Finset Set MeasureTheory
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLgamma_pos gLref gLNucData regParticlesOfG gLzU gLzU_nonneg gLAU
  gLGridCoupling)

namespace FreeBoundary

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Monotonicity in the data -/

section MonotoneData

private lemma md_lin {b s0 hu s0' hu' : ℝ} (hb : 0 ≤ b) (e0 : s0 ≤ s0') (e1 : hu ≤ hu') :
    2 * hu + 2 * b * s0 ≤ 2 * hu' + 2 * b * s0' := by
  have := mul_le_mul_of_nonneg_left e0 hb
  linarith

private lemma md_M0 {mm b s0 hu s0' hu' : ℝ} (hm : 0 ≤ mm) (hb : 0 ≤ b) (e0 : s0 ≤ s0')
    (e1 : hu ≤ hu') :
    mm * (s0 + 2 * (2 * hu + 2 * b * s0)) ≤ mm * (s0' + 2 * (2 * hu' + 2 * b * s0')) := by
  have := md_lin hb e0 e1
  exact mul_le_mul_of_nonneg_left (by linarith) hm

private lemma md_xi {e mm b s0 hu hs hv s0' hu' hs' hv' C C' : ℝ} (he : 0 ≤ e) (hb : 0 ≤ b)
    (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) (hC0 : 0 ≤ C)
    (e0 : s0 ≤ s0') (e1 : hu ≤ hu') (e2 : hs ≤ hs') (e3 : hv ≤ hv') (eC : C ≤ C') :
    s0 + 4 * (2 * hu + 2 * b * s0) + 2 * (e * Real.sqrt (16 * (2 * hu + 2 * b * s0) ^ 2 +
      120 * mm ^ 2 * (2 * hv + 2 * b * hs) ^ 2 + 30 * C ^ 2)) ≤
    s0' + 4 * (2 * hu' + 2 * b * s0') + 2 * (e * Real.sqrt (16 * (2 * hu' + 2 * b * s0') ^ 2 +
      120 * mm ^ 2 * (2 * hv' + 2 * b * hs') ^ 2 + 30 * C' ^ 2)) := by
  have hΞ₀ := md_lin hb e0 e1
  have hΞ₁ := md_lin hb e2 e3
  have q1 := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * hu + 2 * b * s0) hΞ₀ 2
  have q2 := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * hv + 2 * b * hs) hΞ₁ 2
  have q3 := pow_le_pow_left₀ hC0 eC 2
  have q4 := mul_le_mul_of_nonneg_left q2 (by positivity : (0 : ℝ) ≤ 120 * mm ^ 2)
  have hQ : 16 * (2 * hu + 2 * b * s0) ^ 2 + 120 * mm ^ 2 * (2 * hv + 2 * b * hs) ^ 2 +
      30 * C ^ 2 ≤ 16 * (2 * hu' + 2 * b * s0') ^ 2 + 120 * mm ^ 2 * (2 * hv' + 2 * b * hs') ^ 2 +
      30 * C' ^ 2 := by linarith
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQ) he
  linarith

private lemma md_o {Cχ D4 F F' s0 s0' : ℝ} (hC : 0 ≤ Cχ) (hD : 0 ≤ D4) (eF : F ≤ F')
    (e0 : s0 ≤ s0') : 8 * Cχ * F + 8 * D4 * s0 ≤ 8 * Cχ * F' + 8 * D4 * s0' := by
  have h1 := mul_le_mul_of_nonneg_left eF hC
  have h2 := mul_le_mul_of_nonneg_left e0 hD
  linarith

private lemma md_Wo {mm Cχ D2 cJ M M' s0 s0' : ℝ} (hm : 0 ≤ mm) (hC : 0 ≤ Cχ) (hD : 0 ≤ D2)
    (hcJ : 0 ≤ cJ) (eM : M ≤ M') (e0 : s0 ≤ s0') :
    (2 + 12 * mm) * Cχ * (5 / 3 * M + cJ * s0) + ((3 + 12 * mm) * Cχ + 14 * D2) * s0 ≤
      (2 + 12 * mm) * Cχ * (5 / 3 * M' + cJ * s0') + ((3 + 12 * mm) * Cχ + 14 * D2) * s0' := by
  have h0 := mul_le_mul_of_nonneg_left e0 hcJ
  have h1 : 5 / 3 * M + cJ * s0 ≤ 5 / 3 * M' + cJ * s0' := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (2 + 12 * mm) * Cχ)
  have h3 := mul_le_mul_of_nonneg_left e0 (by positivity : (0 : ℝ) ≤ (3 + 12 * mm) * Cχ + 14 * D2)
  linarith

/-- `Φ_U` is monotone in the data `(s0, hu, hs, hv)`. -/
lemma gridPhiU_mono_data (sys : CoulombSystem eta ν)
    {V Hunit Cχ D2 D4 s0 hu hs hv s0' hu' hs' hv' : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ Hunit)
    (hCχ : 0 ≤ Cχ) (hD2 : 0 ≤ D2) (hD4 : 0 ≤ D4) (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) (h2 : 0 ≤ hs)
    (h3 : 0 ≤ hv) (e0 : s0 ≤ s0') (e1 : hu ≤ hu') (e2 : hs ≤ hs') (e3 : hv ≤ hv') :
    gridPhiU sys V Hunit Cχ D2 D4 s0 hu hs hv ≤ gridPhiU sys V Hunit Cχ D2 D4 s0' hu' hs' hv' := by
  have hb := relBU_nonneg sys hV hH
  have hM := sys.one_le_maxMass
  have hm0 : 0 ≤ sys.maxMass := by linarith
  have hcJ := gridFlowConstU_nonneg sys hV
  have hA : 0 ≤ gLAU sys V := by
    unfold gLAU
    have := gLzU_nonneg sys hV
    positivity
  have hσ := sigmaU_nonneg sys hV
  have hM₀ := md_M0 (b := relBU sys V Hunit) hm0 hb e0 e1
  have hM₀n : 0 ≤ sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0)) := by
    positivity
  have hC₀ := gLtailMU_mono sys hV hH hM₀
  have hC₀n := gLtailMU_nonneg sys hV hH hM₀n
  have hξ := md_xi (e := (eta : ℝ)) (mm := sys.maxMass) (Nat.cast_nonneg _) hb h0 h1 h2 h3 hC₀n
    e0 e1 e2 e3 hC₀
  have hF := flow2_mono (g := 1) hcJ hA hσ hξ hM₀ e0
  show flow2 _ _ _ _ _ _ _ ≤ flow2 _ _ _ _ _ _ _
  exact flow2_mono hcJ hA hσ (md_o hCχ hD4 hF e0) (md_Wo hm0 hCχ hD2 hcJ hM₀ e0)
    (mul_le_mul_of_nonneg_left e0 hCχ)

private lemma md_tau {mm X X' C C' : ℝ} (hm : 0 ≤ mm) (eX : X ≤ X') (eC : C ≤ C') :
    2 * mm * (2 * mm * X + C) ≤ 2 * mm * (2 * mm * X' + C') := by
  have := mul_le_mul_of_nonneg_left eX (by positivity : (0 : ℝ) ≤ 2 * mm)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private lemma md_beta {mm X X' C C' : ℝ} (hm : 0 ≤ mm) (eX : X ≤ X') (eC : C ≤ C') :
    128 * mm * (128 * mm * X + 8 * C) ≤ 128 * mm * (128 * mm * X' + 8 * C') := by
  have := mul_le_mul_of_nonneg_left eX (by positivity : (0 : ℝ) ≤ 128 * mm)
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private lemma md_A1 {δ τ δ' τ' Cχ CO : ℝ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hC : 0 ≤ Cχ) (hO : 0 ≤ CO)
    (eδ : δ ≤ δ') (eτ : τ ≤ τ') :
    2 * δ * (Cχ * τ + CO * δ) + CO * δ ^ 2 + Cχ * τ ^ 2 ≤
      2 * δ' * (Cχ * τ' + CO * δ') + CO * δ' ^ 2 + Cχ * τ' ^ 2 := by
  have : 0 ≤ δ' := hδ.trans eδ
  have : 0 ≤ τ' := hτ.trans eτ
  gcongr

private lemma md_A2 {e δ δ' G G' f β β' mW mW' T T' M M' : ℝ} (he : 0 ≤ e) (hδ : 0 ≤ δ)
    (hG : 0 ≤ G) (hf : 0 ≤ f) (hβ : 0 ≤ β) (hmW : 0 ≤ mW) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (eδ : δ ≤ δ') (eG : G ≤ G') (eβ : β ≤ β') (emW : mW ≤ mW') (eT : T ≤ T') (eM : M ≤ M') :
    2 * (e * δ * G + (f * β * mW + f * T * M + 52 * T * β)) ≤
      2 * (e * δ' * G' + (f * β' * mW' + f * T' * M' + 52 * T' * β')) := by
  have : 0 ≤ δ' := hδ.trans eδ
  have : 0 ≤ G' := hG.trans eG
  have : 0 ≤ β' := hβ.trans eβ
  have : 0 ≤ mW' := hmW.trans emW
  have : 0 ≤ T' := hT.trans eT
  have : 0 ≤ M' := hM.trans eM
  gcongr

/-- **The constants are monotone in the data** `(s0, hu, hs, hv)`. -/
lemma gridConstsSharp_gLU_mono_data (sys : CoulombSystem eta ν)
    {V Hunit Cχ CO D2 D4 s0 hu hs hv s0' hu' hs' hv' : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ Hunit)
    (hCχ : 0 ≤ Cχ) (hCO : 0 ≤ CO) (hD2 : 0 ≤ D2) (hD4 : 0 ≤ D4) (h0 : 0 ≤ s0) (h1 : 0 ≤ hu)
    (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) (e0 : s0 ≤ s0') (e1 : hu ≤ hu') (e2 : hs ≤ hs')
    (e3 : hv ≤ hv') :
    (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).1 ≤
        (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0' hu' hs' hv').1 ∧
      (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).2.1 ≤
        (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0' hu' hs' hv').2.1 ∧
      (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).2.2 ≤
        (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0' hu' hs' hv').2.2 := by
  have hb := relBU_nonneg sys hV hH
  have hM := sys.one_le_maxMass
  have hm0 : 0 ≤ sys.maxMass := by linarith
  have hcJ := gridFlowConstU_nonneg sys hV
  have hz := gLzU_nonneg sys hV
  have hM₀ := md_M0 (b := relBU sys V Hunit) hm0 hb e0 e1
  have hM₀n : 0 ≤ sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0)) := by
    positivity
  have hC₀ := gLtailMU_mono sys hV hH hM₀
  have hC₀n := gLtailMU_nonneg sys hV hH hM₀n
  have hΞ₁ := md_lin (b := relBU sys V Hunit) hb e2 e3
  have hΞ₁n : 0 ≤ 2 * hv + 2 * relBU sys V Hunit * hs := by positivity
  have hτ := md_tau hm0 hΞ₁ hC₀
  have hτn : 0 ≤ 2 * sys.maxMass * (2 * sys.maxMass * (2 * hv + 2 * relBU sys V Hunit * hs) +
      gLtailMU sys V Hunit (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0)))) := by
    positivity
  have hβ := md_beta hm0 hΞ₁ hC₀
  have hβn : 0 ≤ 128 * sys.maxMass * (128 * sys.maxMass * (2 * hv + 2 * relBU sys V Hunit * hs) +
      8 * gLtailMU sys V Hunit (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0)))) :=
    by positivity
  have he : (0 : ℝ) ≤ eta := Nat.cast_nonneg _
  have hδ := mul_le_mul_of_nonneg_left hτ he
  have hδn := mul_nonneg he hτn
  have hWo := md_Wo hm0 hCχ hD2 hcJ hM₀ e0
  have hXbn : 0 ≤ 5 / 3 * (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0))) +
      gridFlowConstU sys V * s0 := by positivity
  have hWon : 0 ≤ (2 + 12 * sys.maxMass) * Cχ *
      (5 / 3 * (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0))) +
        gridFlowConstU sys V * s0) + ((3 + 12 * sys.maxMass) * Cχ + 14 * D2) * s0 := by positivity
  have hCs := mul_le_mul_of_nonneg_left e0 hCχ
  have hW : 5 / 3 * ((2 + 12 * sys.maxMass) * Cχ *
      (5 / 3 * (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0))) +
        gridFlowConstU sys V * s0) + ((3 + 12 * sys.maxMass) * Cχ + 14 * D2) * s0) +
        gridFlowConstU sys V * (Cχ * s0) ≤
      5 / 3 * ((2 + 12 * sys.maxMass) * Cχ *
      (5 / 3 * (sys.maxMass * (s0' + 2 * (2 * hu' + 2 * relBU sys V Hunit * s0'))) +
        gridFlowConstU sys V * s0') + ((3 + 12 * sys.maxMass) * Cχ + 14 * D2) * s0') +
        gridFlowConstU sys V * (Cχ * s0') := by
    have := mul_le_mul_of_nonneg_left hCs hcJ
    linarith
  have hWn : 0 ≤ 5 / 3 * ((2 + 12 * sys.maxMass) * Cχ *
      (5 / 3 * (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0))) +
        gridFlowConstU sys V * s0) + ((3 + 12 * sys.maxMass) * Cχ + 14 * D2) * s0) +
        gridFlowConstU sys V * (Cχ * s0) := by positivity
  have hmW := mul_le_mul_of_nonneg_left hW hm0
  have hG := gLtailMU_mono sys hV hH hmW
  have hGn := gLtailMU_nonneg sys hV hH (mul_nonneg hm0 hWn)
  have hΦ := gridPhiU_mono_data sys hV hH hCχ hD2 hD4 h0 h1 h2 h3 e0 e1 e2 e3
  have hΦn := gridPhiU_nonneg sys (hs := hs) (hv := hv) hV hH hCχ hD2 hD4 h0 h1
  have h1z : 0 ≤ 1 + gLzU sys V := by linarith
  have hT : 3072 * sys.maxMass ^ 2 * gridPhiU sys V Hunit Cχ D2 D4 s0 hu hs hv * (1 + gLzU sys V) ≤
      3072 * sys.maxMass ^ 2 * gridPhiU sys V Hunit Cχ D2 D4 s0' hu' hs' hv' *
        (1 + gLzU sys V) := by gcongr
  have hTn : 0 ≤ 3072 * sys.maxMass ^ 2 * gridPhiU sys V Hunit Cχ D2 D4 s0 hu hs hv *
      (1 + gLzU sys V) := by positivity
  have hcF : 0 ≤ 18 * Real.sqrt 8 * Real.sqrt 79 * gLzU sys V := by positivity
  refine ⟨?_, ?_, ?_⟩
  · simp only [gridConstsSharp_gLU]
    exact md_A1 hδn hτn hCχ hCO hδ hτ
  · simp only [gridConstsSharp_gLU]
    exact md_A2 he hδn hGn hcF hβn (mul_nonneg hm0 hWn) hTn hM₀n hδ hG hβ hmW hT hM₀
  · simp only [gridConstsSharp_gLU]
    have : 0 ≤ (eta : ℝ) * (2 * sys.maxMass * (2 * sys.maxMass *
        (2 * hv' + 2 * relBU sys V Hunit * hs') + gLtailMU sys V Hunit
          (sys.maxMass * (s0' + 2 * (2 * hu' + 2 * relBU sys V Hunit * s0'))))) := hδn.trans hδ
    exact mul_le_mul (mul_le_mul_of_nonneg_left hδ (by norm_num)) e0 h0 (by positivity)

end MonotoneData

/-! ## The zero-mode shift -/

lemma norm_zeroModeShift_le (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) :
    ‖zeroModeShift sys L θ‖ ≤ zeroWeight sys / 4 := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have h1 := abs_zeroModeShift_re_le sys hL hθ hR
  have h2 := zeroModeShift_re_eq sys hθ L
  rw [← h2, Complex.norm_real, Real.norm_eq_abs]
  refine h1.trans ?_
  have hQ := zeroWeight_nonneg sys
  have hpi : Real.pi / (2 * L) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc zeroWeight sys * (Real.pi / (2 * L)) ≤ zeroWeight sys * (1 / 4) :=
        mul_le_mul_of_nonneg_left hpi hQ
    _ = zeroWeight sys / 4 := by ring

/-! ## The domain constant -/

lemma domConst_mono (q : Fin eta → ℝ) {c₀ D C D' C' : ℝ} (hD : D ≤ D') (hC : C ≤ C') :
    domConst q c₀ D C ≤ domConst q c₀ D' C' := by
  unfold domConst
  have h1 : (0 : ℝ) ≤ 6 * (1 + (Fintype.card (Fin eta × Fin 3) : ℝ)) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hD h1
  have := mul_le_mul_of_nonneg_left hC (pairWeight_nonneg q)
  linarith

lemma one_le_domConst (q : Fin eta → ℝ) {c₀ D C : ℝ} (hc₀ : 0 ≤ c₀) (hD : 0 ≤ D) (hC : 0 ≤ C) :
    1 ≤ domConst q c₀ D C := by
  unfold domConst
  have := mul_nonneg (pairWeight_nonneg q) hC
  have : (0 : ℝ) ≤ 6 * (1 + (Fintype.card (Fin eta × Fin 3) : ℝ)) ^ 2 * D := by positivity
  linarith

/-! ## `prop:free-dyn`, non-Born–Oppenheimer -/

section FreeDynNBO

/-- **`prop:free-dyn` for a fixed Schwartz observable, without the domain hypotheses**
(non-Born–Oppenheimer: `ν` empty, all particles quantum with masses `m_i ≥ 1`). The statement of
`free_dyn_grid_gLU_schwartz` for a mass-weighted cutoff `χ` (`DomCutoff`, with bounds `D ≤ D̄`,
`C ≤ C̄`), where `hdom0`, `hdom1` are replaced by the free-space regularity of the initial state
`u = ψ_∞(0)`: `H_∞ h = k` for `h = H_∞ u`, weak gradients `∇h = g'`, `∂_a ∇u = g2 · a`, and
`u/|x_i - x_j|`, `∂_a u/|x_i - x_j|` in `L²`. The constants are `gridConstsSharp_gLU` at the data
`(N, Λ N, Λ N, Λ² N)`, `N = dataNorm` and `Λ = domConst` at `c₀ = Q/4`, `D̄`, `C̄`: functions
of the system, `V_θ`, `f`, the free-space data and `(D̄, C̄)` only. -/
theorem free_dyn_grid_nbo [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχf : ∀ x : MolecularPositionTorus eta,
      χ (molecularPositionParticle a x) = (f (particle (cellCoord L x) a) : ℂ))
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
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hc₀ := norm_zeroModeShift_le sys hL2 hθ hR
  obtain ⟨h₀, h₁, hdom0, hdom1, n0, n1, n2⟩ := cut_state_domain sys hL hR0 hρ hone P hP hpos X hret
    (hHam 0) hH1 (hgrad 0) hg' hg2 hY hZ hc₀
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_grid_gLU_schwartz sys hL2 hθ
    hR hR0 hρ hone P hP hpos X.toCutoff hret hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε
    hleak0 hleak1 hdom0 hdom1 a hf0 hf1 F hFf hfR hRL χ hχf m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro φ₀ N Λ A K ψg
  -- the constants at the actual data
  set A' := gridConstsSharp_gLU sys (tv R θ) molecularCanonicalUnitHardyConstant
    (obsMomC (ftDecay F)) (obsMomC (ftDecay F)) (obsMomD2 (ftDecay F)) (obsMomD4 (ftDecay F))
    ‖φ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖ with hA'
  have hb : ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
      ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.toCutoff.commConst * ε * t) +
        ((A'.1 + (A'.2.2 * Real.sqrt 3 ^ 5 + ‖φ₀‖ ^ 2) * obsTailC (ftDecay F) 5) * (1 / K) ^ 5 +
          A'.2.1 * t * (1 / K) ^ 3) := hbound
  refine hb.trans ?_
  -- monotonicity
  have hN : 0 ≤ N := dataNorm_nonneg _ _ _ _ _ _ _
  have hc0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have hΛ0 : domConst sys.charge (zeroWeight sys / 4) X.D X.C ≤ Λ :=
    domConst_mono sys.charge hDbar hCbar
  have hΛ1 : 1 ≤ domConst sys.charge (zeroWeight sys / 4) X.D X.C :=
    one_le_domConst sys.charge hc0 X.D_nonneg X.C_nonneg
  have e1 : ‖h₀‖ ≤ Λ * N := n1.trans (mul_le_mul_of_nonneg_right hΛ0 hN)
  have e2 : ‖h₁‖ ≤ Λ ^ 2 * N :=
    n2.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hΛ0 2) hN)
  have hV := hθ.tv_nonneg
  have hHu : 0 ≤ molecularCanonicalUnitHardyConstant := by
    unfold molecularCanonicalUnitHardyConstant
    positivity
  have hB : ∀ n, 0 ≤ ftDecay F n := ftDecay_nonneg F
  have hC6 : 0 ≤ obsMomC (ftDecay F) := by unfold obsMomC; have := hB 6; positivity
  have hD2 : 0 ≤ obsMomD2 (ftDecay F) := by unfold obsMomD2; have := hB 8; positivity
  have hD4 : 0 ≤ obsMomD4 (ftDecay F) := by unfold obsMomD4; have := hB 10; positivity
  obtain ⟨m1, m2, m3⟩ := gridConstsSharp_gLU_mono_data sys hV hHu hC6 hC6 hD2 hD4
    (norm_nonneg φ₀) (norm_nonneg h₀) (norm_nonneg h₀) (norm_nonneg h₁) n0 e1 e1 e2
  have hT : 0 ≤ obsTailC (ftDecay F) 5 := by unfold obsTailC; have := hB 11; positivity
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hcomm : X.toCutoff.commConst ≤ (Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2) := by
    unfold Cutoff.commConst
    have : X.toCutoff.D1 + X.toCutoff.D2 / 2 ≤ Dbar + Dbar / 2 := by
      change X.D + X.D / 2 ≤ Dbar + Dbar / 2
      linarith
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have hφN : ‖φ₀‖ ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ (norm_nonneg _) n0 2
  have hA3 : 0 ≤ A'.2.2 := gridConstsSharp_gLU_nonneg_three sys hV hHu _ _ _ _ (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have ht' : 0 ≤ ‖ψ t‖ + ‖ψ 0‖ := by positivity
  gcongr

end FreeDynNBO

end FreeBoundary
