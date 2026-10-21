import PlaneWave.FreeBoundary.UpperComposite
import PlaneWave.FreeBoundary.IMS
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# `app:free`, part 13: the explicit localisation pair and the upper bound

The localisation pair of the IMS argument, built from Mathlib's smooth transition function
`T = Real.smoothTransition` and the squared configuration radius `|r|² = Σ_a r_a²` (`cfgSq`):
`χ = cos(π/2 · T((|r|² - R₁²)/(R_L² - R₁²)))`, `η = sin(…)`. Then `χ² + η² = 1`, `χ = 1` for
`|r| < R₁`, `χ = 0` unless every particle lies in `B_{R_L}(0)`, both are exchange-invariant, and
`Σ_a ((∂_aχ)² + (∂_aη)²) ≤ π² B² R_L²/(R_L² - R₁²)² ≤ π² B²/w²` (`w = R_L - R₁ ≤ R_L`,
`B = sup |T'|`, `smoothSlope`).

* `stdLocPair`;
* **`free_upper_agmon`**: if `E_∞` bounds the free-space form below on the `C²` sector states of
  compact support and the infimum is approached by normalised such states with mass `≤ τ < 1`
  outside the ball `|r| < R_L - w` (Agmon decay: `τ = C e^{-2α(R_L - w)}`), then
  `E_L + C₀ ≤ E_∞ + π² B² τ/(2w²(1 - τ))`;
* **`free_grid_upper_agmon`**: with the grid theorem,
  `E_{N,L} + C₀ ≤ E_∞ + π² B² τ/(2w²(1 - τ)) + C K^{-3}`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

variable {eta : ℕ}

/-! ## The smooth transition -/

lemma deriv_smoothTransition_eq_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds hx) fun y hy =>
        Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [h.deriv_eq, deriv_const]
  · have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy =>
        Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [h.deriv_eq, deriv_const]

lemma exists_smoothSlope : ∃ B : ℝ, ∀ x, |deriv Real.smoothTransition x| ≤ B := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact hC x hx
  · have hx' : x < 0 ∨ 1 < x := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      exact hx
    rw [deriv_smoothTransition_eq_zero hx', abs_zero]
    exact le_trans (norm_nonneg _) (hC 0 ⟨le_rfl, zero_le_one⟩)

/-- A bound `B` for `|T'|`, `T = Real.smoothTransition`. -/
def smoothSlope : ℝ := Classical.choose exists_smoothSlope

lemma abs_deriv_le_smoothSlope (x : ℝ) : |deriv Real.smoothTransition x| ≤ smoothSlope :=
  Classical.choose_spec exists_smoothSlope x

lemma smoothSlope_nonneg : 0 ≤ smoothSlope := le_trans (abs_nonneg _) (abs_deriv_le_smoothSlope 0)

/-! ## The squared configuration radius -/

/-- The squared configuration radius `|r|² = Σ_a r_a²`. -/
def cfgSq (r : Rcfg eta) : ℝ := ∑ a, r a ^ 2

lemma contDiff_cfgSq : ContDiff ℝ 2 (cfgSq (eta := eta)) := by
  unfold cfgSq
  exact ContDiff.sum fun a _ => (contDiff_apply ℝ ℝ a).pow 2

lemma cfgSq_nonneg (r : Rcfg eta) : 0 ≤ cfgSq r := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma cfgSq_freeSwap (i j : Fin eta) (r : Rcfg eta) : cfgSq (freeSwap i j r) = cfgSq r := by
  unfold cfgSq freeSwap
  exact Equiv.sum_comp ((Equiv.swap i j).prodCongr (Equiv.refl (Fin 3)))
    (fun a => r a ^ 2)

lemma norm_particle_sq_le (r : Rcfg eta) (i : Fin eta) : ‖particle r i‖ ^ 2 ≤ cfgSq r := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold cfgSq particle
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun i' => ∑ c : Fin 3, r (i', c) ^ 2)
    (fun i' _ => Finset.sum_nonneg fun c _ => sq_nonneg _) (Finset.mem_univ i)

lemma hasDerivAt_cfgSq_line (r : Rcfg eta) (a : Fin eta × Fin 3) :
    HasDerivAt (fun s : ℝ => cfgSq (r + s • Pi.single a 1)) (2 * r a) 0 := by
  have hb : ∀ b : Fin eta × Fin 3, HasDerivAt
      (fun s : ℝ => (r b + s * (Pi.single a (1 : ℝ) : Rcfg eta) b) ^ 2)
      (2 * r b * (Pi.single a (1 : ℝ) : Rcfg eta) b) 0 := by
    intro b
    refine ((((hasDerivAt_id (0 : ℝ)).mul_const
      ((Pi.single a (1 : ℝ) : Rcfg eta) b)).const_add (r b)).pow 2).congr_deriv ?_
    simp
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun b _ => hb b
  have hfun : (fun s : ℝ => cfgSq (r + s • Pi.single a 1)) =
      fun s => ∑ b ∈ Finset.univ, (r b + s * (Pi.single a (1 : ℝ) : Rcfg eta) b) ^ 2 := by
    funext s
    unfold cfgSq
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  refine hs.congr_deriv ?_
  simp [Pi.single_apply]

/-- The coordinate derivative from the derivative along the coordinate line. -/
lemma dirD_eq_of_hasDerivAt {f : Rcfg eta → ℝ} {r : Rcfg eta} {a : Fin eta × Fin 3}
    (hf : DifferentiableAt ℝ f r) {d : ℝ}
    (h : HasDerivAt (fun s : ℝ => f (r + s • Pi.single a 1)) d 0) : dirD a f r = d := by
  have h2 : HasDerivAt (fun s : ℝ => f (r + s • Pi.single a 1))
      (fderiv ℝ f r (Pi.single a 1)) 0 :=
    hasDerivAt_line (by rw [zero_smul, add_zero]; exact hf.hasFDerivAt)
  exact h2.unique h

/-! ## The localisation pair -/

section Pair

variable (L R0 ρ R1 : ℝ)

/-- The phase `π/2 · T((|r|² - R₁²)/(R_L² - R₁²))`. -/
def locPhase (r : Rcfg eta) : ℝ :=
  Real.pi / 2 * Real.smoothTransition
    ((cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2))

/-- The gradient constant `π² B² R_L²/(R_L² - R₁²)²`. -/
def locConst : ℝ :=
  Real.pi ^ 2 * smoothSlope ^ 2 * retainedRadius L R0 ρ ^ 2 /
    (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) ^ 2

variable {L R0 ρ R1}

lemma contDiff_locPhase : ContDiff ℝ 2 (locPhase (eta := eta) L R0 ρ R1) := by
  unfold locPhase
  exact contDiff_const.mul ((Real.smoothTransition.contDiff (n := 2)).comp
    ((contDiff_cfgSq.sub contDiff_const).div_const _))

lemma hasDerivAt_locPhase_line (r : Rcfg eta) (a : Fin eta × Fin 3) :
    HasDerivAt (fun s : ℝ => locPhase L R0 ρ R1 (r + s • Pi.single a 1))
      (Real.pi / 2 * (deriv Real.smoothTransition
        ((cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) *
        (2 * r a / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)))) 0 := by
  have hT : DifferentiableAt ℝ Real.smoothTransition
      ((cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)) _
  have hin : HasDerivAt (fun s : ℝ => (cfgSq (r + s • Pi.single a 1) - R1 ^ 2) /
      (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) (2 * r a / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) 0 :=
    ((hasDerivAt_cfgSq_line r a).sub_const _).div_const _
  have h0 : (cfgSq (r + (0 : ℝ) • Pi.single a 1) - R1 ^ 2) /
      (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) =
      (cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) := by
    rw [zero_smul, add_zero]
  have hT' : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition
      ((cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)))
      ((cfgSq (r + (0 : ℝ) • Pi.single a 1) - R1 ^ 2) /
        (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) := by
    rw [h0]
    exact hT.hasDerivAt
  have hcomp := hT'.comp (0 : ℝ) hin
  exact hcomp.const_mul (Real.pi / 2)

lemma dirD_locPhase (r : Rcfg eta) (a : Fin eta × Fin 3) :
    dirD a (locPhase L R0 ρ R1) r = Real.pi / 2 * (deriv Real.smoothTransition
        ((cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) *
        (2 * r a / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2))) :=
  dirD_eq_of_hasDerivAt ((contDiff_locPhase.differentiable (by norm_num)) r)
    (hasDerivAt_locPhase_line r a)

lemma dirD_cos_locPhase (r : Rcfg eta) (a : Fin eta × Fin 3) :
    dirD a (fun x => Real.cos (locPhase L R0 ρ R1 x)) r =
      -Real.sin (locPhase L R0 ρ R1 r) * dirD a (locPhase L R0 ρ R1) r := by
  refine dirD_eq_of_hasDerivAt ?_ ?_
  · exact (Real.differentiable_cos _).comp r
      ((contDiff_locPhase.differentiable (by norm_num)) r)
  · have hl := hasDerivAt_locPhase_line (L := L) (R0 := R0) (ρ := ρ) (R1 := R1) r a
    have h0 : locPhase L R0 ρ R1 (r + (0 : ℝ) • Pi.single a 1) = locPhase L R0 ρ R1 r := by
      rw [zero_smul, add_zero]
    have h := (Real.hasDerivAt_cos (locPhase L R0 ρ R1 (r + (0 : ℝ) • Pi.single a 1))).comp
      (0 : ℝ) hl
    rw [h0] at h
    rw [dirD_locPhase]
    exact h

lemma dirD_sin_locPhase (r : Rcfg eta) (a : Fin eta × Fin 3) :
    dirD a (fun x => Real.sin (locPhase L R0 ρ R1 x)) r =
      Real.cos (locPhase L R0 ρ R1 r) * dirD a (locPhase L R0 ρ R1) r := by
  refine dirD_eq_of_hasDerivAt ?_ ?_
  · exact (Real.differentiable_sin _).comp r
      ((contDiff_locPhase.differentiable (by norm_num)) r)
  · have hl := hasDerivAt_locPhase_line (L := L) (R0 := R0) (ρ := ρ) (R1 := R1) r a
    have h0 : locPhase L R0 ρ R1 (r + (0 : ℝ) • Pi.single a 1) = locPhase L R0 ρ R1 r := by
      rw [zero_smul, add_zero]
    have h := (Real.hasDerivAt_sin (locPhase L R0 ρ R1 (r + (0 : ℝ) • Pi.single a 1))).comp
      (0 : ℝ) hl
    rw [h0] at h
    rw [dirD_locPhase]
    exact h

lemma grad_sum_identity (φ T' W : ℝ) (r : Rcfg eta) :
    ∑ a : Fin eta × Fin 3, ((-Real.sin φ * (Real.pi / 2 * (T' * (2 * r a / W)))) ^ 2 +
      (Real.cos φ * (Real.pi / 2 * (T' * (2 * r a / W)))) ^ 2) =
      Real.pi ^ 2 * T' ^ 2 * cfgSq r / W ^ 2 := by
  unfold cfgSq
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := Real.sin_sq_add_cos_sq φ
  linear_combination (Real.pi ^ 2 * T' ^ 2 * r a ^ 2 / W ^ 2) * h

/-- **The localisation pair** `χ = cos(locPhase)`, `η = sin(locPhase)`, for `0 < R₁ < R_L`. -/
def stdLocPair (hR1 : 0 < R1) (h12 : R1 < retainedRadius L R0 ρ) :
    LocPair eta L R0 ρ {r | cfgSq r < R1 ^ 2} (locConst L R0 ρ R1) where
  χ := fun r => Real.cos (locPhase L R0 ρ R1 r)
  η := fun r => Real.sin (locPhase L R0 ρ R1 r)
  χ_smooth := Real.contDiff_cos.comp contDiff_locPhase
  η_smooth := Real.contDiff_sin.comp contDiff_locPhase
  sq_add := fun r => Real.cos_sq_add_sin_sq _
  χ_swap := fun i j r => by
    unfold locPhase
    rw [cfgSq_freeSwap]
  η_swap := fun i j r => by
    unfold locPhase
    rw [cfgSq_freeSwap]
  χ_supp := fun r hr i => by
    have hW : 0 < retainedRadius L R0 ρ ^ 2 - R1 ^ 2 := by nlinarith
    have hlt : cfgSq r < retainedRadius L R0 ρ ^ 2 := by
      by_contra hge
      push Not at hge
      apply hr
      have h1 : 1 ≤ (cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) := by
        rw [le_div_iff₀ hW]
        linarith
      simp only [locPhase, Real.smoothTransition.one_of_one_le h1, mul_one]
      exact Real.cos_pi_div_two
    have h2 := norm_particle_sq_le r i
    have hRL : 0 < retainedRadius L R0 ρ := lt_trans hR1 h12
    nlinarith [norm_nonneg (particle r i)]
  χ_one := fun r hr => by
    have hW : 0 < retainedRadius L R0 ρ ^ 2 - R1 ^ 2 := by nlinarith
    have hneg : (cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by simp only [mem_setOf_eq] at hr; linarith) hW.le
    simp only [locPhase, Real.smoothTransition.zero_of_nonpos hneg, mul_zero, Real.cos_zero]
  grad_bound := fun r => by
    have hW : 0 < retainedRadius L R0 ρ ^ 2 - R1 ^ 2 := by nlinarith
    have hsum : ∑ a : Fin eta × Fin 3, (dirD a (fun x => Real.cos (locPhase L R0 ρ R1 x)) r ^ 2 +
        dirD a (fun x => Real.sin (locPhase L R0 ρ R1 x)) r ^ 2) =
        Real.pi ^ 2 * deriv Real.smoothTransition
          ((cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) ^ 2 * cfgSq r /
          (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) ^ 2 := by
      simp_rw [dirD_cos_locPhase, dirD_sin_locPhase, dirD_locPhase]
      exact grad_sum_identity _ _ _ r
    rw [hsum]
    unfold locConst
    obtain ⟨x, hx⟩ : ∃ x, x = (cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) :=
      ⟨_, rfl⟩
    rw [← hx]
    have h0 := cfgSq_nonneg r
    by_cases hd : deriv Real.smoothTransition x = 0
    · rw [hd]
      have : (0 : ℝ) ≤ Real.pi ^ 2 * smoothSlope ^ 2 * retainedRadius L R0 ρ ^ 2 /
          (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) ^ 2 := by positivity
      simpa using this
    · have hx01 : x ≤ 1 := by
        by_contra h
        push Not at h
        exact hd (deriv_smoothTransition_eq_zero (Or.inr h))
      have hQ : cfgSq r ≤ retainedRadius L R0 ρ ^ 2 := by
        rw [hx, div_le_one hW] at hx01
        linarith
      have hB := abs_deriv_le_smoothSlope x
      have hB2 : deriv Real.smoothTransition x ^ 2 ≤ smoothSlope ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hB 2
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc Real.pi ^ 2 * deriv Real.smoothTransition x ^ 2 * cfgSq r
          ≤ Real.pi ^ 2 * smoothSlope ^ 2 * cfgSq r := by gcongr
        _ ≤ Real.pi ^ 2 * smoothSlope ^ 2 * retainedRadius L R0 ρ ^ 2 := by gcongr
  grad_zero := fun r hr a => by
    have hW : 0 < retainedRadius L R0 ρ ^ 2 - R1 ^ 2 := by nlinarith
    have hneg : (cfgSq r - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) < 0 :=
      div_neg_of_neg_of_pos (by simp only [mem_setOf_eq] at hr; linarith) hW
    have hD : dirD a (locPhase L R0 ρ R1) r = 0 := by
      rw [dirD_locPhase, deriv_smoothTransition_eq_zero (Or.inl hneg)]
      ring
    constructor
    · show dirD a (fun x => Real.cos (locPhase L R0 ρ R1 x)) r = 0
      rw [dirD_cos_locPhase, hD, mul_zero]
    · show dirD a (fun x => Real.sin (locPhase L R0 ρ R1 x)) r = 0
      rw [dirD_sin_locPhase, hD, mul_zero]

/-- With the transition width `w = R_L - R₁ ≤ R_L`, the gradient constant is at most
`π² B²/w²`, uniformly in `L`. -/
lemma locConst_le {w : ℝ} (hw : 0 < w) (hR1 : R1 = retainedRadius L R0 ρ - w)
    (hwL : w ≤ retainedRadius L R0 ρ) :
    locConst L R0 ρ R1 ≤ Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 := by
  unfold locConst
  set RL := retainedRadius L R0 ρ
  have hRL : 0 < RL := lt_of_lt_of_le hw hwL
  have hW : RL ^ 2 - R1 ^ 2 = w * (2 * RL - w) := by rw [hR1]; ring
  have hW' : w * RL ≤ RL ^ 2 - R1 ^ 2 := by rw [hW]; nlinarith
  have hpos : 0 < w * RL := by positivity
  rw [div_le_div_iff₀ (pow_pos (lt_of_lt_of_le hpos hW') 2) (by positivity)]
  have hB : 0 ≤ Real.pi ^ 2 * smoothSlope ^ 2 := by positivity
  have hsq : (w * RL) ^ 2 ≤ (RL ^ 2 - R1 ^ 2) ^ 2 := pow_le_pow_left₀ hpos.le hW' 2
  nlinarith [mul_le_mul_of_nonneg_left hsq hB]

end Pair

section System

variable {ν : Type} [Fintype ν]

/-- **`prop:free`, upper bound.** Let `θ ≡ 1` on `[0, L/2 - ρ]`, the nuclei at `P_ℓ ∈ B_{R₀}(0)`
(on the torus at `-P_ℓ/L`), `E_L` the torus ground energy of the sector (zero mode removed),
`0 < w < R_L = L/4 - R₀ - ρ`. If `E_∞` bounds the free-space form below on the `C²` sector states
of compact support, and for every `ε > 0` a normalised such state has energy `≤ E_∞ + ε` and mass
`≤ τ < 1` outside the ball `|r| < R_L - w` (Agmon decay of the ground state:
`τ = C e^{-2α(R_L - w)}`), then `E_L + C₀ ≤ E_∞ + π² B² τ/(2 w² (1 - τ))`. -/
theorem free_upper_agmon (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} {L R R0 ρ w : ℝ}
    {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {E : ℝ} (hE : IsGLTorusGroundEnergy sys lab L θ E)
    (hw : 0 < w) (hwL : w < retainedRadius L R0 ρ)
    {Einf τ : ℝ} (hτ : τ < 1)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (happrox : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | cfgSq r < (retainedRadius L R0 ρ - w) ^ 2}ᶜ, ‖φ r‖ ^ 2 ≤ τ) :
    E + (zeroModeShift sys L θ).re ≤
      Einf + Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * τ / (2 * (1 - τ)) := by
  have hR1 : 0 < retainedRadius L R0 ρ - w := by linarith
  have h12 : retainedRadius L R0 ρ - w < retainedRadius L R0 ρ := by linarith
  have hSm : MeasurableSet {r : Rcfg eta | cfgSq r < (retainedRadius L R0 ρ - w) ^ 2} :=
    measurableSet_lt contDiff_cfgSq.continuous.measurable measurable_const
  have h := free_upper_ims sys hL hθ hR hR0 hρ hone P hP hpos hE hSm (stdLocPair hR1 h12) hτ
    hlow happrox
  have hτ0 : 0 ≤ τ := by
    obtain ⟨φ, -, -, -, -, -, -, ht⟩ := happrox 1 one_pos
    exact le_trans (setIntegral_nonneg_of_ae (ae_of_all _ fun r => by positivity)) ht
  have hM := locConst_le (L := L) (R0 := R0) (ρ := ρ) (R1 := retainedRadius L R0 ρ - w) hw rfl
    hwL.le
  have hd : 0 < 2 * (1 - τ) := by linarith
  have h2 : locConst L R0 ρ (retainedRadius L R0 ρ - w) * τ / (2 * (1 - τ)) ≤
      Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * τ / (2 * (1 - τ)) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hM hτ0) hd.le
  linarith

/-- **`prop:free`, the upper bound for the grid energy**: with the grid theorem (`PlaneWave.FreeBoundary.GridEnergy`),
`E_{N,L} + C₀ ≤ E_∞ + π² B² τ/(2 w² (1 - τ)) + C K^{-3}`, `K = 2πm/L`. -/
theorem free_grid_upper_agmon (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (hw : 0 < w) (hwL : w < retainedRadius L R0 ρ)
    {Einf τ : ℝ} (hτ : τ < 1)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (happrox : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | cfgSq r < (retainedRadius L R0 ρ - w) ^ 2}ᶜ, ‖φ r‖ ^ 2 ≤ τ) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E ∧
      E + (zeroModeShift sys L θ).re ≤
        Einf + Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * τ / (2 * (1 - τ)) ∧
      ∀ m : ℕ, PlaneWaveGridG.gLGridThreshold sys L (tv R θ) E ≤ m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          Eg + (zeroModeShift sys L θ).re ≤
            Einf + Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * τ / (2 * (1 - τ)) +
              PlaneWaveGridG.gLGridErrorConstant sys L (tv R θ) E /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  obtain ⟨E, hE, hgrid⟩ := PlaneWaveGridG.gLSectorGridError sys lab hlab hL hθ
  have hup := free_upper_agmon sys hL hθ hR hR0 hρ hone P hP hpos hE hw hwL hτ hlow happrox
  refine ⟨E, hE, hup, fun m hm => ?_⟩
  obtain ⟨Eg, hEg, herr⟩ := hgrid m hm
  refine ⟨Eg, hEg, ?_⟩
  have h := (abs_le.mp herr).2
  linarith

end System

end

end FreeBoundary
