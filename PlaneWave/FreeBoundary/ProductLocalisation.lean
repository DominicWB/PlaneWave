import PlaneWave.FreeBoundary.UniformFreeEnergy

/-!
# `app:free`: the product localisation pair and `prop:free` in the product geometry

The manuscript's retained region is a product of one-particle balls,
`𝓑_L = {every electron in B_{R_L}(c₀)}`, and assumption (A) is stated with the distance to a
product region. `PlaneWave.FreeBoundary.LocalisationPair` and `PlaneWave.FreeBoundary.LowerBound`
localise with the configuration-space ball `Σ_i |r_i|² < R₁²` (`stdLocPair`), a different region:
a configuration can have every particle in `B_{R₁}(0)` and lie outside that ball. This file builds
the localisation pair of the product geometry and restates `prop:free` and eq:free-energy with it.

* `prodPhase`: `π/2 · (1 - ∏_i (1 - T((|r_i|² - R₁²)/(R_L² - R₁²))))`; `χ = cos(prodPhase)`,
  `η = sin(prodPhase)`; `χ = 1` when every particle lies in `B_{R₁}(0)`, `χ = 0` as soon as one
  particle leaves `B_{R_L}(0)`, and
  `Σ_a ((∂_aχ)² + (∂_aη)²) ≤ η π² B² R_L²/(R_L² - R₁²)² ≤ η π² B²/w²` (`η` particles,
  `B = sup |T'|`, `w = R_L - R₁`);
* `prodLocPair`, `prodTorusLocPair`: the pair in free space and on the torus (cell coordinates);
* `free_upper_agmon_prod`, `free_grid_upper_agmon_prod`, `free_grid_two_sided_prod`,
  `free_grid_exponential_prod`, and with the `L`-uniform grid constant
  `free_grid_two_sidedU_prod`, **`free_grid_exponentialU_prod`**: `prop:free` and eq:free-energy
  with the mass hypotheses (Agmon decay of the free ground state, and (A)) on the complement of the
  product region `{every particle in B_{R_L - w}(0)}`, and the gradient constant `η π² B²/w²`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15
  molecularTorusFiniteMeasureFB15

variable {eta : ℕ}

/-! ## One-particle radii -/

/-- The squared radius `|r_i|²` of particle `i`. -/
def pSq (r : Rcfg eta) (i : Fin eta) : ℝ := ∑ c : Fin 3, r (i, c) ^ 2

lemma pSq_eq_norm_sq (r : Rcfg eta) (i : Fin eta) : pSq r i = ‖particle r i‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma pSq_nonneg (r : Rcfg eta) (i : Fin eta) : 0 ≤ pSq r i :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma contDiff_pSq (i : Fin eta) : ContDiff ℝ 2 (fun r : Rcfg eta => pSq r i) := by
  unfold pSq
  exact ContDiff.sum fun c _ => (contDiff_apply ℝ ℝ (i, c)).pow 2

lemma sq_le_pSq (r : Rcfg eta) (a : Fin eta × Fin 3) : r a ^ 2 ≤ pSq r a.1 := by
  unfold pSq
  exact Finset.single_le_sum (f := fun c => r (a.1, c) ^ 2) (fun c _ => sq_nonneg _)
    (Finset.mem_univ a.2)

lemma pSq_freeSwap (i j k : Fin eta) (r : Rcfg eta) :
    pSq (freeSwap i j r) k = pSq r (Equiv.swap i j k) := rfl

lemma norm_particle_eq_sqrt (r : Rcfg eta) (i : Fin eta) :
    ‖particle r i‖ = Real.sqrt (pSq r i) := by
  rw [pSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

lemma continuous_norm_particle (i : Fin eta) : Continuous fun r : Rcfg eta => ‖particle r i‖ := by
  have h : (fun r : Rcfg eta => ‖particle r i‖) = fun r => Real.sqrt (pSq r i) :=
    funext fun r => norm_particle_eq_sqrt r i
  rw [h]
  exact (contDiff_pSq i).continuous.sqrt

lemma pSq_lt_of_norm_lt {r : Rcfg eta} {i : Fin eta} {R1 : ℝ} (h : ‖particle r i‖ < R1) :
    pSq r i < R1 ^ 2 := by
  rw [pSq_eq_norm_sq]
  have := norm_nonneg (particle r i)
  nlinarith

lemma norm_lt_of_pSq_lt {r : Rcfg eta} {i : Fin eta} {R1 : ℝ} (hR1 : 0 ≤ R1)
    (h : pSq r i < R1 ^ 2) : ‖particle r i‖ < R1 := by
  rw [pSq_eq_norm_sq] at h
  exact (abs_lt_of_sq_lt_sq' h hR1).2

lemma hasDerivAt_pSq_line (r : Rcfg eta) (a : Fin eta × Fin 3) (i : Fin eta) :
    HasDerivAt (fun s : ℝ => pSq (r + s • Pi.single a 1) i)
      (if a.1 = i then 2 * r a else 0) 0 := by
  have hb : ∀ c : Fin 3, HasDerivAt
      (fun s : ℝ => (r (i, c) + s * (Pi.single a (1 : ℝ) : Rcfg eta) (i, c)) ^ 2)
      (2 * r (i, c) * (Pi.single a (1 : ℝ) : Rcfg eta) (i, c)) 0 := by
    intro c
    refine ((((hasDerivAt_id (0 : ℝ)).mul_const
      ((Pi.single a (1 : ℝ) : Rcfg eta) (i, c))).const_add (r (i, c))).pow 2).congr_deriv ?_
    simp
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun c _ => hb c
  have hfun : (fun s : ℝ => pSq (r + s • Pi.single a 1) i) =
      fun s => ∑ c ∈ Finset.univ, (r (i, c) + s * (Pi.single a (1 : ℝ) : Rcfg eta) (i, c)) ^ 2 := by
    funext s
    unfold pSq
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  refine hs.congr_deriv ?_
  obtain ⟨i0, c0⟩ := a
  by_cases h : i0 = i
  · subst h
    simp [Pi.single_apply]
  · have h' : ∀ c : Fin 3, ((i, c) : Fin eta × Fin 3) ≠ (i0, c0) := fun c hc =>
      h (congrArg Prod.fst hc).symm
    simp [h', h]

/-! ## The product localisation pair -/

section Pair

variable (L R0 ρ R1 : ℝ)

/-- The one-particle transition `T((|r_i|² - R₁²)/(R_L² - R₁²))`. -/
def oneT (r : Rcfg eta) (i : Fin eta) : ℝ :=
  Real.smoothTransition ((pSq r i - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2))

/-- The product phase `π/2 · (1 - ∏_i (1 - T_i))`. -/
def prodPhase (r : Rcfg eta) : ℝ := Real.pi / 2 * (1 - ∏ i, (1 - oneT L R0 ρ R1 r i))

/-- The coordinate derivative of the product phase,
`∂_a prodPhase = π/2 · ∏_{j ≠ i} (1 - T_j) · T'(x_i) · 2 r_a/(R_L² - R₁²)`, `a = (i, c)`. -/
def prodPhaseD (r : Rcfg eta) (a : Fin eta × Fin 3) : ℝ :=
  Real.pi / 2 * ((∏ j ∈ Finset.univ.erase a.1, (1 - oneT L R0 ρ R1 r j)) *
    (deriv Real.smoothTransition
        ((pSq r a.1 - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) *
      (2 * r a / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2))))

variable {L R0 ρ R1}

lemma oneT_nonneg (r : Rcfg eta) (i : Fin eta) : 0 ≤ oneT L R0 ρ R1 r i :=
  Real.smoothTransition.nonneg _

lemma oneT_le_one (r : Rcfg eta) (i : Fin eta) : oneT L R0 ρ R1 r i ≤ 1 :=
  Real.smoothTransition.le_one _

lemma contDiff_oneT (i : Fin eta) : ContDiff ℝ 2 (fun r : Rcfg eta => oneT L R0 ρ R1 r i) := by
  unfold oneT
  exact (Real.smoothTransition.contDiff (n := 2)).comp
    (((contDiff_pSq i).sub contDiff_const).div_const _)

lemma contDiff_prodPhase : ContDiff ℝ 2 (prodPhase (eta := eta) L R0 ρ R1) := by
  unfold prodPhase
  exact contDiff_const.mul (contDiff_const.sub
    (contDiff_prod fun i _ => contDiff_const.sub (contDiff_oneT i)))

lemma prodPhase_freeSwap (i j : Fin eta) (r : Rcfg eta) :
    prodPhase L R0 ρ R1 (freeSwap i j r) = prodPhase L R0 ρ R1 r := by
  have h : ∏ k, (1 - oneT L R0 ρ R1 (freeSwap i j r) k) = ∏ k, (1 - oneT L R0 ρ R1 r k) :=
    Equiv.prod_comp (Equiv.swap i j) (fun k => 1 - oneT L R0 ρ R1 r k)
  unfold prodPhase
  rw [h]

lemma hasDerivAt_oneT_line (r : Rcfg eta) (a : Fin eta × Fin 3) (i : Fin eta) :
    HasDerivAt (fun s : ℝ => oneT L R0 ρ R1 (r + s • Pi.single a 1) i)
      (deriv Real.smoothTransition ((pSq r i - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) *
        ((if a.1 = i then 2 * r a else 0) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2))) 0 := by
  have hT : DifferentiableAt ℝ Real.smoothTransition
      ((pSq r i - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)) _
  have hin : HasDerivAt (fun s : ℝ => (pSq (r + s • Pi.single a 1) i - R1 ^ 2) /
      (retainedRadius L R0 ρ ^ 2 - R1 ^ 2))
      ((if a.1 = i then 2 * r a else 0) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) 0 :=
    ((hasDerivAt_pSq_line r a i).sub_const _).div_const _
  have h0 : (pSq (r + (0 : ℝ) • Pi.single a 1) i - R1 ^ 2) /
      (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) =
      (pSq r i - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) := by
    rw [zero_smul, add_zero]
  have hT' : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition
      ((pSq r i - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)))
      ((pSq (r + (0 : ℝ) • Pi.single a 1) i - R1 ^ 2) /
        (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) := by
    rw [h0]
    exact hT.hasDerivAt
  exact hT'.comp (0 : ℝ) hin

lemma hasDerivAt_prodPhase_line (r : Rcfg eta) (a : Fin eta × Fin 3) :
    HasDerivAt (fun s : ℝ => prodPhase L R0 ρ R1 (r + s • Pi.single a 1))
      (prodPhaseD L R0 ρ R1 r a) 0 := by
  classical
  set W := retainedRadius L R0 ρ ^ 2 - R1 ^ 2 with hW
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin eta)), HasDerivAt
      (fun s : ℝ => 1 - oneT L R0 ρ R1 (r + s • Pi.single a 1) i)
      (-(deriv Real.smoothTransition ((pSq r i - R1 ^ 2) / W) *
        ((if a.1 = i then 2 * r a else 0) / W))) 0 :=
    fun i _ => (hasDerivAt_oneT_line r a i).const_sub 1
  have hP := HasDerivAt.fun_finsetProd hf
  simp only [zero_smul, add_zero] at hP
  have hsum : ∑ i ∈ Finset.univ, (∏ j ∈ Finset.univ.erase i, (1 - oneT L R0 ρ R1 r j)) •
      (-(deriv Real.smoothTransition ((pSq r i - R1 ^ 2) / W) *
        ((if a.1 = i then 2 * r a else 0) / W))) =
      -((∏ j ∈ Finset.univ.erase a.1, (1 - oneT L R0 ρ R1 r j)) *
        (deriv Real.smoothTransition ((pSq r a.1 - R1 ^ 2) / W) * (2 * r a / W))) := by
    rw [Finset.sum_eq_single a.1]
    · simp [smul_eq_mul]
    · intro i _ hi
      simp [Ne.symm hi]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hsum] at hP
  have h2 : HasDerivAt (fun s : ℝ => prodPhase L R0 ρ R1 (r + s • Pi.single a 1))
      (Real.pi / 2 * -(-((∏ j ∈ Finset.univ.erase a.1, (1 - oneT L R0 ρ R1 r j)) *
        (deriv Real.smoothTransition ((pSq r a.1 - R1 ^ 2) / W) * (2 * r a / W))))) 0 :=
    (hP.const_sub 1).const_mul (Real.pi / 2)
  refine h2.congr_deriv ?_
  unfold prodPhaseD
  ring

lemma dirD_prodPhase (r : Rcfg eta) (a : Fin eta × Fin 3) :
    dirD a (prodPhase L R0 ρ R1) r = prodPhaseD L R0 ρ R1 r a :=
  dirD_eq_of_hasDerivAt ((contDiff_prodPhase.differentiable (by norm_num)) r)
    (hasDerivAt_prodPhase_line r a)

lemma dirD_cos_prodPhase (r : Rcfg eta) (a : Fin eta × Fin 3) :
    dirD a (fun x => Real.cos (prodPhase L R0 ρ R1 x)) r =
      -Real.sin (prodPhase L R0 ρ R1 r) * prodPhaseD L R0 ρ R1 r a := by
  refine dirD_eq_of_hasDerivAt ?_ ?_
  · exact (Real.differentiable_cos _).comp r
      ((contDiff_prodPhase.differentiable (by norm_num)) r)
  · have hl := hasDerivAt_prodPhase_line (L := L) (R0 := R0) (ρ := ρ) (R1 := R1) r a
    have h0 : prodPhase L R0 ρ R1 (r + (0 : ℝ) • Pi.single a 1) = prodPhase L R0 ρ R1 r := by
      rw [zero_smul, add_zero]
    have h := (Real.hasDerivAt_cos (prodPhase L R0 ρ R1 (r + (0 : ℝ) • Pi.single a 1))).comp
      (0 : ℝ) hl
    rw [h0] at h
    exact h

lemma dirD_sin_prodPhase (r : Rcfg eta) (a : Fin eta × Fin 3) :
    dirD a (fun x => Real.sin (prodPhase L R0 ρ R1 x)) r =
      Real.cos (prodPhase L R0 ρ R1 r) * prodPhaseD L R0 ρ R1 r a := by
  refine dirD_eq_of_hasDerivAt ?_ ?_
  · exact (Real.differentiable_sin _).comp r
      ((contDiff_prodPhase.differentiable (by norm_num)) r)
  · have hl := hasDerivAt_prodPhase_line (L := L) (R0 := R0) (ρ := ρ) (R1 := R1) r a
    have h0 : prodPhase L R0 ρ R1 (r + (0 : ℝ) • Pi.single a 1) = prodPhase L R0 ρ R1 r := by
      rw [zero_smul, add_zero]
    have h := (Real.hasDerivAt_sin (prodPhase L R0 ρ R1 (r + (0 : ℝ) • Pi.single a 1))).comp
      (0 : ℝ) hl
    rw [h0] at h
    exact h

/-- One particle outside `B_{R_L}(0)` makes the phase `π/2`. -/
lemma prodPhase_eq_of_out (hR1 : 0 < R1) (h12 : R1 < retainedRadius L R0 ρ) {r : Rcfg eta}
    {i : Fin eta} (hr : retainedRadius L R0 ρ ^ 2 ≤ pSq r i) :
    prodPhase L R0 ρ R1 r = Real.pi / 2 := by
  have hW : 0 < retainedRadius L R0 ρ ^ 2 - R1 ^ 2 := by nlinarith
  have h1 : 1 ≤ (pSq r i - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) := by
    rw [le_div_iff₀ hW]
    linarith
  have hT : oneT L R0 ρ R1 r i = 1 := Real.smoothTransition.one_of_one_le h1
  have hP : ∏ k, (1 - oneT L R0 ρ R1 r k) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hT, sub_self])
  unfold prodPhase
  rw [hP, sub_zero, mul_one]

/-- Every particle inside `B_{R₁}(0)` makes the phase `0`. -/
lemma prodPhase_eq_zero_of_in (hR1 : 0 < R1) (h12 : R1 < retainedRadius L R0 ρ) {r : Rcfg eta}
    (hr : ∀ i, ‖particle r i‖ < R1) : prodPhase L R0 ρ R1 r = 0 := by
  have hW : 0 < retainedRadius L R0 ρ ^ 2 - R1 ^ 2 := by nlinarith
  have hT : ∀ i, oneT L R0 ρ R1 r i = 0 := by
    intro i
    have hneg : (pSq r i - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [pSq_lt_of_norm_lt (hr i)]) hW.le
    exact Real.smoothTransition.zero_of_nonpos hneg
  unfold prodPhase
  simp [hT]

/-- The gradient of the product phase vanishes when every particle is inside `B_{R₁}(0)`. -/
lemma prodPhaseD_eq_zero_of_in (hR1 : 0 < R1) (h12 : R1 < retainedRadius L R0 ρ)
    {r : Rcfg eta} (hr : ∀ i, ‖particle r i‖ < R1) (a : Fin eta × Fin 3) :
    prodPhaseD L R0 ρ R1 r a = 0 := by
  have hW : 0 < retainedRadius L R0 ρ ^ 2 - R1 ^ 2 := by nlinarith
  have hneg : (pSq r a.1 - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) < 0 :=
    div_neg_of_neg_of_pos (by linarith [pSq_lt_of_norm_lt (hr a.1)]) hW
  unfold prodPhaseD
  rw [deriv_smoothTransition_eq_zero (Or.inl hneg)]
  ring

/-- The one-particle gradient bound
`π² T'(x_i)² |r_i|²/(R_L² - R₁²)² ≤ π² B² R_L²/(R_L² - R₁²)²`. -/
lemma one_particle_grad_le (hR1 : 0 < R1) (h12 : R1 < retainedRadius L R0 ρ) (r : Rcfg eta)
    (i : Fin eta) :
    Real.pi ^ 2 * deriv Real.smoothTransition
        ((pSq r i - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2)) ^ 2 * pSq r i /
      (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) ^ 2 ≤ locConst L R0 ρ R1 := by
  have hW : 0 < retainedRadius L R0 ρ ^ 2 - R1 ^ 2 := by nlinarith
  unfold locConst
  obtain ⟨x, hx⟩ : ∃ x, x = (pSq r i - R1 ^ 2) / (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) :=
    ⟨_, rfl⟩
  rw [← hx]
  have h0 := pSq_nonneg r i
  by_cases hd : deriv Real.smoothTransition x = 0
  · rw [hd]
    have : (0 : ℝ) ≤ Real.pi ^ 2 * smoothSlope ^ 2 * retainedRadius L R0 ρ ^ 2 /
        (retainedRadius L R0 ρ ^ 2 - R1 ^ 2) ^ 2 := by positivity
    simpa using this
  · have hx01 : x ≤ 1 := by
      by_contra h
      push Not at h
      exact hd (deriv_smoothTransition_eq_zero (Or.inr h))
    have hQ : pSq r i ≤ retainedRadius L R0 ρ ^ 2 := by
      rw [hx, div_le_one hW] at hx01
      linarith
    have hB := abs_deriv_le_smoothSlope x
    have hB2 : deriv Real.smoothTransition x ^ 2 ≤ smoothSlope ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hB 2
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc Real.pi ^ 2 * deriv Real.smoothTransition x ^ 2 * pSq r i
        ≤ Real.pi ^ 2 * smoothSlope ^ 2 * pSq r i := by gcongr
      _ ≤ Real.pi ^ 2 * smoothSlope ^ 2 * retainedRadius L R0 ρ ^ 2 := by gcongr

/-- **The gradient bound of the product pair**:
`Σ_a ((∂_a cos φ)² + (∂_a sin φ)²) ≤ η · locConst`. -/
lemma prod_grad_le (hR1 : 0 < R1) (h12 : R1 < retainedRadius L R0 ρ) (r : Rcfg eta) :
    ∑ a : Fin eta × Fin 3, (dirD a (fun x => Real.cos (prodPhase L R0 ρ R1 x)) r ^ 2 +
      dirD a (fun x => Real.sin (prodPhase L R0 ρ R1 x)) r ^ 2) ≤
      (eta : ℝ) * locConst L R0 ρ R1 := by
  have hW : 0 < retainedRadius L R0 ρ ^ 2 - R1 ^ 2 := by nlinarith
  set W := retainedRadius L R0 ρ ^ 2 - R1 ^ 2 with hWdef
  have hterm : ∀ a : Fin eta × Fin 3,
      dirD a (fun x => Real.cos (prodPhase L R0 ρ R1 x)) r ^ 2 +
        dirD a (fun x => Real.sin (prodPhase L R0 ρ R1 x)) r ^ 2 ≤
      Real.pi ^ 2 * deriv Real.smoothTransition ((pSq r a.1 - R1 ^ 2) / W) ^ 2 * r a ^ 2 /
        W ^ 2 := by
    intro a
    rw [dirD_cos_prodPhase, dirD_sin_prodPhase]
    unfold prodPhaseD
    set P := ∏ j ∈ Finset.univ.erase a.1, (1 - oneT L R0 ρ R1 r j) with hPdef
    set T' := deriv Real.smoothTransition ((pSq r a.1 - R1 ^ 2) / W) with hT'
    set φ := prodPhase L R0 ρ R1 r
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun j _ => sub_nonneg.mpr (oneT_le_one r j)
    have hP1 : P ≤ 1 := Finset.prod_le_one (fun j _ => sub_nonneg.mpr (oneT_le_one r j))
      (fun j _ => by linarith [oneT_nonneg (L := L) (R0 := R0) (ρ := ρ) (R1 := R1) r j])
    have hs := Real.sin_sq_add_cos_sq φ
    have e : (-Real.sin φ * (Real.pi / 2 * (P * (T' * (2 * r a / W))))) ^ 2 +
        (Real.cos φ * (Real.pi / 2 * (P * (T' * (2 * r a / W))))) ^ 2 =
        P ^ 2 * (Real.pi ^ 2 * T' ^ 2 * r a ^ 2 / W ^ 2) := by
      calc _ = (Real.sin φ ^ 2 + Real.cos φ ^ 2) * (Real.pi / 2 * (P * (T' * (2 * r a / W)))) ^ 2 :=
            by ring
        _ = (Real.pi / 2 * (P * (T' * (2 * r a / W)))) ^ 2 := by rw [hs, one_mul]
        _ = P ^ 2 * (Real.pi ^ 2 * T' ^ 2 * r a ^ 2 / W ^ 2) := by
            field_simp
    rw [e]
    have hP2 : P ^ 2 ≤ 1 := by nlinarith
    have hQ : 0 ≤ Real.pi ^ 2 * T' ^ 2 * r a ^ 2 / W ^ 2 := by positivity
    calc P ^ 2 * (Real.pi ^ 2 * T' ^ 2 * r a ^ 2 / W ^ 2)
        ≤ 1 * (Real.pi ^ 2 * T' ^ 2 * r a ^ 2 / W ^ 2) := mul_le_mul_of_nonneg_right hP2 hQ
      _ = _ := one_mul _
  calc ∑ a : Fin eta × Fin 3, (dirD a (fun x => Real.cos (prodPhase L R0 ρ R1 x)) r ^ 2 +
        dirD a (fun x => Real.sin (prodPhase L R0 ρ R1 x)) r ^ 2)
      ≤ ∑ a : Fin eta × Fin 3,
          Real.pi ^ 2 * deriv Real.smoothTransition ((pSq r a.1 - R1 ^ 2) / W) ^ 2 * r a ^ 2 /
            W ^ 2 := Finset.sum_le_sum fun a _ => hterm a
    _ = ∑ i : Fin eta,
          Real.pi ^ 2 * deriv Real.smoothTransition ((pSq r i - R1 ^ 2) / W) ^ 2 * pSq r i /
            W ^ 2 := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold pSq
        rw [Finset.mul_sum, Finset.sum_div]
    _ ≤ ∑ _i : Fin eta, locConst L R0 ρ R1 :=
        Finset.sum_le_sum fun i _ => one_particle_grad_le hR1 h12 r i
    _ = (eta : ℝ) * locConst L R0 ρ R1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The product localisation pair** `χ = cos(prodPhase)`, `η = sin(prodPhase)`, for
`0 < R₁ < R_L`: inner region `{every particle in B_{R₁}(0)}`, gradient constant `η · locConst`. -/
def prodLocPair (hR1 : 0 < R1) (h12 : R1 < retainedRadius L R0 ρ) :
    LocPair eta L R0 ρ {r | ∀ i, ‖particle r i‖ < R1} ((eta : ℝ) * locConst L R0 ρ R1) where
  χ := fun r => Real.cos (prodPhase L R0 ρ R1 r)
  η := fun r => Real.sin (prodPhase L R0 ρ R1 r)
  χ_smooth := Real.contDiff_cos.comp contDiff_prodPhase
  η_smooth := Real.contDiff_sin.comp contDiff_prodPhase
  sq_add := fun r => Real.cos_sq_add_sin_sq _
  χ_swap := fun i j r => by
    show Real.cos (prodPhase L R0 ρ R1 (freeSwap i j r)) = Real.cos (prodPhase L R0 ρ R1 r)
    rw [prodPhase_freeSwap]
  η_swap := fun i j r => by
    show Real.sin (prodPhase L R0 ρ R1 (freeSwap i j r)) = Real.sin (prodPhase L R0 ρ R1 r)
    rw [prodPhase_freeSwap]
  χ_supp := fun r hr i => by
    by_contra hlt
    push Not at hlt
    apply hr
    have hRL : 0 < retainedRadius L R0 ρ := lt_trans hR1 h12
    have hge : retainedRadius L R0 ρ ^ 2 ≤ pSq r i := by
      rw [pSq_eq_norm_sq]
      nlinarith
    simp only [prodPhase_eq_of_out hR1 h12 hge, Real.cos_pi_div_two]
  χ_one := fun r hr => by
    simp only [prodPhase_eq_zero_of_in hR1 h12 hr, Real.cos_zero]
  grad_bound := fun r => prod_grad_le hR1 h12 r
  grad_zero := fun r hr a => by
    have hD := prodPhaseD_eq_zero_of_in hR1 h12 hr a
    constructor
    · show dirD a (fun x => Real.cos (prodPhase L R0 ρ R1 x)) r = 0
      rw [dirD_cos_prodPhase, hD, mul_zero]
    · show dirD a (fun x => Real.sin (prodPhase L R0 ρ R1 x)) r = 0
      rw [dirD_sin_prodPhase, hD, mul_zero]

lemma measurableSet_prodInner (R1 : ℝ) :
    MeasurableSet {r : Rcfg eta | ∀ i, ‖particle r i‖ < R1} := by
  have h : {r : Rcfg eta | ∀ i, ‖particle r i‖ < R1} = ⋂ i, {r | ‖particle r i‖ < R1} := by
    ext r
    simp
  rw [h]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt (continuous_norm_particle i).measurable measurable_const

/-! ### On the torus -/

lemma abs_le_of_prodPhase (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hR1 : 0 < R1)
    (h12 : R1 < retainedRadius L R0 ρ) {r : Rcfg eta}
    (hr : prodPhase L R0 ρ R1 r ≠ Real.pi / 2) (a : Fin eta × Fin 3) : |r a| ≤ L / 4 := by
  have hlt : pSq r a.1 < retainedRadius L R0 ρ ^ 2 := by
    by_contra hge
    push Not at hge
    exact hr (prodPhase_eq_of_out hR1 h12 hge)
  have hRL : 0 < retainedRadius L R0 ρ := lt_trans hR1 h12
  have h1 : r a ^ 2 < retainedRadius L R0 ρ ^ 2 := lt_of_le_of_lt (sq_le_pSq r a) hlt
  have h2 : |r a| < retainedRadius L R0 ρ := abs_lt_of_sq_lt_sq h1 hRL.le
  have h3 : retainedRadius L R0 ρ ≤ L / 4 := by
    unfold retainedRadius
    linarith
  linarith

lemma constOutside_cos_prod (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hR1 : 0 < R1)
    (h12 : R1 < retainedRadius L R0 ρ) :
    ConstOutside L (fun r : Rcfg eta => Real.cos (prodPhase L R0 ρ R1 r)) 0 := by
  intro r hr a
  refine abs_le_of_prodPhase hR0 hρ hR1 h12 (fun h => hr ?_) a
  simp only [h, Real.cos_pi_div_two]

lemma constOutside_sin_prod (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hR1 : 0 < R1)
    (h12 : R1 < retainedRadius L R0 ρ) :
    ConstOutside L (fun r : Rcfg eta => Real.sin (prodPhase L R0 ρ R1 r)) 1 := by
  intro r hr a
  refine abs_le_of_prodPhase hR0 hρ hR1 h12 (fun h => hr ?_) a
  simp only [h, Real.sin_pi_div_two]

lemma contDiff_cosProdPhase :
    ContDiff ℝ 2 (fun r : Rcfg eta => Real.cos (prodPhase L R0 ρ R1 r)) :=
  Real.contDiff_cos.comp contDiff_prodPhase

lemma contDiff_sinProdPhase :
    ContDiff ℝ 2 (fun r : Rcfg eta => Real.sin (prodPhase L R0 ρ R1 r)) :=
  Real.contDiff_sin.comp contDiff_prodPhase

lemma measurableSet_prodInnerT (L R1 : ℝ) :
    MeasurableSet {x : MolecularPositionTorus eta | ∀ i, ‖particle (cellCoord L x) i‖ < R1} :=
  (measurableSet_prodInner R1).preimage (measurable_cellCoord L)

/-- **The product localisation pair on the torus**, `c = cos(prodPhase(L·rep))`, `e = sin(…)`. -/
def prodTorusLocPair (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hR1 : 0 < R1)
    (h12 : R1 < retainedRadius L R0 ρ) :
    TorusLocPair eta L R0 ρ {x | ∀ i, ‖particle (cellCoord L x) i‖ < R1}
      ((eta : ℝ) * locConst L R0 ρ R1) where
  c := cellFun L (fun r => Real.cos (prodPhase L R0 ρ R1 r))
  e := cellFun L (fun r => Real.sin (prodPhase L R0 ρ R1 r))
  c_smooth := contDiff_liftR_cell hL contDiff_cosProdPhase (constOutside_cos_prod hR0 hρ hR1 h12)
  e_smooth := contDiff_liftR_cell hL contDiff_sinProdPhase (constOutside_sin_prod hR0 hρ hR1 h12)
  sq_add := fun x => Real.cos_sq_add_sin_sq _
  c_swap := fun i j x => by
    unfold cellFun
    exact (prodLocPair (eta := eta) hR1 h12).χ_swap i j (cellCoord L x)
  e_swap := fun i j x => by
    unfold cellFun
    exact (prodLocPair (eta := eta) hR1 h12).η_swap i j (cellCoord L x)
  c_supp := fun x hx i => (prodLocPair (eta := eta) hR1 h12).χ_supp (cellCoord L x) hx i
  c_one := fun x hx => (prodLocPair (eta := eta) hR1 h12).χ_one (cellCoord L x) hx
  grad_bound := fun x => by
    rw [show (∑ a : Fin eta × Fin 3,
        (tDR a (cellFun L (fun r => Real.cos (prodPhase L R0 ρ R1 r))) x ^ 2 +
        tDR a (cellFun L (fun r => Real.sin (prodPhase L R0 ρ R1 r))) x ^ 2)) =
        L ^ 2 * ∑ a : Fin eta × Fin 3,
          (dirD a (fun r => Real.cos (prodPhase L R0 ρ R1 r)) (cellCoord L x) ^ 2 +
            dirD a (fun r => Real.sin (prodPhase L R0 ρ R1 r)) (cellCoord L x) ^ 2) by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [tDR_cell hL contDiff_cosProdPhase (constOutside_cos_prod hR0 hρ hR1 h12),
        tDR_cell hL contDiff_sinProdPhase (constOutside_sin_prod hR0 hρ hR1 h12)]
      ring]
    have h := (prodLocPair (eta := eta) hR1 h12).grad_bound (cellCoord L x)
    have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
    calc L ^ 2 * _ ≤ L ^ 2 * ((eta : ℝ) * locConst L R0 ρ R1) := mul_le_mul_of_nonneg_left h hL2
      _ = (eta : ℝ) * locConst L R0 ρ R1 * L ^ 2 := mul_comm _ _
  grad_zero := fun x hx a => by
    have h := (prodLocPair (eta := eta) hR1 h12).grad_zero (cellCoord L x) hx a
    constructor
    · rw [tDR_cell hL contDiff_cosProdPhase (constOutside_cos_prod hR0 hρ hR1 h12)]
      have h1 : dirD a (fun r => Real.cos (prodPhase L R0 ρ R1 r)) (cellCoord L x) = 0 := h.1
      rw [h1, mul_zero]
    · rw [tDR_cell hL contDiff_sinProdPhase (constOutside_sin_prod hR0 hρ hR1 h12)]
      have h2 : dirD a (fun r => Real.sin (prodPhase L R0 ρ R1 r)) (cellCoord L x) = 0 := h.2
      rw [h2, mul_zero]

/-- `η · locConst ≤ η π² B²/w²` for the transition width `w = R_L - R₁ ≤ R_L`. -/
lemma eta_locConst_le {w : ℝ} (hw : 0 < w) (hR1 : R1 = retainedRadius L R0 ρ - w)
    (hwL : w ≤ retainedRadius L R0 ρ) :
    (eta : ℝ) * locConst L R0 ρ R1 ≤ (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 := by
  have h := locConst_le (L := L) (R0 := R0) (ρ := ρ) hw hR1 hwL
  have he : (0 : ℝ) ≤ eta := Nat.cast_nonneg _
  calc (eta : ℝ) * locConst L R0 ρ R1 ≤ (eta : ℝ) * (Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2) :=
        mul_le_mul_of_nonneg_left h he
    _ = _ := by ring

end Pair

/-! ## `prop:free` in the product geometry -/

section System

variable {ν : Type} [Fintype ν]

/-- **`prop:free`, upper bound, product geometry.** As `free_upper_agmon`, with the Agmon mass
hypothesis on the complement of the product region `{every particle in B_{R_L - w}(0)}`:
`E_L + C₀ ≤ E_∞ + η π² B² τ/(2 w² (1 - τ))`. -/
theorem free_upper_agmon_prod (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ} {L R R0 ρ w : ℝ}
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
      ∫ r in {r | ∀ i, ‖particle r i‖ < retainedRadius L R0 ρ - w}ᶜ, ‖φ r‖ ^ 2 ≤ τ) :
    E + (zeroModeShift sys L θ).re ≤
      Einf + (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * τ / (2 * (1 - τ)) := by
  have hR1 : 0 < retainedRadius L R0 ρ - w := by linarith
  have h12 : retainedRadius L R0 ρ - w < retainedRadius L R0 ρ := by linarith
  have h := free_upper_ims sys hL hθ hR hR0 hρ hone P hP hpos hE
    (measurableSet_prodInner _) (prodLocPair hR1 h12) hτ hlow happrox
  have hτ0 : 0 ≤ τ := by
    obtain ⟨φ, -, -, -, -, -, -, ht⟩ := happrox 1 one_pos
    exact le_trans (setIntegral_nonneg_of_ae (ae_of_all _ fun r => by positivity)) ht
  have hM := eta_locConst_le (eta := eta) (L := L) (R0 := R0) (ρ := ρ)
    (R1 := retainedRadius L R0 ρ - w) hw rfl hwL.le
  have hd : 0 < 2 * (1 - τ) := by linarith
  have h2 : (eta : ℝ) * locConst L R0 ρ (retainedRadius L R0 ρ - w) * τ / (2 * (1 - τ)) ≤
      (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * τ / (2 * (1 - τ)) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hM hτ0) hd.le
  linarith

/-- **`prop:free`, the upper bound for the grid energy, product geometry**:
`E_{N,L} + C₀ ≤ E_∞ + η π² B² τ/(2 w² (1 - τ)) + C K^{-3}`, `K = 2πm/L`. -/
theorem free_grid_upper_agmon_prod (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
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
      ∫ r in {r | ∀ i, ‖particle r i‖ < retainedRadius L R0 ρ - w}ᶜ, ‖φ r‖ ^ 2 ≤ τ) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E ∧
      E + (zeroModeShift sys L θ).re ≤
        Einf + (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * τ / (2 * (1 - τ)) ∧
      ∀ m : ℕ, PlaneWaveGridG.gLGridThreshold sys L (tv R θ) E ≤ m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          Eg + (zeroModeShift sys L θ).re ≤
            Einf + (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * τ / (2 * (1 - τ)) +
              PlaneWaveGridG.gLGridErrorConstant sys L (tv R θ) E /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  obtain ⟨E, hE, hgrid⟩ := PlaneWaveGridG.gLSectorGridError sys lab hlab hL hθ
  have hup := free_upper_agmon_prod sys hL hθ hR hR0 hρ hone P hP hpos hE hw hwL hτ hlow happrox
  refine ⟨E, hE, hup, fun m hm => ?_⟩
  obtain ⟨Eg, hEg, herr⟩ := hgrid m hm
  refine ⟨Eg, hEg, ?_⟩
  have h := (abs_le.mp herr).2
  linarith

/-- **`prop:free`, the two-sided bound, product geometry** (eq:free-energy). As
`free_grid_two_sided`, with the mass hypotheses (Agmon decay of the free ground state, and
assumption (A) for `C²` approximants of the torus ground state) on the complement of the product
region `{every particle in B_{R_L - w}(0)}`, and
`δ = η π² B²/w² · max(τ/(2(1-τ)), τ_A/(2(1-τ_A)))`: `|E_L + C₀ - E_∞| ≤ δ` and
`|E_{N,L} + C₀ - E_∞| ≤ δ + C K^{-3}`. -/
theorem free_grid_two_sided_prod (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (hw : 0 < w) (hwL : w < retainedRadius L R0 ρ)
    {EL : ℝ} (hEL : IsGLTorusGroundEnergy sys lab L θ EL)
    {Einf τ τA : ℝ} (hτ : τ < 1) (hτA : τA < 1)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (happrox : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | ∀ i, ‖particle r i‖ < retainedRadius L R0 ρ - w}ᶜ, ‖φ r‖ ^ 2 ≤ τ)
    (hA : ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy sys L θ u hu ≤ EL + ε ∧
      ∫ x in {x | ∀ i, ‖particle (cellCoord L x) i‖ < retainedRadius L R0 ρ - w}ᶜ,
        ‖u x‖ ^ 2 ≤ τA) :
    |EL + (zeroModeShift sys L θ).re - Einf| ≤
        (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 *
          max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) ∧
      ∀ m : ℕ, PlaneWaveGridG.gLGridThreshold sys L (tv R θ) EL ≤ m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 *
                max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) +
              PlaneWaveGridG.gLGridErrorConstant sys L (tv R θ) EL /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  have hR1 : 0 < retainedRadius L R0 ρ - w := by linarith
  have h12 : retainedRadius L R0 ρ - w < retainedRadius L R0 ρ := by linarith
  set K0 := (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 with hK0
  have hK0nn : 0 ≤ K0 := by positivity
  set δ := K0 * max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) with hδ
  have hτA0 : 0 ≤ τA := by
    obtain ⟨u, -, -, -, -, ht⟩ := hA 1 one_pos
    exact le_trans (setIntegral_nonneg_of_ae (ae_of_all _ fun x => by positivity)) ht
  -- upper bound
  have hup := free_upper_agmon_prod sys hL hθ hR hR0 hρ hone P hP hpos hEL hw hwL hτ hlow happrox
  have hup' : EL + (zeroModeShift sys L θ).re ≤ Einf + δ := by
    have h1 : K0 * τ / (2 * (1 - τ)) = K0 * (τ / (2 * (1 - τ))) := by ring
    have h2 : K0 * (τ / (2 * (1 - τ))) ≤ δ :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) hK0nn
    linarith
  -- lower bound
  have hlowb := free_lower_torus sys hL hθ hR hR0 hρ hone P hP hpos hEL
    (measurableSet_prodInnerT L (retainedRadius L R0 ρ - w))
    (prodTorusLocPair hL hR0 hρ hR1 h12) hτA hlow hA
  have hM := eta_locConst_le (eta := eta) (L := L) (R0 := R0) (ρ := ρ)
    (R1 := retainedRadius L R0 ρ - w) hw rfl hwL.le
  have hlow' : Einf ≤ EL + (zeroModeShift sys L θ).re + δ := by
    have hdA : 0 < 2 * (1 - τA) := by linarith
    have h1 : (eta : ℝ) * locConst L R0 ρ (retainedRadius L R0 ρ - w) * τA / (2 * (1 - τA)) ≤
        K0 * (τA / (2 * (1 - τA))) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hM (div_nonneg hτA0 hdA.le)
    have h2 : K0 * (τA / (2 * (1 - τA))) ≤ δ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hK0nn
    linarith
  have habs : |EL + (zeroModeShift sys L θ).re - Einf| ≤ δ := by
    rw [abs_le]
    constructor <;> linarith
  refine ⟨habs, fun m hm => ?_⟩
  obtain ⟨E, hE, hgrid⟩ := PlaneWaveGridG.gLSectorGridError sys lab hlab hL hθ
  have hEE : E = EL := hE.unique hEL
  subst hEE
  obtain ⟨Eg, hEg, herr⟩ := hgrid m hm
  refine ⟨Eg, hEg, ?_⟩
  have h3 : |Eg + (zeroModeShift sys L θ).re - Einf| ≤
      |Eg - E| + |E + (zeroModeShift sys L θ).re - Einf| := by
    have := abs_add_le (Eg - E) (E + (zeroModeShift sys L θ).re - Einf)
    rw [show Eg - E + (E + (zeroModeShift sys L θ).re - Einf) =
      Eg + (zeroModeShift sys L θ).re - Einf by ring] at this
    exact this
  linarith

/-- **eq:free-energy in exponential form, product geometry.** As `free_grid_exponential`, with the
masses outside the product region `{every particle in B_d(0)}`, `d = R_L - w`, at most
`A e^{-2αd}` (Agmon decay of the free ground state) and `A' e^{-2βd}` (assumption (A)), both at
most `1/2`: `|E_L + C₀ - E_∞| ≤ C' e^{-γ L}` and `|E_{N,L} + C₀ - E_∞| ≤ C' e^{-γ L} + C K^{-3}`,
with `γ = min(α, β)/2` and `C' = η π² B²/w² · max(A, A') · e^{2 max(α, β)(R₀ + ρ + w)}`. -/
theorem free_grid_exponential_prod (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (hw : 0 < w) (hwL : w < retainedRadius L R0 ρ)
    {EL : ℝ} (hEL : IsGLTorusGroundEnergy sys lab L θ EL)
    {Einf A α A' β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsmall : A * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))) ≤ 1 / 2)
    (hsmall' : A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w))) ≤ 1 / 2)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (happrox : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | ∀ i, ‖particle r i‖ < retainedRadius L R0 ρ - w}ᶜ, ‖φ r‖ ^ 2 ≤
        A * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))))
    (hA : ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy sys L θ u hu ≤ EL + ε ∧
      ∫ x in {x | ∀ i, ‖particle (cellCoord L x) i‖ < retainedRadius L R0 ρ - w}ᶜ,
        ‖u x‖ ^ 2 ≤ A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w)))) :
    |EL + (zeroModeShift sys L θ).re - Einf| ≤
        (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
          Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) ∧
      ∀ m : ℕ, PlaneWaveGridG.gLGridThreshold sys L (tv R θ) EL ≤ m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
              Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) +
              PlaneWaveGridG.gLGridErrorConstant sys L (tv R θ) EL /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  set d := retainedRadius L R0 ρ - w with hd
  have hd0 : 0 < d := by linarith
  set τ := A * Real.exp (-(2 * α * d)) with hτ_def
  set τA := A' * Real.exp (-(2 * β * d)) with hτA_def
  have hτ0 : 0 ≤ τ := by
    obtain ⟨φ, -, -, -, -, -, -, ht⟩ := happrox 1 one_pos
    exact le_trans (setIntegral_nonneg_of_ae (ae_of_all _ fun r => by positivity)) ht
  have hτA0 : 0 ≤ τA := by
    obtain ⟨u, -, -, -, -, ht⟩ := hA 1 one_pos
    exact le_trans (setIntegral_nonneg_of_ae (ae_of_all _ fun x => by positivity)) ht
  obtain ⟨h1, h2⟩ := free_grid_two_sided_prod sys lab hlab hL hθ hR hR0 hρ hone P hP hpos hw hwL
    hEL (by linarith : τ < 1) (by linarith : τA < 1) hlow happrox hA
  have hA0 : 0 ≤ A := by
    by_contra h
    push Not at h
    have : A * Real.exp (-(2 * α * d)) < 0 := mul_neg_of_neg_of_pos h (Real.exp_pos _)
    linarith
  have hexp : ∀ γ' : ℝ, min α β ≤ γ' → Real.exp (-(2 * γ' * d)) ≤
      Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) := by
    intro γ' hγ'
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hdL : d = L / 4 - R0 - ρ - w := by rw [hd]; unfold retainedRadius; ring
    have hm1 : min α β ≤ max α β := min_le_max
    have hm0 : 0 ≤ min α β := le_min hα hβ
    have hRw : 0 ≤ R0 + ρ + w := by linarith
    rw [hdL]
    nlinarith [mul_le_mul_of_nonneg_right hγ' hd0.le, mul_le_mul_of_nonneg_right hm1 hRw]
  have hbound : max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) ≤
      max A A' * (Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2))) := by
    apply max_le
    · calc τ / (2 * (1 - τ)) ≤ τ := half_ratio_le hτ0 hsmall
        _ = A * Real.exp (-(2 * α * d)) := rfl
        _ ≤ max A A' * (Real.exp (2 * max α β * (R0 + ρ + w)) *
              Real.exp (-(min α β * L / 2))) :=
          mul_le_mul (le_max_left _ _) (hexp α (min_le_left _ _)) (Real.exp_pos _).le
            (le_trans hA0 (le_max_left _ _))
    · calc τA / (2 * (1 - τA)) ≤ τA := half_ratio_le hτA0 hsmall'
        _ = A' * Real.exp (-(2 * β * d)) := rfl
        _ ≤ max A A' * (Real.exp (2 * max α β * (R0 + ρ + w)) *
              Real.exp (-(min α β * L / 2))) :=
          mul_le_mul (le_max_right _ _) (hexp β (min_le_right _ _)) (Real.exp_pos _).le
            (le_trans hA0 (le_max_left _ _))
  have hK0 : 0 ≤ (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 := by positivity
  have hfin := mul_le_mul_of_nonneg_left hbound hK0
  have heq : (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * (max A A' *
      (Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)))) =
      (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
        Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) := by ring
  rw [heq] at hfin
  refine ⟨h1.trans hfin, fun m hm => ?_⟩
  obtain ⟨Eg, hEg, herr⟩ := h2 m hm
  exact ⟨Eg, hEg, by linarith⟩

/-- **`prop:free`, the two-sided bound, product geometry, `L`-uniform grid constant.** As
`free_grid_two_sided_prod`, for `L ≥ 2π`, with the grid error `C K^{-3}` of
`gLSectorGridErrorU`. -/
theorem free_grid_two_sidedU_prod (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L)
    (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (hw : 0 < w) (hwL : w < retainedRadius L R0 ρ)
    {EL : ℝ} (hEL : IsGLTorusGroundEnergy sys lab L θ EL)
    {Einf τ τA : ℝ} (hτ : τ < 1) (hτA : τA < 1)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (happrox : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | ∀ i, ‖particle r i‖ < retainedRadius L R0 ρ - w}ᶜ, ‖φ r‖ ^ 2 ≤ τ)
    (hA : ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy sys L θ u hu ≤ EL + ε ∧
      ∫ x in {x | ∀ i, ‖particle (cellCoord L x) i‖ < retainedRadius L R0 ρ - w}ᶜ,
        ‖u x‖ ^ 2 ≤ τA) :
    |EL + (zeroModeShift sys L θ).re - Einf| ≤
        (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 *
          max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) ∧
      ∀ Eb : ℝ, |EL| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys (tv R θ) Eb ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 *
                max (τ / (2 * (1 - τ))) (τA / (2 * (1 - τA))) +
              PlaneWaveGridG.gLErrorConstU sys (tv R θ) Eb /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have h := free_grid_two_sided_prod sys lab hlab hL0 hθ hR hR0 hρ hone P hP hpos hw hwL hEL hτ
    hτA hlow happrox hA
  refine ⟨h.1, fun Eb hEb m hm hK => ?_⟩
  obtain ⟨E, hE, hgrid⟩ := PlaneWaveGridG.gLSectorGridErrorU sys lab hlab hL hθ
  have hEE : E = EL := hE.unique hEL
  subst hEE
  obtain ⟨Eg, hEg, herr⟩ := hgrid Eb hEb m hm hK
  refine ⟨Eg, hEg, ?_⟩
  have h3 : |Eg + (zeroModeShift sys L θ).re - Einf| ≤
      |Eg - E| + |E + (zeroModeShift sys L θ).re - Einf| := by
    have := abs_add_le (Eg - E) (E + (zeroModeShift sys L θ).re - Einf)
    rw [show Eg - E + (E + (zeroModeShift sys L θ).re - Einf) =
      Eg + (zeroModeShift sys L θ).re - Einf by ring] at this
    exact this
  linarith [h.1]

/-- **eq:free-energy in exponential form, product geometry, `L`-uniform grid constant**
(`prop:free` as stated, with the retained region and assumption (A) in the product geometry of
the manuscript). For `L ≥ 2π`: `|E_L + C₀ - E_∞| ≤ C' e^{-γ L}` and, for every energy budget
`E_b ≥ |E_L| + 1` and `m ≥ η + 8` with `K = (2π/L) m ≥ K₀(E_b)`,
`|E_{N,L} + C₀ - E_∞| ≤ C' e^{-γ L} + C(E_b) K^{-3}`, with `γ = min(α, β)/2`,
`C' = η π² B²/w² · max(A, A') · e^{2 max(α, β)(R₀ + ρ + w)}`; `K₀` and `C` do not depend on
`L`. -/
theorem free_grid_exponentialU_prod (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L R R0 ρ w : ℝ} {θ : ℝ → ℝ} (hL : 2 * Real.pi ≤ L)
    (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (hw : 0 < w) (hwL : w < retainedRadius L R0 ρ)
    {EL : ℝ} (hEL : IsGLTorusGroundEnergy sys lab L θ EL)
    {Einf A α A' β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsmall : A * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))) ≤ 1 / 2)
    (hsmall' : A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w))) ≤ 1 / 2)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (happrox : ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | ∀ i, ‖particle r i‖ < retainedRadius L R0 ρ - w}ᶜ, ‖φ r‖ ^ 2 ≤
        A * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))))
    (hA : ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy sys L θ u hu ≤ EL + ε ∧
      ∫ x in {x | ∀ i, ‖particle (cellCoord L x) i‖ < retainedRadius L R0 ρ - w}ᶜ,
        ‖u x‖ ^ 2 ≤ A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w)))) :
    |EL + (zeroModeShift sys L θ).re - Einf| ≤
        (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
          Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) ∧
      ∀ Eb : ℝ, |EL| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        PlaneWaveGridG.gLKThresholdU sys (tv R θ) Eb ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy sys lab L m
            (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L (tv R θ))
              (PlaneWaveGridG.gLref L θ (tv R θ)) m) Eg ∧
          |Eg + (zeroModeShift sys L θ).re - Einf| ≤
            (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
              Real.exp (2 * max α β * (R0 + ρ + w)) * Real.exp (-(min α β * L / 2)) +
              PlaneWaveGridG.gLErrorConstU sys (tv R θ) Eb /
                ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have h := free_grid_exponential_prod sys lab hlab hL0 hθ hR hR0 hρ hone P hP hpos hw hwL hEL
    hα hβ hsmall hsmall' hlow happrox hA
  refine ⟨h.1, fun Eb hEb m hm hK => ?_⟩
  obtain ⟨E, hE, hgrid⟩ := PlaneWaveGridG.gLSectorGridErrorU sys lab hlab hL hθ
  have hEE : E = EL := hE.unique hEL
  subst hEE
  obtain ⟨Eg, hEg, herr⟩ := hgrid Eb hEb m hm hK
  refine ⟨Eg, hEg, ?_⟩
  have h3 : |Eg + (zeroModeShift sys L θ).re - Einf| ≤
      |Eg - E| + |E + (zeroModeShift sys L θ).re - Einf| := by
    have := abs_add_le (Eg - E) (E + (zeroModeShift sys L θ).re - Einf)
    rw [show Eg - E + (E + (zeroModeShift sys L θ).re - Einf) =
      Eg + (zeroModeShift sys L θ).re - Einf by ring] at this
    exact this
  linarith [h.1]

end System

end

end FreeBoundary
