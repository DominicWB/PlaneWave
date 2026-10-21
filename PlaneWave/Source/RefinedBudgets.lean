import PlaneWave.Source.RetainedRotations

/-!
# Flux/source build, block 5: goodness with refined budgets

* `isGood_perturb'`: a perturbation `e` with `‖e‖ ≤ δ`, `‖(1+A) e‖ ≤ δ₁` keeps goodness with the
  budget `M + δ (1+K')^{5/2} + δ₁ (1+K')^{1/2}` (`K' = √3 g n` bounds every cube momentum; the
  tails of `e` vanish beyond `K'`).  With `δ = O(Ξ K^{-3} polylog)`, `δ₁ = O(Ξ K^{-1} polylog)`
  (the rotated data), the extra budget is `O(Ξ K^{-1/2} polylog)`.
* `good_of_decomp` (**the static form of `lem:good-stab`**): if `A χ = f + e - W_N χ - d` with
  `Θ(χ) ≤ Θ₁`, `Θ(f) ≤ Θ_f`, `‖e‖ ≤ ε`, `‖d‖ ≤ δ`, then `χ` is good with the budget
  `2Θ₁ + (2m̄ + 1)(2m̄ Θ_f + (ε + δ)(1+K')^{1/2} + C_tail(3m̄Θ₁) + √2 C_m (1+2g) Θ₁)`.
  The defect `e` and the correction `d` enter through `(1+K')^{1/2}` only (the weighted tail at
  `λ ≤ K'` is `λ^{-1/2}`), not through a power of `K'` that would absorb the budget.
* `good_stab'` (`lem:good-stab` with that budget): `e^{-iH's} χ₀` for `H' = H_N + ΔH`,
  `χ₀ = P ψ₀ + r₀`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Good

variable (sys : CoulombSystem eta ν) {L : ℝ} {n : ℕ}

omit [Fintype ν] in
lemma one_le_rpow_mul_rpow_neg {l K p : ℝ} (hl : 1 ≤ l) (hlK : l ≤ K) (hp : 0 ≤ p) :
    1 ≤ (1 + K) ^ p * l ^ (-p) := by
  have hl0 : 0 < l := by linarith
  rw [Real.rpow_neg hl0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hl0 _), one_mul]
  exact Real.rpow_le_rpow hl0.le (by linarith) hp

omit [Fintype ν] in
/-- **Refined perturbation of good states.** -/
theorem isGood_perturb' (hL : 0 < L) {M δ δ₁ : ℝ} {u e : En eta n} (hu : IsGood sys L 1 M u)
    (he : ‖e‖ ≤ δ) (he1 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 e‖ ≤ δ₁) :
    IsGood sys L 1 (M + (δ * (1 + Real.sqrt 3 * (gF L * n)) ^ (5 / 2 : ℝ) +
      δ₁ * (1 + Real.sqrt 3 * (gF L * n)) ^ (1 / 2 : ℝ))) (u + e) := by
  set Kq := Real.sqrt 3 * (gF L * n)
  have hKq : 0 ≤ Kq := by have := gF_pos hL; positivity
  have hδ : 0 ≤ δ := le_trans (norm_nonneg _) he
  have hδ₁ : 0 ≤ δ₁ := le_trans (norm_nonneg _) he1
  have hp52 : 1 ≤ (1 + Kq) ^ (5 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hp12 : 1 ≤ (1 + Kq) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have he_good : IsGood sys L 1 (δ * (1 + Kq) ^ (5 / 2 : ℝ) + δ₁ * (1 + Kq) ^ (1 / 2 : ℝ)) e := by
    refine ⟨?_, fun a l hl => ⟨?_, ?_⟩⟩
    · rw [one_mul]
      have h1 : δ ≤ δ * (1 + Kq) ^ (5 / 2 : ℝ) := le_mul_of_one_le_right hδ hp52
      have h2 : δ₁ ≤ δ₁ * (1 + Kq) ^ (1 / 2 : ℝ) := le_mul_of_one_le_right hδ₁ hp12
      linarith
    · rw [one_mul]
      by_cases hlK : Kq ≤ l
      · rw [regTail_eq_zero_of_large hL a hlK, norm_zero]
        have := Real.rpow_nonneg (show (0 : ℝ) ≤ l by linarith) (-(5 / 2 : ℝ))
        have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + Kq by linarith) (5 / 2 : ℝ)
        have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + Kq by linarith) (1 / 2 : ℝ)
        positivity
      · push Not at hlK
        have h1 := one_le_rpow_mul_rpow_neg hl hlK.le (by norm_num : (0 : ℝ) ≤ 5 / 2)
        have hl0 : 0 ≤ l ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
        calc ‖regTail L a l e‖ ≤ ‖e‖ := norm_regTail_le L a l e
          _ ≤ δ := he
          _ ≤ δ * ((1 + Kq) ^ (5 / 2 : ℝ) * l ^ (-(5 / 2 : ℝ))) := le_mul_of_one_le_right hδ h1
          _ ≤ (δ * (1 + Kq) ^ (5 / 2 : ℝ) + δ₁ * (1 + Kq) ^ (1 / 2 : ℝ)) * l ^ (-(5 / 2 : ℝ)) := by
              have : 0 ≤ δ₁ * (1 + Kq) ^ (1 / 2 : ℝ) * l ^ (-(5 / 2 : ℝ)) := by positivity
              nlinarith
    · rw [one_mul]
      by_cases hlK : Kq ≤ l
      · rw [regTail_eq_zero_of_large hL a hlK, wt_one_zero, norm_zero]
        have := Real.rpow_nonneg (show (0 : ℝ) ≤ l by linarith) (-(1 / 2 : ℝ))
        have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + Kq by linarith) (5 / 2 : ℝ)
        have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + Kq by linarith) (1 / 2 : ℝ)
        positivity
      · push Not at hlK
        have h1 := one_le_rpow_mul_rpow_neg hl hlK.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
        have hl0 : 0 ≤ l ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
        rw [wt_regTail]
        calc ‖regTail L a l (FSSpectral.wt (sb eta n) (Asym sys L n) 1 e)‖
            ≤ ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 e‖ := norm_regTail_le L a l _
          _ ≤ δ₁ := he1
          _ ≤ δ₁ * ((1 + Kq) ^ (1 / 2 : ℝ) * l ^ (-(1 / 2 : ℝ))) := le_mul_of_one_le_right hδ₁ h1
          _ ≤ (δ * (1 + Kq) ^ (5 / 2 : ℝ) + δ₁ * (1 + Kq) ^ (1 / 2 : ℝ)) * l ^ (-(1 / 2 : ℝ)) := by
              have : 0 ≤ δ * (1 + Kq) ^ (5 / 2 : ℝ) * l ^ (-(1 / 2 : ℝ)) := by
                have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + Kq by linarith) (5 / 2 : ℝ)
                positivity
              nlinarith
  exact isGood_add sys hu he_good

/-- The budget of the static goodness criterion. -/
noncomputable def Mdec (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (Θ₁ Θf ε δ : ℝ) : ℝ :=
  2 * Θ₁ + (2 * sys.maxMass + 1) *
    (2 * sys.maxMass * Θf + (ε + δ) * Real.sqrt (1 + Real.sqrt 3 * (gF L * n)) +
      (CtW sys L Hunit (3 * sys.maxMass * Θ₁) +
        Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) * Θ₁))

variable (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

omit [Fintype ν] in
/-- Goodness from the tails of `A χ` (`l^{-1/2}` decay below the cube cutoff). -/
theorem good_of_kin_tails (hL : 0 < L) (χ : En eta n) {Θ₁ B : ℝ}
    (hΘ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ‖ ≤ Θ₁) (hB : 0 ≤ B)
    (hAt : ∀ (a : Fin eta) (l : ℝ), 1 ≤ l → l < Real.sqrt 3 * (gF L * n) →
      ‖regTail L a l (FSSpectral.kin (sb eta n) (Asym sys L n) χ)‖ ≤ B * l ^ (-(1 / 2 : ℝ))) :
    IsGood sys L 1 (2 * Θ₁ + (2 * sys.maxMass + 1) * B) χ := by
  have hm := sys.one_le_maxMass
  have hΘ₁0 : 0 ≤ Θ₁ := le_trans (norm_nonneg _) hΘ
  have hχΘ : ‖χ‖ ≤ Θ₁ := (norm_le_wt sys L n zero_le_one χ).trans hΘ
  have hMB : 0 ≤ (2 * sys.maxMass + 1) * B := by positivity
  refine ⟨?_, fun a l hl => ?_⟩
  · rw [one_mul]; linarith
  have hl0 : 0 < l := by linarith
  by_cases hlK : Real.sqrt 3 * (gF L * n) ≤ l
  · rw [regTail_eq_zero_of_large hL a hlK, norm_zero, wt_one_zero, norm_zero]
    exact ⟨by have := Real.rpow_nonneg hl0.le (-(5 / 2 : ℝ)); positivity,
      by have := Real.rpow_nonneg hl0.le (-(1 / 2 : ℝ)); positivity⟩
  push Not at hlK
  have hAt' := hAt a l hl hlK
  have hmass := sys.mass_le_maxMass a
  have hinv : 1 / l ^ 2 * l ^ (-(1 / 2 : ℝ)) = l ^ (-(5 / 2 : ℝ)) := by
    rw [rpow_neg_five_half_eq hl0, rpow_neg_half_eq hl0]; field_simp
  have hT : ‖regTail L a l χ‖ ≤ 2 * sys.maxMass * B * l ^ (-(5 / 2 : ℝ)) := by
    refine (regTail_le_kin sys hL a hl0 χ).trans ?_
    rw [kin_regTail]
    calc 2 * sys.mass a / l ^ 2 * ‖regTail L a l (FSSpectral.kin (sb eta n) (Asym sys L n) χ)‖
        ≤ 2 * sys.maxMass * (1 / l ^ 2) * (B * l ^ (-(1 / 2 : ℝ))) := by
          rw [div_eq_mul_one_div (2 * sys.mass a)]
          gcongr
      _ = 2 * sys.maxMass * B * (1 / l ^ 2 * l ^ (-(1 / 2 : ℝ))) := by ring
      _ = _ := by rw [hinv]
  have h52 : l ^ (-(5 / 2 : ℝ)) ≤ l ^ (-(1 / 2 : ℝ)) := rpow_le_of_le_one hl (by norm_num)
  have hlr : 0 ≤ l ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hl0.le _
  have hlr' : 0 ≤ l ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hl0.le _
  constructor
  · rw [one_mul]
    refine hT.trans ?_
    have h1 : 0 ≤ 2 * Θ₁ * l ^ (-(5 / 2 : ℝ)) := by positivity
    have h2 : 0 ≤ B * l ^ (-(5 / 2 : ℝ)) := mul_nonneg hB hlr
    linarith
  · rw [one_mul]
    have hw : FSSpectral.wt (sb eta n) (Asym sys L n) 1 (regTail L a l χ) =
        regTail L a l χ + FSSpectral.kin (sb eta n) (Asym sys L n) (regTail L a l χ) := by
      ext q; rw [wt_one_apply, PiLp.add_apply, kin_apply']; push_cast; ring
    rw [hw, kin_regTail sys a l χ]
    refine (norm_add_le _ _).trans ?_
    have h1 : 0 ≤ 2 * Θ₁ * l ^ (-(1 / 2 : ℝ)) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h52 (by positivity : (0 : ℝ) ≤ 2 * sys.maxMass * B)
    linarith

include hKernel in
/-- The tails of `A χ` from the decomposition `A χ = f + e - W_N χ - d`. -/
theorem kin_tails_of_decomp (Hunit : ℝ) (hL : 0 < L)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (χ f e d : En eta n)
    {Θ₁ Θf ε δ : ℝ} (hΘ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ‖ ≤ Θ₁)
    (hΘf : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 f‖ ≤ Θf) (he : ‖e‖ ≤ ε) (hd : ‖d‖ ≤ δ)
    (hA : FSSpectral.kin (sb eta n) (Asym sys L n) χ =
      f + e - finiteCoulombPotential sys (coulombCellAmplitude L) n χ - d)
    (a : Fin eta) (l : ℝ) (hl : 1 ≤ l) (hlK : l < Real.sqrt 3 * (gF L * n)) :
    ‖regTail L a l (FSSpectral.kin (sb eta n) (Asym sys L n) χ)‖ ≤
      (2 * sys.maxMass * Θf + (ε + δ) * Real.sqrt (1 + Real.sqrt 3 * (gF L * n)) +
        (CtW sys L Hunit (3 * sys.maxMass * Θ₁) + Real.sqrt 2 *
          finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) * Θ₁)) *
        l ^ (-(1 / 2 : ℝ)) := by
  have hg := gF_pos hL
  have hm := sys.one_le_maxMass
  have hΘ₁0 : 0 ≤ Θ₁ := le_trans (norm_nonneg _) hΘ
  have hΘf0 : 0 ≤ Θf := le_trans (norm_nonneg _) hΘf
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) he
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hd
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hχΘ : ‖χ‖ ≤ Θ₁ := (norm_le_wt sys L n zero_le_one χ).trans hΘ
  have hAχ : ‖FSSpectral.kin (sb eta n) (Asym sys L n) χ‖ ≤ Θ₁ := (norm_kin_le_wt sys χ).trans hΘ
  have hCt0 : 0 ≤ CtW sys L Hunit (3 * sys.maxMass * Θ₁) := CtW_nonneg sys hL Hunit (by positivity)
  have hl0 : 0 < l := by linarith
  have hlr : 0 ≤ l ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hl0.le _
  have hsq : 1 ≤ Real.sqrt (1 + Real.sqrt 3 * (gF L * n)) * l ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact one_le_rpow_mul_rpow_neg hl hlK.le (by norm_num)
  have hinv : 1 / l ^ 2 ≤ l ^ (-(1 / 2 : ℝ)) := by
    have : l ^ (-(2 : ℝ)) ≤ l ^ (-(1 / 2 : ℝ)) := rpow_le_of_le_one hl (by norm_num)
    rwa [Real.rpow_neg hl0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← one_div] at this
  rw [hA, map_sub, map_sub, map_add]
  have h1 : ‖regTail L a l f‖ ≤ 2 * sys.maxMass * Θf * l ^ (-(1 / 2 : ℝ)) := by
    refine (regTail_le_kin sys hL a hl0 f).trans ?_
    rw [kin_regTail]
    have hf1 : ‖regTail L a l (FSSpectral.kin (sb eta n) (Asym sys L n) f)‖ ≤ Θf :=
      (norm_regTail_le L a l _).trans ((norm_kin_le_wt sys f).trans hΘf)
    have hma := sys.mass_le_maxMass a
    calc 2 * sys.mass a / l ^ 2 * ‖regTail L a l (FSSpectral.kin (sb eta n) (Asym sys L n) f)‖
        ≤ 2 * sys.maxMass * (1 / l ^ 2) * Θf := by
          rw [div_eq_mul_one_div (2 * sys.mass a)]
          gcongr
      _ ≤ 2 * sys.maxMass * l ^ (-(1 / 2 : ℝ)) * Θf := by gcongr
      _ = _ := by ring
  have h2 : ‖regTail L a l e‖ ≤ ε * Real.sqrt (1 + Real.sqrt 3 * (gF L * n)) *
      l ^ (-(1 / 2 : ℝ)) := by
    refine (norm_regTail_le L a l e).trans (he.trans ?_)
    rw [mul_assoc]; exact le_mul_of_one_le_right hε0 hsq
  have h4 : ‖regTail L a l d‖ ≤ δ * Real.sqrt (1 + Real.sqrt 3 * (gF L * n)) *
      l ^ (-(1 / 2 : ℝ)) := by
    refine (norm_regTail_le L a l d).trans (hd.trans ?_)
    rw [mul_assoc]; exact le_mul_of_one_le_right hδ0 hsq
  have h3 : ‖regTail L a l (finiteCoulombPotential sys (coulombCellAmplitude L) n χ)‖ ≤
      (CtW sys L Hunit (3 * sys.maxMass * Θ₁) + Real.sqrt 2 *
        finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) * Θ₁) *
        l ^ (-(1 / 2 : ℝ)) := by
    have hpos : 0 ≤ Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        (1 + 2 * gF L) * Θ₁ * l ^ (-(1 / 2 : ℝ)) := by positivity
    have hpos' : 0 ≤ CtW sys L Hunit (3 * sys.maxMass * Θ₁) * l ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hCt0 hlr
    by_cases hl2 : 2 * gF L ≤ l
    · have h := regTail_WN_le sys H hKernel Hunit hL hPeriodic a hl hl2 χ
        (M₂ := 3 * sys.maxMass * Θ₁) (by
          have : ‖χ‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) χ‖ ≤ 3 * Θ₁ := by linarith
          calc sys.maxMass * (‖χ‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) χ‖)
              ≤ sys.maxMass * (3 * Θ₁) := mul_le_mul_of_nonneg_left this (by linarith)
            _ = _ := by ring)
      have h' : ‖regTail L a l (finiteCoulombPotential sys (coulombCellAmplitude L) n χ)‖ ≤
          CtW sys L Hunit (3 * sys.maxMass * Θ₁) * l ^ (-(1 / 2 : ℝ)) := h
      linarith
    · push Not at hl2
      have hWN := (potential_le_wt sys Hunit n hL hPeriodic χ).trans
        (mul_le_mul_of_nonneg_left (wt_mono sys L n (by norm_num : (1 / 2 : ℝ) ≤ 1) χ)
          (by positivity))
      have hpow2 : 1 ≤ (1 + 2 * gF L) * l ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hl0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hl0 _),
          one_mul]
        calc l ^ (1 / 2 : ℝ) ≤ l ^ (1 : ℝ) := rpow_le_of_le_one hl (by norm_num)
          _ = l := Real.rpow_one l
          _ ≤ 1 + 2 * gF L := by linarith
      have hc : ‖regTail L a l (finiteCoulombPotential sys (coulombCellAmplitude L) n χ)‖ ≤
          Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) * Θ₁ *
            l ^ (-(1 / 2 : ℝ)) := by
        calc ‖regTail L a l (finiteCoulombPotential sys (coulombCellAmplitude L) n χ)‖
            ≤ ‖finiteCoulombPotential sys (coulombCellAmplitude L) n χ‖ := norm_regTail_le L a l _
          _ ≤ Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
              ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ‖ := hWN
          _ ≤ Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * Θ₁ :=
              mul_le_mul_of_nonneg_left hΘ (by positivity)
          _ ≤ Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * Θ₁ *
              ((1 + 2 * gF L) * l ^ (-(1 / 2 : ℝ))) :=
              le_mul_of_one_le_right (by positivity) hpow2
          _ = _ := by ring
      linarith
  calc ‖regTail L a l f + regTail L a l e -
        regTail L a l (finiteCoulombPotential sys (coulombCellAmplitude L) n χ) - regTail L a l d‖
      ≤ ‖regTail L a l f‖ + ‖regTail L a l e‖ +
        ‖regTail L a l (finiteCoulombPotential sys (coulombCellAmplitude L) n χ)‖ +
        ‖regTail L a l d‖ := by
        refine (norm_sub_le _ _).trans ?_
        exact add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl
    _ ≤ _ := by linarith

include hKernel in
/-- **The static goodness criterion** (the core of `lem:good-stab`). -/
theorem good_of_decomp (Hunit : ℝ) (hL : 0 < L)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (χ f e d : En eta n)
    {Θ₁ Θf ε δ : ℝ} (hΘ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ‖ ≤ Θ₁)
    (hΘf : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 f‖ ≤ Θf) (he : ‖e‖ ≤ ε) (hd : ‖d‖ ≤ δ)
    (hA : FSSpectral.kin (sb eta n) (Asym sys L n) χ =
      f + e - finiteCoulombPotential sys (coulombCellAmplitude L) n χ - d) :
    IsGood sys L 1 (Mdec sys L Hunit n Θ₁ Θf ε δ) χ := by
  have hg := gF_pos hL
  have hm := sys.one_le_maxMass
  have hΘ₁0 : 0 ≤ Θ₁ := le_trans (norm_nonneg _) hΘ
  have hΘf0 : 0 ≤ Θf := le_trans (norm_nonneg _) hΘf
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) he
  have hδ0 : 0 ≤ δ := le_trans (norm_nonneg _) hd
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hCt0 : 0 ≤ CtW sys L Hunit (3 * sys.maxMass * Θ₁) := CtW_nonneg sys hL Hunit (by positivity)
  exact good_of_kin_tails sys hL χ hΘ (by positivity)
    (kin_tails_of_decomp sys H hKernel Hunit hL hPeriodic χ f e d hΘ hΘf he hd hA)

include hKernel in
/-- **`lem:good-stab` with the refined budget**: for `H' = H_N + ΔH` (`ΔH` symmetric,
`‖ΔH v‖ ≤ C_Δ ‖v‖`, `‖ΔH v‖ ≤ α Θ(v)`) and `χ₀ = P ψ₀ + r₀` (`ψ₀ = S u₀`, `H u₀ = S v₀`) with
`Θ(χ₀) ≤ Θ₀`, `Θ(P S v₀) ≤ Θv` and the defect `‖H_N r₀ + ΔH χ₀ - P W (1-P) u₀‖ ≤ ε₀`, every state
`e^{iH'τ} χ₀` is good with the budget `Mdec (C Θ₀) (C Θv) ε₀ (α C Θ₀)`, `C = C_fl`. -/
theorem good_stab' (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : ∀ v, ‖ΔH v‖ ≤ α * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = Sm eta L v₀) (r₀ : En eta n)
    {Θ₀ Θv ε₀ : ℝ}
    (hΘ₀ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L u₀) + r₀)‖ ≤ Θ₀)
    (hΘv : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L v₀))‖ ≤ Θv)
    (hε₀ : ‖finiteCoulombHamiltonian sys L n r₀ + ΔH (ext eta n (Sm eta L u₀) + r₀) -
      ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀))‖ ≤ ε₀)
    (τ : ℝ) :
    IsGood sys L 1 (Mdec sys L Hunit n (Cfl sys L Hunit CΔ * Θ₀) (Cfl sys L Hunit CΔ * Θv) ε₀
      (α * (Cfl sys L Hunit CΔ * Θ₀)))
      (retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀)) := by
  set χ₀ := ext eta n (Sm eta L u₀) + r₀
  set χ := retFlow sys L n hΔsym τ χ₀
  set C := Cfl sys L Hunit CΔ
  have hC := Cfl_nonneg sys Hunit hCΔ (L := L)
  have hΘχ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ‖ ≤ C * Θ₀ :=
    (theta_retFlow_le sys Hunit hL hPeriodic hΔsym hCΔ hΔb τ χ₀).trans
      (mul_le_mul_of_nonneg_left hΘ₀ hC)
  set f := retFlow sys L n hΔsym τ (ext eta n (Sm eta L v₀))
  set e₀ := finiteCoulombHamiltonian sys L n r₀ + ΔH χ₀ -
    ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀))
  set e := retFlow sys L n hΔsym τ e₀
  have hHχ₀ : Hret sys L n ΔH χ₀ = ext eta n (Sm eta L v₀) + e₀ := by
    have hext : ext eta n (H u₀) = finiteCoulombHamiltonian sys L n (ext eta n (Sm eta L u₀)) +
        ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀)) := extract_H_eq sys L H hKernel n u₀
    rw [huv] at hext
    rw [hext]
    have h1 : Hret sys L n ΔH χ₀ = finiteCoulombHamiltonian sys L n (ext eta n (Sm eta L u₀)) +
        finiteCoulombHamiltonian sys L n r₀ + ΔH χ₀ := by
      unfold Hret
      rw [LinearMap.add_apply, map_add]
    rw [h1]
    simp only [e₀]
    abel
  have hdec : Hret sys L n ΔH χ = f + e := by
    rw [Hret_retFlow, hHχ₀, retFlow_add_apply]
  have hΘf : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 f‖ ≤ C * Θv :=
    (theta_retFlow_le sys Hunit hL hPeriodic hΔsym hCΔ hΔb τ _).trans
      (mul_le_mul_of_nonneg_left hΘv hC)
  have he : ‖e‖ ≤ ε₀ := by rw [norm_retFlow]; exact hε₀
  have hd : ‖ΔH χ‖ ≤ α * (C * Θ₀) := (hα χ).trans (mul_le_mul_of_nonneg_left hΘχ hα0)
  have hAeq : FSSpectral.kin (sb eta n) (Asym sys L n) χ =
      f + e - finiteCoulombPotential sys (coulombCellAmplitude L) n χ - ΔH χ := by
    have := Hret_eq_kin_add sys L n ΔH χ
    rw [hdec] at this
    unfold Vret at this
    rw [LinearMap.add_apply] at this
    rw [this]; abel
  exact good_of_decomp sys H hKernel Hunit hL hPeriodic χ f e (ΔH χ) hΘχ hΘf he hd hAeq

end Good

end FSNormal
