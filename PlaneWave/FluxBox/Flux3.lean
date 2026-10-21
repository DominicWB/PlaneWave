import PlaneWave.FluxBox.CompositeConstants

/-!
# Flux route, stage 3, part 53: `thm:flux3`

* the rates of the box ledger along `N = n⁶` (`pl_RateBox`, `pl_EndBox`, `pl_e0`: all `PL (-3)`);
* absorbing the logarithms for every `n ≥ 1` (`PL_final_all`);
* **`thm_flux3`**: for every `ε > 0` there is `C_ε` with
  `|∫₀ᵗ [⟨ψ, Gψ⟩ - ⟨Pψ, GPψ⟩] ds| ≤ C_ε Ξ² (K^{-3+ε} + t K^{-3+ε})` for `n ≥ 64`, `g c_* n ≥ 1`
  (`K = g n`), along the exact trajectory.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory FSAsymp

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

open PLx

section Rates

variable (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) (Hunit : ℝ)

theorem pl_invNbox (c : ℝ) : PL (fun n => c / ((Nbox n : ℕ) : ℝ)) (-6) :=
  ((pl_inv_pow c 6).congr ⟨0, fun n _ => by simp [Nbox]⟩).mono (by norm_num)

include hL in
theorem pl_RateBox (heta : 0 < eta) (M : ℝ) :
    PL (fun n => RateBox sys L Hunit (Nbox n) n (ndB L n) (ndQ L n) M 1) (-3) := by
  have hg := gF_pos hL
  have hcs := cst_pos sys
  -- the rpow leaves
  have r1 : PL (fun n => (gF L * (cst sys * n)) ^ (-(3 : ℝ))) (-3) :=
    (PL.lin_rpow (by positivity : (0 : ℝ) ≤ gF L * cst sys) (-(3 : ℝ))).congr
      ⟨0, fun n _ => by rw [mul_assoc]⟩ |>.mono (by norm_num)
  have r2 : PL (fun n => (gF L * (3 * n / 64)) ^ (-(3 : ℝ))) (-3) :=
    (PL.lin_rpow (by positivity : (0 : ℝ) ≤ gF L * 3 / 64) (-(3 : ℝ))).congr
      ⟨0, fun n _ => by congr 1; ring⟩ |>.mono (by norm_num)
  have hN1 : PL (fun n => 1 / ((Nbox n : ℕ) : ℝ) + 1 / (gF L * (Nbox n : ℕ))) (-3) :=
    ((pl_invNbox 1).add ((pl_invNbox (1 / gF L)).congr ⟨0, fun n _ => by
      rw [div_div]⟩)).mono (by norm_num)
  have he := pl_eRate sys L hL Hunit
  have hCYo := pl_CYo sys L heta
  -- the terms
  have t1 : PL (fun n => 2 * (Cbd sys L * M ^ 2 * (1 / ((Nbox n : ℕ) : ℝ) + 1 / (gF L * (Nbox n : ℕ)))) +
      8 * Hrs sys L Hunit ^ 2 * M ^ 2 * (gF L * (cst sys * n)) ^ (-(3 : ℝ)) +
      6 * (Hrs sys L Hunit * CYo sys L (Nbox n) * eta * M ^ 2 * (gF L * (cst sys * n)) ^ (-(3 : ℝ))))
      (-3) := by
    refine (((hN1.const_mul (2 * Cbd sys L * M ^ 2)).add (r1.const_mul (8 * Hrs sys L Hunit ^ 2 * M ^ 2))).add
      (((hCYo.mul r1).mono (by norm_num)).const_mul (6 * Hrs sys L Hunit * eta * M ^ 2))).congr
      ⟨0, fun n _ => by ring⟩
  have t2 : PL (fun n => 2 * (eRate sys L Hunit (Nbox n) * 1) * (2 * CH sys L Hunit * M)) (-3) :=
    ((he.const_mul (2 * (2 * CH sys L Hunit * M))).congr ⟨0, fun n _ => by ring⟩).mono (by norm_num)
  have t3 : PL (fun n => 3 * CRt sys L * (cXw sys L * (eta ^ 2 * M ^ 2 *
      (gF L * (3 * n / 64)) ^ (-(3 : ℝ))))) (-3) :=
    (r2.const_mul (3 * CRt sys L * cXw sys L * eta ^ 2 * M ^ 2)).congr ⟨0, fun n _ => by ring⟩
  have t4 : PL (fun n => 2 * (eRate sys L Hunit (Nbox n) * 1) * (2 * CYo sys L (Nbox n) * M)) (-3) :=
    (((he.mul hCYo).const_mul (4 * M)).congr ⟨0, fun n _ => by ring⟩).mono (by norm_num)
  have t5 : PL (fun n => K3c sys L Hunit (Nbox n) (ndB L n) M / (n : ℝ) ^ 3) (-3) :=
    (pl_div_pow (pl_K3c sys L hL Hunit heta M) 3).mono (by norm_num)
  have t6 : PL (fun n => 2 * (eRate sys L Hunit (Nbox n) * 1) *
      (2 * Real.sqrt (BopY sys L Hunit (Nbox n) n) * M)) (-3) :=
    (((he.mul (pl_BopY sys L Hunit heta).sqrt).const_mul (4 * M)).congr
      ⟨0, fun n _ => by ring⟩).mono (by norm_num)
  have t7 : PL (fun n => CZle sys L n * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 *
      (1 + 2 * eta * (ndQ L n : ℝ)))) (-3) :=
    (((pl_CZle sys L).mul ((pl_crit (eta : ℝ) (pl_ndQ hL)).const_mul
      ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2))).congr ⟨0, fun n _ => by ring⟩).mono (by norm_num)
  have t8 : PL (fun n => 2 * (CWY sys L (Nbox n) n (ndQ L n) * M ^ 2)) (-3) :=
    ((pl_CWY sys L hL).const_mul (2 * M ^ 2)).congr ⟨0, fun n _ => by ring⟩
  have t9 : PL (fun n => 2 * (eRate sys L Hunit (Nbox n) * 1) * (RY2 sys L n * M)) (-3) :=
    (((he.mul (pl_RY2 sys L)).const_mul (2 * M)).congr ⟨0, fun n _ => by ring⟩).mono (by norm_num)
  refine ((((((((t1.add t2).add t3).add t4).add t5).add t6).add t7).add t8).add t9).congr
    ⟨0, fun n _ => ?_⟩
  unfold RateBox
  rfl

include hL in
theorem pl_EndBox (heta : 0 < eta) (M : ℝ) :
    PL (fun n => EndBox sys L Hunit (Nbox n) n M) (-3) := by
  have hg := gF_pos hL
  have r3 : PL (fun n => (gF L * n) ^ (-(3 : ℝ))) (-3) := PL.lin_rpow hg.le (-(3 : ℝ))
  have r4 : PL (fun n => (gF L * n / 4) ^ (-(4 : ℝ))) (-3) :=
    ((PL.lin_rpow (by positivity : (0 : ℝ) ≤ gF L / 4) (-(4 : ℝ))).congr
      ⟨0, fun n _ => by congr 1; ring⟩).mono (by norm_num)
  have e1 : PL (fun n => 2 * (Cend sys L Hunit * M ^ 2 * (gF L * n) ^ (-(3 : ℝ)))) (-3) :=
    (r3.const_mul (2 * Cend sys L Hunit * M ^ 2)).congr ⟨0, fun n _ => by ring⟩
  have e2 : PL (fun n => 2 * (2 * (CYb sys L * M ^ 2 * (gF L * n) ^ (-(3 : ℝ))) +
      3 * (CYt sys L (Nbox n) * (eta ^ 2 * M ^ 2 * (gF L * n / 4) ^ (-(4 : ℝ)))))) (-3) :=
    ((r3.const_mul (4 * CYb sys L * M ^ 2)).add
      ((((pl_CYt sys L heta).mul r4).mono (by norm_num)).const_mul (6 * eta ^ 2 * M ^ 2))).congr
      ⟨0, fun n _ => by ring⟩
  have e3 : PL (fun n => 2 * (K3e sys L Hunit (Nbox n) M / (n : ℝ) ^ 3)) (-3) :=
    ((pl_div_pow (pl_K3e sys L Hunit heta M) 3).const_mul 2).mono (by norm_num)
  have e4 : PL (fun n => 2 * (CY2 sys L n * M ^ 2)) (-3) :=
    ((pl_CY2 sys L).const_mul (2 * M ^ 2)).congr ⟨0, fun n _ => by ring⟩
  refine (((e1.add e2).add e3).add e4).congr ⟨0, fun n _ => ?_⟩
  unfold EndBox
  rfl

include hL in
theorem pl_e0 : PL (fun n => CB sys L Hunit * cTr sys L Hunit ^ 2 *
    (gF L * ((Nbox n : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) (-3) := by
  have h := (pl_lin_rpow' (gF_pos hL).le 6 (-(1 / 2 : ℝ))).const_mul (CB sys L Hunit * cTr sys L Hunit ^ 2)
  refine (h.congr ⟨0, fun n _ => by unfold Nbox; rfl⟩).mono (by norm_num)

end Rates

/-! ## Absorbing the logarithms -/

omit [Fintype ν] in
theorem PL_final_all {f : ℕ → ℝ} {p : ℝ} (hf : PL f p) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → |f n| ≤ C * (n : ℝ) ^ (p + ε) := by
  obtain ⟨C₀, hC₀, N₀, h⟩ := hf.final hε
  set C₁ := ∑ m ∈ Finset.range N₀, |f m| / (m : ℝ) ^ (p + ε) with hC₁d
  have hC₁ : 0 ≤ C₁ := Finset.sum_nonneg fun m _ =>
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  refine ⟨C₀ + C₁, by positivity, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : 0 < (n : ℝ) ^ (p + ε) := Real.rpow_pos_of_pos hn0 _
  by_cases hN : N₀ ≤ n
  · have h1 := h n hN
    nlinarith
  · push Not at hN
    have hmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr hN
    have hle : |f n| / (n : ℝ) ^ (p + ε) ≤ C₁ :=
      Finset.single_le_sum (f := fun m => |f m| / (m : ℝ) ^ (p + ε))
        (fun m _ => div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) _)) hmem
    rw [div_le_iff₀ hpow] at hle
    nlinarith

/-! ## `thm:flux3` -/

section Final

variable {sys : CoulombSystem eta ν} {L : ℝ}

/-- **`thm:flux3` (the flux side at the target rate)**: for every `ε > 0` there is `C_ε` such that
along the exact trajectory, for every cutoff `n ≥ 64` with `g c_* n ≥ 1` (`K = g n`) and `t ≥ 0`,
`|∫₀ᵗ [⟨ψ, Gψ⟩ - ⟨Pψ, GPψ⟩] ds| ≤ C_ε Ξ² (K^{-3+ε} + t K^{-3+ε})`. -/
theorem thm_flux3 (heta : 0 < eta) (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (p₀ : Fin eta) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 64 ≤ n → 1 ≤ gF L * (cst sys * n) → ∀ (D : EvoData L H) {t : ℝ}, 0 ≤ t →
      |∫ s in (0 : ℝ)..t, ((Gf sys L H p₀ (traj H D s) (traj H D s)).re -
          (Gf sys L H p₀ (molecularH2Truncate n (traj H D s))
            (molecularH2Truncate n (traj H D s))).re)| ≤
        C * D.Xi ^ 2 * (Kc L n ^ (-3 + ε) + t * Kc L n ^ (-3 + ε)) := by
  have hg := gF_pos hL
  have hR := (pl_e0 sys L hL Hunit).add (pl_RateBox sys L hL Hunit heta (2 * cTr sys L Hunit))
  have hE := pl_EndBox sys L hL Hunit heta (2 * cTr sys L Hunit)
  obtain ⟨C₁, hC₁, h₁⟩ := PL_final_all hR hε
  obtain ⟨C₂, hC₂, h₂⟩ := PL_final_all hE hε
  have hgp : 0 < gF L ^ (3 - ε) := Real.rpow_pos_of_pos hg _
  refine ⟨(C₁ + C₂) * gF L ^ (3 - ε), by positivity, fun n hn hl D t ht => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hb := flux_box_scaled hL H hKernel p₀ Hunit hPeriodic hn (Nbox_ge n) hl (ndB_spec hL n)
    (ndQ_spec hL n) D ht
  have hr1 := h₁ n hn1
  have hr2 := h₂ n hn1
  -- `n^{-3+ε} = g^{3-ε} K^{-3+ε}`
  have hK : (n : ℝ) ^ (-3 + ε) = gF L ^ (3 - ε) * Kc L n ^ (-3 + ε) := by
    rw [Kc_eq, Real.mul_rpow hg.le hn0.le, ← mul_assoc, ← Real.rpow_add hg]
    norm_num
  rw [hK] at hr1 hr2
  set R := CB sys L Hunit * cTr sys L Hunit ^ 2 * (gF L * ((Nbox n : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)) +
    RateBox sys L Hunit (Nbox n) n (ndB L n) (ndQ L n) (2 * cTr sys L Hunit) 1 with hRdef
  set E := EndBox sys L Hunit (Nbox n) n (2 * cTr sys L Hunit) with hEdef
  have hX := sq_nonneg D.Xi
  have hKp : 0 ≤ Kc L n ^ (-3 + ε) := by rw [Kc_eq]; exact Real.rpow_nonneg (by positivity) _
  have hR' : R ≤ C₁ * (gF L ^ (3 - ε) * Kc L n ^ (-3 + ε)) := (le_abs_self R).trans hr1
  have hE' : E ≤ C₂ * (gF L ^ (3 - ε) * Kc L n ^ (-3 + ε)) := (le_abs_self E).trans hr2
  refine hb.trans ?_
  have h1 : t * R + E ≤ t * (C₁ * (gF L ^ (3 - ε) * Kc L n ^ (-3 + ε))) +
      C₂ * (gF L ^ (3 - ε) * Kc L n ^ (-3 + ε)) := by
    have := mul_le_mul_of_nonneg_left hR' ht
    linarith
  have h2 : t * (C₁ * (gF L ^ (3 - ε) * Kc L n ^ (-3 + ε))) + C₂ * (gF L ^ (3 - ε) * Kc L n ^ (-3 + ε)) ≤
      (C₁ + C₂) * gF L ^ (3 - ε) * (Kc L n ^ (-3 + ε) + t * Kc L n ^ (-3 + ε)) := by
    have a1 : 0 ≤ C₁ * gF L ^ (3 - ε) * Kc L n ^ (-3 + ε) := by positivity
    have a2 : 0 ≤ C₂ * gF L ^ (3 - ε) * (t * Kc L n ^ (-3 + ε)) := by positivity
    nlinarith
  calc D.Xi ^ 2 * (t * R + E) ≤ D.Xi ^ 2 * ((C₁ + C₂) * gF L ^ (3 - ε) *
        (Kc L n ^ (-3 + ε) + t * Kc L n ^ (-3 + ε))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hX
    _ = (C₁ + C₂) * gF L ^ (3 - ε) * D.Xi ^ 2 * (Kc L n ^ (-3 + ε) + t * Kc L n ^ (-3 + ε)) := by ring

end Final

end FSFlux
