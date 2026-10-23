import PlaneWave.KineticLog.OpenTraj

/-!
# Logarithmic kinetic bound, part 22: the rates of the cell constants, uniform in `L`

With `K = g m`, `m ≥ 8`, `s₀ = ⌊m/4⌋` and `L ≥ 2π`:

* the generic rate lemmas `dForm_rate`, `fForm_rate` (pure real arithmetic), with the aliasing form
  constant `Z_c A_g(s₀, m) ≤ α_F z/√K` (`formAP_rate`, `α_F = 18 √8 √79`) and `Z_c m ≤ z K`;
* **`dRawU_le`**: `δ_raw ≤ δ_U/K³`; **`fRawU_le`**: `F_raw ≤ F_U/√K` (`lem:kinetic-low`,
  `lem:kinetic-strong` for the cell, constants independent of `L`);
* **`datum_res_gL`**: the grid residual of the datum, `‖C_g u₀‖ ≤ R_U Ξ/√K`;
* **`grid_traj_shells_gL`** (`lem:grid-tails`, physical units, uniform in `L`): the grid trajectory
  `v(t) = U_g(t) P' ψ₀` has `‖1_{|q_p|_∞ > T} w_g v(t)‖ ≤ b₁ Ξ/√(g T)` for `2 ≤ T ≤ m`, `g T ≥ 1`,
  from `G v(t) = U_g(t) P' H ψ₀ + U_g(t) C_g u₀` (no uniform `‖G² P' ψ₀‖` is used), the potential
  shells (`grid_pot_shell_U`) and the kinetic division.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- The constant `α_F = 18 √8 √79` of the aliasing form rate. -/
noncomputable def alphaF : ℝ := 18 * Real.sqrt 8 * Real.sqrt 79

lemma alphaF_nonneg : 0 ≤ alphaF := by unfold alphaF; positivity

/-! ## Generic rate arithmetic -/

/-- **The strong-consistency rate arithmetic.** -/
lemma fForm_rate {K Zc fa m tu xu t2 Ct e z cA cB : ℝ} (hK1 : 1 ≤ K)
    (_hZ0 : 0 ≤ Zc) (_hfa0 : 0 ≤ fa) (hZfa : Zc * fa ≤ alphaF * z / Real.sqrt K)
    (hZm : Zc * m ≤ z * K) (htu0 : 0 ≤ tu) (htu : tu ≤ 192 * cA / (K ^ 2 * Real.sqrt K))
    (hxu0 : 0 ≤ xu) (_ht20 : 0 ≤ t2) (ht2 : t2 ≤ cB / (K ^ 2 * Real.sqrt K)) (hCt : 0 ≤ Ct)
    (he : 0 ≤ e) (hz : 0 ≤ z) (hcA : 0 ≤ cA) (hcB : 0 ≤ cB) :
    Zc * (fa * (tu * (1 + 12 * e * K ^ 2) + xu) + 52 * m * tu) +
        t2 * (e * Ct * (1 + 12 * e * K ^ 2)) / Real.sqrt (2 * K) ≤
      (alphaF * z * (192 * cA * (1 + 12 * e) + xu) + 52 * 192 * z * cA +
        cB * e * Ct * (1 + 12 * e)) / Real.sqrt K := by
  have hK0 : 0 < K := by linarith
  set sK := Real.sqrt K with hsK
  have hsK0 : 0 < sK := Real.sqrt_pos.mpr hK0
  have hsK2 : sK ^ 2 = K := Real.sq_sqrt hK0.le
  have hsK1 : 1 ≤ sK := Real.one_le_sqrt.mpr hK1
  have hpoly : 1 + 12 * e * K ^ 2 ≤ (1 + 12 * e) * K ^ 2 := by
    have : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hK1
    nlinarith
  have hpoly0 : 0 ≤ 1 + 12 * e * K ^ 2 := by positivity
  have hs2K : sK ≤ Real.sqrt (2 * K) := Real.sqrt_le_sqrt (by linarith)
  have hα := alphaF_nonneg
  -- the four pieces
  have p1 : Zc * fa * (tu * (1 + 12 * e * K ^ 2)) ≤ alphaF * z / sK *
      (192 * cA / (K ^ 2 * sK) * ((1 + 12 * e) * K ^ 2)) := by
    gcongr
  have p2 : Zc * fa * xu ≤ alphaF * z / sK * xu := mul_le_mul_of_nonneg_right hZfa hxu0
  have p3 : Zc * (52 * m * tu) ≤ 52 * (z * K) * (192 * cA / (K ^ 2 * sK)) := by
    have : Zc * (52 * m * tu) = 52 * (Zc * m) * tu := by ring
    rw [this]
    gcongr
  have p4 : t2 * (e * Ct * (1 + 12 * e * K ^ 2)) / Real.sqrt (2 * K) ≤
      cB / (K ^ 2 * sK) * (e * Ct * ((1 + 12 * e) * K ^ 2)) / sK := by
    gcongr
  have e0 : Zc * (fa * (tu * (1 + 12 * e * K ^ 2) + xu) + 52 * m * tu) =
      Zc * fa * (tu * (1 + 12 * e * K ^ 2)) + Zc * fa * xu + Zc * (52 * m * tu) := by ring
  rw [e0]
  have q1 : alphaF * z / sK * (192 * cA / (K ^ 2 * sK) * ((1 + 12 * e) * K ^ 2)) ≤
      alphaF * z * 192 * cA * (1 + 12 * e) / sK := by
    have e1 : alphaF * z / sK * (192 * cA / (K ^ 2 * sK) * ((1 + 12 * e) * K ^ 2)) =
        alphaF * z * 192 * cA * (1 + 12 * e) / sK / sK := by
      field_simp
    rw [e1]
    exact div_le_self (by positivity) hsK1
  have q3 : 52 * (z * K) * (192 * cA / (K ^ 2 * sK)) ≤ 52 * 192 * z * cA / sK := by
    have e3 : 52 * (z * K) * (192 * cA / (K ^ 2 * sK)) = 52 * 192 * z * cA / sK / K := by
      field_simp
    rw [e3]
    exact div_le_self (by positivity) hK1
  have q4 : cB / (K ^ 2 * sK) * (e * Ct * ((1 + 12 * e) * K ^ 2)) / sK ≤
      cB * e * Ct * (1 + 12 * e) / sK := by
    have e4 : cB / (K ^ 2 * sK) * (e * Ct * ((1 + 12 * e) * K ^ 2)) / sK =
        cB * e * Ct * (1 + 12 * e) / sK / sK := by
      field_simp
    rw [e4]
    exact div_le_self (by positivity) hsK1
  have efin : (alphaF * z * (192 * cA * (1 + 12 * e) + xu) + 52 * 192 * z * cA +
      cB * e * Ct * (1 + 12 * e)) / sK = alphaF * z * 192 * cA * (1 + 12 * e) / sK +
        alphaF * z / sK * xu + 52 * 192 * z * cA / sK + cB * e * Ct * (1 + 12 * e) / sK := by
    ring
  rw [efin]
  linarith

/-- **The weighted-consistency rate arithmetic.** -/
lemma dForm_rate {K Zc fa m tu tv xu xv t2 wv z cA cG W : ℝ} (hK1 : 1 ≤ K)
    (_hZ0 : 0 ≤ Zc) (_hfa0 : 0 ≤ fa) (hZfa : Zc * fa ≤ alphaF * z / Real.sqrt K)
    (hZm : Zc * m ≤ z * K) (htu0 : 0 ≤ tu) (htu : tu ≤ 192 * cA / (K ^ 2 * Real.sqrt K))
    (htv0 : 0 ≤ tv) (htv : tv ≤ 192 * cG / (K ^ 2 * Real.sqrt K))
    (hxu0 : 0 ≤ xu) (hxv0 : 0 ≤ xv) (_ht20 : 0 ≤ t2) (ht2 : t2 ≤ cA / (K ^ 2 * Real.sqrt K))
    (hwv0 : 0 ≤ wv) (hwv : wv ≤ W / Real.sqrt K) (hz : 0 ≤ z) (hcA : 0 ≤ cA) (hcG : 0 ≤ cG) :
    Zc * (fa * (tu * xv + tv * xu) + 52 * m * (tv * tu)) + t2 * wv ≤
      (alphaF * z * 192 * (cA * xv + cG * xu) + 52 * 192 * 192 * z * cG * cA + cA * W) / K ^ 3 := by
  have hK0 : 0 < K := by linarith
  set sK := Real.sqrt K with hsK
  have hsK0 : 0 < sK := Real.sqrt_pos.mpr hK0
  have hsK2 : sK ^ 2 = K := Real.sq_sqrt hK0.le
  have hsK1 : 1 ≤ sK := Real.one_le_sqrt.mpr hK1
  have hα := alphaF_nonneg
  have hW0 : 0 ≤ W := by
    have := hwv0.trans hwv
    rwa [le_div_iff₀ hsK0, zero_mul] at this
  have p1 : Zc * fa * (tu * xv + tv * xu) ≤ alphaF * z / sK *
      (192 * cA / (K ^ 2 * sK) * xv + 192 * cG / (K ^ 2 * sK) * xu) := by
    gcongr
  have p3 : Zc * (52 * m * (tv * tu)) ≤ 52 * (z * K) *
      (192 * cG / (K ^ 2 * sK) * (192 * cA / (K ^ 2 * sK))) := by
    have : Zc * (52 * m * (tv * tu)) = 52 * (Zc * m) * (tv * tu) := by ring
    rw [this]
    gcongr
  have p4 : t2 * wv ≤ cA / (K ^ 2 * sK) * (W / sK) := by gcongr
  have e0 : Zc * (fa * (tu * xv + tv * xu) + 52 * m * (tv * tu)) =
      Zc * fa * (tu * xv + tv * xu) + Zc * (52 * m * (tv * tu)) := by ring
  rw [e0]
  have hK3 : (sK ^ 2) ^ 3 = K ^ 3 := by rw [hsK2]
  have q1 : alphaF * z / sK * (192 * cA / (K ^ 2 * sK) * xv + 192 * cG / (K ^ 2 * sK) * xu) =
      alphaF * z * 192 * (cA * xv + cG * xu) / K ^ 3 := by
    rw [← hsK2]
    field_simp
  have q3 : 52 * (z * K) * (192 * cG / (K ^ 2 * sK) * (192 * cA / (K ^ 2 * sK))) ≤
      52 * 192 * 192 * z * cG * cA / K ^ 3 := by
    have e3 : 52 * (z * K) * (192 * cG / (K ^ 2 * sK) * (192 * cA / (K ^ 2 * sK))) =
        52 * 192 * 192 * z * cG * cA / K ^ 3 / K := by
      rw [← hsK2]
      field_simp
    rw [e3]
    exact div_le_self (by positivity) hK1
  have q4 : cA / (K ^ 2 * sK) * (W / sK) = cA * W / K ^ 3 := by
    rw [← hsK2]
    field_simp
  have efin : (alphaF * z * 192 * (cA * xv + cG * xu) + 52 * 192 * 192 * z * cG * cA + cA * W) /
      K ^ 3 = alphaF * z * 192 * (cA * xv + cG * xu) / K ^ 3 +
        52 * 192 * 192 * z * cG * cA / K ^ 3 + cA * W / K ^ 3 := by ring
  rw [efin]
  linarith

/-! ## Scales at the quarter register -/

/-- `C/(K_s² √K_s) ≤ 192 C/(K² √K)` at `K_s = g ⌊m/4⌋`, `K = g m`, `m ≥ 8`. -/
lemma quarter_rate {g C : ℝ} (hg : 0 < g) (hC : 0 ≤ C) {m : ℕ} (hm : 8 ≤ m) :
    C / ((g * (m / 4 : ℕ)) ^ 2 * Real.sqrt (g * (m / 4 : ℕ))) ≤
      192 * C / ((g * m) ^ 2 * Real.sqrt (g * m)) := by
  obtain ⟨hKs, -⟩ := quarter_scales hg hm
  set K := g * m with hKdef
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hK0 : 0 < K := by positivity
  set Ks := g * ((m / 4 : ℕ) : ℝ) with hKsdef
  have hsq : Real.sqrt K / 3 ≤ Real.sqrt Ks :=
    (sqrt_div_three_le hK0.le).trans (Real.sqrt_le_sqrt hKs)
  have hden : (K / 8) ^ 2 * (Real.sqrt K / 3) ≤ Ks ^ 2 * Real.sqrt Ks :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) hKs 2) hsq (by positivity) (by positivity)
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  calc C / (Ks ^ 2 * Real.sqrt Ks) ≤ C / ((K / 8) ^ 2 * (Real.sqrt K / 3)) :=
        div_le_div_of_nonneg_left hC (by positivity) hden
    _ = 192 * C / (K ^ 2 * Real.sqrt K) := by
        field_simp
        ring

/-- `C/((2K)² √(2K)) ≤ C/(K² √K)`. -/
lemma double_rate {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C) :
    C / ((2 * K) ^ 2 * Real.sqrt (2 * K)) ≤ C / (K ^ 2 * Real.sqrt K) := by
  refine div_le_div_of_nonneg_left hC (by positivity) ?_
  exact mul_le_mul (pow_le_pow_left₀ hK.le (by linarith) 2)
    (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) (by positivity)

/-! ## The rates of the raw constants -/

section Rates

variable (sys : CoulombSystem eta ν) {L V Hunit : ℝ}

lemma ZcL_le (hL : 2 * Real.pi ≤ L) (hV : 0 ≤ V) :
    ZcL sys L V ≤ PlaneWaveGridG.gLzU sys V * (2 * Real.pi / L) := by
  have hL0 := pos_of_two_pi_le hL
  have h := PlaneWaveGridG.gLGridCoupling_eq sys hL0 V
  have hZ : 0 ≤ ZcL sys L V := ZcL_nonneg hL0 hV
  have hM := sys.one_le_maxMass
  have e : PlaneWaveGridG.gLGridCoupling sys L V = sys.maxMass * ZcL sys L V := rfl
  rw [e] at h
  nlinarith

lemma ZcL_formAP_le (hL : 2 * Real.pi ≤ L) (hV : 0 ≤ V) {m : ℕ} (hm : 8 ≤ m) :
    ZcL sys L V * PlaneWaveGridG.formAP (2 * Real.pi / L) (m / 4) m ≤
      alphaF * PlaneWaveGridG.gLzU sys V / Real.sqrt (2 * Real.pi / L * m) := by
  have hL0 := pos_of_two_pi_le hL
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hg1 : 2 * Real.pi / L ≤ 1 := PlaneWaveGridG.g_le_one hL
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hK0 : 0 < 2 * Real.pi / L * m := by positivity
  set ρ := 1 / Real.sqrt (2 * Real.pi / L * m) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρK : ρ ^ 2 * (2 * Real.pi / L * (m : ℝ)) = 1 := by
    rw [hρ, div_pow, Real.sq_sqrt hK0.le]
    field_simp
  have h := FreeBoundary.formAP_rate hg hg1 hρ0 hm hρK (ZcL_nonneg hL0 hV) (ZcL_le sys hL hV)
  refine h.trans (le_of_eq ?_)
  rw [hρ]
  unfold alphaF
  ring

lemma ZcL_mul_le (hL : 2 * Real.pi ≤ L) (hV : 0 ≤ V) (m : ℕ) :
    ZcL sys L V * m ≤ PlaneWaveGridG.gLzU sys V * (2 * Real.pi / L * m) := by
  have h := ZcL_le sys hL hV
  have := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg m)
  linarith

/-- **The weighted-consistency rate constant** `δ_U` (`δ_raw ≤ δ_U/K³`), independent of `L`. -/
noncomputable def dU (sys : CoulombSystem eta ν) (V Hunit c : ℝ) : ℝ :=
  alphaF * PlaneWaveGridG.gLzU sys V * 192 *
      (cAbsU sys V Hunit * xvU sys V c + cGtU sys V c * xuU sys V Hunit) +
    52 * 192 * 192 * PlaneWaveGridG.gLzU sys V * cGtU sys V c * cAbsU sys V Hunit +
    cAbsU sys V Hunit * (eta * FreeBoundary.gLtailMU sys V Hunit 1 * xvU sys V c)

/-- **The strong-consistency rate constant** `F_U` (`F_raw ≤ F_U/√K`), independent of `L`. -/
noncomputable def fU (sys : CoulombSystem eta ν) (V Hunit : ℝ) : ℝ :=
  alphaF * PlaneWaveGridG.gLzU sys V * (192 * cAbsU sys V Hunit * (1 + 12 * eta) +
      xuU sys V Hunit) + 52 * 192 * PlaneWaveGridG.gLzU sys V * cAbsU sys V Hunit +
    cAbsU sys V Hunit * eta * FreeBoundary.gLtailMU sys V Hunit 1 * (1 + 12 * eta)

lemma dU_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ dU sys V Hunit c := by
  unfold dU
  have := alphaF_nonneg
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  have := cAbsU_nonneg (sys := sys) hV hH
  have := xvU_nonneg (sys := sys) hV hc
  have := xuU_nonneg (sys := sys) hV hH
  have := cGtU_nonneg sys hV hc
  have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
  positivity

lemma fU_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ fU sys V Hunit := by
  unfold fU
  have := alphaF_nonneg
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  have := cAbsU_nonneg (sys := sys) hV hH
  have := xuU_nonneg (sys := sys) hV hH
  have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
  positivity

/-- **`δ_raw ≤ δ_U/K³`** (uniform in `L ≥ 2π`). -/
theorem dRawU_le (hL : 2 * Real.pi ≤ L) (hV : 0 ≤ V) (hH : 0 ≤ Hunit) {c : ℝ} (hc : 0 ≤ c)
    {m : ℕ} (hm : 8 ≤ m) (hK1 : 1 ≤ gF L * m) :
    dRawU sys L V Hunit c m ≤ dU sys V Hunit c / (gF L * m) ^ 3 := by
  have hL0 := pos_of_two_pi_le hL
  have hg := gF_pos hL0
  have hK0 : 0 < gF L * m := by linarith
  have hgg : gF L = 2 * Real.pi / L := rfl
  have htu : tuU sys L V Hunit m ≤ 192 * cAbsU sys V Hunit / ((gF L * m) ^ 2 *
      Real.sqrt (gF L * m)) := quarter_rate hg (cAbsU_nonneg hV hH) hm
  have htv : tvU sys L V c m ≤ 192 * cGtU sys V c / ((gF L * m) ^ 2 * Real.sqrt (gF L * m)) := by
    unfold tvU
    have hs := quarter_rate hg (cGtU_nonneg sys hV hc) hm
    refine le_trans ?_ hs
    rw [← hgg]
    apply div_le_div_of_nonneg_left (cGtU_nonneg sys hV hc) (by
      have := (quarter_bounds hm).2.2
      positivity)
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  have ht2 : t2U sys L V Hunit m ≤ cAbsU sys V Hunit / ((gF L * m) ^ 2 * Real.sqrt (gF L * m)) := by
    unfold t2U
    have e : gF L * ((2 * m : ℕ) : ℝ) = 2 * (gF L * m) := by push_cast; ring
    rw [e]
    exact double_rate hK0 (cAbsU_nonneg hV hH)
  have hwv : wvU sys L V Hunit c m ≤
      eta * FreeBoundary.gLtailMU sys V Hunit 1 * xvU sys V c / Real.sqrt (gF L * m) := by
    unfold wvU
    have e : gF L * ((2 * m : ℕ) : ℝ) = 2 * (gF L * m) := by push_cast; ring
    rw [e]
    have h0 : 0 ≤ eta * FreeBoundary.gLtailMU sys V Hunit 1 * xvU sys V c := by
      have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
      have := xvU_nonneg (sys := sys) hV hc
      positivity
    exact div_le_div_of_nonneg_left h0 (Real.sqrt_pos.mpr hK0) (Real.sqrt_le_sqrt (by linarith))
  unfold dRawU
  have hZfa := ZcL_formAP_le sys hL hV hm
  rw [← hgg] at hZfa
  have hZm := ZcL_mul_le sys hL hV m
  rw [← hgg] at hZm
  exact dForm_rate hK1 (ZcL_nonneg hL0 hV) (PlaneWaveGridG.formAP_nonneg _ _ _) hZfa hZm
    (tuU_nonneg hL0 hV hH m) htu (tvU_nonneg hL0 hV hc m) htv (xuU_nonneg hV hH)
    (xvU_nonneg hV hc) (t2U_nonneg hL0 hV hH m) ht2 (wvU_nonneg hV hH hc m) hwv
    (PlaneWaveGridG.gLzU_nonneg sys hV) (cAbsU_nonneg hV hH) (cGtU_nonneg sys hV hc)

/-- **`F_raw ≤ F_U/√K`** (uniform in `L ≥ 2π`). -/
theorem fRawU_le (hL : 2 * Real.pi ≤ L) (hV : 0 ≤ V) (hH : 0 ≤ Hunit) {m : ℕ} (hm : 8 ≤ m)
    (hK1 : 1 ≤ gF L * m) :
    fRawU sys L V Hunit m ≤ fU sys V Hunit / Real.sqrt (gF L * m) := by
  have hL0 := pos_of_two_pi_le hL
  have hg := gF_pos hL0
  have hK0 : 0 < gF L * m := by linarith
  have hgg : gF L = 2 * Real.pi / L := rfl
  have htu : tuU sys L V Hunit m ≤ 192 * cAbsU sys V Hunit / ((gF L * m) ^ 2 *
      Real.sqrt (gF L * m)) := quarter_rate hg (cAbsU_nonneg hV hH) hm
  have ht2 : t2U sys L V Hunit m ≤ cAbsU sys V Hunit / ((gF L * m) ^ 2 * Real.sqrt (gF L * m)) := by
    unfold t2U
    have e : gF L * ((2 * m : ℕ) : ℝ) = 2 * (gF L * m) := by push_cast; ring
    rw [e]
    exact double_rate hK0 (cAbsU_nonneg hV hH)
  unfold fRawU
  have e : gF L * ((2 * m : ℕ) : ℝ) = 2 * (gF L * m) := by push_cast; ring
  rw [e, ← hgg]
  have hZfa := ZcL_formAP_le sys hL hV hm
  rw [← hgg] at hZfa
  have hZm := ZcL_mul_le sys hL hV m
  rw [← hgg] at hZm
  have h := fForm_rate hK1 (ZcL_nonneg (sys := sys) hL0 hV) (PlaneWaveGridG.formAP_nonneg _ _ _)
    hZfa hZm (tuU_nonneg (sys := sys) hL0 hV hH m) htu (xuU_nonneg (sys := sys) hV hH)
    (t2U_nonneg (sys := sys) hL0 hV hH m) ht2 (gLtailMU_nonneg (sys := sys) hV hH zero_le_one)
    (Nat.cast_nonneg eta) (PlaneWaveGridG.gLzU_nonneg sys hV) (cAbsU_nonneg (sys := sys) hV hH)
    (cAbsU_nonneg (sys := sys) hV hH)
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
  · ring
  · unfold fU
    ring

end Rates

/-! ## The potential shells of the grid, physical units -/

section PotShell

variable (sys : CoulombSystem eta ν) {L V : ℝ} (hL : 2 * Real.pi ≤ L) (hV : 0 ≤ V) {m : ℕ}
  {κ : Lat3 → ℝ} (hκb : ∀ x, |κ x| ≤ PlaneWaveGridG.gLgamma L V * coul x)

include hL hV hκb in
/-- **The physical shells of the collocated `g_L` potential**: for `2 ≤ T ≤ 2m` and `g T ≥ 1`,
`‖1_{High T r} V_g v‖ ≤ z (52 + √6162)/√(g T) ‖w_g v‖`. -/
lemma grid_pot_shell_U (T : ℕ) (hT : 2 ≤ T) (hTm : T ≤ 2 * m) (r : Fin eta)
    (hgT : 1 ≤ 2 * Real.pi / L * T) (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖maskOp (High T r) (kOp (vGridK eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        κ) v)‖ ≤
      PlaneWaveGridG.gLzU sys V * (52 + Real.sqrt 6162) / Real.sqrt (2 * Real.pi / L * T) *
        ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (2 * Real.pi / L)) v‖ := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  set g := 2 * Real.pi / L with hgdef
  have hg : 0 < g := by positivity
  have hg1 : g ≤ 1 := PlaneWaveGridG.g_le_one hL
  set P := regParticlesOf sys with hPdef
  have hMeq : P.maxMass = sys.maxMass := rfl
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hgT0 : 0 < g * T := by positivity
  have hsT : 0 < Real.sqrt (g * T) := Real.sqrt_pos.mpr hgT0
  set z := PlaneWaveGridG.gLzU sys V with hz
  have hz0 : 0 ≤ z := PlaneWaveGridG.gLzU_nonneg sys hV
  set Zc' := ZcL sys L V with hZc'
  have hZz : sys.maxMass * Zc' = z * g := PlaneWaveGridG.gLGridCoupling_eq sys hL0 V
  have hJ1 : 1 ≤ T / 2 := by omega
  have hJT : T / 2 ≤ T := Nat.div_le_self T 2
  have h0 := PlaneWaveGridG.vGridK_tailP (P := PlaneWaveGridG.regParticlesOfG sys)
    (D := (PlaneWaveGridG.posNucleiOfG sys.nuclei).toNucData) hg
    (PlaneWaveGridG.gLgamma_pos hL0 hV).le hκb (T / 2) T hJ1 hJT hTm r v
  have h : ‖maskOp (High T r) (kOp (vGridK eta m P (posNucleiOf sys.nuclei).toNucData κ) v)‖ ≤
      Zc' * (26 * ((T / 2 : ℕ) : ℝ)) * ‖maskOp (High (T - T / 2) r) v‖ +
        Zc' * Real.sqrt (26 * PlaneWaveGridG.sobP g / ((T / 2 : ℕ) : ℝ)) *
          ‖wMul (FreeBoundary.wTotPh g) v‖ := h0
  have hsh := FreeBoundary.sq_mul_norm_high_le_phys P hg (T - T / 2) r v
  have hW := FreeBoundary.norm_wTotPh_le P g v
  obtain ⟨ha1, ha2⟩ := shell_arith_U T hT hg hg1
  have hX : 0 < g * (((T - T / 2 : ℕ) : ℝ) + 1) := by positivity
  set Wv := ‖wMul (FreeBoundary.wPhys P g) v‖ with hWv
  have hWv0 : 0 ≤ Wv := norm_nonneg _
  have hZc0 : 0 ≤ Zc' := ZcL_nonneg hL0 hV
  have hs1 : Zc' * (26 * ((T / 2 : ℕ) : ℝ)) * ‖maskOp (High (T - T / 2) r) v‖ ≤
      52 * z / Real.sqrt (g * T) * Wv := by
    have hm1 : ‖maskOp (High (T - T / 2) r) v‖ ≤
        P.maxMass * Wv / (g * (((T - T / 2 : ℕ) : ℝ) + 1)) ^ 2 := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact hsh
    have hT1 : 52 / (T : ℝ) ≤ 52 * g / Real.sqrt (g * T) := by
      rw [div_le_div_iff₀ (by linarith) hsT]
      have hsq : Real.sqrt (g * T) ≤ g * T := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith
      nlinarith
    calc Zc' * (26 * ((T / 2 : ℕ) : ℝ)) * ‖maskOp (High (T - T / 2) r) v‖
        ≤ Zc' * (26 * ((T / 2 : ℕ) : ℝ)) *
            (P.maxMass * Wv / (g * (((T - T / 2 : ℕ) : ℝ) + 1)) ^ 2) := by gcongr
      _ = (sys.maxMass * Zc') * (26 * ((T / 2 : ℕ) : ℝ) /
            (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2) / g ^ 2 * Wv := by
          rw [hMeq]
          field_simp
      _ ≤ (z * g) * (52 / T) / g ^ 2 * Wv := by
          rw [hZz]
          gcongr
      _ ≤ (z * g) * (52 * g / Real.sqrt (g * T)) / g ^ 2 * Wv := by gcongr
      _ = 52 * z / Real.sqrt (g * T) * Wv := by
          field_simp
  have hs2 : Zc' * Real.sqrt (26 * PlaneWaveGridG.sobP g / ((T / 2 : ℕ) : ℝ)) *
      ‖wMul (FreeBoundary.wTotPh g) v‖ ≤ z * Real.sqrt 6162 / Real.sqrt (g * T) * Wv := by
    calc Zc' * Real.sqrt (26 * PlaneWaveGridG.sobP g / ((T / 2 : ℕ) : ℝ)) *
          ‖wMul (FreeBoundary.wTotPh g) v‖
        ≤ Zc' * (Real.sqrt 6162 / (g * Real.sqrt (g * T))) * (P.maxMass * Wv) := by gcongr
      _ = (sys.maxMass * Zc') * Real.sqrt 6162 / (g * Real.sqrt (g * T)) * Wv := by
          rw [hMeq]
          ring
      _ = z * Real.sqrt 6162 / Real.sqrt (g * T) * Wv := by
          rw [hZz]
          field_simp
  refine h.trans ?_
  have e : z * (52 + Real.sqrt 6162) / Real.sqrt (g * T) * Wv =
      52 * z / Real.sqrt (g * T) * Wv + z * Real.sqrt 6162 / Real.sqrt (g * T) * Wv := by ring
  rw [e]
  exact add_le_add hs1 hs2

end PotShell

/-! ## The grid residual of the datum and the shells of the grid trajectory -/

section GridShells

variable (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (FreeBoundary.gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 2 * Real.pi ≤ L) (hθ : FreeBoundary.Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hH : 0 ≤ Hunit)

include hKernel hL hθ hPeriodic hH in
/-- `‖u₀‖ ≤ m̄ b_e Ξ` for the `H²` datum of `H_L`. -/
lemma norm_u0_le_gL (D : EvoData L H) :
    ‖D.u₀‖ ≤ sys.maxMass * (b0eU sys (FreeBoundary.tv R θ) Hunit * D.Xi) := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  obtain ⟨hX1, hX2, -, -⟩ := Xi_parts D
  have hC : 0 ≤ FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit :=
    gLmassConst_nonneg' sys (L := L) Hunit hθ
  have hb0 := FreeBoundary.relBU_nonneg sys hV hH
  have h2 := h2norm_le sys L D.u₀
  have hT := FreeBoundary.kinetic_le_elliptic_gL sys L H hKernel Hunit hL0 hθ hPeriodic hC D.u₀
  rw [FreeBoundary.relB_gL_eq_U sys hL _ hH] at hT
  change ‖coulombFourierKineticH2 sys (gF L) D.u₀‖ ≤
    2 * ‖H D.u₀‖ + 2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * ‖Sm eta L D.u₀‖ at hT
  change ‖D.u₀‖ ≤ sys.maxMass * (‖Sm eta L D.u₀‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) D.u₀‖)
    at h2
  refine h2.trans (mul_le_mul_of_nonneg_left ?_ sys.maxMass_pos.le)
  unfold b0eU
  have : 2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * ‖Sm eta L D.u₀‖ ≤
      2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * D.Xi :=
    mul_le_mul_of_nonneg_left hX1 (by positivity)
  linarith

/-- The datum residual constant
`R_U = α_F z (192 cA (1 + 12 η) + m̄ b_e) + 52·192 z cA + η cA η C_t (1 + 12 η)`,
`cA = 2 m̄ c_tr^U`. -/
noncomputable def resU (sys : CoulombSystem eta ν) (V Hunit : ℝ) : ℝ :=
  alphaF * PlaneWaveGridG.gLzU sys V * (192 * (2 * sys.maxMass * cTrU sys V Hunit) *
      (1 + 12 * eta) + sys.maxMass * b0eU sys V Hunit) +
    52 * 192 * PlaneWaveGridG.gLzU sys V * (2 * sys.maxMass * cTrU sys V Hunit) +
    eta * (2 * sys.maxMass * cTrU sys V Hunit) * eta * FreeBoundary.gLtailMU sys V Hunit 1 *
      (1 + 12 * eta)

lemma resU_nonneg {V Hunit : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ resU sys V Hunit := by
  unfold resU
  have := alphaF_nonneg
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  have := cTrU_nonneg sys hV hH
  have := b0eU_nonneg sys hV hH
  have := gLtailMU_nonneg (sys := sys) hV hH zero_le_one
  have := sys.maxMass_pos
  positivity

set_option maxHeartbeats 400000 in
include hKernel hL hθ hPeriodic hH in
/-- **The grid residual of the datum** (uniform in `L ≥ 2π`): `‖C_g u₀‖ ≤ R_U Ξ/√K` for
`m ≥ 8`, `K = g m ≥ 8`, uniformly over the kernel class. -/
theorem datum_res_gL (D : EvoData L H) (m : ℕ) (hm : 8 ≤ m) (hK8 : 8 ≤ gF L * m) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ))
      (PlaneWaveGridG.gLref L θ (FreeBoundary.tv R θ)) m κ) :
    ‖gResGL sys L H (pos_of_two_pi_le hL) hθ m κ D.u₀‖ ≤
      resU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt (gF L * m) := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  have hg := gF_pos hL0
  have hgg : gF L = 2 * Real.pi / L := rfl
  have hΞ := D.Xi_nonneg
  have hK1 : 1 ≤ gF L * m := by linarith
  have hK0 : 0 < gF L * m := by linarith
  obtain ⟨hKs, -⟩ := quarter_scales hg hm
  have hKs1 : 1 ≤ gF L * ((m / 4 : ℕ) : ℝ) := by linarith
  have h2m : gF L * ((2 * m : ℕ) : ℝ) = 2 * (gF L * m) := by push_cast; ring
  have hK21 : 1 ≤ gF L * ((2 * m : ℕ) : ℝ) := by rw [h2m]; linarith
  obtain ⟨w, hw1, -, hw3⟩ := traj_tails_gL sys H hKernel Hunit hL hθ hPeriodic hH D 0
  rw [D.U0] at hw1
  have hcT0 : 0 ≤ cTrU sys (FreeBoundary.tv R θ) Hunit := cTrU_nonneg sys hV hH
  have hM := sys.maxMass_pos
  set cA := 2 * sys.maxMass * (cTrU sys (FreeBoundary.tv R θ) Hunit * D.Xi) with hcA
  have hcA0 : 0 ≤ cA := by positivity
  -- the shells of the datum at `s₀`
  set τd := cA / ((gF L * ((m / 4 : ℕ) : ℝ)) ^ 2 * Real.sqrt (gF L * ((m / 4 : ℕ) : ℝ))) with hτd
  have hτd0 : 0 ≤ τd := by positivity
  have hτ : ∀ r, ‖maskOp (High (m / 4) r) (regCoeff m (Sm eta L D.u₀))‖ ≤ τd := by
    intro r
    refine (norm_high_regCoeff_le hg (m / 4) r _).trans ?_
    rw [← hw1]
    exact (hw3 r _ hKs1).2
  -- the weight of the datum
  set Xd := sys.maxMass * (b0eU sys (FreeBoundary.tv R θ) Hunit * D.Xi) with hXd
  have hX : ‖wMul (FreeBoundary.wTotPh (2 * Real.pi / L)) (regCoeff m (Sm eta L D.u₀))‖ ≤ Xd :=
    (FreeBoundary.norm_wTotPh_regCoeff_stateMap_le _ D.u₀).trans
      (norm_u0_le_gL sys H hKernel Hunit hL hθ hPeriodic hH D)
  -- the exterior tail of the datum
  set τ₂ := eta * (cA / ((gF L * ((2 * m : ℕ) : ℝ)) ^ 2 *
    Real.sqrt (gF L * ((2 * m : ℕ) : ℝ)))) with hτ₂
  have hτ2 : ‖Sm eta L D.u₀ - molecularH2Truncate (2 * m) (Sm eta L D.u₀)‖ ≤ τ₂ := by
    refine (PlaneWaveDynamics.norm_sub_truncate_le hg (2 * m) _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * ((2 * m : ℕ) : ℝ)) a (Sm eta L D.u₀)‖
        ≤ ∑ _a : Fin eta, cA / ((gF L * ((2 * m : ℕ) : ℝ)) ^ 2 *
            Real.sqrt (gF L * ((2 * m : ℕ) : ℝ))) := Finset.sum_le_sum fun a _ => by
          rw [← hw1]
          exact (hw3 a _ hK21).2
      _ = τ₂ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hres := norm_gRes_gL sys H hKernel Hunit hL hθ hPeriodic hH m hm hκ hK21 D.u₀ hτd0 hτ hX hτ2
  refine hres.trans ?_
  -- the rate arithmetic
  have htu : τd ≤ 192 * cA / ((gF L * m) ^ 2 * Real.sqrt (gF L * m)) :=
    quarter_rate hg hcA0 hm
  have ht2 : τ₂ ≤ eta * cA / ((gF L * m) ^ 2 * Real.sqrt (gF L * m)) := by
    rw [hτ₂, h2m]
    have hd := double_rate hK0 hcA0
    calc (eta : ℝ) * (cA / ((2 * (gF L * m)) ^ 2 * Real.sqrt (2 * (gF L * m))))
        ≤ eta * (cA / ((gF L * m) ^ 2 * Real.sqrt (gF L * m))) :=
          mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
      _ = _ := by ring
  have hZfa := ZcL_formAP_le sys hL hV hm
  rw [← hgg] at hZfa
  have hZm := ZcL_mul_le sys hL hV m
  rw [← hgg] at hZm
  have hf := fForm_rate hK1 (ZcL_nonneg (sys := sys) hL0 hV)
    (PlaneWaveGridG.formAP_nonneg (2 * Real.pi / L) (m / 4) m) hZfa hZm hτd0 htu
    (mul_nonneg hM.le (mul_nonneg (b0eU_nonneg sys hV hH) hΞ)) (by positivity : 0 ≤ τ₂) ht2
    (gLtailMU_nonneg (sys := sys) hV hH zero_le_one) (Nat.cast_nonneg eta)
    (PlaneWaveGridG.gLzU_nonneg sys hV) hcA0 (by positivity : 0 ≤ (eta : ℝ) * cA)
  rw [h2m, ← hgg]
  refine le_trans (le_of_eq ?_) (hf.trans (le_of_eq ?_))
  · rw [hgg]
  · unfold resU
    ring

/-- The shell constant of grid trajectories,
`b₁ = (2 m̄ + 2)(m̄ b_g + R_U + z (52 + √6162) b_g)`. -/
noncomputable def b1gU (sys : CoulombSystem eta ν) (V Hunit : ℝ) : ℝ :=
  (2 * sys.maxMass + 2) * (sys.maxMass * b0gU sys V Hunit + resU sys V Hunit +
    PlaneWaveGridG.gLzU sys V * (52 + Real.sqrt 6162) * b0gU sys V Hunit)

lemma b1gU_nonneg {V Hunit : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ b1gU sys V Hunit := by
  unfold b1gU
  have := b0gU_nonneg sys hV hH
  have := resU_nonneg sys hV hH
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  have := sys.maxMass_pos
  positivity

set_option maxHeartbeats 600000 in
include hKernel hL hθ hPeriodic hH in
/-- **The shells of the grid trajectory, uniform in `L ≥ 2π`** (`lem:grid-tails` in physical
units): for `m ≥ 8`, `K ≥ 8`, `2 ≤ T ≤ m` with `g T ≥ 1`, every time and every kernel of the class,
`‖1_{|q_p|_∞ > T} w_g U_g(t) P' ψ₀‖ ≤ b₁ Ξ/√(g T)`. -/
theorem grid_traj_shells_gL (D : EvoData L H) (m : ℕ) (hm : 8 ≤ m) (hK8 : 8 ≤ gF L * m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ))
      (PlaneWaveGridG.gLref L θ (FreeBoundary.tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (t : ℝ) (p : Fin eta) (T : ℕ) (hT2 : 2 ≤ T) (hTm : T ≤ m) (hgT : 1 ≤ gF L * T) :
    ‖maskOp (High T p) (wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
        (Ug t (regCoeff m (Sm eta L D.u₀))))‖ ≤
      b1gU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt (gF L * T) := by
  classical
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  have hg := gF_pos hL0
  have hgg : gF L = 2 * Real.pi / L := rfl
  have hΞ := D.Xi_nonneg
  have hM := sys.maxMass_pos
  have hκb : ∀ x, |κ x| ≤ PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ) * coul x :=
    fun x => hκ.bound x
  set P := regParticlesOf sys with hPdef
  have hMeq : P.maxMass = sys.maxMass := rfl
  set G := Hgrid eta m P (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) with hGdef
  set x₀ := regCoeff m (Sm eta L D.u₀) with hx₀
  set v := Ug t x₀ with hv
  set x₁ := regCoeff m (Sm eta L D.v₀) with hx₁
  have hgT0 : 0 < gF L * T := by linarith
  have hsT : 0 < Real.sqrt (gF L * T) := Real.sqrt_pos.mpr hgT0
  have hsT1 : 1 ≤ Real.sqrt (gF L * T) := Real.one_le_sqrt.mpr hgT
  have hTr : (T : ℝ) ≤ m := by exact_mod_cast hTm
  have hTK : gF L * T ≤ gF L * m := mul_le_mul_of_nonneg_left hTr hg.le
  obtain ⟨hX1, hX2, hX3, hX4⟩ := Xi_parts D
  -- `G x₀ = P' H u₀ + C_g u₀`, and `P' H u₀ = x₁`
  have hcons := regCoeff_H_eq_gRes_gL sys L H hL0 hθ hKernel m κ D.u₀
  have hHu : regCoeff m (H D.u₀) = x₁ := by rw [D.uv]
  have hGx : G x₀ = x₁ + gResGL sys L H hL0 hθ m κ D.u₀ := by
    rw [← hHu, hcons]
    change G x₀ = G (regCoeff m (molecularH2StateMap eta (2 * Real.pi / L) D.u₀)) - _ + _
    abel
  -- the kinetic part of `v`
  have hkin : wMul (kinT eta m P (2 * Real.pi / L)) v = Ug t (G x₀) -
      kOp (vGridK eta m P (posNucleiOf sys.nuclei).toNucData κ) v := by
    rw [hgcomm t x₀]
    simp only [hGdef, Hgrid, LinearMap.add_apply]
    abel
  -- (a) the flow of `x₁`
  have hb0g := b0gU_nonneg sys hV hH
  have hw1 : ‖wMul (FreeBoundary.wPhys P (gF L)) (Ug t x₁)‖ ≤
      b0gU sys (FreeBoundary.tv R θ) Hunit * D.Xi := by
    have h := FreeBoundary.norm_wPhys_gridFlow_le_gL sys hL hV hκb (Ug t) (hgcomm t) x₁
    refine h.trans ?_
    have hwv0 : ‖wMul (FreeBoundary.wPhys P (2 * Real.pi / L)) x₁‖ ≤
        sys.maxMass * (b0eU sys (FreeBoundary.tv R θ) Hunit * D.Xi) := by
      refine (FreeBoundary.norm_wPhys_regCoeff_stateMap_le P _ D.v₀).trans ?_
      have hC : 0 ≤ FreeBoundary.gLmassConst sys L (FreeBoundary.tv R θ) Hunit :=
        gLmassConst_nonneg' sys (L := L) Hunit hθ
      have hb0 := FreeBoundary.relBU_nonneg sys hV hH
      have h2 := h2norm_le sys L D.v₀
      have hT := FreeBoundary.kinetic_le_elliptic_gL sys L H hKernel Hunit hL0 hθ hPeriodic hC D.v₀
      rw [FreeBoundary.relB_gL_eq_U sys hL _ hH] at hT
      change ‖coulombFourierKineticH2 sys (gF L) D.v₀‖ ≤ 2 * ‖H D.v₀‖ +
        2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * ‖Sm eta L D.v₀‖ at hT
      change ‖D.v₀‖ ≤ sys.maxMass * (‖Sm eta L D.v₀‖ +
        2 * ‖coulombFourierKineticH2 sys (gF L) D.v₀‖) at h2
      refine h2.trans (mul_le_mul_of_nonneg_left ?_ hM.le)
      unfold b0eU
      have : 2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * ‖Sm eta L D.v₀‖ ≤
          2 * FreeBoundary.relBU sys (FreeBoundary.tv R θ) Hunit * D.Xi :=
        mul_le_mul_of_nonneg_left hX4 (by positivity)
      linarith
    have hx1 : ‖x₁‖ ≤ D.Xi := (norm_regCoeff_le _).trans hX4
    have hJ := FreeBoundary.gridFlowConstU_nonneg sys hV
    unfold b0gU
    have e1 := mul_le_mul_of_nonneg_left hwv0 (by norm_num : (0 : ℝ) ≤ 5 / 3)
    have e2 := mul_le_mul_of_nonneg_left hx1 hJ
    linarith
  have ha : ‖maskOp (High T p) (Ug t x₁)‖ ≤
      sys.maxMass * b0gU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt (gF L * T) := by
    have h := FreeBoundary.sq_mul_norm_high_le_phys P hg T p (Ug t x₁)
    have hTT : 1 ≤ (gF L * ((T : ℝ) + 1)) ^ 2 := one_le_pow₀ (by nlinarith)
    have hTT' : Real.sqrt (gF L * T) ≤ (gF L * ((T : ℝ) + 1)) ^ 2 := by
      have h1 : Real.sqrt (gF L * T) ≤ gF L * T := by
        rw [Real.sqrt_le_left hgT0.le]
        exact le_self_pow₀ hgT two_ne_zero
      have h2 : gF L * T ≤ gF L * ((T : ℝ) + 1) := by nlinarith
      have h3 : gF L * ((T : ℝ) + 1) ≤ (gF L * ((T : ℝ) + 1)) ^ 2 :=
        le_self_pow₀ (by nlinarith) two_ne_zero
      linarith
    have hpos : 0 < (gF L * ((T : ℝ) + 1)) ^ 2 := by linarith
    rw [le_div_iff₀ hsT]
    calc ‖maskOp (High T p) (Ug t x₁)‖ * Real.sqrt (gF L * T)
        ≤ ‖maskOp (High T p) (Ug t x₁)‖ * (gF L * ((T : ℝ) + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left hTT' (norm_nonneg _)
      _ ≤ P.maxMass * ‖wMul (FreeBoundary.wPhys P (gF L)) (Ug t x₁)‖ := by
          rw [mul_comm]
          exact h
      _ ≤ sys.maxMass * (b0gU sys (FreeBoundary.tv R θ) Hunit * D.Xi) :=
          mul_le_mul_of_nonneg_left hw1 hM.le
      _ = _ := by ring
  -- (b) the residual of the datum
  have hb : ‖maskOp (High T p) (Ug t (gResGL sys L H hL0 hθ m κ D.u₀))‖ ≤
      resU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt (gF L * T) := by
    refine (norm_maskOp_le _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
    refine (datum_res_gL sys H hKernel Hunit hL hθ hPeriodic hH D m hm hK8 hκ).trans ?_
    have hr0 : 0 ≤ resU sys (FreeBoundary.tv R θ) Hunit * D.Xi := by
      have := resU_nonneg sys hV hH
      positivity
    exact div_le_div_of_nonneg_left hr0 hsT (Real.sqrt_le_sqrt hTK)
  -- (c) the potential shells
  have hvw := grid_traj_weight_gL sys H hKernel Hunit hL hθ hPeriodic hH D m hκb Ug hgcomm t
  have hc : ‖maskOp (High T p) (kOp (vGridK eta m P (posNucleiOf sys.nuclei).toNucData κ) v)‖ ≤
      PlaneWaveGridG.gLzU sys (FreeBoundary.tv R θ) * (52 + Real.sqrt 6162) *
        b0gU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt (gF L * T) := by
    have h := grid_pot_shell_U sys hL hV hκb T hT2 (by omega) p hgT v
    refine h.trans ?_
    have hz := PlaneWaveGridG.gLzU_nonneg sys hV
    have h0 : 0 ≤ PlaneWaveGridG.gLzU sys (FreeBoundary.tv R θ) * (52 + Real.sqrt 6162) /
        Real.sqrt (2 * Real.pi / L * T) := by positivity
    calc PlaneWaveGridG.gLzU sys (FreeBoundary.tv R θ) * (52 + Real.sqrt 6162) /
          Real.sqrt (2 * Real.pi / L * T) * ‖wMul (FreeBoundary.wPhys P (2 * Real.pi / L)) v‖
        ≤ PlaneWaveGridG.gLzU sys (FreeBoundary.tv R θ) * (52 + Real.sqrt 6162) /
          Real.sqrt (2 * Real.pi / L * T) * (b0gU sys (FreeBoundary.tv R θ) Hunit * D.Xi) :=
          mul_le_mul_of_nonneg_left hvw h0
      _ = _ := by
          rw [← hgg]
          ring
  -- the kinetic shell
  set κ₁ := sys.maxMass * b0gU sys (FreeBoundary.tv R θ) Hunit + resU sys (FreeBoundary.tv R θ)
    Hunit + PlaneWaveGridG.gLzU sys (FreeBoundary.tv R θ) * (52 + Real.sqrt 6162) *
      b0gU sys (FreeBoundary.tv R θ) Hunit with hκ₁
  have hk : ‖maskOp (High T p) (wMul (kinT eta m P (2 * Real.pi / L)) v)‖ ≤
      κ₁ * D.Xi / Real.sqrt (gF L * T) := by
    rw [hkin, hGx, map_add, map_sub, map_add]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    have e : κ₁ * D.Xi / Real.sqrt (gF L * T) =
        sys.maxMass * b0gU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt (gF L * T) +
          resU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt (gF L * T) +
          PlaneWaveGridG.gLzU sys (FreeBoundary.tv R θ) * (52 + Real.sqrt 6162) *
            b0gU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt (gF L * T) := by
      rw [hκ₁]
      ring
    rw [e]
    exact add_le_add (add_le_add ha hb) hc
  -- the weight shell
  have hwk : wMul (FreeBoundary.wPhys P (gF L)) v =
      v + (2 : ℂ) • wMul (kinT eta m P (2 * Real.pi / L)) v := by
    ext q
    simp only [wMul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have e : FreeBoundary.wPhys P (gF L) q = 1 + 2 * kinT eta m P (2 * Real.pi / L) q :=
      wPhys_eq_kinT sys (gF L) q
    rw [e]
    push_cast
    ring
  rw [hwk, map_add, map_smul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have hk0 : 0 ≤ κ₁ * D.Xi / Real.sqrt (gF L * T) := by
    have := b0gU_nonneg sys hV hH
    have := resU_nonneg sys hV hH
    have := PlaneWaveGridG.gLzU_nonneg sys hV
    positivity
  have hdiv := norm_high_le_kinT P (show 0 < 2 * Real.pi / L from hg) T p v
  have hA : 2 * P.maxMass / ((2 * Real.pi / L) ^ 2 * ((T : ℝ) + 1) ^ 2) ≤ 2 * sys.maxMass := by
    rw [hMeq]
    apply div_le_self (by positivity)
    have : 1 ≤ 2 * Real.pi / L * ((T : ℝ) + 1) := by
      rw [← hgg]
      nlinarith
    calc (1 : ℝ) ≤ (2 * Real.pi / L * ((T : ℝ) + 1)) ^ 2 := one_le_pow₀ this
      _ = _ := by ring
  have hv1 : ‖maskOp (High T p) v‖ ≤ 2 * sys.maxMass * (κ₁ * D.Xi / Real.sqrt (gF L * T)) :=
    hdiv.trans (mul_le_mul hA hk (norm_nonneg _) (by positivity))
  have e : b1gU sys (FreeBoundary.tv R θ) Hunit * D.Xi / Real.sqrt (gF L * T) =
      2 * sys.maxMass * (κ₁ * D.Xi / Real.sqrt (gF L * T)) +
        2 * (κ₁ * D.Xi / Real.sqrt (gF L * T)) := by
    unfold b1gU
    rw [← hκ₁]
    ring
  rw [e]
  exact add_le_add hv1 (mul_le_mul_of_nonneg_left hk (by norm_num))

end GridShells

end KineticLog
