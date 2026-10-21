import PlaneWave.FreeBoundary.GridSecondOrderPhysical

/-!
# `L`-uniform grid dynamics, stage 4: second moments, duality and the observable error in the
physical weight

The continuum side of the sharp grid-dynamics proof for `g_L`
(`PlaneWave.FreeBoundary.GridDynamicsSharp`) with the physical weight `w_g = 1 + g² Σ_b |n_b|²/m_b`:

* the layer cake with physical momenta: a layer `k ≥ k₀` above the first threshold (`g k₀ ≥ 1`)
  costs `120 m̄² Ξ₁²/g³ + 30 C₀²(N+1)²/g` (the factor `1/k ≤ g` kept), so
  `‖g² |n_r|² F‖ ≤ √Q_g r_g` with `Q_g = (g k₀)⁴ Ξ₀² + 120 m̄² Ξ₁² + 30 C₀²` and
  `r_g = (g(4m+1))^{3/2}` (`layer_boundP`);
* the second moment of the projected trajectory,
  `‖w_g² P ψ(t)‖ ≤ ‖ψ₀‖ + 4 Ξ₀ + 2 η √Q_g r_g` (`second_moment_regCoeff_le_gLU`);
* the `H²` lift of a register vector has norm exactly `‖wTot_g φ‖`
  (`norm_cubeLift_regUnitary_eqP`), and a continuum state has `‖wTot_g P S u‖ ≤ ‖u‖`
  (`norm_wTotPh_regCoeff_stateMap_le`): the conversions of the release (`1 + g²`, `1 + 1/g²`)
  are not needed;
* duality on the grid with the shell of the backward flow as a parameter, with the physical form
  constant `formAP g s m` of the aliasing estimate (`grid_duality_shell_gLU`).

The observable error is assembled from these in `PlaneWave.FreeBoundary.GridObservablePhysical`
(`grid_observable_error_sharp_gLU`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics

open PlaneWaveGridG (gLgamma gLgamma_pos gLref gLNucData regParticlesOfG gLzU gLzU_nonneg gLAU
  sobP formAP formAP_nonneg)

namespace FreeBoundary

/-! ## The layer cake with physical momenta -/

section LayerP

variable {eta m : ℕ}

/-- One layer above the threshold, physical: if `x ≤ B(gk)`, `g k ≥ 1` and `k ≤ N + 1`, then
`((k+1)⁴ - k⁴) x² ≤ 120 M² Ξ₁²/g³ + (30 C₀²/g) (N+1)²`. -/
lemma layer_term_leP {k : ℕ} (hk : 1 ≤ k) {N g M Ξ₁ C₀ x : ℝ} (hg : 0 < g) (hgk : 1 ≤ g * k)
    (hx : 0 ≤ x) (hxB : x ≤ (2 * M / (g * k) ^ 2) * Ξ₁ + C₀ * Real.sqrt (1 / (g * k)))
    (hkN : (k : ℝ) ≤ N + 1) :
    (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * x ^ 2 ≤
      120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 3 + 30 * C₀ ^ 2 / g * (N + 1) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hgk0 : 0 < g * k := mul_pos hg hk0
  have hgne : g ≠ 0 := hg.ne'
  have hkne : (k : ℝ) ≠ 0 := hk0.ne'
  have hBsq : ((2 * M / (g * k) ^ 2) * Ξ₁ + C₀ * Real.sqrt (1 / (g * k))) ^ 2 ≤
      8 * M ^ 2 * Ξ₁ ^ 2 / (g * k) ^ 4 + 2 * C₀ ^ 2 / (g * k) := by
    have hs : Real.sqrt (1 / (g * k)) ^ 2 = 1 / (g * k) := Real.sq_sqrt (by positivity)
    have e1 := sq_add_le_two_sq ((2 * M / (g * k) ^ 2) * Ξ₁) (C₀ * Real.sqrt (1 / (g * k)))
    have e2 : 2 * ((2 * M / (g * k) ^ 2) * Ξ₁) ^ 2 = 8 * M ^ 2 * Ξ₁ ^ 2 / (g * k) ^ 4 := by
      field_simp
      ring
    have e3 : 2 * (C₀ * Real.sqrt (1 / (g * k))) ^ 2 = 2 * C₀ ^ 2 / (g * k) := by
      rw [mul_pow, hs]
      ring
    linarith
  have hx2 : x ^ 2 ≤ 8 * M ^ 2 * Ξ₁ ^ 2 / (g * k) ^ 4 + 2 * C₀ ^ 2 / (g * k) :=
    (pow_le_pow_left₀ hx hxB 2).trans hBsq
  have hwk := layer_weight_le hk
  calc (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * x ^ 2
      ≤ (15 * (k : ℝ) ^ 3) * (8 * M ^ 2 * Ξ₁ ^ 2 / (g * k) ^ 4 + 2 * C₀ ^ 2 / (g * k)) :=
        mul_le_mul hwk hx2 (sq_nonneg _) (by positivity)
    _ = 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 3 * (1 / (g * k)) + 30 * C₀ ^ 2 / g * (k : ℝ) ^ 2 := by
        field_simp
        ring
    _ ≤ 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 3 + 30 * C₀ ^ 2 / g * (N + 1) ^ 2 := by
        have h1gk : 1 / (g * k) ≤ 1 := by
          rw [div_le_one hgk0]
          exact hgk
        have h3 : 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 3 * (1 / (g * k)) ≤ 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 3 :=
          mul_le_of_le_one_right (by positivity) h1gk
        have h4 : (k : ℝ) ^ 2 ≤ (N + 1) ^ 2 := pow_le_pow_left₀ hk0.le hkN 2
        have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 30 * C₀ ^ 2 / g)
        linarith

/-- The layer sum, finer: the `k₀` low layers cost at most `k₀⁴ A` and the `N + 1` high layers at
most `(N+1) B + C (N+1)³`. -/
lemma layer_sum_arithP (N k₀ : ℕ) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∑ k ∈ range (N + 1), (if k < k₀ then (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A
      else B + C * ((N : ℝ) + 1) ^ 2) ≤
        (k₀ : ℝ) ^ 4 * A + ((N : ℝ) + 1) * B + C * ((N : ℝ) + 1) ^ 3 := by
  have hc : 0 ≤ B + C * ((N : ℝ) + 1) ^ 2 := by positivity
  have hsplit : ∀ k ∈ range (N + 1),
      (if k < k₀ then (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A else B + C * ((N : ℝ) + 1) ^ 2) ≤
      (if k < k₀ then (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A else 0) +
        (B + C * ((N : ℝ) + 1) ^ 2) := by
    intro k _
    split_ifs
    · linarith
    · linarith
  refine (sum_le_sum hsplit).trans ?_
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have hlow : ∑ k ∈ range (N + 1),
      (if k < k₀ then (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A else 0) ≤ (k₀ : ℝ) ^ 4 * A := by
    rw [← sum_filter]
    calc ∑ k ∈ (range (N + 1)).filter (· < k₀), (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A
        ≤ ∑ k ∈ range k₀, (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * A := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ =>
            mul_nonneg (layer_weight_nonneg k) hA
          intro k hk
          exact mem_range.mpr (mem_filter.mp hk).2
      _ = (k₀ : ℝ) ^ 4 * A := by
          rw [← Finset.sum_mul]
          have h := Finset.sum_range_sub (fun k : ℕ => ((k : ℝ)) ^ 4) k₀
          simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
          rw [h]
          ring
  rw [Nat.cast_succ]
  have e3 : ((N : ℝ) + 1) * (B + C * ((N : ℝ) + 1) ^ 2) =
      ((N : ℝ) + 1) * B + C * ((N : ℝ) + 1) ^ 3 := by ring
  rw [e3]
  linarith

/-- **The layer bound for one register coordinate, physical momenta:** if every shell of `F` is
at most `Ξ₀` and the shells beyond `k₀` (`g k₀ ≥ 1`) are at most
`B(gk) = (2M/(gk)²) Ξ₁ + C₀ (gk)^{-1/2}`, then `‖g² |n_r|² F‖ ≤ √Q_g r_g` with
`Q_g = (g k₀)⁴ Ξ₀² + 120 M² Ξ₁² + 30 C₀²` and `r_g = (g(4m+1))^{3/2} ≥ 1`. -/
lemma layer_boundP (r : Fin eta) (F : EuclideanSpace ℂ (RCfg eta m)) {g M Ξ₀ Ξ₁ C₀ : ℝ}
    (hg : 0 < g) (k₀ : ℕ) (hk₀ : 1 ≤ k₀) (hk₀g : 1 ≤ g * k₀)
    (hN : 1 ≤ g * (((4 * m : ℕ) : ℝ) + 1))
    (hlow : ∀ k : ℕ, ‖maskOp (Shell r k) F‖ ≤ Ξ₀)
    (hhigh : ∀ k : ℕ, k₀ ≤ k → ‖maskOp (Shell r k) F‖ ≤
      (2 * M / (g * k) ^ 2) * Ξ₁ + C₀ * Real.sqrt (1 / (g * k))) :
    ‖wMul (fun q => g ^ 2 * nsq (gl (q r))) F‖ ≤
      Real.sqrt ((g * k₀) ^ 4 * Ξ₀ ^ 2 + 120 * M ^ 2 * Ξ₁ ^ 2 + 30 * C₀ ^ 2) * rPhys g m := by
  have h1 := layer_sum_le r F
  have hterm : ∀ k ∈ range (4 * m + 1),
      (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * ‖maskOp (Shell r k) F‖ ^ 2 ≤
      (if k < k₀ then (((k : ℝ) + 1) ^ 4 - (k : ℝ) ^ 4) * Ξ₀ ^ 2 else
        120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 3 + 30 * C₀ ^ 2 / g * (((4 * m : ℕ) : ℝ) + 1) ^ 2) := by
    intro k hk
    by_cases hkk : k < k₀
    · rw [if_pos hkk]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hlow k) 2)
        (layer_weight_nonneg k)
    · rw [if_neg hkk]
      have hkk' : k₀ ≤ k := not_lt.mp hkk
      have hkN : (k : ℝ) ≤ ((4 * m : ℕ) : ℝ) + 1 := by
        have h := mem_range.mp hk
        have h' : (k : ℝ) < ((4 * m + 1 : ℕ) : ℝ) := by exact_mod_cast h
        rw [Nat.cast_succ] at h'
        linarith
      have hgk : 1 ≤ g * k :=
        hk₀g.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hkk') hg.le)
      exact layer_term_leP (hk₀.trans hkk') hg hgk (norm_nonneg _) (hhigh k hkk') hkN
  have h2 := (sum_le_sum hterm).trans (layer_sum_arithP (4 * m) k₀ (sq_nonneg Ξ₀)
    (by positivity : (0 : ℝ) ≤ 120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 3)
    (by positivity : (0 : ℝ) ≤ 30 * C₀ ^ 2 / g))
  set N1 : ℝ := ((4 * m : ℕ) : ℝ) + 1 with hN1
  set Y : ℝ := g * N1 with hY
  have hY1 : 1 ≤ Y := hN
  have hY3 : 1 ≤ Y ^ 3 := one_le_pow₀ hY1
  have hYY3 : Y ≤ Y ^ 3 := by
    calc Y = Y * 1 := by ring
      _ ≤ Y * Y ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hY1) (by linarith)
      _ = Y ^ 3 := by ring
  set Q : ℝ := (g * k₀) ^ 4 * Ξ₀ ^ 2 + 120 * M ^ 2 * Ξ₁ ^ 2 + 30 * C₀ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  -- the scaled layer sum
  have hX : ‖wMul (fun q => nsq (gl (q r))) F‖ ^ 2 ≤
      (k₀ : ℝ) ^ 4 * Ξ₀ ^ 2 + N1 * (120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 3) +
        30 * C₀ ^ 2 / g * N1 ^ 3 := h1.trans h2
  have e1 : g ^ 4 * ((k₀ : ℝ) ^ 4 * Ξ₀ ^ 2 + N1 * (120 * M ^ 2 * Ξ₁ ^ 2 / g ^ 3) +
      30 * C₀ ^ 2 / g * N1 ^ 3) =
      (g * k₀) ^ 4 * Ξ₀ ^ 2 + 120 * M ^ 2 * Ξ₁ ^ 2 * Y + 30 * C₀ ^ 2 * Y ^ 3 := by
    rw [hY]
    field_simp
  have hscale : wMul (fun q => g ^ 2 * nsq (gl (q r))) F =
      ((g ^ 2 : ℝ) : ℂ) • wMul (fun q => nsq (gl (q r))) F := by
    ext q
    simp only [wMul_apply, PiLp.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hsq : ‖wMul (fun q => g ^ 2 * nsq (gl (q r))) F‖ ^ 2 ≤ Q * Y ^ 3 := by
    rw [hscale, norm_smul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg g), mul_pow]
    have h4 := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ g ^ 4)
    have e2 : (g ^ 2) ^ 2 = g ^ 4 := by ring
    rw [e2]
    have h5 : 120 * M ^ 2 * Ξ₁ ^ 2 * Y ≤ 120 * M ^ 2 * Ξ₁ ^ 2 * Y ^ 3 :=
      mul_le_mul_of_nonneg_left hYY3 (by positivity)
    have h6 : (g * k₀) ^ 4 * Ξ₀ ^ 2 ≤ (g * k₀) ^ 4 * Ξ₀ ^ 2 * Y ^ 3 :=
      le_mul_of_one_le_right (by positivity) hY3
    have e3 : Q * Y ^ 3 = (g * k₀) ^ 4 * Ξ₀ ^ 2 * Y ^ 3 + 120 * M ^ 2 * Ξ₁ ^ 2 * Y ^ 3 +
        30 * C₀ ^ 2 * Y ^ 3 := by rw [hQ]; ring
    linarith
  have hr : rPhys g m ^ 2 = Y ^ 3 := by
    unfold rPhys
    rw [← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt (by linarith)]
  have hfin : ‖wMul (fun q => g ^ 2 * nsq (gl (q r))) F‖ ^ 2 ≤ (Real.sqrt Q * rPhys g m) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hQ0, hr]
    exact hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (by unfold rPhys; positivity)) two_ne_zero).mp hfin

/-- `‖w_g F‖ ≤ ‖F‖ + Σ_r ‖g² |n_r|² F‖`. -/
lemma norm_wPhys_le_layers (P : RegParticles eta) (g : ℝ) (F : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wPhys P g) F‖ ≤ ‖F‖ + ∑ r : Fin eta, ‖wMul (fun q => g ^ 2 * nsq (gl (q r))) F‖ := by
  have hmono : ‖wMul (wPhys P g) F‖ ≤ ‖wMul (wTotPh g) F‖ :=
    norm_wMul_mono (wPhys_nonneg P g) (wPhys_le_wTotPh P g) F
  have e : wMul (wTotPh g) F = F + ∑ r : Fin eta, wMul (fun q => g ^ 2 * nsq (gl (q r))) F := by
    ext q
    simp only [wMul_apply, PiLp.add_apply, wTotPh]
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    simp only [wMul_apply]
    push_cast
    rw [add_mul, one_mul, Finset.mul_sum, Finset.sum_mul]
  rw [e] at hmono
  exact hmono.trans ((norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _)))

/-- The assembly of the physical second moment on the register. -/
lemma second_moment_assembleP (P : RegParticles eta) (a F : EuclideanSpace ℂ (RCfg eta m))
    {g S0 Ξ₀ R : ℝ}
    (hpt : ∀ q, ‖(wMul (wPhys P g) (wMul (wPhys P g) a)) q‖ ≤
      ‖a q‖ + 2 * ‖F q‖ + 2 * ‖(wMul (wPhys P g) F) q‖)
    (ha : ‖a‖ ≤ S0) (hF : ‖F‖ ≤ Ξ₀)
    (hlayer : ∀ r : Fin eta, ‖wMul (fun q => g ^ 2 * nsq (gl (q r))) F‖ ≤ R) :
    ‖wMul (wPhys P g) (wMul (wPhys P g) a)‖ ≤ S0 + 4 * Ξ₀ + 2 * (eta * R) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h4 := norm_le_add3_of_pointwise (X := wMul (wPhys P g) (wMul (wPhys P g) a)) (A := a)
    (B := ((2 : ℝ) : ℂ) • F) (C := ((2 : ℝ) : ℂ) • wMul (wPhys P g) F) (fun q => by
      simp only [PiLp.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg h2]
      exact hpt q)
  rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg h2] at h4
  have hsum : ∑ r : Fin eta, ‖wMul (fun q => g ^ 2 * nsq (gl (q r))) F‖ ≤ eta * R := by
    calc ∑ r : Fin eta, ‖wMul (fun q => g ^ 2 * nsq (gl (q r))) F‖ ≤ ∑ _r : Fin eta, R :=
          sum_le_sum fun r _ => hlayer r
      _ = eta * R := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h5 := (norm_wPhys_le_layers P g F).trans (add_le_add hF hsum)
  linarith

end LayerP

/-! ## Conversions with the `H²` weight -/

section Conversions

variable {eta m : ℕ}

/-- The `H²` lift of a register vector has norm `‖wTot_g φ‖`. -/
lemma norm_cubeLift_regUnitary_eqP (g : ℝ) (φ : EuclideanSpace ℂ (RCfg eta m)) :
    ‖cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm φ)‖ = ‖wMul (wTotPh g) φ‖ := by
  rw [cubeLift_regUnitary_symm, LinearIsometry.norm_map]
  have e : (fun q : RCfg eta m => molecularFourierH2Weight eta g (liftCfg q)) = wTotPh g :=
    funext fun q => (wTotPh_eq_h2Weight g q).symm
  rw [e]

/-- The physical register weight of a continuum state is at most its `H²` norm. -/
lemma norm_wTotPh_regCoeff_stateMap_le (g : ℝ) (u : MolecularFourierH2 eta) :
    ‖wMul (wTotPh g) (regCoeff m (molecularH2StateMap eta g u))‖ ≤ ‖u‖ := by
  have hpt : ∀ q, ‖(wMul (wTotPh g) (regCoeff m (molecularH2StateMap eta g u))) q‖ ≤
      ‖(regCoeff m u) q‖ := by
    intro q
    have hw : 0 < molecularFourierH2Weight eta g (liftCfg q) :=
      molecularFourierH2Weight_pos eta g _
    have e := wTotPh_eq_h2Weight (m := m) g q
    have hq : ‖(wMul (wTotPh g) (regCoeff m (molecularH2StateMap eta g u))) q‖ =
        ‖(regCoeff m u) q‖ := by
      rw [wMul_apply, regCoeff_apply, molecularH2StateMap_apply, molecularH2Coeff, regCoeff_apply,
        norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (le_trans zero_le_one (wTotPh_ge_one g q)),
        Real.norm_of_nonneg hw.le, e, mul_div_cancel₀ _ hw.ne']
    exact hq.le
  exact (norm_le_of_pointwise hpt).trans (norm_regCoeff_le u)

lemma norm_wPhys_regCoeff_stateMap_le (P : RegParticles eta) (g : ℝ) (u : MolecularFourierH2 eta) :
    ‖wMul (wPhys P g) (regCoeff m (molecularH2StateMap eta g u))‖ ≤ ‖u‖ :=
  (norm_wMul_mono (wPhys_nonneg P g) (wPhys_le_wTotPh P g) _).trans
    (norm_wTotPh_regCoeff_stateMap_le g u)

end Conversions

/-! ## The second moment of the projected trajectory -/

section Continuum

variable {eta : ℕ} {ν : Type} [Fintype ν]

lemma gLtailMU_nonneg (sys : CoulombSystem eta ν) {V : ℝ} (hV : 0 ≤ V) {Hunit : ℝ}
    (hH : 0 ≤ Hunit) {M : ℝ} (hM : 0 ≤ M) : 0 ≤ gLtailMU sys V Hunit M := by
  unfold gLtailMU PlaneWaveGridG.ctailU
  have := PlaneWaveGridG.tBU_nonneg hH
  have := sys.couplingWeight_nonneg
  have : 0 ≤ 1 + V := by linarith
  positivity

/-- Weakening the tail constant in a tail bound `x ≤ (2m̄/K²)((2m̄/K²) Ξ₁ + C ρ)`. -/
lemma tail_weaken {mm K Ξ₁ C C' ρ x : ℝ} (hmm : 0 ≤ mm) (hρ : 0 ≤ ρ) (hCC : C ≤ C')
    (hx : x ≤ (2 * mm / K ^ 2) * ((2 * mm / K ^ 2) * Ξ₁ + C * ρ)) :
    x ≤ (2 * mm / K ^ 2) * ((2 * mm / K ^ 2) * Ξ₁ + C' * ρ) := by
  refine hx.trans (mul_le_mul_of_nonneg_left ?_ (div_nonneg (by linarith) (sq_nonneg K)))
  have := mul_le_mul_of_nonneg_right hCC hρ
  linarith

/-- The physical register weight against the kinetic symbol: `w_g² |c| = |c| + 2 |T c| +
2 w_g |T c|` at the lifted configurations (`T c = ((w_g - 1)/2) c`). -/
lemma norm_wPhys_sq_regCoeff_le_pt (sys : CoulombSystem eta ν) (g : ℝ) (m : ℕ)
    (u : MolecularFourierH2 eta) (q : RCfg eta m) :
    ‖(wMul (wPhys (regParticlesOf sys) g) (wMul (wPhys (regParticlesOf sys) g)
        (regCoeff m (molecularH2StateMap eta g u)))) q‖ ≤
      ‖(regCoeff m (molecularH2StateMap eta g u)) q‖ +
        2 * ‖(regCoeff m (coulombFourierKineticH2 sys g u)) q‖ +
        2 * ‖(wMul (wPhys (regParticlesOf sys) g) (regCoeff m (coulombFourierKineticH2 sys g u))) q‖
      := by
  set P := regParticlesOf sys
  set c : ℂ := molecularH2Coeff g u (liftCfg q)
  have hW0 := wPhys_nonneg P g q
  have hW1 := wPhys_ge_one P g q
  have hkinL : coulombKineticEnergySymbol sys g (liftCfg q) = g ^ 2 / 2 * (wM P q - 1) := by
    unfold coulombKineticEnergySymbol wM
    rw [add_sub_cancel_left, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun r _ => ?_
    simp only [liftCfg, nsq_eq_latticeNormSq]
    rw [show P.mass r = sys.mass r from rfl]
    ring
  have hkin : coulombKineticEnergySymbol sys g (liftCfg q) = (wPhys P g q - 1) / 2 := by
    rw [hkinL, wPhys_eq_wM]
    ring
  have hk0 : 0 ≤ (wPhys P g q - 1) / 2 := by linarith
  have hT : (regCoeff m (coulombFourierKineticH2 sys g u)) q =
      (((wPhys P g q - 1) / 2 : ℝ) : ℂ) * c := by
    rw [regCoeff_apply, coulombFourierKineticH2_apply, hkin]
  have hS : (regCoeff m (molecularH2StateMap eta g u)) q = c := by
    rw [regCoeff_apply, molecularH2StateMap_apply]
  rw [wMul_apply, wMul_apply, wMul_apply, hT, hS]
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hW0, Real.norm_of_nonneg hk0]
  have e : wPhys P g q * (wPhys P g q * ‖c‖) = ‖c‖ + 2 * ((wPhys P g q - 1) / 2 * ‖c‖) +
      2 * (wPhys P g q * ((wPhys P g q - 1) / 2 * ‖c‖)) := by ring
  exact le_of_eq e

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  {θ : ℝ → ℝ} (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 0 < L) {R : ℝ} (hθ : Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hθ hPeriodic in
/-- **The second kinetic moment of the projected trajectory, physical weight** (`lem:grid-data2`):
for `ψ(t) = S u`, `‖w_g² P ψ(t)‖ ≤ ‖ψ₀‖ + 4 Ξ₀ + 2 η √Q_g r_g` uniformly in `t`, where
`Q_g = 16 Ξ₀² + 120 m̄² Ξ₁² + 30 C_tail(M₀)²` (first threshold `1 ≤ g k₀ ≤ 2`) and
`r_g = (g(4m+1))^{3/2}`. -/
theorem second_moment_regCoeff_le_gLU (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    (hL2 : 2 * Real.pi ≤ L) (hH : 0 ≤ Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (m : ℕ)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (t : ℝ) (u : MolecularFourierH2 eta)
    (hu1 : molecularH2StateMap eta (2 * Real.pi / L) u =
      U t (molecularH2StateMap eta (2 * Real.pi / L) u₀))
    (hu2 : H u = U t (H u₀)) (k₀ : ℕ) (hk₀ : 2 ≤ k₀) (hk₀g : 1 ≤ (2 * Real.pi / L) * k₀)
    (hk₀2 : (2 * Real.pi / L) * k₀ ≤ 2)
    (hN : 1 ≤ (2 * Real.pi / L) * (((4 * m : ℕ) : ℝ) + 1)) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB_gL sys L (tv R θ) Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let C₀ : ℝ := gLtailMU sys (tv R θ) Hunit M₀
    let Q : ℝ := 16 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 + 30 * C₀ ^ 2
    ‖wMul (wPhys (regParticlesOf sys) g) (wMul (wPhys (regParticlesOf sys) g)
        (regCoeff m (molecularH2StateMap eta g u)))‖ ≤
      S0 + 4 * Ξ₀ + 2 * (eta * (Real.sqrt Q * rPhys g m)) := by
  intro g b S0 Ξ₀ Ξ₁ M₀ C₀ Q
  have hb : 0 ≤ b := relB_gL_nonneg sys L (tv R θ) Hunit hC
  have hg : 0 < g := by positivity
  have hM₀ : 0 ≤ M₀ := by
    have hM := sys.one_le_maxMass
    have hS0 : 0 ≤ S0 := norm_nonneg _
    have hΞ₀ : 0 ≤ Ξ₀ := by positivity
    positivity
  have hSu : ‖molecularH2StateMap eta g u‖ = S0 := by
    show ‖molecularH2StateMap eta g u‖ = ‖molecularH2StateMap eta g u₀‖
    rw [hu1, LinearIsometryEquiv.norm_map]
  have hTu : ‖coulombFourierKineticH2 sys g u‖ ≤ Ξ₀ := by
    have h := kinetic_le_elliptic_gL sys L H hKernel Hunit hL hθ hPeriodic hC u
    rw [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
    exact h
  have hhigh : ∀ r : Fin eta, ∀ k : ℕ, k₀ ≤ k →
      ‖maskOp (Shell r k) (regCoeff m (coulombFourierKineticH2 sys g u))‖ ≤
        (2 * sys.maxMass / (g * k) ^ 2) * Ξ₁ + C₀ * Real.sqrt (1 / (g * k)) := by
    intro r k hkk
    have hgk1 : 1 ≤ g * k :=
      hk₀g.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hkk) hg.le)
    have hgkpos : 0 < g * k := by linarith
    have hρ : Real.sqrt (1 / (g * k)) ^ 2 * (g * k) = 1 := by
      rw [Real.sq_sqrt (div_nonneg zero_le_one hgkpos.le), div_mul_cancel₀ 1 hgkpos.ne']
    have hT : ‖tailMask g (g * k) r (coulombFourierKineticH2 sys g u)‖ ≤
        (2 * sys.maxMass / (g * k) ^ 2) * Ξ₁ +
          gLtailM sys L (tv R θ) Hunit M₀ * Real.sqrt (1 / (g * k)) :=
      (tails_at_time_gL sys L H hKernel Hunit hL hθ hPeriodic hC U hgraph r (g * k)
        (Real.sqrt (1 / (g * k))) hgk1 (Real.sqrt_nonneg _) hρ u₀ v₀ huv t u hu1 hu2).1
    have hCU : gLtailM sys L (tv R θ) Hunit M₀ * Real.sqrt (1 / (g * k)) ≤
        C₀ * Real.sqrt (1 / (g * k)) :=
      mul_le_mul_of_nonneg_right (gLtailM_le_U sys hL2 hθ.tv_nonneg hH hM₀) (Real.sqrt_nonneg _)
    exact (norm_shell_regCoeff_le hg r k _).trans (hT.trans (by linarith))
  have hQle : (g * k₀) ^ 4 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 + 30 * C₀ ^ 2 ≤ Q := by
    have h0 : 0 ≤ g * k₀ := by positivity
    have h1 : (g * k₀) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 hk₀2 4
    have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg Ξ₀)
    show _ ≤ 16 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 + 30 * C₀ ^ 2
    norm_num at h2
    linarith
  have hlow : ∀ r : Fin eta, ∀ k : ℕ,
      ‖maskOp (Shell r k) (regCoeff m (coulombFourierKineticH2 sys g u))‖ ≤ Ξ₀ := fun r k =>
    (norm_shell_regCoeff_le hg r k _).trans ((norm_tailMask_apply_le g (g * k) r _).trans hTu)
  exact second_moment_assembleP (regParticlesOf sys) _ _
    (norm_wPhys_sq_regCoeff_le_pt sys g m u) ((norm_regCoeff_le _).trans hSu.le)
    ((norm_regCoeff_le _).trans hTu)
    (fun r => (layer_boundP r _ hg k₀ (by omega) hk₀g hN (hlow r) (hhigh r)).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hQle) (by unfold rPhys; positivity)))

end Continuum

/-! ## Duality on the grid, physical weight -/

section Grid

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  {θ : ℝ → ℝ} (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 0 < L) {R : ℝ} (hθ : Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hθ hPeriodic in
/-- **Duality on the grid with the flow shell as a parameter, physical weight**: as
`grid_duality_shell_gL`, with the physical weight `‖w_g U_g(τ) w‖ ≤ W_φ` of the flow, the physical
form constant `formAP g s₀ m` and the physical `H²` budget `M₀`: `|⟪a(t) - ψ_g(t), w⟫|` is at most
`t ((η t₂)(η C_tail(m̄ W_φ) ρ₂) + Z_c (formAP (t₄ m̄ W_φ + τ_φ M₀) + 52 m τ_φ t₄))`. -/
theorem grid_duality_shell_gLU (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    (hL2 : 2 * Real.pi ≤ L) (hH : 0 ≤ Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ} (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ))
        (gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (rho₂ rho₄ : ℝ) (hK₄ : 1 ≤ (2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ))
    (hRho₂ : 0 ≤ rho₂) (hRhoScale₂ : rho₂ ^ 2 * ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) = 1)
    (hRho₄ : 0 ≤ rho₄) (hRhoScale₄ : rho₄ ^ 2 * ((2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ)) = 1)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (w : EuclideanSpace ℂ (RCfg eta m)) (Wφ τφ : ℝ)
    (hW : ∀ τ, ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (Ug τ w)‖ ≤ Wφ)
    (hτφ0 : 0 ≤ τφ) (hτ : ∀ τ r, ‖maskOp (High (m / 4) r) (Ug τ w)‖ ≤ τφ) {t : ℝ} (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB_gL sys L (tv R θ) Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let Ct : ℝ → ℝ := fun M => gLtailMU sys (tv R θ) Hunit M
    let tl : ℝ → ℝ → ℝ := fun K ρ =>
      (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    let s₀ : ℕ := m / 4
    let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (gLgamma L (tv R θ))
    let t₂ : ℝ := tl (g * ((2 * m : ℕ) : ℝ)) rho₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) rho₄
    ‖⟪regCoeff m (U t (molecularH2StateMap eta g u₀)) -
        Ug t (regCoeff m (molecularH2StateMap eta g u₀)), w⟫_ℂ‖ ≤
      ((eta * t₂) * (eta * (Ct (sys.maxMass * Wφ) * rho₂)) +
        Zg * (formAP g s₀ m * (t₄ * (sys.maxMass * Wφ) + τφ * M₀) + 52 * m * (τφ * t₄))) * t := by
  intro g b S0 Ξ₀ Ξ₁ M₀ Ct tl s₀ Zg t₂ t₄
  have hM := sys.one_le_maxMass
  have hb : 0 ≤ b := relB_gL_nonneg sys L (tv R θ) Hunit hC
  have hg : 0 < g := by positivity
  have hγ : 0 ≤ gLgamma L (tv R θ) := (gLgamma_pos hL hθ.tv_nonneg).le
  have hs₀ : 2 ≤ s₀ := by show 2 ≤ m / 4; omega
  have hs₀m : s₀ ≤ m := Nat.div_le_self m 4
  have hs₀2m : (s₀ : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
    exact_mod_cast (show s₀ ≤ 2 * m by omega)
  have hK₄' : 1 ≤ g * (s₀ : ℝ) := hK₄
  have hK₂ : 1 ≤ g * ((2 * m : ℕ) : ℝ) := hK₄'.trans (mul_le_mul_of_nonneg_left hs₀2m hg.le)
  have hW0 : 0 ≤ Wφ := (norm_nonneg _).trans (hW 0)
  have hS0 : 0 ≤ S0 := norm_nonneg _
  have hΞ₀ : 0 ≤ Ξ₀ := by positivity
  have hΞ₁ : 0 ≤ Ξ₁ := by positivity
  have hM₀ : 0 ≤ M₀ := by positivity
  have hCt₀ : 0 ≤ Ct M₀ := gLtailMU_nonneg sys hθ.tv_nonneg hH hM₀
  have hCtU : gLtailM sys L (tv R θ) Hunit M₀ ≤ Ct M₀ :=
    gLtailM_le_U sys hL2 hθ.tv_nonneg hH hM₀
  have hmm : 0 ≤ sys.maxMass := by linarith
  have htl0 : ∀ K ρ, 0 ≤ ρ → 0 ≤ tl K ρ := by
    intro K ρ hρ
    show 0 ≤ (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    have h1 : 0 ≤ 2 * sys.maxMass / K ^ 2 := div_nonneg (by linarith) (sq_nonneg K)
    exact mul_nonneg h1 (add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hCt₀ hρ))
  have ht₂0 : 0 ≤ t₂ := htl0 _ _ hRho₂
  have ht₄0 : 0 ≤ t₄ := htl0 _ _ hRho₄
  have hZg : 0 ≤ Zg := Zc_nonneg hγ
  -- the trajectory and its Duhamel equation on the register
  choose u hu1 hu2 using fun s => hgraph s u₀
  have ha : ∀ s, HasDerivAt (fun s => regCoeff m (U s (molecularH2StateMap eta g u₀)))
      (-(Complex.I • (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ g
          (regCoeff m (U s (molecularH2StateMap eta g u₀))) +
        (regCoeff m (coulombFourierPotentialH2 sys g H (u s - molecularH2Truncate (2 * m) (u s))) -
          DeltaGL sys L hL hθ m κ (regCoeff m (U s (molecularH2StateMap eta g u₀))))))) s := by
    intro s
    have h1 := ((regCoeff (eta := eta) m).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
      (hderiv s u₀)
    refine h1.congr_deriv ?_
    rw [ContinuousLinearMap.coe_restrictScalars', map_neg, map_smul, ← hu2 s,
      regCoeff_H_eq_grid_gL sys L H hKernel hL hθ m κ (u s), hu1 s]
  have hbound := duality_pairing_le (Hgrid_isSymmetric hκ.even) Ug hg0 hgcomm hgderiv ha w ht
    (B := (eta * t₂) * (eta * (Ct (sys.maxMass * Wφ) * rho₂)) +
      Zg * (formAP g s₀ m * (t₄ * (sys.maxMass * Wφ) + τφ * M₀) + 52 * m * (τφ * t₄)))
    (fun s _ => ?_)
  · simp only [h0] at hbound
    exact hbound
  -- the pairing at time `s`
  set φ := Ug (s - t) w with hφ
  have hφW : ‖wMul (wPhys (regParticlesOf sys) g) φ‖ ≤ Wφ := hW (s - t)
  have hφT : ‖wMul (wTotPh g) φ‖ ≤ sys.maxMass * Wφ :=
    (norm_wTotPh_le (regParticlesOf sys) g φ).trans
      (mul_le_mul_of_nonneg_left hφW (regParticlesOf sys).maxMass_pos.le)
  have hu_le : ‖u s‖ ≤ M₀ := by
    have h := h2norm_le sys L (u s)
    have hT := kinetic_le_elliptic_gL sys L H hKernel Hunit hL hθ hPeriodic hC (u s)
    rw [hu1 s, LinearIsometryEquiv.norm_map] at h
    rw [hu1 s, hu2 s, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at hT
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    show ‖molecularH2StateMap eta g u₀‖ + 2 * ‖coulombFourierKineticH2 sys g (u s)‖ ≤ S0 + 2 * Ξ₀
    linarith
  -- (i) the Galerkin source against the lift of the flow
  have hi : ‖⟪regCoeff m (coulombFourierPotentialH2 sys g H
      (u s - molecularH2Truncate (2 * m) (u s))),
      φ⟫_ℂ‖ ≤ (eta * t₂) * (eta * (Ct (sys.maxMass * Wφ) * rho₂)) := by
    refine (norm_inner_galSource_le_gL sys L H hKernel hθ m (u s) φ).trans ?_
    have hδ : ‖molecularH2StateMap eta g (u s) -
        molecularH2Truncate (2 * m) (molecularH2StateMap eta g (u s))‖ ≤ eta * t₂ := by
      refine (norm_sub_truncate_le hg (2 * m) _).trans ?_
      have htl : ∀ c, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g (u s))‖ ≤
          t₂ := fun c => tail_weaken hmm hRho₂ hCtU
        (tails_at_time_gL sys L H hKernel Hunit hL hθ hPeriodic hC U hgraph c
          (g * ((2 * m : ℕ) : ℝ)) rho₂ hK₂ hRho₂ hRhoScale₂ u₀ v₀ huv s (u s) (hu1 s) (hu2 s)).2
      calc ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g (u s))‖
          ≤ ∑ _c : Fin eta, t₂ := sum_le_sum fun c _ => htl c
        _ = eta * t₂ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hMl : 0 ≤ sys.maxMass * Wφ := by positivity
    have hl : ‖cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm φ)‖ ≤ sys.maxMass * Wφ := by
      rw [norm_cubeLift_regUnitary_eqP]
      exact hφT
    have hΛ : ‖coulombFourierPotentialH2 sys g H
        (cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm φ)) -
        molecularH2Truncate (2 * m) (coulombFourierPotentialH2 sys g H
          (cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm φ)))‖ ≤
        eta * (Ct (sys.maxMass * Wφ) * rho₂) := by
      refine (norm_sub_truncate_le hg (2 * m) _).trans ?_
      calc ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (coulombFourierPotentialH2 sys g H
            (cubeLift g (2 * m) ((regUnitary eta (2 * m)).symm φ)))‖
          ≤ ∑ _c : Fin eta, Ct (sys.maxMass * Wφ) * rho₂ :=
            sum_le_sum fun c _ => (potential_tail_le_gL sys L H hKernel Hunit hL hθ hPeriodic c _
                rho₂ _ hK₂ hRho₂ hRhoScale₂ hMl _ hl).trans (mul_le_mul_of_nonneg_right
                  (gLtailM_le_U sys hL2 hθ.tv_nonneg hH hMl) hRho₂)
        _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hΛ0 : 0 ≤ eta * (Ct (sys.maxMass * Wφ) * rho₂) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
        (gLtailMU_nonneg sys hθ.tv_nonneg hH hMl) hRho₂)
    exact mul_le_mul hδ hΛ (norm_nonneg _) (by positivity)
  -- (ii) the grid difference against the flow
  have hii : ‖⟪DeltaGL sys L hL hθ m κ (regCoeff m (U s (molecularH2StateMap eta g u₀))), φ⟫_ℂ‖ ≤
      Zg * (formAP g s₀ m * (t₄ * (sys.maxMass * Wφ) + τφ * M₀) + 52 * m * (τφ * t₄)) := by
    rw [← inner_conj_symm, RCLike.norm_conj]
    have hτu : ∀ r, ‖maskOp (High s₀ r) (regCoeff m
        (U s (molecularH2StateMap eta g u₀)))‖ ≤ t₄ := by
      intro r
      rw [← hu1 s]
      exact (norm_high_regCoeff_le hg s₀ r _).trans (tail_weaken hmm hRho₄ hCtU
        (tails_at_time_gL sys L H hKernel Hunit hL hθ hPeriodic hC U hgraph r (g * (s₀ : ℝ)) rho₄
          hK₄' hRho₄ hRhoScale₄ u₀ v₀ huv s (u s) (hu1 s) (hu2 s)).2)
    have hτv : ∀ r, ‖maskOp (High s₀ r) φ‖ ≤ τφ := fun r => hτ (s - t) r
    have hD0 := PlaneWaveGridG.Delta_formP (P := regParticlesOfG sys)
      (D := gLNucData sys hL hθ) hg hγ
      (by omega : 1 ≤ s₀) hs₀m hκ.gridKernel (regCoeff m (U s (molecularH2StateMap eta g u₀))) φ
      ht₄0 hτφ0 hτu hτv
    have hD : ‖⟪φ, DeltaGL sys L hL hθ m κ (regCoeff m (U s (molecularH2StateMap eta g u₀)))⟫_ℂ‖ ≤
        Zg * (formAP g s₀ m * (t₄ * ‖wMul (wTotPh g) φ‖ +
          τφ * ‖wMul (wTotPh g) (regCoeff m (U s (molecularH2StateMap eta g u₀)))‖) +
          52 * m * (τφ * t₄)) := hD0
    refine hD.trans ?_
    have haT : ‖wMul (wTotPh g) (regCoeff m (U s (molecularH2StateMap eta g u₀)))‖ ≤ M₀ := by
      rw [← hu1 s]
      exact (norm_wTotPh_regCoeff_stateMap_le g (u s)).trans hu_le
    have hA := formAP_nonneg g s₀ m
    have h1 : t₄ * ‖wMul (wTotPh g) φ‖ + τφ * ‖wMul (wTotPh g)
        (regCoeff m (U s (molecularH2StateMap eta g u₀)))‖ ≤
        t₄ * (sys.maxMass * Wφ) + τφ * M₀ :=
      add_le_add (mul_le_mul_of_nonneg_left hφT ht₄0) (mul_le_mul_of_nonneg_left haT hτφ0)
    have h2 := mul_le_mul_of_nonneg_left h1 hA
    have h3 := add_le_add h2 (le_refl (52 * (m : ℝ) * (τφ * t₄)))
    exact mul_le_mul_of_nonneg_left h3 hZg
  rw [inner_sub_left]
  exact (norm_sub_le _ _).trans (add_le_add hi hii)

end Grid

end FreeBoundary
