import PlaneWave.FreeBoundary.HardyInequality

/-!
# Free-space regularity, part 4: the regularity bridge

For a system without clamped nuclei, the two free-space Hamiltonian relations `H_∞ u = h` and
`H_∞ h = k` supply the weak derivatives and Hardy quotients that `cut_state_domain` takes as
hypotheses, and bound the data norm by `C_sys (‖u‖ + ‖h‖ + ‖k‖)`.

For `H_∞ f = h` with `V f = v`, `z = h - v` is the weak kinetic image of `f`. Weak kinetic
regularity gives `Σ_a ‖∂_a f‖² ≤ 2 M ‖f‖ ‖z‖` and `Σ_{a,b} ‖∂_a ∂_b f‖² ≤ 4 M² ‖z‖²` (`M` the
largest mass), Hardy's inequality gives `‖f / r_{ij}‖² ≤ 8 M ‖f‖ ‖z‖`, so
`‖v‖² ≤ 8 M Q² ‖f‖ ‖z‖` (`Q = Σ_{i<j} |q_i q_j|`), and absorbing,
`‖z‖ ≤ 2 ‖h‖ + 8 M Q² ‖f‖`. The constants depend only on the masses, the charges and the number of
particles, not on the cell.

* `HasWeakGrad.unique`: weak gradients are unique;
* `free_hamiltonian_regularity`: the witnesses and bounds from one relation;
* `regConst`, **`free_data_regularity`**: the witnesses for `cut_state_domain`, with
  `dataNorm ≤ regConst · (‖u‖ + ‖h‖ + ‖k‖)`;
* **`cut_state_domain_reg`**: `cut_state_domain` from the two relations;
* **`free_dyn_grid_nbo_reg`**: `prop:free-dyn` (`free_dyn_grid_nbo_cell`) from the Hamiltonian
  relations, with the constants in terms of `‖ψ₀‖ + ‖H_∞ ψ₀‖ + ‖H_∞² ψ₀‖`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLgamma_pos gLref gLNucData regParticlesOfG gLzU gLzU_nonneg gLAU
  gLGridCoupling)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Uniqueness of weak gradients -/

section Unique

/-- **Weak gradients are unique**. -/
lemma HasWeakGrad.unique {f : FreeL2 eta} {g g' : Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad f g) (hg' : HasWeakGrad f g') : g = g' := by
  funext a
  have he : ∀ n, mollN n (g a) = mollN n (g' a) := fun n => by
    refine Lp.ext ?_
    filter_upwards [mollN_ae n (g a), mollN_ae n (g' a)] with x h1 h2
    rw [h1, h2, ← moll_dirD_eq hg (hasCompactSupport_rhoN n) (contDiff_rhoN n) a x,
      moll_dirD_eq hg' (hasCompactSupport_rhoN n) (contDiff_rhoN n) a x]
  exact tendsto_nhds_unique (tendsto_mollN (g a))
    ((tendsto_mollN (g' a)).congr fun n => (he n).symm)

end Unique

/-! ## One Hamiltonian relation -/

section Relation

/-- Absorption: `s ≤ a + w` and `w² ≤ B s` give `s ≤ 2a + B`. -/
lemma absorb_le {s a w B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (h1 : s ≤ a + w)
    (h2 : w ^ 2 ≤ B * s) : s ≤ 2 * a + B := by
  refine not_lt.mp fun hcon => ?_
  have h4 : 0 ≤ s - a := by linarith
  have h3 : s - a ≤ w := by linarith
  have h5 : (s - a) ^ 2 ≤ B * s := (pow_le_pow_left₀ h4 h3 2).trans h2
  have hd : 0 < s - (2 * a + B) := sub_pos.mpr hcon
  nlinarith [mul_pos hd hd, mul_nonneg ha hd.le, mul_nonneg hB hd.le, sq_nonneg a]

lemma norm_pairL2_le (q : Fin eta → ℝ) (F : FiniteElectronPair eta → FreeL2 eta) :
    ‖pairL2 q F‖ ≤ ∑ p : FiniteElectronPair eta, |q p.1.1 * q p.1.2| * ‖F p‖ := by
  unfold pairL2
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- The constant `c₁ = 2 M (3 + 8 M Q²)` of one Hamiltonian relation (`M` the largest mass,
`Q = Σ_{i<j} |q_i q_j|`). -/
noncomputable def relConst (sys : CoulombSystem eta ν) : ℝ :=
  2 * sys.maxMass * (3 + 8 * sys.maxMass * pairWeight sys.charge ^ 2)

lemma relConst_nonneg (sys : CoulombSystem eta ν) : 0 ≤ relConst sys := by
  have := sys.one_le_maxMass
  have := pairWeight_nonneg sys.charge
  unfold relConst
  positivity

/-- **Regularity from one Hamiltonian relation**: if `H_∞ f = h` (no clamped nuclei), then `f` has
weak first and second derivatives and Hardy quotients `f / r_{ij}`, `∂_a f / r_{ij}` in `L²`, and
the derivatives and the quotients `f / r_{ij}` are bounded by `c₁ (‖f‖ + ‖h‖)`. -/
theorem free_hamiltonian_regularity [IsEmpty ν] (sys : CoulombSystem eta ν) (P : ν → E3)
    {f h : FreeL2 eta} (hH : HasFreeHamiltonian sys P f h) :
    ∃ (g : Fin eta × Fin 3 → FreeL2 eta) (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
      (Y : FiniteElectronPair eta → FreeL2 eta)
      (Z : FiniteElectronPair eta → Fin eta × Fin 3 → FreeL2 eta),
      HasWeakGrad f g ∧ (∀ b, HasWeakGrad (g b) (g2 b)) ∧
      (∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * f r) ∧
      (∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * g a r) ∧
      (∀ a, ‖g a‖ ≤ relConst sys * (‖f‖ + ‖h‖)) ∧
      (∀ a b, ‖g2 a b‖ ≤ relConst sys * (‖f‖ + ‖h‖)) ∧
      (∀ p, ‖Y p‖ ≤ relConst sys * (‖f‖ + ‖h‖)) := by
  obtain ⟨v, hv, hK⟩ := hH
  obtain ⟨g, g2, hg, hg2, b1, b2⟩ := weak_kinetic_regularity (fun i => sys.mass_pos i) hK
  choose Y hY hYb using fun p => hardy_weak p hg
  choose Z hZ _ using fun p a => hardy_weak p (hg2 a)
  refine ⟨g, g2, Y, Z, hg, hg2, hY, hZ, ?_⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = sys.maxMass := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = pairWeight sys.charge := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := hMdef ▸ sys.one_le_maxMass
  have hM0 : 0 ≤ M := by linarith
  have hQ0 : 0 ≤ Q := hQdef ▸ pairWeight_nonneg _
  have hf0 := norm_nonneg f
  have hh0 := norm_nonneg h
  have hz0 := norm_nonneg (h - v)
  -- first derivatives: `Σ_a ‖g_a‖² ≤ 2 M ‖f‖ ‖z‖`
  have hmi : ∀ i, 1 ≤ M * (sys.mass i)⁻¹ := fun i => by
    rw [← div_eq_mul_inv, le_div_iff₀ (sys.mass_pos i), one_mul, hMdef]
    exact sys.mass_le_maxMass i
  have hS1w : ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ * ‖g a‖ ^ 2 ≤ 2 * ‖f‖ * ‖h - v‖ := by
    have h0 : 0 ≤ ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ * ‖g a‖ ^ 2 :=
      Finset.sum_nonneg fun a _ => mul_nonneg (inv_nonneg.mpr (sys.mass_pos _).le) (sq_nonneg _)
    refine (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).mp ?_
    calc _ ≤ 4 * ‖f‖ ^ 2 * ‖h - v‖ ^ 2 := b1
      _ = (2 * ‖f‖ * ‖h - v‖) ^ 2 := by ring
  have hS1 : ∑ a : Fin eta × Fin 3, ‖g a‖ ^ 2 ≤ M * (2 * ‖f‖ * ‖h - v‖) := by
    calc ∑ a : Fin eta × Fin 3, ‖g a‖ ^ 2
        ≤ ∑ a : Fin eta × Fin 3, M * ((sys.mass a.1)⁻¹ * ‖g a‖ ^ 2) :=
          Finset.sum_le_sum fun a _ => by
            have := mul_le_mul_of_nonneg_right (hmi a.1) (sq_nonneg ‖g a‖)
            linarith
      _ = M * ∑ a : Fin eta × Fin 3, (sys.mass a.1)⁻¹ * ‖g a‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ M * (2 * ‖f‖ * ‖h - v‖) := mul_le_mul_of_nonneg_left hS1w hM0
  -- second derivatives: `Σ_{a,b} ‖g2_{ab}‖² ≤ 4 M² ‖z‖²`
  have hS2 : ∑ a : Fin eta × Fin 3, ∑ b : Fin eta × Fin 3, ‖g2 a b‖ ^ 2 ≤
      M ^ 2 * (4 * ‖h - v‖ ^ 2) := by
    rw [← b2, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have e := mul_le_mul (hmi a.1) (hmi b.1) zero_le_one (by linarith [hmi a.1])
    have := mul_le_mul_of_nonneg_right e (sq_nonneg ‖g2 a b‖)
    linarith
  -- the Hardy quotients: `‖Y_p‖² ≤ 8 M ‖f‖ ‖z‖`
  have hsub : ∀ i : Fin eta, ∑ c : Fin 3, ‖g (i, c)‖ ^ 2 ≤ ∑ a : Fin eta × Fin 3, ‖g a‖ ^ 2 := by
    intro i
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (f := fun j => ∑ c : Fin 3, ‖g (j, c)‖ ^ 2)
      (fun j _ => Finset.sum_nonneg fun c _ => sq_nonneg _) (Finset.mem_univ i)
  have hY2 : ∀ p, ‖Y p‖ ^ 2 ≤ 8 * M * ‖f‖ * ‖h - v‖ := fun p => by
    have e1 := hYb p
    have e2 := hsub p.1.1
    linarith
  -- the potential: `‖v‖² ≤ 8 M Q² ‖f‖ ‖z‖`
  have hve : v = pairL2 sys.charge Y := hv.unique (hasL2PointwisePotential_pairL2 sys P hY)
  have hv2 : ‖v‖ ^ 2 ≤ 8 * M * Q ^ 2 * ‖f‖ * ‖h - v‖ := by
    have hW0 : 0 ≤ 8 * M * ‖f‖ * ‖h - v‖ := by positivity
    have hYs : ∀ p, ‖Y p‖ ≤ Real.sqrt (8 * M * ‖f‖ * ‖h - v‖) := fun p =>
      (le_abs_self _).trans (Real.abs_le_sqrt (hY2 p))
    have h1 : ‖v‖ ≤ Q * Real.sqrt (8 * M * ‖f‖ * ‖h - v‖) := by
      refine (le_of_eq (congrArg norm hve)).trans ((norm_pairL2_le _ _).trans ?_)
      rw [hQdef, pairWeight, Finset.sum_mul]
      exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hYs p) (abs_nonneg _)
    calc ‖v‖ ^ 2 ≤ (Q * Real.sqrt (8 * M * ‖f‖ * ‖h - v‖)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = 8 * M * Q ^ 2 * ‖f‖ * ‖h - v‖ := by
          rw [mul_pow, Real.sq_sqrt hW0]
          ring
  -- absorption: `‖z‖ ≤ 2 ‖h‖ + 8 M Q² ‖f‖`
  have hzt : ‖h - v‖ ≤ ‖h‖ + ‖v‖ := norm_sub_le h v
  have hZf : ‖h - v‖ ≤ 2 * ‖h‖ + 8 * M * Q ^ 2 * ‖f‖ :=
    absorb_le hh0 (by positivity) hzt (by
      calc ‖v‖ ^ 2 ≤ 8 * M * Q ^ 2 * ‖f‖ * ‖h - v‖ := hv2
        _ = 8 * M * Q ^ 2 * ‖f‖ * ‖h - v‖ := rfl)
  -- the bounds
  obtain ⟨T, hT⟩ : ∃ T, T = ‖f‖ + ‖h‖ := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  obtain ⟨K₀, hK0def⟩ : ∃ K₀, K₀ = 3 + 8 * M * Q ^ 2 := ⟨_, rfl⟩
  have hK₀ : 3 ≤ K₀ := by
    have : 0 ≤ 8 * M * Q ^ 2 := by positivity
    linarith
  have hzK : ‖h - v‖ ≤ K₀ * T := by
    have e1 : 8 * M * Q ^ 2 * ‖f‖ ≤ 8 * M * Q ^ 2 * T :=
      mul_le_mul_of_nonneg_left (by rw [hT]; linarith) (by positivity)
    have e3 : K₀ * T = 3 * T + 8 * M * Q ^ 2 * T := by rw [hK0def]; ring
    have e4 : ‖h‖ ≤ T := by rw [hT]; linarith
    linarith
  have hMK3 : 1 * 3 ≤ M * K₀ := mul_le_mul hM1 hK₀ (by norm_num) hM0
  have hMK : 1 ≤ 2 * M * K₀ := by linarith
  have hMK2 : 2 ≤ M * K₀ := by linarith
  have hfz : ‖f‖ * ‖h - v‖ ≤ K₀ * T ^ 2 := by
    calc ‖f‖ * ‖h - v‖ ≤ T * (K₀ * T) := mul_le_mul (by rw [hT]; linarith) hzK hz0 hT0
      _ = K₀ * T ^ 2 := by ring
  have hc : relConst sys * (‖f‖ + ‖h‖) = 2 * M * K₀ * T := by
    rw [relConst, ← hMdef, ← hQdef, ← hK0def, ← hT]
  have hc0 : 0 ≤ 2 * M * K₀ * T := by positivity
  refine ⟨fun a => ?_, fun a b => ?_, fun p => ?_⟩
  · rw [hc]
    refine le_of_pow_le_pow_left₀ two_ne_zero hc0 ?_
    have h1 : ‖g a‖ ^ 2 ≤ ∑ a : Fin eta × Fin 3, ‖g a‖ ^ 2 :=
      Finset.single_le_sum (f := fun a => ‖g a‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ a)
    have e1 := mul_le_mul_of_nonneg_left hfz (by positivity : (0 : ℝ) ≤ 2 * M)
    have e2 := mul_le_mul_of_nonneg_right hMK (by positivity : 0 ≤ 2 * M * K₀ * T ^ 2)
    calc ‖g a‖ ^ 2 ≤ M * (2 * ‖f‖ * ‖h - v‖) := h1.trans hS1
      _ ≤ 2 * M * K₀ * T ^ 2 := by linarith
      _ ≤ (2 * M * K₀) * (2 * M * K₀ * T ^ 2) := by linarith
      _ = (2 * M * K₀ * T) ^ 2 := by ring
  · rw [hc]
    refine le_of_pow_le_pow_left₀ two_ne_zero hc0 ?_
    have h1 : ‖g2 a b‖ ^ 2 ≤ ∑ a : Fin eta × Fin 3, ∑ b : Fin eta × Fin 3, ‖g2 a b‖ ^ 2 := by
      refine (Finset.single_le_sum (f := fun b => ‖g2 a b‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ b)).trans ?_
      exact Finset.single_le_sum (f := fun a => ∑ b : Fin eta × Fin 3, ‖g2 a b‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ a)
    have h2 := pow_le_pow_left₀ hz0 hzK 2
    calc ‖g2 a b‖ ^ 2 ≤ M ^ 2 * (4 * ‖h - v‖ ^ 2) := h1.trans hS2
      _ ≤ M ^ 2 * (4 * (K₀ * T) ^ 2) := by gcongr
      _ = (2 * M * K₀ * T) ^ 2 := by ring
  · rw [hc]
    refine le_of_pow_le_pow_left₀ two_ne_zero hc0 ?_
    have e1 := mul_le_mul_of_nonneg_left hfz (by positivity : (0 : ℝ) ≤ 8 * M)
    have e2 := mul_le_mul_of_nonneg_left hMK2 (by positivity : 0 ≤ 4 * M * K₀ * T ^ 2)
    calc ‖Y p‖ ^ 2 ≤ 8 * M * ‖f‖ * ‖h - v‖ := hY2 p
      _ ≤ 8 * M * (K₀ * T ^ 2) := by linarith
      _ ≤ 4 * M * K₀ * T ^ 2 * (M * K₀) := by linarith
      _ = (2 * M * K₀ * T) ^ 2 := by ring

end Relation

/-! ## The data of `cut_state_domain` -/

section Data

/-- The constant `C_sys = 1 + c₁ (2n + n² + n_p)` of the regularity bridge (`n = 3η` coordinates,
`n_p` pairs). -/
noncomputable def regConst (sys : CoulombSystem eta ν) : ℝ :=
  1 + relConst sys * (2 * (Fintype.card (Fin eta × Fin 3) : ℝ) +
    (Fintype.card (Fin eta × Fin 3) : ℝ) ^ 2 + (Fintype.card (FiniteElectronPair eta) : ℝ))

lemma one_le_regConst (sys : CoulombSystem eta ν) : 1 ≤ regConst sys := by
  have := relConst_nonneg sys
  unfold regConst
  have : 0 ≤ relConst sys * (2 * (Fintype.card (Fin eta × Fin 3) : ℝ) +
      (Fintype.card (Fin eta × Fin 3) : ℝ) ^ 2 + (Fintype.card (FiniteElectronPair eta) : ℝ)) := by
    positivity
  linarith

/-- **The free-space regularity bridge**: from `H_∞ u = h` and `H_∞ h = k` (no clamped nuclei)
and the weak gradient `g` of `u`, the remaining data of `cut_state_domain` exist, with
`dataNorm ≤ C_sys (‖u‖ + ‖h‖ + ‖k‖)`. -/
theorem free_data_regularity [IsEmpty ν] (sys : CoulombSystem eta ν) (P : ν → E3)
    {u h k : FreeL2 eta} (hH : HasFreeHamiltonian sys P u h)
    (hH' : HasFreeHamiltonian sys P h k) {g : Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad u g) :
    ∃ (g' : Fin eta × Fin 3 → FreeL2 eta) (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
      (Y : FiniteElectronPair eta → FreeL2 eta)
      (Z : FiniteElectronPair eta → Fin eta × Fin 3 → FreeL2 eta),
      HasWeakGrad h g' ∧ (∀ b, HasWeakGrad (g b) (g2 b)) ∧
      (∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * u r) ∧
      (∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * g a r) ∧
      dataNorm u h k g g' g2 Y ≤ regConst sys * (‖u‖ + ‖h‖ + ‖k‖) := by
  obtain ⟨g₀, g2, Y, Z, hg₀, hg2, hY, hZ, bg, bg2, bY⟩ := free_hamiltonian_regularity sys P hH
  obtain ⟨g', _, _, _, hg', _, _, _, bg', _, _⟩ := free_hamiltonian_regularity sys P hH'
  obtain rfl : g₀ = g := hg₀.unique hg
  refine ⟨g', g2, Y, Z, hg', hg2, hY, hZ, ?_⟩
  set c := relConst sys with hcdef
  have hc0 : 0 ≤ c := relConst_nonneg sys
  set n := (Fintype.card (Fin eta × Fin 3) : ℝ) with hndef
  set np := (Fintype.card (FiniteElectronPair eta) : ℝ) with hnpdef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hnp0 : 0 ≤ np := Nat.cast_nonneg _
  have hu := norm_nonneg u
  have hh := norm_nonneg h
  have hk := norm_nonneg k
  set D := ‖u‖ + ‖h‖ + ‖k‖ with hD
  have hA : ‖u‖ + ‖h‖ ≤ D := by linarith
  have hB : ‖h‖ + ‖k‖ ≤ D := by linarith
  have s1 : ∑ a, ‖g₀ a‖ ≤ n * (c * (‖u‖ + ‖h‖)) := by
    calc ∑ a, ‖g₀ a‖ ≤ ∑ _a : Fin eta × Fin 3, c * (‖u‖ + ‖h‖) :=
          Finset.sum_le_sum fun a _ => bg a
      _ = n * (c * (‖u‖ + ‖h‖)) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have s2 : ∑ a, ‖g' a‖ ≤ n * (c * (‖h‖ + ‖k‖)) := by
    calc ∑ a, ‖g' a‖ ≤ ∑ _a : Fin eta × Fin 3, c * (‖h‖ + ‖k‖) :=
          Finset.sum_le_sum fun a _ => bg' a
      _ = n * (c * (‖h‖ + ‖k‖)) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have s3 : ∑ a, ∑ b, ‖g2 b a‖ ≤ n * (n * (c * (‖u‖ + ‖h‖))) := by
    calc ∑ a, ∑ b, ‖g2 b a‖ ≤ ∑ _a : Fin eta × Fin 3, ∑ _b : Fin eta × Fin 3,
          c * (‖u‖ + ‖h‖) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => bg2 b a
      _ = n * (n * (c * (‖u‖ + ‖h‖))) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
  have s4 : ∑ p, ‖Y p‖ ≤ np * (c * (‖u‖ + ‖h‖)) := by
    calc ∑ p, ‖Y p‖ ≤ ∑ _p : FiniteElectronPair eta, c * (‖u‖ + ‖h‖) :=
          Finset.sum_le_sum fun p _ => bY p
      _ = np * (c * (‖u‖ + ‖h‖)) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have t1 := mul_le_mul_of_nonneg_left hA (mul_nonneg hn0 hc0)
  have t2 := mul_le_mul_of_nonneg_left hB (mul_nonneg hn0 hc0)
  have t3 := mul_le_mul_of_nonneg_left hA (mul_nonneg (mul_nonneg hn0 hn0) hc0)
  have t4 := mul_le_mul_of_nonneg_left hA (mul_nonneg hnp0 hc0)
  have hreg : regConst sys * D = D + c * (2 * n + n ^ 2 + np) * D := by
    rw [regConst]
    ring
  unfold dataNorm
  rw [hreg]
  nlinarith

end Data

/-! ## The wrappers -/

section Wrappers

/-- **`cut_state_domain` from the Hamiltonian relations**: for `H_∞ u = h`, `H_∞ h = k` (no
clamped nuclei), the cut state `χ_L u` and its two `g_L` Hamiltonian images are bounded by
`Λ^j C_sys (‖u‖ + ‖h‖ + ‖k‖)`, `j = 0, 1, 2`. -/
theorem cut_state_domain_reg [IsEmpty ν] (sys : CoulombSystem eta ν) {L R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {u h k : FreeL2 eta} (hH : HasFreeHamiltonian sys P u h)
    (hH' : HasFreeHamiltonian sys P h k)
    {c₀ : ℝ} (hc₀ : ‖zeroModeShift sys L θ‖ ≤ c₀) :
    ∃ h₀ h₁ : MolecularPositionL2 eta,
      HasGLHamiltonian sys L θ (X.toCutoff.chiW.cutL2 hL u) h₀ ∧
      HasGLHamiltonian sys L θ h₀ h₁ ∧
      ‖X.toCutoff.chiW.cutL2 hL u‖ ≤ regConst sys * (‖u‖ + ‖h‖ + ‖k‖) ∧
      ‖h₀‖ ≤ domConst sys.charge c₀ X.D X.C * (regConst sys * (‖u‖ + ‖h‖ + ‖k‖)) ∧
      ‖h₁‖ ≤ domConst sys.charge c₀ X.D X.C ^ 2 * (regConst sys * (‖u‖ + ‖h‖ + ‖k‖)) := by
  obtain ⟨g, _, _, _, hg, _⟩ := free_hamiltonian_regularity sys P hH
  obtain ⟨g', g2, Y, Z, hg', hg2, hY, hZ, hN⟩ := free_data_regularity sys P hH hH' hg
  obtain ⟨h₀, h₁, hd0, hd1, n0, n1, n2⟩ := cut_state_domain sys hL hR0 hρ hone P hP hpos X hret
    hH hH' hg hg' hg2 hY hZ hc₀
  have hΛ : 0 ≤ domConst sys.charge c₀ X.D X.C := by
    have := one_le_domConst sys.charge ((norm_nonneg _).trans hc₀) X.D_nonneg X.C_nonneg
    linarith
  exact ⟨h₀, h₁, hd0, hd1, n0.trans hN, n1.trans (mul_le_mul_of_nonneg_left hN hΛ),
    n2.trans (mul_le_mul_of_nonneg_left hN (pow_nonneg hΛ 2))⟩

/-- **`prop:free-dyn` from the Hamiltonian relations** (`free_dyn_grid_nbo_cell` without the
derivative and quotient witnesses): the data norm is replaced by
`C_sys (‖ψ₀‖ + ‖H_∞ ψ₀‖ + ‖H_∞² ψ₀‖)`. -/
theorem free_dyn_grid_nbo_reg [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
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
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
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
      let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
      let φ₀ := X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let N := regConst sys * (‖ψ 0‖ + ‖H 0‖ + ‖k‖)
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
  obtain ⟨g', g2, Y, Z, hg', hg2, hY, hZ, hN⟩ :=
    free_data_regularity sys P (hHam 0) hH1 (hgrad 0)
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_grid_nbo_cell sys hL2 hθ hR
    hR0 hρ hone P hP hpos X hret hDbar hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0
    hleak1 hH1 hg' hg2 hY hZ a hf0 hf1 F hFf hfR hRL m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ φ₀ N Λ A K ψg
  set N₀ := dataNorm (ψ 0) (H 0) k (grad 0) g' g2 Y with hN₀
  set A₀ := gridConstsSharp_gLU sys (tv R θ) molecularCanonicalUnitHardyConstant
    (obsMomC (ftDecay F)) (obsMomC (ftDecay F)) (obsMomD2 (ftDecay F)) (obsMomD4 (ftDecay F))
    N₀ (Λ * N₀) (Λ * N₀) (Λ ^ 2 * N₀) with hA₀
  have hb : ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
      ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) *
        ((Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2) * ε * t) +
        ((A₀.1 + (A₀.2.2 * Real.sqrt 3 ^ 5 + N₀ ^ 2) * obsTailC (ftDecay F) 5) * (1 / K) ^ 5 +
          A₀.2.1 * t * (1 / K) ^ 3) := hbound
  refine hb.trans ?_
  -- monotonicity in the data norm
  have hN0 : 0 ≤ N₀ := dataNorm_nonneg _ _ _ _ _ _ _
  have hc0 : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have hD0 : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  have hC0 : 0 ≤ Cbar := X.C_nonneg.trans hCbar
  have hΛ1 : 1 ≤ Λ := one_le_domConst sys.charge hc0 hD0 hC0
  have hΛ0 : 0 ≤ Λ := by linarith
  have e0 : N₀ ≤ N := hN
  have e1 : Λ * N₀ ≤ Λ * N := mul_le_mul_of_nonneg_left hN hΛ0
  have e2 : Λ ^ 2 * N₀ ≤ Λ ^ 2 * N := mul_le_mul_of_nonneg_left hN (pow_nonneg hΛ0 2)
  have hV := hθ.tv_nonneg
  have hHu : 0 ≤ molecularCanonicalUnitHardyConstant := by
    unfold molecularCanonicalUnitHardyConstant
    positivity
  have hB : ∀ n, 0 ≤ ftDecay F n := ftDecay_nonneg F
  have hC6 : 0 ≤ obsMomC (ftDecay F) := by unfold obsMomC; have := hB 6; positivity
  have hD2 : 0 ≤ obsMomD2 (ftDecay F) := by unfold obsMomD2; have := hB 8; positivity
  have hD4 : 0 ≤ obsMomD4 (ftDecay F) := by unfold obsMomD4; have := hB 10; positivity
  have hΛN : 0 ≤ Λ * N₀ := mul_nonneg hΛ0 hN0
  have hΛ2N : 0 ≤ Λ ^ 2 * N₀ := mul_nonneg (pow_nonneg hΛ0 2) hN0
  obtain ⟨m1, m2, m3⟩ := gridConstsSharp_gLU_mono_data sys hV hHu hC6 hC6 hD2 hD4
    hN0 hΛN hΛN hΛ2N e0 e1 e1 e2
  have hT : 0 ≤ obsTailC (ftDecay F) 5 := by unfold obsTailC; have := hB 11; positivity
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hA3 : 0 ≤ A₀.2.2 := gridConstsSharp_gLU_nonneg_three sys hV hHu _ _ _ _ hN0 hΛN hΛN hΛ2N
  have ht' : 0 ≤ ‖ψ t‖ + ‖ψ 0‖ := by positivity
  gcongr

end Wrappers

end FreeBoundary
