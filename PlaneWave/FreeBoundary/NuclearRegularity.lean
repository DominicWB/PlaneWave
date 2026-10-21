import PlaneWave.FreeBoundary.NuclearPotential

/-!
# Clamped nuclei, part 2: the regularity bridge with nuclei

`free_hamiltonian_regularity` of `PlaneWave.FreeBoundary.RegularityBridge` for any system: with the
nuclear Hardy functions `u/|x_i - P_ℓ|` (`hardy_nuc`), `‖V u‖² ≤ 8 M Q'² ‖u‖ ‖z‖` with
`Q' = Σ_{i<j} |q_i q_j| + Σ_{i,ℓ} |q_i Z_ℓ|`, and the same absorption.

* `chargeWeight`, `relConstN`, `norm_nucL2_le`;
* **`free_hamiltonian_regularity_nuc`**: the weak first and second derivatives, the pair and
  nuclear Hardy quotients, all bounded by `c₁′ (‖u‖ + ‖h‖)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- `Q' = Σ_{i<j} |q_i q_j| + Σ_{i,ℓ} |q_i Z_ℓ|`. -/
def chargeWeight (sys : CoulombSystem eta ν) : ℝ :=
  pairWeight sys.charge + ∑ i : Fin eta, ∑ l : ν, |sys.charge i * sys.nuclei.charge l|

lemma chargeWeight_nonneg (sys : CoulombSystem eta ν) : 0 ≤ chargeWeight sys :=
  add_nonneg (pairWeight_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- The constant `c₁′ = 2M(3 + 8MQ'²)` of the regularity bridge with nuclei. -/
def relConstN (sys : CoulombSystem eta ν) : ℝ :=
  2 * sys.maxMass * (3 + 8 * sys.maxMass * chargeWeight sys ^ 2)

lemma norm_nucL2_le (q : Fin eta → ℝ) (Z : ν → ℝ) (F : Fin eta → ν → FreeL2 eta) :
    ‖nucL2 q Z F‖ ≤ ∑ i : Fin eta, ∑ l : ν, |q i * Z l| * ‖F i l‖ := by
  unfold nucL2
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- **The free-space regularity with clamped nuclei**: from `H_∞ u = h`, weak first and second
derivatives of `u`, the pair Hardy quotients `u/|x_i - x_j|`, `∂_a u/|x_i - x_j|` and the nuclear
ones `u/|x_i - P_ℓ|`, with `‖∂u‖`, `‖∂²u‖`, `‖u/r‖ ≤ c₁′ (‖u‖ + ‖h‖)`. -/
theorem free_hamiltonian_regularity_nuc (sys : CoulombSystem eta ν) (P : ν → E3)
    {f h : FreeL2 eta} (hH : HasFreeHamiltonian sys P f h) :
    ∃ (g : Fin eta × Fin 3 → FreeL2 eta) (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
      (Y : FiniteElectronPair eta → FreeL2 eta)
      (Z : FiniteElectronPair eta → Fin eta × Fin 3 → FreeL2 eta)
      (Yn : Fin eta → ν → FreeL2 eta),
      HasWeakGrad f g ∧ (∀ b, HasWeakGrad (g b) (g2 b)) ∧
      (∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * f r) ∧
      (∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * g a r) ∧
      (∀ i l, ∀ᵐ r, Yn i l r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * f r) ∧
      (∀ a, ‖g a‖ ≤ relConstN sys * (‖f‖ + ‖h‖)) ∧
      (∀ a b, ‖g2 a b‖ ≤ relConstN sys * (‖f‖ + ‖h‖)) ∧
      (∀ p, ‖Y p‖ ≤ relConstN sys * (‖f‖ + ‖h‖)) ∧
      (∀ i l, ‖Yn i l‖ ≤ relConstN sys * (‖f‖ + ‖h‖)) := by
  obtain ⟨v, hv, hK⟩ := hH
  obtain ⟨g, g2, hg, hg2, b1, b2⟩ := weak_kinetic_regularity (fun i => sys.mass_pos i) hK
  choose Y hY hYb using fun p => hardy_weak p hg
  choose Z hZ _ using fun p a => hardy_weak p (hg2 a)
  choose Yn hYn hYnb using fun i l => hardy_nuc i (P l) hg
  refine ⟨g, g2, Y, Z, Yn, hg, hg2, hY, hZ, hYn, ?_⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = sys.maxMass := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = chargeWeight sys := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := hMdef ▸ sys.one_le_maxMass
  have hM0 : 0 ≤ M := by linarith
  have hQ0 : 0 ≤ Q := hQdef ▸ chargeWeight_nonneg sys
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
  have hYn2 : ∀ i l, ‖Yn i l‖ ^ 2 ≤ 8 * M * ‖f‖ * ‖h - v‖ := fun i l => by
    have e1 := hYnb i l
    have e2 := hsub i
    linarith
  -- the potential: `‖v‖² ≤ 8 M Q² ‖f‖ ‖z‖`
  have hve : v = pairL2 sys.charge Y + nucL2 sys.charge sys.nuclei.charge Yn :=
    hv.unique (hasL2PointwisePotential_pair_nucL2 sys P hY hYn)
  have hv2 : ‖v‖ ^ 2 ≤ 8 * M * Q ^ 2 * ‖f‖ * ‖h - v‖ := by
    have hW0 : 0 ≤ 8 * M * ‖f‖ * ‖h - v‖ := by positivity
    have hYs : ∀ p, ‖Y p‖ ≤ Real.sqrt (8 * M * ‖f‖ * ‖h - v‖) := fun p =>
      (le_abs_self _).trans (Real.abs_le_sqrt (hY2 p))
    have hYns : ∀ i l, ‖Yn i l‖ ≤ Real.sqrt (8 * M * ‖f‖ * ‖h - v‖) := fun i l =>
      (le_abs_self _).trans (Real.abs_le_sqrt (hYn2 i l))
    have h1 : ‖v‖ ≤ Q * Real.sqrt (8 * M * ‖f‖ * ‖h - v‖) := by
      refine (le_of_eq (congrArg norm hve)).trans ((norm_add_le _ _).trans ?_)
      rw [hQdef, chargeWeight, add_mul, pairWeight, Finset.sum_mul, Finset.sum_mul]
      refine add_le_add ((norm_pairL2_le _ _).trans (Finset.sum_le_sum fun p _ =>
        mul_le_mul_of_nonneg_left (hYs p) (abs_nonneg _))) ((norm_nucL2_le _ _ _).trans ?_)
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hYns i l) (abs_nonneg _)
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
  have hc : relConstN sys * (‖f‖ + ‖h‖) = 2 * M * K₀ * T := by
    rw [relConstN, ← hMdef, ← hQdef, ← hK0def, ← hT]
  have hc0 : 0 ≤ 2 * M * K₀ * T := by positivity
  have hYgen : ∀ x : ℝ, 0 ≤ x → x ^ 2 ≤ 8 * M * ‖f‖ * ‖h - v‖ → x ≤ 2 * M * K₀ * T := by
    intro x hx0 hx
    refine le_of_pow_le_pow_left₀ two_ne_zero hc0 ?_
    have e1 := mul_le_mul_of_nonneg_left hfz (by positivity : (0 : ℝ) ≤ 8 * M)
    have e2 := mul_le_mul_of_nonneg_left hMK2 (by positivity : 0 ≤ 4 * M * K₀ * T ^ 2)
    calc x ^ 2 ≤ 8 * M * ‖f‖ * ‖h - v‖ := hx
      _ ≤ 8 * M * (K₀ * T ^ 2) := by linarith
      _ ≤ 4 * M * K₀ * T ^ 2 * (M * K₀) := by linarith
      _ = (2 * M * K₀ * T) ^ 2 := by ring
  refine ⟨fun a => ?_, fun a b => ?_, fun p => ?_, fun i l => ?_⟩
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
  · rw [hc]
    exact hYgen _ (norm_nonneg _) (hYn2 i l)

end

end FreeBoundary
