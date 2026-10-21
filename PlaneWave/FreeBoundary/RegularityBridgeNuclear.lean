import PlaneWave.FreeBoundary.CutStateDomainNuclear

/-!
# Clamped nuclei, part 6: the domain theorem from the Hamiltonian relations

`free_data_regularity` and `cut_state_domain_reg` (`PlaneWave.FreeBoundary.RegularityBridge`) with
clamped nuclei: from `H_∞ u = h`, `H_∞ h = k` alone, the data of `cut_state_domain_nuc` exist (the
nuclear Hardy functions of `u` and `∂_a u` by `hardy_nuc`) with
`dataNorm ≤ C′_sys (‖u‖ + ‖h‖ + ‖k‖)`.

* `regConstN`, **`free_data_regularity_nuc`**;
* **`cut_state_domain_reg_nuc`**: `χ_L u` and its two `g_L` images bounded by
  `Λ'^j C′_sys (‖u‖ + ‖h‖ + ‖k‖)`, for a mass-weighted cutoff flat near the nuclei.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

lemma relConstN_nonneg (sys : CoulombSystem eta ν) : 0 ≤ relConstN sys := by
  have := sys.one_le_maxMass
  have := chargeWeight_nonneg sys
  unfold relConstN
  positivity

/-- `C′_sys = 1 + c₁′ (2n + n² + n_p)`. -/
noncomputable def regConstN (sys : CoulombSystem eta ν) : ℝ :=
  1 + relConstN sys * (2 * (Fintype.card (Fin eta × Fin 3) : ℝ) +
    (Fintype.card (Fin eta × Fin 3) : ℝ) ^ 2 + (Fintype.card (FiniteElectronPair eta) : ℝ))

lemma domConstN_nonneg (q : Fin eta → ℝ) (Zc : ν → ℝ) {c₀ D C δ : ℝ} (hc₀ : 0 ≤ c₀)
    (hD : 0 ≤ D) (hC : 0 ≤ C) : 0 ≤ domConstN q Zc c₀ D C δ := by
  unfold domConstN
  have h1 : 0 ≤ pairWeight q * C := mul_nonneg (pairWeight_nonneg q) hC
  have h2 : 0 ≤ (∑ i : Fin eta, ∑ l : ν, |q i * Zc l|) * (D / δ ^ 2) :=
    mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (div_nonneg hD (sq_nonneg _))
  have h3 : (0 : ℝ) ≤ (Fintype.card (Fin eta × Fin 3) : ℝ) := Nat.cast_nonneg _
  positivity

section Data

/-- **The data of the domain theorem with clamped nuclei**, from `H_∞ u = h`, `H_∞ h = k` and the
weak gradient `g` of `u`. -/
theorem free_data_regularity_nuc (sys : CoulombSystem eta ν) (P : ν → E3)
    {u h k : FreeL2 eta} (hH : HasFreeHamiltonian sys P u h)
    (hH' : HasFreeHamiltonian sys P h k) {g : Fin eta × Fin 3 → FreeL2 eta}
    (hg : HasWeakGrad u g) :
    ∃ (g' : Fin eta × Fin 3 → FreeL2 eta) (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
      (Y : FiniteElectronPair eta → FreeL2 eta)
      (Z : FiniteElectronPair eta → Fin eta × Fin 3 → FreeL2 eta)
      (Yn : Fin eta → ν → FreeL2 eta) (Zn : Fin eta → ν → Fin eta × Fin 3 → FreeL2 eta),
      HasWeakGrad h g' ∧ (∀ b, HasWeakGrad (g b) (g2 b)) ∧
      (∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * u r) ∧
      (∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * g a r) ∧
      (∀ i l, ∀ᵐ r, Yn i l r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * u r) ∧
      (∀ i l a, ∀ᵐ r, Zn i l a r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * g a r) ∧
      dataNorm u h k g g' g2 Y ≤ regConstN sys * (‖u‖ + ‖h‖ + ‖k‖) := by
  obtain ⟨g₀, g2, Y, Z, Yn, hg₀, hg2, hY, hZ, hYn, bg, bg2, bY, -⟩ :=
    free_hamiltonian_regularity_nuc sys P hH
  obtain ⟨g', _, _, _, _, hg', _, _, _, _, bg', _, _, _⟩ :=
    free_hamiltonian_regularity_nuc sys P hH'
  obtain rfl : g₀ = g := hg₀.unique hg
  choose Zn hZn _ using fun i l a => hardy_nuc i (P l) (hg2 a)
  refine ⟨g', g2, Y, Z, Yn, Zn, hg', hg2, hY, hZ, hYn, hZn, ?_⟩
  set c := relConstN sys with hcdef
  have hc0 : 0 ≤ c := relConstN_nonneg sys
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
  have hreg : regConstN sys * D = D + c * (2 * n + n ^ 2 + np) * D := by
    rw [regConstN]
    ring
  unfold dataNorm
  rw [hreg]
  nlinarith

end Data

/-- **The domain theorem with clamped nuclei from the Hamiltonian relations**: for `H_∞ u = h`,
`H_∞ h = k` and a mass-weighted cutoff in the retained region, flat near the nuclei, the cut state
`χ_L u` and its two `g_L` Hamiltonian images are bounded by `Λ'^j C′_sys (‖u‖ + ‖h‖ + ‖k‖)`. -/
theorem cut_state_domain_reg_nuc (sys : CoulombSystem eta ν) {L R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ)
    {u h k : FreeL2 eta} (hH : HasFreeHamiltonian sys P u h)
    (hH' : HasFreeHamiltonian sys P h k)
    {c₀ : ℝ} (hc₀ : ‖zeroModeShift sys L θ‖ ≤ c₀) :
    ∃ h₀ h₁ : MolecularPositionL2 eta,
      HasGLHamiltonian sys L θ (X.toCutoff.chiW.cutL2 hL u) h₀ ∧
      HasGLHamiltonian sys L θ h₀ h₁ ∧
      ‖X.toCutoff.chiW.cutL2 hL u‖ ≤ regConstN sys * (‖u‖ + ‖h‖ + ‖k‖) ∧
      ‖h₀‖ ≤ domConstN sys.charge sys.nuclei.charge c₀ X.D X.C δ *
        (regConstN sys * (‖u‖ + ‖h‖ + ‖k‖)) ∧
      ‖h₁‖ ≤ domConstN sys.charge sys.nuclei.charge c₀ X.D X.C δ ^ 2 *
        (regConstN sys * (‖u‖ + ‖h‖ + ‖k‖)) := by
  obtain ⟨g, _, _, _, _, hg, _⟩ := free_hamiltonian_regularity_nuc sys P hH
  obtain ⟨g', g2, Y, Z, Yn, Zn, hg', hg2, hY, hZ, hYn, hZn, hN⟩ :=
    free_data_regularity_nuc sys P hH hH' hg
  obtain ⟨h₀, h₁, hd0, hd1, n0, n1, n2⟩ := cut_state_domain_nuc sys hL hR0 hρ hone P hP hpos X
    hret hδ hflat hH hH' hg hg' hg2 hY hZ hYn hZn hc₀
  have hΛ := domConstN_nonneg sys.charge sys.nuclei.charge (δ := δ) ((norm_nonneg _).trans hc₀)
    X.D_nonneg X.C_nonneg
  exact ⟨h₀, h₁, hd0, hd1, n0.trans hN, n1.trans (mul_le_mul_of_nonneg_left hN hΛ),
    n2.trans (mul_le_mul_of_nonneg_left hN (pow_nonneg hΛ 2))⟩

end FreeBoundary
