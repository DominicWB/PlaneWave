import PlaneWave.FreeBoundary.NuclearCommutator

/-!
# Clamped nuclei, part 5: the domain theorem with clamped nuclei

`cut_state_domain` (`PlaneWave.FreeBoundary.CutStateDomain`) for systems with clamped nuclei, for a
mass-weighted cutoff flat near the nuclei (`IsFlatNear`, radius `δ`). The transplant `φ = T(χ u)`
satisfies `H_L φ = h₀`, `H_L h₀ = h₁` with `‖φ‖ ≤ N`, `‖h₀‖ ≤ Λ' N`, `‖h₁‖ ≤ Λ'² N`
(`N = dataNorm`), where `Λ' = Λ + 3η Σ_{i,ℓ} |q_i Z_ℓ| D/δ²` adds the bounded nuclear part of the
double commutator. The nuclear Hardy functions `u/|x_i - P_ℓ|`, `∂_a u/|x_i - P_ℓ|` enter as
hypotheses only.

* `domConstN`, `norm_commHn_le`;
* **`cut_state_domain_nuc`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- The domain constant with clamped nuclei:
`Λ' = 1 + c₀ + 6 (1 + 3η)² D + (C Σ_{i<j} |q_i q_j| + 3η Σ_{i,ℓ} |q_i Z_ℓ| D/δ²)`. -/
noncomputable def domConstN (q : Fin eta → ℝ) (Zc : ν → ℝ) (c₀ D C δ : ℝ) : ℝ :=
  1 + c₀ + 6 * (1 + (Fintype.card (Fin eta × Fin 3) : ℝ)) ^ 2 * D +
    (pairWeight q * C + (Fintype.card (Fin eta × Fin 3) : ℝ) *
      ((∑ i : Fin eta, ∑ l : ν, |q i * Zc l|) * (D / δ ^ 2)))

section Norms

variable {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m)

lemma norm_commHn_le (hm : ∀ i, 1 ≤ m i) (q : Fin eta → ℝ) (Zc : ν → ℝ) (P : ν → E3) {δ : ℝ}
    (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ) (u h : FreeL2 eta)
    (g g' : Fin eta × Fin 3 → FreeL2 eta) (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
    (Y : FiniteElectronPair eta → FreeL2 eta) {β : ℝ}
    (hu : ‖u‖ ≤ β) (hh : ‖h‖ ≤ β) (hg : ∀ b, ‖g b‖ ≤ β) (hg' : ∀ b, ‖g' b‖ ≤ β)
    (hg2 : ∀ b c, ‖g2 b c‖ ≤ β) (hY : ∀ p, ‖Y p‖ ≤ β) :
    ‖commHn hL X q Zc P hδ hflat u h g g' g2 Y‖ ≤
      Fintype.card (Fin eta × Fin 3) * (1 / 2 *
        (X.D * β + Fintype.card (Fin eta × Fin 3) * (1 / 2 * (3 * X.D * β)))) +
      Fintype.card (Fin eta × Fin 3) * (1 *
        (X.D * β + Fintype.card (Fin eta × Fin 3) * (1 / 2 * (9 * X.D * β)))) +
      pairWeight q * X.C * β +
      Fintype.card (Fin eta × Fin 3) *
        (1 * ((∑ i : Fin eta, ∑ l : ν, |q i * Zc l|) * (X.D / δ ^ 2) * β)) := by
  have h1 := norm_commH_le hL X hm q u h g g' g2 Y hu hh hg hg' hg2 hY
  have hB0 : 0 ≤ (∑ i : Fin eta, ∑ l : ν, |q i * Zc l|) * (X.D / δ ^ 2) :=
    mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (div_nonneg X.D_nonneg (by positivity))
  have h2 := norm_sum_smul_le (β := (∑ i : Fin eta, ∑ l : ν, |q i * Zc l|) * (X.D / δ ^ 2) * β)
    (fun a => 2 * kc m a) (fun a => (X.nucBW q Zc P hδ hflat a).cutL2 hL u) (norm_two_kc_le hm)
    (fun a => ((X.nucBW q Zc P hδ hflat a).norm_cutL2_le hL u).trans
      (mul_le_mul_of_nonneg_left hu hB0))
  unfold commHn
  refine (norm_sub_le _ _).trans ?_
  linarith

end Norms

section Domain

theorem cut_state_domain_nuc (sys : CoulombSystem eta ν) {L R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ)
    {u h k : FreeL2 eta} {g g' : Fin eta × Fin 3 → FreeL2 eta}
    {g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta}
    {Y : FiniteElectronPair eta → FreeL2 eta}
    {Z : FiniteElectronPair eta → Fin eta × Fin 3 → FreeL2 eta}
    (hH : HasFreeHamiltonian sys P u h) (hH' : HasFreeHamiltonian sys P h k)
    (hg : HasWeakGrad u g) (hg' : HasWeakGrad h g') (hg2 : ∀ b, HasWeakGrad (g b) (g2 b))
    (hY : ∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * u r)
    (hZ : ∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * g a r)
    {Yn : Fin eta → ν → FreeL2 eta} {Zn : Fin eta → ν → Fin eta × Fin 3 → FreeL2 eta}
    (hYn : ∀ i l, ∀ᵐ r, Yn i l r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * u r)
    (hZn : ∀ i l a, ∀ᵐ r, Zn i l a r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * g a r)
    {c₀ : ℝ} (hc₀ : ‖zeroModeShift sys L θ‖ ≤ c₀) :
    ∃ h₀ h₁ : MolecularPositionL2 eta,
      HasGLHamiltonian sys L θ (X.toCutoff.chiW.cutL2 hL u) h₀ ∧
      HasGLHamiltonian sys L θ h₀ h₁ ∧
      ‖X.toCutoff.chiW.cutL2 hL u‖ ≤ dataNorm u h k g g' g2 Y ∧
      ‖h₀‖ ≤ domConstN sys.charge sys.nuclei.charge c₀ X.D X.C δ * dataNorm u h k g g' g2 Y ∧
      ‖h₁‖ ≤ domConstN sys.charge sys.nuclei.charge c₀ X.D X.C δ ^ 2 *
        dataNorm u h k g g' g2 Y := by
  set C₀ := zeroModeShift sys L θ with hC₀def
  set N := dataNorm u h k g g' g2 Y with hNdef
  -- the relations
  have hdom0 := transplant_hasGLHamiltonian sys hL hR0 hρ hone P hP hpos X.toCutoff hret hH hg
  have hTh := transplant_hasGLHamiltonian sys hL hR0 hρ hone P hP hpos X.toCutoff hret hH' hg'
  have hK : HasFreeWeakKinetic sys.mass u
      (h - (pairL2 sys.charge Y + nucL2 sys.charge sys.nuclei.charge Yn)) := by
    obtain ⟨v, hv, hKv⟩ := hH
    have e := hv.unique (hasL2PointwisePotential_pair_nucL2 sys P hY hYn)
    rw [← e]
    exact hKv
  have hC := commT_hasGLHamiltonian_nuc sys hL hR0 hρ hone P hP hpos X hret hδ hflat hK hg hg'
    hg2 hY hZ hYn hZn
  have hdom1 := (hTh.sub sys (hdom0.smul sys C₀)).add sys hC
  refine ⟨_, _, hdom0, hdom1, ?_⟩
  -- the bounds
  have hm := sys.one_le_mass
  have hN := dataNorm_nonneg u h k g g' g2 Y
  have hc0 : 0 ≤ c₀ := (norm_nonneg _).trans hc₀
  have hD := X.D_nonneg
  have bu := le_dataNorm_u u h k g g' g2 Y
  have bh := le_dataNorm_h u h k g g' g2 Y
  have bk := le_dataNorm_k u h k g g' g2 Y
  have bg := le_dataNorm_g u h k g g' g2 Y
  have bg' := le_dataNorm_g' u h k g g' g2 Y
  have bg2 := le_dataNorm_g2 u h k g g' g2 Y
  have bY := le_dataNorm_Y u h k g g' g2 Y
  have hchi : ∀ f : FreeL2 eta, ‖f‖ ≤ N → ‖X.toCutoff.chiW.cutL2 hL f‖ ≤ N := fun f hf => by
    have := X.toCutoff.chiW.norm_cutL2_le hL f
    have e : X.toCutoff.chiW.B = 1 := rfl
    rw [e, one_mul] at this
    exact this.trans hf
  have nφ := hchi u bu
  have nTh := hchi h bh
  have nTk := hchi k bk
  have nCu := X.norm_commT_le' hL hm u g bu bg
  have nCh := X.norm_commT_le' hL hm h g' bh bg'
  set W := (∑ i : Fin eta, ∑ l : ν, |sys.charge i * sys.nuclei.charge l|) * (X.D / δ ^ 2) with hW
  have hW0 : 0 ≤ W := mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    abs_nonneg _) (div_nonneg X.D_nonneg (by positivity))
  have nH := norm_commHn_le hL X hm sys.charge sys.nuclei.charge P hδ hflat u h g g' g2 Y bu bh bg
    bg' bg2 bY
  have hn : (0 : ℝ) ≤ Fintype.card (Fin eta × Fin 3) := Nat.cast_nonneg _
  have hF : 0 ≤ pairWeight sys.charge * X.C + (Fintype.card (Fin eta × Fin 3) : ℝ) * W :=
    add_nonneg (mul_nonneg (pairWeight_nonneg _) X.C_nonneg) (mul_nonneg hn hW0)
  obtain ⟨k1, k2⟩ := domConst_bounds hn hc0 hD hF hN
  have sm : ∀ x : MolecularPositionL2 eta, ∀ b : ℝ, ‖x‖ ≤ b → ‖C₀ • x‖ ≤ c₀ * b := fun x b hx => by
    rw [norm_smul]
    exact mul_le_mul hc₀ hx (norm_nonneg _) hc0
  -- `‖h₀‖`
  have n0 : ‖X.toCutoff.chiW.cutL2 hL h - C₀ • X.toCutoff.chiW.cutL2 hL u +
      X.toCutoff.commT hL sys.mass u g‖ ≤
      (1 + c₀ + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D))) * N := by
    have t1 := norm_add_le (X.toCutoff.chiW.cutL2 hL h - C₀ • X.toCutoff.chiW.cutL2 hL u)
      (X.toCutoff.commT hL sys.mass u g)
    have t2 := norm_sub_le (X.toCutoff.chiW.cutL2 hL h) (C₀ • X.toCutoff.chiW.cutL2 hL u)
    have t3 := sm _ _ nφ
    have e : (1 + c₀ + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D))) * N =
        N + c₀ * N + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D * N)) := by ring
    rw [e]
    linarith
  refine ⟨nφ, n0.trans (by simpa [domConstN, hW] using k1), ?_⟩
  -- `‖h₁‖`
  set h₀ := X.toCutoff.chiW.cutL2 hL h - C₀ • X.toCutoff.chiW.cutL2 hL u +
      X.toCutoff.commT hL sys.mass u g with hh₀
  have t1 := norm_add_le (X.toCutoff.chiW.cutL2 hL k - C₀ • X.toCutoff.chiW.cutL2 hL h +
    X.toCutoff.commT hL sys.mass h g' - C₀ • h₀)
    (commHn hL X sys.charge sys.nuclei.charge P hδ hflat u h g g' g2 Y -
      C₀ • X.toCutoff.commT hL sys.mass u g)
  have t2 := norm_sub_le (X.toCutoff.chiW.cutL2 hL k - C₀ • X.toCutoff.chiW.cutL2 hL h +
    X.toCutoff.commT hL sys.mass h g') (C₀ • h₀)
  have t3 := norm_add_le (X.toCutoff.chiW.cutL2 hL k - C₀ • X.toCutoff.chiW.cutL2 hL h)
    (X.toCutoff.commT hL sys.mass h g')
  have t4 := norm_sub_le (X.toCutoff.chiW.cutL2 hL k) (C₀ • X.toCutoff.chiW.cutL2 hL h)
  have t5 := norm_sub_le (commHn hL X sys.charge sys.nuclei.charge P hδ hflat u h g g' g2 Y)
    (C₀ • X.toCutoff.commT hL sys.mass u g)
  have s1 := sm _ _ nTh
  have s2 := sm _ _ n0
  have s3 := sm _ _ nCu
  have e : domConstN sys.charge sys.nuclei.charge c₀ X.D X.C δ ^ 2 * N =
      (1 + c₀ + 6 * (1 + (Fintype.card (Fin eta × Fin 3) : ℝ)) ^ 2 * X.D +
        (pairWeight sys.charge * X.C + (Fintype.card (Fin eta × Fin 3) : ℝ) * W)) ^ 2 * N := rfl
  rw [e]
  refine le_trans ?_ k2
  have e2 : (1 + c₀ + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D)) +
      c₀ * (1 + c₀ + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D))) +
      ((Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (X.D + (Fintype.card (Fin eta × Fin 3) : ℝ) *
        (1 / 2 * (3 * X.D)))) + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 * (X.D +
          (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (9 * X.D)))) +
        (pairWeight sys.charge * X.C + (Fintype.card (Fin eta × Fin 3) : ℝ) * W)) +
      c₀ * ((Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D)))) * N =
      N + c₀ * N + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D * N)) +
        c₀ * ((1 + c₀ + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D))) * N) +
        ((Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (X.D * N +
          (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D * N)))) +
          (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 * (X.D * N +
            (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (9 * X.D * N)))) +
          pairWeight sys.charge * X.C * N + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 * (W * N))) +
        c₀ * ((Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D * N))) := by ring
  rw [e2]
  linarith

end Domain

end FreeBoundary
