import PlaneWave.FreeBoundary.NuclearSingularIdentity

/-!
# Clamped nuclei, part 4: the transplanted commutator in `D(H_L)`

`commT_hasGLHamiltonian` (`PlaneWave.FreeBoundary.CommutatorTransplant`) for systems with clamped
nuclei. For a cutoff flat near the nuclei, `V u = pairL2 Y + nucL2 Yn`,
`V g_a = pairL2 Z_a + nucL2 Zn_a`, and the double commutator has, besides the pair part
`Σ β_{ij} Y_{ij}`, the bounded nuclear part `Σ_a w_a ∂_aχ ∂_aV u` (`nucDW`).

* `nucDW`, `nucBW`: the bounded nuclear weight `∂_aχ ∂_aV` as a weight on the box;
* `IP_add`;
* **`freeId_comm_nuc`**: `⟨KΨ, [K, χ] u⟩` with the nuclear terms;
* `commHn`, `inner_commHn`, **`commT_hasGLHamiltonian_nuc`**:
  `H_L T([K, χ] u) = commHn - C₀ T([K, χ] u)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The nuclear weight -/

namespace DomCutoff

variable {L : ℝ} {m : Fin eta → ℝ} (X : DomCutoff eta L m) (q : Fin eta → ℝ) (Zc : ν → ℝ)
  (P : ν → E3)

/-- `∂_aχ ∂_aV` for the nuclear interaction `V`. -/
noncomputable def nucDW (a : Fin eta × Fin 3) (r : Rcfg eta) : ℝ :=
  dirD a X.χ r * nucDV q Zc P 0 a r

lemma measurable_nucDW (a : Fin eta × Fin 3) : Measurable (X.nucDW q Zc P a) := by
  have hc1 : Continuous (dirD a X.χ) := continuous_dirD X.smooth (by norm_num) a
  have hnd : ∀ i l, Measurable (ndir 0 i (P l) a) := by
    intro i l
    unfold ndir
    have hY : Continuous fun r : Rcfg eta => particleCLM i r - P l :=
      (particleCLM i).continuous.sub continuous_const
    have h2 : Continuous fun r : Rcfg eta => ‖particleCLM i r - P l‖ ^ 2 + (0 : ℝ) ^ 2 :=
      (hY.norm.pow 2).add continuous_const
    exact ((hY.inner continuous_const).neg.measurable).div (h2.mul h2.sqrt).measurable
  unfold nucDW nucDV
  exact hc1.measurable.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun l _ =>
    measurable_const.mul (hnd i l))

lemma nucDW_mem (a : Fin eta × Fin 3) {r : Rcfg eta} (hr : X.nucDW q Zc P a r ≠ 0) :
    r ∈ tsupport X.χ :=
  mem_tsupport_of_dirD_ne (a := a) fun h => hr (by rw [nucDW, h, zero_mul])

/-- The weight `∂_aχ ∂_aV` on the box, bounded by `Σ_{i,ℓ} |q_i Z_ℓ| D/δ²` for a cutoff flat near
the nuclei. -/
noncomputable def nucBW {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ)
    (a : Fin eta × Fin 3) : BoxWeight eta L :=
  BoxWeight.ofReal (X.nucDW q Zc P a) (X.measurable_nucDW q Zc P a)
    ((∑ i : Fin eta, ∑ l : ν, |q i * Zc l|) * (X.D / δ ^ 2))
    (fun r => (abs_mul_nucDV_le q Zc hδ hflat 0 a r).trans
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (X.d1 a r) (by positivity))
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)))
    fun r hr => box_of_tsupport X.box r (X.nucDW_mem q Zc P a hr)

lemma nucBW_w {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ) (a : Fin eta × Fin 3)
    (r : Rcfg eta) : (X.nucBW q Zc P hδ hflat a).w r = ((X.nucDW q Zc P a r : ℝ) : ℂ) := rfl

lemma nucBW_mem {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ) (a : Fin eta × Fin 3)
    {r : Rcfg eta} (hr : (X.nucBW q Zc P hδ hflat a).w r ≠ 0) : r ∈ tsupport X.χ :=
  X.nucDW_mem q Zc P a fun h => hr (by rw [nucBW_w, h, Complex.ofReal_zero])

end DomCutoff

/-! ## The kinetic energy of the commutator with nuclei -/

section Commutator

lemma IP_add {Φ : Rcfg eta → ℂ} (hΦ : Continuous Φ) {ζ : Rcfg eta → ℝ} (hζ : Continuous ζ)
    (hζc : HasCompactSupport ζ) (f₁ f₂ : FreeL2 eta) :
    IP Φ ζ (f₁ + f₂) = IP Φ ζ f₁ + IP Φ ζ f₂ := by
  unfold IP
  rw [← integral_add (integrable_conj_mul_weight hΦ hζ hζc f₁)
    (integrable_conj_mul_weight hΦ hζ hζc f₂)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add f₁ f₂] with r hr
  rw [hr, Pi.add_apply]
  ring

variable {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m) (q : Fin eta → ℝ)
  (Zc : ν → ℝ)
include hL

/-- **The kinetic energy of the commutator with clamped nuclei**: as `freeId_comm`, with
`V u = pairL2 Y + nucL2 Yn`, `V g_a = pairL2 Z_a + nucL2 Zn_a` and the bounded nuclear part
`Σ_a 2c_a IP Ψ (∂_aχ ∂_aV) u` of the double commutator. -/
theorem freeId_comm_nuc {P : ν → E3} {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ)
    {u h : FreeL2 eta} {g g' : Fin eta × Fin 3 → FreeL2 eta}
    {g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta}
    {Y : FiniteElectronPair eta → FreeL2 eta}
    {Z : FiniteElectronPair eta → Fin eta × Fin 3 → FreeL2 eta}
    {Yn : Fin eta → ν → FreeL2 eta} {Zn : Fin eta → ν → Fin eta × Fin 3 → FreeL2 eta}
    (hK : HasFreeWeakKinetic m u (h - (pairL2 q Y + nucL2 q Zc Yn))) (hg : HasWeakGrad u g)
    (hg' : HasWeakGrad h g') (hg2 : ∀ b, HasWeakGrad (g b) (g2 b))
    (hY : ∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * u r)
    (hZ : ∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * g a r)
    (hYn : ∀ i l, ∀ᵐ r, Yn i l r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * u r)
    (hZn : ∀ i l a, ∀ᵐ r, Zn i l a r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * g a r)
    {Ψ : Rcfg eta → ℂ} (hΨ : ContDiff ℝ 3 Ψ) :
    ∑ a : Fin eta × Fin 3, kc m a * (IP (freeKinetic m Ψ) (dirD a (dirD a X.χ)) u +
        2 * IP (freeKinetic m Ψ) (dirD a X.χ) (g a)) =
      ∑ a : Fin eta × Fin 3, kc m a * (termA X Ψ u h g a -
          IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y + nucL2 q Zc Yn)) +
        ∑ a : Fin eta × Fin 3, 2 * kc m a * (termB X Ψ u g g' g2 a -
          IP Ψ (dirD a X.χ) (pairL2 q (fun p => Z p a) + nucL2 q Zc (fun i l => Zn i l a))) -
        (∑ p : FiniteElectronPair eta, ∫ r, conj (Ψ r) * ((commBeta m q X.χ p r : ℂ) * Y p r)) -
        ∑ a : Fin eta × Fin 3, 2 * kc m a * IP Ψ (X.nucDW q Zc P a) u := by
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by norm_num)
  have hS := singular_identity hL X q hg hY hZ hΨ1
  have hSn := nuc_singular_identity hL X q Zc hδ hflat hg hYn hZn hΨ1
  have hA : ∀ a, IP (freeKinetic m Ψ) (dirD a (dirD a X.χ)) u =
      termA X Ψ u h g a - IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y + nucL2 q Zc Yn) := by
    intro a
    rw [freeId_A hL X hK hg (hΨ.of_le (by norm_num)) a]
    unfold termA
    ring
  have hB : ∀ a, IP (freeKinetic m Ψ) (dirD a X.χ) (g a) =
      termB X Ψ u g g' g2 a +
        (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y + nucL2 q Zc Yn) +
          IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y + nucL2 q Zc Yn)) := by
    intro a
    rw [freeId_B hL X hK hg hg' hg2 hΨ a]
    unfold termB
    ring
  simp_rw [hA, hB]
  -- splitting the potential terms
  have hc1 : ∀ a, Continuous (dirD a X.χ) := fun a => continuous_dirD X.smooth (by norm_num) a
  have hc2 : ∀ a, Continuous (dirD a (dirD a X.χ)) := fun a =>
    continuous_dirD (X.c1 a) (by norm_num) a
  have hcs1 : ∀ a, HasCompactSupport (dirD a X.χ) := fun a => X.hcs_of_sub hL (X.ts1 a)
  have hcs2 : ∀ a, HasCompactSupport (dirD a (dirD a X.χ)) := fun a =>
    X.hcs_of_sub hL (X.ts2 a a)
  have s1 : ∀ a, IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y + nucL2 q Zc Yn) =
      IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) + IP Ψ (dirD a (dirD a X.χ)) (nucL2 q Zc Yn) :=
    fun a => IP_add hΨ.continuous (hc2 a) (hcs2 a) _ _
  have s2 : ∀ a, IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y + nucL2 q Zc Yn) =
      IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y) + IP (dirD a Ψ) (dirD a X.χ) (nucL2 q Zc Yn) :=
    fun a => IP_add (continuous_dirD hΨ (by norm_num) a) (hc1 a) (hcs1 a) _ _
  have s3 : ∀ a, IP Ψ (dirD a X.χ) (pairL2 q (fun p => Z p a) +
      nucL2 q Zc (fun i l => Zn i l a)) = IP Ψ (dirD a X.χ) (pairL2 q (fun p => Z p a)) +
        IP Ψ (dirD a X.χ) (nucL2 q Zc (fun i l => Zn i l a)) :=
    fun a => IP_add hΨ.continuous (hc1 a) (hcs1 a) _ _
  simp_rw [s1, s2, s3]
  -- the two singular identities in `IP` notation
  have hS' : ∑ a : Fin eta × Fin 3, 2 * kc m a *
      (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) + IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y)) =
      -(∑ a : Fin eta × Fin 3, 2 * kc m a * IP Ψ (dirD a X.χ) (pairL2 q fun p => Z p a)) -
        ∑ p : FiniteElectronPair eta,
          ∫ r, conj (Ψ r) * ((commBeta m q X.χ p r : ℂ) * Y p r) := by
    simp_rw [two_kc]
    exact hS
  have hSn' : ∑ a : Fin eta × Fin 3, 2 * kc m a *
      (IP Ψ (dirD a (dirD a X.χ)) (nucL2 q Zc Yn) + IP (dirD a Ψ) (dirD a X.χ) (nucL2 q Zc Yn)) =
      -(∑ a : Fin eta × Fin 3, 2 * kc m a *
          IP Ψ (dirD a X.χ) (nucL2 q Zc fun i l => Zn i l a)) -
        ∑ a : Fin eta × Fin 3, 2 * kc m a * IP Ψ (X.nucDW q Zc P a) u := by
    simp_rw [two_kc]
    exact hSn
  set Bs := ∑ p : FiniteElectronPair eta, ∫ r, conj (Ψ r) * ((commBeta m q X.χ p r : ℂ) * Y p r)
    with hBs
  have key : ∑ a : Fin eta × Fin 3, 2 * kc m a *
      (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) + IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y) +
        (IP Ψ (dirD a (dirD a X.χ)) (nucL2 q Zc Yn) +
          IP (dirD a Ψ) (dirD a X.χ) (nucL2 q Zc Yn)) +
        IP Ψ (dirD a X.χ) (pairL2 q fun p => Z p a) +
        IP Ψ (dirD a X.χ) (nucL2 q Zc fun i l => Zn i l a) + IP Ψ (X.nucDW q Zc P a) u) +
      Bs = 0 := by
    have hsum : ∑ a : Fin eta × Fin 3, 2 * kc m a *
        (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) + IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y) +
          (IP Ψ (dirD a (dirD a X.χ)) (nucL2 q Zc Yn) +
            IP (dirD a Ψ) (dirD a X.χ) (nucL2 q Zc Yn)) +
          IP Ψ (dirD a X.χ) (pairL2 q fun p => Z p a) +
          IP Ψ (dirD a X.χ) (nucL2 q Zc fun i l => Zn i l a) + IP Ψ (X.nucDW q Zc P a) u) =
        ∑ a : Fin eta × Fin 3, 2 * kc m a *
          (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) + IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y)) +
        ∑ a : Fin eta × Fin 3, 2 * kc m a *
          (IP Ψ (dirD a (dirD a X.χ)) (nucL2 q Zc Yn) +
            IP (dirD a Ψ) (dirD a X.χ) (nucL2 q Zc Yn)) +
        ∑ a : Fin eta × Fin 3, 2 * kc m a * IP Ψ (dirD a X.χ) (pairL2 q fun p => Z p a) +
        ∑ a : Fin eta × Fin 3, 2 * kc m a *
          IP Ψ (dirD a X.χ) (nucL2 q Zc fun i l => Zn i l a) +
        ∑ a : Fin eta × Fin 3, 2 * kc m a * IP Ψ (X.nucDW q Zc P a) u := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hsum]
    linear_combination hS' + hSn'
  have e1 : ∑ a : Fin eta × Fin 3, kc m a *
        (termA X Ψ u h g a - (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) +
          IP Ψ (dirD a (dirD a X.χ)) (nucL2 q Zc Yn)) +
        2 * (termB X Ψ u g g' g2 a + (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) +
          IP Ψ (dirD a (dirD a X.χ)) (nucL2 q Zc Yn) +
          (IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y) +
            IP (dirD a Ψ) (dirD a X.χ) (nucL2 q Zc Yn))))) =
      ∑ a : Fin eta × Fin 3, kc m a * (termA X Ψ u h g a -
          (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) +
            IP Ψ (dirD a (dirD a X.χ)) (nucL2 q Zc Yn))) +
        ∑ a : Fin eta × Fin 3, 2 * kc m a * (termB X Ψ u g g' g2 a -
          (IP Ψ (dirD a X.χ) (pairL2 q fun p => Z p a) +
            IP Ψ (dirD a X.χ) (nucL2 q Zc fun i l => Zn i l a))) -
        ∑ a : Fin eta × Fin 3, 2 * kc m a * IP Ψ (X.nucDW q Zc P a) u +
        ∑ a : Fin eta × Fin 3, 2 * kc m a *
          (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) + IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y) +
            (IP Ψ (dirD a (dirD a X.χ)) (nucL2 q Zc Yn) +
              IP (dirD a Ψ) (dirD a X.χ) (nucL2 q Zc Yn)) +
            IP Ψ (dirD a X.χ) (pairL2 q fun p => Z p a) +
            IP Ψ (dirD a X.χ) (nucL2 q Zc fun i l => Zn i l a) + IP Ψ (X.nucDW q Zc P a) u) := by
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e1]
  linear_combination key

end Commutator

/-! ## The torus image with nuclei -/

section Image

variable {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m) (q : Fin eta → ℝ)
  (Zc : ν → ℝ) (P : ν → E3) {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ)

/-- **The torus image of `H_∞ [K, χ] u` without its potential part, with nuclei**:
`commH - Σ_a 2c_a T(∂_aχ ∂_aV u)`. -/
noncomputable def commHn (u h : FreeL2 eta) (g g' : Fin eta × Fin 3 → FreeL2 eta)
    (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
    (Y : FiniteElectronPair eta → FreeL2 eta) : MolecularPositionL2 eta :=
  commH hL X q u h g g' g2 Y -
    ∑ a : Fin eta × Fin 3, (2 * kc m a) • (X.nucBW q Zc P hδ hflat a).cutL2 hL u

lemma inner_commHn (s : Finset (FourierConfig eta Lattice3)) (c : FourierConfig eta Lattice3 → ℂ)
    (u h : FreeL2 eta) (g g' : Fin eta × Fin 3 → FreeL2 eta)
    (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
    (Y : FiniteElectronPair eta → FreeL2 eta) :
    inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (molecularPositionFourierTest eta s c))
        (commHn hL X q Zc P hδ hflat u h g g' g2 Y) =
      ((tScale eta L : ℂ))⁻¹ * (∑ a : Fin eta × Fin 3, kc m a * termA X (liftTest L s c) u h g a +
        ∑ a : Fin eta × Fin 3, 2 * kc m a * termB X (liftTest L s c) u g g' g2 a -
        (∑ p : FiniteElectronPair eta,
          ∫ r, conj (liftTest L s c r) * ((commBeta m q X.χ p r : ℂ) * Y p r)) -
        ∑ a : Fin eta × Fin 3, 2 * kc m a * IP (liftTest L s c) (X.nucDW q Zc P a) u) := by
  have h2 : inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (molecularPositionFourierTest eta s c))
      (∑ a : Fin eta × Fin 3, (2 * kc m a) • (X.nucBW q Zc P hδ hflat a).cutL2 hL u) =
      ((tScale eta L : ℂ))⁻¹ *
        ∑ a : Fin eta × Fin 3, 2 * kc m a * IP (liftTest L s c) (X.nucDW q Zc P a) u := by
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_smul_right, inner_test_real hL _ (X.nucBW_w q Zc P hδ hflat a)]
    ring
  unfold commHn
  rw [inner_sub_right, inner_commH, h2]
  ring

end Image

/-! ## The torus Hamiltonian relation of the commutator with nuclei -/

section Relation

/-- **The transplanted commutator is in `D(H_L)`, with clamped nuclei.** As
`commT_hasGLHamiltonian`, for a mass-weighted cutoff flat near the nuclei (`IsFlatNear`), with
the nuclear Hardy functions `Yn_{iℓ} = u/|x_i - P_ℓ|`, `Zn_{iℓ,a} = g_a/|x_i - P_ℓ|`:
`H_L T([K, χ] u) = commHn - C₀ T([K, χ] u)`. -/
theorem commT_hasGLHamiltonian_nuc (sys : CoulombSystem eta ν) {L R0 ρ : ℝ}
    {θ : ℝ → ℝ} (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear X.χ P δ)
    {u h : FreeL2 eta} {g g' : Fin eta × Fin 3 → FreeL2 eta}
    {g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta}
    {Y : FiniteElectronPair eta → FreeL2 eta}
    {Z : FiniteElectronPair eta → Fin eta × Fin 3 → FreeL2 eta}
    {Yn : Fin eta → ν → FreeL2 eta} {Zn : Fin eta → ν → Fin eta × Fin 3 → FreeL2 eta}
    (hK : HasFreeWeakKinetic sys.mass u
      (h - (pairL2 sys.charge Y + nucL2 sys.charge sys.nuclei.charge Yn)))
    (hg : HasWeakGrad u g) (hg' : HasWeakGrad h g') (hg2 : ∀ b, HasWeakGrad (g b) (g2 b))
    (hY : ∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * u r)
    (hZ : ∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * g a r)
    (hYn : ∀ i l, ∀ᵐ r, Yn i l r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * u r)
    (hZn : ∀ i l a, ∀ᵐ r, Zn i l a r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * g a r) :
    HasGLHamiltonian sys L θ (X.toCutoff.commT hL sys.mass u g)
      (commHn hL X sys.charge sys.nuclei.charge P hδ hflat u h g g' g2 Y -
        zeroModeShift sys L θ • X.toCutoff.commT hL sys.mass u g) := by
  set C₀ := zeroModeShift sys L θ with hC₀
  set Zc := sys.nuclei.charge with hZc
  have hrt := ret_of_tsupport hret
  -- the potential part
  set P₂ : MolecularPositionL2 eta := ∑ a : Fin eta × Fin 3, kc sys.mass a •
    ((X.toCutoff.d2W a).cutL2 hL (pairL2 sys.charge Y + nucL2 sys.charge Zc Yn) +
      (2 : ℂ) • (X.toCutoff.d1W a).cutL2 hL
        (pairL2 sys.charge (fun p => Z p a) + nucL2 sys.charge Zc (fun i l => Zn i l a)))
    with hP₂
  have hpot : HasL2PointwisePotential volume (gLFourierPotential sys L θ)
      (X.toCutoff.commT hL sys.mass u g) (P₂ - C₀ • X.toCutoff.commT hL sys.mass u g) := by
    have h1 : HasL2PointwisePotential volume (gLFourierPotential sys L θ)
        (X.toCutoff.commT hL sys.mass u g) (∑ a : Fin eta × Fin 3, kc sys.mass a •
          (((X.toCutoff.d2W a).cutL2 hL (pairL2 sys.charge Y + nucL2 sys.charge Zc Yn) -
            C₀ • (X.toCutoff.d2W a).cutL2 hL u) +
          (2 : ℂ) • ((X.toCutoff.d1W a).cutL2 hL (pairL2 sys.charge (fun p => Z p a) +
              nucL2 sys.charge Zc (fun i l => Zn i l a)) -
            C₀ • (X.toCutoff.d1W a).cutL2 hL (g a)))) := by
      rw [commT_eq]
      have hA : ∀ a, HasL2PointwisePotential volume (gLFourierPotential sys L θ)
          ((X.toCutoff.d2W a).cutL2 hL u)
          ((X.toCutoff.d2W a).cutL2 hL (pairL2 sys.charge Y + nucL2 sys.charge Zc Yn) -
            C₀ • (X.toCutoff.d2W a).cutL2 hL u) := fun a =>
        potential_cutL2 sys hL hR0 hρ hone P hP hpos _ (fun r hr => hrt r (X.d2W_mem a hr))
          (hasL2PointwisePotential_pair_nucL2 sys P hY hYn)
      have hB : ∀ a, HasL2PointwisePotential volume (gLFourierPotential sys L θ)
          ((X.toCutoff.d1W a).cutL2 hL (g a))
          ((X.toCutoff.d1W a).cutL2 hL (pairL2 sys.charge (fun p => Z p a) +
              nucL2 sys.charge Zc (fun i l => Zn i l a)) -
            C₀ • (X.toCutoff.d1W a).cutL2 hL (g a)) := fun a =>
        potential_cutL2 sys hL hR0 hρ hone P hP hpos _ (fun r hr => hrt r (X.d1W_mem a hr))
          (hasL2PointwisePotential_pair_nucL2 sys P (fun p => hZ p a) fun i l => hZn i l a)
      exact hasL2Pot_sum _ fun a _ => hasL2Pot_smul ((hA a).add (hasL2Pot_smul (hB a) 2)) _
    have e : (∑ a : Fin eta × Fin 3, kc sys.mass a •
          (((X.toCutoff.d2W a).cutL2 hL (pairL2 sys.charge Y + nucL2 sys.charge Zc Yn) -
            C₀ • (X.toCutoff.d2W a).cutL2 hL u) +
          (2 : ℂ) • ((X.toCutoff.d1W a).cutL2 hL (pairL2 sys.charge (fun p => Z p a) +
              nucL2 sys.charge Zc (fun i l => Zn i l a)) -
            C₀ • (X.toCutoff.d1W a).cutL2 hL (g a)))) =
        P₂ - C₀ • X.toCutoff.commT hL sys.mass u g := by
      rw [hP₂, commT_eq, Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by module
    rwa [e] at h1
  refine hasGLHamiltonian_of_fourierTests sys hpot fun s c => ?_
  -- the kinetic part
  have e2 : commHn hL X sys.charge Zc P hδ hflat u h g g' g2 Y -
      C₀ • X.toCutoff.commT hL sys.mass u g - (P₂ - C₀ • X.toCutoff.commT hL sys.mass u g) =
      commHn hL X sys.charge Zc P hδ hflat u h g g' g2 Y - P₂ := by
    abel
  have hΨ : ContDiff ℝ 3 (liftTest L s c) := contDiff_liftTest L s c 3
  have hid := freeId_comm_nuc hL X sys.charge Zc hδ hflat hK hg hg' hg2 hY hZ hYn hZn hΨ
  have iP : inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (molecularPositionFourierTest eta s c)) P₂ =
      ((tScale eta L : ℂ))⁻¹ * ∑ a : Fin eta × Fin 3, kc sys.mass a *
        (IP (liftTest L s c) (dirD a (dirD a X.χ)) (pairL2 sys.charge Y + nucL2 sys.charge Zc Yn) +
          2 * IP (liftTest L s c) (dirD a X.χ) (pairL2 sys.charge (fun p => Z p a) +
            nucL2 sys.charge Zc (fun i l => Zn i l a))) := by
    rw [hP₂, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_smul_right, inner_add_right, inner_smul_right,
      inner_test_real hL (X.toCutoff.d2W a) (ζ := dirD a (dirD a X.χ)) (fun r => rfl),
      inner_test_real hL (X.toCutoff.d1W a) (ζ := dirD a X.χ) (fun r => rfl)]
    ring
  have iK : inner ℂ ((ContinuousMap.toLp 2 volume ℂ)
      (coulombPositionKineticTest sys (2 * Real.pi / L) s c)) (X.toCutoff.commT hL sys.mass u g) =
      ((tScale eta L : ℂ))⁻¹ * ∑ a : Fin eta × Fin 3, kc sys.mass a *
        (IP (freeKinetic sys.mass (liftTest L s c)) (dirD a (dirD a X.χ)) u +
          2 * IP (freeKinetic sys.mass (liftTest L s c)) (dirD a X.χ) (g a)) := by
    rw [commT_eq, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_smul_right, inner_add_right, inner_smul_right,
      inner_kinTest_real hL sys (X.toCutoff.d2W a) (ζ := dirD a (dirD a X.χ)) (fun r => rfl),
      inner_kinTest_real hL sys (X.toCutoff.d1W a) (ζ := dirD a X.χ) (fun r => rfl)]
    ring
  rw [e2, inner_sub_right, inner_commHn, iP, iK, hid, ← mul_sub]
  congr 1
  have e3 : ∑ a : Fin eta × Fin 3, kc sys.mass a * (termA X (liftTest L s c) u h g a -
        IP (liftTest L s c) (dirD a (dirD a X.χ)) (pairL2 sys.charge Y + nucL2 sys.charge Zc Yn)) +
      ∑ a : Fin eta × Fin 3, 2 * kc sys.mass a * (termB X (liftTest L s c) u g g' g2 a -
        IP (liftTest L s c) (dirD a X.χ) (pairL2 sys.charge (fun p => Z p a) +
          nucL2 sys.charge Zc (fun i l => Zn i l a))) =
      ∑ a : Fin eta × Fin 3, kc sys.mass a * termA X (liftTest L s c) u h g a +
        ∑ a : Fin eta × Fin 3, 2 * kc sys.mass a * termB X (liftTest L s c) u g g' g2 a -
        ∑ a : Fin eta × Fin 3, kc sys.mass a *
          (IP (liftTest L s c) (dirD a (dirD a X.χ)) (pairL2 sys.charge Y +
              nucL2 sys.charge Zc Yn) +
            2 * IP (liftTest L s c) (dirD a X.χ) (pairL2 sys.charge (fun p => Z p a) +
              nucL2 sys.charge Zc (fun i l => Zn i l a))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e3]
  ring

end Relation

end FreeBoundary
