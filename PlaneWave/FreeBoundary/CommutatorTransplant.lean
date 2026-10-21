import PlaneWave.FreeBoundary.SecondCommutator

/-!
# The cut initial state in `D(H_L²)`, part 5: the commutator on the torus

For the non-Born–Oppenheimer system (`ν` empty: all particles quantum), the transplanted
commutator `T([K, χ] u)` lies in `D(H_L)`: on the torus,
`H_L T([K, χ] u) = commH - C₀ T([K, χ] u)`, where `commH` is the transplant of the free-space
expression of `freeId_comm` (bounded weights times `u`, `∇u`, `∇²u`, `∇h`, and the singular term
`Σ_{i<j} β_{ij} u/|x_i - x_j|` with `|β_{ij}| ≤ |q_i q_j| C`).

* `hasL2Pot_smul`, `hasL2Pot_sub`, `hasL2Pot_sum`: the pointwise potential relation is linear;
* `potential_cutL2`: `V_L T_w f = T_w (V_∞ f) - C₀ T_w f` for a weight in the retained region;
* `commTA`, `commTB`, `commH`: the torus images of `termA`, `termB` and of the whole expression;
* **`commT_hasGLHamiltonian`**: the torus Hamiltonian relation of the transplanted commutator.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15

variable {eta : ℕ}

/-! ## The pointwise potential relation is linear -/

section PotLinear

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {V : α → ℂ}

lemma hasL2Pot_smul {f g : Lp ℂ 2 μ} (h : HasL2PointwisePotential μ V f g) (c : ℂ) :
    HasL2PointwisePotential μ V (c • f) (c • g) := by
  filter_upwards [h, Lp.coeFn_smul c f, Lp.coeFn_smul c g] with x hx e1 e2
  rw [e2, Pi.smul_apply, hx, e1, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

lemma hasL2Pot_sub {f₁ f₂ g₁ g₂ : Lp ℂ 2 μ} (h₁ : HasL2PointwisePotential μ V f₁ g₁)
    (h₂ : HasL2PointwisePotential μ V f₂ g₂) :
    HasL2PointwisePotential μ V (f₁ - f₂) (g₁ - g₂) := by
  filter_upwards [h₁, h₂, Lp.coeFn_sub f₁ f₂, Lp.coeFn_sub g₁ g₂] with x e1 e2 e3 e4
  rw [e4, e3, Pi.sub_apply, Pi.sub_apply, e1, e2]
  ring

lemma hasL2Pot_sum {ι : Type*} (s : Finset ι) {f g : ι → Lp ℂ 2 μ}
    (h : ∀ i ∈ s, HasL2PointwisePotential μ V (f i) (g i)) :
    HasL2PointwisePotential μ V (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasL2PointwisePotential.zero μ V
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end PotLinear

/-! ## The potential of a weighted transplant -/

section Potential

variable {ν : Type} [Fintype ν]

lemma ret_of_tsupport {L R0 ρ : ℝ} {χ : Rcfg eta → ℝ}
    (hret : ∀ r, χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ) :
    ∀ r ∈ tsupport χ, ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ := by
  have hcl : IsClosed {r : Rcfg eta | ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le (particleCLM i).continuous.norm continuous_const
  exact fun r hr => closure_minimal (fun y hy => hret y hy) hcl hr

/-- **The potential of a weighted transplant**: on the retained region the `g_L` interaction is
`V_∞ - C₀`, so `V_L T_w f = T_w (V_∞ f) - C₀ T_w f`. -/
lemma potential_cutL2 (sys : CoulombSystem eta ν) {L R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (W : BoxWeight eta L)
    (hW : ∀ r, W.w r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {f v : FreeL2 eta} (hv : HasL2PointwisePotential volume (fun r => (freePot sys P r : ℂ)) f v) :
    HasL2PointwisePotential volume (gLFourierPotential sys L θ) (W.cutL2 hL f)
      (W.cutL2 hL v - zeroModeShift sys L θ • W.cutL2 hL f) := by
  filter_upwards [Lp.coeFn_sub (W.cutL2 hL v) (zeroModeShift sys L θ • W.cutL2 hL f),
    Lp.coeFn_smul (zeroModeShift sys L θ) (W.cutL2 hL f),
    W.cutL2_ae hL v, W.cutL2_ae hL f, (qmp_cellCoord hL.ne').ae hv]
    with x h1 h2 h3 h4 h5
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
  simp only [BoxWeight.cutFun]
  rw [h5]
  by_cases h0 : W.w (cellCoord L x) = 0
  · simp [h0]
  · rw [gLFourierPotential_eq_freePot sys hL hR0 hρ hone P hP hpos x (hW _ h0)]
    ring

end Potential

/-! ## The weights of the commutator -/

namespace DomCutoff

variable {L : ℝ} {m : Fin eta → ℝ} (X : DomCutoff eta L m) (q : Fin eta → ℝ)

lemma w1_w (a : Fin eta × Fin 3) (r : Rcfg eta) :
    (X.w1 a).w r = ((dirD a X.χ r : ℝ) : ℂ) := rfl

lemma w2_w (a b : Fin eta × Fin 3) (r : Rcfg eta) :
    (X.w2 a b).w r = ((dirD b (dirD a X.χ) r : ℝ) : ℂ) := rfl

lemma w3_w (a b c : Fin eta × Fin 3) (r : Rcfg eta) :
    (X.w3 a b c).w r = ((dirD c (dirD b (dirD a X.χ)) r : ℝ) : ℂ) := rfl

lemma w4_w (a b c d : Fin eta × Fin 3) (r : Rcfg eta) :
    (X.w4 a b c d).w r = ((dirD d (dirD c (dirD b (dirD a X.χ))) r : ℝ) : ℂ) := rfl

lemma mem_tsupport_of_commBeta_ne (p : FiniteElectronPair eta) {r : Rcfg eta}
    (h : commBeta m q X.χ p r ≠ 0) : r ∈ tsupport X.χ := by
  by_contra hr
  exact h (commBeta_eq_zero_of_notMem m q p hr)

/-- The singular weight `β_{ij}`, bounded by `|q_i q_j| C`. -/
noncomputable def betaW (p : FiniteElectronPair eta) : BoxWeight eta L :=
  BoxWeight.ofReal (commBeta m q X.χ p) (X.measurable_commBeta q p) (|q p.1.1 * q p.1.2| * X.C)
    (X.abs_commBeta_le q p) fun r hr =>
      box_of_tsupport X.box r (X.mem_tsupport_of_commBeta_ne q p hr)

lemma betaW_w (p : FiniteElectronPair eta) (r : Rcfg eta) :
    (X.betaW q p).w r = ((commBeta m q X.χ p r : ℝ) : ℂ) := rfl

lemma betaW_B (p : FiniteElectronPair eta) : (X.betaW q p).B = |q p.1.1 * q p.1.2| * X.C := rfl

/-- Every weight of the commutator vanishes off `tsupport χ`. -/
lemma chainW_mem {f : Rcfg eta → ℝ} (hf : Continuous f) (hs : tsupport f ⊆ tsupport X.χ)
    (hb : ∀ r, |f r| ≤ X.D) {r : Rcfg eta} (hr : (X.chainW hf hs hb).w r ≠ 0) :
    r ∈ tsupport X.χ :=
  hs (subset_tsupport f fun h => hr (by rw [chainW_w, h, Complex.ofReal_zero]))

lemma d1W_mem (a : Fin eta × Fin 3) {r : Rcfg eta} (hr : (X.toCutoff.d1W a).w r ≠ 0) :
    r ∈ tsupport X.χ :=
  mem_tsupport_of_dirD_ne (a := a) fun h => hr (by simp [Cutoff.d1W, h])

lemma d2W_mem (a : Fin eta × Fin 3) {r : Rcfg eta} (hr : (X.toCutoff.d2W a).w r ≠ 0) :
    r ∈ tsupport X.χ :=
  X.ts1 a (mem_tsupport_of_dirD_ne (a := a) fun h => hr (by simp [Cutoff.d2W, h]))

end DomCutoff

/-! ## Inner products with trigonometric tests -/

section Inner

variable {ν : Type} [Fintype ν] {L : ℝ} (hL : 0 < L)

/-- `⟨Φ, T_ζ f⟩ = L^{-3η/2} IP Ψ ζ f` for a real weight `ζ`, `Ψ` the lift of the test `Φ`. -/
lemma inner_test_real (W : BoxWeight eta L) {ζ : Rcfg eta → ℝ} (hW : ∀ r, W.w r = (ζ r : ℂ))
    (s : Finset (FourierConfig eta Lattice3)) (c : FourierConfig eta Lattice3 → ℂ)
    (f : FreeL2 eta) :
    inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (molecularPositionFourierTest eta s c))
        (W.cutL2 hL f) =
      ((tScale eta L : ℂ))⁻¹ * IP (liftTest L s c) ζ f := by
  rw [inner_test_cutL2 hL W s c f]
  unfold IP
  simp_rw [hW]

/-- `⟨K_L Φ, T_ζ f⟩ = L^{-3η/2} IP (KΨ) ζ f` for a real weight `ζ`. -/
lemma inner_kinTest_real (sys : CoulombSystem eta ν) (W : BoxWeight eta L) {ζ : Rcfg eta → ℝ}
    (hW : ∀ r, W.w r = (ζ r : ℂ)) (s : Finset (FourierConfig eta Lattice3))
    (c : FourierConfig eta Lattice3 → ℂ) (f : FreeL2 eta) :
    inner ℂ ((ContinuousMap.toLp 2 volume ℂ)
        (coulombPositionKineticTest sys (2 * Real.pi / L) s c)) (W.cutL2 hL f) =
      ((tScale eta L : ℂ))⁻¹ * IP (freeKinetic sys.mass (liftTest L s c)) ζ f := by
  rw [inner_kineticTest_cutL2 sys hL W s c f]
  unfold IP
  simp_rw [hW]

end Inner

/-! ## The torus image of the commutator expression -/

section Image

variable {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m) (q : Fin eta → ℝ)

/-- The torus image of `termA`. -/
noncomputable def commTA (u h : FreeL2 eta) (g : Fin eta × Fin 3 → FreeL2 eta)
    (a : Fin eta × Fin 3) : MolecularPositionL2 eta :=
  (X.w2 a a).cutL2 hL h + ∑ b : Fin eta × Fin 3, kc m b •
    ((X.w4 a a b b).cutL2 hL u + (2 : ℂ) • (X.w3 a a b).cutL2 hL (g b))

/-- The torus image of `termB`. -/
noncomputable def commTB (u : FreeL2 eta) (g g' : Fin eta × Fin 3 → FreeL2 eta)
    (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta) (a : Fin eta × Fin 3) :
    MolecularPositionL2 eta :=
  (X.w1 a).cutL2 hL (g' a) + ∑ b : Fin eta × Fin 3, kc m b •
    (-(X.w4 a a b b).cutL2 hL u - (2 : ℂ) • (X.w3 a a b).cutL2 hL (g b) +
      (X.w4 a b b a).cutL2 hL u + (X.w3 a b b).cutL2 hL (g a) +
      (2 : ℂ) • (X.w3 a b a).cutL2 hL (g b) + (2 : ℂ) • (X.w2 a b).cutL2 hL (g2 b a))

/-- **The torus image of `H_∞ [K, χ] u`, without its potential part**:
`Σ_a c_a T(A_a) + Σ_a 2c_a T(B_a) - Σ_{i<j} T(β_{ij} u/|x_i - x_j|)`. -/
noncomputable def commH (u h : FreeL2 eta) (g g' : Fin eta × Fin 3 → FreeL2 eta)
    (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
    (Y : FiniteElectronPair eta → FreeL2 eta) : MolecularPositionL2 eta :=
  ∑ a : Fin eta × Fin 3, kc m a • commTA hL X u h g a +
    ∑ a : Fin eta × Fin 3, (2 * kc m a) • commTB hL X u g g' g2 a -
    ∑ p : FiniteElectronPair eta, (X.betaW q p).cutL2 hL (Y p)

variable (s : Finset (FourierConfig eta Lattice3)) (c : FourierConfig eta Lattice3 → ℂ)

lemma inner_commTA (u h : FreeL2 eta) (g : Fin eta × Fin 3 → FreeL2 eta)
    (a : Fin eta × Fin 3) :
    inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (molecularPositionFourierTest eta s c))
        (commTA hL X u h g a) =
      ((tScale eta L : ℂ))⁻¹ * termA X (liftTest L s c) u h g a := by
  unfold commTA termA
  rw [inner_add_right, inner_test_real hL _ (X.w2_w a a), inner_sum, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [inner_smul_right, inner_add_right, inner_smul_right, inner_test_real hL _ (X.w4_w a a b b),
    inner_test_real hL _ (X.w3_w a a b)]
  ring

lemma inner_commTB (u : FreeL2 eta) (g g' : Fin eta × Fin 3 → FreeL2 eta)
    (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta) (a : Fin eta × Fin 3) :
    inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (molecularPositionFourierTest eta s c))
        (commTB hL X u g g' g2 a) =
      ((tScale eta L : ℂ))⁻¹ * termB X (liftTest L s c) u g g' g2 a := by
  unfold commTB termB
  rw [inner_add_right, inner_test_real hL _ (X.w1_w a), inner_sum, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [inner_smul_right, inner_add_right, inner_add_right, inner_add_right, inner_add_right,
    inner_sub_right, inner_neg_right, inner_smul_right, inner_smul_right, inner_smul_right,
    inner_test_real hL _ (X.w4_w a a b b), inner_test_real hL _ (X.w3_w a a b),
    inner_test_real hL _ (X.w4_w a b b a), inner_test_real hL _ (X.w3_w a b b),
    inner_test_real hL _ (X.w3_w a b a), inner_test_real hL _ (X.w2_w a b)]
  ring

lemma inner_commH (u h : FreeL2 eta) (g g' : Fin eta × Fin 3 → FreeL2 eta)
    (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
    (Y : FiniteElectronPair eta → FreeL2 eta) :
    inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (molecularPositionFourierTest eta s c))
        (commH hL X q u h g g' g2 Y) =
      ((tScale eta L : ℂ))⁻¹ * (∑ a : Fin eta × Fin 3, kc m a * termA X (liftTest L s c) u h g a +
        ∑ a : Fin eta × Fin 3, 2 * kc m a * termB X (liftTest L s c) u g g' g2 a -
        ∑ p : FiniteElectronPair eta,
          ∫ r, conj (liftTest L s c r) * ((commBeta m q X.χ p r : ℂ) * Y p r)) := by
  unfold commH
  rw [inner_sub_right, inner_add_right, inner_sum, inner_sum, inner_sum, mul_sub, mul_add,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_smul_right, inner_commTA]
      ring
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_smul_right, inner_commTB]
      ring
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_test_real hL _ (X.betaW_w q p)]
    rfl

end Image

/-! ## The torus Hamiltonian relation of the commutator -/

section Relation

variable {ν : Type} [Fintype ν]

lemma commT_eq {L : ℝ} (hL : 0 < L) (X : Cutoff eta L) (m : Fin eta → ℝ) (u : FreeL2 eta)
    (g : Fin eta × Fin 3 → FreeL2 eta) :
    X.commT hL m u g = ∑ a : Fin eta × Fin 3, kc m a •
      ((X.d2W a).cutL2 hL u + (2 : ℂ) • (X.d1W a).cutL2 hL (g a)) := rfl

/-- **The transplanted commutator is in `D(H_L)`** (non-Born–Oppenheimer: no clamped nuclei).
Let `H_∞ u = h` with `V_∞ u = Σ_{i<j} q_i q_j Y_{ij}`, `Y_{ij} = u/|x_i - x_j|`, weak
gradients `∇u = g`, `∇h = g'`, `∂_a g_b = g2 b a`, and `Z_{ij,a} = g_a/|x_i - x_j|` in `L²`. For a
mass-weighted cutoff `χ` in the retained region,
`H_L T([K, χ] u) = commH - C₀ T([K, χ] u)`. -/
theorem commT_hasGLHamiltonian [IsEmpty ν] (sys : CoulombSystem eta ν) {L R0 ρ : ℝ}
    {θ : ℝ → ℝ} (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {u h : FreeL2 eta} {g g' : Fin eta × Fin 3 → FreeL2 eta}
    {g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta}
    {Y : FiniteElectronPair eta → FreeL2 eta}
    {Z : FiniteElectronPair eta → Fin eta × Fin 3 → FreeL2 eta}
    (hK : HasFreeWeakKinetic sys.mass u (h - pairL2 sys.charge Y)) (hg : HasWeakGrad u g)
    (hg' : HasWeakGrad h g') (hg2 : ∀ b, HasWeakGrad (g b) (g2 b))
    (hY : ∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * u r)
    (hZ : ∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * g a r) :
    HasGLHamiltonian sys L θ (X.toCutoff.commT hL sys.mass u g)
      (commH hL X sys.charge u h g g' g2 Y -
        zeroModeShift sys L θ • X.toCutoff.commT hL sys.mass u g) := by
  set C₀ := zeroModeShift sys L θ with hC₀
  have hrt := ret_of_tsupport hret
  -- the potential part
  set P₂ : MolecularPositionL2 eta := ∑ a : Fin eta × Fin 3, kc sys.mass a •
    ((X.toCutoff.d2W a).cutL2 hL (pairL2 sys.charge Y) +
      (2 : ℂ) • (X.toCutoff.d1W a).cutL2 hL (pairL2 sys.charge fun p => Z p a)) with hP₂
  have hpot : HasL2PointwisePotential volume (gLFourierPotential sys L θ)
      (X.toCutoff.commT hL sys.mass u g) (P₂ - C₀ • X.toCutoff.commT hL sys.mass u g) := by
    have h1 : HasL2PointwisePotential volume (gLFourierPotential sys L θ)
        (X.toCutoff.commT hL sys.mass u g) (∑ a : Fin eta × Fin 3, kc sys.mass a •
          (((X.toCutoff.d2W a).cutL2 hL (pairL2 sys.charge Y) -
            C₀ • (X.toCutoff.d2W a).cutL2 hL u) +
          (2 : ℂ) • ((X.toCutoff.d1W a).cutL2 hL (pairL2 sys.charge fun p => Z p a) -
            C₀ • (X.toCutoff.d1W a).cutL2 hL (g a)))) := by
      rw [commT_eq]
      have hA : ∀ a, HasL2PointwisePotential volume (gLFourierPotential sys L θ)
          ((X.toCutoff.d2W a).cutL2 hL u) ((X.toCutoff.d2W a).cutL2 hL (pairL2 sys.charge Y) -
            C₀ • (X.toCutoff.d2W a).cutL2 hL u) := fun a =>
        potential_cutL2 sys hL hR0 hρ hone P hP hpos _ (fun r hr => hrt r (X.d2W_mem a hr))
          (hasL2PointwisePotential_pairL2 sys P hY)
      have hB : ∀ a, HasL2PointwisePotential volume (gLFourierPotential sys L θ)
          ((X.toCutoff.d1W a).cutL2 hL (g a))
          ((X.toCutoff.d1W a).cutL2 hL (pairL2 sys.charge fun p => Z p a) -
            C₀ • (X.toCutoff.d1W a).cutL2 hL (g a)) := fun a =>
        potential_cutL2 sys hL hR0 hρ hone P hP hpos _ (fun r hr => hrt r (X.d1W_mem a hr))
          (hasL2PointwisePotential_pairL2 sys P fun p => hZ p a)
      exact hasL2Pot_sum _ fun a _ => hasL2Pot_smul ((hA a).add (hasL2Pot_smul (hB a) 2)) _
    have e : (∑ a : Fin eta × Fin 3, kc sys.mass a •
          (((X.toCutoff.d2W a).cutL2 hL (pairL2 sys.charge Y) -
            C₀ • (X.toCutoff.d2W a).cutL2 hL u) +
          (2 : ℂ) • ((X.toCutoff.d1W a).cutL2 hL (pairL2 sys.charge fun p => Z p a) -
            C₀ • (X.toCutoff.d1W a).cutL2 hL (g a)))) =
        P₂ - C₀ • X.toCutoff.commT hL sys.mass u g := by
      rw [hP₂, commT_eq, Finset.smul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by module
    rwa [e] at h1
  refine hasGLHamiltonian_of_fourierTests sys hpot fun s c => ?_
  -- the kinetic part
  have e2 : commH hL X sys.charge u h g g' g2 Y - C₀ • X.toCutoff.commT hL sys.mass u g -
      (P₂ - C₀ • X.toCutoff.commT hL sys.mass u g) = commH hL X sys.charge u h g g' g2 Y - P₂ := by
    abel
  have hΨ : ContDiff ℝ 3 (liftTest L s c) := contDiff_liftTest L s c 3
  have hid := freeId_comm hL X sys.charge hK hg hg' hg2 hY hZ hΨ
  have iP : inner ℂ ((ContinuousMap.toLp 2 volume ℂ) (molecularPositionFourierTest eta s c)) P₂ =
      ((tScale eta L : ℂ))⁻¹ * ∑ a : Fin eta × Fin 3, kc sys.mass a *
        (IP (liftTest L s c) (dirD a (dirD a X.χ)) (pairL2 sys.charge Y) +
          2 * IP (liftTest L s c) (dirD a X.χ) (pairL2 sys.charge fun p => Z p a)) := by
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
  rw [e2, inner_sub_right, inner_commH, iP, iK, hid, ← mul_sub]
  congr 1
  have e3 : ∑ a : Fin eta × Fin 3, kc sys.mass a * (termA X (liftTest L s c) u h g a -
        IP (liftTest L s c) (dirD a (dirD a X.χ)) (pairL2 sys.charge Y)) +
      ∑ a : Fin eta × Fin 3, 2 * kc sys.mass a * (termB X (liftTest L s c) u g g' g2 a -
        IP (liftTest L s c) (dirD a X.χ) (pairL2 sys.charge fun p => Z p a)) =
      ∑ a : Fin eta × Fin 3, kc sys.mass a * termA X (liftTest L s c) u h g a +
        ∑ a : Fin eta × Fin 3, 2 * kc sys.mass a * termB X (liftTest L s c) u g g' g2 a -
        ∑ a : Fin eta × Fin 3, kc sys.mass a *
          (IP (liftTest L s c) (dirD a (dirD a X.χ)) (pairL2 sys.charge Y) +
            2 * IP (liftTest L s c) (dirD a X.χ) (pairL2 sys.charge fun p => Z p a)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e3]
  ring

end Relation

end FreeBoundary
