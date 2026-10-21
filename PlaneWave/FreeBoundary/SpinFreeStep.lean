import PlaneWave.FreeBoundary.FreeDynamicsBOUniform

/-!
# Spin, part 1: the free-space step with internal spin

The spin-inclusive free-space space `L²(ℝ^{3η}) ⊗ ℂ^ς` is `FreeSpinL2 eta ς`: one component for
each spin configuration `σ ∈ ς`, with the Hilbert norm `‖Ψ‖² = Σ_σ ‖Ψ_σ‖²`. The Hamiltonian does
not act on spin, so a solution curve `Ψ` solves the free-space equation in each component, and the
torus evolution acts on each component (`spinIso`). With the leakage summed over the spin
components, `Σ_σ ‖1_{(B^one)ᶜ} Ψ_σ‖² ≤ ε²` and `Σ_σ ‖1_S ∇Ψ_σ‖² ≤ ε²`, Duhamel's estimate in the
spin-inclusive space gives the bound of `free_dyn_torus` with the same constant
`C = 3η (D₁ + D₂/2)` and the Hilbert norms `‖Ψ(t)‖ + ‖Ψ(0)‖`; no factor depends on the number of
spin components.

* `piLpMap`, `spinIso`: operators acting on each component;
* `Cutoff.norm_commT_le₂`: the commutator bound with separate leakages;
* `Cutoff.sum_norm_commT_sq_le`: `Σ_σ ‖T([K, χ] Ψ_σ)‖² ≤ (C ε)²`;
* `Cutoff.obs_cut_le`: the observable with and without the cutoff;
* **`free_dyn_torus_spin`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

variable {eta : ℕ}

/-! ## Componentwise operators -/

section Components

variable {ς : Type*} [Fintype ς]

/-- A continuous linear map applied to each component of `PiLp 2`. -/
noncomputable def piLpMap {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (A : F →L[ℂ] G) :
    PiLp 2 (fun _ : ς => F) →L[ℂ] PiLp 2 (fun _ : ς => G) :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ς => G)).symm :
      (ς → G) →L[ℂ] PiLp 2 (fun _ : ς => G)).comp
    ((ContinuousLinearMap.pi fun σ => A.comp (ContinuousLinearMap.proj σ)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ς => F) :
        PiLp 2 (fun _ : ς => F) →L[ℂ] (ς → F)))

lemma piLpMap_apply {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (A : F →L[ℂ] G) (x : PiLp 2 (fun _ : ς => F))
    (σ : ς) : piLpMap A x σ = A (x σ) :=
  rfl

/-- If `‖A v‖ ≤ c ‖v‖`, then `‖(A ⊗ 1) x‖ ≤ c ‖x‖`. -/
lemma norm_piLpMap_le {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {A : F →L[ℂ] G} {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ v, ‖A v‖ ≤ c * ‖v‖) (x : PiLp 2 (fun _ : ς => F)) :
    ‖piLpMap A x‖ ≤ c * ‖x‖ := by
  rw [PiLp.norm_eq_of_L2 (piLpMap A x), PiLp.norm_eq_of_L2 x]
  calc Real.sqrt (∑ σ, ‖piLpMap A x σ‖ ^ 2) ≤ Real.sqrt (∑ σ, (c * ‖x σ‖) ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun σ _ => ?_)
        rw [piLpMap_apply]
        exact pow_le_pow_left₀ (norm_nonneg _) (hA _) 2
    _ = c * Real.sqrt (∑ σ, ‖x σ‖ ^ 2) := by
        have e : (∑ σ, (c * ‖x σ‖) ^ 2) = c ^ 2 * ∑ σ, ‖x σ‖ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by ring
        rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

/-- A family of isometries acting on each component (`U(t) ⊗ 1`). -/
noncomputable def spinIso {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : ℝ → E ≃ₗᵢ[ℂ] E) (t : ℝ) : PiLp 2 (fun _ : ς => E) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : ς => E) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun _ => U t

lemma spinIso_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : ℝ → E ≃ₗᵢ[ℂ] E) (t : ℝ) (x : PiLp 2 (fun _ : ς => E)) (σ : ς) :
    spinIso U t x σ = U t (x σ) :=
  rfl

end Components

/-- The spin-inclusive free-space space `L²(ℝ^{3η}) ⊗ ℂ^ς`, one component for each spin
configuration. -/
abbrev FreeSpinL2 (eta : ℕ) (ς : Type*) [Fintype ς] := PiLp 2 (fun _ : ς => FreeL2 eta)

/-! ## The commutator with spin -/

namespace Cutoff

variable {L : ℝ}

/-- **The commutator bound with separate leakages**: `‖1_{(B^one)ᶜ} f‖ ≤ e₀` and `‖1_S ∇f‖ ≤ e₁`
give `‖T([K, χ] f)‖ ≤ 3η (D₁ e₁ + (D₂/2) e₀)` (masses `≥ 1`). -/
lemma norm_commT_le₂ (X : Cutoff eta L) (hL : 0 < L) {m : Fin eta → ℝ} (hm : ∀ i, 1 ≤ m i)
    {S Bone : Set (Rcfg eta)} (hSm : MeasurableSet S) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    (f : FreeL2 eta) (g : Fin eta × Fin 3 → FreeL2 eta) {e0 e1 : ℝ} (he0 : 0 ≤ e0)
    (he1 : 0 ≤ e1) (h0 : ∫ r in Boneᶜ, ‖f r‖ ^ 2 ≤ e0 ^ 2)
    (h1 : ∫ r in S, ∑ a, ‖g a r‖ ^ 2 ≤ e1 ^ 2) :
    ‖X.commT hL m f g‖ ≤ (Fintype.card (Fin eta × Fin 3) : ℝ) * (X.D1 * e1 + X.D2 / 2 * e0) := by
  have hf2 : Integrable (fun r => ‖f r‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hg2 : ∀ a, Integrable (fun r => ‖g a r‖ ^ 2) := fun a =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (g a))).mp (Lp.memLp (g a))
  have hS0 : ∫ r in S, ‖f r‖ ^ 2 ≤ e0 ^ 2 :=
    le_trans (setIntegral_mono_set hf2.integrableOn (ae_of_all _ fun r => by positivity)
      hSB.eventuallyLE) h0
  have hS1 : ∀ a, ∫ r in S, ‖g a r‖ ^ 2 ≤ e1 ^ 2 := by
    intro a
    refine le_trans (integral_mono_of_nonneg (ae_of_all _ fun r => by positivity)
      (integrable_finsetSum _ fun b _ => hg2 b).integrableOn (ae_of_all _ fun r => ?_)) h1
    exact Finset.single_le_sum (f := fun b => ‖g b r‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ a)
  have hT2 : ∀ a, ‖(X.d2W a).cutL2 hL f‖ ≤ X.D2 * e0 := fun a =>
    (X.d2W a).norm_cutL2_le_of_supp hL hSm (fun r hr => by simp [d2W, hd2S r hr a]) f he0 hS0
  have hT1 : ∀ a, ‖(X.d1W a).cutL2 hL (g a)‖ ≤ X.D1 * e1 := fun a =>
    (X.d1W a).norm_cutL2_le_of_supp hL hSm (fun r hr => by simp [d1W, hdS r hr a]) (g a) he1
      (hS1 a)
  have hc : ∀ a : Fin eta × Fin 3, ‖(-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹‖ ≤ 1 / 2 := by
    intro a
    have hm0 : 0 < m a.1 := lt_of_lt_of_le one_pos (hm a.1)
    rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [h2]
    have h3 : (m a.1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hm a.1)
    nlinarith
  unfold commT
  calc ‖∑ a : Fin eta × Fin 3, ((-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹) •
        ((X.d2W a).cutL2 hL f + (2 : ℂ) • (X.d1W a).cutL2 hL (g a))‖
      ≤ ∑ a : Fin eta × Fin 3, ‖((-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹) •
        ((X.d2W a).cutL2 hL f + (2 : ℂ) • (X.d1W a).cutL2 hL (g a))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin eta × Fin 3, 1 / 2 * (X.D2 * e0 + 2 * (X.D1 * e1)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_smul]
        have hv : ‖(X.d2W a).cutL2 hL f + (2 : ℂ) • (X.d1W a).cutL2 hL (g a)‖ ≤
            X.D2 * e0 + 2 * (X.D1 * e1) := by
          refine (norm_add_le _ _).trans (add_le_add (hT2 a) ?_)
          rw [norm_smul]
          have h2 : ‖(2 : ℂ)‖ = 2 := by simp
          rw [h2]
          exact mul_le_mul_of_nonneg_left (hT1 a) (by norm_num)
        exact mul_le_mul (hc a) hv (norm_nonneg _) (by norm_num)
    _ = (Fintype.card (Fin eta × Fin 3) : ℝ) * (X.D1 * e1 + X.D2 / 2 * e0) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- **The spin-summed commutator bound**: if the leakages summed over the spin components are at
most `ε²`, then `Σ_σ ‖T([K, χ] Ψ_σ)‖² ≤ (3η (D₁ + D₂/2) ε)²`. -/
lemma sum_norm_commT_sq_le (X : Cutoff eta L) (hL : 0 < L) {m : Fin eta → ℝ}
    (hm : ∀ i, 1 ≤ m i) {S Bone : Set (Rcfg eta)} (hSm : MeasurableSet S) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ς : Type*} [Fintype ς] (f : ς → FreeL2 eta) (g : ς → Fin eta × Fin 3 → FreeL2 eta)
    {ε : ℝ} (h0 : ∑ σ, ∫ r in Boneᶜ, ‖f σ r‖ ^ 2 ≤ ε ^ 2)
    (h1 : ∑ σ, ∫ r in S, ∑ a, ‖g σ a r‖ ^ 2 ≤ ε ^ 2) :
    ∑ σ, ‖X.commT hL m (f σ) (g σ)‖ ^ 2 ≤ (X.commConst * ε) ^ 2 := by
  set n : ℝ := (Fintype.card (Fin eta × Fin 3) : ℝ) with hn
  set I0 : ς → ℝ := fun σ => ∫ r in Boneᶜ, ‖f σ r‖ ^ 2 with hI0
  set I1 : ς → ℝ := fun σ => ∫ r in S, ∑ a, ‖g σ a r‖ ^ 2 with hI1
  have p0 : ∀ σ, 0 ≤ I0 σ := fun σ => setIntegral_nonneg_of_ae (ae_of_all _ fun r => by positivity)
  have p1 : ∀ σ, 0 ≤ I1 σ := fun σ => setIntegral_nonneg_of_ae (ae_of_all _ fun r => by positivity)
  have hb : ∀ σ, ‖X.commT hL m (f σ) (g σ)‖ ≤
      n * (X.D1 * Real.sqrt (I1 σ) + X.D2 / 2 * Real.sqrt (I0 σ)) := fun σ =>
    X.norm_commT_le₂ hL hm hSm hSB hdS hd2S (f σ) (g σ) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt (p0 σ)]) (by rw [Real.sq_sqrt (p1 σ)])
  rcases isEmpty_or_nonempty (Fin eta × Fin 3) with he | ⟨⟨a0⟩⟩
  · have hn0 : n = 0 := by rw [hn, Fintype.card_eq_zero, Nat.cast_zero]
    have hz : ∀ σ, ‖X.commT hL m (f σ) (g σ)‖ = 0 := fun σ =>
      le_antisymm (by simpa [hn0] using hb σ) (norm_nonneg _)
    simp only [hz]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  · have hD1 : 0 ≤ X.D1 := (abs_nonneg _).trans (X.d1 0 a0)
    have hD2 : 0 ≤ X.D2 := (abs_nonneg _).trans (X.d2 0 a0)
    set c1 : ℝ := n ^ 2 * (X.D1 ^ 2 + X.D1 * X.D2 / 2) with hc1
    set c2 : ℝ := n ^ 2 * (X.D1 * X.D2 / 2 + X.D2 ^ 2 / 4) with hc2
    have hc10 : 0 ≤ c1 := by positivity
    have hc20 : 0 ≤ c2 := by positivity
    have key : ∀ σ, ‖X.commT hL m (f σ) (g σ)‖ ^ 2 ≤ c1 * I1 σ + c2 * I0 σ := by
      intro σ
      have hu := Real.sq_sqrt (p1 σ)
      have hv := Real.sq_sqrt (p0 σ)
      have hu0 := Real.sqrt_nonneg (I1 σ)
      have hv0 := Real.sqrt_nonneg (I0 σ)
      have huv : Real.sqrt (I1 σ) * Real.sqrt (I0 σ) ≤ (I0 σ + I1 σ) / 2 := by
        nlinarith [sq_nonneg (Real.sqrt (I1 σ) - Real.sqrt (I0 σ))]
      have hs : (X.D1 * Real.sqrt (I1 σ) + X.D2 / 2 * Real.sqrt (I0 σ)) ^ 2 ≤
          (X.D1 ^ 2 + X.D1 * X.D2 / 2) * I1 σ + (X.D1 * X.D2 / 2 + X.D2 ^ 2 / 4) * I0 σ := by
        have hDD : 0 ≤ X.D1 * X.D2 := mul_nonneg hD1 hD2
        have h := mul_le_mul_of_nonneg_left huv hDD
        nlinarith
      have hb2 := pow_le_pow_left₀ (norm_nonneg _) (hb σ) 2
      calc ‖X.commT hL m (f σ) (g σ)‖ ^ 2
          ≤ (n * (X.D1 * Real.sqrt (I1 σ) + X.D2 / 2 * Real.sqrt (I0 σ))) ^ 2 := hb2
        _ = n ^ 2 * (X.D1 * Real.sqrt (I1 σ) + X.D2 / 2 * Real.sqrt (I0 σ)) ^ 2 := by ring
        _ ≤ n ^ 2 * ((X.D1 ^ 2 + X.D1 * X.D2 / 2) * I1 σ +
            (X.D1 * X.D2 / 2 + X.D2 ^ 2 / 4) * I0 σ) :=
          mul_le_mul_of_nonneg_left hs (sq_nonneg n)
        _ = c1 * I1 σ + c2 * I0 σ := by rw [hc1, hc2]; ring
    have hsum : ∑ σ, (c1 * I1 σ + c2 * I0 σ) = c1 * ∑ σ, I1 σ + c2 * ∑ σ, I0 σ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc ∑ σ, ‖X.commT hL m (f σ) (g σ)‖ ^ 2 ≤ ∑ σ, (c1 * I1 σ + c2 * I0 σ) :=
          Finset.sum_le_sum fun σ _ => key σ
      _ = c1 * ∑ σ, I1 σ + c2 * ∑ σ, I0 σ := hsum
      _ ≤ c1 * ε ^ 2 + c2 * ε ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hc10) (mul_le_mul_of_nonneg_left h0 hc20)
      _ = (X.commConst * ε) ^ 2 := by
          rw [hc1, hc2]
          unfold commConst
          rw [← hn]
          ring

/-- The observable with and without the cutoff: for `0 ≤ χ_o ≤ 1`,
`|∫ χ_o |f|² - ∫ χ_o χ² |f|²| ≤ ‖1_{(B^one)ᶜ} f‖²`. -/
lemma obs_cut_le (X : Cutoff eta L) {Bone : Set (Rcfg eta)} (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) {χo : Rcfg eta → ℝ} (hχo0 : ∀ r, 0 ≤ χo r)
    (hχo1 : ∀ r, χo r ≤ 1) (hχom : Measurable χo) (f : FreeL2 eta) :
    |(∫ r, χo r * ‖f r‖ ^ 2) - ∫ r, χo r * (X.χ r ^ 2 * ‖f r‖ ^ 2)| ≤
      ∫ r in Boneᶜ, ‖f r‖ ^ 2 := by
  have hf2 : Integrable (fun r => ‖f r‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hχm : Measurable X.χ := X.smooth.continuous.measurable
  have hχ2 : ∀ r, X.χ r ^ 2 ≤ 1 := fun r => by
    have := X.le_one r
    have := X.nonneg r
    nlinarith
  have hI1 : Integrable (fun r => χo r * ‖f r‖ ^ 2) :=
    hf2.bdd_mul (c := 1) hχom.aestronglyMeasurable (ae_of_all _ fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχo0 r)]
      exact hχo1 r)
  have hI2 : Integrable (fun r => χo r * (X.χ r ^ 2 * ‖f r‖ ^ 2)) := by
    have h := hf2.bdd_mul (c := 1) (hχom.mul (hχm.pow_const 2)).aestronglyMeasurable
      (ae_of_all _ fun r => by
        simp only [Pi.mul_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hχo0 r) (sq_nonneg _))]
        nlinarith [hχo0 r, hχo1 r, sq_nonneg (X.χ r), hχ2 r])
    refine h.congr (ae_of_all _ fun r => ?_)
    simp only [Pi.mul_apply]
    ring
  rw [← integral_sub hI1 hI2]
  have hpt0 : ∀ r, 0 ≤ χo r * ‖f r‖ ^ 2 - χo r * (X.χ r ^ 2 * ‖f r‖ ^ 2) := fun r => by
    have h2 : 0 ≤ χo r * ‖f r‖ ^ 2 * (1 - X.χ r ^ 2) :=
      mul_nonneg (mul_nonneg (hχo0 r) (sq_nonneg _)) (by linarith [hχ2 r])
    nlinarith
  rw [abs_of_nonneg (integral_nonneg hpt0)]
  calc ∫ r, (χo r * ‖f r‖ ^ 2 - χo r * (X.χ r ^ 2 * ‖f r‖ ^ 2))
      ≤ ∫ r, Boneᶜ.indicator (fun r => ‖f r‖ ^ 2) r := by
        refine integral_mono_of_nonneg (ae_of_all _ hpt0) (hf2.indicator hBm.compl)
          (ae_of_all _ fun r => ?_)
        by_cases hr : r ∈ Bone
        · rw [indicator_of_notMem (fun h : r ∈ Boneᶜ => h hr)]
          simp [hχB r hr]
        · rw [indicator_of_mem hr]
          have h1 := hχo1 r
          have h2 : 0 ≤ X.χ r ^ 2 * ‖f r‖ ^ 2 := by positivity
          nlinarith [hχo0 r, sq_nonneg (‖f r‖)]
    _ = ∫ r in Boneᶜ, ‖f r‖ ^ 2 := integral_indicator hBm.compl

end Cutoff

/-! ## Two facts in a Hilbert space -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `|⟨x, Gx⟩ - ⟨y, Gy⟩| ≤ ‖x - y‖ (‖x‖ + ‖y‖)` for `‖G‖ ≤ 1`. -/
lemma norm_inner_sub_inner_le (G : E →L[ℂ] E) (hG : ∀ v, ‖G v‖ ≤ ‖v‖) (x y : E) :
    ‖⟪x, G x⟫_ℂ - ⟪y, G y⟫_ℂ‖ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := by
  have h : ⟪x, G x⟫_ℂ - ⟪y, G y⟫_ℂ = ⟪x - y, G x⟫_ℂ + ⟪y, G (x - y)⟫_ℂ := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [h]
  calc ‖⟪x - y, G x⟫_ℂ + ⟪y, G (x - y)⟫_ℂ‖
      ≤ ‖x - y‖ * ‖G x‖ + ‖y‖ * ‖G (x - y)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hG _) (norm_nonneg _))
    _ = ‖x - y‖ * (‖x‖ + ‖y‖) := by ring

/-- `⟨e y, G (e y)⟩ = ⟨y, G y⟩` for `|e| = 1`. -/
lemma inner_unit_smul (G : E →L[ℂ] E) {e : ℂ} (he : ‖e‖ = 1) (y : E) :
    ⟪e • y, G (e • y)⟫_ℂ = ⟪y, G y⟫_ℂ := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', he]
  simp

/-- `Σ a (b + c) ≤ √(Σ a²) (√(Σ b²) + √(Σ c²))`. -/
lemma sum_mul_add_le_sqrt {ς : Type*} [Fintype ς] (a b c : ς → ℝ) :
    ∑ σ, a σ * (b σ + c σ) ≤
      Real.sqrt (∑ σ, a σ ^ 2) * (Real.sqrt (∑ σ, b σ ^ 2) + Real.sqrt (∑ σ, c σ ^ 2)) := by
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a c
  have e : ∑ σ, a σ * (b σ + c σ) = ∑ σ, a σ * b σ + ∑ σ, a σ * c σ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => by ring
  rw [e, mul_add]
  exact add_le_add h1 h2

/-- The evolution on each component is a strongly continuous group, and solves the Schrödinger
equation for the componentwise relation. -/
lemma spinIso_props {ς : Type*} [Fintype ς] (U : ℝ → E ≃ₗᵢ[ℂ] E) (Rel : E → E → Prop)
    (hU0 : ∀ x, U 0 x = x) (hUadd : ∀ s t x, U (s + t) x = U s (U t x))
    (hUcont : ∀ x, Continuous fun t => U t x)
    (hUderiv : ∀ t f h, Rel f h → HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t) :
    (∀ x : PiLp 2 (fun _ : ς => E), spinIso U 0 x = x) ∧
      (∀ s t (x : PiLp 2 (fun _ : ς => E)), spinIso U (s + t) x = spinIso U s (spinIso U t x)) ∧
      (∀ x : PiLp 2 (fun _ : ς => E), Continuous fun t => spinIso U t x) ∧
      (∀ t (Φ Ζ : PiLp 2 (fun _ : ς => E)), (∀ σ, Rel (Φ σ) (Ζ σ)) →
        HasDerivAt (fun s => spinIso U s Φ) (-(Complex.I • spinIso U t Ζ)) t) := by
  classical
  refine ⟨fun x => PiLp.ext fun σ => hU0 (x σ), fun s t x => PiLp.ext fun σ => hUadd s t (x σ),
    fun x => (PiLp.continuous_toLp 2 (fun _ : ς => E)).comp
      (continuous_pi fun σ => hUcont (x σ)), fun t Φ Ζ hH => ?_⟩
  have hd : HasDerivAt (fun s => (fun σ => U s (Φ σ) : ς → E))
      (fun σ => -(Complex.I • U t (Ζ σ))) t :=
    hasDerivAt_pi.2 fun σ => hUderiv t (Φ σ) (Ζ σ) (hH σ)
  have hd2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ς => E)).symm.hasFDerivAt.comp_hasDerivAt
    t hd
  have e1 : (fun s => spinIso U s Φ) = (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : ς => E)).symm ∘ fun s σ => U s (Φ σ) :=
    rfl
  have e2 : -(Complex.I • spinIso U t Ζ) = (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : ς => E)).symm (fun σ => -(Complex.I • U t (Ζ σ))) :=
    rfl
  rw [e1, e2]
  exact hd2

end Hilbert

/-! ## The free-space step with spin -/

section Step

variable {ν : Type} [Fintype ν]

/-- **The free-space step of `prop:free-dyn` with internal spin.** For a solution curve `Ψ` of the
free-space equation in `L²(ℝ^{3η}) ⊗ ℂ^ς` (each component solves it; `∇Ψ_σ` the weak gradients)
whose leakages, summed over the spin components, are at most `ε²` on `[0, t]`, the transplanted
cut state `φ(s) = (T(χ Ψ_σ(s)))_σ` and the torus evolution `U(t)` on each component satisfy
* `‖φ(t) - e^{-iC₀t} (U(t) ⊗ 1) φ(0)‖ ≤ C ε t`, `C = 3η (D₁ + D₂/2)`;
* for `0 ≤ χ_o ≤ 1` with continuous torus version `G`,
  `|Σ_σ ⟨Ψ_σ(t), χ_o Ψ_σ(t)⟩ - Σ_σ ⟨U(t)φ_σ(0), G U(t)φ_σ(0)⟩| ≤ ε² + (‖Ψ(t)‖ + ‖Ψ(0)‖) C ε t`,
with the Hilbert norms of the spin-inclusive space. -/
theorem free_dyn_torus_spin (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hθ : Profile R θ) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (U : ℝ → MolecularPositionL2 eta ≃ₗᵢ[ℂ] MolecularPositionL2 eta)
    (hU0 : ∀ ψ, U 0 ψ = ψ) (hUadd : ∀ s t ψ, U (s + t) ψ = U s (U t ψ))
    (hUcont : ∀ ψ, Continuous fun t => U t ψ)
    (hUderiv : ∀ t f h, HasGLHamiltonian sys L θ f h →
      HasDerivAt (fun s => U s f) (-(Complex.I • U t h)) t)
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ς : Type*} [Fintype ς]
    {Ψ HΨ : ℝ → FreeSpinL2 eta ς} {grad : ℝ → ς → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt Ψ (-(Complex.I • HΨ s)) s)
    (hHam : ∀ s σ, HasFreeHamiltonian sys P (Ψ s σ) (HΨ s σ))
    (hgrad : ∀ s σ, HasWeakGrad (Ψ s σ) (grad s σ))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in Boneᶜ, ‖Ψ s σ r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∑ σ, ∫ r in S, ∑ a, ‖grad s σ a r‖ ^ 2 ≤ ε ^ 2)
    {χo : Rcfg eta → ℝ} (hχo0 : ∀ r, 0 ≤ χo r) (hχo1 : ∀ r, χo r ≤ 1) (hχom : Measurable χo)
    (G : C(MolecularPositionTorus eta, ℂ)) (hG : ∀ x, G x = (χo (cellCoord L x) : ℂ)) :
    ‖piLpMap (X.chiW.cutL2 hL) (Ψ t) - Complex.exp (-(Complex.I * (zeroModeShift sys L θ).re * t))
        • spinIso U t (piLpMap (X.chiW.cutL2 hL) (Ψ 0))‖ ≤ X.commConst * ε * t ∧
      ‖((∑ σ, ∫ r, χo r * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) - ∑ σ, ⟪U t (X.chiW.cutL2 hL (Ψ 0 σ)),
          mulCLM G (U t (X.chiW.cutL2 hL (Ψ 0 σ)))⟫_ℂ‖ ≤
        ε ^ 2 + (‖Ψ t‖ + ‖Ψ 0‖) * (X.commConst * ε * t) := by
  classical
  have hC₀ := zeroModeShift_re_eq sys hθ L
  obtain ⟨hU0s, hUadds, hUconts, hUderivs⟩ := spinIso_props (ς := ς) U (HasGLHamiltonian sys L θ)
    hU0 hUadd hUcont hUderiv
  -- the commutator on each component
  obtain ⟨commS, hcommS⟩ : ∃ c : ℝ → PiLp 2 (fun _ : ς => MolecularPositionL2 eta),
      c = fun s => WithLp.toLp 2 fun σ => X.commT hL sys.mass (Ψ s σ) (grad s σ) := ⟨_, rfl⟩
  have hcomm_apply : ∀ s σ, commS s σ = X.commT hL sys.mass (Ψ s σ) (grad s σ) := by
    intro s σ
    rw [hcommS]
  have hrel : ∀ s σ, HasGLHamiltonian sys L θ (piLpMap (X.chiW.cutL2 hL) (Ψ s) σ)
      ((piLpMap (X.chiW.cutL2 hL) (HΨ s) - zeroModeShift sys L θ •
        piLpMap (X.chiW.cutL2 hL) (Ψ s) + commS s) σ) := by
    intro s σ
    rw [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, piLpMap_apply, piLpMap_apply,
      hcomm_apply]
    exact transplant_hasGLHamiltonian sys hL hR0 hρ hone P hP hpos X hret (hHam s σ) (hgrad s σ)
  have hΨσ : ∀ s σ, HasDerivAt (fun s => Ψ s σ) (-(Complex.I • HΨ s σ)) s := fun s σ =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ς => FreeL2 eta) σ).hasFDerivAt.comp_hasDerivAt s (hψd s)
  have hderiv : ∀ s, HasDerivAt (fun s => piLpMap (X.chiW.cutL2 hL) (Ψ s))
      (-(Complex.I • ((piLpMap (X.chiW.cutL2 hL) (HΨ s) - zeroModeShift sys L θ •
        piLpMap (X.chiW.cutL2 hL) (Ψ s) + commS s) +
        (((zeroModeShift sys L θ).re : ℝ) : ℂ) • piLpMap (X.chiW.cutL2 hL) (Ψ s) +
          -commS s))) s := by
    intro s
    have hc : HasDerivAt (fun s => (fun σ => X.chiW.cutL2 hL (Ψ s σ) :
        ς → MolecularPositionL2 eta)) (fun σ => X.chiW.cutL2 hL (-(Complex.I • HΨ s σ))) s :=
      hasDerivAt_pi.2 fun σ =>
        ((X.chiW.cutL2 hL).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hΨσ s σ)
    have hd2 := (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : ς => MolecularPositionL2 eta)).symm.hasFDerivAt.comp_hasDerivAt s hc
    have e1 : (fun s => piLpMap (X.chiW.cutL2 hL) (Ψ s)) = (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : ς => MolecularPositionL2 eta)).symm ∘ fun s σ => X.chiW.cutL2 hL (Ψ s σ) :=
      rfl
    have e2 : -(Complex.I • ((piLpMap (X.chiW.cutL2 hL) (HΨ s) - zeroModeShift sys L θ •
        piLpMap (X.chiW.cutL2 hL) (Ψ s) + commS s) +
        (((zeroModeShift sys L θ).re : ℝ) : ℂ) • piLpMap (X.chiW.cutL2 hL) (Ψ s) +
          -commS s)) = (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : ς => MolecularPositionL2 eta)).symm
          (fun σ => X.chiW.cutL2 hL (-(Complex.I • HΨ s σ))) := by
      refine PiLp.ext fun σ => ?_
      simp only [PiLp.neg_apply, PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, piLpMap_apply,
        hcomm_apply]
      change _ = X.chiW.cutL2 hL (-(Complex.I • HΨ s σ))
      rw [hC₀, map_neg, map_smul]
      module
    rw [e1, e2]
    exact hd2
  have hc0 : 0 ≤ X.commConst * ε := by
    rcases isEmpty_or_nonempty (Fin eta × Fin 3) with he | ⟨⟨a0⟩⟩
    · unfold Cutoff.commConst
      rw [Fintype.card_eq_zero, Nat.cast_zero, zero_mul, zero_mul]
    · have h1 : 0 ≤ X.D1 := (abs_nonneg _).trans (X.d1 0 a0)
      have h2 : 0 ≤ X.D2 := (abs_nonneg _).trans (X.d2 0 a0)
      unfold Cutoff.commConst
      positivity
  have hbound : ∀ s ∈ Icc 0 t, ‖-commS s‖ ≤ X.commConst * ε := by
    intro s hs
    rw [norm_neg]
    have hsq : ‖commS s‖ ^ 2 ≤ (X.commConst * ε) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [hcomm_apply]
      exact X.sum_norm_commT_sq_le hL sys.one_le_mass hSm hSB hdS hd2S (fun σ => Ψ s σ)
        (grad s) (hleak0 s hs) (hleak1 s hs)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc0 two_ne_zero).mp hsq
  have hD := duhamel_phase (fun Φ Ζ : PiLp 2 (fun _ : ς => MolecularPositionL2 eta) =>
      ∀ σ, HasGLHamiltonian sys L θ (Φ σ) (Ζ σ)) (spinIso U) hU0s hUadds hUconts hUderivs
    (φ := fun s => piLpMap (X.chiW.cutL2 hL) (Ψ s))
    (ζ := fun s => piLpMap (X.chiW.cutL2 hL) (HΨ s) - zeroModeShift sys L θ •
      piLpMap (X.chiW.cutL2 hL) (Ψ s) + commS s)
    (r := fun s => -commS s) (zeroModeShift sys L θ).re (fun s σ => hrel s σ) hderiv ht hbound
  refine ⟨hD, ?_⟩
  -- the observable
  obtain ⟨Xt, hXt⟩ : ∃ x : PiLp 2 (fun _ : ς => MolecularPositionL2 eta),
      x = piLpMap (X.chiW.cutL2 hL) (Ψ t) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ z : PiLp 2 (fun _ : ς => MolecularPositionL2 eta),
      z = spinIso U t (piLpMap (X.chiW.cutL2 hL) (Ψ 0)) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℂ, e = Complex.exp (-(Complex.I * (zeroModeShift sys L θ).re * t)) :=
    ⟨_, rfl⟩
  rw [← hXt, ← hZ, ← he] at hD
  have he1 : ‖e‖ = 1 := by
    rw [he, Complex.norm_exp]
    simp
  have hG1 : ‖G‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).mpr fun x => by
    rw [hG x, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχo0 _)]
    exact hχo1 _
  have hGv0 : ∀ v, ‖mulCLM G v‖ ≤ 1 * ‖v‖ := fun v => by
    rw [one_mul]
    exact ((mulCLM G).le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg _)
      ((norm_mulCLM_le G).trans hG1))
  have hcut1 : ∀ v : FreeL2 eta, ‖X.chiW.cutL2 hL v‖ ≤ 1 * ‖v‖ := fun v => by
    have h := X.chiW.norm_cutL2_le hL v
    have hB : X.chiW.B = 1 := rfl
    rwa [hB] at h
  have hXn : ‖Xt‖ ≤ ‖Ψ t‖ := by
    have := norm_piLpMap_le zero_le_one hcut1 (Ψ t)
    rwa [one_mul, ← hXt] at this
  have hZn : ‖Z‖ ≤ ‖Ψ 0‖ := by
    rw [hZ, LinearIsometryEquiv.norm_map]
    have := norm_piLpMap_le zero_le_one hcut1 (Ψ 0)
    rwa [one_mul] at this
  have hYn : ‖e • Z‖ ≤ ‖Ψ 0‖ := by
    rw [norm_smul, he1, one_mul]
    exact hZn
  -- the componentwise comparison, summed with the Cauchy-Schwarz inequality
  have hGv1 : ∀ v, ‖mulCLM G v‖ ≤ ‖v‖ := fun v => by
    have := hGv0 v
    rwa [one_mul] at this
  have hw2 : ∀ r, ‖X.chiW.w r‖ ^ 2 = X.χ r ^ 2 := fun r => by
    simp [Cutoff.chiW, Complex.norm_real, sq_abs]
  have hobs : ∀ σ, ⟪Xt σ, mulCLM G (Xt σ)⟫_ℂ =
      ((∫ r, χo r * (X.χ r ^ 2 * ‖Ψ t σ r‖ ^ 2) : ℝ) : ℂ) := by
    intro σ
    rw [hXt, piLpMap_apply]
    have h := X.chiW.inner_cutL2_mulCLM hL G hG (Ψ t σ)
    simp only [hw2] at h
    exact h
  have hcomp : ∀ σ, ‖⟪Xt σ, mulCLM G (Xt σ)⟫_ℂ - ⟪Z σ, mulCLM G (Z σ)⟫_ℂ‖ ≤
      ‖Xt σ - e • Z σ‖ * (‖Xt σ‖ + ‖e • Z σ‖) := by
    intro σ
    have h := norm_inner_sub_inner_le (mulCLM G) hGv1 (Xt σ) (e • Z σ)
    rwa [inner_unit_smul (mulCLM G) he1 (Z σ)] at h
  have hdiff : ‖∑ σ, ⟪Xt σ, mulCLM G (Xt σ)⟫_ℂ - ∑ σ, ⟪Z σ, mulCLM G (Z σ)⟫_ℂ‖ ≤
      ‖Xt - e • Z‖ * (‖Xt‖ + ‖e • Z‖) := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun σ _ => hcomp σ).trans ?_)
    rw [PiLp.norm_eq_of_L2 (Xt - e • Z), PiLp.norm_eq_of_L2 Xt, PiLp.norm_eq_of_L2 (e • Z)]
    simp only [PiLp.sub_apply, PiLp.smul_apply]
    exact sum_mul_add_le_sqrt _ _ _
  have hsumZ : ∑ σ, ⟪Z σ, mulCLM G (Z σ)⟫_ℂ =
      ∑ σ, ⟪U t (X.chiW.cutL2 hL (Ψ 0 σ)), mulCLM G (U t (X.chiW.cutL2 hL (Ψ 0 σ)))⟫_ℂ := by
    rw [hZ]
    rfl
  rw [hsumZ] at hdiff
  -- the leakage of the observable
  have hfree : |(∑ σ, ∫ r, χo r * ‖Ψ t σ r‖ ^ 2) -
      ∑ σ, ∫ r, χo r * (X.χ r ^ 2 * ‖Ψ t σ r‖ ^ 2)| ≤ ε ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    exact (Finset.sum_le_sum fun σ _ =>
      X.obs_cut_le hBm hχB hχo0 hχo1 hχom (Ψ t σ)).trans (hleak0 t ⟨ht, le_rfl⟩)
  have hsplit : ((∑ σ, ∫ r, χo r * ‖Ψ t σ r‖ ^ 2 : ℝ) : ℂ) -
      ∑ σ, ⟪U t (X.chiW.cutL2 hL (Ψ 0 σ)), mulCLM G (U t (X.chiW.cutL2 hL (Ψ 0 σ)))⟫_ℂ =
      ((((∑ σ, ∫ r, χo r * ‖Ψ t σ r‖ ^ 2) -
        ∑ σ, ∫ r, χo r * (X.χ r ^ 2 * ‖Ψ t σ r‖ ^ 2) : ℝ)) : ℂ) +
        (∑ σ, ⟪Xt σ, mulCLM G (Xt σ)⟫_ℂ -
          ∑ σ, ⟪U t (X.chiW.cutL2 hL (Ψ 0 σ)), mulCLM G (U t (X.chiW.cutL2 hL (Ψ 0 σ)))⟫_ℂ) := by
    simp only [hobs]
    push_cast
    ring
  rw [hsplit]
  have hn : ‖Xt - e • Z‖ * (‖Xt‖ + ‖e • Z‖) ≤ (X.commConst * ε * t) * (‖Ψ t‖ + ‖Ψ 0‖) :=
    mul_le_mul hD (add_le_add hXn hYn) (by positivity) (by positivity)
  calc ‖((((∑ σ, ∫ r, χo r * ‖Ψ t σ r‖ ^ 2) -
        ∑ σ, ∫ r, χo r * (X.χ r ^ 2 * ‖Ψ t σ r‖ ^ 2) : ℝ)) : ℂ) +
        (∑ σ, ⟪Xt σ, mulCLM G (Xt σ)⟫_ℂ -
          ∑ σ, ⟪U t (X.chiW.cutL2 hL (Ψ 0 σ)), mulCLM G (U t (X.chiW.cutL2 hL (Ψ 0 σ)))⟫_ℂ)‖
      ≤ ε ^ 2 + ‖Xt - e • Z‖ * (‖Xt‖ + ‖e • Z‖) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ hdiff)
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hfree
    _ ≤ ε ^ 2 + (‖Ψ t‖ + ‖Ψ 0‖) * (X.commConst * ε * t) := by linarith

end Step

end FreeBoundary
