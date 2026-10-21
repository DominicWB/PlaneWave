import PlaneWave.Source.FirstSourceRound

/-!
# Source side, leftovers: the rest of `lem:phi` and `lem:a2`

* Weight tools on `E_n`: Hölder between `ℰ⁰` and `ℰ^{1/2}` (`wt_le_holder_half`), the cube bound
  `‖ℰ^{s+t} v‖ ≤ (1 + A_max)^t ‖ℰ^s v‖`, and register tails from weights
  (`regTail_le_wt`: `‖1{|k_a| > λ} v‖ ≤ (2 m_a/λ²)^s ‖ℰ^s v‖`).
* **`lem:phi`, the remaining displays** of eq:phi-norms and after it, for the backward observable
  flow `φ = e^{iH'τ} A_{p₀} v` of a good `v`: the interpolation `‖ℰ^α φ‖ ≤ C M K^α` for
  `0 ≤ α ≤ 1/2` (`phi_interp`), `‖ℰ^{1+ε} φ‖ ≤ (1+A_max)^ε C M K^{3/2}` (`phi_eps`), and the tails
  `‖1{|k_a| > λ} φ‖ ≤ C M min(λ^{-1} K^{1/2}, λ^{-2} K^{3/2})` (`phi_tail`).
* **`lem:a2`**: for cube vectors, `P Σ_b O Σ_b P = 0` (`sig_O_sig_emb`), so
  `½ P [Σ_b, [Σ_b, O]] P = A^{(2)} = ½ P (Σ_b² O + O Σ_b²) P` (`dcomm_emb`),
  `⟨u, A^{(2)} u⟩ = -Re ⟨Σ_b u, Σ_b O u⟩` (`a2_form`), and for good `u`
  `|⟨u, A^{(2)} u⟩| ≤ c_s² c_E^{2s} M² (C_{s+1} Λ^{4s-1})^{1/2}` (`a2_bound`), of order
  `K^{-5} K^{2s - 1/2} = K^{-4+2(s-3/4)}` (`M₀ ∝ n^{-5}`, `Λ ∝ K`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal

namespace FSSrc1

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Weight tools -/

section Weights

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

omit [Fintype ν] in
/-- **Hölder between `ℰ⁰` and `ℰ^{1/2}`**: `‖ℰ^{θ/2} q‖ ≤ ‖ℰ^{1/2} q‖^θ ‖q‖^{1-θ}`, `0 ≤ θ ≤ 1`. -/
lemma wt_le_holder_half {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (q : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (θ / 2) q‖ ≤
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) q‖ ^ θ * ‖q‖ ^ (1 - θ) := by
  rcases h0.eq_or_lt with h00 | hpos
  · subst h00
    have : FSSpectral.wt (sb eta n) (Asym sys L n) (0 / 2) q = q := by
      ext k
      rw [FSSpectral.wt, fc_sb_apply]
      simp
    rw [this]; simp
  rcases h1.eq_or_lt with h11 | hlt
  · subst h11; simp
  set a : Cfg eta n → ℝ := fun k => (1 + Asym sys L n k) * ‖q.ofLp k‖ ^ 2 with ha
  set c : Cfg eta n → ℝ := fun k => ‖q.ofLp k‖ ^ 2 with hc
  have hA1 : ∀ k, 0 ≤ 1 + Asym sys L n k := fun k => by linarith [FSGalerkin.Asym_nonneg sys L n k]
  have ha0 : ∀ k, 0 ≤ a k := fun k => by simp only [ha]; have := hA1 k; positivity
  have hc0 : ∀ k, 0 ≤ c k := fun k => by simp only [hc]; positivity
  have hconj := Real.holderConjugate_one_div hpos (by linarith : 0 < 1 - θ) (by ring)
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hconj
    (f := fun k => a k ^ θ) (g := fun k => c k ^ (1 - θ))
    (fun k _ => Real.rpow_nonneg (ha0 k) _) (fun k _ => Real.rpow_nonneg (hc0 k) _)
  have hL : ∑ k, a k ^ θ * c k ^ (1 - θ) =
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (θ / 2) q‖ ^ 2 := by
    rw [norm_sq_wt]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ha, hc]
    have hX := hA1 k
    have hY := norm_nonneg (q.ofLp k)
    rw [Real.mul_rpow hX (sq_nonneg _), mul_assoc,
      ← Real.rpow_add' (sq_nonneg _) (by ring_nf; norm_num)]
    have e1 : ((1 + Asym sys L n k) ^ (θ / 2)) ^ 2 = (1 + Asym sys L n k) ^ θ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; ring_nf
    rw [e1]
    norm_num
  have hR1 : ∑ k, (a k ^ θ) ^ (1 / θ) =
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) q‖ ^ 2 := by
    rw [norm_sq_wt_half]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Real.rpow_mul (ha0 k), mul_one_div_cancel hpos.ne', Real.rpow_one]
  have hR2 : ∑ k, (c k ^ (1 - θ)) ^ (1 / (1 - θ)) = ‖q‖ ^ 2 := by
    rw [norm_sq_En]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Real.rpow_mul (hc0 k), mul_one_div_cancel (by linarith : (1 - θ) ≠ 0), Real.rpow_one]
  rw [hL, hR1, hR2, one_div_one_div, one_div_one_div] at hH
  have hW0 := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) q)
  have hq0 := norm_nonneg q
  have hrhs : (‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) q‖ ^ 2) ^ θ * (‖q‖ ^ 2) ^ (1 - θ) =
      (‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) q‖ ^ θ * ‖q‖ ^ (1 - θ)) ^ 2 := by
    rw [FSGalerkin.sq_rpow_eq hW0, FSGalerkin.sq_rpow_eq hq0, mul_pow]
  rw [hrhs] at hH
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hH

omit [Fintype ν] in
/-- On the cube, `‖ℰ^{s+t} v‖ ≤ (1 + A_max)^t ‖ℰ^s v‖` for `t ≥ 0`. -/
lemma wt_add_le_Amax {s t : ℝ} (ht : 0 ≤ t) (v : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (s + t) v‖ ≤
      (1 + Amax eta L n) ^ t * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ := by
  have hAm : 0 ≤ 1 + Amax eta L n := by
    have := FSGalerkin.Asym_nonneg sys L n; have := Asym_le_Amax sys (L := L) (n := n)
    unfold Amax; positivity
  rw [← Real.sqrt_sq (norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) (s + t) v)),
    ← Real.sqrt_sq (mul_nonneg (Real.rpow_nonneg hAm t) (norm_nonneg _)), mul_pow]
  refine Real.sqrt_le_sqrt ?_
  rw [norm_sq_wt, norm_sq_wt, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hk0 : 0 ≤ 1 + Asym sys L n k := by linarith [FSGalerkin.Asym_nonneg sys L n k]
  have hkle : 1 + Asym sys L n k ≤ 1 + Amax eta L n := by linarith [Asym_le_Amax sys (L := L) k]
  have key : (1 + Asym sys L n k) ^ (s + t) ≤
      (1 + Amax eta L n) ^ t * (1 + Asym sys L n k) ^ s := by
    rw [Real.rpow_add (by linarith [FSGalerkin.Asym_nonneg sys L n k] : 0 < 1 + Asym sys L n k),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hk0 hkle ht) (Real.rpow_nonneg hk0 _)
  calc ((1 + Asym sys L n k) ^ (s + t)) ^ 2 * ‖v.ofLp k‖ ^ 2
      ≤ ((1 + Amax eta L n) ^ t * (1 + Asym sys L n k) ^ s) ^ 2 * ‖v.ofLp k‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.rpow_nonneg hk0 _) key 2) (sq_nonneg _)
    _ = ((1 + Amax eta L n) ^ t) ^ 2 * (((1 + Asym sys L n k) ^ s) ^ 2 * ‖v.ofLp k‖ ^ 2) := by
        ring

omit [Fintype ν] in
/-- `A ≥ |k_a|²/(2 m_a)`. -/
lemma kabs_sq_le_Asym (a : Fin eta) (q : Cfg eta n) :
    finitePlaneWaveKabs (2 * Real.pi / L) n (q a) ^ 2 ≤ 2 * sys.mass a * Asym sys L n q := by
  have h := component_sq_le_mass_mul_massKineticSymbol (fun b => sys.mass_pos b)
    (finitePlaneWaveKabs (2 * Real.pi / L) n) q a
  unfold Asym
  linarith

omit [Fintype ν] in
/-- **Register tails from weights**: `‖1{|k_a| > λ} v‖ ≤ (2 m_a/λ²)^s ‖ℰ^s v‖` for `λ > 0`,
`s ≥ 0`. -/
lemma regTail_le_wt (a : Fin eta) {l : ℝ} (hl : 0 < l) {s : ℝ} (hs : 0 ≤ s) (v : En eta n) :
    ‖regTail L a l v‖ ≤ (2 * sys.mass a / l ^ 2) ^ s *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ := by
  have hm := sys.mass_pos a
  have hc0 : 0 ≤ 2 * sys.mass a / l ^ 2 := by positivity
  rw [← Real.sqrt_sq (norm_nonneg (regTail L a l v)),
    ← Real.sqrt_sq (mul_nonneg (Real.rpow_nonneg hc0 s) (norm_nonneg _)), mul_pow]
  refine Real.sqrt_le_sqrt ?_
  rw [norm_sq_regTail, norm_sq_wt, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  split_ifs with hk
  · have hk0 : 0 ≤ 1 + Asym sys L n k := by linarith [FSGalerkin.Asym_nonneg sys L n k]
    have h1 : 1 ≤ 2 * sys.mass a / l ^ 2 * (1 + Asym sys L n k) := by
      have hkl : l ^ 2 < finitePlaneWaveKabs (2 * Real.pi / L) n (k a) ^ 2 :=
        pow_lt_pow_left₀ hk hl.le two_ne_zero
      have h2 := kabs_sq_le_Asym sys L n a k
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [FSGalerkin.Asym_nonneg sys L n k]
    have h3 : 1 ≤ (2 * sys.mass a / l ^ 2) ^ s * (1 + Asym sys L n k) ^ s := by
      rw [← Real.mul_rpow hc0 hk0]; exact Real.one_le_rpow h1 hs
    have h4 : 1 ≤ ((2 * sys.mass a / l ^ 2) ^ s) ^ 2 * ((1 + Asym sys L n k) ^ s) ^ 2 := by
      rw [← mul_pow]; nlinarith
    have := sq_nonneg ‖v.ofLp k‖
    nlinarith
  · positivity

end Weights

/-! ## `lem:phi`: the remaining displays -/

section PhiRest

variable (sys : CoulombSystem eta ν) (L : ℝ) {n : ℕ} (p₀ : Fin eta) (hL : 0 < L)

/-- The energy-norm constant of `lem:phi`: `‖ℰ^{1/2} φ‖ ≤ c_φ(C_Δ) M Λ_n^{1/2}`. -/
noncomputable def cPhi (sys : CoulombSystem eta ν) (L Hunit CΔ : ℝ) : ℝ :=
  CflS sys L Hunit CΔ (1 / 2) * Real.sqrt (FSDatum.momentConst1 eta (1 / 2) ((eta : ℝ) / 2))

include hL in
/-- `‖ℰ^{1/2} φ‖ ≤ c_φ M Λ_n^{1/2}`. -/
lemma phi_half (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {M : ℝ} {v : En eta n} (hv : IsGood sys L 1 M v)
    (hΛ : 1 ≤ LamN sys L n) (τ : ℝ) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2)
        (retFlow sys L n hΔsym τ (bdatum sys L p₀ v))‖ ≤
      cPhi sys L Hunit CΔ * M * LamN sys L n ^ (1 / 2 : ℝ) := by
  have h := (phi_norms sys L p₀ hL Hunit hPeriodic hΔsym hCΔ hΔb hv hΛ τ (s := 1 / 2)
    (by norm_num) (by norm_num)).2
  have e4 : 4 * (1 / 2 : ℝ) - 1 = 1 := by norm_num
  rw [e4, Real.rpow_one] at h
  refine h.trans (le_of_eq ?_)
  unfold cPhi
  rw [Real.sqrt_mul (FSDatum.momentConst1_nonneg eta (by norm_num) (by positivity)),
    Real.sqrt_eq_rpow (LamN sys L n)]
  ring

include hL in
/-- **`lem:phi`, interpolation**: `‖ℰ^α φ‖ ≤ c_φ^{2α} M Λ_n^α` for `0 ≤ α ≤ 1/2` (eq:phi-norms
and the line after it; `Λ_n = (3η m_max)^{1/2} K`). -/
theorem phi_interp (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {M : ℝ} {v : En eta n} (hv : IsGood sys L 1 M v)
    (hΛ : 1 ≤ LamN sys L n) (τ : ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) α (retFlow sys L n hΔsym τ (bdatum sys L p₀ v))‖ ≤
      cPhi sys L Hunit CΔ ^ (2 * α) * M * LamN sys L n ^ α := by
  set φ := retFlow sys L n hΔsym τ (bdatum sys L p₀ v)
  have hM : 0 ≤ M := by
    have := hv.1; have := norm_nonneg v
    have := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) 1 v); linarith
  have hc : 0 ≤ cPhi sys L Hunit CΔ := by
    unfold cPhi
    exact mul_nonneg (CflS_nonneg sys (L := L) Hunit hCΔ _) (Real.sqrt_nonneg _)
  have hΛ0 : 0 ≤ LamN sys L n := by linarith
  have hθ0 : 0 ≤ 2 * α := by linarith
  have hθ1 : 2 * α ≤ 1 := by linarith
  have hH := wt_le_holder_half sys L n hθ0 hθ1 φ
  rw [show 2 * α / 2 = α by ring] at hH
  have h1 := phi_half sys L p₀ hL Hunit hPeriodic hΔsym hCΔ hΔb hv hΛ τ
  have h0 := (phi_norms sys L p₀ hL Hunit hPeriodic hΔsym hCΔ hΔb hv hΛ τ (s := 1)
    (by norm_num) le_rfl).1
  refine hH.trans ?_
  have hA : ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ‖ ^ (2 * α) ≤
      (cPhi sys L Hunit CΔ * M * LamN sys L n ^ (1 / 2 : ℝ)) ^ (2 * α) :=
    Real.rpow_le_rpow (norm_nonneg _) h1 hθ0
  have hB : ‖φ‖ ^ (1 - 2 * α) ≤ M ^ (1 - 2 * α) :=
    Real.rpow_le_rpow (norm_nonneg _) h0 (by linarith)
  calc ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) φ‖ ^ (2 * α) * ‖φ‖ ^ (1 - 2 * α)
      ≤ (cPhi sys L Hunit CΔ * M * LamN sys L n ^ (1 / 2 : ℝ)) ^ (2 * α) * M ^ (1 - 2 * α) :=
        mul_le_mul hA hB (Real.rpow_nonneg (norm_nonneg _) _)
          (Real.rpow_nonneg (by positivity) _)
    _ = cPhi sys L Hunit CΔ ^ (2 * α) * (M ^ (2 * α) * M ^ (1 - 2 * α)) *
          LamN sys L n ^ α := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hΛ0 _),
          Real.mul_rpow hc hM, ← Real.rpow_mul hΛ0]
        ring_nf
    _ = cPhi sys L Hunit CΔ ^ (2 * α) * M * LamN sys L n ^ α := by
        rw [← Real.rpow_add' hM (by norm_num), show 2 * α + (1 - 2 * α) = 1 by ring,
          Real.rpow_one]

include hL in
/-- **`lem:phi`, the supercritical weight**: on `ran P`,
`‖ℰ^{1+ε} φ‖ ≤ (1 + A_max)^ε C_fl(1) M (C₁ Λ_n³)^{1/2}` (`O(K^{3/2+2ε})`). -/
theorem phi_eps (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {M : ℝ} {v : En eta n} (hv : IsGood sys L 1 M v)
    (hΛ : 1 ≤ LamN sys L n) (τ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 + ε)
        (retFlow sys L n hΔsym τ (bdatum sys L p₀ v))‖ ≤
      (1 + Amax eta L n) ^ ε * (CflS sys L Hunit CΔ 1 *
        (M * Real.sqrt (FSDatum.momentConst1 eta 1 ((eta : ℝ) / 2) * LamN sys L n ^ (3 : ℝ)))) := by
  have h := (phi_norms sys L p₀ hL Hunit hPeriodic hΔsym hCΔ hΔb hv hΛ τ (s := 1)
    (by norm_num) le_rfl).2
  have e : 4 * (1 : ℝ) - 1 = 3 := by norm_num
  rw [e] at h
  refine (wt_add_le_Amax sys L n hε _).trans ?_
  have hAm : 0 ≤ 1 + Amax eta L n := by unfold Amax; positivity
  exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hAm _)

include hL in
/-- **`lem:phi`, the tails**: `‖1{|k_a| > λ} φ‖ ≤ (2 m_a)^{1/2} λ^{-1} c_φ M Λ_n^{1/2}` and
`≤ 2 m_a λ^{-2} C_fl(1) M (C₁ Λ_n³)^{1/2}` for `λ > 0`, i.e.
`C M min(λ^{-1} K^{1/2}, λ^{-2} K^{3/2})`. -/
theorem phi_tail (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {M : ℝ} {v : En eta n} (hv : IsGood sys L 1 M v)
    (hΛ : 1 ≤ LamN sys L n) (τ : ℝ) (a : Fin eta) {l : ℝ} (hl : 0 < l) :
    ‖regTail L a l (retFlow sys L n hΔsym τ (bdatum sys L p₀ v))‖ ≤
        (2 * sys.mass a / l ^ 2) ^ (1 / 2 : ℝ) *
          (cPhi sys L Hunit CΔ * M * LamN sys L n ^ (1 / 2 : ℝ)) ∧
      ‖regTail L a l (retFlow sys L n hΔsym τ (bdatum sys L p₀ v))‖ ≤
        2 * sys.mass a / l ^ 2 * (CflS sys L Hunit CΔ 1 *
          (M * Real.sqrt (FSDatum.momentConst1 eta 1 ((eta : ℝ) / 2) * LamN sys L n ^ (3 : ℝ)))) := by
  have hm := sys.mass_pos a
  have hc0 : 0 ≤ 2 * sys.mass a / l ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · refine (regTail_le_wt sys L n a hl (by norm_num : (0 : ℝ) ≤ 1 / 2) _).trans ?_
    exact mul_le_mul_of_nonneg_left (phi_half sys L p₀ hL Hunit hPeriodic hΔsym hCΔ hΔb hv hΛ τ)
      (Real.rpow_nonneg hc0 _)
  · have h := (phi_norms sys L p₀ hL Hunit hPeriodic hΔsym hCΔ hΔb hv hΛ τ (s := 1)
      (by norm_num) le_rfl).2
    have e : 4 * (1 : ℝ) - 1 = 3 := by norm_num
    rw [e] at h
    have h2 := regTail_le_wt sys L n a hl (s := 1) zero_le_one
      (retFlow sys L n hΔsym τ (bdatum sys L p₀ v))
    rw [Real.rpow_one] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left h hc0)

end PhiRest

/-! ## `lem:a2` -/

section A2

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n) (p₀ : Fin eta)

/-- `A^{(2)} = ½ (Σ_b² O + O Σ_b²)` on `ℓ²` (`O = A_{p₀}^E`, the truncated observable). -/
noncomputable def A2op : L2 eta →L[ℂ] L2 eta :=
  (1 / 2 : ℂ) • (Sig sys L n hL hn * Sig sys L n hL hn * Ofull sys L n p₀ +
    Ofull sys L n p₀ * Sig sys L n hL hn * Sig sys L n hL hn)

/-- **`Σ_b O Σ_b` vanishes on cube vectors** (`O R = 0` and `Σ_b` maps `ran P` into `ran R`). -/
lemma sig_O_sig_emb (v : En eta n) :
    Sig sys L n hL hn (Ofull sys L n p₀ (Sig sys L n hL hn (emb eta n v))) = 0 := by
  rw [← Ofull_trunc sys p₀, trunc_sig_emb sys hL hn v, map_zero, map_zero]

/-- **The double commutator on cube vectors**: `[Σ_b, [Σ_b, O]] u = (Σ_b² O + O Σ_b²) u`, so
`½ P [Σ_b, [Σ_b, O]] P = A^{(2)}` (the middle term drops). -/
lemma dcomm_emb (v : En eta n) :
    FSConj.cm (Sig sys L n hL hn) (FSConj.cm (Sig sys L n hL hn) (Ofull sys L n p₀)) (emb eta n v) =
      (Sig sys L n hL hn * Sig sys L n hL hn * Ofull sys L n p₀ +
        Ofull sys L n p₀ * Sig sys L n hL hn * Sig sys L n hL hn) (emb eta n v) := by
  unfold FSConj.cm
  simp only [sub_apply, add_apply, mul_apply_eq_comp, map_sub]
  rw [sig_O_sig_emb sys hL hn p₀ v]
  abel

/-- **`lem:a2`, the identity**: `⟨u, A^{(2)} u⟩ = -Re ⟨Σ_b u, Σ_b O u⟩` for `u ∈ ran P`. -/
theorem a2_form (v : En eta n) :
    ⟪emb eta n v, A2op sys hL hn p₀ (emb eta n v)⟫_ℂ =
      ((-(⟪Sig sys L n hL hn (emb eta n v),
        Sig sys L n hL hn (Ofull sys L n p₀ (emb eta n v))⟫_ℂ).re : ℝ) : ℂ) := by
  set Sg := Sig sys L n hL hn
  set O := Ofull sys L n p₀
  set x := emb eta n v
  have hskew := (Sig_skew_unitary (sys := sys) hL hn).1
  have hadj : ContinuousLinearMap.adjoint Sg = -Sg := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hskew
  have hO : ∀ y z : L2 eta, ⟪y, O z⟫_ℂ = ⟪O y, z⟫_ℂ := fun y z => by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      (Ofull_selfAdjoint sys p₀ (L := L) (n := n)).star_eq]
  have hS : ∀ y z : L2 eta, ⟪y, Sg z⟫_ℂ = -⟪Sg y, z⟫_ℂ := fun y z => by
    rw [← ContinuousLinearMap.adjoint_inner_left, hadj, neg_apply, inner_neg_left]
  have e1 : ⟪x, Sg (Sg (O x))⟫_ℂ = -⟪Sg x, Sg (O x)⟫_ℂ := hS x _
  have e2 : ⟪x, O (Sg (Sg x))⟫_ℂ = -conj ⟪Sg x, Sg (O x)⟫_ℂ := by
    rw [hO, hS, inner_conj_symm]
  unfold A2op
  simp only [smul_apply, add_apply, mul_apply_eq_comp, inner_smul_right, inner_add_right]
  rw [e1, e2]
  set z := ⟪Sg x, Sg (O x)⟫_ℂ
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im]
  ring

/-- **`lem:a2`, the bound**: for a good cube state `u` (`IsGood 1 M v`) and `3/4 < s ≤ 1`,
`|⟨u, A^{(2)} u⟩| ≤ (c_s c_E^s)² M · M (C_{s+1} Λ^{4s-1})^{1/2}` with `c_s² = #Ch² M₀ Z_{2s}`,
`M₀ = c_{M₀} n^{-5}` and `Λ = K/√2048`: of order `K^{-4+2(s-3/4)}`. -/
theorem a2_bound {M : ℝ} {v : En eta n} (hv : IsGood sys L 1 M v) {s : ℝ} (hs : 3 / 4 < s)
    (hs1 : s ≤ 1) (hΛ : 1 ≤ Lam sys L n) :
    ‖⟪emb eta n v, A2op sys hL hn p₀ (emb eta n v)⟫_ℂ‖ ≤
      (cSt sys L n s * cE sys L ^ s) ^ 2 * M *
        (M * Real.sqrt (momentConst eta (s + 1) * Lam sys L n ^ (4 * s - 1))) := by
  rw [a2_form sys hL hn p₀ v, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  have hM : 0 ≤ M := by
    have := hv.1; have := norm_nonneg v
    have := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) 1 v); linarith
  have hcs : 0 ≤ cSt sys L n s * cE sys L ^ s := by
    unfold cSt
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by linarith [one_le_cE sys (L := L)]) _)
  refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
  rw [Ofull_emb sys hL p₀ v]
  have h1 := norm_sig_emb_wt_le sys hL hn hs v
  have h2 := norm_sig_emb_wt_le sys hL hn hs (datum sys L p₀ v)
  have hwv : ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ ≤ M := by
    refine (wt_mono sys L n hs1 v).trans ?_
    have := hv.1; have := norm_nonneg v; linarith
  have hd := wt_datum_sq_le sys L p₀ hL (Cg := 1) (Ξ := M) (r' := s) (by linarith) (by linarith) hΛ v
    (by simpa using hv)
  have hX : 0 ≤ momentConst eta (s + 1) * Lam sys L n ^ (4 * s - 1) := by
    have := FSGalerkin.momentConst_nonneg eta (r := s + 1) (by linarith)
    exact mul_nonneg this (Real.rpow_nonneg (by linarith) _)
  have hwd : ‖FSSpectral.wt (sb eta n) (Asym sys L n) s (datum sys L p₀ v)‖ ≤
      M * Real.sqrt (momentConst eta (s + 1) * Lam sys L n ^ (4 * s - 1)) := by
    have hrhs : 0 ≤ M * Real.sqrt (momentConst eta (s + 1) * Lam sys L n ^ (4 * s - 1)) :=
      mul_nonneg hM (Real.sqrt_nonneg _)
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hrhs two_ne_zero).mp ?_
    rw [mul_pow, Real.sq_sqrt hX]
    nlinarith [hd]
  unfold cSt at h1 h2 hcs ⊢
  calc ‖Sig sys L n hL hn (emb eta n v)‖ * ‖Sig sys L n hL hn (emb eta n (datum sys L p₀ v))‖
      ≤ (Real.sqrt (Fintype.card (Ch eta) ^ 2 * M0 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3)))) *
          cE sys L ^ s * M) *
        (Real.sqrt (Fintype.card (Ch eta) ^ 2 * M0 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3)))) *
          cE sys L ^ s * (M * Real.sqrt (momentConst eta (s + 1) * Lam sys L n ^ (4 * s - 1)))) := by
        refine mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left hwv hcs))
          (h2.trans (mul_le_mul_of_nonneg_left hwd hcs)) (norm_nonneg _)
          (mul_nonneg hcs hM)
    _ = _ := by ring

end A2

end FSSrc1
