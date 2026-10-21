import PlaneWave.FluxSourceSpin

/-!
# Auxiliary clauses of the manuscript, part 2: `app:flux` and `app:source`

* `gap_sharp` — `lem:gap`: "the constant `3/32` is sharp over configurations and mass ratios".
  For every `ε > 0` there are masses, a cutoff and momenta satisfying the hypotheses of `gap` with
  `ω < (3/32 + ε) K² μ⁻¹`. The configuration is collinear: `k_p = k_b = (K/4) e`,
  `ν = (3/4 + ε'/2) K e`, `M_p = 1`, `m_b = ε'/8` (`ε' = min(ε, 1)`).
* `pin_sharp` — `lem:pin`: "the constant is sharp". For every `κ > 9/64` there is a pair in the
  resonance window `|F| < |θ|²/4` of `pin_core` with `min(|ξ|², |ξ + θ|²) = |ξ|² < κ |θ|²`
  (the anti-parallel configuration `ξ = -s θ`, `s ↓ 3/8`).
* `acorr_PR`, `norm_acorr_PR_le` — `lem:acorr`, the second identity of eq:acorr-id and the third
  bound of eq:acorr: `[Σ_b, O]_{PR} = -O Σ_{b,PR}` and `‖[Σ_b, O]_{PR} x‖ ≤ ‖O‖ ‖Σ_{b,PR} x‖`
  (`O = A_p^E`, `R = 1 - P`).
* `tavg_mass` — `lem:tavg`, the second identity: `t ∫ ‖w_x‖² dx = √π ‖u‖²`, for the spectral
  decomposition `u = Σ_k y_k` into mutually orthogonal components.
* `flow_datum_interp` — `lem:phi` with `A_p^E` for `0 ≤ α ≤ 1/2`, in particular `0 < α < 1/4`:
  `‖ℰ^α φ(τ)‖ ≤ M φ_{1/2}^{2α}`, with `φ_{1/2} = O(K^{1/2})` up to logarithms (`pl_phiSC0`), by
  interpolation between `‖φ‖ ≤ M` and `‖ℰ^{1/2} φ‖ ≤ M φ_{1/2}` (`flow_datum_bounds`,
  `wt_le_holder_half`).
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace FluxSourceTest

section GapSharp

/-- The inequality behind `gap_sharp`. -/
lemma gap_sharp_ineq {K ε e1 : ℝ} (hK : 0 < K) (he1 : 0 < e1) (he1' : e1 ≤ 1) (he1ε : e1 ≤ ε) :
    (2 * (K / 4 * ((3 / 4 + e1 / 2) * K)) + ((3 / 4 + e1 / 2) * K) ^ 2) / (2 * 1) +
        (((3 / 4 + e1 / 2) * K) ^ 2 - 2 * (K / 4 * ((3 / 4 + e1 / 2) * K))) / (2 * (e1 / 8)) <
      (3 * K ^ 2 / 32 + ε * K ^ 2) * (1 / 1 + 1 / (e1 / 8)) := by
  have hK2 : 0 < K ^ 2 := by positivity
  have e1' : (2 * (K / 4 * ((3 / 4 + e1 / 2) * K)) + ((3 / 4 + e1 / 2) * K) ^ 2) / (2 * 1) =
      K ^ 2 * (15 / 32 + e1 / 2 + e1 ^ 2 / 8) := by ring
  have e2' : (((3 / 4 + e1 / 2) * K) ^ 2 - 2 * (K / 4 * ((3 / 4 + e1 / 2) * K))) / (2 * (e1 / 8)) =
      K ^ 2 * ((3 / 4 + 2 * e1 + e1 ^ 2) / e1) := by
    field_simp
    ring
  have e3' : (3 * K ^ 2 / 32 + ε * K ^ 2) * (1 / 1 + 1 / (e1 / 8)) =
      K ^ 2 * ((3 / 32 + ε) * ((e1 + 8) / e1)) := by
    field_simp
  rw [e1', e2', e3', ← mul_add]
  refine mul_lt_mul_of_pos_left ?_ hK2
  rw [show (15 / 32 + e1 / 2 + e1 ^ 2 / 8) + (3 / 4 + 2 * e1 + e1 ^ 2) / e1 =
      (e1 * (15 / 32 + e1 / 2 + e1 ^ 2 / 8) + (3 / 4 + 2 * e1 + e1 ^ 2)) / e1 by
    field_simp, mul_div_assoc', div_lt_div_iff_of_pos_right he1]
  have h2 : e1 ^ 2 ≤ e1 := by nlinarith
  have h3 : e1 ^ 3 ≤ e1 := by nlinarith
  have h4 : e1 * e1 ≤ ε * e1 := mul_le_mul_of_nonneg_right he1ε he1.le
  nlinarith

/-- **`lem:gap`: the constant `3/32` is sharp** over configurations and mass ratios: in every real
inner product space with a unit vector `e`, for every cutoff `K > 0` and every `ε > 0` there are
masses and momenta satisfying the hypotheses of `gap` with `ω < (3/32 + ε) K² (1/M + 1/m)`. -/
theorem gap_sharp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e : E}
    (he : ‖e‖ = 1) {K : ℝ} (hK : 0 < K) {ε : ℝ} (hε : 0 < ε) :
    ∃ M m : ℝ, 0 < M ∧ 0 < m ∧ ∃ kp kb ν : E, ‖kp‖ ≤ K / 4 ∧ ‖kb‖ ≤ K / 4 ∧
      (K < ‖kp + ν‖ ∨ K < ‖kb - ν‖) ∧
      mismatch M m kp kb ν < (3 * K ^ 2 / 32 + ε * K ^ 2) * (1 / M + 1 / m) := by
  set e1 := min ε 1 with he1def
  have he1 : 0 < e1 := lt_min hε one_pos
  have he1' : e1 ≤ 1 := min_le_right _ _
  have he1ε : e1 ≤ ε := min_le_left _ _
  have hee : ⟪e, e⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hK4 : ‖(K / 4) • e‖ = K / 4 := by
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity)]
  refine ⟨1, e1 / 8, one_pos, by positivity, (K / 4) • e, (K / 4) • e,
    ((3 / 4 + e1 / 2) * K) • e, hK4.le, hK4.le, Or.inl ?_, ?_⟩
  · rw [← add_smul, norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity)]
    nlinarith
  · have hin : ⟪(K / 4) • e, ((3 / 4 + e1 / 2) * K) • e⟫_ℝ = K / 4 * ((3 / 4 + e1 / 2) * K) := by
      rw [real_inner_smul_left, real_inner_smul_right, hee, mul_one]
    have hnn : ‖((3 / 4 + e1 / 2) * K) • e‖ = (3 / 4 + e1 / 2) * K := by
      rw [norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity)]
    unfold mismatch
    rw [hin, hnn]
    exact gap_sharp_ineq hK he1 he1' he1ε

end GapSharp

end FluxSourceTest

namespace FSLattice

open FluxSourceTest

/-- **`lem:pin`: the constant is sharp.** For every `κ > 9/64` there are a relative momentum `c`
and a transfer `θ` in the resonance window `|F_c(θ)| < |θ|²/4` of `pin_core` with
`|c|² < κ |θ|²` and `|c|² ≤ |c + θ|²`: the bound `min(|c|², |c + θ|²) > (9/64)|θ|²` of
`pin_two_sided` cannot be improved. -/
theorem pin_sharp {κ : ℝ} (hκ : 9 / 64 < κ) :
    ∃ (c : Fin 3 → ℝ) (θ : L3), |slabF c θ| < lsq θ / 4 ∧ ∑ i, c i ^ 2 < κ * lsq θ ∧
      ∑ i, c i ^ 2 ≤ qd c θ := by
  set δ := min (1 / 8) ((κ - 9 / 64) / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 8 := min_le_left _ _
  have hδ2 : δ ≤ (κ - 9 / 64) / 2 := min_le_right _ _
  set s := 3 / 8 + δ with hs
  refine ⟨![-s, 0, 0], ![1, 0, 0], ?_, ?_, ?_⟩
  · have hF : slabF ![-s, 0, 0] ![1, 0, 0] = 1 - 2 * s := by
      simp [slabF, lsq, Fin.sum_univ_three]
      ring
    have hl : lsq ![(1 : ℤ), 0, 0] = 1 := by simp [lsq]
    rw [hF, hl, abs_lt]
    constructor <;> linarith
  · have hl : lsq ![(1 : ℤ), 0, 0] = 1 := by simp [lsq]
    rw [hl, Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    nlinarith
  · simp only [qd, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    nlinarith

end FSLattice

namespace FSNormal

open PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Acorr

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n) (p₀ : Fin eta)

/-- **`lem:acorr`, the second identity of eq:acorr-id**: `[Σ_b, O]_{PR} = -O Σ_{b,PR}`, i.e.
`P (Σ_b O - O Σ_b) R x = -O (P Σ_b R x)` for every `x`, with `R x = x - P x` and `O = A_p^E`. -/
theorem acorr_PR (x : L2 eta) :
    molecularH2Truncate n (Sig sys L n hL hn (Ofull sys L n p₀ (x - molecularH2Truncate n x)) -
        Ofull sys L n p₀ (Sig sys L n hL hn (x - molecularH2Truncate n x))) =
      -Ofull sys L n p₀ (molecularH2Truncate n (Sig sys L n hL hn (x - molecularH2Truncate n x))) := by
  have h0 : molecularH2Truncate n (0 : L2 eta) = 0 := by
    have := molecularH2Truncate_sub n (0 : L2 eta) 0
    rw [sub_self] at this
    rw [this, sub_self]
  have hneg : ∀ z : L2 eta, molecularH2Truncate n (-z) = -molecularH2Truncate n z := fun z => by
    have := molecularH2Truncate_sub n (0 : L2 eta) z
    rw [zero_sub, h0, zero_sub] at this
    exact this
  rw [Ofull_sub_trunc sys p₀ x, map_zero, zero_sub, hneg, trunc_Ofull sys p₀, Ofull_trunc sys p₀]

/-- **`lem:acorr`, the third bound of eq:acorr**: `‖[Σ_b, O]_{PR} x‖ ≤ ‖O‖ ‖Σ_{b,PR} x‖`. -/
theorem norm_acorr_PR_le (x : L2 eta) :
    ‖molecularH2Truncate n (Sig sys L n hL hn (Ofull sys L n p₀ (x - molecularH2Truncate n x)) -
        Ofull sys L n p₀ (Sig sys L n hL hn (x - molecularH2Truncate n x)))‖ ≤
      ‖Ofull sys L n p₀‖ * ‖molecularH2Truncate n (Sig sys L n hL hn (x - molecularH2Truncate n x))‖ := by
  rw [acorr_PR sys hL hn p₀ x, norm_neg]
  exact (Ofull sys L n p₀).le_opNorm _

end Acorr

section PhiInterp

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ}

include hL in
/-- **`lem:phi` with `A_p^E`, `0 ≤ α ≤ 1/2`**: the backward flow `φ(τ)` of the datum `A_p^E w` of a
good state satisfies `‖ℰ^α φ(τ)‖ ≤ M φ_{1/2}^{2α}`, where `φ_{1/2} = phiSC … (1/2) = O(K^{1/2})` up
to logarithms (`pl_phiSC0`); this covers `0 < α < 1/4`, which `flow_datum_bounds` leaves out. -/
theorem flow_datum_interp (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) (hΛ : 1 ≤ Lam sys L n) (p₀ : Fin eta) {M : ℝ}
    (w : En eta n) (hw : IsGood sys L 1 M w) (τ : ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) α (retFlow sys L n hΔsym τ (datum sys L p₀ w))‖ ≤
      M * phiSC sys L Hunit n CΔ (1 / 2) ^ (2 * α) := by
  obtain ⟨h0, -, h2⟩ := flow_datum_bounds sys hL Hunit hPeriodic hΔsym hCΔ hΔb hΛ p₀ w hw τ
    (σ := 1 / 2) (by norm_num) (by norm_num)
  set q := retFlow sys L n hΔsym τ (datum sys L p₀ w)
  set S := phiSC sys L Hunit n CΔ (1 / 2)
  have hM := good_nonneg hw
  have hS : 0 ≤ S := mul_nonneg (CflS_nonneg sys Hunit hCΔ _) (Real.sqrt_nonneg _)
  have hθ0 : 0 ≤ 2 * α := by linarith
  have hθ1 : 2 * α ≤ 1 := by linarith
  have hH := FSSrc1.wt_le_holder_half sys L n hθ0 hθ1 q
  rw [show 2 * α / 2 = α by ring] at hH
  refine hH.trans ?_
  have e1 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) q‖ ^ (2 * α) ≤ (M * S) ^ (2 * α) :=
    Real.rpow_le_rpow (norm_nonneg _) h2 hθ0
  have e2 : ‖q‖ ^ (1 - 2 * α) ≤ M ^ (1 - 2 * α) := Real.rpow_le_rpow (norm_nonneg _) h0 (by linarith)
  calc ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) q‖ ^ (2 * α) * ‖q‖ ^ (1 - 2 * α)
      ≤ (M * S) ^ (2 * α) * M ^ (1 - 2 * α) :=
        mul_le_mul e1 e2 (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (by positivity) _)
    _ = M * S ^ (2 * α) := by
        rw [Real.mul_rpow hM hS, mul_comm (M ^ (2 * α)), mul_assoc, ← Real.rpow_add' hM
          (by norm_num : (2 * α + (1 - 2 * α)) ≠ 0)]
        rw [show 2 * α + (1 - 2 * α) = (1 : ℝ) by ring, Real.rpow_one]
        ring

end PhiInterp

end FSNormal

namespace FSSpectral

open MeasureTheory

section TavgMass

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι : Type*} [Fintype ι] (lam : ι → ℝ) (y : ι → F)

/-- For mutually orthogonal components, `‖Σ_k e^{iλ_k τ} y_k‖ = ‖Σ_k y_k‖`. -/
lemma norm_sq_flowVec_of_orth (horth : Pairwise fun k l => ⟪y k, y l⟫_ℂ = 0) (τ : ℝ) :
    ‖flowVec lam y τ‖ ^ 2 = ‖∑ k, y k‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  rw [ofReal_norm_sq_eq_inner, ofReal_norm_sq_eq_inner]
  unfold flowVec
  have hsum : ∑ k, y k = ∑ k, (1 : ℂ) • y k := by simp
  rw [hsum, inner_sum_smul, inner_sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun l _ hlk => by rw [horth (Ne.symm hlk), mul_zero])
      (fun h => absurd (Finset.mem_univ k) h),
    Finset.sum_eq_single k (fun l _ hlk => by rw [horth (Ne.symm hlk), mul_zero])
      (fun h => absurd (Finset.mem_univ k) h)]
  have h1 : (starRingEnd ℂ) (Complex.exp (Complex.I * (lam k : ℂ) * τ)) *
      Complex.exp (Complex.I * (lam k : ℂ) * τ) = 1 := by
    rw [Complex.conj_mul', Complex.norm_exp]
    simp
  rw [h1]
  simp

/-- **`lem:tavg`, the second identity**: `t ∫ ‖w_x‖² dx = √π ‖u‖²` for `u = Σ_k y_k` with
mutually orthogonal spectral components `y_k`. -/
theorem tavg_mass {t : ℝ} (ht : 0 < t) (horth : Pairwise fun k l => ⟪y k, y l⟫_ℂ = 0) :
    t * ∫ x : ℝ, ‖gaussVec lam y t x‖ ^ 2 = Real.sqrt Real.pi * ‖∑ k, y k‖ ^ 2 := by
  have h := tavg_identity lam y ht
  have hc : (fun τ : ℝ => Real.exp (-(τ ^ 2 / t ^ 2)) * ‖flowVec lam y τ‖ ^ 2) =
      fun τ => ‖∑ k, y k‖ ^ 2 * Real.exp (-(1 / t ^ 2) * τ ^ 2) := by
    funext τ
    rw [norm_sq_flowVec_of_orth lam y horth τ, mul_comm]
    congr 2
    ring
  rw [hc, integral_const_mul, integral_gaussian] at h
  have e : Real.sqrt (Real.pi / (1 / t ^ 2)) = Real.sqrt Real.pi * t := by
    rw [div_div_eq_mul_div, div_one, Real.sqrt_mul' _ (by positivity), Real.sqrt_sq ht.le]
  rw [e] at h
  have h2 : t * (t * ∫ x : ℝ, ‖gaussVec lam y t x‖ ^ 2) =
      t * (Real.sqrt Real.pi * ‖∑ k, y k‖ ^ 2) := by
    linear_combination (-1 : ℝ) * h
  exact mul_left_cancel₀ ht.ne' h2

end TavgMass

end FSSpectral
