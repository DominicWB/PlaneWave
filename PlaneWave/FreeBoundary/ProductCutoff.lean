import PlaneWave.FreeBoundary.RegularityBridgeNuclear

/-!
# Clamped nuclei, part 7: a product cutoff flat near the nuclei

For equal masses `m_i = m₀` (the moving particles are electrons) the product
`χ(r) = Π_i q(x_i)` of one smooth bump `q` (`q = 1` on `B_1(0)`, `0` outside `B_2(0)`) is a
mass-weighted cutoff at `L = 8`. It is symmetric under every exchange of particles, so
`∂_{(i,c)}χ = ∂_{(j,c)}χ` wherever `x_i = x_j`; with the mean value inequality this gives the
cancellation `|∇_iχ/m₀ - ∇_jχ/m₀| ≤ C |x_i - x_j|`. It is flat in the coordinates of particle `i`
wherever `|x_i| < 1`, hence near nuclei `P_ℓ` with `|P_ℓ| + δ ≤ 1`.

* `swapCLM`, `dirD_swap_sym`, `freeSwap_eq_self`: exchanges and derivatives;
* `bumpQ`, `prodChi`, `contDiff_prodChi`, `prodChi_freeSwap`, `dirD_prodChi_flat`;
* `exists_lipschitz_family`: a uniform Lipschitz constant for compactly supported `C¹` functions;
* **`prodChi_isFlatNear`**; the cutoff itself (`DomCutoff eta L m` for constant `m ≥ 1`,
  `L ≥ 8`) is `exists_prodCutoff` (`PlaneWave.FreeBoundary.ProductCutoffCancellation`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology NNReal
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

variable {eta : ℕ}

/-! ## Exchanges and derivatives -/

section Swap

/-- The exchange of particles `i` and `j` as a continuous linear map. -/
noncomputable def swapCLM (i j : Fin eta) : Rcfg eta →L[ℝ] Rcfg eta :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj ((Equiv.swap i j) a.1, a.2)

lemma swapCLM_apply (i j : Fin eta) (r : Rcfg eta) : swapCLM i j r = freeSwap i j r := rfl

lemma swapCLM_single (i j : Fin eta) (c : Fin 3) :
    swapCLM i j (Pi.single (i, c) 1) = Pi.single (j, c) 1 := by
  funext a
  obtain ⟨k, d⟩ := a
  simp only [swapCLM_apply, freeSwap, Pi.single_apply, Prod.mk.injEq, Equiv.swap_apply_eq_iff,
    Equiv.swap_apply_left]

/-- For `χ` symmetric under the exchange of `i` and `j`: `∂_{(i,c)}χ(r) = ∂_{(j,c)}χ(σ r)`. -/
lemma dirD_swap_sym {χ : Rcfg eta → ℝ} (hχ : Differentiable ℝ χ) {i j : Fin eta}
    (hsym : ∀ r, χ (freeSwap i j r) = χ r) (c : Fin 3) (r : Rcfg eta) :
    dirD (i, c) χ r = dirD (j, c) χ (freeSwap i j r) := by
  have e : χ = fun r => χ (swapCLM i j r) := funext fun r => (hsym r).symm
  have h1 : dirD (i, c) χ r = dirD (i, c) (fun r => χ (swapCLM i j r)) r :=
    congrArg (fun f => dirD (i, c) f r) e
  have h' : HasFDerivAt (fun r => χ (swapCLM i j r))
      ((fderiv ℝ χ (swapCLM i j r)).comp (swapCLM i j)) r :=
    (hχ (swapCLM i j r)).hasFDerivAt.comp r (swapCLM i j).hasFDerivAt
  rw [h1]
  unfold dirD
  rw [h'.fderiv, ContinuousLinearMap.comp_apply, swapCLM_single]
  rfl

lemma freeSwap_eq_self {i j : Fin eta} {r : Rcfg eta} (h : particle r i = particle r j) :
    freeSwap i j r = r := by
  funext a
  obtain ⟨k, d⟩ := a
  have hd : ∀ d : Fin 3, r (i, d) = r (j, d) := fun d => congrArg (fun v : E3 => v d) h
  unfold freeSwap
  by_cases hki : k = i
  · subst hki
    simp only [Equiv.swap_apply_left]
    exact (hd d).symm
  · by_cases hkj : k = j
    · subst hkj
      simp only [Equiv.swap_apply_right]
      exact hd d
    · simp only [Equiv.swap_apply_of_ne_of_ne hki hkj]

end Swap

/-! ## A uniform Lipschitz constant -/

lemma exists_lipschitz_family {ι : Type*} [Fintype ι] {f : ι → Rcfg eta → ℝ}
    (hf : ∀ i, ContDiff ℝ 1 (f i)) (hs : ∀ i, HasCompactSupport (f i)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i x y, |f i x - f i y| ≤ K * ‖x - y‖ := by
  choose C hC using fun i =>
    ((hf i).continuous_fderiv (by norm_num)).bounded_above_of_compact_support
      ((hs i).fderiv (𝕜 := ℝ))
  refine ⟨∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i x y => ?_⟩
  have hK : ∀ z, ‖fderiv ℝ (f i) z‖ ≤ ∑ i, |C i| := fun z =>
    (hC i z).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun j => |C j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)))
  have hL : LipschitzWith ⟨∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _⟩ (f i) :=
    lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) ((hf i).differentiable (by norm_num)) fun z => by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hK z
  have := hL.dist_le_mul x y
  rwa [Real.dist_eq, dist_eq_norm] at this

/-! ## The product cutoff -/

section Product

/-- The one-particle bump: `1` on `B_1(0)`, supported in `B_2(0)`. -/
noncomputable def bumpQ : ContDiffBump (0 : E3) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The product cutoff `Π_i q(x_i)`. -/
noncomputable def prodChi (r : Rcfg eta) : ℝ := ∏ i : Fin eta, bumpQ (particle r i)

lemma contDiff_prodChi {n : ℕ∞} : ContDiff ℝ n (prodChi (eta := eta)) := by
  unfold prodChi
  exact contDiff_prod fun i _ => bumpQ.contDiff.comp (particleCLM i).contDiff

lemma prodChi_nonneg (r : Rcfg eta) : 0 ≤ prodChi r :=
  Finset.prod_nonneg fun _ _ => bumpQ.nonneg

lemma prodChi_le_one (r : Rcfg eta) : prodChi r ≤ 1 :=
  Finset.prod_le_one (fun _ _ => bumpQ.nonneg) fun _ _ => bumpQ.le_one

lemma abs_coord_le_norm_particle (r : Rcfg eta) (i : Fin eta) (c : Fin 3) :
    |r (i, c)| ≤ ‖particle r i‖ := by
  have h2 : (r (i, c)) ^ 2 ≤ ‖particle r i‖ ^ 2 := by
    rw [norm_sq_E3]
    exact Finset.single_le_sum (f := fun d : Fin 3 => ((particle r i) d) ^ 2)
      (fun d _ => sq_nonneg _) (Finset.mem_univ c)
  exact (sq_le_sq.mp h2).trans (le_of_eq (abs_of_nonneg (norm_nonneg _)))

lemma norm_particle_lt_of_prodChi_ne {r : Rcfg eta} (h : prodChi r ≠ 0) (i : Fin eta) :
    ‖particle r i‖ < 2 := by
  have hi : bumpQ (particle r i) ≠ 0 := (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
  have hs : particle r i ∈ Function.support (bumpQ : E3 → ℝ) := hi
  rw [bumpQ.support_eq] at hs
  simpa [bumpQ] using hs

lemma prodChi_freeSwap (i j : Fin eta) (r : Rcfg eta) : prodChi (freeSwap i j r) = prodChi r := by
  unfold prodChi
  exact Equiv.prod_comp (Equiv.swap i j) (fun k => bumpQ (particle r k))

/-- **Flatness**: `∂_{(i,c)}χ(r) = 0` where `|x_i| < 1`. -/
lemma dirD_prodChi_flat {r : Rcfg eta} {i : Fin eta} (hi : ‖particle r i‖ < 1) (c : Fin 3) :
    dirD (i, c) prodChi r = 0 := by
  have hd : ∀ k ∈ (Finset.univ : Finset (Fin eta)),
      HasFDerivAt (fun r : Rcfg eta => bumpQ (particle r k))
        ((fderiv ℝ (bumpQ : E3 → ℝ) (particle r k)).comp (particleCLM k)) r := fun k _ =>
    ((bumpQ.contDiff (n := 1)).differentiable (by norm_num) _).hasFDerivAt.comp r
      (particleCLM k).hasFDerivAt
  have hP := HasFDerivAt.finsetProd hd
  have hzero : fderiv ℝ (bumpQ : E3 → ℝ) (particle r i) = 0 := by
    have hev : (bumpQ : E3 → ℝ) =ᶠ[𝓝 (particle r i)] fun _ => 1 := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show particle r i ∈ Metric.ball (0 : E3) 1 by
        simpa using hi)] with y hy
      exact bumpQ.one_of_mem_closedBall (Metric.ball_subset_closedBall (by simpa [bumpQ] using hy))
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  unfold dirD prodChi
  rw [hP.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [particleCLM_apply, particle_single]
  by_cases hk : i = k
  · subst hk
    rw [if_pos rfl, hzero]
    simp
  · rw [if_neg hk, map_zero, mul_zero]

/-- The product cutoff is flat near nuclei `P_ℓ` with `|P_ℓ| + δ ≤ 1`. -/
theorem prodChi_isFlatNear {ν : Type} (P : ν → E3) {δ : ℝ} (hP : ∀ l, ‖P l‖ + δ ≤ 1) :
    IsFlatNear (prodChi (eta := eta)) P δ := by
  intro r i l hr c
  refine dirD_prodChi_flat ?_ c
  calc ‖particle r i‖ = ‖(particle r i - P l) + P l‖ := by rw [sub_add_cancel]
    _ ≤ ‖particle r i - P l‖ + ‖P l‖ := norm_add_le _ _
    _ < δ + ‖P l‖ := by linarith
    _ ≤ 1 := by linarith [hP l]

end Product

end FreeBoundary
