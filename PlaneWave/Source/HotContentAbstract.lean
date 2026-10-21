import PlaneWave.Source.SpectralLayer
import PlaneWave.Source.LoewnerHeinz

/-!
# Flux/source build, block 1a: the abstract time-averaged hot-content bound

Combines the three abstract tools of the spectral block into the bound behind eq:tavg-quarter
(`prop:tavgU`), still on an abstract finite-dimensional space:

* `tavg_window_bound` (`dev/PlaneWave.Source.SpectralLayer.lean`): the time average of `‖C e^{iHτ} u‖²` is controlled by
  the `C`-content of quasi-eigenstates below an energy `X`, the spectral moment
  `Σ_i (1 + λ_i + C₀)^p |⟪b_i, u⟫|²` and the high spectral content `‖1{H ≥ X - Δ} u‖²`;
* `norm_ePow_le_of_norm_ePow_le` (`dev/PlaneWave.Source.LoewnerHeinz.lean`, Löwner–Heinz): the graph-norm comparison
  `‖(H + C₀ + 1) v‖ ≤ C_G ‖(1 + A) v‖` gives `‖(H + C₀ + 1)^{p/2} u‖ ≤ C_G^{p/2} ‖(1 + A)^{p/2} u‖`
  for `p ≤ 2`, which turns the spectral moment into the kinetic one (as in `lem:retflow`);
* `specleak` (`lem:specleak`): for a datum with kinetic support in `A ≤ E₀ < X - Δ`,
  `‖1{H ≥ X - Δ} u‖ ≤ C_V/(X - Δ - E₀) ‖(1 + A)^{1/2} u‖` (as in `cor:spectail`).

`tavg_hot_abstract` is the result; the concrete layer supplies `α, β` from `lem:qtail` (for the
hot projector `C = 1 - Q`) and the datum's weighted norms from `cor:spectail`.
-/

set_option autoImplicit false

open MeasureTheory Complex
open scoped InnerProductSpace Real

namespace FSSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `ePow` of a function of the eigenvalues is the calculus of the corresponding real power. -/
lemma ePow_comp_eq_fc (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (g : ℝ → ℝ) (s : ℝ) (v : E) :
    FluxSourceTest.ePow b (fun i => g (lam i)) s v = fc b lam (fun l => ((g l ^ s : ℝ) : ℂ)) v := by
  unfold FluxSourceTest.ePow fc
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]

/-- The kinetic weights are `ePow` of `1 + A`. -/
lemma ePow_one_add_eq_wt (f : OrthonormalBasis κ ℂ E) (A : κ → ℝ) (s : ℝ) (v : E) :
    FluxSourceTest.ePow f (fun k => 1 + A k) s v = wt f A s v :=
  ePow_comp_eq_fc f A (fun l => 1 + l) s v

/-- **The abstract time-averaged hot-content bound** (skeleton of eq:tavg-quarter).

Hypotheses: `H = T + V` symmetric with orthonormal eigenbasis `(b, lam)`, `H ≥ -C₀`,
`‖V v‖ ≤ C_V ‖(1+A)^{1/2} v‖`, the graph comparison `‖(H + C₀ + 1) v‖ ≤ C_G ‖(1 + A) v‖`, a
contraction `C` whose action on quasi-eigenstates of width `Δ` and energy `-C₀ ≤ E' ≤ X` is
`‖C q‖² ≤ (α + β (1 + E' + C₀)^p) ‖q‖²` with `0 ≤ p ≤ 2`, and a datum `u` with kinetic support in
`A ≤ E₀`, `E₀ < X - Δ`.  Conclusion: the time average of `‖C e^{iHτ} u‖²` over `[0, t]` is at most
`2e [√π (α ‖u‖² + β (1+Δ)^p C_G^p ‖(1+A)^{p/2} u‖² + (C_V/(X - Δ - E₀))² ‖(1+A)^{1/2} u‖²)
+ √(2π) e^{-t²Δ²/2} ‖u‖²]`. -/
theorem tavg_hot_abstract [FiniteDimensional ℂ E] [DecidableEq κ]
    (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (f : OrthonormalBasis κ ℂ E) (A : κ → ℝ)
    (hA : ∀ k, 0 ≤ A k) (H V : E →ₗ[ℂ] E) (hH : H.IsSymmetric)
    (hb : ∀ i, H (b i) = (lam i : ℂ) • b i) (hHV : ∀ v, H v = kin f A v + V v)
    {CV : ℝ} (hCV : 0 ≤ CV) (hV : ∀ v, ‖V v‖ ≤ CV * ‖wt f A (1 / 2) v‖)
    {C₀ : ℝ} (hlow : ∀ i, -C₀ ≤ lam i) {CG : ℝ} (hCG : 0 ≤ CG)
    (hG : ∀ v, ‖fc b lam (fun l => ((l + C₀ + 1 : ℝ) : ℂ)) v‖ ≤ CG * ‖wt f A 1 v‖)
    (Cop : E →ₗ[ℂ] E) (hCop : ∀ v, ‖Cop v‖ ≤ ‖v‖)
    {t Δ X p α β E₀ : ℝ} (ht : 0 < t) (hΔ : 0 ≤ Δ) (hX : -C₀ ≤ X) (hp0 : 0 ≤ p) (hp2 : p ≤ 2)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hE : E₀ < X - Δ)
    (hq : ∀ E' : ℝ, -C₀ ≤ E' → E' ≤ X → ∀ q : E,
        ‖H q - (E' : ℂ) • q‖ ≤ Δ * ‖q‖ → ‖Cop q‖ ^ 2 ≤ (α + β * (1 + E' + C₀) ^ p) * ‖q‖ ^ 2)
    (u : E) (hu : ∀ k, E₀ < A k → ⟪f k, u⟫_ℂ = 0) :
    (1 / t) * ∫ τ in (0 : ℝ)..t,
        ‖Cop (fc b lam (fun x => Complex.exp (Complex.I * (x : ℂ) * τ)) u)‖ ^ 2 ≤
      2 * Real.exp 1 * (Real.sqrt π * (α * ‖u‖ ^ 2 +
          β * (1 + Δ) ^ p * (CG ^ (p / 2)) ^ 2 * ‖wt f A (p / 2) u‖ ^ 2 +
          (CV / (X - Δ - E₀)) ^ 2 * ‖wt f A (1 / 2) u‖ ^ 2) +
        Real.sqrt (2 * π) * Real.exp (-(t ^ 2 * Δ ^ 2) / 2) * ‖u‖ ^ 2) := by
  have h1 := tavg_window_bound b lam H hb hlow Cop hCop ht hΔ hX hp0 hα hβ hq u
  refine h1.trans ?_
  -- the three parts of the spectral sum
  have hx : ∀ i, 0 ≤ lam i + C₀ + 1 := fun i => by linarith [hlow i]
  have hy : ∀ k, 0 ≤ 1 + A k := fun k => by linarith [hA k]
  -- (a) the moment, through Löwner–Heinz
  have hmom : ∑ i, (1 + lam i + C₀) ^ p * ‖⟪b i, u⟫_ℂ‖ ^ 2 ≤
      (CG ^ (p / 2)) ^ 2 * ‖wt f A (p / 2) u‖ ^ 2 := by
    have hG' : ∀ v, ‖FluxSourceTest.ePow b (fun i => lam i + C₀ + 1) 1 v‖ ≤
        CG * ‖FluxSourceTest.ePow f (fun k => 1 + A k) 1 v‖ := by
      intro v
      rw [ePow_comp_eq_fc b lam (fun l => l + C₀ + 1), ePow_one_add_eq_wt]
      simpa only [Real.rpow_one] using hG v
    have hs : p / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by positivity, by linarith⟩
    have hLH := FluxSourceTest.norm_ePow_le_of_norm_ePow_le b f hx hy hCG hG' hs u
    rw [ePow_one_add_eq_wt] at hLH
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hLH 2
    rw [FluxSourceTest.norm_sq_ePow, mul_pow] at hsq
    refine le_of_eq_of_le ?_ hsq
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hx i)]
    norm_num
    ring_nf
  -- (b) the high spectral part, through the spectral leakage
  have hhigh : ∑ i, (if X - Δ ≤ lam i then (1 : ℝ) else 0) * ‖⟪b i, u⟫_ℂ‖ ^ 2 ≤
      (CV / (X - Δ - E₀)) ^ 2 * ‖wt f A (1 / 2) u‖ ^ 2 := by
    have hsl := specleak b lam f A H V hH hb hHV hCV hV hE u hu
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hsl 2
    rw [mul_pow] at hsq
    refine le_of_eq_of_le ?_ hsq
    rw [specGe, norm_sq_fc]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  -- (c) assemble
  have hsplit : ∑ i, (α + β * (1 + Δ) ^ p * (1 + lam i + C₀) ^ p +
        (if X - Δ ≤ lam i then 1 else 0)) * ‖⟪b i, u⟫_ℂ‖ ^ 2 =
      α * ‖u‖ ^ 2 + β * (1 + Δ) ^ p * ∑ i, (1 + lam i + C₀) ^ p * ‖⟪b i, u⟫_ℂ‖ ^ 2 +
        ∑ i, (if X - Δ ≤ lam i then (1 : ℝ) else 0) * ‖⟪b i, u⟫_ℂ‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right u, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hβΔ : 0 ≤ β * (1 + Δ) ^ p := by positivity
  rw [hsplit]
  have key : α * ‖u‖ ^ 2 + β * (1 + Δ) ^ p * ∑ i, (1 + lam i + C₀) ^ p * ‖⟪b i, u⟫_ℂ‖ ^ 2 +
        ∑ i, (if X - Δ ≤ lam i then (1 : ℝ) else 0) * ‖⟪b i, u⟫_ℂ‖ ^ 2 ≤
      α * ‖u‖ ^ 2 + β * (1 + Δ) ^ p * (CG ^ (p / 2)) ^ 2 * ‖wt f A (p / 2) u‖ ^ 2 +
        (CV / (X - Δ - E₀)) ^ 2 * ‖wt f A (1 / 2) u‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hmom hβΔ
    nlinarith [this, hhigh]
  have hpi : 0 ≤ Real.sqrt π := Real.sqrt_nonneg _
  have he : 0 ≤ 2 * Real.exp 1 := by positivity
  gcongr

end FSSpectral
