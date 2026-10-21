import PlaneWave.FreeBoundary.RangeCut

/-!
# `app:free`, part 7: the position-space kernel, the retained region and the torus Fourier
coefficients

The manuscript defines the range-truncated kernel by the nearest-image distance,
`g_L(x) = θ(|x|_ni)/|x|_ni`, `|x|_ni = min_n |x - L n|` (`niDist`, `gLni`).

* `niDist_eq_norm`: on the closed cell `‖x‖_∞ ≤ L/2` the nearest image is `x` itself;
* `gLni_eq_inv`: `g_L(x) = 1/|x|` for `|x| ≤ L/2 - ρ` when `θ ≡ 1` on `[0, L/2 - ρ]`;
* **`retained_potential`** (the retained region): with the nuclei in `B_{R₀}(c₀)`,
  `R_L = L/4 - R₀ - ρ` and every electron in `B_{R_L}(c₀)`, every pair distance is at most
  `L/2 - ρ` (`retained_pair`, `retained_nuclear`), so the `g_L` interaction (zero mode included:
  it is the function `g_L` itself) equals the free-space Coulomb interaction;
* **`mFourierCoeff_gLtorus`** (the first identity of eq:rangecut): the torus Fourier coefficients
  of `g_L`, in the dimensionless coordinates `x = r/L` of the release (`UnitAddTorus (Fin 3)`),
  are `ĝ_L(ν) = Ω⁻¹ ∫_{ℝ³} g(r) e^{-i k_ν·r} dr` (`ghat`, `PlaneWave.FreeBoundary.RangeCut`); at `ν = 0` this is the zero
  mode `ĝ_L(0) = Ω⁻¹ ∫ g_L`. So the Fourier-space Hamiltonian of `PlaneWave.FreeBoundary.CubeHamiltonian`–`PlaneWave.FreeBoundary.GridEnergy`, with the zero
  mode added back, is the torus Hamiltonian of the function `g_L`.
-/

set_option autoImplicit false

open MeasureTheory Set Real PlaneWaveCertificate
open scoped InnerProductSpace

namespace FreeBoundary

/-! ## The nearest-image distance -/

/-- The lattice translate `L n`. -/
noncomputable def latVec (L : ℝ) (n : Fin 3 → ℤ) : E3 := WithLp.toLp 2 (fun c => L * (n c : ℝ))

/-- The nearest-image distance on the cell `T_L`. -/
noncomputable def niDist (L : ℝ) (x : E3) : ℝ := ⨅ n : Fin 3 → ℤ, ‖x - latVec L n‖

/-- **The range-truncated kernel** `g_L(x) = θ(|x|_ni)/|x|_ni`. -/
noncomputable def gLni (L : ℝ) (θ : ℝ → ℝ) (x : E3) : ℝ := θ (niDist L x) / niDist L x

lemma niDist_le (L : ℝ) (x : E3) (n : Fin 3 → ℤ) : niDist L x ≤ ‖x - latVec L n‖ :=
  ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; exact norm_nonneg _⟩ n

lemma latVec_zero (L : ℝ) : latVec L 0 = 0 := by
  unfold latVec
  ext c
  simp

/-- A cell coordinate is no farther from `0` than from any lattice translate. -/
lemma sq_le_sq_sub_lattice {L t : ℝ} (hL : 0 ≤ L) (ht : |t| ≤ L / 2) (n : ℤ) :
    t ^ 2 ≤ (t - L * n) ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  have key : (t - L * n) ^ 2 = t ^ 2 + (L * n) * (L * n - 2 * t) := by ring
  rw [key]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_iff.mpr hn
    have a : L * (n : ℝ) ≤ -L := by nlinarith [mul_nonneg hL (by linarith : (0 : ℝ) ≤ -(n : ℝ) - 1)]
    have b : L * (n : ℝ) - 2 * t ≤ 0 := by linarith
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (by linarith : L * (n : ℝ) ≤ 0) b]
  · subst hn
    simp
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have a : L ≤ L * (n : ℝ) := by nlinarith [mul_nonneg hL (by linarith : (0 : ℝ) ≤ (n : ℝ) - 1)]
    have b : 0 ≤ L * (n : ℝ) - 2 * t := by linarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ L * (n : ℝ)) b]

lemma abs_coord_le_norm (x : E3) (c : Fin 3) : |x c| ≤ ‖x‖ := by
  have h : (x c) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (f := fun i => (x i) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ c)
  rw [← sq_abs] at h
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- On the closed cell the nearest image is the point itself. -/
lemma niDist_eq_norm {L : ℝ} (hL : 0 ≤ L) {x : E3} (hx : ∀ c, |x c| ≤ L / 2) :
    niDist L x = ‖x‖ := by
  apply le_antisymm
  · have h := niDist_le L x 0
    rwa [latVec_zero, sub_zero] at h
  · apply le_ciInf
    intro n
    have h : ‖x‖ ^ 2 ≤ ‖x - latVec L n‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_le_sum fun c _ => ?_
      have hc : (x - latVec L n) c = x c - L * (n c : ℝ) := by
        simp [latVec]
      rw [hc]
      exact sq_le_sq_sub_lattice hL (hx c) (n c)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- On the closed cell `g_L` is the radial kernel `g = θ(|x|)/|x|`. -/
lemma gLni_eq_gker {L : ℝ} (hL : 0 ≤ L) (θ : ℝ → ℝ) {x : E3} (hx : ∀ c, |x c| ≤ L / 2) :
    gLni L θ x = gker θ x := by
  unfold gLni gker
  rw [niDist_eq_norm hL hx]

/-- `g_L(x) = 1/|x|` for `|x| ≤ L/2 - ρ` when `θ ≡ 1` on `[0, L/2 - ρ]`. -/
lemma gLni_eq_inv {L ρ : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ) {θ : ℝ → ℝ}
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) {x : E3} (hx : ‖x‖ ≤ L / 2 - ρ) :
    gLni L θ x = 1 / ‖x‖ := by
  have hcell : ∀ c, |x c| ≤ L / 2 := fun c => (abs_coord_le_norm x c).trans (by linarith)
  unfold gLni
  rw [niDist_eq_norm hL.le hcell, hone _ (norm_nonneg _) hx]

/-! ## The retained region -/

/-- The radius `R_L = L/4 - R₀ - ρ` of the retained region. -/
noncomputable def retainedRadius (L R0 ρ : ℝ) : ℝ := L / 4 - R0 - ρ

/-- Two electrons of the retained region are at distance at most `2 R_L ≤ L/2 - ρ`. -/
theorem retained_pair {L R0 ρ : ℝ} (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) {θ : ℝ → ℝ}
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) (c0 ri rj : E3)
    (hi : ‖ri - c0‖ ≤ retainedRadius L R0 ρ) (hj : ‖rj - c0‖ ≤ retainedRadius L R0 ρ) :
    gLni L θ (ri - rj) = 1 / ‖ri - rj‖ := by
  apply gLni_eq_inv hL hρ hone
  have h : ‖ri - rj‖ ≤ ‖ri - c0‖ + ‖rj - c0‖ := by
    calc ‖ri - rj‖ = ‖(ri - c0) - (rj - c0)‖ := by congr 1; abel
      _ ≤ ‖ri - c0‖ + ‖rj - c0‖ := norm_sub_le _ _
  unfold retainedRadius at hi hj
  linarith

/-- An electron of the retained region and a nucleus in `B_{R₀}(c₀)` are at distance at most
`R_L + R₀ = L/4 - ρ ≤ L/2 - ρ`. -/
theorem retained_nuclear {L R0 ρ : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ) {θ : ℝ → ℝ}
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) (c0 ri Rl : E3)
    (hi : ‖ri - c0‖ ≤ retainedRadius L R0 ρ) (hl : ‖Rl - c0‖ ≤ R0) :
    gLni L θ (ri - Rl) = 1 / ‖ri - Rl‖ := by
  apply gLni_eq_inv hL hρ hone
  have h : ‖ri - Rl‖ ≤ ‖ri - c0‖ + ‖Rl - c0‖ := by
    calc ‖ri - Rl‖ = ‖(ri - c0) - (Rl - c0)‖ := by congr 1; abel
      _ ≤ ‖ri - c0‖ + ‖Rl - c0‖ := norm_sub_le _ _
  unfold retainedRadius at hi
  linarith

section Potential

variable {eta : ℕ} {ν : Type*} [Fintype ν]

/-- The `g_L` interaction `Σ_{a<b} q_a q_b g_L(r_a - r_b) + Σ_{a,ℓ} q_a Z_ℓ g_L(r_a - R_ℓ)`. -/
noncomputable def potL (L : ℝ) (θ : ℝ → ℝ) (q : Fin eta → ℝ) (Z : ν → ℝ) (Rn : ν → E3)
    (r : Fin eta → E3) : ℝ :=
  (∑ pair : FiniteElectronPair eta, q pair.1.1 * q pair.1.2 * gLni L θ (r pair.1.1 - r pair.1.2)) +
    ∑ a, ∑ l, q a * Z l * gLni L θ (r a - Rn l)

/-- The free-space Coulomb interaction. -/
noncomputable def potInf (q : Fin eta → ℝ) (Z : ν → ℝ) (Rn : ν → E3) (r : Fin eta → E3) : ℝ :=
  (∑ pair : FiniteElectronPair eta, q pair.1.1 * q pair.1.2 * (1 / ‖r pair.1.1 - r pair.1.2‖)) +
    ∑ a, ∑ l, q a * Z l * (1 / ‖r a - Rn l‖)

/-- **The retained region**: with the nuclei in `B_{R₀}(c₀)` and every electron in
`B_{R_L}(c₀)`, `R_L = L/4 - R₀ - ρ`, the `g_L` interaction is the free-space Coulomb interaction,
when `θ ≡ 1` on `[0, L/2 - ρ]`. -/
theorem retained_potential {L R0 ρ : ℝ} (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) {θ : ℝ → ℝ}
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1) (c0 : E3) (q : Fin eta → ℝ) (Z : ν → ℝ)
    (Rn : ν → E3) (hRn : ∀ l, ‖Rn l - c0‖ ≤ R0) (r : Fin eta → E3)
    (hr : ∀ a, ‖r a - c0‖ ≤ retainedRadius L R0 ρ) :
    potL L θ q Z Rn r = potInf q Z Rn r := by
  unfold potL potInf
  congr 1
  · refine Finset.sum_congr rfl fun pair _ => ?_
    rw [retained_pair hL hR0 hρ hone c0 _ _ (hr _) (hr _)]
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => ?_
    rw [retained_nuclear hL hρ hone c0 _ _ (hr a) (hRn l)]

end Potential

/-! ## The torus Fourier coefficients -/

/-- The point of the cell `(-L/2, L/2]³` representing a point of the unit torus (dimensionless
coordinates `x = r/L`). -/
noncomputable def cellRep (L : ℝ) (t : UnitAddTorus (Fin 3)) : E3 :=
  WithLp.toLp 2 (fun c => L * (AddCircle.equivIoc 1 (-1 / 2) (t c) : ℝ))

/-- The range-truncated kernel as a function on the unit torus. -/
noncomputable def gLtorus (L : ℝ) (θ : ℝ → ℝ) (t : UnitAddTorus (Fin 3)) : ℂ :=
  (gLni L θ (cellRep L t) : ℂ)

/-- The integrand of `gFT`. -/
noncomputable def ftInt (θ : ℝ → ℝ) (k y : E3) : ℂ :=
  (gker θ y : ℂ) * Complex.exp (-(Complex.I * (⟪k, y⟫_ℝ : ℂ)))

lemma inner_kvec_smul (L : ℝ) (hL : L ≠ 0) (ν : Lattice3) (x : Fin 3 → ℝ) :
    ⟪kvec L ν, (WithLp.toLp 2 (L • x) : E3)⟫_ℝ = ∑ c, 2 * π * (ν c : ℝ) * x c := by
  simp only [kvec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  field_simp

/-- **The torus Fourier coefficients of `g_L` are `ĝ_L`** (for a profile vanishing beyond
`R ≤ L/2`). -/
theorem mFourierCoeff_gLtorus {L : ℝ} (hL : 0 < L) {R : ℝ} {θ : ℝ → ℝ} (hθ : Profile R θ)
    (hR : R ≤ L / 2) (ν : Lattice3) :
    UnitAddTorus.mFourierCoeff (gLtorus L θ) ν = ghat L θ ν := by
  have hL0 : L ≠ 0 := hL.ne'
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ ν (fun _ => -1 / 2)]
  set S : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | ∀ i, x i ∈ Ioc ((fun _ : Fin 3 => (-1 / 2 : ℝ)) i)
    ((fun _ : Fin 3 => (-1 / 2 : ℝ)) i + 1)} with hS
  set G : E3 → ℂ := ftInt θ (kvec L ν) with hG
  -- the integrand on the box
  have hbox : ∀ x ∈ S, (UnitAddTorus.mFourier (-ν) (fun i => (x i : UnitAddCircle))) •
      gLtorus L θ (fun i => (x i : UnitAddCircle)) = G (WithLp.toLp 2 (L • x)) := by
    intro x hx
    have hrep : cellRep L (fun i => (x i : UnitAddCircle)) = WithLp.toLp 2 (L • x) := by
      unfold cellRep
      congr 1
      funext c
      rw [AddCircle.equivIoc_coe_of_mem (hx c)]
      rfl
    have hcell : ∀ c, |(WithLp.toLp 2 (L • x) : E3) c| ≤ L / 2 := by
      intro c
      have h := hx c
      simp only [Set.mem_Ioc] at h
      change |L * x c| ≤ L / 2
      rw [abs_mul, abs_of_pos hL]
      have : |x c| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [h.1, h.2]
      nlinarith
    have hF : UnitAddTorus.mFourier (-ν) (fun i => (x i : UnitAddCircle)) =
        Complex.exp (-(Complex.I * ((∑ c, 2 * π * (ν c : ℝ) * x c : ℝ) : ℂ))) := by
      simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      simp only [Pi.neg_apply, Int.cast_neg, div_one]
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hF, gLtorus, hrep, gLni_eq_gker hL.le θ hcell, hG, ftInt, inner_kvec_smul L hL0 ν x,
      smul_eq_mul]
    ring
  have hSm : MeasurableSet S := by
    have hSeq : S = ⋂ i : Fin 3, (fun x : Fin 3 → ℝ => x i) ⁻¹' Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
      ext x
      simp [hS]
    rw [hSeq]
    exact MeasurableSet.iInter fun i => measurableSet_Ioc.preimage (measurable_pi_apply i)
  rw [setIntegral_congr_fun hSm hbox]
  -- the integrand vanishes off the box
  have hzero : ∀ x, x ∉ S → G (WithLp.toLp 2 (L • x)) = 0 := by
    intro x hx
    have hx' : ∃ c, x c ∉ Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
      by_contra hcon
      push Not at hcon
      exact hx hcon
    obtain ⟨c, hc⟩ := hx'
    have hc' : 1 / 2 ≤ |x c| := by
      simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hc
      rcases hc with hc | hc
      · rw [le_abs]; right; linarith
      · rw [le_abs]; left; linarith
    have hn : R ≤ ‖(WithLp.toLp 2 (L • x) : E3)‖ := by
      have h1 := abs_coord_le_norm (WithLp.toLp 2 (L • x) : E3) c
      have h2 : |(WithLp.toLp 2 (L • x) : E3) c| = L * |x c| := by
        change |L * x c| = L * |x c|
        rw [abs_mul, abs_of_pos hL]
      rw [h2] at h1
      nlinarith
    rw [hG, ftInt, gker, hθ.vanish _ hn, zero_div, Complex.ofReal_zero, zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  -- to `E3`, and the scaling `y = L x`
  have h1 : ∫ x : Fin 3 → ℝ, G (WithLp.toLp 2 (L • x)) = ∫ y : E3, G (L • y) := by
    have := (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding (fun y : E3 => G (L • y))
    rw [← this]
    rfl
  rw [h1, Measure.integral_comp_smul, finrank_euclideanSpace_fin]
  unfold ghat
  rw [hG]
  change |(L ^ 3)⁻¹| • gFT θ (kvec L ν) = _
  rw [abs_of_pos (by positivity), Complex.real_smul, div_eq_inv_mul]
  push_cast
  ring

/-- The zero mode of the torus kernel: `ĝ_L(0) = Ω⁻¹ ∫ g_L`, `|ĝ_L(0)| ≤ π/(2L)` for `R = L/2`. -/
theorem mFourierCoeff_gLtorus_zero {L : ℝ} (hL : 0 < L) {θ : ℝ → ℝ} (hθ : Profile (L / 2) θ) :
    ‖UnitAddTorus.mFourierCoeff (gLtorus L θ) (fun _ => 0)‖ ≤ π / (2 * L) := by
  rw [mFourierCoeff_gLtorus hL hθ le_rfl]
  exact ghat_zero_le_half hL hθ

end FreeBoundary
