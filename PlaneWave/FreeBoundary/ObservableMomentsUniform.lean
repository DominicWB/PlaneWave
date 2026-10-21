import PlaneWave.FreeBoundary.GridDynamicsUniformTheorem
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# `L`-uniform moments of a fixed observable

The constants of `PlaneWave.FreeBoundary.GridDynamicsUniformTheorem` are functions of the moments
`C_χ`, `‖O‖`, `g² D₂`, `g⁴ D₄` and of the `(Hχ)` constants `C_{χ,M}` of the torus observable `χ`.
For the cell version `χ(t) = f(L · rep t)` of a fixed one-particle observable `f`, these are Riemann
sums of moments of `f̂`; here they are bounded uniformly in `L`, for a Schwartz function `f`
vanishing outside the open cell `(-L/2, L/2)³`:

* `mFourierCoeff_cell`: `χ̂(ν) = L⁻³ 𝓕f(ν/L)` (Mathlib's `𝓕f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`);
* `ftDecay F N = sup_ξ (1 + |ξ|)^N |𝓕F(ξ)|`, finite for a Schwartz `F`;
* `tsum_latWeight_le`: the lattice sum `Σ_ν L⁻³ (1 + |ν/L|)⁻⁶ ≤ 27` for `L ≥ 1`;
* `CellDecay`: `|c(ν)| ≤ B_N L⁻³ (1 + |ν/L|)^{-N}`, and its consequences
  `Σ |c| ≤ 27 B₆`, `g² Σ |ν|² |c| ≤ 27 (2π)² B₈`, `g⁴ Σ |ν|⁴ |c| ≤ 27 (2π)⁴ B₁₀` and `(Hχ)` with
  `C_{χ,M} = 27 (2π)^M B_{M+6}`;
* `gridConstsSharp_gLU_mono`: the constants are monotone in the moments, and
  `gridConstsPosU_le_of_decay`: at a cell observable they are dominated by `L`-free ones;
* `free_dyn_grid_gLU_decay`: `prop:free-dyn` for an observable `0 ≤ f ≤ 1` vanishing outside the
  ball of radius `R_f`, `L > 2 R_f`, whose transform has decay constants `B_N`;
* **`free_dyn_grid_gLU_schwartz`**: the same for a fixed Schwartz `f` (`F = f` in `𝓢(ℝ³, ℂ)`),
  with `B_N = ftDecay F N`: the constants `(A₁, A₂, A₃)` and `C_{χ,5}` are functions of the
  system, of `V_θ`, of the data `(‖φ(0)‖, ‖h₀‖, ‖h₁‖)` and of `f` only.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap
open Finset Set MeasureTheory
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLgamma_pos gLref gLNucData regParticlesOfG gLzU gLzU_nonneg gLAU
  gLGridCoupling)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The coefficients of a cell function -/

section Coefficients

/-- The frequency `ν / L ∈ ℝ³` of the lattice vector `ν` (the momentum is `k_ν = 2π ν / L`). -/
noncomputable def latFreq (L : ℝ) (n : Lattice3) : E3 := WithLp.toLp 2 (fun c => (n c : ℝ) / L)

lemma latFreq_apply (L : ℝ) (n : Lattice3) (c : Fin 3) : latFreq L n c = (n c : ℝ) / L := rfl

lemma latFreq_neg (L : ℝ) (n : Lattice3) : latFreq L (-n) = -latFreq L n := by
  ext c
  simp only [latFreq_apply, Pi.neg_apply, Int.cast_neg, PiLp.neg_apply, neg_div]

lemma norm_latFreq_sq (L : ℝ) (n : Lattice3) : ‖latFreq L n‖ ^ 2 = nsq n / L ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, nsq_eq_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [latFreq_apply, div_pow]

lemma abs_div_le_norm_latFreq {L : ℝ} (hL : 0 < L) (n : Lattice3) (c : Fin 3) :
    |(n c : ℝ)| / L ≤ ‖latFreq L n‖ := by
  have h := abs_coord_le_norm (latFreq L n) c
  rwa [latFreq_apply, abs_div, abs_of_pos hL] at h

/-- `g |ν|_∞ ≤ 2π |ν/L|` for `g = 2π/L`. -/
lemma mul_latticeSupNorm_le {L : ℝ} (hL : 0 < L) (n : Lattice3) :
    2 * Real.pi / L * latticeSupNorm n ≤ 2 * Real.pi * ‖latFreq L n‖ := by
  have h : latticeSupNorm n / L ≤ ‖latFreq L n‖ := by
    unfold latticeSupNorm
    rw [← max_div_div_right hL.le, ← max_div_div_right hL.le]
    exact max_le (max_le (abs_div_le_norm_latFreq hL n 0) (abs_div_le_norm_latFreq hL n 1))
      (abs_div_le_norm_latFreq hL n 2)
  have e : 2 * Real.pi / L * latticeSupNorm n = 2 * Real.pi * (latticeSupNorm n / L) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- `g² |ν|² = (2π)² |ν/L|²` for `g = 2π/L`. -/
lemma sq_mul_nsq_eq {L : ℝ} (hL : 0 < L) (n : Lattice3) :
    (2 * Real.pi / L) ^ 2 * nsq n = (2 * Real.pi) ^ 2 * ‖latFreq L n‖ ^ 2 := by
  rw [norm_latFreq_sq]
  field_simp

/-- **The torus coefficients of a function on the cell.** If `χ(t) = f(L · rep t)` on the unit
torus and `f` vanishes outside the open cell `(-L/2, L/2)³`, then `χ̂(ν) = L⁻³ 𝓕f(ν/L)`. -/
theorem mFourierCoeff_cell {L : ℝ} (hL : 0 < L) {f : E3 → ℂ}
    (hf : ∀ y : E3, f y ≠ 0 → ∀ c, |y c| < L / 2) {χ : C(UnitAddTorus (Fin 3), ℂ)}
    (hχ : ∀ t, χ t = f (cellRep L t)) (n : Lattice3) :
    mFourierCoeff χ n = ((L ^ 3)⁻¹ : ℝ) • 𝓕 f (latFreq L n) := by
  have hL0 : L ≠ 0 := hL.ne'
  rw [mFourierCoeff_eq_integral _ n (fun _ => -1 / 2)]
  set S : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | ∀ i, x i ∈ Ioc ((fun _ : Fin 3 => (-1 / 2 : ℝ)) i)
    ((fun _ : Fin 3 => (-1 / 2 : ℝ)) i + 1)} with hS
  set G : E3 → ℂ := fun v =>
    Complex.exp (↑(-2 * Real.pi * ⟪v, latFreq L n⟫_ℝ) * Complex.I) • f v with hG
  have hinner : ∀ x : Fin 3 → ℝ,
      ⟪(WithLp.toLp 2 (L • x) : E3), latFreq L n⟫_ℝ = ∑ c, (n c : ℝ) * x c := by
    intro x
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, latFreq_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hbox : ∀ x ∈ S, mFourier (-n) (fun i => (x i : UnitAddCircle)) •
      χ (fun i => (x i : UnitAddCircle)) = G (WithLp.toLp 2 (L • x)) := by
    intro x hx
    have hrep : cellRep L (fun i => (x i : UnitAddCircle)) = WithLp.toLp 2 (L • x) := by
      unfold cellRep
      congr 1
      funext c
      rw [AddCircle.equivIoc_coe_of_mem (hx c)]
      rfl
    have hF : mFourier (-n) (fun i => (x i : UnitAddCircle)) =
        Complex.exp (-(Complex.I * ((∑ c, 2 * Real.pi * (n c : ℝ) * x c : ℝ) : ℂ))) := by
      simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      simp only [Pi.neg_apply, Int.cast_neg, div_one]
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    have hr : (-2 * Real.pi * ⟪(WithLp.toLp 2 (L • x) : E3), latFreq L n⟫_ℝ) =
        -(∑ c, 2 * Real.pi * (n c : ℝ) * x c) := by
      rw [hinner, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hF, hχ, hrep, hG]
    simp only
    rw [hr]
    congr 2
    push_cast
    ring
  have hSm : MeasurableSet S := by
    have hSeq : S = ⋂ i : Fin 3, (fun x : Fin 3 → ℝ => x i) ⁻¹' Ioc (-1 / 2 : ℝ) (-1 / 2 + 1) := by
      ext x
      simp [hS]
    rw [hSeq]
    exact MeasurableSet.iInter fun i => measurableSet_Ioc.preimage (measurable_pi_apply i)
  rw [setIntegral_congr_fun hSm hbox]
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
    have hf0 : f (WithLp.toLp 2 (L • x)) = 0 := by
      by_contra hne
      have h := hf _ hne c
      have h2 : |(WithLp.toLp 2 (L • x) : E3) c| = L * |x c| := by
        change |L * x c| = L * |x c|
        rw [abs_mul, abs_of_pos hL]
      rw [h2] at h
      nlinarith
    rw [hG]
    simp only
    rw [hf0, smul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have h1 : ∫ x : Fin 3 → ℝ, G (WithLp.toLp 2 (L • x)) = ∫ y : E3, G (L • y) := by
    have := (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding (fun y : E3 => G (L • y))
    rw [← this]
    rfl
  rw [h1, Measure.integral_comp_smul, finrank_euclideanSpace_fin, Real.fourier_eq',
    abs_of_pos (by positivity : (0 : ℝ) < (L ^ 3)⁻¹)]

end Coefficients

/-! ## Lattice sums -/

section LatticeSums

/-- The one-dimensional weight `h / (1 + h |n|)²`. -/
noncomputable def w1 (h : ℝ) (n : ℤ) : ℝ := h / (1 + h * |(n : ℝ)|) ^ 2

lemma w1_nonneg {h : ℝ} (hh : 0 ≤ h) (n : ℤ) : 0 ≤ w1 h n := by
  unfold w1
  positivity

/-- Telescoping: `Σ_{k<N} h/(1+h(k+1))² ≤ 1 - 1/(1+hN)`. -/
lemma sum_range_w1_succ_le {h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    ∑ k ∈ Finset.range N, h / (1 + h * ((k : ℝ) + 1)) ^ 2 ≤ 1 - 1 / (1 + h * N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h1 : 0 < 1 + h * N := by positivity
    have h2 : 0 < 1 + h * ((N : ℝ) + 1) := by positivity
    have key : h / (1 + h * ((N : ℝ) + 1)) ^ 2 ≤
        1 / (1 + h * N) - 1 / (1 + h * ((N : ℝ) + 1)) := by
      rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hh h2.le) hh]
    push_cast
    linarith

lemma w1_neg_succ (h : ℝ) (k : ℕ) :
    w1 h (-((k : ℤ) + 1)) = h / (1 + h * ((k : ℝ) + 1)) ^ 2 := by
  unfold w1
  push_cast
  rw [abs_neg, abs_of_nonneg (by positivity)]

lemma w1_natCast_succ (h : ℝ) (k : ℕ) :
    w1 h ((k + 1 : ℕ) : ℤ) = h / (1 + h * ((k : ℝ) + 1)) ^ 2 := by
  unfold w1
  push_cast
  rw [abs_of_nonneg (by positivity)]

lemma sum_range_w1_neg_le {h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    ∑ k ∈ Finset.range N, w1 h (-((k : ℤ) + 1)) ≤ 1 := by
  simp_rw [w1_neg_succ]
  have := sum_range_w1_succ_le hh N
  have : 0 ≤ 1 / (1 + h * N) := by positivity
  linarith

lemma sum_range_w1_le {h : ℝ} (hh : 0 ≤ h) (N : ℕ) :
    ∑ k ∈ Finset.range N, w1 h (k : ℤ) ≤ h + 1 := by
  cases N with
  | zero => simp; linarith
  | succ N =>
    rw [Finset.sum_range_succ']
    have e : ∀ k : ℕ, w1 h ((k + 1 : ℕ) : ℤ) = h / (1 + h * ((k : ℝ) + 1)) ^ 2 :=
      w1_natCast_succ h
    simp_rw [e]
    have h0 : w1 h ((0 : ℕ) : ℤ) = h := by
      unfold w1
      simp
    rw [h0]
    have := sum_range_w1_succ_le hh N
    have : 0 ≤ 1 / (1 + h * N) := by positivity
    linarith

lemma summable_w1_nat {h : ℝ} (hh : 0 ≤ h) : Summable fun k : ℕ => w1 h (k : ℤ) :=
  summable_of_sum_range_le (fun _ => w1_nonneg hh _) (sum_range_w1_le hh)

lemma summable_w1_neg {h : ℝ} (hh : 0 ≤ h) : Summable fun k : ℕ => w1 h (-((k : ℤ) + 1)) :=
  summable_of_sum_range_le (fun _ => w1_nonneg hh _) (sum_range_w1_neg_le hh)

lemma summable_w1 {h : ℝ} (hh : 0 ≤ h) : Summable (w1 h) :=
  Summable.of_nat_of_neg_add_one (summable_w1_nat hh) (summable_w1_neg hh)

lemma tsum_w1_le {h : ℝ} (hh : 0 ≤ h) : ∑' n, w1 h n ≤ h + 2 := by
  rw [tsum_of_nat_of_neg_add_one (summable_w1_nat hh) (summable_w1_neg hh)]
  have h1 := Real.tsum_le_of_sum_range_le (fun k => w1_nonneg hh _) (sum_range_w1_le hh)
  have h2 := Real.tsum_le_of_sum_range_le (fun k => w1_nonneg hh _) (sum_range_w1_neg_le hh)
  linarith

/-- The lattice weight `L⁻³ (1 + |ν/L|)⁻⁶`. -/
noncomputable def latWeight (L : ℝ) (n : Lattice3) : ℝ := (L ^ 3)⁻¹ / (1 + ‖latFreq L n‖) ^ 6

lemma latWeight_nonneg {L : ℝ} (hL : 0 < L) (n : Lattice3) : 0 ≤ latWeight L n := by
  unfold latWeight
  positivity

lemma latWeight_le_prod {L : ℝ} (hL : 0 < L) (n : Lattice3) :
    latWeight L n ≤ ∏ c, w1 L⁻¹ (n c) := by
  rw [Fin.prod_univ_three]
  unfold latWeight w1
  have hc : ∀ c, L⁻¹ * |(n c : ℝ)| ≤ ‖latFreq L n‖ := by
    intro c
    have := abs_div_le_norm_latFreq hL n c
    rwa [div_eq_inv_mul] at this
  have e : L⁻¹ / (1 + L⁻¹ * |(n 0 : ℝ)|) ^ 2 * (L⁻¹ / (1 + L⁻¹ * |(n 1 : ℝ)|) ^ 2) *
      (L⁻¹ / (1 + L⁻¹ * |(n 2 : ℝ)|) ^ 2) = (L ^ 3)⁻¹ / ((1 + L⁻¹ * |(n 0 : ℝ)|) ^ 2 *
        (1 + L⁻¹ * |(n 1 : ℝ)|) ^ 2 * (1 + L⁻¹ * |(n 2 : ℝ)|) ^ 2) := by
    field_simp
  rw [e]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc (1 + L⁻¹ * |(n 0 : ℝ)|) ^ 2 * (1 + L⁻¹ * |(n 1 : ℝ)|) ^ 2 * (1 + L⁻¹ * |(n 2 : ℝ)|) ^ 2
      ≤ (1 + ‖latFreq L n‖) ^ 2 * (1 + ‖latFreq L n‖) ^ 2 * (1 + ‖latFreq L n‖) ^ 2 := by
        have h0 : 0 ≤ L⁻¹ := by positivity
        gcongr
        · exact hc 0
        · exact hc 1
        · exact hc 2
    _ = (1 + ‖latFreq L n‖) ^ 6 := by ring

lemma sum_latWeight_le {L : ℝ} (hL : 1 ≤ L) (s : Finset Lattice3) :
    ∑ n ∈ s, latWeight L n ≤ 27 := by
  have hL0 : 0 < L := by linarith
  have hh : 0 ≤ L⁻¹ := by positivity
  have hh1 : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  set T : Finset ℤ := s.biUnion fun n => Finset.univ.image n
  have hsub : s ⊆ Fintype.piFinset fun _ : Fin 3 => T := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro c
    exact Finset.mem_biUnion.mpr ⟨n, hn, Finset.mem_image_of_mem n (Finset.mem_univ c)⟩
  have hT : ∑ k ∈ T, w1 L⁻¹ k ≤ 3 :=
    ((summable_w1 hh).sum_le_tsum T (fun k _ => w1_nonneg hh k)).trans
      ((tsum_w1_le hh).trans (by linarith))
  calc ∑ n ∈ s, latWeight L n ≤ ∑ n ∈ s, ∏ c, w1 L⁻¹ (n c) :=
        Finset.sum_le_sum fun n _ => latWeight_le_prod hL0 n
    _ ≤ ∑ n ∈ Fintype.piFinset (fun _ : Fin 3 => T), ∏ c, w1 L⁻¹ (n c) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => Finset.prod_nonneg fun c _ => w1_nonneg hh _)
    _ = ∏ _c : Fin 3, ∑ k ∈ T, w1 L⁻¹ k :=
        (Finset.prod_univ_sum (fun _ => T) (fun _ k => w1 L⁻¹ k)).symm
    _ ≤ ∏ _c : Fin 3, (3 : ℝ) :=
        Finset.prod_le_prod (fun c _ => Finset.sum_nonneg fun k _ => w1_nonneg hh k)
          (fun c _ => hT)
    _ = 27 := by norm_num

lemma summable_latWeight {L : ℝ} (hL : 1 ≤ L) : Summable (latWeight L) :=
  summable_of_sum_le (fun n => latWeight_nonneg (by linarith) n) (sum_latWeight_le hL)

/-- **The lattice sum** `Σ_ν L⁻³ (1 + |ν/L|)⁻⁶ ≤ 27` for `L ≥ 1`. -/
lemma tsum_latWeight_le {L : ℝ} (hL : 1 ≤ L) : ∑' n, latWeight L n ≤ 27 :=
  Real.tsum_le_of_sum_le (fun n => latWeight_nonneg (by linarith) n) (sum_latWeight_le hL)

end LatticeSums

/-! ## Moments under coefficient decay -/

section Moments

/-- Decay of lattice coefficients at the frequencies `ν/L`:
`|c(ν)| ≤ B_N L⁻³ (1 + |ν/L|)^{-N}` for every `N`. -/
def CellDecay (L : ℝ) (B : ℕ → ℝ) (c : Lattice3 → ℂ) : Prop :=
  ∀ (N : ℕ) (n : Lattice3), ‖c n‖ ≤ B N * ((L ^ 3)⁻¹ / (1 + ‖latFreq L n‖) ^ N)

variable {L : ℝ} {B : ℕ → ℝ} {c : Lattice3 → ℂ}

lemma CellDecay.nonneg (hc : CellDecay L B c) (hL : 0 < L) (N : ℕ) : 0 ≤ B N := by
  have h := hc N 0
  have hp : 0 < (L ^ 3)⁻¹ / (1 + ‖latFreq L 0‖) ^ N := by positivity
  exact le_of_mul_le_mul_right (by rw [zero_mul]; exact (norm_nonneg _).trans h) hp

lemma CellDecay.le_latWeight (hc : CellDecay L B c) (hL : 0 < L) (k : ℕ) (n : Lattice3) :
    (1 + ‖latFreq L n‖) ^ k * ‖c n‖ ≤ B (k + 6) * latWeight L n := by
  have h := hc (k + 6) n
  have hp : 0 < 1 + ‖latFreq L n‖ := by positivity
  calc (1 + ‖latFreq L n‖) ^ k * ‖c n‖
      ≤ (1 + ‖latFreq L n‖) ^ k * (B (k + 6) * ((L ^ 3)⁻¹ / (1 + ‖latFreq L n‖) ^ (k + 6))) := by
        gcongr
    _ = B (k + 6) * latWeight L n := by
        unfold latWeight
        rw [pow_add]
        field_simp

lemma CellDecay.summable_norm (hc : CellDecay L B c) (hL : 1 ≤ L) :
    Summable fun n => ‖c n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_latWeight hL).mul_left (B 6))
  simpa using hc.le_latWeight (by linarith) 0 n

/-- `C_χ = Σ |c| ≤ 27 B₆`. -/
lemma CellDecay.tsum_norm_le (hc : CellDecay L B c) (hL : 1 ≤ L) :
    ∑' n, ‖c n‖ ≤ 27 * B 6 := by
  have hL0 : 0 < L := by linarith
  calc ∑' n, ‖c n‖ ≤ ∑' n, B 6 * latWeight L n :=
        (hc.summable_norm hL).tsum_le_tsum (fun n => by simpa using hc.le_latWeight hL0 0 n)
          ((summable_latWeight hL).mul_left _)
    _ = B 6 * ∑' n, latWeight L n := tsum_mul_left
    _ ≤ B 6 * 27 := mul_le_mul_of_nonneg_left (tsum_latWeight_le hL) (hc.nonneg hL0 6)
    _ = 27 * B 6 := by ring

lemma nsq_le_mul_latFreq (hL : 0 < L) (n : Lattice3) :
    nsq n ≤ L ^ 2 * (1 + ‖latFreq L n‖) ^ 2 := by
  have h2 : nsq n = L ^ 2 * ‖latFreq L n‖ ^ 2 := by
    rw [norm_latFreq_sq]
    field_simp
  rw [h2]
  have h0 := norm_nonneg (latFreq L n)
  gcongr
  linarith

lemma CellDecay.nsq_mul_le (hc : CellDecay L B c) (hL : 0 < L) (n : Lattice3) :
    nsq n * ‖c n‖ ≤ L ^ 2 * (B 8 * latWeight L n) := by
  have h1 := nsq_le_mul_latFreq hL n
  have h2 : (1 + ‖latFreq L n‖) ^ 2 * ‖c n‖ ≤ B 8 * latWeight L n := hc.le_latWeight hL 2 n
  calc nsq n * ‖c n‖ ≤ L ^ 2 * (1 + ‖latFreq L n‖) ^ 2 * ‖c n‖ := by gcongr
    _ = L ^ 2 * ((1 + ‖latFreq L n‖) ^ 2 * ‖c n‖) := by ring
    _ ≤ L ^ 2 * (B 8 * latWeight L n) := by gcongr

lemma CellDecay.nsq_sq_mul_le (hc : CellDecay L B c) (hL : 0 < L) (n : Lattice3) :
    nsq n ^ 2 * ‖c n‖ ≤ L ^ 4 * (B 10 * latWeight L n) := by
  have h1 := nsq_le_mul_latFreq hL n
  have h1' : nsq n ^ 2 ≤ (L ^ 2 * (1 + ‖latFreq L n‖) ^ 2) ^ 2 :=
    pow_le_pow_left₀ (nsq_nonneg n) h1 2
  have h2 : (1 + ‖latFreq L n‖) ^ 4 * ‖c n‖ ≤ B 10 * latWeight L n := hc.le_latWeight hL 4 n
  calc nsq n ^ 2 * ‖c n‖ ≤ (L ^ 2 * (1 + ‖latFreq L n‖) ^ 2) ^ 2 * ‖c n‖ := by gcongr
    _ = L ^ 4 * ((1 + ‖latFreq L n‖) ^ 4 * ‖c n‖) := by ring
    _ ≤ L ^ 4 * (B 10 * latWeight L n) := by gcongr

lemma CellDecay.summable_nsq (hc : CellDecay L B c) (hL : 1 ≤ L) :
    Summable fun n => nsq n * ‖c n‖ :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (nsq_nonneg n) (norm_nonneg _))
    (fun n => hc.nsq_mul_le (by linarith) n)
    (((summable_latWeight hL).mul_left (B 8)).mul_left (L ^ 2))

lemma CellDecay.summable_nsq_sq (hc : CellDecay L B c) (hL : 1 ≤ L) :
    Summable fun n => nsq n ^ 2 * ‖c n‖ :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (nsq_nonneg n) 2) (norm_nonneg _))
    (fun n => hc.nsq_sq_mul_le (by linarith) n)
    (((summable_latWeight hL).mul_left (B 10)).mul_left (L ^ 4))

/-- `g² D₂ = g² Σ |ν|² |c| ≤ 27 (2π)² B₈`. -/
lemma CellDecay.momTwo_le (hc : CellDecay L B c) (hL : 1 ≤ L) :
    (2 * Real.pi / L) ^ 2 * momTwo c ≤ 27 * (2 * Real.pi) ^ 2 * B 8 := by
  have hL0 : 0 < L := by linarith
  have hs := hc.summable_nsq hL
  have hw := ((summable_latWeight hL).mul_left (B 8)).mul_left ((2 * Real.pi) ^ 2)
  unfold momTwo
  rw [← tsum_mul_left]
  calc ∑' n, (2 * Real.pi / L) ^ 2 * (nsq n * ‖c n‖)
      ≤ ∑' n, (2 * Real.pi) ^ 2 * (B 8 * latWeight L n) := by
        refine (hs.mul_left _).tsum_le_tsum (fun n => ?_) hw
        calc (2 * Real.pi / L) ^ 2 * (nsq n * ‖c n‖)
            ≤ (2 * Real.pi / L) ^ 2 * (L ^ 2 * (B 8 * latWeight L n)) :=
              mul_le_mul_of_nonneg_left (hc.nsq_mul_le hL0 n) (by positivity)
          _ = (2 * Real.pi) ^ 2 * (B 8 * latWeight L n) := by field_simp
    _ = (2 * Real.pi) ^ 2 * B 8 * ∑' n, latWeight L n := by
        rw [tsum_mul_left, tsum_mul_left]
        ring
    _ ≤ (2 * Real.pi) ^ 2 * B 8 * 27 := by
        have := hc.nonneg hL0 8
        exact mul_le_mul_of_nonneg_left (tsum_latWeight_le hL) (by positivity)
    _ = 27 * (2 * Real.pi) ^ 2 * B 8 := by ring

/-- `g⁴ D₄ = g⁴ Σ |ν|⁴ |c| ≤ 27 (2π)⁴ B₁₀`. -/
lemma CellDecay.momFour_le (hc : CellDecay L B c) (hL : 1 ≤ L) :
    (2 * Real.pi / L) ^ 4 * momFour c ≤ 27 * (2 * Real.pi) ^ 4 * B 10 := by
  have hL0 : 0 < L := by linarith
  have hs := hc.summable_nsq_sq hL
  have hw := ((summable_latWeight hL).mul_left (B 10)).mul_left ((2 * Real.pi) ^ 4)
  unfold momFour
  rw [← tsum_mul_left]
  calc ∑' n, (2 * Real.pi / L) ^ 4 * (nsq n ^ 2 * ‖c n‖)
      ≤ ∑' n, (2 * Real.pi) ^ 4 * (B 10 * latWeight L n) := by
        refine (hs.mul_left _).tsum_le_tsum (fun n => ?_) hw
        calc (2 * Real.pi / L) ^ 4 * (nsq n ^ 2 * ‖c n‖)
            ≤ (2 * Real.pi / L) ^ 4 * (L ^ 4 * (B 10 * latWeight L n)) :=
              mul_le_mul_of_nonneg_left (hc.nsq_sq_mul_le hL0 n) (by positivity)
          _ = (2 * Real.pi) ^ 4 * (B 10 * latWeight L n) := by field_simp
    _ = (2 * Real.pi) ^ 4 * B 10 * ∑' n, latWeight L n := by
        rw [tsum_mul_left, tsum_mul_left]
        ring
    _ ≤ (2 * Real.pi) ^ 4 * B 10 * 27 := by
        have := hc.nonneg hL0 10
        exact mul_le_mul_of_nonneg_left (tsum_latWeight_le hL) (by positivity)
    _ = 27 * (2 * Real.pi) ^ 4 * B 10 := by ring

/-- **`(Hχ)` with `L`-free constants** `C_{χ,M} = 27 (2π)^M B_{M+6}`. -/
lemma CellDecay.hChi (hc : CellDecay L B c) (hL : 1 ≤ L) :
    HChi (2 * Real.pi / L) c (fun M => 27 * (2 * Real.pi) ^ M * B (M + 6)) := by
  have hL0 : 0 < L := by linarith
  refine ⟨hc.summable_norm hL, fun M _ ρ hρ => ?_⟩
  have hterm : ∀ n, ρ ^ M * (if ρ < 2 * Real.pi / L * latticeSupNorm n then ‖c n‖ else 0) ≤
      (2 * Real.pi) ^ M * (B (M + 6) * latWeight L n) := by
    intro n
    split_ifs with h
    · have h1 : ρ ≤ 2 * Real.pi * (1 + ‖latFreq L n‖) := by
        have := mul_latticeSupNorm_le hL0 n
        have : 0 ≤ 2 * Real.pi := by positivity
        nlinarith [norm_nonneg (latFreq L n)]
      have h2 : ρ ^ M ≤ (2 * Real.pi) ^ M * (1 + ‖latFreq L n‖) ^ M := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by linarith) h1 M
      have h3 := hc.le_latWeight hL0 M n
      calc ρ ^ M * ‖c n‖ ≤ (2 * Real.pi) ^ M * (1 + ‖latFreq L n‖) ^ M * ‖c n‖ := by gcongr
        _ = (2 * Real.pi) ^ M * ((1 + ‖latFreq L n‖) ^ M * ‖c n‖) := by ring
        _ ≤ (2 * Real.pi) ^ M * (B (M + 6) * latWeight L n) := by gcongr
    · rw [mul_zero]
      have := hc.nonneg hL0 (M + 6)
      have := latWeight_nonneg hL0 n
      positivity
  have hs1 : Summable fun n => (if ρ < 2 * Real.pi / L * latticeSupNorm n then ‖c n‖ else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp)
      (fun n => by split_ifs <;> simp) (hc.summable_norm hL)
  rw [← tsum_mul_left]
  calc ∑' n, ρ ^ M * (if ρ < 2 * Real.pi / L * latticeSupNorm n then ‖c n‖ else 0)
      ≤ ∑' n, (2 * Real.pi) ^ M * (B (M + 6) * latWeight L n) :=
        (hs1.mul_left _).tsum_le_tsum hterm
          (((summable_latWeight hL).mul_left _).mul_left _)
    _ = (2 * Real.pi) ^ M * B (M + 6) * ∑' n, latWeight L n := by
        rw [tsum_mul_left, tsum_mul_left]
        ring
    _ ≤ (2 * Real.pi) ^ M * B (M + 6) * 27 := by
        have := hc.nonneg hL0 (M + 6)
        exact mul_le_mul_of_nonneg_left (tsum_latWeight_le hL) (by positivity)
    _ = 27 * (2 * Real.pi) ^ M * B (M + 6) := by ring

/-- The coefficients of a cell function decay with the decay constants of `𝓕 f`. -/
lemma cellDecay_of_fourier (hL : 0 < L) {f : E3 → ℂ}
    (hf : ∀ y : E3, f y ≠ 0 → ∀ c, |y c| < L / 2) {χ : C(UnitAddTorus (Fin 3), ℂ)}
    (hχ : ∀ t, χ t = f (cellRep L t))
    (hB : ∀ (N : ℕ) (ξ : E3), (1 + ‖ξ‖) ^ N * ‖𝓕 f ξ‖ ≤ B N) :
    CellDecay L B (mFourierCoeff χ) := by
  intro N n
  rw [mFourierCoeff_cell hL hf hχ n, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hp : 0 < (1 + ‖latFreq L n‖) ^ N := by positivity
  have h' : ‖𝓕 f (latFreq L n)‖ ≤ B N / (1 + ‖latFreq L n‖) ^ N := by
    rw [le_div_iff₀ hp, mul_comm]
    exact hB N (latFreq L n)
  calc (L ^ 3)⁻¹ * ‖𝓕 f (latFreq L n)‖ ≤ (L ^ 3)⁻¹ * (B N / (1 + ‖latFreq L n‖) ^ N) := by
        gcongr
    _ = B N * ((L ^ 3)⁻¹ / (1 + ‖latFreq L n‖) ^ N) := by ring

/-- The decay passes to the reflected observable `χ(-·)`. -/
lemma CellDecay.chiRefl {χ : C(UnitAddTorus (Fin 3), ℂ)} (hc : CellDecay L B (mFourierCoeff χ)) :
    CellDecay L B (mFourierCoeff (chiRefl χ)) := by
  intro N n
  rw [mFourierCoeff_chiRefl]
  have h := hc N (-n)
  rwa [latFreq_neg, norm_neg] at h

end Moments

/-! ## Monotonicity of the constants in the moments -/

section Monotone

lemma gLtailMU_mono (sys : CoulombSystem eta ν) {V Hunit : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ Hunit)
    {M M' : ℝ} (h : M ≤ M') : gLtailMU sys V Hunit M ≤ gLtailMU sys V Hunit M' := by
  have h1 := gLtailMU_nonneg sys hV hH (zero_le_one' ℝ)
  unfold gLtailMU at h1 ⊢
  rw [mul_one] at h1
  exact mul_le_mul_of_nonneg_left h h1

private lemma mono_aux_o {Cχ Cχ' D4 D4' F s0 : ℝ} (hF : 0 ≤ F) (h0 : 0 ≤ s0) (hC : Cχ ≤ Cχ')
    (hD : D4 ≤ D4') : 8 * Cχ * F + 8 * D4 * s0 ≤ 8 * Cχ' * F + 8 * D4' * s0 := by
  have h1 := mul_le_mul_of_nonneg_right hC hF
  have h2 := mul_le_mul_of_nonneg_right hD h0
  nlinarith

private lemma mono_aux_W {m Cχ Cχ' D2 D2' Xb s0 : ℝ} (hm : 0 ≤ m) (hXb : 0 ≤ Xb) (h0 : 0 ≤ s0)
    (hC : Cχ ≤ Cχ') (hD : D2 ≤ D2') :
    (2 + 12 * m) * Cχ * Xb + ((3 + 12 * m) * Cχ + 14 * D2) * s0 ≤
      (2 + 12 * m) * Cχ' * Xb + ((3 + 12 * m) * Cχ' + 14 * D2') * s0 := by
  have h1 : (2 + 12 * m) * Cχ ≤ (2 + 12 * m) * Cχ' := mul_le_mul_of_nonneg_left hC (by linarith)
  have h2 : (3 + 12 * m) * Cχ + 14 * D2 ≤ (3 + 12 * m) * Cχ' + 14 * D2' := by
    have := mul_le_mul_of_nonneg_left hC (by linarith : (0 : ℝ) ≤ 3 + 12 * m)
    linarith
  have h3 := mul_le_mul_of_nonneg_right h1 hXb
  have h4 := mul_le_mul_of_nonneg_right h2 h0
  linarith

/-- `Φ_U` is monotone in the moments `C_χ`, `D₂`, `D₄`. -/
lemma gridPhiU_mono (sys : CoulombSystem eta ν) {V Hunit Cχ D2 D4 Cχ' D2' D4' s0 hu hs hv : ℝ}
    (hV : 0 ≤ V) (hH : 0 ≤ Hunit) (hC : Cχ ≤ Cχ') (hD2 : D2 ≤ D2') (hD4 : D4 ≤ D4')
    (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) :
    gridPhiU sys V Hunit Cχ D2 D4 s0 hu hs hv ≤ gridPhiU sys V Hunit Cχ' D2' D4' s0 hu hs hv := by
  have hb := relBU_nonneg sys hV hH
  have hM := sys.one_le_maxMass
  have hcJ := gridFlowConstU_nonneg sys hV
  have hA : 0 ≤ gLAU sys V := by
    unfold gLAU
    have := gLzU_nonneg sys hV
    positivity
  have hσ := sigmaU_nonneg sys hV
  have hM₀ : 0 ≤ sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0)) := by positivity
  have hXb : 0 ≤ 5 / 3 * (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0))) +
      gridFlowConstU sys V * s0 := by positivity
  show flow2 _ _ _ _ _ _ _ ≤ flow2 _ _ _ _ _ _ _
  refine flow2_mono hcJ hA hσ ?_ ?_ (mul_le_mul_of_nonneg_right hC h0)
  · exact mono_aux_o (flow2_nonneg hcJ hA hσ (by positivity) hM₀ h0) h0 hC hD4
  · exact mono_aux_W (by linarith) hXb h0 hC hD2

private lemma mono_aux_A1 {δ τ Cχ Cχ' CO CO' : ℝ} (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hC : Cχ ≤ Cχ')
    (hO : CO ≤ CO') :
    2 * δ * (Cχ * τ + CO * δ) + CO * δ ^ 2 + Cχ * τ ^ 2 ≤
      2 * δ * (Cχ' * τ + CO' * δ) + CO' * δ ^ 2 + Cχ' * τ ^ 2 := by
  have h1 : Cχ * τ + CO * δ ≤ Cχ' * τ + CO' * δ := by
    have := mul_le_mul_of_nonneg_right hC hτ
    have := mul_le_mul_of_nonneg_right hO hδ
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * δ)
  have h3 := mul_le_mul_of_nonneg_right hO (by positivity : (0 : ℝ) ≤ δ ^ 2)
  have h4 := mul_le_mul_of_nonneg_right hC (by positivity : (0 : ℝ) ≤ τ ^ 2)
  linarith

private lemma mono_aux_A2 {e d G G' f b mW mW' T T' M : ℝ} (hed : 0 ≤ e * d) (hfb : 0 ≤ f * b)
    (hf : 0 ≤ f) (hM : 0 ≤ M) (hb : 0 ≤ b) (hG : G ≤ G') (hW : mW ≤ mW') (hT : T ≤ T') :
    2 * (e * d * G + (f * b * mW + f * T * M + 52 * T * b)) ≤
      2 * (e * d * G' + (f * b * mW' + f * T' * M + 52 * T' * b)) := by
  have h1 := mul_le_mul_of_nonneg_left hG hed
  have h2 := mul_le_mul_of_nonneg_left hW hfb
  have h3 : f * T * M ≤ f * T' * M :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hf) hM
  have h4 : 52 * T * b ≤ 52 * T' * b := mul_le_mul_of_nonneg_right (by linarith) hb
  linarith

private lemma mono_aux_mW {m cJ Wo Wo' S S' : ℝ} (hm : 0 ≤ m) (hcJ : 0 ≤ cJ) (hW : Wo ≤ Wo')
    (hS : S ≤ S') : m * (5 / 3 * Wo + cJ * S) ≤ m * (5 / 3 * Wo' + cJ * S') := by
  have := mul_le_mul_of_nonneg_left hS hcJ
  exact mul_le_mul_of_nonneg_left (by linarith) hm

/-- **The constants are monotone in the moments**: `A₁` and `A₂` increase with `C_χ`, `‖O‖`,
`D₂`, `D₄`; `A₃` does not depend on them. -/
lemma gridConstsSharp_gLU_mono (sys : CoulombSystem eta ν)
    {V Hunit Cχ CO D2 D4 Cχ' CO' D2' D4' s0 hu hs hv : ℝ} (hV : 0 ≤ V) (hH : 0 ≤ Hunit)
    (hC : Cχ ≤ Cχ') (hO : CO ≤ CO') (hD2 : D2 ≤ D2') (hD4 : D4 ≤ D4') (h0 : 0 ≤ s0)
    (h1 : 0 ≤ hu) (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).1 ≤
        (gridConstsSharp_gLU sys V Hunit Cχ' CO' D2' D4' s0 hu hs hv).1 ∧
      (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).2.1 ≤
        (gridConstsSharp_gLU sys V Hunit Cχ' CO' D2' D4' s0 hu hs hv).2.1 ∧
      (gridConstsSharp_gLU sys V Hunit Cχ CO D2 D4 s0 hu hs hv).2.2 =
        (gridConstsSharp_gLU sys V Hunit Cχ' CO' D2' D4' s0 hu hs hv).2.2 := by
  have hb := relBU_nonneg sys hV hH
  have hM := sys.one_le_maxMass
  have hcJ := gridFlowConstU_nonneg sys hV
  have hz := gLzU_nonneg sys hV
  have hM₀ : 0 ≤ sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0)) := by positivity
  have hκ : 0 ≤ gLtailMU sys V Hunit
      (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0))) :=
    gLtailMU_nonneg sys hV hH hM₀
  have hXb : 0 ≤ 5 / 3 * (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0))) +
      gridFlowConstU sys V * s0 := by positivity
  have hΦ := gridPhiU_mono sys (hs := hs) (hv := hv) hV hH hC hD2 hD4 h0 h1
  refine ⟨?_, ?_, rfl⟩
  · simp only [gridConstsSharp_gLU]
    exact mono_aux_A1 (by positivity) (by positivity) hC hO
  · simp only [gridConstsSharp_gLU]
    refine mono_aux_A2 (by positivity) (by positivity) (by positivity) hM₀ (by positivity)
      (gLtailMU_mono sys hV hH (mono_aux_mW (by linarith) hcJ
        (mono_aux_W (by linarith) hXb h0 hC hD2) (mul_le_mul_of_nonneg_right hC h0)))
      (mono_aux_mW (by linarith) hcJ (mono_aux_W (by linarith) hXb h0 hC hD2)
        (mul_le_mul_of_nonneg_right hC h0)) ?_
    have : 0 ≤ 1 + gLzU sys V := by linarith
    have := mul_le_mul_of_nonneg_right hΦ this
    have h3072 : (0 : ℝ) ≤ 3072 * sys.maxMass ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left this h3072
    simpa only [mul_assoc] using this

end Monotone

/-! ## The constants at a cell observable -/

section Comparison

/-- The `L`-free moment constants of an observable whose Fourier transform has the decay
constants `B_N = sup_ξ (1 + |ξ|)^N |f̂(ξ)|`: `C_χ, ‖O‖ ≤ 27 B₆`, `g² D₂ ≤ 27 (2π)² B₈`,
`g⁴ D₄ ≤ 27 (2π)⁴ B₁₀`. -/
noncomputable def obsMomC (B : ℕ → ℝ) : ℝ := 27 * B 6

noncomputable def obsMomD2 (B : ℕ → ℝ) : ℝ := 27 * (2 * Real.pi) ^ 2 * B 8

noncomputable def obsMomD4 (B : ℕ → ℝ) : ℝ := 27 * (2 * Real.pi) ^ 4 * B 10

/-- The `L`-free `(Hχ)` constants `C_{χ,M} = 27 (2π)^M B_{M+6}`. -/
noncomputable def obsTailC (B : ℕ → ℝ) (M : ℕ) : ℝ := 27 * (2 * Real.pi) ^ M * B (M + 6)

/-- **The position-space constants at a cell observable are bounded by `L`-free ones**: if the
coefficients of `χ` decay with constants `B`, then `gridConstsPosU` is dominated componentwise by
`gridConstsSharp_gLU` at the moments `obsMomC B`, `obsMomC B`, `obsMomD2 B`, `obsMomD4 B`. -/
theorem gridConstsPosU_le_of_decay (sys : CoulombSystem eta ν) {L V : ℝ} (hL : 1 ≤ L)
    (hV : 0 ≤ V) (a : Fin eta) {χ : C(UnitAddTorus (Fin 3), ℂ)} {B : ℕ → ℝ}
    (hc : CellDecay L B (mFourierCoeff χ)) {s0 hu hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu)
    (h3 : 0 ≤ hv) :
    (gridConstsPosU sys L V a χ s0 hu hv).1 ≤
        (gridConstsSharp_gLU sys V molecularCanonicalUnitHardyConstant (obsMomC B) (obsMomC B)
          (obsMomD2 B) (obsMomD4 B) s0 hu hu hv).1 ∧
      (gridConstsPosU sys L V a χ s0 hu hv).2.1 ≤
        (gridConstsSharp_gLU sys V molecularCanonicalUnitHardyConstant (obsMomC B) (obsMomC B)
          (obsMomD2 B) (obsMomD4 B) s0 hu hu hv).2.1 ∧
      (gridConstsPosU sys L V a χ s0 hu hv).2.2 =
        (gridConstsSharp_gLU sys V molecularCanonicalUnitHardyConstant (obsMomC B) (obsMomC B)
          (obsMomD2 B) (obsMomD4 B) s0 hu hu hv).2.2 := by
  have hr := hc.chiRefl
  have hC : ∑' ν, ‖mFourierCoeff (chiRefl χ) ν‖ ≤ obsMomC B := hr.tsum_norm_le hL
  have hO : ‖convOp (eta := eta) a (mFourierCoeff (chiRefl χ))‖ ≤ obsMomC B :=
    (norm_convOp_le a (hr.summable_norm hL)).trans hC
  exact gridConstsSharp_gLU_mono sys hV molecularCanonicalUnitHardyConstant_nonneg hC hO
    (hr.momTwo_le hL) (hr.momFour_le hL) h0 h1 h1 h3

end Comparison

/-! ## The decay of the Fourier transform -/

section Decay

/-- `B_N(F) = sup_ξ (1 + |ξ|)^N |𝓕F(ξ)|`, finite for a Schwartz function `F`
(`bddAbove_ftDecay`). -/
noncomputable def ftDecay (F : 𝓢(E3, ℂ)) (N : ℕ) : ℝ :=
  ⨆ ξ : E3, (1 + ‖ξ‖) ^ N * ‖𝓕 (F : E3 → ℂ) ξ‖

lemma bddAbove_ftDecay (F : 𝓢(E3, ℂ)) (N : ℕ) :
    BddAbove (Set.range fun ξ : E3 => (1 + ‖ξ‖) ^ N * ‖𝓕 (F : E3 → ℂ) ξ‖) := by
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) (𝓕 F), ?_⟩
  rintro _ ⟨ξ, rfl⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (k := N) (n := 0)
    le_rfl le_rfl (𝓕 F) ξ
  rw [norm_iteratedFDeriv_zero] at h
  exact h

lemma le_ftDecay (F : 𝓢(E3, ℂ)) (N : ℕ) (ξ : E3) :
    (1 + ‖ξ‖) ^ N * ‖𝓕 (F : E3 → ℂ) ξ‖ ≤ ftDecay F N :=
  le_ciSup (bddAbove_ftDecay F N) ξ

lemma ftDecay_nonneg (F : 𝓢(E3, ℂ)) (N : ℕ) : 0 ≤ ftDecay F N :=
  (by positivity : (0 : ℝ) ≤ (1 + ‖(0 : E3)‖) ^ N * ‖𝓕 (F : E3 → ℂ) 0‖).trans (le_ftDecay F N 0)

lemma norm_fourier_le_ftDecay (F : 𝓢(E3, ℂ)) (N : ℕ) (ξ : E3) :
    ‖𝓕 (F : E3 → ℂ) ξ‖ ≤ ftDecay F N / (1 + ‖ξ‖) ^ N := by
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact le_ftDecay F N ξ

end Decay


/-! ## `prop:free-dyn` for a fixed observable -/

section FreeDynFixed

/-- **`prop:free-dyn` with constants depending on the observable only through `f̂`**
(`L ≥ 2π`, `L > 2 R_f`): the statement of `free_dyn_grid_gLU` for a one-particle observable
`0 ≤ f ≤ 1` vanishing outside the ball of radius `R_f`, whose Fourier transform has the decay
constants `B_N ≥ sup_ξ (1 + |ξ|)^N |f̂(ξ)|`. The constants `(A₁, A₂, A₃)` are `gridConstsSharp_gLU`
at the moments `obsMomC B`, `obsMomC B`, `obsMomD2 B`, `obsMomD4 B`, and `C_{χ,5} = obsTailC B 5`:
functions of the system, of `V_θ`, of `(‖φ(0)‖, ‖h₀‖, ‖h₁‖)` and of `B`, so independent of `L`. -/
theorem free_dyn_grid_gLU_decay (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0))
      h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1) (hfm : Measurable f)
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (BB : ℕ → ℝ) (hB : ∀ (N : ℕ) (ξ : E3), (1 + ‖ξ‖) ^ N * ‖𝓕 (fun y => (f y : ℂ)) ξ‖ ≤ BB N)
    (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχf : ∀ x : MolecularPositionTorus eta,
      χ (molecularPositionParticle a x) = (f (particle (cellCoord L x) a) : ℂ))
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let φ₀ := X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let A := gridConstsSharp_gLU sys (tv R θ) molecularCanonicalUnitHardyConstant
        (obsMomC BB) (obsMomC BB) (obsMomD2 BB) (obsMomD4 BB) ‖φ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.commConst * ε * t) +
          ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖φ₀‖ ^ 2) * obsTailC BB 5) * (1 / K) ^ 5 +
            A.2.1 * t * (1 / K) ^ 3) := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  have hL1 : 1 ≤ L := le_trans (by linarith [Real.two_le_pi]) hL2
  have hcell : ∀ s, χ s = (fun y => (f y : ℂ)) (cellRep L s) := fun s => hχf (fun p => s p.2)
  have hsupp : ∀ y : E3, (fun y => (f y : ℂ)) y ≠ 0 → ∀ c, |y c| < L / 2 := by
    intro y hy c
    have hfy : f y ≠ 0 := fun h => hy (by simp [h])
    have := abs_coord_le_norm y c
    have := hfR y hfy
    linarith
  have hdec := cellDecay_of_fourier hL hsupp hcell hB
  have hc : HChi (2 * Real.pi / L) (mFourierCoeff χ) (obsTailC BB) := hdec.hChi hL1
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ :=
    free_dyn_grid_gLU sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hSm hBm hχB hSB hdS hd2S hψd
      hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 a hf0 hf1 hfm χ hχf (obsTailC BB) hc m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro φ₀ A K ψg
  have hb : ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
      ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.commConst * ε * t) +
        (((gridConstsPosU sys L (tv R θ) a χ ‖φ₀‖ ‖h₀‖ ‖h₁‖).1 +
          ((gridConstsPosU sys L (tv R θ) a χ ‖φ₀‖ ‖h₀‖ ‖h₁‖).2.2 * Real.sqrt 3 ^ 5 +
            ‖φ₀‖ ^ 2) * obsTailC BB 5) * (1 / K) ^ 5 +
          (gridConstsPosU sys L (tv R θ) a χ ‖φ₀‖ ‖h₀‖ ‖h₁‖).2.1 * t * (1 / K) ^ 3) := hbound
  obtain ⟨hA1, hA2, hA3⟩ := gridConstsPosU_le_of_decay sys hL1 hθ.tv_nonneg a hdec
    (norm_nonneg φ₀) (norm_nonneg h₀) (norm_nonneg h₁)
  have hA1' : (gridConstsPosU sys L (tv R θ) a χ ‖φ₀‖ ‖h₀‖ ‖h₁‖).1 ≤ A.1 := hA1
  have hA2' : (gridConstsPosU sys L (tv R θ) a χ ‖φ₀‖ ‖h₀‖ ‖h₁‖).2.1 ≤ A.2.1 := hA2
  have hA3' : (gridConstsPosU sys L (tv R θ) a χ ‖φ₀‖ ‖h₀‖ ‖h₁‖).2.2 = A.2.2 := hA3
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  refine hb.trans ?_
  rw [hA3']
  gcongr

/-- **`prop:free-dyn` for a fixed Schwartz observable, with `L`-uniform constants**
(`L ≥ 2π`, `L > 2 R_f`): `free_dyn_grid_gLU_decay` with the decay constants
`B_N = ftDecay F N = sup_ξ (1 + |ξ|)^N |F̂(ξ)|` of a Schwartz function `F = f`. For a fixed `f`
the constants `(A₁, A₂, A₃)` and `C_{χ,5}` depend only on the system, `V_θ`, the data
`(‖φ(0)‖, ‖h₀‖, ‖h₁‖)` and `f`, for all `L ≥ max(2π, 2 R_f)` (`L > 2R_f`). -/
theorem free_dyn_grid_gLU_schwartz (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0))
      h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (χ : C(UnitAddTorus (Fin 3), ℂ))
    (hχf : ∀ x : MolecularPositionTorus eta,
      χ (molecularPositionParticle a x) = (f (particle (cellCoord L x) a) : ℂ))
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let φ₀ := X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let A := gridConstsSharp_gLU sys (tv R θ) molecularCanonicalUnitHardyConstant
        (obsMomC (ftDecay F)) (obsMomC (ftDecay F))
        (obsMomD2 (ftDecay F)) (obsMomD4 (ftDecay F)) ‖φ₀‖ ‖h₀‖ ‖h₀‖ ‖h₁‖
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        ε ^ 2 + (‖ψ t‖ + ‖ψ 0‖) * (X.commConst * ε * t) +
          ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + ‖φ₀‖ ^ 2) * obsTailC (ftDecay F) 5) * (1 / K) ^ 5 +
            A.2.1 * t * (1 / K) ^ 3) := by
  have hfm : Measurable f := by
    have e : f = fun y => (F y).re := by
      funext y
      rw [hFf, Complex.ofReal_re]
    rw [e]
    exact (Complex.continuous_re.comp F.continuous).measurable
  have hFe : (fun y => (f y : ℂ)) = (F : E3 → ℂ) := by
    funext y
    rw [hFf]
  exact free_dyn_grid_gLU_decay sys hL2 hθ hR hR0 hρ hone P hP hpos X hret hSm hBm hχB hSB hdS
    hd2S hψd hHam hgrad ht hε hleak0 hleak1 hdom0 hdom1 a hf0 hf1 hfm hfR hRL (ftDecay F)
    (fun N ξ => by rw [hFe]; exact le_ftDecay F N ξ) χ hχf m hκ hm hK

end FreeDynFixed

end FreeBoundary
