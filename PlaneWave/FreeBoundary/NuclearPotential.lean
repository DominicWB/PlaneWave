import PlaneWave.FreeBoundary.FreeEnergyEndpoint

/-!
# Clamped nuclei, part 1: the nuclear terms

The domain theorem of `prop:free-dyn` with clamped nuclei (plan: `dev/clamped_plan.md`). The
free-space interaction is the pair interaction plus the nuclear terms
`Σ_{i,ℓ} q_i Z_ℓ / |x_i - P_ℓ|`; for `u` with a weak gradient the nuclear Hardy functions
`u/|x_i - P_ℓ|` are in `L²` (`hardy_nuc`), so `V u` is a combination of Hardy functions. A cutoff
is flat near the nuclei if `∇_i χ = 0` wherever `|x_i - P_ℓ| < δ`; then the nuclear part of the
double commutator `[V, [K, χ]]` is a bounded function.

* `nucPot`, `freePot_eq_pair_nuc`: the decomposition of the interaction;
* `nucL2`, `nucL2_ae`, **`hasL2PointwisePotential_pair_nucL2`**: `V u = pairL2 Y + nucL2 Yn` for
  any system;
* `IsFlatNear`, `nucW`, **`abs_nucW_le`**: the nuclear weight
  `Σ_{i,ℓ,c} m_i⁻¹ ∂_{(i,c)}χ · q_i Z_ℓ (x_i - P_ℓ)_c/|x_i - P_ℓ|³` is at most
  `Σ_{i,ℓ} m_i⁻¹ |q_i Z_ℓ| Σ_c |∂_{(i,c)}χ| / δ²` for a cutoff flat near the nuclei.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The nuclear interaction -/

/-- The nuclear interaction `Σ_{i,ℓ} q_i Z_ℓ / |x_i - P_ℓ|`. -/
def nucPot (q : Fin eta → ℝ) (Z : ν → ℝ) (P : ν → E3) (r : Rcfg eta) : ℝ :=
  ∑ i : Fin eta, ∑ l : ν, q i * Z l * ‖particle r i - P l‖⁻¹

lemma freePot_eq_pair_nuc (sys : CoulombSystem eta ν) (P : ν → E3) (r : Rcfg eta) :
    freePot sys P r = pairPot sys.charge r + nucPot sys.charge sys.nuclei.charge P r := by
  rw [freePot_eq]
  unfold pairPot nucPot pinv
  simp only [sub_zero, particleCLM_apply]

/-- `Σ_{i,ℓ} q_i Z_ℓ F_{iℓ}`, for the nuclear Hardy functions `F_{iℓ} = f/|x_i - P_ℓ|`. -/
def nucL2 (q : Fin eta → ℝ) (Z : ν → ℝ) (F : Fin eta → ν → FreeL2 eta) : FreeL2 eta :=
  ∑ i : Fin eta, ∑ l : ν, ((q i * Z l : ℝ) : ℂ) • F i l

lemma nucL2_ae (q : Fin eta → ℝ) (Z : ν → ℝ) (P : ν → E3) {f : FreeL2 eta}
    {F : Fin eta → ν → FreeL2 eta}
    (hF : ∀ i l, ∀ᵐ r, F i l r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * f r) :
    ∀ᵐ r, nucL2 q Z F r = (nucPot q Z P r : ℂ) * f r := by
  have hs := Lp.coeFn_finsetSum (Finset.univ : Finset (Fin eta))
    (fun i => ∑ l : ν, ((q i * Z l : ℝ) : ℂ) • F i l)
  have hs' : ∀ᵐ r, ∀ i : Fin eta, (∑ l : ν, ((q i * Z l : ℝ) : ℂ) • F i l) r =
      ∑ l : ν, ((q i * Z l : ℝ) : ℂ) * F i l r := by
    refine ae_all_iff.mpr fun i => ?_
    have h1 := Lp.coeFn_finsetSum (Finset.univ : Finset ν) (fun l => ((q i * Z l : ℝ) : ℂ) • F i l)
    have h2 : ∀ᵐ r, ∀ l : ν, (((q i * Z l : ℝ) : ℂ) • F i l) r = ((q i * Z l : ℝ) : ℂ) * F i l r :=
      ae_all_iff.mpr fun l => (Lp.coeFn_smul _ (F i l)).mono fun r hr => by rw [hr]; rfl
    filter_upwards [h1, h2] with r h1 h2
    rw [h1, Finset.sum_apply]
    exact Finset.sum_congr rfl fun l _ => h2 l
  have hall : ∀ᵐ r, ∀ i l, F i l r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * f r :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun l => hF i l
  filter_upwards [hs, hs', hall] with r h1 h2 h3
  unfold nucL2
  rw [h1, Finset.sum_apply]
  simp only [h2, h3]
  unfold nucPot
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **`V u` from the Hardy functions, for any system**: `V u = pairL2 Y + nucL2 Yn`. -/
lemma hasL2PointwisePotential_pair_nucL2 (sys : CoulombSystem eta ν) (P : ν → E3)
    {f : FreeL2 eta} {F : FiniteElectronPair eta → FreeL2 eta}
    (hF : ∀ p, ∀ᵐ r, F p r = (pinv p r : ℂ) * f r) {Fn : Fin eta → ν → FreeL2 eta}
    (hFn : ∀ i l, ∀ᵐ r, Fn i l r = ((‖particle r i - P l‖⁻¹ : ℝ) : ℂ) * f r) :
    HasL2PointwisePotential volume (fun r => (freePot sys P r : ℂ)) f
      (pairL2 sys.charge F + nucL2 sys.charge sys.nuclei.charge Fn) := by
  filter_upwards [pairL2_ae sys.charge hF, nucL2_ae sys.charge sys.nuclei.charge P hFn,
    Lp.coeFn_add (pairL2 sys.charge F) (nucL2 sys.charge sys.nuclei.charge Fn)] with r h1 h2 h3
  rw [h3, Pi.add_apply, h1, h2, freePot_eq_pair_nuc]
  push_cast
  ring

/-! ## Cutoffs flat near the nuclei -/

/-- `χ` is flat near the nuclei: `∂_{(i,c)} χ = 0` wherever `|x_i - P_ℓ| < δ` for some `ℓ`. -/
def IsFlatNear (χ : Rcfg eta → ℝ) (P : ν → E3) (δ : ℝ) : Prop :=
  ∀ r i l, ‖particle r i - P l‖ < δ → ∀ c : Fin 3, dirD (i, c) χ r = 0

/-- The nuclear part of `-Σ_a m_a⁻¹ ∂_aχ ∂_aV`:
`Σ_{i,ℓ,c} m_i⁻¹ ∂_{(i,c)}χ · q_i Z_ℓ (x_i - P_ℓ)_c / |x_i - P_ℓ|³`. -/
def nucW (m q : Fin eta → ℝ) (Z : ν → ℝ) (P : ν → E3) (χ : Rcfg eta → ℝ) (r : Rcfg eta) : ℝ :=
  ∑ i : Fin eta, ∑ l : ν, ∑ c : Fin 3, (m i)⁻¹ * dirD (i, c) χ r *
    (q i * Z l * (particle r i - P l) c / ‖particle r i - P l‖ ^ 3)

/-- **The nuclear weight is bounded** for a cutoff flat near the nuclei. -/
theorem abs_nucW_le {m q : Fin eta → ℝ} (hm : ∀ i, 0 < m i) (Z : ν → ℝ) (P : ν → E3)
    {χ : Rcfg eta → ℝ} {δ : ℝ} (hδ : 0 < δ) (hflat : IsFlatNear χ P δ) (r : Rcfg eta) :
    |nucW m q Z P χ r| ≤ ∑ i : Fin eta, ∑ l : ν, ∑ c : Fin 3,
      (m i)⁻¹ * |q i * Z l| * |dirD (i, c) χ r| / δ ^ 2 := by
  unfold nucW
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  have hmi : 0 < (m i)⁻¹ := inv_pos.mpr (hm i)
  by_cases hnear : ‖particle r i - P l‖ < δ
  · rw [hflat r i l hnear c]
    simp
  · have hnear := not_lt.mp hnear
    set y := particle r i - P l with hydef
    have hy : 0 < ‖y‖ := lt_of_lt_of_le hδ hnear
    have hc : |y c| ≤ ‖y‖ := by
      have h2 : (y c) ^ 2 ≤ ‖y‖ ^ 2 := by
        rw [norm_sq_E3]
        exact Finset.single_le_sum (f := fun d : Fin 3 => (y d) ^ 2) (fun d _ => sq_nonneg _)
          (Finset.mem_univ c)
      exact (sq_le_sq.mp h2).trans (le_of_eq (abs_of_nonneg (norm_nonneg _)))
    have key : |q i * Z l * y c / ‖y‖ ^ 3| ≤ |q i * Z l| / δ ^ 2 := by
      rw [abs_div, abs_of_pos (pow_pos hy 3), abs_mul,
        div_le_div_iff₀ (pow_pos hy 3) (by positivity)]
      have h1 : |y c| * δ ^ 2 ≤ ‖y‖ ^ 3 := by
        calc |y c| * δ ^ 2 ≤ ‖y‖ * ‖y‖ ^ 2 :=
              mul_le_mul hc (pow_le_pow_left₀ hδ.le hnear 2) (by positivity) (norm_nonneg _)
          _ = ‖y‖ ^ 3 := by ring
      calc |q i * Z l| * |y c| * δ ^ 2 = |q i * Z l| * (|y c| * δ ^ 2) := by ring
        _ ≤ |q i * Z l| * ‖y‖ ^ 3 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    calc |(m i)⁻¹ * dirD (i, c) χ r * (q i * Z l * y c / ‖y‖ ^ 3)|
        = (m i)⁻¹ * |dirD (i, c) χ r| * |q i * Z l * y c / ‖y‖ ^ 3| := by
          rw [abs_mul, abs_mul, abs_of_pos hmi]
      _ ≤ (m i)⁻¹ * |dirD (i, c) χ r| * (|q i * Z l| / δ ^ 2) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = (m i)⁻¹ * |q i * Z l| * |dirD (i, c) χ r| / δ ^ 2 := by ring

end

end FreeBoundary
