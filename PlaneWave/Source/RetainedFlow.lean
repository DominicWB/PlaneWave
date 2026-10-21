import PlaneWave.Source.TavgQuarterExplicit

/-!
# Flux/source build, block 1b: the retained flow, `lem:retflow`, `lem:quarter-flow`, `prop:src-nc1`

On the Galerkin space `E_n`, with `H' = H_N + ΔH` and the flow `φ(τ) = e^{iH'τ} u`
(`retFlow`, `dev/PlaneWave.Source.TimeAveragedHotContent.lean`):

* `norm_retFlow`, `retFlow_zero`, `retFlow_add`, `continuous_retFlow`, `hasDerivAt_retFlow`:
  `e^{iH'τ}` is a unitary group, continuous, with `∂_τ e^{iH'τ} u = i H' e^{iH'τ} u`;
* `wt_one_le_shifted`: the converse graph bound `‖(1+A) v‖ ≤ C_rev ‖(H' + C_low + 1) v‖`,
  `C_rev = 2 C_low + 6 + C_V²` (the elliptic estimate of `lem:retflow`);
* `retflow` (`lem:retflow`, eq:retflow): `‖(1+A)^s e^{iH'τ} u‖ ≤ C_rev^s C_G^s ‖(1+A)^s u‖` for
  `0 ≤ s ≤ 1`, by Löwner–Heinz in both directions (`dev/PlaneWave.Source.LoewnerHeinz.lean`);
* `quarter_flow` (`lem:quarter-flow`, eq:quarter-flow, for `O = A_p^E`):
  `‖(1+A)^{1/4} e^{iH'τ} A_{p₀}^E v‖² ≤ (C_rev C_G)^{1/2} (1 + η/2)^{1/2} (Cg Ξ)² (1 + 2ηN)` for a
  good `v`, where `Λ ≤ 2^N` (so `N ~ log₂ K`), from the borderline dyadic moment
  `FSDatum.moment_quarter_le_of_tails`;
* `src_nc1` (`prop:src-nc1`, eq:src-nc1): for `y(s) = P W x(s)` with `‖y(s)‖ ≤ a`,
  `|∫₀ᵗ ⟪(1-Q) y(s), e^{iH'(t-s)} u⟫ ds| ≤ a t ((1/t)∫₀ᵗ ‖(1-Q) e^{iH'τ} u‖² dτ)^{1/2}`
  (Cauchy–Schwarz in time); `src_nc1_explicit` combines it with eq:tavg-quarter.
  The infinite-dimensional input `‖P W x‖ ≤ ‖W x‖ ≤ C ‖(1+A)^{1/2} x‖ ≤ C Ξ K^{-3/2}` for
  `x ∈ ran R` is the hypothesis `‖y(s)‖ ≤ a`.
-/

set_option autoImplicit false

open scoped InnerProductSpace Real
open PlaneWaveCertificate MeasureTheory

namespace FSGalerkin

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type*}

/-! ## The retained flow -/

section FlowBasics

variable [Fintype ν] (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) {ΔH : En eta n →ₗ[ℂ] En eta n}
  (hΔsym : ΔH.IsSymmetric)

lemma norm_cexp_I_mul (x τ : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ) * τ)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma inner_retFlow (τ : ℝ) (u : En eta n) (i) :
    ⟪retBasis sys L n hΔsym i, retFlow sys L n hΔsym τ u⟫_ℂ =
      Complex.exp (Complex.I * (retEig sys L n hΔsym i : ℂ) * τ) *
        ⟪retBasis sys L n hΔsym i, u⟫_ℂ :=
  FSSpectral.inner_basis_fc _ _ _ u i

/-- The flow is an isometry. -/
lemma norm_retFlow (τ : ℝ) (u : En eta n) : ‖retFlow sys L n hΔsym τ u‖ = ‖u‖ := by
  have h := FSSpectral.norm_sq_fc (retBasis sys L n hΔsym) (retEig sys L n hΔsym)
    (fun x => Complex.exp (Complex.I * (x : ℂ) * τ)) u
  simp_rw [norm_cexp_I_mul, one_pow, one_mul] at h
  rw [(retBasis sys L n hΔsym).sum_sq_norm_inner_right u] at h
  have h2 : ‖retFlow sys L n hΔsym τ u‖ ^ 2 = ‖u‖ ^ 2 := h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

lemma retFlow_zero (u : En eta n) : retFlow sys L n hΔsym 0 u = u := by
  unfold retFlow
  rw [FSSpectral.fc_congr _ _ (g := fun _ => 1) (fun i => by simp), FSSpectral.fc_one]

lemma retFlow_add (s t : ℝ) (u : En eta n) :
    retFlow sys L n hΔsym (s + t) u = retFlow sys L n hΔsym s (retFlow sys L n hΔsym t u) := by
  unfold retFlow
  rw [FSSpectral.fc_comp]
  refine FSSpectral.fc_congr _ _ (fun i => ?_) u
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma continuous_retFlow (u : En eta n) : Continuous fun τ => retFlow sys L n hΔsym τ u := by
  unfold retFlow FSSpectral.fc
  fun_prop

/-- `∂_τ e^{iH'τ} u = i H' e^{iH'τ} u`. -/
lemma hasDerivAt_retFlow (τ : ℝ) (u : En eta n) :
    HasDerivAt (fun τ => retFlow sys L n hΔsym τ u)
      (Complex.I • Hret sys L n ΔH (retFlow sys L n hΔsym τ u)) τ := by
  have hH := FSSpectral.apply_fc_of_eigen (retBasis sys L n hΔsym) (retEig sys L n hΔsym)
    (Hret sys L n ΔH) (retBasis_eigen sys L n hΔsym)
    (fun x => Complex.exp (Complex.I * (x : ℂ) * τ)) u
  unfold retFlow at hH ⊢
  rw [hH]
  unfold FSSpectral.fc
  rw [Finset.smul_sum]
  have key : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℂ (En eta n)))),
      HasDerivAt (fun τ : ℝ => (Complex.exp (Complex.I * (retEig sys L n hΔsym i : ℂ) * τ) *
          ⟪retBasis sys L n hΔsym i, u⟫_ℂ) • retBasis sys L n hΔsym i)
        (Complex.I • (((retEig sys L n hΔsym i : ℂ) *
          Complex.exp (Complex.I * (retEig sys L n hΔsym i : ℂ) * τ)) *
            ⟪retBasis sys L n hΔsym i, u⟫_ℂ) • retBasis sys L n hΔsym i) τ := by
    intro i _
    have h1 : HasDerivAt (fun τ : ℝ => Complex.I * (retEig sys L n hΔsym i : ℂ) * (τ : ℂ))
        (Complex.I * (retEig sys L n hΔsym i : ℂ)) τ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).const_mul
        (Complex.I * (retEig sys L n hΔsym i : ℂ))
    have hexp := (Complex.hasDerivAt_exp _).comp τ h1
    have h2 := (hexp.mul_const ⟪retBasis sys L n hΔsym i, u⟫_ℂ).smul_const
      (retBasis sys L n hΔsym i)
    refine h2.congr_deriv ?_
    rw [smul_smul]
    congr 1
    ring
  exact HasDerivAt.fun_sum key

end FlowBasics

/-! ## `lem:retflow` -/

section Retflow

variable [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) {n : ℕ}

/-- The converse graph constant `C_rev = 2 C_low + 6 + C_V²`. -/
noncomputable def Crev (sys : CoulombSystem eta ν) (L Hunit CΔ : ℝ) : ℝ :=
  2 * Clow sys L Hunit CΔ + 6 + CVret sys L Hunit CΔ ^ 2

/-- **The converse graph bound** `‖(1+A) v‖ ≤ C_rev ‖(H' + C_low + 1) v‖`. -/
theorem wt_one_le_shifted (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) (v : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ ≤
      Crev sys L Hunit CΔ * ‖FSSpectral.fc (retBasis sys L n hΔsym) (retEig sys L n hΔsym)
        (fun l => ((l + Clow sys L Hunit CΔ + 1 : ℝ) : ℂ)) v‖ := by
  set C₀ := Clow sys L Hunit CΔ with hC₀
  set CV := CVret sys L Hunit CΔ with hCV
  have hC₀0 : 0 ≤ C₀ := (Clow_pos sys Hunit hCΔ).le
  have hCV0 : 0 ≤ CV := CVret_nonneg sys Hunit hCΔ
  set G := FSSpectral.fc (retBasis sys L n hΔsym) (retEig sys L n hΔsym)
    (fun l => ((l + C₀ + 1 : ℝ) : ℂ)) v with hG
  have hlow : ∀ i, -C₀ ≤ retEig sys L n hΔsym i := fun i =>
    eigen_lower (retBasis sys L n hΔsym) (retEig sys L n hΔsym) (Hret sys L n ΔH)
      (retBasis_eigen sys L n hΔsym) (Hret_lower sys Hunit n hL hPeriodic hΔb) i
  -- `‖v‖ ≤ ‖G‖`
  have hvG : ‖v‖ ≤ ‖G‖ := by
    have h2 : ‖v‖ ^ 2 ≤ ‖G‖ ^ 2 := by
      rw [hG, FSSpectral.norm_sq_fc, ← (retBasis sys L n hΔsym).sum_sq_norm_inner_right v]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 : 1 ≤ |retEig sys L n hΔsym i + C₀ + 1| := by
        rw [abs_of_nonneg (by linarith [hlow i])]; linarith [hlow i]
      have : 1 ≤ |retEig sys L n hΔsym i + C₀ + 1| ^ 2 := by nlinarith
      nlinarith [sq_nonneg ‖⟪retBasis sys L n hΔsym i, v⟫_ℂ‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  -- `G = H' v + (C₀ + 1) v`
  have hGeq : G = Hret sys L n ΔH v + ((C₀ + 1 : ℝ) : ℂ) • v := by
    have h1 : (fun l : ℝ => ((l + C₀ + 1 : ℝ) : ℂ)) =
        (fun l : ℝ => (l : ℂ) + ((C₀ + 1 : ℝ) : ℂ)) := by
      funext l; push_cast; ring
    rw [hG, h1, fc_add_fun, fc_const, ← FSSpectral.eigen_fc_id _ _ _ (retBasis_eigen sys L n hΔsym)]
  have hHv : ‖Hret sys L n ΔH v‖ ≤ (C₀ + 2) * ‖G‖ := by
    have : Hret sys L n ΔH v = G - ((C₀ + 1 : ℝ) : ℂ) • v := by rw [hGeq]; abel
    rw [this]
    calc ‖G - ((C₀ + 1 : ℝ) : ℂ) • v‖ ≤ ‖G‖ + ‖((C₀ + 1 : ℝ) : ℂ) • v‖ := norm_sub_le _ _
      _ = ‖G‖ + (C₀ + 1) * ‖v‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ ‖G‖ + (C₀ + 1) * ‖G‖ := by gcongr
      _ = (C₀ + 2) * ‖G‖ := by ring
  -- the elliptic estimate
  set W1 := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ with hW1
  set Wh := ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖ with hWh
  have hV : ‖Vret sys L n ΔH v‖ ≤ CV * Wh := by
    rw [hCV, hWh]
    exact Vret_le_wt sys Hunit n hL hPeriodic hCΔ hΔb v
  have h1 : W1 ≤ ‖v‖ + ‖Hret sys L n ΔH v‖ + CV * Wh := by
    have hkin : FSSpectral.kin (sb eta n) (Asym sys L n) v = Hret sys L n ΔH v - Vret sys L n ΔH v := by
      rw [Hret_eq_kin_add]; abel
    rw [hW1, wt_one_eq, hkin]
    calc _ ≤ ‖v‖ + ‖Hret sys L n ΔH v - Vret sys L n ΔH v‖ := norm_add_le _ _
      _ ≤ ‖v‖ + (‖Hret sys L n ΔH v‖ + ‖Vret sys L n ΔH v‖) := add_le_add le_rfl (norm_sub_le _ _)
      _ ≤ _ := by linarith
  have h2 : Wh ^ 2 ≤ W1 * ‖v‖ := wt_half_sq_le sys L n v
  have h3 : CV * Wh ≤ W1 / 2 + CV ^ 2 / 2 * ‖v‖ := by
    have hsq : (CV * Wh) ^ 2 ≤ (W1 / 2 + CV ^ 2 / 2 * ‖v‖) ^ 2 := by
      have h4 : (CV * Wh) ^ 2 ≤ CV ^ 2 * (W1 * ‖v‖) := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left h2 (sq_nonneg CV)
      nlinarith [sq_nonneg (W1 - CV ^ 2 * ‖v‖), norm_nonneg v]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  unfold Crev
  rw [← hC₀, ← hCV]
  have hG0 := norm_nonneg G
  nlinarith [h1, h3, hHv, hvG, sq_nonneg CV]

/-- **`lem:retflow`**: `‖(1+A)^s e^{iH'τ} u‖ ≤ C_rev^s C_G^s ‖(1+A)^s u‖` for `0 ≤ s ≤ 1`. -/
theorem retflow (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (τ : ℝ) (u : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) s (retFlow sys L n hΔsym τ u)‖ ≤
      Crev sys L Hunit CΔ ^ s * (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ s *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) s u‖ := by
  set C₀ := Clow sys L Hunit CΔ with hC₀
  have hC₀0 : 0 ≤ C₀ := (Clow_pos sys Hunit hCΔ).le
  have hCV0 := CVret_nonneg sys Hunit hCΔ (L := L)
  have hlow : ∀ i, -C₀ ≤ retEig sys L n hΔsym i := fun i =>
    eigen_lower (retBasis sys L n hΔsym) (retEig sys L n hΔsym) (Hret sys L n ΔH)
      (retBasis_eigen sys L n hΔsym) (Hret_lower sys Hunit n hL hPeriodic hΔb) i
  set x : Fin (Module.finrank ℂ (En eta n)) → ℝ := fun i => retEig sys L n hΔsym i + C₀ + 1 with hx
  have hx0 : ∀ i, 0 ≤ x i := fun i => by simp only [hx]; linarith [hlow i]
  have hy0 : ∀ k, 0 ≤ 1 + Asym sys L n k := fun k => by linarith [Asym_nonneg sys L n k]
  have hCrev : 0 ≤ Crev sys L Hunit CΔ := by unfold Crev; positivity
  have hCG : 0 ≤ CVret sys L Hunit CΔ + C₀ + 2 := by linarith
  -- the two graph bounds in `ePow` form
  have hfcx : ∀ v, FluxSourceTest.ePow (retBasis sys L n hΔsym) x 1 v =
      FSSpectral.fc (retBasis sys L n hΔsym) (retEig sys L n hΔsym)
        (fun l => ((l + C₀ + 1 : ℝ) : ℂ)) v := by
    intro v
    unfold FluxSourceTest.ePow FSSpectral.fc
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.rpow_one, smul_smul]
  have hA : ∀ v, ‖FluxSourceTest.ePow (sb eta n) (fun k => 1 + Asym sys L n k) 1 v‖ ≤
      Crev sys L Hunit CΔ * ‖FluxSourceTest.ePow (retBasis sys L n hΔsym) x 1 v‖ := by
    intro v
    rw [FSSpectral.ePow_one_add_eq_wt, hfcx]
    exact wt_one_le_shifted sys Hunit hL hPeriodic hΔsym hCΔ hΔb v
  have hB : ∀ v, ‖FluxSourceTest.ePow (retBasis sys L n hΔsym) x 1 v‖ ≤
      (CVret sys L Hunit CΔ + C₀ + 2) *
        ‖FluxSourceTest.ePow (sb eta n) (fun k => 1 + Asym sys L n k) 1 v‖ := by
    intro v
    rw [FSSpectral.ePow_one_add_eq_wt, hfcx]
    exact graph_le sys Hunit hL hPeriodic hΔsym hCΔ hΔb v
  have hA' := FluxSourceTest.norm_ePow_le_of_norm_ePow_le (sb eta n) (retBasis sys L n hΔsym)
    hy0 hx0 hCrev hA hs
  have hB' := FluxSourceTest.norm_ePow_le_of_norm_ePow_le (retBasis sys L n hΔsym) (sb eta n)
    hx0 hy0 hCG hB hs
  -- the flow preserves the spectral weight
  have hinv : ‖FluxSourceTest.ePow (retBasis sys L n hΔsym) x s (retFlow sys L n hΔsym τ u)‖ =
      ‖FluxSourceTest.ePow (retBasis sys L n hΔsym) x s u‖ := by
    have h2 : ‖FluxSourceTest.ePow (retBasis sys L n hΔsym) x s (retFlow sys L n hΔsym τ u)‖ ^ 2 =
        ‖FluxSourceTest.ePow (retBasis sys L n hΔsym) x s u‖ ^ 2 := by
      rw [FluxSourceTest.norm_sq_ePow, FluxSourceTest.norm_sq_ePow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_retFlow, norm_mul, norm_cexp_I_mul, one_mul]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  calc ‖FSSpectral.wt (sb eta n) (Asym sys L n) s (retFlow sys L n hΔsym τ u)‖
      = ‖FluxSourceTest.ePow (sb eta n) (fun k => 1 + Asym sys L n k) s
          (retFlow sys L n hΔsym τ u)‖ := by rw [FSSpectral.ePow_one_add_eq_wt]
    _ ≤ Crev sys L Hunit CΔ ^ s *
          ‖FluxSourceTest.ePow (retBasis sys L n hΔsym) x s (retFlow sys L n hΔsym τ u)‖ := hA' _
    _ = Crev sys L Hunit CΔ ^ s * ‖FluxSourceTest.ePow (retBasis sys L n hΔsym) x s u‖ := by
        rw [hinv]
    _ ≤ Crev sys L Hunit CΔ ^ s * ((CVret sys L Hunit CΔ + C₀ + 2) ^ s *
          ‖FluxSourceTest.ePow (sb eta n) (fun k => 1 + Asym sys L n k) s u‖) :=
        mul_le_mul_of_nonneg_left (hB' u) (Real.rpow_nonneg hCrev _)
    _ = _ := by rw [FSSpectral.ePow_one_add_eq_wt]; ring

end Retflow

/-! ## `lem:quarter-flow` -/

section Quarter

variable [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) {n : ℕ}

omit [Fintype ν] in
/-- `A ≤ (η/2) R²` when every register momentum is at most `R`. -/
lemma Asym_le_of_kabs_le (hL : 0 < L) (x : Cfg eta n) (R : ℝ) (_hR : 0 ≤ R)
    (hx : ∀ a, finitePlaneWaveKabs (2 * Real.pi / L) n (x a) ≤ R) :
    Asym sys L n x ≤ (eta : ℝ) / 2 * R ^ 2 := by
  unfold Asym massKineticSymbol
  have h1 : ∀ a ∈ Finset.univ, finitePlaneWaveKabs (2 * Real.pi / L) n (x a) ^ 2 / sys.mass a ≤
      R ^ 2 := by
    intro a _
    have hk0 := kabs_nonneg hL (x a)
    have hsq : finitePlaneWaveKabs (2 * Real.pi / L) n (x a) ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ hk0 (hx a) 2
    rw [div_le_iff₀ (sys.mass_pos a)]
    nlinarith [sys.one_le_mass a, sq_nonneg R]
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  nlinarith

omit [Fintype ν] in
/-- On `A ≤ E₀` every register momentum is at most `Λ`. -/
lemma kabs_le_Lam (x : Cfg eta n) (hx : Asym sys L n x ≤ E0 sys L n) (a : Fin eta) :
    finitePlaneWaveKabs (2 * Real.pi / L) n (x a) ≤ Lam sys L n := by
  have hm := fun b => sys.mass_pos b
  have hc := component_sq_le_mass_mul_massKineticSymbol hm
    (finitePlaneWaveKabs (2 * Real.pi / L) n) x a
  have hA : massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) x =
      2 * Asym sys L n x := by unfold Asym; ring
  rw [hA] at hc
  have hma := mass_le_mmax sys a
  have hA0 := Asym_nonneg sys L n x
  have hsq : finitePlaneWaveKabs (2 * Real.pi / L) n (x a) ^ 2 ≤ 2 * mmax sys * E0 sys L n := by
    have h := mul_le_mul hma (show 2 * Asym sys L n x ≤ 2 * E0 sys L n by linarith)
      (by linarith) (by linarith [one_le_mmax sys])
    linarith
  unfold Lam
  exact Real.le_sqrt_of_sq_le hsq

omit [Fintype ν] in
/-- The quarter-power moment of the datum: `‖(1+A)^{1/4} A_{p₀}^E v‖² ≤
(1 + η/2)^{1/2} (Cg Ξ)² (1 + 2ηN)` for a good `v`, when `Λ ≤ 2^N`. -/
theorem wt_quarter_datum_sq_le (hL : 0 < L) {N : ℕ} (hN : Lam sys L n ≤ (2 : ℝ) ^ N)
    (p₀ : Fin eta) {Cg Ξ : ℝ} (v : En eta n) (hv : IsGood sys L Cg Ξ v) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (datum sys L p₀ v)‖ ^ 2 ≤
      (1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * (Cg * Ξ) ^ 2 * (1 + 2 * eta * N) := by
  -- pointwise comparison with the moment
  have hpt : ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (datum sys L p₀ v)‖ ^ 2 ≤
      ∑ p, if Asym sys L n p ≤ E0 sys L n then
        (1 + Asym sys L n p) ^ (1 / 2 : ℝ) * ((1 + Asym sys L n p) ^ 2 * ‖v.ofLp p‖ ^ 2) else 0 := by
    rw [norm_sq_wt]
    refine Finset.sum_le_sum fun p _ => ?_
    have hA0 := Asym_nonneg sys L n p
    have h1 : 0 < 1 + Asym sys L n p := by linarith
    rw [datum_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (datumSym_nonneg sys L p₀ p), mul_pow]
    have hq : ((1 + Asym sys L n p) ^ (1 / 4 : ℝ)) ^ 2 = (1 + Asym sys L n p) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h1.le]; norm_num
    rw [hq]
    have hle := datumSym_le sys L p₀ p
    split_ifs with h
    · rw [if_pos h] at hle
      have hd0 := datumSym_nonneg sys L p₀ p
      have hd : datumSym sys L p₀ p ^ 2 ≤ (1 + Asym sys L n p) ^ 2 :=
        pow_le_pow_left₀ hd0 (by linarith) 2
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd (sq_nonneg _))
        (Real.rpow_nonneg h1.le _)
    · rw [if_neg h] at hle
      have : datumSym sys L p₀ p = 0 := le_antisymm hle (datumSym_nonneg sys L p₀ p)
      rw [this]; simp
  refine hpt.trans ?_
  have hm := sys.mass_pos
  refine FSDatum.moment_quarter_le_of_tails (η := eta) (Asym sys L n)
    (fun a x => finitePlaneWaveKabs (2 * Real.pi / L) n (x a))
    (fun p => (1 + Asym sys L n p) ^ 2 * ‖v.ofLp p‖ ^ 2) (cA := (eta : ℝ) / 2)
    (E₀ := E0 sys L n) (T := Cg * Ξ) N (by positivity) (Asym_nonneg sys L n)
    (fun p => by positivity) (fun x R hR hx => Asym_le_of_kabs_le sys hL x R hR hx)
    (fun x hx a => (kabs_le_Lam sys x hx a).trans hN) ?_ ?_
  · -- `Σ (1+A)² |v|² = Θ(v)² ≤ (Cg Ξ)²`
    have h := hv.1
    have hW : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ ≤ Cg * Ξ := by
      linarith [norm_nonneg v]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hW 2
    rw [norm_sq_wt] at h2
    refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) h2
    rw [Real.rpow_one]
  · -- the weighted tails
    intro a l hl
    have h := (hv.2 a l hl).2
    have hl0 : 0 < l := by linarith
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [norm_sq_wt] at h2
    have heq : (∑ p, ((1 + Asym sys L n p) ^ (1 : ℝ)) ^ 2 * ‖(regTail L a l v).ofLp p‖ ^ 2) =
        ∑ p, if l < finitePlaneWaveKabs (2 * Real.pi / L) n (p a) then
          (1 + Asym sys L n p) ^ 2 * ‖v.ofLp p‖ ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [regTail_apply, Real.rpow_one]
      split_ifs <;> simp
    rw [heq] at h2
    refine h2.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.rpow_natCast (l ^ (-(1 / 2 : ℝ))), ← Real.rpow_mul hl0.le]
    norm_num
    rw [Real.rpow_neg_one]
    ring

/-- **`lem:quarter-flow`** for the truncated datum:
`‖(1+A)^{1/4} e^{iH'τ} A_{p₀}^E v‖ ≤ (C_rev C_G)^{1/4} ((1 + η/2)^{1/2} (Cg Ξ)² (1 + 2ηN))^{1/2}`. -/
theorem quarter_flow (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {N : ℕ} (hN : Lam sys L n ≤ (2 : ℝ) ^ N) (p₀ : Fin eta)
    {Cg Ξ : ℝ} (v : En eta n) (hv : IsGood sys L Cg Ξ v) (τ : ℝ) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4)
        (retFlow sys L n hΔsym τ (datum sys L p₀ v))‖ ≤
      Crev sys L Hunit CΔ ^ (1 / 4 : ℝ) *
        (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ (1 / 4 : ℝ) *
          Real.sqrt ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * (Cg * Ξ) ^ 2 * (1 + 2 * eta * N)) := by
  have h1 := retflow sys Hunit hL hPeriodic hΔsym hCΔ hΔb (s := 1 / 4) ⟨by norm_num, by norm_num⟩ τ
    (datum sys L p₀ v)
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (wt_quarter_datum_sq_le sys hL hN p₀ v hv)
  · have hCrev : 0 ≤ Crev sys L Hunit CΔ := by
      unfold Crev; have := (Clow_pos sys Hunit hCΔ (L := L)).le; positivity
    have hCG : 0 ≤ CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2 := by
      have := CVret_nonneg sys Hunit hCΔ (L := L)
      have := (Clow_pos sys Hunit hCΔ (L := L)).le
      linarith
    exact mul_nonneg (Real.rpow_nonneg hCrev _) (Real.rpow_nonneg hCG _)

end Quarter

/-! ## `prop:src-nc1` -/

section SrcNc1

variable [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) {n : ℕ}

/-- Cauchy–Schwarz in time: `∫₀ᵗ f ≤ (t ∫₀ᵗ f²)^{1/2}` for continuous `f ≥ 0`. -/
lemma integral_le_sqrt_mul (f : ℝ → ℝ) (hf : Continuous f) (_hf0 : ∀ τ, 0 ≤ f τ) {t : ℝ}
    (ht : 0 < t) :
    ∫ τ in (0 : ℝ)..t, f τ ≤ Real.sqrt (t * ∫ τ in (0 : ℝ)..t, f τ ^ 2) := by
  set I := ∫ τ in (0 : ℝ)..t, f τ ^ 2 with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg ht.le fun τ _ => sq_nonneg _
  -- for every `c > 0`, `∫ f ≤ I/(2c) + c t/2`
  have key : ∀ c : ℝ, 0 < c → ∫ τ in (0 : ℝ)..t, f τ ≤ I / (2 * c) + c * t / 2 := by
    intro c hc
    have hpt : ∀ τ ∈ Set.Icc (0 : ℝ) t, f τ ≤ f τ ^ 2 / (2 * c) + c / 2 := by
      intro τ _
      rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (f τ - c)]
    have hc1 : Continuous fun τ => f τ ^ 2 / (2 * c) := (hf.pow 2).div_const _
    have hmono := intervalIntegral.integral_mono_on (μ := volume)
      (g := fun τ => f τ ^ 2 / (2 * c) + c / 2) ht.le
      (hf.intervalIntegrable 0 t) ((hc1.add continuous_const).intervalIntegrable 0 t) hpt
    refine hmono.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_add (hc1.intervalIntegrable 0 t)
      (continuous_const.intervalIntegrable 0 t), intervalIntegral.integral_div,
      intervalIntegral.integral_const, smul_eq_mul, ← hI]
    ring
  rcases hI0.eq_or_lt with h0 | hpos
  · -- `I = 0`: `∫ f ≤ c t/2` for every `c > 0`
    rw [← h0, mul_zero, Real.sqrt_zero]
    by_contra hcon
    push Not at hcon
    set J := ∫ τ in (0 : ℝ)..t, f τ
    have h := key (J / t) (div_pos hcon ht)
    rw [← h0, zero_div, zero_add] at h
    have : J / t * t / 2 = J / 2 := by field_simp
    linarith
  · have hc : 0 < Real.sqrt (I / t) := Real.sqrt_pos.mpr (div_pos hpos ht)
    have h := key (Real.sqrt (I / t)) hc
    refine h.trans (le_of_eq ?_)
    have hsq : Real.sqrt (I / t) ^ 2 = I / t := Real.sq_sqrt (div_pos hpos ht).le
    have hst : Real.sqrt (t * I) = t * Real.sqrt (I / t) := by
      rw [show t * I = t ^ 2 * (I / t) by field_simp, Real.sqrt_mul (sq_nonneg t),
        Real.sqrt_sq ht.le]
    rw [hst]
    field_simp
    rw [hsq]
    field_simp
    ring

/-- `|⟪(1-Q) y, w⟫| ≤ ‖y‖ ‖(1-Q) w‖`. -/
lemma norm_inner_hotProj_le (L l : ℝ) (y w : En eta n) :
    ‖⟪hotProj L l y, w⟫_ℂ‖ ≤ ‖y‖ * ‖hotProj L l w‖ := by
  classical
  have h : ⟪hotProj L l y, w⟫_ℂ = ⟪y, hotProj L l w⟫_ℂ := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold hotProj
    rw [cfgMul_apply, cfgMul_apply]
    split_ifs <;> simp
  rw [h]
  exact norm_inner_le_norm _ _

/-- **`prop:src-nc1`**, Cauchy–Schwarz in time: for continuous `y` with `‖y(s)‖ ≤ a` on `[0, t]`,
`|∫₀ᵗ ⟪(1-Q) y(s), e^{iH'(t-s)} u⟫ ds| ≤ a t ((1/t) ∫₀ᵗ ‖(1-Q) e^{iH'τ} u‖² dτ)^{1/2}`. -/
theorem src_nc1 {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {t : ℝ} (ht : 0 < t)
    (y : ℝ → En eta n) (hy : Continuous y) {a : ℝ} (hya : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖y s‖ ≤ a)
    (l : ℝ) (u : En eta n) :
    ‖∫ s in (0 : ℝ)..t, ⟪hotProj L l (y s), retFlow sys L n hΔsym (t - s) u⟫_ℂ‖ ≤
      a * t * Real.sqrt ((1 / t) *
        ∫ τ in (0 : ℝ)..t, ‖hotProj L l (retFlow sys L n hΔsym τ u)‖ ^ 2) := by
  have hφ := continuous_retFlow sys L n hΔsym u
  have hf : Continuous fun τ => ‖hotProj L l (retFlow sys L n hΔsym τ u)‖ :=
    continuous_norm.comp ((hotProj L l).continuous_of_finiteDimensional.comp hφ)
  have hg : Continuous fun s => ⟪hotProj L l (y s), retFlow sys L n hΔsym (t - s) u⟫_ℂ :=
    ((hotProj L l).continuous_of_finiteDimensional.comp hy).inner
      (hφ.comp (continuous_const.sub continuous_id))
  have ha : 0 ≤ a := (norm_nonneg _).trans (hya 0 ⟨le_rfl, ht.le⟩)
  calc ‖∫ s in (0 : ℝ)..t, ⟪hotProj L l (y s), retFlow sys L n hΔsym (t - s) u⟫_ℂ‖
      ≤ ∫ s in (0 : ℝ)..t, ‖⟪hotProj L l (y s), retFlow sys L n hΔsym (t - s) u⟫_ℂ‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.le
    _ ≤ ∫ s in (0 : ℝ)..t, a * ‖hotProj L l (retFlow sys L n hΔsym (t - s) u)‖ := by
        refine intervalIntegral.integral_mono_on ht.le (hg.norm.intervalIntegrable 0 t)
          ((continuous_const.mul (hf.comp (continuous_const.sub continuous_id))).intervalIntegrable
            0 t) fun s hs => ?_
        exact (norm_inner_hotProj_le L l _ _).trans
          (mul_le_mul_of_nonneg_right (hya s hs) (norm_nonneg _))
    _ = a * ∫ τ in (0 : ℝ)..t, ‖hotProj L l (retFlow sys L n hΔsym τ u)‖ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_sub_left (fun τ => ‖hotProj L l (retFlow sys L n hΔsym τ u)‖)]
        simp
    _ ≤ a * Real.sqrt (t * ∫ τ in (0 : ℝ)..t, ‖hotProj L l (retFlow sys L n hΔsym τ u)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (integral_le_sqrt_mul _ hf (fun τ => norm_nonneg _) ht) ha
    _ = a * t * Real.sqrt ((1 / t) *
          ∫ τ in (0 : ℝ)..t, ‖hotProj L l (retFlow sys L n hΔsym τ u)‖ ^ 2) := by
        rw [mul_assoc]
        congr 1
        rw [show t * ∫ τ in (0 : ℝ)..t, ‖hotProj L l (retFlow sys L n hΔsym τ u)‖ ^ 2 =
            t ^ 2 * ((1 / t) * ∫ τ in (0 : ℝ)..t, ‖hotProj L l (retFlow sys L n hΔsym τ u)‖ ^ 2) by
            field_simp,
          Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]

/-- **eq:src-nc1 with explicit `K`-dependence**:
`|∫₀ᵗ ⟪V_nc^{PR} x(s), φ(t-s)⟫ ds| ≤ a t Cg Ξ √C_tavg K^{s-3} (1 + D_K)^s` for the backward flow
`φ` of the truncated datum of a good state, `‖y(s)‖ = ‖P W x(s)‖ ≤ a`. -/
theorem src_nc1_explicit (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {s : ℝ} (hs : 3 / 2 < s) (hs2 : s ≤ 2)
    (hK : TavgScale sys L Hunit CΔ n) (p₀ : Fin eta) {Cg Ξ t : ℝ} (hCgΞ : 0 ≤ Cg * Ξ)
    (ht : 1 ≤ t) (v : En eta n) (hv : IsGood sys L Cg Ξ v)
    (y : ℝ → En eta n) (hy : Continuous y) {a : ℝ} (hya : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖y s‖ ≤ a) :
    ‖∫ σ in (0 : ℝ)..t, ⟪hotProj L (Kc L n / 4) (y σ),
        retFlow sys L n hΔsym (t - σ) (datum sys L p₀ v)⟫_ℂ‖ ≤
      a * t * (Cg * Ξ) * Real.sqrt (Ctavg sys L Hunit CΔ s) * Kc L n ^ (s - 3) *
        (1 + DK (Kc L n)) ^ s := by
  have ht0 : 0 < t := by linarith
  have h1 := src_nc1 sys (L := L) hΔsym ht0 y hy hya (Kc L n / 4) (datum sys L p₀ v)
  have h2 := tavg_quarter_explicit sys Hunit hL hPeriodic hΔsym hCΔ hΔb hs hs2 hK p₀ hCgΞ ht v hv
  have ha : 0 ≤ a := (norm_nonneg _).trans (hya 0 ⟨le_rfl, ht0.le⟩)
  refine h1.trans ?_
  have hK0 : 0 < Kc L n := by linarith [hK.one_le_K]
  have hD : 0 ≤ 1 + DK (Kc L n) := by linarith [DK_nonneg (Kc L n)]
  have hsq : Real.sqrt (Ctavg sys L Hunit CΔ s * (Cg * Ξ) ^ 2 * Kc L n ^ (2 * s - 6) *
      (1 + DK (Kc L n)) ^ (2 * s)) = (Cg * Ξ) * Real.sqrt (Ctavg sys L Hunit CΔ s) *
        Kc L n ^ (s - 3) * (1 + DK (Kc L n)) ^ s := by
    have e1 : Kc L n ^ (2 * s - 6) = (Kc L n ^ (s - 3)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; congr 1; push_cast; ring
    have e2 : (1 + DK (Kc L n)) ^ (2 * s) = ((1 + DK (Kc L n)) ^ s) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD]; congr 1; push_cast; ring
    rw [e1, e2]
    have hC : 0 ≤ Ctavg sys L Hunit CΔ s := by
      have := Real.sqrt_nonneg (Ctavg sys L Hunit CΔ s)
      by_contra hneg
      push Not at hneg
      -- the time average is nonnegative, so `C_tavg ≥ 0` is forced only through the bound;
      -- we prove it directly from the definition instead
      unfold Ctavg at hneg
      have h1 : 0 ≤ 512 * PA sys L s CΔ := mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun a _ => sq_nonneg _)
      have h2 : 0 ≤ 32768 * PB sys L Hunit s CΔ *
          (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ s * momentConst eta (s / 2 + 1) := by
        have hPB : 0 ≤ PB sys L Hunit s CΔ := Finset.sum_nonneg fun a _ => by
          have := latConst_pos sys a (L := L)
          have : 0 ≤ 2 * (1 + Clow sys L Hunit CΔ + CVret sys L Hunit CΔ ^ 2 / 2) := by
            have := (Clow_pos sys Hunit hCΔ (L := L)).le
            positivity
          positivity
        have hCG : 0 ≤ CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2 := by
          have := CVret_nonneg sys Hunit hCΔ (L := L)
          have := (Clow_pos sys Hunit hCΔ (L := L)).le
          linarith
        have := momentConst_nonneg eta (r := s / 2 + 1) (by linarith)
        have := Real.rpow_nonneg hCG s
        positivity
      have h3 : 0 ≤ CVret sys L Hunit CΔ ^ 2 * (4096 * mmax sys) ^ 2 * momentConst eta (1 / 2 + 1) := by
        have := momentConst_nonneg eta (r := 1 / 2 + 1) (by norm_num)
        positivity
      have := Real.sqrt_nonneg π
      have := Real.sqrt_nonneg (2 * π)
      have he := Real.exp_pos 1
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) he.le)
        (add_nonneg (mul_nonneg (Real.sqrt_nonneg π) (add_nonneg (add_nonneg h1 h2) h3))
          (Real.sqrt_nonneg (2 * π)))]
    rw [show Ctavg sys L Hunit CΔ s * (Cg * Ξ) ^ 2 * (Kc L n ^ (s - 3)) ^ 2 *
        ((1 + DK (Kc L n)) ^ s) ^ 2 =
        Ctavg sys L Hunit CΔ s * ((Cg * Ξ) * Kc L n ^ (s - 3) * (1 + DK (Kc L n)) ^ s) ^ 2 by ring,
      Real.sqrt_mul hC, Real.sqrt_sq (by
        have := Real.rpow_nonneg hK0.le (s - 3)
        have := Real.rpow_nonneg hD s
        positivity)]
    ring
  calc a * t * Real.sqrt ((1 / t) * ∫ τ in (0 : ℝ)..t,
        ‖hotProj L (Kc L n / 4) (retFlow sys L n hΔsym τ (datum sys L p₀ v))‖ ^ 2)
      ≤ a * t * Real.sqrt (Ctavg sys L Hunit CΔ s * (Cg * Ξ) ^ 2 * Kc L n ^ (2 * s - 6) *
          (1 + DK (Kc L n)) ^ (2 * s)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (mul_nonneg ha ht0.le)
    _ = _ := by rw [hsq]; ring

end SrcNc1

end FSGalerkin
