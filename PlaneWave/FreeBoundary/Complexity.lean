import PlaneWave.FreeBoundary.ProductLocalisation

/-!
# `prop:free`: the basis-size complexity `N = O(ε⁻¹ log³(1/ε))`

The last sentence of `prop:free`: with the two-sided bound
`|E_{N,L} + C₀ - E_∞| ≤ C' e^{-γL} + C K^{-3}` (eq:free-energy, `L`-uniform `C`), the choice
`L ≈ γ⁻¹ log(1/ε)`, `K ≈ ε^{-1/3}` gives total error `ε` with
`N = Θ((KL)³) = O(ε⁻¹ log³(1/ε))` grid points per particle.

* `complexity_of_rate`: the arithmetic, for any family of approximations obeying such a rate
  (`L = L₀ + (log(2C' + 2) + log(1/ε))/γ`, `m = ⌈L (K₀ + ((2C + 2)/ε)^{1/3})/(2π)⌉ + m₀`,
  `N = (4m + 1)³`, the grid points per particle of the register of radius `2m`);
* `abs_zeroModeShift_re_le`: `|C₀| ≤ Q π/(2L)` (`Q = Σ|q_a q_b| + Σ|q_a| Z_ℓ`), so that one
  energy budget serves all large cells;
* `sysAt`: the system with the nuclei of the free-space molecule (positions `P_ℓ`) on the torus of
  cell size `L` (positions `-P_ℓ/L`);
* **`free_grid_complexity_prod`**: for the molecule in cells of size `L ≥ L₀ ≥ 2π`, with the
  hypotheses of `free_grid_exponentialU_prod` for every such `L` (profiles of fixed total
  variation; Agmon decay of the free ground state at every radius; assumption (A) in the product
  geometry), there is `D` such that for every `0 < ε ≤ 1/2` some cell size `L ≥ L₀` and register
  radius `2m` with `(4m + 1)³ ≤ D ε⁻¹ log³(1/ε)` give `|E_{N,L} + C₀ - E_∞| ≤ ε`.
-/

set_option autoImplicit false

open MeasureTheory Filter Set PlaneWaveCertificate
open scoped InnerProductSpace ComplexConjugate BigOperators Topology

namespace FreeBoundary

noncomputable section

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15
  molecularTorusFiniteMeasureFB15

variable {eta : ℕ}

/-! ## The arithmetic -/

lemma rate_aux_one {C' ε : ℝ} (hC' : 0 ≤ C') (hε : 0 < ε) : C' * (ε / (2 * C' + 2)) ≤ ε / 2 := by
  rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

lemma rate_aux_two {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) : C * ε / (2 * C + 2) ≤ ε / 2 := by
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

lemma rate_aux_exp {C' L₀ γ L a lam ε : ℝ} (hC' : 0 ≤ C') (hL₀ : 0 ≤ L₀) (hγ : 0 < γ)
    (hε : 0 < ε) (ha : a = Real.log (2 * C' + 2)) (hlam : lam = Real.log (1 / ε))
    (hL : L = L₀ + (a + lam) / γ) : C' * Real.exp (-(γ * L)) ≤ ε / 2 := by
  have hγL : a + lam ≤ γ * L := by
    rw [hL, mul_add, mul_div_cancel₀ _ hγ.ne']
    have : 0 ≤ γ * L₀ := mul_nonneg hγ.le hL₀
    linarith
  have hexp : Real.exp (-(γ * L)) ≤ Real.exp (-(a + lam)) := Real.exp_le_exp.mpr (by linarith)
  have hval : Real.exp (-(a + lam)) = ε / (2 * C' + 2) := by
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, ha, hlam,
      Real.exp_log (by linarith), Real.exp_log (by positivity)]
    field_simp
  rw [hval] at hexp
  exact (mul_le_mul_of_nonneg_left hexp hC').trans (rate_aux_one hC' hε)

lemma rate_aux_L {L₀ γ L a lam : ℝ} (hL₀ : 0 ≤ L₀) (hγ : 0 < γ) (ha : 0 ≤ a)
    (hlam2 : Real.log 2 ≤ lam) (hL : L = L₀ + (a + lam) / γ) :
    L ≤ ((L₀ + a / γ) / Real.log 2 + 1 / γ) * lam := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0 ≤ (L₀ + a / γ) / Real.log 2 := by positivity
  have h1 : L₀ + a / γ ≤ (L₀ + a / γ) / Real.log 2 * lam := by
    calc L₀ + a / γ = (L₀ + a / γ) / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ (L₀ + a / γ) / Real.log 2 * lam := mul_le_mul_of_nonneg_left hlam2 h0
  have e1 : L = L₀ + a / γ + lam / γ := by rw [hL]; ring
  have e2 : ((L₀ + a / γ) / Real.log 2 + 1 / γ) * lam =
      (L₀ + a / γ) / Real.log 2 * lam + lam / γ := by ring
  rw [e1, e2]
  linarith

lemma rate_aux_cbrt {y : ℝ} (hy : 0 ≤ y) : (y ^ ((1 : ℝ) / 3)) ^ 3 = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

/-- **Complexity from a two-sided rate.** If the approximations `E_g(L, m)` (register radius `2m`,
`K = 2πm/L`) obey `|E_g + C₀(L) - E_∞| ≤ C' e^{-γL} + C K^{-3}` for `L ≥ L₀`, `m ≥ m₀` and
`K ≥ K₀`, then there is `D` such that for every `0 < ε ≤ 1/2` some `L ≥ L₀` and `m` with
`(4m + 1)³ ≤ D ε⁻¹ log³(1/ε)` give error at most `ε`. -/
theorem complexity_of_rate {Q : ℝ → ℕ → ℝ → Prop} {C0 : ℝ → ℝ} {Einf L₀ C' γ Cg K₀ : ℝ}
    {m₀ : ℕ} (hL₀ : 0 ≤ L₀) (hγ : 0 < γ) (hC' : 0 ≤ C')
    (hrate : ∀ L, L₀ ≤ L → 0 < L → ∀ m : ℕ, m₀ ≤ m → K₀ ≤ (2 * Real.pi / L) * m →
      ∃ Eg, Q L m Eg ∧
        |Eg + C0 L - Einf| ≤ C' * Real.exp (-(γ * L)) + Cg / ((2 * Real.pi / L) * m) ^ 3) :
    ∃ D : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ L, L₀ ≤ L ∧ ∃ m : ℕ,
      ((4 * m + 1 : ℕ) : ℝ) ^ 3 ≤ D / ε * Real.log (1 / ε) ^ 3 ∧
      ∃ Eg, Q L m Eg ∧ |Eg + C0 L - Einf| ≤ ε := by
  obtain ⟨Cg', hCg'0, hCgle⟩ : ∃ Cg' : ℝ, 0 ≤ Cg' ∧ Cg ≤ Cg' :=
    ⟨max Cg 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨K0', hK0'0, hK0le⟩ : ∃ K0' : ℝ, 0 ≤ K0' ∧ K₀ ≤ K0' :=
    ⟨max K₀ 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = Real.log (2 * C' + 2) := ⟨_, rfl⟩
  have ha : 0 < a := by rw [ha_def]; exact Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = (L₀ + a / γ) / Real.log 2 + 1 / γ := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; positivity
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = (2 * Cg' + 2) ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by rw [hb_def]; exact Real.rpow_nonneg (by linarith) _
  have hb3 : b ^ 3 = 2 * Cg' + 2 := by rw [hb_def]; exact rate_aux_cbrt (by linarith)
  obtain ⟨c₄, hc₄⟩ : ∃ c₄ : ℝ, c₄ = c₁ * K0' + c₁ * b + (4 * m₀ + 5) / Real.log 2 := ⟨_, rfl⟩
  have hc₄0 : 0 ≤ c₄ := by rw [hc₄]; positivity
  refine ⟨c₄ ^ 3, fun ε hε hε2 => ?_⟩
  -- the scales
  have hinv : 2 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = Real.log (1 / ε) := ⟨_, rfl⟩
  have hlam2 : Real.log 2 ≤ lam := by rw [hlam]; exact Real.log_le_log (by norm_num) hinv
  have hlam0 : 0 < lam := lt_of_lt_of_le hlog2 hlam2
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = L₀ + (a + lam) / γ := ⟨_, rfl⟩
  have hLpos : 0 < L := by rw [hL_def]; positivity
  have hLL₀ : L₀ ≤ L := by
    have : 0 ≤ (a + lam) / γ := by positivity
    rw [hL_def]
    linarith
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (1 / ε) ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs_def]; exact Real.one_le_rpow (by linarith) (by norm_num)
  have hs0 : 0 ≤ s := by linarith
  have hs3 : s ^ 3 = 1 / ε := by rw [hs_def]; exact rate_aux_cbrt (by positivity)
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = b * s := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht_def]; positivity
  have ht3 : t ^ 3 = (2 * Cg' + 2) / ε := by
    rw [ht_def, mul_pow, hb3, hs3]
    ring
  have htpos : 0 < t := by
    have h3 : 0 < t ^ 3 := by rw [ht3]; positivity
    rcases ht0.lt_or_eq with h | h
    · exact h
    · rw [← h] at h3
      norm_num at h3
  obtain ⟨x, hx_def⟩ : ∃ x : ℝ, x = L * (K0' + t) / (2 * Real.pi) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx_def]; positivity
  obtain ⟨m, hm_def⟩ : ∃ m : ℕ, m = ⌈x⌉₊ + m₀ := ⟨_, rfl⟩
  have hmm₀ : m₀ ≤ m := by rw [hm_def]; exact Nat.le_add_left _ _
  have hxm : x ≤ (m : ℝ) := by
    have h1 := Nat.le_ceil x
    have h2 : ((⌈x⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show ⌈x⌉₊ ≤ m by omega)
    linarith
  have hmx : (m : ℝ) ≤ x + 1 + m₀ := by
    have h1 := Nat.ceil_lt_add_one hx0
    have h2 : (m : ℝ) = ((⌈x⌉₊ : ℕ) : ℝ) + m₀ := by rw [hm_def]; push_cast; ring
    linarith
  -- the momentum cutoff
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = (2 * Real.pi / L) * m := ⟨_, rfl⟩
  have hKx : K0' + t ≤ K := by
    have h1 : (2 * Real.pi / L) * x = K0' + t := by
      rw [hx_def]
      field_simp
    have h2 : (2 * Real.pi / L) * x ≤ (2 * Real.pi / L) * m :=
      mul_le_mul_of_nonneg_left hxm (by positivity)
    rw [hK_def]
    linarith
  have hKK₀ : K₀ ≤ (2 * Real.pi / L) * m := by rw [← hK_def]; linarith
  have hKt : t ≤ K := by linarith
  obtain ⟨Eg, hQ, herr⟩ := hrate L hLL₀ hLpos m hmm₀ hKK₀
  rw [← hK_def] at herr
  refine ⟨L, hLL₀, m, ?_, Eg, hQ, ?_⟩
  · -- the size of the register
    have hLle : L ≤ c₁ * lam := by
      rw [hc₁]
      exact rate_aux_L hL₀ hγ ha.le hlam2 hL_def
    have h4x : 4 * x ≤ L * (K0' + t) := by
      have e : 4 * x = (2 / Real.pi) * (L * (K0' + t)) := by
        rw [hx_def]
        field_simp
        ring
      have hpi : 2 / Real.pi ≤ 1 := by
        rw [div_le_one Real.pi_pos]
        exact Real.two_le_pi
      rw [e]
      exact mul_le_of_le_one_left (by positivity) hpi
    have h4m : 4 * (m : ℝ) + 1 ≤ L * K0' + L * t + (4 * (m₀ : ℝ) + 5) := by
      have e : L * (K0' + t) = L * K0' + L * t := by ring
      linarith
    have hA1 : L * K0' ≤ c₁ * K0' * lam * s := by
      calc L * K0' ≤ c₁ * lam * K0' := mul_le_mul_of_nonneg_right hLle hK0'0
        _ ≤ c₁ * lam * K0' * s := le_mul_of_one_le_right (by positivity) hs1
        _ = c₁ * K0' * lam * s := by ring
    have hA2 : L * t ≤ c₁ * b * lam * s := by
      calc L * t ≤ c₁ * lam * t := mul_le_mul_of_nonneg_right hLle ht0
        _ = c₁ * b * lam * s := by rw [ht_def]; ring
    have hA3 : (4 * (m₀ : ℝ) + 5) ≤ (4 * m₀ + 5) / Real.log 2 * lam * s := by
      have h0 : 0 ≤ (4 * (m₀ : ℝ) + 5) / Real.log 2 := by positivity
      calc (4 * (m₀ : ℝ) + 5) = (4 * m₀ + 5) / Real.log 2 * Real.log 2 := by field_simp
        _ ≤ (4 * m₀ + 5) / Real.log 2 * lam := mul_le_mul_of_nonneg_left hlam2 h0
        _ ≤ (4 * m₀ + 5) / Real.log 2 * lam * s :=
            le_mul_of_one_le_right (by positivity) hs1
    have e : c₄ * lam * s = c₁ * K0' * lam * s + c₁ * b * lam * s +
        (4 * m₀ + 5) / Real.log 2 * lam * s := by rw [hc₄]; ring
    have hm4 : ((4 * m + 1 : ℕ) : ℝ) ≤ c₄ * lam * s := by
      push_cast
      linarith
    have h0 : (0 : ℝ) ≤ ((4 * m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 := pow_le_pow_left₀ h0 hm4 3
    have e3 : (c₄ * lam * s) ^ 3 = c₄ ^ 3 / ε * Real.log (1 / ε) ^ 3 := by
      rw [mul_pow, mul_pow, hs3, ← hlam]
      ring
    rw [e3] at h3
    exact h3
  · -- the error
    have h1 : C' * Real.exp (-(γ * L)) ≤ ε / 2 :=
      rate_aux_exp hC' hL₀ hγ hε ha_def hlam hL_def
    have h2 : Cg / K ^ 3 ≤ ε / 2 := by
      have hK0 : 0 < K := lt_of_lt_of_le htpos hKt
      have hK3 : t ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ ht0 hKt 3
      calc Cg / K ^ 3 ≤ Cg' / K ^ 3 := div_le_div_of_nonneg_right hCgle (by positivity)
        _ ≤ Cg' / t ^ 3 := div_le_div_of_nonneg_left hCg'0 (by positivity) hK3
        _ = Cg' * ε / (2 * Cg' + 2) := by
            rw [ht3]
            field_simp
        _ ≤ ε / 2 := rate_aux_two hCg'0 hε
    calc |Eg + C0 L - Einf| ≤ C' * Real.exp (-(γ * L)) + Cg / K ^ 3 := herr
      _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
      _ = ε := by ring

/-! ## The zero mode -/

/-- The charge weight `Q = Σ_{a<b} |q_a q_b| + Σ_a |q_a| Σ_ℓ Z_ℓ` of the zero mode. -/
def zeroWeight {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) : ℝ :=
  (∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2|) +
    ∑ i : Fin eta, |sys.charge i| * ∑ ell : ν, sys.nuclei.charge ell

lemma zeroWeight_nonneg {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) :
    0 ≤ zeroWeight sys := by
  unfold zeroWeight
  have h : ∀ i : Fin eta, 0 ≤ |sys.charge i| * ∑ ell : ν, sys.nuclei.charge ell := fun i =>
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun ell _ => sys.nuclei.charge_nonneg ell)
  exact add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.sum_nonneg fun i _ => h i)

/-- **The zero-mode shift is `O(1/L)`**: `|C₀| ≤ Q π/(2L)` for a profile of range `R ≤ L/2`. -/
lemma abs_zeroModeShift_re_le {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L R : ℝ}
    {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ) (hR : R ≤ L / 2) :
    |(zeroModeShift sys L θ).re| ≤ zeroWeight sys * (Real.pi / (2 * L)) := by
  set g := ghat L θ (fun _ => 0) with hg_def
  have hg : ‖g‖ ≤ Real.pi / (2 * L) := by
    have h1 := ghat_zero_le hL hθ
    have hR0 : 0 ≤ R := hθ.pos.le
    calc ‖g‖ ≤ 2 * Real.pi * R ^ 2 / L ^ 3 := h1
      _ ≤ 2 * Real.pi * (L / 2) ^ 2 / L ^ 3 := by gcongr
      _ = Real.pi / (2 * L) := by
          field_simp
  have e1 : ‖∑ pair : FiniteElectronPair eta,
      ((sys.charge pair.1.1 * sys.charge pair.1.2 : ℝ) : ℂ) * g‖ ≤
      (∑ pair : FiniteElectronPair eta, |sys.charge pair.1.1 * sys.charge pair.1.2|) * ‖g‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun pair _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have e2 : ‖∑ i : Fin eta, ((sys.charge i : ℝ) : ℂ) *
      ∑ ell : ν, (sys.nuclei.charge ell : ℂ) * g‖ ≤
      (∑ i : Fin eta, |sys.charge i| * ∑ ell : ν, sys.nuclei.charge ell) * ‖g‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ell _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sys.nuclei.charge_nonneg ell)]
  have hz : ‖zeroModeShift sys L θ‖ ≤ zeroWeight sys * ‖g‖ := by
    unfold zeroModeShift zeroWeight
    refine (norm_add_le _ _).trans ?_
    rw [add_mul]
    exact add_le_add e1 e2
  calc |(zeroModeShift sys L θ).re| ≤ ‖zeroModeShift sys L θ‖ := Complex.abs_re_le_norm _
    _ ≤ zeroWeight sys * ‖g‖ := hz
    _ ≤ zeroWeight sys * (Real.pi / (2 * L)) :=
        mul_le_mul_of_nonneg_left hg (zeroWeight_nonneg sys)

/-! ## The molecule in cells of size `L` -/

section Family

variable {ν : Type} [Fintype ν]

/-- The system with the nuclei of the free-space molecule (positions `P_ℓ`) on the torus of cell
size `L`: unit-torus positions `-P_ℓ/L`, as in `hpos` of `prop:free`. -/
def sysAt (sys : CoulombSystem eta ν) (P : ν → E3) (L : ℝ) : CoulombSystem eta ν :=
  { sys with nuclei := { sys.nuclei with
      position := fun l => fun c => ((-(P l c) / L : ℝ) : UnitAddCircle) } }

/-- **`prop:free`, the complexity statement** (`N = O(ε⁻¹ log³(1/ε))`). Consider the molecule
(particles of `sys`, nuclei at `P_ℓ ∈ B_{R₀}(0)`) in the cells of size `L ≥ L₀ ≥ 2π`, with
range-truncation profiles `θ_L` of range `R_L ≤ L/2`, `θ_L ≡ 1` on `[0, L/2 - ρ]` and fixed total
variation `V`. Assume the hypotheses of `free_grid_exponentialU_prod` for every such `L`:
`E_∞` bounds the free-space form below; Agmon decay of the free ground state, uniformly in the
radius (normalised `C²` approximants with mass `≤ A e^{-2αd}` outside the product region
`{every particle in B_d(0)}`, every `d > 0`); and assumption (A) in the product geometry for the
torus ground states, with `α, β > 0`, and `A e^{-2αd₀}`, `A' e^{-2βd₀} ≤ 1/2` at
`d₀ = R_{L₀} - w`. Then there is `D` such that for every `0 < ε ≤ 1/2` some cell size `L ≥ L₀`
and register radius `2m` (`N = (4m + 1)³` grid points per particle) with
`N ≤ D ε⁻¹ log³(1/ε)` give `|E_{N,L} + C₀ - E_∞| ≤ ε`. -/
theorem free_grid_complexity_prod (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {R0 ρ w : ℝ} (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ) (hw : 0 < w)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    {R : ℝ → ℝ} {θ : ℝ → ℝ → ℝ} {V L₀ : ℝ} (hL₀ : 2 * Real.pi ≤ L₀)
    (hwL₀ : w < retainedRadius L₀ R0 ρ)
    (hfam : ∀ L, L₀ ≤ L → Profile (R L) (θ L) ∧ R L ≤ L / 2 ∧
      (∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ L r = 1) ∧ tv (R L) (θ L) = V)
    {Einf A α A' β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hA0 : 0 ≤ A) (hA'0 : 0 ≤ A')
    (hsmall : A * Real.exp (-(2 * α * (retainedRadius L₀ R0 ρ - w))) ≤ 1 / 2)
    (hsmall' : A' * Real.exp (-(2 * β * (retainedRadius L₀ R0 ρ - w))) ≤ 1 / 2)
    (hlow : ∀ ψ : Rcfg eta → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      IsFreeSector sys.sign lab ψ → Integrable (fun r => freePot sys P r * ‖ψ r‖ ^ 2) →
      Einf * ∫ r, ‖ψ r‖ ^ 2 ≤ freeEnergy sys P ψ)
    (hagmon : ∀ d > 0, ∀ ε > 0, ∃ φ : Rcfg eta → ℂ, ContDiff ℝ 2 φ ∧ HasCompactSupport φ ∧
      IsFreeSector sys.sign lab φ ∧ Integrable (fun r => freePot sys P r * ‖φ r‖ ^ 2) ∧
      ∫ r, ‖φ r‖ ^ 2 = 1 ∧ freeEnergy sys P φ ≤ Einf + ε ∧
      ∫ r in {r | ∀ i, ‖particle r i‖ < d}ᶜ, ‖φ r‖ ^ 2 ≤ A * Real.exp (-(2 * α * d)))
    (hA : ∀ L, L₀ ≤ L → ∀ EL, IsGLTorusGroundEnergy (sysAt sys P L) lab L (θ L) EL →
      ∀ ε > 0, ∃ u : C(MolecularPositionTorus eta, ℂ),
      ∃ hu : ContDiff ℝ 2 (torusRealLift u),
      (∀ i j : Fin eta, i ≠ j → lab i = lab j →
        ∀ x, u (molecularPositionSwap i j x) = sys.sign i * u x) ∧
      ∫ x, ‖u x‖ ^ 2 = 1 ∧ torusEnergy (sysAt sys P L) L (θ L) u hu ≤ EL + ε ∧
      ∫ x in {x | ∀ i, ‖particle (cellCoord L x) i‖ < retainedRadius L R0 ρ - w}ᶜ,
        ‖u x‖ ^ 2 ≤ A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w)))) :
    ∃ D : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ L, L₀ ≤ L ∧ ∃ m : ℕ,
      ((4 * m + 1 : ℕ) : ℝ) ^ 3 ≤ D / ε * Real.log (1 / ε) ^ 3 ∧
      ∃ Eg, PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy (sysAt sys P L) lab L m
          (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L V)
            (PlaneWaveGridG.gLref L (θ L) V) m) Eg ∧
        |Eg + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf| ≤ ε := by
  set C' := (eta : ℝ) * Real.pi ^ 2 * smoothSlope ^ 2 / w ^ 2 * max A A' *
    Real.exp (2 * max α β * (R0 + ρ + w)) with hC'
  have hC'0 : 0 ≤ C' := by
    have : 0 ≤ max A A' := le_trans hA0 (le_max_left _ _)
    positivity
  set γ := min α β / 2 with hγ
  have hγ0 : 0 < γ := by have := lt_min hα hβ; positivity
  set Eb := |Einf| + C' + zeroWeight sys / 4 + 1 with hEb
  have hL₀0 : 0 ≤ L₀ := le_trans (by positivity) hL₀
  refine complexity_of_rate (Q := fun L m Eg =>
      PlaneWaveGridG.IsGLSectorKernelGridGroundEnergy (sysAt sys P L) lab L m
        (PlaneWaveGridG.sharpKernel (PlaneWaveGridG.gLgamma L V)
          (PlaneWaveGridG.gLref L (θ L) V) m) Eg)
    (C0 := fun L => (zeroModeShift (sysAt sys P L) L (θ L)).re)
    (Cg := PlaneWaveGridG.gLErrorConstU sys V Eb)
    (K₀ := PlaneWaveGridG.gLKThresholdU sys V Eb) (m₀ := eta + 8) hL₀0 hγ0 hC'0 ?_
  intro L hLL₀ hLpos m hm hK
  obtain ⟨hθ, hRL, hone, htv⟩ := hfam L hLL₀
  have hL2π : 2 * Real.pi ≤ L := le_trans hL₀ hLL₀
  have hmono : retainedRadius L₀ R0 ρ ≤ retainedRadius L R0 ρ := by
    unfold retainedRadius
    linarith
  have hwL : w < retainedRadius L R0 ρ := lt_of_lt_of_le hwL₀ hmono
  have hd0 : 0 < retainedRadius L R0 ρ - w := by linarith
  have hsm : A * Real.exp (-(2 * α * (retainedRadius L R0 ρ - w))) ≤ 1 / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA0) hsmall
    nlinarith
  have hsm' : A' * Real.exp (-(2 * β * (retainedRadius L R0 ρ - w))) ≤ 1 / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA'0) hsmall'
    nlinarith
  obtain ⟨EL, hEL⟩ := exists_gLTorusGroundEnergy (sysAt sys P L) hlab hLpos hθ
    molecularCanonicalUnitHardyConstant canonicalPeriodicCoulombHardyBound_explicit
  have h := free_grid_exponentialU_prod (sysAt sys P L) lab hlab hL2π hθ hRL hR0 hρ hone P hP
    (fun l => rfl) hw hwL hEL hα.le hβ.le hsm hsm' hlow
    (hagmon (retainedRadius L R0 ρ - w) hd0) (hA L hLL₀ EL hEL)
  rw [htv] at h
  obtain ⟨h1, h2⟩ := h
  -- the energy budget
  have hexp1 : Real.exp (-(min α β * L / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := lt_min hα hβ
    have : 0 ≤ min α β * L := by positivity
    linarith
  have hEL1 : |EL + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf| ≤ C' := by
    refine h1.trans ?_
    have : C' * Real.exp (-(min α β * L / 2)) ≤ C' * 1 := mul_le_mul_of_nonneg_left hexp1 hC'0
    rw [mul_one] at this
    exact this
  have hz := abs_zeroModeShift_re_le (sysAt sys P L) hLpos hθ hRL
  have hz' : zeroWeight (sysAt sys P L) * (Real.pi / (2 * L)) ≤ zeroWeight sys / 4 := by
    have hq : zeroWeight (sysAt sys P L) = zeroWeight sys := rfl
    rw [hq]
    have hpi : Real.pi / (2 * L) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have := mul_le_mul_of_nonneg_left hpi (zeroWeight_nonneg sys)
    linarith
  have hEb' : |EL| + 1 ≤ Eb := by
    have habs : |EL| ≤ |EL + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf| +
        |(zeroModeShift (sysAt sys P L) L (θ L)).re| + |Einf| := by
      have := abs_add_le (EL + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf)
        (Einf - (zeroModeShift (sysAt sys P L) L (θ L)).re)
      rw [show EL + (zeroModeShift (sysAt sys P L) L (θ L)).re - Einf +
          (Einf - (zeroModeShift (sysAt sys P L) L (θ L)).re) = EL by ring] at this
      have h3 := abs_sub Einf (zeroModeShift (sysAt sys P L) L (θ L)).re
      linarith
    rw [hEb]
    linarith
  obtain ⟨Eg, hEg, herr⟩ := h2 Eb hEb' m hm hK
  refine ⟨Eg, hEg, ?_⟩
  have e : min α β * L / 2 = γ * L := by rw [hγ]; ring
  rw [e] at herr
  exact herr

end Family

end

end FreeBoundary
