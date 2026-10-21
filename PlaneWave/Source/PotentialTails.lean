import PlaneWave.Source.MixedClass

/-!
# Flux/source build, block 5: potential tails and the Coulomb form bound

* `FSDatum.moment_le_of_tails1`: the dyadic moment bound for states with tails
  `Σ_{k_a > λ} |v|² ≤ T²/λ`: `Σ_{A ≤ E₀} (1 + A)^{2r} |v|² ≤ C T² Λ^{4r-1}` for `r > 1/4`
  (the analogue of `cor:spectail` for the potential output `W_N u`).
* `norm_res_hot_WN_le`: `‖(1 - Q) W_N u‖ ≤ η C_tail (K/4)^{-1/2}`, and `wt_res_low_WN_le`:
  `‖(1+A)^s 1{A ≤ e_H} W_N u‖ ≤ C (C_tail + C_m Θ(u)) Λ_H^{2s - 1/2}` (`Λ_H ~ K`): the weighted
  potential tail `‖E^s P W u‖ ≤ C Ξ K^{2s-1/2}` of `lem:mixed` ("the potential-tail bound and
  dyadic summation").
* `kato_pair` (**the Coulomb form bound** `‖E^{-1/4} W_N E^{-1/4}‖ ≤ C` of `lem:h4`):
  `|⟪W_N y, φ⟫| ≤ √2 C_m ‖(1+A)^{1/4} y‖ ‖(1+A)^{1/4} φ‖`, from Hardy `|W_N| ≤ √2 C_m (1+A)^{1/2}`
  and Löwner–Heinz (`dev/PlaneWave.Source.LoewnerHeinz.lean`) at exponent `1/2`, in the eigenbasis of `W_N`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSDatum

open Finset

/-- The constant of `moment_le_of_tails1`. -/
noncomputable def momentConst1 (η : ℕ) (r cA : ℝ) : ℝ :=
  (1 + cA) ^ (2 * r) * (1 + 2 * η * (4 : ℝ) ^ (4 * r - 1) / ((2 : ℝ) ^ (4 * r - 1) - 1))

lemma momentConst1_nonneg (η : ℕ) {r cA : ℝ} (hr : 1 / 4 < r) (hcA : 0 ≤ cA) :
    0 ≤ momentConst1 η r cA := by
  unfold momentConst1
  have h1 : 1 < (2 : ℝ) ^ (4 * r - 1) := Real.one_lt_rpow (by norm_num) (by linarith)
  have : 0 < (2 : ℝ) ^ (4 * r - 1) - 1 := by linarith
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ 1 + cA by linarith) (2 * r)
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (4 * r - 1)
  positivity

/-- **Weighted moments from `λ^{-1}` register tails**: if `Σ |v|² ≤ T²` and
`Σ_{k_a > λ} |v|² ≤ T²/λ` for `λ ≥ 1`, then for `r > 1/4`
`Σ_{A ≤ E₀} (1 + A)^{2r} |v|² ≤ C T² Λ^{4r-1}`, where every register momentum is at most `Λ ≥ 1` on
`{A ≤ E₀}`. -/
theorem moment_le_of_tails1 {X : Type*} [Fintype X] {η : ℕ} (A : X → ℝ) (k : Fin η → X → ℝ)
    (v : X → ℂ) {cA E₀ Λ T r : ℝ} (hcA : 0 ≤ cA) (hA0 : ∀ x, 0 ≤ A x) (hΛ : 1 ≤ Λ)
    (hr : 1 / 4 < r) (hT : 0 ≤ T)
    (hAk : ∀ x (R : ℝ), 0 ≤ R → (∀ a, k a x ≤ R) → A x ≤ cA * R ^ 2)
    (hkA : ∀ x, A x ≤ E₀ → ∀ a, k a x ≤ Λ)
    (hv : ∑ x, ‖v x‖ ^ 2 ≤ T ^ 2)
    (htail : ∀ a (l : ℝ), 1 ≤ l → ∑ x, (if l < k a x then ‖v x‖ ^ 2 else 0) ≤ T ^ 2 / l) :
    ∑ x, (if A x ≤ E₀ then (1 + A x) ^ (2 * r) * ‖v x‖ ^ 2 else 0) ≤
      momentConst1 η r cA * T ^ 2 * Λ ^ (4 * r - 1) := by
  unfold momentConst1
  have h41 : 0 < 4 * r - 1 := by linarith
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hΛ (by norm_num : (1 : ℝ) < 2)
  have hJ1 : ∀ x, A x ≤ E₀ → ∀ a, k a x ≤ (2 : ℝ) ^ (n + 1) :=
    fun x hx a => (hkA x hx a).trans hn2.le
  have hJ2 : (2 : ℝ) ^ (n + 1) ≤ 2 * Λ := by rw [pow_succ]; linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, (2 : ℝ) ^ (4 * r - 1) = q := ⟨_, rfl⟩
  rw [hq]
  have hq1 : 1 < q := hq ▸ Real.one_lt_rpow (by norm_num) h41
  have hB : (4 : ℝ) ^ (2 * r) = 2 * q := by
    rw [← hq]
    calc (4 : ℝ) ^ (2 * r) = (2 : ℝ) ^ (4 * r) := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
          congr 1; push_cast; ring
      _ = (2 : ℝ) ^ ((4 * r - 1) + 1) := by rw [sub_add_cancel]
      _ = (2 : ℝ) ^ (4 * r - 1) * (2 : ℝ) ^ (1 : ℝ) := Real.rpow_add (by norm_num) _ _
      _ = 2 * (2 : ℝ) ^ (4 * r - 1) := by rw [Real.rpow_one]; ring
  have hq2 : q ^ 2 = (4 : ℝ) ^ (4 * r - 1) := by
    rw [← hq, Real.rpow_pow_comm (by norm_num)]; norm_num
  have hqJ : q ^ (n + 1) ≤ q * Λ ^ (4 * r - 1) := by
    rw [← hq, Real.rpow_pow_comm (by norm_num), ← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) hJ2 h41.le
  have hL : 1 ≤ Λ ^ (4 * r - 1) := Real.one_le_rpow hΛ h41.le
  have hgeom : ∑ j ∈ range (n + 1), q ^ (j + 1) ≤
      (4 : ℝ) ^ (4 * r - 1) * Λ ^ (4 * r - 1) / (q - 1) := by
    rw [le_div_iff₀ (by linarith)]
    have hsum : ∑ j ∈ range (n + 1), q ^ (j + 1) = q * ∑ j ∈ range (n + 1), q ^ j := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => pow_succ' q j
    rw [hsum, mul_assoc, geom_sum_mul, ← hq2]
    nlinarith
  have hC : 0 ≤ (1 + cA) ^ (2 * r) := Real.rpow_nonneg (by linarith) _
  have hpt : ∀ x, (if A x ≤ E₀ then (1 + A x) ^ (2 * r) * ‖v x‖ ^ 2 else 0) ≤
      (1 + cA) ^ (2 * r) * (‖v x‖ ^ 2 + ∑ j ∈ range (n + 1), ∑ a,
        ((4 : ℝ) ^ (2 * r)) ^ (j + 1) * (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0)) := by
    intro x
    by_cases hx : A x ≤ E₀
    · rw [if_pos hx]
      exact rpow_mul_le_dyadic (fun a => k a x) (hA0 x) hcA hr0 (by positivity) (hAk x) (n + 1)
        (hJ1 x hx)
    · rw [if_neg hx]
      apply mul_nonneg hC
      apply add_nonneg (by positivity)
      apply sum_nonneg; intro j _; apply sum_nonneg; intro a _
      apply mul_nonneg (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
      split_ifs <;> positivity
  have htl : ∀ j : ℕ, ∑ a : Fin η, ((4 : ℝ) ^ (2 * r)) ^ (j + 1) *
      ∑ x, (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0) ≤
        (η : ℝ) * (2 * T ^ 2 * q ^ (j + 1)) := by
    intro j
    have h1 : ∀ a : Fin η, ((4 : ℝ) ^ (2 * r)) ^ (j + 1) *
        ∑ x, (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0) ≤ 2 * T ^ 2 * q ^ (j + 1) := by
      intro a
      calc ((4 : ℝ) ^ (2 * r)) ^ (j + 1) * ∑ x, (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0)
          ≤ ((4 : ℝ) ^ (2 * r)) ^ (j + 1) * (T ^ 2 / (2 : ℝ) ^ j) :=
            mul_le_mul_of_nonneg_left (htail a _ (one_le_pow₀ (by norm_num))) (by positivity)
        _ = 2 * T ^ 2 * q ^ (j + 1) := by
            rw [hB, mul_pow, pow_succ (2 : ℝ)]
            field_simp
    calc _ ≤ ∑ a : Fin η, 2 * T ^ 2 * q ^ (j + 1) := sum_le_sum fun a _ => h1 a
      _ = (η : ℝ) * (2 * T ^ 2 * q ^ (j + 1)) := by simp
  calc ∑ x, (if A x ≤ E₀ then (1 + A x) ^ (2 * r) * ‖v x‖ ^ 2 else 0)
      ≤ ∑ x, (1 + cA) ^ (2 * r) * (‖v x‖ ^ 2 + ∑ j ∈ range (n + 1), ∑ a,
          ((4 : ℝ) ^ (2 * r)) ^ (j + 1) * (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0)) :=
        sum_le_sum fun x _ => hpt x
    _ = (1 + cA) ^ (2 * r) * (∑ x, ‖v x‖ ^ 2 + ∑ j ∈ range (n + 1), ∑ a,
          ((4 : ℝ) ^ (2 * r)) ^ (j + 1) *
            ∑ x, (if (2 : ℝ) ^ j < k a x then ‖v x‖ ^ 2 else 0)) := by
      rw [← mul_sum, sum_add_distrib]
      congr 2
      simp_rw [mul_sum]
      exact sum_comm.trans (sum_congr rfl fun j _ => sum_comm)
    _ ≤ (1 + cA) ^ (2 * r) *
          (T ^ 2 + ∑ j ∈ range (n + 1), (η : ℝ) * (2 * T ^ 2 * q ^ (j + 1))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add hv (sum_le_sum fun j _ => htl j)
    _ = (1 + cA) ^ (2 * r) * (T ^ 2 + 2 * η * T ^ 2 * ∑ j ∈ range (n + 1), q ^ (j + 1)) := by
      rw [mul_sum]
      congr 2
      exact sum_congr rfl fun j _ => by ring
    _ ≤ (1 + cA) ^ (2 * r) * (T ^ 2 * Λ ^ (4 * r - 1) + 2 * η * T ^ 2 *
          ((4 : ℝ) ^ (4 * r - 1) * Λ ^ (4 * r - 1) / (q - 1))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add (le_mul_of_one_le_right (pow_nonneg hT 2) hL)
      exact mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

end FSDatum

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Potential tails on good states -/

section PotTails

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

omit [Fintype ν] in
/-- On `A ≤ E` every register momentum is at most `(2 m_max E)^{1/2}`. -/
lemma kabs_le_of_Asym_le (x : Cfg eta n) {E : ℝ} (hx : Asym sys L n x ≤ E) (a : Fin eta) :
    finitePlaneWaveKabs (2 * Real.pi / L) n (x a) ≤ Real.sqrt (2 * mmax sys * E) := by
  have hm := fun b => sys.mass_pos b
  have hc := component_sq_le_mass_mul_massKineticSymbol hm
    (finitePlaneWaveKabs (2 * Real.pi / L) n) x a
  have hA : massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) x =
      2 * Asym sys L n x := by unfold Asym; ring
  rw [hA] at hc
  have hma := mass_le_mmax sys a
  have hA0 := FSGalerkin.Asym_nonneg sys L n x
  have hsq : finitePlaneWaveKabs (2 * Real.pi / L) n (x a) ^ 2 ≤ 2 * mmax sys * E := by
    have h := mul_le_mul hma (show 2 * Asym sys L n x ≤ 2 * E by linarith)
      (by linarith) (by linarith [one_le_mmax sys])
    linarith
  exact Real.le_sqrt_of_sq_le hsq

/-- The tail constant of `W_N` for states with `m̄ (‖u‖ + 2 ‖A u‖) ≤ M₂`. -/
noncomputable abbrev CtW (sys : CoulombSystem eta ν) (L Hunit M₂ : ℝ) : ℝ :=
  finiteCoulombPhysicalTailConstant sys L Hunit (molecularCanonicalLowConstant L)
    (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L) M₂

include hL in
lemma CtW_nonneg (Hunit : ℝ) {M₂ : ℝ} (hM₂ : 0 ≤ M₂) : 0 ≤ CtW sys L Hunit M₂ := by
  obtain ⟨hBlow, hCs, hBker, -, -, -⟩ := molecularCanonicalTailConstants_spec L hL
  exact finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM₂

include hL hKernel in
/-- **The hot part of the potential output**: `‖(1 - Q) W_N u‖ ≤ η C_tail (K/4)^{-1/2}`. -/
theorem norm_res_hot_WN_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hK1 : 1 ≤ Kc L n / 4) (hK2 : 2 * gF L ≤ Kc L n / 4) (u : En eta n) {M₂ : ℝ}
    (hM₂ : sys.maxMass * (‖u‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖) ≤ M₂) :
    ‖FSKernel.res (fun p => ¬ IsCold n p) (finiteCoulombPotential sys (coulombCellAmplitude L) n u)‖ ≤
      eta * (CtW sys L Hunit M₂ * (Kc L n / 4) ^ (-(1 / 2 : ℝ))) := by
  refine (norm_res_hot_le_sum hL _).trans ?_
  calc ∑ a, ‖regTail L a (Kc L n / 4) (finiteCoulombPotential sys (coulombCellAmplitude L) n u)‖
      ≤ ∑ _a : Fin eta, CtW sys L Hunit M₂ * (Kc L n / 4) ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_le_sum fun a _ => regTail_WN_le sys H hKernel Hunit hL hPeriodic a hK1 hK2 u hM₂
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

open Classical in
include hL hKernel in
/-- **The weighted potential tail on low energies**:
`‖(1+A)^s 1{A ≤ E} W_N u‖² ≤ C_s T² Λ^{4s-1}` with `T² = C_tail² + 2 C_m² (1 + 2g) Θ(u)²` and
`Λ = (2 m_max E)^{1/2} ≥ 1`, for `s > 1/4`. -/
theorem wt_res_low_WN_sq_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {s : ℝ} (hs : 1 / 4 < s) (u : En eta n) {M₂ : ℝ}
    (hM₂ : sys.maxMass * (‖u‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) u‖) ≤ M₂)
    {E : ℝ} (hΛ : 1 ≤ Real.sqrt (2 * mmax sys * E)) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) s
        (FSKernel.res (fun p => Asym sys L n p ≤ E)
          (finiteCoulombPotential sys (coulombCellAmplitude L) n u))‖ ^ 2 ≤
      FSDatum.momentConst1 eta s ((eta : ℝ) / 2) *
        (CtW sys L Hunit M₂ ^ 2 + 2 * finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          (1 + 2 * gF L) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2) *
        Real.sqrt (2 * mmax sys * E) ^ (4 * s - 1) := by
  set y := finiteCoulombPotential sys (coulombCellAmplitude L) n u with hy
  set Θ := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖
  set Cm := finiteCoulombPhysicalMassConstant sys L Hunit
  set T2 := CtW sys L Hunit M₂ ^ 2 + 2 * Cm ^ 2 * (1 + 2 * gF L) * Θ ^ 2 with hT2
  have hg := gF_pos hL
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hT20 : 0 ≤ T2 := by positivity
  have hy0 : ‖y‖ ^ 2 ≤ 2 * Cm ^ 2 * Θ ^ 2 := by
    have h1 := potential_le_wt sys Hunit n hL hPeriodic u
    have h2 := wt_mono sys L n (by norm_num : (1 / 2 : ℝ) ≤ 1) u
    have h3 : ‖y‖ ≤ Real.sqrt 2 * Cm * Θ :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    calc ‖y‖ ^ 2 ≤ (Real.sqrt 2 * Cm * Θ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = 2 * Cm ^ 2 * Θ ^ 2 := by rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  have hM₂0 : 0 ≤ M₂ := le_trans (by have := sys.one_le_maxMass; positivity) hM₂
  have key := FSDatum.moment_le_of_tails1 (η := eta) (Asym sys L n)
    (fun a x => finitePlaneWaveKabs (2 * Real.pi / L) n (x a)) y.ofLp (cA := (eta : ℝ) / 2)
    (E₀ := E) (Λ := Real.sqrt (2 * mmax sys * E)) (T := Real.sqrt T2) (r := s)
    (by positivity) (fun x => FSGalerkin.Asym_nonneg sys L n x) hΛ hs (Real.sqrt_nonneg _)
    (fun x R hR hx => Asym_le_of_kabs_le sys hL x R hR hx)
    (fun x hx a => kabs_le_of_Asym_le sys x hx a) ?_ ?_
  · rw [Real.sq_sqrt hT20] at key
    refine le_of_eq_of_le ?_ key
    rw [norm_sq_wt]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [FSKernel.res_apply]
    have h0 : 0 ≤ 1 + Asym sys L n p := by linarith [FSGalerkin.Asym_nonneg sys L n p]
    have e : ((1 + Asym sys L n p) ^ s) ^ 2 = (1 + Asym sys L n p) ^ (2 * s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; ring_nf
    split_ifs
    · rw [e]
    · simp
  · rw [Real.sq_sqrt hT20, ← norm_sq_En]
    refine hy0.trans ?_
    have : 0 ≤ CtW sys L Hunit M₂ ^ 2 := sq_nonneg _
    have : 2 * Cm ^ 2 * Θ ^ 2 ≤ 2 * Cm ^ 2 * (1 + 2 * gF L) * Θ ^ 2 := by
      have : 0 ≤ 2 * Cm ^ 2 * Θ ^ 2 := by positivity
      nlinarith
    linarith
  · intro a l hl
    rw [Real.sq_sqrt hT20]
    have hl0 : 0 < l := by linarith
    have hsq : ∑ x, (if l < finitePlaneWaveKabs (2 * Real.pi / L) n (x a) then ‖y.ofLp x‖ ^ 2
        else 0) = ‖regTail L a l y‖ ^ 2 := (norm_sq_regTail L a l y).symm
    rw [hsq, le_div_iff₀ hl0]
    by_cases hl2 : 2 * gF L ≤ l
    · have h := regTail_WN_le sys H hKernel Hunit hL hPeriodic a hl hl2 u hM₂
      have h2 : ‖regTail L a l y‖ ^ 2 ≤ CtW sys L Hunit M₂ ^ 2 * l⁻¹ := by
        calc ‖regTail L a l y‖ ^ 2 ≤ (CtW sys L Hunit M₂ * l ^ (-(1 / 2 : ℝ))) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h 2
          _ = CtW sys L Hunit M₂ ^ 2 * l⁻¹ := by
              have e : (l ^ (-(1 / 2 : ℝ))) ^ 2 = l⁻¹ := by
                rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num [Real.rpow_neg_one]
              rw [mul_pow, e]
      have : ‖regTail L a l y‖ ^ 2 * l ≤ CtW sys L Hunit M₂ ^ 2 := by
        calc ‖regTail L a l y‖ ^ 2 * l ≤ CtW sys L Hunit M₂ ^ 2 * l⁻¹ * l :=
              mul_le_mul_of_nonneg_right h2 hl0.le
          _ = CtW sys L Hunit M₂ ^ 2 := by field_simp
      have : 0 ≤ 2 * Cm ^ 2 * (1 + 2 * gF L) * Θ ^ 2 := by positivity
      linarith
    · push Not at hl2
      have h1 : ‖regTail L a l y‖ ^ 2 ≤ 2 * Cm ^ 2 * Θ ^ 2 :=
        (pow_le_pow_left₀ (norm_nonneg _) (norm_regTail_le L a l y) 2).trans hy0
      have h2 : ‖regTail L a l y‖ ^ 2 * l ≤ 2 * Cm ^ 2 * Θ ^ 2 * (1 + 2 * gF L) :=
        mul_le_mul h1 (by linarith) hl0.le (by positivity)
      have : 0 ≤ CtW sys L Hunit M₂ ^ 2 := sq_nonneg _
      nlinarith

end PotTails

/-! ## The Coulomb form bound (Kato) -/

section Kato

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

/-- The eigenvector basis of `W_N`. -/
noncomputable def potBasis : OrthonormalBasis (Fin (Module.finrank ℂ (En eta n))) ℂ (En eta n) :=
  (finiteCoulombPotential_isSymmetric sys (coulombCellAmplitude L) n).eigenvectorBasis rfl

/-- The eigenvalues of `W_N`. -/
noncomputable def potEig : Fin (Module.finrank ℂ (En eta n)) → ℝ :=
  (finiteCoulombPotential_isSymmetric sys (coulombCellAmplitude L) n).eigenvalues rfl

lemma potBasis_eigen (i : Fin (Module.finrank ℂ (En eta n))) :
    finiteCoulombPotential sys (coulombCellAmplitude L) n (potBasis sys L n i) =
      (potEig sys L n i : ℂ) • potBasis sys L n i :=
  (finiteCoulombPotential_isSymmetric sys (coulombCellAmplitude L) n).apply_eigenvectorBasis rfl i

variable {sys L n}

lemma inner_potBasis_W (v : En eta n) (i : Fin (Module.finrank ℂ (En eta n))) :
    ⟪potBasis sys L n i, finiteCoulombPotential sys (coulombCellAmplitude L) n v⟫_ℂ =
      (potEig sys L n i : ℂ) * ⟪potBasis sys L n i, v⟫_ℂ := by
  rw [← finiteCoulombPotential_isSymmetric sys (coulombCellAmplitude L) n, potBasis_eigen,
    inner_smul_left, Complex.conj_ofReal]

lemma norm_ePow_pot (v : En eta n) :
    ‖FluxSourceTest.ePow (potBasis sys L n) (fun i => |potEig sys L n i|) 1 v‖ =
      ‖finiteCoulombPotential sys (coulombCellAmplitude L) n v‖ := by
  have h2 : ‖FluxSourceTest.ePow (potBasis sys L n) (fun i => |potEig sys L n i|) 1 v‖ ^ 2 =
      ‖finiteCoulombPotential sys (coulombCellAmplitude L) n v‖ ^ 2 := by
    rw [FluxSourceTest.norm_sq_ePow, ← (potBasis sys L n).sum_sq_norm_inner_right
      (finiteCoulombPotential sys (coulombCellAmplitude L) n v)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_potBasis_W, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

omit [Fintype ν] in
/-- `ePow` of the standard basis with eigenvalues `(1+A)^{1/2}` is a spectral weight. -/
lemma ePow_sqrt_eq_wt (t : ℝ) (v : En eta n) :
    FluxSourceTest.ePow (sb eta n) (fun k => (1 + Asym sys L n k) ^ (1 / 2 : ℝ)) t v =
      FSSpectral.wt (sb eta n) (Asym sys L n) (t / 2) v := by
  rw [← FSSpectral.ePow_one_add_eq_wt]
  unfold FluxSourceTest.ePow
  refine Finset.sum_congr rfl fun k _ => ?_
  have h0 : 0 ≤ 1 + Asym sys L n k := by linarith [FSGalerkin.Asym_nonneg sys L n k]
  rw [← Real.rpow_mul h0]
  congr 3
  ring

/-- **The Coulomb form bound** (Kato, `‖E^{-1/4} W_N E^{-1/4}‖ ≤ √2 C_m`):
`|⟪W_N y, φ⟫| ≤ √2 C_m ‖(1+A)^{1/4} y‖ ‖(1+A)^{1/4} φ‖`. -/
theorem kato_pair (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (y φ : En eta n) :
    ‖⟪finiteCoulombPotential sys (coulombCellAmplitude L) n y, φ⟫_ℂ‖ ≤
      Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) y‖ *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖ := by
  set b := potBasis sys L n
  set μ := potEig sys L n
  set C := Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit
  have hC : 0 ≤ C := by have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit; positivity
  -- Hardy in eigenbasis form
  have h1 : ∀ v, ‖FluxSourceTest.ePow b (fun i => |μ i|) 1 v‖ ≤
      C * ‖FluxSourceTest.ePow (sb eta n) (fun k => (1 + Asym sys L n k) ^ (1 / 2 : ℝ)) 1 v‖ := by
    intro v
    rw [norm_ePow_pot, ePow_sqrt_eq_wt]
    exact potential_le_wt sys Hunit n hL hPeriodic v
  -- Löwner–Heinz at exponent `1/2`
  have h2 := FluxSourceTest.norm_ePow_le_of_norm_ePow_le b (sb eta n) (fun i => abs_nonneg (μ i))
    (fun k => Real.rpow_nonneg (by linarith [FSGalerkin.Asym_nonneg sys L n k]) _) hC h1
    (s := 1 / 2) ⟨by norm_num, by norm_num⟩
  have h3 : ∀ v, ‖FluxSourceTest.ePow b (fun i => |μ i|) (1 / 2) v‖ ≤
      C ^ (1 / 2 : ℝ) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) v‖ := by
    intro v
    have := h2 v
    rwa [ePow_sqrt_eq_wt, show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] at this
  -- the pairing in the eigenbasis
  have hexp : ⟪finiteCoulombPotential sys (coulombCellAmplitude L) n y, φ⟫_ℂ =
      ∑ i, (μ i : ℂ) * (conj ⟪b i, y⟫_ℂ * ⟪b i, φ⟫_ℂ) := by
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← inner_conj_symm, inner_potBasis_W, map_mul, Complex.conj_ofReal]
    ring
  rw [hexp]
  calc ‖∑ i, (μ i : ℂ) * (conj ⟪b i, y⟫_ℂ * ⟪b i, φ⟫_ℂ)‖
      ≤ ∑ i, (|μ i| ^ (1 / 2 : ℝ) * ‖⟪b i, y⟫_ℂ‖) * (|μ i| ^ (1 / 2 : ℝ) * ‖⟪b i, φ⟫_ℂ‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
        have e : |μ i| ^ (1 / 2 : ℝ) * |μ i| ^ (1 / 2 : ℝ) = |μ i| := by
          rw [← Real.rpow_add' (abs_nonneg _) (by norm_num)]; norm_num
        calc |μ i| * (‖⟪b i, y⟫_ℂ‖ * ‖⟪b i, φ⟫_ℂ‖) =
            (|μ i| ^ (1 / 2 : ℝ) * |μ i| ^ (1 / 2 : ℝ)) * (‖⟪b i, y⟫_ℂ‖ * ‖⟪b i, φ⟫_ℂ‖) := by
              rw [e]
          _ = _ := by ring
    _ ≤ Real.sqrt (∑ i, (|μ i| ^ (1 / 2 : ℝ) * ‖⟪b i, y⟫_ℂ‖) ^ 2) *
          Real.sqrt (∑ i, (|μ i| ^ (1 / 2 : ℝ) * ‖⟪b i, φ⟫_ℂ‖) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖FluxSourceTest.ePow b (fun i => |μ i|) (1 / 2) y‖ *
          ‖FluxSourceTest.ePow b (fun i => |μ i|) (1 / 2) φ‖ := by
        rw [← Real.sqrt_sq (norm_nonneg (FluxSourceTest.ePow b (fun i => |μ i|) (1 / 2) y)),
          ← Real.sqrt_sq (norm_nonneg (FluxSourceTest.ePow b (fun i => |μ i|) (1 / 2) φ)),
          FluxSourceTest.norm_sq_ePow, FluxSourceTest.norm_sq_ePow]
        congr 2 <;> exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (C ^ (1 / 2 : ℝ) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) y‖) *
          (C ^ (1 / 2 : ℝ) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖) :=
        mul_le_mul (h3 y) (h3 φ) (norm_nonneg _) (by positivity)
    _ = C * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) y‖ *
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖ := by
        have : C ^ (1 / 2 : ℝ) * C ^ (1 / 2 : ℝ) = C := by
          rw [← Real.rpow_add' hC (by norm_num)]; norm_num
        calc _ = (C ^ (1 / 2 : ℝ) * C ^ (1 / 2 : ℝ)) *
              ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) y‖ *
              ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖ := by ring
          _ = _ := by rw [this]

end Kato

end FSNormal
