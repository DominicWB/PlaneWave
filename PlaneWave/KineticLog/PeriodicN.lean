import PlaneWave.KineticLog.PeriodicUniform

/-!
# Logarithmic kinetic bound, part 34: the periodic endpoints in terms of `N`

At fixed cell size `L` the number of Fourier modes per register is `N = Θ(K³)`, so the periodic
bounds read `C 𝒟² [1 + t + log(2 + N)]/N`. Here `N` is the mode count of the Lean cube
`|ν|_∞ ≤ k`, `N = #FinitePlaneWaveMode k = (2k + 1)³` (`finitePlaneWaveMode_card`): for Galerkin,
`k = n` with `K = 2πn/L`; for the grid, `k = m` with `K = 2πm/L`, the unpadded admissible size
`n = 2m + 1` of `app:source` (`N = n³`; the padded register has `(2n - 1)³ = (4m + 1)³` points).

* `basis_N_arith`, `basis_N_arith_stop`: for `k ≥ 1`,
  `[1 + t + log(2 + K)]/K³ ≤ c_L [1 + t + log(2 + N)]/N` and
  `[1 + (1 + log(2 + K))/τ]/K³ ≤ c_L [1 + (1 + log(2 + N))/τ]/N`, with
  `c_L = (27 L³/(8π³)) (1 + log(1 + 2π/L))` (`cNL`);
* **`thm_kinetic_log_galerkin_N`**, **`thm_kinetic_log_grid_N`**, **`kinetic_retained_galerkin_N`**,
  **`cor_stopping_log_galerkin_N`**, **`cor_stopping_log_grid_N`** and the spin versions: the
  `_all` endpoints of `PeriodicUniform` with `K` replaced by `N` (constants first).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal FSGalerkin

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The basis count -/

/-- The constant of the basis count, `c_L = (27 L³/(8π³)) (1 + log(1 + 2π/L))`. -/
noncomputable def cNL (L : ℝ) : ℝ :=
  27 * L ^ 3 / (8 * Real.pi ^ 3) * (1 + Real.log (1 + 2 * Real.pi / L))

lemma cNL_nonneg {L : ℝ} (hL : 0 < L) : 0 ≤ cNL L := by
  unfold cNL
  have h1 : 0 ≤ 2 * Real.pi / L := by have := Real.pi_pos; positivity
  have : 0 ≤ Real.log (1 + 2 * Real.pi / L) := Real.log_nonneg (by linarith)
  have := Real.pi_pos
  positivity

/-- The number of one-particle Fourier modes of the cube `|ν|_∞ ≤ k`, `(2k + 1)³`. -/
lemma modes_eq (k : ℕ) :
    (Fintype.card (FinitePlaneWaveMode k) : ℝ) = (2 * (k : ℝ) + 1) ^ 3 := by
  rw [finitePlaneWaveMode_card]
  push_cast
  ring

/-- `1/K³ ≤ (27 L³/(8π³))/N` for `K = 2πk/L`, `N = (2k + 1)³`, `k ≥ 1`. -/
lemma inv_cube_le_N {L : ℝ} (hL : 0 < L) {k : ℕ} (hk : 1 ≤ k) :
    1 / Kc L k ^ 3 ≤
      27 * L ^ 3 / (8 * Real.pi ^ 3) / (Fintype.card (FinitePlaneWaveMode k) : ℝ) := by
  rw [modes_eq]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpi := Real.pi_pos
  have hKc : Kc L k = 2 * Real.pi / L * k := rfl
  rw [hKc]
  have hN0 : 0 < (2 * (k : ℝ) + 1) ^ 3 := by positivity
  have hcube : (2 * (k : ℝ) + 1) ^ 3 ≤ 27 * (k : ℝ) ^ 3 := by
    have h1 : 2 * (k : ℝ) + 1 ≤ 3 * k := by linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 3
    nlinarith
  have e : 1 / (2 * Real.pi / L * k) ^ 3 = L ^ 3 / (8 * Real.pi ^ 3 * (k : ℝ) ^ 3) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) hN0]
  have : L ^ 3 * (2 * (k : ℝ) + 1) ^ 3 ≤ L ^ 3 * (27 * (k : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hcube (by positivity)
  have e2 : 27 * L ^ 3 / (8 * Real.pi ^ 3) * (8 * Real.pi ^ 3 * (k : ℝ) ^ 3) =
      L ^ 3 * (27 * (k : ℝ) ^ 3) := by
    field_simp
  rw [e2]
  exact this

/-- `log(2 + K) ≤ log(1 + 2π/L) + log(2 + N)`. -/
lemma log_K_le_N {L : ℝ} (hL : 0 < L) (k : ℕ) :
    Real.log (2 + Kc L k) ≤ Real.log (1 + 2 * Real.pi / L) +
      Real.log (2 + (Fintype.card (FinitePlaneWaveMode k) : ℝ)) := by
  rw [modes_eq]
  have hpi := Real.pi_pos
  have ha : 0 < 2 * Real.pi / L := by positivity
  have hKc : Kc L k = 2 * Real.pi / L * k := rfl
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkN : (k : ℝ) ≤ (2 * (k : ℝ) + 1) ^ 3 := by
    have h1 : (k : ℝ) ≤ 2 * k + 1 := by linarith
    have h2 : (1 : ℝ) ≤ 2 * k + 1 := by linarith
    calc (k : ℝ) ≤ 2 * k + 1 := h1
      _ = (2 * k + 1) * 1 := by ring
      _ ≤ (2 * k + 1) * (2 * k + 1) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          nlinarith
      _ = (2 * k + 1) ^ 3 := by ring
  rw [← Real.log_mul (by linarith) (by positivity), hKc]
  apply Real.log_le_log (by positivity)
  have : 2 * Real.pi / L * k ≤ 2 * Real.pi / L * (2 * (k : ℝ) + 1) ^ 3 :=
    mul_le_mul_of_nonneg_left hkN ha.le
  nlinarith [this]

/-- **The basis count**: `[1 + t + log(2 + K)]/K³ ≤ c_L [1 + t + log(2 + N)]/N`. -/
lemma basis_N_arith {L : ℝ} (hL : 0 < L) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    (1 + t + Real.log (2 + Kc L k)) / Kc L k ^ 3 ≤
      cNL L * ((1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode k) : ℝ))) /
        (Fintype.card (FinitePlaneWaveMode k) : ℝ)) := by
  set N : ℝ := (Fintype.card (FinitePlaneWaveMode k) : ℝ) with hN
  have hpi := Real.pi_pos
  have hN0 : 0 < N := by rw [hN, modes_eq]; positivity
  have hb : 0 ≤ Real.log (1 + 2 * Real.pi / L) :=
    Real.log_nonneg (by have : 0 ≤ 2 * Real.pi / L := by positivity
                        linarith)
  have hlogN : 0 ≤ Real.log (2 + N) := Real.log_nonneg (by linarith)
  have hX : 1 + t + Real.log (2 + Kc L k) ≤
      (1 + Real.log (1 + 2 * Real.pi / L)) * (1 + t + Real.log (2 + N)) := by
    have := log_K_le_N hL k
    rw [← hN] at this
    nlinarith
  have hA := inv_cube_le_N hL hk
  rw [← hN] at hA
  have hQ0 : 0 ≤ 1 + t + Real.log (2 + Kc L k) := by
    have : 0 ≤ Kc L k := by
      change 0 ≤ 2 * Real.pi / L * k
      positivity
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Kc L k by linarith)
    linarith
  calc (1 + t + Real.log (2 + Kc L k)) / Kc L k ^ 3
      = (1 + t + Real.log (2 + Kc L k)) * (1 / Kc L k ^ 3) := by ring
    _ ≤ ((1 + Real.log (1 + 2 * Real.pi / L)) * (1 + t + Real.log (2 + N))) *
          (27 * L ^ 3 / (8 * Real.pi ^ 3) / N) :=
        mul_le_mul hX hA (div_nonneg zero_le_one (pow_nonneg (Kc_nonneg' hL k) 3))
          (mul_nonneg (by linarith) (by linarith))
    _ = cNL L * ((1 + t + Real.log (2 + N)) / N) := by
        unfold cNL
        ring

/-- **The basis count for the stopping bound**:
`[1 + (1 + log(2 + K))/τ]/K³ ≤ c_L [1 + (1 + log(2 + N))/τ]/N`. -/
lemma basis_N_arith_stop {L : ℝ} (hL : 0 < L) {k : ℕ} (hk : 1 ≤ k) {τ : ℝ} (hτ : 0 < τ) :
    (1 + (1 + Real.log (2 + Kc L k)) / τ) / Kc L k ^ 3 ≤
      cNL L * ((1 + (1 + Real.log (2 + (Fintype.card (FinitePlaneWaveMode k) : ℝ))) / τ) /
        (Fintype.card (FinitePlaneWaveMode k) : ℝ)) := by
  set N : ℝ := (Fintype.card (FinitePlaneWaveMode k) : ℝ) with hN
  have hpi := Real.pi_pos
  have hN0 : 0 < N := by rw [hN, modes_eq]; positivity
  set b := Real.log (1 + 2 * Real.pi / L) with hbdef
  have hb : 0 ≤ b :=
    Real.log_nonneg (by have : 0 ≤ 2 * Real.pi / L := by positivity
                        linarith)
  have hlogN : 0 ≤ Real.log (2 + N) := Real.log_nonneg (by linarith)
  have hlog := log_K_le_N hL k
  rw [← hN, ← hbdef] at hlog
  have hX : 1 + (1 + Real.log (2 + Kc L k)) / τ ≤ (1 + b) * (1 + (1 + Real.log (2 + N)) / τ) := by
    have h1 : (1 + Real.log (2 + Kc L k)) / τ ≤ (b + (1 + Real.log (2 + N))) / τ :=
      div_le_div_of_nonneg_right (by linarith) hτ.le
    have h2 : (b + (1 + Real.log (2 + N))) / τ = b / τ + (1 + Real.log (2 + N)) / τ := by ring
    have h3 : b / τ ≤ b + b * ((1 + Real.log (2 + N)) / τ) := by
      have e : b * ((1 + Real.log (2 + N)) / τ) = b / τ * (1 + Real.log (2 + N)) := by ring
      rw [e]
      have : b / τ ≤ b / τ * (1 + Real.log (2 + N)) := by
        have := div_nonneg hb hτ.le
        nlinarith
      linarith
    nlinarith
  have hA := inv_cube_le_N hL hk
  rw [← hN] at hA
  have hQ0 : 0 ≤ 1 + (1 + Real.log (2 + Kc L k)) / τ := by
    have : 0 ≤ Kc L k := by
      change 0 ≤ 2 * Real.pi / L * k
      positivity
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Kc L k by linarith)
    have : 0 ≤ (1 + Real.log (2 + Kc L k)) / τ := div_nonneg (by linarith) hτ.le
    linarith
  calc (1 + (1 + Real.log (2 + Kc L k)) / τ) / Kc L k ^ 3
      = (1 + (1 + Real.log (2 + Kc L k)) / τ) * (1 / Kc L k ^ 3) := by ring
    _ ≤ ((1 + b) * (1 + (1 + Real.log (2 + N)) / τ)) * (27 * L ^ 3 / (8 * Real.pi ^ 3) / N) :=
        mul_le_mul hX hA (div_nonneg zero_le_one (pow_nonneg (Kc_nonneg' hL k) 3))
          (mul_nonneg (by linarith) (by
            have : 0 ≤ (1 + Real.log (2 + N)) / τ := div_nonneg (by linarith) hτ.le
            linarith))
    _ = cNL L * ((1 + (1 + Real.log (2 + N)) / τ) / N) := by
        unfold cNL
        rw [← hbdef]
        ring

/-- Rescaling a bound `C X Q/K³` with `Q/K³ ≤ c (Q'/N)`. -/
lemma scale_N {C X Q K c Q' N : ℝ} (hC : 0 ≤ C) (hX : 0 ≤ X) (h : Q / K ^ 3 ≤ c * (Q' / N)) :
    C * X * Q / K ^ 3 ≤ C * c * X * Q' / N := by
  calc C * X * Q / K ^ 3 = C * X * (Q / K ^ 3) := by ring
    _ ≤ C * X * (c * (Q' / N)) := mul_le_mul_of_nonneg_left h (mul_nonneg hC hX)
    _ = C * c * X * Q' / N := by ring

/-- Rescaling a bound `C X (Q/K³)` with `Q/K³ ≤ c (Q'/N)`. -/
lemma scale_N' {C X Q K c Q' N : ℝ} (hC : 0 ≤ C) (hX : 0 ≤ X) (h : Q / K ^ 3 ≤ c * (Q' / N)) :
    C * X * (Q / K ^ 3) ≤ C * c * X * (Q' / N) := by
  calc C * X * (Q / K ^ 3) ≤ C * X * (c * (Q' / N)) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg hC hX)
    _ = C * c * X * (Q' / N) := by ring

section Galerkin

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hL hKernel in
/-- **`thm:kinetic-log`, Galerkin case, in terms of `N`**: with `N = (2n + 1)³` modes per register,
`|⟨ψ(t), T_{p₀} ψ(t)⟩ - ⟨ψ_N(t), T_{p₀} ψ_N(t)⟩| ≤ C 𝒟² [1 + t + log(2 + N)]/N`. -/
theorem thm_kinetic_log_galerkin_N (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (D : EvoData L H) (t : ℝ),
      0 ≤ t →
      |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
          (regKin sys (gF L) p₀).expect (emb eta n (retFlow sys L n (zero_isSymmetric (n := n))
            (-t) (ext eta n (Sm eta L D.u₀))))| ≤
        C * D.Xi ^ 2 * (1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) /
          (Fintype.card (FinitePlaneWaveMode n) : ℝ) := by
  obtain ⟨C, hC, N₀, h⟩ := thm_kinetic_log_galerkin_all sys hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1, fun n hn p₀ D t ht => ?_⟩
  exact (h n (le_trans (le_max_left _ _) hn) p₀ D t ht).trans
    (scale_N hC (sq_nonneg _) (basis_N_arith hL (le_trans (le_max_right _ _) hn) ht))

include hL hKernel in
/-- **eq:kinetic-retained-galerkin in terms of `N`**:
`‖P ψ(t) - ψ_N(t)‖ ≤ C 𝒟 [1 + t + log(2 + N)]/N`. -/
theorem kinetic_retained_galerkin_N (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (D : EvoData L H) (t : ℝ), 0 ≤ t →
      ‖molecularH2Truncate n (D.U t (Sm eta L D.u₀)) -
          emb eta n
              (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀)))‖ ≤
        C * D.Xi * (1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) /
          (Fintype.card (FinitePlaneWaveMode n) : ℝ) := by
  obtain ⟨C, hC, N₀, h⟩ := kinetic_retained_galerkin sys hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1, fun n hn D t ht => ?_⟩
  exact (h n (le_trans (le_max_left _ _) hn) D t ht).trans
    (scale_N hC D.Xi_nonneg (basis_N_arith hL (le_trans (le_max_right _ _) hn) ht))

include hL hKernel in
/-- **`cor:stopping-log`, Galerkin case, in terms of `N`**: the signed secants differ by at most
`(C 𝒟²/v_p) [1 + (1 + log(2 + N))/τ]/N`. -/
theorem cor_stopping_log_galerkin_N (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (D : EvoData L H) {vp τ : ℝ},
      0 < vp → 0 < τ →
      let ψN : ℝ → L2 eta := fun s =>
        emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-s) (ext eta n (Sm eta L D.u₀)))
      |((regKin sys (gF L) p₀).expect (D.U τ (Sm eta L D.u₀)) -
            (regKin sys (gF L) p₀).expect (D.U 0 (Sm eta L D.u₀))) / (vp * τ) -
          ((regKin sys (gF L) p₀).expect (ψN τ) - (regKin sys (gF L) p₀).expect (ψN 0)) /
            (vp * τ)| ≤
        C * D.Xi ^ 2 / vp *
          (1 + (1 + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) / τ) /
            (Fintype.card (FinitePlaneWaveMode n) : ℝ) := by
  obtain ⟨C, hC, N₀, h⟩ := cor_stopping_log_galerkin_all sys hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1, fun n hn p₀ D vp τ hvp hτ => ?_⟩
  refine (h n (le_trans (le_max_left _ _) hn) p₀ D hvp hτ).trans ?_
  have hb := basis_N_arith_stop hL (le_trans (le_max_right _ _) hn) hτ
  have e1 : ∀ c : ℝ, c * D.Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 =
      c * (D.Xi ^ 2 / vp) * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 := fun c => by ring
  rw [e1]
  refine (scale_N hC (div_nonneg (sq_nonneg _) hvp.le) hb).trans (le_of_eq ?_)
  ring

include hL hKernel in
/-- **eq:kinetic-retained-galerkin with spin, in terms of `N`**: one constant for every finite
spin set. -/
theorem kinetic_retained_galerkin_spin_N (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (S : Type) [Fintype S]
      (Ds : S → EvoData L H) (t : ℝ), 0 ≤ t →
      Real.sqrt (∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - FSSpin.galS sys n Ds t σ‖ ^ 2)
        ≤ C * FSSpin.XiS Ds * ((1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) /
          (Fintype.card (FinitePlaneWaveMode n) : ℝ)) := by
  obtain ⟨C, hC, N₀, h⟩ := kinetic_retained_galerkin_spin_all sys hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1, fun n hn S _ Ds t ht => ?_⟩
  exact (h n (le_trans (le_max_left _ _) hn) S Ds t ht).trans
    (scale_N' hC (FSSpin.XiS_nonneg Ds) (basis_N_arith hL (le_trans (le_max_right _ _) hn) ht))

include hL hKernel in
/-- **`thm:kinetic-log`, Galerkin case with spin, in terms of `N`**. -/
theorem thm_kinetic_log_galerkin_spin_N (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (S : Type) [Fintype S]
      (Ds : S → EvoData L H) (t : ℝ), 0 ≤ t →
      |FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds t) -
          FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds t)| ≤
        C * FSSpin.XiS Ds ^ 2 *
          ((1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) /
            (Fintype.card (FinitePlaneWaveMode n) : ℝ)) := by
  obtain ⟨C, hC, N₀, h⟩ := thm_kinetic_log_galerkin_spin_all sys hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1, fun n hn p₀ S _ Ds t ht => ?_⟩
  exact (h n (le_trans (le_max_left _ _) hn) p₀ S Ds t ht).trans
    (scale_N' hC (sq_nonneg _) (basis_N_arith hL (le_trans (le_max_right _ _) hn) ht))

include hL hKernel in
/-- **`cor:stopping-log`, Galerkin case with spin, in terms of `N`**. -/
theorem cor_stopping_log_galerkin_spin_N (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (S : Type) [Fintype S]
      (Ds : S → EvoData L H) {vp τ : ℝ}, 0 < vp → 0 < τ →
        |(FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds τ) -
              FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds 0)) / (vp * τ) -
            (FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds τ) -
              FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds 0)) / (vp * τ)| ≤
          C * FSSpin.XiS Ds ^ 2 *
            ((1 + (1 + Real.log (2 + (Fintype.card (FinitePlaneWaveMode n) : ℝ))) / τ) /
              (Fintype.card (FinitePlaneWaveMode n) : ℝ) / vp) := by
  obtain ⟨C, hC, N₀, h⟩ := cor_stopping_log_galerkin_spin_all sys hL H hKernel Hunit hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max N₀ 1,
    fun n hn p₀ S _ Ds vp τ hvp hτ => ?_⟩
  refine (h n (le_trans (le_max_left _ _) hn) p₀ S Ds hvp hτ).trans ?_
  have hb := basis_N_arith_stop hL (le_trans (le_max_right _ _) hn) hτ
  have hX := FSSpin.XiS_nonneg Ds
  have e1 : C * FSSpin.XiS Ds ^ 2 * ((1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 / vp) =
      C * (FSSpin.XiS Ds ^ 2 / vp) * ((1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3) := by
    ring
  rw [e1]
  refine (scale_N' hC (div_nonneg (sq_nonneg _) hvp.le) hb).trans (le_of_eq ?_)
  ring

end Galerkin

section Grid

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **`thm:kinetic-log`, grid case, in terms of `N`**: for the unpadded admissible size
`n = 2m + 1` (`N = n³ = (2m + 1)³`, `K = 2πm/L`, register `(4m + 1)³`), every kernel of the class
and every grid propagator, `|⟨ψ(t), T_{p₀} ψ(t)⟩ - ⟨ψ_g(t), T_{p₀} ψ_g(t)⟩| ≤
C 𝒟² [1 + t + log(2 + N)]/N`. -/
theorem thm_kinetic_log_grid_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) {κ : Lat3 → ℝ},
      IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
          (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys)
            (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            κ (2 * Real.pi / L) x))) t) →
        ∀ (D : EvoData L H) (t : ℝ), 0 ≤ t →
          |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
              regExpect sys (gF L) p₀ (Ug t (regCoeff m (Sm eta L D.u₀)))| ≤
            C * D.Xi ^ 2 * (1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode m) : ℝ))) /
              (Fintype.card (FinitePlaneWaveMode m) : ℝ) := by
  obtain ⟨C, hC, m₀, h⟩ := thm_kinetic_log_grid_all sys H hKernel Hunit hL hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max m₀ 1,
    fun m hm p₀ κ hκ Ug hg0 hgcomm hgderiv D t ht => ?_⟩
  exact (h m (le_trans (le_max_left _ _) hm) p₀ hκ Ug hg0 hgcomm hgderiv D t ht).trans
    (scale_N hC (sq_nonneg _) (basis_N_arith hL (le_trans (le_max_right _ _) hm) ht))

include hKernel hL hPeriodic in
/-- **`cor:stopping-log`, grid case, in terms of `N`**. -/
theorem cor_stopping_log_grid_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) {κ : Lat3 → ℝ},
      IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
          (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys)
            (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            κ (2 * Real.pi / L) x))) t) →
        ∀ (D : EvoData L H) {vp τ : ℝ}, 0 < vp → 0 < τ →
          |((regKin sys (gF L) p₀).expect (D.U τ (Sm eta L D.u₀)) -
                (regKin sys (gF L) p₀).expect (D.U 0 (Sm eta L D.u₀))) / (vp * τ) -
              (regExpect sys (gF L) p₀ (Ug τ (regCoeff m (Sm eta L D.u₀))) -
                regExpect sys (gF L) p₀ (Ug 0 (regCoeff m (Sm eta L D.u₀)))) / (vp * τ)| ≤
            C * D.Xi ^ 2 / vp *
              (1 + (1 + Real.log (2 + (Fintype.card (FinitePlaneWaveMode m) : ℝ))) / τ) /
                (Fintype.card (FinitePlaneWaveMode m) : ℝ) := by
  obtain ⟨C, hC, m₀, h⟩ := cor_stopping_log_grid_all sys H hKernel Hunit hL hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max m₀ 1,
    fun m hm p₀ κ hκ Ug hg0 hgcomm hgderiv D vp τ hvp hτ => ?_⟩
  refine (h m (le_trans (le_max_left _ _) hm) p₀ hκ Ug hg0 hgcomm hgderiv D hvp hτ).trans ?_
  have hb := basis_N_arith_stop hL (le_trans (le_max_right _ _) hm) hτ
  have e1 : ∀ c : ℝ, c * D.Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 =
      c * (D.Xi ^ 2 / vp) * (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 := fun c => by ring
  rw [e1]
  refine (scale_N hC (div_nonneg (sq_nonneg _) hvp.le) hb).trans (le_of_eq ?_)
  ring

include hKernel hL hPeriodic in
/-- **`thm:kinetic-log`, grid case with spin, in terms of `N`**. -/
theorem thm_kinetic_log_grid_spin_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) (S : Type) [Fintype S]
      {κ : Lat3 → ℝ}, IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
          (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys)
            (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            κ (2 * Real.pi / L) x))) t) →
        ∀ (Ds : S → EvoData L H) (t : ℝ), 0 ≤ t →
          |FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds t) -
              regExpectS sys (gF L) p₀ (gridS m Ug Ds t)| ≤
            C * FSSpin.XiS Ds ^ 2 *
              ((1 + t + Real.log (2 + (Fintype.card (FinitePlaneWaveMode m) : ℝ))) /
                (Fintype.card (FinitePlaneWaveMode m) : ℝ)) := by
  obtain ⟨C, hC, m₀, h⟩ := thm_kinetic_log_grid_spin_all sys H hKernel Hunit hL hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max m₀ 1,
    fun m hm p₀ S _ κ hκ Ug hg0 hgcomm hgderiv Ds t ht => ?_⟩
  exact (h m (le_trans (le_max_left _ _) hm) p₀ S hκ Ug hg0 hgcomm hgderiv Ds t ht).trans
    (scale_N' hC (sq_nonneg _) (basis_N_arith hL (le_trans (le_max_right _ _) hm) ht))

include hKernel hL hPeriodic in
/-- **`cor:stopping-log`, grid case with spin, in terms of `N`**. -/
theorem cor_stopping_log_grid_spin_N :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (p₀ : Fin eta) (S : Type) [Fintype S]
      {κ : Lat3 → ℝ}, IsGridKernel (coulombCellAmplitude L) m κ →
      ∀ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
        (∀ x, Ug 0 x = x) →
        (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
          (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys)
            (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) (Ug t x)) →
        (∀ t x, HasDerivAt (fun s => Ug s x)
          (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            κ (2 * Real.pi / L) x))) t) →
        ∀ (Ds : S → EvoData L H) {vp τ : ℝ}, 0 < vp → 0 < τ →
          |(FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds τ) -
                FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds 0)) / (vp * τ) -
              (regExpectS sys (gF L) p₀ (gridS m Ug Ds τ) -
                regExpectS sys (gF L) p₀ (gridS m Ug Ds 0)) / (vp * τ)| ≤
            C * FSSpin.XiS Ds ^ 2 *
              ((1 + (1 + Real.log (2 + (Fintype.card (FinitePlaneWaveMode m) : ℝ))) / τ) /
                (Fintype.card (FinitePlaneWaveMode m) : ℝ) / vp) := by
  obtain ⟨C, hC, m₀, h⟩ := cor_stopping_log_grid_spin_all sys H hKernel Hunit hL hPeriodic
  refine ⟨C * cNL L, mul_nonneg hC (cNL_nonneg hL), max m₀ 1,
    fun m hm p₀ S _ κ hκ Ug hg0 hgcomm hgderiv Ds vp τ hvp hτ => ?_⟩
  refine (h m (le_trans (le_max_left _ _) hm) p₀ S hκ Ug hg0 hgcomm hgderiv Ds hvp hτ).trans ?_
  have hb := basis_N_arith_stop hL (le_trans (le_max_right _ _) hm) hτ
  have e1 : C * FSSpin.XiS Ds ^ 2 * ((1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 / vp) =
      C * (FSSpin.XiS Ds ^ 2 / vp) * ((1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3) := by
    ring
  rw [e1]
  refine (scale_N' hC (div_nonneg (sq_nonneg _) hvp.le) hb).trans (le_of_eq ?_)
  ring

end Grid

end KineticLog
