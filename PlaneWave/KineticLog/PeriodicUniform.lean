import PlaneWave.KineticLog.GalerkinSpin
import PlaneWave.KineticLog.GridSpin

/-!
# Logarithmic kinetic bound, part 32: the periodic endpoints with the constants first

In `thm:kinetic-log` and `cor:stopping-log` the constants `C, K₀` precede the measured register
`p` and, with finite internal spin, serve every finite spin set. The endpoints of
`GalerkinEndpoint`, `GridEndpoint`, `GalerkinSpin` and `GridSpin` take the measured particle, and
the spin set, before the constants (their proofs use the same constants for all of them). This file
states the endpoints with the constants first:

* `exists_const_forall_fin`: constants chosen for each element of a finite type, monotone in the
  constant, give one constant (their sum) and one threshold (their maximum) for all;
* **`thm_kinetic_log_galerkin_all`**, **`cor_stopping_log_galerkin_all`**,
  **`thm_kinetic_log_grid_all`**, **`cor_stopping_log_grid_all`**:
  `∃ C ≥ 0, ∃ N₀, ∀ n ≥ N₀, ∀ p₀, …`;
* **`kinetic_retained_galerkin_spin_all`**, **`thm_kinetic_log_galerkin_spin_all`**,
  **`cor_stopping_log_galerkin_spin_all`**, **`thm_kinetic_log_grid_spin_all`**,
  **`cor_stopping_log_grid_spin_all`**: `∃ C ≥ 0, ∃ N₀, ∀ n ≥ N₀, ∀ p₀, ∀ S finite, …` with the
  spin-summed data norm `Ξ_S`; one constant for every finite spin set, so there is no
  spin-dimension factor.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal FSGalerkin

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **One constant for a finite family**: if for every `p` of a finite type there are `C_p ≥ 0` and
`N_p` with `R C_p n p` for `n ≥ N_p`, and `R` is monotone in the constant, then `C = Σ_p C_p` and
`N₀ = max_p N_p` serve every `p`. -/
lemma exists_const_forall_fin {ι : Type*} [Fintype ι] {R : ℝ → ℕ → ι → Prop}
    (hmono : ∀ (C C' : ℝ) (n : ℕ) (p : ι), C ≤ C' → R C n p → R C' n p)
    (h : ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → R C n p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ p, R C n p := by
  classical
  choose C hC N₀ hN using h
  refine ⟨∑ p, C p, Finset.sum_nonneg fun p _ => hC p, Finset.univ.sup N₀, fun n hn p => ?_⟩
  have hp : N₀ p ≤ n := le_trans (Finset.le_sup (Finset.mem_univ p)) hn
  exact hmono _ _ n p (Finset.single_le_sum (fun q _ => hC q) (Finset.mem_univ p)) (hN p n hp)

/-- `C X Q/K³` is monotone in `C` for `X, Q, K ≥ 0`. -/
lemma mono_div_cube {C C' X Q K : ℝ} (hCC' : C ≤ C') (hX : 0 ≤ X) (hQ : 0 ≤ Q) (hK : 0 ≤ K) :
    C * X * Q / K ^ 3 ≤ C' * X * Q / K ^ 3 := by
  apply div_le_div_of_nonneg_right _ (pow_nonneg hK 3)
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right hCC' (mul_nonneg hX hQ)

/-- `C X/v Q/K³` is monotone in `C` for `X, Q, K ≥ 0`, `v > 0`. -/
lemma mono_div_cube' {C C' X v Q K : ℝ} (hCC' : C ≤ C') (hX : 0 ≤ X) (hv : 0 < v) (hQ : 0 ≤ Q)
    (hK : 0 ≤ K) : C * X / v * Q / K ^ 3 ≤ C' * X / v * Q / K ^ 3 := by
  have e : ∀ c : ℝ, c * X / v * Q / K ^ 3 = c * (X / v) * Q / K ^ 3 := fun c => by ring
  rw [e, e]
  exact mono_div_cube hCC' (div_nonneg hX hv.le) hQ hK

section Galerkin

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hL in
lemma Kc_nonneg' (n : ℕ) : 0 ≤ Kc L n := by
  change 0 ≤ gF L * n
  exact mul_nonneg (gF_pos hL).le (Nat.cast_nonneg n)

include hL in
lemma logQ_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ 1 + t + Real.log (2 + Kc L n) := by
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Kc L n by linarith [Kc_nonneg' hL n])
  linarith

include hL in
lemma logQ'_nonneg (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ 1 + (1 + Real.log (2 + Kc L n)) / τ := by
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + Kc L n by linarith [Kc_nonneg' hL n])
  have : 0 ≤ (1 + Real.log (2 + Kc L n)) / τ := div_nonneg (by linarith) hτ.le
  linarith

include hL hKernel in
/-- **`thm:kinetic-log`, Galerkin case, constants first**: there are `C ≥ 0` and `N₀` such that
for every cutoff `n ≥ N₀`, every measured particle `p₀`, every datum and every `t ≥ 0`,
`|⟨ψ(t), T_{p₀} ψ(t)⟩ - ⟨ψ_N(t), T_{p₀} ψ_N(t)⟩| ≤ C 𝒟² [1 + t + log(2 + K)]/K³`. -/
theorem thm_kinetic_log_galerkin_all (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (D : EvoData L H) (t : ℝ),
      0 ≤ t →
      |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
          (regKin sys (gF L) p₀).expect (emb eta n (retFlow sys L n (zero_isSymmetric (n := n))
            (-t) (ext eta n (Sm eta L D.u₀))))| ≤
        C * D.Xi ^ 2 * (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := by
  refine exists_const_forall_fin ?_
    (fun p₀ => thm_kinetic_log_galerkin sys hL H hKernel Hunit hPeriodic p₀)
  intro C C' n p hCC' h D t ht
  exact (h D t ht).trans (mono_div_cube hCC' (sq_nonneg _) (logQ_nonneg hL n ht)
    (Kc_nonneg' hL n))

include hL hKernel in
/-- **`cor:stopping-log`, Galerkin case, constants first**: for every cutoff `n ≥ N₀`, every
measured particle, every datum, every window `[0, τ]`, `τ > 0`, and every `v_p > 0`, the signed
secants differ by at most `(C 𝒟²/v_p) [1 + (1 + log(2 + K))/τ]/K³`. -/
theorem cor_stopping_log_galerkin_all (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (D : EvoData L H) {vp τ : ℝ},
      0 < vp → 0 < τ →
      let ψN : ℝ → L2 eta := fun s =>
        emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-s) (ext eta n (Sm eta L D.u₀)))
      |((regKin sys (gF L) p₀).expect (D.U τ (Sm eta L D.u₀)) -
            (regKin sys (gF L) p₀).expect (D.U 0 (Sm eta L D.u₀))) / (vp * τ) -
          ((regKin sys (gF L) p₀).expect (ψN τ) - (regKin sys (gF L) p₀).expect (ψN 0)) /
            (vp * τ)| ≤
        C * D.Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 := by
  refine exists_const_forall_fin ?_
    (fun p₀ => cor_stopping_log_galerkin sys hL H hKernel Hunit hPeriodic p₀)
  intro C C' n p hCC' h D vp τ hvp hτ
  exact (h D hvp hτ).trans (mono_div_cube' hCC' (sq_nonneg _) hvp (logQ'_nonneg hL n hτ)
    (Kc_nonneg' hL n))

include hL hKernel in
/-- **`eq:kinetic-retained-galerkin` with spin, constants first**: one constant and one cutoff
threshold for every finite spin set `S`:
`‖(P ⊗ 1) Ψ(t) - Ψ_N(t)‖ ≤ C Ξ_S [1 + t + log(2 + K)]/K³`. -/
theorem kinetic_retained_galerkin_spin_all (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (S : Type) [Fintype S]
      (Ds : S → EvoData L H) (t : ℝ), 0 ≤ t →
      Real.sqrt (∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - FSSpin.galS sys n Ds t σ‖ ^ 2)
        ≤ C * FSSpin.XiS Ds * ((1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3) := by
  obtain ⟨C, hC, N₀, h⟩ := kinetic_retained_galerkin sys hL H hKernel Hunit hPeriodic
  refine ⟨C, hC, N₀, fun n hn S _ Ds t ht => ?_⟩
  set r := (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 with hr
  have hr0 : 0 ≤ r := div_nonneg (logQ_nonneg hL n ht) (pow_nonneg (Kc_nonneg' hL n) 3)
  have hσ : ∀ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - FSSpin.galS sys n Ds t σ‖ ≤
      C * r * (Ds σ).Xi := fun σ => by
    have := h n hn (Ds σ) t ht
    calc _ ≤ C * (Ds σ).Xi * (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := this
      _ = C * r * (Ds σ).Xi := by rw [hr]; ring
  have hsq : ∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - FSSpin.galS sys n Ds t σ‖ ^ 2 ≤
      (C * r * FSSpin.XiS Ds) ^ 2 := by
    calc ∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) - FSSpin.galS sys n Ds t σ‖ ^ 2
        ≤ ∑ σ, (C * r) ^ 2 * (Ds σ).Xi ^ 2 := Finset.sum_le_sum fun σ _ => by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hσ σ) 2
      _ = (C * r) ^ 2 * ∑ σ, (Ds σ).Xi ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (C * r) ^ 2 * FSSpin.XiS Ds ^ 2 :=
          mul_le_mul_of_nonneg_left (FSSpin.sum_Xi_sq_le Ds) (sq_nonneg _)
      _ = (C * r * FSSpin.XiS Ds) ^ 2 := by ring
  calc Real.sqrt (∑ σ, ‖molecularH2Truncate n (FSSpin.exactS Ds t σ) -
        FSSpin.galS sys n Ds t σ‖ ^ 2) ≤ Real.sqrt ((C * r * FSSpin.XiS Ds) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = C * r * FSSpin.XiS Ds := Real.sqrt_sq (by have := FSSpin.XiS_nonneg Ds; positivity)
    _ = C * FSSpin.XiS Ds * r := by ring

include hL hKernel in
/-- **`thm:kinetic-log`, Galerkin case with spin, constants first**: one constant and one cutoff
threshold for every measured particle and every finite spin set:
`|⟨Ψ(t), (T_{p₀} ⊗ 1) Ψ(t)⟩ - ⟨Ψ_N(t), (T_{p₀} ⊗ 1) Ψ_N(t)⟩| ≤ C Ξ_S² [1 + t + log(2+K)]/K³`. -/
theorem thm_kinetic_log_galerkin_spin_all (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (S : Type) [Fintype S]
      (Ds : S → EvoData L H) (t : ℝ), 0 ≤ t →
      |FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds t) -
          FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds t)| ≤
        C * FSSpin.XiS Ds ^ 2 * ((1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3) := by
  obtain ⟨C, hC, N₀, h⟩ := thm_kinetic_log_galerkin_all sys hL H hKernel Hunit hPeriodic
  refine ⟨C, hC, N₀, fun n hn p₀ S _ Ds t ht => ?_⟩
  have hr : 0 ≤ (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 :=
    div_nonneg (logQ_nonneg hL n ht) (pow_nonneg (Kc_nonneg' hL n) 3)
  rw [FSSpin.expectS_sub]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h n hn p₀ (Ds σ) t ht
  calc _ ≤ C * (Ds σ).Xi ^ 2 * (1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + t + Real.log (2 + Kc L n)) / Kc L n ^ 3) := by ring

include hL hKernel in
/-- **`cor:stopping-log`, Galerkin case with spin, constants first**: one constant and one cutoff
threshold for every measured particle and every finite spin set; the spin-inclusive signed
secants differ by at most `(C Ξ_S²/v_p) [1 + (1 + log(2 + K))/τ]/K³`. -/
theorem cor_stopping_log_galerkin_spin_all (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ (p₀ : Fin eta) (S : Type) [Fintype S]
      (Ds : S → EvoData L H) {vp τ : ℝ}, 0 < vp → 0 < τ →
        |(FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds τ) -
              FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds 0)) / (vp * τ) -
            (FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds τ) -
              FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds 0)) / (vp * τ)| ≤
          C * FSSpin.XiS Ds ^ 2 * ((1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 / vp) := by
  obtain ⟨C, hC, N₀, h⟩ := cor_stopping_log_galerkin_all sys hL H hKernel Hunit hPeriodic
  refine ⟨C, hC, N₀, fun n hn p₀ S _ Ds vp τ hvp hτ => ?_⟩
  have hr : 0 ≤ (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 / vp :=
    div_nonneg (div_nonneg (logQ'_nonneg hL n hτ) (pow_nonneg (Kc_nonneg' hL n) 3)) hvp.le
  have e : (FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds τ) -
        FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds 0)) / (vp * τ) -
      (FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds τ) -
        FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.galS sys n Ds 0)) / (vp * τ) =
      ∑ σ, (((regKin sys (gF L) p₀).expect (FSSpin.exactS Ds τ σ) -
          (regKin sys (gF L) p₀).expect (FSSpin.exactS Ds 0 σ)) / (vp * τ) -
        ((regKin sys (gF L) p₀).expect (FSSpin.galS sys n Ds τ σ) -
          (regKin sys (gF L) p₀).expect (FSSpin.galS sys n Ds 0 σ)) / (vp * τ)) := by
    simp only [FSSpin.expectS, ← Finset.sum_sub_distrib, Finset.sum_div]
  rw [e]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h n hn p₀ (Ds σ) hvp hτ
  calc _ ≤ C * (Ds σ).Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + (1 + Real.log (2 + Kc L n)) / τ) / Kc L n ^ 3 / vp) := by ring

end Galerkin

section Grid

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **`thm:kinetic-log`, grid case, constants first**: there are `C ≥ 0` and `m₀` such that for
every register radius `2m` with `m ≥ m₀`, every measured particle `p₀`, every kernel of the class
`IsGridKernel`, every grid propagator, every datum and every `t ≥ 0`,
`|⟨ψ(t), T_{p₀} ψ(t)⟩ - ⟨ψ_g(t), T_{p₀} ψ_g(t)⟩| ≤ C 𝒟² [1 + t + log(2 + K)]/K³`. -/
theorem thm_kinetic_log_grid_all :
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
            C * D.Xi ^ 2 * (1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3 := by
  refine exists_const_forall_fin ?_
    (fun p₀ => thm_kinetic_log_grid sys H hKernel Hunit hL hPeriodic p₀)
  intro C C' m p hCC' h κ hκ Ug hg0 hgcomm hgderiv D t ht
  exact (h hκ Ug hg0 hgcomm hgderiv D t ht).trans (mono_div_cube hCC' (sq_nonneg _)
    (logQ_nonneg hL m ht) (Kc_nonneg' hL m))

include hKernel hL hPeriodic in
/-- **`cor:stopping-log`, grid case, constants first**: one constant and one threshold for every
measured particle, kernel of the class, grid propagator, datum, window `[0, τ]`, `τ > 0`, and
`v_p > 0`. -/
theorem cor_stopping_log_grid_all :
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
            C * D.Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 := by
  refine exists_const_forall_fin ?_
    (fun p₀ => cor_stopping_log_grid sys H hKernel Hunit hL hPeriodic p₀)
  intro C C' m p hCC' h κ hκ Ug hg0 hgcomm hgderiv D vp τ hvp hτ
  exact (h hκ Ug hg0 hgcomm hgderiv D hvp hτ).trans (mono_div_cube' hCC' (sq_nonneg _) hvp
    (logQ'_nonneg hL m hτ) (Kc_nonneg' hL m))

include hKernel hL hPeriodic in
/-- **`thm:kinetic-log`, grid case with spin, constants first**: one constant and one threshold
for every measured particle, every finite spin set, every kernel of the class and every grid
propagator:
`|⟨Ψ(t), (T_{p₀} ⊗ 1) Ψ(t)⟩ - ⟨Ψ_g(t), (T_{p₀} ⊗ 1) Ψ_g(t)⟩| ≤ C Ξ_S² [1 + t + log(2+K)]/K³`. -/
theorem thm_kinetic_log_grid_spin_all :
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
            C * FSSpin.XiS Ds ^ 2 * ((1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3) := by
  obtain ⟨C, hC, m₀, h⟩ := thm_kinetic_log_grid_all sys H hKernel Hunit hL hPeriodic
  refine ⟨C, hC, m₀, fun m hm p₀ S _ κ hκ Ug hg0 hgcomm hgderiv Ds t ht => ?_⟩
  have hr : 0 ≤ (1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3 :=
    div_nonneg (logQ_nonneg hL m ht) (pow_nonneg (Kc_nonneg' hL m) 3)
  have e : FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds t) -
      regExpectS sys (gF L) p₀ (gridS m Ug Ds t) =
      ∑ σ, ((regKin sys (gF L) p₀).expect (FSSpin.exactS Ds t σ) -
        regExpect sys (gF L) p₀ (gridS m Ug Ds t σ)) := by
    simp only [FSSpin.expectS, regExpectS, Finset.sum_sub_distrib]
  rw [e]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h m hm p₀ hκ Ug hg0 hgcomm hgderiv (Ds σ) t ht
  calc _ ≤ C * (Ds σ).Xi ^ 2 * (1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + t + Real.log (2 + Kc L m)) / Kc L m ^ 3) := by ring

include hKernel hL hPeriodic in
/-- **`cor:stopping-log`, grid case with spin, constants first**: one constant and one threshold
for every measured particle, every finite spin set, every kernel of the class, every grid
propagator, every window `[0, τ]`, `τ > 0`, and every `v_p > 0`. -/
theorem cor_stopping_log_grid_spin_all :
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
            C * FSSpin.XiS Ds ^ 2 * ((1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 / vp) := by
  obtain ⟨C, hC, m₀, h⟩ := cor_stopping_log_grid_all sys H hKernel Hunit hL hPeriodic
  refine ⟨C, hC, m₀, fun m hm p₀ S _ κ hκ Ug hg0 hgcomm hgderiv Ds vp τ hvp hτ => ?_⟩
  have hr : 0 ≤ (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 / vp :=
    div_nonneg (div_nonneg (logQ'_nonneg hL m hτ) (pow_nonneg (Kc_nonneg' hL m) 3)) hvp.le
  have e : (FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds τ) -
        FSSpin.expectS (regKin sys (gF L) p₀) (FSSpin.exactS Ds 0)) / (vp * τ) -
      (regExpectS sys (gF L) p₀ (gridS m Ug Ds τ) -
        regExpectS sys (gF L) p₀ (gridS m Ug Ds 0)) / (vp * τ) =
      ∑ σ, (((regKin sys (gF L) p₀).expect (FSSpin.exactS Ds τ σ) -
          (regKin sys (gF L) p₀).expect (FSSpin.exactS Ds 0 σ)) / (vp * τ) -
        (regExpect sys (gF L) p₀ (gridS m Ug Ds τ σ) -
          regExpect sys (gF L) p₀ (gridS m Ug Ds 0 σ)) / (vp * τ)) := by
    simp only [FSSpin.expectS, regExpectS, ← Finset.sum_sub_distrib, Finset.sum_div]
  rw [e]
  refine FSSpin.abs_sum_le Ds hC hr fun σ => ?_
  have := h m hm p₀ hκ Ug hg0 hgcomm hgderiv (Ds σ) hvp hτ
  calc _ ≤ C * (Ds σ).Xi ^ 2 / vp * (1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 := this
    _ = C * (Ds σ).Xi ^ 2 * ((1 + (1 + Real.log (2 + Kc L m)) / τ) / Kc L m ^ 3 / vp) := by ring

end Grid

end KineticLog
