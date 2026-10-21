import PlaneWave.Observable.ThirdOrderSamePair

/-!
# The flux and source theorems on the spin-inclusive space

`thm:flux`, `thm:flux2`, `thm:flux3`, `thm:src1`, `thm:src3` and `cor:stopping3` for spin-valued
states. The manuscript states these results with all norms including the spin sum
(eq:spin-sobolev): the Hamiltonian, the projector `P`, the observable `A_{p₀}` and the force
operator act as the identity on spin. A spin-inclusive state is therefore a family
`Ψ = (Ψ_σ)_{σ ∈ S}` over a finite set `S` of spin configurations (`S = Fin η → Fin 2` for
electrons, `S = Fin η → Fin D` in the release's `CoulombSpinL2 η D`), every quantity in the
theorems is the sum of its spin components, and the data norm is
`Ξ_S = ‖Ψ₀‖ + ‖HΨ₀‖ + ‖H²Ψ₀‖` with the norms of `ℓ²(S; ℓ²)` (`XiS`, `XiS_eq_norm`).

A spin-inclusive datum is a family `Ds : S → EvoData L H`. The theorems hold for every family;
the physical case is the one in which all members share one propagator (`spinFamily`), so that
`Ψ(t) = (U(t) ⊗ 1) Ψ₀` (`exactS_spinFamily`).

The proofs apply the scalar theorems componentwise and use Minkowski's inequality in `ℓ²(S)`,
`Σ_σ Ξ_σ² ≤ Ξ_S²` (`sum_Xi_sq_le`). The constants are those of the scalar theorems; there is no
factor depending on the number of spin configurations. The completion hypotheses of `thm:src3`
and `cor:stopping3` concern operators `Σ₃`, `R₃` on the spatial cube space and are unchanged: on
the spin-inclusive space the generator and the residual are the spin-diagonal `Σ₃ ⊗ 1` and
`R₃ ⊗ 1`, as the spin-independence of the Hamiltonian makes natural.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin

namespace FSSpin

open FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν] {S : Type} [Fintype S]

/-! ## Spin-inclusive data and states -/

section Data

variable {L : ℝ} {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}

/-- The spin-inclusive datum with a common propagator: the components `u σ` (`H u σ = S v σ`)
evolved with the propagator of `D`. -/
def spinFamily (D : EvoData L H) (u v : S → MolecularFourierH2 eta)
    (huv : ∀ σ, H (u σ) = Sm eta L (v σ)) : S → EvoData L H :=
  fun σ => { D with u₀ := u σ, v₀ := v σ, uv := huv σ }

/-- The spin-inclusive exact state `Ψ(t) = (U(t) ⊗ 1) Ψ₀`. -/
noncomputable def exactS (Ds : S → EvoData L H) (t : ℝ) : S → L2 eta :=
  fun σ => (Ds σ).U t (Sm eta L (Ds σ).u₀)

omit [Fintype S] in
lemma exactS_spinFamily (D : EvoData L H) (u v : S → MolecularFourierH2 eta)
    (huv : ∀ σ, H (u σ) = Sm eta L (v σ)) (t : ℝ) (σ : S) :
    exactS (spinFamily D u v huv) t σ = D.U t (Sm eta L (u σ)) := rfl

/-- The spin-inclusive data norm `Ξ_S = ‖S Ψ₀‖ + ‖H Ψ₀‖ + ‖H Φ₀‖` (`H Ψ₀ = S Φ₀`), with the norms
of `ℓ²(S; ℓ²)`. -/
noncomputable def XiS (Ds : S → EvoData L H) : ℝ :=
  Real.sqrt (∑ σ, ‖Sm eta L (Ds σ).u₀‖ ^ 2) + Real.sqrt (∑ σ, ‖H (Ds σ).u₀‖ ^ 2) +
    Real.sqrt (∑ σ, ‖H (Ds σ).v₀‖ ^ 2)

/-- `Ξ_S` in terms of the norms of the spin-inclusive space `PiLp 2 (S → ℓ²)`. -/
lemma XiS_eq_norm (Ds : S → EvoData L H) :
    XiS Ds = ‖(WithLp.toLp 2 (fun σ => Sm eta L (Ds σ).u₀) : PiLp 2 (fun _ : S => L2 eta))‖ +
      ‖(WithLp.toLp 2 (fun σ => H (Ds σ).u₀) : PiLp 2 (fun _ : S => L2 eta))‖ +
      ‖(WithLp.toLp 2 (fun σ => H (Ds σ).v₀) : PiLp 2 (fun _ : S => L2 eta))‖ := by
  simp only [XiS, PiLp.norm_eq_of_L2]

lemma XiS_nonneg (Ds : S → EvoData L H) : 0 ≤ XiS Ds := by unfold XiS; positivity

/-- **Minkowski in `ℓ²(S)`**: `Σ_σ Ξ_σ² ≤ Ξ_S²`. -/
lemma sum_Xi_sq_le (Ds : S → EvoData L H) : ∑ σ, (Ds σ).Xi ^ 2 ≤ XiS Ds ^ 2 := by
  have h1 := PlaneWaveSpin.sqrt_sum_sq_add_le
    (fun σ => ‖Sm eta L (Ds σ).u₀‖ + ‖H (Ds σ).u₀‖) (fun σ => ‖H (Ds σ).v₀‖)
  have h2 := PlaneWaveSpin.sqrt_sum_sq_add_le
    (fun σ => ‖Sm eta L (Ds σ).u₀‖) (fun σ => ‖H (Ds σ).u₀‖)
  have hX : Real.sqrt (∑ σ, (Ds σ).Xi ^ 2) ≤ XiS Ds := by
    have e : ∑ σ, (Ds σ).Xi ^ 2 =
        ∑ σ, (‖Sm eta L (Ds σ).u₀‖ + ‖H (Ds σ).u₀‖ + ‖H (Ds σ).v₀‖) ^ 2 := rfl
    rw [e]
    refine h1.trans ?_
    unfold XiS
    linarith
  exact (Real.sqrt_le_left (XiS_nonneg Ds)).1 hX

/-- Componentwise bounds `g σ ≤ C Ξ_σ² r` sum to `C Ξ_S² r`. -/
lemma sum_le_of_le (Ds : S → EvoData L H) {g : S → ℝ} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (h : ∀ σ, g σ ≤ C * (Ds σ).Xi ^ 2 * r) : ∑ σ, g σ ≤ C * XiS Ds ^ 2 * r := by
  calc ∑ σ, g σ ≤ ∑ σ, C * (Ds σ).Xi ^ 2 * r := Finset.sum_le_sum fun σ _ => h σ
    _ = C * (∑ σ, (Ds σ).Xi ^ 2) * r := by rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ C * XiS Ds ^ 2 * r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sum_Xi_sq_le Ds) hC) hr

/-- Componentwise bounds `|f σ| ≤ C Ξ_σ² r` give `|Σ_σ f σ| ≤ C Ξ_S² r`. -/
lemma abs_sum_le (Ds : S → EvoData L H) {f : S → ℝ} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (h : ∀ σ, |f σ| ≤ C * (Ds σ).Xi ^ 2 * r) : |∑ σ, f σ| ≤ C * XiS Ds ^ 2 * r :=
  (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_of_le Ds hC hr h)

end Data

/-! ## Spin-inclusive flux and kinetic quantities -/

section Defs

variable {L : ℝ} {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}

variable (H) in
/-- The `H²` coordinates of the spin-inclusive exact state: `S (trajS H Ds s σ) = U(s) S u₀σ`. -/
noncomputable def trajS (Ds : S → EvoData L H) (s : ℝ) : S → MolecularFourierH2 eta :=
  fun σ => FSFlux.traj H (Ds σ) s

/-- The spin-inclusive projector `P ⊗ 1`. -/
noncomputable def truncS (n : ℕ) (Ψ : S → MolecularFourierH2 eta) : S → MolecularFourierH2 eta :=
  fun σ => molecularH2Truncate n (Ψ σ)

variable (L H) in
/-- The spin-inclusive force form `𝔊_S(Ψ, Φ) = Σ_σ 𝔊(Ψ_σ, Φ_σ)` (the force operator `i[W, A]` acts
as the identity on spin). -/
noncomputable def GfS (sys : CoulombSystem eta ν) (p₀ : Fin eta) (Ψ Φ : S → MolecularFourierH2 eta) :
    ℂ :=
  ∑ σ, FSFlux.Gf sys L H p₀ (Ψ σ) (Φ σ)

/-- The spin-inclusive Galerkin state `Ψ_N(t) = e^{-itH_N} P Ψ₀`. -/
noncomputable def galS (sys : CoulombSystem eta ν) (n : ℕ) (Ds : S → EvoData L H) (t : ℝ) :
    S → L2 eta :=
  fun σ => emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L (Ds σ).u₀)))

/-- The expectation of `μ ⊗ 1` in a spin-inclusive state: `⟨Ψ, (μ ⊗ 1) Ψ⟩ = Σ_σ ⟨Ψ_σ, μ Ψ_σ⟩`. -/
noncomputable def expectS {sys : CoulombSystem eta ν} {g : ℝ} (μ : KinMult sys g) (Ψ : S → L2 eta) :
    ℝ :=
  ∑ σ, μ.expect (Ψ σ)

omit [Fintype ν] in
lemma expectS_sub {sys : CoulombSystem eta ν} {g : ℝ} (μ : KinMult sys g) (Ψ Φ : S → L2 eta) :
    expectS μ Ψ - expectS μ Φ = ∑ σ, (μ.expect (Ψ σ) - μ.expect (Φ σ)) := by
  simp only [expectS, Finset.sum_sub_distrib]

end Defs

/-! ## The flux theorems -/

section Flux

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta)

include hKernel hL in
/-- The spin-inclusive flux integral is the sum of the component integrals (each integrand is
continuous). -/
lemma integral_GfS (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (n : ℕ)
    (Ds : S → EvoData L H) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, ((GfS L H sys p₀ (trajS H Ds s) (trajS H Ds s)).re -
        (GfS L H sys p₀ (truncS n (trajS H Ds s)) (truncS n (trajS H Ds s))).re) =
      ∑ σ, ∫ s in (0 : ℝ)..t,
        ((FSFlux.Gf sys L H p₀ (FSFlux.traj H (Ds σ) s) (FSFlux.traj H (Ds σ) s)).re -
          (FSFlux.Gf sys L H p₀ (molecularH2Truncate n (FSFlux.traj H (Ds σ) s))
            (molecularH2Truncate n (FSFlux.traj H (Ds σ) s))).re) := by
  simp only [GfS, trajS, truncS, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine intervalIntegral.integral_finsetSum fun σ _ => ?_
  have hct := FSFlux.continuous_traj sys hL H hKernel Hunit hPeriodic (Ds σ)
  have hP := (FSFlux.continuous_trunc n).comp hct
  exact ((Complex.continuous_re.comp (FSFlux.continuous_Gf sys H p₀ hct hct)).sub
    (Complex.continuous_re.comp (FSFlux.continuous_Gf sys H p₀ hP hP))).intervalIntegrable 0 t

include hKernel hL in
/-- **`thm:flux` with spin**: for the spin-inclusive state, with `δ = (1 - P)Ψ`,
eq:flux-nc `|𝔊(δ, δ)| + 2 |𝔊(δ, 1_{>K/2} PΨ)| ≤ C Ξ_S² K^{-2}` and
eq:flux-bd `|𝔊(Ψ, Ψ) - 𝔊(PΨ, PΨ)| ≤ C Ξ_S² K^{-1}`, with the constant of `FSFlux.thm_flux`. -/
theorem thm_flux_spin (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → 2 ≤ Kc L n → ∀ (Ds : S → EvoData L H) (s : ℝ),
      ‖GfS L H sys p₀ (trajS H Ds s - truncS n (trajS H Ds s))
            (trajS H Ds s - truncS n (trajS H Ds s))‖ +
          2 * ‖GfS L H sys p₀ (trajS H Ds s - truncS n (trajS H Ds s))
            (fun σ => FSFlux.hotA L n (trajS H Ds s σ))‖ ≤
        C * XiS Ds ^ 2 * Kc L n ^ (-(2 : ℝ)) ∧
      |(GfS L H sys p₀ (trajS H Ds s) (trajS H Ds s)).re -
          (GfS L H sys p₀ (truncS n (trajS H Ds s)) (truncS n (trajS H Ds s))).re| ≤
        C * XiS Ds ^ 2 * Kc L n ^ (-(1 : ℝ)) := by
  obtain ⟨C, hC, h⟩ := FSFlux.thm_flux sys hL H hKernel p₀ Hunit hPeriodic
  refine ⟨C, hC, fun n hn hK Ds s => ⟨?_, ?_⟩⟩
  · have hr : 0 ≤ Kc L n ^ (-(2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    refine le_trans ?_ (sum_le_of_le Ds hC hr fun σ => (h n hn hK (Ds σ) s).1)
    simp only [GfS, trajS, truncS, Pi.sub_apply]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    exact add_le_add (norm_sum_le _ _) (mul_le_mul_of_nonneg_left (norm_sum_le _ _) zero_le_two)
  · have hr : 0 ≤ Kc L n ^ (-(1 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have e : (GfS L H sys p₀ (trajS H Ds s) (trajS H Ds s)).re -
        (GfS L H sys p₀ (truncS n (trajS H Ds s)) (truncS n (trajS H Ds s))).re =
        ∑ σ, ((FSFlux.Gf sys L H p₀ (FSFlux.traj H (Ds σ) s) (FSFlux.traj H (Ds σ) s)).re -
          (FSFlux.Gf sys L H p₀ (molecularH2Truncate n (FSFlux.traj H (Ds σ) s))
            (molecularH2Truncate n (FSFlux.traj H (Ds σ) s))).re) := by
      simp only [GfS, trajS, truncS, Complex.re_sum, Finset.sum_sub_distrib]
    rw [e]
    exact abs_sum_le Ds hC hr fun σ => (h n hn hK (Ds σ) s).2

include hKernel hL in
/-- **`thm:flux2` with spin** (eq:flux2): for `0 < ε ≤ 1/4`,
`|∫₀ᵗ (𝔊(Ψ, Ψ) - 𝔊(PΨ, PΨ))| ≤ C Ξ_S² (K^{-3} + t K^{-2+4ε})` for every spin-inclusive datum,
with the constant of `FSFlux.thm_flux2`. -/
theorem thm_flux2_spin (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 2 ≤ n → 4 ≤ Kc L n → ∀ (Ds : S → EvoData L H) {t : ℝ}, 0 ≤ t →
      |∫ s in (0 : ℝ)..t, ((GfS L H sys p₀ (trajS H Ds s) (trajS H Ds s)).re -
          (GfS L H sys p₀ (truncS n (trajS H Ds s)) (truncS n (trajS H Ds s))).re)| ≤
        C * XiS Ds ^ 2 * (Kc L n ^ (-(3 : ℝ)) + t * Kc L n ^ (-2 + 4 * ε)) := by
  obtain ⟨C, hC, h⟩ := FSFlux.thm_flux2 sys hL H hKernel p₀ Hunit hPeriodic hε hε1
  refine ⟨C, hC, fun n hn hK Ds t ht => ?_⟩
  rw [integral_GfS sys hL H hKernel p₀ Hunit hPeriodic n Ds t]
  have hK0 : 0 ≤ Kc L n := by linarith
  exact abs_sum_le Ds hC
    (add_nonneg (Real.rpow_nonneg hK0 _) (mul_nonneg ht (Real.rpow_nonneg hK0 _)))
    fun σ => h n hn hK (Ds σ) ht

include hKernel hL in
/-- **`thm:flux3` with spin**: for every `ε > 0`,
`|∫₀ᵗ (𝔊(Ψ, Ψ) - 𝔊(PΨ, PΨ))| ≤ C_ε Ξ_S² (K^{-3+ε} + t K^{-3+ε})` for every spin-inclusive datum,
with the constant of `FSFlux.thm_flux3`. -/
theorem thm_flux3_spin (heta : 0 < eta) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 64 ≤ n → 1 ≤ gF L * (FSFlux.cst sys * n) →
      ∀ (Ds : S → EvoData L H) {t : ℝ}, 0 ≤ t →
      |∫ s in (0 : ℝ)..t, ((GfS L H sys p₀ (trajS H Ds s) (trajS H Ds s)).re -
          (GfS L H sys p₀ (truncS n (trajS H Ds s)) (truncS n (trajS H Ds s))).re)| ≤
        C * XiS Ds ^ 2 * (Kc L n ^ (-3 + ε) + t * Kc L n ^ (-3 + ε)) := by
  obtain ⟨C, hC, h⟩ := FSFlux.thm_flux3 heta hL H hKernel p₀ Hunit hPeriodic hε
  refine ⟨C, hC, fun n hn hl Ds t ht => ?_⟩
  rw [integral_GfS sys hL H hKernel p₀ Hunit hPeriodic n Ds t]
  have hK0 : 0 ≤ Kc L n := by
    rw [FSNormal.Kc_eq]; exact mul_nonneg (gF_pos hL).le n.cast_nonneg
  exact abs_sum_le Ds hC
    (add_nonneg (Real.rpow_nonneg hK0 _) (mul_nonneg ht (Real.rpow_nonneg hK0 _)))
    fun σ => h n hn hl (Ds σ) ht

end Flux

/-! ## The source theorems -/

section Source

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel hL in
/-- **`thm:src1` with spin**: `|⟨Ψ(t), A_{p₀} Ψ(t)⟩ - ⟨Ψ_N(t), A_{p₀} Ψ_N(t)⟩| ≤
C Ξ_S² (K^{-3} + t K^{-2})` for every spin-inclusive datum, every `t ≥ 0` and every cutoff with
`K ≥ 1`, with the constant of `FSSrc1.thm_src1`. -/
theorem thm_src1_spin (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 1 ≤ Kc L n → ∀ (Ds : S → EvoData L H) (t : ℝ), 0 ≤ t →
      |expectS (regKin sys (gF L) p₀) (exactS Ds t) -
          expectS (regKin sys (gF L) p₀) (galS sys n Ds t)| ≤
        C * XiS Ds ^ 2 * (Kc L n ^ (-(3 : ℝ)) + t * Kc L n ^ (-(2 : ℝ))) := by
  obtain ⟨C, hC, h⟩ := FSSrc1.thm_src1 sys hL H hKernel Hunit hPeriodic p₀
  refine ⟨C, hC, fun n hK Ds t ht => ?_⟩
  have hK0 : 0 ≤ Kc L n := by linarith
  rw [expectS_sub]
  exact abs_sum_le Ds hC
    (add_nonneg (Real.rpow_nonneg hK0 _) (mul_nonneg ht (Real.rpow_nonneg hK0 _)))
    fun σ => h n hK (Ds σ) t ht

include hKernel in
/-- **`thm:src3` with spin** (conditional analytic completion): under the completion hypotheses
of `FSAsymp.thm_src3` (on the spatial cube space; spin plays no role in them),
`|⟨Ψ(t), A_{p₀} Ψ(t)⟩ - ⟨Ψ_N(t), A_{p₀} Ψ_N(t)⟩| ≤ C_ε Ξ_S² (1 + t) K^{-3+ε}` for every
spin-inclusive datum and every `t ≥ 1`, with the constant and threshold of `FSAsymp.thm_src3`. -/
theorem thm_src3_spin (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) {ε : ℝ} (hε : 0 < ε) {C3 : ℝ} (hC3 : 0 ≤ C3) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N₀ ≤ n →
      ∀ (S3 R3 : En eta n →L[ℂ] En eta n), S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n) →
      FSConj.cm S3 (Akin sys L n) = -(H3ret sys hL hn H - R3) →
      ‖S3‖ ≤ FSAsymp.z3F L C3 q n →
      (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u →
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤ FSAsymp.betaF L C3 q n * M) →
      (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u → ‖R3 u‖ ≤ FSAsymp.betaF L C3 q n * M) →
      ∀ (Ds : S → EvoData L H) (t : ℝ), 1 ≤ t →
        |expectS (regKin sys (gF L) p₀) (exactS Ds t) -
            expectS (regKin sys (gF L) p₀) (galS sys n Ds t)| ≤
          C * XiS Ds ^ 2 * (1 + t) * Kc L n ^ (-3 + ε) := by
  obtain ⟨C, hC, N₀, h⟩ := FSAsymp.thm_src3 sys hL H hKernel Hunit hPeriodic p₀ hε hC3 q
  refine ⟨C, hC, N₀, fun n hn hN S3 R3 hS3 hA3 hz3 hβ hR3 Ds t ht => ?_⟩
  have hK0 : 0 ≤ Kc L n := by
    rw [FSNormal.Kc_eq]; exact mul_nonneg (gF_pos hL).le n.cast_nonneg
  have hr : 0 ≤ (1 + t) * Kc L n ^ (-3 + ε) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hK0 _)
  rw [expectS_sub]
  refine (abs_sum_le Ds hC hr fun σ => ?_).trans_eq (by ring)
  exact (h n hn hN S3 R3 hS3 hA3 hz3 hβ hR3 (Ds σ) t ht).trans_eq (by ring)

include hKernel in
/-- **`cor:stopping3` with spin** (conditional): under the completion hypotheses of
`FSAsymp.cor_stopping3`, the secant-slope estimator of the stopping power in the spin-inclusive
state deviates from its Galerkin counterpart by at most
`C_ε Ξ_S² / v_p (K^{-3+ε} + K^{-3+ε}/T)` for every `T ≥ 1`, with the constant and threshold of
`FSAsymp.cor_stopping3`. -/
theorem cor_stopping3_spin (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) {ε : ℝ} (hε : 0 < ε) {C3 : ℝ} (hC3 : 0 ≤ C3) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ (n : ℕ) (hn : 2 ≤ n), N₀ ≤ n →
      ∀ (S3 R3 : En eta n →L[ℂ] En eta n), S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n) →
      FSConj.cm S3 (Akin sys L n) = -(H3ret sys hL hn H - R3) →
      ‖S3‖ ≤ FSAsymp.z3F L C3 q n →
      (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u →
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤ FSAsymp.betaF L C3 q n * M) →
      (∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u → ‖R3 u‖ ≤ FSAsymp.betaF L C3 q n * M) →
      ∀ (Ds : S → EvoData L H) {vp T : ℝ}, 0 < vp → 1 ≤ T →
        |(expectS (regKin sys (gF L) p₀) (exactS Ds T) -
              expectS (regKin sys (gF L) p₀) (exactS Ds 0)) / (vp * T) -
            (expectS (regKin sys (gF L) p₀) (galS sys n Ds T) -
              expectS (regKin sys (gF L) p₀) (galS sys n Ds 0)) / (vp * T)| ≤
          C * XiS Ds ^ 2 / vp * (Kc L n ^ (-3 + ε) + Kc L n ^ (-3 + ε) / T) := by
  obtain ⟨C, hC, N₀, h⟩ := FSAsymp.cor_stopping3 sys hL H hKernel Hunit hPeriodic p₀ hε hC3 q
  refine ⟨C, hC, N₀, fun n hn hN S3 R3 hS3 hA3 hz3 hβ hR3 Ds vp T hvp hT => ?_⟩
  have hK0 : 0 ≤ Kc L n := by
    rw [FSNormal.Kc_eq]; exact mul_nonneg (gF_pos hL).le n.cast_nonneg
  have hT0 : 0 < T := by linarith
  have hr : 0 ≤ (Kc L n ^ (-3 + ε) + Kc L n ^ (-3 + ε) / T) / vp :=
    div_nonneg (add_nonneg (Real.rpow_nonneg hK0 _)
      (div_nonneg (Real.rpow_nonneg hK0 _) hT0.le)) hvp.le
  have e : ∀ (a b c d : S → ℝ),
      (∑ σ, a σ - ∑ σ, b σ) / (vp * T) - (∑ σ, c σ - ∑ σ, d σ) / (vp * T) =
        ∑ σ, ((a σ - b σ) / (vp * T) - (c σ - d σ) / (vp * T)) := by
    intro a b c d
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib]
  simp only [expectS]
  rw [e]
  refine (abs_sum_le Ds hC hr fun σ => ?_).trans_eq (by ring)
  have hσ := h n hn hN S3 R3 hS3 hA3 hz3 hβ hR3 (Ds σ) hvp hT
  dsimp only at hσ
  exact hσ.trans_eq (by ring)

end Source

end FSSpin
