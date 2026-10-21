import PlaneWave.FreeBoundary.GridSecondMomentPhysical

/-!
# `L`-uniform grid dynamics, stage 4: the observable error and its rates

The sharp observable bound of `thm:grid-dyn-sharp` for `g_L`
(`PlaneWave.FreeBoundary.GridDynamicsSharp`) with every intermediate constant in physical units:

* **`grid_observable_error_sharp_gLU`**: `|⟪ψ(t), χ(x_a) ψ(t)⟫ - ⟪ψ_g(t), O_g ψ_g(t)⟫|` is at most
  term (I) + term (II) + `2 t B_d`, where `B_d` is the bound of `grid_duality_shell_gLU` at the
  flow shell `τ_φ = m̄² r_g Φ/(g(⌊m/4⌋+1))⁴`; the second moments of the backward flows are
  `X_g ≤ r_g Φ`, `Φ = flow2(1; c_J, A, σ_U; o, W_o, C_χ ‖ψ₀‖)`, with the `L`-free
  `c_J = (4/3)(1 + 4A)`, `A = gLAU`, `σ_U = 2A + 4√79 z`;
* the arithmetic of the rates in physical units: `r_g/(g(⌊m/4⌋+1))⁴ ≤ 3072 K^{-5/2}`
  (`shell_rate_sharpP`) and `Z_c formAP ≤ 18 √8 √79 z K^{-1/2}` (`formAP_rate`), so term (III) pairs
  at `t K⁻³` with an `L`-free constant (`grid_rate_arith_sharpP`).

The rates with the `L`-free constants (`grid_observable_rate_sharp_gLU`) and the final theorems
are in `PlaneWave.FreeBoundary.GridDynamicsUniformTheorem`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics

open PlaneWaveGridG (gLgamma gLgamma_pos gLref gLNucData regParticlesOfG gLzU gLzU_nonneg gLAU
  sobP formAP formAP_nonneg gLGridCoupling)

namespace FreeBoundary

section Grid

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  {θ : ℝ → ℝ} (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 0 < L) {R : ℝ} (hθ : Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hθ hPeriodic in
set_option maxHeartbeats 400000 in
/-- **Observable error on the grid, sharp, physical weight** (`thm:grid-dyn-sharp`, Fourier side,
`L ≥ 2π`). The setting of `grid_observable_error_sharp_gL`: the observable error is at most
`2 δ (C_χ t₁ + τ_χ ‖ψ₀‖ + ‖O‖ δ) + ‖O‖ δ²` (term (I)) `+ C_χ t₁² + τ_χ^∞(m) ‖ψ₀‖²` (term (II))
`+ 2 t B_d` (term (III)), with the bound `B_d` of `grid_duality_shell_gLU` at the flow shell
`τ_φ = m̄² r_g Φ/(g(⌊m/4⌋+1))⁴` (`r_g = (g(4m+1))^{3/2}`). Here `ξ = ‖ψ₀‖ + 4 Ξ₀ + 2 η √Q_g`,
`F = flow2(1; c_J, A, σ_U; ξ, M₀, ‖ψ₀‖)` bounds `X_g(v)/r_g` for `v ∈ {P ψ(t), ψ_g(t)}`,
`o = 8 C_χ F + 8 g⁴ D⁽⁴⁾_χ ‖ψ₀‖`, `W_o = (2 + 12 m̄) C_χ X_b + ((3 + 12 m̄) C_χ + 14 g² D'_χ) ‖ψ₀‖`
and `Φ = flow2(1; c_J, A, σ_U; o, W_o, C_χ ‖ψ₀‖)`; the tail constant is the `L`-free `gLtailMU`. -/
theorem grid_observable_error_sharp_gLU (hC : 0 ≤ gLmassConst sys L (tv R θ) Hunit)
    (hL2 : 2 * Real.pi ≤ L) (hH : 0 ≤ Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ} (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ))
        (gLref L θ (tv R θ)) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hgrid eta m
      (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x))) t)
    (rho₁ rho₂ rho₄ : ℝ) (hK₄ : 1 ≤ (2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ))
    (hRho₁ : 0 ≤ rho₁) (hRhoScale₁ : rho₁ ^ 2 * ((2 * Real.pi / L) * (m : ℝ)) = 1)
    (hRho₂ : 0 ≤ rho₂) (hRhoScale₂ : rho₂ ^ 2 * ((2 * Real.pi / L) * ((2 * m : ℕ) : ℝ)) = 1)
    (hRho₄ : 0 ≤ rho₄) (hRhoScale₄ : rho₄ ^ 2 * ((2 * Real.pi / L) * ((m / 4 : ℕ) : ℝ)) = 1)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (a : Fin eta) (χ : Lattice3 → ℂ) (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (hχ4 : Summable fun ν => nsq ν ^ 2 * ‖χ ν‖)
    (hreal : ∀ ν, χ (-ν) = conj (χ ν)) (k₀ : ℕ) (hk₀ : 2 ≤ k₀)
    (hk₀g : 1 ≤ (2 * Real.pi / L) * k₀) (hk₀2 : (2 * Real.pi / L) * k₀ ≤ 2) {t : ℝ}
    (ht : 0 ≤ t) :
    let g : ℝ := 2 * Real.pi / L
    let b : ℝ := relB_gL sys L (tv R θ) Hunit
    let S0 : ℝ := ‖molecularH2StateMap eta g u₀‖
    let Ξ₀ : ℝ := 2 * ‖H u₀‖ + 2 * b * S0
    let Ξ₁ : ℝ := 2 * ‖H v₀‖ + 2 * b * ‖molecularH2StateMap eta g v₀‖
    let M₀ : ℝ := sys.maxMass * (S0 + 2 * Ξ₀)
    let Ct : ℝ → ℝ := fun M => gLtailMU sys (tv R θ) Hunit M
    let tl : ℝ → ℝ → ℝ := fun K ρ =>
      (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    let s₀ : ℕ := m / 4
    let Zg : ℝ := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        (gLgamma L (tv R θ))
    let CO : ℝ := ‖convOp (eta := eta) a χ‖
    let Cχ : ℝ := ∑' ν, ‖χ ν‖
    let τχ : ℝ := ∑' ν, if g * (m : ℝ) < g * Real.sqrt (latticeNormSq ν) then ‖χ ν‖ else 0
    let cJ : ℝ := gridFlowConstU sys (tv R θ)
    let A : ℝ := gLAU sys (tv R θ)
    let Xb : ℝ := 5 / 3 * M₀ + cJ * S0
    let Wo : ℝ := (2 + 12 * sys.maxMass) * Cχ * Xb +
      ((3 + 12 * sys.maxMass) * Cχ + 14 * (g ^ 2 * momTwo χ)) * S0
    let W : ℝ := 5 / 3 * Wo + cJ * (Cχ * S0)
    let Q : ℝ := 16 * Ξ₀ ^ 2 + 120 * sys.maxMass ^ 2 * Ξ₁ ^ 2 + 30 * Ct M₀ ^ 2
    let r : ℝ := rPhys g m
    let σ : ℝ := sigmaU sys (tv R θ)
    let ξ : ℝ := S0 + 4 * Ξ₀ + 2 * (eta * Real.sqrt Q)
    let F : ℝ := flow2 1 cJ A σ ξ M₀ S0
    let o : ℝ := 8 * Cχ * F + 8 * (g ^ 4 * momFour χ) * S0
    let Φ : ℝ := flow2 1 cJ A σ o Wo (Cχ * S0)
    let τφ : ℝ := sys.maxMass ^ 2 * (r * Φ) / (g * ((s₀ : ℝ) + 1)) ^ 4
    let t₁ : ℝ := tl (g * (m : ℝ)) rho₁
    let t₂ : ℝ := tl (g * ((2 * m : ℕ) : ℝ)) rho₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) rho₄
    let δ : ℝ := eta * t₂
    let Bd : ℝ := (eta * t₂) * (eta * (Ct (sys.maxMass * W) * rho₂)) +
      Zg * (formAP g s₀ m * (t₄ * (sys.maxMass * W) + τφ * M₀) + 52 * m * (τφ * t₄))
    let ψg := Ug t (regCoeff m (molecularH2StateMap eta g u₀))
    ‖⟪U t (molecularH2StateMap eta g u₀), convOp a χ (U t (molecularH2StateMap eta g u₀))⟫_ℂ -
        ⟪ψg, gridObs a χ ψg⟫_ℂ‖ ≤
      (2 * (δ * (Cχ * t₁ + τχ * S0 + CO * δ)) + CO * δ ^ 2) +
        (Cχ * (t₁ * t₁) + supTail χ m * (S0 * S0)) + 2 * (Bd * t) := by
  intro g b S0 Ξ₀ Ξ₁ M₀ Ct tl s₀ Zg CO Cχ τχ cJ A Xb Wo W Q r σ ξ F o Φ τφ t₁ t₂ t₄ δ Bd ψg
  have hM := sys.one_le_maxMass
  have hmm : 0 ≤ sys.maxMass := by linarith
  have hb : 0 ≤ b := relB_gL_nonneg sys L (tv R θ) Hunit hC
  have hg : 0 < g := by positivity
  have hg1 : g ^ 2 ≤ 1 := pow_le_one₀ hg.le (PlaneWaveGridG.g_le_one hL2)
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hs₀m : s₀ ≤ m := Nat.div_le_self m 4
  have hs₀mr : (s₀ : ℝ) ≤ m := by exact_mod_cast hs₀m
  have hK₁ : 1 ≤ g * (m : ℝ) :=
    (show 1 ≤ g * (s₀ : ℝ) from hK₄).trans (mul_le_mul_of_nonneg_left hs₀mr hg.le)
  have hm2m : (m : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by push_cast; linarith
  have hK₂ : 1 ≤ g * ((2 * m : ℕ) : ℝ) := hK₁.trans (mul_le_mul_of_nonneg_left hm2m hg.le)
  have hN : 1 ≤ g * (((4 * m : ℕ) : ℝ) + 1) := by
    have h4m : (m : ℝ) ≤ ((4 * m : ℕ) : ℝ) + 1 := by push_cast; linarith
    exact hK₁.trans (mul_le_mul_of_nonneg_left h4m hg.le)
  have hS0 : 0 ≤ S0 := norm_nonneg _
  have hΞ₀ : 0 ≤ Ξ₀ := by positivity
  have hΞ₁ : 0 ≤ Ξ₁ := by positivity
  have hM₀ : 0 ≤ M₀ := by positivity
  have hCt₀ : 0 ≤ Ct M₀ := gLtailMU_nonneg sys hθ.tv_nonneg hH hM₀
  have hCtU : gLtailM sys L (tv R θ) Hunit M₀ ≤ Ct M₀ :=
    gLtailM_le_U sys hL2 hθ.tv_nonneg hH hM₀
  have htl0 : ∀ K ρ, 0 ≤ ρ → 0 ≤ tl K ρ := by
    intro K ρ hρ
    show 0 ≤ (2 * sys.maxMass / K ^ 2) * ((2 * sys.maxMass / K ^ 2) * Ξ₁ + Ct M₀ * ρ)
    have h1 : 0 ≤ 2 * sys.maxMass / K ^ 2 := div_nonneg (by linarith) (sq_nonneg K)
    exact mul_nonneg h1 (add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hCt₀ hρ))
  have ht₁0 : 0 ≤ t₁ := htl0 _ _ hRho₁
  have ht₂0 : 0 ≤ t₂ := htl0 _ _ hRho₂
  have hδ0 : 0 ≤ δ := mul_nonneg (Nat.cast_nonneg _) ht₂0
  have hCO : 0 ≤ CO := norm_nonneg _
  have hCχ : 0 ≤ Cχ := tsum_nonneg fun ν => norm_nonneg _
  have hτχ : 0 ≤ τχ := tsum_nonneg fun ν => by split_ifs <;> simp
  have hcJ : 0 ≤ cJ := gridFlowConstU_nonneg sys hθ.tv_nonneg
  have hA0 : 0 ≤ A := by
    show 0 ≤ gLAU sys (tv R θ)
    unfold gLAU
    have := gLzU_nonneg sys hθ.tv_nonneg
    positivity
  -- the exact state at time `t`
  obtain ⟨u, hu1, hu2⟩ := hgraph t u₀
  have hψ : U t (molecularH2StateMap eta g u₀) = molecularH2StateMap eta g u := hu1.symm
  have hSu : ‖molecularH2StateMap eta g u‖ = S0 := by
    rw [← hψ, LinearIsometryEquiv.norm_map]
  have hnorm_le : ∀ (x : MolecularFourierH2 eta), ‖molecularH2StateMap eta g x‖ = S0 →
      ‖coulombFourierKineticH2 sys g x‖ ≤ Ξ₀ → ‖x‖ ≤ M₀ := by
    intro x hx hT
    refine (h2norm_le sys L x).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    show ‖molecularH2StateMap eta g x‖ + 2 * ‖coulombFourierKineticH2 sys g x‖ ≤ S0 + 2 * Ξ₀
    rw [hx]
    linarith
  have hu_le : ‖u‖ ≤ M₀ := by
    refine hnorm_le u hSu ?_
    have h := kinetic_le_elliptic_gL sys L H hKernel Hunit hL hθ hPeriodic hC u
    rw [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
    exact h
  have hu₀_le : ‖u₀‖ ≤ M₀ :=
    hnorm_le u₀ rfl (kinetic_le_elliptic_gL sys L H hKernel Hunit hL hθ hPeriodic hC u₀)
  -- the tails at `K` and `2K`
  have ht₁ : ∀ c, ‖tailMask g (g * (m : ℝ)) c (molecularH2StateMap eta g u)‖ ≤ t₁ := fun c =>
    tail_weaken hmm hRho₁ hCtU (tails_at_time_gL sys L H hKernel Hunit hL hθ hPeriodic hC U hgraph
      c (g * (m : ℝ)) rho₁ hK₁ hRho₁ hRhoScale₁ u₀ v₀ huv t u hu1 hu2).2
  have ht₂ : ∀ c, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖ ≤ t₂ :=
    fun c => tail_weaken hmm hRho₂ hCtU (tails_at_time_gL sys L H hKernel Hunit hL hθ hPeriodic hC
      U hgraph c (g * ((2 * m : ℕ) : ℝ)) rho₂ hK₂ hRho₂ hRhoScale₂ u₀ v₀ huv t u hu1 hu2).2
  have hsum : ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖
      ≤ δ := by
    calc ∑ c : Fin eta, ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖
        ≤ ∑ _c : Fin eta, t₂ := sum_le_sum fun c _ => ht₂ c
      _ = δ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hδ : ‖molecularH2StateMap eta g u -
      molecularH2Truncate (2 * m) (molecularH2StateMap eta g u)‖ ≤ δ :=
    (norm_sub_truncate_le hg (2 * m) _).trans hsum
  -- symmetry of the observables
  have hO : ∀ x y, ⟪convOp a χ x, y⟫_ℂ = ⟪x, convOp a χ y⟫_ℂ := convOp_symm a hχ1 hreal
  have hOg : ∀ x y : EuclideanSpace ℂ (RCfg eta m), ⟪gridObs a χ x, y⟫_ℂ = ⟪x, gridObs a χ y⟫_ℂ :=
    gridObs_symm a hχ1 hreal
  -- (I): the never-projected tail at cutoff `2K`
  have hI : ‖⟪molecularH2StateMap eta g u, convOp a χ (molecularH2StateMap eta g u)⟫_ℂ -
      ⟪molecularH2Truncate (2 * m) (molecularH2StateMap eta g u),
        convOp a χ (molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))⟫_ℂ‖ ≤
      2 * (δ * (Cχ * t₁ + τχ * S0 + CO * δ)) + CO * δ ^ 2 := by
    have h := norm_inner_sub_proj_le (convOp a χ) hO (molecularH2StateMap eta g u)
      (molecularH2StateMap eta g u - molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))
    rw [sub_sub_cancel] at h
    refine h.trans ?_
    have hchi : ‖convOp a χ (molecularH2StateMap eta g u) -
        molecularH2Truncate (2 * m) (convOp a χ (molecularH2StateMap eta g u))‖ ≤
        Cχ * t₁ + τχ * S0 + CO * δ := by
      have hc := chitail hg (2 * m) a hχ1 (molecularH2StateMap eta g u)
      have e : g * ((2 * m : ℕ) : ℝ) / 2 = g * (m : ℝ) := by push_cast; ring
      rw [e] at hc
      refine hc.trans ?_
      have hA : Cχ * ‖tailMask g (g * (m : ℝ)) a (molecularH2StateMap eta g u)‖ ≤ Cχ * t₁ :=
        mul_le_mul_of_nonneg_left (ht₁ a) hCχ
      have hB : τχ * ‖molecularH2StateMap eta g u‖ ≤ τχ * S0 := by rw [hSu]
      have hC' : CO * ∑ c : Fin eta,
          ‖tailMask g (g * ((2 * m : ℕ) : ℝ)) c (molecularH2StateMap eta g u)‖ ≤ CO * δ :=
        mul_le_mul_of_nonneg_left hsum hCO
      exact add_le_add (add_le_add hA hB) hC'
    have h1 : ‖⟪molecularH2StateMap eta g u - molecularH2Truncate (2 * m)
        (molecularH2StateMap eta g u),
        convOp a χ (molecularH2StateMap eta g u)⟫_ℂ‖ ≤ δ * (Cχ * t₁ + τχ * S0 + CO * δ) := by
      rw [inner_sub_truncate_left]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul hδ hchi (norm_nonneg _) hδ0)
    have h2 : ‖⟪molecularH2StateMap eta g u - molecularH2Truncate (2 * m)
        (molecularH2StateMap eta g u),
        convOp a χ (molecularH2StateMap eta g u -
          molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))⟫_ℂ‖ ≤ CO * δ ^ 2 := by
      refine (norm_inner_le_norm _ _).trans ?_
      set d := molecularH2StateMap eta g u - molecularH2Truncate (2 * m)
          (molecularH2StateMap eta g u)
      have hd : ‖convOp a χ d‖ ≤ CO * ‖d‖ := (convOp a χ).le_opNorm d
      calc ‖d‖ * ‖convOp a χ d‖ ≤ ‖d‖ * (CO * ‖d‖) := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
        _ = CO * ‖d‖ ^ 2 := by ring
        _ ≤ CO * δ ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hδ 2) hCO
    linarith
  -- (II): the form bound of the collocated observable
  have hAS : ‖regCoeff m (molecularH2StateMap eta g u)‖ ≤ S0 :=
    (norm_regCoeff_le _).trans hSu.le
  have hII : ‖⟪molecularH2Truncate (2 * m) (molecularH2StateMap eta g u),
        convOp a χ (molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))⟫_ℂ -
      ⟪regCoeff m (molecularH2StateMap eta g u),
        gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ‖ ≤
      Cχ * (t₁ * t₁) + supTail χ m * (S0 * S0) := by
    rw [inner_truncate_convOp a hχ1, norm_sub_rev]
    refine (norm_inner_gridObs_sub_galObs_le a hχ1 _ _).trans ?_
    have hHh : ‖maskOp (High m a) (regCoeff m (molecularH2StateMap eta g u))‖ ≤ t₁ :=
      (norm_high_regCoeff_le hg m a _).trans (ht₁ a)
    have h1 : ‖maskOp (High m a) (regCoeff m (molecularH2StateMap eta g u))‖ *
        ‖maskOp (High m a) (regCoeff m (molecularH2StateMap eta g u))‖ ≤ t₁ * t₁ :=
      mul_le_mul hHh hHh (norm_nonneg _) ht₁0
    have h2 : ‖regCoeff m (molecularH2StateMap eta g u)‖ *
        ‖regCoeff m (molecularH2StateMap eta g u)‖ ≤ S0 * S0 :=
      mul_le_mul hAS hAS (norm_nonneg _) hS0
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hCχ)
      (mul_le_mul_of_nonneg_left h2 (supTail_nonneg χ m))
  -- (III): the in-band error, by duality against the backward grid flows
  have ha₀ : ‖wMul (wPhys (regParticlesOf sys) g) (regCoeff m (molecularH2StateMap eta g u₀))‖ ≤
      M₀ := (norm_wPhys_regCoeff_stateMap_le (regParticlesOf sys) g u₀).trans hu₀_le
  have haS₀ : ‖regCoeff m (molecularH2StateMap eta g u₀)‖ ≤ S0 := norm_regCoeff_le _
  have haT : ‖wMul (wPhys (regParticlesOf sys) g) (regCoeff m (molecularH2StateMap eta g u))‖ ≤
      Xb := by
    have h := (norm_wPhys_regCoeff_stateMap_le (m := m) (regParticlesOf sys) g u).trans hu_le
    show _ ≤ 5 / 3 * M₀ + cJ * S0
    have : 0 ≤ cJ * S0 := mul_nonneg hcJ hS0
    linarith
  have hbT : ‖wMul (wPhys (regParticlesOf sys) g) ψg‖ ≤ Xb := by
    refine (norm_wPhys_gridFlow_le_gL sys hL2 hθ.tv_nonneg hκ.bound (Ug t) (hgcomm t) _).trans ?_
    exact add_le_add (mul_le_mul_of_nonneg_left ha₀ (by norm_num))
      (mul_le_mul_of_nonneg_left haS₀ hcJ)
  have hbS : ‖ψg‖ ≤ S0 := by
    show ‖Ug t (regCoeff m (molecularH2StateMap eta g u₀))‖ ≤ S0
    rw [LinearIsometryEquiv.norm_map]
    exact haS₀
  have hWa : ∀ τ, ‖wMul (wPhys (regParticlesOf sys) g)
      (Ug τ (gridObs a χ (regCoeff m (molecularH2StateMap eta g u))))‖ ≤ W := fun τ =>
    norm_wPhys_gridFlow_gridObs_le_gL sys hL2 hθ.tv_nonneg hκ.bound (Ug τ) (hgcomm τ) a hχ1 hχ2 _
      haT hAS
  have hWb : ∀ τ, ‖wMul (wPhys (regParticlesOf sys) g) (Ug τ (gridObs a χ ψg))‖ ≤ W := fun τ =>
    norm_wPhys_gridFlow_gridObs_le_gL sys hL2 hθ.tv_nonneg hκ.bound (Ug τ) (hgcomm τ) a hχ1 hχ2 _
      hbT hbS
  -- the sharp shells: second moments of the backward flows and the double kinetic division
  have hr : 1 ≤ r := one_le_rPhys hN
  have hr0 : 0 ≤ r := by linarith
  have hσ0 : 0 ≤ σ := sigmaU_nonneg sys hθ.tv_nonneg
  have hsc : secondConstP (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (gLgamma L (tv R θ)) g m ≤ σ * r := secondConstP_le_gL sys hL2 hθ.tv_nonneg m hN
  have hX2 : ∀ (s : ℝ) (x : MolecularFourierH2 eta),
      molecularH2StateMap eta g x = U s (molecularH2StateMap eta g u₀) → H x = U s (H u₀) →
      ‖wMul (wPhys (regParticlesOf sys) g) (wMul (wPhys (regParticlesOf sys) g)
        (regCoeff m (molecularH2StateMap eta g x)))‖ ≤ ξ * r := by
    intro s x hx1 hx2
    have h : ‖wMul (wPhys (regParticlesOf sys) g) (wMul (wPhys (regParticlesOf sys) g)
        (regCoeff m (molecularH2StateMap eta g x)))‖ ≤
        S0 + 4 * Ξ₀ + 2 * (eta * (Real.sqrt Q * r)) :=
      second_moment_regCoeff_le_gLU sys L H hKernel Hunit hL hθ hPeriodic hC hL2 hH U hgraph m u₀
        v₀ huv s x hx1 hx2 k₀ hk₀ hk₀g hk₀2 hN
    refine h.trans ?_
    have h1 : S0 ≤ S0 * r := le_mul_of_one_le_right hS0 hr
    have h2 : 4 * Ξ₀ ≤ 4 * Ξ₀ * r := le_mul_of_one_le_right (by positivity) hr
    have e : (S0 + 4 * Ξ₀ + 2 * (eta * Real.sqrt Q)) * r =
        S0 * r + 4 * Ξ₀ * r + 2 * (eta * (Real.sqrt Q * r)) := by ring
    show _ ≤ (S0 + 4 * Ξ₀ + 2 * (eta * Real.sqrt Q)) * r
    rw [e]
    linarith
  have hξ0 : 0 ≤ ξ := by
    have h2 : 0 ≤ 2 * (eta * Real.sqrt Q) :=
      mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
    show 0 ≤ S0 + 4 * Ξ₀ + 2 * (eta * Real.sqrt Q)
    linarith
  have hF0 : 0 ≤ F := flow2_nonneg hcJ hA0 hσ0 hξ0 hM₀ hS0
  have hξF : ξ ≤ F := le_flow2 hcJ hA0 hσ0 hξ0 hM₀ hS0
  have hXaT : ‖wMul (wPhys (regParticlesOf sys) g) (wMul (wPhys (regParticlesOf sys) g)
      (regCoeff m (molecularH2StateMap eta g u)))‖ ≤ r * F :=
    ((hX2 t u hu1 hu2).trans (mul_le_mul_of_nonneg_right hξF hr0)).trans_eq (mul_comm _ _)
  have hXbT : ‖wMul (wPhys (regParticlesOf sys) g) (wMul (wPhys (regParticlesOf sys) g) ψg)‖ ≤
      r * F := by
    have h0' := hX2 0 u₀ (h0 _).symm (h0 _).symm
    have h := norm_wPhys_sq_gridFlow_le_gL sys hL2 hθ.tv_nonneg hκ.bound hκ.support (Ug t)
      (hgcomm t) _ h0' ha₀ haS₀
    exact h.trans (flow2_le_mul hcJ hA0 hM₀ hS0 hr hsc le_rfl)
  have hXb0 : 0 ≤ Xb := add_nonneg (mul_nonneg (by norm_num) hM₀) (mul_nonneg hcJ hS0)
  have hD2 : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hWo0 : 0 ≤ Wo :=
    add_nonneg (mul_nonneg (mul_nonneg (by linarith) hCχ) hXb0)
      (mul_nonneg (add_nonneg (mul_nonneg (by linarith) hCχ) (by positivity)) hS0)
  have ho0 : 0 ≤ o := add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCχ) hF0)
    (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by positivity) (momFour_nonneg χ))) hS0)
  have hΦ0 : 0 ≤ Φ := flow2_nonneg hcJ hA0 hσ0 ho0 hWo0 (mul_nonneg hCχ hS0)
  have hτφ0 : 0 ≤ τφ := div_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hr0 hΦ0)) (by positivity)
  have hτ : ∀ v : EuclideanSpace ℂ (RCfg eta m),
      ‖wMul (wPhys (regParticlesOf sys) g) (wMul (wPhys (regParticlesOf sys) g) v)‖ ≤ r * F →
      ‖wMul (wPhys (regParticlesOf sys) g) v‖ ≤ Xb → ‖v‖ ≤ S0 →
      ∀ τ r', ‖maskOp (High (m / 4) r') (Ug τ (gridObs a χ v))‖ ≤ τφ := by
    intro v hXv hYv hSv τ r'
    have h := shell_gridFlow_gridObs_le_gLU sys hL2 hθ.tv_nonneg hκ.bound hκ.support Ug hgcomm a
      hχ1 hχ2 hχ4 v hr hXv hYv hSv hXb0 hS0 hsc τ r'
    have hpos : (0 : ℝ) < (g * ((s₀ : ℝ) + 1)) ^ 4 := by positivity
    show _ ≤ sys.maxMass ^ 2 * (r * Φ) / (g * ((s₀ : ℝ) + 1)) ^ 4
    rw [le_div_iff₀ hpos]
    linarith
  have hτa := hτ _ hXaT haT hAS
  have hτb := hτ _ hXbT hbT hbS
  have he : regCoeff m (molecularH2StateMap eta g u) - ψg =
      regCoeff m (U t (molecularH2StateMap eta g u₀)) -
        Ug t (regCoeff m (molecularH2StateMap eta g u₀)) := by
    rw [hψ]
  have hd1 : ‖⟪regCoeff m (molecularH2StateMap eta g u) - ψg,
      gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ‖ ≤ Bd * t := by
    have h := grid_duality_shell_gLU sys L H hKernel Hunit hL hθ hPeriodic hC hL2 hH U h0 hgraph
        hderiv m hm hκ Ug hg0 hgcomm hgderiv rho₂ rho₄ hK₄ hRho₂ hRhoScale₂ hRho₄ hRhoScale₄ u₀ v₀
        huv _ W τφ hWa hτφ0 hτa ht
    rw [he]
    exact h
  have hd2 : ‖⟪regCoeff m (molecularH2StateMap eta g u) - ψg, gridObs a χ ψg⟫_ℂ‖ ≤ Bd * t := by
    have h := grid_duality_shell_gLU sys L H hKernel Hunit hL hθ hPeriodic hC hL2 hH U h0 hgraph
        hderiv m hm hκ Ug hg0 hgcomm hgderiv rho₂ rho₄ hK₄ hRho₂ hRhoScale₂ hRho₄ hRhoScale₄ u₀ v₀
        huv _ W τφ hWb hτφ0 hτb ht
    rw [he]
    exact h
  have hIII : ‖⟪regCoeff m (molecularH2StateMap eta g u),
        gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ - ⟪ψg, gridObs a χ ψg⟫_ℂ‖ ≤
      2 * (Bd * t) :=
    (norm_inner_sub_inner_le (gridObs a χ) hOg _ _).trans ((add_le_add hd1 hd2).trans_eq (by ring))
  -- assembly
  rw [hψ]
  have hsplit : ⟪molecularH2StateMap eta g u, convOp a χ (molecularH2StateMap eta g u)⟫_ℂ -
      ⟪ψg, gridObs a χ ψg⟫_ℂ =
      (⟪molecularH2StateMap eta g u, convOp a χ (molecularH2StateMap eta g u)⟫_ℂ -
        ⟪molecularH2Truncate (2 * m) (molecularH2StateMap eta g u),
          convOp a χ (molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))⟫_ℂ) +
      (⟪molecularH2Truncate (2 * m) (molecularH2StateMap eta g u),
          convOp a χ (molecularH2Truncate (2 * m) (molecularH2StateMap eta g u))⟫_ℂ -
        ⟪regCoeff m (molecularH2StateMap eta g u),
          gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ) +
      (⟪regCoeff m (molecularH2StateMap eta g u),
          gridObs a χ (regCoeff m (molecularH2StateMap eta g u))⟫_ℂ - ⟪ψg, gridObs a χ ψg⟫_ℂ) := by
    ring
  rw [hsplit]
  exact (norm_add₃_le).trans (add_le_add (add_le_add hI hII) hIII)

end Grid


/-! ## The arithmetic of the rates in physical units -/

section Arith

/-- **The sharp shells, physical:** `r_g/(g(⌊m/4⌋+1))⁴ ≤ 3072 ρ⁵` when `ρ² g m = 1`, `m ≥ 8`. -/
lemma shell_rate_sharpP {g ρ : ℝ} {m : ℕ} (hg : 0 < g) (hρ : 0 ≤ ρ) (hm : 8 ≤ m)
    (hρK : ρ ^ 2 * (g * (m : ℝ)) = 1) :
    rPhys g m / (g * (((m / 4 : ℕ) : ℝ) + 1)) ^ 4 ≤ 3072 * ρ ^ 5 := by
  have h := (shell_rate_sharp hg hρ hm hρK).1
  have hsg2 : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg.le
  have hr : rPhys g m = g * Real.sqrt g * Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3 := by
    unfold rPhys
    rw [Real.sqrt_mul hg.le, mul_pow]
    have e : Real.sqrt g ^ 3 = g * Real.sqrt g := by
      calc Real.sqrt g ^ 3 = Real.sqrt g ^ 2 * Real.sqrt g := by ring
        _ = g * Real.sqrt g := by rw [hsg2]
    rw [e]
  have hp : (0 : ℝ) < (((m / 4 : ℕ) : ℝ) + 1) ^ 4 := by positivity
  rw [div_le_iff₀ hp] at h
  rw [hr, mul_pow, div_le_iff₀ (by positivity)]
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ g * Real.sqrt g)
  have e2 : g * Real.sqrt g * (g ^ 2 * Real.sqrt g) = g ^ 4 := by
    calc g * Real.sqrt g * (g ^ 2 * Real.sqrt g) = g ^ 3 * Real.sqrt g ^ 2 := by ring
      _ = g ^ 4 := by rw [hsg2]; ring
  calc g * Real.sqrt g * Real.sqrt (((4 * m : ℕ) : ℝ) + 1) ^ 3
      ≤ g * Real.sqrt g * (3072 * (g ^ 2 * Real.sqrt g) * ρ ^ 5 *
          (((m / 4 : ℕ) : ℝ) + 1) ^ 4) := h2
    _ = 3072 * ρ ^ 5 * (((m / 4 : ℕ) : ℝ) + 1) ^ 4 *
          (g * Real.sqrt g * (g ^ 2 * Real.sqrt g)) := by ring
    _ = 3072 * ρ ^ 5 * (g ^ 4 * (((m / 4 : ℕ) : ℝ) + 1) ^ 4) := by rw [e2]; ring

/-- **The form constant, physical:** `Z_c formAP g ⌊m/4⌋ m ≤ 18 √8 √79 z ρ` when `Z_c ≤ z g`,
`0 < g ≤ 1`, `ρ² g m = 1` and `m ≥ 8`. -/
lemma formAP_rate {g ρ z Zg : ℝ} {m : ℕ} (hg : 0 < g) (hg1 : g ≤ 1) (hρ : 0 ≤ ρ) (hm : 8 ≤ m)
    (hρK : ρ ^ 2 * (g * (m : ℝ)) = 1) (hZg : 0 ≤ Zg) (hZz : Zg ≤ z * g) :
    Zg * formAP g (m / 4) m ≤ 18 * Real.sqrt 8 * Real.sqrt 79 * z * ρ := by
  have hz : 0 ≤ z := by
    by_contra h
    push Not at h
    have : z * g < 0 := mul_neg_of_neg_of_pos h hg
    linarith
  have hs1 : 1 ≤ m / 4 := by omega
  have hσ : g ^ 3 + 78 ≤ 79 := by
    have := pow_le_one₀ hg.le hg1 (n := 3)
    linarith
  have h := PlaneWaveGridG.coupling_formAP_le hg hZg hZz hσ hs1 (Nat.div_le_self m 4)
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hs0 : (0 : ℝ) < ((m / 4 : ℕ) : ℝ) := by
    have : 0 < m / 4 := by omega
    exact_mod_cast this
  have hgs : 0 < g * ((m / 4 : ℕ) : ℝ) := by positivity
  have hsq : 0 < Real.sqrt (g * ((m / 4 : ℕ) : ℝ)) := Real.sqrt_pos.mpr hgs
  have e : Real.sqrt 8 * ρ * Real.sqrt (g * ((m / 4 : ℕ) : ℝ)) =
      Real.sqrt (8 * ρ ^ 2 * (g * ((m / 4 : ℕ) : ℝ))) := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 8 * ρ ^ 2 by positivity) (g * ((m / 4 : ℕ) : ℝ)),
      Real.sqrt_mul (show (0 : ℝ) ≤ 8 by norm_num) (ρ ^ 2), Real.sqrt_sq hρ]
  have key : 1 ≤ Real.sqrt 8 * ρ * Real.sqrt (g * ((m / 4 : ℕ) : ℝ)) := by
    rw [e, Real.one_le_sqrt]
    have h1 : ρ ^ 2 * (g * (m : ℝ)) ≤ ρ ^ 2 * (g * (8 * ((m / 4 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hg.le) (sq_nonneg ρ)
    nlinarith
  refine h.trans ?_
  rw [div_le_iff₀ hsq]
  have h0 : 0 ≤ 18 * z * Real.sqrt 79 := by positivity
  calc 18 * z * Real.sqrt 79 = 18 * z * Real.sqrt 79 * 1 := by ring
    _ ≤ 18 * z * Real.sqrt 79 * (Real.sqrt 8 * ρ * Real.sqrt (g * ((m / 4 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left key h0
    _ = 18 * Real.sqrt 8 * Real.sqrt 79 * z * ρ * Real.sqrt (g * ((m / 4 : ℕ) : ℝ)) := by ring

/-- **The rates of `thm:grid-dyn-sharp`, physical constants.** The explicit bound of
`grid_observable_error_sharp_gLU`, at `ρ = K^{-1/2}` (`K = g m`), `ρ₂ = (2K)^{-1/2}`,
`ρ₄ = (g⌊m/4⌋)^{-1/2}` and a flow shell `τ_φ ≤ m̄² r_g Φ/(g(⌊m/4⌋+1))⁴`, is at most
`A₁ K^{-5} + A₂ t K^{-3} + A₃ K^{-5/2} τ_χ + S0² τ^∞` for `m ≥ 8`, `K ≥ 8`, `g ≤ 1` and
`Z_c ≤ z g`, with `A₂ = 2 (η δ₁ C_t(m̄ W) + c_F β₄ m̄ W + c_F T M₀ + 52 T β₄)`,
`c_F = 18 √8 √79 z`, `T = 3072 m̄² Φ (1 + z)`. -/
lemma grid_rate_arith_sharpP {η mm Ξ₁ C₀ g t S0 sT Cχ CO τχ Zg M₀ W Φ z τφ : ℝ} {m : ℕ}
    {Ct : ℝ → ℝ}
    (hη : 0 ≤ η) (hmm : 1 ≤ mm) (hΞ₁ : 0 ≤ Ξ₁) (hC₀ : 0 ≤ C₀) (hg : 0 < g) (hg1 : g ≤ 1)
    (hm : 8 ≤ m) (hK : 8 ≤ g * m) (ht : 0 ≤ t) (hS0 : 0 ≤ S0) (hCχ : 0 ≤ Cχ) (hCO : 0 ≤ CO)
    (hτχ : 0 ≤ τχ) (hZg : 0 ≤ Zg) (hZz : Zg ≤ z * g) (hz : 0 ≤ z) (hM₀ : 0 ≤ M₀) (hW : 0 ≤ W)
    (hCt : ∀ M, 0 ≤ M → 0 ≤ Ct M) (hΦ : 0 ≤ Φ) (hτφ0 : 0 ≤ τφ)
    (hτφ : τφ ≤ mm ^ 2 * (rPhys g m * Φ) / (g * (((m / 4 : ℕ) : ℝ) + 1)) ^ 4) :
    let K : ℝ := g * m
    let tl : ℝ → ℝ → ℝ := fun K ρ => (2 * mm / K ^ 2) * ((2 * mm / K ^ 2) * Ξ₁ + C₀ * ρ)
    let ρ : ℝ := Real.sqrt (1 / K)
    let ρ₂ : ℝ := Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ)))
    let ρ₄ : ℝ := Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ)))
    let s₀ : ℕ := m / 4
    let t₁ : ℝ := tl (g * (m : ℝ)) ρ
    let t₂ : ℝ := tl (g * ((2 * m : ℕ) : ℝ)) ρ₂
    let t₄ : ℝ := tl (g * (s₀ : ℝ)) ρ₄
    let δ : ℝ := η * t₂
    let Bd : ℝ := (η * t₂) * (η * (Ct (mm * W) * ρ₂)) +
      Zg * (formAP g s₀ m * (t₄ * (mm * W) + τφ * M₀) + 52 * m * (τφ * t₄))
    let τ₁ : ℝ := 2 * mm * (2 * mm * Ξ₁ + C₀)
    let β₄ : ℝ := 128 * mm * (128 * mm * Ξ₁ + 8 * C₀)
    let δ₁ : ℝ := η * τ₁
    let cF : ℝ := 18 * Real.sqrt 8 * Real.sqrt 79 * z
    let T : ℝ := 3072 * mm ^ 2 * Φ * (1 + z)
    (2 * (δ * (Cχ * t₁ + τχ * S0 + CO * δ)) + CO * δ ^ 2) + (Cχ * (t₁ * t₁) + sT * (S0 * S0)) +
        2 * (Bd * t) ≤
      (2 * δ₁ * (Cχ * τ₁ + CO * δ₁) + CO * δ₁ ^ 2 + Cχ * τ₁ ^ 2) * (1 / K) ^ 5 +
        2 * (η * δ₁ * Ct (mm * W) + (cF * β₄ * (mm * W) + cF * T * M₀ + 52 * T * β₄)) * t *
          (1 / K) ^ 3 +
        2 * δ₁ * S0 * Real.sqrt (1 / K) ^ 5 * τχ + S0 ^ 2 * sT := by
  intro K tl ρ ρ₂ ρ₄ s₀ t₁ t₂ t₄ δ Bd τ₁ β₄ δ₁ cF T
  have hmm0 : 0 ≤ mm := by linarith
  have hKpos : 0 < K := by show 0 < g * (m : ℝ); linarith
  have hK1 : 1 ≤ K := by show 1 ≤ g * (m : ℝ); linarith
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρK : ρ ^ 2 * K = 1 := by
    show Real.sqrt (1 / K) ^ 2 * K = 1
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hρ2 : ρ ^ 2 = 1 / K := Real.sq_sqrt (by positivity)
  have hρ1 : ρ ≤ 1 := by
    have h5 : ρ ^ 2 ≤ 1 := by
      rw [hρ2, div_le_one hKpos]
      exact hK1
    nlinarith
  have hρK' : ρ ^ 2 * (g * (m : ℝ)) = 1 := hρK
  have hm0 : (0 : ℝ) < m := by
    have : 0 < m := by omega
    exact_mod_cast this
  have h2m : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  have hK₂pos : 0 < g * ((2 * m : ℕ) : ℝ) := by rw [h2m]; positivity
  have hK₂ : K ≤ 1 * (g * ((2 * m : ℕ) : ℝ)) := by
    show g * (m : ℝ) ≤ 1 * (g * ((2 * m : ℕ) : ℝ))
    rw [h2m]
    nlinarith
  have hρ₂0 : 0 ≤ ρ₂ := Real.sqrt_nonneg _
  have hρ₂K : ρ₂ ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1 := by
    show Real.sqrt (1 / (g * ((2 * m : ℕ) : ℝ))) ^ 2 * (g * ((2 * m : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hρ₂ρ : ρ₂ ≤ ρ := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hK₂pos hKpos]
    have := hK₂
    linarith
  have hs : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by
    have : m ≤ 8 * (m / 4) := by omega
    exact_mod_cast this
  have hs0 : (0 : ℝ) < ((m / 4 : ℕ) : ℝ) := by
    have : 0 < m / 4 := by omega
    exact_mod_cast this
  have hK₄pos : 0 < g * ((m / 4 : ℕ) : ℝ) := by positivity
  have hK₄ : K ≤ 8 * (g * (s₀ : ℝ)) := by
    show g * (m : ℝ) ≤ 8 * (g * ((m / 4 : ℕ) : ℝ))
    nlinarith
  have hρ₄0 : 0 ≤ ρ₄ := Real.sqrt_nonneg _
  have hρ₄K : ρ₄ ^ 2 * (g * (s₀ : ℝ)) = 1 := by
    show Real.sqrt (1 / (g * ((m / 4 : ℕ) : ℝ))) ^ 2 * (g * ((m / 4 : ℕ) : ℝ)) = 1
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  -- the tails
  have hτ₁0 : 0 ≤ τ₁ := by positivity
  have hβ₄0 : 0 ≤ β₄ := by positivity
  have ht₁ : t₁ ≤ τ₁ * ρ ^ 5 := by
    have h := tl_rate (c := 1) hmm0 hΞ₁ hC₀ le_rfl hρ0 hρK hK1 (by linarith) hρ0 hρK
    have e : 2 * mm * 1 ^ 2 * (2 * mm * 1 ^ 2 * Ξ₁ + 1 * C₀) * ρ ^ 5 = τ₁ * ρ ^ 5 := by
      show _ = 2 * mm * (2 * mm * Ξ₁ + C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have ht₂ : t₂ ≤ τ₁ * ρ ^ 5 := by
    have h := tl_rate (c := 1) hmm0 hΞ₁ hC₀ le_rfl hρ0 hρK hK1 hK₂ hρ₂0 hρ₂K
    have e : 2 * mm * 1 ^ 2 * (2 * mm * 1 ^ 2 * Ξ₁ + 1 * C₀) * ρ ^ 5 = τ₁ * ρ ^ 5 := by
      show _ = 2 * mm * (2 * mm * Ξ₁ + C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have ht₄ : t₄ ≤ β₄ * ρ ^ 5 := by
    have h := tl_rate (c := 8) hmm0 hΞ₁ hC₀ (by norm_num) hρ0 hρK hK1 hK₄ hρ₄0 hρ₄K
    have e : 2 * mm * 8 ^ 2 * (2 * mm * 8 ^ 2 * Ξ₁ + 8 * C₀) * ρ ^ 5 = β₄ * ρ ^ 5 := by
      show _ = 128 * mm * (128 * mm * Ξ₁ + 8 * C₀) * ρ ^ 5
      ring
    exact h.trans (le_of_eq e)
  have htl0 : ∀ K' ρ', 0 ≤ ρ' → 0 ≤ tl K' ρ' := by
    intro K' ρ' hρ'
    show 0 ≤ (2 * mm / K' ^ 2) * ((2 * mm / K' ^ 2) * Ξ₁ + C₀ * ρ')
    have h1 : 0 ≤ 2 * mm / K' ^ 2 := div_nonneg (by linarith) (sq_nonneg K')
    exact mul_nonneg h1 (add_nonneg (mul_nonneg h1 hΞ₁) (mul_nonneg hC₀ hρ'))
  have ht₁0 : 0 ≤ t₁ := htl0 _ _ hρ0
  have ht₂0 : 0 ≤ t₂ := htl0 _ _ hρ₂0
  have ht₄0 : 0 ≤ t₄ := htl0 _ _ hρ₄0
  -- the form constant and the shells, physical
  have hfA : Zg * formAP g s₀ m ≤ cF * ρ := formAP_rate hg hg1 hρ0 hm hρK' hZg hZz
  have hfA0 : 0 ≤ Zg * formAP g s₀ m := mul_nonneg hZg (formAP_nonneg g s₀ m)
  have hsh := shell_rate_sharpP hg hρ0 hm hρK'
  have hmW : 0 ≤ mm * W := by positivity
  have hT0 : 0 ≤ T := by positivity
  have hmΦ : 0 ≤ mm ^ 2 * Φ := mul_nonneg (sq_nonneg _) hΦ
  have hτφ5 : τφ ≤ 3072 * mm ^ 2 * Φ * ρ ^ 5 := by
    have e : mm ^ 2 * (rPhys g m * Φ) / (g * (((m / 4 : ℕ) : ℝ) + 1)) ^ 4 =
        (mm ^ 2 * Φ) * (rPhys g m / (g * (((m / 4 : ℕ) : ℝ) + 1)) ^ 4) := by ring
    have h := mul_le_mul_of_nonneg_left hsh hmΦ
    rw [e] at hτφ
    linarith
  have hτφ' : τφ ≤ T * 1 ^ 2 * ρ ^ 5 := by
    have h1 : 3072 * mm ^ 2 * Φ * ρ ^ 5 ≤ T * 1 ^ 2 * ρ ^ 5 := by
      have hρ5 : 0 ≤ ρ ^ 5 := by positivity
      have : 3072 * mm ^ 2 * Φ ≤ 3072 * mm ^ 2 * Φ * (1 + z) :=
        le_mul_of_one_le_right (by positivity) (by linarith)
      have e : T * 1 ^ 2 * ρ ^ 5 = 3072 * mm ^ 2 * Φ * (1 + z) * ρ ^ 5 := by
        show 3072 * mm ^ 2 * Φ * (1 + z) * 1 ^ 2 * ρ ^ 5 = _
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_right this hρ5
    linarith
  have hmτ : Zg * (m : ℝ) * τφ ≤ T * 1 * ρ ^ 3 := by
    have h1 : Zg * (m : ℝ) ≤ z * (g * (m : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hZz hm0.le
      linarith
    have h2 : Zg * (m : ℝ) * τφ ≤ z * (g * (m : ℝ)) * (3072 * mm ^ 2 * Φ * ρ ^ 5) :=
      mul_le_mul h1 hτφ5 hτφ0 (by positivity)
    have e : z * (g * (m : ℝ)) * (3072 * mm ^ 2 * Φ * ρ ^ 5) =
        3072 * mm ^ 2 * Φ * z * ρ ^ 3 * (ρ ^ 2 * (g * (m : ℝ))) := by ring
    rw [hρK', mul_one] at e
    have h3 : 3072 * mm ^ 2 * Φ * z * ρ ^ 3 ≤ T * 1 * ρ ^ 3 := by
      have hρ3 : 0 ≤ ρ ^ 3 := by positivity
      have e2 : T * 1 * ρ ^ 3 = 3072 * mm ^ 2 * Φ * (1 + z) * ρ ^ 3 := by
        show 3072 * mm ^ 2 * Φ * (1 + z) * 1 * ρ ^ 3 = _
        ring
      rw [e2]
      have : 3072 * mm ^ 2 * Φ * z ≤ 3072 * mm ^ 2 * Φ * (1 + z) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_right this hρ3
    linarith
  have hCtL : 0 ≤ Ct (mm * W) := hCt _ hmW
  -- the two pieces
  have hI := rate_arith_I (sT := sT) hη hτ₁0 rfl ht₁ ht₂ ht₁0 ht₂0 hCχ hCO hτχ hS0 hρ0
  have hIII := rate_arith_III_sharp (m := Zg * (m : ℝ)) (Xa := M₀) (Zg := 1)
    (fA := Zg * formAP g s₀ m) (g := 1) (T := T) (cF := cF) hη hτ₁0 hρ0 hρ1 ht₂ hρ₂ρ hρ₂0 hCtL
    zero_le_one hfA hfA0 ht₄ ht₄0 hmW hτφ' hτφ0 hmτ hM₀ zero_le_one ht hβ₄0 hT0
  have eB : 2 * (Bd * t) = 2 * (((η * t₂) * (η * (Ct (mm * W) * ρ₂)) +
      1 * (Zg * formAP g s₀ m * (t₄ * (mm * W) + τφ * M₀) + 52 * (Zg * (m : ℝ)) * (τφ * t₄))) *
        t) := by
    show 2 * (((η * t₂) * (η * (Ct (mm * W) * ρ₂)) +
      Zg * (formAP g s₀ m * (t₄ * (mm * W) + τφ * M₀) + 52 * m * (τφ * t₄))) * t) = _
    ring
  have eA : 2 * (η * (η * τ₁) * Ct (mm * W) + 1 * (cF * β₄ * (mm * W) + cF * T * 1 ^ 2 * M₀ +
      52 * T * 1 * β₄)) * t * ρ ^ 6 =
      2 * (η * δ₁ * Ct (mm * W) + (cF * β₄ * (mm * W) + cF * T * M₀ + 52 * T * β₄)) * t *
        ρ ^ 6 := by
    show _ = 2 * (η * (η * τ₁) * Ct (mm * W) + (cF * β₄ * (mm * W) + cF * T * M₀ + 52 * T * β₄)) *
      t * ρ ^ 6
    ring
  rw [← eB, eA] at hIII
  have hρ10 : ρ ^ 10 = (1 / K) ^ 5 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, pow_mul, hρ2]
  have hρ6 : ρ ^ 6 = (1 / K) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hρ2]
  rw [hρ10] at hI
  rw [hρ6] at hIII
  show _ ≤ _ + _ * t * (1 / K) ^ 3 + 2 * δ₁ * S0 * ρ ^ 5 * τχ + S0 ^ 2 * sT
  linarith

end Arith

end FreeBoundary
