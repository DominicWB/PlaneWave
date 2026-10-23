import PlaneWave.KineticLog.GridRates

/-!
# Logarithmic kinetic bound, part 15: the periodic grid endpoint

**`thm:kinetic-log`, grid case** (`thm_kinetic_log_grid`): for the constructed periodic Coulomb
Hamiltonian `H`, every exact propagator (`EvoData`, datum `ψ₀ ∈ D(H²)`), every register radius
`2m` with `m ≥ m₀` (`K = 2π m/L`, `N = (4m+1)³` points per register, cutoff `2K`), every kernel of
the full class `IsGridKernel` (eq:kernelclass), every grid propagator `U_g` of the grid
Hamiltonian, every measured particle `p₀` and every `t ≥ 0`,

  `|⟨ψ(t), T_{p₀} ψ(t)⟩ - ⟨ψ_g(t), T_{p₀} ψ_g(t)⟩| ≤ C 𝒟² [1 + t + log(2 + K)]/K³`,

with `ψ_g(t) = U_g(t) P' ψ₀` (the projected datum is not renormalised) and `𝒟 = Ξ`.  The constants
`C` and `m₀` depend only on the fixed system, the cell, `Hunit` and `p₀`: they precede the
quantifiers over the cutoff, the kernel, the propagators, the datum and the time.

Proof (`sec:kinetic-grid`): with `Λ = K²/(1024 m̄)`, the common shift `c + d`
(`c = shiftC`, `d = c_gr + 1`) and the filtered datum `p = 1_{H + c ≤ Λ} ψ₀`,

* the exact Fourier tail beyond the cube `2m` costs `η² c_tr² Ξ²/(2K)³` (`grid_proj_term`);
* the initial filter costs `‖ψ₀ - p‖ (‖T_p ·‖ + ‖T_p ·‖) ≤ C Ξ²/K⁴` twice (graph pairing);
* the filtered comparison is the core estimate `grid_core_pair` paired with `z = T_p x` and
  `z = T_p y`, where `‖z‖ ≤ C Ξ` and `‖W z‖ ≤ C Ξ K^{3/2}` (layer cake of the exact and grid
  trajectory shells, `norm_wM_regKin_shells`), the dyadic part costs
  `48 δ_G K^{-3} (t + log(2 + 2Λ))` and the separated part
  `2 (F_G/(√K (Λ - d))) ‖(H + c + d)ψ₀‖ ‖(G + c + d) z‖/(2Λ) ≤ C Ξ² K^{-3}`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal
open FSGalerkin (Kc)

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Register helpers -/

section RegHelpers

variable (sys : CoulombSystem eta ν) (g : ℝ) {m : ℕ}

omit [Fintype ν] in
/-- **Graph pairing on the register**: `|⟨a, A_p a⟩ - ⟨b, A_p b⟩| ≤ ‖a - b‖ (‖A_p a‖ + ‖A_p b‖)`. -/
lemma regExpect_pair_le (p : Fin eta) (a b : EuclideanSpace ℂ (RCfg eta m)) :
    |regExpect sys g p a - regExpect sys g p b| ≤
      ‖a - b‖ * (‖wMul (regKinSym sys g p) a‖ + ‖wMul (regKinSym sys g p) b‖) := by
  refine (regExpect_sub_le sys g p a b).trans ?_
  rw [mul_add]
  exact add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)

omit [Fintype ν] in
/-- `‖A_p v‖ ≤ (g²/2)(1 + 12 η m²) ‖v‖` on the register. -/
lemma norm_regKin_le_poly (p : Fin eta) (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (regKinSym sys g p) v‖ ≤ g ^ 2 / 2 * (1 + 12 * eta * (m : ℝ) ^ 2) * ‖v‖ := by
  refine (norm_regKin_le sys g p v).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact (norm_wM_le_wTot (regParticlesOf sys) v).trans (norm_wTot_le_reg v)

omit [Fintype ν] in
/-- `‖W A_p v‖ ≤ (g²/2)(1 + 12 η m²)² ‖v‖` on the register. -/
lemma norm_wM_regKin_le_poly (p : Fin eta) (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys g p) v)‖ ≤
      g ^ 2 / 2 * (1 + 12 * eta * (m : ℝ) ^ 2) ^ 2 * ‖v‖ := by
  refine (norm_wM_regKin_le sys g p v).trans ?_
  have hc : (0 : ℝ) ≤ 1 + 12 * eta * (m : ℝ) ^ 2 := by positivity
  have h1 : ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) v)‖ ≤
      (1 + 12 * eta * (m : ℝ) ^ 2) * ‖wMul (wM (regParticlesOf sys)) v‖ :=
    (norm_wM_le_wTot (regParticlesOf sys) _).trans (norm_wTot_le_reg _)
  have h2 : ‖wMul (wM (regParticlesOf sys)) v‖ ≤ (1 + 12 * eta * (m : ℝ) ^ 2) * ‖v‖ :=
    (norm_wM_le_wTot (regParticlesOf sys) v).trans (norm_wTot_le_reg v)
  calc g ^ 2 / 2 * ‖wMul (wM (regParticlesOf sys)) (wMul (wM (regParticlesOf sys)) v)‖
      ≤ g ^ 2 / 2 * ((1 + 12 * eta * (m : ℝ) ^ 2) *
          ((1 + 12 * eta * (m : ℝ) ^ 2) * ‖v‖)) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hc)
    _ = _ := by ring

end RegHelpers

/-! ## The exact Fourier tail beyond the register cube -/

section ProjTerm

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **The exact Fourier tail beyond the register cube `2m`**: no cross term (`P' T_p = T_p P'`),
and `|⟨ψ(t), T_p ψ(t)⟩ - ⟨P' ψ(t), T_p P' ψ(t)⟩| ≤ η² (c_tr Ξ)²/(2K)³`. -/
lemma grid_proj_term (D : EvoData L H) (t : ℝ) (m : ℕ) (hK1 : 1 ≤ gF L * (2 * m : ℕ))
    (p₀ : Fin eta) :
    |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
        regExpect sys (gF L) p₀ (regCoeff m (D.U t (Sm eta L D.u₀)))| ≤
      (eta : ℝ) ^ 2 * (cTr sys L Hunit * D.Xi) ^ 2 / (gF L * (2 * m : ℕ)) ^ 3 := by
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D t
  set μ := regKin sys (gF L) p₀ with hμ
  set M := cTr sys L Hunit * D.Xi with hM
  set K := gF L * ((2 * m : ℕ) : ℝ) with hKdef
  have hK0 : 0 < K := by linarith
  have hM0 : 0 ≤ M := hF.nonneg
  have hsplit := μ.expect_split (2 * m) w
  have htail0 := μ.expect_tail_nonneg (2 * m) w
  have htail := μ.expect_tail_le (2 * m) w
  have hR := fgood_R hF hL hK1
  have hTt : ‖coulombFourierKineticH2 sys (gF L) w -
      molecularH2Truncate (2 * m) (coulombFourierKineticH2 sys (gF L) w)‖ ≤
      eta * M * K ^ (-(1 / 2 : ℝ)) := by
    refine (PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) (2 * m) _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * ((2 * m : ℕ) : ℝ)) a
          (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ ∑ _a : Fin eta, M * K ^ (-(1 / 2 : ℝ)) :=
          Finset.sum_le_sum fun a _ => (hF.2 a K hK1).2
      _ = eta * M * K ^ (-(1 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hpow : K ^ (-(5 / 2 : ℝ)) * K ^ (-(1 / 2 : ℝ)) = 1 / K ^ 3 := by
    rw [← Real.rpow_add hK0, show (-(5 / 2 : ℝ)) + (-(1 / 2)) = -(3 : ℝ) by norm_num,
      Real.rpow_neg hK0.le, one_div]
    congr 1
    exact_mod_cast Real.rpow_natCast K 3
  have hproj : μ.expect (molecularH2StateMap eta (gF L) (w - molecularH2Truncate (2 * m) w)) ≤
      (eta : ℝ) ^ 2 * M ^ 2 / K ^ 3 := by
    refine htail.trans ?_
    have h1 := mul_le_mul hR hTt (norm_nonneg _) (by positivity)
    refine h1.trans (le_of_eq ?_)
    calc eta * M * K ^ (-(5 / 2 : ℝ)) * (eta * M * K ^ (-(1 / 2 : ℝ))) =
          (eta : ℝ) ^ 2 * M ^ 2 * (K ^ (-(5 / 2 : ℝ)) * K ^ (-(1 / 2 : ℝ))) := by ring
      _ = _ := by rw [hpow]; ring
  have hreg : μ.expect (molecularH2StateMap eta (gF L) (molecularH2Truncate (2 * m) w)) =
      regExpect sys (gF L) p₀ (regCoeff m (molecularH2StateMap eta (gF L) w)) :=
    expect_truncate_eq_reg sys (gF L) (m := m) p₀ w
  have hSw : molecularH2StateMap eta (gF L) w = D.U t (Sm eta L D.u₀) := hw1
  rw [← hSw, hsplit, hreg, add_sub_cancel_left, abs_of_nonneg htail0]
  exact hproj

end ProjTerm

/-! ## The constant of the grid endpoint -/

section Constant

variable (sys : CoulombSystem eta ν) (L Hunit : ℝ)

/-- The total shift `c' = c + c_gr + 1` of the grid comparison. -/
noncomputable def cPr : ℝ :=
  shiftC sys L Hunit + (cGr (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (coulombCellAmplitude L) (2 * Real.pi / L) + 1)

/-- The filter constant `ε₁ = (1 + c)² (1024 m̄)²` (`‖ψ₀ - p‖ ≤ ε₁ Ξ/K⁴`). -/
noncomputable def epsG : ℝ := (1 + shiftC sys L Hunit) ^ 2 * (1024 * sys.maxMass) ^ 2

/-- `ℓ = 1 + 12 η/g²` (`1 + 12 η m² ≤ ℓ K²`). -/
noncomputable def ellG : ℝ := 1 + 12 * eta / gF L ^ 2

/-- The first graph constant of `T_p x`, `T_p y`: `‖T_p ·‖ ≤ ζ Ξ`. -/
noncomputable def zetaG : ℝ :=
  gF L ^ 2 / 2 * ((1 + 2 / gF L ^ 2) * cTr sys L Hunit) + gF L ^ 2 / 2 * bG0 sys L Hunit +
    gF L ^ 2 / 2 * ellG (eta := eta) L * epsG sys L Hunit

/-- The second weighted constant: `‖W T_p ·‖ ≤ ω Ξ K^{3/2}`. -/
noncomputable def omegaG (T₀ : ℕ) : ℝ :=
  3 * Real.sqrt (gF L) * ((1 + 2 / gF L ^ 2) * cTr sys L Hunit) *
      (2 * (T₀ : ℝ) ^ 2 + 4 / Real.sqrt (gF L)) +
    3 * Real.sqrt (gF L) * (2 * (T₀ : ℝ) ^ 2 * bG0 sys L Hunit + 4 * bG1 sys L Hunit) +
    gF L ^ 2 / 2 * ellG (eta := eta) L ^ 2 * epsG sys L Hunit

/-- The constant of `‖(G + c') T_p ·‖ ≤ γ Ξ K^{3/2}`. -/
noncomputable def gammaG (T₀ : ℕ) : ℝ :=
  5 * gF L ^ 2 / 8 * omegaG sys L Hunit T₀ +
    (26 * ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) *
      (J0g ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (gF L) : ℝ) +
      cPr sys L Hunit) * zetaG sys L Hunit

/-- **The constant of the grid kinetic theorem.** -/
noncomputable def gridC (T₀ : ℕ) : ℝ :=
  (eta : ℝ) ^ 2 * cTr sys L Hunit ^ 2 + 4 * epsG sys L Hunit * zetaG sys L Hunit +
    4 * fG_grid sys L Hunit * (1 + cPr sys L Hunit) * gammaG sys L Hunit T₀ *
      (1024 * sys.maxMass) ^ 2 +
    192 * dG_grid sys L Hunit (cPr sys L Hunit) * (1 + cPr sys L Hunit) ^ 2 * zetaG sys L Hunit

variable {sys L Hunit}

lemma cPr_nonneg (hL : 0 < L) : 0 ≤ cPr sys L Hunit := by
  unfold cPr
  have := two_le_shiftC sys L Hunit
  have := cGr_nonneg (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
    (coulombCellAmplitude_pos hL).le
  linarith

lemma bG0_nonneg (hL : 0 < L) : 0 ≤ bG0 sys L Hunit := by
  unfold bG0
  have := cTr_nonneg sys hL Hunit
  have := gF_pos hL
  have := Zc_nonneg (P := regParticlesOf sys) (D := (posNucleiOf sys.nuclei).toNucData)
    (coulombCellAmplitude_pos hL).le
  have := (regParticlesOf sys).maxMass_pos
  positivity

lemma bG1_nonneg (hL : 0 < L) : 0 ≤ bG1 sys L Hunit := by
  unfold bG1
  obtain ⟨hBlow, hCs, hBker, -, -, -⟩ := molecularCanonicalTailConstants_spec L hL
  have := gtcSum_nonneg hL (finiteCoulombPhysicalMassConstant_nonneg sys L Hunit) hBlow hCs hBker
  have := gF_pos hL
  have := sys.one_le_maxMass
  positivity

lemma zetaG_nonneg (hL : 0 < L) : 0 ≤ zetaG sys L Hunit := by
  unfold zetaG ellG epsG
  have := cTr_nonneg sys hL Hunit
  have := bG0_nonneg (sys := sys) (Hunit := Hunit) hL
  have := gF_pos hL
  have := two_le_shiftC sys L Hunit
  have := sys.one_le_maxMass
  positivity

lemma omegaG_nonneg (hL : 0 < L) (T₀ : ℕ) : 0 ≤ omegaG sys L Hunit T₀ := by
  unfold omegaG ellG epsG
  have := cTr_nonneg sys hL Hunit
  have := bG0_nonneg (sys := sys) (Hunit := Hunit) hL
  have := bG1_nonneg (sys := sys) (Hunit := Hunit) hL
  have := gF_pos hL
  have := two_le_shiftC sys L Hunit
  have := sys.one_le_maxMass
  positivity

lemma gammaG_nonneg (hL : 0 < L) (T₀ : ℕ) : 0 ≤ gammaG sys L Hunit T₀ := by
  unfold gammaG
  have := omegaG_nonneg (sys := sys) (Hunit := Hunit) hL T₀
  have := zetaG_nonneg (sys := sys) (Hunit := Hunit) hL
  have := cPr_nonneg (sys := sys) (Hunit := Hunit) hL
  have := Zc_nonneg (P := regParticlesOf sys) (D := (posNucleiOf sys.nuclei).toNucData)
    (coulombCellAmplitude_pos hL).le
  have := (regParticlesOf sys).maxMass_pos
  have := gF_pos hL
  positivity

lemma gridC_nonneg (hL : 0 < L) (T₀ : ℕ) : 0 ≤ gridC sys L Hunit T₀ := by
  unfold gridC
  have := zetaG_nonneg (sys := sys) (Hunit := Hunit) hL
  have := gammaG_nonneg (sys := sys) (Hunit := Hunit) hL T₀
  have := cPr_nonneg (sys := sys) (Hunit := Hunit) hL
  have := fG_grid_nonneg (sys := sys) (Hunit := Hunit) hL
  have :=
      dG_grid_nonneg (sys := sys) (Hunit := Hunit) hL (cPr_nonneg (sys := sys) (Hunit := Hunit) hL)
  have := cTr_nonneg sys hL Hunit
  have hε : 0 ≤ epsG sys L Hunit := by unfold epsG; positivity
  have := sys.one_le_maxMass
  positivity

end Constant

/-! ## The explicit grid estimate -/

/-- The scale arithmetic of the grid comparison with `Λ = K²/(1024 m̄)`. -/
lemma gscale_arith {K mb c cg Ks : ℝ} (hK8 : 8 ≤ K) (hmb : 1 ≤ mb) (hc : 2 ≤ c) (hcg : 0 ≤ cg)
    (hKbig : 2048 * mb * (1 + c + cg) ≤ K ^ 2) (hKs : K / 8 ≤ Ks) :
    2 * (1 + c + cg) ≤ K ^ 2 / (1024 * mb) ∧
      K ^ 2 / (1024 * mb) + c ≤ Ks ^ 2 / (4 * mb) ∧
      K ^ 2 / (1024 * mb) + c ≤ (2 * K) ^ 2 / (4 * mb) ∧
      4 * mb * (2 * (K ^ 2 / (1024 * mb)) + cg) ≤ Ks ^ 2 := by
  have hmb0 : 0 < mb := by linarith
  have hKs2 : K ^ 2 / 64 ≤ Ks ^ 2 := by
    have h := pow_le_pow_left₀ (by linarith) hKs 2
    rw [div_pow] at h
    norm_num at h
    linarith
  have hcK : c * (2048 * mb) ≤ K ^ 2 := by nlinarith
  have hcgK : cg * (2048 * mb) ≤ K ^ 2 := by nlinarith
  have hΛ : K ^ 2 / (1024 * mb) * (4 * mb) = K ^ 2 / 256 := by
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · rw [le_div_iff₀ (by positivity), add_mul, hΛ]
    nlinarith
  · rw [le_div_iff₀ (by positivity), add_mul, hΛ]
    nlinarith
  · have e : 4 * mb * (2 * (K ^ 2 / (1024 * mb)) + cg) = K ^ 2 / 128 + 4 * mb * cg := by
      field_simp
      ring
    rw [e]
    nlinarith

/-- `log(2 + 2Λ) ≤ 2 log(2 + K)` for `Λ = K²/(1024 m̄)`. -/
lemma log_two_add_Lambda_le {K mb : ℝ} (hK : 0 ≤ K) (hmb : 1 ≤ mb) :
    Real.log (2 + 2 * (K ^ 2 / (1024 * mb))) ≤ 2 * Real.log (2 + K) := by
  have h0 : 0 ≤ K ^ 2 := sq_nonneg K
  have h1 : 2 * (K ^ 2 / (1024 * mb)) ≤ K ^ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : 2 + 2 * (K ^ 2 / (1024 * mb)) ≤ (2 + K) ^ 2 := by nlinarith
  have h3 : 0 < 2 + 2 * (K ^ 2 / (1024 * mb)) := by positivity
  calc Real.log (2 + 2 * (K ^ 2 / (1024 * mb))) ≤ Real.log ((2 + K) ^ 2) :=
        Real.log_le_log h3 h2
    _ = 2 * Real.log (2 + K) := by rw [Real.log_pow]; norm_num

/-- `3 g² m √m = 3 √g K √K` for `K = g m`. -/
lemma three_g2_msqrtm {g : ℝ} (hg : 0 < g) {m : ℝ} (_hm : 0 ≤ m) :
    3 * g ^ 2 * (m * Real.sqrt m) = 3 * Real.sqrt g * ((g * m) * Real.sqrt (g * m)) := by
  rw [Real.sqrt_mul hg.le]
  have hsg : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg.le
  have hsg0 : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
  set sg := Real.sqrt g
  rw [← hsg]
  ring

/-- **The final arithmetic of the grid comparison** (pure real inequalities). -/
lemma grid_assemble {K sK X t Q lg e Λ d c' δ δG F fG ζ γ a0 ε₁ mb A B D Cx Cy : ℝ}
    (hK1 : 1 ≤ K) (hsK0 : 0 < sK) (hX : 0 ≤ X) (hQ1 : 1 ≤ Q)
    (hlg0 : 0 ≤ t + lg) (hlg : t + lg ≤ 2 * Q) (hmb : 1 ≤ mb) (hΛ : Λ * (1024 * mb) = K ^ 2)
    (hdΛ : d ≤ Λ / 2) (he : e ≤ ε₁ * X / K ^ 4)
    (hc' : 0 ≤ c') (hδ : δ ≤ δG / K ^ 3) (hF : F ≤ fG / sK)
    (hζ : 0 ≤ ζ) (hγ : 0 ≤ γ) (ha0 : 0 ≤ a0) (hε : 0 ≤ ε₁) (hδG : 0 ≤ δG) (hfG : 0 ≤ fG)
    (hA : A ≤ a0 * X ^ 2 / K ^ 3) (hB : B ≤ e * (2 * (ζ * X))) (hD : D ≤ e * (2 * (ζ * X)))
    (hCx : Cx ≤ 48 * δ * (t + lg) * ((1 + c') ^ 2 * X) * (ζ * X) +
      2 * (F / (Λ - d)) * ((1 + c') * X) * (γ * (K * sK) * X / (2 * Λ)))
    (hCy : Cy ≤ 48 * δ * (t + lg) * ((1 + c') ^ 2 * X) * (ζ * X) +
      2 * (F / (Λ - d)) * ((1 + c') * X) * (γ * (K * sK) * X / (2 * Λ))) :
    A + B + D + Cx + Cy ≤ (a0 + 4 * ε₁ * ζ + 4 * fG * (1 + c') * γ * (1024 * mb) ^ 2 +
      192 * δG * (1 + c') ^ 2 * ζ) * X ^ 2 * Q / K ^ 3 := by
  have hK0 : 0 < K := by linarith
  have hK3 : 0 < K ^ 3 := by positivity
  have hmb0 : 0 < mb := by linarith
  have hΛ0 : 0 < Λ := by
    have : 0 < K ^ 2 := by positivity
    have h2 : 0 < Λ * (1024 * mb) := by rw [hΛ]; exact this
    exact pos_of_mul_pos_left h2 (by positivity)
  have hΛd : Λ / 2 ≤ Λ - d := by linarith
  have hΛd0 : 0 < Λ - d := by linarith
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
  -- the projection piece
  have pA : A ≤ a0 * X ^ 2 * Q / K ^ 3 := by
    refine hA.trans ?_
    apply div_le_div_of_nonneg_right _ hK3.le
    exact le_mul_of_one_le_right (mul_nonneg ha0 hX2) hQ1
  -- the filter pieces
  have pB : e * (2 * (ζ * X)) ≤ 2 * ε₁ * ζ * X ^ 2 * Q / K ^ 3 := by
    have h1 : e * (2 * (ζ * X)) ≤ ε₁ * X / K ^ 4 * (2 * (ζ * X)) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    refine h1.trans ?_
    have hK43 : K ^ 3 ≤ K ^ 4 := by
      calc K ^ 3 = K ^ 3 * 1 := by ring
        _ ≤ K ^ 3 * K := by gcongr
        _ = K ^ 4 := by ring
    have h2 : ε₁ * X / K ^ 4 * (2 * (ζ * X)) = 2 * ε₁ * ζ * X ^ 2 / K ^ 4 := by ring
    rw [h2]
    calc 2 * ε₁ * ζ * X ^ 2 / K ^ 4 ≤ 2 * ε₁ * ζ * X ^ 2 / K ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) hK3 hK43
      _ ≤ 2 * ε₁ * ζ * X ^ 2 * Q / K ^ 3 := by
          apply div_le_div_of_nonneg_right _ hK3.le
          exact le_mul_of_one_le_right (by positivity) hQ1
  -- the dyadic part of the core
  have pC1 : 48 * δ * (t + lg) * ((1 + c') ^ 2 * X) * (ζ * X) ≤
      96 * δG * (1 + c') ^ 2 * ζ * X ^ 2 * Q / K ^ 3 := by
    have h1 : 48 * δ * (t + lg) * ((1 + c') ^ 2 * X) * (ζ * X) ≤
        48 * (δG / K ^ 3) * (2 * Q) * ((1 + c') ^ 2 * X) * (ζ * X) := by gcongr
    refine h1.trans (le_of_eq ?_)
    field_simp
    ring
  -- the separated part of the core
  have pC2 : 2 * (F / (Λ - d)) * ((1 + c') * X) * (γ * (K * sK) * X / (2 * Λ)) ≤
      2 * fG * (1 + c') * γ * (1024 * mb) ^ 2 * X ^ 2 * Q / K ^ 3 := by
    have hFd : F / (Λ - d) ≤ fG / sK / (Λ / 2) := by
      calc F / (Λ - d) ≤ fG / sK / (Λ - d) := div_le_div_of_nonneg_right hF hΛd0.le
        _ ≤ fG / sK / (Λ / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hΛd
    have h1 : 2 * (F / (Λ - d)) * ((1 + c') * X) * (γ * (K * sK) * X / (2 * Λ)) ≤
        2 * (fG / sK / (Λ / 2)) * ((1 + c') * X) * (γ * (K * sK) * X / (2 * Λ)) := by gcongr
    refine h1.trans ?_
    have hΛe : Λ = K ^ 2 / (1024 * mb) := by
      rw [eq_div_iff (by positivity)]
      exact hΛ
    have h2 : 2 * (fG / sK / (Λ / 2)) * ((1 + c') * X) * (γ * (K * sK) * X / (2 * Λ)) =
        2 * fG * (1 + c') * γ * (1024 * mb) ^ 2 * X ^ 2 / K ^ 3 := by
      rw [hΛe]
      field_simp
    rw [h2]
    apply div_le_div_of_nonneg_right _ hK3.le
    have : 0 ≤ 2 * fG * (1 + c') * γ * (1024 * mb) ^ 2 * X ^ 2 := by positivity
    exact le_mul_of_one_le_right this hQ1
  have hfin : (a0 + 4 * ε₁ * ζ + 4 * fG * (1 + c') * γ * (1024 * mb) ^ 2 +
      192 * δG * (1 + c') ^ 2 * ζ) * X ^ 2 * Q / K ^ 3 =
      a0 * X ^ 2 * Q / K ^ 3 + 2 * (2 * ε₁ * ζ * X ^ 2 * Q / K ^ 3) +
        2 * (96 * δG * (1 + c') ^ 2 * ζ * X ^ 2 * Q / K ^ 3 +
          2 * fG * (1 + c') * γ * (1024 * mb) ^ 2 * X ^ 2 * Q / K ^ 3) := by ring
  rw [hfin]
  linarith [hB.trans pB, hD.trans pB, hCx.trans (add_le_add pC1 pC2),
    hCy.trans (add_le_add pC1 pC2)]

section Explicit

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

set_option maxHeartbeats 1000000 in
include hKernel hL hPeriodic in
/-- **The grid kinetic estimate with explicit constant**: under the scale conditions
`m ≥ 8`, `K = g m ≥ 8`, `K² ≥ 2048 m̄ (1 + c + c_gr)` and `max(4, 1/g) ≤ T₀ ≤ m`,
`|⟨ψ(t), T_p ψ(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C(T₀) Ξ² [1 + t + log(2 + K)]/K³`. -/
theorem grid_kinetic_explicit (p₀ : Fin eta) {c : ℝ} (E : ExactEigen L H c)
    (hcdef : c = shiftC sys L Hunit) (m : ℕ) (hm : 8 ≤ m) (hK8 : 8 ≤ gF L * m)
    (hKbig : 2048 * sys.maxMass * (1 + c + cGr (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) (2 * Real.pi / L)) ≤
        (gF L * m) ^ 2)
    {T₀ : ℕ} (hT₀4 : 4 ≤ T₀) (hT₀g : 1 ≤ gF L * T₀) (hT₀m : T₀ ≤ m)
    {κ : Lat3 → ℝ} (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgcomm : ∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      κ (2 * Real.pi / L) (Ug t x))
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t)
    (D : EvoData L H) {t : ℝ} (ht : 0 ≤ t) :
    |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
        regExpect sys (gF L) p₀ (Ug t (regCoeff m (Sm eta L D.u₀)))| ≤
      gridC sys L Hunit T₀ * D.Xi ^ 2 * (1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3 := by
  classical
  -- scales
  have hg : 0 < gF L := gF_pos hL
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hK0 : 0 < gF L * m := by positivity
  have hK1 : 1 ≤ gF L * (m : ℝ) := by linarith
  have hmb1 : 1 ≤ sys.maxMass := sys.one_le_maxMass
  have hc2 : 2 ≤ c := hcdef ▸ two_le_shiftC sys L Hunit
  have hcg0 := cGr_nonneg (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (2 * Real.pi / L) (coulombCellAmplitude_pos hL).le
  obtain ⟨hKs, -⟩ := quarter_scales hg hm
  obtain ⟨hΛbig, hΛs, hΛ2', hΛg'⟩ := gscale_arith hK8 hmb1 hc2 hcg0 hKbig hKs
  have hs2 : (2 : ℝ) ≤ ((m / 4 : ℕ) : ℝ) := (quarter_bounds hm).2.2
  have h2m : gF L * ((2 * m : ℕ) : ℝ) = 2 * (gF L * m) := by
    push_cast
    ring
  have hKs1 : 1 ≤ gF L * ((m / 4 : ℕ) : ℝ) := by linarith
  have hKs2 : 2 * gF L ≤ gF L * ((m / 4 : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hs2 hg.le
    linarith
  have hK21 : 1 ≤ gF L * ((2 * m : ℕ) : ℝ) := by rw [h2m]; linarith
  have hK22 : 2 * gF L ≤ gF L * ((2 * m : ℕ) : ℝ) := by
    rw [h2m]
    have : 2 * gF L ≤ gF L * m := by
      have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ m by linarith) hg.le
      linarith
    linarith
  have hΛ2 : (gF L * m) ^ 2 / (1024 * sys.maxMass) + c ≤
      (gF L * ((2 * m : ℕ) : ℝ)) ^ 2 / (4 * sys.maxMass) := by rw [h2m]; exact hΛ2'
  have hΛg : 4 * (regParticlesOf sys).maxMass * (2 * ((gF L * m) ^ 2 / (1024 * sys.maxMass)) +
      cGr (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
        (2 * Real.pi / L)) ≤ (2 * Real.pi / L) ^ 2 * (((m / 4 : ℕ) : ℝ) + 1) ^ 2 := by
    refine hΛg'.trans ?_
    change (gF L * ((m / 4 : ℕ) : ℝ)) ^ 2 ≤ gF L ^ 2 * (((m / 4 : ℕ) : ℝ) + 1) ^ 2
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hg.le) 2
  have hΛ1 : 1 ≤ (gF L * m) ^ 2 / (1024 * sys.maxMass) := by linarith
  have hdΛ : cGr (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
      (2 * Real.pi / L) + 1 < (gF L * m) ^ 2 / (1024 * sys.maxMass) := by linarith
  have hd0 : 0 ≤ cGr (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (coulombCellAmplitude L) (2 * Real.pi / L) + 1 := by linarith
  have hc1 : ∀ a : GrIdx eta m, 1 ≤ grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) hκ.even a + (c + (cGr (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) (2 * Real.pi / L) + 1)) :=
    fun a => by
      have := grE_lower (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
        hκ.even (coulombCellAmplitude_pos hL).le hκ.bound hg a
      linarith
  -- the filter
  have hΞ := D.Xi_nonneg
  have hΛ0 : 0 < (gF L * m) ^ 2 / (1024 * sys.maxMass) := by linarith
  have hHs2 : ‖ExactEigen.Hs2 (c := c) D‖ ≤ (1 + c) ^ 2 * D.Xi := by
    have := ExactEigen.norm_Hs2_le (c := c) D
    rwa [abs_of_pos (by linarith)] at this
  have hε₁ : epsG sys L Hunit = (1 + c) ^ 2 * (1024 * sys.maxMass) ^ 2 := by
    rw [hcdef]
    rfl
  have he : ‖Sm eta L D.u₀ - E.proj (E.finite ((gF L * m) ^ 2 / (1024 * sys.maxMass))).toFinset
      (Sm eta L D.u₀)‖ ≤ epsG sys L Hunit * D.Xi / (gF L * m) ^ 4 := by
    refine (E.norm_sub_proj_le _ hΛ0 _ (ExactEigen.Hs2 (c := c) D) fun i hi => ?_).trans ?_
    · have hi' : (gF L * m) ^ 2 / (1024 * sys.maxMass) < E.nu i := by
        by_contra h
        exact hi (by simpa using not_lt.mp h)
      rw [E.inner_b_Hs2 sys hKernel D i, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (E.nu_pos i)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hΛ0.le hi'.le 2) (norm_nonneg _)
    · have e1 : epsG sys L Hunit * D.Xi / (gF L * m) ^ 4 =
          (1 + c) ^ 2 * D.Xi / ((gF L * m) ^ 2 / (1024 * sys.maxMass)) ^ 2 := by
        rw [hε₁]
        field_simp
      rw [e1]
      exact div_le_div_of_nonneg_right hHs2 (by positivity)
  -- abbreviations
  set K := gF L * (m : ℝ) with hKdef
  set Λ := K ^ 2 / (1024 * sys.maxMass) with hΛdef
  set cg := cGr (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
    (2 * Real.pi / L) with hcg
  set X := D.Xi with hX
  set ψ₀ := Sm eta L D.u₀ with hψ₀
  set p := E.proj (E.finite Λ).toFinset ψ₀ with hpdef
  set e := ‖ψ₀ - p‖ with hedef
  have he0 : 0 ≤ e := norm_nonneg _
  -- the four register states
  set φe := regCoeff m (D.U t ψ₀) with hφe
  set φg := Ug t (regCoeff m ψ₀) with hφg
  set x := regCoeff m (D.U t p) with hxdef
  set y := Ug t (regCoeff m p) with hydef
  have hφx : ‖φe - x‖ ≤ e := by
    rw [hφe, hxdef, ← map_sub, ← map_sub]
    exact (norm_regCoeff_le _).trans (le_of_eq (LinearIsometryEquiv.norm_map _ _))
  have hφy : ‖y - φg‖ ≤ e := by
    rw [hφg, hydef, ← map_sub, LinearIsometryEquiv.norm_map, ← map_sub]
    exact (norm_regCoeff_le _).trans (le_of_eq (norm_sub_rev _ _))
  -- the four pieces
  have hA := grid_proj_term sys H hKernel Hunit hL hPeriodic D t m hK21 p₀
  have hB := regExpect_pair_le sys (gF L) p₀ φe x
  have hC := regExpect_sub_le sys (gF L) p₀ x y
  have hD := regExpect_pair_le sys (gF L) p₀ y φg
  -- polynomial factors of the register
  have hcT := cTr_nonneg sys hL Hunit
  have hε0 : 0 ≤ epsG sys L Hunit := by rw [hε₁]; positivity
  have hℓ0 : 0 ≤ 12 * (eta : ℝ) / gF L ^ 2 := by positivity
  have hℓ1 : 1 ≤ ellG (eta := eta) L := by
    unfold ellG
    linarith
  have hmK : (m : ℝ) = K / gF L := by
    rw [hKdef]
    field_simp
  have hK2 : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hK1
  have hpoly : 1 + 12 * (eta : ℝ) * (m : ℝ) ^ 2 ≤ ellG (eta := eta) L * K ^ 2 := by
    rw [hmK]
    unfold ellG
    have e : 12 * (eta : ℝ) * (K / gF L) ^ 2 = 12 * eta / gF L ^ 2 * K ^ 2 := by
      field_simp
    rw [e]
    linarith only [hK2]
  have hpoly0 : (0 : ℝ) ≤ 1 + 12 * (eta : ℝ) * (m : ℝ) ^ 2 := by positivity
  have hK4 : 0 < K ^ 4 := by positivity
  have hLe : gF L ^ 2 / 2 * (1 + 12 * (eta : ℝ) * (m : ℝ) ^ 2) * e ≤
      gF L ^ 2 / 2 * ellG (eta := eta) L * epsG sys L Hunit * X := by
    have h1 : gF L ^ 2 / 2 * (1 + 12 * (eta : ℝ) * (m : ℝ) ^ 2) * e ≤
        gF L ^ 2 / 2 * (ellG (eta := eta) L * K ^ 2) * (epsG sys L Hunit * X / K ^ 4) := by
      gcongr
    refine h1.trans ?_
    have h2 : gF L ^ 2 / 2 * (ellG (eta := eta) L * K ^ 2) * (epsG sys L Hunit * X / K ^ 4) =
        gF L ^ 2 / 2 * ellG (eta := eta) L * epsG sys L Hunit * X / K ^ 2 := by
      field_simp
    rw [h2]
    exact div_le_self (by positivity) hK2
  have hLe2 : gF L ^ 2 / 2 * (1 + 12 * (eta : ℝ) * (m : ℝ) ^ 2) ^ 2 * e ≤
      gF L ^ 2 / 2 * ellG (eta := eta) L ^ 2 * epsG sys L Hunit * X := by
    have h1 : gF L ^ 2 / 2 * (1 + 12 * (eta : ℝ) * (m : ℝ) ^ 2) ^ 2 * e ≤
        gF L ^ 2 / 2 * (ellG (eta := eta) L * K ^ 2) ^ 2 * (epsG sys L Hunit * X / K ^ 4) := by
      gcongr
    refine h1.trans (le_of_eq ?_)
    field_simp
  -- first graph bounds
  obtain ⟨hWe0, hWeT⟩ := exact_traj_shells sys H hKernel Hunit hL hPeriodic D t m p₀
  obtain ⟨hWg0, hWgT⟩ := grid_traj_shells sys H hKernel Hunit hL hPeriodic D m hm hK8 hκ Ug
    hgcomm t p₀
  have hb0 := bG0_nonneg (sys := sys) (Hunit := Hunit) hL
  have hb1 := bG1_nonneg (sys := sys) (Hunit := Hunit) hL
  have hTe : ‖wMul (regKinSym sys (gF L) p₀) φe‖ ≤
      gF L ^ 2 / 2 * ((1 + 2 / gF L ^ 2) * cTr sys L Hunit) * X := by
    refine (norm_regKin_le sys (gF L) p₀ φe).trans ?_
    calc gF L ^ 2 / 2 * ‖wMul (wM (regParticlesOf sys)) φe‖
        ≤ gF L ^ 2 / 2 * ((1 + 2 / gF L ^ 2) * (cTr sys L Hunit * X)) :=
          mul_le_mul_of_nonneg_left hWe0 (by positivity)
      _ = _ := by ring
  have hTg : ‖wMul (regKinSym sys (gF L) p₀) φg‖ ≤ gF L ^ 2 / 2 * bG0 sys L Hunit * X := by
    refine (norm_regKin_le sys (gF L) p₀ φg).trans ?_
    calc gF L ^ 2 / 2 * ‖wMul (wM (regParticlesOf sys)) φg‖
        ≤ gF L ^ 2 / 2 * (bG0 sys L Hunit * X) := mul_le_mul_of_nonneg_left hWg0 (by positivity)
      _ = _ := by ring
  have hTdx : ‖wMul (regKinSym sys (gF L) p₀) (φe - x)‖ ≤
      gF L ^ 2 / 2 * ellG (eta := eta) L * epsG sys L Hunit * X := by
    refine (norm_regKin_le_poly sys (gF L) p₀ _).trans (le_trans ?_ hLe)
    exact mul_le_mul_of_nonneg_left hφx (by positivity)
  have hTdy : ‖wMul (regKinSym sys (gF L) p₀) (y - φg)‖ ≤
      gF L ^ 2 / 2 * ellG (eta := eta) L * epsG sys L Hunit * X := by
    refine (norm_regKin_le_poly sys (gF L) p₀ _).trans (le_trans ?_ hLe)
    exact mul_le_mul_of_nonneg_left hφy (by positivity)
  have hζdef : zetaG sys L Hunit = gF L ^ 2 / 2 * ((1 + 2 / gF L ^ 2) * cTr sys L Hunit) +
      gF L ^ 2 / 2 * bG0 sys L Hunit + gF L ^ 2 / 2 * ellG (eta := eta) L * epsG sys L Hunit :=
    rfl
  have hτe0 : 0 ≤ gF L ^ 2 / 2 * ((1 + 2 / gF L ^ 2) * cTr sys L Hunit) * X := by positivity
  have hτg0 : 0 ≤ gF L ^ 2 / 2 * bG0 sys L Hunit * X := by positivity
  have hℓ10 : 0 ≤ gF L ^ 2 / 2 * ellG (eta := eta) L * epsG sys L Hunit * X := by positivity
  have hTx : ‖wMul (regKinSym sys (gF L) p₀) x‖ ≤ zetaG sys L Hunit * X := by
    have e1 : wMul (regKinSym sys (gF L) p₀) x =
        wMul (regKinSym sys (gF L) p₀) φe - wMul (regKinSym sys (gF L) p₀) (φe - x) := by
      rw [map_sub]
      abel
    rw [e1, hζdef]
    refine (norm_sub_le _ _).trans ?_
    linarith only [hTe, hTdx, hτg0]
  have hTy : ‖wMul (regKinSym sys (gF L) p₀) y‖ ≤ zetaG sys L Hunit * X := by
    have e1 : wMul (regKinSym sys (gF L) p₀) y =
        wMul (regKinSym sys (gF L) p₀) φg + wMul (regKinSym sys (gF L) p₀) (y - φg) := by
      rw [map_sub]
      abel
    rw [e1, hζdef]
    refine (norm_add_le _ _).trans ?_
    linarith only [hTg, hTdy, hτe0]
  have hTe' : ‖wMul (regKinSym sys (gF L) p₀) φe‖ ≤ zetaG sys L Hunit * X := by
    rw [hζdef]
    linarith only [hTe, hτg0, hℓ10]
  have hTg' : ‖wMul (regKinSym sys (gF L) p₀) φg‖ ≤ zetaG sys L Hunit * X := by
    rw [hζdef]
    linarith only [hTg, hτe0, hℓ10]
  -- the second weighted moments (layer cake)
  have hT₀1 : 1 ≤ T₀ := by omega
  have hsK0 : 0 < Real.sqrt K := Real.sqrt_pos.mpr (by linarith)
  have hKsK : 1 ≤ K * Real.sqrt K :=
    one_le_mul_of_one_le_of_one_le hK1 (Real.one_le_sqrt.mpr hK1)
  have hresc : 3 * gF L ^ 2 * ((m : ℝ) * Real.sqrt m) = 3 * Real.sqrt (gF L) * (K * Real.sqrt K) :=
    three_g2_msqrtm hg (Nat.cast_nonneg m)
  have hsg0 : 0 < Real.sqrt (gF L) := Real.sqrt_pos.mpr hg
  have hSE := norm_wM_regKin_shells sys (gF L) m (by omega) p₀ φe hT₀1 hT₀m hWe0
    (by positivity : 0 ≤ (1 + 2 / gF L ^ 2) * (cTr sys L Hunit * X) / Real.sqrt (gF L))
    (fun T hT1 _ => hWeT T (hT₀g.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hT1) hg.le)))
  have hSG := norm_wM_regKin_shells sys (gF L) m (by omega) p₀ φg hT₀1 hT₀m hWg0
    (by positivity : 0 ≤ bG1 sys L Hunit * X)
    (fun T hT1 hT2 => hWgT T (hT₀g.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hT1) hg.le))
      (hT₀4.trans hT1) hT2)
  set σe := 3 * Real.sqrt (gF L) * ((1 + 2 / gF L ^ 2) * cTr sys L Hunit) *
    (2 * (T₀ : ℝ) ^ 2 + 4 / Real.sqrt (gF L)) with hσe
  set σg := 3 * Real.sqrt (gF L) * (2 * (T₀ : ℝ) ^ 2 * bG0 sys L Hunit + 4 * bG1 sys L Hunit)
    with hσg
  set ℓ2 := gF L ^ 2 / 2 * ellG (eta := eta) L ^ 2 * epsG sys L Hunit with hℓ2
  have hσe0 : 0 ≤ σe := by positivity
  have hσg0 : 0 ≤ σg := by positivity
  have hℓ20 : 0 ≤ ℓ2 := by positivity
  have hSE' : ‖wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) φe)‖ ≤
      σe * (K * Real.sqrt K) * X := by
    refine hSE.trans (le_of_eq ?_)
    rw [hresc, hσe, ← hX]
    field_simp
  have hSG' : ‖wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) φg)‖ ≤
      σg * (K * Real.sqrt K) * X := by
    refine hSG.trans (le_of_eq ?_)
    rw [hresc, hσg, ← hX]
    ring
  have hWdx : ‖wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) (φe - x))‖ ≤
      ℓ2 * X := by
    refine (norm_wM_regKin_le_poly sys (gF L) p₀ _).trans (le_trans ?_ hLe2)
    exact mul_le_mul_of_nonneg_left hφx (by positivity)
  have hWdy : ‖wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) (y - φg))‖ ≤
      ℓ2 * X := by
    refine (norm_wM_regKin_le_poly sys (gF L) p₀ _).trans (le_trans ?_ hLe2)
    exact mul_le_mul_of_nonneg_left hφy (by positivity)
  have hωdef : omegaG sys L Hunit T₀ = σe + σg + ℓ2 := rfl
  have hℓ2K : ℓ2 * X ≤ ℓ2 * (K * Real.sqrt K) * X := by
    have h0 : 0 ≤ ℓ2 * X := by positivity
    calc ℓ2 * X = ℓ2 * X * 1 := by ring
      _ ≤ ℓ2 * X * (K * Real.sqrt K) := mul_le_mul_of_nonneg_left hKsK h0
      _ = _ := by ring
  have hWx : ‖wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) x)‖ ≤
      omegaG sys L Hunit T₀ * (K * Real.sqrt K) * X := by
    have e1 : wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) x) =
        wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) φe) -
          wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) (φe - x)) := by
      rw [map_sub, map_sub]
      abel
    rw [e1, hωdef]
    refine (norm_sub_le _ _).trans ?_
    have h3 : 0 ≤ σg * (K * Real.sqrt K) * X := by positivity
    linarith only [hSE', hWdx, hℓ2K, h3]
  have hWy : ‖wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) y)‖ ≤
      omegaG sys L Hunit T₀ * (K * Real.sqrt K) * X := by
    have e1 : wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) y) =
        wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) φg) +
          wMul (wM (regParticlesOf sys)) (wMul (regKinSym sys (gF L) p₀) (y - φg)) := by
      rw [map_sub, map_sub]
      abel
    rw [e1, hωdef]
    refine (norm_add_le _ _).trans ?_
    have h3 : 0 ≤ σe * (K * Real.sqrt K) * X := by positivity
    linarith only [hSG', hWdy, hℓ2K, h3]
  -- the grid graph norm of `T_p x`, `T_p y`
  set c' := c + (cg + 1) with hc'
  have hc'0 : 0 ≤ c' := by linarith
  have hc'def : c' = cPr sys L Hunit := by rw [hc', hcdef]; rfl
  have hζ0 : 0 ≤ zetaG sys L Hunit := zetaG_nonneg (sys := sys) (Hunit := Hunit) hL
  have hω0 : 0 ≤ omegaG sys L Hunit T₀ := omegaG_nonneg (sys := sys) (Hunit := Hunit) hL T₀
  have hγdef : gammaG sys L Hunit T₀ = 5 * gF L ^ 2 / 8 * omegaG sys L Hunit T₀ +
      (26 * ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) *
        (J0g ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
          (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (gF L) : ℝ) + c') *
        zetaG sys L Hunit := by
    rw [hc'def]
    rfl
  have hZJ : 0 ≤ 26 * ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) *
      (J0g ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (gF L) : ℝ) := by
    have := Zc_nonneg (P := regParticlesOf sys) (D := (posNucleiOf sys.nuclei).toNucData)
      (coulombCellAmplitude_pos hL).le
    have := (regParticlesOf sys).maxMass_pos
    positivity
  have hGz : ∀ z : EuclideanSpace ℂ (RCfg eta m),
      ‖z‖ ≤ zetaG sys L Hunit * X →
      ‖wMul (wM (regParticlesOf sys)) z‖ ≤ omegaG sys L Hunit T₀ * (K * Real.sqrt K) * X →
      ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) z‖ +
        c' * ‖z‖ ≤ gammaG sys L Hunit T₀ * (K * Real.sqrt K) * X := by
    intro z hz1 hz2
    have h := (gridRegHam (eta := eta) (m := m) (P := regParticlesOf sys)
      (D := (posNucleiOf sys.nuclei).toNucData) (coulombCellAmplitude_pos hL).le hκ.bound
      hg).op_le z
    rw [gridRegHam_op, gridRegHam_W, gridRegHam_g, gridRegHam_Z, gridRegHam_J0] at h
    change ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) z‖ ≤ _ at h
    rw [hγdef]
    have hA1 : 5 * gF L ^ 2 / 8 * ‖wMul (wM (regParticlesOf sys)) z‖ ≤
        5 * gF L ^ 2 / 8 * (omegaG sys L Hunit T₀ * (K * Real.sqrt K) * X) :=
      mul_le_mul_of_nonneg_left hz2 (by positivity)
    have hA2 : (26 * ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) *
        (J0g ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
          (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (gF L) : ℝ) + c') * ‖z‖ ≤
        (26 * ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
          (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) *
          (J0g ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
            (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (gF L) : ℝ) + c') *
          (zetaG sys L Hunit * X) := mul_le_mul_of_nonneg_left hz1 (add_nonneg hZJ hc'0)
    have hA3 : (26 * ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) *
        (J0g ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
          (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (gF L) : ℝ) + c') *
          (zetaG sys L Hunit * X) ≤
        (26 * ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
          (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) *
          (J0g ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
            (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (gF L) : ℝ) + c') *
          zetaG sys L Hunit * (K * Real.sqrt K) * X := by
      have h0 : 0 ≤ (26 * ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
          (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) *
          (J0g ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
            (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (gF L) : ℝ) + c') *
          zetaG sys L Hunit * X :=
        mul_nonneg (mul_nonneg (add_nonneg hZJ hc'0) hζ0) hΞ
      calc _ = (26 * ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
            (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) *
            (J0g ((regParticlesOf sys).maxMass * Zc (regParticlesOf sys)
              (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)) (gF L) : ℝ) + c') *
            zetaG sys L Hunit * X * 1 := by ring
        _ ≤ _ * (K * Real.sqrt K) := mul_le_mul_of_nonneg_left hKsK h0
        _ = _ := by ring
    have hz0 := norm_nonneg z
    linarith only [h, hA1, hA2, hA3]
  -- the core comparison paired with `T_p x` and `T_p y`
  have hHs2' : ‖ExactEigen.Hs2 (c := c') D‖ ≤ (1 + c') ^ 2 * X := by
    have := ExactEigen.norm_Hs2_le (c := c') D
    rwa [abs_of_nonneg hc'0] at this
  have hHs1' : ‖Hs1 c' D‖ ≤ (1 + c') * X := norm_Hs1_le hc'0 D
  have hcore : ∀ z : EuclideanSpace ℂ (RCfg eta m),
      ‖z‖ ≤ zetaG sys L Hunit * X →
      ‖wMul (wM (regParticlesOf sys)) z‖ ≤ omegaG sys L Hunit T₀ * (K * Real.sqrt K) * X →
      ‖⟪x - y, z⟫_ℂ‖ ≤ 48 * dRawG sys L Hunit c' m * (t + Real.log (2 + 2 * Λ)) *
          ((1 + c') ^ 2 * X) * (zetaG sys L Hunit * X) +
        2 * (fRawG sys L Hunit m / (Λ - (cg + 1))) * ((1 + c') * X) *
          (gammaG sys L Hunit T₀ * (K * Real.sqrt K) * X / (2 * Λ)) := by
    intro z hz1 hz2
    have h := grid_core_pair sys H hKernel Hunit hL hPeriodic E hcdef hd0 m hm hκ Ug hg0 hgderiv
      hc1 hΛ1 hdΛ hKs1 hKs2 hK21 hK22 hΛs hΛ2 hΛg D ht z
    refine h.trans ?_
    have hδ0 := dRawG_nonneg (sys := sys) (Hunit := Hunit) hL hc'0 m
    have hF0 : 0 ≤ fRawG sys L Hunit m / (Λ - (cg + 1)) :=
      div_nonneg (fRawG_nonneg (sys := sys) (Hunit := Hunit) hL m) (by linarith)
    have hlg : 0 ≤ t + Real.log (2 + 2 * Λ) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 2 * Λ by linarith)
      linarith
    have hGz' := hGz z hz1 hz2
    have hΛ2pos : 0 < 2 * Λ := by linarith
    gcongr
  have hCx := hcore _ hTx hWx
  have hCy := hcore _ hTy hWy
  -- assemble
  have hA' : |(regKin sys (gF L) p₀).expect (D.U t ψ₀) - regExpect sys (gF L) p₀ φe| ≤
      (eta : ℝ) ^ 2 * cTr sys L Hunit ^ 2 * X ^ 2 / K ^ 3 := by
    refine hA.trans ?_
    rw [h2m]
    have hK3 : 0 < K ^ 3 := by positivity
    calc (eta : ℝ) ^ 2 * (cTr sys L Hunit * X) ^ 2 / (2 * K) ^ 3
        ≤ (eta : ℝ) ^ 2 * (cTr sys L Hunit * X) ^ 2 / K ^ 3 :=
          div_le_div_of_nonneg_left (by positivity) hK3
            (pow_le_pow_left₀ hK0.le (by linarith) 3)
      _ = _ := by ring
  have hB' : |regExpect sys (gF L) p₀ φe - regExpect sys (gF L) p₀ x| ≤
      e * (2 * (zetaG sys L Hunit * X)) := by
    refine hB.trans ?_
    calc ‖φe - x‖ * (‖wMul (regKinSym sys (gF L) p₀) φe‖ + ‖wMul (regKinSym sys (gF L) p₀) x‖)
        ≤ e * (zetaG sys L Hunit * X + zetaG sys L Hunit * X) :=
          mul_le_mul hφx (add_le_add hTe' hTx) (by positivity) he0
      _ = _ := by ring
  have hD' : |regExpect sys (gF L) p₀ y - regExpect sys (gF L) p₀ φg| ≤
      e * (2 * (zetaG sys L Hunit * X)) := by
    refine hD.trans ?_
    calc ‖y - φg‖ * (‖wMul (regKinSym sys (gF L) p₀) y‖ + ‖wMul (regKinSym sys (gF L) p₀) φg‖)
        ≤ e * (zetaG sys L Hunit * X + zetaG sys L Hunit * X) :=
          mul_le_mul hφy (add_le_add hTy hTg') (by positivity) he0
      _ = _ := by ring
  have htri : |(regKin sys (gF L) p₀).expect (D.U t ψ₀) - regExpect sys (gF L) p₀ φg| ≤
      |(regKin sys (gF L) p₀).expect (D.U t ψ₀) - regExpect sys (gF L) p₀ φe| +
        |regExpect sys (gF L) p₀ φe - regExpect sys (gF L) p₀ x| +
        |regExpect sys (gF L) p₀ y - regExpect sys (gF L) p₀ φg| +
        ‖⟪x - y, wMul (regKinSym sys (gF L) p₀) x⟫_ℂ‖ +
        ‖⟪x - y, wMul (regKinSym sys (gF L) p₀) y⟫_ℂ‖ := by
    have h1 := abs_sub_le ((regKin sys (gF L) p₀).expect (D.U t ψ₀))
      (regExpect sys (gF L) p₀ φe) (regExpect sys (gF L) p₀ φg)
    have h2 := abs_sub_le (regExpect sys (gF L) p₀ φe) (regExpect sys (gF L) p₀ x)
      (regExpect sys (gF L) p₀ φg)
    have h3 := abs_sub_le (regExpect sys (gF L) p₀ x) (regExpect sys (gF L) p₀ y)
      (regExpect sys (gF L) p₀ φg)
    linarith only [h1, h2, h3, hC]
  have hlogΛ : Real.log (2 + 2 * Λ) ≤ 2 * Real.log (2 + K) :=
    log_two_add_Lambda_le hK0.le hmb1
  have hlog0 : 0 ≤ Real.log (2 + K) := Real.log_nonneg (by linarith)
  have hQ1 : 1 ≤ 1 + t + Real.log (2 + K) := by linarith
  have hlgQ : t + Real.log (2 + 2 * Λ) ≤ 2 * (1 + t + Real.log (2 + K)) := by linarith
  have hlg0 : 0 ≤ t + Real.log (2 + 2 * Λ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 2 * Λ by linarith)
    linarith
  have hδ := dRawG_le (sys := sys) (Hunit := Hunit) hL hc'0 hm hK1
  have hF := fRawG_le (sys := sys) (Hunit := Hunit) hL hm hK1
  have hfin := grid_assemble (sK := Real.sqrt K) (mb := sys.maxMass) hK1 hsK0 hΞ hQ1 hlg0 hlgQ
    hmb1 (by rw [hΛdef]; field_simp) (show cg + 1 ≤ Λ / 2 by linarith) he hc'0 hδ hF hζ0
    (gammaG_nonneg (sys := sys) (Hunit := Hunit) hL T₀) (by positivity) hε0
    (dG_grid_nonneg (sys := sys) (Hunit := Hunit) hL hc'0)
    (fG_grid_nonneg (sys := sys) (Hunit := Hunit) hL) hA' hB' hD' hCx hCy
  refine htri.trans (hfin.trans (le_of_eq ?_))
  unfold gridC
  rw [← hc'def]

end Explicit

/-! ## Thresholds -/

section GridScales

variable (sys : CoulombSystem eta ν) (L Hunit : ℝ)

/-- The trajectory-shell threshold `T₀ = max(4, ⌈1/g⌉)`. -/
noncomputable def T0G : ℕ := max 4 ⌈1 / gF L⌉₊

/-- The register threshold `m₀ = max(8, ⌈8/g⌉, ⌈√(2048 m̄ (1 + c + c_gr))/g⌉, T₀)`. -/
noncomputable def mGrid : ℕ :=
  max (max 8 ⌈8 / gF L⌉₊) (max ⌈Real.sqrt (2048 * sys.maxMass * (1 + shiftC sys L Hunit +
    cGr (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
      (2 * Real.pi / L))) / gF L⌉₊ (T0G L))

variable {sys L Hunit}

lemma T0G_scales (hL : 0 < L) : 4 ≤ T0G L ∧ 1 ≤ gF L * T0G L := by
  have hg := gF_pos hL
  refine ⟨le_max_left _ _, ?_⟩
  have h1 : 1 / gF L ≤ (T0G L : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  rw [div_le_iff₀ hg] at h1
  linarith

/-- The scale conditions of `grid_kinetic_explicit` beyond `mGrid`. -/
lemma mGrid_scales (hL : 0 < L) {m : ℕ} (hm : mGrid sys L Hunit ≤ m) :
    8 ≤ m ∧ 8 ≤ gF L * m ∧
      2048 * sys.maxMass * (1 + shiftC sys L Hunit + cGr (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) (2 * Real.pi / L)) ≤
        (gF L * m) ^ 2 ∧ T0G L ≤ m := by
  have hg := gF_pos hL
  have h1 : max 8 ⌈8 / gF L⌉₊ ≤ m := le_trans (le_max_left _ _) hm
  have h2 : max ⌈Real.sqrt (2048 * sys.maxMass * (1 + shiftC sys L Hunit +
      cGr (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
        (2 * Real.pi / L))) / gF L⌉₊ (T0G L) ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨le_trans (le_max_left _ _) h1, ?_, ?_, le_trans (le_max_right _ _) h2⟩
  · have h8 : 8 / gF L ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) h1)
    rw [div_le_iff₀ hg] at h8
    linarith
  · have hc := two_le_shiftC sys L Hunit
    have hcg := cGr_nonneg (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) (coulombCellAmplitude_pos hL).le
    have hmb := sys.one_le_maxMass
    have hA0 : 0 ≤ 2048 * sys.maxMass * (1 + shiftC sys L Hunit + cGr (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) (2 * Real.pi / L)) := by
      positivity
    have hs : Real.sqrt (2048 * sys.maxMass * (1 + shiftC sys L Hunit + cGr (regParticlesOf sys)
        (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) (2 * Real.pi / L))) / gF L ≤
        (m : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_left _ _) h2)
    rw [div_le_iff₀ hg] at hs
    calc _ = Real.sqrt (2048 * sys.maxMass * (1 + shiftC sys L Hunit + cGr (regParticlesOf sys)
          (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) (2 * Real.pi / L))) ^ 2 :=
          (Real.sq_sqrt hA0).symm
      _ ≤ (gF L * m) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (by linarith) 2

end GridScales

/-- **The secant arithmetic** of `cor:stopping-log`: two pointwise bounds at `τ` and `0` give
the bound for the difference of the signed secants. -/
lemma secant_arith {a1 a0 b1 b0 C X vp τ K lg : ℝ} (hC : 0 ≤ C) (hvp : 0 < vp) (hτ : 0 < τ)
    (hK : 0 < K) (h1 : |a1 - b1| ≤ C * X ^ 2 * (1 + τ + lg) / K ^ 3)
    (h0 : |a0 - b0| ≤ C * X ^ 2 * (1 + 0 + lg) / K ^ 3) :
    |(a1 - a0) / (vp * τ) - (b1 - b0) / (vp * τ)| ≤
      2 * C * X ^ 2 / vp * (1 + (1 + lg) / τ) / K ^ 3 := by
  have hvτ : 0 < vp * τ := mul_pos hvp hτ
  have e : (a1 - a0) / (vp * τ) - (b1 - b0) / (vp * τ) = ((a1 - b1) - (a0 - b0)) / (vp * τ) := by
    ring
  rw [e, abs_div, abs_of_pos hvτ, div_le_iff₀ hvτ]
  have hsum : |(a1 - b1) - (a0 - b0)| ≤ |a1 - b1| + |a0 - b0| := abs_sub _ _
  have hK3 : 0 < K ^ 3 := by positivity
  have e2 : 2 * C * X ^ 2 / vp * (1 + (1 + lg) / τ) / K ^ 3 * (vp * τ) =
      2 * C * X ^ 2 * (τ + (1 + lg)) / K ^ 3 := by
    field_simp
  have hCX : 0 ≤ C * X ^ 2 * τ := by positivity
  have hfin : C * X ^ 2 * (1 + τ + lg) / K ^ 3 + C * X ^ 2 * (1 + 0 + lg) / K ^ 3 ≤
      2 * C * X ^ 2 * (τ + (1 + lg)) / K ^ 3 := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hK3.le
    linarith only [hCX]
  rw [e2]
  linarith only [hsum, h1, h0, hfin]

/-! ## The grid endpoints -/

section GridEndpoint

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **`thm:kinetic-log`, grid case** (`eq:kinetic-log`): there are `C ≥ 0` and `m₀` such that
for every register radius `2m` with `m ≥ m₀` (`K = 2π m/L`), every kernel `κ` of the class
`IsGridKernel` (eq:kernelclass), every grid propagator `U_g` of `G = H_grid[κ]`, every datum
`ψ₀ ∈ D(H²)` and every `t ≥ 0`,
`|⟨ψ(t), T_{p₀} ψ(t)⟩ - ⟨ψ_g(t), T_{p₀} ψ_g(t)⟩| ≤ C 𝒟² [1 + t + log(2 + K)]/K³`,
where `ψ_g(t) = U_g(t) P' ψ₀` (not renormalised). -/
theorem thm_kinetic_log_grid (p₀ : Fin eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ {κ : Lat3 → ℝ},
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
  obtain ⟨E⟩ := exists_exactEigen sys H hKernel Hunit hL hPeriodic
  refine ⟨gridC sys L Hunit (T0G L), gridC_nonneg hL _, mGrid sys L Hunit,
    fun m hm κ hκ Ug hg0 hgcomm hgderiv D t ht => ?_⟩
  obtain ⟨hm8, hK8, hKbig, hT₀m⟩ := mGrid_scales hL hm
  obtain ⟨hT₀4, hT₀g⟩ := T0G_scales hL
  exact grid_kinetic_explicit sys H hKernel Hunit hL hPeriodic p₀ E rfl m hm8 hK8 hKbig hT₀4
    hT₀g hT₀m hκ Ug hg0 hgcomm hgderiv D ht

include hKernel hL hPeriodic in
/-- **`cor:stopping-log`, grid case** (`eq:stopping-log`): for every window `[0, τ]`, `τ > 0`,
and reference speed `v_p > 0`, the signed secants of the exact and grid trajectories differ by
at most `(C 𝒟²/v_p) [1 + (1 + log(2 + K))/τ]/K³`, uniformly over the kernel class and the grid
propagators. -/
theorem cor_stopping_log_grid (p₀ : Fin eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ {κ : Lat3 → ℝ},
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
  obtain ⟨C, hC, m₀, h⟩ := thm_kinetic_log_grid sys H hKernel Hunit hL hPeriodic p₀
  refine ⟨2 * C, by positivity, max m₀ (mGrid sys L Hunit),
    fun m hm κ hκ Ug hg0 hgcomm hgderiv D vp τ hvp hτ => ?_⟩
  have hm₀ : m₀ ≤ m := le_trans (le_max_left _ _) hm
  obtain ⟨-, hK8, -, -⟩ := mGrid_scales hL (le_trans (le_max_right _ _) hm)
  have hK0 : 0 < Kc L m := by change 0 < gF L * m; linarith
  exact secant_arith hC hvp hτ hK0 (h m hm₀ hκ Ug hg0 hgcomm hgderiv D τ hτ.le)
    (h m hm₀ hκ Ug hg0 hgcomm hgderiv D 0 le_rfl)

end GridEndpoint

end KineticLog
