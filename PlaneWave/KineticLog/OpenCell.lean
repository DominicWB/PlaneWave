import PlaneWave.KineticLog.OpenRates

/-!
# Logarithmic kinetic bound, part 23: the cell-to-grid kinetic estimate, uniform in `L`

The grid step of `prop:free-kinetic-log`: for the range-cut cell Hamiltonian `H_L` (`L ≥ 2π`),
every exact propagator of `H_L` (`EvoData`), every register radius `2m` with `m ≥ 8` and
`K = 2π m/L ≥ K₀`, every kernel of the open-grid class (`PlaneWaveGridG.IsGridKernel γ_L ρ_L m`,
agreement with `ĝ_L`), every grid propagator `U_g` and every `t ≥ 0`,

  `|⟨u_L(t), T_p u_L(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C_U 𝒟_*² [1 + t + log(2 + K)]/K³`,

with `ψ_g(t) = U_g(t) P' φ₀` (not renormalised), `𝒟_* = Ξ` the data norm of the cell datum and the
constants `C_U`, `K₀` independent of `L` (`cell_kinetic_explicit`, `thm_cell_kinetic_log_gL`).

The proof is that of the periodic grid case (`PlaneWave.KineticLog.GridEndpoint`) with the inputs
of `PlaneWave.KineticLog.OpenExact`–`.OpenRates` in the physical weight; the layer cake starts at
the physical threshold `g T₀ ∈ [1, 2]`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal
open FSGalerkin (Kc)

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The exact Fourier tail beyond the register cube -/

section ProjTermGL

variable (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (FreeBoundary.gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 2 * Real.pi ≤ L) (hθ : FreeBoundary.Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hH : 0 ≤ Hunit)

include hKernel hL hθ hPeriodic hH in
/-- **The exact Fourier tail of `H_L` beyond the register cube `2m`**: no cross term, and
`|⟨u(t), T_p u(t)⟩ - ⟨P' u(t), T_p P' u(t)⟩| ≤ 2 η² m̄ c_tr^U² Ξ²/K³`. -/
lemma grid_proj_term_gL (D : EvoData L H) (t : ℝ) (m : ℕ) (hK1 : 1 ≤ gF L * m) (p₀ : Fin eta) :
    |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
        regExpect sys (gF L) p₀ (regCoeff m (D.U t (Sm eta L D.u₀)))| ≤
      2 * (eta : ℝ) ^ 2 * sys.maxMass * cTrU sys (FreeBoundary.tv R θ) Hunit ^ 2 * D.Xi ^ 2 /
        (gF L * m) ^ 3 := by
  have hL0 := pos_of_two_pi_le hL
  have hV := hθ.tv_nonneg
  have hg := gF_pos hL0
  obtain ⟨w, hw1, -, hw3⟩ := traj_tails_gL sys H hKernel Hunit hL hθ hPeriodic hH D t
  set μ := regKin sys (gF L) p₀ with hμ
  set cT := cTrU sys (FreeBoundary.tv R θ) Hunit with hcT
  have hcT0 : 0 ≤ cT := cTrU_nonneg sys hV hH
  have hΞ := D.Xi_nonneg
  have hM := sys.maxMass_pos
  set K := gF L * (m : ℝ) with hKdef
  have hK0 : 0 < K := by linarith
  have h2m : gF L * ((2 * m : ℕ) : ℝ) = 2 * K := by push_cast; ring
  have hK2 : 1 ≤ gF L * ((2 * m : ℕ) : ℝ) := by rw [h2m]; linarith
  have hsplit := μ.expect_split (2 * m) w
  have htail0 := μ.expect_tail_nonneg (2 * m) w
  have htail := μ.expect_tail_le (2 * m) w
  have hS : ‖molecularH2StateMap eta (gF L) w - molecularH2Truncate (2 * m)
      (molecularH2StateMap eta (gF L) w)‖ ≤
      eta * (2 * sys.maxMass * (cT * D.Xi) / ((2 * K) ^ 2 * Real.sqrt (2 * K))) := by
    refine (PlaneWaveDynamics.norm_sub_truncate_le hg (2 * m) _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * ((2 * m : ℕ) : ℝ)) a
          (molecularH2StateMap eta (gF L) w)‖
        ≤ ∑ _a : Fin eta, 2 * sys.maxMass * (cT * D.Xi) / ((2 * K) ^ 2 * Real.sqrt (2 * K)) :=
          Finset.sum_le_sum fun a _ => by
            have h := (hw3 a _ hK2).2
            refine h.trans (le_of_eq ?_)
            rw [h2m]
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hT : ‖coulombFourierKineticH2 sys (gF L) w -
      molecularH2Truncate (2 * m) (coulombFourierKineticH2 sys (gF L) w)‖ ≤
      eta * (cT * D.Xi / Real.sqrt (2 * K)) := by
    refine (PlaneWaveDynamics.norm_sub_truncate_le hg (2 * m) _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * ((2 * m : ℕ) : ℝ)) a
          (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ ∑ _a : Fin eta, cT * D.Xi / Real.sqrt (2 * K) :=
          Finset.sum_le_sum fun a _ => by
            have h := (hw3 a _ hK2).1
            refine h.trans (le_of_eq ?_)
            rw [h2m]
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hproj : μ.expect (molecularH2StateMap eta (gF L) (w - molecularH2Truncate (2 * m) w)) ≤
      2 * (eta : ℝ) ^ 2 * sys.maxMass * cT ^ 2 * D.Xi ^ 2 / K ^ 3 := by
    refine htail.trans ?_
    have h1 := mul_le_mul hS hT (norm_nonneg _) (by positivity)
    refine h1.trans ?_
    have hs2K : Real.sqrt (2 * K) ^ 2 = 2 * K := Real.sq_sqrt (by linarith)
    have hs0 : 0 < Real.sqrt (2 * K) := Real.sqrt_pos.mpr (by linarith)
    have e : eta * (2 * sys.maxMass * (cT * D.Xi) / ((2 * K) ^ 2 * Real.sqrt (2 * K))) *
        (eta * (cT * D.Xi / Real.sqrt (2 * K))) =
        2 * (eta : ℝ) ^ 2 * sys.maxMass * cT ^ 2 * D.Xi ^ 2 / K ^ 3 / 8 := by
      field_simp
      rw [hs2K]
      ring
    rw [e]
    have h0 : 0 ≤ 2 * (eta : ℝ) ^ 2 * sys.maxMass * cT ^ 2 * D.Xi ^ 2 / K ^ 3 := by positivity
    linarith
  have hreg : μ.expect (molecularH2StateMap eta (gF L) (molecularH2Truncate (2 * m) w)) =
      regExpect sys (gF L) p₀ (regCoeff m (molecularH2StateMap eta (gF L) w)) :=
    expect_truncate_eq_reg sys (gF L) (m := m) p₀ w
  have hSw : molecularH2StateMap eta (gF L) w = D.U t (Sm eta L D.u₀) := hw1
  rw [← hSw, hsplit, hreg, add_sub_cancel_left, abs_of_nonneg htail0]
  exact hproj

end ProjTermGL

/-! ## The constants of the cell estimate -/

section ConstantU

variable (sys : CoulombSystem eta ν) (V Hunit : ℝ)

/-- The total shift `c' = c_U + c_g^U + 1`. -/
noncomputable def cPrU : ℝ := cU sys V Hunit + (cGrU sys V + 1)

/-- The filter constant `ε_U = (1 + c_U)² (1024 m̄)²`. -/
noncomputable def epsU : ℝ := (1 + cU sys V Hunit) ^ 2 * (1024 * sys.maxMass) ^ 2

/-- The first graph constant of `T_p x`, `T_p y`: `‖T_p ·‖ ≤ ζ Ξ`. -/
noncomputable def zetaU : ℝ :=
  1 / 2 * b0eU sys V Hunit + 1 / 2 * b0gU sys V Hunit + 1 / 2 * (1 + 12 * eta) * epsU sys V Hunit

/-- The second weighted constant: `‖w_g T_p ·‖ ≤ ω Ξ K^{3/2}`. -/
noncomputable def omegaU : ℝ :=
  12 * (b0eU sys V Hunit + (2 * sys.maxMass + 2) * cTrU sys V Hunit) +
    12 * (b0gU sys V Hunit + b1gU sys V Hunit) +
    1 / 2 * (1 + 12 * eta) ^ 2 * epsU sys V Hunit

/-- The constant of `‖(G + c') T_p ·‖ ≤ γ Ξ K^{3/2}`. -/
noncomputable def gammaU : ℝ :=
  5 / 8 * omegaU sys V Hunit + (PlaneWaveGridG.gLAU sys V + cPrU sys V Hunit) * zetaU sys V Hunit

/-- **The constant of the cell-to-grid kinetic estimate**, independent of `L`. -/
noncomputable def cellC : ℝ :=
  2 * (eta : ℝ) ^ 2 * sys.maxMass * cTrU sys V Hunit ^ 2 +
    4 * epsU sys V Hunit * zetaU sys V Hunit +
    4 * fU sys V Hunit * (1 + cPrU sys V Hunit) * gammaU sys V Hunit * (1024 * sys.maxMass) ^ 2 +
    192 * dU sys V Hunit (cPrU sys V Hunit) * (1 + cPrU sys V Hunit) ^ 2 * zetaU sys V Hunit

variable {sys V Hunit}

lemma cPrU_nonneg (hV : 0 ≤ V) : 0 ≤ cPrU sys V Hunit := by
  unfold cPrU
  have := two_le_cU sys V Hunit
  have := cGrU_nonneg sys hV
  linarith

lemma epsU_nonneg : 0 ≤ epsU sys V Hunit := by unfold epsU; positivity

lemma zetaU_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ zetaU sys V Hunit := by
  unfold zetaU
  have := b0eU_nonneg sys hV hH
  have := b0gU_nonneg sys hV hH
  have := epsU_nonneg (sys := sys) (V := V) (Hunit := Hunit)
  positivity

lemma omegaU_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ omegaU sys V Hunit := by
  unfold omegaU
  have := b0eU_nonneg sys hV hH
  have := b0gU_nonneg sys hV hH
  have := b1gU_nonneg sys hV hH
  have := cTrU_nonneg sys hV hH
  have := epsU_nonneg (sys := sys) (V := V) (Hunit := Hunit)
  have := sys.maxMass_pos
  positivity

lemma gammaU_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ gammaU sys V Hunit := by
  unfold gammaU
  have := omegaU_nonneg (sys := sys) hV hH
  have := zetaU_nonneg (sys := sys) hV hH
  have := cPrU_nonneg (sys := sys) (Hunit := Hunit) hV
  have : 0 ≤ PlaneWaveGridG.gLAU sys V := by
    unfold PlaneWaveGridG.gLAU
    have := PlaneWaveGridG.gLzU_nonneg sys hV
    positivity
  positivity

lemma cellC_nonneg (hV : 0 ≤ V) (hH : 0 ≤ Hunit) : 0 ≤ cellC sys V Hunit := by
  unfold cellC
  have := zetaU_nonneg (sys := sys) hV hH
  have := gammaU_nonneg (sys := sys) hV hH
  have := cPrU_nonneg (sys := sys) (Hunit := Hunit) hV
  have := fU_nonneg sys hV hH
  have := dU_nonneg sys hV hH (cPrU_nonneg (sys := sys) (Hunit := Hunit) hV)
  have := cTrU_nonneg sys hV hH
  have := epsU_nonneg (sys := sys) (V := V) (Hunit := Hunit)
  have := sys.maxMass_pos
  positivity

end ConstantU

lemma sq_div_sqrt_aux {s m B' : ℝ} (hs : 0 < s) :
    3 * (s ^ 2) ^ 2 * (4 * (m * Real.sqrt m) * (B' / s)) =
      12 * ((s ^ 2 * m) * (s * Real.sqrt m)) * B' := by
  field_simp
  ring

/-- `3 g² (T₀² B₀ + 4 m √m B'/√g) ≤ 12 B₀ + 12 K √K B'` for `g T₀ ≤ 2`, `K = g m`. -/
lemma layer_phys_arith {g T₀ m B₀ B' : ℝ} (hg : 0 < g) (hT₀ : g * T₀ ≤ 2)
    (hT₀0 : 0 ≤ T₀) (hB₀ : 0 ≤ B₀) :
    3 * g ^ 2 * (T₀ ^ 2 * B₀ + 4 * (m * Real.sqrt m) * (B' / Real.sqrt g)) ≤
      12 * B₀ + 12 * ((g * m) * Real.sqrt (g * m)) * B' := by
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
  have hsg2 : Real.sqrt g ^ 2 = g := Real.sq_sqrt hg.le
  have h1 : 3 * g ^ 2 * (T₀ ^ 2 * B₀) ≤ 12 * B₀ := by
    have : (g * T₀) ^ 2 ≤ 4 := by
      have h0 : 0 ≤ g * T₀ := by positivity
      nlinarith
    have e : 3 * g ^ 2 * (T₀ ^ 2 * B₀) = 3 * (g * T₀) ^ 2 * B₀ := by ring
    rw [e]
    nlinarith
  have h2 : 3 * g ^ 2 * (4 * (m * Real.sqrt m) * (B' / Real.sqrt g)) =
      12 * ((g * m) * Real.sqrt (g * m)) * B' := by
    have h := sq_div_sqrt_aux (m := m) (B' := B') hsg
    rw [hsg2] at h
    rw [Real.sqrt_mul hg.le]
    exact h
  have e : 3 * g ^ 2 * (T₀ ^ 2 * B₀ + 4 * (m * Real.sqrt m) * (B' / Real.sqrt g)) =
      3 * g ^ 2 * (T₀ ^ 2 * B₀) + 3 * g ^ 2 * (4 * (m * Real.sqrt m) * (B' / Real.sqrt g)) := by
    ring
  rw [e, h2]
  linarith

/-! ## The explicit cell estimate -/

section Explicit

variable (sys : CoulombSystem eta ν) {L R : ℝ} {θ : ℝ → ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (FreeBoundary.gLlatHam sys L θ) N u q)
  (Hunit : ℝ) (hL : 2 * Real.pi ≤ L) (hθ : FreeBoundary.Profile R θ)
  (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hH : 0 ≤ Hunit)

set_option maxHeartbeats 1000000 in
include hKernel hL hθ hPeriodic hH in
/-- **The cell-to-grid kinetic estimate with explicit `L`-free constant**: for the range-cut
cell Hamiltonian `H_L` (`L ≥ 2π`), under `m ≥ 8`, `K = g m ≥ 8`, `K² ≥ 2048 m̄ (1 + c_U + c_g^U)`
and a layer-cake threshold `T₀ ≥ 2` with `1 ≤ g T₀ ≤ 2`, `T₀ ≤ m`,
`|⟨u(t), T_p u(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C_U Ξ² [1 + t + log(2 + K)]/K³`. -/
theorem cell_kinetic_explicit (p₀ : Fin eta) {c : ℝ} (E : ExactEigen L H c)
    (hcdef : c = cU sys (FreeBoundary.tv R θ) Hunit) (m : ℕ) (hm : 8 ≤ m) (hK8 : 8 ≤ gF L * m)
    (hKbig : 2048 * sys.maxMass * (1 + c + cGrU sys (FreeBoundary.tv R θ)) ≤ (gF L * m) ^ 2)
    {T₀ : ℕ} (hT₀2 : 2 ≤ T₀) (hT₀g : 1 ≤ gF L * T₀) (hT₀g2 : gF L * T₀ ≤ 2) (hT₀m : T₀ ≤ m)
    {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ))
      (PlaneWaveGridG.gLref L θ (FreeBoundary.tv R θ)) m κ)
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
      cellC sys (FreeBoundary.tv R θ) Hunit * D.Xi ^ 2 * (1 + t + Real.log (2 + gF L * m)) /
        (gF L * m) ^ 3 := by
  classical
  -- scales
  have hL0 := pos_of_two_pi_le hL
  have hV : 0 ≤ FreeBoundary.tv R θ := hθ.tv_nonneg
  have hg : 0 < gF L := gF_pos hL0
  have hκb : ∀ x, |κ x| ≤ PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ) * coul x :=
    fun x => hκ.bound x
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hK0 : 0 < gF L * m := by positivity
  have hK1 : 1 ≤ gF L * (m : ℝ) := by linarith
  have hmb1 : 1 ≤ sys.maxMass := sys.one_le_maxMass
  have hc2 : 2 ≤ c := hcdef ▸ two_le_cU sys _ Hunit
  have hcg0 : 0 ≤ cGrU sys (FreeBoundary.tv R θ) := cGrU_nonneg sys hV
  obtain ⟨hKs, -⟩ := quarter_scales hg hm
  obtain ⟨hΛbig, hΛs, hΛ2', hΛg'⟩ := gscale_arith hK8 hmb1 hc2 hcg0 hKbig hKs
  have h2m : gF L * ((2 * m : ℕ) : ℝ) = 2 * (gF L * m) := by
    push_cast
    ring
  have hKs1 : 1 ≤ gF L * ((m / 4 : ℕ) : ℝ) := by linarith
  have hK21 : 1 ≤ gF L * ((2 * m : ℕ) : ℝ) := by rw [h2m]; linarith
  have hΛ2 : (gF L * m) ^ 2 / (1024 * sys.maxMass) + c ≤
      (gF L * ((2 * m : ℕ) : ℝ)) ^ 2 / (4 * sys.maxMass) := by rw [h2m]; exact hΛ2'
  have hΛg : 4 * sys.maxMass * (2 * ((gF L * m) ^ 2 / (1024 * sys.maxMass)) +
      cGrU sys (FreeBoundary.tv R θ)) ≤ (2 * Real.pi / L * (((m / 4 : ℕ) : ℝ) + 1)) ^ 2 := by
    refine hΛg'.trans ?_
    change (gF L * ((m / 4 : ℕ) : ℝ)) ^ 2 ≤ (gF L * (((m / 4 : ℕ) : ℝ) + 1)) ^ 2
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hg.le) 2
  have hΛ1 : 1 ≤ (gF L * m) ^ 2 / (1024 * sys.maxMass) := by linarith
  have hdΛ : cGrU sys (FreeBoundary.tv R θ) + 1 < (gF L * m) ^ 2 / (1024 * sys.maxMass) := by
    linarith
  have hd0 : 0 ≤ cGrU sys (FreeBoundary.tv R θ) + 1 := by linarith
  have hc1 : ∀ a : GrIdx eta m, 1 ≤ grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) hκ.even a + (c + (cGrU sys (FreeBoundary.tv R θ) + 1)) := fun a => by
    have := grE_lower_U sys hL hV hκ.even hκb a
    linarith
  -- the filter
  have hΞ := D.Xi_nonneg
  have hΛ0 : 0 < (gF L * m) ^ 2 / (1024 * sys.maxMass) := by linarith
  have hHs2 : ‖ExactEigen.Hs2 (c := c) D‖ ≤ (1 + c) ^ 2 * D.Xi := by
    have := ExactEigen.norm_Hs2_le (c := c) D
    rwa [abs_of_pos (by linarith)] at this
  have hε₁ : epsU sys (FreeBoundary.tv R θ) Hunit = (1 + c) ^ 2 * (1024 * sys.maxMass) ^ 2 := by
    rw [hcdef]
    rfl
  have hsym := FreeBoundary.gLH2_symm sys L θ H hKernel hθ
  have he : ‖Sm eta L D.u₀ - E.proj (E.finite ((gF L * m) ^ 2 / (1024 * sys.maxMass))).toFinset
      (Sm eta L D.u₀)‖ ≤ epsU sys (FreeBoundary.tv R θ) Hunit * D.Xi / (gF L * m) ^ 4 := by
    refine (E.norm_sub_proj_le _ hΛ0 _ (ExactEigen.Hs2 (c := c) D) fun i hi => ?_).trans ?_
    · have hi' : (gF L * m) ^ 2 / (1024 * sys.maxMass) < E.nu i := by
        by_contra h
        exact hi (by simpa using not_lt.mp h)
      rw [E.inner_b_Hs2_of_symm hsym D i, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (E.nu_pos i)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hΛ0.le hi'.le 2) (norm_nonneg _)
    · have e1 : epsU sys (FreeBoundary.tv R θ) Hunit * D.Xi / (gF L * m) ^ 4 =
          (1 + c) ^ 2 * D.Xi / ((gF L * m) ^ 2 / (1024 * sys.maxMass)) ^ 2 := by
        rw [hε₁]
        field_simp
      rw [e1]
      exact div_le_div_of_nonneg_right hHs2 (by positivity)
  -- abbreviations
  set K := gF L * (m : ℝ) with hKdef
  set Λ := K ^ 2 / (1024 * sys.maxMass) with hΛdef
  set cg := cGrU sys (FreeBoundary.tv R θ) with hcg
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
  have hA : |(regKin sys (gF L) p₀).expect (D.U t ψ₀) - regExpect sys (gF L) p₀ φe| ≤
      2 * (eta : ℝ) ^ 2 * sys.maxMass * cTrU sys (FreeBoundary.tv R θ) Hunit ^ 2 * X ^ 2 / K ^ 3 :=
    grid_proj_term_gL sys H hKernel Hunit hL hθ hPeriodic hH D t m hK1 p₀
  have hB := regExpect_pair_le sys (gF L) p₀ φe x
  have hC := regExpect_sub_le sys (gF L) p₀ x y
  have hD := regExpect_pair_le sys (gF L) p₀ y φg
  -- polynomial factors of the register
  have hb0e := b0eU_nonneg sys hV hH
  have hb0g := b0gU_nonneg sys hV hH
  have hb1g := b1gU_nonneg sys hV hH
  have hcT := cTrU_nonneg sys hV hH
  have hε0 : 0 ≤ epsU sys (FreeBoundary.tv R θ) Hunit := epsU_nonneg
  have hη0 : (0 : ℝ) ≤ 1 + 12 * (eta : ℝ) := by positivity
  have hK2 : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hK1
  have hpoly : 1 + 12 * (eta : ℝ) * K ^ 2 ≤ (1 + 12 * (eta : ℝ)) * K ^ 2 := by
    have e1 : (1 + 12 * (eta : ℝ)) * K ^ 2 = K ^ 2 + 12 * eta * K ^ 2 := by ring
    rw [e1]
    linarith only [hK2]
  have hK4 : 0 < K ^ 4 := by positivity
  have hLe : 1 / 2 * (1 + 12 * (eta : ℝ) * K ^ 2) * e ≤
      1 / 2 * (1 + 12 * (eta : ℝ)) * epsU sys (FreeBoundary.tv R θ) Hunit * X := by
    have h1 : 1 / 2 * (1 + 12 * (eta : ℝ) * K ^ 2) * e ≤
        1 / 2 * ((1 + 12 * (eta : ℝ)) * K ^ 2) *
          (epsU sys (FreeBoundary.tv R θ) Hunit * X / K ^ 4) := by
      gcongr
    refine h1.trans ?_
    have h2 : 1 / 2 * ((1 + 12 * (eta : ℝ)) * K ^ 2) *
        (epsU sys (FreeBoundary.tv R θ) Hunit * X / K ^ 4) =
        1 / 2 * (1 + 12 * (eta : ℝ)) * epsU sys (FreeBoundary.tv R θ) Hunit * X / K ^ 2 := by
      field_simp
    rw [h2]
    exact div_le_self (by positivity) hK2
  have hLe2 : 1 / 2 * (1 + 12 * (eta : ℝ) * K ^ 2) ^ 2 * e ≤
      1 / 2 * (1 + 12 * (eta : ℝ)) ^ 2 * epsU sys (FreeBoundary.tv R θ) Hunit * X := by
    have h1 : 1 / 2 * (1 + 12 * (eta : ℝ) * K ^ 2) ^ 2 * e ≤
        1 / 2 * ((1 + 12 * (eta : ℝ)) * K ^ 2) ^ 2 *
          (epsU sys (FreeBoundary.tv R θ) Hunit * X / K ^ 4) := by
      gcongr
    refine h1.trans (le_of_eq ?_)
    field_simp
  -- first graph bounds
  obtain ⟨hWe0, hWeT⟩ := exact_traj_shells_gL sys H hKernel Hunit hL hθ hPeriodic hH D t m p₀
  have hWg0 := grid_traj_weight_gL sys H hKernel Hunit hL hθ hPeriodic hH D m hκb Ug hgcomm t
  have hWgT := grid_traj_shells_gL sys H hKernel Hunit hL hθ hPeriodic hH D m hm hK8 hκ Ug hgcomm
    t p₀
  have hTe : ‖wMul (regKinSym sys (gF L) p₀) φe‖ ≤
      1 / 2 * b0eU sys (FreeBoundary.tv R θ) Hunit * X := by
    refine (norm_regKin_le_wPhys sys (gF L) p₀ φe).trans ?_
    calc 1 / 2 * ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L)) φe‖
        ≤ 1 / 2 * (b0eU sys (FreeBoundary.tv R θ) Hunit * X) :=
          mul_le_mul_of_nonneg_left hWe0 (by norm_num)
      _ = _ := by ring
  have hTg : ‖wMul (regKinSym sys (gF L) p₀) φg‖ ≤
      1 / 2 * b0gU sys (FreeBoundary.tv R θ) Hunit * X := by
    refine (norm_regKin_le_wPhys sys (gF L) p₀ φg).trans ?_
    calc 1 / 2 * ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L)) φg‖
        ≤ 1 / 2 * (b0gU sys (FreeBoundary.tv R θ) Hunit * X) :=
          mul_le_mul_of_nonneg_left hWg0 (by norm_num)
      _ = _ := by ring
  have hTdx : ‖wMul (regKinSym sys (gF L) p₀) (φe - x)‖ ≤
      1 / 2 * (1 + 12 * (eta : ℝ)) * epsU sys (FreeBoundary.tv R θ) Hunit * X := by
    have h : ‖wMul (regKinSym sys (gF L) p₀) (φe - x)‖ ≤
        1 / 2 * (1 + 12 * (eta : ℝ) * K ^ 2) * ‖φe - x‖ :=
      norm_regKin_le_polyU sys (gF L) p₀ (φe - x)
    refine h.trans (le_trans ?_ hLe)
    exact mul_le_mul_of_nonneg_left hφx (by positivity)
  have hTdy : ‖wMul (regKinSym sys (gF L) p₀) (y - φg)‖ ≤
      1 / 2 * (1 + 12 * (eta : ℝ)) * epsU sys (FreeBoundary.tv R θ) Hunit * X := by
    have h : ‖wMul (regKinSym sys (gF L) p₀) (y - φg)‖ ≤
        1 / 2 * (1 + 12 * (eta : ℝ) * K ^ 2) * ‖y - φg‖ :=
      norm_regKin_le_polyU sys (gF L) p₀ (y - φg)
    refine h.trans (le_trans ?_ hLe)
    exact mul_le_mul_of_nonneg_left hφy (by positivity)
  have hζdef : zetaU sys (FreeBoundary.tv R θ) Hunit =
      1 / 2 * b0eU sys (FreeBoundary.tv R θ) Hunit + 1 / 2 * b0gU sys (FreeBoundary.tv R θ) Hunit +
        1 / 2 * (1 + 12 * (eta : ℝ)) * epsU sys (FreeBoundary.tv R θ) Hunit := rfl
  have hτe0 : 0 ≤ 1 / 2 * b0eU sys (FreeBoundary.tv R θ) Hunit * X := by positivity
  have hτg0 : 0 ≤ 1 / 2 * b0gU sys (FreeBoundary.tv R θ) Hunit * X := by positivity
  have hℓ10 : 0 ≤ 1 / 2 * (1 + 12 * (eta : ℝ)) * epsU sys (FreeBoundary.tv R θ) Hunit * X := by
    positivity
  have hTx : ‖wMul (regKinSym sys (gF L) p₀) x‖ ≤ zetaU sys (FreeBoundary.tv R θ) Hunit * X := by
    have e1 : wMul (regKinSym sys (gF L) p₀) x =
        wMul (regKinSym sys (gF L) p₀) φe - wMul (regKinSym sys (gF L) p₀) (φe - x) := by
      rw [map_sub]
      abel
    rw [e1, hζdef]
    refine (norm_sub_le _ _).trans ?_
    linarith only [hTe, hTdx, hτg0]
  have hTy : ‖wMul (regKinSym sys (gF L) p₀) y‖ ≤ zetaU sys (FreeBoundary.tv R θ) Hunit * X := by
    have e1 : wMul (regKinSym sys (gF L) p₀) y =
        wMul (regKinSym sys (gF L) p₀) φg + wMul (regKinSym sys (gF L) p₀) (y - φg) := by
      rw [map_sub]
      abel
    rw [e1, hζdef]
    refine (norm_add_le _ _).trans ?_
    linarith only [hTg, hTdy, hτe0]
  have hTe' : ‖wMul (regKinSym sys (gF L) p₀) φe‖ ≤ zetaU sys (FreeBoundary.tv R θ) Hunit * X := by
    rw [hζdef]
    linarith only [hTe, hτg0, hℓ10]
  have hTg' : ‖wMul (regKinSym sys (gF L) p₀) φg‖ ≤ zetaU sys (FreeBoundary.tv R θ) Hunit * X := by
    rw [hζdef]
    linarith only [hTg, hτe0, hℓ10]
  -- the second weighted moments (layer cake in the physical weight)
  have hT₀1 : 1 ≤ T₀ := by omega
  have hsK0 : 0 < Real.sqrt K := Real.sqrt_pos.mpr (by linarith)
  have hKsK : 1 ≤ K * Real.sqrt K :=
    one_le_mul_of_one_le_of_one_le hK1 (Real.one_le_sqrt.mpr hK1)
  have hsg0 : 0 < Real.sqrt (gF L) := Real.sqrt_pos.mpr hg
  have hT₀0 : (0 : ℝ) ≤ T₀ := Nat.cast_nonneg T₀
  have hshell : ∀ (C : ℝ) (T : ℕ), C / Real.sqrt (gF L * T) = C / Real.sqrt (gF L) / Real.sqrt T :=
    fun C T => by rw [Real.sqrt_mul hg.le, div_div]
  set Ce := (2 * sys.maxMass + 2) * (cTrU sys (FreeBoundary.tv R θ) Hunit * X) with hCe
  set Cg := b1gU sys (FreeBoundary.tv R θ) Hunit * X with hCg
  have hCe0 : 0 ≤ Ce := by
    have := sys.maxMass_pos
    positivity
  have hCg0 : 0 ≤ Cg := by positivity
  have hSE := norm_w_regKin_shells sys (gF L) m (by omega)
    (FreeBoundary.wPhys (regParticlesOf sys) (gF L)) p₀ φe hT₀1 hT₀m hWe0
    (by positivity : 0 ≤ Ce / Real.sqrt (gF L))
    (fun T hT1 _ => by
      rw [← hshell]
      exact hWeT T (hT₀g.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hT1) hg.le)))
  have hSG := norm_w_regKin_shells sys (gF L) m (by omega)
    (FreeBoundary.wPhys (regParticlesOf sys) (gF L)) p₀ φg hT₀1 hT₀m hWg0
    (by positivity : 0 ≤ Cg / Real.sqrt (gF L))
    (fun T hT1 hT2 => by
      rw [← hshell]
      exact hWgT T (hT₀2.trans hT1) hT2
        (hT₀g.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hT1) hg.le)))
  have hlE : 3 * gF L ^ 2 * ((T₀ : ℝ) ^ 2 * (b0eU sys (FreeBoundary.tv R θ) Hunit * X) +
      4 * ((m : ℝ) * Real.sqrt m) * (Ce / Real.sqrt (gF L))) ≤
      12 * (b0eU sys (FreeBoundary.tv R θ) Hunit * X) + 12 * (K * Real.sqrt K) * Ce :=
    layer_phys_arith hg hT₀g2 hT₀0 (by positivity)
  have hlG : 3 * gF L ^ 2 * ((T₀ : ℝ) ^ 2 * (b0gU sys (FreeBoundary.tv R θ) Hunit * X) +
      4 * ((m : ℝ) * Real.sqrt m) * (Cg / Real.sqrt (gF L))) ≤
      12 * (b0gU sys (FreeBoundary.tv R θ) Hunit * X) + 12 * (K * Real.sqrt K) * Cg :=
    layer_phys_arith hg hT₀g2 hT₀0 (by positivity)
  set σe := 12 * (b0eU sys (FreeBoundary.tv R θ) Hunit +
    (2 * sys.maxMass + 2) * cTrU sys (FreeBoundary.tv R θ) Hunit) with hσe
  set σg := 12 * (b0gU sys (FreeBoundary.tv R θ) Hunit + b1gU sys (FreeBoundary.tv R θ) Hunit)
    with hσg
  set ℓ2 := 1 / 2 * (1 + 12 * (eta : ℝ)) ^ 2 * epsU sys (FreeBoundary.tv R θ) Hunit with hℓ2
  have hσe0 : 0 ≤ σe := by
    have := sys.maxMass_pos
    positivity
  have hσg0 : 0 ≤ σg := by positivity
  have hℓ20 : 0 ≤ ℓ2 := by positivity
  have hbe1 : b0eU sys (FreeBoundary.tv R θ) Hunit * X ≤
      b0eU sys (FreeBoundary.tv R θ) Hunit * X * (K * Real.sqrt K) :=
    le_mul_of_one_le_right (by positivity) hKsK
  have hbg1 : b0gU sys (FreeBoundary.tv R θ) Hunit * X ≤
      b0gU sys (FreeBoundary.tv R θ) Hunit * X * (K * Real.sqrt K) :=
    le_mul_of_one_le_right (by positivity) hKsK
  have hSE' : ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
      (wMul (regKinSym sys (gF L) p₀) φe)‖ ≤ σe * (K * Real.sqrt K) * X := by
    refine hSE.trans (hlE.trans ?_)
    have e1 : σe * (K * Real.sqrt K) * X = 12 * (b0eU sys (FreeBoundary.tv R θ) Hunit * X *
        (K * Real.sqrt K)) + 12 * (K * Real.sqrt K) * Ce := by
      rw [hσe, hCe]
      ring
    rw [e1]
    linarith only [hbe1]
  have hSG' : ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
      (wMul (regKinSym sys (gF L) p₀) φg)‖ ≤ σg * (K * Real.sqrt K) * X := by
    refine hSG.trans (hlG.trans ?_)
    have e1 : σg * (K * Real.sqrt K) * X = 12 * (b0gU sys (FreeBoundary.tv R θ) Hunit * X *
        (K * Real.sqrt K)) + 12 * (K * Real.sqrt K) * Cg := by
      rw [hσg, hCg]
      ring
    rw [e1]
    linarith only [hbg1]
  have hWdx : ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
      (wMul (regKinSym sys (gF L) p₀) (φe - x))‖ ≤ ℓ2 * X := by
    have h : ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
        (wMul (regKinSym sys (gF L) p₀) (φe - x))‖ ≤
        1 / 2 * (1 + 12 * (eta : ℝ) * K ^ 2) ^ 2 * ‖φe - x‖ :=
      norm_wPhys_regKin_le_polyU sys (gF L) p₀ (φe - x)
    refine h.trans (le_trans ?_ hLe2)
    exact mul_le_mul_of_nonneg_left hφx (by positivity)
  have hWdy : ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
      (wMul (regKinSym sys (gF L) p₀) (y - φg))‖ ≤ ℓ2 * X := by
    have h : ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
        (wMul (regKinSym sys (gF L) p₀) (y - φg))‖ ≤
        1 / 2 * (1 + 12 * (eta : ℝ) * K ^ 2) ^ 2 * ‖y - φg‖ :=
      norm_wPhys_regKin_le_polyU sys (gF L) p₀ (y - φg)
    refine h.trans (le_trans ?_ hLe2)
    exact mul_le_mul_of_nonneg_left hφy (by positivity)
  have hωdef : omegaU sys (FreeBoundary.tv R θ) Hunit = σe + σg + ℓ2 := rfl
  have hℓ2K : ℓ2 * X ≤ ℓ2 * (K * Real.sqrt K) * X := by
    have h0 : 0 ≤ ℓ2 * X := by positivity
    calc ℓ2 * X = ℓ2 * X * 1 := by ring
      _ ≤ ℓ2 * X * (K * Real.sqrt K) := mul_le_mul_of_nonneg_left hKsK h0
      _ = _ := by ring
  have hWx : ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
      (wMul (regKinSym sys (gF L) p₀) x)‖ ≤
      omegaU sys (FreeBoundary.tv R θ) Hunit * (K * Real.sqrt K) * X := by
    have e1 : wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
        (wMul (regKinSym sys (gF L) p₀) x) =
        wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L)) (wMul (regKinSym sys (gF L) p₀) φe) -
          wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
            (wMul (regKinSym sys (gF L) p₀) (φe - x)) := by
      rw [map_sub, map_sub]
      abel
    rw [e1, hωdef]
    refine (norm_sub_le _ _).trans ?_
    have h3 : 0 ≤ σg * (K * Real.sqrt K) * X := by positivity
    linarith only [hSE', hWdx, hℓ2K, h3]
  have hWy : ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
      (wMul (regKinSym sys (gF L) p₀) y)‖ ≤
      omegaU sys (FreeBoundary.tv R θ) Hunit * (K * Real.sqrt K) * X := by
    have e1 : wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
        (wMul (regKinSym sys (gF L) p₀) y) =
        wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L)) (wMul (regKinSym sys (gF L) p₀) φg) +
          wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L))
            (wMul (regKinSym sys (gF L) p₀) (y - φg)) := by
      rw [map_sub, map_sub]
      abel
    rw [e1, hωdef]
    refine (norm_add_le _ _).trans ?_
    have h3 : 0 ≤ σe * (K * Real.sqrt K) * X := by positivity
    linarith only [hSG', hWdy, hℓ2K, h3]
  -- the grid graph norm of `T_p x`, `T_p y`
  set c' := c + (cg + 1) with hc'
  have hc'0 : 0 ≤ c' := by linarith
  have hc'def : c' = cPrU sys (FreeBoundary.tv R θ) Hunit := by rw [hc', hcdef]; rfl
  have hζ0 : 0 ≤ zetaU sys (FreeBoundary.tv R θ) Hunit := zetaU_nonneg hV hH
  have hω0 : 0 ≤ omegaU sys (FreeBoundary.tv R θ) Hunit := omegaU_nonneg hV hH
  have hA0 : 0 ≤ PlaneWaveGridG.gLAU sys (FreeBoundary.tv R θ) := by
    unfold PlaneWaveGridG.gLAU
    have := PlaneWaveGridG.gLzU_nonneg sys hV
    positivity
  have hγdef : gammaU sys (FreeBoundary.tv R θ) Hunit =
      5 / 8 * omegaU sys (FreeBoundary.tv R θ) Hunit +
        (PlaneWaveGridG.gLAU sys (FreeBoundary.tv R θ) + c') *
          zetaU sys (FreeBoundary.tv R θ) Hunit := by
    rw [hc'def]
    rfl
  have hGz : ∀ z : EuclideanSpace ℂ (RCfg eta m),
      ‖z‖ ≤ zetaU sys (FreeBoundary.tv R θ) Hunit * X →
      ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L)) z‖ ≤
        omegaU sys (FreeBoundary.tv R θ) Hunit * (K * Real.sqrt K) * X →
      ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) z‖ +
        c' * ‖z‖ ≤ gammaU sys (FreeBoundary.tv R θ) Hunit * (K * Real.sqrt K) * X := by
    intro z hz1 hz2
    have h := (FreeBoundary.gridGraphNorm_gL sys hL hV hκb z).1
    have hz2' : ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (2 * Real.pi / L)) z‖ ≤
        omegaU sys (FreeBoundary.tv R θ) Hunit * (K * Real.sqrt K) * X := hz2
    rw [hγdef]
    have hA1 : 5 / 8 * ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (2 * Real.pi / L)) z‖ ≤
        5 / 8 * (omegaU sys (FreeBoundary.tv R θ) Hunit * (K * Real.sqrt K) * X) :=
      mul_le_mul_of_nonneg_left hz2' (by norm_num)
    have hA2 : (PlaneWaveGridG.gLAU sys (FreeBoundary.tv R θ) + c') * ‖z‖ ≤
        (PlaneWaveGridG.gLAU sys (FreeBoundary.tv R θ) + c') *
          (zetaU sys (FreeBoundary.tv R θ) Hunit * X) :=
      mul_le_mul_of_nonneg_left hz1 (add_nonneg hA0 hc'0)
    have hA3 : (PlaneWaveGridG.gLAU sys (FreeBoundary.tv R θ) + c') *
        (zetaU sys (FreeBoundary.tv R θ) Hunit * X) ≤
        (PlaneWaveGridG.gLAU sys (FreeBoundary.tv R θ) + c') *
          zetaU sys (FreeBoundary.tv R θ) Hunit * (K * Real.sqrt K) * X := by
      have h0 : 0 ≤ (PlaneWaveGridG.gLAU sys (FreeBoundary.tv R θ) + c') *
          zetaU sys (FreeBoundary.tv R θ) Hunit * X :=
        mul_nonneg (mul_nonneg (add_nonneg hA0 hc'0) hζ0) hΞ
      calc _ = (PlaneWaveGridG.gLAU sys (FreeBoundary.tv R θ) + c') *
            zetaU sys (FreeBoundary.tv R θ) Hunit * X * 1 := by ring
        _ ≤ _ * (K * Real.sqrt K) := mul_le_mul_of_nonneg_left hKsK h0
        _ = _ := by ring
    have hz0 := norm_nonneg z
    linarith only [h, hA1, hA2, hA3]
  -- the core comparison paired with `T_p x` and `T_p y`
  have hcore : ∀ z : EuclideanSpace ℂ (RCfg eta m),
      ‖z‖ ≤ zetaU sys (FreeBoundary.tv R θ) Hunit * X →
      ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (gF L)) z‖ ≤
        omegaU sys (FreeBoundary.tv R θ) Hunit * (K * Real.sqrt K) * X →
      ‖⟪x - y, z⟫_ℂ‖ ≤ 48 * dRawU sys L (FreeBoundary.tv R θ) Hunit c' m *
          (t + Real.log (2 + 2 * Λ)) * ((1 + c') ^ 2 * X) *
          (zetaU sys (FreeBoundary.tv R θ) Hunit * X) +
        2 * (fRawU sys L (FreeBoundary.tv R θ) Hunit m / (Λ - (cg + 1))) * ((1 + c') * X) *
          (gammaU sys (FreeBoundary.tv R θ) Hunit * (K * Real.sqrt K) * X / (2 * Λ)) := by
    intro z hz1 hz2
    have hHs2' : ‖ExactEigen.Hs2 (c := c') D‖ ≤ (1 + c') ^ 2 * X := by
      have := ExactEigen.norm_Hs2_le (c := c') D
      rwa [abs_of_nonneg hc'0] at this
    have hHs1' : ‖Hs1 c' D‖ ≤ (1 + c') * X := norm_Hs1_le hc'0 D
    have h := grid_core_pair_gL sys H hKernel Hunit hL hθ hPeriodic hH E hcdef hd0 m hm hκ Ug hg0
      hgderiv hc1 hΛ1 hdΛ hKs1 hK21 hΛs hΛ2 hΛg D ht z
    refine h.trans ?_
    have hδ0 : 0 ≤ dRawU sys L (FreeBoundary.tv R θ) Hunit c' m := dRawU_nonneg hL0 hV hH hc'0 m
    have hF0 : 0 ≤ fRawU sys L (FreeBoundary.tv R θ) Hunit m / (Λ - (cg + 1)) :=
      div_nonneg (fRawU_nonneg hL0 hV hH m) (by linarith)
    have hlg : 0 ≤ t + Real.log (2 + 2 * Λ) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 2 * Λ by linarith)
      linarith
    have hGz' := hGz z hz1 hz2
    have hΛ2pos : 0 < 2 * Λ := by linarith
    gcongr
  have hCx := hcore _ hTx hWx
  have hCy := hcore _ hTy hWy
  -- assemble
  have hB' : |regExpect sys (gF L) p₀ φe - regExpect sys (gF L) p₀ x| ≤
      e * (2 * (zetaU sys (FreeBoundary.tv R θ) Hunit * X)) := by
    refine hB.trans ?_
    calc ‖φe - x‖ * (‖wMul (regKinSym sys (gF L) p₀) φe‖ + ‖wMul (regKinSym sys (gF L) p₀) x‖)
        ≤ e * (zetaU sys (FreeBoundary.tv R θ) Hunit * X +
            zetaU sys (FreeBoundary.tv R θ) Hunit * X) :=
          mul_le_mul hφx (add_le_add hTe' hTx) (by positivity) he0
      _ = _ := by ring
  have hD' : |regExpect sys (gF L) p₀ y - regExpect sys (gF L) p₀ φg| ≤
      e * (2 * (zetaU sys (FreeBoundary.tv R θ) Hunit * X)) := by
    refine hD.trans ?_
    calc ‖y - φg‖ * (‖wMul (regKinSym sys (gF L) p₀) y‖ + ‖wMul (regKinSym sys (gF L) p₀) φg‖)
        ≤ e * (zetaU sys (FreeBoundary.tv R θ) Hunit * X +
            zetaU sys (FreeBoundary.tv R θ) Hunit * X) :=
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
  have hδ : dRawU sys L (FreeBoundary.tv R θ) Hunit c' m ≤
      dU sys (FreeBoundary.tv R θ) Hunit c' / K ^ 3 := dRawU_le sys hL hV hH hc'0 hm hK1
  have hF : fRawU sys L (FreeBoundary.tv R θ) Hunit m ≤
      fU sys (FreeBoundary.tv R θ) Hunit / Real.sqrt K := fRawU_le sys hL hV hH hm hK1
  have hfin := grid_assemble (sK := Real.sqrt K) (mb := sys.maxMass) hK1 hsK0 hΞ hQ1 hlg0 hlgQ
    hmb1 (by rw [hΛdef]; field_simp) (show cg + 1 ≤ Λ / 2 by linarith) he hc'0 hδ hF hζ0
    (gammaU_nonneg hV hH) (by positivity) hε0 (dU_nonneg sys hV hH hc'0) (fU_nonneg sys hV hH)
    hA hB' hD' hCx hCy
  refine htri.trans (hfin.trans (le_of_eq ?_))
  unfold cellC
  rw [← hc'def]

end Explicit

/-! ## The `L`-uniform cell estimate -/

/-- The layer-cake threshold `T₀ = max(2, ⌈1/g⌉)` (`1 ≤ g T₀ ≤ 2` for `L ≥ 2π`). -/
noncomputable def T0U (L : ℝ) : ℕ := max 2 ⌈1 / gF L⌉₊

lemma gF_le_one {L : ℝ} (hL : 2 * Real.pi ≤ L) : gF L ≤ 1 := by
  have hL0 := pos_of_two_pi_le hL
  unfold gF
  rw [div_le_one hL0]
  exact hL

lemma T0U_scales {L : ℝ} (hL : 2 * Real.pi ≤ L) {m : ℕ} (hm : 2 ≤ m) (hK : 1 ≤ gF L * m) :
    2 ≤ T0U L ∧ 1 ≤ gF L * T0U L ∧ gF L * T0U L ≤ 2 ∧ T0U L ≤ m := by
  have hL0 := pos_of_two_pi_le hL
  have hg := gF_pos hL0
  have hg1 := gF_le_one hL
  have h3 : gF L * (1 / gF L) = 1 := by field_simp
  refine ⟨le_max_left _ _, ?_, ?_, ?_⟩
  · have h1 : 1 / gF L ≤ (⌈1 / gF L⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈1 / gF L⌉₊ : ℝ) ≤ (T0U L : ℝ) := by
      exact_mod_cast le_max_right 2 ⌈1 / gF L⌉₊
    calc (1 : ℝ) = gF L * (1 / gF L) := h3.symm
      _ ≤ gF L * T0U L := mul_le_mul_of_nonneg_left (h1.trans h2) hg.le
  · unfold T0U
    rcases le_total 2 ⌈1 / gF L⌉₊ with h | h
    · rw [max_eq_right h]
      have h1 : (⌈1 / gF L⌉₊ : ℝ) < 1 / gF L + 1 := Nat.ceil_lt_add_one (by positivity)
      have h4 : gF L * (⌈1 / gF L⌉₊ : ℝ) ≤ gF L * (1 / gF L + 1) :=
        mul_le_mul_of_nonneg_left h1.le hg.le
      rw [mul_add, h3, mul_one] at h4
      linarith
    · rw [max_eq_left h]
      push_cast
      linarith
  · unfold T0U
    refine max_le hm (Nat.ceil_le.mpr ?_)
    rw [div_le_iff₀ hg, mul_comm]
    exact hK

/-- The register threshold of the cell estimate, `K₀^U = max(8, √(2048 m̄ (1 + c_U + c_g^U)))`. -/
noncomputable def cellK0 (sys : CoulombSystem eta ν) (V Hunit : ℝ) : ℝ :=
  max 8 (Real.sqrt (2048 * sys.maxMass * (1 + cU sys V Hunit + cGrU sys V)))

lemma cellK0_scales {sys : CoulombSystem eta ν} {V Hunit K : ℝ} (hV : 0 ≤ V)
    (hK : cellK0 sys V Hunit ≤ K) :
    8 ≤ K ∧ 2048 * sys.maxMass * (1 + cU sys V Hunit + cGrU sys V) ≤ K ^ 2 := by
  have h8 : 8 ≤ K := (le_max_left _ _).trans hK
  refine ⟨h8, ?_⟩
  have hs := (le_max_right _ _).trans hK
  have h0 : 0 ≤ 2048 * sys.maxMass * (1 + cU sys V Hunit + cGrU sys V) := by
    have := two_le_cU sys V Hunit
    have := cGrU_nonneg sys hV
    have := sys.maxMass_pos
    positivity
  calc 2048 * sys.maxMass * (1 + cU sys V Hunit + cGrU sys V) =
        Real.sqrt (2048 * sys.maxMass * (1 + cU sys V Hunit + cGrU sys V)) ^ 2 :=
          (Real.sq_sqrt h0).symm
    _ ≤ K ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2

/-- **The cell-to-grid kinetic estimate, uniform in the cell** (the grid step of
`prop:free-kinetic-log`): the constants `C`, `K₀` depend only on the system, the range cut and
`Hunit`; for every `L ≥ 2π`, every completed range-cut Hamiltonian `H_L`, every `m ≥ 8` with
`K = 2πm/L ≥ K₀`, every kernel of the open-grid class, every grid propagator `U_g`, every exact
propagator of `H_L` and every `t ≥ 0`,
`|⟨u(t), T_p u(t)⟩ - ⟨ψ_g(t), T_p ψ_g(t)⟩| ≤ C Ξ² [1 + t + log(2 + K)]/K³`,
`ψ_g(t) = U_g(t) P' u₀` not renormalised. -/
theorem thm_cell_kinetic_log_gL (sys : CoulombSystem eta ν) {R : ℝ} {θ : ℝ → ℝ}
    (hθ : FreeBoundary.Profile R θ) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hH : 0 ≤ Hunit) (p₀ : Fin eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ L : ℝ, 2 * Real.pi ≤ L →
      ∀ (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2),
      (∀ N u q, H (molecularH2Truncate N u) q =
        fourierCubeKernelAction (2 * Real.pi / L) (FreeBoundary.gLlatHam sys L θ) N u q) →
      ∀ m : ℕ, 8 ≤ m → K₀ ≤ gF L * m →
      ∀ {κ : Lat3 → ℝ}, PlaneWaveGridG.IsGridKernel (PlaneWaveGridG.gLgamma L (FreeBoundary.tv R θ))
        (PlaneWaveGridG.gLref L θ (FreeBoundary.tv R θ)) m κ →
      ∀ (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m)),
      (∀ x, Ug 0 x = x) →
      (∀ t x, Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
        κ (2 * Real.pi / L) (Ug t x)) →
      (∀ t x, HasDerivAt (fun s => Ug s x)
        (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
          (2 * Real.pi / L) x))) t) →
      ∀ (D : EvoData L H) (t : ℝ), 0 ≤ t →
        |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
            regExpect sys (gF L) p₀ (Ug t (regCoeff m (Sm eta L D.u₀)))| ≤
          C * D.Xi ^ 2 * (1 + t + Real.log (2 + gF L * m)) / (gF L * m) ^ 3 := by
  have hV : 0 ≤ FreeBoundary.tv R θ := hθ.tv_nonneg
  refine ⟨cellC sys (FreeBoundary.tv R θ) Hunit, cellC_nonneg hV hH,
    cellK0 sys (FreeBoundary.tv R θ) Hunit, by unfold cellK0; positivity, ?_⟩
  intro L hL H hKernel m hm hK₀ κ hκ Ug hg0 hgcomm hgderiv D t ht
  obtain ⟨hK8, hKbig⟩ := cellK0_scales hV hK₀
  obtain ⟨E⟩ := exists_exactEigen_gL sys H hKernel Hunit (pos_of_two_pi_le hL) hθ hPeriodic
  have E' : ExactEigen L H (cU sys (FreeBoundary.tv R θ) Hunit) :=
    shift_gL_eq_U sys (FreeBoundary.tv R θ) Hunit hL hH ▸ E
  obtain ⟨hT2, hTg, hTg2, hTm⟩ := T0U_scales hL (by omega : 2 ≤ m) (by linarith)
  exact cell_kinetic_explicit sys H hKernel Hunit hL hθ hPeriodic hH p₀ E' rfl m hm hK8 hKbig
    hT2 hTg hTg2 hTm hκ Ug hg0 hgcomm hgderiv D ht

end KineticLog
