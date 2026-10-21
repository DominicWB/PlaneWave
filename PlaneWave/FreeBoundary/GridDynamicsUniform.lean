import PlaneWave.FreeBoundary.GridDynamicsTheorem

/-!
# `L`-uniform constants of the grid dynamics: stages 1–3

The constants `(A₁, A₂, A₃) = gridConstsSharp_gL` of `thm:grid-dyn-sharp` for the `g_L` system
(`PlaneWave.FreeBoundary.GridDynamicsSharp`) grow polynomially in `L`: the grid core of the release
works in lattice units (weight `wM = 1 + Σ_b |n_b|²/m_b`, kinetic scale `g²/2`, lattice Sobolev
constant), and its relative-bound radius `J₀ ~ (Z/g²)² ~ L²` and trajectory constant
`(4/3)(1 + 104 Z J₀/g²) ~ L³` reflect the ratio `Z/g² ~ L` of the lattice coupling to the lattice
kinetic scale. This file removes the first three sources of `L`-dependence (for `L ≥ 2π`):

* **Stage 1** (the tail and relative-bound constants in physical units). With the physical tail
  constant `c_tail^P` of `PlaneWave.FreeBoundary.UniformCubic` (`gLtailM`,
  `PlaneWave.FreeBoundary.GridDynamicsInterface`), the tail constant is at most the `L`-free
  `gLtailMU` (`gLtailM_le_U`), the mass constant and the relative-bound constant `b = C √(4C² + 2)`
  do not depend on `L` (`gLmassConst_eq_U`, `relB_gL_eq_U`), and so `A₁ ≤ gridA1U`, `A₃ ≤ gridA3U`
  with `L`-free right-hand sides (`gridConstsSharp_gL_one_le_U`, `gridConstsSharp_gL_three_le_U`).
* **Stage 2** (the relative bound with a physical splitting radius). In physical units (weight
  `w_g = 1 + g² Σ_b |n_b|²/m_b`, `wPhys`; kinetic scale `1/2`), the relative bound of the grid
  potential (`gridRegHamP`, `PlaneWave.FreeBoundary.UniformGridCore`) has the splitting radius
  `J₀ = J0P`, for which `g J₀` (the splitting momentum) is bounded independently of `L`, the small
  constant `B ≤ 1/8` and the low-transfer constant `26 Z J₀ ≤ A = gLAU = 43264·79 z³ + 52 z`
  (`gLGridA_le_U`), `z = m̄ Z_c/g` the `L`-free physical coupling.
* **Stage 3** (first-order graph-norm equivalence, uniform in `L`). The generic register
  Hamiltonian with kinetic scale `c` (`RegHamP`) satisfies `‖H u‖ ≤ (5c/4)‖W u‖ + A‖u‖`,
  `‖W u‖ ≤ (4/3)(‖u‖ + (‖H u‖ + A‖u‖)/c)` and the trajectory bound
  `‖W (U u)‖ ≤ (5/3)‖W u‖ + (4/3)(1 + 2A/c)‖u‖` (`RegHamP.op_le`, `RegHamP.elliptic_gen`,
  `RegHamP.flow_le_weight`). For the `g_L` grid Hamiltonian (`gridRegHamU`):
  `‖H_grid v‖ ≤ (5/8)‖w_g v‖ + A‖v‖`, `‖w_g v‖ ≤ (8/3)‖H_grid v‖ + (4/3)(1 + 2A)‖v‖`
  (`gridGraphNorm_gL`) and `‖w_g (U v)‖ ≤ (5/3)‖w_g v‖ + (4/3)(1 + 4A)‖v‖`
  (`norm_wPhys_gridFlow_le_gL`): the trajectory constant is `L`-free. The collocated
  observable in the physical weight:
  `‖w_g (O_g u)‖ ≤ (2 + 12 m̄) C_χ ‖w_g u‖ + ((3 + 12 m̄) C_χ + 14 g² D'_χ)‖u‖`
  (`norm_wPhys_gridObs_le`), `g² D'_χ = Σ_ν |gν|² |χ̂(ν)|` the physical second moment, and the
  backward flow of `O_g v` (`norm_wPhys_gridFlow_gridObs_le_gL`).

Stage 4 (the second-moment and observable estimates in the physical weight, which make `A₂` uniform)
is in
`PlaneWave.FreeBoundary.GridSecondOrderPhysical`–`PlaneWave.FreeBoundary.GridDynamicsUniformTheorem`
(`thm_grid_dyn_sharp_gLU`); `thm_grid_dyn_sharp_gL` (`PlaneWave.FreeBoundary.GridDynamicsTheorem`)
is kept, with its polynomial-`L` constants.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate
open Finset

/-! ## The register Hamiltonian with a general kinetic scale -/

namespace PlaneWaveGridG.RegHamP

variable {ι : Type*} [Fintype ι] (H : RegHamP ι)

/-- The kinetic part is at most `c` times the weight. -/
lemma norm_kin_le (u : EuclideanSpace ℂ ι) : ‖wMul H.kin u‖ ≤ H.c * ‖wMul H.W u‖ := by
  have hc := H.c_pos.le
  have h := norm_wMul_mono (w := H.kin) (w' := fun q => H.c * H.W q) H.kin_nonneg
    (fun q => by
      rw [H.kin_eq]
      have := H.W_ge_one q
      nlinarith) u
  have e : wMul (fun q => H.c * H.W q) u = ((H.c : ℝ) : ℂ) • wMul H.W u := by
    ext q
    simp only [wMul_apply, PiLp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg hc] at h
  exact h

/-- **Forward graph-norm bound**: `‖H u‖ ≤ (5c/4) ‖W u‖ + A ‖u‖`. -/
lemma op_le (u : EuclideanSpace ℂ ι) :
    ‖H.op u‖ ≤ 5 * H.c / 4 * ‖wMul H.W u‖ + H.A * ‖u‖ := by
  have h1 := H.norm_kin_le u
  have hV := H.op_bound u
  have h2 : H.B * ‖wMul H.W u‖ ≤ H.c / 4 * ‖wMul H.W u‖ :=
    mul_le_mul_of_nonneg_right H.small (norm_nonneg _)
  have h3 : ‖H.op u‖ ≤ ‖wMul H.kin u‖ + ‖H.V u‖ := by
    simp only [RegHamP.op, LinearMap.add_apply]
    exact norm_add_le _ _
  linarith

/-- **Elliptic estimate for every state**: `‖W u‖ ≤ (4/3)(‖u‖ + (‖H u‖ + A ‖u‖)/c)`. -/
lemma elliptic_gen (u : EuclideanSpace ℂ ι) :
    ‖wMul H.W u‖ ≤ 4 / 3 * (‖u‖ + (‖H.op u‖ + H.A * ‖u‖) / H.c) := by
  have hc := H.c_pos
  have hkin : wMul H.kin u = H.op u - H.V u := by
    simp only [RegHamP.op, LinearMap.add_apply]
    abel
  have h1 : ‖wMul H.kin u‖ ≤ ‖H.op u‖ + ‖H.V u‖ := by
    rw [hkin]
    exact norm_sub_le _ _
  have hV := H.op_bound u
  have h2 : ‖wMul H.W u‖ ≤ ‖u‖ + 1 / H.c * ‖wMul H.kin u‖ := by
    rw [H.wMul_W_eq u]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hBX : H.B * ‖wMul H.W u‖ ≤ H.c / 4 * ‖wMul H.W u‖ :=
    mul_le_mul_of_nonneg_right H.small (norm_nonneg _)
  have h3 : ‖wMul H.kin u‖ ≤ (‖H.op u‖ + H.A * ‖u‖) + H.c / 4 * ‖wMul H.W u‖ := by linarith
  have h4 : 1 / H.c * ‖wMul H.kin u‖ ≤
      1 / H.c * ((‖H.op u‖ + H.A * ‖u‖) + H.c / 4 * ‖wMul H.W u‖) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have e : 1 / H.c * ((‖H.op u‖ + H.A * ‖u‖) + H.c / 4 * ‖wMul H.W u‖) =
      (‖H.op u‖ + H.A * ‖u‖) / H.c + ‖wMul H.W u‖ / 4 := by
    field_simp
  linarith

/-- **Regularity of a trajectory**: for a unitary `U` commuting with `H`, the weight of `U u` is
bounded by the graph norm of `u`, uniformly in `U`. -/
lemma flow_le (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (hcomm : ∀ x, U (H.op x) = H.op (U x)) (u : EuclideanSpace ℂ ι) :
    ‖wMul H.W (U u)‖ ≤ 4 / 3 * (‖u‖ + (‖H.op u‖ + H.A * ‖u‖) / H.c) := by
  have h := H.elliptic_gen (U u)
  rw [← hcomm, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
  exact h

/-- The same, in terms of the weight of `u`: `‖W (U u)‖ ≤ (5/3)‖W u‖ + (4/3)(1 + 2A/c)‖u‖`. -/
lemma flow_le_weight (U : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    (hcomm : ∀ x, U (H.op x) = H.op (U x)) (u : EuclideanSpace ℂ ι) :
    ‖wMul H.W (U u)‖ ≤ 5 / 3 * ‖wMul H.W u‖ + 4 / 3 * (1 + 2 * H.A / H.c) * ‖u‖ := by
  have hc := H.c_pos
  have h := H.flow_le U hcomm u
  have hop := H.op_le u
  have h2 : (‖H.op u‖ + H.A * ‖u‖) / H.c ≤
      (5 * H.c / 4 * ‖wMul H.W u‖ + 2 * H.A * ‖u‖) / H.c :=
    div_le_div_of_nonneg_right (by linarith) hc.le
  have e : (5 * H.c / 4 * ‖wMul H.W u‖ + 2 * H.A * ‖u‖) / H.c =
      5 / 4 * ‖wMul H.W u‖ + 2 * H.A / H.c * ‖u‖ := by
    field_simp
  rw [e] at h2
  calc ‖wMul H.W (U u)‖ ≤ 4 / 3 * (‖u‖ + (‖H.op u‖ + H.A * ‖u‖) / H.c) := h
    _ ≤ 4 / 3 * (‖u‖ + (5 / 4 * ‖wMul H.W u‖ + 2 * H.A / H.c * ‖u‖)) := by linarith
    _ = 5 / 3 * ‖wMul H.W u‖ + 4 / 3 * (1 + 2 * H.A / H.c) * ‖u‖ := by ring

end PlaneWaveGridG.RegHamP

namespace FreeBoundary

open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics

open PlaneWaveGridG (gLgamma gLgamma_pos regParticlesOfG posNucleiOfG gLzU gLzU_nonneg gLAU tBU
  ctailU gLmassConstU gLGridCoupling J0P)

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Stage 1: the tail and relative-bound constants -/

/-- The `L`-free tail constant `Q (1 + V) c_tail^U M` (`c_tail^U = ctailU`). -/
noncomputable def gLtailMU (sys : CoulombSystem eta ν) (V Hunit M : ℝ) : ℝ :=
  sys.couplingWeight * ((1 + V) * ctailU Hunit) * M

/-- The tail constant is bounded uniformly in `L ≥ 2π`. -/
lemma gLtailM_le_U (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) {V : ℝ}
    (hV : 0 ≤ V) {Hunit : ℝ} (hH : 0 ≤ Hunit) {M : ℝ} (hM : 0 ≤ M) :
    gLtailM sys L V Hunit M ≤ gLtailMU sys V Hunit M := by
  have h := PlaneWaveGridG.ctailP_gL_le hL hH
  have hW := sys.couplingWeight_nonneg
  have hV1 : 0 ≤ 1 + V := by linarith
  unfold gLtailM gLtailMU
  have h2 : (1 + V) * FSNormal.ctailP (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L) ≤
      (1 + V) * ctailU Hunit := mul_le_mul_of_nonneg_left h hV1
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hW) hM

/-- The mass constant does not depend on `L ≥ 2π`. -/
lemma gLmassConst_eq_U (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) (V : ℝ)
    {Hunit : ℝ} (hH : 0 ≤ Hunit) : gLmassConst sys L V Hunit = gLmassConstU sys V Hunit := by
  unfold gLmassConst gLmassConstU
  rw [PlaneWaveGridG.tB_gL_eq hL hH]

lemma gLmassConstU_nonneg (sys : CoulombSystem eta ν) {V : ℝ} (hV : 0 ≤ V) {Hunit : ℝ}
    (hH : 0 ≤ Hunit) : 0 ≤ gLmassConstU sys V Hunit := by
  unfold gLmassConstU
  have := sys.massCouplingWeight_nonneg
  have := PlaneWaveGridG.tBU_nonneg hH
  have : 0 ≤ 1 + V := by linarith
  positivity

/-- The relative-bound constant `b = C √(4C² + 2)`, `C = gLmassConstU`, `L`-free. -/
noncomputable def relBU (sys : CoulombSystem eta ν) (V Hunit : ℝ) : ℝ :=
  gLmassConstU sys V Hunit * Real.sqrt (4 * gLmassConstU sys V Hunit ^ 2 + 2)

lemma relB_gL_eq_U (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) (V : ℝ)
    {Hunit : ℝ} (hH : 0 ≤ Hunit) : relB_gL sys L V Hunit = relBU sys V Hunit := by
  unfold relB_gL relBU
  rw [gLmassConst_eq_U sys hL V hH]

lemma relBU_nonneg (sys : CoulombSystem eta ν) {V : ℝ} (hV : 0 ≤ V) {Hunit : ℝ}
    (hH : 0 ≤ Hunit) : 0 ≤ relBU sys V Hunit :=
  mul_nonneg (gLmassConstU_nonneg sys hV hH) (Real.sqrt_nonneg _)

/-- The rate `τ₁ = 2 m̄ (2 m̄ Ξ₁ + C_t(M₀))` of `gridConstsSharp_gL` with the `L`-free
constants. -/
noncomputable def tauOneU (sys : CoulombSystem eta ν) (V Hunit s0 hu hs hv : ℝ) : ℝ :=
  2 * sys.maxMass * (2 * sys.maxMass * (2 * hv + 2 * relBU sys V Hunit * hs) +
    gLtailMU sys V Hunit (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0))))

/-- The constant `A₁` of `thm:grid-dyn-sharp`, `L`-free. -/
noncomputable def gridA1U (sys : CoulombSystem eta ν) (V Hunit : ℝ) (a : Fin eta)
    (χ : Lattice3 → ℂ) (s0 hu hs hv : ℝ) : ℝ :=
  let τ₁ : ℝ := tauOneU sys V Hunit s0 hu hs hv
  let δ₁ : ℝ := eta * τ₁
  let CO : ℝ := ‖convOp (eta := eta) a χ‖
  let Cχ : ℝ := ∑' ν, ‖χ ν‖
  2 * δ₁ * (Cχ * τ₁ + CO * δ₁) + CO * δ₁ ^ 2 + Cχ * τ₁ ^ 2

/-- The constant `A₃` of `thm:grid-dyn-sharp`, `L`-free. -/
noncomputable def gridA3U (sys : CoulombSystem eta ν) (V Hunit s0 hu hs hv : ℝ) : ℝ :=
  2 * (eta * tauOneU sys V Hunit s0 hu hs hv) * s0

lemma tauOne_le_U (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) {V : ℝ}
    (hV : 0 ≤ V) {Hunit : ℝ} (hH : 0 ≤ Hunit) {s0 hu : ℝ} (hs hv : ℝ) (h0 : 0 ≤ s0)
    (h1 : 0 ≤ hu) :
    2 * sys.maxMass * (2 * sys.maxMass * (2 * hv + 2 * relB_gL sys L V Hunit * hs) +
      gLtailM sys L V Hunit (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB_gL sys L V Hunit * s0)))) ≤
    tauOneU sys V Hunit s0 hu hs hv := by
  rw [relB_gL_eq_U sys hL V hH]
  unfold tauOneU
  have hb := relBU_nonneg sys hV hH
  have hM := sys.maxMass_pos
  have hM0 : 0 ≤ sys.maxMass * (s0 + 2 * (2 * hu + 2 * relBU sys V Hunit * s0)) := by positivity
  have h := gLtailM_le_U sys hL hV hH hM0
  exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) h) (by positivity)

lemma A1_mono {e CO Cχ τ τ' : ℝ} (he : 0 ≤ e) (hCO : 0 ≤ CO) (hCχ : 0 ≤ Cχ) (hτ : 0 ≤ τ)
    (hττ : τ ≤ τ') :
    2 * (e * τ) * (Cχ * τ + CO * (e * τ)) + CO * (e * τ) ^ 2 + Cχ * τ ^ 2 ≤
      2 * (e * τ') * (Cχ * τ' + CO * (e * τ')) + CO * (e * τ') ^ 2 + Cχ * τ' ^ 2 := by
  have hτ' : 0 ≤ τ' := hτ.trans hττ
  gcongr

lemma tauOne_nonneg (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) {V : ℝ}
    (hV : 0 ≤ V) {Hunit : ℝ} (hH : 0 ≤ Hunit) {s0 hu hs hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu)
    (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    0 ≤ 2 * sys.maxMass * (2 * sys.maxMass * (2 * hv + 2 * relB_gL sys L V Hunit * hs) +
      gLtailM sys L V Hunit
        (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB_gL sys L V Hunit * s0)))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hb : 0 ≤ relB_gL sys L V Hunit := by
    rw [relB_gL_eq_U sys hL V hH]
    exact relBU_nonneg sys hV hH
  have hM := sys.maxMass_pos
  have ht := gLtailM_nonneg sys hL0 hV Hunit
    (M := sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB_gL sys L V Hunit * s0))) (by positivity)
  positivity

/-- **Stage 1: `A₁` is bounded uniformly in `L ≥ 2π`.** -/
theorem gridConstsSharp_gL_one_le_U (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L)
    {V : ℝ} (hV : 0 ≤ V) {Hunit : ℝ} (hH : 0 ≤ Hunit) (a : Fin eta) (χ : Lattice3 → ℂ)
    {s0 hu hs hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    (gridConstsSharp_gL sys L V Hunit a χ s0 hu hs hv).1 ≤ gridA1U sys V Hunit a χ s0 hu hs hv := by
  have hτ := tauOne_le_U sys hL hV hH hs hv h0 h1
  have hτ0 := tauOne_nonneg sys hL hV hH h0 h1 h2 h3
  have hC : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  exact A1_mono (Nat.cast_nonneg eta) (norm_nonneg _) hC hτ0 hτ

/-- **Stage 1: `A₃` is bounded uniformly in `L ≥ 2π`.** -/
theorem gridConstsSharp_gL_three_le_U (sys : CoulombSystem eta ν) {L : ℝ}
    (hL : 2 * Real.pi ≤ L) {V : ℝ} (hV : 0 ≤ V) {Hunit : ℝ} (hH : 0 ≤ Hunit) (a : Fin eta)
    (χ : Lattice3 → ℂ) {s0 hu hs hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) :
    (gridConstsSharp_gL sys L V Hunit a χ s0 hu hs hv).2.2 ≤ gridA3U sys V Hunit s0 hu hs hv := by
  have hτ := tauOne_le_U sys hL hV hH hs hv h0 h1
  have he : (0 : ℝ) ≤ eta := Nat.cast_nonneg eta
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτ he) (by norm_num)) h0

/-! ## Stage 2: the relative bound with a physical splitting radius -/

/-- **Stage 2.** The low-transfer constant `26 Z J₀` of the relative bound of the `g_L` grid
potential in physical units, `Z = m̄ Z_c` and `J₀ = J0P Z g` (whose splitting momentum `g J₀` is
bounded independently of `L`), is at most the `L`-free `A = gLAU` for `L ≥ 2π`. -/
lemma gLGridA_le_U (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) {V : ℝ}
    (hV : 0 ≤ V) :
    26 * gLGridCoupling sys L V * (J0P (gLGridCoupling sys L V) (2 * Real.pi / L) : ℝ) ≤
      gLAU sys V := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hg1 := PlaneWaveGridG.g_le_one hL
  have hz0 := gLzU_nonneg sys hV
  have hZ0 : 0 ≤ gLGridCoupling sys L V :=
    mul_nonneg sys.maxMass_pos.le (PlaneWaveGridG.Zc_nonneg (gLgamma_pos hL0 hV).le)
  have hz : gLGridCoupling sys L V ≤ gLzU sys V * (2 * Real.pi / L) :=
    (PlaneWaveGridG.gLGridCoupling_eq sys hL0 V).le
  have hσ : (2 * Real.pi / L) ^ 3 + 78 ≤ 79 := by
    have := pow_le_one₀ hg.le hg1 (n := 3)
    linarith
  have h := PlaneWaveGridG.J0P_A_le hZ0 hg hz hσ
  have h2 : 52 * gLzU sys V * (2 * Real.pi / L) ≤ 52 * gLzU sys V := by
    have := mul_le_mul_of_nonneg_left hg1 (by positivity : (0 : ℝ) ≤ 52 * gLzU sys V)
    linarith
  unfold gLAU
  linarith

/-! ## Stage 3: first-order graph-norm equivalence, uniform in `L` -/

/-- The physical weight `w_g(q) = 1 + g² Σ_b |n_b|²/m_b` of the register (the weight `wMP` of the
grid core). -/
noncomputable def wPhys {m : ℕ} (P : RegParticles eta) (g : ℝ) (q : RCfg eta m) : ℝ :=
  1 + g ^ 2 * ∑ b, nsq (gl (q b)) / P.mass b

lemma wPhys_eq_wM {m : ℕ} (P : RegParticles eta) (g : ℝ) (q : RCfg eta m) :
    wPhys P g q = 1 + g ^ 2 * (wM P q - 1) := by
  unfold wPhys wM
  ring

lemma wPhys_ge_one {m : ℕ} (P : RegParticles eta) (g : ℝ) (q : RCfg eta m) : 1 ≤ wPhys P g q := by
  rw [wPhys_eq_wM]
  have := wM_ge_one P q
  have := sq_nonneg g
  nlinarith

lemma wPhys_le_wM {m : ℕ} (P : RegParticles eta) {g : ℝ} (hg : g ^ 2 ≤ 1) (q : RCfg eta m) :
    wPhys P g q ≤ wM P q := by
  rw [wPhys_eq_wM]
  have := wM_ge_one P q
  nlinarith

/-- `w_g = (1 - g²) + g² wM`. -/
lemma wMul_wPhys_eq {m : ℕ} (P : RegParticles eta) (g : ℝ) (u : EuclideanSpace ℂ (RCfg eta m)) :
    wMul (wPhys P g) u = ((1 - g ^ 2 : ℝ) : ℂ) • u + ((g ^ 2 : ℝ) : ℂ) • wMul (wM P) u := by
  ext q
  simp only [wMul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, wPhys_eq_wM]
  push_cast
  ring

lemma norm_wPhys_le {m : ℕ} (P : RegParticles eta) {g : ℝ} (hg : g ^ 2 ≤ 1)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wPhys P g) u‖ ≤ (1 - g ^ 2) * ‖u‖ + g ^ 2 * ‖wMul (wM P) u‖ := by
  rw [wMul_wPhys_eq]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (sq_nonneg g)]

/-- `g² ‖wM u‖ ≤ ‖w_g u‖ + (1 - g²)‖u‖`: the lattice weight costs `g⁻²`. -/
lemma sq_mul_norm_wM_le {m : ℕ} (P : RegParticles eta) {g : ℝ} (hg : g ^ 2 ≤ 1)
    (u : EuclideanSpace ℂ (RCfg eta m)) :
    g ^ 2 * ‖wMul (wM P) u‖ ≤ ‖wMul (wPhys P g) u‖ + (1 - g ^ 2) * ‖u‖ := by
  have e : ((g ^ 2 : ℝ) : ℂ) • wMul (wM P) u =
      wMul (wPhys P g) u - ((1 - g ^ 2 : ℝ) : ℂ) • u := by
    rw [wMul_wPhys_eq]
    abel
  have h := norm_sub_le (wMul (wPhys P g) u) (((1 - g ^ 2 : ℝ) : ℂ) • u)
  rw [← e, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg g), Real.norm_of_nonneg (by linarith)] at h
  exact h

/-- **Stage 3.** The `g_L` grid Hamiltonian as a register Hamiltonian with the physical weight
`w_g`, kinetic scale `c = 1/2` and the `L`-free constant `A = gLAU` (`L ≥ 2π`). -/
noncomputable def gridRegHamU (sys : CoulombSystem eta ν) {L V : ℝ} (hL : 2 * Real.pi ≤ L)
    (hV : 0 ≤ V) {m : ℕ} {κ : Lat3 → ℝ} (hκb : ∀ x, |κ x| ≤ gLgamma L V * coul x) :
    PlaneWaveGridG.RegHamP (RCfg eta m) :=
  PlaneWaveGridG.gridRegHamP (eta := eta) (m := m) (P := regParticlesOfG sys)
    (D := (posNucleiOfG sys.nuclei).toNucData)
    (gLgamma_pos (lt_of_lt_of_le (by positivity) hL) hV).le hκb
    (div_pos (by positivity) (lt_of_lt_of_le (by positivity) hL)) (gLAU sys V)
    (gLGridA_le_U sys hL hV)

section GridHam

variable (sys : CoulombSystem eta ν) {L V : ℝ} (hL : 2 * Real.pi ≤ L) (hV : 0 ≤ V) {m : ℕ}
  {κ : Lat3 → ℝ} (hκb : ∀ x, |κ x| ≤ gLgamma L V * coul x)

lemma gridRegHamU_op (x : EuclideanSpace ℂ (RCfg eta m)) :
    (gridRegHamU sys hL hV hκb).op x =
      Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) x :=
  rfl

lemma gridRegHamU_wMul (x : EuclideanSpace ℂ (RCfg eta m)) :
    PlaneWaveGridG.wMul (gridRegHamU sys hL hV hκb).W x =
      wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) x := rfl

lemma gridRegHamU_c : (gridRegHamU (m := m) sys hL hV hκb).c = 1 / 2 := rfl

lemma gridRegHamU_A : (gridRegHamU (m := m) sys hL hV hκb).A = gLAU sys V := rfl

include hL hV hκb in
/-- **Stage 3: uniform first-order graph-norm equivalence** for the `g_L` grid Hamiltonian
(`L ≥ 2π`): `‖H_grid v‖ ≤ (5/8)‖w_g v‖ + A‖v‖` and `‖w_g v‖ ≤ (8/3)‖H_grid v‖ + (4/3)(1 + 2A)‖v‖`,
`A = gLAU` `L`-free. -/
theorem gridGraphNorm_gL (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) v‖ ≤
        5 / 8 * ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) v‖ + gLAU sys V * ‖v‖ ∧
      ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) v‖ ≤
        8 / 3 * ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
          (2 * Real.pi / L) v‖ + 4 / 3 * (1 + 2 * gLAU sys V) * ‖v‖ := by
  have h1 := (gridRegHamU sys hL hV hκb).op_le v
  have h2 := (gridRegHamU sys hL hV hκb).elliptic_gen v
  rw [gridRegHamU_op, gridRegHamU_wMul, gridRegHamU_c, gridRegHamU_A] at h1 h2
  constructor
  · linarith
  · have e : (‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) v‖ + gLAU sys V * ‖v‖) / (1 / 2) =
          2 * ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
            (2 * Real.pi / L) v‖ + 2 * gLAU sys V * ‖v‖ := by ring
    rw [e] at h2
    linarith

/-- The `L`-free trajectory constant `(4/3)(1 + 4A)`, `A = gLAU`. -/
noncomputable def gridFlowConstU (sys : CoulombSystem eta ν) (V : ℝ) : ℝ :=
  4 / 3 * (1 + 4 * gLAU sys V)

lemma gridFlowConstU_nonneg {V : ℝ} (hV : 0 ≤ V) : 0 ≤ gridFlowConstU sys V := by
  unfold gridFlowConstU gLAU
  have := gLzU_nonneg sys hV
  positivity

include hL hV hκb in
/-- **Stage 3: regularity of grid trajectories, uniform in `L`** (`L ≥ 2π`):
`‖w_g (U v)‖ ≤ (5/3)‖w_g v‖ + (4/3)(1 + 4A)‖v‖` for every unitary `U` commuting with `H_grid`. -/
theorem norm_wPhys_gridFlow_le_gL
    (U : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hcomm : ∀ x, U (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (U x))
    (v : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (U v)‖ ≤
      5 / 3 * ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) v‖ +
        gridFlowConstU sys V * ‖v‖ := by
  have h := (gridRegHamU sys hL hV hκb).flow_le_weight U hcomm v
  rw [gridRegHamU_wMul, gridRegHamU_wMul, gridRegHamU_c, gridRegHamU_A] at h
  have e : 4 / 3 * (1 + 2 * gLAU sys V / (1 / 2)) = gridFlowConstU sys V := by
    unfold gridFlowConstU
    ring
  rw [e] at h
  exact h

end GridHam

/-- **The collocated observable in the physical weight**:
`‖w_g (O_g u)‖ ≤ (2 + 12 m̄) C_χ ‖w_g u‖ + ((3 + 12 m̄) C_χ + 14 g² D'_χ)‖u‖` (`g ≤ 1`), with the
physical second moment `g² D'_χ = Σ_ν |gν|² |χ̂(ν)|`. -/
theorem norm_wPhys_gridObs_le {m : ℕ} (P : RegParticles eta) {g : ℝ} (hg : g ^ 2 ≤ 1)
    (a : Fin eta) {c : Lat3 → ℂ} (hc : Summable fun ν => ‖c ν‖)
    (hc2 : Summable fun ν => nsq ν * ‖c ν‖) (u : EuclideanSpace ℂ (RCfg eta m)) :
    ‖wMul (wPhys P g) (gridObs a c u)‖ ≤
      (2 + 12 * P.maxMass) * (∑' ν, ‖c ν‖) * ‖wMul (wPhys P g) u‖ +
        ((3 + 12 * P.maxMass) * (∑' ν, ‖c ν‖) + 14 * (g ^ 2 * momTwo c)) * ‖u‖ := by
  have hC : 0 ≤ ∑' ν, ‖c ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hM := P.one_le_maxMass
  have hD : 0 ≤ momTwo c := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  have hg3 : 0 ≤ 1 - g ^ 2 := by linarith
  have hU := norm_nonneg u
  have h1 := norm_wPhys_le P hg (gridObs a c u)
  have h2 := norm_wM_gridObs_le P a hc hc2 u
  have h3 : ‖gridObs a c u‖ ≤ (∑' ν, ‖c ν‖) * ‖u‖ :=
    ((gridObs a c).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (norm_gridObs_le a hc) (norm_nonneg u))
  have h4 := sq_mul_norm_wM_le P hg u
  have hk : 0 ≤ (2 + 12 * P.maxMass) * (∑' ν, ‖c ν‖) := mul_nonneg (by linarith) hC
  have h5 : (1 - g ^ 2) * ‖gridObs a c u‖ ≤ (1 - g ^ 2) * ((∑' ν, ‖c ν‖) * ‖u‖) :=
    mul_le_mul_of_nonneg_left h3 hg3
  have h6 : g ^ 2 * ‖wMul (wM P) (gridObs a c u)‖ ≤
      (2 + 12 * P.maxMass) * (∑' ν, ‖c ν‖) * (g ^ 2 * ‖wMul (wM P) u‖) +
        14 * (g ^ 2 * momTwo c) * ‖u‖ := by
    have := mul_le_mul_of_nonneg_left h2 hg2
    linarith
  have h7 : (2 + 12 * P.maxMass) * (∑' ν, ‖c ν‖) * (g ^ 2 * ‖wMul (wM P) u‖) ≤
      (2 + 12 * P.maxMass) * (∑' ν, ‖c ν‖) *
        (‖wMul (wPhys P g) u‖ + (1 - g ^ 2) * ‖u‖) :=
    mul_le_mul_of_nonneg_left h4 hk
  have h8 : 0 ≤ (3 + 12 * P.maxMass) * g ^ 2 * ((∑' ν, ‖c ν‖) * ‖u‖) := by positivity
  nlinarith

/-- **The backward grid flow of `O_g v` in the physical weight, uniform in `L`** (`L ≥ 2π`). -/
theorem norm_wPhys_gridFlow_gridObs_le_gL (sys : CoulombSystem eta ν) {L V : ℝ}
    (hL : 2 * Real.pi ≤ L) (hV : 0 ≤ V) {m : ℕ} {κ : Lat3 → ℝ}
    (hκb : ∀ x, |κ x| ≤ gLgamma L V * coul x)
    (U : EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hcomm : ∀ x, U (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) x) = Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) (U x))
    (a : Fin eta) {χ : Lat3 → ℂ} (hχ1 : Summable fun ν => ‖χ ν‖)
    (hχ2 : Summable fun ν => nsq ν * ‖χ ν‖) (v : EuclideanSpace ℂ (RCfg eta m)) {X S : ℝ}
    (hX : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) v‖ ≤ X) (hS : ‖v‖ ≤ S) :
    ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (U (gridObs a χ v))‖ ≤
      5 / 3 * ((2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * X +
        ((3 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) + 14 * ((2 * Real.pi / L) ^ 2 * momTwo χ)) * S) +
        gridFlowConstU sys V * ((∑' ν, ‖χ ν‖) * S) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hg1 := PlaneWaveGridG.g_le_one hL
  have hg : 0 < 2 * Real.pi / L := by positivity
  have hg2 : (2 * Real.pi / L) ^ 2 ≤ 1 := pow_le_one₀ hg.le hg1
  have hC : 0 ≤ ∑' ν, ‖χ ν‖ := tsum_nonneg fun ν => norm_nonneg _
  have hD : 0 ≤ momTwo χ := tsum_nonneg fun ν => mul_nonneg (nsq_nonneg ν) (norm_nonneg _)
  have hJ := gridFlowConstU_nonneg sys hV
  have hM := sys.one_le_maxMass
  have h1 := norm_wPhys_gridFlow_le_gL sys hL hV hκb U hcomm (gridObs a χ v)
  have h2 := norm_wPhys_gridObs_le (regParticlesOf sys) hg2 a hχ1 hχ2 v
  have h3 : ‖gridObs a χ v‖ ≤ (∑' ν, ‖χ ν‖) * ‖v‖ :=
    ((gridObs a χ).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_gridObs_le a hχ1) (norm_nonneg v))
  have hc1 : 0 ≤ (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) := mul_nonneg (by linarith) hC
  have hc2 : 0 ≤ (3 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) + 14 * ((2 * Real.pi / L) ^ 2 * momTwo χ) :=
    add_nonneg (mul_nonneg (by linarith) hC) (by positivity)
  have h2' : ‖wMul (wPhys (regParticlesOf sys) (2 * Real.pi / L)) (gridObs a χ v)‖ ≤
      (2 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) * X +
        ((3 + 12 * sys.maxMass) * (∑' ν, ‖χ ν‖) + 14 * ((2 * Real.pi / L) ^ 2 * momTwo χ)) * S :=
    h2.trans (add_le_add (mul_le_mul_of_nonneg_left hX hc1) (mul_le_mul_of_nonneg_left hS hc2))
  have h3' : ‖gridObs a χ v‖ ≤ (∑' ν, ‖χ ν‖) * S := h3.trans (mul_le_mul_of_nonneg_left hS hC)
  exact h1.trans (add_le_add (mul_le_mul_of_nonneg_left h2' (by norm_num))
    (mul_le_mul_of_nonneg_left h3' hJ))

end FreeBoundary
