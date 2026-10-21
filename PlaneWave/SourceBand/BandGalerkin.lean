import PlaneWave.SourceBand.Band

/-!
# Source band block, part 3: `lem:band` for the Galerkin states; `lem:good-stab` (band)

* `fgood_cubeLift`: a good cube state (`IsGood`) is a good full-space state (`FGood`) through its
  lift, so the shell bound `band_W` applies to it;
* **`band_of_decomp`** (the static band criterion): if `A χ = f + e - W_N χ - d` with `χ` good,
  `Θ(f) ≤ Θ_f`, `‖1_S e‖ ≤ ε`, `‖1_S d‖ ≤ δ`, then
  `‖1_S ℰ χ̂‖ ≤ C(M, Θ_f) λ^{-1} ρ^{1/2} + ε + δ` and `‖1_S χ̂‖ ≤ (2m̄/λ²)(…)`;
* `retained_decomp`: the decomposition of a retained flow `e^{iH'τ} χ₀` (`H' = H_N + ΔH`) used by
  `good_stab'`;
* **`band_stab_gen`**, **`band_stab`** (`lem:good-stab`, band-good conclusion, repaired): with
  `‖ΔH u‖ ≤ α₁ Θ(u)`, `α₁ ≤ A/K`, and defect `ε₀ ≤ E/K` (repair (B) of the readiness review) the
  retained trajectory satisfies eq:band for every `λ ≥ max(2, g)`, `1 ≤ ρ ≤ λ`, uniformly in time;
  `band_stab_A`: the same with the shell hypothesis (iii) on the whole range (repair (A));
* **`band_galerkin`** (`lem:band` for `ψ_N(t)` and for `e^{iH_N(t-s)} P ψ(t)`): for every datum,
  every flow time and every cutoff with `K ≥ 1`, with a constant independent of the cutoff
  (`EvoData.restart` restarts the data at time `t`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal FSFlux

namespace FSBand

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Galerkin

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

omit [Fintype ν] in
lemma kinetic_cubeLift_emb (χ : En eta n) :
    coulombFourierKineticH2 sys (gF L) (cubeLift (gF L) n χ) =
      emb eta n (FSSpectral.kin (sb eta n) (Asym sys L n) χ) := by
  ext q
  rw [kinetic_apply', emb_kin_apply]
  change _ * Sm eta L (cubeLift (gF L) n χ) q = _
  rw [stateMap_cubeLift']

omit [Fintype ν] in
lemma wt_one_eq (χ : En eta n) :
    FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ = χ + FSSpectral.kin (sb eta n) (Asym sys L n) χ := by
  ext q
  rw [wt_one_apply, PiLp.add_apply, kin_apply']
  push_cast; ring

omit [Fintype ν] in
lemma emb_wt_one (χ : En eta n) :
    emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ) =
      Sm eta L (cubeLift (gF L) n χ) + coulombFourierKineticH2 sys (gF L) (cubeLift (gF L) n χ) := by
  rw [stateMap_cubeLift', kinetic_cubeLift_emb, ← map_add, wt_one_eq]

omit [Fintype ν] in
/-- A good cube state lifts to a good full-space state. -/
lemma fgood_cubeLift {M : ℝ} {χ : En eta n} (hχ : IsGood sys L 1 M χ) :
    FGood sys L M (cubeLift (gF L) n χ) := by
  refine ⟨?_, fun a l hl => ⟨?_, ?_⟩⟩
  · rw [stateMap_cubeLift', kinetic_cubeLift_emb, norm_emb, norm_emb]
    have h1 := hχ.1
    have h2 := norm_kin_le_wt sys (L := L) χ
    rw [one_mul] at h1; linarith
  · rw [stateMap_cubeLift', tailMask_emb, norm_emb]
    have := (hχ.2 a l hl).1; rwa [one_mul] at this
  · rw [kinetic_cubeLift_emb, tailMask_emb, norm_emb, ← kin_regTail]
    have := (hχ.2 a l hl).2; rw [one_mul] at this
    exact (norm_kin_le_wt sys _).trans this

omit [Fintype ν] in
include hL in
/-- Shells beyond `√3 K` miss the cube. -/
lemma shMask_emb_eq_zero (a : Fin eta) (cube : Bool) {lam ρ : ℝ}
    (hlam : Real.sqrt 3 * (gF L * n) < lam) (x : En eta n) :
    shMask a (physSh cube (gF L) lam ρ) (emb eta n x) = 0 := by
  have hg := gF_pos hL
  have hlam0 : 0 < lam := lt_of_le_of_lt (by positivity) hlam
  ext q
  rw [shMask_apply]
  split_ifs with h
  · by_cases hq : q ∈ fourierConfigCube eta n
    · exfalso
      have h1 := physSh_ge hg hlam0.le h
      have hP := (inP_iff_mem_cube n q).mpr hq
      have hc : ∀ i, ((q a i : ℤ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := fun i => by
        have := hP a i
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      have h2 : nsq (q a) ≤ 3 * (n : ℝ) ^ 2 := by
        unfold nsq; linarith [hc 0, hc 1, hc 2]
      have h3 : (lam / gF L) ^ 2 ≤ (Real.sqrt 3 * n) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]; linarith
      have h4 : lam / gF L ≤ Real.sqrt 3 * n :=
        (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h3
      rw [div_le_iff₀ hg] at h4
      nlinarith
    · simp only [emb, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply]
      rw [finiteFourierLpEmbed_apply_not_mem_cube eta n _ q hq]
      simp
  · simp

/-- The constant of the static band criterion: `(2^{5/2} + C_{K1}) M + 8 m̄ Θ_f`. -/
noncomputable def bandG (sys : CoulombSystem eta ν) (L Hunit M Θf : ℝ) : ℝ :=
  (2 ^ (5 / 2 : ℝ) + bandK1 sys L Hunit) * M + 8 * sys.maxMass * Θf

include hKernel hL in
/-- **The static band criterion** (`lem:band` for a cube state given by its equation): if
`A χ = f + e - W_N χ - d` with `χ` good (`M`), `Θ(f) ≤ Θ_f`, `‖1_S e‖ ≤ ε` and `‖1_S d‖ ≤ δ`, then
for `λ ≥ max(2, g)`, `1 ≤ ρ ≤ λ`:
`‖1_S ℰ χ̂‖ ≤ C λ^{-1} ρ^{1/2} + ε + δ` and `‖1_S χ̂‖ ≤ (2m̄/λ²)(C λ^{-1} ρ^{1/2} + ε + δ)`. -/
theorem band_of_decomp (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (χ f e d : En eta n) {M Θf ε δ : ℝ} (hχ : IsGood sys L 1 M χ)
    (hΘf : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 f‖ ≤ Θf)
    (hA : FSSpectral.kin (sb eta n) (Asym sys L n) χ =
      f + e - finiteCoulombPotential sys (coulombCellAmplitude L) n χ - d)
    (a : Fin eta) (cube : Bool) {lam ρ : ℝ} (hlam2 : 2 ≤ lam) (hlamg : gF L ≤ lam) (hρ : 1 ≤ ρ)
    (hρl : ρ ≤ lam)
    (he : ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n e)‖ ≤ ε)
    (hd : ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n d)‖ ≤ δ) :
    ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ))‖ ≤
        bandG sys L Hunit M Θf * lam⁻¹ * Real.sqrt ρ + (ε + δ) ∧
      ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n χ)‖ ≤
        2 * sys.maxMass / lam ^ 2 * (bandG sys L Hunit M Θf * lam⁻¹ * Real.sqrt ρ + (ε + δ)) := by
  have hg := gF_pos hL
  have hlam0 : 0 < lam := by linarith
  have hm := sys.one_le_maxMass
  have hM : 0 ≤ M := good_nonneg hχ
  have hΘf0 : 0 ≤ Θf := le_trans (norm_nonneg _) hΘf
  set sh := physSh cube (gF L) lam ρ
  have hsh2 : ∀ y, sh y → ((lam / 2) / gF L) ^ 2 < nsq y := by
    intro y hy
    have h1 := physSh_ge hg hlam0.le hy
    have h2 : ((lam / 2) / gF L) ^ 2 < (lam / gF L) ^ 2 := by
      apply pow_lt_pow_left₀ _ (by positivity) two_ne_zero
      rw [div_lt_div_iff_of_pos_right hg]; linarith
    linarith
  have hdec : emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ) =
      emb eta n χ + emb eta n f + emb eta n e -
        emb eta n (finiteCoulombPotential sys (coulombCellAmplitude L) n χ) - emb eta n d := by
    rw [wt_one_eq, hA]; simp only [map_add, map_sub]; abel
  have h1 : ‖shMask a sh (emb eta n χ)‖ ≤ M * (lam / 2) ^ (-(5 / 2 : ℝ)) := by
    refine (norm_shMask_le_tail hg a sh hsh2 _).trans ?_
    rw [tailMask_emb, norm_emb]
    have := (hχ.2 a (lam / 2) (by linarith)).1; rwa [one_mul] at this
  have h2 : ‖shMask a sh (emb eta n f)‖ ≤ 8 * sys.maxMass * Θf * (1 / lam ^ 2) := by
    refine (norm_shMask_le_tail hg a sh hsh2 _).trans ?_
    rw [tailMask_emb, norm_emb]
    have hl2 : (0 : ℝ) < lam / 2 := by linarith
    refine (regTail_le_kin sys hL a hl2 f).trans ?_
    rw [kin_regTail]
    have hk : ‖regTail L a (lam / 2) (FSSpectral.kin (sb eta n) (Asym sys L n) f)‖ ≤ Θf :=
      (norm_regTail_le L a _ _).trans ((norm_kin_le_wt sys f).trans hΘf)
    have hma := sys.mass_le_maxMass a
    have hma0 := sys.mass_pos a
    calc 2 * sys.mass a / (lam / 2) ^ 2 *
          ‖regTail L a (lam / 2) (FSSpectral.kin (sb eta n) (Asym sys L n) f)‖
        ≤ 2 * sys.maxMass / (lam / 2) ^ 2 * Θf := by
          refine mul_le_mul (div_le_div_of_nonneg_right (by linarith) (by positivity)) hk
            (norm_nonneg _) (by positivity)
      _ = 8 * sys.maxMass * Θf * (1 / lam ^ 2) := by field_simp; ring
  have h5 : ‖shMask a sh (emb eta n (finiteCoulombPotential sys (coulombCellAmplitude L) n χ))‖ ≤
      bandK1 sys L Hunit * M * lam⁻¹ * Real.sqrt ρ := by
    rw [← ext_W_cubeLift sys H hKernel χ, emb_ext, shMask_truncate]
    refine (molecularH2Truncate_norm_le n _).trans ?_
    exact band_W sys hL H hKernel Hunit hPeriodic (fgood_cubeLift sys hχ) a cube hlam2 hlamg hρ hρl
  have hA' : ‖shMask a sh (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ))‖ ≤
      bandG sys L Hunit M Θf * lam⁻¹ * Real.sqrt ρ + (ε + δ) := by
    rw [hdec, map_sub, map_sub, map_add, map_add]
    have n1 := norm_sub_le (shMask a sh (emb eta n χ) + shMask a sh (emb eta n f) +
      shMask a sh (emb eta n e) -
        shMask a sh (emb eta n (finiteCoulombPotential sys (coulombCellAmplitude L) n χ)))
      (shMask a sh (emb eta n d))
    have n2 := norm_sub_le (shMask a sh (emb eta n χ) + shMask a sh (emb eta n f) +
      shMask a sh (emb eta n e))
        (shMask a sh (emb eta n (finiteCoulombPotential sys (coulombCellAmplitude L) n χ)))
    have n3 := norm_add_le (shMask a sh (emb eta n χ) + shMask a sh (emb eta n f))
      (shMask a sh (emb eta n e))
    have n4 := norm_add_le (shMask a sh (emb eta n χ)) (shMask a sh (emb eta n f))
    have k1 := mul_le_mul_of_nonneg_left (tail52_arith hlam2 hρ) hM
    have k2 := mul_le_mul_of_nonneg_left (inv_sq_arith (by linarith : (1 : ℝ) ≤ lam) hρ)
      (by positivity : (0 : ℝ) ≤ 8 * sys.maxMass * Θf)
    have e2 : bandG sys L Hunit M Θf * lam⁻¹ * Real.sqrt ρ =
        M * (2 ^ (5 / 2 : ℝ) * lam⁻¹ * Real.sqrt ρ) +
          8 * sys.maxMass * Θf * (lam⁻¹ * Real.sqrt ρ) +
          bandK1 sys L Hunit * M * lam⁻¹ * Real.sqrt ρ := by
      unfold bandG; ring
    rw [e2]
    linarith
  refine ⟨hA', ?_⟩
  have h6 := shell_state_le sys hL hlam0 a sh (fun y hy => physSh_ge hg hlam0.le hy)
    (cubeLift (gF L) n χ)
  rw [← emb_wt_one, stateMap_cubeLift'] at h6
  exact h6.trans (mul_le_mul_of_nonneg_left hA' (by positivity))

include hKernel hL in
/-- The decomposition of a retained flow `χ = e^{iH'τ} χ₀`, `χ₀ = P ψ₀ + r₀` (as in `good_stab'`):
`A χ = f + e - W_N χ - ΔH χ` with `f = e^{iH'τ} P S v₀` and `e = e^{iH'τ} e₀`, `e₀` the defect. -/
theorem retained_decomp (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = Sm eta L v₀) (r₀ : En eta n) {Θv ε₀ : ℝ}
    (hΘv : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L v₀))‖ ≤ Θv)
    (hε₀ : ‖finiteCoulombHamiltonian sys L n r₀ + ΔH (ext eta n (Sm eta L u₀) + r₀) -
      ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀))‖ ≤ ε₀) (τ : ℝ) :
    ∃ f e : En eta n,
      FSSpectral.kin (sb eta n) (Asym sys L n)
          (retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀)) =
        f + e - finiteCoulombPotential sys (coulombCellAmplitude L) n
            (retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀)) -
          ΔH (retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀)) ∧
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 f‖ ≤ Cfl sys L Hunit CΔ * Θv ∧ ‖e‖ ≤ ε₀ := by
  set χ₀ := ext eta n (Sm eta L u₀) + r₀
  set χ := retFlow sys L n hΔsym τ χ₀
  have hC := Cfl_nonneg sys Hunit hCΔ (L := L)
  set f := retFlow sys L n hΔsym τ (ext eta n (Sm eta L v₀))
  set e₀ := finiteCoulombHamiltonian sys L n r₀ + ΔH χ₀ -
    ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀))
  set e := retFlow sys L n hΔsym τ e₀
  have hHχ₀ : Hret sys L n ΔH χ₀ = ext eta n (Sm eta L v₀) + e₀ := by
    have hext : ext eta n (H u₀) = finiteCoulombHamiltonian sys L n (ext eta n (Sm eta L u₀)) +
        ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀)) := extract_H_eq sys L H hKernel n u₀
    rw [huv] at hext
    rw [hext]
    have h1 : Hret sys L n ΔH χ₀ = finiteCoulombHamiltonian sys L n (ext eta n (Sm eta L u₀)) +
        finiteCoulombHamiltonian sys L n r₀ + ΔH χ₀ := by
      unfold Hret
      rw [LinearMap.add_apply, map_add]
    rw [h1]
    simp only [e₀]
    abel
  have hdec : Hret sys L n ΔH χ = f + e := by
    rw [Hret_retFlow, hHχ₀, retFlow_add_apply]
  refine ⟨f, e, ?_, ?_, ?_⟩
  · have := Hret_eq_kin_add sys L n ΔH χ
    rw [hdec] at this
    unfold Vret at this
    rw [LinearMap.add_apply] at this
    rw [this]; abel
  · exact (theta_retFlow_le sys Hunit hL hPeriodic hΔsym hCΔ hΔb τ _).trans
      (mul_le_mul_of_nonneg_left hΘv hC)
  · rw [norm_retFlow]; exact hε₀

/-- The goodness budget of the retained flow (`good_stab'`). -/
noncomputable def Mret (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (CΔ α Θ₀ Θv ε₀ : ℝ) : ℝ :=
  Mdec sys L Hunit n (Cfl sys L Hunit CΔ * Θ₀) (Cfl sys L Hunit CΔ * Θv) ε₀
    (α * (Cfl sys L Hunit CΔ * Θ₀))

include hKernel hL in
/-- **`lem:good-stab`, the band conclusion, general form**: for the retained flow
`χ(τ) = e^{iH'τ} χ₀` of `good_stab'`, with shell bounds `‖1_S e₀‖ ≤ ε_S` on the defect and
`‖1_S ΔH χ(τ)‖ ≤ δ_S` on the perturbation,
`‖1_S ℰ χ̂‖ ≤ C λ^{-1} ρ^{1/2} + ε_S + δ_S` (and `‖1_S χ̂‖ ≤ (2m̄/λ²)(…)`). -/
theorem band_stab_gen (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : ∀ v, ‖ΔH v‖ ≤ α * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = Sm eta L v₀) (r₀ : En eta n)
    {Θ₀ Θv ε₀ : ℝ}
    (hΘ₀ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L u₀) + r₀)‖ ≤ Θ₀)
    (hΘv : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L v₀))‖ ≤ Θv)
    (hε₀ : ‖finiteCoulombHamiltonian sys L n r₀ + ΔH (ext eta n (Sm eta L u₀) + r₀) -
      ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀))‖ ≤ ε₀)
    (τ : ℝ) (a : Fin eta) (cube : Bool) {lam ρ εS δS : ℝ} (hlam2 : 2 ≤ lam) (hlamg : gF L ≤ lam)
    (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam)
    (heS : ∀ e : En eta n, ‖e‖ ≤ ε₀ → ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n e)‖ ≤ εS)
    (hdS : ‖shMask a (physSh cube (gF L) lam ρ)
      (emb eta n (ΔH (retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀))))‖ ≤ δS) :
    ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1
        (retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀))))‖ ≤
        bandG sys L Hunit (Mret sys L Hunit n CΔ α Θ₀ Θv ε₀) (Cfl sys L Hunit CΔ * Θv) * lam⁻¹ *
          Real.sqrt ρ + (εS + δS) ∧
      ‖shMask a (physSh cube (gF L) lam ρ)
          (emb eta n (retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀)))‖ ≤
        2 * sys.maxMass / lam ^ 2 * (bandG sys L Hunit (Mret sys L Hunit n CΔ α Θ₀ Θv ε₀)
          (Cfl sys L Hunit CΔ * Θv) * lam⁻¹ * Real.sqrt ρ + (εS + δS)) := by
  have hgood := good_stab' sys H hKernel Hunit hL hPeriodic hΔsym hCΔ hΔb hα0 hα u₀ v₀ huv r₀
    hΘ₀ hΘv hε₀ τ
  obtain ⟨f, e, hA, hf, he⟩ := retained_decomp sys hL H hKernel Hunit hPeriodic hΔsym hCΔ hΔb
    u₀ v₀ huv r₀ hΘv hε₀ τ
  exact band_of_decomp sys hL H hKernel Hunit hPeriodic _ f e _ hgood hf hA a cube hlam2 hlamg hρ
    hρl (heS e he) hdS

include hKernel hL in
/-- **`lem:good-stab`, the band-good conclusion, repaired (B)**: if moreover `α ≤ A/K` and the
defect is `ε₀ ≤ E/K` (`K = g n`), then for every `λ ≥ max(2, g)` and `1 ≤ ρ ≤ λ`, uniformly in `τ`,
`‖1_S ℰ χ̂(τ)‖ ≤ C' λ^{-1} ρ^{1/2}` and `‖1_S χ̂(τ)‖ ≤ 2m̄ C' λ^{-3} ρ^{1/2}`, with
`C' = C + √3 (E + A C_fl Θ₀)`; shells beyond `√3 K` are empty. -/
theorem band_stab (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : ∀ v, ‖ΔH v‖ ≤ α * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = Sm eta L v₀) (r₀ : En eta n)
    {Θ₀ Θv ε₀ A E : ℝ}
    (hΘ₀ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L u₀) + r₀)‖ ≤ Θ₀)
    (hΘv : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L v₀))‖ ≤ Θv)
    (hε₀ : ‖finiteCoulombHamiltonian sys L n r₀ + ΔH (ext eta n (Sm eta L u₀) + r₀) -
      ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀))‖ ≤ ε₀)
    (hK : 0 < gF L * n) (hαK : α ≤ A / (gF L * n)) (hεK : ε₀ ≤ E / (gF L * n))
    (τ : ℝ) (a : Fin eta) (cube : Bool) {lam ρ : ℝ} (hlam2 : 2 ≤ lam) (hlamg : gF L ≤ lam)
    (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam) :
    ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1
        (retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀))))‖ ≤
        (bandG sys L Hunit (Mret sys L Hunit n CΔ α Θ₀ Θv ε₀) (Cfl sys L Hunit CΔ * Θv) +
          Real.sqrt 3 * (E + A * (Cfl sys L Hunit CΔ * Θ₀))) * lam⁻¹ * Real.sqrt ρ ∧
      ‖shMask a (physSh cube (gF L) lam ρ)
          (emb eta n (retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀)))‖ ≤
        2 * sys.maxMass * (bandG sys L Hunit (Mret sys L Hunit n CΔ α Θ₀ Θv ε₀)
          (Cfl sys L Hunit CΔ * Θv) + Real.sqrt 3 * (E + A * (Cfl sys L Hunit CΔ * Θ₀))) *
          lam ^ (-(3 : ℝ)) * Real.sqrt ρ := by
  have hg := gF_pos hL
  have hlam0 : 0 < lam := by linarith
  have hm := sys.one_le_maxMass
  have hC := Cfl_nonneg sys Hunit hCΔ (L := L)
  have hΘ₀0 : 0 ≤ Θ₀ := le_trans (norm_nonneg _) hΘ₀
  have hΘv0 : 0 ≤ Θv := le_trans (norm_nonneg _) hΘv
  have hε0 : 0 ≤ ε₀ := le_trans (norm_nonneg _) hε₀
  have hE : 0 ≤ E := by
    have := hε0.trans hεK
    rwa [le_div_iff₀ hK, zero_mul] at this
  have hA0 : 0 ≤ A := by
    have := hα0.trans hαK
    rwa [le_div_iff₀ hK, zero_mul] at this
  set χ := retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀)
  set C₀ := bandG sys L Hunit (Mret sys L Hunit n CΔ α Θ₀ Θv ε₀) (Cfl sys L Hunit CΔ * Θv)
  set C₁ := Real.sqrt 3 * (E + A * (Cfl sys L Hunit CΔ * Θ₀))
  have hC₁ : 0 ≤ C₁ := by positivity
  have hgood := good_stab' sys H hKernel Hunit hL hPeriodic hΔsym hCΔ hΔb hα0 hα u₀ v₀ huv r₀
    hΘ₀ hΘv hε₀ τ
  have hC₀ : 0 ≤ C₀ := by
    have hM := good_nonneg hgood
    have := bandK1_nonneg sys hL Hunit
    simp only [C₀, bandG]
    have : (0 : ℝ) ≤ 2 ^ (5 / 2 : ℝ) := by positivity
    positivity
  -- the main bound
  have hmain : ‖shMask a (physSh cube (gF L) lam ρ)
      (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ))‖ ≤ (C₀ + C₁) * lam⁻¹ * Real.sqrt ρ := by
    by_cases hlK : lam ≤ Real.sqrt 3 * (gF L * n)
    · -- `1/K ≤ √3/λ`
      have hKinv : 1 / (gF L * n) ≤ Real.sqrt 3 * lam⁻¹ := by
        rw [div_le_iff₀ hK]
        calc (1 : ℝ) = Real.sqrt 3 * lam⁻¹ * (lam / Real.sqrt 3) := by
              field_simp
          _ ≤ Real.sqrt 3 * lam⁻¹ * (gF L * n) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [div_le_iff₀ (by positivity)]; linarith
      have hsq : 1 ≤ Real.sqrt ρ := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
      have hd : ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n (ΔH χ))‖ ≤
          A * (Cfl sys L Hunit CΔ * Θ₀) * (1 / (gF L * n)) := by
        refine (norm_shMask_le _ _ _).trans ?_
        rw [norm_emb]
        refine (hα χ).trans ?_
        have hΘχ := (theta_retFlow_le sys Hunit hL hPeriodic hΔsym hCΔ hΔb τ _).trans
          (mul_le_mul_of_nonneg_left hΘ₀ hC)
        calc α * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ‖
            ≤ A / (gF L * n) * (Cfl sys L Hunit CΔ * Θ₀) :=
              mul_le_mul hαK hΘχ (norm_nonneg _) (by positivity)
          _ = A * (Cfl sys L Hunit CΔ * Θ₀) * (1 / (gF L * n)) := by ring
      have h := (band_stab_gen sys hL H hKernel Hunit hPeriodic hΔsym hCΔ hΔb hα0 hα u₀ v₀ huv r₀
        hΘ₀ hΘv hε₀ τ a cube (εS := E * (1 / (gF L * n))) hlam2 hlamg hρ hρl
        (fun e he => (norm_shMask_le _ _ _).trans (by
          rw [norm_emb]; refine he.trans (hεK.trans (le_of_eq ?_)); ring)) hd).1
      refine h.trans ?_
      have k : E * (1 / (gF L * n)) + A * (Cfl sys L Hunit CΔ * Θ₀) * (1 / (gF L * n)) ≤
          C₁ * lam⁻¹ * Real.sqrt ρ := by
        have e1 : E * (1 / (gF L * n)) + A * (Cfl sys L Hunit CΔ * Θ₀) * (1 / (gF L * n)) =
            (E + A * (Cfl sys L Hunit CΔ * Θ₀)) * (1 / (gF L * n)) := by ring
        rw [e1]
        calc (E + A * (Cfl sys L Hunit CΔ * Θ₀)) * (1 / (gF L * n))
            ≤ (E + A * (Cfl sys L Hunit CΔ * Θ₀)) * (Real.sqrt 3 * lam⁻¹) :=
              mul_le_mul_of_nonneg_left hKinv (by positivity)
          _ = C₁ * lam⁻¹ := by simp only [C₁]; ring
          _ ≤ C₁ * lam⁻¹ * Real.sqrt ρ := by
              have : 0 ≤ C₁ * lam⁻¹ := by positivity
              nlinarith
      have : C₀ * lam⁻¹ * Real.sqrt ρ + C₁ * lam⁻¹ * Real.sqrt ρ = (C₀ + C₁) * lam⁻¹ * Real.sqrt ρ := by
        ring
      linarith
    · push Not at hlK
      rw [shMask_emb_eq_zero hL a cube hlK, norm_zero]
      positivity
  refine ⟨hmain, ?_⟩
  have hsh : ∀ y, physSh cube (gF L) lam ρ y → (lam / gF L) ^ 2 ≤ nsq y :=
    fun y hy => physSh_ge hg hlam0.le hy
  have h6 := shell_state_le sys hL hlam0 a (physSh cube (gF L) lam ρ) hsh (cubeLift (gF L) n χ)
  rw [← emb_wt_one, stateMap_cubeLift'] at h6
  refine h6.trans ?_
  calc 2 * sys.maxMass / lam ^ 2 *
        ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ))‖
      ≤ 2 * sys.maxMass / lam ^ 2 * ((C₀ + C₁) * lam⁻¹ * Real.sqrt ρ) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = 2 * sys.maxMass * (C₀ + C₁) * lam ^ (-(3 : ℝ)) * Real.sqrt ρ := by
        rw [rpow_neg_three_eq hlam0]; ring

include hKernel hL in
/-- **`lem:good-stab`, the band-good conclusion, repaired (A)**: the shell hypothesis (iii)
`‖1_S ΔH u‖ ≤ α₃ λ^{-1} ρ^{1/2} Θ(u)` on the whole range and a defect `ε₀ ≤ E/K` give eq:band
for every `λ ≥ max(2, g)`, `1 ≤ ρ ≤ λ`, uniformly in `τ`. -/
theorem band_stab_A (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : ∀ v, ‖ΔH v‖ ≤ α * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = Sm eta L v₀) (r₀ : En eta n)
    {Θ₀ Θv ε₀ α₃ E : ℝ}
    (hΘ₀ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L u₀) + r₀)‖ ≤ Θ₀)
    (hΘv : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L v₀))‖ ≤ Θv)
    (hε₀ : ‖finiteCoulombHamiltonian sys L n r₀ + ΔH (ext eta n (Sm eta L u₀) + r₀) -
      ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀))‖ ≤ ε₀)
    (hK : 0 < gF L * n) (hεK : ε₀ ≤ E / (gF L * n)) (hα₃ : 0 ≤ α₃)
    (τ : ℝ) (a : Fin eta) (cube : Bool) {lam ρ : ℝ} (hlam2 : 2 ≤ lam) (hlamg : gF L ≤ lam)
    (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam)
    (hiii : ∀ u : En eta n, ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n (ΔH u))‖ ≤
      α₃ * lam⁻¹ * Real.sqrt ρ * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) :
    ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1
        (retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀))))‖ ≤
        (bandG sys L Hunit (Mret sys L Hunit n CΔ α Θ₀ Θv ε₀) (Cfl sys L Hunit CΔ * Θv) +
          Real.sqrt 3 * E + α₃ * (Cfl sys L Hunit CΔ * Θ₀)) * lam⁻¹ * Real.sqrt ρ := by
  have hg := gF_pos hL
  have hlam0 : 0 < lam := by linarith
  have hC := Cfl_nonneg sys Hunit hCΔ (L := L)
  have hΘ₀0 : 0 ≤ Θ₀ := le_trans (norm_nonneg _) hΘ₀
  have hε0 : 0 ≤ ε₀ := le_trans (norm_nonneg _) hε₀
  have hE : 0 ≤ E := by
    have := hε0.trans hεK
    rwa [le_div_iff₀ hK, zero_mul] at this
  set χ := retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀)
  have hgood := good_stab' sys H hKernel Hunit hL hPeriodic hΔsym hCΔ hΔb hα0 hα u₀ v₀ huv r₀
    hΘ₀ hΘv hε₀ τ
  have hC₀ : 0 ≤ bandG sys L Hunit (Mret sys L Hunit n CΔ α Θ₀ Θv ε₀) (Cfl sys L Hunit CΔ * Θv) := by
    have hM := good_nonneg hgood
    have := bandK1_nonneg sys hL Hunit
    have hΘv0 : 0 ≤ Θv := le_trans (norm_nonneg _) hΘv
    unfold bandG
    have : (0 : ℝ) ≤ 2 ^ (5 / 2 : ℝ) := by positivity
    have := sys.one_le_maxMass
    unfold Mret at hM ⊢
    positivity
  by_cases hlK : lam ≤ Real.sqrt 3 * (gF L * n)
  · have hKinv : 1 / (gF L * n) ≤ Real.sqrt 3 * lam⁻¹ := by
      rw [div_le_iff₀ hK]
      calc (1 : ℝ) = Real.sqrt 3 * lam⁻¹ * (lam / Real.sqrt 3) := by
            field_simp
        _ ≤ Real.sqrt 3 * lam⁻¹ * (gF L * n) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [div_le_iff₀ (by positivity)]; linarith
    have hsq : 1 ≤ Real.sqrt ρ := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
    have hΘχ := (theta_retFlow_le sys Hunit hL hPeriodic hΔsym hCΔ hΔb τ
      (ext eta n (Sm eta L u₀) + r₀)).trans (mul_le_mul_of_nonneg_left hΘ₀ hC)
    have hd : ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n (ΔH χ))‖ ≤
        α₃ * (Cfl sys L Hunit CΔ * Θ₀) * (lam⁻¹ * Real.sqrt ρ) := by
      refine (hiii χ).trans ?_
      calc α₃ * lam⁻¹ * Real.sqrt ρ * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ‖
          ≤ α₃ * lam⁻¹ * Real.sqrt ρ * (Cfl sys L Hunit CΔ * Θ₀) :=
            mul_le_mul_of_nonneg_left hΘχ (by positivity)
        _ = _ := by ring
    have h := (band_stab_gen sys hL H hKernel Hunit hPeriodic hΔsym hCΔ hΔb hα0 hα u₀ v₀ huv r₀
      hΘ₀ hΘv hε₀ τ a cube (εS := E * (1 / (gF L * n))) hlam2 hlamg hρ hρl
      (fun e he => (norm_shMask_le _ _ _).trans (by
        rw [norm_emb]; refine he.trans (hεK.trans (le_of_eq ?_)); ring)) hd).1
    refine h.trans ?_
    have k : E * (1 / (gF L * n)) ≤ Real.sqrt 3 * E * (lam⁻¹ * Real.sqrt ρ) := by
      calc E * (1 / (gF L * n)) ≤ E * (Real.sqrt 3 * lam⁻¹) := mul_le_mul_of_nonneg_left hKinv hE
        _ = Real.sqrt 3 * E * lam⁻¹ := by ring
        _ ≤ Real.sqrt 3 * E * (lam⁻¹ * Real.sqrt ρ) := by
            have : 0 ≤ Real.sqrt 3 * E * lam⁻¹ := by positivity
            nlinarith
    have e1 : (bandG sys L Hunit (Mret sys L Hunit n CΔ α Θ₀ Θv ε₀) (Cfl sys L Hunit CΔ * Θv) +
        Real.sqrt 3 * E + α₃ * (Cfl sys L Hunit CΔ * Θ₀)) * lam⁻¹ * Real.sqrt ρ =
        bandG sys L Hunit (Mret sys L Hunit n CΔ α Θ₀ Θv ε₀) (Cfl sys L Hunit CΔ * Θv) * lam⁻¹ *
          Real.sqrt ρ + Real.sqrt 3 * E * (lam⁻¹ * Real.sqrt ρ) +
          α₃ * (Cfl sys L Hunit CΔ * Θ₀) * (lam⁻¹ * Real.sqrt ρ) := by ring
    rw [e1]
    linarith
  · push Not at hlK
    rw [shMask_emb_eq_zero hL a cube hlK, norm_zero]
    have : 0 ≤ α₃ * (Cfl sys L Hunit CΔ * Θ₀) := by positivity
    positivity

/-- The evolution data restarted at time `t` (datum `ψ(t)`, `H ψ(t) = S v(t)`). -/
noncomputable def restart (D : EvoData L H) (t : ℝ) : EvoData L H where
  U := D.U
  U0 := D.U0
  graph := D.graph
  deriv := D.deriv
  cont := D.cont
  u₀ := traj H D t
  v₀ := Classical.choose (D.graph t D.v₀)
  uv := by
    rw [traj_H, D.uv]
    exact (Classical.choose_spec (D.graph t D.v₀)).1.symm

omit [Fintype ν] in
lemma restart_u₀ (D : EvoData L H) (t : ℝ) : (restart H D t).u₀ = traj H D t := rfl

omit [Fintype ν] in
lemma restart_Xi (D : EvoData L H) (t : ℝ) : (restart H D t).Xi = D.Xi := by
  unfold EvoData.Xi
  change ‖Sm eta L (traj H D t)‖ + ‖H (traj H D t)‖ + ‖H (Classical.choose (D.graph t D.v₀))‖ = _
  rw [traj_S, traj_H, (Classical.choose_spec (D.graph t D.v₀)).2, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

/-- The cutoff-independent constant of `lem:band` for the Galerkin states (per unit `Ξ`). -/
noncomputable def bandN (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  bandG sys L Hunit (FSSrc1.mNu sys L Hunit) (Cfl sys L Hunit 0 * cvT sys L Hunit) +
    3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit

include hKernel hL in
/-- **`lem:band` for the Galerkin flows** `e^{iH_N τ} P ψ₀` (so `ψ_N(t)` at `τ = -t`, and, for the
data restarted at `t`, the backward trajectory `e^{iH_N(t-s)} P ψ(t)`): for every cutoff with
`K ≥ 1`, every `λ ≥ max(2, g)` and `1 ≤ ρ ≤ λ`, uniformly in `τ` and in the cutoff,
`‖1_S ℰ û‖ ≤ C Ξ λ^{-1} ρ^{1/2}` and `‖1_S û‖ ≤ 2m̄ C Ξ λ^{-3} ρ^{1/2}`. -/
theorem band_galerkin (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (D : EvoData L H) (τ : ℝ) (a : Fin eta) (cube : Bool) {lam ρ : ℝ}
    (hlam2 : 2 ≤ lam) (hlamg : gF L ≤ lam) (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam) :
    ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1
        (retFlow sys L n (zero_isSymmetric (n := n)) τ (ext eta n (Sm eta L D.u₀)))))‖ ≤
        bandN sys L Hunit * D.Xi * lam⁻¹ * Real.sqrt ρ ∧
      ‖shMask a (physSh cube (gF L) lam ρ)
          (emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) τ (ext eta n (Sm eta L D.u₀))))‖ ≤
        2 * sys.maxMass * bandN sys L Hunit * D.Xi * lam ^ (-(3 : ℝ)) * Real.sqrt ρ := by
  have hg := gF_pos hL
  have hlam0 : 0 < lam := by linarith
  have hm := sys.one_le_maxMass
  have hΞ := D.Xi_nonneg
  have hK0 : 0 < gF L * n := by linarith
  have hC := Cfl_nonneg sys Hunit le_rfl (L := L)
  have hcv := cvT_nonneg sys (L := L) Hunit
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hcT := cTr_nonneg sys hL Hunit
  set χ := retFlow sys L n (zero_isSymmetric (n := n)) τ (ext eta n (Sm eta L D.u₀))
  have hgood : IsGood sys L 1 (FSSrc1.mNu sys L Hunit * D.Xi) χ :=
    isGood_mono sys (psiN_good sys hL H hKernel Hunit hPeriodic hKg D τ)
      (mul_le_mul_of_nonneg_right (FSSrc1.mN_le_mNu (sys := sys) Hunit hL hKg) hΞ)
  have hM := good_nonneg hgood
  have hK1 := bandK1_nonneg sys hL Hunit
  have hmNu : 0 ≤ FSSrc1.mNu sys L Hunit := by
    unfold FSSrc1.mNu
    have := Cfl_nonneg sys (L := L) Hunit (le_refl (0 : ℝ))
    have := CtW_nonneg sys hL Hunit (M₂ := 3 * sys.maxMass * (Cfl sys L Hunit 0 * (2 * cTr sys L Hunit)))
      (by positivity)
    positivity
  have hbN : 0 ≤ bandN sys L Hunit := by
    unfold bandN bandG
    have : (0 : ℝ) ≤ 2 ^ (5 / 2 : ℝ) := by positivity
    positivity
  have hmain : ‖shMask a (physSh cube (gF L) lam ρ)
      (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ))‖ ≤
      bandN sys L Hunit * D.Xi * lam⁻¹ * Real.sqrt ρ := by
    by_cases hlK : lam ≤ Real.sqrt 3 * (gF L * n)
    · have hF0 := datum_fgood sys hL H hKernel Hunit hPeriodic D
      have hW0 : ‖Wp sys L H (D.u₀ - molecularH2Truncate n D.u₀)‖ ≤ omC sys L Hunit n * D.Xi :=
        (fgood_W H hKernel Hunit hL hPeriodic hF0 hKg).trans (le_of_eq (by unfold omC; ring))
      have hε₀ : ‖finiteCoulombHamiltonian sys L n 0 + (0 : En eta n →ₗ[ℂ] En eta n)
          (ext eta n (Sm eta L D.u₀) + 0) -
            ext eta n (Wp sys L H (D.u₀ - molecularH2Truncate n D.u₀))‖ ≤ omC sys L Hunit n * D.Xi := by
        simp only [map_zero, LinearMap.zero_apply, zero_add, zero_sub, norm_neg]
        exact (norm_ext_le _).trans hW0
      have hΘv := theta_v0_le sys hL H hKernel Hunit hPeriodic (n := n) D
      obtain ⟨f, e, hA, hf, he⟩ := retained_decomp sys hL H hKernel Hunit hPeriodic
        (zero_isSymmetric (n := n)) le_rfl (fun v => by simp) D.u₀ D.v₀ D.uv 0 hΘv hε₀ τ
      rw [add_zero] at hA
      have hA' : FSSpectral.kin (sb eta n) (Asym sys L n) χ =
          f + e - finiteCoulombPotential sys (coulombCellAmplitude L) n χ - 0 := by
        rw [hA, LinearMap.zero_apply]
      have h := (band_of_decomp sys hL H hKernel Hunit hPeriodic χ f e 0 hgood hf hA' a cube
        hlam2 hlamg hρ hρl (ε := omC sys L Hunit n * D.Xi) (δ := 0)
        ((norm_shMask_le _ _ _).trans (by rw [norm_emb]; exact he))
        (by rw [map_zero, map_zero, norm_zero])).1
      refine h.trans ?_
      -- `ω Ξ ≤ 3 η C_m c_tr Ξ λ^{-1} ρ^{1/2}` for `λ ≤ √3 K`
      have hKinv : (gF L * n) ^ (-(3 / 2 : ℝ)) ≤ Real.sqrt 3 * lam⁻¹ := by
        have h1 : (gF L * n) ^ (-(3 / 2 : ℝ)) ≤ (gF L * n)⁻¹ := by
          have := rpow_le_of_le_one hKg (show -(3 / 2 : ℝ) ≤ -1 by norm_num)
          rwa [Real.rpow_neg_one] at this
        refine h1.trans ?_
        rw [inv_le_iff_one_le_mul₀ hK0]
        calc (1 : ℝ) = Real.sqrt 3 * lam⁻¹ * (lam / Real.sqrt 3) := by field_simp
          _ ≤ Real.sqrt 3 * lam⁻¹ * (gF L * n) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [div_le_iff₀ (by positivity)]; linarith
      have hsq : 1 ≤ Real.sqrt ρ := by rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
      have hom : omC sys L Hunit n * D.Xi ≤
          3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit * D.Xi *
            lam⁻¹ * Real.sqrt ρ := by
        unfold omC
        have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
        have h0 : 0 ≤ Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit *
            cTr sys L Hunit * D.Xi := by positivity
        calc Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit *
              (gF L * n) ^ (-(3 / 2 : ℝ)) * D.Xi
            = (Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit *
                cTr sys L Hunit * D.Xi) * (gF L * n) ^ (-(3 / 2 : ℝ)) := by ring
          _ ≤ (Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit *
                cTr sys L Hunit * D.Xi) * (Real.sqrt 3 * lam⁻¹) :=
              mul_le_mul_of_nonneg_left hKinv h0
          _ = 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit * D.Xi *
                lam⁻¹ := by
              have e : (Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit *
                  cTr sys L Hunit * D.Xi) * (Real.sqrt 3 * lam⁻¹) = (Real.sqrt 3 * Real.sqrt 3) *
                    (eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit * D.Xi *
                      lam⁻¹) := by ring
              rw [e, h3]; ring
          _ ≤ _ := by
              have : 0 ≤ 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit *
                  D.Xi * lam⁻¹ := by positivity
              nlinarith
      have hG : bandG sys L Hunit (FSSrc1.mNu sys L Hunit * D.Xi) (Cfl sys L Hunit 0 * (cvT sys L Hunit * D.Xi)) =
          bandG sys L Hunit (FSSrc1.mNu sys L Hunit) (Cfl sys L Hunit 0 * cvT sys L Hunit) * D.Xi := by
        unfold bandG; ring
      rw [hG]
      have e1 : bandN sys L Hunit * D.Xi * lam⁻¹ * Real.sqrt ρ =
          bandG sys L Hunit (FSSrc1.mNu sys L Hunit) (Cfl sys L Hunit 0 * cvT sys L Hunit) * D.Xi * lam⁻¹ *
            Real.sqrt ρ + 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit *
              cTr sys L Hunit * D.Xi * lam⁻¹ * Real.sqrt ρ := by
        unfold bandN; ring
      rw [e1]
      linarith
    · push Not at hlK
      rw [shMask_emb_eq_zero hL a cube hlK, norm_zero]
      positivity
  refine ⟨hmain, ?_⟩
  have hsh : ∀ y, physSh cube (gF L) lam ρ y → (lam / gF L) ^ 2 ≤ nsq y :=
    fun y hy => physSh_ge hg hlam0.le hy
  have h6 := shell_state_le sys hL hlam0 a (physSh cube (gF L) lam ρ) hsh (cubeLift (gF L) n χ)
  rw [← emb_wt_one, stateMap_cubeLift'] at h6
  refine h6.trans ?_
  calc 2 * sys.maxMass / lam ^ 2 *
        ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1 χ))‖
      ≤ 2 * sys.maxMass / lam ^ 2 * (bandN sys L Hunit * D.Xi * lam⁻¹ * Real.sqrt ρ) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = 2 * sys.maxMass * bandN sys L Hunit * D.Xi * lam ^ (-(3 : ℝ)) * Real.sqrt ρ := by
        rw [rpow_neg_three_eq hlam0]; ring

include hKernel hL in
/-- **`lem:band` for the backward Galerkin trajectory** `e^{iH_N(t-s)} P ψ(t)` (any flow time `τ`):
the Galerkin bound for the data restarted at `t`. -/
theorem band_backward (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (D : EvoData L H) (t τ : ℝ) (a : Fin eta) (cube : Bool) {lam ρ : ℝ}
    (hlam2 : 2 ≤ lam) (hlamg : gF L ≤ lam) (hρ : 1 ≤ ρ) (hρl : ρ ≤ lam) :
    ‖shMask a (physSh cube (gF L) lam ρ) (emb eta n (FSSpectral.wt (sb eta n) (Asym sys L n) 1
        (retFlow sys L n (zero_isSymmetric (n := n)) τ (ext eta n (Sm eta L (traj H D t))))))‖ ≤
        bandN sys L Hunit * D.Xi * lam⁻¹ * Real.sqrt ρ ∧
      ‖shMask a (physSh cube (gF L) lam ρ)
          (emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) τ (ext eta n (Sm eta L (traj H D t)))))‖ ≤
        2 * sys.maxMass * bandN sys L Hunit * D.Xi * lam ^ (-(3 : ℝ)) * Real.sqrt ρ := by
  have h := band_galerkin sys hL H hKernel Hunit hPeriodic hKg (restart H D t) τ a cube hlam2 hlamg
    hρ hρl
  rw [restart_Xi, restart_u₀] at h
  exact h

end Galerkin

end FSBand
