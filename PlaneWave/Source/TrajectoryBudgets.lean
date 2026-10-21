import PlaneWave.Source.RetainedComparison

/-!
# Flux/source build, block 5: the budgets of the trajectories

Every state of the argument is good, with a budget linear in the data norm
`Ξ = ‖S u₀‖ + ‖H u₀‖ + ‖H v₀‖` (`H u₀ = S v₀`) and with explicit `K`-dependent coefficients:

* the exact trajectory `ψ(t)`: `FGood (c_tr Ξ)` (`traj_good`, from `prop:dyn-boot`);
* the dressed retained part `a(t) = P e^{Σ_b} ψ(t)`: `‖R ψ̃(t)‖ ≤ ρ̃ Ξ`, `‖W (w - P w)‖ ≤ ω̃ Ξ`,
  `‖a(t) - P ψ(t)‖ ≤ δ_a Ξ` and `a(t)` good with `m_a Ξ` (`aT_bounds`, `lem:dressed-tails` and the
  refined perturbation of good states);
* the retained trajectory `χ(s) = e^{-iH's} a(0)` (`chi_good`, `lem:good-stab`);
* the rotated trajectory `χ'(s) = U χ(s)` (`rot_good`, the rotated-datum check
  eq:rotated-datum-check: `‖U χ - χ‖ ≤ ‖Z₂ χ‖ + ‖Σ₃ χ‖`);
* the Galerkin trajectory `ψ_N(t)` and the comparison trajectory `ψ_N^{r₀}(t) = e^{-iH_N t} U a(0)`
  (`psiN_good`, `psiNr_good`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The data -/

/-- **The data of the exact evolution**: the propagator of `exists_coulombFourierPropagator` and a
datum `u₀ ∈ D(H²)`, `H u₀ = S v₀`. -/
structure EvoData (L : ℝ)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) where
  U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
    lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2
  U0 : ∀ x, U 0 x = x
  graph : ∀ t u, ∃ u' : MolecularFourierH2 eta, Sm eta L u' = U t (Sm eta L u) ∧ H u' = U t (H u)
  deriv : ∀ t u, HasDerivAt (fun s => U s (Sm eta L u)) (-(Complex.I • U t (H u))) t
  cont : ∀ x, Continuous fun t => U t x
  u₀ : MolecularFourierH2 eta
  v₀ : MolecularFourierH2 eta
  uv : H u₀ = Sm eta L v₀

namespace EvoData

variable {L : ℝ} {H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}

/-- The data norm `Ξ = ‖S u₀‖ + ‖H u₀‖ + ‖H v₀‖`. -/
noncomputable def Xi (D : EvoData L H) : ℝ := ‖Sm eta L D.u₀‖ + ‖H D.u₀‖ + ‖H D.v₀‖

lemma Xi_nonneg (D : EvoData L H) : 0 ≤ D.Xi := by unfold Xi; positivity

end EvoData

/-! ## The per-unit budgets -/

section Consts

variable (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ)

omit [Fintype ν] in
lemma Kc_eq : Kc L n = gF L * n := rfl

/-- The trajectory budget per unit `Ξ`. -/
noncomputable def cTr : ℝ := Mtraj sys L Hunit 1 1 1 1

/-- `‖R ψ(t)‖ ≤ ρ Ξ`. -/
noncomputable def rhoC : ℝ := eta * cTr sys L Hunit * (gF L * n) ^ (-(5 / 2 : ℝ))

/-- `‖W (1 - P) w(t)‖ ≤ ω Ξ`. -/
noncomputable def omC : ℝ :=
  Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit *
    (gF L * n) ^ (-(3 / 2 : ℝ))

/-- `‖R ψ̃(t)‖ ≤ ρ̃ Ξ`. -/
noncomputable def rhoT : ℝ :=
  rhoC sys L Hunit n + a0c sys L n * cTr sys L Hunit +
    Asig sys L n * (a0c sys L n * cTr sys L Hunit + Asig sys L n * rhoC sys L Hunit n)

/-- `‖W (w - P w)‖ ≤ ω̃ Ξ` for the dressed state. -/
noncomputable def omT : ℝ :=
  omC sys L Hunit n + finiteCoulombPhysicalMassConstant sys L Hunit * (a1c sys L n * cTr sys L Hunit) +
    CZ sys L Hunit n * (a0c sys L n * cTr sys L Hunit + Asig sys L n * rhoC sys L Hunit n)

/-- `‖a(t) - P ψ(t)‖ ≤ δ_a Ξ`. -/
noncomputable def dA : ℝ :=
  Asig sys L n * (rhoC sys L Hunit n + (a0c sys L n * cTr sys L Hunit + Asig sys L n * rhoC sys L Hunit n))

/-- The cube bound `K' = √3 g n`. -/
noncomputable def Kq : ℝ := Real.sqrt 3 * (gF L * n)

omit [Fintype ν] in
/-- The goodness cost of a perturbation of norm `δ` (and `‖(1+A) e‖ ≤ (1 + A_max) δ`). -/
noncomputable def pertF (eta : ℕ) (L : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  δ * (1 + Kq L n) ^ (5 / 2 : ℝ) + (1 + Amax eta L n) * δ * (1 + Kq L n) ^ (1 / 2 : ℝ)

/-- The budget of `a(t)`. -/
noncomputable def mA : ℝ := 2 * cTr sys L Hunit + pertF eta L n (dA sys L Hunit n)

/-- `Θ(P S v₀) ≤ c_v Ξ`. -/
noncomputable def cvT : ℝ := 3 + 2 * relB sys L Hunit

/-- The defect of the retained datum. -/
noncomputable def eps0chi : ℝ :=
  (Amax eta L n + CVN sys L Hunit n) * dA sys L Hunit n +
    alphaD sys L Hunit n * mA sys L Hunit n + omC sys L Hunit n

/-- The budget of `χ(s)`. -/
noncomputable def mChi : ℝ :=
  Mdec sys L Hunit n (Cfl sys L Hunit (CDelta sys L Hunit n) * mA sys L Hunit n)
    (Cfl sys L Hunit (CDelta sys L Hunit n) * cvT sys L Hunit) (eps0chi sys L Hunit n)
    (alphaD sys L Hunit n * (Cfl sys L Hunit (CDelta sys L Hunit n) * mA sys L Hunit n))

/-- `‖U χ(s) - χ(s)‖ ≤ δ_rot Ξ`. -/
noncomputable def dRot (s β : ℝ) : ℝ := (z2uC sys L Hunit n s + β) * mChi sys L Hunit n

/-- The budget of `χ'(s)`. -/
noncomputable def mRot (s β : ℝ) : ℝ := mChi sys L Hunit n + pertF eta L n (dRot sys L Hunit n s β)

/-- The budget of `ψ_N(t)`. -/
noncomputable def mN : ℝ :=
  Mdec sys L Hunit n (Cfl sys L Hunit 0 * (2 * cTr sys L Hunit)) (Cfl sys L Hunit 0 * cvT sys L Hunit)
    (omC sys L Hunit n) 0

/-- `‖U a(0) - a(0)‖ ≤ δ_rot⁰ Ξ`. -/
noncomputable def dRot0 (s β : ℝ) : ℝ := (z2uC sys L Hunit n s + β) * mA sys L Hunit n

/-- `‖U a(0) - P ψ₀‖ ≤ δ_r Ξ`. -/
noncomputable def dR (s β : ℝ) : ℝ := dRot0 sys L Hunit n s β + dA sys L Hunit n

/-- The budget of `ψ_N^{r₀}(t)`. -/
noncomputable def mNr (s β : ℝ) : ℝ :=
  Mdec sys L Hunit n (Cfl sys L Hunit 0 * (mA sys L Hunit n + (1 + Amax eta L n) * dRot0 sys L Hunit n s β))
    (Cfl sys L Hunit 0 * cvT sys L Hunit)
    ((Amax eta L n + CVN sys L Hunit n) * dR sys L Hunit n s β + omC sys L Hunit n) 0

end Consts

/-! ## Elementary facts -/

section Facts

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ}

include hL in
lemma Mtraj_le (Hunit : ℝ) {s0 hu hv sv Ξ : ℝ} (hs0 : s0 ≤ Ξ) (hhu : hu ≤ Ξ) (hhv : hv ≤ Ξ) (hsv : sv ≤ Ξ) :
    Mtraj sys L Hunit s0 hu hv sv ≤ cTr sys L Hunit * Ξ := by
  obtain ⟨c, hct, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ M₂, finiteCoulombPhysicalTailConstant sys L Hunit
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) M₂ = c * M₂ :=
    ⟨CtW sys L Hunit 1, CtW_nonneg sys hL Hunit zero_le_one, fun M₂ => CtW_eq_mul sys Hunit M₂⟩
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hb := relB_nonneg sys L Hunit hC
  have hg := gF_pos hL
  have hm := sys.one_le_maxMass
  unfold cTr Mtraj
  simp only [hc]
  set g3 := (1 + 2 * gF L) ^ 3
  set b := relB sys L Hunit
  set m := sys.maxMass
  have hg3 : 0 ≤ g3 := by positivity
  have k1 : g3 * (s0 + (2 * hu + 2 * b * s0)) ≤ g3 * (Ξ + (2 * Ξ + 2 * b * Ξ)) := by
    apply mul_le_mul_of_nonneg_left _ hg3
    have := mul_le_mul_of_nonneg_left hs0 hb
    linarith
  have k2 : (1 + 2 * m) * (2 * m * (2 * hv + 2 * b * sv) + c * (m * (s0 + 2 * (2 * hu + 2 * b * s0)))) ≤
      (1 + 2 * m) * (2 * m * (2 * Ξ + 2 * b * Ξ) + c * (m * (Ξ + 2 * (2 * Ξ + 2 * b * Ξ)))) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have e1 := mul_le_mul_of_nonneg_left hsv hb
    have e2 := mul_le_mul_of_nonneg_left hs0 hb
    have h4 : 2 * hv + 2 * b * sv ≤ 2 * Ξ + 2 * b * Ξ := by linarith
    have h5 : s0 + 2 * (2 * hu + 2 * b * s0) ≤ Ξ + 2 * (2 * Ξ + 2 * b * Ξ) := by linarith
    have := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℝ) ≤ 2 * m)
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ m)) hct
    linarith
  calc _ ≤ g3 * (Ξ + (2 * Ξ + 2 * b * Ξ)) +
        (1 + 2 * m) * (2 * m * (2 * Ξ + 2 * b * Ξ) + c * (m * (Ξ + 2 * (2 * Ξ + 2 * b * Ξ)))) :=
        add_le_add k1 k2
    _ = _ := by ring

include hL in
lemma cTr_nonneg (Hunit : ℝ) : 0 ≤ cTr sys L Hunit := by
  have := Mtraj_le sys hL Hunit (Ξ := 1) (le_refl (1 : ℝ)) (le_refl (1 : ℝ)) (le_refl (1 : ℝ))
    (le_refl (1 : ℝ))
  have h0 : 0 ≤ Mtraj sys L Hunit 1 1 1 1 := by
    unfold Mtraj
    have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
    have hb := relB_nonneg sys L Hunit hC
    have hct := CtW_nonneg sys hL Hunit (M₂ := sys.maxMass * (1 + 2 * (2 * 1 + 2 * relB sys L Hunit * 1)))
      (by have := sys.one_le_maxMass; positivity)
    have hg := gF_pos hL
    have hm := sys.one_le_maxMass
    positivity
  unfold cTr; exact h0

omit [Fintype ν] in
lemma FGood_mono {M M' : ℝ} {w : MolecularFourierH2 eta} (h : FGood sys L M w) (hMM : M ≤ M') :
    FGood sys L M' w := by
  refine ⟨h.1.trans hMM, fun a l hl => ⟨(h.2 a l hl).1.trans ?_, (h.2 a l hl).2.trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right hMM (Real.rpow_nonneg (by linarith) _)
  · exact mul_le_mul_of_nonneg_right hMM (Real.rpow_nonneg (by linarith) _)

omit [Fintype ν] in
/-- `‖(1+A) v‖ ≤ (1 + A_max) ‖v‖`. -/
lemma wt_one_le_Amax (v : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ ≤ (1 + Amax eta L n) * ‖v‖ := by
  have h := norm_wt_le_Amax sys (L := L) (by norm_num : (0 : ℝ) ≤ 1) v
  rwa [Real.rpow_one] at h

omit [Fintype ν] in
include hL in
/-- **Goodness under a small perturbation** in the form used for every trajectory. -/
lemma isGood_add_small {M δ : ℝ} {u e : En eta n} (hu : IsGood sys L 1 M u) (he : ‖e‖ ≤ δ) :
    IsGood sys L 1 (M + pertF eta L n δ) (u + e) := by
  have h1 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 e‖ ≤ (1 + Amax eta L n) * δ :=
    (wt_one_le_Amax sys e).trans (mul_le_mul_of_nonneg_left he (by linarith [Amax_nonneg eta L n]))
  have h := isGood_perturb' sys hL hu he h1
  unfold pertF Kq
  exact isGood_mono sys h (le_of_eq (by ring))

/-- `Mdec` is homogeneous. -/
lemma Mdec_hom (Hunit c a b e d : ℝ) :
    Mdec sys L Hunit n (a * c) (b * c) (e * c) (d * c) = Mdec sys L Hunit n a b e d * c := by
  unfold Mdec
  rw [CtW_eq_mul sys Hunit (3 * sys.maxMass * (a * c)), CtW_eq_mul sys Hunit (3 * sys.maxMass * a)]
  ring

/-- `H_N v = (A + W_N) v`. -/
lemma HN_apply (v : En eta n) :
    finiteCoulombHamiltonian sys L n v = (Akin sys L n + VN sys L n) v := by
  have h := congrArg (fun T : En eta n →L[ℂ] En eta n => T v) (HN_eq sys (L := L) (n := n))
  simpa only [LinearMap.coe_toContinuousLinearMap'] using h

include hL in
lemma norm_HN_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖finiteCoulombHamiltonian sys L n v‖ ≤ (Amax eta L n + CVN sys L Hunit n) * ‖v‖ := by
  rw [HN_apply, add_apply, add_mul]
  refine (norm_add_le _ _).trans (add_le_add (norm_Akin_le sys v) ?_)
  exact ((VN sys L n).le_opNorm v).trans (mul_le_mul_of_nonneg_right
    (opNorm_VN_le sys hL Hunit hPeriodic) (norm_nonneg _))

end Facts

/-! ## The trajectories -/

section Traj

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel hL in
/-- **The exact trajectory is good**, with the budget `c_tr Ξ`. -/
theorem traj_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (t : ℝ) :
    ∃ w : MolecularFourierH2 eta, Sm eta L w = D.U t (Sm eta L D.u₀) ∧ H w = D.U t (H D.u₀) ∧
      FGood sys L (cTr sys L Hunit * D.Xi) w := by
  obtain ⟨w, h1, h2⟩ := D.graph t D.u₀
  refine ⟨w, h1, h2, ?_⟩
  have hF := traj_fgood (sys := sys) H hKernel Hunit hL hPeriodic D.U D.graph D.u₀ D.v₀ D.uv t w h1 h2
  refine FGood_mono sys hF (Mtraj_le sys hL Hunit ?_ ?_ ?_ ?_)
  · unfold EvoData.Xi; have := norm_nonneg (H D.u₀); have := norm_nonneg (H D.v₀); linarith
  · unfold EvoData.Xi; have := norm_nonneg (Sm eta L D.u₀); have := norm_nonneg (H D.v₀); linarith
  · unfold EvoData.Xi; have := norm_nonneg (Sm eta L D.u₀); have := norm_nonneg (H D.u₀); linarith
  · rw [← D.uv]
    unfold EvoData.Xi; have := norm_nonneg (Sm eta L D.u₀); have := norm_nonneg (H D.v₀); linarith

omit [Fintype ν] in
lemma wt_add_apply (s : ℝ) (x y : En eta n) :
    FSSpectral.wt (sb eta n) (Asym sys L n) s (x + y) =
      FSSpectral.wt (sb eta n) (Asym sys L n) s x + FSSpectral.wt (sb eta n) (Asym sys L n) s y := by
  unfold FSSpectral.wt; exact FSSpectral.fc_add _ _ _ x y

include hKernel in
/-- **The dressed state** at time `t`: the exterior and potential bounds of `lem:dressed-tails`,
`‖a(t) - P ψ(t)‖ ≤ δ_a Ξ`, and `a(t)` good with `m_a Ξ`. -/
theorem aT_bounds (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (D : EvoData L H) (t : ℝ) :
    ‖psiT sys hL hn D.U D.u₀ t - molecularH2Truncate n (psiT sys hL hn D.U D.u₀ t)‖ ≤
        rhoT sys L Hunit n * D.Xi ∧
      (∀ w : MolecularFourierH2 eta, Sm eta L w = psiT sys hL hn D.U D.u₀ t →
        ‖Wp sys L H (w - molecularH2Truncate n w)‖ ≤ omT sys L Hunit n * D.Xi) ∧
      ‖aT sys hL hn D.U D.u₀ t - ext eta n (D.U t (Sm eta L D.u₀))‖ ≤ dA sys L Hunit n * D.Xi ∧
      IsGood sys L 1 (mA sys L Hunit n * D.Xi) (aT sys hL hn D.U D.u₀ t) := by
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D t
  have hΞ := D.Xi_nonneg
  have hR := fgood_R hF hL hKg
  have hW := fgood_W H hKernel Hunit hL hPeriodic hF hKg
  have hρ : ‖Sm eta L w - molecularH2Truncate n (Sm eta L w)‖ ≤ rhoC sys L Hunit n * D.Xi :=
    hR.trans (le_of_eq (by unfold rhoC; ring))
  have hω : ‖Wp sys L H (w - molecularH2Truncate n w)‖ ≤ omC sys L Hunit n * D.Xi :=
    hW.trans (le_of_eq (by unfold omC; ring))
  obtain ⟨-, h2, h3, h4⟩ := dressed_tails sys hL hn H hKernel Hunit hPeriodic w hρ hω hF.1
  have hpsi : psiT sys hL hn D.U D.u₀ t = exp (Sig sys L n hL hn) (Sm eta L w) := by
    unfold psiT; rw [hw1]
  have hdiff : ‖aT sys hL hn D.U D.u₀ t - ext eta n (D.U t (Sm eta L D.u₀))‖ ≤
      dA sys L Hunit n * D.Xi := by
    have e : aT sys hL hn D.U D.u₀ t - ext eta n (D.U t (Sm eta L D.u₀)) =
        ext eta n (molecularH2Truncate n (exp (Sig sys L n hL hn) (Sm eta L w)) -
          molecularH2Truncate n (Sm eta L w)) := by
      unfold aT; rw [hpsi, ← hw1, map_sub, extract_truncate, extract_truncate]
    rw [e]
    exact (norm_ext_le _).trans (h4.trans (le_of_eq (by unfold dA; ring)))
  refine ⟨?_, ?_, hdiff, ?_⟩
  · rw [hpsi]; exact h2.trans (le_of_eq (by unfold rhoT; ring))
  · intro w' hw'
    have : w' = exp (SigG sys hL hn) w :=
      molecularH2StateMap_injective eta (gF L) (by
        change Sm eta L w' = Sm eta L (exp (SigG sys hL hn) w)
        rw [hw', hpsi, exp_SigG_apply])
    rw [this]; exact h3.trans (le_of_eq (by unfold omT; ring))
  · have hP : IsGood sys L 1 (2 * (cTr sys L Hunit * D.Xi)) (ext eta n (Sm eta L w)) := ext_good sys hF
    rw [← hw1] at hdiff
    have h := isGood_add_small sys hL hP hdiff
    rw [add_sub_cancel] at h
    refine isGood_mono sys h (le_of_eq ?_)
    unfold mA pertF; ring

include hKernel hL in
/-- The exact datum is good: `FGood (c_tr Ξ) u₀`. -/
lemma datum_fgood (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) : FGood sys L (cTr sys L Hunit * D.Xi) D.u₀ := by
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D 0
  have : w = D.u₀ := molecularH2StateMap_injective eta (gF L) (by
    change Sm eta L w = Sm eta L D.u₀
    rw [hw1, D.U0])
  rwa [this] at hF

include hKernel hL in
/-- `Θ(P S v₀) ≤ c_v Ξ`. -/
lemma theta_v0_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L D.v₀))‖ ≤
      cvT sys L Hunit * D.Xi := by
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hb := relB_nonneg sys L Hunit hC
  rw [ext_wt_one]
  refine (norm_ext_le _).trans ((norm_add_le _ _).trans ?_)
  have hT := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC D.v₀
  have hv : ‖Sm eta L D.v₀‖ = ‖H D.u₀‖ := by rw [D.uv]
  have hT' : ‖coulombFourierKineticH2 sys (gF L) D.v₀‖ ≤
      2 * ‖H D.v₀‖ + 2 * relB sys L Hunit * ‖Sm eta L D.v₀‖ := hT
  rw [hv] at hT' ⊢
  unfold cvT EvoData.Xi
  have := norm_nonneg (Sm eta L D.u₀)
  have := norm_nonneg (H D.u₀)
  have := norm_nonneg (H D.v₀)
  have : relB sys L Hunit * ‖H D.u₀‖ ≤
      relB sys L Hunit * (‖Sm eta L D.u₀‖ + ‖H D.u₀‖ + ‖H D.v₀‖) :=
    mul_le_mul_of_nonneg_left (by linarith) hb
  nlinarith

include hKernel in
/-- **The retained trajectory is good** (`lem:good-stab` for `H' = H_N + ΔH`). -/
theorem chi_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (D : EvoData L H) (τ : ℝ) :
    IsGood sys L 1 (mChi sys L Hunit n * D.Xi)
      (retFlow sys L n (dH_symm sys hL hn H hKernel) τ (aT sys hL hn D.U D.u₀ 0)) := by
  obtain ⟨-, -, hd, hg⟩ := aT_bounds sys hL hn H hKernel Hunit hPeriodic hKg D 0
  rw [D.U0] at hd
  have hΞ := D.Xi_nonneg
  set r₀ := aT sys hL hn D.U D.u₀ 0 - ext eta n (Sm eta L D.u₀)
  have hχ₀ : ext eta n (Sm eta L D.u₀) + r₀ = aT sys hL hn D.U D.u₀ 0 := by simp only [r₀]; abel
  have hΘ₀ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L D.u₀) + r₀)‖ ≤
      mA sys L Hunit n * D.Xi := by rw [hχ₀]; exact theta_le_good sys hg
  have hΘv := theta_v0_le sys hL H hKernel Hunit hPeriodic (n := n) D
  have hF0 := datum_fgood sys hL H hKernel Hunit hPeriodic D
  have hW0 : ‖Wp sys L H (D.u₀ - molecularH2Truncate n D.u₀)‖ ≤ omC sys L Hunit n * D.Xi :=
    (fgood_W H hKernel Hunit hL hPeriodic hF0 hKg).trans (le_of_eq (by unfold omC; ring))
  have hε₀ : ‖finiteCoulombHamiltonian sys L n r₀ + dH sys hL hn H (ext eta n (Sm eta L D.u₀) + r₀) -
      ext eta n (Wp sys L H (D.u₀ - molecularH2Truncate n D.u₀))‖ ≤ eps0chi sys L Hunit n * D.Xi := by
    rw [hχ₀]
    have k1 := (norm_HN_le sys hL Hunit hPeriodic r₀).trans
      (mul_le_mul_of_nonneg_left hd (by
        have := Amax_nonneg eta L n; have := CVN_nonneg sys Hunit (L := L) (n := n); positivity))
    have k2 := (norm_dH_le_wt sys hL hn H hKernel Hunit hPeriodic (aT sys hL hn D.U D.u₀ 0)).trans
      (mul_le_mul_of_nonneg_left (theta_le_good sys hg) (alphaD_nonneg sys hL Hunit))
    have k3 := (norm_ext_le (n := n) _).trans hW0
    have := norm_sub_le (finiteCoulombHamiltonian sys L n r₀ + dH sys hL hn H (aT sys hL hn D.U D.u₀ 0))
      (ext eta n (Wp sys L H (D.u₀ - molecularH2Truncate n D.u₀)))
    have := norm_add_le (finiteCoulombHamiltonian sys L n r₀) (dH sys hL hn H (aT sys hL hn D.U D.u₀ 0))
    have e : eps0chi sys L Hunit n * D.Xi = (Amax eta L n + CVN sys L Hunit n) * (dA sys L Hunit n * D.Xi) +
        alphaD sys L Hunit n * (mA sys L Hunit n * D.Xi) + omC sys L Hunit n * D.Xi := by
      unfold eps0chi; ring
    rw [e]; linarith
  have h := good_stab' sys H hKernel Hunit hL hPeriodic (dH_symm sys hL hn H hKernel)
    (CDelta_nonneg sys hL Hunit) (norm_dH_le sys hL hn H hKernel Hunit hPeriodic)
    (alphaD_nonneg sys hL Hunit) (norm_dH_le_wt sys hL hn H hKernel Hunit hPeriodic)
    D.u₀ D.v₀ D.uv r₀ hΘ₀ hΘv hε₀ τ
  rw [hχ₀] at h
  refine isGood_mono sys h (le_of_eq ?_)
  rw [show Cfl sys L Hunit (CDelta sys L Hunit n) * (mA sys L Hunit n * D.Xi) =
      (Cfl sys L Hunit (CDelta sys L Hunit n) * mA sys L Hunit n) * D.Xi by ring,
    show Cfl sys L Hunit (CDelta sys L Hunit n) * (cvT sys L Hunit * D.Xi) =
      (Cfl sys L Hunit (CDelta sys L Hunit n) * cvT sys L Hunit) * D.Xi by ring,
    show alphaD sys L Hunit n * ((Cfl sys L Hunit (CDelta sys L Hunit n) * mA sys L Hunit n) * D.Xi) =
      (alphaD sys L Hunit n * (Cfl sys L Hunit (CDelta sys L Hunit n) * mA sys L Hunit n)) * D.Xi by ring,
    Mdec_hom]
  rfl

include hKernel in
/-- **The rotated trajectory is good** (eq:rotated-datum-check). -/
theorem rot_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) {s : ℝ} (hs : 3 / 4 < s) (hs1 : s ≤ 1) (hK1 : 1 ≤ Kc L n / 4)
    (S3 : En eta n →L[ℂ] En eta n) (hS3 : S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n)) {β : ℝ}
    (hβ : ∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u →
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤ β * M)
    (D : EvoData L H) (τ : ℝ) :
    ‖rotT sys hL hn H hKernel S3 (aT sys hL hn D.U D.u₀ 0) τ -
        retFlow sys L n (dH_symm sys hL hn H hKernel) (-τ) (aT sys hL hn D.U D.u₀ 0)‖ ≤
        dRot sys L Hunit n s β * D.Xi ∧
      IsGood sys L 1 (mRot sys L Hunit n s β * D.Xi) (rotT sys hL hn H hKernel S3 (aT sys hL hn D.U D.u₀ 0) τ) := by
  set χ := retFlow sys L n (dH_symm sys hL hn H hKernel) (-τ) (aT sys hL hn D.U D.u₀ 0)
  have hχ := chi_good sys hL hn H hKernel Hunit hPeriodic hKg D (-τ)
  have hZ := (norm_Z2_good sys hL hn H hKernel Hunit hPeriodic hs hs1 hK1 hχ).2
  have hS : ‖S3 χ‖ ≤ β * (mChi sys L Hunit n * D.Xi) := by
    have h1 := hβ _ χ hχ
    have h2 := norm_le_wt sys L n (by norm_num : (0 : ℝ) ≤ 1 / 4) (S3 χ)
    have h3 := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n χ)))
    linarith
  have hd : ‖rotT sys hL hn H hKernel S3 (aT sys hL hn D.U D.u₀ 0) τ - χ‖ ≤ dRot sys L Hunit n s β * D.Xi := by
    refine (norm_Urot_sub_le sys hL hn H hKernel S3 hS3 χ).trans ?_
    have e : dRot sys L Hunit n s β * D.Xi = mChi sys L Hunit n * D.Xi * z2uC sys L Hunit n s +
        β * (mChi sys L Hunit n * D.Xi) := by unfold dRot; ring
    rw [e]; linarith
  refine ⟨hd, ?_⟩
  have h := isGood_add_small sys hL hχ hd
  rw [add_sub_cancel] at h
  refine isGood_mono sys h (le_of_eq ?_)
  unfold mRot pertF; ring

include hKernel hL in
/-- **The Galerkin trajectory is good** (`lem:good-stab` with `ΔH = 0`). -/
theorem psiN_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (D : EvoData L H) (τ : ℝ) :
    IsGood sys L 1 (mN sys L Hunit n * D.Xi)
      (retFlow sys L n (zero_isSymmetric (n := n)) τ (ext eta n (Sm eta L D.u₀))) := by
  have hΞ := D.Xi_nonneg
  have hF0 := datum_fgood sys hL H hKernel Hunit hPeriodic D
  have hg := ext_good sys (n := n) hF0
  have hΘ₀ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L D.u₀) + 0)‖ ≤
      2 * cTr sys L Hunit * D.Xi := by
    rw [add_zero]; exact (theta_le_good sys hg).trans (le_of_eq (by ring))
  have hΘv := theta_v0_le sys hL H hKernel Hunit hPeriodic (n := n) D
  have hW0 : ‖Wp sys L H (D.u₀ - molecularH2Truncate n D.u₀)‖ ≤ omC sys L Hunit n * D.Xi :=
    (fgood_W H hKernel Hunit hL hPeriodic hF0 hKg).trans (le_of_eq (by unfold omC; ring))
  have hε₀ : ‖finiteCoulombHamiltonian sys L n 0 + (0 : En eta n →ₗ[ℂ] En eta n)
      (ext eta n (Sm eta L D.u₀) + 0) - ext eta n (Wp sys L H (D.u₀ - molecularH2Truncate n D.u₀))‖ ≤
      omC sys L Hunit n * D.Xi := by
    simp only [map_zero, LinearMap.zero_apply, zero_add, zero_sub, norm_neg]
    exact (norm_ext_le _).trans hW0
  have h := good_stab' sys H hKernel Hunit hL hPeriodic (zero_isSymmetric (n := n)) le_rfl
    (fun v => by simp) le_rfl (fun v => by simp) D.u₀ D.v₀ D.uv 0 hΘ₀ hΘv hε₀ τ
  rw [add_zero] at h
  refine isGood_mono sys h (le_of_eq ?_)
  rw [show Cfl sys L Hunit 0 * (2 * cTr sys L Hunit * D.Xi) =
      (Cfl sys L Hunit 0 * (2 * cTr sys L Hunit)) * D.Xi by ring,
    show Cfl sys L Hunit 0 * (cvT sys L Hunit * D.Xi) = (Cfl sys L Hunit 0 * cvT sys L Hunit) * D.Xi by ring,
    show (0 : ℝ) * ((Cfl sys L Hunit 0 * (2 * cTr sys L Hunit)) * D.Xi) = 0 * D.Xi by ring,
    Mdec_hom]
  rfl

include hKernel in
/-- **The comparison trajectory `ψ_N^{r₀}` is good**, and `‖U a(0) - P ψ₀‖ ≤ δ_r Ξ`. -/
theorem psiNr_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) {s : ℝ} (hs : 3 / 4 < s) (hs1 : s ≤ 1) (hK1 : 1 ≤ Kc L n / 4)
    (S3 : En eta n →L[ℂ] En eta n) (hS3 : S3 ∈ skewAdjoint (En eta n →L[ℂ] En eta n)) {β : ℝ}
    (hβ : ∀ (M : ℝ) (u : En eta n), IsGood sys L 1 M u →
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n u))‖ +
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (S3 u)‖ ≤ β * M)
    (D : EvoData L H) (τ : ℝ) :
    ‖Urot sys hL hn H S3 (aT sys hL hn D.U D.u₀ 0) - ext eta n (Sm eta L D.u₀)‖ ≤
        dR sys L Hunit n s β * D.Xi ∧
      IsGood sys L 1 (mNr sys L Hunit n s β * D.Xi)
        (retFlow sys L n (zero_isSymmetric (n := n)) τ (Urot sys hL hn H S3 (aT sys hL hn D.U D.u₀ 0))) := by
  have hΞ := D.Xi_nonneg
  obtain ⟨-, -, hd, hg⟩ := aT_bounds sys hL hn H hKernel Hunit hPeriodic hKg D 0
  rw [D.U0] at hd
  set a₀ := aT sys hL hn D.U D.u₀ 0
  have hZ := (norm_Z2_good sys hL hn H hKernel Hunit hPeriodic hs hs1 hK1 hg).2
  have hS : ‖S3 a₀‖ ≤ β * (mA sys L Hunit n * D.Xi) := by
    have h1 := hβ _ a₀ hg
    have h2 := norm_le_wt sys L n (by norm_num : (0 : ℝ) ≤ 1 / 4) (S3 a₀)
    have h3 := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (S3 (VN sys L n a₀)))
    linarith
  have hd0 : ‖Urot sys hL hn H S3 a₀ - a₀‖ ≤ dRot0 sys L Hunit n s β * D.Xi := by
    refine (norm_Urot_sub_le sys hL hn H hKernel S3 hS3 a₀).trans ?_
    have e : dRot0 sys L Hunit n s β * D.Xi = mA sys L Hunit n * D.Xi * z2uC sys L Hunit n s +
        β * (mA sys L Hunit n * D.Xi) := by unfold dRot0; ring
    rw [e]; linarith
  set r₀ := Urot sys hL hn H S3 a₀ - ext eta n (Sm eta L D.u₀)
  have hr : ‖r₀‖ ≤ dR sys L Hunit n s β * D.Xi := by
    have e : r₀ = (Urot sys hL hn H S3 a₀ - a₀) + (a₀ - ext eta n (Sm eta L D.u₀)) := by
      simp only [r₀]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have e2 : dR sys L Hunit n s β * D.Xi = dRot0 sys L Hunit n s β * D.Xi + dA sys L Hunit n * D.Xi := by
      unfold dR; ring
    rw [e2]; exact add_le_add hd0 hd
  refine ⟨hr, ?_⟩
  have hχ₀ : ext eta n (Sm eta L D.u₀) + r₀ = Urot sys hL hn H S3 a₀ := by simp only [r₀]; abel
  have hΘ₀ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L D.u₀) + r₀)‖ ≤
      (mA sys L Hunit n + (1 + Amax eta L n) * dRot0 sys L Hunit n s β) * D.Xi := by
    rw [hχ₀]
    have e : Urot sys hL hn H S3 a₀ = a₀ + (Urot sys hL hn H S3 a₀ - a₀) := by abel
    rw [e, wt_add_apply sys]
    refine (norm_add_le _ _).trans ?_
    have k1 := theta_le_good sys hg
    have k2 := (wt_one_le_Amax sys (Urot sys hL hn H S3 a₀ - a₀)).trans
      (mul_le_mul_of_nonneg_left hd0 (by linarith [Amax_nonneg eta L n]))
    have e2 : (mA sys L Hunit n + (1 + Amax eta L n) * dRot0 sys L Hunit n s β) * D.Xi =
        mA sys L Hunit n * D.Xi + (1 + Amax eta L n) * (dRot0 sys L Hunit n s β * D.Xi) := by ring
    rw [e2]; linarith
  have hΘv := theta_v0_le sys hL H hKernel Hunit hPeriodic (n := n) D
  have hF0 := datum_fgood sys hL H hKernel Hunit hPeriodic D
  have hW0 : ‖Wp sys L H (D.u₀ - molecularH2Truncate n D.u₀)‖ ≤ omC sys L Hunit n * D.Xi :=
    (fgood_W H hKernel Hunit hL hPeriodic hF0 hKg).trans (le_of_eq (by unfold omC; ring))
  have hε₀ : ‖finiteCoulombHamiltonian sys L n r₀ + (0 : En eta n →ₗ[ℂ] En eta n)
      (ext eta n (Sm eta L D.u₀) + r₀) - ext eta n (Wp sys L H (D.u₀ - molecularH2Truncate n D.u₀))‖ ≤
      ((Amax eta L n + CVN sys L Hunit n) * dR sys L Hunit n s β + omC sys L Hunit n) * D.Xi := by
    simp only [LinearMap.zero_apply, add_zero]
    refine (norm_sub_le _ _).trans ?_
    have k1 := (norm_HN_le sys hL Hunit hPeriodic r₀).trans
      (mul_le_mul_of_nonneg_left hr (by
        have := Amax_nonneg eta L n; have := CVN_nonneg sys Hunit (L := L) (n := n); positivity))
    have k2 := (norm_ext_le (n := n) _).trans hW0
    have e : ((Amax eta L n + CVN sys L Hunit n) * dR sys L Hunit n s β + omC sys L Hunit n) * D.Xi =
        (Amax eta L n + CVN sys L Hunit n) * (dR sys L Hunit n s β * D.Xi) + omC sys L Hunit n * D.Xi := by
      ring
    rw [e]; linarith
  have h := good_stab' sys H hKernel Hunit hL hPeriodic (zero_isSymmetric (n := n)) le_rfl
    (fun v => by simp) le_rfl (fun v => by simp) D.u₀ D.v₀ D.uv r₀ hΘ₀ hΘv hε₀ τ
  rw [hχ₀] at h
  refine isGood_mono sys h (le_of_eq ?_)
  rw [show Cfl sys L Hunit 0 * ((mA sys L Hunit n + (1 + Amax eta L n) * dRot0 sys L Hunit n s β) * D.Xi) =
      (Cfl sys L Hunit 0 * (mA sys L Hunit n + (1 + Amax eta L n) * dRot0 sys L Hunit n s β)) * D.Xi by ring,
    show Cfl sys L Hunit 0 * (cvT sys L Hunit * D.Xi) = (Cfl sys L Hunit 0 * cvT sys L Hunit) * D.Xi by ring,
    show (0 : ℝ) * ((Cfl sys L Hunit 0 * (mA sys L Hunit n + (1 + Amax eta L n) * dRot0 sys L Hunit n s β)) *
      D.Xi) = 0 * D.Xi by ring,
    Mdec_hom]
  rfl

end Traj

end FSNormal
