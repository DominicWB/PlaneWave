import PlaneWave.KineticLog.GridConsistency

/-!
# Logarithmic kinetic bound, part 11: the filtered grid comparison

For the filtered datum `p = 1_{H + c ≤ Λ} ψ₀` (`ExactEigen.proj`), the exact evolution projected
on the register, `x(t) = P' U(t) p`, and the grid evolution of its projection,
`y(t) = U_g(t) P' p`, have grid eigen-coordinates (`grid_coord`)

  `⟪e_a, x(t) - y(t)⟫ = i e^{-i E_a t} (Φ c₂)_a + (Y d_t)_a - e^{-i E_a t} (Y d₀)_a`,

where on the low rows `E_a + c + d ≤ 2Λ` the matrix `Φ_ak = φ_t(λ_a - μ_k) A_ak/μ_k²` is the
dyadic Duhamel matrix of the consistency block (`grA`) and on the high rows `Y` is the separated
Sylvester block (`grY`); `c₂ = ((H + c + d)² ψ₀)` and `d₀ = ((H + c + d) ψ₀)` in the exact
eigenbasis, `d_t = e^{-i(ν - c)t} d₀`.

Pairing with a register vector `z` and splitting the rows (`norm_sum_conj_split`) gives the core
estimate (`grid_core_pair`):

  `|⟪x(t) - y(t), z⟫| ≤ 48 δ (t + log(2 + 2Λ)) ‖(H + c + d)² ψ₀‖ ‖z‖
      + 2 ‖Y‖ ‖(H + c + d) ψ₀‖ ‖(G + c + d) z‖/(2Λ)`,

with `δ = δ_raw` (`grid_delta_raw`, `dyadic_duhamel`) and `‖Y‖ ≤ F_raw/(Λ - d)`
(`grid_transfer_raw`).  The second term is the spectral orthogonality of `lem:kinetic-high`: the
separated part lives on grid energies above `2Λ`, so only `(1 - S_g) z` is seen, and
`‖(1 - S_g) z‖ ≤ ‖(G + c + d) z‖/(2Λ)`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Core

variable (sys : CoulombSystem eta ν) {L : ℝ}
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL in
/-- **Grid eigen-coordinates of the filtered difference.** -/
lemma grid_coord {c : ℝ} (E : ExactEigen L H c) {d : ℝ} (hd : 0 ≤ d) (m : ℕ) {κ : Lat3 → ℝ}
    (hκe : ∀ x, κ (-x) = κ x)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t)
    (Λ : ℝ) (s : Finset E.ι) (D : EvoData L H) (t : ℝ) (a : GrIdx eta m) :
    let ε : ℂ := Complex.exp (-(Complex.I * (grE (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a : ℂ) * t))
    let c2 : EuclideanSpace ℂ s :=
      WithLp.toLp 2 (fun k => ⟪E.b k, ExactEigen.Hs2 (c := c + d) D⟫_ℂ)
    let d0 : EuclideanSpace ℂ s := WithLp.toLp 2 (fun k => ⟪E.b k, Hs1 (c + d) D⟫_ℂ)
    let dt : EuclideanSpace ℂ s := WithLp.toLp 2
      (fun k => Complex.exp (-(Complex.I * ((E.nu k - c : ℝ) : ℂ) * t)) * d0 k)
    ⟪grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a,
        regCoeff m (D.U t (E.proj s (Sm eta L D.u₀))) -
          Ug t (regCoeff m (E.proj s (Sm eta L D.u₀)))⟫_ℂ =
      Complex.I * ε * mop (fun a (k : s) =>
          phiT t (grLam sys L m hκe (c + d) Λ a - (E.nu k + d)) *
            (grA sys L H m hκe E d Λ s a k / ((E.nu k + d : ℝ) : ℂ) ^ 2)) c2 a +
        mop (grY sys L H m hκe E d Λ s) dt a - ε * mop (grY sys L H m hκe E d Λ s) d0 a := by
  intro ε c2 d0 dt
  classical
  set e := grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe
    with he
  set Ea := grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a
    with hEa
  set β : s → ℂ := fun k => ⟪E.b k, Sm eta L D.u₀⟫_ℂ with hβ
  set X : s → ℂ := fun k => ⟪e a, regCoeff m (E.b k)⟫_ℂ with hX
  set ph : s → ℂ := fun k => Complex.exp (-(Complex.I * ((E.nu k - c : ℝ) : ℂ) * t)) with hph
  -- the two evolutions
  have hUp : ⟪e a, regCoeff m (D.U t (E.proj s (Sm eta L D.u₀)))⟫_ℂ =
      ∑ k : s, β k * ph k * X k := by
    unfold ExactEigen.proj
    rw [map_sum, map_sum, inner_sum, ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearIsometryEquiv.map_smul, E.evo_b D k t, smul_smul, map_smul, inner_smul_right]
  have hp : ⟪e a, regCoeff m (E.proj s (Sm eta L D.u₀))⟫_ℂ = ∑ k : s, β k * X k := by
    unfold ExactEigen.proj
    rw [map_sum, inner_sum, ← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, inner_smul_right]
  have hflow := inner_grB_flow (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (2 * Real.pi / L) hκe Ug hg0 hgderiv a t (regCoeff m (E.proj s (Sm eta L D.u₀)))
  rw [inner_sub_right, hUp, hflow, hp]
  -- the datum coordinates
  have hc2 : ∀ k : s, c2 k = ((E.nu k + d : ℝ) : ℂ) ^ 2 * β k := fun k => by
    change ⟪E.b k, ExactEigen.Hs2 (c := c + d) D⟫_ℂ = _
    exact (E.shift d hd).inner_b_Hs2 sys hKernel D k.1
  have hd0 : ∀ k : s, d0 k = ((E.nu k + d : ℝ) : ℂ) * β k := fun k => by
    change ⟪E.b k, H D.u₀ + ((c + d : ℝ) : ℂ) • Sm eta L D.u₀⟫_ℂ = _
    exact (E.shift d hd).inner_b_Hs sys hKernel k.1 D.u₀
  by_cases ha : Ea + (c + d) ≤ 2 * Λ
  · -- low row: the separated block vanishes
    have hY0 : ∀ v : EuclideanSpace ℂ s, mop (grY sys L H m hκe E d Λ s) v a = 0 := fun v => by
      rw [mop_apply]
      exact Finset.sum_eq_zero fun k _ => by simp [grY, ← hEa, ha]
    rw [hY0, hY0, mul_zero, add_zero, sub_zero, mop_apply, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hlam : grLam sys L m hκe (c + d) Λ a = Ea + (c + d) := min_eq_left ha
    have hA : grA sys L H m hκe E d Λ s a k = ((Ea + c - E.nu k : ℝ) : ℂ) * X k := by
      simp only [grA, ← hEa, if_pos ha]
      exact (grid_cons sys L H hKernel hL m hκe E a k).symm
    rw [hlam, hA, hc2 k]
    have hω : Ea + (c + d) - (E.nu k + d) = Ea + c - E.nu k := by ring
    rw [hω]
    have hn0 : ((E.nu k + d : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by linarith [E.nu_pos k])
    have hφ := phiT_mul_self t (Ea + c - E.nu k)
    have hexp : ε * Complex.exp (Complex.I * ((Ea + c - E.nu k : ℝ) : ℂ) * t) = ph k := by
      simp only [ε, hph, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have key : Complex.I * ε * (phiT t (Ea + c - E.nu k) *
        (((Ea + c - E.nu k : ℝ) : ℂ) * X k / ((E.nu k + d : ℝ) : ℂ) ^ 2) *
          (((E.nu k + d : ℝ) : ℂ) ^ 2 * β k)) =
        Complex.I * ε * (phiT t (Ea + c - E.nu k) * ((Ea + c - E.nu k : ℝ) : ℂ)) * X k * β k := by
      field_simp
    rw [key, hφ]
    have hI : Complex.I * ε * (-Complex.I * (Complex.exp (Complex.I *
        ((Ea + c - E.nu k : ℝ) : ℂ) * t) - 1)) * X k * β k =
        (ε * Complex.exp (Complex.I * ((Ea + c - E.nu k : ℝ) : ℂ) * t) - ε) * X k * β k := by
      have hII : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
      linear_combination (ε * (Complex.exp (Complex.I * ((Ea + c - E.nu k : ℝ) : ℂ) * t) - 1) *
        X k * β k) * hII
    rw [hI, hexp]
    ring
  · -- high row: the low block vanishes
    have hA0 : mop (fun a (k : s) => phiT t (grLam sys L m hκe (c + d) Λ a - (E.nu k + d)) *
        (grA sys L H m hκe E d Λ s a k / ((E.nu k + d : ℝ) : ℂ) ^ 2)) c2 a = 0 := by
      rw [mop_apply]
      exact Finset.sum_eq_zero fun k _ => by simp [grA, ← hEa, ha]
    rw [hA0, mul_zero, zero_add, mop_apply, mop_apply]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hn0 : ((E.nu k + d : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by linarith [E.nu_pos k])
    simp only [grY, ← hEa, if_neg ha]
    change β k * ph k * X k - ε * (β k * X k) =
      X k / ((E.nu k + d : ℝ) : ℂ) * (ph k * d0 k) -
        ε * (X k / ((E.nu k + d : ℝ) : ℂ) * d0 k)
    rw [hd0 k]
    field_simp

include hKernel hL hPeriodic in
/-- **The core grid comparison** (`lem:kinetic-dyadic` + `lem:kinetic-leakage` + spectral
orthogonality): for the filtered datum `p = 1_{H + c ≤ Λ} ψ₀`, every register vector `z` and
every `t ≥ 0`,
`|⟪P' U(t) p - U_g(t) P' p, z⟫| ≤ 48 δ_raw (t + log(2 + 2Λ)) ‖(H + c + d)² ψ₀‖ ‖z‖
  + 2 (F_raw/(Λ - d)) ‖(H + c + d) ψ₀‖ (‖G z‖ + (c + d) ‖z‖)/(2Λ)`. -/
theorem grid_core_pair {c : ℝ} (E : ExactEigen L H c) (hcdef : c = shiftC sys L Hunit)
    {d : ℝ} (hd : 0 ≤ d) (m : ℕ) (hm : 8 ≤ m) {κ : Lat3 → ℝ}
    (hκ : IsGridKernel (coulombCellAmplitude L) m κ)
    (Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m))
    (hg0 : ∀ x, Ug 0 x = x)
    (hgderiv : ∀ t x, HasDerivAt (fun s => Ug s x)
      (-(Complex.I • Ug t (Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) x))) t)
    (hc1 : ∀ a : GrIdx eta m, 1 ≤ grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) hκ.even a + (c + d))
    {Λ : ℝ} (hΛ1 : 1 ≤ Λ) (hdΛ : d < Λ)
    (hKs1 : 1 ≤ gF L * (m / 4 : ℕ)) (hKs2 : 2 * gF L ≤ gF L * (m / 4 : ℕ))
    (hK1 : 1 ≤ gF L * (2 * m : ℕ)) (hK2 : 2 * gF L ≤ gF L * (2 * m : ℕ))
    (hΛs : Λ + c ≤ (gF L * (m / 4 : ℕ)) ^ 2 / (4 * sys.maxMass))
    (hΛ2 : Λ + c ≤ (gF L * (2 * m : ℕ)) ^ 2 / (4 * sys.maxMass))
    (hΛg : 4 * (regParticlesOf sys).maxMass * (2 * Λ + cGr (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) (2 * Real.pi / L)) ≤
        (2 * Real.pi / L) ^ 2 * (((m / 4 : ℕ) : ℝ) + 1) ^ 2)
    (D : EvoData L H) {t : ℝ} (ht : 0 ≤ t) (z : EuclideanSpace ℂ (RCfg eta m)) :
    ‖⟪regCoeff m (D.U t (E.proj (E.finite Λ).toFinset (Sm eta L D.u₀))) -
        Ug t (regCoeff m (E.proj (E.finite Λ).toFinset (Sm eta L D.u₀))), z⟫_ℂ‖ ≤
      48 * dRawG sys L Hunit (c + d) m * (t + Real.log (2 + 2 * Λ)) *
          ‖ExactEigen.Hs2 (c := c + d) D‖ * ‖z‖ +
        2 * (fRawG sys L Hunit m / (Λ - d)) * ‖Hs1 (c + d) D‖ *
          ((‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
            (2 * Real.pi / L) z‖ + (c + d) * ‖z‖) / (2 * Λ)) := by
  classical
  set s := (E.finite Λ).toFinset with hsdef
  have hs : ∀ k ∈ s, E.nu k ≤ Λ := fun k hk => by simpa [hsdef] using hk
  have hc : 2 ≤ c := hcdef ▸ two_le_shiftC sys L Hunit
  have hcd : 0 ≤ c + d := by linarith
  set e := grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκ.even
    with he
  set lam : GrIdx eta m → ℝ := fun a => grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (2 * Real.pi / L) hκ.even a + (c + d) with hlamdef
  set ε : GrIdx eta m → ℂ := fun a => Complex.exp (-(Complex.I * (grE (regParticlesOf sys)
    (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκ.even a : ℂ) * t)) with hεdef
  set c2 : EuclideanSpace ℂ s := WithLp.toLp 2 (fun k => ⟪E.b k, ExactEigen.Hs2 (c := c + d) D⟫_ℂ)
    with hc2
  set d0 : EuclideanSpace ℂ s := WithLp.toLp 2 (fun k => ⟪E.b k, Hs1 (c + d) D⟫_ℂ) with hd0
  set dt : EuclideanSpace ℂ s := WithLp.toLp 2
    (fun k => Complex.exp (-(Complex.I * ((E.nu k - c : ℝ) : ℂ) * t)) * d0 k) with hdt
  set Φ := fun a (k : s) => phiT t (grLam sys L m hκ.even (c + d) Λ a - (E.nu k + d)) *
    (grA sys L H m hκ.even E d Λ s a k / ((E.nu k + d : ℝ) : ℂ) ^ 2) with hΦ
  set Y := grY sys L H m hκ.even E d Λ s with hY
  set Xl : EuclideanSpace ℂ (GrIdx eta m) := WithLp.toLp 2
    (fun a => Complex.I * ε a * mop Φ c2 a) with hXl
  set Xh : EuclideanSpace ℂ (GrIdx eta m) := WithLp.toLp 2
    (fun a => mop Y dt a - ε a * mop Y d0 a) with hXh
  set x := regCoeff m (D.U t (E.proj s (Sm eta L D.u₀))) -
    Ug t (regCoeff m (E.proj s (Sm eta L D.u₀))) with hx
  have hcoord : ∀ a, ⟪e a, x⟫_ℂ = Xl a + Xh a := fun a => by
    have h := grid_coord sys H hKernel hL E hd m hκ.even Ug hg0 hgderiv Λ s D t a
    simp only at h
    rw [h]
    simp only [hXl, hXh, eucl_toLp_apply]
    ring
  have hXh0 : ∀ a, lam a ≤ 2 * Λ → Xh a = 0 := by
    intro a ha
    have hY0 : ∀ v : EuclideanSpace ℂ s, mop Y v a = 0 := fun v => by
      rw [mop_apply]
      exact Finset.sum_eq_zero fun k _ => by
        simp only [hY, grY]
        rw [if_pos ha, zero_mul]
    simp only [hXh, eucl_toLp_apply, hY0, mul_zero, sub_zero]
  -- the pairing in coordinates
  set Z := e.repr z with hZ
  have hinner : ⟪x, z⟫_ℂ = ∑ a, conj (Xl a + Xh a) * Z a := by
    rw [← e.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcoord a, inner_conj_symm, hZ, OrthonormalBasis.repr_apply_apply]
  have hsplit := norm_sum_conj_split lam (M := 2 * Λ) (by linarith) Xl Xh Z hXh0
  rw [← hinner] at hsplit
  -- the norms
  have hZn : ‖Z‖ = ‖z‖ := e.repr.norm_map z
  have hlamZ : ‖(WithLp.toLp 2 (fun a => (lam a : ℂ) * Z a) : EuclideanSpace ℂ (GrIdx eta m))‖ =
      ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ (2 * Real.pi / L) z +
        ((c + d : ℝ) : ℂ) • z‖ := by
    rw [← e.repr.norm_map]
    congr 1
    ext a
    rw [OrthonormalBasis.repr_apply_apply, inner_add_right, inner_smul_right, he,
      inner_grB_Hgrid, eucl_toLp_apply, hZ, OrthonormalBasis.repr_apply_apply, hlamdef]
    push_cast
    ring
  have hGz : ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) z + ((c + d : ℝ) : ℂ) • z‖ ≤
      ‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) z‖ + (c + d) * ‖z‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hcd]
  have hunit : ∀ a, ‖ε a‖ = 1 := fun a => by
    rw [hεdef, Complex.norm_exp]
    simp
  have hXln : ‖Xl‖ = ‖mop Φ c2‖ := norm_diag_unit _ (fun a => by
    rw [norm_mul, Complex.norm_I, one_mul, hunit a]) _
  have hdtn : ‖dt‖ = ‖d0‖ := norm_diag_unit _ (fun k => by
    rw [Complex.norm_exp]
    simp) _
  have hXhn : ‖Xh‖ ≤ 2 * ‖mop Y‖ * ‖d0‖ := by
    have h1 : ‖Xh‖ ≤ ‖mop Y dt‖ + ‖(WithLp.toLp 2 (fun a => ε a * mop Y d0 a) :
        EuclideanSpace ℂ (GrIdx eta m))‖ := by
      have e1 : Xh = mop Y dt - (WithLp.toLp 2 (fun a => ε a * mop Y d0 a) :
          EuclideanSpace ℂ (GrIdx eta m)) := by
        ext a
        simp [hXh]
      rw [e1]
      exact norm_sub_le _ _
    have h2 : ‖(WithLp.toLp 2 (fun a => ε a * mop Y d0 a) : EuclideanSpace ℂ (GrIdx eta m))‖ =
        ‖mop Y d0‖ := norm_diag_unit _ hunit _
    rw [h2] at h1
    refine h1.trans ?_
    have h3 := norm_mop_apply_le Y dt
    have h4 := norm_mop_apply_le Y d0
    rw [hdtn] at h3
    linarith
  -- the dyadic estimate on the low rows
  have hδ := grid_delta_raw sys H hKernel Hunit hL hPeriodic E hcdef hd m hm hκ hc1 hΛ1 hKs1 hKs2
    hK1 hK2 hΛs hΛ2 hΛg s hs
  have hlamC : ∀ a, 1 ≤ grLam sys L m hκ.even (c + d) Λ a ∧
      grLam sys L m hκ.even (c + d) Λ a ≤ 2 * Λ := fun a =>
    ⟨le_min (hc1 a) (by linarith), min_le_right _ _⟩
  have hdy := dyadic_duhamel (grLam sys L m hκ.even (c + d) Λ) (fun k : s => E.nu k + d)
    (grA sys L H m hκ.even E d Λ s) (M := 2 * Λ) (δ := dRawG sys L Hunit (c + d) m)
    (by linarith) (dRawG_nonneg (sys := sys) (Hunit := Hunit) hL hcd m) hlamC
    (fun k => ⟨by linarith [E.one_le k], by linarith [hs k k.2]⟩) hδ ht c2
  -- the separated transfer on the high rows
  have hYn := grid_transfer_raw sys H hKernel Hunit hL hPeriodic E hcdef hd m hm hκ hΛ1 hdΛ hKs1
    hKs2 hK1 hK2 hΛs hΛ2 s hs
  have hc2n : ‖c2‖ ≤ ‖ExactEigen.Hs2 (c := c + d) D‖ := norm_coords_le E s _
  have hd0n : ‖d0‖ ≤ ‖Hs1 (c + d) D‖ := norm_coords_le E s _
  have hlog : 0 ≤ t + Real.log (2 + 2 * Λ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 2 * Λ by linarith)
    linarith
  have hδ0 := dRawG_nonneg (sys := sys) (Hunit := Hunit) hL hcd m
  have hF0 : 0 ≤ fRawG sys L Hunit m / (Λ - d) :=
    div_nonneg (fRawG_nonneg (sys := sys) (Hunit := Hunit) hL m) (by linarith)
  refine hsplit.trans ?_
  rw [hXln, hZn, hlamZ]
  have hΛ2pos : 0 < 2 * Λ := by linarith
  have t1 : ‖mop Φ c2‖ * ‖z‖ ≤ 48 * dRawG sys L Hunit (c + d) m * (t + Real.log (2 + 2 * Λ)) *
      ‖ExactEigen.Hs2 (c := c + d) D‖ * ‖z‖ := by
    refine mul_le_mul_of_nonneg_right (hdy.trans ?_) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left hc2n (by positivity)
  have t2 : ‖Xh‖ * (‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) z + ((c + d : ℝ) : ℂ) • z‖ / (2 * Λ)) ≤
      2 * (fRawG sys L Hunit m / (Λ - d)) * ‖Hs1 (c + d) D‖ *
        ((‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
          (2 * Real.pi / L) z‖ + (c + d) * ‖z‖) / (2 * Λ)) := by
    have h1 : ‖Xh‖ ≤ 2 * (fRawG sys L Hunit m / (Λ - d)) * ‖Hs1 (c + d) D‖ := by
      refine hXhn.trans ?_
      have := mul_le_mul hYn hd0n (norm_nonneg _) hF0
      nlinarith
    exact mul_le_mul h1 (div_le_div_of_nonneg_right hGz hΛ2pos.le) (by positivity)
      (by positivity)
  linarith

end Core

end KineticLog
