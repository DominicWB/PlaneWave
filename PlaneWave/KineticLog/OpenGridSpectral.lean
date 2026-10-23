import PlaneWave.KineticLog.OpenExact

/-!
# Logarithmic kinetic bound, part 18: grid spectral data of the isolated cell, uniform in `L`

The grid side of `lem:kinetic-low` for the range-cut cell, in the physical weight
`w_g = 1 + g² Σ_b |n_b|²/m_b` (`FreeBoundary.wPhys`) and with constants that do not depend on the
cell side `L ≥ 2π`.  The grid Hamiltonian `G` of a kernel with `|κ| ≤ γ_L coul`,
`γ_L = (1 + V_θ)/(πL)`, is the register Hamiltonian `gridRegHamU` of kinetic scale `1/2` and
`L`-free constant `A = gLAU` (`PlaneWave.FreeBoundary.GridDynamicsUniform`):

* **`grE_lower_U`**: `E_a ≥ -c_g^U`, `c_g^U = 2A + 1/4`, for every kernel of the class;
* **`norm_wPhys_grVL_le`**: the low inverse-weighted grid states have `‖w_g v‖ ≤ c_W^U ‖f‖`,
  `c_W^U = (4/3)(1 + 2(1 + c + A))`;
* **`grid_low_tail_U`** (`lem:kinetic-low`, grid side, uniform in `L`): if
  `4 m̄ (2Λ + c_g^U) ≤ (g(T+1))²` and `g T ≥ 1`, then
  `‖1_{High T r} (G + c)⁻¹ 1_{G + c ≤ 2Λ} f‖ ≤ C_gt^U / ((g(T+1))² √(gT)) ‖f‖`, with
  `C_gt^U = 4 m̄ z (52 + √6162) c_W^U` and the `L`-free coupling `z = gLzU` (`m̄ Z_c = z g`).
  The collocated potential has the physical shells of `vGridK_tailP`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The shell arithmetic in physical units -/

/-- With `J = ⌊T/2⌋`: `26 J/((T - J) + 1)² ≤ 52/T` and, for `0 < g ≤ 1`,
`√(26 (1 + 78/g³)/J) ≤ √6162/(g √(g T))`. -/
lemma shell_arith_U (T : ℕ) (hT : 2 ≤ T) {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) :
    26 * ((T / 2 : ℕ) : ℝ) / (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2 ≤ 52 / T ∧
      Real.sqrt (26 * PlaneWaveGridG.sobP g / ((T / 2 : ℕ) : ℝ)) ≤
        Real.sqrt 6162 / (g * Real.sqrt (g * T)) := by
  set J := T / 2 with hJ
  have hJ1 : 1 ≤ J := by omega
  have h2J : 2 * J ≤ T := by omega
  have h3J : T ≤ 3 * J := by omega
  have hJT : J ≤ T := by omega
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have h2Jr : 2 * (J : ℝ) ≤ T := by exact_mod_cast h2J
  have h3Jr : (T : ℝ) ≤ 3 * J := by exact_mod_cast h3J
  have hX : ((T - J : ℕ) : ℝ) = T - J := by rw [Nat.cast_sub hJT]
  constructor
  · rw [hX, div_le_div_iff₀ (by nlinarith) (by linarith)]
    have h1 : (T : ℝ) / 2 ≤ T - J + 1 := by linarith
    have h2 : ((T : ℝ) / 2) ^ 2 ≤ (T - J + 1) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    have h3 : 26 * (J : ℝ) * T ≤ 13 * T * T := by nlinarith
    nlinarith
  · have hg3 : 0 < g ^ 3 := by positivity
    have hsob : PlaneWaveGridG.sobP g ≤ 79 / g ^ 3 := by
      unfold PlaneWaveGridG.sobP
      have : g ^ 3 ≤ 1 := pow_le_one₀ hg.le hg1
      rw [le_div_iff₀ hg3]
      have e : (1 + 78 / g ^ 3) * g ^ 3 = g ^ 3 + 78 := by field_simp
      rw [e]
      linarith
    have hgT : 0 < g * T := by positivity
    have hsq3 : Real.sqrt (g ^ 3 * T) = g * Real.sqrt (g * T) := by
      rw [show g ^ 3 * (T : ℝ) = g ^ 2 * (g * T) by ring, Real.sqrt_mul (sq_nonneg g),
        Real.sqrt_sq hg.le]
    have e : Real.sqrt 6162 / (g * Real.sqrt (g * T)) = Real.sqrt (6162 / (g ^ 3 * T)) := by
      rw [Real.sqrt_div' 6162 (by positivity), hsq3]
    rw [e]
    refine Real.sqrt_le_sqrt ?_
    have hS0 : 0 ≤ PlaneWaveGridG.sobP g := (PlaneWaveGridG.sobP_pos hg).le
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    have h1 : 26 * PlaneWaveGridG.sobP g * (g ^ 3 * T) ≤ 26 * 79 * T := by
      have := mul_le_mul_of_nonneg_right hsob (by positivity : (0 : ℝ) ≤ g ^ 3 * T)
      have e2 : 79 / g ^ 3 * (g ^ 3 * T) = 79 * T := by field_simp
      nlinarith
    nlinarith

/-! ## The grid spectrum and the low grid states, uniform in `L` -/

section GridU

variable (sys : CoulombSystem eta ν) {L V : ℝ} (hL : 2 * Real.pi ≤ L) (hV : 0 ≤ V) {m : ℕ}
  {κ : Lat3 → ℝ} (hκe : ∀ x, κ (-x) = κ x)
  (hκb : ∀ x, |κ x| ≤ PlaneWaveGridG.gLgamma L V * coul x)

/-- The `L`-free lower bound `c_g^U = 2A + 1/4` of `-G` (`A = gLAU`). -/
noncomputable def cGrU (sys : CoulombSystem eta ν) (V : ℝ) : ℝ :=
  2 * PlaneWaveGridG.gLAU sys V + 1 / 4

lemma cGrU_nonneg (hV : 0 ≤ V) : 0 ≤ cGrU sys V := by
  unfold cGrU PlaneWaveGridG.gLAU
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  positivity

include hL hV hκb in
/-- **The uniform lower bound of the grid spectrum** (`L ≥ 2π`): `E_a ≥ -c_g^U`. -/
lemma grE_lower_U (a : GrIdx eta m) :
    -cGrU sys V ≤ grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) hκe a := by
  have h := (FreeBoundary.gridRegHamU sys hL hV hκb).eigen_lower
    (grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a)
    ((grB (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
      hκe).orthonormal.1 a)
    (grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a)
    (grB_eigen (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe a)
  rw [FreeBoundary.gridRegHamU_A, FreeBoundary.gridRegHamU_c] at h
  unfold cGrU
  linarith

/-- The weight constant of the low grid states, `c_W^U = (4/3)(1 + 2(1 + c + A))`. -/
noncomputable def cWvU (sys : CoulombSystem eta ν) (V c : ℝ) : ℝ :=
  4 / 3 * (1 + 2 * (1 + c + PlaneWaveGridG.gLAU sys V))

lemma cWvU_nonneg (hV : 0 ≤ V) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ cWvU sys V c := by
  unfold cWvU PlaneWaveGridG.gLAU
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  positivity

include hL hV hκb in
/-- **The physical weight of the low grid states**: `‖w_g v‖ ≤ c_W^U ‖f‖`. -/
lemma norm_wPhys_grVL_le {c : ℝ} (Λ : ℝ) (hc : 0 ≤ c)
    (hc1 : ∀ a : GrIdx eta m, 1 ≤ grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) hκe a + c)
    (f : EuclideanSpace ℂ (GrIdx eta m)) :
    ‖wMul (FreeBoundary.wPhys (regParticlesOf sys) (2 * Real.pi / L))
        (grVL (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            (2 * Real.pi / L) hκe c Λ f)‖ ≤
      cWvU sys V c * ‖f‖ := by
  set v := grVL (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L) hκe c Λ f
  have h := (FreeBoundary.gridRegHamU sys hL hV hκb).elliptic_gen v
  rw [FreeBoundary.gridRegHamU_wMul, FreeBoundary.gridRegHamU_op, FreeBoundary.gridRegHamU_c,
    FreeBoundary.gridRegHamU_A] at h
  have h1 := norm_grVL_apply_le (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (2 * Real.pi / L) hκe c Λ hc1 f
  have h2 := norm_Hgrid_grVL_le (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
    (2 * Real.pi / L) hκe Λ hc hc1 f
  have hA : 0 ≤ PlaneWaveGridG.gLAU sys V := by
    unfold PlaneWaveGridG.gLAU
    have := PlaneWaveGridG.gLzU_nonneg sys hV
    positivity
  have hAv : PlaneWaveGridG.gLAU sys V * ‖v‖ ≤ PlaneWaveGridG.gLAU sys V * ‖f‖ :=
    mul_le_mul_of_nonneg_left h1 hA
  have e : (‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
      (2 * Real.pi / L) v‖ + PlaneWaveGridG.gLAU sys V * ‖v‖) / (1 / 2) =
      2 * (‖Hgrid eta m (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData κ
        (2 * Real.pi / L) v‖ + PlaneWaveGridG.gLAU sys V * ‖v‖) := by ring
  rw [e] at h
  unfold cWvU
  have e2 : 4 / 3 * (1 + 2 * (1 + c + PlaneWaveGridG.gLAU sys V)) * ‖f‖ =
      4 / 3 * (‖f‖ + 2 * ((1 + c) * ‖f‖ + PlaneWaveGridG.gLAU sys V * ‖f‖)) := by ring
  rw [e2]
  linarith

/-- The absorption constant of the low grid states, `C_gt^U = 4 m̄ z (52 + √6162) c_W^U`. -/
noncomputable def cGtU (sys : CoulombSystem eta ν) (V c : ℝ) : ℝ :=
  4 * sys.maxMass * (PlaneWaveGridG.gLzU sys V * (52 + Real.sqrt 6162) * cWvU sys V c)

lemma cGtU_nonneg (hV : 0 ≤ V) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ cGtU sys V c := by
  unfold cGtU
  have := PlaneWaveGridG.gLzU_nonneg sys hV
  have := cWvU_nonneg sys hV hc
  have := sys.maxMass_pos
  positivity

set_option maxHeartbeats 1000000 in
include hL hV hκb in
/-- **Absorption of the momentum tails of low grid states, uniform in `L ≥ 2π`**
(`lem:kinetic-low`, grid side): if `g T ≥ 1` and `4 m̄ (2Λ + c_g^U) ≤ (g (T+1))²`, then
`‖1_{High T r} (G + c)⁻¹ 1_{G + c ≤ 2Λ} f‖ ≤ C_gt^U / ((g (T+1))² √(g T)) ‖f‖`. -/
theorem grid_low_tail_U {c Λ : ℝ} (hc : 0 ≤ c) (hΛ0 : 0 ≤ Λ)
    (hc1 : ∀ a : GrIdx eta m, 1 ≤ grE (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
      (2 * Real.pi / L) hκe a + c)
    (T : ℕ) (hT : 2 ≤ T) (hTm : T ≤ 2 * m) (r : Fin eta) (hgT : 1 ≤ 2 * Real.pi / L * T)
    (hΛ : 4 * sys.maxMass * (2 * Λ + cGrU sys V) ≤ (2 * Real.pi / L * ((T : ℝ) + 1)) ^ 2)
    (f : EuclideanSpace ℂ (GrIdx eta m)) :
    ‖maskOp (High T r)
        (grVL (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
            (2 * Real.pi / L) hκe c Λ f)‖ ≤
      cGtU sys V c / ((2 * Real.pi / L * ((T : ℝ) + 1)) ^ 2 *
        Real.sqrt (2 * Real.pi / L * T)) * ‖f‖ := by
  classical
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  set g := 2 * Real.pi / L with hgdef
  have hg : 0 < g := by positivity
  have hg1 : g ≤ 1 := PlaneWaveGridG.g_le_one hL
  set P := regParticlesOf sys with hPdef
  set Dn := (posNucleiOf sys.nuclei).toNucData with hDn
  have hM := P.maxMass_pos
  have hMeq : P.maxMass = sys.maxMass := rfl
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hgT0 : 0 < g * T := by positivity
  have hsT : 0 < Real.sqrt (g * T) := Real.sqrt_pos.mpr hgT0
  have hsT1 : 1 ≤ Real.sqrt (g * T) := Real.one_le_sqrt.mpr hgT
  have hgTT : 0 < (g * ((T : ℝ) + 1)) ^ 2 := by positivity
  have hcG := cGrU_nonneg sys hV
  set z := PlaneWaveGridG.gLzU sys V with hz
  have hz0 : 0 ≤ z := PlaneWaveGridG.gLzU_nonneg sys hV
  set Zc' := PlaneWaveGridG.Zc (PlaneWaveGridG.regParticlesOfG sys)
    (PlaneWaveGridG.posNucleiOfG sys.nuclei).toNucData (PlaneWaveGridG.gLgamma L V) with hZc'
  have hZc0 : 0 ≤ Zc' := PlaneWaveGridG.Zc_nonneg (PlaneWaveGridG.gLgamma_pos hL0 hV).le
  have hZz : sys.maxMass * Zc' = z * g := PlaneWaveGridG.gLGridCoupling_eq sys hL0 V
  set A := 2 * sys.maxMass / (g * ((T : ℝ) + 1)) ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have hAΛ : A * (2 * Λ + cGrU sys V) ≤ 1 / 2 := by
    rw [hA, div_mul_eq_mul_div, div_le_iff₀ hgTT]
    linarith
  set tailG : EuclideanSpace ℂ (GrIdx eta m) →L[ℂ] EuclideanSpace ℂ (RCfg eta m) :=
    (LinearMap.toContinuousLinearMap (maskOp (High T r))) ∘L grVL P Dn g hκe c Λ with htailG
  have htail : ∀ f, tailG f = maskOp (High T r) (grVL P Dn g hκe c Λ f) := fun f => rfl
  set N := ‖tailG‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  set Vt := z * (52 + Real.sqrt 6162) * cWvU sys V c with hVt
  have hVt0 : 0 ≤ Vt := by
    have := cWvU_nonneg sys hV hc
    positivity
  -- the potential part
  have hV' : ∀ f, ‖maskOp (High T r) (kOp (vGridK eta m P Dn κ) (grVL P Dn g hκe c Λ f))‖ ≤
      Vt / Real.sqrt (g * T) * ‖f‖ := by
    intro f
    set v := grVL P Dn g hκe c Λ f with hv
    have hJ1 : 1 ≤ T / 2 := by omega
    have hJT : T / 2 ≤ T := Nat.div_le_self T 2
    have h0 := PlaneWaveGridG.vGridK_tailP (P := PlaneWaveGridG.regParticlesOfG sys)
      (D := (PlaneWaveGridG.posNucleiOfG sys.nuclei).toNucData) hg
      (PlaneWaveGridG.gLgamma_pos hL0 hV).le hκb (T / 2) T hJ1 hJT hTm r v
    have h : ‖maskOp (High T r) (kOp (vGridK eta m P Dn κ) v)‖ ≤
        Zc' * (26 * ((T / 2 : ℕ) : ℝ)) * ‖maskOp (High (T - T / 2) r) v‖ +
          Zc' * Real.sqrt (26 * PlaneWaveGridG.sobP g / ((T / 2 : ℕ) : ℝ)) *
            ‖wMul (FreeBoundary.wTotPh g) v‖ := h0
    have hsh := FreeBoundary.sq_mul_norm_high_le_phys P hg (T - T / 2) r v
    have hW := FreeBoundary.norm_wTotPh_le P g v
    have hE := norm_wPhys_grVL_le sys hL hV hκe hκb Λ hc hc1 f
    obtain ⟨ha1, ha2⟩ := shell_arith_U T hT hg hg1
    have hX : 0 < g * (((T - T / 2 : ℕ) : ℝ) + 1) := by positivity
    have hcW := cWvU_nonneg sys hV hc
    have hf := norm_nonneg f
    set Wv := ‖wMul (FreeBoundary.wPhys P g) v‖ with hWv
    have hWv0 : 0 ≤ Wv := norm_nonneg _
    -- the shell term
    have hs1 : Zc' * (26 * ((T / 2 : ℕ) : ℝ)) * ‖maskOp (High (T - T / 2) r) v‖ ≤
        52 * z / Real.sqrt (g * T) * Wv := by
      have hm1 : ‖maskOp (High (T - T / 2) r) v‖ ≤
          P.maxMass * Wv / (g * (((T - T / 2 : ℕ) : ℝ) + 1)) ^ 2 := by
        rw [le_div_iff₀ (by positivity), mul_comm]
        exact hsh
      have hT1 : 52 / (T : ℝ) ≤ 52 * g / Real.sqrt (g * T) := by
        rw [div_le_div_iff₀ (by linarith) hsT]
        have hsq : Real.sqrt (g * T) ≤ g * T := by
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith
        nlinarith
      calc Zc' * (26 * ((T / 2 : ℕ) : ℝ)) * ‖maskOp (High (T - T / 2) r) v‖
          ≤ Zc' * (26 * ((T / 2 : ℕ) : ℝ)) *
              (P.maxMass * Wv / (g * (((T - T / 2 : ℕ) : ℝ) + 1)) ^ 2) := by gcongr
        _ = (sys.maxMass * Zc') * (26 * ((T / 2 : ℕ) : ℝ) /
              (((T - T / 2 : ℕ) : ℝ) + 1) ^ 2) / g ^ 2 * Wv := by
            rw [hMeq]
            field_simp
        _ ≤ (z * g) * (52 / T) / g ^ 2 * Wv := by
            rw [hZz]
            gcongr
        _ ≤ (z * g) * (52 * g / Real.sqrt (g * T)) / g ^ 2 * Wv := by gcongr
        _ = 52 * z / Real.sqrt (g * T) * Wv := by
            field_simp
    -- the weight term
    have hs2 : Zc' * Real.sqrt (26 * PlaneWaveGridG.sobP g / ((T / 2 : ℕ) : ℝ)) *
        ‖wMul (FreeBoundary.wTotPh g) v‖ ≤ z * Real.sqrt 6162 / Real.sqrt (g * T) * Wv := by
      have hm2 : ‖wMul (FreeBoundary.wTotPh g) v‖ ≤ P.maxMass * Wv := hW
      calc Zc' * Real.sqrt (26 * PlaneWaveGridG.sobP g / ((T / 2 : ℕ) : ℝ)) *
            ‖wMul (FreeBoundary.wTotPh g) v‖
          ≤ Zc' * (Real.sqrt 6162 / (g * Real.sqrt (g * T))) * (P.maxMass * Wv) := by gcongr
        _ = (sys.maxMass * Zc') * Real.sqrt 6162 / (g * Real.sqrt (g * T)) * Wv := by
            rw [hMeq]
            ring
        _ = z * Real.sqrt 6162 / Real.sqrt (g * T) * Wv := by
            rw [hZz]
            field_simp
    refine h.trans ?_
    have hsum : 52 * z / Real.sqrt (g * T) * Wv + z * Real.sqrt 6162 / Real.sqrt (g * T) * Wv =
        z * (52 + Real.sqrt 6162) / Real.sqrt (g * T) * Wv := by ring
    have hfin : z * (52 + Real.sqrt 6162) / Real.sqrt (g * T) * Wv ≤ Vt / Real.sqrt (g * T) * ‖f‖ :=
      by
      rw [hVt]
      have h3 : 0 ≤ z * (52 + Real.sqrt 6162) / Real.sqrt (g * T) := by positivity
      calc z * (52 + Real.sqrt 6162) / Real.sqrt (g * T) * Wv
          ≤ z * (52 + Real.sqrt 6162) / Real.sqrt (g * T) * (cWvU sys V c * ‖f‖) :=
            mul_le_mul_of_nonneg_left hE h3
        _ = _ := by ring
    linarith
  -- the eigenvalue part
  have hEg : ∀ f, ‖maskOp (High T r) (Hgrid eta m P Dn κ g (grVL P Dn g hκe c Λ f))‖ ≤
      N * ((2 * Λ + cGrU sys V) * ‖f‖) := by
    intro f
    rw [Hgrid_grVL, ← htail]
    refine (tailG.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ hN0)
    refine norm_le_of_coord (by positivity) fun a => ?_
    change ‖(if grE P Dn g hκe a + c ≤ 2 * Λ then (grE P Dn g hκe a : ℂ) else 0) * f a‖ ≤
      (2 * Λ + cGrU sys V) * ‖f a‖
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    split_ifs with ha
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      have hl := grE_lower_U sys hL hV hκe hκb a
      constructor <;> linarith
    · rw [norm_zero]
      positivity
  -- absorption
  have hstep : ∀ f, ‖tailG f‖ ≤
      (A * (2 * Λ + cGrU sys V) * N + A * (Vt / Real.sqrt (g * T))) * ‖f‖ := by
    intro f
    rw [htail]
    set v := grVL P Dn g hκe c Λ f
    have h1 := norm_high_le_kinT P hg T r v
    have hsplit : wMul (kinT eta m P g) v =
        Hgrid eta m P Dn κ g v - kOp (vGridK eta m P Dn κ) v := by
      simp only [Hgrid, LinearMap.add_apply]
      abel
    rw [hsplit, map_sub] at h1
    have h2 := norm_sub_le (maskOp (High T r) (Hgrid eta m P Dn κ g v))
      (maskOp (High T r) (kOp (vGridK eta m P Dn κ) v))
    have h3 := hEg f
    have h4 := hV' f
    have eA : 2 * P.maxMass / (g ^ 2 * ((T : ℝ) + 1) ^ 2) = A := by
      rw [hA, hMeq, mul_pow]
    rw [eA] at h1
    calc ‖maskOp (High T r) v‖
        ≤ A * ‖maskOp (High T r) (Hgrid eta m P Dn κ g v) -
            maskOp (High T r) (kOp (vGridK eta m P Dn κ) v)‖ := h1
      _ ≤ A * (N * ((2 * Λ + cGrU sys V) * ‖f‖) + Vt / Real.sqrt (g * T) * ‖f‖) :=
          mul_le_mul_of_nonneg_left (h2.trans (add_le_add h3 h4)) hA0
      _ = _ := by ring
  have hNle : N ≤ A * (2 * Λ + cGrU sys V) * N + A * (Vt / Real.sqrt (g * T)) :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) hstep
  have hN2 : N ≤ 2 * (A * (Vt / Real.sqrt (g * T))) := by
    have : A * (2 * Λ + cGrU sys V) * N ≤ N / 2 := by
      have := mul_le_mul_of_nonneg_right hAΛ hN0
      linarith
    linarith
  have hfin : 2 * (A * (Vt / Real.sqrt (g * T))) =
      cGtU sys V c / ((g * ((T : ℝ) + 1)) ^ 2 * Real.sqrt (g * T)) := by
    rw [hA, hVt]
    unfold cGtU
    field_simp
    ring
  have hfinal : ‖tailG f‖ ≤ N * ‖f‖ := tailG.le_opNorm f
  rw [htail] at hfinal
  calc ‖maskOp (High T r) (grVL P Dn g hκe c Λ f)‖ ≤ N * ‖f‖ := hfinal
    _ ≤ 2 * (A * (Vt / Real.sqrt (g * T))) * ‖f‖ :=
        mul_le_mul_of_nonneg_right hN2 (norm_nonneg _)
    _ = _ := by rw [hfin]

end GridU

end KineticLog
