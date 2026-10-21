import PlaneWave.FreeBoundary.UniformGridCore
import PlaneWave.FreeBoundary.UniformCubic
import PlaneWave.FreeBoundary.GridEnergy

/-!
# `app:free`, `L`-uniform constants, part 3: `thm:grid-energy` for `g_L` with constants
uniform in `L`

`PlaneWave.FreeBoundary.GridEnergy` proves `|E_{N,L} - E_L| ≤ C(L)/K³` for the range-truncated kernel `g_L`, with a constant
that grows polynomially in the cell side `L`. Here the same comparison is assembled from the
physical-unit grid core (`PlaneWave.FreeBoundary.UniformGridCore`, `grid_galerkin_energyP`) and the cubic error with the sharper
Sobolev constant (`PlaneWave.FreeBoundary.UniformCubic`, `gL_sector_cubic_errorP`). For `L ≥ 2π` (so `g = 2π/L ≤ 1`):

* the physical coupling `z = m̄ Z_c/g` of the `g_L` system does not depend on `L`
  (`gLGridCoupling_eq`: `m̄ Z_c = z g`, `z = gLzU`);
* the release constants of the cubic error are bounded independently of `L`
  (`tB_gL_eq`, `ctailP_gL_le`, `gLCubicConstP_le_U`, `gLCubicThresholdP_le`);
* **`gLSectorKernelGridErrorU`**: the torus ground energy `E_L` exists, and for every energy
  budget `E_b ≥ |E_L| + 1`, every `m ≥ η + 8` with `K = (2π/L) m ≥ K₀(E_b)` and every kernel of
  the class, the grid ground energy satisfies `|E_g - E_L| ≤ C(E_b)/K³`. The threshold `K₀`
  (`gLKThresholdU`) and the constant `C` (`gLErrorConstU`) depend on the system, on the total
  variation `V` of the profile and on `E_b`, not on `L`; `gLSectorGridErrorU` is the case of the
  truncated kernel `(g_L)_{≤2K}`.

With `E_L + C₀ → E_∞` (`PlaneWave.FreeBoundary.LowerBound`), `|E_L| + 1` is bounded for large `L`, so one budget `E_b` serves
for all large cells.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate BigOperators
open Finset PlaneWaveCertificate FreeBoundary FSNormal

namespace PlaneWaveGridG

/-! ## The coupling is linear in the amplitude -/

section Coupling

lemma coupling_mul {ν' : Type*} {eta' : ℕ} (D : NucData ν') (c γ : ℝ) (t : Term eta' ν') :
    coupling eta' D (c * γ) t = c * coupling eta' D γ t := by
  cases t with
  | inl _ => rfl
  | inr il => simp only [coupling]; ring

lemma Zc_mul {ν' : Type*} [Fintype ν'] {eta' : ℕ} (P : RegParticles eta') (D : NucData ν')
    (c γ : ℝ) : Zc P D (c * γ) = c * Zc P D γ := by
  unfold Zc
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [coupling_mul]; ring

end Coupling

section Uniform

variable {eta : ℕ} {ν : Type} [Fintype ν] {R : ℝ} {θ : ℝ → ℝ}

/-- The physical coupling `z = m̄ Z_c(γ)/g` of the `g_L` system (`γ = (1 + V)/(πL)`,
`g = 2π/L`); it does not depend on `L`. -/
noncomputable def gLzU (sys : CoulombSystem eta ν) (V : ℝ) : ℝ :=
  sys.maxMass * Zc (regParticlesOfG sys) (posNucleiOfG sys.nuclei).toNucData
    ((1 + V) / (2 * Real.pi ^ 2))

lemma gLzU_nonneg (sys : CoulombSystem eta ν) {V : ℝ} (hV : 0 ≤ V) : 0 ≤ gLzU sys V :=
  mul_nonneg sys.maxMass_pos.le (Zc_nonneg (by positivity))

/-- `m̄ Z_c = z g`. -/
lemma gLGridCoupling_eq (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (V : ℝ) :
    gLGridCoupling sys L V = gLzU sys V * (2 * Real.pi / L) := by
  unfold gLGridCoupling gLzU
  have e : gLgamma L V = (2 * Real.pi / L) * ((1 + V) / (2 * Real.pi ^ 2)) := by
    unfold gLgamma coulombCellAmplitude
    field_simp
  rw [e, Zc_mul]
  ring

/-! ## The constants of the grid core for `g_L`, with `σ = 79` (`g ≤ 1`) -/

/-- `A = 43264 · 79 z³ + 52 z`. -/
noncomputable def gLAU (sys : CoulombSystem eta ν) (V : ℝ) : ℝ :=
  43264 * 79 * gLzU sys V ^ 3 + 52 * gLzU sys V

/-- The energy bound of the grid core. -/
noncomputable def gLEbigU (sys : CoulombSystem eta ν) (V Eb : ℝ) : ℝ :=
  EbigU sys.maxMass (gLzU sys V) 79 (gLAU sys V) Eb

/-- The comparison constant of the grid core. -/
noncomputable def gLCgridU (sys : CoulombSystem eta ν) (V Eb : ℝ) : ℝ :=
  CgridU sys.maxMass (gLzU sys V) 79 (gLAU sys V) Eb

/-! ## The release constants of the cubic error for `L ≥ 2π` -/

/-- The Hardy constant of the `g_L` amplitude, `B = H/(2π²)`. -/
noncomputable def tBU (Hunit : ℝ) : ℝ := Hunit / (2 * Real.pi ^ 2)

/-- An `L`-free bound for the tail constant `c_tail` (`L ≥ 2π`). -/
noncomputable def ctailU (Hunit : ℝ) : ℝ :=
  (2 + Real.sqrt 2) * tBU Hunit + 108 / Real.pi ^ 2 + Real.sqrt (8532 / Real.pi ^ 4)

noncomputable def gLformConstU (sys : CoulombSystem eta ν) (V Hunit : ℝ) : ℝ :=
  sys.couplingWeight * ((1 + V) * tBU Hunit)

noncomputable def gLmassConstU (sys : CoulombSystem eta ν) (V Hunit : ℝ) : ℝ :=
  sys.massCouplingWeight * ((1 + V) * tBU Hunit)

noncomputable def gLH2ConstU (sys : CoulombSystem eta ν) (V Hunit E0 : ℝ) : ℝ :=
  sys.maxMass * uniformBOEigenH2Constant E0 (gLmassConstU sys V Hunit)

noncomputable def gLtailConstU (sys : CoulombSystem eta ν) (V Hunit E0 : ℝ) : ℝ :=
  sys.couplingWeight * ((1 + V) * ctailU Hunit) * gLH2ConstU sys V Hunit E0

/-- The cubic error constant, `L`-free. -/
noncomputable def gLCubicConstU (sys : CoulombSystem eta ν) (V Eb : ℝ) : ℝ :=
  64 * ((1 / 2 : ℝ) + gLformConstU sys V molecularCanonicalUnitHardyConstant + Eb) *
    (∑ a, sys.mass a) * (∑ a, sys.mass a ^ 2) *
      (gLtailConstU sys V molecularCanonicalUnitHardyConstant Eb) ^ 2

/-- The cubic size threshold in physical units. -/
noncomputable def gLKcubU (sys : CoulombSystem eta ν) (V Eb : ℝ) : ℝ :=
  5 + 4 * sys.maxMass * Eb +
    32 * (∑ a, sys.mass a ^ 2) * (gLtailConstU sys V molecularCanonicalUnitHardyConstant Eb) ^ 2

lemma tBU_nonneg {Hunit : ℝ} (hH : 0 ≤ Hunit) : 0 ≤ tBU Hunit := by
  unfold tBU; positivity

lemma g_le_one {L : ℝ} (hL : 2 * Real.pi ≤ L) : 2 * Real.pi / L ≤ 1 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  rw [div_le_one hL0]; exact hL

lemma tB_gL_eq {L : ℝ} (hL : 2 * Real.pi ≤ L) {Hunit : ℝ} (hH : 0 ≤ Hunit) :
    tB (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L) = tBU Hunit := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hg1 := g_le_one hL
  have hg0 : 0 < 2 * Real.pi / L := by positivity
  have hmin : physicalH1Scale (2 * Real.pi / L) = (2 * Real.pi / L) ^ 2 := by
    unfold physicalH1Scale
    exact min_eq_right (pow_le_one₀ hg0.le hg1)
  unfold tB tBU
  rw [hmin]
  have e : coulombCellAmplitude L ^ 2 * Hunit ^ 2 / (2 * Real.pi / L) ^ 2 =
      (Hunit / (2 * Real.pi ^ 2)) ^ 2 := by
    unfold coulombCellAmplitude
    field_simp
  rw [e, Real.sqrt_sq (by positivity)]

lemma tBlow_gL_eq {L : ℝ} (hL : 0 < L) :
    tBlow (coulombCellAmplitude L ^ 2) (2 * Real.pi / L) = 27 / Real.pi ^ 2 := by
  unfold tBlow coulombCellAmplitude
  rw [Real.sqrt_sq (by positivity)]
  field_simp
  ring

lemma tCsP_tBker_gL_le {L : ℝ} (hL : 2 * Real.pi ≤ L) :
    tCsP (2 * Real.pi / L) * tBker (coulombCellAmplitude L ^ 2) (2 * Real.pi / L) ≤
      Real.sqrt (8532 / Real.pi ^ 4) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hπ := Real.pi_pos
  unfold tCsP tBker
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have e : (1 + 78 / (2 * Real.pi / L) ^ 3) *
      (432 * coulombCellAmplitude L ^ 2 * (2 * Real.pi / L)) =
        864 / (Real.pi * L ^ 3) + 8424 / Real.pi ^ 4 := by
    unfold coulombCellAmplitude
    field_simp
    ring
  rw [e]
  have hL3 : (2 * Real.pi) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by positivity) hL 3
  have h1 : 864 / (Real.pi * L ^ 3) ≤ 108 / Real.pi ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hL3 (by positivity : (0 : ℝ) ≤ 108 * Real.pi)]
  have e2 : 108 / Real.pi ^ 4 + 8424 / Real.pi ^ 4 = 8532 / Real.pi ^ 4 := by ring
  linarith

lemma ctailP_gL_le {L : ℝ} (hL : 2 * Real.pi ≤ L) {Hunit : ℝ} (hH : 0 ≤ Hunit) :
    ctailP (coulombCellAmplitude L ^ 2) Hunit (2 * Real.pi / L) ≤ ctailU Hunit := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hg1 := g_le_one hL
  have hg0 : 0 < 2 * Real.pi / L := by positivity
  unfold ctailP tZP
  rw [tB_gL_eq hL hH, tBlow_gL_eq hL0]
  have hs : Real.sqrt (2 * (2 * Real.pi / L)) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by linarith)
  have hT := tCsP_tBker_gL_le hL
  have hB := tBU_nonneg hH
  have h1 : (1 + Real.sqrt (2 * (2 * Real.pi / L))) * tBU Hunit ≤ (1 + Real.sqrt 2) * tBU Hunit :=
    mul_le_mul_of_nonneg_right (by linarith) hB
  unfold ctailU
  have e : 4 * (27 / Real.pi ^ 2) = 108 / Real.pi ^ 2 := by ring
  linarith

lemma gLformConst_gL_eq (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) (V : ℝ)
    {Hunit : ℝ} (hH : 0 ≤ Hunit) : gLformConst sys L V Hunit = gLformConstU sys V Hunit := by
  unfold gLformConst gLformConstU
  rw [tB_gL_eq hL hH]

lemma gLH2Const_gL_eq (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) (V : ℝ)
    {Hunit : ℝ} (hH : 0 ≤ Hunit) (E0 : ℝ) :
    gLH2Const sys L V Hunit E0 = gLH2ConstU sys V Hunit E0 := by
  unfold gLH2Const gLH2ConstU gLmassConst gLmassConstU
  rw [tB_gL_eq hL hH]

lemma gLH2ConstU_mono (sys : CoulombSystem eta ν) (V Hunit : ℝ) {E0 E1 : ℝ} (hE : E0 ≤ E1) :
    gLH2ConstU sys V Hunit E0 ≤ gLH2ConstU sys V Hunit E1 := by
  unfold gLH2ConstU uniformBOEigenH2Constant
  exact mul_le_mul_of_nonneg_left (by linarith) sys.maxMass_pos.le

lemma gLtailConstP_le_U (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) {V : ℝ}
    (hV : 0 ≤ V) {Hunit : ℝ} (hH : 0 ≤ Hunit) {E0 E1 : ℝ} (hE0 : 0 ≤ E0) (hE : E0 ≤ E1) :
    gLtailConstP sys L V Hunit E0 ≤ gLtailConstU sys V Hunit E1 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hg0 : 0 < 2 * Real.pi / L := by positivity
  unfold gLtailConstP gLtailConstU
  rw [gLH2Const_gL_eq sys hL V hH]
  have hc := ctailP_nonneg (C := coulombCellAmplitude L ^ 2) (Hunit := Hunit) hg0
  have hcU := ctailP_gL_le hL hH
  have hw := sys.couplingWeight_nonneg
  have hM0 : 0 ≤ gLH2ConstU sys V Hunit E0 := by
    rw [← gLH2Const_gL_eq sys hL V hH]
    exact gLH2Const_nonneg sys L V Hunit hE0
  have hM1 := gLH2ConstU_mono sys V Hunit hE
  have h1 : 0 ≤ sys.couplingWeight * ((1 + V) * ctailP (coulombCellAmplitude L ^ 2) Hunit
      (2 * Real.pi / L)) := by positivity
  calc sys.couplingWeight * ((1 + V) * ctailP (coulombCellAmplitude L ^ 2) Hunit
        (2 * Real.pi / L)) * gLH2ConstU sys V Hunit E0
      ≤ sys.couplingWeight * ((1 + V) * ctailU Hunit) * gLH2ConstU sys V Hunit E0 := by
        gcongr
    _ ≤ sys.couplingWeight * ((1 + V) * ctailU Hunit) * gLH2ConstU sys V Hunit E1 := by
        have : 0 ≤ sys.couplingWeight * ((1 + V) * ctailU Hunit) := by
          have := hc.trans hcU
          positivity
        exact mul_le_mul_of_nonneg_left hM1 this

lemma gLtailConstU_nonneg (sys : CoulombSystem eta ν) {V : ℝ} (hV : 0 ≤ V) {Hunit : ℝ}
    (hH : 0 ≤ Hunit) {E0 : ℝ} (hE0 : 0 ≤ E0) : 0 ≤ gLtailConstU sys V Hunit E0 := by
  unfold gLtailConstU gLH2ConstU ctailU
  have := tBU_nonneg hH
  have := sys.couplingWeight_nonneg
  have := sys.maxMass_pos
  have := uniformBOEigenH2Constant_nonneg (B := gLmassConstU sys V Hunit) hE0
  positivity

lemma gLCubicConstP_le_U (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) {V : ℝ}
    (hV : 0 ≤ V) {E Eb : ℝ} (hE : |E| + 1 ≤ Eb) :
    gLCubicConstP sys L V E ≤ gLCubicConstU sys V Eb := by
  have hH := molecularCanonicalUnitHardyConstant_nonneg
  unfold gLCubicConstP gLCubicConstU
  rw [gLformConst_gL_eq sys hL V hH]
  have hT := gLtailConstP_le_U sys hL hV hH (by positivity : (0 : ℝ) ≤ |E| + 1) hE
  have hT0 : 0 ≤ gLtailConstP sys L V molecularCanonicalUnitHardyConstant (|E| + 1) := by
    unfold gLtailConstP
    have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
    have hg0 : 0 < 2 * Real.pi / L := by positivity
    have := ctailP_nonneg (C := coulombCellAmplitude L ^ 2)
      (Hunit := molecularCanonicalUnitHardyConstant) hg0
    have := sys.couplingWeight_nonneg
    have := gLH2Const_nonneg sys L V molecularCanonicalUnitHardyConstant
      (by positivity : (0 : ℝ) ≤ |E| + 1)
    positivity
  have hF := mul_nonneg sys.couplingWeight_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + V)
    (tBU_nonneg hH))
  have hS1 : 0 ≤ ∑ a, sys.mass a := Finset.sum_nonneg fun a _ => (sys.mass_pos a).le
  have hS2 : 0 ≤ ∑ a, sys.mass a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hEabs : |E| ≤ Eb := by linarith
  have hEb0 : 0 ≤ Eb := le_trans (by positivity) hE
  unfold gLformConstU at hF ⊢
  have hT2 := pow_le_pow_left₀ hT0 hT 2
  have h1 : 0 ≤ 64 * ((1 / 2 : ℝ) + sys.couplingWeight * ((1 + V) *
      tBU molecularCanonicalUnitHardyConstant) + Eb) * (∑ a, sys.mass a) *
        (∑ a, sys.mass a ^ 2) := by positivity
  gcongr

lemma gLCubicThresholdP_le (sys : CoulombSystem eta ν) {L : ℝ} (hL : 2 * Real.pi ≤ L) {V : ℝ}
    (hV : 0 ≤ V) {E Eb : ℝ} (hE : |E| + 1 ≤ Eb) {M : ℕ} (hMeta : eta ≤ M)
    (hK : gLKcubU sys V Eb ≤ (2 * Real.pi / L) * M) :
    gLCubicThresholdP sys L V E ≤ M := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hg0 : 0 < 2 * Real.pi / L := by positivity
  have hg1 := g_le_one hL
  have hH := molecularCanonicalUnitHardyConstant_nonneg
  set g := 2 * Real.pi / L with hgdef
  set T := gLtailConstP sys L V molecularCanonicalUnitHardyConstant (|E| + 1) with hTdef
  set TU := gLtailConstU sys V molecularCanonicalUnitHardyConstant Eb with hTUdef
  have hT := gLtailConstP_le_U sys hL hV hH (by positivity : (0 : ℝ) ≤ |E| + 1) hE
  have hT0 : 0 ≤ T := by
    rw [hTdef]
    unfold gLtailConstP
    have := ctailP_nonneg (C := coulombCellAmplitude L ^ 2)
      (Hunit := molecularCanonicalUnitHardyConstant) hg0
    have := sys.couplingWeight_nonneg
    have := gLH2Const_nonneg sys L V molecularCanonicalUnitHardyConstant
      (by positivity : (0 : ℝ) ≤ |E| + 1)
    positivity
  have hT2 : T ^ 2 ≤ TU ^ 2 := pow_le_pow_left₀ hT0 hT 2
  have hS2 : 0 ≤ ∑ a, sys.mass a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hM0 : 0 < sys.maxMass := sys.maxMass_pos
  have hKU : 5 + 4 * sys.maxMass * Eb + 32 * (∑ a, sys.mass a ^ 2) * TU ^ 2 ≤ g * M := hK
  set x := 1 + 2 * g + 4 * sys.maxMass * (|E| + 1) + 32 * (∑ a, sys.mass a ^ 2) * T ^ 2
    with hxdef
  have hx : x + g ≤ g * M := by
    have h1 : 4 * sys.maxMass * (|E| + 1) ≤ 4 * sys.maxMass * Eb :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    have h2 : 32 * (∑ a, sys.mass a ^ 2) * T ^ 2 ≤ 32 * (∑ a, sys.mass a ^ 2) * TU ^ 2 :=
      mul_le_mul_of_nonneg_left hT2 (by positivity)
    linarith
  have hM1 : (1 : ℝ) ≤ M := by
    have h5 : (5 : ℝ) ≤ g * M := by
      have : 0 ≤ 4 * sys.maxMass * Eb + 32 * (∑ a, sys.mass a ^ 2) * TU ^ 2 := by
        have hEb0 : 0 ≤ Eb := le_trans (by positivity) hE
        positivity
      linarith
    nlinarith
  unfold gLCubicThresholdP coulombExplicitCubicThreshold
  rw [← hgdef, ← hTdef, ← hxdef]
  refine max_le (by exact_mod_cast hM1) (max_le hMeta ?_)
  have hceil : (Nat.ceil (x / g) : ℝ) < x / g + 1 := by
    have hx0 : 0 ≤ x / g := by
      have hEp : 0 ≤ |E| + 1 := by positivity
      rw [hxdef]
      positivity
    exact Nat.ceil_lt_add_one hx0
  have hxg : x / g + 1 ≤ M := by
    rw [div_add_one hg0.ne', div_le_iff₀ hg0]
    linarith
  have hlt : (Nat.ceil (x / g) : ℝ) < M := lt_of_lt_of_le hceil hxg
  have : Nat.ceil (x / g) < M := by exact_mod_cast hlt
  omega

/-! ## The `L`-uniform grid energy theorem -/

/-- The size threshold `K₀` in physical units (`L`-free). -/
noncomputable def gLKThresholdU (sys : CoulombSystem eta ν) (V Eb : ℝ) : ℝ :=
  max (8 * Real.sqrt (sys.maxMass * gLEbigU sys V Eb) + 4)
    (max (gLKcubU sys V Eb / 2) (gLCubicConstU sys V Eb ^ ((1 : ℝ) / 3) / 2))

/-- The error constant `512 C_grid + C_cub/8` (`L`-free). -/
noncomputable def gLErrorConstU (sys : CoulombSystem eta ν) (V Eb : ℝ) : ℝ :=
  512 * gLCgridU sys V Eb + gLCubicConstU sys V Eb / 8

lemma gLCubicConstU_nonneg (sys : CoulombSystem eta ν) {V : ℝ} (hV : 0 ≤ V) {Eb : ℝ}
    (hEb : 0 ≤ Eb) : 0 ≤ gLCubicConstU sys V Eb := by
  have hH := molecularCanonicalUnitHardyConstant_nonneg
  unfold gLCubicConstU
  have h1 : 0 ≤ gLformConstU sys V molecularCanonicalUnitHardyConstant :=
    mul_nonneg sys.couplingWeight_nonneg (mul_nonneg (by linarith) (tBU_nonneg hH))
  have h2 : 0 ≤ ∑ a, sys.mass a := Finset.sum_nonneg fun a _ => (sys.mass_pos a).le
  have h3 : 0 ≤ ∑ a, sys.mass a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  positivity

/-- **Grid energy theorem for the range-truncated kernel `g_L`, with constants uniform in `L`.**
For `L ≥ 2π` the torus ground energy `E_L` of the `g_L` Hamiltonian exists, and for every energy
budget `E_b ≥ |E_L| + 1`, every `m ≥ η + 8` with `K = (2π/L) m ≥ K₀(E_b)` and every kernel `κ` of
the class (`IsGridKernel γ ρ m κ`, `γ ρ = ĝ_L`), the grid ground energy `E_g` satisfies
`|E_g - E_L| ≤ C(E_b)/K³`. The threshold `K₀ = gLKThresholdU` and the constant
`C = gLErrorConstU` depend on the system, the total variation `V` of the profile and `E_b`, not
on `L`. -/
theorem gLSectorKernelGridErrorU (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L : ℝ} (hL : 2 * Real.pi ≤ L) (hθ : Profile R θ) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E ∧
      ∀ Eb : ℝ, |E| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        gLKThresholdU sys (tv R θ) Eb ≤ (2 * Real.pi / L) * m →
        ∀ κ : Lat3 → ℝ, IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ →
        ∃ Eg : ℝ, IsGLSectorKernelGridGroundEnergy sys lab L m κ Eg ∧
          |Eg - E| ≤ gLErrorConstU sys (tv R θ) Eb / ((2 * Real.pi / L) * m) ^ 3 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨E, hE, hCubic⟩ := gL_sector_cubic_errorP sys lab hlab hL0 hθ
  refine ⟨E, hE, ?_⟩
  intro Eb hEb m hm hKm κ hκ
  set g : ℝ := 2 * Real.pi / L with hgdef
  have hg : 0 < g := by positivity
  have hg1 : g ≤ 1 := g_le_one hL
  set V := tv R θ with hVdef
  have hV : 0 ≤ V := hθ.tv_nonneg
  have hEb0 : 0 ≤ Eb := le_trans (by positivity) hEb
  have hm8 : 8 ≤ m := by omega
  have hmeta : eta ≤ m := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  set K : ℝ := g * m with hKdef
  have hK0 : 0 < K := by positivity
  have hK1 : 8 * Real.sqrt (sys.maxMass * gLEbigU sys V Eb) + 4 ≤ K :=
    (le_max_left _ _).trans hKm
  have hK2 : gLKcubU sys V Eb / 2 ≤ K :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hKm
  have hK3 : gLCubicConstU sys V Eb ^ ((1 : ℝ) / 3) / 2 ≤ K :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hKm
  -- the cube `2m`
  have hcubthr : gLCubicThresholdP sys L V E ≤ 2 * m := by
    refine gLCubicThresholdP_le sys hL hV hEb (by omega) ?_
    rw [← hgdef]
    push_cast
    linarith
  obtain ⟨EN, uN, hSN, hnN, hEigN, hGN, hNonneg, hRate⟩ := hCubic (2 * m) hcubthr
  have hgal := galRitz_of_ground_gL sys lab m hL0 hθ EN uN hSN hnN hEigN hGN
  set γ : ℝ := gLgamma L V with hγdef
  have hγ : 0 ≤ γ := (gLgamma_pos hL0 hV).le
  set P := regParticlesOfG sys with hPdef
  set D := gLNucData sys hL0 hθ with hDdef
  set M : ℝ := sys.maxMass with hMdef
  have hM0 : 0 < M := sys.maxMass_pos
  set z : ℝ := gLzU sys V with hzdef
  have hz0 : 0 ≤ z := gLzU_nonneg sys hV
  set A : ℝ := gLAU sys V with hAdef
  -- the cubic constant
  set Ccub : ℝ := gLCubicConstP sys L V E with hCcubdef
  set CcubU : ℝ := gLCubicConstU sys V Eb with hCcubUdef
  have hCcub0 : 0 ≤ Ccub := gLCubicConstP_nonneg sys L hV E
  have hCcubU0 : 0 ≤ CcubU := gLCubicConstU_nonneg sys hV hEb0
  have hCcubLe : Ccub ≤ CcubU := gLCubicConstP_le_U sys hL hV hEb
  have hcube : CcubU ≤ (2 * K) ^ 3 := by
    have h1 : CcubU ^ ((1 : ℝ) / 3) ≤ 2 * K := by linarith
    have h2 : (CcubU ^ ((1 : ℝ) / 3)) ^ 3 = CcubU := by
      rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow hCcubU0 (by norm_num)
    calc CcubU = (CcubU ^ ((1 : ℝ) / 3)) ^ 3 := h2.symm
      _ ≤ (2 * K) ^ 3 := pow_le_pow_left₀ (Real.rpow_nonneg hCcubU0 _) h1 3
  have hK2m : g * ((2 * m : ℕ) : ℝ) = 2 * K := by rw [hKdef]; push_cast; ring
  have hENE : EN - E ≤ 1 := by
    refine hRate.trans ?_
    rw [hK2m, div_le_one (by positivity)]
    exact hCcubLe.trans hcube
  have hEbN : |EN| ≤ Eb := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le E]
    · linarith [le_abs_self E]
  -- the grid core
  have hNZ := exists_nonzero_sec sys hlab m hmeta
  have hP : ∀ a b, lab a = lab b → P.mass a = P.mass b ∧ P.charge a = P.charge b :=
    fun a b h => ⟨sys.mass_eq a b (hlab a b h), sys.charge_eq a b (hlab a b h)⟩
  set s : ℕ := m / 4 with hsdef
  have hs2 : 2 ≤ s := by omega
  have hsm : s ≤ m := Nat.div_le_self m 4
  have hms : m ≤ 8 * s := by omega
  have hsr : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hz : P.maxMass * Zc P D γ ≤ z * g := by
    have e : P.maxMass * Zc P D γ = gLGridCoupling sys L V := rfl
    rw [e, gLGridCoupling_eq sys hL0 V]
  have hσ : g ^ 3 + 78 ≤ 79 := by
    have : g ^ 3 ≤ 1 := pow_le_one₀ hg.le hg1
    linarith
  have hA : 43264 * 79 * z ^ 3 + 52 * z * g ≤ A := by
    rw [hAdef]
    unfold gLAU
    rw [← hzdef]
    have := mul_le_mul_of_nonneg_left hg1 hz0
    linarith
  have hEbig0 : 0 ≤ M * gLEbigU sys V Eb := by
    refine mul_nonneg hM0.le (le_trans ?_ (le_max_left _ _))
    have : 0 ≤ gLAU sys V := by unfold gLAU; positivity
    linarith
  have hbig : 4 * P.maxMass * EbigU P.maxMass z 79 A Eb ≤ (g * s) ^ 2 := by
    have e : P.maxMass * EbigU P.maxMass z 79 A Eb = M * gLEbigU sys V Eb := rfl
    have hs4 : (m : ℝ) ≤ 4 * s + 3 := by exact_mod_cast (by omega : m ≤ 4 * s + 3)
    have h1 : K ≤ 4 * (g * s) + 3 * g := by
      have := mul_le_mul_of_nonneg_left hs4 hg.le
      rw [hKdef]
      linarith
    have hgs : 2 * Real.sqrt (M * gLEbigU sys V Eb) ≤ g * s := by linarith
    have h2 := pow_le_pow_left₀ (by positivity) hgs 2
    rw [mul_pow, Real.sq_sqrt hEbig0] at h2
    calc 4 * P.maxMass * EbigU P.maxMass z 79 A Eb = 4 * (M * gLEbigU sys V Eb) := by
          rw [mul_assoc, e]
      _ ≤ (g * s) ^ 2 := by linarith
  obtain ⟨Eg, hRitz, hdiff⟩ := grid_galerkin_energyP (P := P) (D := D) (m := m) sys.sign lab hP
    hγ hg hs2 hsm hms hκ.gridKernel hNZ hz hσ hA EN Eb hEbN hgal hbig
  have hRitz' : IsSecRitz sys.sign lab
      (Hgrid eta m P (posNucleiOfG sys.nuclei).toNucData κ g) Eg := hRitz
  have hpos : IsGLSectorKernelGridGroundEnergy sys lab L m κ Eg :=
    (isSecRitz_Hpos_iff sys.sign lab P (posNucleiOfG sys.nuclei) κ hκ.even g Eg).mpr hRitz'
  set Cg : ℝ := CgridU P.maxMass z 79 A Eb with hCgdef
  have hCg0 : 0 ≤ Cg := by
    rw [hCgdef]
    unfold CgridU
    exact mul_nonneg (CformU_nonneg hz0) (sq_nonneg _)
  have hCgE : Cg = gLCgridU sys V Eb := rfl
  have hdiff' : |Eg - EN| ≤ 512 * Cg / K ^ 3 := by
    refine hdiff.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hK8 : K ≤ 8 * (g * s) := by
      have h8 : (m : ℝ) ≤ 8 * s := by exact_mod_cast hms
      have := mul_le_mul_of_nonneg_left h8 hg.le
      rw [hKdef]
      linarith
    have h3 : K ^ 3 ≤ 512 * (g * s) ^ 3 := by
      calc K ^ 3 ≤ (8 * (g * s)) ^ 3 := pow_le_pow_left₀ hK0.le hK8 3
        _ = 512 * (g * s) ^ 3 := by ring
    linarith [mul_le_mul_of_nonneg_left h3 hCg0]
  have hrate' : EN - E ≤ CcubU / (8 * K ^ 3) := by
    refine hRate.trans ?_
    rw [hK2m]
    have e : (2 * K) ^ 3 = 8 * K ^ 3 := by ring
    rw [e]
    exact div_le_div_of_nonneg_right hCcubLe (by positivity)
  have htri : |Eg - E| ≤ |Eg - EN| + |EN - E| := by
    have := abs_sub_le Eg EN E
    linarith
  rw [abs_of_nonneg hNonneg] at htri
  refine ⟨Eg, hpos, ?_⟩
  calc |Eg - E| ≤ |Eg - EN| + (EN - E) := htri
    _ ≤ 512 * Cg / K ^ 3 + CcubU / (8 * K ^ 3) := add_le_add hdiff' hrate'
    _ = gLErrorConstU sys V Eb / K ^ 3 := by
        unfold gLErrorConstU
        rw [← hCgE, ← hCcubUdef]
        field_simp

/-- **Grid energy theorem for the truncated kernel `(g_L)_{≤2K}`, with constants uniform in
`L`.** -/
theorem gLSectorGridErrorU (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L : ℝ} (hL : 2 * Real.pi ≤ L) (hθ : Profile R θ) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E ∧
      ∀ Eb : ℝ, |E| + 1 ≤ Eb → ∀ m : ℕ, eta + 8 ≤ m →
        gLKThresholdU sys (tv R θ) Eb ≤ (2 * Real.pi / L) * m →
        ∃ Eg : ℝ, IsGLSectorKernelGridGroundEnergy sys lab L m
            (sharpKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m) Eg ∧
          |Eg - E| ≤ gLErrorConstU sys (tv R θ) Eb / ((2 * Real.pi / L) * m) ^ 3 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨E, hE, hGrid⟩ := gLSectorKernelGridErrorU sys lab hlab hL hθ
  exact ⟨E, hE, fun Eb hEb m hm hK => hGrid Eb hEb m hm hK _ (sharpKernel_isGridKernel
    (gLgamma_pos hL0 hθ.tv_nonneg).le (gLref_neg L θ _) (gLref_bound hL0 hθ) m)⟩

end Uniform

end PlaneWaveGridG
