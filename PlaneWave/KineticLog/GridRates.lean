import PlaneWave.KineticLog.GridTraj

/-!
# Logarithmic kinetic bound, part 14: the rates of the raw grid constants

With `K = g m`, `m ≥ 8` and `s₀ = ⌊m/4⌋ ≥ m/8`, the raw constants of `GridConsistency` have the
rates of `lem:kinetic-low` and `lem:kinetic-strong`:

* `δ_raw ≤ δ_G / K³` (`dRawG_le`), uniformly over the kernel class;
* `F_raw ≤ F_G / √K` (`fRawG_le`).

The constants `δ_G`, `F_G` depend on the fixed system, the cell, `Hunit` and the shift only.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGrid PlaneWaveGridDynamics
  PlaneWaveKinetic FSNormal

namespace KineticLog

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Scales -/

/-- `m/8 ≤ ⌊m/4⌋ ≤ m/4` and `2 ≤ ⌊m/4⌋` for `m ≥ 8`. -/
lemma quarter_bounds {m : ℕ} (hm : 8 ≤ m) :
    (m : ℝ) / 8 ≤ ((m / 4 : ℕ) : ℝ) ∧ ((m / 4 : ℕ) : ℝ) ≤ (m : ℝ) / 4 ∧
      (2 : ℝ) ≤ ((m / 4 : ℕ) : ℝ) := by
  have h1 : m ≤ 8 * (m / 4) := by omega
  have h2 : 4 * (m / 4) ≤ m := Nat.mul_div_le m 4
  have h3 : 2 ≤ m / 4 := by omega
  refine ⟨?_, ?_, by exact_mod_cast h3⟩
  · have : (m : ℝ) ≤ 8 * ((m / 4 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  · have : 4 * ((m / 4 : ℕ) : ℝ) ≤ m := by exact_mod_cast h2
    linarith

/-- `√K/3 ≤ √(K/8)`. -/
lemma sqrt_div_three_le {K : ℝ} (hK : 0 ≤ K) : Real.sqrt K / 3 ≤ Real.sqrt (K / 8) := by
  have e : Real.sqrt (K / 9) = Real.sqrt K / 3 := by
    rw [Real.sqrt_div' K (by norm_num : (0 : ℝ) ≤ 9)]
    have : Real.sqrt 9 = 3 := by
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]
  rw [← e]
  exact Real.sqrt_le_sqrt (by linarith)

/-- The scale facts at `s₀ = ⌊m/4⌋`: `K/8 ≤ g s₀` and `√K/(3√g) ≤ √s₀`. -/
lemma quarter_scales {g : ℝ} (hg : 0 < g) {m : ℕ} (hm : 8 ≤ m) :
    g * m / 8 ≤ g * ((m / 4 : ℕ) : ℝ) ∧
      Real.sqrt (g * m) / (3 * Real.sqrt g) ≤ Real.sqrt ((m / 4 : ℕ) : ℝ) := by
  obtain ⟨h1, -, -⟩ := quarter_bounds hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨by nlinarith, ?_⟩
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.mpr hg
  have e : Real.sqrt (g * m) / (3 * Real.sqrt g) = Real.sqrt (m : ℝ) / 3 := by
    rw [Real.sqrt_mul hg.le]
    field_simp
  rw [e]
  exact (sqrt_div_three_le hm0).trans (Real.sqrt_le_sqrt h1)

/-! ## The component rates -/

section Components

variable (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ)

lemma tuG_le (hL : 0 < L) {m : ℕ} (hm : 8 ≤ m) :
    tuG sys L Hunit m ≤ 192 * cAbs sys L Hunit / ((gF L * m) ^ 2 * Real.sqrt (gF L * m)) := by
  have hg := gF_pos hL
  obtain ⟨hKs, -⟩ := quarter_scales hg hm
  set K := gF L * m with hKdef
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hK0 : 0 < K := by positivity
  set Ks := gF L * ((m / 4 : ℕ) : ℝ) with hKsdef
  have hsq : Real.sqrt K / 3 ≤ Real.sqrt Ks :=
    (sqrt_div_three_le hK0.le).trans (Real.sqrt_le_sqrt hKs)
  have hden : (K / 8) ^ 2 * (Real.sqrt K / 3) ≤ Ks ^ 2 * Real.sqrt Ks :=
    mul_le_mul (pow_le_pow_left₀ (by positivity) hKs 2) hsq (by positivity) (by positivity)
  have hc := cAbs_nonneg sys Hunit hL
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  unfold tuG
  calc cAbs sys L Hunit / (Ks ^ 2 * Real.sqrt Ks)
      ≤ cAbs sys L Hunit / ((K / 8) ^ 2 * (Real.sqrt K / 3)) :=
        div_le_div_of_nonneg_left hc (by positivity) hden
    _ = 192 * cAbs sys L Hunit / (K ^ 2 * Real.sqrt K) := by
        field_simp
        ring

lemma tvG_le (hL : 0 < L) {c : ℝ} (hc : 0 ≤ c) {m : ℕ} (hm : 8 ≤ m) :
    tvG sys L c m ≤ 192 * Real.sqrt (gF L) * cGt (regParticlesOf sys)
      (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) (2 * Real.pi / L) c /
        ((gF L * m) ^ 2 * Real.sqrt (gF L * m)) := by
  have hg := gF_pos hL
  obtain ⟨hKs, hss⟩ := quarter_scales hg hm
  set K := gF L * m with hKdef
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hK0 : 0 < K := by positivity
  have hsg : 0 < Real.sqrt (gF L) := Real.sqrt_pos.mpr hg
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  set s := ((m / 4 : ℕ) : ℝ) with hsdef
  have hs0 : (2 : ℝ) ≤ s := (quarter_bounds hm).2.2
  have hcG := cGt_nonneg (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
    (coulombCellAmplitude_pos hL).le hc
  have hgs : (K / 8) ^ 2 ≤ (2 * Real.pi / L) ^ 2 * (s + 1) ^ 2 := by
    have : K / 8 ≤ (2 * Real.pi / L) * (s + 1) := by
      change K / 8 ≤ gF L * (s + 1)
      nlinarith
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) this 2
  have hden : (K / 8) ^ 2 * (Real.sqrt K / (3 * Real.sqrt (gF L))) ≤
      (2 * Real.pi / L) ^ 2 * (s + 1) ^ 2 * Real.sqrt s :=
    mul_le_mul hgs hss (by positivity) (by positivity)
  unfold tvG
  calc cGt (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
        (2 * Real.pi / L) c / ((2 * Real.pi / L) ^ 2 * (s + 1) ^ 2 * Real.sqrt s)
      ≤ cGt (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
        (2 * Real.pi / L) c / ((K / 8) ^ 2 * (Real.sqrt K / (3 * Real.sqrt (gF L)))) :=
        div_le_div_of_nonneg_left hcG (by positivity) hden
    _ = _ := by
        field_simp
        ring

lemma t2G_le (hL : 0 < L) {m : ℕ} (hm : 8 ≤ m) :
    t2G sys L Hunit m ≤ cAbs sys L Hunit / ((gF L * m) ^ 2 * Real.sqrt (gF L * m)) := by
  have hg := gF_pos hL
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  set K := gF L * m with hKdef
  have hK0 : 0 < K := by positivity
  have hc := cAbs_nonneg sys Hunit hL
  have e : gF L * ((2 * m : ℕ) : ℝ) = 2 * K := by
    rw [hKdef]
    push_cast
    ring
  unfold t2G
  rw [e]
  refine div_le_div_of_nonneg_left hc (by positivity) ?_
  exact mul_le_mul (pow_le_pow_left₀ hK0.le (by linarith) 2)
    (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) (by positivity)

lemma wvG_le (hL : 0 < L) {c : ℝ} (hc : 0 ≤ c) {m : ℕ} (hm : 8 ≤ m) :
    wvG sys L Hunit c m ≤
      eta * CtW sys L Hunit 1 * ((1 + gF L ^ 2) * xvG sys L c) / Real.sqrt (gF L * m) := by
  have hg := gF_pos hL
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  set K := gF L * m with hKdef
  have hK0 : 0 < K := by positivity
  have e : gF L * ((2 * m : ℕ) : ℝ) = 2 * K := by
    rw [hKdef]
    push_cast
    ring
  unfold wvG
  rw [e]
  have h0 : 0 ≤ eta * CtW sys L Hunit 1 * ((1 + gF L ^ 2) * xvG sys L c) := by
    have := CtW_nonneg sys hL Hunit zero_le_one
    have := xvG_nonneg (sys := sys) hL hc
    positivity
  exact div_le_div_of_nonneg_left h0 (Real.sqrt_pos.mpr hK0) (Real.sqrt_le_sqrt (by linarith))

lemma formA_quarter_le (hL : 0 < L) {m : ℕ} (hm : 8 ≤ m) :
    formA (m / 4) m ≤ 390 * Real.sqrt (gF L) / Real.sqrt (gF L * m) := by
  have hg := gF_pos hL
  obtain ⟨-, hss⟩ := quarter_scales hg hm
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hs1 : 1 ≤ m / 4 := by omega
  have hsm : m / 4 ≤ m := Nat.div_le_self m 4
  have h := formA_le hs1 hsm
  have hK0 : 0 < gF L * m := by positivity
  have hsK : 0 < Real.sqrt (gF L * m) := Real.sqrt_pos.mpr hK0
  have hsg : 0 < Real.sqrt (gF L) := Real.sqrt_pos.mpr hg
  refine h.trans ?_
  calc 130 / Real.sqrt ((m / 4 : ℕ) : ℝ)
      ≤ 130 / (Real.sqrt (gF L * m) / (3 * Real.sqrt (gF L))) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hss
    _ = 390 * Real.sqrt (gF L) / Real.sqrt (gF L * m) := by
        field_simp
        ring

end Components

/-! ## The rates -/

section Rates

variable (sys : CoulombSystem eta ν) (L Hunit : ℝ)

/-- **The weighted-consistency rate constant** `δ_G` (`δ_raw ≤ δ_G/K³`). -/
noncomputable def dG_grid (c : ℝ) : ℝ :=
  Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) *
      (74880 * Real.sqrt (gF L) * cAbs sys L Hunit * xvG sys L c +
        74880 * gF L * cGt (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
          (coulombCellAmplitude L) (2 * Real.pi / L) c * xuG sys L Hunit +
        1916928 * cGt (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData
          (coulombCellAmplitude L) (2 * Real.pi / L) c * cAbs sys L Hunit / Real.sqrt (gF L)) +
    cAbs sys L Hunit * (eta * CtW sys L Hunit 1 * ((1 + gF L ^ 2) * xvG sys L c))

/-- **The strong-consistency rate constant** `F_G` (`F_raw ≤ F_G/√K`). -/
noncomputable def fG_grid : ℝ :=
  Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L) *
      (74880 * Real.sqrt (gF L) * cAbs sys L Hunit * (1 + 12 * eta / gF L ^ 2) +
        390 * Real.sqrt (gF L) * xuG sys L Hunit + 9984 * cAbs sys L Hunit / gF L) +
    cAbs sys L Hunit * (eta * CtW sys L Hunit 1 * ((1 + gF L ^ 2) * (1 + 12 * eta / gF L ^ 2)))

variable {sys L Hunit}

lemma dG_grid_nonneg (hL : 0 < L) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ dG_grid sys L Hunit c := by
  unfold dG_grid
  have := Zc_nonneg (P := regParticlesOf sys) (D := (posNucleiOf sys.nuclei).toNucData)
    (coulombCellAmplitude_pos hL).le
  have := cAbs_nonneg sys Hunit hL
  have := xvG_nonneg (sys := sys) hL hc
  have := xuG_nonneg (sys := sys) (L := L) (Hunit := Hunit)
  have := cGt_nonneg (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
    (coulombCellAmplitude_pos hL).le hc
  have := CtW_nonneg sys hL Hunit zero_le_one
  have := gF_pos hL
  positivity

lemma fG_grid_nonneg (hL : 0 < L) : 0 ≤ fG_grid sys L Hunit := by
  unfold fG_grid
  have := Zc_nonneg (P := regParticlesOf sys) (D := (posNucleiOf sys.nuclei).toNucData)
    (coulombCellAmplitude_pos hL).le
  have := cAbs_nonneg sys Hunit hL
  have := xuG_nonneg (sys := sys) (L := L) (Hunit := Hunit)
  have := CtW_nonneg sys hL Hunit zero_le_one
  have := gF_pos hL
  positivity

/-- **`δ_raw ≤ δ_G/K³`** for `m ≥ 8`. -/
theorem dRawG_le (hL : 0 < L) {c : ℝ} (hc : 0 ≤ c) {m : ℕ} (hm : 8 ≤ m) (hK1 : 1 ≤ gF L * m) :
    dRawG sys L Hunit c m ≤ dG_grid sys L Hunit c / (gF L * m) ^ 3 := by
  have hg := gF_pos hL
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hK0 : 0 < gF L * m := by positivity
  have hA := formA_quarter_le (L := L) hL hm
  have hU := tuG_le sys Hunit hL hm
  have hV := tvG_le sys hL hc hm
  have hT := t2G_le sys Hunit hL hm
  have hW := wvG_le sys Hunit hL hc hm
  have hZ := Zc_nonneg (P := regParticlesOf sys) (D := (posNucleiOf sys.nuclei).toNucData)
    (coulombCellAmplitude_pos hL).le
  have hA0 := formA_nonneg (m / 4) m
  have hU0 := tuG_nonneg (sys := sys) (Hunit := Hunit) hL m
  have hV0 := tvG_nonneg (sys := sys) hL hc m
  have hT0 := t2G_nonneg (sys := sys) (Hunit := Hunit) hL m
  have hW0 := wvG_nonneg (sys := sys) (Hunit := Hunit) hL hc m
  have hXv := xvG_nonneg (sys := sys) hL hc
  have hXu := xuG_nonneg (sys := sys) (L := L) (Hunit := Hunit)
  have hcA := cAbs_nonneg sys Hunit hL
  have hcG := cGt_nonneg (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (2 * Real.pi / L)
    (coulombCellAmplitude_pos hL).le hc
  have hCt := CtW_nonneg sys hL Hunit zero_le_one
  unfold dG_grid
  set Zg := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
  set cA := cAbs sys L Hunit
  set cG := cGt (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
    (2 * Real.pi / L) c
  set Xv := xvG sys L c
  set Xu := xuG sys L Hunit
  set Ct := CtW sys L Hunit 1
  set sK := Real.sqrt (gF L * m) with hsK
  set sg := Real.sqrt (gF L) with hsg
  have hsK0 : 0 < sK := Real.sqrt_pos.mpr hK0
  have hsg0 : 0 < sg := Real.sqrt_pos.mpr hg
  have hsK2 : sK ^ 2 = gF L * m := Real.sq_sqrt hK0.le
  have hsg2 : sg ^ 2 = gF L := Real.sq_sqrt hg.le
  have hsK1 : 1 ≤ sK := by
    rw [hsK]
    exact Real.one_le_sqrt.mpr hK1
  -- step 1: the component bounds
  have step1 : dRawG sys L Hunit c m ≤ Zg * (390 * sg / sK *
      (192 * cA / ((gF L * m) ^ 2 * sK) * Xv + 192 * sg * cG / ((gF L * m) ^ 2 * sK) * Xu) +
        52 * m * (192 * sg * cG / ((gF L * m) ^ 2 * sK) * (192 * cA / ((gF L * m) ^ 2 * sK)))) +
      cA / ((gF L * m) ^ 2 * sK) * (eta * Ct * ((1 + gF L ^ 2) * Xv) / sK) := by
    unfold dRawG
    gcongr
  refine step1.trans ?_
  -- step 2: the algebra, with `K = sK²`, `g = sg²`, `m = sK²/sg²`
  have hm_eq : (m : ℝ) = sK ^ 2 / sg ^ 2 := by
    rw [hsK2, hsg2]
    field_simp
  have hgK : gF L * (m : ℝ) = sK ^ 2 := hsK2.symm
  rw [hgK, hm_eq, ← hsg2]
  have hX : 0 ≤ Zg * (1916928 * cG * cA) := by positivity
  have e1 : Zg * (390 * sg / sK * (192 * cA / ((sK ^ 2) ^ 2 * sK) * Xv +
      192 * sg * cG / ((sK ^ 2) ^ 2 * sK) * Xu) + 52 * (sK ^ 2 / sg ^ 2) *
        (192 * sg * cG / ((sK ^ 2) ^ 2 * sK) * (192 * cA / ((sK ^ 2) ^ 2 * sK)))) +
      cA / ((sK ^ 2) ^ 2 * sK) * (eta * Ct * ((1 + (sg ^ 2) ^ 2) * Xv) / sK) =
      (Zg * (74880 * sg * cA * Xv + 74880 * sg ^ 2 * cG * Xu) +
        cA * (eta * Ct * ((1 + (sg ^ 2) ^ 2) * Xv))) / (sK ^ 2) ^ 3 +
      Zg * (1916928 * cG * cA) / sg / (sK ^ 2) ^ 4 := by
    field_simp
    ring
  rw [e1]
  have h4 : Zg * (1916928 * cG * cA) / sg / (sK ^ 2) ^ 4 ≤
      Zg * (1916928 * cG * cA) / sg / (sK ^ 2) ^ 3 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : (1 : ℝ) ≤ sK ^ 2 := by nlinarith
    calc (sK ^ 2) ^ 3 = (sK ^ 2) ^ 3 * 1 := by ring
      _ ≤ (sK ^ 2) ^ 3 * sK ^ 2 := by gcongr
      _ = (sK ^ 2) ^ 4 := by ring
  calc (Zg * (74880 * sg * cA * Xv + 74880 * sg ^ 2 * cG * Xu) +
        cA * (eta * Ct * ((1 + (sg ^ 2) ^ 2) * Xv))) / (sK ^ 2) ^ 3 +
        Zg * (1916928 * cG * cA) / sg / (sK ^ 2) ^ 4
      ≤ (Zg * (74880 * sg * cA * Xv + 74880 * sg ^ 2 * cG * Xu) +
        cA * (eta * Ct * ((1 + (sg ^ 2) ^ 2) * Xv))) / (sK ^ 2) ^ 3 +
        Zg * (1916928 * cG * cA) / sg / (sK ^ 2) ^ 3 := by linarith
    _ = _ := by
        field_simp
        ring

set_option maxHeartbeats 1000000 in
/-- **`F_raw ≤ F_G/√K`** for `m ≥ 8` and `K ≥ 1`. -/
theorem fRawG_le (hL : 0 < L) {m : ℕ} (hm : 8 ≤ m) (hK1 : 1 ≤ gF L * m) :
    fRawG sys L Hunit m ≤ fG_grid sys L Hunit / Real.sqrt (gF L * m) := by
  have hg := gF_pos hL
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hK0 : 0 < gF L * m := by positivity
  have hA := formA_quarter_le (L := L) hL hm
  have hU := tuG_le sys Hunit hL hm
  have hT := t2G_le sys Hunit hL hm
  have hZ := Zc_nonneg (P := regParticlesOf sys) (D := (posNucleiOf sys.nuclei).toNucData)
    (coulombCellAmplitude_pos hL).le
  have hA0 := formA_nonneg (m / 4) m
  have hU0 := tuG_nonneg (sys := sys) (Hunit := Hunit) hL m
  have hT0 := t2G_nonneg (sys := sys) (Hunit := Hunit) hL m
  have hXu := xuG_nonneg (sys := sys) (L := L) (Hunit := Hunit)
  have hcA := cAbs_nonneg sys Hunit hL
  have hCt := CtW_nonneg sys hL Hunit zero_le_one
  have h2m : Real.sqrt (gF L * m) ≤ Real.sqrt (gF L * ((2 * m : ℕ) : ℝ)) := by
    refine Real.sqrt_le_sqrt ?_
    push_cast
    nlinarith
  unfold fG_grid
  set Zg := Zc (regParticlesOf sys) (posNucleiOf sys.nuclei).toNucData (coulombCellAmplitude L)
  set cA := cAbs sys L Hunit
  set Xu := xuG sys L Hunit
  set Ct := CtW sys L Hunit 1
  set sK := Real.sqrt (gF L * m) with hsK
  set sg := Real.sqrt (gF L) with hsg
  have hsK0 : 0 < sK := Real.sqrt_pos.mpr hK0
  have hsg0 : 0 < sg := Real.sqrt_pos.mpr hg
  have hsK2 : sK ^ 2 = gF L * m := Real.sq_sqrt hK0.le
  have hsg2 : sg ^ 2 = gF L := Real.sq_sqrt hg.le
  have hsK1 : 1 ≤ sK := by
    rw [hsK]
    exact Real.one_le_sqrt.mpr hK1
  have step1 : fRawG sys L Hunit m ≤ Zg * (390 * sg / sK *
      (192 * cA / ((gF L * m) ^ 2 * sK) * (1 + 12 * eta * (m : ℝ) ^ 2) + Xu) +
        52 * m * (192 * cA / ((gF L * m) ^ 2 * sK))) +
      cA / ((gF L * m) ^ 2 * sK) * (eta * Ct * ((1 + gF L ^ 2) *
        (1 + 12 * eta * (m : ℝ) ^ 2))) / sK := by
    unfold fRawG
    gcongr
  refine step1.trans ?_
  have hm_eq : (m : ℝ) = sK ^ 2 / sg ^ 2 := by
    rw [hsK2, hsg2]
    field_simp
  have hgK : gF L * (m : ℝ) = sK ^ 2 := hsK2.symm
  rw [hgK, hm_eq, ← hsg2]
  have e1 : Zg * (390 * sg / sK * (192 * cA / ((sK ^ 2) ^ 2 * sK) *
      (1 + 12 * eta * (sK ^ 2 / sg ^ 2) ^ 2) + Xu) +
        52 * (sK ^ 2 / sg ^ 2) * (192 * cA / ((sK ^ 2) ^ 2 * sK))) +
      cA / ((sK ^ 2) ^ 2 * sK) * (eta * Ct * ((1 + (sg ^ 2) ^ 2) *
        (1 + 12 * eta * (sK ^ 2 / sg ^ 2) ^ 2))) / sK =
      Zg * (74880 * sg * cA) / sK ^ 6 + Zg * (898560 * eta * cA) / (sg ^ 3 * sK ^ 2) +
        Zg * (390 * sg * Xu) / sK + Zg * (9984 * cA) / (sg ^ 2 * sK ^ 3) +
        cA * (eta * Ct * (1 + (sg ^ 2) ^ 2)) / sK ^ 6 +
        cA * (eta * Ct * (1 + (sg ^ 2) ^ 2)) * (12 * eta) / ((sg ^ 2) ^ 2 * sK ^ 2) := by
    field_simp
    ring
  rw [e1]
  have hp : ∀ k : ℕ, 1 ≤ k → ∀ P : ℝ, 0 ≤ P → P / sK ^ k ≤ P / sK := by
    intro k hk P hP
    apply div_le_div_of_nonneg_left hP hsK0
    calc sK = sK ^ 1 := (pow_one sK).symm
      _ ≤ sK ^ k := pow_le_pow_right₀ hsK1 hk
  have hη : (0 : ℝ) ≤ eta := Nat.cast_nonneg _
  have t1 := hp 6 (by norm_num) (Zg * (74880 * sg * cA)) (by positivity)
  have t2 : Zg * (898560 * eta * cA) / (sg ^ 3 * sK ^ 2) ≤
      Zg * (898560 * eta * cA) / sg ^ 3 / sK := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : sK ≤ sK ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have t4 : Zg * (9984 * cA) / (sg ^ 2 * sK ^ 3) ≤ Zg * (9984 * cA) / sg ^ 2 / sK := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : sK ≤ sK ^ 3 := by
      calc sK = sK ^ 1 := (pow_one sK).symm
        _ ≤ sK ^ 3 := pow_le_pow_right₀ hsK1 (by norm_num)
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have t5 := hp 6 (by norm_num) (cA * (eta * Ct * (1 + (sg ^ 2) ^ 2))) (by positivity)
  have t6 : cA * (eta * Ct * (1 + (sg ^ 2) ^ 2)) * (12 * eta) / ((sg ^ 2) ^ 2 * sK ^ 2) ≤
      cA * (eta * Ct * (1 + (sg ^ 2) ^ 2)) * (12 * eta) / (sg ^ 2) ^ 2 / sK := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : sK ≤ sK ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hfin : Zg * (74880 * sg * cA) / sK + Zg * (898560 * eta * cA) / sg ^ 3 / sK +
      Zg * (390 * sg * Xu) / sK + Zg * (9984 * cA) / sg ^ 2 / sK +
      cA * (eta * Ct * (1 + (sg ^ 2) ^ 2)) / sK +
      cA * (eta * Ct * (1 + (sg ^ 2) ^ 2)) * (12 * eta) / (sg ^ 2) ^ 2 / sK =
      (Zg * (74880 * sg * cA * (1 + 12 * eta / (sg ^ 2) ^ 2) + 390 * sg * Xu +
        9984 * cA / sg ^ 2) + cA * (eta * Ct * ((1 + (sg ^ 2) ^ 2) *
          (1 + 12 * eta / (sg ^ 2) ^ 2)))) / sK := by
    field_simp
    ring
  linarith

end Rates

end KineticLog
