import PlaneWave.Source.CutoffLedger

/-!
# Flux/source build, block 5: the cutoff dependence of the budgets and of the error constant

`err(n, t) = E₀(n) + t E₁(n)` (`errC_eq`) with

* `E₀ = C_red + δ_rot (m_χ + m_rot) + δ_r (m_r + m_N) + T₂ + T₄ + T₅ = O(n^{-3} polylog)`;
* `E₁ = m_rot m_w L + src + f_c C_Acorr m_V = O(n^{max(2s, s₁, 2s₂) - 9/2} polylog)`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSAsymp

open FSNormal PL

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (Hunit : ℝ) (heta : 0 < eta)

/-! ## The trajectory defects -/

include hL in
theorem pl_rhoC : PL (fun n => rhoC sys L Hunit n) (-5 / 2) := by
  have h := (lin_rpow (gF_pos hL).le (-(5 / 2 : ℝ))).const_mul (eta * cTr sys L Hunit)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold rhoC; ring

include hL in
theorem pl_omC : PL (fun n => omC sys L Hunit n) (-3 / 2) := by
  have h := (lin_rpow (gF_pos hL).le (-(3 / 2 : ℝ))).const_mul
    (Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold omC; ring

include hL in
theorem pl_rhoT : PL (fun n => rhoT sys L Hunit n) (-5 / 2) := by
  have hA := pl_Asig sys (L := L)
  have ha0 := (pl_a0c sys (L := L)).mul_const (cTr sys L Hunit)
  have hr := pl_rhoC sys hL Hunit
  have h := (hr.add ha0).add_le (hA.mul (ha0.add_le (hA.mul hr) (r := -5 / 2) le_rfl (by norm_num)))
    (r := -5 / 2) le_rfl (by norm_num)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold rhoT; ring

include hL in
theorem pl_omT : PL (fun n => omT sys L Hunit n) (-3 / 2) := by
  have hA := pl_Asig sys (L := L)
  have ha0 := (pl_a0c sys (L := L)).mul_const (cTr sys L Hunit)
  have ha1 := ((pl_a1c sys (L := L)).mul_const (cTr sys L Hunit)).const_mul
    (finiteCoulombPhysicalMassConstant sys L Hunit)
  have hr := pl_rhoC sys hL Hunit
  have h := ((pl_omC sys hL Hunit).add ha1).add_le ((pl_CZ sys Hunit (L := L)).mul
    (ha0.add_le (hA.mul hr) (r := -5 / 2) le_rfl (by norm_num))) (r := -3 / 2) le_rfl (by norm_num)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold omT; ring

include hL in
theorem pl_dA : PL (fun n => dA sys L Hunit n) (-7 / 2) := by
  have hA := pl_Asig sys (L := L)
  have ha0 := (pl_a0c sys (L := L)).mul_const (cTr sys L Hunit)
  have hr := pl_rhoC sys hL Hunit
  have h := hA.mul_le (hr.add (ha0.add_le (hA.mul hr) (r := -5 / 2) le_rfl (by norm_num)))
    (r := -7 / 2) (by norm_num)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold dA; ring

omit [Fintype ν] in
include hL in
theorem pl_Kqpow {r : ℝ} (hr : 0 ≤ r) : PL (fun n => (1 + Kq L n) ^ r) r := by
  have h := ((const 1).add_le (lin (Real.sqrt 3 * gF L)) (r := 1) (by norm_num) le_rfl).rpow
    ⟨0, fun n _ => by have := gF_pos hL; positivity⟩ hr
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (le_of_eq (by ring))
  unfold Kq; ring_nf

omit [Fintype ν] in
include hL in
theorem pl_pertF {δ : ℕ → ℝ} {q : ℝ} (hδ : PL δ q) : PL (fun n => pertF eta L n (δ n)) (q + 5 / 2) := by
  have t1 := hδ.mul (pl_Kqpow hL (r := 5 / 2) (by norm_num))
  have t2 := (((const 1).add_le (pl_Amax (eta := eta) (L := L)) (r := 2) (by norm_num) le_rfl).mul hδ).mul_le
    (pl_Kqpow hL (r := 1 / 2) (by norm_num)) (r := q + 5 / 2) (by linarith)
  have h := t1.add t2
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL in
theorem pl_mA : PL (fun n => mA sys L Hunit n) 0 := by
  have h := (const (2 * cTr sys L Hunit)).add_le (pl_pertF hL (eta := eta) (pl_dA sys hL Hunit))
    (r := 0) le_rfl (by norm_num)
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL in
theorem pl_eps0chi : PL (fun n => eps0chi sys L Hunit n) (-1) := by
  have hAV := (pl_Amax (eta := eta) (L := L)).add_le (pl_CVN sys Hunit (L := L)) (r := 2) le_rfl
    (by norm_num)
  have h := ((hAV.mul (pl_dA sys hL Hunit)).add_le ((pl_alphaD sys Hunit (L := L)).mul (pl_mA sys hL Hunit))
    (r := -1) (by norm_num) (by norm_num)).add_le (pl_omC sys hL Hunit) (r := -1) le_rfl (by norm_num)
  exact h.congr ⟨0, fun n _ => rfl⟩

/-! ## The goodness budgets -/

/-- `Mdec` of bounded arguments with decaying defects is bounded. -/
theorem pl_Mdec {a b e d : ℕ → ℝ} (ha : PL a 0) (hb : PL b 0) (he : PL e (-1 / 2))
    (hd : PL d (-1 / 2)) : PL (fun n => Mdec sys L Hunit n (a n) (b n) (e n) (d n)) 0 := by
  have hsq : PL (fun n => Real.sqrt (1 + Real.sqrt 3 * (gF L * n))) (1 / 2) := by
    have := ((const 1).add_le (lin (Real.sqrt 3 * gF L)) (r := 1) (by norm_num) le_rfl).sqrt
    refine (this.congr ⟨0, fun n _ => by ring_nf⟩).mono (by norm_num)
  have t1 := (hb.const_mul (2 * sys.maxMass)).add_le ((he.add hd).mul hsq) (r := 0) le_rfl (by norm_num)
  have t2 := (ha.const_mul (CtW sys L Hunit 1 * (3 * sys.maxMass))).add
    (ha.const_mul (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L)))
  have h := (ha.const_mul 2).add ((t1.add t2).const_mul (2 * sys.maxMass + 1))
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold Mdec
  rw [CtW_eq_mul sys Hunit (3 * sys.maxMass * a n)]
  ring

include hL in
theorem pl_mChi : PL (fun n => mChi sys L Hunit n) 0 := by
  have hCD := pl_CDelta sys Hunit (L := L)
  have hCfl := pl_Cfl sys Hunit hCD (L := L)
  have hmA := pl_mA sys hL Hunit
  have h := pl_Mdec sys Hunit (L := L) (hCfl.mul_le hmA (r := 0) (by norm_num))
    (hCfl.mul_const (cvT sys L Hunit)) ((pl_eps0chi sys hL Hunit).mono (by norm_num))
    (((pl_alphaD sys Hunit (L := L)).mul (hCfl.mul hmA)).mono (by norm_num))
  exact h.congr ⟨0, fun n _ => rfl⟩

section Beta

variable {β : ℕ → ℝ} (hβ : PL β (-3))

include hL hβ in
theorem pl_dRot (s : ℝ) : PL (fun n => dRot sys L Hunit n s (β n)) (-3) := by
  have h := ((pl_z2uC sys hL Hunit s).add hβ).mul_le (pl_mChi sys hL Hunit) (r := -3) (by norm_num)
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL hβ in
theorem pl_mRot (s : ℝ) : PL (fun n => mRot sys L Hunit n s (β n)) 0 := by
  have h := (pl_mChi sys hL Hunit).add_le (pl_pertF hL (eta := eta) (pl_dRot sys hL Hunit hβ s))
    (r := 0) le_rfl (by norm_num)
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL in
theorem pl_mN : PL (fun n => mN sys L Hunit n) 0 := by
  have h := pl_Mdec sys Hunit (L := L) (const (Cfl sys L Hunit 0 * (2 * cTr sys L Hunit)))
    (const (Cfl sys L Hunit 0 * cvT sys L Hunit)) ((pl_omC sys hL Hunit).mono (by norm_num))
    (zero (p := -1 / 2))
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL hβ in
theorem pl_dRot0 (s : ℝ) : PL (fun n => dRot0 sys L Hunit n s (β n)) (-3) := by
  have h := ((pl_z2uC sys hL Hunit s).add hβ).mul_le (pl_mA sys hL Hunit) (r := -3) (by norm_num)
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL hβ in
theorem pl_dR (s : ℝ) : PL (fun n => dR sys L Hunit n s (β n)) (-3) := by
  have h := (pl_dRot0 sys hL Hunit hβ s).add_le (pl_dA sys hL Hunit) (r := -3) le_rfl (by norm_num)
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL hβ in
theorem pl_mNr (s : ℝ) : PL (fun n => mNr sys L Hunit n s (β n)) 0 := by
  have hA1 := (const 1).add_le (pl_Amax (eta := eta) (L := L)) (r := 2) (by norm_num) le_rfl
  have hAV := (pl_Amax (eta := eta) (L := L)).add_le (pl_CVN sys Hunit (L := L)) (r := 2) le_rfl
    (by norm_num)
  have ha := ((pl_mA sys hL Hunit).add_le (hA1.mul (pl_dRot0 sys hL Hunit hβ s)) (r := 0) le_rfl
    (by norm_num)).const_mul (Cfl sys L Hunit 0)
  have he := (hAV.mul (pl_dR sys hL Hunit hβ s)).add_le (pl_omC sys hL Hunit) (r := -1 / 2)
    (by norm_num) (by norm_num)
  have h := pl_Mdec sys Hunit (L := L) ha (const (Cfl sys L Hunit 0 * cvT sys L Hunit)) he
    (zero (p := -1 / 2))
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL hβ in
theorem pl_mW (s : ℝ) : PL (fun n => mW sys L Hunit n s (β n)) 0 :=
  ((pl_mRot sys hL Hunit hβ s).add (pl_mNr sys hL Hunit hβ s)).congr ⟨0, fun _ _ => rfl⟩

end Beta

include hL in
theorem pl_mV : PL (fun n => mV sys L Hunit n) 0 :=
  ((pl_mA sys hL Hunit).add (pl_mChi sys hL Hunit)).congr ⟨0, fun _ _ => rfl⟩

/-! ## The source and the nonsecular constants -/

include hL in
theorem pl_fC : PL (fun n => fC sys L Hunit n) (-3 / 2) := by
  have hA := pl_Asig sys (L := L)
  have hZ := pl_CZ sys Hunit (L := L)
  have hX := pl_CX sys Hunit (L := L)
  have hc := ((hZ.const_mul 2).add_le ((hA.const_mul 2).mul hZ) (r := 0) le_rfl (by norm_num)).add_le
    (((hA.pow 2).const_mul 4).mul hX) (r := 0) le_rfl (by norm_num)
  have h := (pl_omT sys hL Hunit).add_le (hc.mul (pl_rhoT sys hL Hunit)) (r := -3 / 2) le_rfl
    (by norm_num)
  exact h.congr ⟨0, fun n _ => rfl⟩

theorem pl_CAcorr : PL (fun n => CAcorr sys L n) (-3 / 2) := by
  have hA := pl_Asig sys (L := L)
  have ha0 := pl_a0c sys (L := L)
  have hE := pl_E0 sys (L := L)
  have t1 := ((hE.mul ((const 1).add_le (hA.pow 2) (r := 0) le_rfl (by norm_num))).mul
    ((hA.const_mul 2).mul ha0)).mono (q := -3 / 2) (by norm_num)
  have t2 := ((hA.mul ha0).mul ((const 1).add_le hE (r := 2) (by norm_num) le_rfl)).mono
    (q := -3 / 2) (by norm_num)
  have h := t1.add t2
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL in
/-- **The source constant**. -/
theorem pl_srcC {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) (hs₂ : 1 / 4 ≤ s₂) :
    PL (fun n => srcC sys L Hunit n s₁ s₂) (max (s₁ - 9 / 2) (max (2 * s₂ - 9 / 2) (-3))) := by
  have hCD := pl_CDelta sys Hunit (L := L)
  have hCD0 : ∀ n, 0 ≤ CDelta sys L Hunit n := fun n => CDelta_nonneg sys hL Hunit
  have hmV := pl_mV sys hL Hunit
  have hT := pl_Ctavg sys Hunit hCD hCD0 (L := L) hs₁
  set R := max (s₁ - 9 / 2) (max (2 * s₂ - 9 / 2) (-3))
  have hR1 : s₁ - 9 / 2 ≤ R := le_max_left _ _
  have hR2 : 2 * s₂ - 9 / 2 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR3 : (-3 : ℝ) ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  have t1 := (((((pl_omT sys hL Hunit).mul hmV).mul hT.sqrt).mul (pl_Kc hL (s₁ - 3))).mul
    (pl_DKpow hL hs₁)).mono (q := R) (by linarith)
  have t2 := (((pl_Asig sys (L := L)).mul (pl_rhoT sys hL Hunit)).mul
    (((pl_CflS sys Hunit hCD hCD0 (L := L) (σ := 1 / 2) (by norm_num)).mul
      (hmV.mul (pl_momF sys hL (1 / 2)))).const_mul
      (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit))).mono (q := R) (by linarith)
  have t3 := ((pl_omT sys hL Hunit).mul (((pl_cSt sys (L := L) s₂).mul_const (cE sys L ^ s₂)).mul
    ((pl_CflS sys Hunit hCD hCD0 (L := L) (σ := s₂) (by linarith)).mul
      (hmV.mul (pl_momF sys hL s₂))))).mono (q := R) (by linarith)
  have t4 := (((((pl_Asig sys (L := L)).const_mul 2).mul (pl_CZ sys Hunit (L := L))).add_le
    ((((pl_Asig sys (L := L)).pow 2).const_mul 4).mul (pl_CX sys Hunit (L := L))) (r := -1) (by norm_num)
      (by norm_num)).mul ((pl_rhoT sys hL Hunit).mul hmV)).mono (q := R) (by linarith)
  have h := t1.add ((t2.add t3).add t4)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold srcC; ring

include hL in
theorem pl_T2C : PL (fun n => T2C sys L Hunit n) (-7 / 2) := by
  have hA := pl_Asig sys (L := L)
  have hm := pl_mChi sys hL Hunit
  have hx := hA.mul (((pl_a0c sys (L := L)).const_mul 2).mul hm)
  have t1 := ((hx.const_mul 2).mul hm).mono (q := -7 / 2) (by norm_num)
  have t2 := ((pl_E0 sys (L := L)).mul (hx.pow 2)).mono (q := -7 / 2) (by norm_num)
  have h := t1.add t2
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL in
theorem pl_T4C : PL (fun n => T4C sys L Hunit n) (-5) := by
  have h := (pl_E0 sys (L := L)).mul (((pl_Asig sys (L := L)).mul (pl_rhoT sys hL Hunit)).pow 2)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

include hL in
theorem pl_T5C : PL (fun n => T5C sys L Hunit n) (-7 / 2) := by
  have h1 := (const 1).add_le (((pl_E0 sys (L := L)).const_mul 2).mul (pl_a0c sys (L := L))) (r := 0)
    le_rfl (by norm_num)
  have h := ((h1.mul (pl_mA sys hL Hunit)).mul ((pl_Asig sys (L := L)).mul (pl_rhoT sys hL Hunit))).const_mul 2
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold T5C; ring

include hL heta in
theorem pl_redC : PL (fun n => redC sys L Hunit n) (-3) := by
  have h := ((const (cTr sys L Hunit ^ 2)).add (((pl_mN sys hL Hunit).pow 2).mono (by norm_num))).mul
    ((pl_Kc4 hL (-(3 : ℝ))).add (pl_lamE sys hL heta (-(3 : ℝ))))
  refine ((h.const_mul (eta : ℝ)).congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold redC; ring

/-! ## The error constant -/

/-- The time-independent part of the error constant. -/
noncomputable def E0err (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s β : ℝ) : ℝ :=
  redC sys L Hunit n + dRot sys L Hunit n s β * (mChi sys L Hunit n + mRot sys L Hunit n s β) +
    dR sys L Hunit n s β * (mNr sys L Hunit n s β + mN sys L Hunit n) + T2C sys L Hunit n +
    T4C sys L Hunit n + T5C sys L Hunit n

/-- The secular part of the error constant. -/
noncomputable def E1err (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s s₁ s₂ z3 β : ℝ) : ℝ :=
  mRot sys L Hunit n s β * (mW sys L Hunit n s β * ledC sys L Hunit n s z3 β) +
    srcC sys L Hunit n s₁ s₂ + fC sys L Hunit n * (CAcorr sys L n * mV sys L Hunit n)

lemma errC_eq (n : ℕ) (s s₁ s₂ z3 β t : ℝ) :
    errC sys L Hunit n s s₁ s₂ z3 β t =
      E0err sys L Hunit n s β + t * E1err sys L Hunit n s s₁ s₂ z3 β := by
  unfold errC T1C T3C E0err E1err; ring

section Final

variable {z3 β : ℕ → ℝ} (hz3 : PL z3 (-2)) (hβ : PL β (-3))

include hL heta hβ in
theorem pl_E0err (s : ℝ) : PL (fun n => E0err sys L Hunit n s (β n)) (-3) := by
  have t1 := (pl_dRot sys hL Hunit hβ s).mul_le ((pl_mChi sys hL Hunit).add (pl_mRot sys hL Hunit hβ s))
    (r := -3) (by norm_num)
  have t2 := (pl_dR sys hL Hunit hβ s).mul_le ((pl_mNr sys hL Hunit hβ s).add (pl_mN sys hL Hunit))
    (r := -3) (by norm_num)
  have h := ((((pl_redC sys hL Hunit heta).add t1).add t2).add_le (pl_T2C sys hL Hunit) (r := -3) le_rfl
    (by norm_num)).add_le (pl_T4C sys hL Hunit) (r := -3) le_rfl (by norm_num) |>.add_le
    (pl_T5C sys hL Hunit) (r := -3) le_rfl (by norm_num)
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL heta hz3 hβ in
theorem pl_E1err {s s₁ s₂ : ℝ} (hs : 3 / 4 ≤ s) (hs₁ : 0 ≤ s₁) (hs₂ : 1 / 4 ≤ s₂) :
    PL (fun n => E1err sys L Hunit n s s₁ s₂ (z3 n) (β n))
      (max (2 * s - 9 / 2) (max (s₁ - 9 / 2) (max (2 * s₂ - 9 / 2) (-3)))) := by
  set R := max (2 * s - 9 / 2) (max (s₁ - 9 / 2) (max (2 * s₂ - 9 / 2) (-3)))
  have hR0 : 2 * s - 9 / 2 ≤ R := le_max_left _ _
  have hR1 : max (s₁ - 9 / 2) (max (2 * s₂ - 9 / 2) (-3)) ≤ R := le_max_right _ _
  have hR3 : (-3 : ℝ) ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hR1
  have t1 := (pl_mRot sys hL Hunit hβ s).mul_le ((pl_mW sys hL Hunit hβ s).mul
    (pl_ledC sys hL Hunit heta hz3 hβ hs)) (r := R) (by linarith)
  have t2 := (pl_srcC sys hL Hunit hs₁ hs₂).mono hR1
  have t3 := (pl_fC sys hL Hunit).mul_le ((pl_CAcorr sys (L := L)).mul (pl_mV sys hL Hunit))
    (r := R) (by linarith)
  have h := (t1.add t2).add t3
  exact h.congr ⟨0, fun n _ => rfl⟩

end Final

end FSAsymp
