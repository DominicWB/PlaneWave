import PlaneWave.Source.CutoffBasicConstants

/-!
# Flux/source build, block 5: the cutoff dependence of the scales and the derived constants

Linear scales (`Λ`, `λ_E`, `l_H`, `K`), the logarithmic factors (`D_K`, `N_Λ`, `J_n`, `C_res`), the
generator constants (`z_b`, `C_Zws`, `c_s`, `z₂`, `z₂ᵤ`), the relative constants
(`α_bb`, `α_mix`, `α_Δ`, `α₃`, `α₄`, `z_c`, `g_u`, `w_s`) and the flow constants at a
bounded `C_Δ(n)`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSAsymp

open FSNormal PL

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (Hunit : ℝ)

/-! ## Linear scales -/

omit [Fintype ν] in
include hL in
lemma Lam_eq (n : ℕ) : Lam sys L n = gL L / Real.sqrt 2048 * n := by
  have hg := gL_pos hL
  have hm : 0 < mmax sys := lt_of_lt_of_le one_pos (one_le_mmax sys)
  have hs : (gL L / Real.sqrt 2048 * n) ^ 2 = gL L ^ 2 * (n : ℝ) ^ 2 / 2048 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num)]; ring
  have e : 2 * mmax sys * E0 sys L n = (gL L / Real.sqrt 2048 * n) ^ 2 := by
    rw [hs]; unfold E0 Kc; field_simp; ring
  unfold Lam
  rw [e, Real.sqrt_sq (by positivity)]

omit [Fintype ν] in
include hL in
theorem pl_Lam (r : ℝ) : PL (fun n => Lam sys L n ^ r) r := by
  have h := lin_rpow (show (0 : ℝ) ≤ gL L / Real.sqrt 2048 by have := gL_pos hL; positivity) r
  exact h.congr ⟨0, fun n _ => by rw [Lam_eq sys hL]⟩

omit [Fintype ν] in
include hL in
lemma lamE_eq (heta : 0 < eta) (n : ℕ) :
    lamE sys L n = gL L / Real.sqrt (2048 * mmax sys * eta) * n := by
  have hg := gL_pos hL
  have hm : 0 < mmax sys := lt_of_lt_of_le one_pos (one_le_mmax sys)
  have he : (0 : ℝ) < eta := by exact_mod_cast heta
  have hs : (gL L / Real.sqrt (2048 * mmax sys * eta) * n) ^ 2 =
      gL L ^ 2 * (n : ℝ) ^ 2 / (2048 * mmax sys * eta) := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity)]; ring
  have e : 2 * E0 sys L n / eta = (gL L / Real.sqrt (2048 * mmax sys * eta) * n) ^ 2 := by
    rw [hs]; unfold E0 Kc; field_simp; ring
  unfold lamE
  rw [e, Real.sqrt_sq (by positivity)]

omit [Fintype ν] in
include hL in
theorem pl_lamE (heta : 0 < eta) (r : ℝ) : PL (fun n => lamE sys L n ^ r) r := by
  have h := lin_rpow (show (0 : ℝ) ≤ gL L / Real.sqrt (2048 * mmax sys * eta) by
    have := gL_pos hL; positivity) r
  exact h.congr ⟨0, fun n _ => by rw [lamE_eq sys hL heta]⟩

omit [Fintype ν] in
include hL in
lemma lH_eq (heta : 0 < eta) (n : ℕ) :
    lH sys L n = gF L / Real.sqrt (32 * mtop sys * eta) * n := by
  have hg := gF_pos hL
  have hm : 0 < mtop sys := lt_of_lt_of_le one_pos (one_le_mtop sys)
  have he : (0 : ℝ) < eta := by exact_mod_cast heta
  have hs : (gF L / Real.sqrt (32 * mtop sys * eta) * n) ^ 2 =
      gF L ^ 2 * (n : ℝ) ^ 2 / (32 * mtop sys * eta) := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by positivity)]; ring
  have e : 2 * eH sys L n / eta = (gF L / Real.sqrt (32 * mtop sys * eta) * n) ^ 2 := by
    rw [hs]; unfold eH; field_simp; ring
  unfold lH
  rw [e, Real.sqrt_sq (by positivity)]

omit [Fintype ν] in
include hL in
theorem pl_highF (heta : 0 < eta) : PL (fun n => highF sys L n) (-5 / 2) := by
  have h := (lin_rpow (show (0 : ℝ) ≤ gF L / Real.sqrt (32 * mtop sys * eta) by
    have := gF_pos hL; positivity) (-(5 / 2 : ℝ))).const_mul (eta : ℝ)
  refine (h.congr ⟨0, fun n _ => by unfold highF; rw [lH_eq sys hL heta]⟩).mono (by norm_num)

omit [Fintype ν] in
include hL in
theorem pl_hotF : PL (fun n => hotF eta L n) (-5 / 2) := by
  have h := (pl_Kc4 hL (-(5 / 2 : ℝ))).const_mul (eta : ℝ)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

omit [Fintype ν] in
include hL in
/-- `√(2 m_max e_H)` is linear in `n`. -/
theorem pl_sqrt_eH (r : ℝ) : PL (fun n => Real.sqrt (2 * mmax sys * eH sys L n) ^ r) r := by
  have hg := gF_pos hL
  have hm : 0 < mmax sys := lt_of_lt_of_le one_pos (one_le_mmax sys)
  have hmt : 0 < mtop sys := lt_of_lt_of_le one_pos (one_le_mtop sys)
  have h := lin_rpow (show (0 : ℝ) ≤ Real.sqrt (2 * mmax sys * (gF L ^ 2 / (64 * mtop sys))) by
    positivity) r
  refine h.congr ⟨0, fun n _ => ?_⟩
  have e : 2 * mmax sys * eH sys L n =
      (Real.sqrt (2 * mmax sys * (gF L ^ 2 / (64 * mtop sys))) * n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    unfold eH; ring
  rw [e, Real.sqrt_sq (by positivity)]

/-! ## Logarithmic factors -/

omit [Fintype ν] in
include hL in
theorem pl_DK : PL (fun n => DK (Kc L n)) 0 := by
  have h := ((log_lin (a := 2) (b := gL L) (by norm_num) (gL_pos hL).le).const_mul 6).sqrt
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

omit [Fintype ν] in
include hL in
theorem pl_DKpow {s : ℝ} (hs : 0 ≤ s) : PL (fun n => (1 + DK (Kc L n)) ^ s) 0 := by
  have h := ((const 1).add' (pl_DK hL)).rpow ⟨0, fun n _ => by
    have := DK_nonneg (Kc L n); positivity⟩ hs
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

omit [Fintype ν] in
include hL in
theorem pl_NL : PL (fun n => (NL sys L n : ℝ)) 0 := by
  have hc : 0 < gL L / Real.sqrt 2048 := by have := gL_pos hL; positivity
  have h := natlog_of_le (x := fun n => Lam sys L n) (c := gL L / Real.sqrt 2048) 1
    ⟨⌈(gL L / Real.sqrt 2048)⁻¹⌉₊, fun n hn => by
      rw [Lam_eq sys hL, pow_one]
      refine ⟨?_, le_rfl⟩
      have h1 : (gL L / Real.sqrt 2048)⁻¹ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      calc (1 : ℝ) = gL L / Real.sqrt 2048 * (gL L / Real.sqrt 2048)⁻¹ :=
            (mul_inv_cancel₀ hc.ne').symm
        _ ≤ gL L / Real.sqrt 2048 * n := mul_le_mul_of_nonneg_left h1 hc.le⟩
  have h2 := h.add' (const 1)
  refine (h2.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold NL; push_cast; ring

omit [Fintype ν] in
theorem pl_Jn (heta : 0 < eta) : PL (fun n => (Jn sys n : ℝ)) 0 := by
  have he : (1 : ℝ) ≤ eta := by exact_mod_cast heta
  have hm := one_le_mtop sys
  exact natlog_of_le (x := fun n => mtop sys * eta * (n : ℝ) ^ 2) (c := mtop sys * eta) 2
    ⟨1, fun n hn => by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      refine ⟨?_, le_rfl⟩
      have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have : (1 : ℝ) ≤ mtop sys * eta := by nlinarith
      nlinarith⟩

theorem pl_CRes : PL (fun n => CRes sys L n) 0 := by
  have hlog : PL (fun n => (Nat.log 2 n : ℝ)) 0 := by
    have h := natlog_of_le (x := fun n => (n : ℝ)) (c := 1) 1 ⟨1, fun n hn => by
      refine ⟨by exact_mod_cast hn, by rw [pow_one, one_mul]⟩⟩
    exact h.congr ⟨0, fun n _ => by simp⟩
  have h := ((hlog.add' (const 1)).const_mul (Fintype.card (Ch eta) : ℝ)).mul_const
    (440000 / c0 L ^ 2 + 3520000)
  have h2 := ((const 1).add' h).const_mul (chbT sys L)
  refine (h2.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold CRes; ring

/-! ## Generator constants -/

theorem pl_zbC (heta : 0 < eta) : PL (fun n => zbC sys L n) (-2) := by
  have h := ((((pl_Jn sys heta).const_mul 2).add' (const 3)).const_mul (CS1 sys L)).mul (npow (-2))
  refine (h.congr ⟨1, fun n hn => ?_⟩).mono (by norm_num)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold zbC
  rw [Real.rpow_neg hn0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

theorem pl_CZws (s : ℝ) : PL (fun n => CZws sys L Hunit n s) (-3 / 2) := by
  have h := ((((pl_M1 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul_const
    (1 + 26 * (1 + 1 / (2 * (2 * s) - 3)))).sqrt.const_mul
      (finiteCoulombPhysicalMassConstant sys L Hunit)).mul_const (cE sys L ^ s)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

theorem pl_cSt (s : ℝ) : PL (fun n => cSt sys L n s) (-5 / 2) := by
  have h := (((pl_M0 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul_const
    (1 + 26 * (1 + 1 / (2 * (2 * s) - 3)))).sqrt
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

include hL in
theorem pl_z2C (heta : 0 < eta) : PL (fun n => z2C sys L Hunit n) (-2) := by
  have h := (pl_zbC sys heta (L := L)).add' (((pl_CHmix sys Hunit (L := L)).mul (pl_inv_eH sys hL)).const_mul 2)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold z2C; ring

include hL in
theorem pl_z2uC (s : ℝ) : PL (fun n => z2uC sys L Hunit n s) (-3) := by
  have h1 := (npow (-3)).const_mul (CSg sys L)
  have h2 := (pl_CZws sys Hunit (L := L) s).mul (pl_inv_eH sys hL)
  have h3 := ((pl_CHmix sys Hunit (L := L)).mul (pl_inv_eH sys hL)).mul (pl_hotF hL (eta := eta))
  have h := h1.add' (h2.add' h3)
  refine (h.congr ⟨1, fun n hn => ?_⟩).mono (by norm_num)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold z2uC
  rw [Real.rpow_neg hn0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

/-! ## Relative constants -/

theorem pl_zc : PL (fun n => zc sys L Hunit n) (-1) := by
  have h := ((pl_a1c sys (L := L)).const_mul (2 * finiteCoulombPhysicalMassConstant sys L Hunit)).add'
    ((pl_Asig sys (L := L)).mul_const (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit))
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold zc; ring

theorem pl_alphaBB : PL (fun n => alphaBB sys L Hunit n) (-1) := by
  have h := (((pl_Asig sys (L := L)).mul_const (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit)).add'
    ((pl_CV sys Hunit (L := L)).mul ((pl_a0c sys (L := L)).const_mul 2))).const_mul (1 / 2)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold alphaBB; ring

theorem pl_alphaMix : PL (fun n => alphaMix sys L Hunit n) (-1) := by
  have h := (((pl_a1c sys (L := L)).const_mul (2 * finiteCoulombPhysicalMassConstant sys L Hunit)).add'
    ((pl_Asig sys (L := L)).const_mul (2 * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit)))).add'
    ((pl_CV sys Hunit (L := L)).mul ((pl_a0c sys (L := L)).const_mul 2))
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold alphaMix; ring

theorem pl_alphaD : PL (fun n => alphaD sys L Hunit n) (-1) := by
  have hA := pl_Asig sys (L := L)
  have ha0 := pl_a0c sys (L := L)
  have ha1 := pl_a1c sys (L := L)
  have hX := pl_CX sys Hunit (L := L)
  set Cm := finiteCoulombPhysicalMassConstant sys L Hunit
  have t1 := (ha1.const_mul (2 * Cm)).add' (hA.mul_const (Real.sqrt 2 * Cm))
  have t2 := ((hA.mul (((const (Real.sqrt 2 * Cm)).add' (ha1.const_mul (2 * Cm))).add'
    (hA.mul_const (Real.sqrt 2 * Cm)))).add' (hX.mul (ha0.const_mul 2))).const_mul (1 / 2)
  have t3 := ((hA.pow 2).mul hX).const_mul 4
  have h := (t1.add' t2).add' t3
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  simp only [alphaD]; ring

theorem pl_alpha3 : PL (fun n => alpha3 sys L Hunit n) (-2) := by
  have h := (((pl_Asig sys (L := L)).mul (pl_zc sys Hunit (L := L))).add'
    (((pl_CZ sys Hunit (L := L)).const_mul 2).mul ((pl_a0c sys (L := L)).const_mul 2))).const_mul (1 / 2)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold alpha3; ring

theorem pl_alpha4 : PL (fun n => alpha4 sys L Hunit n) (-3) := by
  have hA := pl_Asig sys (L := L)
  have ha0 := pl_a0c sys (L := L)
  have hZ := pl_CZ sys Hunit (L := L)
  have hX := pl_CX sys Hunit (L := L)
  have hV := pl_CV sys Hunit (L := L)
  have hzc := pl_zc sys Hunit (L := L)
  set Cm := finiteCoulombPhysicalMassConstant sys L Hunit
  have t1 := (((hA.pow 2).mul hzc).add' (((hA.mul (hZ.const_mul 2)).mul (ha0.const_mul 2)).const_mul 3)).const_mul
    (1 / 6)
  have t2 := (((((hA.pow 3).mul_const (Real.sqrt 2 * Cm)).add'
    ((((hA.pow 2).mul hV).mul (ha0.const_mul 2)).const_mul 7)).add'
    ((((hA.const_mul 2).pow 2).mul (hA.const_mul 2)).mul (hZ.const_mul 2))).add'
    ((((hA.const_mul 2).pow 3).mul hX).mul (ha0.const_mul 2))).const_mul (1 / 24)
  have h := t1.add' t2
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold alpha4; ring

include hL in
theorem pl_guC (heta : 0 < eta) : PL (fun n => guC sys L Hunit n) (-1) := by
  have h := (((pl_alphaBB sys Hunit (L := L)).add' ((pl_CRes sys (L := L)).mul (npow (-3)))).add'
    ((pl_alphaMix sys Hunit (L := L)).add' ((pl_CHmix sys Hunit (L := L)).mul (pl_highF sys hL heta))))
  refine (h.congr ⟨1, fun n hn => ?_⟩).mono (by norm_num)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold guC
  rw [Real.rpow_neg hn0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

include hL in
theorem pl_wsC (s : ℝ) : PL (fun n => wsC sys L Hunit n s) (2 * s - 1 / 2) := by
  have h := ((pl_sqrt_eH sys hL (4 * s - 1)).const_mul (FSDatum.momentConst1 eta s ((eta : ℝ) / 2) *
    ((CtW sys L Hunit 1 * (3 * sys.maxMass)) ^ 2 +
      2 * finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (1 + 2 * gF L)))).sqrt
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (le_of_eq (by ring))

/-! ## Flow constants at a bounded `C_Δ(n)` -/

section Flow

variable {D : ℕ → ℝ} (hD : PL D 0) (hD0 : ∀ n, 0 ≤ D n)

include hD in
theorem pl_CVret : PL (fun n => CVret sys L Hunit (D n)) 0 := by
  have h := (const (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit)).add hD
  exact h.congr ⟨0, fun n _ => rfl⟩

include hD in
theorem pl_Clow : PL (fun n => Clow sys L Hunit (D n)) 0 := by
  have h := (const (finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 + 1 / 4)).add hD
  exact h.congr ⟨0, fun n _ => by unfold Clow; ring⟩

include hD in
theorem pl_Crev : PL (fun n => Crev sys L Hunit (D n)) 0 := by
  have h := (((pl_Clow sys Hunit hD (L := L)).const_mul 2).add (const 6)).add
    (((pl_CVret sys Hunit hD (L := L)).pow 2).mono (by norm_num))
  exact h.congr ⟨0, fun n _ => rfl⟩

include hD in
theorem pl_Cflsum : PL (fun n => CVret sys L Hunit (D n) + Clow sys L Hunit (D n) + 2) 0 :=
  ((pl_CVret sys Hunit hD (L := L)).add (pl_Clow sys Hunit hD (L := L))).add (const 2)

include hD in
theorem pl_Cfl : PL (fun n => Cfl sys L Hunit (D n)) 0 := by
  have h := (pl_Crev sys Hunit hD (L := L)).mul (pl_Cflsum sys Hunit hD (L := L))
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

include hD hD0 in
theorem pl_CflS {σ : ℝ} (hσ : 0 ≤ σ) : PL (fun n => CflS sys L Hunit (D n) σ) 0 := by
  have h1 := (pl_Crev sys Hunit hD (L := L)).rpow ⟨0, fun n _ => by
    unfold Crev; have := (Clow_pos sys Hunit (hD0 n) (L := L)).le; positivity⟩ hσ
  have h2 := (pl_Cflsum sys Hunit hD (L := L)).rpow ⟨0, fun n _ => by
    have := CVret_nonneg sys Hunit (hD0 n) (L := L)
    have := (Clow_pos sys Hunit (hD0 n) (L := L)).le
    positivity⟩ hσ
  have h := h1.mul h2
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

include hD hD0 in
theorem pl_Ctavg {s : ℝ} (hs : 0 ≤ s) : PL (fun n => Ctavg sys L Hunit (D n) s) 0 := by
  have hPA : PL (fun n => PA sys L s (D n)) 0 := by
    refine (sum Finset.univ (F := fun a n => (4 * qtailC2 sys L a s * (1 + D n) +
      2 * qtailC sys L a ^ 2) ^ 2) fun a _ => ?_).congr ⟨0, fun n _ => rfl⟩
    have := ((((const 1).add hD).const_mul (4 * qtailC2 sys L a s)).add
      (const (2 * qtailC sys L a ^ 2))).pow 2
    exact (this.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)
  have hg : PL (fun n => 2 * (1 + Clow sys L Hunit (D n) + CVret sys L Hunit (D n) ^ 2 / 2)) 0 := by
    have := (((const 1).add (pl_Clow sys Hunit hD (L := L))).add
      ((((pl_CVret sys Hunit hD (L := L)).pow 2).mono (by norm_num)).mul_const (1 / 2))).const_mul 2
    exact this.congr ⟨0, fun n _ => by ring⟩
  have hg0 : ∃ N : ℕ, ∀ n, N ≤ n →
      0 ≤ 2 * (1 + Clow sys L Hunit (D n) + CVret sys L Hunit (D n) ^ 2 / 2) :=
    ⟨0, fun n _ => by have := (Clow_pos sys Hunit (hD0 n) (L := L)).le; positivity⟩
  have hPB : PL (fun n => PB sys L Hunit s (D n)) 0 := by
    refine (sum Finset.univ (F := fun a n => qtailC2 sys L a s ^ 2 * latConst sys L a ^ s *
      (2 * (1 + Clow sys L Hunit (D n) + CVret sys L Hunit (D n) ^ 2 / 2)) ^ s) fun a _ => ?_).congr
      ⟨0, fun n _ => rfl⟩
    have := (hg.rpow hg0 hs).const_mul (qtailC2 sys L a s ^ 2 * latConst sys L a ^ s)
    exact (this.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)
  have hX := (pl_Cflsum sys Hunit hD (L := L)).rpow ⟨0, fun n _ => by
    have := CVret_nonneg sys Hunit (hD0 n) (L := L)
    have := (Clow_pos sys Hunit (hD0 n) (L := L)).le
    positivity⟩ hs
  have h := ((((hPA.const_mul 512).add' (((hPB.const_mul 32768).mul hX).mul_const
    (momentConst eta (s / 2 + 1)))).add' (((pl_CVret sys Hunit hD (L := L)).pow 2).mul_const
      ((4096 * mmax sys) ^ 2 * momentConst eta (1 / 2 + 1)))).const_mul (Real.sqrt Real.pi)).add'
    (const (Real.sqrt (2 * Real.pi)))
  refine ((h.const_mul (2 * Real.exp 1)).congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold Ctavg; ring

end Flow

end FSAsymp
