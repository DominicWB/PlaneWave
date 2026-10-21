import PlaneWave.FluxBox.RoundConstants

/-!
# Flux route, stage 3, part 52: the cutoff dependence of the composite constants

`PL` bounds for every constant of the box ledger along `N = n⁶`, `nd = ndB`, `nd' = ndQ`:
the good-state bounds (`pl_Bpsi`, `pl_Bss`), the word constants (`pl_KC4L`, `pl_KCword`, `pl_KCrest`,
`pl_KCC`), P2/P3 (`pl_KP2`, `pl_KP2g`, `pl_B3n`, `pl_K3c`, `pl_K3e`, `pl_BopY`), the out-of-box rate
(`pl_eRate`, order `n⁻⁹`), round 1 and round 2 (`pl_CYo`, `pl_CYt`, `pl_CZle`, `pl_CY2`, `pl_RY2`,
`pl_CWY`), and **`pl_RateBox`**, **`pl_EndBox`**, **`pl_e0`** (all `PL (-3)`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory FSAsymp

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

namespace PLx

variable {f g : ℕ → ℝ}

theorem mul0 (hf : PL f 0) (hg : PL g 0) : PL (fun n => f n * g n) 0 :=
  (hf.mul hg).mono (by norm_num)

theorem sqrt0 (hf : PL f 0) : PL (fun n => Real.sqrt (f n)) 0 :=
  hf.sqrt.mono (by norm_num)

theorem pow0 (hf : PL f 0) (m : ℕ) : PL (fun n => f n ^ m) 0 :=
  (hf.pow m).mono (by norm_num)

theorem mono0 {p : ℝ} (hf : PL f p) (hp : p ≤ 0) : PL f 0 := hf.mono hp

end PLx

open PLx

section Comp

variable (sys : CoulombSystem eta ν) (L : ℝ) (hL : 0 < L) (Hunit : ℝ)

omit [Fintype ν] in
theorem pl_crit {nd : ℕ → ℕ} (e : ℝ) (h : PL (fun n => (nd n : ℝ)) 0) :
    PL (fun n => 1 + 2 * e * nd n) 0 :=
  ((PL.const 1).add (h.const_mul (2 * e))).congr ⟨0, fun n _ => by ring⟩

omit [Fintype ν] in
theorem pl_lgB2 : PL (fun n => (Nat.log 2 (2 * Nbox n) : ℝ) + 2) 0 := pl_lgB.add (PL.const 2)

omit [Fintype ν] in
include hL in
theorem pl_Bpsi (M C₀ : ℝ) : PL (fun n => Bpsi sys L (Nbox n) (ndB L n) M C₀) 0 := by
  refine ((mul0 pl_lgB2 (pl_crit (eta : ℝ) (pl_ndB hL))).const_mul
    (125 * (2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * C₀ *
      ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2)))).congr ⟨0, fun n _ => ?_⟩
  unfold Bpsi
  ring

omit [Fintype ν] in
include hL in
theorem pl_Bss (M : ℝ) : PL (fun n => Bss sys L (Nbox n) (ndB L n) M) 0 := by
  refine ((pl_lgB2.const_mul (2 * 125 * (4 * cXw sys L ^ 2 * M ^ 2))).add
    ((mul0 pl_lgB2 (pl_crit (eta : ℝ) (pl_ndB hL))).const_mul
      (125 * (Wwc sys L * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2))))).congr ⟨0, fun n _ => ?_⟩
  unfold Bss
  ring

theorem pl_KCdeg (j₁ j₂ j₃ : Ch eta) : PL (fun n => KCdeg sys L (Nbox n) j₁ j₂ j₃) 0 := by
  refine ((mul0 ((PL.const (17728 * chC sys L j₂)).add (pl_LamS2.const_mul (chC sys L j₂)))
    (pl_lgB2.const_mul 250)).const_mul
      (32 * mmax sys / gF L ^ 2 * (chC sys L j₁ / cst sys ^ 2) * chC sys L j₃)).congr
    ⟨0, fun n _ => ?_⟩
  unfold KCdeg
  ring

theorem pl_KY1 (heta : 0 < eta) (j₂ : Ch eta) (c₁ : ℝ) : PL (fun n => KY1 sys L (Nbox n) j₂ c₁) 0 := by
  refine ((pow0 (pl_LamB sys heta) 2).const_mul
    (2048 * mmax sys ^ 2 / gF L ^ 4 * CYc sys L j₂ ^ 2 * c₁ ^ 2 * 277)).congr ⟨0, fun n _ => ?_⟩
  unfold KY1
  ring

lemma GamC_eq (B : ℝ) : GamC sys L B =
    ((Fintype.card (Ch eta) : ℝ) * ∑ j₃ : Ch eta, (64 * chC sys L j₃) ^ 2 * 277) * B := by
  unfold GamC
  rw [mul_assoc, Finset.sum_mul]

theorem pl_GamC {B : ℕ → ℝ} (hB : PL B 0) : PL (fun n => GamC sys L (B n)) 0 :=
  (hB.const_mul _).congr ⟨0, fun n _ => GamC_eq sys L (B n)⟩

theorem pl_KC4L (heta : 0 < eta) (j₂ j₁ : Ch eta) {B₁ Bπ Bc : ℕ → ℝ} (h1 : PL B₁ 0)
    (hπ : PL Bπ 0) (hc : PL Bc 0) :
    PL (fun n => KC4L sys L (Nbox n) Hunit j₂ j₁ (B₁ n) (Bπ n) (Bc n)) 0 := by
  have hA := ((pl_GamC sys L h1).add (mul0 (pl_KY1 sys L heta j₂ (chC sys L j₁ * (1 / cst sys ^ 2))) hπ))
  have hS := PL.sum (Finset.univ : Finset (Ch eta)) (F := fun j₃ n =>
    (KCsh sys L Hunit j₁ j₂ j₃ + KCdeg sys L (Nbox n) j₁ j₂ j₃) * Bc n)
    (fun j₃ _ => mul0 ((PL.const _).add (pl_KCdeg sys L j₁ j₂ j₃)) hc)
  refine ((hA.const_mul (1 / 2)).add hS).congr ⟨0, fun n _ => ?_⟩
  unfold KC4L
  ring

theorem pl_KC4S (j₂ j₁ : Ch eta) {Bπ Bc : ℕ → ℝ} (hπ : PL Bπ 0) (hc : PL Bc 0) :
    PL (fun n => KC4S sys L Hunit j₂ j₁ (Bπ n) (Bc n)) 0 := by
  refine ((hπ.const_mul ((8 * cYb sys L j₂) ^ 2 * 277 * (26 * cst sys * chC sys L j₁) ^ 2)).add
    (hc.const_mul ((8 * cYb sys L j₂) ^ 2 * 277 * (4 * cst sys) ^ 2 * (chC sys L j₁ ^ 2 * Hunit ^ 2)))).congr
    ⟨0, fun n _ => ?_⟩
  unfold KC4S
  ring

theorem pl_KC1 (j₂ j₁ : Ch eta) {Bc : ℕ → ℝ} (hc : PL Bc 0) :
    PL (fun n => KC1 sys L Hunit j₂ j₁ (Bc n)) 0 := by
  refine (hc.const_mul (2 * ((32 * mmax sys * chC sys L j₂ * chC sys L j₁ / (gF L ^ 2 * cst sys ^ 2)) ^ 2 *
      277 * Hunit ^ 2) + 2 * ((2048 * mmax sys * chC sys L j₂ / gF L ^ 2) ^ 2 * 277 *
      (chC sys L j₁ ^ 2 * Hunit ^ 2)))).congr ⟨0, fun n _ => ?_⟩
  unfold KC1
  ring

theorem pl_KC2 (j₂ j₁ : Ch eta) {Bc : ℕ → ℝ} (hc : PL Bc 0) :
    PL (fun n => KC2 sys L Hunit j₂ j₁ (Bc n)) 0 := by
  refine (hc.const_mul ((32 * mmax sys * chC sys L j₂ * chC sys L j₁ / (gF L ^ 2 * cst sys ^ 2)) ^ 2 *
      277 * Hunit ^ 2)).congr ⟨0, fun n _ => ?_⟩
  unfold KC2
  ring

theorem pl_KCword (heta : 0 < eta) (j₂ j₁ : Ch eta) {B₁ Bπ Bc : ℕ → ℝ} (h1 : PL B₁ 0)
    (hπ : PL Bπ 0) (hc : PL Bc 0) :
    PL (fun n => KCword sys L (Nbox n) Hunit j₂ j₁ (B₁ n) (Bπ n) (Bc n)) 0 := by
  have hG := pl_GamC sys L h1
  have hA := ((hG.add (hπ.const_mul (KW1 sys L Hunit (chC sys L j₂) (cY3' sys L j₁)))).const_mul (1 / 2))
  have hB := ((hG.add (pl_KC4S sys L Hunit j₂ j₁ hπ hc)).const_mul (1 / 2))
  have hC := (pl_KC4L sys L Hunit heta j₂ j₁ h1 hπ hc).const_mul 2
  by_cases hj : j₂ = j₁
  · refine ((hA.add hB).add hC).congr ⟨0, fun n _ => ?_⟩
    unfold KCword
    rw [if_pos hj]
    ring
  · have hD := ((hG.add (pl_KC1 sys L Hunit j₂ j₁ hc)).const_mul (1 / 2)).add
      ((hG.add (pl_KC2 sys L Hunit j₂ j₁ hc)).const_mul (1 / 2))
    refine (((hA.add hB).add hC).add hD).congr ⟨0, fun n _ => ?_⟩
    unfold KCword
    rw [if_neg hj]
    ring

theorem pl_KCrest (heta : 0 < eta) {B₁ Bπ Bc : ℕ → ℝ} (h1 : PL B₁ 0) (hπ : PL Bπ 0) (hc : PL Bc 0) :
    PL (fun n => KCrest sys L (Nbox n) Hunit (B₁ n) (Bπ n) (Bc n)) 0 := by
  have h := PL.sum (Finset.univ : Finset (Ch eta)) (F := fun j₁ n => ∑ j₂ : Ch eta,
    KCword sys L (Nbox n) Hunit j₂ j₁ (B₁ n) (Bπ n) (Bc n))
    (fun j₁ _ => PL.sum Finset.univ (F := fun j₂ n => KCword sys L (Nbox n) Hunit j₂ j₁ (B₁ n) (Bπ n) (Bc n))
      (fun j₂ _ => pl_KCword sys L Hunit heta j₂ j₁ h1 hπ hc))
  exact (h.const_mul (4 / 3)).congr ⟨0, fun n _ => by unfold KCrest; rfl⟩

include hL in
theorem pl_KCC (heta : 0 < eta) (M : ℝ) :
    PL (fun n => KCC sys L (Nbox n) (ndB L n) M Hunit) 0 := by
  have h1 := PL.sum (Finset.univ : Finset (Ch eta)) (F := fun j n => Kss sys L j / 2 * Bss sys L (Nbox n) (ndB L n) M)
    (fun j _ => (pl_Bss sys L hL M).const_mul _)
  have h2 := pl_KCrest sys L Hunit heta (pl_Bpsi sys L hL M 1) (pl_Bpsi sys L hL M (4 * mmax sys / gF L ^ 2))
    (pl_Bpsi sys L hL M (2 * cXw sys L))
  exact (h1.add h2).congr ⟨0, fun n _ => by unfold KCC; rfl⟩

theorem pl_Kw (heta : 0 < eta) (j₂ j₁ : Ch eta) : PL (fun n => Kw sys L Hunit (Nbox n) j₂ j₁) 0 := by
  have hY := pl_KY1 sys L heta j₂ (chC sys L j₁ * (1 / cst sys ^ 2))
  refine (((PL.const ((2 * KW1 sys L Hunit (chC sys L j₂) (chC sys L j₁ * (1 / cst sys ^ 2)) +
      2 * KL2 sys L Hunit (2048 * mmax sys * chC sys L j₂ / gF L ^ 2) j₁) +
    KW1 sys L Hunit (chC sys L j₂) (chC sys L j₁ * (1 / cst sys ^ 2)) +
    KW1 sys L Hunit (chC sys L j₂) (cY3 sys L j₁) + 2 * KL2 sys L Hunit (cYb sys L j₂) j₁)).add
      (hY.const_mul 3))).congr ⟨0, fun n _ => ?_⟩
  unfold Kw
  ring

theorem pl_KP2 (heta : 0 < eta) : PL (fun n => KP2 sys L Hunit (Nbox n)) 0 := by
  have h := PL.sum (Finset.univ : Finset (Ch eta)) (F := fun j₁ n => ∑ j₂ : Ch eta, Kw sys L Hunit (Nbox n) j₂ j₁)
    (fun j₁ _ => PL.sum Finset.univ (F := fun j₂ n => Kw sys L Hunit (Nbox n) j₂ j₁)
      (fun j₂ _ => pl_Kw sys L Hunit heta j₂ j₁))
  exact (h.const_mul _).congr ⟨0, fun n _ => by unfold KP2; rfl⟩

theorem pl_KP2g (heta : 0 < eta) (M : ℝ) : PL (fun n => KP2g sys L Hunit (Nbox n) M) 0 := by
  refine (mul0 (pl_KP2 sys L Hunit heta) (pl_lgB2.const_mul
    ((Fintype.card (Ch eta) : ℝ) * 125 * (4 * cXw sys L ^ 2 * M ^ 2)))).congr ⟨0, fun n _ => ?_⟩
  unfold KP2g
  ring

include hL in
theorem pl_B3n (M : ℝ) : PL (fun n => B3n sys L Hunit (Nbox n) (ndB L n) M) 0 := by
  refine ((pl_lgB2.const_mul ((81 * cSum sys L) ^ 2 * 125 * (4 * cXw sys L ^ 2 * M ^ 2))).add
    ((mul0 pl_lgB2 (pl_crit (eta : ℝ) (pl_ndB hL))).const_mul (cSum sys L ^ 2 * Hunit ^ 2 * 125 *
      (W5c sys L * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2))))).congr ⟨0, fun n _ => ?_⟩
  unfold B3n
  ring

include hL in
theorem pl_K3c (heta : 0 < eta) (M : ℝ) : PL (fun n => K3c sys L Hunit (Nbox n) (ndB L n) M) 0 := by
  have h1 := (pl_KCC sys L hL Hunit heta M).const_mul 2
  have h2 := (sqrt0 ((pl_KP2g sys L Hunit heta M).const_mul
    (2 * CH sys L Hunit ^ 2 * eta ^ 2 * M ^ 2 / (gF L * cst sys) ^ 3))).const_mul 2
  have h3 := (sqrt0 ((mul0 ((pl_KP2 sys L Hunit heta).mul_const ((Fintype.card (Ch eta) : ℝ) ^ 3))
    (pl_B3n sys L hL Hunit M)).mul_const (eta ^ 2 * M ^ 2 * (4 / gF L) ^ 5))).const_mul 2
  exact ((h1.add h2).add h3).congr ⟨0, fun n _ => by unfold K3c; rfl⟩

theorem pl_K3e (heta : 0 < eta) (M : ℝ) : PL (fun n => K3e sys L Hunit (Nbox n) M) 0 := by
  refine ((sqrt0 ((pl_KP2g sys L Hunit heta M).const_mul (eta ^ 2 * M ^ 2 * (4 / gF L) ^ 5))).const_mul 2).congr
    ⟨0, fun n _ => rfl⟩

theorem pl_BopY (heta : 0 < eta) : PL (fun n => BopY sys L Hunit (Nbox n) n) 1 := by
  have h := ((mul0 (pl_KP2 sys L Hunit heta) (pl_lgB2.const_mul ((Fintype.card (Ch eta) : ℝ) * 500))).mul
    (PL.npow_nat 1))
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold BopY
  ring

include hL in
theorem pl_eRate : PL (fun n => eRate sys L Hunit (Nbox n)) (-9) := by
  have h := (pl_lin_rpow' (c := gF L) (gF_pos hL).le 6 (-(3 / 2 : ℝ))).const_mul
    (Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold eRate Nbox
  ring

theorem pl_CYo (heta : 0 < eta) : PL (fun n => CYo sys L (Nbox n)) 0 :=
  (PL.sum (p := 0) (Finset.univ : Finset (Ch eta)) (F := fun j n => CYc sys L j * LamB sys (Nbox n) *
    (Real.sqrt 2 * Real.sqrt (cXw sys L))) (fun j _ =>
      (((pl_LamB sys heta).const_mul (CYc sys L j)).mul (PL.const _)).mono (by norm_num))).congr
    ⟨0, fun n _ => by unfold CYo; rfl⟩

theorem pl_CYt (heta : 0 < eta) : PL (fun n => CYt sys L (Nbox n)) 0 :=
  (PL.sum (p := 0) (Finset.univ : Finset (Ch eta)) (F := fun j n => CYc sys L j * LamB sys (Nbox n) *
    (Real.sqrt 2 * Real.sqrt (cXw sys L))) (fun j _ =>
      (((pl_LamB sys heta).const_mul (CYc sys L j)).mul (PL.const _)).mono (by norm_num))).congr
    ⟨0, fun n _ => by unfold CYt; rfl⟩

theorem pl_zLeC (j : Ch eta) : PL (fun n => zLeC sys L n j) (-3) :=
  ((pl_cube34 611).const_mul (9 * muCh sys j * chC sys L j ^ 2 / Mtot sys j)).congr
    ⟨0, fun n _ => by unfold zLeC; rfl⟩

theorem pl_y2C (j : Ch eta) : PL (fun n => y2C sys L n j) (-3) :=
  ((pl_cube34 611).const_mul (84 * muCh sys j ^ 2 * chC sys L j ^ 2 / (gF L ^ 2 * Mtot sys j))).congr
    ⟨0, fun n _ => by unfold y2C; rfl⟩

theorem pl_CZle : PL (fun n => CZle sys L n) (-3) :=
  (PL.sum (p := -3) (Finset.univ : Finset (Ch eta)) (F := fun j n => zLeC sys L n j *
    (Real.sqrt 2 * (8 / 3) * (19 / 3) ^ 3) * (cXw sys L ^ 2 * Real.sqrt (cXw sys L))) (fun j _ =>
      ((((pl_zLeC sys L j).mul (PL.const _)).mul (PL.const _)).mono (by norm_num)))).congr
    ⟨0, fun n _ => by unfold CZle; rfl⟩

theorem pl_CY2 : PL (fun n => CY2 sys L n) (-3) :=
  (PL.sum (p := -3) (Finset.univ : Finset (Ch eta)) (F := fun j n => y2C sys L n j *
    (125 * ((Nat.log 2 n : ℝ) + 2)) * (Real.sqrt 2 * cXw sys L ^ 2)) (fun j _ =>
      ((((pl_y2C sys L j).mul ((pl_lgn.add (PL.const 2)).const_mul 125)).mul (PL.const _)).mono
        (by norm_num)))).congr ⟨0, fun n _ => by unfold CY2; rfl⟩

theorem pl_np1_cube : PL (fun n => ((n : ℝ) + 1) ^ 3) 3 := by
  have h : PL (fun n => (n : ℝ) + 1) 1 :=
    ((PL.lin 1).add ((PL.const 1).mono (by norm_num))).congr ⟨0, fun n _ => by ring⟩
  exact (h.pow 3).mono (by norm_num)

theorem pl_RY2 : PL (fun n => RY2 sys L n) 1 :=
  (PL.sum (p := 1) (Finset.univ : Finset (Ch eta)) (F := fun j n => y2C sys L n j * ((n : ℝ) / 2) * ((n : ℝ) + 1) ^ 3)
    (fun j _ => ((((pl_y2C sys L j).mul ((PL.npow_nat 1).const_mul (1 / 2))).mul pl_np1_cube).congr
      ⟨0, fun n _ => by ring⟩).mono (by norm_num))).congr ⟨0, fun n _ => by unfold RY2; rfl⟩

include hL in
theorem pl_CWY : PL (fun n => CWY sys L (Nbox n) n (ndQ L n)) (-3) := by
  have h1 := PL.sum (p := -3) (Finset.univ : Finset (Ch eta)) (F := fun j n => chC sys L j * y2C sys L n j *
    LamS (2 * Nbox n) * (125 * ((Nat.log 2 (Nbox n) : ℝ) + 2)) * (Real.sqrt 2 * cXw sys L ^ 2))
    (fun j _ => (((((pl_y2C sys L j).const_mul (chC sys L j)).mul pl_LamS2).mul
      ((pl_lgN.add (PL.const 2)).const_mul 125)).mul (PL.const _)).mono (by norm_num))
  have h2 := PL.sum (p := -3) (Finset.univ : Finset (Ch eta)) (F := fun j' n => ∑ j : Ch eta,
    chC sys L j' * y2C sys L n j * LamS (2 * Nbox n) ^ 2 * cWc sys L)
    (fun j' _ => PL.sum (p := -3) Finset.univ (F := fun j n => chC sys L j' * y2C sys L n j *
      LamS (2 * Nbox n) ^ 2 * cWc sys L) (fun j _ =>
        ((((pl_y2C sys L j).const_mul (chC sys L j')).mul (pow0 pl_LamS2 2)).mul (PL.const _)).mono
          (by norm_num)))
  have h3 := sqrt0 ((pl_crit (eta : ℝ) (pl_ndQ hL)).const_mul ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ)))
  refine (h1.add ((h2.mul h3).mono (by norm_num))).congr ⟨0, fun n _ => ?_⟩
  unfold CWY
  rfl

end Comp

end FSFlux
