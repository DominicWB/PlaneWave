import PlaneWave.Source.CutoffScales

/-!
# Flux/source build, block 5: the cutoff dependence of the ledger and of the budgets

With `z₃(n) = O(n^{-2} polylog)` and `β(n) = O(n^{-3} polylog)` (the conditional hypotheses of
`thm:src3`):

* the ledger coefficients: `k₀ = O(n^{-3})`, `k_{1/4} = O(n^{2s-9/2})`, `k_{1/2} = O(n^{-7/2})`,
  `k_s = O(n^{-4})`, and the ledger constant against the Galerkin flow `L = O(n^{2s-9/2})`;
* the budgets `m_a, m_χ, m_rot, m_N, m_r, m_w, m_V = O(polylog)` and the defects
  `δ_a = O(n^{-7/2})`, `δ_rot, δ_r = O(n^{-3})`, `ρ̃ = O(n^{-5/2})`, `ω̃ = O(n^{-3/2})`;
* the error constant `err = E₀ + t E₁` with `E₀ = O(n^{-3} polylog)` and
  `E₁ = O(n^{max(2s, s₁, 2s₂) - 9/2} polylog)` (`pl_E0err`, `pl_E1err`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSAsymp

open FSNormal

namespace PL

variable {f g : ℕ → ℝ} {p q r : ℝ}

theorem add_le (hf : PL f p) (hg : PL g q) (hp : p ≤ r) (hq : q ≤ r) :
    PL (fun n => f n + g n) r := (hf.mono hp).add (hg.mono hq)

theorem mul_le (hf : PL f p) (hg : PL g q) (h : p + q ≤ r) : PL (fun n => f n * g n) r :=
  (hf.mul hg).mono h

end PL

open PL

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (Hunit : ℝ) (heta : 0 < eta)

/-! ## The second-order ledger constants -/

include hL heta in
theorem pl_r2aC (s : ℝ) : PL (fun n => r2aC sys L Hunit n s) (-3) := by
  have hz := pl_z2C sys hL Hunit heta
  have hg := pl_guC sys hL Hunit heta
  have hu := pl_z2uC sys hL Hunit s
  have hA := pl_Amax (eta := eta) (L := L)
  have hVD := (pl_CVN sys Hunit (L := L)).add_le (pl_CDelta sys Hunit (L := L)) le_rfl (by norm_num)
    (r := 1)
  have t1 := hz.mul_le hg (r := -3) (by norm_num)
  have t2 := (((hz.const_mul 2).mul hA).mul hu).mono (q := -3) (by norm_num)
  have t3 := (((hz.pow 2).const_mul 4).mul hVD).mono (q := -3) (by norm_num)
  have t4 := ((((hz.const_mul 2).mul ((hz.const_mul 2).mul hA)).add_le (((hz.pow 2).const_mul 4).mul hVD)
    (r := -2) (by norm_num) (by norm_num)).mul hu).mono (q := -3) (by norm_num)
  have h := (((t1.add t2).add t3).add t4).const_mul (1 / 2)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold r2aC; ring

include hL heta in
theorem pl_d2uC (s : ℝ) : PL (fun n => d2uC sys L Hunit n s) (-1) := by
  have hz := pl_z2C sys hL Hunit heta
  have hD := pl_alphaD sys Hunit (L := L)
  have hu := pl_z2uC sys hL Hunit s
  have hVD := (pl_CVN sys Hunit (L := L)).add_le (pl_CDelta sys Hunit (L := L)) le_rfl (by norm_num)
    (r := 1)
  have t := (hz.mul ((const (cvC sys L Hunit)).add_le hD (r := 0) le_rfl (by norm_num))).add_le
    (hVD.mul hu) (r := -1) (by norm_num) (by norm_num)
  have h := (((hD.add (pl_guC sys hL Hunit heta)).add t).add_le (pl_r2aC sys hL Hunit heta s)
    (r := -1) le_rfl (by norm_num))
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold d2uC; ring

include hL heta in
theorem pl_d2oC : PL (fun n => d2oC sys L Hunit n) 0 := by
  have hz := pl_z2C sys hL Hunit heta
  have hA := pl_Amax (eta := eta) (L := L)
  have hVD := (pl_CVN sys Hunit (L := L)).add_le (pl_CDelta sys Hunit (L := L)) le_rfl (by norm_num)
    (r := 1)
  have t1 := ((hz.const_mul 2).mul hA).mono (q := 0) (by norm_num)
  have t2 := ((hz.const_mul 2).mul hVD).mono (q := 0) (by norm_num)
  have t3 := (((hz.const_mul 2).mul ((hz.const_mul 2).mul hA)).add_le (((hz.pow 2).const_mul 4).mul hVD)
    (r := 0) (by norm_num) (by norm_num))
  have h := ((pl_CDelta sys Hunit (L := L)).add t1).add t2 |>.add t3
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold d2oC; ring

section Hyp

variable {z3 β : ℕ → ℝ} (hz3 : PL z3 (-2)) (hβ : PL β (-3))

include heta hβ in
theorem pl_h3guC : PL (fun n => h3guC sys L Hunit n (β n)) (-2) := by
  have t1 := ((pl_zbC sys heta (L := L)).mul_const (cvC sys L Hunit))
  have t2 := ((pl_CVN sys Hunit (L := L)).mul ((npow (-3)).const_mul (CSg sys L))).mono (q := -2)
    (by norm_num)
  have h := ((t1.add t2).add (pl_alpha3 sys Hunit (L := L))).add_le hβ le_rfl (by norm_num)
  refine h.congr ⟨1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold h3guC
  rw [Real.rpow_neg hn0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

include hL heta hz3 hβ in
theorem pl_r2bC : PL (fun n => r2bC sys L Hunit n (z3 n) (β n)) (-3) := by
  have hA := pl_Amax (eta := eta) (L := L)
  have hVd := (pl_CVN sys Hunit (L := L)).add_le (pl_d2oC sys hL Hunit heta) le_rfl (by norm_num)
    (r := 1)
  have t1 := hz3.mul_le (pl_h3guC sys Hunit heta hβ (L := L)) (r := -3) (by norm_num)
  have t2 := (((hz3.const_mul 2).mul hA).mul hβ).mono (q := -3) (by norm_num)
  have t3 := (((hz3.pow 2).const_mul 4).mul hVd).mono (q := -3) (by norm_num)
  have t4 := (((hz3.const_mul 2).mul ((hz3.const_mul 2).mul hA)).add_le (((hz3.pow 2).const_mul 4).mul hVd)
    (r := 0) (by norm_num) (by norm_num)).mul_le hβ (r := -3) (by norm_num)
  have h := (((t1.add t2).add t3).add t4).const_mul (1 / 2)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold r2bC; ring

include hL heta hz3 hβ in
theorem pl_k0C (s : ℝ) : PL (fun n => k0C sys L Hunit n s (z3 n) (β n)) (-3) := by
  have t1 := ((pl_CRes sys (L := L)).mul (npow (-3))).mono (q := -3) (by norm_num)
  have t2 := ((pl_CVN sys Hunit (L := L)).mul (((pl_CHmix sys Hunit (L := L)).mul (pl_inv_eH sys hL)).mul
    (pl_hotF hL (eta := eta)))).mono (q := -3) (by norm_num)
  have t3 := ((pl_z2C sys hL Hunit heta).mul (pl_alphaD sys Hunit (L := L))).add_le
    ((pl_CDelta sys Hunit (L := L)).mul (pl_z2uC sys hL Hunit s)) (r := -3) (by norm_num) (by norm_num)
  have t4 := (hz3.mul (pl_d2uC sys hL Hunit heta s)).add_le ((pl_d2oC sys hL Hunit heta).mul hβ)
    (r := -3) (by norm_num) (by norm_num)
  have h := (((((((t1.add hβ).add (pl_alpha4 sys Hunit (L := L))).add t2).add t3).add
    (pl_r2aC sys hL Hunit heta s)).add t4).add (pl_r2bC sys hL Hunit heta hz3 hβ))
  refine h.congr ⟨1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold k0C
  rw [Real.rpow_neg hn0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

include hL heta hβ in
theorem pl_k14C {s : ℝ} (hs : 3 / 4 ≤ s) : PL (fun n => k14C sys L Hunit n s (β n)) (2 * s - 9 / 2) := by
  have hq := pl_eHq sys hL
  have t1 := (((pl_CHmix sys Hunit (L := L)).mul (pl_highF sys hL heta)).mul hq)
  have t2 := ((((pl_CZws sys Hunit (L := L) s).mul (pl_inv_eH sys hL)).mul (pl_wsC sys hL Hunit s)).mul hq)
  have t3 := hβ.const_mul (1 + cvC sys L Hunit)
  have h := (t1.add_le t2 (r := 2 * s - 9 / 2) (by linarith) (by linarith)).add_le t3
    (r := 2 * s - 9 / 2) le_rfl (by linarith)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold k14C; ring

include hL in
theorem pl_k12C (s : ℝ) : PL (fun n => k12C sys L Hunit n s) (-7 / 2) := by
  have h := ((pl_CZws sys Hunit (L := L) s).mul (pl_inv_eH sys hL)).mul_const (cvC sys L Hunit)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold k12C; ring

include hL in
theorem pl_ksC (s : ℝ) : PL (fun n => ksC sys L Hunit n s) (-4) := by
  have h := ((pl_Kc4 hL (-(1 / 2 : ℝ))).const_mul (eta * (CtW sys L Hunit 1 * (3 * sys.maxMass)))).mul
    ((pl_CZws sys Hunit (L := L) s).mul (pl_inv_eH sys hL))
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold ksC; ring

end Hyp

/-! ## The flow constants of the datum -/

include hL in
theorem pl_phi14C : PL (fun n => phi14C sys L Hunit 0 (NL sys L n)) 0 := by
  have h := ((((pl_NL sys hL).const_mul (2 * eta)).add (const 1)).const_mul
    ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ))).sqrt.const_mul
    (Crev sys L Hunit 0 ^ (1 / 4 : ℝ) * (CVret sys L Hunit 0 + Clow sys L Hunit 0 + 2) ^ (1 / 4 : ℝ))
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold phi14C; ring_nf

omit [Fintype ν] in
include hL in
theorem pl_momF (σ : ℝ) : PL (fun n => momF sys L n σ) (2 * σ - 1 / 2) := by
  have h := ((pl_Lam sys hL (4 * σ - 1)).const_mul (momentConst eta (σ + 1))).sqrt
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (le_of_eq (by ring))

include hL in
theorem pl_phiSC0 (σ : ℝ) : PL (fun n => phiSC sys L Hunit n 0 σ) (2 * σ - 1 / 2) := by
  have h := (pl_momF sys hL σ).const_mul (CflS sys L Hunit 0 σ)
  exact h.congr ⟨0, fun n _ => rfl⟩

section Ledger

variable {z3 β : ℕ → ℝ} (hz3 : PL z3 (-2)) (hβ : PL β (-3))

include hL heta hz3 hβ in
/-- **The ledger constant against the Galerkin flow**: `L = O(n^{2s - 9/2} polylog)`. -/
theorem pl_ledC {s : ℝ} (hs : 3 / 4 ≤ s) :
    PL (fun n => ledC sys L Hunit n s (z3 n) (β n)) (2 * s - 9 / 2) := by
  have t0 := (pl_k0C sys hL Hunit heta hz3 hβ s).mul_const 1
  have t1 := (pl_k14C sys hL Hunit heta hβ hs).mul_le (pl_phi14C sys hL Hunit) (r := 2 * s - 9 / 2)
    (by linarith)
  have t2 := (pl_k12C sys hL Hunit s).mul_le (pl_phiSC0 sys hL Hunit (1 / 2)) (r := 2 * s - 9 / 2)
    (by linarith)
  have t3 := (pl_ksC sys hL Hunit s).mul_le (pl_phiSC0 sys hL Hunit s) (r := 2 * s - 9 / 2)
    (by linarith)
  have h := ((t0.add_le t1 (r := 2 * s - 9 / 2) (by linarith) le_rfl).add t2).add t3
  exact h.congr ⟨0, fun n _ => rfl⟩

end Ledger

end FSAsymp
