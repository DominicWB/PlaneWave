import PlaneWave.FluxBox.OutOfBoxErrors

/-!
# Flux route, stage 3, part 49: the box ledger

* **the ledger on the box** (`ledger_box_eq`): the flat ledger, the com ledger, the ledger of the
  symbol current and the far–cold ledger combined, with the pointwise rest
  `R = Re⟨u,i[W,Ŵ_c]u⟩ - Re⟨u,i[W,Y₁]u⟩ - Re⟨u,N^{FC}u⟩ + Re⟨u,Z_a u⟩ = Re e_bd(u) - Re e_bd(Pu) + n^{rr} + cm^{rr}`
  (`Rf_eq`);
* **the box ledger bound** (`ledger_box_le`): `|∫₀ᵗ Re⟨u, X_N u⟩| ≤ t RateBox + EndBox` for the box
  states along the trajectory;
* **the flux on the box** (`flux_box_total`): `|∫₀ᵗ F| ≤ t (C_B (c_Tr Ξ)² (gN)^{-1/2} + RateBox) + EndBox`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section LedgerBox

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta) {N : ℕ} (n : ℕ)

include hL hKernel in
/-- **The pointwise rest of the box ledger**. -/
lemma Rf_eq (hn : 1 ≤ n) (u : En eta N) :
    (⟪u, (Complex.I • (WN sys L N ∘ₗ Whc sys L p₀ n - Whc sys L p₀ n ∘ₗ WN sys L N)) u⟫_ℂ).re -
        (⟪u, (Complex.I • (WN sys L N ∘ₗ Y1N sys L p₀ N n - Y1N sys L p₀ N n ∘ₗ WN sys L N)) u⟫_ℂ).re -
        (⟪u, NFC sys L p₀ N n u⟫_ℂ).re + (⟪u, ZaN sys L p₀ N n u⟫_ℂ).re =
      (ebd sys L p₀ u).re - (ebd sys L p₀ (PN N n u)).re + nflRR sys L p₀ n u + cmRR sys L p₀ n u := by
  rw [flat_comm_eq n hL u, nfl_split hL H hKernel hn u, re_comm_eq WN_symm (Y1N_symm hL H hKernel) u,
    ← nfcFC_eq hL H hKernel u]
  have h2 := cm_split (sys := sys) (L := L) (p₀ := p₀) n u
  have h4 := cmQQ_eq (sys := sys) (p₀ := p₀) n hL H hKernel u
  linarith

include hL hKernel in
/-- **The ledger on the box**. -/
theorem ledger_box_eq (hn : 1 ≤ n) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, (⟪ub H D N s, XN sys L p₀ N n (ub H D N s)⟫_ℂ).re =
      -((⟪ub H D N t, Whc sys L p₀ n (ub H D N t)⟫_ℂ).re -
          (⟪ub H D N 0, Whc sys L p₀ n (ub H D N 0)⟫_ℂ).re) +
        (∫ s in (0 : ℝ)..t,
          ((⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Whc sys L p₀ n - Whc sys L p₀ n ∘ₗ WN sys L N))
              (ub H D N s)⟫_ℂ).re -
            (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y1N sys L p₀ N n - Y1N sys L p₀ N n ∘ₗ WN sys L N))
              (ub H D N s)⟫_ℂ).re -
            (⟪ub H D N s, NFC sys L p₀ N n (ub H D N s)⟫_ℂ).re +
            (⟪ub H D N s, ZaN sys L p₀ N n (ub H D N s)⟫_ℂ).re)) +
        (∫ s in (0 : ℝ)..t, eY sys H D (Whc sys L p₀ n : En eta N →ₗ[ℂ] En eta N) s) +
        (∫ s in (0 : ℝ)..t, (⟪ub H D N s, XresN sys L p₀ N n (ub H D N s)⟫_ℂ).re) +
        ((⟪ub H D N t, Y1N sys L p₀ N n (ub H D N t)⟫_ℂ).re -
          (⟪ub H D N 0, Y1N sys L p₀ N n (ub H D N 0)⟫_ℂ).re) -
        (∫ s in (0 : ℝ)..t, eY sys H D (Y1N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N) s) +
        ((⟪ub H D N t, Y3N sys L p₀ N n (ub H D N t)⟫_ℂ).re -
          (⟪ub H D N 0, Y3N sys L p₀ N n (ub H D N 0)⟫_ℂ).re) -
        (∫ s in (0 : ℝ)..t, (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y3N sys L p₀ N n -
          Y3N sys L p₀ N n ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re) -
        (∫ s in (0 : ℝ)..t, eY sys H D (Y3N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N) s) -
        (∫ s in (0 : ℝ)..t, (⟪ub H D N s, FSKernel.kop (zaLe sys L p₀ N n) (ub H D N s)⟫_ℂ).re) -
        ((⟪ub H D N t, Y2N sys L p₀ N n (ub H D N t)⟫_ℂ).re -
          (⟪ub H D N 0, Y2N sys L p₀ N n (ub H D N 0)⟫_ℂ).re) +
        (∫ s in (0 : ℝ)..t, (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y2N sys L p₀ N n -
          Y2N sys L p₀ N n ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re) +
        (∫ s in (0 : ℝ)..t, eY sys H D (Y2N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N) s) := by
  have h1 := ledger_flat sys hL H hKernel p₀ (N := N) n Hunit hPeriodic D t
  have h2 := ledger_cm sys hL H hKernel p₀ (N := N) n Hunit hPeriodic D t
  have h3 := ledger_za sys hL H hKernel p₀ (N := N) n Hunit hPeriodic D t
  have h4 := ledger_fc sys hL H hKernel p₀ (N := N) n hn Hunit hPeriodic D t
  have c1 := continuous_form_ub H (N := N) D
    (Complex.I • (WN sys L N ∘ₗ Whc sys L p₀ n - Whc sys L p₀ n ∘ₗ WN sys L N))
  have c2 := continuous_form_ub H (N := N) D
    (Complex.I • (WN sys L N ∘ₗ Y1N sys L p₀ N n - Y1N sys L p₀ N n ∘ₗ WN sys L N))
  have c3 := continuous_form_ub H (N := N) D (NFC sys L p₀ N n)
  have c4 := continuous_form_ub H (N := N) D (ZaN sys L p₀ N n)
  have c12 : Continuous fun s =>
      (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Whc sys L p₀ n - Whc sys L p₀ n ∘ₗ WN sys L N))
        (ub H D N s)⟫_ℂ).re -
      (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y1N sys L p₀ N n - Y1N sys L p₀ N n ∘ₗ WN sys L N))
        (ub H D N s)⟫_ℂ).re := c1.sub c2
  have c123 : Continuous fun s =>
      (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Whc sys L p₀ n - Whc sys L p₀ n ∘ₗ WN sys L N))
        (ub H D N s)⟫_ℂ).re -
      (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y1N sys L p₀ N n - Y1N sys L p₀ N n ∘ₗ WN sys L N))
        (ub H D N s)⟫_ℂ).re -
      (⟪ub H D N s, NFC sys L p₀ N n (ub H D N s)⟫_ℂ).re := c12.sub c3
  rw [intervalIntegral.integral_add (c123.intervalIntegrable 0 t) (c4.intervalIntegrable 0 t),
    intervalIntegral.integral_sub (c12.intervalIntegrable 0 t) (c3.intervalIntegrable 0 t),
    intervalIntegral.integral_sub (c1.intervalIntegrable 0 t) (c2.intervalIntegrable 0 t)]
  linarith

end LedgerBox

/-! ## The box ledger bound -/

section LedgerBound

variable {sys : CoulombSystem eta ν} {L : ℝ}

omit [Fintype ν] in
lemma abs_integral_le_of {f : ℝ → ℝ} {C t : ℝ} (ht : 0 ≤ t) (h : ∀ s, |f s| ≤ C) :
    |∫ s in (0 : ℝ)..t, f s| ≤ t * C := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (f := f) (C := C)
    (fun s _ => by rw [Real.norm_eq_abs]; exact h s)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at this
  linarith

omit [Fintype ν] in
lemma abs_re_inner_le {X : Type*} [Fintype X] {A : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X}
    {u : EuclideanSpace ℂ X} {b : ℝ} (h : ‖⟪u, A u⟫_ℂ‖ ≤ b) : |(⟪u, A u⟫_ℂ).re| ≤ b :=
  (Complex.abs_re_le_norm _).trans h

variable (sys L) in
/-- The per-time rate of the box ledger (`M` the goodness constant of the box states). -/
noncomputable def RateBox (Hunit : ℝ) (N n nd nd' : ℕ) (M Xi : ℝ) : ℝ :=
  (2 * (Cbd sys L * M ^ 2 * (1 / (N : ℝ) + 1 / (gF L * N))) +
    8 * Hrs sys L Hunit ^ 2 * M ^ 2 * (gF L * (cst sys * n)) ^ (-(3 : ℝ)) +
    6 * (Hrs sys L Hunit * CYo sys L N * eta * M ^ 2 * (gF L * (cst sys * n)) ^ (-(3 : ℝ)))) +
  2 * (eRate sys L Hunit N * Xi) * (2 * CH sys L Hunit * M) +
  3 * CRt sys L * (cXw sys L * (eta ^ 2 * M ^ 2 * (gF L * (3 * n / 64)) ^ (-(3 : ℝ)))) +
  2 * (eRate sys L Hunit N * Xi) * (2 * CYo sys L N * M) +
  K3c sys L Hunit N nd M / (n : ℝ) ^ 3 +
  2 * (eRate sys L Hunit N * Xi) * (2 * Real.sqrt (BopY sys L Hunit N n) * M) +
  CZle sys L n * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd')) +
  2 * (CWY sys L N n nd' * M ^ 2) +
  2 * (eRate sys L Hunit N * Xi) * (RY2 sys L n * M)

variable (sys L) in
/-- The endpoint constant of the box ledger. -/
noncomputable def EndBox (Hunit : ℝ) (N n : ℕ) (M : ℝ) : ℝ :=
  2 * (Cend sys L Hunit * M ^ 2 * (gF L * n) ^ (-(3 : ℝ))) +
  2 * (2 * (CYb sys L * M ^ 2 * (gF L * n) ^ (-(3 : ℝ))) +
    3 * (CYt sys L N * (eta ^ 2 * M ^ 2 * (gF L * n / 4) ^ (-(4 : ℝ))))) +
  2 * (K3e sys L Hunit N M / (n : ℝ) ^ 3) +
  2 * (CY2 sys L n * M ^ 2)

/-- **The box ledger bound**: for the box states along the trajectory,
`|∫₀ᵗ Re⟨u, X_N u⟩| ≤ t RateBox + EndBox`. -/
theorem ledger_box_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (p₀ : Fin eta) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {N n : ℕ} (hn : 64 ≤ n) (hnN : n ≤ N) (hl : 1 ≤ gF L * (cst sys * n)) {nd nd' : ℕ}
    (hnd : gF L * (2 * N) ≤ 2 ^ nd) (hnd' : gF L * ((n : ℝ) / 4) ≤ 2 ^ nd')
    (D : EvoData L H) {t : ℝ} (ht : 0 ≤ t) :
    |∫ s in (0 : ℝ)..t, (⟪ub H D N s, XN sys L p₀ N n (ub H D N s)⟫_ℂ).re| ≤
      t * RateBox sys L Hunit N n nd nd' (2 * (cTr sys L Hunit * D.Xi)) D.Xi +
        EndBox sys L Hunit N n (2 * (cTr sys L Hunit * D.Xi)) := by
  have hg := gF_pos hL
  have hcs := cst_pos sys
  have hc32 := cst_le32 sys
  have hn1 : 1 ≤ n := by omega
  have hn8 : 8 ≤ n := by omega
  have hN : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hnR : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hgn : 32 ≤ gF L * n := by
    have : gF L * (cst sys * n) * 32 ≤ gF L * n := by
      have : cst sys * 32 ≤ 1 := by linarith
      nlinarith
    linarith
  have hK4 : 4 ≤ gF L * n := by linarith
  have hgN : 2 ≤ gF L * N := by nlinarith
  have hgN1 : 1 ≤ gF L * N := by linarith
  have hl64 : 1 ≤ gF L * (3 * n / 64) := by
    have : gF L * (cst sys * n) ≤ gF L * (3 * n / 64) := by
      apply mul_le_mul_of_nonneg_left _ hg.le
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    linarith
  have hl4 : 1 ≤ gF L * ((n : ℝ) / 4) := by
    have : gF L * (cst sys * n) ≤ gF L * ((n : ℝ) / 4) := by
      apply mul_le_mul_of_nonneg_left _ hg.le
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    linarith
  set M := 2 * (cTr sys L Hunit * D.Xi) with hMdef
  have hu : ∀ s, IsGood sys L 1 M (ub H D N s) := fun s => ub_good sys hL H hKernel Hunit hPeriodic D N s
  have hM : 0 ≤ M := good_M_nonneg (hu 0)
  have hΞ := D.Xi_nonneg
  have heR : 0 ≤ eRate sys L Hunit N := by
    unfold eRate
    have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
    have := cTr_nonneg sys hL Hunit
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ gF L * N) (-(3 / 2 : ℝ))
    positivity
  have he0 : 0 ≤ 2 * (eRate sys L Hunit N * D.Xi) := by positivity
  rw [ledger_box_eq sys hL H hKernel p₀ n hn1 Hunit hPeriodic D t]
  -- the integrals
  have i1 := abs_integral_le_of ht (C := 2 * (Cbd sys L * M ^ 2 * (1 / (N : ℝ) + 1 / (gF L * N))) +
      8 * Hrs sys L Hunit ^ 2 * M ^ 2 * (gF L * (cst sys * n)) ^ (-(3 : ℝ)) +
      6 * (Hrs sys L Hunit * CYo sys L N * eta * M ^ 2 * (gF L * (cst sys * n)) ^ (-(3 : ℝ))))
    (f := fun s => (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Whc sys L p₀ n -
        Whc sys L p₀ n ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re -
      (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y1N sys L p₀ N n - Y1N sys L p₀ N n ∘ₗ WN sys L N))
        (ub H D N s)⟫_ℂ).re -
      (⟪ub H D N s, NFC sys L p₀ N n (ub H D N s)⟫_ℂ).re +
      (⟪ub H D N s, ZaN sys L p₀ N n (ub H D N s)⟫_ℂ).re) (fun s => by
        rw [Rf_eq sys hL H hKernel p₀ n hn1]
        have a1 := (Complex.abs_re_le_norm _).trans
          (norm_ebd_good sys hL H hKernel p₀ hN2 hgN (hu s))
        have a2 := (Complex.abs_re_le_norm _).trans
          (norm_ebd_good sys hL H hKernel p₀ hN2 hgN (isGood_res sys (hu s)
            (fun q : Cfg eta N => InP (n : ℝ) (cidx N q))))
        have a3 := norm_nflRR_le sys p₀ hL H hKernel Hunit hPeriodic hl (hu s)
        have a4 := norm_cmRR_le sys p₀ hL H hKernel Hunit hPeriodic hl (hu s)
        have b1 := abs_le.mp a1
        have b2 := abs_le.mp a2
        have b3 := abs_le.mp a3
        have b4 := abs_le.mp a4
        rw [abs_le]
        constructor <;> linarith)
  have i2 := abs_integral_le_of ht (C := 2 * (eRate sys L Hunit N * D.Xi) * (2 * CH sys L Hunit * M))
    (f := fun s => eY sys H D (Whc sys L p₀ n : En eta N →ₗ[ℂ] En eta N) s) (fun s =>
      (abs_eY_le hL H hKernel Hunit hPeriodic D hgN1 _ s).trans
        (mul_le_mul_of_nonneg_left (norm_Whc_good hL Hunit hPeriodic (hu s)) he0))
  have i3 := abs_integral_le_of ht
    (C := 3 * CRt sys L * (cXw sys L * (eta ^ 2 * M ^ 2 * (gF L * (3 * n / 64)) ^ (-(3 : ℝ)))))
    (f := fun s => (⟪ub H D N s, XresN sys L p₀ N n (ub H D N s)⟫_ℂ).re) (fun s =>
      abs_re_inner_le (norm_Xres_le hL H hKernel hn hl64 (hu s)))
  have i4 := abs_integral_le_of ht (C := 2 * (eRate sys L Hunit N * D.Xi) * (2 * CYo sys L N * M))
    (f := fun s => eY sys H D (Y1N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N) s) (fun s =>
      (abs_eY_le hL H hKernel Hunit hPeriodic D hgN1 _ s).trans
        (mul_le_mul_of_nonneg_left (norm_Y1N_good hL H hKernel (hu s)) he0))
  have i5 := abs_integral_le_of ht (C := K3c sys L Hunit N nd M / (n : ℝ) ^ 3)
    (f := fun s => (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y3N sys L p₀ N n -
          Y3N sys L p₀ N n ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re) (fun s =>
      abs_comm_Y3_good_le hL H hKernel Hunit hPeriodic hn8 hnN hnd hl (hu s))
  have i6 := abs_integral_le_of ht
    (C := 2 * (eRate sys L Hunit N * D.Xi) * (2 * Real.sqrt (BopY sys L Hunit N n) * M))
    (f := fun s => eY sys H D (Y3N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N) s) (fun s =>
      (abs_eY_le hL H hKernel Hunit hPeriodic D hgN1 _ s).trans
        (mul_le_mul_of_nonneg_left (norm_Y3N_good hL H hKernel Hunit hPeriodic hn1 hN (hu s)) he0))
  have i7 := abs_integral_le_of ht
    (C := CZle sys L n * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd')))
    (f := fun s => (⟪ub H D N s, FSKernel.kop (zaLe sys L p₀ N n) (ub H D N s)⟫_ℂ).re) (fun s =>
      abs_re_inner_le (norm_form_zaLe_good hL H hKernel hn8 hnd' (hu s)))
  have i8 := abs_integral_le_of ht (C := 2 * (CWY sys L N n nd' * M ^ 2))
    (f := fun s => (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y2N sys L p₀ N n -
          Y2N sys L p₀ N n ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re) (fun s =>
      norm_comm_WY2_good hL H hKernel hn8 hN hnd' (hu s))
  have i9 := abs_integral_le_of ht (C := 2 * (eRate sys L Hunit N * D.Xi) * (RY2 sys L n * M))
    (f := fun s => eY sys H D (Y2N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N) s) (fun s =>
      (abs_eY_le hL H hKernel Hunit hPeriodic D hgN1 _ s).trans
        (mul_le_mul_of_nonneg_left (norm_Y2N_good hL H hKernel hn8 (hu s)) he0))
  -- the endpoints
  have j1 : ∀ s, |(⟪ub H D N s, Whc sys L p₀ n (ub H D N s)⟫_ℂ).re| ≤
      Cend sys L Hunit * M ^ 2 * (gF L * n) ^ (-(3 : ℝ)) := fun s =>
    abs_re_inner_le (norm_Whc_form_le sys p₀ hL Hunit hPeriodic (by omega) hK4 (hu s))
  have j2 : ∀ s, |(⟪ub H D N s, Y1N sys L p₀ N n (ub H D N s)⟫_ℂ).re| ≤
      2 * (CYb sys L * M ^ 2 * (gF L * n) ^ (-(3 : ℝ))) +
        3 * (CYt sys L N * (eta ^ 2 * M ^ 2 * (gF L * n / 4) ^ (-(4 : ℝ)))) := fun s =>
    abs_re_inner_le (norm_Y1_form_le hL H hKernel hn8 hK4 (hu s))
  have j3 : ∀ s, |(⟪ub H D N s, Y3N sys L p₀ N n (ub H D N s)⟫_ℂ).re| ≤
      K3e sys L Hunit N M / (n : ℝ) ^ 3 := fun s =>
    abs_re_inner_le (abs_inner_Y3_good_le hL H hKernel Hunit hPeriodic hn1 hN hl4 (hu s))
  have j4 : ∀ s, |(⟪ub H D N s, Y2N sys L p₀ N n (ub H D N s)⟫_ℂ).re| ≤ CY2 sys L n * M ^ 2 :=
    fun s => abs_re_inner_le (norm_Y2_form_good hL H hKernel hn8 (hu s))
  have k1 := abs_le.mp (j1 t)
  have k1' := abs_le.mp (j1 0)
  have k2 := abs_le.mp (j2 t)
  have k2' := abs_le.mp (j2 0)
  have k3 := abs_le.mp (j3 t)
  have k3' := abs_le.mp (j3 0)
  have k4 := abs_le.mp (j4 t)
  have k4' := abs_le.mp (j4 0)
  have l1 := abs_le.mp i1
  have l2 := abs_le.mp i2
  have l3 := abs_le.mp i3
  have l4 := abs_le.mp i4
  have l5 := abs_le.mp i5
  have l6 := abs_le.mp i6
  have l7 := abs_le.mp i7
  have l8 := abs_le.mp i8
  have l9 := abs_le.mp i9
  have hR : t * RateBox sys L Hunit N n nd nd' M D.Xi =
      t * (2 * (Cbd sys L * M ^ 2 * (1 / (N : ℝ) + 1 / (gF L * N))) +
        8 * Hrs sys L Hunit ^ 2 * M ^ 2 * (gF L * (cst sys * n)) ^ (-(3 : ℝ)) +
        6 * (Hrs sys L Hunit * CYo sys L N * eta * M ^ 2 * (gF L * (cst sys * n)) ^ (-(3 : ℝ)))) +
      t * (2 * (eRate sys L Hunit N * D.Xi) * (2 * CH sys L Hunit * M)) +
      t * (3 * CRt sys L * (cXw sys L * (eta ^ 2 * M ^ 2 * (gF L * (3 * n / 64)) ^ (-(3 : ℝ))))) +
      t * (2 * (eRate sys L Hunit N * D.Xi) * (2 * CYo sys L N * M)) +
      t * (K3c sys L Hunit N nd M / (n : ℝ) ^ 3) +
      t * (2 * (eRate sys L Hunit N * D.Xi) * (2 * Real.sqrt (BopY sys L Hunit N n) * M)) +
      t * (CZle sys L n * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd'))) +
      t * (2 * (CWY sys L N n nd' * M ^ 2)) +
      t * (2 * (eRate sys L Hunit N * D.Xi) * (RY2 sys L n * M)) := by
    unfold RateBox; ring
  have hE : EndBox sys L Hunit N n M =
      2 * (Cend sys L Hunit * M ^ 2 * (gF L * n) ^ (-(3 : ℝ))) +
      2 * (2 * (CYb sys L * M ^ 2 * (gF L * n) ^ (-(3 : ℝ))) +
        3 * (CYt sys L N * (eta ^ 2 * M ^ 2 * (gF L * n / 4) ^ (-(4 : ℝ))))) +
      2 * (K3e sys L Hunit N M / (n : ℝ) ^ 3) +
      2 * (CY2 sys L n * M ^ 2) := by
    unfold EndBox; ring
  rw [hR, hE, abs_le]
  constructor <;> linarith

/-- **The flux on the box**: `|∫₀ᵗ F| ≤ t (C_B (c_Tr Ξ)² (gN)^{-1/2} + RateBox) + EndBox`, where
`F(s) = Re⟨ψ, Gψ⟩ - Re⟨Pψ, GPψ⟩` along the exact trajectory. -/
theorem flux_box_total (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (p₀ : Fin eta) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {N n : ℕ} (hn : 64 ≤ n) (hnN : n ≤ N) (hl : 1 ≤ gF L * (cst sys * n)) {nd nd' : ℕ}
    (hnd : gF L * (2 * N) ≤ 2 ^ nd) (hnd' : gF L * ((n : ℝ) / 4) ≤ 2 ^ nd')
    (D : EvoData L H) {t : ℝ} (ht : 0 ≤ t) :
    |∫ s in (0 : ℝ)..t, ((Gf sys L H p₀ (traj H D s) (traj H D s)).re -
        (Gf sys L H p₀ (molecularH2Truncate n (traj H D s))
          (molecularH2Truncate n (traj H D s))).re)| ≤
      t * (CB sys L Hunit * (cTr sys L Hunit * D.Xi) ^ 2 * (gF L * N) ^ (-(1 / 2 : ℝ)) +
          RateBox sys L Hunit N n nd nd' (2 * (cTr sys L Hunit * D.Xi)) D.Xi) +
        EndBox sys L Hunit N n (2 * (cTr sys L Hunit * D.Xi)) := by
  have hg := gF_pos hL
  have hcs := cst_pos sys
  have hc32 := cst_le32 sys
  have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hgN1 : 1 ≤ gF L * N := by
    have : gF L * (cst sys * n) ≤ gF L * N := by
      apply mul_le_mul_of_nonneg_left _ hg.le
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    linarith
  have hct := continuous_traj sys hL H hKernel Hunit hPeriodic D
  have hcF : Continuous fun s => (Gf sys L H p₀ (traj H D s) (traj H D s)).re -
      (Gf sys L H p₀ (molecularH2Truncate n (traj H D s)) (molecularH2Truncate n (traj H D s))).re := by
    have hP := (continuous_trunc n).comp hct
    exact (Complex.continuous_re.comp (continuous_Gf sys H p₀ hct hct)).sub
      (Complex.continuous_re.comp (continuous_Gf sys H p₀ hP hP))
  have hcG := continuous_form_ub H (N := N) D (XN sys L p₀ N n)
  have hcFG : Continuous fun s => (Gf sys L H p₀ (traj H D s) (traj H D s)).re -
      (Gf sys L H p₀ (molecularH2Truncate n (traj H D s)) (molecularH2Truncate n (traj H D s))).re -
      (⟪ub H D N s, XN sys L p₀ N n (ub H D N s)⟫_ℂ).re := hcF.sub hcG
  have hpt : ∀ s, |(Gf sys L H p₀ (traj H D s) (traj H D s)).re -
      (Gf sys L H p₀ (molecularH2Truncate n (traj H D s)) (molecularH2Truncate n (traj H D s))).re -
      (⟪ub H D N s, XN sys L p₀ N n (ub H D N s)⟫_ℂ).re| ≤
      CB sys L Hunit * (cTr sys L Hunit * D.Xi) ^ 2 * (gF L * N) ^ (-(1 / 2 : ℝ)) := by
    intro s
    obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D s
    have hw : traj H D s = w := traj_eq H D s w hw1
    rw [ub_eq, hw]
    exact flux_box sys hL H hKernel p₀ Hunit hPeriodic hnN hgN1 hF
  have hI : ∫ s in (0 : ℝ)..t, ((Gf sys L H p₀ (traj H D s) (traj H D s)).re -
        (Gf sys L H p₀ (molecularH2Truncate n (traj H D s)) (molecularH2Truncate n (traj H D s))).re) =
      (∫ s in (0 : ℝ)..t, ((Gf sys L H p₀ (traj H D s) (traj H D s)).re -
        (Gf sys L H p₀ (molecularH2Truncate n (traj H D s)) (molecularH2Truncate n (traj H D s))).re -
        (⟪ub H D N s, XN sys L p₀ N n (ub H D N s)⟫_ℂ).re)) +
      ∫ s in (0 : ℝ)..t, (⟪ub H D N s, XN sys L p₀ N n (ub H D N s)⟫_ℂ).re := by
    rw [← intervalIntegral.integral_add (hcFG.intervalIntegrable 0 t) (hcG.intervalIntegrable 0 t)]
    congr 1
    funext s
    ring
  have h1 := abs_integral_le_of ht hpt
  have h2 := ledger_box_le hL H hKernel p₀ Hunit hPeriodic hn hnN hl hnd hnd' D ht
  rw [hI]
  refine (abs_add_le _ _).trans ?_
  linarith

end LedgerBound

end FSFlux
