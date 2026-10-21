import PlaneWave.FluxBox.BlockBound

/-!
# Flux route, stage 3, part 47: round 3 on good box states

* tails of a good box state: `‖u_F‖ ≤ η M (gn/4)^{-5/2}` (`norm_res_far_good`) and
  `‖W u_{¬C}‖ ≤ C_H √2 η M (g c_* n)^{-3/2}` (`norm_W_notC_good`);
* the products of the round-3 commutator: P2 (`P2_prod_good`: `‖W u_{¬C}‖ ‖Ỹ u‖ ≤ √(α_W K_{P2,g})/n³`)
  and P3 (`P3_prod_good`: `‖Ỹ W u‖ ‖u_F‖ ≤ √(K_{P2} #ch³ B₃' η² M² (4/g)⁵)/n³`);
* **the round-3 commutator on a good box state** (`abs_comm_Y3_good_le`: `|Re⟨u, i[W,Y₃] u⟩| ≤ K₃/n³`);
* **the round-3 endpoint** (`abs_inner_Y3_good_le`: `|⟨u, Y₃ u⟩| ≤ K₃ₑ/n³`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Alg

omit [Fintype ν] in
lemma rpow_m52_sq {x : ℝ} (hx : 0 < x) : (x ^ (-(5 / 2 : ℝ))) ^ 2 = 1 / x ^ 5 := by
  have e : (x ^ (-(5 / 2 : ℝ))) ^ 2 = x ^ (-(5 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  rw [e, Real.rpow_neg hx.le, one_div]
  norm_cast

omit [Fintype ν] in
lemma rpow_m32_sq {x : ℝ} (hx : 0 < x) : (x ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / x ^ 3 := by
  have e : (x ^ (-(3 / 2 : ℝ))) ^ 2 = x ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  rw [e, Real.rpow_neg hx.le, one_div]
  norm_cast

omit [Fintype ν] in
/-- Products from squares: `a² ≤ A/m^p`, `b² ≤ B/m^q`, `p + q = 6` give `ab ≤ √(AB)/m³`. -/
lemma mul_le_sqrt_div {a b A B m : ℝ} {p q : ℕ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hm : 0 < m) (h1 : a ^ 2 ≤ A / m ^ p) (h2 : b ^ 2 ≤ B / m ^ q) (hpq : p + q = 6) :
    a * b ≤ Real.sqrt (A * B) / m ^ 3 := by
  have hab : (a * b) ^ 2 ≤ A * B / (m ^ 3) ^ 2 := by
    rw [mul_pow]
    calc a ^ 2 * b ^ 2 ≤ (A / m ^ p) * (B / m ^ q) := mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = A * B / (m ^ 3) ^ 2 := by
          rw [div_mul_div_comm, ← pow_add, hpq, ← pow_mul]
  have h3 : a * b = Real.sqrt ((a * b) ^ 2) := (Real.sqrt_sq (mul_nonneg ha hb)).symm
  rw [h3]
  calc Real.sqrt ((a * b) ^ 2) ≤ Real.sqrt (A * B / (m ^ 3) ^ 2) := Real.sqrt_le_sqrt hab
    _ = Real.sqrt (A * B) / m ^ 3 := by
        rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]

end Alg

/-! ## Tails of a good box state -/

section Tails

variable {sys : CoulombSystem eta ν} {L : ℝ} {N : ℕ}

omit [Fintype ν] in
lemma kabs_gt_of_not_inQ (hL : 0 < L) {n : ℕ} {q : Cfg eta N} (h : ¬ InQ (n : ℝ) (cidx N q)) :
    ∃ c, gF L * ((n : ℝ) / 4) < finitePlaneWaveKabs (2 * Real.pi / L) N (q c) := by
  simp only [InQ, not_forall, not_le] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, kabs_gt_of_lsq_gt hL (by positivity) q c hc⟩

omit [Fintype ν] in
/-- **The far tail of a good box state**: `‖u_F‖ ≤ η M (gn/4)^{-5/2}`. -/
lemma norm_res_far_good (hL : 0 < L) {n : ℕ} (hl : 1 ≤ gF L * ((n : ℝ) / 4)) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) u‖ ≤
      eta * M * (gF L * ((n : ℝ) / 4)) ^ (-(5 / 2 : ℝ)) :=
  (res_tails_good sys hu _ hl (fun _ hq => kabs_gt_of_not_inQ hL hq)).1

omit [Fintype ν] in
/-- `‖u_F‖² ≤ η² M² (4/g)⁵/n⁵`. -/
lemma sq_norm_res_far_good (hL : 0 < L) {n : ℕ} (hn : 1 ≤ n) (hl : 1 ≤ gF L * ((n : ℝ) / 4)) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) u‖ ^ 2 ≤
      eta ^ 2 * M ^ 2 * (4 / gF L) ^ 5 / (n : ℝ) ^ 5 := by
  have hg := gF_pos hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hM := good_M_nonneg hu
  have hx : 0 < gF L * ((n : ℝ) / 4) := by positivity
  have h := norm_res_far_good hL hl hu
  have h0 := norm_nonneg (FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) u)
  refine (pow_le_pow_left₀ h0 h 2).trans (le_of_eq ?_)
  rw [mul_pow, rpow_m52_sq hx]
  field_simp

/-- **The cold-complement potential of a good box state**: `‖W u_{¬C}‖ ≤ C_H √2 η M (g c_* n)^{-3/2}`. -/
lemma norm_W_notC_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {n : ℕ}
    (hl : 1 ≤ gF L * (cst sys * n)) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖WN sys L N (FSKernel.res (fun p => ¬ InC (n : ℝ) (cst sys) (cidx N p)) u)‖ ≤
      CH sys L Hunit * (Real.sqrt 2 * eta * M * (gF L * (cst sys * n)) ^ (-(3 / 2 : ℝ))) := by
  have hW : WN sys L N = FSKernel.kop (wNK sys L N) := VN_eq_kop sys hL H hKernel
  rw [hW]
  exact norm_kop_res_cold_le sys hL Hunit hPeriodic hl hu _ (fun q p => norm_potKernel_le sys hL _ _)
    _ (fun q hq => hq)

/-- `‖W u_{¬C}‖² ≤ 2 C_H² η² M²/(g c_*)³ / n³`. -/
lemma sq_norm_W_notC_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {n : ℕ} (hn : 1 ≤ n)
    (hl : 1 ≤ gF L * (cst sys * n)) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖WN sys L N (FSKernel.res (fun p => ¬ InC (n : ℝ) (cst sys) (cidx N p)) u)‖ ^ 2 ≤
      2 * CH sys L Hunit ^ 2 * eta ^ 2 * M ^ 2 / (gF L * cst sys) ^ 3 / (n : ℝ) ^ 3 := by
  have hg := gF_pos hL
  have hcs := cst_pos sys
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hM := good_M_nonneg hu
  have hCH := CH_nonneg sys hL Hunit
  have hx : 0 < gF L * (cst sys * n) := by positivity
  have h := norm_W_notC_good hL H hKernel Hunit hPeriodic hl hu
  have h0 := norm_nonneg (WN sys L N (FSKernel.res (fun p => ¬ InC (n : ℝ) (cst sys) (cidx N p)) u))
  refine (pow_le_pow_left₀ h0 h 2).trans (le_of_eq ?_)
  rw [mul_pow, mul_pow, mul_pow, mul_pow, rpow_m32_sq hx, Real.sq_sqrt (by norm_num)]
  field_simp

end Tails

/-! ## The round-3 commutator and endpoint on good box states -/

section Round3

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

variable (sys L) in
/-- The P2 constant of a good state: `‖Ỹ u‖² ≤ KP2g/n³`. -/
noncomputable def KP2g (Hunit : ℝ) (N : ℕ) (M : ℝ) : ℝ :=
  KP2 sys L Hunit N * ((Fintype.card (Ch eta) : ℝ) *
    (125 * (Nat.log 2 (2 * N) + 2) * (4 * cXw sys L ^ 2 * M ^ 2)))

lemma KP2g_nonneg (hL : 0 < L) (Hunit : ℝ) (N : ℕ) (M : ℝ) : 0 ≤ KP2g sys L Hunit N M := by
  unfold KP2g
  have := KP2_nonneg (sys := sys) hL Hunit N
  positivity

/-- **P2 on a good box state**: `‖W u_{¬C}‖ ‖Ỹ u‖ ≤ √(α_W KP2g)/n³`. -/
theorem P2_prod_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hl : 1 ≤ gF L * (cst sys * n)) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖WN sys L N (FSKernel.res (fun p => ¬ InC (n : ℝ) (cst sys) (cidx N p)) u)‖ *
        ‖Yt sys L p₀ N n u‖ ≤
      Real.sqrt (2 * CH sys L Hunit ^ 2 * eta ^ 2 * M ^ 2 / (gF L * cst sys) ^ 3 *
        KP2g sys L Hunit N M) / (n : ℝ) ^ 3 := by
  have hH := finiteSupportUnitLatticeCoulombHardyBound_of_canonicalPeriodic Hunit hPeriodic
  have hg := gF_pos hL
  have hcs := cst_pos sys
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := sq_norm_W_notC_good hL H hKernel Hunit hPeriodic hn hl hu
  have h2 : ‖Yt sys L p₀ N n u‖ ^ 2 ≤ KP2g sys L Hunit N M / (n : ℝ) ^ 3 := by
    have := norm_sq_Yt_good_le (p₀ := p₀) hH hL hn hN H hKernel hu
    unfold KP2g
    refine this.trans (le_of_eq ?_)
    ring
  have hCH := CH_nonneg sys hL Hunit
  exact mul_le_sqrt_div (norm_nonneg _) (norm_nonneg _) (by positivity) (KP2g_nonneg hL Hunit N M)
    hn0 h1 h2 rfl

variable (sys L) in
/-- The P3 line-square constant without the cutoff: `B₃ ≤ n² B₃'`. -/
noncomputable def B3n (Hunit : ℝ) (N nd : ℕ) (M : ℝ) : ℝ :=
  (81 * cSum sys L) ^ 2 * (125 * (Nat.log 2 (2 * N) + 2) * (4 * cXw sys L ^ 2 * M ^ 2)) +
    cSum sys L ^ 2 * (Hunit ^ 2 * (125 * (Nat.log 2 (2 * N) + 2) *
      (W5c sys L * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd)))))

lemma B3n_nonneg (hL : 0 < L) (Hunit : ℝ) (N nd : ℕ) (M : ℝ) : 0 ≤ B3n sys L Hunit N nd M := by
  unfold B3n
  have := cSum_nonneg (sys := sys) hL
  have := W5c_nonneg (sys := sys) hL
  have : (0 : ℝ) ≤ (1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  positivity

lemma B3_le_B3n (hL : 0 < L) (Hunit : ℝ) (hn : 2 ≤ n) (N nd : ℕ) (M : ℝ) :
    B3 sys L Hunit N n nd M ≤ (n : ℝ) ^ 2 * B3n sys L Hunit N nd M := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hcs := cst_pos sys
  have hc32 := cst_le32 sys
  have hcS := cSum_nonneg (sys := sys) hL
  have hW := W5c_nonneg (sys := sys) hL
  have hr : (0 : ℝ) ≤ (1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hX : 0 ≤ 125 * ((Nat.log 2 (2 * N) : ℝ) + 2) * (4 * cXw sys L ^ 2 * M ^ 2) := by positivity
  have hY : 0 ≤ cSum sys L ^ 2 * (Hunit ^ 2 * (125 * ((Nat.log 2 (2 * N) : ℝ) + 2) *
      (W5c sys L * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd))))) := by
    positivity
  have h1 : (cst sys * n + 1) ^ 2 ≤ (n : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  unfold B3 B3n
  have e1 : (81 * (cst sys * n + 1) * cSum sys L) ^ 2 =
      (cst sys * n + 1) ^ 2 * (81 * cSum sys L) ^ 2 := by ring
  rw [e1, mul_add]
  have h3 : (cst sys * n + 1) ^ 2 * (81 * cSum sys L) ^ 2 *
      (125 * ((Nat.log 2 (2 * N) : ℝ) + 2) * (4 * cXw sys L ^ 2 * M ^ 2)) ≤
      (n : ℝ) ^ 2 * ((81 * cSum sys L) ^ 2 *
        (125 * ((Nat.log 2 (2 * N) : ℝ) + 2) * (4 * cXw sys L ^ 2 * M ^ 2))) := by
    have h5 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (sq_nonneg (81 * cSum sys L)) hX)
    calc (cst sys * n + 1) ^ 2 * (81 * cSum sys L) ^ 2 *
          (125 * ((Nat.log 2 (2 * N) : ℝ) + 2) * (4 * cXw sys L ^ 2 * M ^ 2)) =
        (cst sys * n + 1) ^ 2 * ((81 * cSum sys L) ^ 2 *
          (125 * ((Nat.log 2 (2 * N) : ℝ) + 2) * (4 * cXw sys L ^ 2 * M ^ 2))) := by ring
      _ ≤ _ := h5
  have h4 := le_mul_of_one_le_left hY h2
  linarith

/-- **P3 on a good box state**: `‖Ỹ W u‖ ‖u_F‖ ≤ √(K_{P2} #ch³ B₃' η² M² (4/g)⁵)/n³`. -/
theorem P3_prod_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hn : 2 ≤ n) (hN : 1 ≤ N)
    {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd) (hl : 1 ≤ gF L * ((n : ℝ) / 4)) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖Yt sys L p₀ N n (WN sys L N u)‖ * ‖FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) u‖ ≤
      Real.sqrt (KP2 sys L Hunit N * (Fintype.card (Ch eta) : ℝ) ^ 3 * B3n sys L Hunit N nd M *
        (eta ^ 2 * M ^ 2 * (4 / gF L) ^ 5)) / (n : ℝ) ^ 3 := by
  classical
  have hH := finiteSupportUnitLatticeCoulombHardyBound_of_canonicalPeriodic Hunit hPeriodic
  have hg := gF_pos hL
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hK := KP2_nonneg (sys := sys) hL Hunit N
  have hB := B3n_nonneg (sys := sys) hL Hunit N nd M
  have h1 : ‖Yt sys L p₀ N n (WN sys L N u)‖ ^ 2 ≤
      KP2 sys L Hunit N * (Fintype.card (Ch eta) : ℝ) ^ 3 * B3n sys L Hunit N nd M / (n : ℝ) ^ 1 := by
    have h := norm_sq_Yt_cold_le (p₀ := p₀) hH hL hn1 H hKernel (WN sys L N u)
    have h3 := lineSq_CWu_good_le (n := n) hH hL hN hnd H hKernel hu
    have h4 := B3_le_B3n (sys := sys) hL Hunit hn N nd M
    refine h.trans ?_
    have hc : (0 : ℝ) ≤ (Fintype.card (Ch eta) : ℝ) ^ 3 := by positivity
    calc KP2 sys L Hunit N / (n : ℝ) ^ 3 * ∑ j, lineSq j (fun _ => 1) (fun b =>
          if InC (n : ℝ) (cst sys) (cidx N b) then ‖(WN sys L N u).ofLp b‖ else 0) ≤
        KP2 sys L Hunit N / (n : ℝ) ^ 3 *
          ((Fintype.card (Ch eta) : ℝ) ^ 3 * ((n : ℝ) ^ 2 * B3n sys L Hunit N nd M)) :=
          mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 hc)) (by positivity)
      _ = _ := by field_simp
  have h2 := sq_norm_res_far_good hL hn1 hl hu
  refine mul_le_sqrt_div (norm_nonneg _) (norm_nonneg _) (by positivity) (by positivity) hn0 h1 h2 rfl

variable (sys L) in
/-- The round-3 commutator constant of a good box state. -/
noncomputable def K3c (Hunit : ℝ) (N nd : ℕ) (M : ℝ) : ℝ :=
  2 * KCC sys L N nd M Hunit +
    2 * Real.sqrt (2 * CH sys L Hunit ^ 2 * eta ^ 2 * M ^ 2 / (gF L * cst sys) ^ 3 *
      KP2g sys L Hunit N M) +
    2 * Real.sqrt (KP2 sys L Hunit N * (Fintype.card (Ch eta) : ℝ) ^ 3 * B3n sys L Hunit N nd M *
      (eta ^ 2 * M ^ 2 * (4 / gF L) ^ 5))

/-- **The round-3 commutator on a good box state**: `|Re⟨u, i[W, Y₃] u⟩| ≤ K₃/n³`. -/
theorem abs_comm_Y3_good_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hn : 8 ≤ n)
    (hnN : n ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd) (hl : 1 ≤ gF L * (cst sys * n)) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) :
    |(⟪u, (Complex.I • (WN sys L N ∘ₗ Y3N sys L p₀ N n - Y3N sys L p₀ N n ∘ₗ WN sys L N)) u⟫_ℂ).re| ≤
      K3c sys L Hunit N nd M / (n : ℝ) ^ 3 := by
  have hH := finiteSupportUnitLatticeCoulombHardyBound_of_canonicalPeriodic Hunit hPeriodic
  have hN : 1 ≤ N := by omega
  have hn1 : 1 ≤ n := by omega
  have hcs := cst_pos sys
  have hc32 := cst_le32 sys
  have hl4 : 1 ≤ gF L * ((n : ℝ) / 4) := by
    have hg := gF_pos hL
    have : gF L * (cst sys * n) ≤ gF L * ((n : ℝ) / 4) := by
      apply mul_le_mul_of_nonneg_left _ hg.le
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    linarith
  have hsplit := abs_comm_Y3_sub_CC_le (p₀ := p₀) hL H hKernel hn1 u
  have hCC := abs_im_CC_good_le (p₀ := p₀) hH hL hn hnN hnd hu H hKernel
  have hP2 := P2_prod_good (p₀ := p₀) hL H hKernel Hunit hPeriodic hn1 hN hl hu
  have hP3 := P3_prod_good (p₀ := p₀) hL H hKernel Hunit hPeriodic (by omega) hN hnd hl4 hu
  have habs := abs_sub_abs_le_abs_sub
    (⟪u, (Complex.I • (WN sys L N ∘ₗ Y3N sys L p₀ N n - Y3N sys L p₀ N n ∘ₗ WN sys L N)) u⟫_ℂ).re
    (-(2 * (⟪WN sys L N (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u),
      Yt sys L p₀ N n (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u)⟫_ℂ).im))
  rw [sub_neg_eq_add, abs_neg, abs_mul, abs_two] at habs
  unfold K3c
  rw [add_div, add_div]
  have e1 : 2 * KCC sys L N nd M Hunit / (n : ℝ) ^ 3 = 2 * (KCC sys L N nd M Hunit / (n : ℝ) ^ 3) := by
    ring
  have e2 : 2 * Real.sqrt (2 * CH sys L Hunit ^ 2 * eta ^ 2 * M ^ 2 / (gF L * cst sys) ^ 3 *
      KP2g sys L Hunit N M) / (n : ℝ) ^ 3 = 2 * (Real.sqrt (2 * CH sys L Hunit ^ 2 * eta ^ 2 * M ^ 2 /
      (gF L * cst sys) ^ 3 * KP2g sys L Hunit N M) / (n : ℝ) ^ 3) := by ring
  have e3 : 2 * Real.sqrt (KP2 sys L Hunit N * (Fintype.card (Ch eta) : ℝ) ^ 3 *
      B3n sys L Hunit N nd M * (eta ^ 2 * M ^ 2 * (4 / gF L) ^ 5)) / (n : ℝ) ^ 3 =
      2 * (Real.sqrt (KP2 sys L Hunit N * (Fintype.card (Ch eta) : ℝ) ^ 3 *
      B3n sys L Hunit N nd M * (eta ^ 2 * M ^ 2 * (4 / gF L) ^ 5)) / (n : ℝ) ^ 3) := by ring
  rw [e1, e2, e3]
  linarith

variable (sys L) in
/-- The round-3 endpoint constant of a good box state. -/
noncomputable def K3e (Hunit : ℝ) (N : ℕ) (M : ℝ) : ℝ :=
  2 * Real.sqrt (eta ^ 2 * M ^ 2 * (4 / gF L) ^ 5 * KP2g sys L Hunit N M)

/-- **The round-3 endpoint on a good box state**: `|⟨u, Y₃ u⟩| ≤ K₃ₑ/n³`. -/
theorem abs_inner_Y3_good_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hl : 1 ≤ gF L * ((n : ℝ) / 4)) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖⟪u, Y3N sys L p₀ N n u⟫_ℂ‖ ≤ K3e sys L Hunit N M / (n : ℝ) ^ 3 := by
  have hH := finiteSupportUnitLatticeCoulombHardyBound_of_canonicalPeriodic Hunit hPeriodic
  have hg := gF_pos hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine (abs_inner_Y3_le (p₀ := p₀) hL H hKernel hn u).trans ?_
  have h1 := sq_norm_res_far_good hL hn hl hu
  have hK := KP2g_nonneg (sys := sys) hL Hunit N M
  have h2' : ‖Yt sys L p₀ N n u‖ ^ 2 ≤ KP2g sys L Hunit N M / (n : ℝ) ^ 1 := by
    have := norm_sq_Yt_good_le (p₀ := p₀) hH hL hn hN H hKernel hu
    refine this.trans ?_
    unfold KP2g
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_left _ (by positivity) (by
      have : (n : ℝ) ^ 1 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
      exact this)
    have := KP2_nonneg (sys := sys) hL Hunit N
    positivity
  have hM := good_M_nonneg hu
  have hp := mul_le_sqrt_div (norm_nonneg _) (norm_nonneg _) (by positivity) hK hn0 h1 h2' rfl
  unfold K3e
  have e : 2 * Real.sqrt (eta ^ 2 * M ^ 2 * (4 / gF L) ^ 5 * KP2g sys L Hunit N M) / (n : ℝ) ^ 3 =
      2 * (Real.sqrt (eta ^ 2 * M ^ 2 * (4 / gF L) ^ 5 * KP2g sys L Hunit N M) / (n : ℝ) ^ 3) := by ring
  rw [e]
  linarith

end Round3

end FSFlux
