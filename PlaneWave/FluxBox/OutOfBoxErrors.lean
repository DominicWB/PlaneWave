import PlaneWave.FluxBox.Round3GoodStates

/-!
# Flux route, stage 3, part 48: the dressings on good box states and the out-of-box errors

* crude bounds of the four dressings on a good box state (`‖Y u‖ ≤ C M`): `‖Ŵ_c u‖ ≤ 2 C_H M`
  (`norm_Whc_good`), `‖Y₁ u‖ ≤ 2 C_{Yo} M` (`norm_Y1N_good`), `‖Y₂ u‖ ≤ R_{Y₂} M` (`norm_Y2N_good`),
  `‖Y₃ u‖ ≤ 2 √B_op M` (`norm_Y3N_good`, from the crude operator bound `norm_Yt_op_le`:
  `‖Ỹ x‖² ≤ K_{P2} #ch 500 (log₂ 2N + 2) n ‖x‖²`);
* **the out-of-box error of an elimination** (`abs_eY_le`):
  `|e_Y(s)| ≤ 2 √3 η C_m c_Tr Ξ (gN)^{-3/2} ‖Y u_s‖`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Crude

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

omit [Fintype ν] in
/-- `√(Σ (1 + 2E)|v|²) ≤ M` for a good box state. -/
lemma sqrt_wns_good {M : ℝ} {v : En eta N} (hv : IsGood sys L 1 M v) :
    Real.sqrt (weightedNormSq (hw sys L N) v) ≤ M := by
  have hM := good_M_nonneg hv
  refine (sqrt_wns_le sys v).trans ?_
  have h := hv.1
  rw [one_mul] at h
  have ha := norm_nonneg v
  have hb := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 v)
  rw [Real.sqrt_le_left hM]
  nlinarith

omit [Fintype ν] in
lemma norm_le_good {M : ℝ} {v : En eta N} (hv : IsGood sys L 1 M v) : ‖v‖ ≤ M := by
  have h := hv.1
  rw [one_mul] at h
  have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 v)
  linarith

/-- `‖Ŵ_c u‖ ≤ 2 C_H M` on a good box state. -/
lemma norm_Whc_good (hL : 0 < L) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖Whc sys L p₀ n u‖ ≤ 2 * CH sys L Hunit * M := by
  have hCH := CH_nonneg sys hL Hunit
  have h1 := (norm_WhN_le sys hL p₀ Hunit hPeriodic u).trans
    (mul_le_mul_of_nonneg_left (sqrt_wns_good hu) hCH)
  have h2 := (norm_WhN_le sys hL p₀ Hunit hPeriodic (PN N n u)).trans
    (mul_le_mul_of_nonneg_left (sqrt_wns_good (isGood_res sys hu _)) hCH)
  have h3 : ‖PN N n (WhN sys L p₀ N (PN N n u))‖ ≤ ‖WhN sys L p₀ N (PN N n u)‖ :=
    FSKernel.norm_res_le _ _
  unfold Whc
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-- `‖Y v‖ ≤ C_{Yo} M` on a good box state. -/
lemma norm_YcN_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {M : ℝ} {v : En eta N} (hv : IsGood sys L 1 M v) :
    ‖YcN sys L p₀ N v‖ ≤ CYo sys L N * M := by
  have hM := good_M_nonneg hv
  have hcX : 0 ≤ cXw sys L := by unfold cXw; have := gF_pos hL; have := one_le_mmax sys; positivity
  have hX : ∑ q, (1 + Xall q) * ‖v.ofLp q‖ ^ 2 ≤ cXw sys L * M ^ 2 := by
    refine (sum_Xall_le (sys := sys) hL v).trans (mul_le_mul_of_nonneg_left ?_ hcX)
    have h := hv.1
    rw [one_mul] at h
    have ha := norm_nonneg v
    have hb := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 v)
    nlinarith
  refine (norm_YcN_le hL H hKernel _).trans ?_
  unfold CYo
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have hC0 : 0 ≤ CYc sys L j * LamB sys N := mul_nonneg (CYc_nonneg hL j) (LamB_nonneg (sys := sys) N)
  have h1 : ∑ p, rY (sys := sys) (L := L) j p ^ 2 * ‖v.ofLp p‖ ^ 2 ≤
      (CYc sys L j * LamB sys N) ^ 2 * 2 * (cXw sys L * M ^ 2) := by
    have h2 : ∀ p : Cfg eta N, rY (sys := sys) (L := L) j p ^ 2 ≤
        (CYc sys L j * LamB sys N) ^ 2 * 2 * (1 + Xall p) := by
      intro p
      have h3 := rY_le (sys := sys) hL j p
      have h4 := rY_nonneg (sys := sys) hL j p
      have h5 : rY (sys := sys) (L := L) j p ^ 2 ≤
          (CYc sys L j * LamB sys N * (Real.sqrt 2 * Real.sqrt (Xall p))) ^ 2 :=
        pow_le_pow_left₀ h4 h3 2
      have e : (CYc sys L j * LamB sys N * (Real.sqrt 2 * Real.sqrt (Xall p))) ^ 2 =
          (CYc sys L j * LamB sys N) ^ 2 * 2 * Xall p := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (Xall_nonneg p)]; ring
      rw [e] at h5
      have : 0 ≤ (CYc sys L j * LamB sys N) ^ 2 * 2 := by positivity
      nlinarith
    calc ∑ p, rY (sys := sys) (L := L) j p ^ 2 * ‖v.ofLp p‖ ^ 2
        ≤ ∑ p, (CYc sys L j * LamB sys N) ^ 2 * 2 * ((1 + Xall p) * ‖v.ofLp p‖ ^ 2) := by
          refine Finset.sum_le_sum fun p _ => ?_
          calc rY (sys := sys) (L := L) j p ^ 2 * ‖v.ofLp p‖ ^ 2
              ≤ (CYc sys L j * LamB sys N) ^ 2 * 2 * (1 + Xall p) * ‖v.ofLp p‖ ^ 2 :=
                mul_le_mul_of_nonneg_right (h2 p) (sq_nonneg _)
            _ = _ := by ring
      _ = (CYc sys L j * LamB sys N) ^ 2 * 2 * ∑ p, (1 + Xall p) * ‖v.ofLp p‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hX (by positivity)
  refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
  rw [show (CYc sys L j * LamB sys N) ^ 2 * 2 * (cXw sys L * M ^ 2) =
    (CYc sys L j * LamB sys N * M) ^ 2 * (2 * cXw sys L) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_mul (by norm_num)]
  ring

/-- `‖Y₁ u‖ ≤ 2 C_{Yo} M` on a good box state. -/
lemma norm_Y1N_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖Y1N sys L p₀ N n u‖ ≤ 2 * CYo sys L N * M := by
  have h1 := norm_YcN_good (p₀ := p₀) hL H hKernel hu
  have h2 := norm_YcN_good (p₀ := p₀) hL H hKernel (isGood_res sys hu
    (fun q : Cfg eta N => InP (n : ℝ) (cidx N q)))
  have h3 : ‖PN N n (YcN sys L p₀ N (PN N n u))‖ ≤ ‖YcN sys L p₀ N (PN N n u)‖ :=
    FSKernel.norm_res_le _ _
  unfold Y1N
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-- `‖Y₂ u‖ ≤ R_{Y₂} M` on a good box state. -/
lemma norm_Y2N_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖Y2N sys L p₀ N n u‖ ≤ RY2 sys L n * M := by
  have hR : 0 ≤ RY2 sys L n := by
    unfold RY2
    exact Finset.sum_nonneg fun j _ => by
      have := y2C_nonneg (sys := sys) (n := n) hL j
      positivity
  exact (norm_Y2N_le (p₀ := p₀) hL H hKernel hn u).trans
    (mul_le_mul_of_nonneg_left (norm_le_good hu) hR)

variable (sys L) in
/-- The crude operator constant of `Ỹ`: `‖Ỹ x‖² ≤ B_op ‖x‖²`. -/
noncomputable def BopY (Hunit : ℝ) (N n : ℕ) : ℝ :=
  KP2 sys L Hunit N * (Fintype.card (Ch eta) : ℝ) * (500 * (Nat.log 2 (2 * N) + 2)) * n

lemma BopY_nonneg (hL : 0 < L) (Hunit : ℝ) (N n : ℕ) : 0 ≤ BopY sys L Hunit N n := by
  unfold BopY
  have := KP2_nonneg (sys := sys) hL Hunit N
  positivity

omit [Fintype ν] in
open Classical in
/-- On the cold ball the line weight is `≤ 4n⁴`. -/
lemma w32_cold_le (hn : 1 ≤ n) (j : Ch eta) {p : Cfg eta N}
    (hp : InC (n : ℝ) (cst sys) (cidx N p)) :
    w32 (regSum {lead j} (cidx N p)) ≤ 4 * (n : ℝ) ^ 4 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcs := cst_pos sys
  have hc32 := cst_le32 sys
  have e : regSum {lead j} (cidx N p) = cidx N p (lead j) := by simp [regSum]
  rw [e]
  set l := 1 + FSLattice.lsq (cidx N p (lead j)) with hl
  have hl1 : 1 ≤ l := by have := FSLattice.lsq_nonneg (cidx N p (lead j)); linarith
  have hs : Real.sqrt l ≤ l := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hw : w32 (cidx N p (lead j)) = l * Real.sqrt l := rfl
  have h1 : FSLattice.lsq (cidx N p (lead j)) ≤ (cst sys * n) ^ 2 := hp (lead j)
  have h2 : (cst sys * n) ^ 2 ≤ (n : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have h3 : l ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
  rw [hw]
  calc l * Real.sqrt l ≤ l * l := mul_le_mul_of_nonneg_left hs (by linarith)
    _ ≤ (2 * (n : ℝ) ^ 2) * (2 * (n : ℝ) ^ 2) := mul_le_mul h3 h3 (by linarith) (by positivity)
    _ = 4 * (n : ℝ) ^ 4 := by ring

open Classical in
/-- **The crude operator bound of `Ỹ`**: `‖Ỹ x‖ ≤ √B_op ‖x‖`. -/
theorem norm_Yt_op_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) (hN : 1 ≤ N)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (x : En eta N) :
    ‖Yt sys L p₀ N n x‖ ≤ Real.sqrt (BopY sys L Hunit N n) * ‖x‖ := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hK := KP2_nonneg (sys := sys) hL Hunit N
  have hline : ∀ j : Ch eta, lineSq j (fun _ => 1) (fun b => if InC (n : ℝ) (cst sys) (cidx N b) then
      ‖x.ofLp b‖ else 0) ≤ 125 * (Nat.log 2 (2 * N) + 2) * (4 * (n : ℝ) ^ 4 * ‖x‖ ^ 2) := by
    intro j
    have h := lineSq_le j (fun _ => zero_le_one) (fun b => if InC (n : ℝ) (cst sys) (cidx N b) then
      ‖x.ofLp b‖ else 0) (fun p => w32 (regSum {lead j} (cidx N p))) (fun p => w32_pos _)
      (fun q => lineSum_inv_w32_le hN (coord_lead j) q)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hx2 : ∑ p, ‖x.ofLp p‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun p _ => sq_nonneg _)]
    rw [← hx2, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [one_mul]
    split_ifs with hp
    · exact mul_le_mul_of_nonneg_right (w32_cold_le hn j hp) (sq_nonneg _)
    · rw [sq, mul_zero, mul_zero]
      positivity
  have h1 := norm_sq_Yt_cold_le (p₀ := p₀) hH hL hn H hKernel x
  have h2 : ‖Yt sys L p₀ N n x‖ ^ 2 ≤ BopY sys L Hunit N n * ‖x‖ ^ 2 := by
    refine h1.trans ?_
    calc KP2 sys L Hunit N / (n : ℝ) ^ 3 * ∑ j, lineSq j (fun _ => 1) (fun b =>
          if InC (n : ℝ) (cst sys) (cidx N b) then ‖x.ofLp b‖ else 0) ≤
        KP2 sys L Hunit N / (n : ℝ) ^ 3 * ∑ _j : Ch eta,
          125 * (Nat.log 2 (2 * N) + 2) * (4 * (n : ℝ) ^ 4 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hline j) (by positivity)
      _ = BopY sys L Hunit N n * ‖x‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          unfold BopY
          field_simp
          ring
  have hB := BopY_nonneg (sys := sys) hL Hunit N n
  rw [← Real.sqrt_sq (norm_nonneg (Yt sys L p₀ N n x)), ← Real.sqrt_sq (norm_nonneg x),
    ← Real.sqrt_mul hB]
  exact Real.sqrt_le_sqrt h2

/-- `‖Y₃ u‖ ≤ 2 √B_op M` on a good box state. -/
lemma norm_Y3N_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (hn : 1 ≤ n) (hN : 1 ≤ N)
    {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖Y3N sys L p₀ N n u‖ ≤ 2 * Real.sqrt (BopY sys L Hunit N n) * M := by
  have hH := finiteSupportUnitLatticeCoulombHardyBound_of_canonicalPeriodic Hunit hPeriodic
  have hop := norm_Yt_op_le (p₀ := p₀) hH hL hn hN H hKernel
  have h1 := hop u
  have h2 := norm_Ytd_le hop u
  have hs := Real.sqrt_nonneg (BopY sys L Hunit N n)
  have hu' := norm_le_good hu
  refine (norm_Y3N_le hL H hKernel hn u).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hu' hs]

end Crude

/-! ## The out-of-box error -/

section EY

variable {sys : CoulombSystem eta ν} {L : ℝ} {N : ℕ}

variable (sys L) in
/-- The out-of-box rate `√3 η C_m c_Tr (gN)^{-3/2}` (times `Ξ`). -/
noncomputable def eRate (Hunit : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit *
    (gF L * N) ^ (-(3 / 2 : ℝ))

/-- **The out-of-box error of an elimination**: `|e_Y(s)| ≤ 2 eRate Ξ ‖Y u_s‖`. -/
theorem abs_eY_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (D : EvoData L H)
    (hN : 1 ≤ gF L * N) (Y : En eta N →ₗ[ℂ] En eta N) (s : ℝ) :
    |eY sys H D Y s| ≤ 2 * (eRate sys L Hunit N * D.Xi) * ‖Y (ub H D N s)‖ := by
  refine (norm_eY_le sys H D Y s).trans ?_
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D s
  have hw : traj H D s = w := traj_eq H D s w hw1
  rw [hw]
  have h := fgood_W H hKernel Hunit hL hPeriodic hF hN
  have e : Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit *
      (cTr sys L Hunit * D.Xi) * (gF L * N) ^ (-(3 / 2 : ℝ)) = eRate sys L Hunit N * D.Xi := by
    unfold eRate; ring
  rw [e] at h
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num)) (norm_nonneg _)

end EY

end FSFlux
