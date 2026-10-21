import PlaneWave.FluxBox.ComElimination

/-!
# Flux route, stage 2, part 14: the classes of the com remainder

With `c = u_C`, `w = u_{Wm}`, `f = u_{F'}`, `δ = R u` (so `u = c + w + f + δ`):

* `inner_W_Y1`: `⟨W u, Y₁ u⟩ = ⟨R W u, R Y φ⟩ + ⟨W u, Y δ⟩`;
* **`cm_split`**: `2 Im⟨W u, Y₁ u⟩ = cm^{FC}(u) + cm^{QQ}(u) + cm^{rr}(u)` with
  `cm^{FC} = 2 Im[⟨W c, Y δ⟩ + ⟨R W (f+δ), R Y c⟩ + ⟨R W c, R Y f⟩]` (to round 3),
  `cm^{QQ} = 2 Im⟨R W (c+w), R Y (c+w)⟩ = -Re⟨u, Z_a u⟩` (`cmQQ_eq`), and the restricted rest;
* `norm_YcN_le`, `norm_YcN_res_le`: `‖Y v‖ ≤ Σ_j ‖r_j v‖`, and for a restriction with tails at `l`,
  `‖Y (res S u)‖ ≤ C_Y' η M l^{-3/2}`;
* **`norm_cmRR_le`**: `|cm^{rr}(u)| ≤ 6 H_rs C_Y' η M² (c_* K)⁻³` for a good box state;
* **the far–cold operator** `N^{FC} = X + X†`, `X = -i B^{FC}`,
  `B^{FC} = (R W P Ŵ - Π_{F'} W R Ŵ + Π_{F'} Ŵ R W + Π_F W R Y - R Y W - Π_{F'} Y R W) Π_C`, with
  `n^{FC}(u) + cm^{FC}(u) = Re⟨u, N^{FC} u⟩` (`nfcFC_eq`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The operator norm of the dressing -/

section NormY

omit [Fintype ν] in
lemma kop_fsum {X : Type*} [Fintype X] {ι : Type*} (s : Finset ι) (κ : ι → X → X → ℂ) :
    FSKernel.kop (∑ j ∈ s, κ j) = ∑ j ∈ s, FSKernel.kop (κ j) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext u q; simp [FSKernel.kop_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, FSKernel.kop_add, ih]

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

/-- **`‖Y v‖ ≤ Σ_j (Σ r_j² |v|²)^{1/2}`.** -/
theorem norm_YcN_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (v : En eta N) :
    ‖YcN sys L p₀ N v‖ ≤ ∑ j, Real.sqrt (∑ p, rY (sys := sys) (L := L) j p ^ 2 * ‖v.ofLp p‖ ^ 2) := by
  have e : YcN sys L p₀ N = ∑ j, FSKernel.kop (ycKc (sys := sys) (L := L) (p₀ := p₀) (N := N) j) := by
    show FSKernel.kop (ycK sys L p₀ N) = _
    rw [← kop_fsum]
    congr 1
    funext q p
    rw [ycK_eq_sum hL q p, Finset.sum_apply, Finset.sum_apply]
  rw [e, LinearMap.coe_sum, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have h := norm_sq_kop_ycKc_le (p₀ := p₀) hL H hKernel j v
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt h

/-- The tail constant of the dressing: `Σ_j C_j Λ_N √2 √c_X`. -/
noncomputable def CYo (sys : CoulombSystem eta ν) (L : ℝ) (N : ℕ) : ℝ :=
  ∑ j : Ch eta, CYc sys L j * LamB sys N * (Real.sqrt 2 * Real.sqrt (cXw sys L))

/-- **The dressing on a restricted good state**: `‖Y (res S u)‖ ≤ C_Y' η M l^{-3/2}`. -/
theorem norm_YcN_res_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) (S : Cfg eta N → Prop) {l : ℝ} (hl : 1 ≤ l)
    (hS : ∀ q, S q → ∃ c, l < finitePlaneWaveKabs (2 * Real.pi / L) N (q c)) :
    ‖YcN sys L p₀ N (FSKernel.res S u)‖ ≤ CYo sys L N * (eta * M * l ^ (-(3 / 2 : ℝ))) := by
  have hl0 : 0 < l := by linarith
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  have hX := sum_Xall_res_le sys hL hu S hl hS
  have hcX : 0 ≤ cXw sys L := by unfold cXw; have := gF_pos hL; have := one_le_mmax sys; positivity
  refine (norm_YcN_le hL H hKernel _).trans ?_
  unfold CYo
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have hC0 : 0 ≤ CYc sys L j * LamB sys N := mul_nonneg (CYc_nonneg hL j) (LamB_nonneg (sys := sys) N)
  have h1 : ∑ p, rY (sys := sys) (L := L) j p ^ 2 * ‖(FSKernel.res S u).ofLp p‖ ^ 2 ≤
      (CYc sys L j * LamB sys N) ^ 2 * 2 * (cXw sys L * (eta ^ 2 * M ^ 2 * l ^ (-(3 : ℝ)))) := by
    have h2 : ∀ p : Cfg eta N, rY (sys := sys) (L := L) j p ^ 2 ≤ (CYc sys L j * LamB sys N) ^ 2 * 2 * (1 + Xall p) := by
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
    calc ∑ p, rY (sys := sys) (L := L) j p ^ 2 * ‖(FSKernel.res S u).ofLp p‖ ^ 2
        ≤ ∑ p, (CYc sys L j * LamB sys N) ^ 2 * 2 * ((1 + Xall p) * ‖(FSKernel.res S u).ofLp p‖ ^ 2) := by
          refine Finset.sum_le_sum fun p _ => ?_
          calc rY (sys := sys) (L := L) j p ^ 2 * ‖(FSKernel.res S u).ofLp p‖ ^ 2
              ≤ (CYc sys L j * LamB sys N) ^ 2 * 2 * (1 + Xall p) * ‖(FSKernel.res S u).ofLp p‖ ^ 2 :=
                mul_le_mul_of_nonneg_right (h2 p) (sq_nonneg _)
            _ = _ := by ring
      _ = (CYc sys L j * LamB sys N) ^ 2 * 2 * ∑ p, (1 + Xall p) * ‖(FSKernel.res S u).ofLp p‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hX (by positivity)
  refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
  have hp : l ^ (-(3 : ℝ)) = (l ^ (-(3 / 2 : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
  rw [hp, show (CYc sys L j * LamB sys N) ^ 2 * 2 * (cXw sys L * (eta ^ 2 * M ^ 2 * (l ^ (-(3 / 2 : ℝ))) ^ 2)) =
    (CYc sys L j * LamB sys N * (eta * M * l ^ (-(3 / 2 : ℝ)))) ^ 2 * (2 * cXw sys L) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_mul (by norm_num)]
  ring

end NormY

/-! ## The split of the com remainder -/

section CmSplit

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) {N : ℕ} (n : ℕ)

/-- The far–cold part of the com remainder. -/
noncomputable def cmFC (u : En eta N) : ℝ :=
  2 * (⟪WN sys L N (CN sys N n u), YcN sys L p₀ N (RN N n u)⟫_ℂ).im +
    2 * (⟪RN N n (WN sys L N (FpN N n u + RN N n u)), RN N n (YcN sys L p₀ N (CN sys N n u))⟫_ℂ).im +
    2 * (⟪RN N n (WN sys L N (CN sys N n u)), RN N n (YcN sys L p₀ N (FpN N n u))⟫_ℂ).im

/-- The bulk–bulk part of the com remainder (the symbol current). -/
noncomputable def cmQQ (u : En eta N) : ℝ :=
  2 * (⟪RN N n (WN sys L N (QN N n u)), RN N n (YcN sys L p₀ N (QN N n u))⟫_ℂ).im

/-- The restricted part of the com remainder. -/
noncomputable def cmRR (u : En eta N) : ℝ :=
  2 * (⟪WN sys L N (WmN sys N n u + FpN N n u + RN N n u), YcN sys L p₀ N (RN N n u)⟫_ℂ).im +
    2 * (⟪RN N n (WN sys L N (FpN N n u + RN N n u)), RN N n (YcN sys L p₀ N (WmN sys N n u))⟫_ℂ).im +
    2 * (⟪RN N n (WN sys L N (WmN sys N n u + FpN N n u + RN N n u)),
      RN N n (YcN sys L p₀ N (FpN N n u))⟫_ℂ).im

variable {sys L p₀}

omit [Fintype ν] in
lemma u_eq_CWFR (u : En eta N) :
    u = CN sys N n u + WmN sys N n u + FpN N n u + RN N n u := by
  have h1 : u = PN N n u + RN N n u := by rw [RN_eq]; abel
  rw [PN_eq_CWF] at h1
  conv_lhs => rw [h1]
  abel

/-- `⟨W u, Y₁ u⟩ = ⟨R W u, R Y φ⟩ + ⟨W u, Y δ⟩`. -/
lemma inner_W_Y1 (u : En eta N) :
    ⟪WN sys L N u, Y1N sys L p₀ N n u⟫_ℂ =
      ⟪RN N n (WN sys L N u), RN N n (YcN sys L p₀ N (PN N n u))⟫_ℂ +
        ⟪WN sys L N u, YcN sys L p₀ N (RN N n u)⟫_ℂ := by
  have hu : u = PN N n u + RN N n u := by rw [RN_eq]; abel
  have e : Y1N sys L p₀ N n u = RN N n (YcN sys L p₀ N (PN N n u)) + YcN sys L p₀ N (RN N n u) := by
    unfold Y1N
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      RN_eq n (YcN sys L p₀ N (PN N n u))]
    have h2 : YcN sys L p₀ N u = YcN sys L p₀ N (PN N n u) + YcN sys L p₀ N (RN N n u) := by
      rw [← map_add, ← hu]
    rw [h2]; abel
  rw [e, inner_add_right]
  congr 1
  rw [RN_symm n (WN sys L N u) (RN N n (YcN sys L p₀ N (PN N n u))), RN_idem]

omit [Fintype ν] in
lemma res_symm' (S : Cfg eta N → Prop) [DecidablePred S] :
    (FSKernel.res S : En eta N →ₗ[ℂ] En eta N).IsSymmetric := by
  intro u v
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [FSKernel.res_apply, Pi.star_apply, RCLike.star_def]
  split_ifs <;> simp

omit [Fintype ν] in
lemma QN_eq' (u : En eta N) : QN N n u = CN sys N n u + WmN sys N n u := QN_eq_CN_add u

omit [Fintype ν] in
lemma FN_eq (u : En eta N) :
    FSKernel.res (fun q : Cfg eta N => ¬ InQ (n : ℝ) (cidx N q)) u = FpN N n u + RN N n u := by
  classical
  ext q
  simp only [FSKernel.res_apply, PiLp.add_apply]
  by_cases hQ : InQ (n : ℝ) (cidx N q)
  · have hP := inQ_imp_inP (Nat.cast_nonneg n) hQ
    simp [hQ, hP]
  · by_cases hP : InP (n : ℝ) (cidx N q)
    · simp [hQ, hP]
    · simp [hQ, hP]

/-- **The split of the com remainder**: `2 Im⟨W u, Y₁ u⟩ = cm^{FC} + cm^{QQ} + cm^{rr}`. -/
theorem cm_split (u : En eta N) :
    2 * (⟪WN sys L N u, Y1N sys L p₀ N n u⟫_ℂ).im = cmFC sys L p₀ n u + cmQQ sys L p₀ n u + cmRR sys L p₀ n u := by
  rw [inner_W_Y1]
  have hu := u_eq_CWFR (sys := sys) n u
  have hP : PN N n u = CN sys N n u + WmN sys N n u + FpN N n u := by rw [PN_eq_CWF]; abel
  have hQ : QN N n u = CN sys N n u + WmN sys N n u := QN_eq_CN_add u
  unfold cmFC cmQQ cmRR
  rw [hP, hQ]
  set c := CN sys N n u
  set w := WmN sys N n u
  set f := FpN N n u
  set δ := RN N n u
  have hWu : WN sys L N u = WN sys L N c + WN sys L N w + WN sys L N f + WN sys L N δ := by
    conv_lhs => rw [hu]
    simp only [map_add]
  rw [hWu]
  simp only [map_add, inner_add_left, inner_add_right, Complex.add_im]
  ring

/-- The symbol current `Z_a = Π_Q i(W R Y - Y R W) Π_Q`. -/
noncomputable def ZaN (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ) :
    En eta N →ₗ[ℂ] En eta N :=
  QN N n ∘ₗ (Complex.I • (WN sys L N ∘ₗ RN N n ∘ₗ YcN sys L p₀ N -
    YcN sys L p₀ N ∘ₗ RN N n ∘ₗ WN sys L N)) ∘ₗ QN N n

/-- `cm^{QQ}(u) = -Re⟨u, Z_a u⟩`. -/
lemma cmQQ_eq (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (u : En eta N) : cmQQ sys L p₀ n u = -(⟪u, ZaN sys L p₀ N n u⟫_ℂ).re := by
  classical
  have hY := YcN_symm (sys := sys) (p₀ := p₀) (N := N) hL H hKernel
  have hW := WN_symm (sys := sys) (L := L) (N := N)
  have hQs := res_symm' (N := N) (fun q : Cfg eta N => InQ (n : ℝ) (cidx N q))
  have hRs := RN_symm (eta := eta) (N := N) n
  unfold ZaN cmQQ
  set v := QN N n u
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hQs u, LinearMap.smul_apply, inner_smul_right,
    LinearMap.sub_apply, inner_sub_right, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearMap.comp_apply, ← hW v, ← hY v]
  have e1 : ⟪WN sys L N v, RN N n (YcN sys L p₀ N v)⟫_ℂ =
      ⟪RN N n (WN sys L N v), RN N n (YcN sys L p₀ N v)⟫_ℂ := by
    rw [hRs (WN sys L N v) (RN N n (YcN sys L p₀ N v)), RN_idem]
  have e2 : ⟪YcN sys L p₀ N v, RN N n (WN sys L N v)⟫_ℂ =
      conj ⟪RN N n (WN sys L N v), RN N n (YcN sys L p₀ N v)⟫_ℂ := by
    rw [inner_conj_symm, hRs (YcN sys L p₀ N v) (RN N n (WN sys L N v)), RN_idem]
  rw [e1, e2, mul_sub, re_I_sub]
  ring

end CmSplit

/-! ## The restricted com classes are at target -/

section CmRR

variable (sys : CoulombSystem eta ν) {L : ℝ} {N : ℕ} (p₀ : Fin eta)

/-- **The restricted com classes**: `|cm^{rr}(u)| ≤ 6 H_rs C_Y' η M² (c_* K)⁻³`. -/
theorem norm_cmRR_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {n : ℕ}
    (hl : 1 ≤ gF L * (cst sys * n)) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    |cmRR sys L p₀ n u| ≤
      6 * (Hrs sys L Hunit * CYo sys L N * eta * M ^ 2 * (gF L * (cst sys * n)) ^ (-(3 : ℝ))) := by
  classical
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  set l := gF L * (cst sys * n)
  have hl0 : 0 < l := by linarith
  have hW : WN sys L N = FSKernel.kop (wNK sys L N) := VN_eq_kop sys hL H hKernel
  have hκW : ∀ q p, ‖wNK sys L N q p‖ ≤ potMaj sys L (cidx N q) (cidx N p) := fun q p =>
    norm_potKernel_le sys hL _ _
  have hc4 : cst sys ≤ 1 / 4 := (cst_le sys).trans (by norm_num)
  have hc0 := cst_pos sys
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- supports outside the cold ball
  set Sc : Cfg eta N → Prop := fun q => ¬ InC (n : ℝ) (cst sys) (cidx N q)
  have sC : ∀ q, Sc q → ∃ c, l < finitePlaneWaveKabs (2 * Real.pi / L) N (q c) := fun q hq =>
    kabs_gt_of_not_inC sys hL hq
  have sR : ∀ q : Cfg eta N, ¬ InP (n : ℝ) (cidx N q) → ¬ InC (n : ℝ) (cst sys) (cidx N q) := by
    intro q hq hC; exact hq (inQ_imp_inP hn0 (inC_imp_inQ hn0 hc0.le hc4 hC))
  have sW : ∀ q : Cfg eta N, (InQ (n : ℝ) (cidx N q) ∧ ¬ InC (n : ℝ) (cst sys) (cidx N q)) →
      ¬ InC (n : ℝ) (cst sys) (cidx N q) := fun q hq => hq.2
  have sF : ∀ q : Cfg eta N, (InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)) →
      ¬ InC (n : ℝ) (cst sys) (cidx N q) := fun q hq hC =>
    hq.2 (inC_imp_inQ hn0 hc0.le hc4 hC)
  have sQ : ∀ q : Cfg eta N, ¬ InQ (n : ℝ) (cidx N q) → ¬ InC (n : ℝ) (cst sys) (cidx N q) :=
    fun q hq hC => hq (inC_imp_inQ hn0 hc0.le hc4 hC)
  have eWFR : WmN sys N n u + FpN N n u + RN N n u = FSKernel.res Sc u := by
    ext q
    simp only [FSKernel.res_apply, PiLp.add_apply, Sc]
    by_cases h1 : InQ (n : ℝ) (cidx N q) <;> by_cases h2 : InC (n : ℝ) (cst sys) (cidx N q) <;>
      by_cases h3 : InP (n : ℝ) (cidx N q)
    all_goals first
      | (exfalso; exact h3 (inQ_imp_inP hn0 h1))
      | (exfalso; exact h1 (inC_imp_inQ hn0 hc0.le hc4 h2))
      | simp [h1, h2, h3]
  have eFR : FpN N n u + RN N n u = FSKernel.res (fun q : Cfg eta N => ¬ InQ (n : ℝ) (cidx N q)) u :=
    (FN_eq n u).symm
  -- the factors
  set h₀ := CH sys L Hunit * (Real.sqrt 2 * eta * M * l ^ (-(3 / 2 : ℝ)))
  set y₀ := CYo sys L N * (eta * M * l ^ (-(3 / 2 : ℝ)))
  have bW1 : ‖WN sys L N (WmN sys N n u + FpN N n u + RN N n u)‖ ≤ h₀ := by
    rw [eWFR, hW]; exact norm_kop_res_cold_le sys hL Hunit hPeriodic hl hu _ hκW Sc (fun q hq => hq)
  have bW2 : ‖WN sys L N (FpN N n u + RN N n u)‖ ≤ h₀ := by
    rw [eFR, hW]; exact norm_kop_res_cold_le sys hL Hunit hPeriodic hl hu _ hκW _ sQ
  have bYR : ‖YcN sys L p₀ N (RN N n u)‖ ≤ y₀ :=
    norm_YcN_res_le hL H hKernel hu _ hl (fun q hq => sC q (sR q hq))
  have bYW : ‖YcN sys L p₀ N (WmN sys N n u)‖ ≤ y₀ :=
    norm_YcN_res_le hL H hKernel hu _ hl (fun q hq => sC q (sW q hq))
  have bYF : ‖YcN sys L p₀ N (FpN N n u)‖ ≤ y₀ :=
    norm_YcN_res_le hL H hKernel hu _ hl (fun q hq => sC q (sF q hq))
  have h00 : 0 ≤ h₀ := le_trans (norm_nonneg _) bW1
  have y00 : 0 ≤ y₀ := le_trans (norm_nonneg _) bYR
  have pr : ∀ (a b : En eta N), ‖a‖ ≤ h₀ → ‖b‖ ≤ y₀ → |(⟪a, b⟫_ℂ).im| ≤ h₀ * y₀ := by
    intro a b ha hb
    exact (Complex.abs_im_le_norm _).trans ((norm_inner_le_norm (𝕜 := ℂ) _ _).trans
      (mul_le_mul ha hb (norm_nonneg _) h00))
  have hRc : ∀ x : En eta N, ‖RN N n x‖ ≤ ‖x‖ := fun x => FSKernel.norm_res_le _ x
  have p1 := pr _ _ bW1 bYR
  have p2 := pr _ _ ((hRc _).trans bW2) ((hRc _).trans bYW)
  have p3 := pr _ _ ((hRc _).trans bW1) ((hRc _).trans bYF)
  have htot : |cmRR sys L p₀ n u| ≤ 6 * (h₀ * y₀) := by
    unfold cmRR
    have := abs_add_le (2 * (⟪WN sys L N (WmN sys N n u + FpN N n u + RN N n u),
      YcN sys L p₀ N (RN N n u)⟫_ℂ).im + 2 * (⟪RN N n (WN sys L N (FpN N n u + RN N n u)),
        RN N n (YcN sys L p₀ N (WmN sys N n u))⟫_ℂ).im)
      (2 * (⟪RN N n (WN sys L N (WmN sys N n u + FpN N n u + RN N n u)),
        RN N n (YcN sys L p₀ N (FpN N n u))⟫_ℂ).im)
    have := abs_add_le (2 * (⟪WN sys L N (WmN sys N n u + FpN N n u + RN N n u),
      YcN sys L p₀ N (RN N n u)⟫_ℂ).im) (2 * (⟪RN N n (WN sys L N (FpN N n u + RN N n u)),
        RN N n (YcN sys L p₀ N (WmN sys N n u))⟫_ℂ).im)
    simp only [abs_mul, abs_two] at *
    linarith
  refine htot.trans (le_of_eq ?_)
  have hp : l ^ (-(3 / 2 : ℝ)) * l ^ (-(3 / 2 : ℝ)) = l ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_add hl0]; norm_num
  simp only [h₀, y₀, Hrs]
  rw [show CH sys L Hunit * (Real.sqrt 2 * eta * M * l ^ (-(3 / 2 : ℝ))) *
      (CYo sys L N * (eta * M * l ^ (-(3 / 2 : ℝ)))) =
    CH sys L Hunit * (Real.sqrt 2 * eta) * CYo sys L N * eta * M ^ 2 *
      (l ^ (-(3 / 2 : ℝ)) * l ^ (-(3 / 2 : ℝ))) by ring, hp]

end CmRR

/-! ## The far–cold operator -/

section FarCold

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ)

/-- The far region `F = ¬ Q` on the box. -/
noncomputable abbrev FN : En eta N →ₗ[ℂ] En eta N :=
  FSKernel.res fun q : Cfg eta N => ¬ InQ (n : ℝ) (cidx N q)

/-- The far–cold chains `B^{FC}` (cold input, far output). -/
noncomputable def BFC : En eta N →ₗ[ℂ] En eta N :=
  (RN N n ∘ₗ WN sys L N ∘ₗ PN N n ∘ₗ WhN sys L p₀ N -
    FpN N n ∘ₗ WN sys L N ∘ₗ RN N n ∘ₗ WhN sys L p₀ N +
    FpN N n ∘ₗ WhN sys L p₀ N ∘ₗ RN N n ∘ₗ WN sys L N +
    FN N n ∘ₗ WN sys L N ∘ₗ RN N n ∘ₗ YcN sys L p₀ N -
    RN N n ∘ₗ YcN sys L p₀ N ∘ₗ WN sys L N -
    FpN N n ∘ₗ YcN sys L p₀ N ∘ₗ RN N n ∘ₗ WN sys L N) ∘ₗ CN sys N n

/-- The kernel of `X = -i B^{FC}`. -/
noncomputable def xFCK : Cfg eta N → Cfg eta N → ℂ :=
  FSKernel.matK (-Complex.I • BFC sys L p₀ N n)

/-- The kernel of the far–cold operator `N^{FC} = X + X†`. -/
noncomputable def nFCK (q p : Cfg eta N) : ℂ :=
  xFCK sys L p₀ N n q p + conj (xFCK sys L p₀ N n p q)

/-- The far–cold operator. -/
noncomputable abbrev NFC : En eta N →ₗ[ℂ] En eta N := FSKernel.kop (nFCK sys L p₀ N n)

variable {sys L p₀ N n}

lemma nFCK_conj (q p : Cfg eta N) : nFCK sys L p₀ N n p q = conj (nFCK sys L p₀ N n q p) := by
  unfold nFCK; rw [map_add, Complex.conj_conj]; ring

lemma NFC_symm : (NFC sys L p₀ N n : En eta N →ₗ[ℂ] En eta N).IsSymmetric :=
  FSKernel.kop_symm _ fun q p => nFCK_conj q p

/-- `Re⟨u, N^{FC} u⟩ = 2 Im⟨u, B^{FC} u⟩`. -/
lemma re_NFC (u : En eta N) :
    (⟪u, NFC sys L p₀ N n u⟫_ℂ).re = 2 * (⟪u, BFC sys L p₀ N n u⟫_ℂ).im := by
  have hk : FSKernel.kop (xFCK sys L p₀ N n) = -Complex.I • BFC sys L p₀ N n := FSKernel.kop_matK _
  have e : NFC sys L p₀ N n = FSKernel.kop (xFCK sys L p₀ N n) +
      FSKernel.kop (fun q p => conj (xFCK sys L p₀ N n p q)) := by
    rw [← FSKernel.kop_add]; rfl
  calc (⟪u, NFC sys L p₀ N n u⟫_ℂ).re =
        (⟪u, FSKernel.kop (xFCK sys L p₀ N n) u⟫_ℂ + ⟪FSKernel.kop (xFCK sys L p₀ N n) u, u⟫_ℂ).re := by
        rw [e, LinearMap.add_apply, inner_add_right, ← FSKernel.inner_kop]
    _ = 2 * (⟪u, FSKernel.kop (xFCK sys L p₀ N n) u⟫_ℂ).re := by
        rw [← inner_conj_symm (FSKernel.kop (xFCK sys L p₀ N n) u) u, Complex.add_re, Complex.conj_re]
        ring
    _ = 2 * (⟪u, BFC sys L p₀ N n u⟫_ℂ).im := by
        rw [hk, LinearMap.smul_apply, inner_smul_right]
        simp [Complex.mul_re]

/-- **The far–cold classes form one operator**: `n^{FC}(u) + cm^{FC}(u) = Re⟨u, N^{FC} u⟩`. -/
theorem nfcFC_eq (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (u : En eta N) :
    nflFC sys L p₀ n u + cmFC sys L p₀ n u = (⟪u, NFC sys L p₀ N n u⟫_ℂ).re := by
  classical
  rw [re_NFC]
  have hY := YcN_symm (sys := sys) (p₀ := p₀) (N := N) hL H hKernel
  have hW := WN_symm (sys := sys) (L := L) (N := N)
  have hWh := WhN_symm (sys := sys) (p₀ := p₀) (N := N) hL
  have hR := RN_symm (eta := eta) (N := N) n
  have hP := PN_symm (eta := eta) (N := N) n
  have hFp := res_symm' (N := N) (fun q : Cfg eta N => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
  have hF := res_symm' (N := N) (fun q : Cfg eta N => ¬ InQ (n : ℝ) (cidx N q))
  set c := CN sys N n u
  set f := FpN N n u
  set δ := RN N n u
  have hFu : FN N n u = f + δ := FN_eq n u
  have t1 : ⟪u, RN N n (WN sys L N (PN N n (WhN sys L p₀ N c)))⟫_ℂ =
      ⟪WN sys L N δ, PN N n (WhN sys L p₀ N c)⟫_ℂ := by
    rw [← hR u, ← hW]
  have t2 : ⟪u, FpN N n (WN sys L N (RN N n (WhN sys L p₀ N c)))⟫_ℂ =
      ⟪RN N n (WN sys L N f), RN N n (WhN sys L p₀ N c)⟫_ℂ := by
    rw [← hFp u, ← hW, hR (WN sys L N f) (RN N n (WhN sys L p₀ N c)), RN_idem]
  have t3 : ⟪u, FpN N n (WhN sys L p₀ N (RN N n (WN sys L N c)))⟫_ℂ =
      conj ⟪RN N n (WN sys L N c), RN N n (WhN sys L p₀ N f)⟫_ℂ := by
    rw [← hFp u, ← hWh, inner_conj_symm, hR (WhN sys L p₀ N f) (RN N n (WN sys L N c)), RN_idem]
  have t4 : ⟪u, FN N n (WN sys L N (RN N n (YcN sys L p₀ N c)))⟫_ℂ =
      ⟪RN N n (WN sys L N (f + δ)), RN N n (YcN sys L p₀ N c)⟫_ℂ := by
    rw [← hF u, ← hW, hFu, hR (WN sys L N (f + δ)) (RN N n (YcN sys L p₀ N c)), RN_idem]
  have t5 : ⟪u, RN N n (YcN sys L p₀ N (WN sys L N c))⟫_ℂ =
      conj ⟪WN sys L N c, YcN sys L p₀ N δ⟫_ℂ := by
    rw [← hR u, ← hY, inner_conj_symm]
  have t6 : ⟪u, FpN N n (YcN sys L p₀ N (RN N n (WN sys L N c)))⟫_ℂ =
      conj ⟪RN N n (WN sys L N c), RN N n (YcN sys L p₀ N f)⟫_ℂ := by
    rw [← hFp u, ← hY, inner_conj_symm, hR (YcN sys L p₀ N f) (RN N n (WN sys L N c)), RN_idem]
  have hB : ⟪u, BFC sys L p₀ N n u⟫_ℂ =
      ⟪u, RN N n (WN sys L N (PN N n (WhN sys L p₀ N c)))⟫_ℂ -
        ⟪u, FpN N n (WN sys L N (RN N n (WhN sys L p₀ N c)))⟫_ℂ +
        ⟪u, FpN N n (WhN sys L p₀ N (RN N n (WN sys L N c)))⟫_ℂ +
        ⟪u, FN N n (WN sys L N (RN N n (YcN sys L p₀ N c)))⟫_ℂ -
        ⟪u, RN N n (YcN sys L p₀ N (WN sys L N c))⟫_ℂ -
        ⟪u, FpN N n (YcN sys L p₀ N (RN N n (WN sys L N c)))⟫_ℂ := by
    unfold BFC
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, inner_sub_right,
      inner_add_right]
    rfl
  rw [hB, t1, t2, t3, t4, t5, t6]
  unfold nflFC cmFC
  simp only [Complex.sub_im, Complex.add_im, Complex.conj_im]
  have hδ : u - PN N n u = δ := (RN_eq n u).symm
  ring

end FarCold

end FSFlux
