import PlaneWave.FluxBox.ResonantComFlux

/-!
# Flux route, stage 2, part 13: the com elimination and its endpoint

* `Y₁ = Y - P Y P` (`Y1N`), symmetric, with `i[T_N, Y₁] = X^{cm,gap} = G^{cm,gap} - P G^{cm,gap} P`
  (`comm_Y1N`) and `X^cm = X^{cm,gap} + X^{cm,res}` (`Xcm_split`);
* **`ledger_cm`**: along the exact evolution
  `∫₀ᵗ Re⟨u, X^cm u⟩ = ∫₀ᵗ Re⟨u, X^{cm,res} u⟩ + [Re⟨u, Y₁ u⟩]₀ᵗ - ∫₀ᵗ Re⟨u, i[W_N, Y₁] u⟩ - ∫₀ᵗ e_{Y₁}`;
* `norm_form_ycK_le`: `|⟨a, Y b⟩| ≤ Σ_j (Σ r_j |a|²)^{1/2} (Σ r_j |b|²)^{1/2}`, `r_j = C_j Λ_N |Π_j|`;
* `norm_ycK_bulk_le`: on bulk-fed hops (`p ∈ Q`, `q ∉ P`) `|y(q, p)| ≤ potMaj(q, p)` (the gap
  `ω ≥ g²|θ|²/(6μ)`, `|Π| ≤ n/2 ≤ 2|θ|/3`, `μ/M̄ ≤ 1/4`);
* **`norm_Y1_form_le`**: for a good box state `|⟨u, Y₁ u⟩| ≤ 2 B M² K⁻³ + 3 C_Y Λ_N √(2 c_X) η² M² (K/4)⁻⁴`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The first com elimination -/

section Elim

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ)

/-- The com dressing of the flux, `Y₁ = Y - P Y P`. -/
noncomputable def Y1N : En eta N →ₗ[ℂ] En eta N :=
  YcN sys L p₀ N - PN N n ∘ₗ YcN sys L p₀ N ∘ₗ PN N n

/-- The gapped com flux `X^{cm,gap} = G^{cm,gap} - P G^{cm,gap} P`. -/
noncomputable def XgapN : En eta N →ₗ[ℂ] En eta N :=
  FSKernel.kop (gcmGap sys L p₀ N) - PN N n ∘ₗ FSKernel.kop (gcmGap sys L p₀ N) ∘ₗ PN N n

variable {sys L p₀ N n}

lemma Y1N_symm (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    (Y1N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N).IsSymmetric := by
  intro x y
  unfold Y1N
  have hY := YcN_symm (sys := sys) (p₀ := p₀) (N := N) hL H hKernel
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_left, inner_sub_right]
  rw [hY x y, PN_symm n (YcN sys L p₀ N (PN N n x)) y, hY (PN N n x) (PN N n y),
    PN_symm n x (YcN sys L p₀ N (PN N n y))]

/-- **`i[T_N, Y₁] = X^{cm,gap}`.** -/
theorem comm_Y1N (hL : 0 < L) :
    Complex.I • (TN sys L N ∘ₗ Y1N sys L p₀ N n - Y1N sys L p₀ N n ∘ₗ TN sys L N) =
      XgapN sys L p₀ N n := by
  have h := comm_YcN (sys := sys) (p₀ := p₀) (N := N) hL
  have hPT := PN_TN_comm (sys := sys) (L := L) (N := N) n
  unfold Y1N XgapN
  rw [← h]
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, map_smul]
  have e1 : TN sys L N (PN N n (YcN sys L p₀ N (PN N n v))) =
      PN N n (TN sys L N (YcN sys L p₀ N (PN N n v))) := by
    have := congrArg (fun T => T (YcN sys L p₀ N (PN N n v))) hPT
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    exact this.symm
  have e2 : PN N n (YcN sys L p₀ N (PN N n (TN sys L N v))) =
      PN N n (YcN sys L p₀ N (TN sys L N (PN N n v))) := by
    have := congrArg (fun T => T v) hPT
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this]
  rw [e1, e2]
  module

/-- `X^cm = X^{cm,gap} + X^{cm,res}`. -/
lemma Xcm_split : Xcm sys L p₀ n = XgapN sys L p₀ N n + XresN sys L p₀ N n := by
  unfold Xcm XgapN XresN
  rw [GcmN_split]
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
  abel

end Elim

section Ledger

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta) {N : ℕ} (n : ℕ)

include hL hKernel in
/-- **The com ledger**: along the exact evolution,
`∫₀ᵗ Re⟨u, X^cm u⟩ = ∫₀ᵗ Re⟨u, X^{cm,res} u⟩ + [Re⟨u, Y₁ u⟩]₀ᵗ - ∫₀ᵗ Re⟨u, i[W, Y₁] u⟩ - ∫₀ᵗ e_{Y₁}`. -/
theorem ledger_cm (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, (⟪ub H D N s, Xcm sys L p₀ n (ub H D N s)⟫_ℂ).re =
      (∫ s in (0 : ℝ)..t, (⟪ub H D N s, XresN sys L p₀ N n (ub H D N s)⟫_ℂ).re) +
        ((⟪ub H D N t, Y1N sys L p₀ N n (ub H D N t)⟫_ℂ).re -
          (⟪ub H D N 0, Y1N sys L p₀ N n (ub H D N 0)⟫_ℂ).re) -
        (∫ s in (0 : ℝ)..t, (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y1N sys L p₀ N n -
          Y1N sys L p₀ N n ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re) -
        ∫ s in (0 : ℝ)..t, eY sys H D (Y1N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N) s := by
  have hE := elim_box sys hL H hKernel (N := N) Hunit hPeriodic D (Y1N sys L p₀ N n)
    (Y1N_symm hL H hKernel) t
  rw [comm_Y1N hL] at hE
  have hsplit : ∀ s, (⟪ub H D N s, Xcm sys L p₀ n (ub H D N s)⟫_ℂ).re =
      (⟪ub H D N s, XgapN sys L p₀ N n (ub H D N s)⟫_ℂ).re +
        (⟪ub H D N s, XresN sys L p₀ N n (ub H D N s)⟫_ℂ).re := by
    intro s
    rw [Xcm_split, LinearMap.add_apply, inner_add_right, Complex.add_re]
  rw [intervalIntegral.integral_congr (fun s _ => hsplit s)]
  have hc1 := continuous_form_ub H (N := N) D (XgapN sys L p₀ N n)
  have hc2 := continuous_form_ub H (N := N) D (XresN sys L p₀ N n)
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable 0 t) (hc2.intervalIntegrable 0 t), hE]
  ring

end Ledger

/-! ## The form bound of the dressing -/

section YForm

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

/-- **The form of the dressing**: `|⟨a, Y b⟩| ≤ Σ_j (Σ r_j |a|²)^{1/2} (Σ r_j |b|²)^{1/2}`. -/
theorem norm_form_ycK_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (a b : En eta N) :
    ‖⟪a, YcN sys L p₀ N b⟫_ℂ‖ ≤ ∑ j, Real.sqrt (∑ q, rY (sys := sys) (L := L) j q * ‖a.ofLp q‖ ^ 2) *
      Real.sqrt (∑ p, rY (sys := sys) (L := L) j p * ‖b.ofLp p‖ ^ 2) := by
  classical
  refine (norm_inner_kop_le₂ _ a b).trans ?_
  set K : Ch eta → Cfg eta N → Cfg eta N → ℝ := fun j q p =>
    if OnCh j (cidx N q) (cidx N p) then ‖ycK sys L p₀ N q p‖ else 0
  have hK0 : ∀ j q p, 0 ≤ K j q p := fun j q p => by simp only [K]; split_ifs <;> positivity
  have hdec : ∀ q p, ‖ycK sys L p₀ N q p‖ ≤ ∑ j, K j q p := by
    intro q p
    rw [ycK_eq_sum hL q p]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [K, ycKc]
    split_ifs <;> simp
  have hrow : ∀ j p, ∑ q, K j q p ≤ rY (sys := sys) (L := L) j p := fun j p =>
    row_ycK_le (sys := sys) (p₀ := p₀) hL j p
  have hcol : ∀ j q, ∑ p, K j q p ≤ rY (sys := sys) (L := L) j q := by
    intro j q
    refine le_trans (le_of_eq ?_) (hrow j q)
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [K]
    by_cases hj : OnCh j (cidx N q) (cidx N p)
    · rw [if_pos hj, if_pos (onCh_symm hj), ycK_conj hL H hKernel p q, Complex.norm_conj]
    · rw [if_neg hj, if_neg (fun h => hj (onCh_symm h))]
  have hj : ∀ j, ∑ q, ∑ p, ‖a.ofLp q‖ * ‖b.ofLp p‖ * K j q p ≤
      Real.sqrt (∑ q, rY (sys := sys) (L := L) j q * ‖a.ofLp q‖ ^ 2) *
        Real.sqrt (∑ p, rY (sys := sys) (L := L) j p * ‖b.ofLp p‖ ^ 2) := by
    intro j
    refine (sum_kernel_cs (K j) (hK0 j) (fun q => ‖a.ofLp q‖) (fun p => ‖b.ofLp p‖)).trans ?_
    have h1 : ∑ q, ∑ p, ‖a.ofLp q‖ ^ 2 * K j q p ≤ ∑ q, rY (sys := sys) (L := L) j q * ‖a.ofLp q‖ ^ 2 := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [← Finset.mul_sum]
      calc ‖a.ofLp q‖ ^ 2 * ∑ p, K j q p ≤ ‖a.ofLp q‖ ^ 2 * rY (sys := sys) (L := L) j q :=
            mul_le_mul_of_nonneg_left (hcol j q) (sq_nonneg _)
        _ = _ := by ring
    have h2 : ∑ q, ∑ p, ‖b.ofLp p‖ ^ 2 * K j q p ≤ ∑ p, rY (sys := sys) (L := L) j p * ‖b.ofLp p‖ ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [← Finset.mul_sum]
      calc ‖b.ofLp p‖ ^ 2 * ∑ q, K j q p ≤ ‖b.ofLp p‖ ^ 2 * rY (sys := sys) (L := L) j p :=
            mul_le_mul_of_nonneg_left (hrow j p) (sq_nonneg _)
        _ = _ := by ring
    exact mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  calc ∑ q, ∑ p, ‖a.ofLp q‖ * ‖b.ofLp p‖ * ‖ycK sys L p₀ N q p‖
      ≤ ∑ q, ∑ p, ∑ j, ‖a.ofLp q‖ * ‖b.ofLp p‖ * K j q p := by
        refine Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun p _ => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hdec q p) (by positivity)
    _ = ∑ j, ∑ q, ∑ p, ‖a.ofLp q‖ * ‖b.ofLp p‖ * K j q p :=
        sum3_comm (fun q p j => ‖a.ofLp q‖ * ‖b.ofLp p‖ * K j q p)
    _ ≤ _ := Finset.sum_le_sum fun j _ => hj j

lemma rY_le (hL : 0 < L) (j : Ch eta) (q : Cfg eta N) :
    rY (sys := sys) (L := L) j q ≤ CYc sys L j * LamB sys N * (Real.sqrt 2 * Real.sqrt (Xall q)) := by
  unfold rY
  have h0 : 0 ≤ CYc sys L j * LamB sys N :=
    mul_nonneg (CYc_nonneg hL j) (LamB_nonneg (sys := sys) N)
  refine mul_le_mul_of_nonneg_left ?_ h0
  refine (piC_le_sqrt j (cidx N q)).trans ?_
  rw [← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  have : ∑ c ∈ moved j, nsq (cidx N q c) ≤ Xall q :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun c _ _ => FSLattice.lsq_nonneg _)
  linarith

end YForm

/-! ## The bulk-fed dressing -/

section Bulk

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

omit [Fintype ν] in
lemma mu_div_Mtot_pair (pr : FiniteElectronPair eta) :
    muCh sys (.inr pr) / Mtot sys (.inr pr) ≤ 1 / 4 := by
  have ha := sys.mass_pos pr.1.1
  have hb := sys.mass_pos pr.1.2
  have hM := Mtot_pos sys (.inr pr)
  simp only [muCh, Mtot]
  rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg (sys.mass pr.1.1 - sys.mass pr.1.2)]

omit [Fintype ν] in
/-- A hop from the bulk ball out of the cube has `|θ| > 3n/4`. -/
lemma rho_gt_of_bulk_out {n : ℕ} {j : Ch eta} {q p : Cfg eta N}
    (hj : OnCh j (cidx N q) (cidx N p)) (hq : ¬ InP (n : ℝ) (cidx N q))
    (hp : InQ (n : ℝ) (cidx N p)) : 3 * n / 4 < FSChannel.rho (chT N j q p) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [InP, not_forall, not_le] at hq
  obtain ⟨c, i, hci⟩ := hq
  have e := cidx_onCh hj
  have hqc : (cidx N q c i : ℝ) = (cidx N p c i : ℝ) + (tr j (chT N j q p) c i : ℝ) := by
    rw [e]; simp
  have htr := abs_tr_le j (chT N j q p) c i
  have hθi := abs_coord_le_rho (chT N j q p) i
  have hpc : |((cidx N p c i : ℤ) : ℝ)| ≤ n / 4 :=
    (abs_coord_le_rho (cidx N p c) i).trans (rho_le_of_inQ hn0 hp c)
  rw [hqc] at hci
  have := abs_add_le ((cidx N p c i : ℤ) : ℝ) ((tr j (chT N j q p) c i : ℤ) : ℝ)
  linarith

/-- **The bulk-fed dressing is `potMaj`-dominated**: for `p ∈ Q`, `q ∉ P` (`n ≥ 8`),
`|y(q, p)| ≤ potMaj(q, p)`. -/
theorem norm_ycK_bulk_le (hL : 0 < L) {n : ℕ} (hn : 8 ≤ n) {q p : Cfg eta N}
    (hq : ¬ InP (n : ℝ) (cidx N q)) (hp : InQ (n : ℝ) (cidx N p)) :
    ‖ycK sys L p₀ N q p‖ ≤ potMaj sys L (cidx N q) (cidx N p) := by
  have hg := gF_pos hL
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases h0 : ycK sys L p₀ N q p = 0
  · rw [h0, norm_zero]; exact potMaj_nonneg sys hL _ _
  have hgap : gapC sys L N q p := by
    by_contra hg'
    apply h0
    unfold ycK FSKernel.divK
    dsimp only
    unfold gcmGap
    rw [if_neg hg']
    split_ifs <;> simp
  obtain ⟨hne, j, hj, -⟩ := hgap
  have hne' : cidx N q ≠ cidx N p := fun h => hne (finiteConfigLatticeIndex_injective eta N h)
  have hμ := muCh_pos sys j
  have hM := Mtot_pos sys j
  have hcC := chC_nonneg sys hL j
  set θ := chT N j q p
  set ρ := FSChannel.rho θ
  have hρ : 3 * n / 4 < ρ := rho_gt_of_bulk_out hj hq hp
  have hρ0 : 0 < ρ := by
    have : (0 : ℝ) < 3 * n / 4 := by have : (8 : ℝ) ≤ n := by exact_mod_cast hn
                                     linarith
    linarith
  have hρsq : ρ ^ 2 = FSLattice.lsq θ := FSChannel.rho_sq θ
  -- the gap
  have hcsq : ∑ i, cCh sys j (cidx N p) i ^ 2 ≤ (n / 4 : ℝ) ^ 2 :=
    cCh_sq_le sys j (cidx N p) (fun c _ => hp c)
  have hdot := FSLattice.dot_sq_le (cCh sys j (cidx N p)) θ
  have hgapE : gF L ^ 2 * ρ ^ 2 / (6 * muCh sys j) ≤ |Asym sys L N q - Asym sys L N p| := by
    rw [Asym_hop hj, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))]
    have hF : ρ ^ 2 / 3 ≤ |FSLattice.slabF (cCh sys j (cidx N p)) θ| := by
      have ht : |∑ i, (θ i : ℝ) * cCh sys j (cidx N p) i| ≤ ρ * (n / 4) := by
        rw [← Real.sqrt_sq (abs_nonneg _), sq_abs]
        rw [show ρ * (n / 4 : ℝ) = Real.sqrt ((ρ * (n / 4)) ^ 2) by
          rw [Real.sqrt_sq (by positivity)]]
        apply Real.sqrt_le_sqrt
        rw [mul_pow, hρsq]
        exact hdot.trans (mul_le_mul_of_nonneg_left hcsq (FSLattice.lsq_nonneg θ))
      have e : FSLattice.slabF (cCh sys j (cidx N p)) θ =
          FSLattice.lsq θ + 2 * ∑ i, (θ i : ℝ) * cCh sys j (cidx N p) i := rfl
      rw [e, ← hρsq]
      have h1 : ρ * (n / 4) ≤ ρ ^ 2 / 3 := by nlinarith
      rw [abs_le] at ht
      rw [le_abs]
      left
      linarith [ht.1]
    calc gF L ^ 2 * ρ ^ 2 / (6 * muCh sys j) = gF L ^ 2 / (2 * muCh sys j) * (ρ ^ 2 / 3) := by
          field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hF (by positivity)
  -- the com coefficient
  have hpi : piC j (cidx N p) ≤ n / 2 := by
    cases j with
    | inl a => simp only [piC]; positivity
    | inr pr =>
      simp only [piC]
      have h1 := FSChannel.rho_add_le (cidx N p pr.1.1) (cidx N p pr.1.2)
      have h2 := rho_le_of_inQ hn0 hp pr.1.1
      have h3 := rho_le_of_inQ hn0 hp pr.1.2
      linarith
  have hE0 : Asym sys L N q ≠ Asym sys L N p := by
    intro h; rw [h, sub_self, abs_zero] at hgapE
    have : 0 < gF L ^ 2 * ρ ^ 2 / (6 * muCh sys j) := by positivity
    linarith
  have hd : 0 < |Asym sys L N q - Asym sys L N p| := abs_pos.mpr (sub_ne_zero.mpr hE0)
  rw [potMaj_eq_chan hL hj hne']
  change ‖ycK sys L p₀ N q p‖ ≤ chC sys L j / FSLattice.lsq θ
  unfold ycK FSKernel.divK
  dsimp only
  rw [if_neg hE0, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_neg,
    Complex.norm_I, one_mul]
  have hg1 : ‖gcmGap sys L p₀ N q p‖ ≤ ‖gcmK sys L p₀ N q p‖ := by
    unfold gcmGap; split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hg2 : ‖gcmK sys L p₀ N q p‖ ≤ chC sys L j / FSLattice.lsq θ *
      (gF L ^ 2 * ρ * piC j (cidx N p) / Mtot sys j) := by
    rw [gcmK_eq hL hj, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul (norm_wNK_chan_le hL hj hne) (abs_comC_le sys p₀ (gF L) j _ _)
      (abs_nonneg _) (by rw [← hρsq]; positivity)
  have key : gF L ^ 2 * ρ * piC j (cidx N p) / Mtot sys j ≤ gF L ^ 2 * ρ ^ 2 / (6 * muCh sys j) := by
    cases j with
    | inl a =>
      have : piC (.inl a : Ch eta) (cidx N p) = 0 := rfl
      rw [this, mul_zero, zero_div]; positivity
    | inr pr =>
      have h1 := mu_div_Mtot_pair (sys := sys) pr
      have hμ' := muCh_pos sys (.inr pr)
      have hM' := Mtot_pos sys (.inr pr)
      have h2 : piC (.inr pr) (cidx N p) ≤ 2 * ρ / 3 := by linarith
      rw [div_le_iff₀ hM'] at h1
      rw [div_le_div_iff₀ hM' (by positivity)]
      have hp0 := piC_nonneg (.inr pr) (cidx N p)
      have : gF L ^ 2 * ρ * piC (.inr pr) (cidx N p) * (6 * muCh sys (.inr pr)) ≤
          gF L ^ 2 * ρ * (2 * ρ / 3) * (6 * (1 / 4 * Mtot sys (.inr pr))) := by
        gcongr
      nlinarith
  rw [div_le_iff₀ hd]
  calc ‖gcmGap sys L p₀ N q p‖ ≤ chC sys L j / FSLattice.lsq θ *
        (gF L ^ 2 * ρ * piC j (cidx N p) / Mtot sys j) := hg1.trans hg2
    _ ≤ chC sys L j / FSLattice.lsq θ * |Asym sys L N q - Asym sys L N p| :=
        mul_le_mul_of_nonneg_left (key.trans hgapE) (by rw [← hρsq]; positivity)

end Bulk

/-! ## The endpoint of the com elimination -/

section Endpoint

variable (sys : CoulombSystem eta ν) {L : ℝ} {N : ℕ}

/-- The bulk-fed endpoint for any `potMaj`-dominated kernel:
`|⟨R u, κ Q u⟩| ≤ 2 η m_max c_E √C₁ M² x⁶`. -/
lemma endpoint_bulk_kop (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n) (hK : 4 ≤ gF L * n) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) {x : ℝ} (hx0 : 0 ≤ x)
    (hxdef : x = (gF L * n) ^ (-(1 / 2 : ℝ)))
    (hδ2 : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖ ≤ eta * M * x)
    (κ : Cfg eta N → Cfg eta N → ℂ) (hκ : ∀ q p, ‖κ q p‖ ≤ potMaj sys L (cidx N q) (cidx N p)) :
    ‖⟪RN N n u, FSKernel.kop κ (QN N n u)⟫_ℂ‖ ≤ 4 * eta * mmax sys * FSNormal.cE sys L *
      Real.sqrt (Fintype.card (Ch eta) * (∑ j : Ch eta, chC sys L j ^ 2) * (1000 * gF L / 3) *
        FSChannel.Zs 2) * M ^ 2 * x ^ 6 / 2 := by
  have hK0 : 0 < gF L * n := by linarith
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := gF_pos hL
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  have h1 := norm_inner_RN_le sys hL n u (FSKernel.kop κ (QN N n u))
  have h2 := norm_sq_R_kop_Q_le sys hL hn κ hκ u
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁ : ℝ, C₁ = Fintype.card (Ch eta) * (∑ j : Ch eta, chC sys L j ^ 2) *
      (1000 * gF L / 3) * FSChannel.Zs 2 := ⟨_, rfl⟩
  rw [← hC₁def]
  have hC₁ : 0 ≤ C₁ := by
    rw [hC₁def]
    have := (FSChannel.Zs_pos (by norm_num : (3 : ℝ) / 2 < 2)).le
    have : 0 ≤ ∑ j : Ch eta, chC sys L j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    positivity
  have hcE := FSNormal.one_le_cE (sys := sys) (L := L)
  have hwt : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖ ≤ M := by
    have := hu.1; have := norm_nonneg u; linarith
  have hx2 : x ^ 2 = 1 / (gF L * n) := by rw [hxdef, ← inv_eq_xpow hK0, one_div]
  have e : (Fintype.card (Ch eta) : ℝ) * ∑ j : Ch eta, chC sys L j ^ 2 * (1000 / (3 * n)) *
      FSChannel.Zs 2 * (FSNormal.cE sys L ^ 2 * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖ ^ 2) =
      C₁ * x ^ 2 * (FSNormal.cE sys L * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖) ^ 2 := by
    rw [hx2, hC₁def, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    field_simp
  rw [e] at h2
  have h3 : ‖RN N n (FSKernel.kop κ (QN N n u))‖ ≤ Real.sqrt C₁ * x * (FSNormal.cE sys L * M) := by
    have h4 : ‖RN N n (FSKernel.kop κ (QN N n u))‖ ≤ Real.sqrt C₁ * x *
        (FSNormal.cE sys L * ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖) := by
      have h5 := Real.sqrt_le_sqrt h2
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity), Real.sqrt_mul hC₁,
        Real.sqrt_sq hx0, Real.sqrt_sq (by positivity)] at h5
      exact h5
    refine h4.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact mul_le_mul_of_nonneg_left hwt (by positivity)
  have hmm := one_le_mmax sys
  have h5 : 1 / (1 + (gF L * n) ^ 2 / (2 * mmax sys)) ≤ 2 * mmax sys * x ^ 4 := by
    have hx4 : x ^ 4 = 1 / (gF L * n) ^ 2 := by
      rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx2]; field_simp
    rw [hx4, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [sq_nonneg (gF L * n)]
  have h6 : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖ *
      ‖RN N n (FSKernel.kop κ (QN N n u))‖ ≤ (eta * M * x) * (Real.sqrt C₁ * x * (FSNormal.cE sys L * M)) :=
    mul_le_mul hδ2 h3 (norm_nonneg _) (by positivity)
  calc ‖⟪RN N n u, FSKernel.kop κ (QN N n u)⟫_ℂ‖
      ≤ ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖ * ‖RN N n (FSKernel.kop κ (QN N n u))‖ /
          (1 + (gF L * n) ^ 2 / (2 * mmax sys)) := h1
    _ = ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖ * ‖RN N n (FSKernel.kop κ (QN N n u))‖ *
          (1 / (1 + (gF L * n) ^ 2 / (2 * mmax sys))) := by rw [mul_one_div]
    _ ≤ (eta * M * x) * (Real.sqrt C₁ * x * (FSNormal.cE sys L * M)) * (2 * mmax sys * x ^ 4) :=
        mul_le_mul h6 h5 (by positivity) (by positivity)
    _ = _ := by ring


variable {sys}

/-- `Σ r_j |res S u|² ≤ C_j Λ_N √2 √c_X η² M² l⁻⁴` for a good state with tails at `l`. -/
lemma sum_rY_res_le (hL : 0 < L) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u)
    (S : Cfg eta N → Prop) {l : ℝ} (hl : 1 ≤ l)
    (hS : ∀ q, S q → ∃ c, l < finitePlaneWaveKabs (2 * Real.pi / L) N (q c)) (j : Ch eta) :
    ∑ q, rY (sys := sys) (L := L) j q * ‖(FSKernel.res S u).ofLp q‖ ^ 2 ≤
      CYc sys L j * LamB sys N * (Real.sqrt 2 * Real.sqrt (cXw sys L)) *
        (eta ^ 2 * M ^ 2 * l ^ (-(4 : ℝ))) := by
  have hl0 : 0 < l := by linarith
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  set v := FSKernel.res S u
  have hv := (res_tails_good sys hu S hl hS).1
  have hX := sum_Xall_res_le sys hL hu S hl hS
  have hC0 : 0 ≤ CYc sys L j * LamB sys N := mul_nonneg (CYc_nonneg hL j) (LamB_nonneg (sys := sys) N)
  have hcX : 0 ≤ cXw sys L := by unfold cXw; have := gF_pos hL; have := one_le_mmax sys; positivity
  have h1 : ∑ q, rY (sys := sys) (L := L) j q * ‖v.ofLp q‖ ^ 2 ≤
      CYc sys L j * LamB sys N * Real.sqrt 2 * ∑ q, Real.sqrt (Xall q) * ‖v.ofLp q‖ ^ 2 := by
    rw [mul_assoc (CYc sys L j * LamB sys N), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have := rY_le (sys := sys) hL j q
    calc rY (sys := sys) (L := L) j q * ‖v.ofLp q‖ ^ 2
        ≤ CYc sys L j * LamB sys N * (Real.sqrt 2 * Real.sqrt (Xall q)) * ‖v.ofLp q‖ ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = _ := by ring
  have h2 : ∑ q, Real.sqrt (Xall q) * ‖v.ofLp q‖ ^ 2 ≤
      ‖v‖ * Real.sqrt (∑ q, (1 + Xall q) * ‖v.ofLp q‖ ^ 2) := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun q => ‖v.ofLp q‖)
      (fun q => Real.sqrt (Xall q) * ‖v.ofLp q‖)
    have e1 : ∑ q, ‖v.ofLp q‖ * (Real.sqrt (Xall q) * ‖v.ofLp q‖) =
        ∑ q, Real.sqrt (Xall q) * ‖v.ofLp q‖ ^ 2 := Finset.sum_congr rfl fun q _ => by ring
    have e2 : ∑ q, (Real.sqrt (Xall q) * ‖v.ofLp q‖) ^ 2 = ∑ q, Xall q * ‖v.ofLp q‖ ^ 2 :=
      Finset.sum_congr rfl fun q _ => by rw [mul_pow, Real.sq_sqrt (Xall_nonneg q)]
    rw [e1, e2, ← EuclideanSpace.norm_eq] at hcs
    refine hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (norm_nonneg _))
    exact Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h3 : ‖v‖ * Real.sqrt (∑ q, (1 + Xall q) * ‖v.ofLp q‖ ^ 2) ≤
      (eta * M * l ^ (-(5 / 2 : ℝ))) * (Real.sqrt (cXw sys L) * (eta * M * l ^ (-(3 / 2 : ℝ)))) := by
    refine mul_le_mul hv ?_ (Real.sqrt_nonneg _) (by positivity)
    refine (Real.sqrt_le_sqrt hX).trans (le_of_eq ?_)
    have hp : l ^ (-(3 : ℝ)) = (l ^ (-(3 / 2 : ℝ))) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num
    rw [hp, show eta ^ 2 * M ^ 2 * (l ^ (-(3 / 2 : ℝ))) ^ 2 = (eta * M * l ^ (-(3 / 2 : ℝ))) ^ 2 by ring,
      Real.sqrt_mul hcX, Real.sqrt_sq (by positivity)]
  have hp4 : l ^ (-(5 / 2 : ℝ)) * l ^ (-(3 / 2 : ℝ)) = l ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_add hl0]; norm_num
  calc ∑ q, rY (sys := sys) (L := L) j q * ‖v.ofLp q‖ ^ 2
      ≤ CYc sys L j * LamB sys N * Real.sqrt 2 * (‖v‖ * Real.sqrt (∑ q, (1 + Xall q) * ‖v.ofLp q‖ ^ 2)) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ ≤ CYc sys L j * LamB sys N * Real.sqrt 2 *
          ((eta * M * l ^ (-(5 / 2 : ℝ))) * (Real.sqrt (cXw sys L) * (eta * M * l ^ (-(3 / 2 : ℝ))))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = CYc sys L j * LamB sys N * (Real.sqrt 2 * Real.sqrt (cXw sys L)) *
          (eta ^ 2 * M ^ 2 * (l ^ (-(5 / 2 : ℝ)) * l ^ (-(3 / 2 : ℝ)))) := by ring
    _ = _ := by rw [hp4]

/-- The bulk constant of the com endpoint. -/
noncomputable def CYb (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  4 * eta * mmax sys * FSNormal.cE sys L * Real.sqrt (Fintype.card (Ch eta) *
    (∑ j : Ch eta, chC sys L j ^ 2) * (1000 * gF L / 3) * FSChannel.Zs 2) / 2

/-- The tail constant of the com endpoint. -/
noncomputable def CYt (sys : CoulombSystem eta ν) (L : ℝ) (N : ℕ) : ℝ :=
  ∑ j : Ch eta, CYc sys L j * LamB sys N * (Real.sqrt 2 * Real.sqrt (cXw sys L))

/-- **The endpoint of the com elimination**: for a good box state (`n ≥ 8`, `K = g n ≥ 4`),
`|⟨u, Y₁ u⟩| ≤ 2 C_b M² K⁻³ + 3 C_t η² M² (K/4)⁻⁴`. -/
theorem norm_Y1_form_le {p₀ : Fin eta} (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {n : ℕ} (hn : 8 ≤ n) (hK : 4 ≤ gF L * n) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖⟪u, Y1N sys L p₀ N n u⟫_ℂ‖ ≤ 2 * (CYb sys L * M ^ 2 * (gF L * n) ^ (-(3 : ℝ))) +
      3 * (CYt sys L N * (eta ^ 2 * M ^ 2 * (gF L * n / 4) ^ (-(4 : ℝ)))) := by
  classical
  set Y := YcN sys L p₀ N
  have hg := gF_pos hL
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2 : 2 ≤ n := by omega
  have hK0 : 0 < gF L * n := by linarith
  have hK1 : 1 ≤ gF L * n := by linarith
  have hK4 : 1 ≤ gF L * n / 4 := by linarith
  have hYs : Y.IsSymmetric := YcN_symm hL H hKernel
  have hsplit : u = PN N n u + RN N n u := by rw [RN_eq]; abel
  have hexp : ⟪u, Y1N sys L p₀ N n u⟫_ℂ =
      ⟪PN N n u, Y (RN N n u)⟫_ℂ + ⟪RN N n u, Y (PN N n u)⟫_ℂ + ⟪RN N n u, Y (RN N n u)⟫_ℂ := by
    unfold Y1N
    rw [LinearMap.sub_apply, inner_sub_right, LinearMap.comp_apply, LinearMap.comp_apply,
      ← PN_symm n u]
    have e : ⟪u, Y u⟫_ℂ = ⟪PN N n u + RN N n u, Y (PN N n u + RN N n u)⟫_ℂ := by rw [← hsplit]
    rw [e, map_add, inner_add_left, inner_add_right, inner_add_right]
    ring
  have hPR : ‖⟪PN N n u, Y (RN N n u)⟫_ℂ‖ = ‖⟪RN N n u, Y (PN N n u)⟫_ℂ‖ := by
    rw [← hYs (PN N n u) (RN N n u), ← inner_conj_symm, Complex.norm_conj]
  set Fp : Cfg eta N → Prop := fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)
  have hRP : ⟪RN N n u, Y (PN N n u)⟫_ℂ = ⟪RN N n u, Y (QN N n u)⟫_ℂ +
      ⟪RN N n u, Y (FSKernel.res Fp u)⟫_ℂ := by
    rw [PN_eq_QN_add, map_add, inner_add_right]
  -- the bulk-fed piece
  set κ' : Cfg eta N → Cfg eta N → ℂ := fun q p =>
    if ¬ InP (n : ℝ) (cidx N q) ∧ InQ (n : ℝ) (cidx N p) then ycK sys L p₀ N q p else 0
  have hκ' : ∀ q p, ‖κ' q p‖ ≤ potMaj sys L (cidx N q) (cidx N p) := by
    intro q p
    simp only [κ']
    split_ifs with h
    · exact norm_ycK_bulk_le hL hn h.1 h.2
    · rw [norm_zero]; exact potMaj_nonneg sys hL _ _
  have hbulk_eq : RN N n (Y (QN N n u)) = RN N n (FSKernel.kop κ' (QN N n u)) := by
    ext q
    simp only [FSKernel.res_apply, Y, FSKernel.kop_apply, κ']
    by_cases hq : InP (n : ℝ) (cidx N q)
    · simp [hq]
    simp only [hq, not_false_eq_true, if_true, true_and]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : InQ (n : ℝ) (cidx N p)
    · simp [hp]
    · simp [hp]
  have hbulk : ⟪RN N n u, Y (QN N n u)⟫_ℂ = ⟪RN N n u, FSKernel.kop κ' (QN N n u)⟫_ℂ := by
    have e1 : ⟪RN N n u, Y (QN N n u)⟫_ℂ = ⟪RN N n u, RN N n (Y (QN N n u))⟫_ℂ := by
      rw [← RN_symm n (RN N n u) (Y (QN N n u)), RN_idem]
    have e2 : ⟪RN N n u, FSKernel.kop κ' (QN N n u)⟫_ℂ =
        ⟪RN N n u, RN N n (FSKernel.kop κ' (QN N n u))⟫_ℂ := by
      rw [← RN_symm n (RN N n u) (FSKernel.kop κ' (QN N n u)), RN_idem]
    rw [e1, hbulk_eq, ← e2]
  obtain ⟨x, hxdef⟩ : ∃ x, x = (gF L * n) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hxdef]; exact Real.rpow_nonneg hK0.le _
  have hδt := res_tails_good sys hu (fun q : Cfg eta N => ¬ InP (n : ℝ) (cidx N q)) hK1 (by
    intro q hq
    obtain ⟨c, hc⟩ := exists_reg_of_not_inP (by positivity) hq
    exact ⟨c, kabs_gt_of_lsq_gt hL (by positivity) q c hc⟩)
  have hδ2 : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 (RN N n u)‖ ≤ eta * M * x := by
    rw [hxdef]; exact hδt.2
  have hA := endpoint_bulk_kop sys hL hn2 hK hu hx0 hxdef hδ2 κ' hκ'
  have hx6 : x ^ 6 = (gF L * n) ^ (-(3 : ℝ)) := by
    have h6 := rpow_half_pow hK0 6
    have e : -(((6 : ℕ) : ℝ) / 2) = -(3 : ℝ) := by norm_num
    rw [e] at h6
    rw [hxdef]; exact h6.symm
  have hA' : ‖⟪RN N n u, Y (QN N n u)⟫_ℂ‖ ≤ CYb sys L * M ^ 2 * (gF L * n) ^ (-(3 : ℝ)) := by
    rw [hbulk, ← hx6]
    refine hA.trans (le_of_eq ?_)
    unfold CYb; ring
  -- the tail pieces
  have sR : ∀ q : Cfg eta N, ¬ InP (n : ℝ) (cidx N q) →
      ∃ c, gF L * n / 4 < finitePlaneWaveKabs (2 * Real.pi / L) N (q c) := by
    intro q hq
    obtain ⟨c, hc⟩ := exists_reg_of_not_inP hn0 hq
    refine ⟨c, lt_of_le_of_lt ?_ (kabs_gt_of_lsq_gt hL hn0 q c hc)⟩
    nlinarith
  have sF : ∀ q : Cfg eta N, Fp q → ∃ c, gF L * n / 4 < finitePlaneWaveKabs (2 * Real.pi / L) N (q c) := by
    intro q hq
    obtain ⟨c, hc⟩ := exists_reg_of_not_inQ hq.2
    refine ⟨c, ?_⟩
    have := kabs_gt_of_lsq_gt hL (by positivity : (0 : ℝ) ≤ n / 4) q c hc
    linarith [show gF L * (n / 4) = gF L * n / 4 by ring]
  set T := eta ^ 2 * M ^ 2 * (gF L * n / 4) ^ (-(4 : ℝ))
  have tR := fun j => sum_rY_res_le hL hu (fun q : Cfg eta N => ¬ InP (n : ℝ) (cidx N q)) hK4 sR j
  have tF := fun j => sum_rY_res_le hL hu Fp hK4 sF j
  have hT0 : 0 ≤ T := by
    have : 0 < gF L * n / 4 := by linarith
    positivity
  have hcj : ∀ j, 0 ≤ CYc sys L j * LamB sys N * (Real.sqrt 2 * Real.sqrt (cXw sys L)) := fun j =>
    mul_nonneg (mul_nonneg (CYc_nonneg hL j) (LamB_nonneg (sys := sys) N)) (by positivity)
  have hsq : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ c → b ≤ c → Real.sqrt a * Real.sqrt b ≤ c := by
    intro a b c ha hb hc hac hbc
    calc Real.sqrt a * Real.sqrt b ≤ Real.sqrt c * Real.sqrt c :=
          mul_le_mul (Real.sqrt_le_sqrt hac) (Real.sqrt_le_sqrt hbc) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = c := Real.mul_self_sqrt hc
  have hrY0 : ∀ j (v : En eta N), 0 ≤ ∑ q, rY (sys := sys) (L := L) j q * ‖v.ofLp q‖ ^ 2 :=
    fun j v => Finset.sum_nonneg fun q _ => mul_nonneg (rY_nonneg hL j q) (sq_nonneg _)
  have hB : ‖⟪RN N n u, Y (FSKernel.res Fp u)⟫_ℂ‖ ≤ CYt sys L N * T := by
    refine (norm_form_ycK_le hL H hKernel _ _).trans ?_
    unfold CYt
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hsq _ _ _ (hrY0 j _) (hrY0 j _)
      (mul_nonneg (hcj j) hT0) (tR j) (tF j)
  have hC : ‖⟪RN N n u, Y (RN N n u)⟫_ℂ‖ ≤ CYt sys L N * T := by
    refine (norm_form_ycK_le hL H hKernel _ _).trans ?_
    unfold CYt
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hsq _ _ _ (hrY0 j _) (hrY0 j _)
      (mul_nonneg (hcj j) hT0) (tR j) (tR j)
  rw [hexp]
  have h3 := norm_add₃_le (a := ⟪PN N n u, Y (RN N n u)⟫_ℂ) (b := ⟪RN N n u, Y (PN N n u)⟫_ℂ)
    (c := ⟪RN N n u, Y (RN N n u)⟫_ℂ)
  have h2 : ‖⟪RN N n u, Y (PN N n u)⟫_ℂ‖ ≤ CYb sys L * M ^ 2 * (gF L * n) ^ (-(3 : ℝ)) +
      CYt sys L N * T := by
    rw [hRP]; exact (norm_add_le _ _).trans (add_le_add hA' hB)
  rw [hPR] at h3
  linarith

end Endpoint

end FSFlux
