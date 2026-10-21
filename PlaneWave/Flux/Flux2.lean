import PlaneWave.Flux.PhaseBulkBlock

/-!
# Flux route, part 6: `prop:phase` and `thm:flux2`

For a state `u = w_s` (`x = S u`, `1_Q u` its bulk part `liftQ`), with `z = ⟨W u, Y x⟩`:

* `Wf_re_eq` (eq:herm): `Re 𝔚(u, u) = -2 Im z`;
* `inner_W_Y_split`: `z = ⟨W 1_Q u, Y 1_Q x⟩ + ⟨W (u - 1_Q u), Y 1_Q x⟩ + ⟨Y 1_Q (W u), R x⟩`
  (the bulk block of `C₁`, its tail part, and `C₂`);
* the three bounds, for `FGood M w` and `K = g n ≥ 4`:
  - the bulk block (`bulk_good_le`): `|Im ⟨W 1_Q u, Y 1_Q x⟩| ≤ C M² K^{-2+4ε}`, by `bulk_im_le`
    and eq:nrm-b (`nrm_b`);
  - the tail part of `C₁` (`tail_C1_le`): `|⟨W (u - 1_Q u), Y 1_Q x⟩| ≤ C M² K^{-2}`, Hardy on the
    `K/4`-tailed `u - 1_Q u` (`‖W(u - 1_Q u)‖ ≤ C M K^{-3/2}`) against the dressed tail
    `‖Y 1_Q x‖ ≤ C M K^{-1/2}` — no chains are needed;
  - `C₂` (`C2_le`, eq:chain-b): `|⟨Y 1_Q (W u), R x⟩| ≤ C M² K^{-2+2ε}`, the fractional Gram
    bound with the weighted potential tail on `Q` (`W_tails` and `moment_Q`);
* **`thm_phase`** (`prop:phase`): `|𝔚(ψ(s), ψ(s))| ≤ C_ε Ξ² K^{-2+4ε}` for `0 < ε ≤ 1/4`;
* **`thm_flux2`**: `|∫₀ᵗ (𝔊(ψ, ψ) - 𝔊(Pψ, Pψ))| ≤ C_ε Ξ² (K^{-3} + t K^{-2+4ε})`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Weights and the norm inventory -/

omit [Fintype ν] in
lemma Ws_mono {s s' : ℝ} (h : s ≤ s') (p : Cf eta) : Ws s p ≤ Ws s' p := by
  unfold Ws
  have := lsqC_nonneg p
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

section Inventory

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)

omit [Fintype ν] in
include hL in
/-- **eq:nrm-b**: for a good state, `Σ_Q (1+|p|²)^{2(r+1)} |ψ_p|² ≤ c_L² C_r (2M)² (K/4)^{4r-1}`,
`r > 1/4`. -/
theorem nrm_b {n : ℕ} (hΛ : 1 ≤ gF L * n / 4) {r : ℝ} (hr : 1 / 4 < r) {M : ℝ}
    {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    ∑ p ∈ Qs eta n, Ws (r + 1) p * ‖Sm eta L w p‖ ^ 2 ≤
      cL sys L ^ 2 * (FSDatum.momentConst1 eta r ((eta : ℝ) / gF L ^ 2) * (2 * M) ^ 2 *
        (gF L * n / 4) ^ (4 * r - 1)) := by
  have hM := hF.nonneg
  set v : L2 eta := Sm eta L w + coulombFourierKineticH2 sys (gF L) w
  have hv : ‖v‖ ≤ 2 * M := by
    have := (norm_add_le (Sm eta L w) (coulombFourierKineticH2 sys (gF L) w)).trans hF.1
    linarith
  have htail : ∀ (a : Fin eta) (l : ℝ), 1 ≤ l → ‖tailMask (gF L) l a v‖ ^ 2 ≤ (2 * M) ^ 2 / l := by
    intro a l hl
    have hl0 : 0 < l := by linarith
    have h1 := (hF.2 a l hl).1
    have h2 := (hF.2 a l hl).2
    have h52 : l ^ (-(5 / 2 : ℝ)) ≤ l ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hl (by norm_num)
    have h3 : ‖tailMask (gF L) l a v‖ ≤ 2 * M * l ^ (-(1 / 2 : ℝ)) := by
      simp only [v, map_add]
      refine (norm_add_le _ _).trans ?_
      have := mul_le_mul_of_nonneg_left h52 hM
      linarith
    have hp := Real.rpow_nonneg hl0.le (-(1 / 2 : ℝ))
    calc ‖tailMask (gF L) l a v‖ ^ 2 ≤ (2 * M * l ^ (-(1 / 2 : ℝ))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ = (2 * M) ^ 2 / l := by
          have e : (l ^ (-(1 / 2 : ℝ))) ^ 2 = l⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]; norm_num [Real.rpow_neg_one]
          rw [mul_pow, e, div_eq_mul_inv]
  have hmom := moment_Q hL hΛ v hr (by positivity) hv htail
  have hcL : 0 ≤ cL sys L := by
    unfold cL; have := one_le_mtop sys; have : 0 < gF L ^ 2 := by have := gF_pos hL; positivity
    positivity
  have hpt : ∀ p, Ws (r + 1) p * ‖Sm eta L w p‖ ^ 2 ≤
      cL sys L ^ 2 * ((1 + lsqC p) ^ (2 * r) * ‖v p‖ ^ 2) := by
    intro p
    have hl := lsqC_nonneg p
    have hb : 0 < 1 + lsqC p := by linarith
    have hE0 : 0 ≤ Ek sys L p := by
      rw [Ek, E]
      exact Finset.sum_nonneg fun c _ => by
        have := sys.mass_pos c; have := nsq_nonneg (p c); positivity
    have hvp : v p = ((1 + Ek sys L p : ℝ) : ℂ) * Sm eta L w p := by
      simp only [v, lp.coeFn_add, Pi.add_apply, kinetic_apply', Sm]
      push_cast; ring
    have eW : Ws (r + 1) p = (1 + lsqC p) ^ (2 * r) * (1 + lsqC p) ^ 2 := by
      unfold Ws
      rw [show 2 * (r + 1) = 2 * r + 2 by ring, Real.rpow_add hb,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [eW, hvp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have h1 := one_add_lsqC_le (sys := sys) hL p
    have h2 : (1 + lsqC p) ^ 2 ≤ (cL sys L * (1 + Ek sys L p)) ^ 2 :=
      pow_le_pow_left₀ hb.le h1 2
    have h3 := Real.rpow_nonneg hb.le (2 * r)
    have h4 := sq_nonneg ‖Sm eta L w p‖
    calc (1 + lsqC p) ^ (2 * r) * (1 + lsqC p) ^ 2 * ‖Sm eta L w p‖ ^ 2
        ≤ (1 + lsqC p) ^ (2 * r) * (cL sys L * (1 + Ek sys L p)) ^ 2 * ‖Sm eta L w p‖ ^ 2 := by
          gcongr
      _ = cL sys L ^ 2 * ((1 + lsqC p) ^ (2 * r) * ((1 + Ek sys L p) * ‖Sm eta L w p‖) ^ 2) := by
          ring
  calc ∑ p ∈ Qs eta n, Ws (r + 1) p * ‖Sm eta L w p‖ ^ 2
      ≤ ∑ p ∈ Qs eta n, cL sys L ^ 2 * ((1 + lsqC p) ^ (2 * r) * ‖v p‖ ^ 2) :=
        Finset.sum_le_sum fun p _ => hpt p
    _ = cL sys L ^ 2 * ∑ p ∈ Qs eta n, (1 + lsqC p) ^ (2 * r) * ‖v p‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmom (sq_nonneg _)

variable (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel hL in
/-- `‖W u‖ ≤ √3 C_m M` for a good state. -/
lemma norm_W_good (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {M : ℝ}
    {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    ‖Wp sys L H w‖ ≤ Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * M := by
  have h1 : ‖Sm eta L w‖ ≤ M := by
    have := hF.1; have := norm_nonneg (coulombFourierKineticH2 sys (gF L) w); linarith
  have h2 : ‖coulombFourierKineticH2 sys (gF L) w‖ ≤ M := by
    have := hF.1; have := norm_nonneg (Sm eta L w); linarith
  have h := norm_W_le_of sys hL H hKernel Hunit hPeriodic w h1 h2 le_rfl
  have hM := hF.nonneg
  rw [show 3 * M * M = 3 * M ^ 2 by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq hM] at h
  linarith

/-- The tail constant of the potential output per unit `M`:
`T_W² = (2 m̄ C_tail(1))² + 3 C_m² (1 + 2g)`. -/
noncomputable def TW1 (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  Real.sqrt ((2 * sys.maxMass * CtW sys L Hunit 1) ^ 2 +
    3 * finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (1 + 2 * gF L))

include hKernel hL in
/-- **The potential tails of a good state at every threshold** (eq:lam-gen):
`‖1_{a, > l} W u‖² ≤ (T_W M)²/l` for `l ≥ 1`, and `‖W u‖ ≤ T_W M`. -/
theorem W_tails (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {M : ℝ}
    {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    ‖Wp sys L H w‖ ≤ TW1 sys L Hunit * M ∧
      ∀ (a : Fin eta) (l : ℝ), 1 ≤ l →
        ‖tailMask (gF L) l a (Wp sys L H w)‖ ^ 2 ≤ (TW1 sys L Hunit * M) ^ 2 / l := by
  have hM := hF.nonneg
  have hg := gF_pos hL
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hCt1 : 0 ≤ CtW sys L Hunit 1 := CtW_nonneg sys hL Hunit zero_le_one
  have hW := norm_W_good sys hL H hKernel Hunit hPeriodic hF
  set Cm := finiteCoulombPhysicalMassConstant sys L Hunit
  set T2 := (2 * sys.maxMass * CtW sys L Hunit 1) ^ 2 + 3 * Cm ^ 2 * (1 + 2 * gF L)
  have hT20 : 0 ≤ T2 := by positivity
  have hTW : (TW1 sys L Hunit * M) ^ 2 = T2 * M ^ 2 := by
    unfold TW1; rw [mul_pow, Real.sq_sqrt hT20]
  have hW2 : ‖Wp sys L H w‖ ^ 2 ≤ 3 * Cm ^ 2 * M ^ 2 := by
    calc ‖Wp sys L H w‖ ^ 2 ≤ (Real.sqrt 3 * Cm * M) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hW 2
      _ = 3 * Cm ^ 2 * M ^ 2 := by rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  constructor
  · have h1 : ‖Wp sys L H w‖ ^ 2 ≤ (TW1 sys L Hunit * M) ^ 2 := by
      rw [hTW]
      have : 3 * Cm ^ 2 ≤ T2 := by
        have : 0 ≤ (2 * sys.maxMass * CtW sys L Hunit 1) ^ 2 := sq_nonneg _
        have : 3 * Cm ^ 2 ≤ 3 * Cm ^ 2 * (1 + 2 * gF L) := by
          have : 0 ≤ 3 * Cm ^ 2 := by positivity
          nlinarith
        linarith
      nlinarith [sq_nonneg M]
    have hT0 : 0 ≤ TW1 sys L Hunit * M := mul_nonneg (Real.sqrt_nonneg _) hM
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hT0 two_ne_zero).mp h1
  · intro a l hl
    have hl0 : 0 < l := by linarith
    rw [hTW, le_div_iff₀ hl0]
    by_cases hl2 : 2 * gF L ≤ l
    · -- eq:lam-gen
      obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
        molecularCanonicalTailConstants_spec L hL
      have hm := sys.one_le_maxMass
      have hM2 : 0 ≤ 2 * sys.maxMass * M := by positivity
      have hw2 : ‖w‖ ≤ 2 * sys.maxMass * M := by
        have h := PlaneWaveDynamics.h2norm_le sys L w
        have h1 := hF.1
        have := norm_nonneg (Sm eta L w)
        have := norm_nonneg (coulombFourierKineticH2 sys (gF L) w)
        calc ‖w‖ ≤ sys.maxMass * (‖molecularH2StateMap eta (2 * Real.pi / L) w‖ +
              2 * ‖coulombFourierKineticH2 sys (2 * Real.pi / L) w‖) := h
          _ ≤ sys.maxMass * (2 * M) := by
              refine mul_le_mul_of_nonneg_left ?_ (by linarith)
              change ‖Sm eta L w‖ + 2 * ‖coulombFourierKineticH2 sys (gF L) w‖ ≤ 2 * M
              linarith
          _ = 2 * sys.maxMass * M := by ring
      have hρ : Real.sqrt (1 / l) ^ 2 * l = 1 := by
        rw [Real.sq_sqrt (by positivity)]; field_simp
      have h := potential_tail_le sys L H hKernel Hunit hL hPeriodic a l (Real.sqrt (1 / l))
        (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
        (molecularCanonicalKernelConstant L) (2 * sys.maxMass * M) hl (Real.sqrt_nonneg _) hρ
        hBlow hCs hBker hM2 hl2 hLow hKernelScale hSobolev w hw2
      have hct : CtW sys L Hunit (2 * sys.maxMass * M) = CtW sys L Hunit 1 * (2 * sys.maxMass * M) :=
        CtW_eq_mul sys Hunit _
      change ‖tailMask (gF L) l a (Wp sys L H w)‖ ≤ CtW sys L Hunit (2 * sys.maxMass * M) *
        Real.sqrt (1 / l) at h
      rw [hct] at h
      have h2 : ‖tailMask (gF L) l a (Wp sys L H w)‖ ^ 2 * l ≤
          (2 * sys.maxMass * CtW sys L Hunit 1) ^ 2 * M ^ 2 := by
        have h0 : 0 ≤ CtW sys L Hunit 1 * (2 * sys.maxMass * M) * Real.sqrt (1 / l) := by positivity
        have h3 := pow_le_pow_left₀ (norm_nonneg _) h 2
        calc ‖tailMask (gF L) l a (Wp sys L H w)‖ ^ 2 * l
            ≤ (CtW sys L Hunit 1 * (2 * sys.maxMass * M) * Real.sqrt (1 / l)) ^ 2 * l :=
              mul_le_mul_of_nonneg_right h3 hl0.le
          _ = (2 * sys.maxMass * CtW sys L Hunit 1) ^ 2 * M ^ 2 * (Real.sqrt (1 / l) ^ 2 * l) := by
              ring
          _ = _ := by rw [hρ, mul_one]
      have : 0 ≤ 3 * Cm ^ 2 * (1 + 2 * gF L) * M ^ 2 := by positivity
      nlinarith
    · push Not at hl2
      have h1 : ‖tailMask (gF L) l a (Wp sys L H w)‖ ^ 2 ≤ 3 * Cm ^ 2 * M ^ 2 :=
        (pow_le_pow_left₀ (norm_nonneg _) (norm_tailMask_le _ _ _ _) 2).trans hW2
      have h2 : ‖tailMask (gF L) l a (Wp sys L H w)‖ ^ 2 * l ≤ 3 * Cm ^ 2 * M ^ 2 * (1 + 2 * gF L) :=
        mul_le_mul h1 (by linarith) hl0.le (by positivity)
      have : 0 ≤ (2 * sys.maxMass * CtW sys L Hunit 1) ^ 2 * M ^ 2 := by positivity
      nlinarith

end Inventory

/-! ## The three pieces of `𝔚` -/

section Phase

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta) {n : ℕ} (hn : 2 ≤ n)

/-- **eq:herm**: `Re 𝔚(u, u) = -2 Im ⟨W u, Y S u⟩`. -/
lemma Wf_re_eq (u : MolecularFourierH2 eta) :
    (Wf sys hL hn p₀ H u u).re = -2 * (⟪Wp sys L H u, Yop sys hL hn p₀ (Sm eta L u)⟫_ℂ).im := by
  unfold Wf
  rw [← inner_conj_symm (Yop sys hL hn p₀ (Sm eta L u)) (Wp sys L H u)]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_re,
    Complex.conj_im]
  ring

open Classical in
/-- `⟨v, Y (x - 1_Q x)⟩ = ⟨Y 1_Q v, R x⟩`. -/
lemma inner_Ysub (v x : L2 eta) :
    ⟪v, Yop sys hL hn p₀ (x - lpTruncate (Qs eta n) x)⟫_ℂ =
      ⟪Yop sys hL hn p₀ (lpTruncate (Qs eta n) v), x - molecularH2Truncate n x⟫_ℂ := by
  have hsub : Qs eta n ⊆ fourierConfigCube eta n := Qs_subset_cube (by omega)
  have hB : ⟪v, Yop sys hL hn p₀ (x - lpTruncate (Qs eta n) x)⟫_ℂ =
      ⟪lpTruncate (Qs eta n) v, Yop sys hL hn p₀ (x - lpTruncate (Qs eta n) x)⟫_ℂ := by
    refine inner_eq_of_pt _ _ _ _ fun q => ?_
    by_cases hq : q ∈ Qs eta n
    · left; refine ⟨?_, rfl⟩; rw [lpTruncate_apply, if_pos hq]
    · right; right
      have := Ysub_apply_of_not_inQ (sys := sys) p₀ hL hn x hq
      exact ⟨this, this⟩
  rw [hB, ← ContinuousLinearMap.adjoint_inner_left, adjoint_Yop]
  refine inner_eq_of_pt _ _ _ _ fun q => ?_
  by_cases hq : q ∈ fourierConfigCube eta n
  · right; left
    have := YQ_apply_of_inP (sys := sys) p₀ hL hn v hq
    exact ⟨this, this⟩
  · left
    refine ⟨rfl, ?_⟩
    have hqQ : q ∉ Qs eta n := fun h => hq (hsub h)
    rw [lp.coeFn_sub, Pi.sub_apply, lpTruncate_apply, if_neg hqQ, sub_zero, lp.coeFn_sub,
      Pi.sub_apply, molecularH2Truncate_apply, cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq,
      sub_zero]

/-- **The decomposition of `⟨W u, Y S u⟩`**: the bulk block of `C₁`, its tail part, and `C₂`. -/
lemma inner_W_Y_split (u : MolecularFourierH2 eta) :
    ⟪Wp sys L H u, Yop sys hL hn p₀ (Sm eta L u)⟫_ℂ =
      ⟪Wp sys L H (liftQ L n (Sm eta L u)), Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Sm eta L u))⟫_ℂ +
        ⟪Wp sys L H (u - liftQ L n (Sm eta L u)),
          Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Sm eta L u))⟫_ℂ +
        ⟪Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Wp sys L H u)),
          Sm eta L u - molecularH2Truncate n (Sm eta L u)⟫_ℂ := by
  set x := Sm eta L u
  have h1 : Yop sys hL hn p₀ x = Yop sys hL hn p₀ (lpTruncate (Qs eta n) x) +
      Yop sys hL hn p₀ (x - lpTruncate (Qs eta n) x) := by rw [← map_add]; congr 1; abel
  have h2 : Wp sys L H u = Wp sys L H (liftQ L n x) + Wp sys L H (u - liftQ L n x) := by
    rw [← map_add]; congr 1; abel
  rw [h1, inner_add_right, inner_Ysub sys hL p₀ hn, h2, inner_add_left]

include hKernel hL in
/-- **The tail part of `C₁`**: `|⟨W (u - 1_Q u), Y 1_Q x⟩| ≤ √3 C_m η M (K/4)^{-3/2} · c_{YQ} M/√n`
(Hardy on the `K/4`-tailed `u - 1_Q u` against the dressed tail). -/
theorem tail_C1_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hK : 4 ≤ gF L * n) {M : ℝ} {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    ‖⟪Wp sys L H (w - liftQ L n (Sm eta L w)),
        Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Sm eta L w))⟫_ℂ‖ ≤
      Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * eta * M *
          (gF L * n / 4) ^ (-(3 / 2 : ℝ)) * (cYQ sys L p₀ * M / Real.sqrt n) := by
  have hM := hF.nonneg
  have hlam : 1 ≤ gF L * n / 4 := by linarith
  have hl0 : 0 < gF L * n / 4 := by linarith
  set x := (eta : ℝ) * M
  have hx : 0 ≤ x := by positivity
  set U := w - liftQ L n (Sm eta L w)
  have e4 : gF L * ((n : ℕ) : ℝ) / 4 = gF L * n / 4 := rfl
  have hSU : ‖Sm eta L U‖ ≤ x * (gF L * n / 4) ^ (-(5 / 2 : ℝ)) := by
    rw [map_sub, stateMap_liftQ]
    refine (norm_sub_truncQ_le hL n _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n / 4) a (Sm eta L w)‖
        ≤ ∑ _a : Fin eta, M * (gF L * n / 4) ^ (-(5 / 2 : ℝ)) :=
          Finset.sum_le_sum fun a _ => (hF.2 a _ hlam).1
      _ = x * (gF L * n / 4) ^ (-(5 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; simp only [x]; ring
  have hTU : ‖coulombFourierKineticH2 sys (gF L) U‖ ≤ x * (gF L * n / 4) ^ (-(1 / 2 : ℝ)) := by
    rw [map_sub, kinetic_liftQ]
    refine (norm_sub_truncQ_le hL n _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n / 4) a (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ ∑ _a : Fin eta, M * (gF L * n / 4) ^ (-(1 / 2 : ℝ)) :=
          Finset.sum_le_sum fun a _ => (hF.2 a _ hlam).2
      _ = x * (gF L * n / 4) ^ (-(1 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; simp only [x]; ring
  have hle : x * (gF L * n / 4) ^ (-(5 / 2 : ℝ)) ≤ x * (gF L * n / 4) ^ (-(1 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hlam (by norm_num)) hx
  have hWU := norm_W_le_of sys hL H hKernel Hunit hPeriodic U hSU hTU hle
  rw [sqrt_three_tail hx hl0] at hWU
  have hY := norm_YQ_le (sys := sys) p₀ hL hn w
  have hc := cYQ_nonneg (sys := sys) p₀ hL
  have hYM : ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Sm eta L w))‖ ≤
      cYQ sys L p₀ * M / Real.sqrt n :=
    hY.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hF.1 hc) (Real.sqrt_nonneg _))
  refine (norm_inner_le_norm _ _).trans ?_
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  calc ‖Wp sys L H U‖ * ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Sm eta L w))‖
      ≤ finiteCoulombPhysicalMassConstant sys L Hunit *
          (Real.sqrt 3 * x * (gF L * n / 4) ^ (-(3 / 2 : ℝ))) * (cYQ sys L p₀ * M / Real.sqrt n) :=
        mul_le_mul hWU hYM (norm_nonneg _) (by positivity)
    _ = _ := by simp only [x]; ring

include hKernel hL in
/-- **`C₂`** (eq:chain-b): `‖Y 1_Q (W u)‖ ≤ #Ch (S Z_{2s} C_s)^{1/2} T_W M (K/4)^{(4s-1)/2}/√n`
for `s > 3/4`, `K = g n ≥ 4`. -/
theorem norm_YQW_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hK : 4 ≤ gF L * n) {s : ℝ} (hs : 3 / 4 < s) {M : ℝ} {w : MolecularFourierH2 eta}
    (hF : FGood sys L M w) :
    ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Wp sys L H w))‖ ≤
      Fintype.card (Ch eta) *
        Real.sqrt ((∑ j : Ch eta, (cY sys p₀ * chC sys L j) ^ 2 * (416 / 3)) *
          (1 + 26 * (1 + 1 / (2 * (2 * s) - 3))) *
            FSDatum.momentConst1 eta s ((eta : ℝ) / gF L ^ 2)) *
        (TW1 sys L Hunit * M) * (gF L * n / 4) ^ ((4 * s - 1) / 2) / Real.sqrt n := by
  have hM := hF.nonneg
  have hΛ : 1 ≤ gF L * n / 4 := by linarith
  have hΛ0 : 0 < gF L * n / 4 := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hW, htl⟩ := W_tails sys hL H hKernel Hunit hPeriodic hF
  have hT0 : 0 ≤ TW1 sys L Hunit * M := mul_nonneg (Real.sqrt_nonneg _) hM
  have hmom := moment_Q hL hΛ (Wp sys L H w) (r := s) (by linarith) hT0 hW htl
  have hG := norm_YQ_sq_le_s (sys := sys) p₀ hL hn hs (Wp sys L H w)
  set S := ∑ j : Ch eta, (cY sys p₀ * chC sys L j) ^ 2 * (416 / 3)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  set Z := (1 + 26 * (1 + 1 / (2 * (2 * s) - 3)) : ℝ)
  have hZ : 0 ≤ Z := by
    have : 0 < 2 * (2 * s) - 3 := by linarith
    positivity
  set mc := FSDatum.momentConst1 eta s ((eta : ℝ) / gF L ^ 2)
  have hmc : 0 ≤ mc := FSDatum.momentConst1_nonneg eta (by linarith) (by
    have := gF_pos hL; positivity)
  have hMY : MY sys L n p₀ = S / n := by
    unfold MY; simp only [S]; rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [hMY] at hG
  have hWs : ∑ p ∈ Qs eta n, Ws s p * ‖(Wp sys L H w : Cf eta → ℂ) p‖ ^ 2 =
      ∑ p ∈ Qs eta n, (1 + lsqC p) ^ (2 * s) * ‖(Wp sys L H w : Cf eta → ℂ) p‖ ^ 2 := rfl
  rw [hWs] at hG
  set T := TW1 sys L Hunit * M
  have hpow : ((gF L * n / 4) ^ ((4 * s - 1) / 2)) ^ 2 = (gF L * n / 4) ^ (4 * s - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le]; norm_num
  have hsq : ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Wp sys L H w))‖ ^ 2 ≤
      (Fintype.card (Ch eta) * Real.sqrt (S * Z * mc) * T * (gF L * n / 4) ^ ((4 * s - 1) / 2) /
        Real.sqrt n) ^ 2 := by
    refine hG.trans ?_
    rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hn0.le, hpow]
    have h1 := mul_le_mul_of_nonneg_left hmom
      (show 0 ≤ (Fintype.card (Ch eta) : ℝ) ^ 2 * (S / n) * Z by positivity)
    calc (Fintype.card (Ch eta) : ℝ) ^ 2 * (S / n) * Z *
          ∑ p ∈ Qs eta n, (1 + lsqC p) ^ (2 * s) * ‖(Wp sys L H w : Cf eta → ℂ) p‖ ^ 2
        ≤ (Fintype.card (Ch eta) : ℝ) ^ 2 * (S / n) * Z * (mc * T ^ 2 *
            (gF L * n / 4) ^ (4 * s - 1)) := h1
      _ = _ := by rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  have hR0 : 0 ≤ Fintype.card (Ch eta) * Real.sqrt (S * Z * mc) * T *
      (gF L * n / 4) ^ ((4 * s - 1) / 2) / Real.sqrt n := by
    have := Real.rpow_nonneg hΛ0.le ((4 * s - 1) / 2)
    positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR0 two_ne_zero).mp hsq

include hKernel in
/-- **The bulk block for a good state**: with `s = 3/4 + ε`, `0 < ε ≤ 1/4`,
`|Im ⟨W 1_Q u, Y 1_Q x⟩| ≤ (C_b Z_{2s}/(2n²)) c_L² (C (2M)² (K/4)^{4ε} + M²)`. -/
theorem bulk_good_le (hK : 4 ≤ gF L * n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) {M : ℝ}
    {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    |(⟪Wp sys L H (liftQ L n (Sm eta L w)),
        Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Sm eta L w))⟫_ℂ).im| ≤
      cBulk sys L p₀ / (2 * n ^ 2) * (1 + 26 * (1 + 1 / (2 * (2 * (3 / 4 + ε)) - 3))) *
        (cL sys L ^ 2 * (FSDatum.momentConst1 eta (1 / 4 + ε) ((eta : ℝ) / gF L ^ 2) * (2 * M) ^ 2 *
          (gF L * n / 4) ^ (4 * (1 / 4 + ε) - 1)) + cL sys L ^ 2 * M ^ 2) := by
  have hΛ : 1 ≤ gF L * n / 4 := by linarith
  have hb := bulk_im_le p₀ H hKernel hL hn (s := 3 / 4 + ε) (by linarith) (Sm eta L w)
  refine hb.trans ?_
  have h1 := nrm_b sys hL hΛ (r := 1 / 4 + ε) (by linarith) hF
  rw [show (1 / 4 + ε) + 1 = 3 / 4 + ε + 1 / 2 by ring] at h1
  have h2 : ∑ p ∈ Qs eta n, Ws (3 / 4 + ε) p * ‖Sm eta L w p‖ ^ 2 ≤ cL sys L ^ 2 * M ^ 2 := by
    calc ∑ p ∈ Qs eta n, Ws (3 / 4 + ε) p * ‖Sm eta L w p‖ ^ 2
        ≤ ∑ p ∈ Qs eta n, Ws 1 p * ‖Sm eta L w p‖ ^ 2 :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_right (Ws_mono (by linarith) p) (sq_nonneg _)
      _ ≤ cL sys L ^ 2 * (‖Sm eta L w‖ + ‖coulombFourierKineticH2 sys (gF L) w‖) ^ 2 :=
          sum_Ws_stateMap_le (sys := sys) hL n w
      _ ≤ cL sys L ^ 2 * M ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _))
            hF.1 2) (sq_nonneg _)
  have hcB : 0 ≤ cBulk sys L p₀ / (2 * n ^ 2) * (1 + 26 * (1 + 1 / (2 * (2 * (3 / 4 + ε)) - 3))) := by
    have hcD : 0 ≤ cDel sys L p₀ := by
      unfold cDel cE
      have := cgap_pos sys (gF_pos hL).ne'
      have := sys.mass_pos p₀
      have : 0 ≤ ∑ c : Fin eta, gF L ^ 2 / (2 * sys.mass c) :=
        Finset.sum_nonneg fun c _ => by have := sys.mass_pos c; positivity
      positivity
    have : 0 ≤ cBulk sys L p₀ := by
      unfold cBulk
      exact Finset.sum_nonneg fun j _ => by have := chC_nonneg sys hL j; positivity
    have : 0 < 2 * (2 * (3 / 4 + ε)) - 3 := by linarith
    positivity
  exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) hcB

/-- The phase constant: `2 (C_a + C_b + C_c)`. -/
noncomputable def phC (sys : CoulombSystem eta ν) (L Hunit : ℝ) (p₀ : Fin eta) (ε : ℝ) : ℝ :=
  2 * (cBulk sys L p₀ / 2 * (1 + 26 * (1 + 1 / (2 * (2 * (3 / 4 + ε)) - 3))) * cL sys L ^ 2 *
        (4 * FSDatum.momentConst1 eta (1 / 4 + ε) ((eta : ℝ) / gF L ^ 2) + 1) * gF L ^ 2 +
      8 * Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * eta * cYQ sys L p₀ *
        Real.sqrt (gF L) +
      eta * Fintype.card (Ch eta) *
        Real.sqrt ((∑ j : Ch eta, (cY sys p₀ * chC sys L j) ^ 2 * (416 / 3)) *
          (1 + 26 * (1 + 1 / (2 * (2 * (3 / 4 + ε)) - 3))) *
            FSDatum.momentConst1 eta (3 / 4 + ε) ((eta : ℝ) / gF L ^ 2)) *
        TW1 sys L Hunit * Real.sqrt (gF L))

set_option maxHeartbeats 1000000 in
include hKernel in
/-- **`prop:phase` for a good state**: for `0 < ε ≤ 1/4` and `K = g n ≥ 4`,
`|𝔚(w, w)| ≤ phC M² K^{-2+4ε}`. -/
theorem phase_state (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hK : 4 ≤ gF L * n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) {M : ℝ}
    {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    |(Wf sys hL hn p₀ H w w).re| ≤ phC sys L Hunit p₀ ε * M ^ 2 * (gF L * n) ^ (-2 + 4 * ε) := by
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hg := gF_pos hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hM := hF.nonneg
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  set x := Sm eta L w
  rw [Wf_re_eq sys hL H p₀ hn w, abs_mul, abs_neg, abs_two, inner_W_Y_split sys hL H p₀ hn w,
    Complex.add_im, Complex.add_im]
  -- the three pieces
  have ha := bulk_good_le sys hL H hKernel p₀ hn hK hε hε1 hF
  have hb := tail_C1_le sys hL H hKernel p₀ hn Hunit hPeriodic hK hF
  have hY := norm_YQW_le sys hL H hKernel p₀ hn Hunit hPeriodic hK (s := 3 / 4 + ε) (by linarith) hF
  have hR := fgood_R hF hL hK1
  have hc2 : ‖⟪Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Wp sys L H w)),
      x - molecularH2Truncate n x⟫_ℂ‖ ≤
      ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Wp sys L H w))‖ * (eta * M * K ^ (-(5 / 2 : ℝ))) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
  -- the powers of `K`
  have hsq : 1 / Real.sqrt n = Real.sqrt (gF L) * K ^ (-(1 / 2 : ℝ)) := by
    rw [rpow_neg_half_eq hK0, Real.sqrt_mul hg.le]
    field_simp
  have hn2 : 1 / (n : ℝ) ^ 2 = gF L ^ 2 * K ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hK0.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hKdef]
    field_simp
  have hK4 : ∀ r : ℝ, (K / 4) ^ r = (4 : ℝ) ^ (-r) * K ^ r := fun r => by
    rw [div_eq_mul_inv, Real.mul_rpow hK0.le (by norm_num), Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num)]
    ring
  have h43 : (4 : ℝ) ^ (-(-(3 / 2 : ℝ))) = 8 := by
    rw [neg_neg, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have hΛle : ∀ r : ℝ, 0 ≤ r → (K / 4) ^ r ≤ K ^ r := fun r hr =>
    Real.rpow_le_rpow (by linarith) (by linarith) hr
  have hp4 : 1 ≤ K ^ (4 * ε) := Real.one_le_rpow hK1 (by linarith)
  have hsplitK : K ^ (-2 + 4 * ε) = K ^ (-(2 : ℝ)) * K ^ (4 * ε) := by
    rw [← Real.rpow_add hK0]
  have hm2 : K ^ (-(2 : ℝ)) ≤ K ^ (-2 + 4 * ε) := Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
  have hm22 : K ^ (-2 + 2 * ε) ≤ K ^ (-2 + 4 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
  have hp2 := Real.rpow_nonneg hK0.le (-(2 : ℝ))
  have hpe := Real.rpow_nonneg hK0.le (4 * ε)
  -- (a)
  set Z := (1 + 26 * (1 + 1 / (2 * (2 * (3 / 4 + ε)) - 3)) : ℝ)
  have hZ : 0 ≤ Z := by
    have : 0 < 2 * (2 * (3 / 4 + ε)) - 3 := by linarith
    positivity
  set mcA := FSDatum.momentConst1 eta (1 / 4 + ε) ((eta : ℝ) / gF L ^ 2)
  have hmcA : 0 ≤ mcA := FSDatum.momentConst1_nonneg eta (by linarith) (by positivity)
  have hcBulk : 0 ≤ cBulk sys L p₀ := by
    unfold cBulk
    have hcD : 0 ≤ cDel sys L p₀ := by
      unfold cDel cE
      have := cgap_pos sys hg.ne'
      have := sys.mass_pos p₀
      have : 0 ≤ ∑ c : Fin eta, gF L ^ 2 / (2 * sys.mass c) :=
        Finset.sum_nonneg fun c _ => by have := sys.mass_pos c; positivity
      positivity
    exact Finset.sum_nonneg fun j _ => by have := chC_nonneg sys hL j; positivity
  have hcL := cL sys L
  set Ca := cBulk sys L p₀ / 2 * Z * cL sys L ^ 2 * (4 * mcA + 1) * gF L ^ 2
  have hA : |(⟪Wp sys L H (liftQ L n x), Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)⟫_ℂ).im| ≤
      Ca * M ^ 2 * K ^ (-2 + 4 * ε) := by
    refine ha.trans ?_
    have e4 : 4 * (1 / 4 + ε) - 1 = 4 * ε := by ring
    rw [e4]
    have hl := hΛle (4 * ε) (by linarith)
    have hX : cL sys L ^ 2 * (mcA * (2 * M) ^ 2 * (K / 4) ^ (4 * ε)) + cL sys L ^ 2 * M ^ 2 ≤
        cL sys L ^ 2 * M ^ 2 * (4 * mcA + 1) * K ^ (4 * ε) := by
      have h1 : mcA * (2 * M) ^ 2 * (K / 4) ^ (4 * ε) ≤ 4 * mcA * M ^ 2 * K ^ (4 * ε) := by
        have : mcA * (2 * M) ^ 2 = 4 * mcA * M ^ 2 := by ring
        rw [this]; exact mul_le_mul_of_nonneg_left hl (by positivity)
      have h2 : M ^ 2 ≤ M ^ 2 * K ^ (4 * ε) := le_mul_of_one_le_right (sq_nonneg _) hp4
      have := sq_nonneg (cL sys L)
      nlinarith
    calc cBulk sys L p₀ / (2 * n ^ 2) * Z *
          (cL sys L ^ 2 * (mcA * (2 * M) ^ 2 * (K / 4) ^ (4 * ε)) + cL sys L ^ 2 * M ^ 2)
        ≤ cBulk sys L p₀ / (2 * n ^ 2) * Z * (cL sys L ^ 2 * M ^ 2 * (4 * mcA + 1) * K ^ (4 * ε)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = cBulk sys L p₀ / 2 * Z * cL sys L ^ 2 * (4 * mcA + 1) * M ^ 2 * K ^ (4 * ε) *
            (1 / (n : ℝ) ^ 2) := by
          rw [div_eq_mul_inv (cBulk sys L p₀) (2 * (n : ℝ) ^ 2), mul_inv, one_div,
            div_eq_mul_inv (cBulk sys L p₀) 2]
          ring
      _ = Ca * M ^ 2 * K ^ (-2 + 4 * ε) := by
          rw [hn2, hsplitK]; simp only [Ca]; ring
  -- (b)
  set Cb := 8 * Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * eta * cYQ sys L p₀ *
    Real.sqrt (gF L)
  have hcYQ := cYQ_nonneg (sys := sys) p₀ hL
  have hB : ‖⟪Wp sys L H (w - liftQ L n x), Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)⟫_ℂ‖ ≤
      Cb * M ^ 2 * K ^ (-2 + 4 * ε) := by
    refine hb.trans ?_
    rw [hK4, h43]
    have e : Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * eta * M *
        (8 * K ^ (-(3 / 2 : ℝ))) * (cYQ sys L p₀ * M / Real.sqrt n) =
        Cb * M ^ 2 * (K ^ (-(3 / 2 : ℝ)) * K ^ (-(1 / 2 : ℝ))) := by
      rw [div_eq_mul_one_div _ (Real.sqrt n), hsq]; simp only [Cb]; ring
    rw [e, ← Real.rpow_add hK0, show -(3 / 2 : ℝ) + -(1 / 2) = -2 by norm_num]
    exact mul_le_mul_of_nonneg_left hm2 (by positivity)
  -- (c)
  set S := ∑ j : Ch eta, (cY sys p₀ * chC sys L j) ^ 2 * (416 / 3)
  set mcB := FSDatum.momentConst1 eta (3 / 4 + ε) ((eta : ℝ) / gF L ^ 2)
  set Cc := eta * Fintype.card (Ch eta) * Real.sqrt (S * Z * mcB) * TW1 sys L Hunit *
    Real.sqrt (gF L)
  have hTW := Real.sqrt_nonneg ((2 * sys.maxMass * CtW sys L Hunit 1) ^ 2 +
    3 * finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 * (1 + 2 * gF L))
  have hC : ‖⟪Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Wp sys L H w)),
      x - molecularH2Truncate n x⟫_ℂ‖ ≤ Cc * M ^ 2 * K ^ (-2 + 4 * ε) := by
    refine hc2.trans ?_
    have e1 : (4 * (3 / 4 + ε) - 1) / 2 = 1 + 2 * ε := by ring
    rw [e1] at hY
    have hl := hΛle (1 + 2 * ε) (by linarith)
    have hY' : ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Wp sys L H w))‖ ≤
        Fintype.card (Ch eta) * Real.sqrt (S * Z * mcB) * (TW1 sys L Hunit * M) *
          K ^ (1 + 2 * ε) * (Real.sqrt (gF L) * K ^ (-(1 / 2 : ℝ))) := by
      refine hY.trans ?_
      rw [div_eq_mul_one_div _ (Real.sqrt n), hsq]
      have : 0 ≤ Fintype.card (Ch eta) * Real.sqrt (S * Z * mcB) * (TW1 sys L Hunit * M) := by
        positivity
      have h0 := Real.rpow_nonneg hK0.le (-(1 / 2 : ℝ))
      gcongr
    have hR0 : 0 ≤ eta * M * K ^ (-(5 / 2 : ℝ)) := by positivity
    calc ‖Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Wp sys L H w))‖ * (eta * M * K ^ (-(5 / 2 : ℝ)))
        ≤ Fintype.card (Ch eta) * Real.sqrt (S * Z * mcB) * (TW1 sys L Hunit * M) *
            K ^ (1 + 2 * ε) * (Real.sqrt (gF L) * K ^ (-(1 / 2 : ℝ))) *
              (eta * M * K ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_right hY' hR0
      _ = Cc * M ^ 2 * (K ^ (1 + 2 * ε) * K ^ (-(1 / 2 : ℝ)) * K ^ (-(5 / 2 : ℝ))) := by
          simp only [Cc]; ring
      _ = Cc * M ^ 2 * K ^ (-2 + 2 * ε) := by
          rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]; ring_nf
      _ ≤ Cc * M ^ 2 * K ^ (-2 + 4 * ε) :=
          mul_le_mul_of_nonneg_left hm22 (by positivity)
  -- collect
  have hi2 := Complex.abs_im_le_norm
    ⟪Wp sys L H (w - liftQ L n x), Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)⟫_ℂ
  have hi3 := Complex.abs_im_le_norm ⟪Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Wp sys L H w)),
    x - molecularH2Truncate n x⟫_ℂ
  have hsum := abs_add_le
    ((⟪Wp sys L H (liftQ L n x), Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)⟫_ℂ).im +
      (⟪Wp sys L H (w - liftQ L n x), Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)⟫_ℂ).im)
    (⟪Yop sys hL hn p₀ (lpTruncate (Qs eta n) (Wp sys L H w)), x - molecularH2Truncate n x⟫_ℂ).im
  have hsum2 := abs_add_le
    (⟪Wp sys L H (liftQ L n x), Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)⟫_ℂ).im
    (⟪Wp sys L H (w - liftQ L n x), Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)⟫_ℂ).im
  have hfin : 2 * ((Ca + Cb + Cc) * M ^ 2 * K ^ (-2 + 4 * ε)) =
      phC sys L Hunit p₀ ε * M ^ 2 * K ^ (-2 + 4 * ε) := by
    unfold phC; simp only [Ca, Cb, Cc, Z, mcA, mcB, S]; ring
  rw [← hfin]
  linarith

end Phase

/-! ## `prop:phase` and `thm:flux2` -/

section Final

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta)

include hKernel in
/-- **`prop:phase`** (eq:phase): for `0 < ε ≤ 1/4` there is `C` with
`|⟨ψ(s), i[W, Y] ψ(s)⟩| ≤ C Ξ² K^{-2+4ε}` for every datum, every time and every cutoff `n ≥ 2`
with `K = g n ≥ 4`. -/
theorem thm_phase (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (hn : 2 ≤ n), 4 ≤ Kc L n → ∀ (D : EvoData L H) (s : ℝ),
      |(Wf sys hL hn p₀ H (traj H D s) (traj H D s)).re| ≤ C * D.Xi ^ 2 * Kc L n ^ (-2 + 4 * ε) := by
  have hc := cTr_nonneg sys hL Hunit
  refine ⟨|phC sys L Hunit p₀ ε| * cTr sys L Hunit ^ 2, by positivity, ?_⟩
  intro n hn hK D s
  rw [Kc_eq] at hK ⊢
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D s
  have hw : traj H D s = w := traj_eq H D s w hw1
  rw [hw]
  have h := phase_state sys hL H hKernel p₀ hn Hunit hPeriodic hK hε hε1 hF
  have hK0 : 0 < gF L * n := by linarith
  have hp := Real.rpow_nonneg hK0.le (-2 + 4 * ε)
  refine h.trans ?_
  calc phC sys L Hunit p₀ ε * (cTr sys L Hunit * D.Xi) ^ 2 * (gF L * n) ^ (-2 + 4 * ε)
      ≤ |phC sys L Hunit p₀ ε| * (cTr sys L Hunit * D.Xi) ^ 2 * (gF L * n) ^ (-2 + 4 * ε) := by
        gcongr; exact le_abs_self _
    _ = _ := by ring

include hKernel hL in
/-- **`thm:flux2`** (eq:flux2): for `0 < ε ≤ 1/4` there is `C` with
`|∫₀ᵗ (⟨ψ, G ψ⟩ - ⟨Pψ, G Pψ⟩)| ≤ C Ξ² (K^{-3} + t K^{-2+4ε})` for every datum, every `t ≥ 0` and
every cutoff `n ≥ 2` with `K = g n ≥ 4`. -/
theorem thm_flux2 (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 2 ≤ n → 4 ≤ Kc L n → ∀ (D : EvoData L H) {t : ℝ}, 0 ≤ t →
      |∫ s in (0 : ℝ)..t, ((Gf sys L H p₀ (traj H D s) (traj H D s)).re -
          (Gf sys L H p₀ (molecularH2Truncate n (traj H D s))
            (molecularH2Truncate n (traj H D s))).re)| ≤
        C * D.Xi ^ 2 * (Kc L n ^ (-(3 : ℝ)) + t * Kc L n ^ (-2 + 4 * ε)) := by
  obtain ⟨Cφ, hCφ, hph⟩ := thm_phase sys hL H hKernel p₀ Hunit hPeriodic hε hε1
  exact thm_flux2_of_phase sys hL H hKernel p₀ Hunit hPeriodic (by linarith) hCφ hph

end Final

end FSFlux
