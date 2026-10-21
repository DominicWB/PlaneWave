import PlaneWave.Source.Stopping3Conditional

/-!
# The first source round: `lem:phi`, `prop:src-decomp`, `prop:src1`, `thm:src1`

The first source round of `app:source`, for the bare observable `A_{p₀}`, by the direct route of
the readiness review (`scope/remaining/review_S1.md`): the coupling `V^{RP} = R W P` is paired with
the backward observable flow as `⟨ψ, R W P φ⟩ = ⟨δ, W φ⟩`, so `‖δ‖ = O(ΞK^{-5/2})`, Hardy and the
energy norm `‖ℰ^{1/2} φ‖ = O(ΞK^{1/2})` of `lem:phi` give `O(Ξ²K^{-2})` per unit time without the
elimination of the bulk-fed part.

* `bdatum`: the bare datum `A_{p₀} v` on `E_n`; its weighted moments from the tails of a good `v`
  (`wt_bdatum_sq_le_tails`), and **`phi_norms`** (`lem:phi`, eq:phi-norms for `ℰ^s`, `1/4 < s ≤ 1`,
  along the retained flow `e^{iH'τ}` of any bounded symmetric `ΔH`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal

namespace FSSrc1

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The bare datum and `lem:phi` -/

section Datum

variable (sys : CoulombSystem eta ν) (L : ℝ) {n : ℕ} (p₀ : Fin eta) (hL : 0 < L)

/-- **The bare datum `A_{p₀} v`** on `E_n` (the observable applied to a cube state). -/
noncomputable def bdatum (v : En eta n) : En eta n :=
  cfgMul (fun p => (Aproj sys L p₀ p : ℂ)) v

omit [Fintype ν] in
lemma bdatum_apply (v : En eta n) (p : Cfg eta n) :
    (bdatum sys L p₀ v).ofLp p = (Aproj sys L p₀ p : ℂ) * v.ofLp p := rfl

omit [Fintype ν] in
/-- Pointwise `|A_{p₀} v| ≤ |(1 + A) v|`. -/
lemma norm_bdatum_apply_le (v : En eta n) (p : Cfg eta n) :
    ‖(bdatum sys L p₀ v).ofLp p‖ ≤
      ‖(FSSpectral.wt (sb eta n) (Asym sys L n) 1 v).ofLp p‖ := by
  rw [bdatum_apply, FSNormal.wt_one_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Aproj_nonneg sys L p₀ p),
    Real.norm_of_nonneg (by linarith [FSGalerkin.Asym_nonneg sys L n p])]
  exact mul_le_mul_of_nonneg_right (by linarith [Aproj_le_Asym sys L p₀ p]) (norm_nonneg _)

omit [Fintype ν] in
/-- `‖A_{p₀} v‖ ≤ Θ(v)`. -/
lemma norm_bdatum_le (v : En eta n) :
    ‖bdatum sys L p₀ v‖ ≤ ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_En, norm_sq_En]
  exact Finset.sum_le_sum fun p _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_bdatum_apply_le sys L p₀ v p) 2

omit [Fintype ν] in
/-- `‖ℰ^r A_{p₀} v‖² ≤ Σ_p ((1 + A_p)^r)² |((1+A) v)_p|²`. -/
lemma wt_bdatum_sq_le (r : ℝ) (v : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) r (bdatum sys L p₀ v)‖ ^ 2 ≤
      ∑ p, ((1 + Asym sys L n p) ^ r) ^ 2 *
        ‖(FSSpectral.wt (sb eta n) (Asym sys L n) 1 v).ofLp p‖ ^ 2 := by
  rw [norm_sq_wt]
  exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_bdatum_apply_le sys L p₀ v p) 2) (sq_nonneg _)

/-- The momentum bound `Λ_n = (2 m_max A_max)^{1/2}` of the cube (`A ≤ A_max` on `E_n`). -/
noncomputable def LamN (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * mmax sys * Amax eta L n)

omit [Fintype ν] in
lemma LamN_eq (hL : 0 < L) :
    LamN sys L n = Real.sqrt (3 * eta * mmax sys) * (gF L * n) := by
  unfold LamN Amax
  have hg := gF_pos hL
  have e : 2 * mmax sys * (3 * eta * gF L ^ 2 * n ^ 2 / 2) =
      (3 * eta * mmax sys) * (gF L * n) ^ 2 := by ring
  rw [e, Real.sqrt_mul (by have := one_le_mmax sys; positivity), Real.sqrt_sq (by positivity)]

omit [Fintype ν] in
lemma one_le_LamN (hL : 0 < L) (heta : 0 < eta) (hK : 1 ≤ gF L * n) : 1 ≤ LamN sys L n := by
  rw [LamN_eq sys L hL]
  have h1 : (1 : ℝ) ≤ 3 * eta * mmax sys := by
    have := one_le_mmax sys
    have : (1 : ℝ) ≤ eta := by exact_mod_cast heta
    nlinarith
  have h2 : 1 ≤ Real.sqrt (3 * eta * mmax sys) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt h1
  nlinarith

include hL in
omit [Fintype ν] in
/-- **Weighted moments of the bare datum from the tails of a good state**: for `IsGood 1 M v` and
`r > 1/4`, `‖ℰ^r A_{p₀} v‖² ≤ C_r M² Λ_n^{4r-1}`. -/
theorem wt_bdatum_sq_le_tails {M : ℝ} {v : En eta n} (hv : IsGood sys L 1 M v) {r : ℝ}
    (hr : 1 / 4 < r) (hΛ : 1 ≤ LamN sys L n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) r (bdatum sys L p₀ v)‖ ^ 2 ≤
      FSDatum.momentConst1 eta r ((eta : ℝ) / 2) * M ^ 2 * LamN sys L n ^ (4 * r - 1) := by
  set y := FSSpectral.wt (sb eta n) (Asym sys L n) 1 v with hy
  have hM : 0 ≤ M := by have := hv.1; have := norm_nonneg v; have := norm_nonneg y; linarith
  have key := FSDatum.moment_le_of_tails1 (η := eta) (Asym sys L n)
    (fun a x => finitePlaneWaveKabs (2 * Real.pi / L) n (x a)) y.ofLp (cA := (eta : ℝ) / 2)
    (E₀ := Amax eta L n) (Λ := LamN sys L n) (T := M) (r := r)
    (by positivity) (fun x => FSGalerkin.Asym_nonneg sys L n x) hΛ hr hM
    (fun x R hR hx => Asym_le_of_kabs_le sys hL x R hR hx)
    (fun x hx a => kabs_le_of_Asym_le sys x hx a) ?_ ?_
  · refine (wt_bdatum_sq_le sys L p₀ r v).trans (le_of_eq_of_le ?_ key)
    refine Finset.sum_congr rfl fun p _ => ?_
    have h0 : 0 ≤ 1 + Asym sys L n p := by linarith [FSGalerkin.Asym_nonneg sys L n p]
    have e : ((1 + Asym sys L n p) ^ r) ^ 2 = (1 + Asym sys L n p) ^ (2 * r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; ring_nf
    rw [if_pos (Asym_le_Amax sys p), e]
  · rw [← norm_sq_En]
    have h1 := hv.1
    have : ‖y‖ ≤ M := by have := norm_nonneg v; linarith
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  · intro a l hl
    have hl0 : 0 < l := by linarith
    have hsq : ∑ x, (if l < finitePlaneWaveKabs (2 * Real.pi / L) n (x a) then ‖y.ofLp x‖ ^ 2
        else 0) = ‖regTail L a l y‖ ^ 2 := (norm_sq_regTail L a l y).symm
    rw [hsq, hy, ← wt_regTail sys a l v]
    have h := (hv.2 a l hl).2
    rw [one_mul] at h
    have h2 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (regTail L a l v)‖ ^ 2 ≤
        (M * l ^ (-(1 / 2 : ℝ))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    have e : (M * l ^ (-(1 / 2 : ℝ))) ^ 2 = M ^ 2 / l := by
      rw [mul_pow, ← Real.rpow_natCast (l ^ (-(1 / 2 : ℝ))), ← Real.rpow_mul hl0.le]
      norm_num [Real.rpow_neg_one, div_eq_mul_inv]
    rw [e] at h2
    exact h2

include hL in
/-- **`lem:phi`** (eq:phi-norms, bare observable): for a good `v` (`IsGood 1 M v`), every symmetric
`ΔH` with `‖ΔH‖ ≤ C_Δ`, every `τ` and `1/4 < s ≤ 1`, the backward observable flow
`φ = e^{iH'τ} A_{p₀} v` has `‖φ‖ ≤ M` and
`‖ℰ^s φ‖ ≤ C_fl(s) M (C_s Λ_n^{4s-1})^{1/2}` with `Λ_n = (3η m_max)^{1/2} K`; at `s = 1/2` this is
the energy norm `O(M K^{1/2})`, at `s = 1` the graph norm `O(M K^{3/2})`. -/
theorem phi_norms (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {M : ℝ} {v : En eta n} (hv : IsGood sys L 1 M v)
    (hΛ : 1 ≤ LamN sys L n) (τ : ℝ) {s : ℝ} (hs : 1 / 4 < s) (hs1 : s ≤ 1) :
    ‖retFlow sys L n hΔsym τ (bdatum sys L p₀ v)‖ ≤ M ∧
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) s (retFlow sys L n hΔsym τ (bdatum sys L p₀ v))‖ ≤
        CflS sys L Hunit CΔ s * (M * Real.sqrt (FSDatum.momentConst1 eta s ((eta : ℝ) / 2) *
          LamN sys L n ^ (4 * s - 1))) := by
  have hM : 0 ≤ M := by
    have := hv.1; have := norm_nonneg v
    have := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) 1 v); linarith
  refine ⟨?_, ?_⟩
  · rw [norm_retFlow]
    refine (norm_bdatum_le sys L p₀ v).trans ?_
    have := hv.1; have := norm_nonneg v; linarith
  · have h1 := retflow sys Hunit hL hPeriodic hΔsym hCΔ hΔb (s := s) ⟨by linarith, hs1⟩ τ
      (bdatum sys L p₀ v)
    have h2 := wt_bdatum_sq_le_tails sys L p₀ hL hv hs hΛ
    obtain ⟨X, hXd⟩ : ∃ X, X = FSDatum.momentConst1 eta s ((eta : ℝ) / 2) *
        LamN sys L n ^ (4 * s - 1) := ⟨_, rfl⟩
    have hX : 0 ≤ X := by
      rw [hXd]
      exact mul_nonneg (FSDatum.momentConst1_nonneg eta hs (by positivity))
        (Real.rpow_nonneg (by linarith) _)
    have h2' : ‖FSSpectral.wt (sb eta n) (Asym sys L n) s (bdatum sys L p₀ v)‖ ^ 2 ≤ M ^ 2 * X := by
      rw [hXd]; linarith
    rw [← hXd]
    have h3 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) s (bdatum sys L p₀ v)‖ ≤
        M * Real.sqrt X := by
      have hrhs : 0 ≤ M * Real.sqrt X := mul_nonneg hM (Real.sqrt_nonneg _)
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) hrhs two_ne_zero).mp ?_
      rw [mul_pow, Real.sq_sqrt hX]
      exact h2'
    refine h1.trans ?_
    have hfl := CflS_nonneg sys (L := L) Hunit hCΔ s
    unfold CflS at hfl ⊢
    exact mul_le_mul_of_nonneg_left h3 hfl

end Datum

/-! ## The observable on cube vectors and the exact decomposition (`prop:src-decomp`) -/

section Decomp

variable (sys : CoulombSystem eta ν) {L : ℝ} {n : ℕ} (p₀ : Fin eta)

omit [Fintype ν] in
lemma regSymbol_idx (v : Cfg eta n) :
    regSymbol sys (gF L) p₀ (finiteConfigLatticeIndex eta n v) = Aproj sys L p₀ v := by
  unfold regSymbol Aproj
  rw [kabs_eq_lattice, mul_pow, Real.sq_sqrt (latticeNormSq_nonneg _)]
  change 1 / 2 * (gF L ^ 2 * latticeNormSq (finitePlaneWaveLatticeIndex n (v p₀)) / sys.mass p₀) = _
  unfold gF
  have := sys.mass_pos p₀
  field_simp

omit [Fintype ν] in
/-- `A_{p₀}` on a cube lift: `μ (lift x) = emb (A_{p₀} x)`. -/
lemma h2_cubeLift (x : En eta n) :
    (regKin sys (gF L) p₀).h2 (cubeLift (gF L) n x) = emb eta n (bdatum sys L p₀ x) := by
  ext q
  rw [KinMult.h2_apply]
  have hc := congrArg (fun y : L2 eta => y q) (stateMap_cubeLift' (L := L) x)
  simp only [Sm, molecularH2StateMap_apply] at hc
  rw [hc]
  change (regSymbol sys (gF L) p₀ q : ℂ) * _ = _
  by_cases hq : q ∈ fourierConfigCube eta n
  · rcases Finset.mem_image.mp hq with ⟨p, _, rfl⟩
    simp only [emb, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply,
      finiteFourierLpEmbed_apply_index]
    rw [bdatum_apply, regSymbol_idx]
  · simp only [emb, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply]
    rw [finiteFourierLpEmbed_apply_not_mem_cube eta n _ q hq,
      finiteFourierLpEmbed_apply_not_mem_cube eta n _ q hq, mul_zero]

omit [Fintype ν] in
/-- The truncation of an `H²` state is the lift of its cube part. -/
lemma trunc_eq_cubeLift (w : MolecularFourierH2 eta) :
    molecularH2Truncate n w = cubeLift (gF L) n (ext eta n (Sm eta L w)) := by
  apply molecularH2StateMap_injective eta (gF L)
  change Sm eta L (molecularH2Truncate n w) = Sm eta L (cubeLift (gF L) n (ext eta n (Sm eta L w)))
  rw [stateMap_cubeLift', emb_ext, Sm, stateMap_truncate]

omit [Fintype ν] in
/-- **eq:src-decomp** (`prop:src-decomp`): with `a = P ψ` (`ψ = S w`), `δ = R ψ` and a cube state
`y`, `⟨ψ, A ψ⟩ - ⟨y, A y⟩ = ⟨δ, A δ⟩ + ⟨a - y, A a⟩ + conj ⟨a - y, A y⟩`. -/
theorem src_decomp (w : MolecularFourierH2 eta) (y : En eta n) :
    (((regKin sys (gF L) p₀).expect (Sm eta L w) - (regKin sys (gF L) p₀).expect (emb eta n y) :
        ℝ) : ℂ) =
      ((regKin sys (gF L) p₀).expect (Sm eta L (w - molecularH2Truncate n w)) : ℂ) +
        ⟪ext eta n (Sm eta L w) - y, bdatum sys L p₀ (ext eta n (Sm eta L w))⟫_ℂ +
        conj ⟪ext eta n (Sm eta L w) - y, bdatum sys L p₀ y⟫_ℂ := by
  set m := regKin sys (gF L) p₀
  set a := ext eta n (Sm eta L w)
  set A := cubeLift (gF L) n a
  set B := cubeLift (gF L) n y
  have ht := trunc_eq_cubeLift (L := L) (n := n) w
  have hE : m.expect (Sm eta L w) =
      m.expect (Sm eta L A) + m.expect (Sm eta L (w - molecularH2Truncate n w)) := by
    rw [m.expect_split n w]
    congr 2
    rw [ht]
  have hy : m.expect (emb eta n y) = m.expect (Sm eta L B) := by rw [stateMap_cubeLift']
  have e1 : ((m.expect (Sm eta L A) : ℝ) : ℂ) - ((m.expect (Sm eta L B) : ℝ) : ℂ) =
      ⟪Sm eta L A - Sm eta L B, m.h2 A⟫_ℂ + ⟪m.h2 B, Sm eta L A - Sm eta L B⟫_ℂ := by
    rw [← m.inner_stateMap_h2_self, ← m.inner_stateMap_h2_self, inner_sub_left, inner_sub_right,
      ← m.inner_stateMap_h2 B A, ← m.inner_stateMap_h2 B B]
    ring
  have hSA : Sm eta L A = emb eta n a := stateMap_cubeLift' a
  have hSB : Sm eta L B = emb eta n y := stateMap_cubeLift' y
  have hμA : m.h2 A = emb eta n (bdatum sys L p₀ a) := h2_cubeLift sys p₀ a
  have hμB : m.h2 B = emb eta n (bdatum sys L p₀ y) := h2_cubeLift sys p₀ y
  rw [hSA, hSB, hμA, hμB] at e1
  have e2 : ⟪emb eta n a - emb eta n y, emb eta n (bdatum sys L p₀ a)⟫_ℂ =
      ⟪a - y, bdatum sys L p₀ a⟫_ℂ := by
    rw [← map_sub]; exact inner_emb_emb n _ _
  have e3 : ⟪emb eta n (bdatum sys L p₀ y), emb eta n a - emb eta n y⟫_ℂ =
      conj ⟪a - y, bdatum sys L p₀ y⟫_ℂ := by
    rw [← map_sub, inner_emb_emb, inner_conj_symm]
  rw [hE, hy, hSA, hSB]
  push_cast
  linear_combination e1 + e2 + e3

omit [Fintype ν] in
/-- eq:src-decomp in absolute values. -/
theorem src_decomp_le (w : MolecularFourierH2 eta) (y : En eta n) :
    |(regKin sys (gF L) p₀).expect (Sm eta L w) - (regKin sys (gF L) p₀).expect (emb eta n y)| ≤
      (regKin sys (gF L) p₀).expect (Sm eta L (w - molecularH2Truncate n w)) +
        ‖⟪ext eta n (Sm eta L w) - y, bdatum sys L p₀ (ext eta n (Sm eta L w))⟫_ℂ‖ +
        ‖⟪ext eta n (Sm eta L w) - y, bdatum sys L p₀ y⟫_ℂ‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖) (src_decomp sys (L := L) p₀ w y)
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  rw [h]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans (add_le_add ?_ le_rfl)) (by rw [RCLike.norm_conj])
  rw [Complex.norm_real, Real.norm_of_nonneg ((regKin sys (gF L) p₀).expect_nonneg _)]

end Decomp

/-! ## The Galerkin defect and its Duhamel pairing (eq:src-pair) -/

section Defect

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (n : ℕ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- The cube part `a(t) = P ψ(t)` of the exact trajectory. -/
noncomputable def aP (D : EvoData L H) (t : ℝ) : En eta n := ext eta n (D.U t (Sm eta L D.u₀))

/-- `P H ψ(t)` on `E_n`. -/
noncomputable def gP (D : EvoData L H) (t : ℝ) : En eta n := ext eta n (D.U t (H D.u₀))

/-- The coupling `f(t) = P H ψ(t) - H_N a(t)`, which is `P W δ(t)` (`fP_eq`). -/
noncomputable def fP (D : EvoData L H) (t : ℝ) : En eta n :=
  gP n H D t - Hret sys L n 0 (aP n H D t)

omit [Fintype ν] in
lemma aP_zero (D : EvoData L H) : aP n H D 0 = ext eta n (Sm eta L D.u₀) := by
  unfold aP; rw [D.U0]

omit [Fintype ν] in
lemma aP_hasDerivAt (D : EvoData L H) (t : ℝ) :
    HasDerivAt (aP n H D) (-(Complex.I • gP n H D t)) t := by
  have hd := (((ext eta n).restrictScalars ℝ).hasFDerivAt
    (x := D.U t (Sm eta L D.u₀))).comp_hasDerivAt t (D.deriv t D.u₀)
  have e : ((ext eta n).restrictScalars ℝ) (-(Complex.I • D.U t (H D.u₀))) =
      -(Complex.I • gP n H D t) := by
    simp only [ContinuousLinearMap.coe_restrictScalars', map_neg, map_smul]
    rfl
  rw [← e]
  exact hd

lemma aP_deriv (D : EvoData L H) (t : ℝ) :
    HasDerivAt (aP n H D) (-(Complex.I • (Hret sys L n 0 (aP n H D t) + fP sys n H D t))) t := by
  have e : Hret sys L n 0 (aP n H D t) + fP sys n H D t = gP n H D t := by unfold fP; abel
  rw [e]
  exact aP_hasDerivAt n H D t

omit [Fintype ν] in
lemma continuous_aP (D : EvoData L H) : Continuous (aP n H D) :=
  (ext eta n).continuous.comp (D.cont _)

lemma continuous_fP (D : EvoData L H) : Continuous (fP sys n H D) := by
  unfold fP gP
  exact ((ext eta n).continuous.comp (D.cont _)).sub
    ((LinearMap.continuous_of_finiteDimensional _).comp (continuous_aP n H D))

include hKernel in
/-- **`f(t) = P W δ(t)`**: for the `H²` coordinate `w` of `ψ(t)`, `f(t) = P W (w - P w)`. -/
lemma fP_eq (D : EvoData L H) (t : ℝ) (w : MolecularFourierH2 eta)
    (hw1 : Sm eta L w = D.U t (Sm eta L D.u₀)) (hw2 : H w = D.U t (H D.u₀)) :
    fP sys n H D t = ext eta n (Wp sys L H (w - molecularH2Truncate n w)) := by
  have hext : ext eta n (H w) = finiteCoulombHamiltonian sys L n (ext eta n (Sm eta L w)) +
      ext eta n (Wp sys L H (w - molecularH2Truncate n w)) := extract_H_eq sys L H hKernel n w
  unfold fP gP aP
  rw [← hw2, ← hw1, hext]
  simp only [Hret, add_zero]
  abel

/-- **eq:src-pair** (`prop:src-decomp`): the Galerkin defect `η(t) = a(t) - ψ_N(t)` paired with any
`x` is `⟨η(t), x⟩ = i ∫₀ᵗ ⟨P W δ(s), e^{iH_N(t-s)} x⟩ ds` (with `+i`; the text has `-i`). -/
theorem src_pair (D : EvoData L H) (t : ℝ) (x : En eta n) :
    ⟪aP n H D t - retFlow sys L n (zero_isSymmetric (n := n)) (-t) (aP n H D 0), x⟫_ℂ =
      Complex.I * ∫ s in (0 : ℝ)..t,
        ⟪fP sys n H D s, retFlow sys L n (zero_isSymmetric (n := n)) (t - s) x⟫_ℂ := by
  have h := duhamel_weak_of sys (zero_isSymmetric (n := n)) (aP n H D) (fP sys n H D)
    (continuous_fP sys n H D) (aP_deriv sys n H D) t x
  rw [inner_sub_left, h]
  ring

include hKernel hL in
/-- Hardy for cube lifts in the energy norm: `‖W v‖ ≤ √2 C_m ‖ℰ^{1/2} v‖`. -/
lemma norm_W_cubeLift_half_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖Wp sys L H (cubeLift (gF L) n v)‖ ≤
      Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖ := by
  have h := potential_form_bound sys H hKernel Hunit hL hPeriodic (cubeLift (gF L) n v)
  rw [stateMap_cubeLift'] at h
  have h2 : ∑' q, (1 + 2 * Ek sys L q) * ‖emb eta n v q‖ ^ 2 ≤
      2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖ ^ 2 := by
    rw [form_emb, norm_sq_wt_half, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have h0 := FSGalerkin.Asym_nonneg sys L n p
    nlinarith [sq_nonneg ‖v.ofLp p‖]
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have h3 : ‖Wp sys L H (cubeLift (gF L) n v)‖ ^ 2 ≤ (Real.sqrt 2 *
      finiteCoulombPhysicalMassConstant sys L Hunit *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    calc _ ≤ _ := h
      _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          (2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

end Defect

/-! ## `prop:src1` and `thm:src1` -/

section Consts

variable (sys : CoulombSystem eta ν) (L Hunit : ℝ)

/-- The pairing constant `c_P = η c_tr √2 C_m C_fl(1/2) (C_{1/2} (3η m_max)^{1/2})^{1/2}`. -/
noncomputable def cP : ℝ :=
  eta * cTr sys L Hunit * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit) *
    CflS sys L Hunit 0 (1 / 2) *
    Real.sqrt (FSDatum.momentConst1 eta (1 / 2) ((eta : ℝ) / 2) * Real.sqrt (3 * eta * mmax sys))

/-- A cutoff-independent budget of the Galerkin trajectory (`mN ≤ mNu` for `K ≥ 1`). -/
noncomputable def mNu : ℝ :=
  2 * (Cfl sys L Hunit 0 * (2 * cTr sys L Hunit)) + (2 * sys.maxMass + 1) *
    (2 * sys.maxMass * (Cfl sys L Hunit 0 * cvT sys L Hunit) +
      Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit *
        Real.sqrt (1 + Real.sqrt 3) +
      (CtW sys L Hunit (3 * sys.maxMass * (Cfl sys L Hunit 0 * (2 * cTr sys L Hunit))) +
        Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) *
          (Cfl sys L Hunit 0 * (2 * cTr sys L Hunit))))

variable {sys L}

lemma cP_nonneg (hL : 0 < L) : 0 ≤ cP sys L Hunit := by
  unfold cP
  have := cTr_nonneg sys hL Hunit
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have := CflS_nonneg sys (L := L) Hunit le_rfl (1 / 2)
  positivity

/-- `K^{-3/2} (1 + √3 K)^{1/2} ≤ (1 + √3)^{1/2}` for `K ≥ 1`. -/
lemma rpow_mul_sqrt_le {K : ℝ} (hK : 1 ≤ K) :
    K ^ (-(3 / 2 : ℝ)) * Real.sqrt (1 + Real.sqrt 3 * K) ≤ Real.sqrt (1 + Real.sqrt 3) := by
  have hK0 : 0 < K := by linarith
  set x := K ^ (-(3 / 2 : ℝ)) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hK0.le _
  have hx2 : x ^ 2 = K ^ (-(3 : ℝ)) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; norm_num
  have h3 : K ^ (-(3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK (by norm_num)
  have h2 : K ^ (-(3 : ℝ)) * K ≤ 1 := by
    have e : K ^ (-(3 : ℝ)) * K = K ^ (-(2 : ℝ)) := by
      rw [show (-(2 : ℝ)) = -(3 : ℝ) + 1 by norm_num, Real.rpow_add hK0, Real.rpow_one]
    rw [e]; exact Real.rpow_le_one_of_one_le_of_nonpos hK (by norm_num)
  have hs3 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rw [← Real.sqrt_sq hx0, ← Real.sqrt_mul (sq_nonneg x)]
  refine Real.sqrt_le_sqrt ?_
  rw [hx2, mul_add, mul_one]
  nlinarith [mul_le_mul_of_nonneg_left h2 hs3]

/-- **The Galerkin budget is uniform in the cutoff**: `mN ≤ mNu` for `K ≥ 1`. -/
lemma mN_le_mNu (hL : 0 < L) {n : ℕ} (hK : 1 ≤ gF L * n) : mN sys L Hunit n ≤ mNu sys L Hunit := by
  unfold mN Mdec mNu omC
  have hm : 0 ≤ 2 * sys.maxMass + 1 := by have := sys.one_le_maxMass; linarith
  have hc : 0 ≤ Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit *
      cTr sys L Hunit := by
    have := cTr_nonneg sys hL Hunit
    have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
    positivity
  have key : (Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit *
      (gF L * n) ^ (-(3 / 2 : ℝ)) + 0) * Real.sqrt (1 + Real.sqrt 3 * (gF L * n)) ≤
      Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit *
        Real.sqrt (1 + Real.sqrt 3) := by
    rw [add_zero, mul_assoc]
    exact mul_le_mul_of_nonneg_left (rpow_mul_sqrt_le hK) hc
  gcongr

end Consts

section Main

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (n : ℕ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel hL in
/-- The pairing at one time: `|⟨P W δ(s), e^{iH_N τ} A_{p₀} v⟩| ≤ c_P Ξ M K^{-2}` for a good `v`. -/
lemma pair_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) (hK : 1 ≤ gF L * n) (D : EvoData L H) (s τ : ℝ) {M : ℝ} {v : En eta n}
    (hv : IsGood sys L 1 M v) :
    ‖⟪fP sys n H D s, retFlow sys L n (zero_isSymmetric (n := n)) τ (bdatum sys L p₀ v)⟫_ℂ‖ ≤
      cP sys L Hunit * D.Xi * M * (gF L * n) ^ (-(2 : ℝ)) := by
  have heta : 0 < eta := Fin.pos p₀
  have hΛ := one_le_LamN sys L hL heta hK
  have hK0 : 0 < gF L * n := by linarith
  set φ := retFlow sys L n (zero_isSymmetric (n := n)) τ (bdatum sys L p₀ v)
  obtain ⟨w, hw1, hw2, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D s
  rw [fP_eq sys n H hKernel D s w hw1 hw2]
  have hpair : ⟪ext eta n (Wp sys L H (w - molecularH2Truncate n w)), φ⟫_ℂ =
      ⟪Sm eta L (w - molecularH2Truncate n w), Wp sys L H (cubeLift (gF L) n φ)⟫_ℂ := by
    rw [inner_ext, emb_eq_stateMap L n φ]
    exact (potential_symm sys L H hKernel (w - molecularH2Truncate n w)
      (cubeLift (gF L) n φ)).symm
  rw [hpair]
  refine (norm_inner_le_norm _ _).trans ?_
  have hδ : ‖Sm eta L (w - molecularH2Truncate n w)‖ ≤
      eta * (cTr sys L Hunit * D.Xi) * (gF L * n) ^ (-(5 / 2 : ℝ)) := by
    rw [map_sub, Sm, stateMap_truncate]; exact fgood_R hF hL hK
  have hW := norm_W_cubeLift_half_le sys hL n H hKernel Hunit hPeriodic φ
  have hφ := (phi_norms sys L p₀ hL Hunit hPeriodic (zero_isSymmetric (n := n)) le_rfl
    (fun _ => by simp) hv hΛ τ (s := 1 / 2) (by norm_num) (by norm_num)).2
  have e4 : 4 * (1 / 2 : ℝ) - 1 = 1 := by norm_num
  rw [e4, Real.rpow_one, LamN_eq sys L hL] at hφ
  have hM : 0 ≤ M := by
    have := hv.1; have := norm_nonneg v
    have := norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) 1 v); linarith
  have hΞ := D.Xi_nonneg
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hfl := CflS_nonneg sys (L := L) Hunit le_rfl (1 / 2)
  have hc1 := FSDatum.momentConst1_nonneg eta (r := 1 / 2) (by norm_num) (by positivity : (0 : ℝ) ≤ eta / 2)
  have hct := cTr_nonneg sys hL Hunit
  -- the cutoff powers
  have hsq : Real.sqrt (FSDatum.momentConst1 eta (1 / 2) ((eta : ℝ) / 2) *
      (Real.sqrt (3 * eta * mmax sys) * (gF L * n))) =
      Real.sqrt (FSDatum.momentConst1 eta (1 / 2) ((eta : ℝ) / 2) * Real.sqrt (3 * eta * mmax sys)) *
        (gF L * n) ^ (1 / 2 : ℝ) := by
    rw [← mul_assoc, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (gF L * n)]
  have hpow : (gF L * n) ^ (-(5 / 2 : ℝ)) * (gF L * n) ^ (1 / 2 : ℝ) = (gF L * n) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hK0]; norm_num
  rw [hsq] at hφ
  calc ‖Sm eta L (w - molecularH2Truncate n w)‖ * ‖Wp sys L H (cubeLift (gF L) n φ)‖
      ≤ (eta * (cTr sys L Hunit * D.Xi) * (gF L * n) ^ (-(5 / 2 : ℝ))) *
          (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
            (CflS sys L Hunit 0 (1 / 2) * (M * (Real.sqrt (FSDatum.momentConst1 eta (1 / 2)
              ((eta : ℝ) / 2) * Real.sqrt (3 * eta * mmax sys)) * (gF L * n) ^ (1 / 2 : ℝ))))) := by
        refine mul_le_mul hδ (hW.trans (mul_le_mul_of_nonneg_left hφ (by positivity)))
          (norm_nonneg _) (by positivity)
    _ = cP sys L Hunit * D.Xi * M *
          ((gF L * n) ^ (-(5 / 2 : ℝ)) * (gF L * n) ^ (1 / 2 : ℝ)) := by unfold cP; ring
    _ = cP sys L Hunit * D.Xi * M * (gF L * n) ^ (-(2 : ℝ)) := by rw [hpow]

include hKernel hL in
/-- **`prop:src1`** (by the direct route): for a good cube state `v` (`IsGood 1 M v`) and `t ≥ 0`,
`|∫₀ᵗ ⟨ψ(s), V^{RP} e^{iH_N(t-s)} A_{p₀} v⟩ ds| ≤ t c_P Ξ M K^{-2}`. This is stronger than
eq:src1 (`C_ε Ξ² [K^{-7/2} + t K^{-2+ε}]`). -/
theorem prop_src1 (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) (hK : 1 ≤ gF L * n) (D : EvoData L H) {t : ℝ} (ht : 0 ≤ t) {M : ℝ}
    {v : En eta n} (hv : IsGood sys L 1 M v) :
    ‖∫ s in (0 : ℝ)..t, ⟪fP sys n H D s,
        retFlow sys L n (zero_isSymmetric (n := n)) (t - s) (bdatum sys L p₀ v)⟫_ℂ‖ ≤
      cP sys L Hunit * D.Xi * M * (gF L * n) ^ (-(2 : ℝ)) * t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => ⟪fP sys n H D s, retFlow sys L n (zero_isSymmetric (n := n)) (t - s)
      (bdatum sys L p₀ v)⟫_ℂ)
    (C := cP sys L Hunit * D.Xi * M * (gF L * n) ^ (-(2 : ℝ)))
    (fun s _ => pair_le sys hL n H hKernel Hunit hPeriodic p₀ hK D s (t - s) hv)
  rwa [sub_zero, abs_of_nonneg ht] at h

include hKernel hL in
/-- **`thm:src1`, explicit form**: for `K ≥ 1` and `t ≥ 0`,
`|⟨ψ(t), A_{p₀} ψ(t)⟩ - ⟨ψ_N(t), A_{p₀} ψ_N(t)⟩| ≤ (η c_tr Ξ)² K^{-3} + c_P Ξ (2 c_tr + m_N) Ξ K^{-2} t`. -/
theorem thm_src1_explicit (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) (hK : 1 ≤ gF L * n) (D : EvoData L H) {t : ℝ} (ht : 0 ≤ t) :
    |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
        (regKin sys (gF L) p₀).expect (emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-t)
          (ext eta n (Sm eta L D.u₀))))| ≤
      (eta * cTr sys L Hunit * D.Xi) ^ 2 * (gF L * n) ^ (-(3 : ℝ)) +
        cP sys L Hunit * D.Xi * ((2 * cTr sys L Hunit + mN sys L Hunit n) * D.Xi) *
          (gF L * n) ^ (-(2 : ℝ)) * t := by
  obtain ⟨w, hw1, hw2, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D t
  have hK0 : 0 < gF L * n := by linarith
  have hΞ := D.Xi_nonneg
  have hct := cTr_nonneg sys hL Hunit
  set y := retFlow sys L n (zero_isSymmetric (n := n)) (-t) (ext eta n (Sm eta L D.u₀)) with hy_def
  rw [← hw1]
  have hdec := src_decomp_le sys (L := L) p₀ w y
  have ha : ext eta n (Sm eta L w) = aP n H D t := by unfold aP; rw [hw1]
  have hy : y = retFlow sys L n (zero_isSymmetric (n := n)) (-t) (aP n H D 0) := by
    rw [aP_zero]
  rw [ha] at hdec
  -- the exterior term `⟨δ, A δ⟩ ≤ ‖R ψ‖ ‖R T ψ‖`
  have htail : (regKin sys (gF L) p₀).expect (Sm eta L (w - molecularH2Truncate n w)) ≤
      (eta * cTr sys L Hunit * D.Xi) ^ 2 * (gF L * n) ^ (-(3 : ℝ)) := by
    have h1 := (regKin sys (gF L) p₀).expect_tail_le n w
    have hR := fgood_R hF hL hK
    have hT : ‖coulombFourierKineticH2 sys (gF L) w -
        molecularH2Truncate n (coulombFourierKineticH2 sys (gF L) w)‖ ≤
        eta * (cTr sys L Hunit * D.Xi) * (gF L * n) ^ (-(1 / 2 : ℝ)) := by
      refine (PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) n _).trans ?_
      calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n) a (coulombFourierKineticH2 sys (gF L) w)‖
          ≤ ∑ _a : Fin eta, cTr sys L Hunit * D.Xi * (gF L * n) ^ (-(1 / 2 : ℝ)) :=
            Finset.sum_le_sum fun a _ => (hF.2 a _ hK).2
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hpow : (gF L * n) ^ (-(5 / 2 : ℝ)) * (gF L * n) ^ (-(1 / 2 : ℝ)) =
        (gF L * n) ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_add hK0]; norm_num
    calc _ ≤ _ := h1
      _ ≤ (eta * (cTr sys L Hunit * D.Xi) * (gF L * n) ^ (-(5 / 2 : ℝ))) *
          (eta * (cTr sys L Hunit * D.Xi) * (gF L * n) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul hR hT (norm_nonneg _) (by positivity)
      _ = (eta * cTr sys L Hunit * D.Xi) ^ 2 *
          ((gF L * n) ^ (-(5 / 2 : ℝ)) * (gF L * n) ^ (-(1 / 2 : ℝ))) := by ring
      _ = _ := by rw [hpow]
  -- the two pairings, by eq:src-pair and `prop:src1`
  have hga : IsGood sys L 1 (2 * (cTr sys L Hunit * D.Xi)) (aP n H D t) := by
    rw [← ha]; exact ext_good sys (n := n) hF
  have hgy : IsGood sys L 1 (mN sys L Hunit n * D.Xi) y :=
    psiN_good sys hL H hKernel Hunit hPeriodic hK D (-t)
  have hp1 : ‖⟪aP n H D t - y, bdatum sys L p₀ (aP n H D t)⟫_ℂ‖ ≤
      cP sys L Hunit * D.Xi * (2 * (cTr sys L Hunit * D.Xi)) * (gF L * n) ^ (-(2 : ℝ)) * t := by
    rw [hy, src_pair sys n H D t, norm_mul, Complex.norm_I, one_mul]
    exact prop_src1 sys hL n H hKernel Hunit hPeriodic p₀ hK D ht hga
  have hp2 : ‖⟪aP n H D t - y, bdatum sys L p₀ y⟫_ℂ‖ ≤
      cP sys L Hunit * D.Xi * (mN sys L Hunit n * D.Xi) * (gF L * n) ^ (-(2 : ℝ)) * t := by
    have e := src_pair sys n H D t (bdatum sys L p₀ y)
    rw [← hy] at e
    rw [e, norm_mul, Complex.norm_I, one_mul]
    exact prop_src1 sys hL n H hKernel Hunit hPeriodic p₀ hK D ht hgy
  calc _ ≤ _ := hdec
    _ ≤ (eta * cTr sys L Hunit * D.Xi) ^ 2 * (gF L * n) ^ (-(3 : ℝ)) +
        cP sys L Hunit * D.Xi * (2 * (cTr sys L Hunit * D.Xi)) * (gF L * n) ^ (-(2 : ℝ)) * t +
        cP sys L Hunit * D.Xi * (mN sys L Hunit n * D.Xi) * (gF L * n) ^ (-(2 : ℝ)) * t := by
      gcongr
    _ = _ := by ring

end Main

section Uniform

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel hL in
/-- **`thm:src1`**: there is `C`, depending on the system, the cell, `Hunit` and `p₀` only, such
that for every cutoff with `K ≥ 1`, every datum and every `t ≥ 0`,
`|⟨ψ(t), A_{p₀} ψ(t)⟩ - ⟨ψ_N(t), A_{p₀} ψ_N(t)⟩| ≤ C Ξ² (K^{-3} + t K^{-2})`. -/
theorem thm_src1 (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (p₀ : Fin eta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 1 ≤ Kc L n → ∀ (D : EvoData L H) (t : ℝ), 0 ≤ t →
      |(regKin sys (gF L) p₀).expect (D.U t (Sm eta L D.u₀)) -
          (regKin sys (gF L) p₀).expect (emb eta n (retFlow sys L n (zero_isSymmetric (n := n)) (-t)
            (ext eta n (Sm eta L D.u₀))))| ≤
        C * D.Xi ^ 2 * (Kc L n ^ (-(3 : ℝ)) + t * Kc L n ^ (-(2 : ℝ))) := by
  have hct := cTr_nonneg sys hL Hunit
  have hcP := cP_nonneg (sys := sys) Hunit hL
  have hmNu : 0 ≤ mNu sys L Hunit := by
    unfold mNu
    have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
    have := Cfl_nonneg sys (L := L) Hunit (le_refl (0 : ℝ))
    have := cvT_nonneg sys (L := L) Hunit
    have := sys.one_le_maxMass
    have := CtW_nonneg sys hL Hunit (M₂ := 3 * sys.maxMass * (Cfl sys L Hunit 0 * (2 * cTr sys L Hunit)))
      (by positivity)
    have := gF_pos hL
    positivity
  refine ⟨(eta * cTr sys L Hunit) ^ 2 + cP sys L Hunit * (2 * cTr sys L Hunit + mNu sys L Hunit),
    by positivity, fun n hK D t ht => ?_⟩
  rw [Kc_eq] at hK ⊢
  have h := thm_src1_explicit sys hL n H hKernel Hunit hPeriodic p₀ hK D ht
  have hmN := mN_le_mNu (sys := sys) Hunit hL hK
  have hΞ := D.Xi_nonneg
  have hK0 : 0 < gF L * n := by linarith
  have h3 := Real.rpow_nonneg hK0.le (-(3 : ℝ))
  have h2 := Real.rpow_nonneg hK0.le (-(2 : ℝ))
  refine h.trans ?_
  set k3 := (gF L * n) ^ (-(3 : ℝ))
  set k2 := (gF L * n) ^ (-(2 : ℝ))
  set X := D.Xi
  set a := (eta * cTr sys L Hunit) ^ 2
  set b := cP sys L Hunit * (2 * cTr sys L Hunit + mNu sys L Hunit)
  have hB : cP sys L Hunit * X * ((2 * cTr sys L Hunit + mN sys L Hunit n) * X) * k2 * t ≤
      b * (X ^ 2 * (t * k2)) := by
    have e : cP sys L Hunit * X * ((2 * cTr sys L Hunit + mN sys L Hunit n) * X) * k2 * t =
        cP sys L Hunit * (2 * cTr sys L Hunit + mN sys L Hunit n) * (X ^ 2 * (t * k2)) := by ring
    rw [e]
    have h1 : cP sys L Hunit * (2 * cTr sys L Hunit + mN sys L Hunit n) ≤ b :=
      mul_le_mul_of_nonneg_left (by linarith) hcP
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hA : (eta * cTr sys L Hunit * X) ^ 2 * k3 = a * X ^ 2 * k3 := by ring
  have e : (a + b) * X ^ 2 * (k3 + t * k2) =
      a * X ^ 2 * k3 + b * (X ^ 2 * (t * k2)) + (b * X ^ 2 * k3 + a * X ^ 2 * (t * k2)) := by ring
  rw [e]
  have hb0 : 0 ≤ b := by positivity
  have h0 : 0 ≤ b * X ^ 2 * k3 + a * X ^ 2 * (t * k2) := by positivity
  linarith

end Uniform

end FSSrc1
