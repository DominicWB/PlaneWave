import PlaneWave.Source.BulkGoodStates

/-!
# Flux/source build, block 5: the mixed class

`H₂^mix = P[Σ_b, V_nc]P = -P Z P - P[Σ_b, V_b]P` (`Z = W Σ_D + (W Σ_D)†`) on `E_n`, and its
generator.

* `FSKernel.matK`, `FSKernel.kop_matK`: every linear map on `ℂ^X` is the kernel operator of its
  matrix `κ(q, p) = (T e_p)_q`; `matK_conj_of_symm` for symmetric maps.
* `Hmix_cold`, `Hmix_hot` (the input split): on cold inputs (`v` supported in `Q`)
  `H₂^mix v = -(1 - Q) P W Σ_b v`; on hot inputs (`v` supported in `P \ Q`)
  `H₂^mix v = -P (W Σ_D)† v = P Σ_b W v`, which lands in `Q`.  Hence `H₂^mix` joins `Q` to `P \ Q`
  only (`hmixC_eq_zero`), and it is symmetric (`Hmix_symm`).
* `norm_Zw_emb_wt_le`: `‖W Σ_b v‖ ≤ C_m (#Ch² M₁ Z_{2s})^{1/2} c_E^s ‖(1+A)^s v‖` (`3/4 < s`,
  `M₁ ∝ n⁻³`), the weighted slice bound of `lem:slice` for the cold-to-hot orientation.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSKernel

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The matrix kernel `κ(q, p) = (T e_p)_q` of a linear map on `ℂ^X`. -/
noncomputable def matK (T : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X) (q p : X) : ℂ :=
  (T (EuclideanSpace.single p 1)).ofLp q

/-- **Every linear map on `ℂ^X` is the kernel operator of its matrix.** -/
theorem kop_matK (T : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X) : kop (matK T) = T := by
  refine (EuclideanSpace.basisFun X ℂ).toBasis.ext fun p => ?_
  ext q
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, kop_apply]
  rw [Finset.sum_eq_single p]
  · rw [PiLp.ofLp_single, Pi.single_eq_same, one_mul]; rfl
  · intro r _ hr
    rw [PiLp.ofLp_single, Pi.single_eq_of_ne hr, zero_mul]
  · intro h; exact absurd (Finset.mem_univ p) h

omit [Fintype X] in
lemma matK_apply (T : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X) (q p : X) :
    matK T q p = (T (EuclideanSpace.single p 1)).ofLp q := rfl

/-- A symmetric map has a Hermitian matrix. -/
theorem matK_conj_of_symm {T : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X} (hT : T.IsSymmetric)
    (q p : X) : matK T p q = conj (matK T q p) := by
  have h1 : matK T p q = ⟪EuclideanSpace.single p (1 : ℂ), T (EuclideanSpace.single q 1)⟫_ℂ := by
    rw [EuclideanSpace.inner_single_left, map_one, one_mul]; rfl
  have h2 : matK T q p = ⟪EuclideanSpace.single q (1 : ℂ), T (EuclideanSpace.single p 1)⟫_ℂ := by
    rw [EuclideanSpace.inner_single_left, map_one, one_mul]; rfl
  rw [h1, h2, ← hT, inner_conj_symm]

omit [DecidableEq X] in
/-- The Laplace bound with a column weight: `‖kop (divK d κ) (dg w u)‖ ≤ B/(a - b) ‖u‖` whenever
`‖kop κ (dg w u)‖ ≤ B ‖u‖` (cold-to-hot orientation). -/
theorem norm_divK_HL_wt_le (d : X → ℝ) (hd : ∀ q, 0 ≤ d q) {a b B : ℝ} (hb : 0 ≤ b) (hab : b < a)
    (hB0 : 0 ≤ B) (κ : X → X → ℂ) (hκ : ∀ q p, κ q p ≠ 0 → a ≤ d q ∧ d p ≤ b) (w : X → ℂ)
    (hB : ∀ u, ‖kop κ (dg w u)‖ ≤ B * ‖u‖) (u : EuclideanSpace ℂ X) :
    ‖kop (divK d κ) (dg w u)‖ ≤ B / (a - b) * ‖u‖ := by
  have e1 : kop (divK d κ) (dg w u) = kop (divK d fun q p => κ q p * w p) u := by
    have h := congrArg (fun T : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X => T u)
      (kop_dg w (divK d κ))
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    rw [h]
    have e : (fun q p => divK d κ q p * w p) = divK d fun q p => κ q p * w p := by
      funext q p; rw [divK_mul_right]
    rw [e]
  have e2 : ∀ u, kop (fun q p => κ q p * w p) u = kop κ (dg w u) := by
    intro u
    have h := congrArg (fun T : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X => T u) (kop_dg w κ)
    simp only [LinearMap.coe_comp, Function.comp_apply] at h
    exact h.symm
  rw [e1]
  refine norm_divK_HL_le d hd hb hab hB0 _ (fun q p h => hκ q p ?_) (fun u => ?_) u
  · intro h0; apply h; rw [h0, zero_mul]
  · rw [e2]; exact hB u

omit [Fintype X] [DecidableEq X] in
lemma divK_add (d : X → ℝ) (κ κ' : X → X → ℂ) :
    divK d (κ + κ') = divK d κ + divK d κ' := by
  classical
  funext q p
  simp only [divK, Pi.add_apply]
  split_ifs
  · rw [add_zero]
  · rw [add_div]

omit [Fintype X] [DecidableEq X] in
/-- Division of a Hermitian kernel by a real mismatch gives a skew-Hermitian kernel. -/
lemma divK_skew (d : X → ℝ) (κ : X → X → ℂ) (hκ : ∀ q p, κ p q = conj (κ q p)) (q p : X) :
    divK d κ p q = -conj (divK d κ q p) := by
  classical
  unfold divK
  by_cases h : d q = d p
  · rw [if_pos h.symm, if_pos h]; simp
  · rw [if_neg (Ne.symm h), if_neg h, hκ q p, map_div₀, Complex.conj_ofReal,
      ← div_neg, ← Complex.ofReal_neg, neg_sub]

omit [Fintype X] [DecidableEq X] in
/-- Conjugating the transposed quotient: if `κ(p, q) = conj κ'(q, p)` then
`conj (divK d κ p q) = -divK d κ' q p`. -/
lemma divK_conj_swap (d : X → ℝ) (κ κ' : X → X → ℂ) (h : ∀ q p, κ p q = conj (κ' q p)) (q p : X) :
    conj (divK d κ p q) = -divK d κ' q p := by
  classical
  unfold divK
  by_cases hqp : d q = d p
  · rw [if_pos hqp.symm, if_pos hqp]; simp
  · rw [if_neg (Ne.symm hqp), if_neg hqp, map_div₀, h q p, Complex.conj_conj, Complex.conj_ofReal,
      ← div_neg, ← Complex.ofReal_neg, neg_sub]

omit [DecidableEq X] in
/-- A vector supported in `P` pairs only with the `P`-part. -/
lemma inner_eq_inner_res (P : X → Prop) (x φ : EuclideanSpace ℂ X)
    (hx : ∀ q, ¬ P q → x.ofLp q = 0) : ⟪x, φ⟫_ℂ = ⟪x, res P φ⟫_ℂ := by
  classical
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [res_apply]
  split_ifs with hq
  · rfl
  · simp [hx q hq]

omit [DecidableEq X] in
/-- Restrictions are self-adjoint. -/
lemma inner_res_left (P : X → Prop) (x y : EuclideanSpace ℂ X) :
    ⟪res P x, y⟫_ℂ = ⟪x, res P y⟫_ℂ := by
  classical
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, res_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs <;> simp

omit [Fintype X] [DecidableEq X] in
lemma res_res_of (P : X → Prop) (x : EuclideanSpace ℂ X) (hx : ∀ q, ¬ P q → x.ofLp q = 0) :
    res P x = x := by
  classical
  ext q
  rw [res_apply]
  split_ifs with hq
  · rfl
  · rw [hx q hq]

end FSKernel

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Supports of cube vectors -/

/-- A cube configuration is *cold* if it lies in the bulk block `Q`. -/
abbrev IsCold (n : ℕ) (p : Cfg eta n) : Prop := InQ (n : ℝ) (finiteConfigLatticeIndex eta n p)

omit [Fintype ν] in
lemma emb_apply_index (n : ℕ) (v : En eta n) (p : Cfg eta n) :
    emb eta n v (finiteConfigLatticeIndex eta n p) = v.ofLp p := by
  simp only [emb, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply,
    finiteFourierLpEmbed_apply_index]

omit [Fintype ν] in
lemma emb_apply_eq_zero (n : ℕ) (v : En eta n) {q : Cf eta}
    (h : ∀ p : Cfg eta n, finiteConfigLatticeIndex eta n p = q → v.ofLp p = 0) :
    emb eta n v q = 0 := by
  classical
  by_cases hq : q ∈ fourierConfigCube eta n
  · unfold fourierConfigCube at hq
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hq
    rw [emb_apply_index]; exact h p rfl
  · simp only [emb, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply]
    exact finiteFourierLpEmbed_apply_not_mem_cube eta n _ q hq

omit [Fintype ν] in
/-- A cold-supported cube vector is supported in `Q`. -/
lemma emb_cold_supp (n : ℕ) {v : En eta n} (hv : ∀ p, ¬ IsCold n p → v.ofLp p = 0) {q : Cf eta}
    (hq : ¬ InQ (n : ℝ) q) : emb eta n v q = 0 :=
  emb_apply_eq_zero n v fun p hp => hv p (by rw [IsCold, hp]; exact hq)

omit [Fintype ν] in
/-- A hot-supported cube vector vanishes on `Q` and outside `P`. -/
lemma emb_hot_supp (n : ℕ) {v : En eta n} (hv : ∀ p, IsCold n p → v.ofLp p = 0) {q : Cf eta}
    (hq : InQ (n : ℝ) q ∨ ¬ InP (n : ℝ) q) : emb eta n v q = 0 := by
  refine emb_apply_eq_zero n v fun p hp => ?_
  rcases hq with hq | hq
  · exact hv p (by rw [IsCold, hp]; exact hq)
  · exfalso; apply hq; rw [← hp]
    exact inP_of_mem_cube (finiteConfigLatticeIndex_mem_cube eta n p)

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)

/-- `Σ_b y` vanishes on `P \ Q`: a crossing has an end in `Q` and an end outside `P`. -/
lemma sig_apply_eq_zero_of_mid (y : L2 eta) {q : Cf eta} (hqP : InP (n : ℝ) q)
    (hqQ : ¬ InQ (n : ℝ) q) : Sig sys L n hL hn y q = 0 := by
  rw [Sig_apply]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  rw [sigK_eq_zero_of_not_cross (not_cross_of_inP_not_inQ hqP hqQ).1, zero_mul]

/-- For `x` supported in `Q`, `Σ_b x` vanishes on `P`. -/
lemma sig_apply_eq_zero_of_inP (x : L2 eta) (hx : ∀ p, ¬ InQ (n : ℝ) p → x p = 0) {q : Cf eta}
    (hq : InP (n : ℝ) q) : Sig sys L n hL hn x q = 0 := by
  rw [Sig_apply]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  unfold sigK
  split_ifs with hc
  · rcases hc with ⟨-, hp⟩ | ⟨hq', -⟩
    · rw [hx p (fun h => hp (h.inP (Nat.cast_nonneg n))), mul_zero]
    · exact absurd hq hq'
  · rw [zero_mul]

/-- For `x` supported in `P \ Q`, `Σ_b x = 0`. -/
lemma sig_eq_zero_of_mid (x : L2 eta) (hx : ∀ p, InQ (n : ℝ) p ∨ ¬ InP (n : ℝ) p → x p = 0) :
    Sig sys L n hL hn x = 0 := by
  ext q
  rw [Sig_apply, lp.coeFn_zero, Pi.zero_apply]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  unfold sigK
  split_ifs with hc
  · rcases hc with ⟨-, hp⟩ | ⟨-, hp⟩
    · rw [hx p (Or.inr hp), mul_zero]
    · rw [hx p (Or.inl hp), mul_zero]
  · rw [zero_mul]

/-- For `x` supported in `P \ Q`, `V_b x = 0`. -/
lemma Vb_eq_zero_of_mid (x : L2 eta) (hx : ∀ p, InQ (n : ℝ) p ∨ ¬ InP (n : ℝ) p → x p = 0) :
    Vb sys L n hL x = 0 := by
  ext q
  rw [Vb_apply, lp.coeFn_zero, Pi.zero_apply]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  unfold vbK
  split_ifs with hc
  · rcases hc with ⟨-, hp⟩ | ⟨-, hp⟩
    · rw [hx p (Or.inr hp), mul_zero]
    · rw [hx p (Or.inl hp), mul_zero]
  · rw [zero_mul]

/-- `P Σ_b P y = 0` in cube coordinates: `ext (Σ_b (P y)) = 0`. -/
lemma ext_sig_trunc (y : L2 eta) :
    ext eta n (Sig sys L n hL hn (molecularH2Truncate n y)) = 0 := by
  have h := sig_interior sys hL hn (molecularH2Truncate n y)
  rw [truncate_truncate, sub_self, map_zero] at h
  rw [← extract_truncate n, h, map_zero]

/-! ## The mixed block -/

section Mixed

variable (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- **The mixed block** `H₂^mix = P[Σ_b, V_nc]P = -P Z P - P[Σ_b, V_b]P` on `E_n`. -/
noncomputable def Hmix : En eta n →L[ℂ] En eta n :=
  ext eta n ∘L (-(Zsym sys hL hn H) - FSConj.cm (Sig sys L n hL hn) (Vb sys L n hL)) ∘L emb eta n

lemma Hmix_apply (v : En eta n) :
    Hmix sys hL hn H v = -ext eta n (Zw sys hL hn H (emb eta n v)) -
      ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) (emb eta n v)) -
      ext eta n (Sig sys L n hL hn (Vb sys L n hL (emb eta n v))) +
      ext eta n (Vb sys L n hL (Sig sys L n hL hn (emb eta n v))) := by
  simp only [Hmix, Zsym, FSConj.cm, ContinuousLinearMap.comp_apply, sub_apply,
    neg_apply, add_apply, mul_apply_eq_comp, map_sub, map_neg, map_add]
  abel

open Classical in
omit [Fintype ν] in
include hL in
/-- On the cube, the hot projector `1 - Q` is the restriction to the hot configurations. -/
lemma hotProj_eq_res (y : En eta n) :
    hotProj L (Kc L n / 4) y = FSKernel.res (fun p => ¬ IsCold n p) y := by
  ext p
  rw [FSKernel.res_apply]
  unfold hotProj
  rw [cfgMul_apply]
  have hiff := inQ_idx_iff (L := L) hL p
  by_cases hp : IsCold n p
  · have h1 := hiff.mp hp
    rw [if_neg (by push Not; exact h1), if_neg (not_not.mpr hp), zero_mul]
  · have h1 : ∃ a, Kc L n / 4 < finitePlaneWaveKabs (2 * Real.pi / L) n (p a) := by
      by_contra hno; push Not at hno; exact hp (hiff.mpr hno)
    rw [if_pos h1, if_pos hp, one_mul]

open Classical in
include hKernel in
/-- **Cold inputs**: for `v` supported in `Q`, `H₂^mix v = -(1 - Q) P W Σ_b v`. -/
theorem Hmix_cold (v : En eta n) (hv : ∀ p, ¬ IsCold n p → v.ofLp p = 0) :
    Hmix sys hL hn H v = -hotProj L (Kc L n / 4) (ext eta n (Zw sys hL hn H (emb eta n v))) := by
  set x := emb eta n v with hxdef
  have hxQ : ∀ q, ¬ InQ (n : ℝ) q → x q = 0 := fun q hq => emb_cold_supp n hv hq
  -- `V_b Σ_b x = Q W Σ_b x`
  have hSP : ∀ p, InP (n : ℝ) p → Sm eta L (SigD sys L n hL (by omega) x) p = 0 := by
    intro p hp
    rw [stateMap_SigD hL hn]
    exact sig_apply_eq_zero_of_inP sys hL hn x hxQ hp
  have h1 : Vb sys L n hL (Sig sys L n hL hn x) = lpTruncate (Qs eta n) (Zw sys hL hn H x) := by
    have h := Vb_exterior sys hL H hKernel (SigD sys L n hL (by omega) x) hSP
    rw [stateMap_SigD hL hn] at h
    exact h
  -- the lift of `x`
  set u := liftQ L n x with hu
  have hSu : Sm eta L u = x := by
    rw [hu, stateMap_liftQ]
    ext q
    rw [lpTruncate_apply]
    split_ifs with hq
    · rfl
    · exact (hxQ q (fun h => hq (mem_Qs.mpr h))).symm
  -- `(W Σ_D)† x = -Σ_b W u`
  have h2 : ContinuousLinearMap.adjoint (Zw sys hL hn H) x = -Sig sys L n hL hn (Wp sys L H u) := by
    have h := congrArg (fun A : L2 eta →L[ℂ] L2 eta => A u) (sig_W sys hL hn H hKernel)
    simp only [mul_apply_eq_comp, neg_apply] at h
    rw [h, hSu, neg_neg]
  -- `V_b x = (1 - P) W u`
  have h3 : Vb sys L n hL x = Wp sys L H u - molecularH2Truncate n (Wp sys L H u) := by
    ext q
    rw [sub_truncate_apply]
    by_cases hqQ : InQ (n : ℝ) q
    · rw [if_pos (hqQ.inP (Nat.cast_nonneg n)), Vb_apply]
      refine (tsum_congr fun p => ?_).trans tsum_zero
      unfold vbK
      split_ifs with hc
      · rw [hxQ p (fun h => not_inP_of_cross_inQ hc hqQ (h.inP (Nat.cast_nonneg n))), mul_zero]
      · rw [zero_mul]
    · rw [Vb_apply_out sys H hKernel hL n x hqQ]
  have h4 : ext eta n (Sig sys L n hL hn (Vb sys L n hL x)) =
      ext eta n (Sig sys L n hL hn (Wp sys L H u)) := by
    rw [h3, map_sub, map_sub, ext_sig_trunc sys hL hn, sub_zero]
  rw [Hmix_apply, ← hxdef, h4, h2, h1, map_neg, ← ext_sub_truncQ hL]
  abel

open Classical in
/-- **Hot inputs**: for `v` supported in `P \ Q`, `H₂^mix v = -P (W Σ_D)† v`. -/
theorem Hmix_hot (v : En eta n) (hv : ∀ p, IsCold n p → v.ofLp p = 0) :
    Hmix sys hL hn H v = -ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) (emb eta n v)) := by
  set x := emb eta n v with hxdef
  have hx : ∀ q, InQ (n : ℝ) q ∨ ¬ InP (n : ℝ) q → x q = 0 := fun q hq => emb_hot_supp n hv hq
  have hS : Sig sys L n hL hn x = 0 := sig_eq_zero_of_mid sys hL hn x hx
  have hV : Vb sys L n hL x = 0 := Vb_eq_zero_of_mid sys hL x hx
  have hZ : Zw sys hL hn H x = 0 := by
    have hD : SigD sys L n hL (by omega) x = 0 := by
      apply molecularH2StateMap_injective eta (gF L)
      change Sm eta L _ = Sm eta L _
      rw [stateMap_SigD hL hn, hS, map_zero]
    rw [Zw, ContinuousLinearMap.comp_apply, hD, map_zero]
  rw [Hmix_apply, ← hxdef, hZ, hV, hS]
  simp only [map_zero]
  abel

include hKernel in
/-- The output of a hot input is cold: `(H₂^mix v)_q = 0` for hot `q`. -/
lemma Hmix_hot_supp (v : En eta n) (hv : ∀ p, IsCold n p → v.ofLp p = 0) {q : Cfg eta n}
    (hq : ¬ IsCold n q) : (Hmix sys hL hn H v).ofLp q = 0 := by
  rw [Hmix_hot sys hL hn H v hv, PiLp.neg_apply, extractCLM_apply]
  have h := congrArg (fun A : L2 eta →L[ℂ] L2 eta => A (cubeLift (gF L) n v))
    (sig_W sys hL hn H hKernel)
  simp only [mul_apply_eq_comp, neg_apply] at h
  rw [stateMap_cubeLift'] at h
  rw [show ContinuousLinearMap.adjoint (Zw sys hL hn H) (emb eta n v) =
    -Sig sys L n hL hn (Wp sys L H (cubeLift (gF L) n v)) by rw [h, neg_neg]]
  rw [lp.coeFn_neg, Pi.neg_apply, neg_neg]
  exact sig_apply_eq_zero_of_mid sys hL hn _
    (inP_of_mem_cube (finiteConfigLatticeIndex_mem_cube eta n q)) hq

omit [Fintype ν] in
lemma emb_single (p : Cfg eta n) :
    emb eta n (EuclideanSpace.single p 1) = ev (finiteConfigLatticeIndex eta n p) := by
  rw [emb_eq_sum, Finset.sum_eq_single p]
  · rw [PiLp.ofLp_single, Pi.single_eq_same, one_smul]
  · intro r _ hr; rw [PiLp.ofLp_single, Pi.single_eq_of_ne hr, zero_smul]
  · intro h; exact absurd (Finset.mem_univ p) h

/-- The matrix of `H₂^mix`. -/
noncomputable def hmixC (q p : Cfg eta n) : ℂ :=
  FSKernel.matK (Hmix sys hL hn H : En eta n →ₗ[ℂ] En eta n) q p

omit [Fintype ν] in
lemma single_supp (p : Cfg eta n) {r : Cfg eta n} (hr : r ≠ p) :
    (EuclideanSpace.single p (1 : ℂ)).ofLp r = 0 := by
  rw [PiLp.ofLp_single, Pi.single_eq_of_ne hr]

/-- The matrix element `(W Σ_b e_p)(q)` between cube configurations. -/
noncomputable def zwE (q p : Cfg eta n) : ℂ :=
  Zw sys hL hn H (ev (finiteConfigLatticeIndex eta n p)) (finiteConfigLatticeIndex eta n q)

include hKernel in
lemma hmixC_cold_hot {p q : Cfg eta n} (hp : IsCold n p) (hq : ¬ IsCold n q) :
    hmixC sys hL hn H q p = -zwE sys hL hn H q p := by
  classical
  unfold hmixC zwE
  rw [FSKernel.matK_apply]
  change (Hmix sys hL hn H (EuclideanSpace.single p 1)).ofLp q = _
  rw [Hmix_cold sys hL hn H hKernel _ (fun r hr => single_supp p (fun h => hr (h ▸ hp))),
    PiLp.neg_apply, hotProj_eq_res hL, FSKernel.res_apply, if_pos hq, extractCLM_apply, emb_single]

include hKernel in
lemma hmixC_cold_cold {p q : Cfg eta n} (hp : IsCold n p) (hq : IsCold n q) :
    hmixC sys hL hn H q p = 0 := by
  classical
  unfold hmixC
  rw [FSKernel.matK_apply]
  change (Hmix sys hL hn H (EuclideanSpace.single p 1)).ofLp q = _
  rw [Hmix_cold sys hL hn H hKernel _ (fun r hr => single_supp p (fun h => hr (h ▸ hp))),
    PiLp.neg_apply, hotProj_eq_res hL, FSKernel.res_apply, if_neg (not_not.mpr hq), neg_zero]

lemma hmixC_hot_cold {p : Cfg eta n} (hp : ¬ IsCold n p) (q : Cfg eta n) :
    hmixC sys hL hn H q p = -conj (zwE sys hL hn H p q) := by
  unfold hmixC zwE
  rw [FSKernel.matK_apply]
  change (Hmix sys hL hn H (EuclideanSpace.single p 1)).ofLp q = _
  rw [Hmix_hot sys hL hn H _ (fun r hr => single_supp p (fun h => hp (h ▸ hr))),
    PiLp.neg_apply, extractCLM_apply, emb_single, ← inner_ev_left,
    ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_ev_left]

include hKernel in
lemma hmixC_hot_hot {p q : Cfg eta n} (hp : ¬ IsCold n p) (hq : ¬ IsCold n q) :
    hmixC sys hL hn H q p = 0 := by
  unfold hmixC
  rw [FSKernel.matK_apply]
  exact Hmix_hot_supp sys hL hn H hKernel _ (fun r hr => single_supp p (fun h => hp (h ▸ hr))) hq

include hKernel in
/-- **`H₂^mix` joins `Q` to `P \ Q` only.** -/
lemma hmixC_eq_zero {p q : Cfg eta n} (h : IsCold n q ↔ IsCold n p) : hmixC sys hL hn H q p = 0 := by
  by_cases hp : IsCold n p
  · exact hmixC_cold_cold sys hL hn H hKernel hp (h.mpr hp)
  · exact hmixC_hot_hot sys hL hn H hKernel hp (fun hq => hp (h.mp hq))

include hKernel in
/-- **The matrix of `H₂^mix` is Hermitian.** -/
theorem hmixC_conj (q p : Cfg eta n) : hmixC sys hL hn H p q = conj (hmixC sys hL hn H q p) := by
  by_cases hp : IsCold n p <;> by_cases hq : IsCold n q
  · rw [hmixC_cold_cold sys hL hn H hKernel hp hq, hmixC_cold_cold sys hL hn H hKernel hq hp, map_zero]
  · rw [hmixC_cold_hot sys hL hn H hKernel hp hq, hmixC_hot_cold sys hL hn H hq p, map_neg]
  · rw [hmixC_hot_cold sys hL hn H hp q, hmixC_cold_hot sys hL hn H hKernel hq hp, map_neg,
      Complex.conj_conj]
  · rw [hmixC_hot_hot sys hL hn H hKernel hp hq, hmixC_hot_hot sys hL hn H hKernel hq hp, map_zero]

theorem Hmix_eq_kop : (Hmix sys hL hn H : En eta n →ₗ[ℂ] En eta n) = FSKernel.kop (hmixC sys hL hn H) :=
  (FSKernel.kop_matK _).symm

include hKernel in
/-- **`H₂^mix` is symmetric.** -/
theorem Hmix_symm : (Hmix sys hL hn H : En eta n →ₗ[ℂ] En eta n).IsSymmetric := by
  rw [Hmix_eq_kop]
  exact FSKernel.kop_symm _ fun q p => hmixC_conj sys hL hn H hKernel q p

/-! ## Bounds for `H₂^mix` -/

omit [Fintype ν] in
include hL in
/-- `Σ_{p ∈ Q} (1+|p|²)^{2s} |(emb v)_p|² ≤ (c_E^s)² ‖(1+A)^s v‖²`. -/
lemma sum_Ws_emb_le {s : ℝ} (hs0 : 0 ≤ s) (v : En eta n) :
    ∑ p ∈ Qs eta n, Ws s p * ‖emb eta n v p‖ ^ 2 ≤
      (cE sys L ^ s) ^ 2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ ^ 2 := by
  have hcE := one_le_cE sys (L := L)
  have hsub : Qs eta n ⊆ fourierConfigCube eta n := fun q hq =>
    (inP_iff_mem_cube n q).mp ((mem_Qs.mp hq).inP (Nat.cast_nonneg n))
  have h1 : ∑ p ∈ Qs eta n, Ws s p * ‖emb eta n v p‖ ^ 2 ≤
      ∑ p ∈ fourierConfigCube eta n, Ws s p * ‖emb eta n v p‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
      mul_nonneg (Ws_pos s p).le (sq_nonneg _)
  refine h1.trans ?_
  unfold fourierConfigCube
  rw [Finset.sum_image (fun p _ q _ h => finiteConfigLatticeIndex_injective eta n h), norm_sq_wt,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [emb_apply_index]
  have hle := one_add_lsqC_le sys hL (finiteConfigLatticeIndex eta n c)
  rw [← Asym_eq_Ek] at hle
  have hA0 := FSGalerkin.Asym_nonneg sys L n c
  have hl0 : 0 ≤ 1 + lsqC (finiteConfigLatticeIndex eta n c) := by
    linarith [lsqC_nonneg (finiteConfigLatticeIndex eta n c)]
  have hW' : Ws s (finiteConfigLatticeIndex eta n c) ≤
      (cE sys L ^ s) ^ 2 * ((1 + Asym sys L n c) ^ s) ^ 2 := by
    unfold Ws
    rw [← mul_pow, ← Real.mul_rpow (by linarith) (by linarith), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    rw [show (s * ((2 : ℕ) : ℝ)) = 2 * s by push_cast; ring]
    exact Real.rpow_le_rpow hl0 hle (by linarith)
  calc Ws s (finiteConfigLatticeIndex eta n c) * ‖v.ofLp c‖ ^ 2 ≤
        (cE sys L ^ s) ^ 2 * ((1 + Asym sys L n c) ^ s) ^ 2 * ‖v.ofLp c‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hW' (sq_nonneg _)
    _ = _ := by ring

/-- The constant of the weighted slice bound, `C_m (#Ch² M₁ Z_{2s})^{1/2} c_E^s`. -/
noncomputable def CZws (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  finiteCoulombPhysicalMassConstant sys L Hunit *
    Real.sqrt (Fintype.card (Ch eta) ^ 2 * M1 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3)))) *
      cE sys L ^ s

lemma CZws_nonneg (Hunit : ℝ) (s : ℝ) : 0 ≤ CZws sys L Hunit n s := by
  unfold CZws
  have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have := one_le_cE sys (L := L)
  have := Real.rpow_nonneg (show (0 : ℝ) ≤ cE sys L by linarith) s
  positivity

include hKernel in
/-- **The weighted slice bound** (`lem:slice`, cold-to-hot orientation):
`‖W Σ_b v‖ ≤ C_m (#Ch² M₁ Z_{2s})^{1/2} c_E^s ‖(1+A)^s v‖` for `3/4 < s`. -/
theorem norm_Zw_emb_wt_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {s : ℝ} (hs : 3 / 4 < s) (v : En eta n) :
    ‖Zw sys hL hn H (emb eta n v)‖ ≤ CZws sys L Hunit n s *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ := by
  set x := emb eta n v
  have hZ : Zw sys hL hn H x =
      Wp sys L H (SigD sys L n hL (by omega) (lpTruncate (Qs eta n) x)) := by
    rw [Zw, ContinuousLinearMap.comp_apply, SigD_emb sys hL hn v]
  rw [hZ]
  have hf := potential_form_bound sys H hKernel Hunit hL hPeriodic
    (SigD sys L n hL (by omega) (lpTruncate (Qs eta n) x))
  rw [show Sm eta L (SigD sys L n hL (by omega) (lpTruncate (Qs eta n) x)) =
    Sig sys L n hL hn (lpTruncate (Qs eta n) x) from stateMap_SigD hL hn _] at hf
  have hform := (form_sig_Q_state_le sys hL hn hs x).2
  have hW := sum_Ws_emb_le sys hL (by linarith : (0 : ℝ) ≤ s) v
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hM1 : 0 ≤ M1 sys L n := by
    rw [M1_eq sys (by omega)]; have := cM1_nonneg sys (L := L); positivity
  have hZs : 0 ≤ 1 + 26 * (1 + 1 / (2 * (2 * s) - 3)) := by
    have : 0 < 2 * (2 * s) - 3 := by linarith
    positivity
  have h2 : ‖Wp sys L H (SigD sys L n hL (by omega) (lpTruncate (Qs eta n) x))‖ ^ 2 ≤
      (CZws sys L Hunit n s * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖) ^ 2 := by
    unfold CZws
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    calc _ ≤ _ := hf
      _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          (Fintype.card (Ch eta) ^ 2 * M1 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3))) *
            ∑ p ∈ Qs eta n, Ws s p * ‖x p‖ ^ 2) := mul_le_mul_of_nonneg_left hform (sq_nonneg _)
      _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          (Fintype.card (Ch eta) ^ 2 * M1 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3))) *
            ((cE sys L ^ s) ^ 2 * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ ^ 2)) := by
          gcongr
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (CZws_nonneg sys Hunit s)
    (norm_nonneg _)) two_ne_zero).mp h2

/-- The operator bound `‖H₂^mix‖ ≤ 2 C_Z + 2 A_σ C_V`. -/
noncomputable def CHmix (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  2 * CZ sys L Hunit n + 2 * Asig sys L n * CV sys L Hunit n

include hL in
lemma CHmix_nonneg (Hunit : ℝ) : 0 ≤ CHmix sys L Hunit n := by
  unfold CHmix
  have := CZ_nonneg sys Hunit (L := L) (n := n)
  have := CV_nonneg sys Hunit (L := L) (n := n)
  have := Asig_nonneg (sys := sys) (n := n) hL
  positivity

include hKernel in
/-- **`‖H₂^mix v‖ ≤ (2 C_Z + 2 A_σ C_V) ‖v‖`**. -/
theorem norm_Hmix_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) : ‖Hmix sys hL hn H v‖ ≤ CHmix sys L Hunit n * ‖v‖ := by
  have hZ := norm_Zsym_le sys hL hn H Hunit hPeriodic hKernel
  have hc : ‖FSConj.cm (Sig sys L n hL hn) (Vb sys L n hL)‖ ≤
      2 * Asig sys L n * CV sys L Hunit n :=
    (norm_cm_le _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left (norm_Sig_le hL hn)
      (by norm_num)) (opNorm_Vb_le sys hL H hKernel Hunit hPeriodic) (norm_nonneg _)
      (by have := Asig_nonneg (sys := sys) (n := n) hL; positivity))
  have hop : ‖-(Zsym sys hL hn H) - FSConj.cm (Sig sys L n hL hn) (Vb sys L n hL)‖ ≤
      CHmix sys L Hunit n := by
    unfold CHmix
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg]; linarith
  calc ‖Hmix sys hL hn H v‖ ≤ ‖(-(Zsym sys hL hn H) - FSConj.cm (Sig sys L n hL hn)
        (Vb sys L n hL)) (emb eta n v)‖ := by
        simp only [Hmix, ContinuousLinearMap.comp_apply]; exact norm_ext_le _
    _ ≤ CHmix sys L Hunit n * ‖emb eta n v‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
    _ = CHmix sys L Hunit n * ‖v‖ := by rw [norm_emb]

/-! ## The energy split and the mixed generator `Σ₂^mix` -/

/-- **The mixed energy threshold** `e_H = g² n²/(64 m_top)`: hot configurations have
`A ≥ 2 e_H`, configurations with `A ≤ e_H` are cold. -/
noncomputable def eH (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  gF L ^ 2 * n ^ 2 / (64 * mtop sys)

omit [Fintype ν] in
include hL in
lemma eH_pos (hn0 : 0 < n) : 0 < eH sys L n := by
  unfold eH
  have := gF_pos hL
  have := one_le_mtop sys
  have : (0 : ℝ) < n := by exact_mod_cast hn0
  positivity

omit [Fintype ν] in
/-- **Hot configurations have `A ≥ 2 e_H`.** -/
lemma two_eH_le_of_hot {q : Cfg eta n} (hq : ¬ IsCold n q) : 2 * eH sys L n ≤ Asym sys L n q := by
  rw [Asym_eq_Ek]
  unfold IsCold InQ at hq
  push Not at hq
  obtain ⟨a, ha⟩ := hq
  set k := finiteConfigLatticeIndex eta n q
  have hma := mass_le_mtop sys a
  have hm := sys.mass_pos a
  have hmt := one_le_mtop sys
  have hterm : gF L ^ 2 / (2 * sys.mass a) * nsq (k a) ≤ Ek sys L k := by
    unfold Ek E
    exact Finset.single_le_sum (f := fun c => gF L ^ 2 / (2 * sys.mass c) * nsq (k c))
      (fun c _ => mul_nonneg (by have := sys.mass_pos c; positivity) (nsq_nonneg _))
      (Finset.mem_univ a)
  refine le_trans ?_ hterm
  unfold eH
  have hg := sq_nonneg (gF L)
  have h1 : gF L ^ 2 / (2 * mtop sys) ≤ gF L ^ 2 / (2 * sys.mass a) :=
    div_le_div_of_nonneg_left hg (by positivity) (by linarith)
  have h2 : ((n : ℝ) / 4) ^ 2 ≤ nsq (k a) := ha.le
  calc 2 * (gF L ^ 2 * n ^ 2 / (64 * mtop sys)) = gF L ^ 2 / (2 * mtop sys) * ((n : ℝ) / 4) ^ 2 := by
        field_simp; ring
    _ ≤ gF L ^ 2 / (2 * sys.mass a) * nsq (k a) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)

omit [Fintype ν] in
include hL in
lemma isCold_of_le_eH (hn0 : 0 < n) {q : Cfg eta n} (hq : Asym sys L n q ≤ eH sys L n) :
    IsCold n q := by
  by_contra h
  have h1 := two_eH_le_of_hot sys (L := L) h
  have h2 := eH_pos sys hL hn0
  linarith

open Classical in
/-- The cold-to-hot gapped kernel: inputs with `A ≤ e_H`. -/
noncomputable def kHL (q p : Cfg eta n) : ℂ :=
  if Asym sys L n p ≤ eH sys L n then hmixC sys hL hn H q p else 0

open Classical in
/-- The hot-to-cold gapped kernel: outputs with `A ≤ e_H`. -/
noncomputable def kLH (q p : Cfg eta n) : ℂ :=
  if Asym sys L n q ≤ eH sys L n then hmixC sys hL hn H q p else 0

open Classical in
/-- The resonant kernel: both ends with `A > e_H`. -/
noncomputable def kRes (q p : Cfg eta n) : ℂ :=
  if Asym sys L n q ≤ eH sys L n ∨ Asym sys L n p ≤ eH sys L n then 0 else hmixC sys hL hn H q p

include hKernel in
lemma hmixC_split (q p : Cfg eta n) :
    hmixC sys hL hn H q p = kHL sys hL hn H q p + kLH sys hL hn H q p + kRes sys hL hn H q p := by
  unfold kHL kLH kRes
  by_cases hp : Asym sys L n p ≤ eH sys L n <;> by_cases hq : Asym sys L n q ≤ eH sys L n
  · rw [if_pos hp, if_pos hq, if_pos (Or.inl hq),
      hmixC_cold_cold sys hL hn H hKernel (isCold_of_le_eH sys hL (by omega) hp)
        (isCold_of_le_eH sys hL (by omega) hq)]
    ring
  · rw [if_pos hp, if_neg hq, if_pos (Or.inr hp)]; ring
  · rw [if_neg hp, if_pos hq, if_pos (Or.inl hq)]; ring
  · rw [if_neg hp, if_neg hq, if_neg (by tauto)]; ring

include hKernel in
lemma kHL_supp {q p : Cfg eta n} (h : kHL sys hL hn H q p ≠ 0) :
    2 * eH sys L n ≤ Asym sys L n q ∧ Asym sys L n p ≤ eH sys L n := by
  unfold kHL at h
  split_ifs at h with hp
  · refine ⟨two_eH_le_of_hot sys fun hq => h ?_, hp⟩
    exact hmixC_cold_cold sys hL hn H hKernel (isCold_of_le_eH sys hL (by omega) hp) hq
  · exact absurd rfl h

include hKernel in
lemma kLH_supp {q p : Cfg eta n} (h : kLH sys hL hn H q p ≠ 0) :
    Asym sys L n q ≤ eH sys L n ∧ 2 * eH sys L n ≤ Asym sys L n p := by
  unfold kLH at h
  split_ifs at h with hq
  · refine ⟨hq, two_eH_le_of_hot sys fun hp => h ?_⟩
    exact hmixC_cold_cold sys hL hn H hKernel hp (isCold_of_le_eH sys hL (by omega) hq)
  · exact absurd rfl h

include hKernel in
lemma kHL_conj (q p : Cfg eta n) : kHL sys hL hn H p q = conj (kLH sys hL hn H q p) := by
  unfold kHL kLH
  split_ifs
  · exact hmixC_conj sys hL hn H hKernel q p
  · simp

include hKernel in
lemma kLH_conj (q p : Cfg eta n) : kLH sys hL hn H p q = conj (kHL sys hL hn H q p) := by
  unfold kHL kLH
  split_ifs
  · exact hmixC_conj sys hL hn H hKernel q p
  · simp

include hKernel in
lemma kRes_conj (q p : Cfg eta n) : kRes sys hL hn H p q = conj (kRes sys hL hn H q p) := by
  unfold kRes
  by_cases h : Asym sys L n q ≤ eH sys L n ∨ Asym sys L n p ≤ eH sys L n
  · rw [if_pos h, if_pos (Or.comm.mp h), map_zero]
  · rw [if_neg h, if_neg (fun h' => h (Or.comm.mp h'))]
    exact hmixC_conj sys hL hn H hKernel q p

/-- `H₂^{mix,gap}`, the gapped part of the mixed block. -/
noncomputable def HmixGap : En eta n →ₗ[ℂ] En eta n :=
  FSKernel.kop (kHL sys hL hn H + kLH sys hL hn H)

/-- `H₂^{mix,res}`, the resonant part (both ends with `A > e_H`). -/
noncomputable def HmixRes : En eta n →ₗ[ℂ] En eta n := FSKernel.kop (kRes sys hL hn H)

/-- **The mixed generator** `Σ₂^mix = H₂^{mix,gap}/ω`. -/
noncomputable def Sig2mix : En eta n →ₗ[ℂ] En eta n :=
  FSKernel.kop (FSKernel.divK (Asym sys L n) (kHL sys hL hn H + kLH sys hL hn H))

include hKernel in
theorem Hmix_split :
    (Hmix sys hL hn H : En eta n →ₗ[ℂ] En eta n) = HmixGap sys hL hn H + HmixRes sys hL hn H := by
  rw [Hmix_eq_kop, HmixGap, HmixRes, ← FSKernel.kop_add]
  congr 1
  funext q p
  simp only [Pi.add_apply]
  exact hmixC_split sys hL hn H hKernel q p

lemma Sig2mix_eq : Sig2mix sys hL hn H =
    FSKernel.kop (FSKernel.divK (Asym sys L n) (kHL sys hL hn H)) +
      FSKernel.kop (FSKernel.divK (Asym sys L n) (kLH sys hL hn H)) := by
  rw [Sig2mix, FSKernel.divK_add, FSKernel.kop_add]

include hKernel in
/-- **The homological equation** `[A, Σ₂^mix] = H₂^{mix,gap}`. -/
theorem comm_Sig2mix :
    FSKernel.dg (fun q => (Asym sys L n q : ℂ)) ∘ₗ Sig2mix sys hL hn H -
      Sig2mix sys hL hn H ∘ₗ FSKernel.dg (fun q => (Asym sys L n q : ℂ)) = HmixGap sys hL hn H := by
  unfold Sig2mix HmixGap
  apply FSKernel.comm_divK
  intro q p hqp
  rw [Pi.add_apply, Pi.add_apply]
  have h1 : kHL sys hL hn H q p = 0 := by
    by_contra h
    obtain ⟨h1, h2⟩ := kHL_supp sys hL hn H hKernel h
    have := eH_pos sys hL (show 0 < n by omega)
    linarith
  have h2 : kLH sys hL hn H q p = 0 := by
    by_contra h
    obtain ⟨h1, h2⟩ := kLH_supp sys hL hn H hKernel h
    have := eH_pos sys hL (show 0 < n by omega)
    linarith
  rw [h1, h2, add_zero]

include hKernel in
/-- **`Σ₂^mix` is skew-adjoint.** -/
theorem inner_Sig2mix (u v : En eta n) :
    ⟪Sig2mix sys hL hn H u, v⟫_ℂ = -⟪u, Sig2mix sys hL hn H v⟫_ℂ := by
  unfold Sig2mix
  refine FSKernel.kop_skew _ (fun q p => FSKernel.divK_skew _ _ (fun q p => ?_) q p) u v
  simp only [Pi.add_apply]
  rw [kHL_conj sys hL hn H hKernel q p, kLH_conj sys hL hn H hKernel q p, map_add, add_comm]

include hKernel in
theorem HmixGap_symm : (HmixGap sys hL hn H).IsSymmetric := by
  unfold HmixGap
  refine FSKernel.kop_symm _ fun q p => ?_
  simp only [Pi.add_apply]
  rw [kHL_conj sys hL hn H hKernel q p, kLH_conj sys hL hn H hKernel q p, map_add, add_comm]

include hKernel in
theorem HmixRes_symm : (HmixRes sys hL hn H).IsSymmetric :=
  FSKernel.kop_symm _ fun q p => kRes_conj sys hL hn H hKernel q p

/-! ## Bounds for `Σ₂^mix` -/

open Classical in
/-- The cold-to-hot gapped part acts on the low inputs: `kop k_HL u = H₂^mix (1{A ≤ e_H} u)`. -/
lemma kop_kHL (u : En eta n) :
    FSKernel.kop (kHL sys hL hn H) u =
      Hmix sys hL hn H (FSKernel.res (fun p => Asym sys L n p ≤ eH sys L n) u) := by
  have h : (Hmix sys hL hn H : En eta n →ₗ[ℂ] En eta n)
      (FSKernel.res (fun p => Asym sys L n p ≤ eH sys L n) u) =
      FSKernel.kop (hmixC sys hL hn H) (FSKernel.res (fun p => Asym sys L n p ≤ eH sys L n) u) := by
    rw [Hmix_eq_kop]
  change _ = (Hmix sys hL hn H : En eta n →ₗ[ℂ] En eta n) _
  rw [h]
  ext q
  simp only [FSKernel.kop_apply, FSKernel.res_apply, kHL]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

open Classical in
/-- The hot-to-cold gapped part has low outputs: `kop k_LH u = 1{A ≤ e_H} H₂^mix u`. -/
lemma kop_kLH (u : En eta n) :
    FSKernel.kop (kLH sys hL hn H) u =
      FSKernel.res (fun q => Asym sys L n q ≤ eH sys L n) (Hmix sys hL hn H u) := by
  have h : (Hmix sys hL hn H : En eta n →ₗ[ℂ] En eta n) u = FSKernel.kop (hmixC sys hL hn H) u := by
    rw [Hmix_eq_kop]
  ext q
  rw [FSKernel.res_apply]
  change _ = if _ then ((Hmix sys hL hn H : En eta n →ₗ[ℂ] En eta n) u).ofLp q else 0
  rw [h]
  simp only [FSKernel.kop_apply, kLH]
  split_ifs <;> simp

open Classical in
/-- The resonant part: `kop k_res u = 1{A > e_H} H₂^mix 1{A > e_H} u`. -/
lemma kop_kRes (u : En eta n) :
    FSKernel.kop (kRes sys hL hn H) u =
      FSKernel.res (fun q => ¬ Asym sys L n q ≤ eH sys L n)
        (Hmix sys hL hn H (FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) u)) := by
  have h : (Hmix sys hL hn H : En eta n →ₗ[ℂ] En eta n)
      (FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) u) =
      FSKernel.kop (hmixC sys hL hn H) (FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) u) := by
    rw [Hmix_eq_kop]
  ext q
  rw [FSKernel.res_apply]
  change _ = if _ then ((Hmix sys hL hn H : En eta n →ₗ[ℂ] En eta n) _).ofLp q else 0
  rw [h, FSKernel.kop_apply, FSKernel.kop_apply]
  by_cases hq : Asym sys L n q ≤ eH sys L n
  · rw [if_neg (not_not.mpr hq)]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [kRes, if_pos (Or.inl hq), mul_zero]
  · rw [if_pos hq]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [FSKernel.res_apply, kRes]
    by_cases hp : Asym sys L n p ≤ eH sys L n
    · rw [if_pos (Or.inr hp), if_neg (not_not.mpr hp), mul_zero, zero_mul]
    · rw [if_neg (by tauto), if_pos hp]

include hKernel in
lemma norm_kop_kHL_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (u : En eta n) : ‖FSKernel.kop (kHL sys hL hn H) u‖ ≤ CHmix sys L Hunit n * ‖u‖ := by
  rw [kop_kHL sys hL hn H]
  exact (norm_Hmix_le sys hL hn H hKernel Hunit hPeriodic _).trans
    (mul_le_mul_of_nonneg_left (FSKernel.norm_res_le _ _) (CHmix_nonneg sys hL Hunit))

include hKernel in
lemma norm_kop_kLH_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (u : En eta n) : ‖FSKernel.kop (kLH sys hL hn H) u‖ ≤ CHmix sys L Hunit n * ‖u‖ := by
  rw [kop_kLH sys hL hn H]
  exact (FSKernel.norm_res_le _ _).trans (norm_Hmix_le sys hL hn H hKernel Hunit hPeriodic _)

include hKernel in
/-- **The Laplace bound, cold-to-hot**: `‖Σ_HL u‖ ≤ ‖H₂^mix‖/e_H ‖u‖`. -/
theorem norm_SHL_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (u : En eta n) :
    ‖FSKernel.kop (FSKernel.divK (Asym sys L n) (kHL sys hL hn H)) u‖ ≤
      CHmix sys L Hunit n / eH sys L n * ‖u‖ := by
  have he := eH_pos sys hL (show 0 < n by omega)
  have h := FSKernel.norm_divK_HL_le (Asym sys L n) (fun q => Asym_nonneg (sys := sys) (L := L) q)
    (a := 2 * eH sys L n) (b := eH sys L n) he.le (by linarith) (CHmix_nonneg sys hL Hunit)
    (kHL sys hL hn H) (fun q p h => kHL_supp sys hL hn H hKernel h)
    (norm_kop_kHL_le sys hL hn H hKernel Hunit hPeriodic) u
  rwa [show 2 * eH sys L n - eH sys L n = eH sys L n by ring] at h

include hKernel in
/-- **The Laplace bound, hot-to-cold**: `‖Σ_LH u‖ ≤ ‖H₂^mix‖/e_H ‖u‖`. -/
theorem norm_SLH_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (u : En eta n) :
    ‖FSKernel.kop (FSKernel.divK (Asym sys L n) (kLH sys hL hn H)) u‖ ≤
      CHmix sys L Hunit n / eH sys L n * ‖u‖ := by
  have he := eH_pos sys hL (show 0 < n by omega)
  have h := FSKernel.norm_divK_LH_le (Asym sys L n) (fun q => Asym_nonneg (sys := sys) (L := L) q)
    (a := 2 * eH sys L n) (b := eH sys L n) he.le (by linarith) (CHmix_nonneg sys hL Hunit)
    (kLH sys hL hn H) (fun q p h => kLH_supp sys hL hn H hKernel h)
    (norm_kop_kLH_le sys hL hn H hKernel Hunit hPeriodic) u
  rwa [show 2 * eH sys L n - eH sys L n = eH sys L n by ring] at h

omit [Fintype ν] in
/-- The spectral weight is the diagonal `(1+A)^s`. -/
lemma wt_eq_dg (s : ℝ) (v : En eta n) :
    FSSpectral.wt (sb eta n) (Asym sys L n) s v =
      FSKernel.dg (fun q => (((1 + Asym sys L n q) ^ s : ℝ) : ℂ)) v := by
  ext q
  rw [FSKernel.dg_apply]
  unfold FSSpectral.wt
  rw [fc_sb_apply]

open Classical in
include hKernel in
/-- **The weighted Laplace bound** (eq:mixed-weighted, cold-to-hot):
`‖Σ_HL u‖ ≤ C_Zs/e_H ‖(1+A)^s u‖` with `C_Zs = O(K^{-3/2})`, so `‖Σ_HL E^{-s}‖ = O(K^{-7/2})`. -/
theorem norm_SHL_wt_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {s : ℝ} (hs : 3 / 4 < s) (u : En eta n) :
    ‖FSKernel.kop (FSKernel.divK (Asym sys L n) (kHL sys hL hn H)) u‖ ≤
      CZws sys L Hunit n s / eH sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s u‖ := by
  have he := eH_pos sys hL (show 0 < n by omega)
  set w : Cfg eta n → ℂ := fun q => (((1 + Asym sys L n q) ^ (-s) : ℝ) : ℂ) with hw
  have hpos : ∀ q, 0 < 1 + Asym sys L n q := fun q => by
    linarith [Asym_nonneg (sys := sys) (L := L) q]
  -- `u = dg w ((1+A)^s u)`
  have hu : u = FSKernel.dg w (FSSpectral.wt (sb eta n) (Asym sys L n) s u) := by
    ext q
    rw [FSKernel.dg_apply, wt_eq_dg, FSKernel.dg_apply, hw, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.rpow_add (hpos q), neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]
  have hB : ∀ x, ‖FSKernel.kop (kHL sys hL hn H) (FSKernel.dg w x)‖ ≤ CZws sys L Hunit n s * ‖x‖ := by
    intro x
    rw [kop_kHL sys hL hn H]
    set y := FSKernel.res (fun p => Asym sys L n p ≤ eH sys L n) (FSKernel.dg w x) with hy
    have hcold : ∀ p, ¬ IsCold n p → y.ofLp p = 0 := by
      intro p hp
      rw [hy, FSKernel.res_apply, if_neg (fun h => hp (isCold_of_le_eH sys hL (by omega) h))]
    rw [Hmix_cold sys hL hn H hKernel y hcold, norm_neg]
    have hwy : ‖FSSpectral.wt (sb eta n) (Asym sys L n) s y‖ ≤ ‖x‖ := by
      refine (FSKernel.norm_le_of_coord_le fun q => ?_).trans (le_of_eq rfl)
      rw [wt_eq_dg, FSKernel.dg_apply, hy, FSKernel.res_apply]
      split_ifs
      · rw [FSKernel.dg_apply, hw, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (hpos q),
          add_neg_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]
      · rw [mul_zero, norm_zero]; exact norm_nonneg _
    calc ‖hotProj L (Kc L n / 4) (ext eta n (Zw sys hL hn H (emb eta n y)))‖
        ≤ ‖ext eta n (Zw sys hL hn H (emb eta n y))‖ := norm_hotProj_le _ _ _
      _ ≤ ‖Zw sys hL hn H (emb eta n y)‖ := norm_ext_le _
      _ ≤ CZws sys L Hunit n s * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s y‖ :=
          norm_Zw_emb_wt_le sys hL hn H hKernel Hunit hPeriodic hs y
      _ ≤ CZws sys L Hunit n s * ‖x‖ :=
          mul_le_mul_of_nonneg_left hwy (CZws_nonneg sys Hunit s)
  have h := FSKernel.norm_divK_HL_wt_le (Asym sys L n) (fun q => Asym_nonneg (sys := sys) (L := L) q)
    (a := 2 * eH sys L n) (b := eH sys L n) he.le (by linarith) (CZws_nonneg sys Hunit s)
    (kHL sys hL hn H) (fun q p h => kHL_supp sys hL hn H hKernel h) w hB
    (FSSpectral.wt (sb eta n) (Asym sys L n) s u)
  rw [← hu, show 2 * eH sys L n - eH sys L n = eH sys L n by ring] at h
  exact h

include hKernel in
/-- The outputs of `Σ_HL` are hot. -/
lemma SHL_out (u : En eta n) {q : Cfg eta n} (hq : IsCold n q) :
    (FSKernel.kop (FSKernel.divK (Asym sys L n) (kHL sys hL hn H)) u).ofLp q = 0 := by
  rw [FSKernel.kop_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  have : FSKernel.divK (Asym sys L n) (kHL sys hL hn H) q p = 0 := by
    unfold FSKernel.divK
    split_ifs
    · rfl
    · have hk : kHL sys hL hn H q p = 0 := by
        by_contra h
        unfold kHL at h
        split_ifs at h with hp
        · exact h (hmixC_cold_cold sys hL hn H hKernel (isCold_of_le_eH sys hL (by omega) hp) hq)
        · exact h rfl
      rw [hk, zero_div]
  rw [this, mul_zero]

include hKernel in
lemma kLH_in {q p : Cfg eta n} (h : kLH sys hL hn H q p ≠ 0) : ¬ IsCold n p := by
  intro hp
  unfold kLH at h
  split_ifs at h with hq
  · exact h (hmixC_cold_cold sys hL hn H hKernel hp (isCold_of_le_eH sys hL (by omega) hq))
  · exact h rfl

open Classical in
include hKernel in
/-- The inputs of `Σ_LH` are hot. -/
lemma SLH_in (u : En eta n) :
    FSKernel.kop (FSKernel.divK (Asym sys L n) (kLH sys hL hn H)) u =
      FSKernel.kop (FSKernel.divK (Asym sys L n) (kLH sys hL hn H))
        (FSKernel.res (fun p => ¬ IsCold n p) u) := by
  refine FSKernel.kop_res_of_cols _ _ (fun q p h => ?_) u
  unfold FSKernel.divK at h
  split_ifs at h
  · exact absurd rfl h
  · exact kLH_in sys hL hn H hKernel (fun h0 => h (by rw [h0, zero_div]))

include hKernel in
/-- **The two orientations are adjoint**: `⟪Σ_LH y, φ⟫ = -⟪y, Σ_HL φ⟫`. -/
theorem inner_SLH (y φ : En eta n) :
    ⟪FSKernel.kop (FSKernel.divK (Asym sys L n) (kLH sys hL hn H)) y, φ⟫_ℂ =
      -⟪y, FSKernel.kop (FSKernel.divK (Asym sys L n) (kHL sys hL hn H)) φ⟫_ℂ := by
  rw [FSKernel.inner_kop, ← inner_neg_right]
  congr 1
  ext q
  simp only [FSKernel.kop_apply, PiLp.neg_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [FSKernel.divK_conj_swap (Asym sys L n) (kLH sys hL hn H) (kHL sys hL hn H)
    (fun q p => kLH_conj sys hL hn H hKernel q p) q p]
  ring

/-! ## Tails -/

omit [Fintype ν] in
/-- **Union bound**: `‖1{∃ a, |k_a| > l} u‖ ≤ Σ_a ‖1{|k_a| > l} u‖`. -/
lemma norm_hotProj_le_sum (l : ℝ) (u : En eta n) :
    ‖hotProj L l u‖ ≤ ∑ a, ‖regTail L a l u‖ := by
  classical
  have hcoord : ∀ q, ‖(hotProj L l u).ofLp q‖ ≤
      ‖(∑ a, FSKernel.absv (regTail L a l u)).ofLp q‖ := by
    intro q
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    simp only [FSKernel.absv_apply]
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun a _ => norm_nonneg _)]
    unfold hotProj
    rw [cfgMul_apply]
    split_ifs with h
    · obtain ⟨a, ha⟩ := h
      rw [one_mul]
      calc ‖u.ofLp q‖ = ‖(regTail L a l u).ofLp q‖ := by rw [regTail_apply, if_pos ha]
        _ ≤ ∑ a, ‖(regTail L a l u).ofLp q‖ :=
            Finset.single_le_sum (f := fun a => ‖(regTail L a l u).ofLp q‖)
              (fun a _ => norm_nonneg _) (Finset.mem_univ a)
    · rw [zero_mul, norm_zero]; exact Finset.sum_nonneg fun a _ => norm_nonneg _
  refine (FSKernel.norm_le_of_coord_le hcoord).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
  simp only [FSKernel.norm_absv]

omit [Fintype ν] in
include hL in
/-- `‖(1 - Q) u‖ ≤ Σ_a ‖1{|k_a| > K/4} u‖`. -/
lemma norm_res_hot_le_sum (u : En eta n) :
    ‖FSKernel.res (fun p => ¬ IsCold n p) u‖ ≤ ∑ a, ‖regTail L a (Kc L n / 4) u‖ := by
  rw [← hotProj_eq_res hL]; exact norm_hotProj_le_sum _ u

omit [Fintype ν] in
include hL in
/-- **The hot part of a good state**: `‖(1 - Q) u‖ ≤ η M (K/4)^{-5/2}`. -/
lemma norm_res_hot_good {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) (hK : 1 ≤ Kc L n / 4) :
    ‖FSKernel.res (fun p => ¬ IsCold n p) u‖ ≤ eta * (M * (Kc L n / 4) ^ (-(5 / 2 : ℝ))) := by
  refine (norm_res_hot_le_sum hL u).trans ?_
  calc ∑ a, ‖regTail L a (Kc L n / 4) u‖ ≤ ∑ _a : Fin eta, M * (Kc L n / 4) ^ (-(5 / 2 : ℝ)) :=
        Finset.sum_le_sum fun a _ => by simpa only [one_mul] using (hu.2 a _ hK).1
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The momentum scale `l_H = (2 e_H/η)^{1/2}` of the high-energy set `A > e_H`. -/
noncomputable def lH (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * eH sys L n / eta)

omit [Fintype ν] in
lemma eH_nonneg : 0 ≤ eH sys L n := by
  unfold eH; have := one_le_mtop sys; positivity

omit [Fintype ν] in
include hL in
/-- On `A > e_H` some register exceeds `l_H`. -/
lemma exists_kabs_of_high {q : Cfg eta n} (hq : ¬ Asym sys L n q ≤ eH sys L n) :
    ∃ a, lH sys L n < finitePlaneWaveKabs (2 * Real.pi / L) n (q a) := by
  by_contra hno
  push Not at hno
  have h := Asym_le_of_kabs_le sys hL q (lH sys L n) (Real.sqrt_nonneg _) hno
  have he := eH_nonneg sys (L := L) (n := n)
  have hl : (eta : ℝ) / 2 * lH sys L n ^ 2 ≤ eH sys L n := by
    unfold lH
    rw [Real.sq_sqrt (by positivity)]
    rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) eta) with h0 | h0
    · rw [← h0]; simp only [zero_div, zero_mul]; exact he
    · rw [show (eta : ℝ) / 2 * (2 * eH sys L n / eta) = eH sys L n by field_simp]
  exact hq (h.trans hl)

open Classical in
omit [Fintype ν] in
include hL in
/-- `‖1{A > e_H} u‖ ≤ Σ_a ‖1{|k_a| > l_H} u‖`. -/
lemma norm_res_high_le_sum (u : En eta n) :
    ‖FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) u‖ ≤
      ∑ a, ‖regTail L a (lH sys L n) u‖ := by
  refine le_trans (FSKernel.norm_le_of_coord_le fun q => ?_) (norm_hotProj_le_sum _ u)
  rw [FSKernel.res_apply]
  unfold hotProj
  rw [cfgMul_apply]
  by_cases h1 : Asym sys L n q ≤ eH sys L n
  · rw [if_neg (not_not.mpr h1), norm_zero]; exact norm_nonneg _
  · rw [if_pos h1, if_pos (exists_kabs_of_high sys hL h1), one_mul]

omit [Fintype ν] in
include hL in
/-- **The high-energy part of a good state**: `‖1{A > e_H} u‖ ≤ η M l_H^{-5/2}`. -/
lemma norm_res_high_good {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) (hl : 1 ≤ lH sys L n) :
    ‖FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) u‖ ≤
      eta * (M * lH sys L n ^ (-(5 / 2 : ℝ))) := by
  refine (norm_res_high_le_sum sys hL u).trans ?_
  calc ∑ a, ‖regTail L a (lH sys L n) u‖ ≤ ∑ _a : Fin eta, M * lH sys L n ^ (-(5 / 2 : ℝ)) :=
        Finset.sum_le_sum fun a _ => by simpa only [one_mul] using (hu.2 a _ hl).1
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

open Classical in
omit [Fintype ν] in
/-- `‖1{A > e} φ‖ ≤ (1 + e)^{-1/4} ‖(1+A)^{1/4} φ‖`. -/
lemma norm_res_high_le_wt {e : ℝ} (he : 0 ≤ e) (φ : En eta n) :
    ‖FSKernel.res (fun p => ¬ Asym sys L n p ≤ e) φ‖ ≤
      (1 + e) ^ (-(1 / 4 : ℝ)) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖ := by
  have he1 : 0 < 1 + e := by linarith
  have hc0 : 0 ≤ (1 + e) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg he1.le _
  have hy : ‖((((1 + e) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ)) •
      FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖ =
      (1 + e) ^ (-(1 / 4 : ℝ)) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) φ‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
  rw [← hy]
  refine FSKernel.norm_le_of_coord_le fun q => ?_
  rw [FSKernel.res_apply, PiLp.smul_apply, wt_eq_dg, FSKernel.dg_apply, smul_eq_mul, norm_mul,
    norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hc0]
  by_cases hq : Asym sys L n q ≤ e
  · rw [if_neg (not_not.mpr hq), norm_zero]; positivity
  · rw [if_pos hq]
    have hA := Asym_nonneg (sys := sys) (L := L) q
    have h1 : 0 < 1 + Asym sys L n q := by linarith
    rw [abs_of_nonneg (Real.rpow_nonneg h1.le _), ← mul_assoc]
    have key : 1 ≤ (1 + e) ^ (-(1 / 4 : ℝ)) * (1 + Asym sys L n q) ^ (1 / 4 : ℝ) := by
      rw [Real.rpow_neg he1.le, ← div_eq_inv_mul, one_le_div (Real.rpow_pos_of_pos he1 _)]
      push Not at hq
      exact Real.rpow_le_rpow he1.le (by linarith) (by norm_num)
    exact le_mul_of_one_le_left (norm_nonneg _) key

open Classical in
omit [Fintype ν] in
/-- Hot configurations are high: `‖(1 - Q) φ‖ ≤ ‖1{A > e_H} φ‖` when `e_H > 0`. -/
lemma norm_res_hot_le_high (he : 0 < eH sys L n) (φ : En eta n) :
    ‖FSKernel.res (fun p => ¬ IsCold n p) φ‖ ≤
      ‖FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) φ‖ := by
  refine FSKernel.norm_le_of_coord_le fun q => ?_
  rw [FSKernel.res_apply, FSKernel.res_apply]
  by_cases h1 : IsCold n q
  · rw [if_neg (not_not.mpr h1), norm_zero]; exact norm_nonneg _
  · have h2 : ¬ Asym sys L n q ≤ eH sys L n := by
      have := two_eH_le_of_hot sys (L := L) h1; intro h; linarith
    rw [if_pos h1, if_pos h2]

include hKernel in
/-- **`Σ₂^mix` on a general state**: the cold-to-hot part by the weighted Laplace bound, the
hot-to-cold part by the operator bound on the hot input. -/
theorem norm_Sig2mix_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {s : ℝ} (hs : 3 / 4 < s) (u : En eta n) :
    ‖Sig2mix sys hL hn H u‖ ≤
      CZws sys L Hunit n s / eH sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) s u‖ +
        CHmix sys L Hunit n / eH sys L n * ‖FSKernel.res (fun p => ¬ IsCold n p) u‖ := by
  rw [Sig2mix_eq, LinearMap.add_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_SHL_wt_le sys hL hn H hKernel Hunit hPeriodic hs u
  · rw [SLH_in sys hL hn H hKernel]
    exact norm_SLH_le sys hL hn H hKernel Hunit hPeriodic _

include hKernel in
/-- The operator bound `‖Σ₂^mix‖ ≤ 2 ‖H₂^mix‖/e_H`. -/
theorem norm_Sig2mix_op_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (u : En eta n) :
    ‖Sig2mix sys hL hn H u‖ ≤ 2 * (CHmix sys L Hunit n / eH sys L n) * ‖u‖ := by
  rw [Sig2mix_eq, LinearMap.add_apply]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_SHL_le sys hL hn H hKernel Hunit hPeriodic u
  have h2 := norm_SLH_le sys hL hn H hKernel Hunit hPeriodic u
  linarith

include hKernel in
/-- **The resonant mixed residual paired with a flow**:
`|⟪H₂^{mix,res} u, φ⟫| ≤ ‖H₂^mix‖ ‖1{A > e_H} u‖ ‖1{A > e_H} φ‖`. -/
theorem norm_inner_HmixRes_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (u φ : En eta n) :
    ‖⟪HmixRes sys hL hn H u, φ⟫_ℂ‖ ≤ CHmix sys L Hunit n *
      ‖FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) u‖ *
        ‖FSKernel.res (fun p => ¬ Asym sys L n p ≤ eH sys L n) φ‖ := by
  classical
  unfold HmixRes
  rw [kop_kRes sys hL hn H, FSKernel.inner_res_left]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact norm_Hmix_le sys hL hn H hKernel Hunit hPeriodic _

/-- The relative constant of `‖H₂^mix v‖ ≤ α_mix Θ(v)`. -/
noncomputable def alphaMix (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  2 * finiteCoulombPhysicalMassConstant sys L Hunit * a1c sys L n +
    2 * (Asig sys L n * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit)) +
      CV sys L Hunit n * (2 * a0c sys L n)

include hKernel in
/-- **`‖H₂^mix v‖ ≤ α_mix Θ(v)`**, `α_mix = O(K^{-1})`. -/
theorem norm_Hmix_wt_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖Hmix sys hL hn H v‖ ≤ alphaMix sys L Hunit n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  set Θ := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖
  have hZ := norm_Zw_emb_le sys hL hn H hKernel Hunit hPeriodic v
  have hZa := norm_Zw_adj_emb_le sys hL hn H hKernel Hunit hPeriodic v
  have hVb := norm_Vb_emb_le sys hL H hKernel Hunit hPeriodic v
  have hS := norm_sig_emb_le' sys hL hn v
  have hA := norm_Sig_le (sys := sys) hL hn
  have hA0 := Asig_nonneg (sys := sys) (n := n) hL
  have hCV := opNorm_Vb_le sys hL H hKernel Hunit hPeriodic (n := n)
  have hCV0 := CV_nonneg sys Hunit (L := L) (n := n)
  have k3 : ‖ext eta n (Sig sys L n hL hn (Vb sys L n hL (emb eta n v)))‖ ≤
      Asig sys L n * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * Θ) :=
    (norm_ext_le _).trans (((Sig sys L n hL hn).le_opNorm _).trans
      (mul_le_mul hA hVb (norm_nonneg _) hA0))
  have k4 : ‖ext eta n (Vb sys L n hL (Sig sys L n hL hn (emb eta n v)))‖ ≤
      CV sys L Hunit n * (2 * a0c sys L n * Θ) :=
    (norm_ext_le _).trans (((Vb sys L n hL).le_opNorm _).trans
      (mul_le_mul hCV hS (norm_nonneg _) hCV0))
  rw [Hmix_apply]
  calc _ ≤ ‖ext eta n (Zw sys hL hn H (emb eta n v))‖ +
        ‖ext eta n (ContinuousLinearMap.adjoint (Zw sys hL hn H) (emb eta n v))‖ +
        ‖ext eta n (Sig sys L n hL hn (Vb sys L n hL (emb eta n v)))‖ +
        ‖ext eta n (Vb sys L n hL (Sig sys L n hL hn (emb eta n v)))‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ le_rfl)) le_rfl)) le_rfl)
        rw [norm_neg]
    _ ≤ 2 * finiteCoulombPhysicalMassConstant sys L Hunit * a1c sys L n * Θ +
        Asig sys L n * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * Θ) +
        Asig sys L n * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * Θ) +
        CV sys L Hunit n * (2 * a0c sys L n * Θ) := by
        gcongr
        · exact (norm_ext_le _).trans hZ
        · exact (norm_ext_le _).trans hZa
    _ = alphaMix sys L Hunit n * Θ := by unfold alphaMix; ring

end Mixed

end FSNormal
