import PlaneWave.Source.GoodStatesBothSpaces

/-!
# Flux/source build, block 3f: the observable and the nonsecular terms

* the truncated observable `O = A_{p₀}^E` on `ℓ²` (`Ofull`, the diagonal multiplier with symbol
  `A_{p₀} 1{Q} 1{E ≤ E₀}`): self-adjoint, `‖O‖ ≤ E₀`, supported in `Q`, and `P O P = A_{p₀}^E`
  on the cube (`Ofull_emb`);
* the bulk generator on cube vectors: `Σ_b v = Σ_b Q v`, `P Σ_b v = 0`,
  `‖Σ_b v‖ ≤ a₀ (‖v‖ + ‖A v‖)`;
* **the nonsecular terms of eq:nf-assembly** with `Ũ = e^{Σ_b}`, `Ã = Ũ O Ũ*`:
  the `RR` term `|⟪r, Ã r⟫| ≤ E₀ (A_σ ‖r‖)²` (`T4_le`), the cross term
  `|⟪P ψ̃, Ã r⟫| ≤ (Θ(a) + 2 E₀ a₀ Θ(a)) A_σ ‖r‖` (`T5_le`), and the observable correction
  `|⟪χ, (P Ã P - O) χ⟫| ≤ 2 ‖P d‖ Θ(χ) + E₀ ‖P d‖²`, `‖P d‖ ≤ 2 A_σ a₀ Θ(χ)` (`T2_le`);
* **`lem:acorr`, vector bound**: `‖(P Ã P - O) w‖ ≤ (E₀ (1 + A_σ²) 2 A_σ a₀ + A_σ a₀ (1 + E₀)) 2Θ(w)`
  (`Acorr_le`), i.e. `C K^{-3/2} Θ(w)`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic NormedSpace FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n) (p₀ : Fin eta)

/-! ## The truncated observable on `ℓ²` -/

open Classical in
/-- The symbol of `A_{p₀}^E` on the full lattice. -/
noncomputable def dsymF (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (p₀ : Fin eta) (q : Cf eta) : ℝ :=
  if InQ (n : ℝ) q ∧ Ek sys L q ≤ E0 sys L n then regSymbol sys (gF L) p₀ q else 0

omit [Fintype ν] in
lemma E0_nonneg : 0 ≤ E0 sys L n := by
  unfold E0; have := one_le_mmax sys; positivity

omit [Fintype ν] in
lemma dsymF_nonneg (q : Cf eta) : 0 ≤ dsymF sys L n p₀ q := by
  unfold dsymF; split_ifs
  · exact regSymbol_nonneg sys _ p₀ q
  · exact le_rfl

omit [Fintype ν] in
lemma dsymF_le_Ek (q : Cf eta) : dsymF sys L n p₀ q ≤ Ek sys L q := by
  unfold dsymF; split_ifs
  · rw [Ek, E_eq_kineticSymbol]; exact regSymbol_le_kin sys _ p₀ q
  · exact E_nonneg (fun c => sys.mass_pos c) q

omit [Fintype ν] in
lemma dsymF_le_E0 (q : Cf eta) : dsymF sys L n p₀ q ≤ E0 sys L n := by
  unfold dsymF; split_ifs with h
  · have h1 := regSymbol_le_kin sys (gF L) p₀ q
    rw [← E_eq_kineticSymbol] at h1
    exact h1.trans h.2
  · exact E0_nonneg sys

omit [Fintype ν] in
lemma dsymF_eq_zero_of_not_mem (q : Cf eta) (hq : q ∉ Qs eta n) : dsymF sys L n p₀ q = 0 := by
  unfold dsymF; rw [if_neg]; rintro ⟨h, -⟩; exact hq (mem_Qs.mpr h)

/-- **The truncated observable `O = A_{p₀}^E` on `ℓ²`.** -/
noncomputable def Ofull (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (p₀ : Fin eta) :
    L2 eta →L[ℂ] L2 eta :=
  diagCLM (fun q => (dsymF sys L n p₀ q : ℂ)) (E0 sys L n) (E0_nonneg sys) (fun q => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dsymF_nonneg sys p₀ q)]
    exact dsymF_le_E0 sys p₀ q)

omit [Fintype ν] in
lemma Ofull_apply (x : L2 eta) (q : Cf eta) :
    Ofull sys L n p₀ x q = (dsymF sys L n p₀ q : ℂ) * x q := rfl

omit [Fintype ν] in
lemma norm_Ofull_apply_le (x : L2 eta) : ‖Ofull sys L n p₀ x‖ ≤ E0 sys L n * ‖x‖ :=
  l2_norm_le_of_le _ x (E0_nonneg sys) fun q => by
    rw [Ofull_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (dsymF_nonneg sys p₀ q)]
    exact mul_le_mul_of_nonneg_right (dsymF_le_E0 sys p₀ q) (norm_nonneg _)

omit [Fintype ν] in
lemma inner_Ofull (x y : L2 eta) :
    ⟪Ofull sys L n p₀ x, y⟫_ℂ = ⟪x, Ofull sys L n p₀ y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun q => ?_
  rw [Ofull_apply, Ofull_apply, RCLike.inner_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

omit [Fintype ν] in
lemma Ofull_selfAdjoint : IsSelfAdjoint (Ofull sys L n p₀) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => inner_Ofull sys p₀ x y

open Classical in
omit [Fintype ν] in
/-- `O` sees only the bulk block: `O x = O (P x)`. -/
lemma Ofull_trunc (x : L2 eta) : Ofull sys L n p₀ (molecularH2Truncate n x) = Ofull sys L n p₀ x := by
  ext q
  rw [Ofull_apply, Ofull_apply, molecularH2Truncate_apply]
  by_cases hq : q ∈ Qs eta n
  · have hP : q ∈ fourierConfigCube eta n :=
      (inP_iff_mem_cube n q).mp ((mem_Qs.mp hq).inP (Nat.cast_nonneg n))
    rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hP]
  · rw [dsymF_eq_zero_of_not_mem sys p₀ q hq]; simp

open Classical in
omit [Fintype ν] in
/-- `O` maps into the bulk block: `P O x = O x`. -/
lemma trunc_Ofull (x : L2 eta) : molecularH2Truncate n (Ofull sys L n p₀ x) = Ofull sys L n p₀ x := by
  ext q
  rw [molecularH2Truncate_apply]
  by_cases hq : q ∈ fourierConfigCube eta n
  · rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hq]
  · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq, Ofull_apply]
    have hq' : q ∉ Qs eta n := fun h =>
      hq ((inP_iff_mem_cube n q).mp ((mem_Qs.mp h).inP (Nat.cast_nonneg n)))
    rw [dsymF_eq_zero_of_not_mem sys p₀ q hq']; simp

omit [Fintype ν] in
/-- `O R = 0`. -/
lemma Ofull_sub_trunc (x : L2 eta) :
    Ofull sys L n p₀ (x - molecularH2Truncate n x) = 0 := by
  rw [map_sub, Ofull_trunc, sub_self]

omit [Fintype ν] in
include hL in
lemma inQ_idx_iff (v : Cfg eta n) :
    InQ (n : ℝ) (finiteConfigLatticeIndex eta n v) ↔
      ∀ a, finitePlaneWaveKabs (2 * Real.pi / L) n (v a) ≤ Kc L n / 4 := by
  unfold InQ
  refine forall_congr' fun a => ?_
  rw [kabs_eq_lattice]
  have hg : 0 < 2 * Real.pi / L := gF_pos hL
  have hK : Kc L n / 4 = 2 * Real.pi / L * ((n : ℝ) / 4) := by unfold Kc gL; ring
  rw [hK]
  have hls : latticeNormSq (finitePlaneWaveLatticeIndex n (v a)) =
      nsq (finiteConfigLatticeIndex eta n v a) := rfl
  rw [hls]
  have hn4 : (0 : ℝ) ≤ (n : ℝ) / 4 := by positivity
  constructor
  · intro h
    refine mul_le_mul_of_nonneg_left ?_ hg.le
    rw [← Real.sqrt_sq hn4]
    exact Real.sqrt_le_sqrt h
  · intro h
    have h1 := le_of_mul_le_mul_left h hg
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt (nsq_nonneg _)] at h2

omit [Fintype ν] in
include hL in
lemma dsymF_idx (v : Cfg eta n) :
    dsymF sys L n p₀ (finiteConfigLatticeIndex eta n v) = datumSym sys L p₀ v := by
  classical
  have hQ := inQ_idx_iff hL v
  have hA := Asym_eq_Ek sys (L := L) v
  have hR : regSymbol sys (gF L) p₀ (finiteConfigLatticeIndex eta n v) = Aproj sys L p₀ v := by
    unfold regSymbol Aproj
    rw [kabs_eq_lattice, mul_pow, Real.sq_sqrt (latticeNormSq_nonneg _)]
    change 1 / 2 * (gF L ^ 2 * latticeNormSq (finitePlaneWaveLatticeIndex n (v p₀)) / sys.mass p₀) = _
    unfold gF
    have := sys.mass_pos p₀
    field_simp
  unfold dsymF datumSym
  by_cases h1 : InQ (n : ℝ) (finiteConfigLatticeIndex eta n v)
  · by_cases h2 : Ek sys L (finiteConfigLatticeIndex eta n v) ≤ E0 sys L n
    · rw [if_pos ⟨h1, h2⟩, if_pos ⟨hQ.mp h1, by rw [hA]; exact h2⟩, hR]
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 (by rw [← hA]; exact h.2))]
  · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 (hQ.mpr h.1))]

omit [Fintype ν] in
include hL in
/-- **`O` on the cube is the datum operator**: `O (emb v) = emb (A_{p₀}^E v)`. -/
lemma Ofull_emb (v : En eta n) : Ofull sys L n p₀ (emb eta n v) = emb eta n (datum sys L p₀ v) := by
  ext q
  rw [Ofull_apply]
  by_cases hq : q ∈ fourierConfigCube eta n
  · rcases Finset.mem_image.mp hq with ⟨p, _, rfl⟩
    simp only [emb, LinearIsometry.coe_toContinuousLinearMap,
      finiteFourierLpIsometry_apply, finiteFourierLpEmbed_apply_index]
    rw [dsymF_idx sys hL p₀ p, datum_apply]
  · simp only [emb, LinearIsometry.coe_toContinuousLinearMap,
      finiteFourierLpIsometry_apply]
    rw [finiteFourierLpEmbed_apply_not_mem_cube eta n _ q hq,
      finiteFourierLpEmbed_apply_not_mem_cube eta n _ q hq, mul_zero]

omit [Fintype ν] in
include hL in
lemma ext_Ofull_emb (v : En eta n) : ext eta n (Ofull sys L n p₀ (emb eta n v)) = datum sys L p₀ v := by
  rw [Ofull_emb sys hL p₀, ext_emb]

/-! ## The bulk generator on cube vectors -/

omit [Fintype ν] in
lemma sub_trunc_emb (v : En eta n) : emb eta n v - molecularH2Truncate n (emb eta n v) = 0 := by
  rw [trunc_emb, sub_self]

open Classical in
lemma sig_emb (v : En eta n) :
    Sig sys L n hL hn (emb eta n v) = Sig sys L n hL hn (lpTruncate (Qs eta n) (emb eta n v)) := by
  rw [sig_split sys hL hn (emb eta n v), sub_trunc_emb, map_zero, add_zero]

lemma trunc_sig_emb (v : En eta n) :
    molecularH2Truncate n (Sig sys L n hL hn (emb eta n v)) = 0 := by
  rw [sig_interior sys hL hn (emb eta n v), sub_trunc_emb, map_zero]

omit [Fintype ν] in
lemma stateMap_cubeLift' (v : En eta n) : Sm eta L (cubeLift (gF L) n v) = emb eta n v :=
  stateMap_cubeLift (gF L) n v

/-- **`‖Σ_b v‖ ≤ a₀ (‖v‖ + ‖A v‖)`** for cube vectors. -/
lemma norm_sig_emb_le (v : En eta n) :
    ‖Sig sys L n hL hn (emb eta n v)‖ ≤
      a0c sys L n * (‖v‖ + ‖FSSpectral.kin (sb eta n) (Asym sys L n) v‖) := by
  have h := norm_sigQ_le sys hL hn (cubeLift (gF L) n v)
  rw [stateMap_cubeLift', norm_kinetic_cubeLift, norm_emb] at h
  rw [sig_emb sys hL hn v]
  exact h

lemma norm_sig_emb_le' (v : En eta n) :
    ‖Sig sys L n hL hn (emb eta n v)‖ ≤
      2 * a0c sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  refine (norm_sig_emb_le sys hL hn v).trans ?_
  have h1 := norm_le_wt sys L n zero_le_one v
  have h2 := norm_kin_le_wt sys (L := L) v
  have := a0c_nonneg sys (L := L) (n := n)
  nlinarith

/-! ## The nonsecular terms -/

/-- `⟪x, e^{Σ} O e^{-Σ} y⟫ = ⟪e^{-Σ} x, O e^{-Σ} y⟫`. -/
lemma inner_conj_O (x y : L2 eta) :
    ⟪x, (exp (Sig sys L n hL hn) * Ofull sys L n p₀ * star (exp (Sig sys L n hL hn))) y⟫_ℂ =
      ⟪exp (-Sig sys L n hL hn) x, Ofull sys L n p₀ (exp (-Sig sys L n hL hn) y)⟫_ℂ := by
  rw [ContinuousLinearMap.star_eq_adjoint, adjoint_exp_Sig]
  simp only [mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_exp_Sig]

/-- **The `RR` term**: `|⟪r, Ã r⟫| ≤ E₀ (A_σ ‖r‖)²` for `r ∈ ran R`. -/
theorem T4_le (x : L2 eta) :
    ‖⟪x - molecularH2Truncate n x, (exp (Sig sys L n hL hn) * Ofull sys L n p₀ *
        star (exp (Sig sys L n hL hn))) (x - molecularH2Truncate n x)⟫_ℂ‖ ≤
      E0 sys L n * (Asig sys L n * ‖x - molecularH2Truncate n x‖) ^ 2 := by
  set r := x - molecularH2Truncate n x
  set Sg := Sig sys L n hL hn
  set O := Ofull sys L n p₀
  have hskew := (Sig_skew_unitary (sys := sys) hL hn).1
  set y := exp (-Sg) r - r
  have hOr : O r = 0 := Ofull_sub_trunc sys p₀ x
  have hOe : O (exp (-Sg) r) = O y := by simp only [y, map_sub, hOr, sub_zero]
  rw [inner_conj_O, hOe, ← inner_Ofull, hOe]
  have hy : ‖y‖ ≤ Asig sys L n * ‖r‖ :=
    (FSConj.norm_exp_neg_sub_one_apply_le hskew r).trans
      ((Sg.le_opNorm r).trans (mul_le_mul_of_nonneg_right (norm_Sig_le hL hn) (norm_nonneg _)))
  calc ‖⟪O y, y⟫_ℂ‖ ≤ ‖O y‖ * ‖y‖ := norm_inner_le_norm _ _
    _ ≤ E0 sys L n * ‖y‖ * ‖y‖ := mul_le_mul_of_nonneg_right (norm_Ofull_apply_le sys p₀ y) (norm_nonneg _)
    _ = E0 sys L n * ‖y‖ ^ 2 := by ring
    _ ≤ E0 sys L n * (Asig sys L n * ‖r‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy 2) (E0_nonneg sys)

/-- **The cross term**: `|⟪P ψ̃, Ã R ψ̃⟫| ≤ (1 + 2 E₀ a₀) Θ(a) A_σ ‖R ψ̃‖` with `a = P ψ̃`. -/
theorem T5_le (x : L2 eta) :
    ‖⟪emb eta n (ext eta n x), (exp (Sig sys L n hL hn) * Ofull sys L n p₀ *
        star (exp (Sig sys L n hL hn))) (x - molecularH2Truncate n x)⟫_ℂ‖ ≤
      (1 + 2 * E0 sys L n * a0c sys L n) *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n x)‖ *
        (Asig sys L n * ‖x - molecularH2Truncate n x‖) := by
  set a := ext eta n x
  set r := x - molecularH2Truncate n x
  set Sg := Sig sys L n hL hn
  set O := Ofull sys L n p₀
  have hskew := (Sig_skew_unitary (sys := sys) hL hn).1
  set y := exp (-Sg) r - r
  have hOr : O r = 0 := Ofull_sub_trunc sys p₀ x
  have hOe : O (exp (-Sg) r) = O y := by simp only [y, map_sub, hOr, sub_zero]
  rw [inner_conj_O, hOe, ← inner_Ofull]
  have hy : ‖y‖ ≤ Asig sys L n * ‖r‖ :=
    (FSConj.norm_exp_neg_sub_one_apply_le hskew r).trans
      ((Sg.le_opNorm r).trans (mul_le_mul_of_nonneg_right (norm_Sig_le hL hn) (norm_nonneg _)))
  set Θa := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 a‖
  have hOa : ‖O (exp (-Sg) (emb eta n a))‖ ≤ (1 + 2 * E0 sys L n * a0c sys L n) * Θa := by
    have e1 : O (exp (-Sg) (emb eta n a)) = O (emb eta n a) +
        O (exp (-Sg) (emb eta n a) - emb eta n a) := by rw [map_sub]; abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖O (emb eta n a)‖ ≤ Θa := by
      rw [Ofull_emb sys hL p₀, norm_emb]; exact norm_datum_le sys L p₀ a
    have h2 : ‖O (exp (-Sg) (emb eta n a) - emb eta n a)‖ ≤ E0 sys L n * (2 * a0c sys L n * Θa) := by
      refine (norm_Ofull_apply_le sys p₀ _).trans (mul_le_mul_of_nonneg_left ?_ (E0_nonneg sys))
      exact (FSConj.norm_exp_neg_sub_one_apply_le hskew _).trans (norm_sig_emb_le' sys hL hn a)
    have : E0 sys L n * (2 * a0c sys L n * Θa) = 2 * E0 sys L n * a0c sys L n * Θa := by ring
    linarith
  calc ‖⟪O (exp (-Sg) (emb eta n a)), y⟫_ℂ‖ ≤ ‖O (exp (-Sg) (emb eta n a))‖ * ‖y‖ :=
        norm_inner_le_norm _ _
    _ ≤ (1 + 2 * E0 sys L n * a0c sys L n) * Θa * (Asig sys L n * ‖r‖) :=
        mul_le_mul hOa hy (norm_nonneg _) (by
          have := E0_nonneg sys (L := L) (n := n); have := a0c_nonneg sys (L := L) (n := n)
          positivity)

/-- The defect `P (e^{-Σ} - 1) v = P (e^{-Σ} - 1 + Σ) v` of a cube vector, `‖·‖ ≤ 2 A_σ a₀ Θ(v)`. -/
lemma norm_trunc_dexp_le (v : En eta n) :
    ‖molecularH2Truncate n (exp (-Sig sys L n hL hn) (emb eta n v) - emb eta n v)‖ ≤
      Asig sys L n * (2 * a0c sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖) := by
  set Sg := Sig sys L n hL hn
  set e := emb eta n v
  have hskew := (Sig_skew_unitary (sys := sys) hL hn).1
  have h1 : molecularH2Truncate n (exp (-Sg) e - e) = molecularH2Truncate n (exp (-Sg) e - e + Sg e) := by
    rw [molecularH2Truncate_add, trunc_sig_emb sys hL hn v, add_zero]
  rw [h1]
  refine (lpTruncate_norm_le _ _).trans ?_
  refine (FSConj.norm_exp_neg_sub_one_add_apply_le hskew e).trans ?_
  refine (Sg.le_opNorm _).trans ?_
  exact mul_le_mul (norm_Sig_le hL hn) (norm_sig_emb_le' sys hL hn v) (norm_nonneg _)
    (Asig_nonneg hL)

/-- **The observable correction `⟪χ, (P Ã P - O) χ⟫`**:
`|·| ≤ 2 ‖P d‖ Θ(χ) + E₀ ‖P d‖²` with `‖P d‖ ≤ 2 A_σ a₀ Θ(χ)`. -/
theorem T2_le (v : En eta n) :
    ‖⟪v, ext eta n ((exp (Sig sys L n hL hn) * Ofull sys L n p₀ *
        star (exp (Sig sys L n hL hn))) (emb eta n v)) - ext eta n (Ofull sys L n p₀ (emb eta n v))⟫_ℂ‖ ≤
      2 * (Asig sys L n * (2 * a0c sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖)) *
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ +
        E0 sys L n * (Asig sys L n * (2 * a0c sys L n *
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖)) ^ 2 := by
  set Sg := Sig sys L n hL hn
  set O := Ofull sys L n p₀
  set e := emb eta n v
  set d := exp (-Sg) e - e
  set pd := molecularH2Truncate n d
  set Θv := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖
  set D := Asig sys L n * (2 * a0c sys L n * Θv)
  have hpd : ‖pd‖ ≤ D := norm_trunc_dexp_le sys hL hn v
  have hOe : ‖O e‖ ≤ Θv := by rw [Ofull_emb sys hL p₀, norm_emb]; exact norm_datum_le sys L p₀ v
  have hOd : O d = O pd := (Ofull_trunc sys p₀ d).symm
  rw [inner_sub_right, inner_ext', inner_ext', inner_conj_O]
  have hed : exp (-Sg) e = e + d := by simp only [d]; abel
  rw [hed, map_add, hOd, inner_add_left, inner_add_right, inner_add_right]
  have e1 : ⟪d, O e⟫_ℂ = ⟪pd, O e⟫_ℂ := by rw [← inner_Ofull, hOd, inner_Ofull]
  have e2 : ⟪d, O pd⟫_ℂ = ⟪O pd, pd⟫_ℂ := by rw [← inner_Ofull, hOd]
  have e3 : ⟪e, O pd⟫_ℂ = ⟪O e, pd⟫_ℂ := by rw [inner_Ofull]
  rw [e1, e2, e3]
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) hpd
  have hΘ0 : 0 ≤ Θv := norm_nonneg _
  have k1 : ‖⟪O e, pd⟫_ℂ‖ ≤ Θv * D :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hOe hpd (norm_nonneg _) hΘ0)
  have k2 : ‖⟪pd, O e⟫_ℂ‖ ≤ D * Θv :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hpd hOe (norm_nonneg _) hD0)
  have k3 : ‖⟪O pd, pd⟫_ℂ‖ ≤ E0 sys L n * D ^ 2 := by
    refine (norm_inner_le_norm _ _).trans ?_
    calc ‖O pd‖ * ‖pd‖ ≤ E0 sys L n * ‖pd‖ * ‖pd‖ :=
          mul_le_mul_of_nonneg_right (norm_Ofull_apply_le sys p₀ pd) (norm_nonneg _)
      _ = E0 sys L n * ‖pd‖ ^ 2 := by ring
      _ ≤ E0 sys L n * D ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hpd 2) (E0_nonneg sys)
  have : ⟪e, O e⟫_ℂ + ⟪O e, pd⟫_ℂ + (⟪pd, O e⟫_ℂ + ⟪O pd, pd⟫_ℂ) - ⟪e, O e⟫_ℂ =
      ⟪O e, pd⟫_ℂ + ⟪pd, O e⟫_ℂ + ⟪O pd, pd⟫_ℂ := by ring
  rw [this]
  calc ‖⟪O e, pd⟫_ℂ + ⟪pd, O e⟫_ℂ + ⟪O pd, pd⟫_ℂ‖
      ≤ ‖⟪O e, pd⟫_ℂ‖ + ‖⟪pd, O e⟫_ℂ‖ + ‖⟪O pd, pd⟫_ℂ‖ := norm_add₃_le
    _ ≤ Θv * D + D * Θv + E0 sys L n * D ^ 2 := by gcongr
    _ = 2 * D * Θv + E0 sys L n * D ^ 2 := by ring

omit [Fintype ν] in
/-- `‖A (A_{p₀}^E v)‖ ≤ E₀ ‖A_{p₀}^E v‖`: the datum is supported in `A ≤ E₀`. -/
lemma norm_kin_datum_le (v : En eta n) :
    ‖FSSpectral.kin (sb eta n) (Asym sys L n) (datum sys L p₀ v)‖ ≤
      E0 sys L n * ‖datum sys L p₀ v‖ := by
  have h2 : ‖FSSpectral.kin (sb eta n) (Asym sys L n) (datum sys L p₀ v)‖ ^ 2 ≤
      (E0 sys L n * ‖datum sys L p₀ v‖) ^ 2 := by
    rw [mul_pow, norm_sq_En, norm_sq_En, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [kin_apply', norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Asym_nonneg sys L n p), mul_pow]
    by_cases hp : Asym sys L n p ≤ E0 sys L n
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Asym_nonneg sys L n p) hp 2) (sq_nonneg _)
    · push Not at hp
      rw [datum_support sys L p₀ v p hp]; simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (E0_nonneg sys) (norm_nonneg _))
    two_ne_zero).mp h2

/-- The constant of `lem:acorr` (vector bound). -/
noncomputable def CAcorr (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  E0 sys L n * (1 + Asig sys L n ^ 2) * (2 * Asig sys L n * a0c sys L n) +
    Asig sys L n * a0c sys L n * (1 + E0 sys L n)

/-- **`lem:acorr`, vector bound**: `‖(P Ã P - O) w‖ ≤ C_Acorr Θ(w)` with `C_Acorr = O(K^{-3/2})`. -/
theorem Acorr_le (w : En eta n) :
    ‖ext eta n ((exp (Sig sys L n hL hn) * Ofull sys L n p₀ * star (exp (Sig sys L n hL hn)))
        (emb eta n w)) - ext eta n (Ofull sys L n p₀ (emb eta n w))‖ ≤
      CAcorr sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 w‖ := by
  set Sg := Sig sys L n hL hn
  set O := Ofull sys L n p₀
  set e := emb eta n w
  set d := exp (-Sg) e - e
  set pd := molecularH2Truncate n d
  set Θw := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 w‖
  have hskew := (Sig_skew_unitary (sys := sys) hL hn).1
  have hA := norm_Sig_le (sys := sys) hL hn
  have hA0 := Asig_nonneg (sys := sys) (n := n) hL
  have ha0 := a0c_nonneg sys (L := L) (n := n)
  have hE0 := E0_nonneg sys (L := L) (n := n)
  have hΘ0 : 0 ≤ Θw := norm_nonneg _
  have hpd : ‖pd‖ ≤ Asig sys L n * (2 * a0c sys L n * Θw) := norm_trunc_dexp_le sys hL hn w
  have hOd : O d = O pd := (Ofull_trunc sys p₀ d).symm
  -- `Ã e = e^{Σ} y` with `y = O e + O pd`
  set y := O e + O pd
  have hAt : (exp Sg * O * star (exp Sg)) e = exp Sg y := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_exp_Sig]
    simp only [mul_apply_eq_comp]
    have : exp (-Sg) e = e + d := by simp only [d]; abel
    rw [this, map_add, hOd]
  have hy_trunc : molecularH2Truncate n y = y := by
    simp only [y]
    rw [molecularH2Truncate_add, trunc_Ofull sys p₀, trunc_Ofull sys p₀]
  -- `P e^{Σ} y = y + Σ R J y`
  have hexp : ext eta n (exp Sg y) = ext eta n y +
      ext eta n (Sg (FSConj.Jx Sg y - molecularH2Truncate n (FSConj.Jx Sg y))) := by
    have h := dressed_interior sys hL hn y
    rw [hy_trunc, sub_self, map_zero, add_zero] at h
    rw [← extract_truncate n (exp Sg y), h, map_add]
  have hcorr : ext eta n ((exp Sg * O * star (exp Sg)) e) - ext eta n (O e) =
      ext eta n (O pd) + ext eta n (Sg (FSConj.Jx Sg y - molecularH2Truncate n (FSConj.Jx Sg y))) := by
    rw [hAt, hexp]; simp only [y, map_add]; abel
  rw [hcorr]
  -- the two pieces
  have hOpd : ‖ext eta n (O pd)‖ ≤ E0 sys L n * (Asig sys L n * (2 * a0c sys L n * Θw)) :=
    (norm_ext_le _).trans ((norm_Ofull_apply_le sys p₀ pd).trans (mul_le_mul_of_nonneg_left hpd hE0))
  have hSy : ‖Sg y‖ ≤ a0c sys L n * (1 + E0 sys L n) * Θw +
      Asig sys L n * (E0 sys L n * (Asig sys L n * (2 * a0c sys L n * Θw))) := by
    rw [map_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [Ofull_emb sys hL p₀]
      refine (norm_sig_emb_le sys hL hn _).trans ?_
      have h1 := norm_datum_le sys L p₀ w
      have h2 := norm_kin_datum_le sys (L := L) p₀ w
      calc a0c sys L n * (‖datum sys L p₀ w‖ + ‖FSSpectral.kin (sb eta n) (Asym sys L n)
            (datum sys L p₀ w)‖) ≤ a0c sys L n * (Θw + E0 sys L n * Θw) := by
            gcongr
            exact h2.trans (mul_le_mul_of_nonneg_left h1 hE0)
        _ = _ := by ring
    · refine (Sg.le_opNorm _).trans (mul_le_mul hA ?_ (norm_nonneg _) hA0)
      exact (norm_Ofull_apply_le sys p₀ pd).trans (mul_le_mul_of_nonneg_left hpd hE0)
  have hJ : ‖ext eta n (Sg (FSConj.Jx Sg y - molecularH2Truncate n (FSConj.Jx Sg y)))‖ ≤
      Asig sys L n * (a0c sys L n * (1 + E0 sys L n) * Θw +
        Asig sys L n * (E0 sys L n * (Asig sys L n * (2 * a0c sys L n * Θw)))) := by
    refine (norm_ext_le _).trans ((Sg.le_opNorm _).trans (mul_le_mul hA ?_ (norm_nonneg _) hA0))
    exact (norm_sub_truncate_le n _).trans ((FSConj.norm_Jx_apply_le hskew y).trans hSy)
  calc _ ≤ ‖ext eta n (O pd)‖ +
        ‖ext eta n (Sg (FSConj.Jx Sg y - molecularH2Truncate n (FSConj.Jx Sg y)))‖ := norm_add_le _ _
    _ ≤ E0 sys L n * (Asig sys L n * (2 * a0c sys L n * Θw)) +
        Asig sys L n * (a0c sys L n * (1 + E0 sys L n) * Θw +
          Asig sys L n * (E0 sys L n * (Asig sys L n * (2 * a0c sys L n * Θw)))) := add_le_add hOpd hJ
    _ = CAcorr sys L n * Θw := by unfold CAcorr; ring

end FSNormal
