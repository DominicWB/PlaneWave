import PlaneWave.Source.SourceTerm

/-!
# Flux/source build, block 4b: reduction to the truncated observable (`lem:bulkobs`,
`lem:bulkobsE`)

For a state `x` with kinetic image `y = E x` and register tails `‖1_{a,>λ} x‖ ≤ M λ^{-5/2}`,
`‖1_{a,>λ} y‖ ≤ M λ^{-1/2}` (`λ ≥ 1`):

  `0 ≤ ⟨x, A_{p₀} x⟩ - ⟨x, A_{p₀}^E x⟩ ≤ η M² ((K/4)^{-3} + λ_E^{-3})`,  `λ_E = (2E₀/η)^{1/2}`,

(`obs_reduction`): `A_{p₀} - A_{p₀}^E` lives where some register exceeds `K/4` (`lem:bulkobs`) or the
total kinetic energy exceeds `E₀` (`lem:bulkobsE`, then some register exceeds `λ_E`), and on each
register tail `Σ E |x|² ≤ ‖1 x‖ ‖1 y‖`. Applied to the exact trajectory (`FGood`) and to good cube
states (`obs_reduction_cube`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic NormedSpace FluxSourceTest
  FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

omit [Fintype ν] in
/-- Cauchy–Schwarz on `ℓ²`: `Σ ‖a q‖ ‖b q‖ ≤ ‖a‖ ‖b‖`. -/
lemma tsum_norm_mul_le (a b : L2 eta) : ∑' q, ‖a q‖ * ‖b q‖ ≤ ‖a‖ * ‖b‖ := by
  have hs := summable_norm_mul_of_sq (summable_sq_coord a) (summable_sq_coord b)
  by_cases ha : ‖a‖ = 0
  · have : a = 0 := norm_eq_zero.mp ha
    subst this; simp
  by_cases hb : ‖b‖ = 0
  · have : b = 0 := norm_eq_zero.mp hb
    subst this; simp
  have ha0 : 0 < ‖a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm ha)
  have hb0 : 0 < ‖b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hb)
  set l := ‖b‖ / ‖a‖
  have hl : 0 < l := div_pos hb0 ha0
  have hpt : ∀ q, ‖a q‖ * ‖b q‖ ≤ (l * ‖a q‖ ^ 2 + ‖b q‖ ^ 2 / l) / 2 := by
    intro q
    have key : (l * ‖a q‖ ^ 2 + ‖b q‖ ^ 2 / l) / 2 - ‖a q‖ * ‖b q‖ =
        (l * ‖a q‖ - ‖b q‖) ^ 2 / (2 * l) := by
      field_simp; ring
    have : 0 ≤ (l * ‖a q‖ - ‖b q‖) ^ 2 / (2 * l) := by positivity
    linarith
  have hsa := summable_sq_coord a
  have hsb := summable_sq_coord b
  have hs2 : Summable fun q => (l * ‖a q‖ ^ 2 + ‖b q‖ ^ 2 / l) / 2 :=
    ((hsa.mul_left l).add (hsb.div_const l)).div_const 2
  calc ∑' q, ‖a q‖ * ‖b q‖ ≤ ∑' q, (l * ‖a q‖ ^ 2 + ‖b q‖ ^ 2 / l) / 2 :=
        hs.tsum_le_tsum hpt hs2
    _ = (l * ‖a‖ ^ 2 + ‖b‖ ^ 2 / l) / 2 := by
        rw [tsum_div_const, (hsa.mul_left l).tsum_add (hsb.div_const l), tsum_mul_left,
          tsum_div_const, tsum_sq_coord, tsum_sq_coord]
    _ = ‖a‖ * ‖b‖ := by simp only [l]; field_simp; ring

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (p₀ : Fin eta)

omit [Fintype ν] in
/-- On a register tail, `Σ_{tail} E |x|² ≤ ‖1 x‖ ‖1 y‖` for `y = E x`. -/
lemma tail_form_le (x y : L2 eta) (hy : ∀ q, y q = (Ek sys L q : ℂ) * x q) (a : Fin eta) (l : ℝ) :
    ∑' q, (if l < gF L * Real.sqrt (latticeNormSq (q a)) then Ek sys L q else 0) * ‖x q‖ ^ 2 ≤
      ‖tailMask (gF L) l a x‖ * ‖tailMask (gF L) l a y‖ := by
  refine le_trans (le_of_eq ?_) (tsum_norm_mul_le _ _)
  refine tsum_congr fun q => ?_
  rw [tailMask_apply, tailMask_apply, hy q]
  have hE := E_nonneg (g := gF L) (fun c => sys.mass_pos c) q
  split_ifs
  · rw [one_mul, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]; ring
  · simp

/-- The register threshold of the kinetic truncation, `λ_E = (2E₀/η)^{1/2}`. -/
noncomputable def lamE (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * E0 sys L n / eta)

open Classical in
omit [Fintype ν] in
include hL in
/-- **`lem:bulkobs` + `lem:bulkobsE`**: `0 ≤ ⟨x, A_{p₀} x⟩ - ⟨x, A_{p₀}^E x⟩ ≤ η M² ((K/4)^{-3} + λ_E^{-3})`
for `K ≥ 4` and `λ_E ≥ 1`. -/
theorem obs_reduction (x y : L2 eta) (hy : ∀ q, y q = (Ek sys L q : ℂ) * x q) {M : ℝ}
    (htail : ∀ (a : Fin eta) (l : ℝ), 1 ≤ l →
      ‖tailMask (gF L) l a x‖ ≤ M * l ^ (-(5 / 2 : ℝ)) ∧
      ‖tailMask (gF L) l a y‖ ≤ M * l ^ (-(1 / 2 : ℝ)))
    (hK : 4 ≤ Kc L n) (hlam : 1 ≤ lamE sys L n) (heta : 0 < eta) :
    0 ≤ (regKin sys (gF L) p₀).expect x - ∑' q, dsymF sys L n p₀ q * ‖x q‖ ^ 2 ∧
    (regKin sys (gF L) p₀).expect x - ∑' q, dsymF sys L n p₀ q * ‖x q‖ ^ 2 ≤
      eta * (M ^ 2 * ((Kc L n / 4) ^ (-(3 : ℝ)) + lamE sys L n ^ (-(3 : ℝ)))) := by
  set K4 := Kc L n / 4
  set lE := lamE sys L n
  have hK4 : 1 ≤ K4 := by simp only [K4]; linarith
  have hsx := summable_sq_coord x
  have hμ : ∀ q, (regKin sys (gF L) p₀).μ q = regSymbol sys (gF L) p₀ q := fun q => rfl
  have hμE : ∀ q, regSymbol sys (gF L) p₀ q ≤ Ek sys L q := fun q => by
    rw [Ek, E_eq_kineticSymbol]; exact regSymbol_le_kin sys _ p₀ q
  have hd_le : ∀ q, dsymF sys L n p₀ q ≤ regSymbol sys (gF L) p₀ q := fun q => by
    unfold dsymF; split_ifs
    · exact le_rfl
    · exact regSymbol_nonneg sys _ p₀ q
  set T : Fin eta → ℝ → Cf eta → ℝ := fun a l q =>
    if l < gF L * Real.sqrt (latticeNormSq (q a)) then Ek sys L q else 0
  -- pointwise: `A_{p₀} - A_{p₀}^E ≤ Σ_a (T_{K/4} + T_{λ_E})`
  have hpt : ∀ q, (regSymbol sys (gF L) p₀ q - dsymF sys L n p₀ q) * ‖x q‖ ^ 2 ≤
      ∑ a, (T a K4 q + T a lE q) * ‖x q‖ ^ 2 := by
    intro q
    have hE := E_nonneg (g := gF L) (fun c => sys.mass_pos c) q
    have hT0 : ∀ a l, 0 ≤ T a l q := fun a l => by simp only [T]; split_ifs <;> linarith
    by_cases hgood : InQ (n : ℝ) q ∧ Ek sys L q ≤ E0 sys L n
    · have : dsymF sys L n p₀ q = regSymbol sys (gF L) p₀ q := by unfold dsymF; rw [if_pos hgood]
      rw [this, sub_self, zero_mul]
      exact Finset.sum_nonneg fun a _ => mul_nonneg (add_nonneg (hT0 a _) (hT0 a _)) (sq_nonneg _)
    · -- some register is in a tail
      have hex : ∃ a, T a K4 q + T a lE q ≥ Ek sys L q := by
        by_cases hQ : InQ (n : ℝ) q
        · have hE0 : E0 sys L n < Ek sys L q := by
            by_contra h; push Not at h; exact hgood ⟨hQ, h⟩
          -- some register carries more than `E₀/η`
          have : ∃ c, E0 sys L n / eta < gF L ^ 2 / (2 * sys.mass c) * nsq (q c) := by
            by_contra hno
            push Not at hno
            have hsum := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hno c
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
            have : Ek sys L q ≤ E0 sys L n := by
              have hE' : Ek sys L q = ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (q c) := rfl
              rw [hE']
              calc _ ≤ (eta : ℝ) * (E0 sys L n / eta) := hsum
                _ = E0 sys L n := by field_simp
            linarith
          obtain ⟨c, hc⟩ := this
          refine ⟨c, ?_⟩
          have hm := sys.one_le_mass c
          have hg := gF_pos hL
          have hnsq : 2 * E0 sys L n / eta < gF L ^ 2 * nsq (q c) := by
            have h1 : gF L ^ 2 / (2 * sys.mass c) * nsq (q c) ≤ gF L ^ 2 * nsq (q c) / 2 := by
              rw [div_mul_eq_mul_div]
              exact div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (nsq_nonneg _)) (by norm_num)
                (by linarith)
            have h2 : 2 * E0 sys L n / eta = 2 * (E0 sys L n / eta) := by ring
            rw [h2]
            linarith
          have hlt : lE < gF L * Real.sqrt (latticeNormSq (q c)) := by
            simp only [lE, lamE]
            have hls : latticeNormSq (q c) = nsq (q c) := rfl
            rw [hls, show gF L * Real.sqrt (nsq (q c)) = Real.sqrt (gF L ^ 2 * nsq (q c)) by
              rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hg.le]]
            exact Real.sqrt_lt_sqrt (div_nonneg (by linarith [E0_nonneg sys (L := L) (n := n)])
              (Nat.cast_nonneg _)) hnsq
          simp only [T]
          rw [if_pos hlt]
          have := hT0 c K4
          simp only [T] at this
          linarith
        · -- outside `Q`
          unfold InQ at hQ
          push Not at hQ
          obtain ⟨c, hc⟩ := hQ
          refine ⟨c, ?_⟩
          have hg := gF_pos hL
          have hlt : K4 < gF L * Real.sqrt (latticeNormSq (q c)) := by
            have hls : latticeNormSq (q c) = nsq (q c) := rfl
            rw [hls]
            have hn4 : (0 : ℝ) ≤ (n : ℝ) / 4 := by positivity
            have h1 : (n : ℝ) / 4 < Real.sqrt (nsq (q c)) := by
              rw [← Real.sqrt_sq hn4]; exact Real.sqrt_lt_sqrt (sq_nonneg _) hc
            simp only [K4, Kc, gL]
            have : gF L = 2 * Real.pi / L := rfl
            rw [this]
            nlinarith
          simp only [T]
          rw [if_pos hlt]
          have := hT0 c lE
          simp only [T] at this
          linarith
      obtain ⟨a, ha⟩ := hex
      have hdiff : regSymbol sys (gF L) p₀ q - dsymF sys L n p₀ q ≤ Ek sys L q := by
        have := dsymF_nonneg sys p₀ q (L := L) (n := n); linarith [hμE q]
      calc (regSymbol sys (gF L) p₀ q - dsymF sys L n p₀ q) * ‖x q‖ ^ 2
          ≤ Ek sys L q * ‖x q‖ ^ 2 := mul_le_mul_of_nonneg_right hdiff (sq_nonneg _)
        _ ≤ (T a K4 q + T a lE q) * ‖x q‖ ^ 2 := mul_le_mul_of_nonneg_right ha (sq_nonneg _)
        _ ≤ ∑ b, (T b K4 q + T b lE q) * ‖x q‖ ^ 2 :=
            Finset.single_le_sum (f := fun b => (T b K4 q + T b lE q) * ‖x q‖ ^ 2)
              (fun b _ => mul_nonneg (add_nonneg (hT0 b _) (hT0 b _)) (sq_nonneg _))
              (Finset.mem_univ a)
  -- summability
  have hsE : ∀ a l, Summable fun q => T a l q * ‖x q‖ ^ 2 := by
    intro a l
    refine (summable_norm_mul_of_sq (summable_sq_coord (tailMask (gF L) l a x))
      (summable_sq_coord (tailMask (gF L) l a y))).congr fun q => ?_
    rw [tailMask_apply, tailMask_apply, hy q]
    have hE := E_nonneg (g := gF L) (fun c => sys.mass_pos c) q
    simp only [T]
    split_ifs
    · rw [one_mul, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]; ring
    · simp
  have hsxy := summable_norm_mul_of_sq (summable_sq_coord x) (summable_sq_coord y)
  have hEq : ∀ q, Ek sys L q * ‖x q‖ ^ 2 = ‖x q‖ * ‖y q‖ := by
    intro q
    rw [hy q, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (E_nonneg (g := gF L) (fun c => sys.mass_pos c) q)]; ring
  have hsμ : Summable fun q => regSymbol sys (gF L) p₀ q * ‖x q‖ ^ 2 :=
    hsxy.of_nonneg_of_le (fun q => mul_nonneg (regSymbol_nonneg sys _ p₀ q) (sq_nonneg _))
      fun q => by rw [← hEq q]; exact mul_le_mul_of_nonneg_right (hμE q) (sq_nonneg _)
  have hsd : Summable fun q => dsymF sys L n p₀ q * ‖x q‖ ^ 2 :=
    hsμ.of_nonneg_of_le (fun q => mul_nonneg (dsymF_nonneg sys p₀ q) (sq_nonneg _))
      fun q => mul_le_mul_of_nonneg_right (hd_le q) (sq_nonneg _)
  have hdiff : (regKin sys (gF L) p₀).expect x - ∑' q, dsymF sys L n p₀ q * ‖x q‖ ^ 2 =
      ∑' q, (regSymbol sys (gF L) p₀ q - dsymF sys L n p₀ q) * ‖x q‖ ^ 2 := by
    unfold KinMult.expect
    simp only [hμ]
    rw [← hsμ.tsum_sub hsd]
    congr 1; funext q; ring
  rw [hdiff]
  constructor
  · exact tsum_nonneg fun q => mul_nonneg (by linarith [hd_le q]) (sq_nonneg _)
  · have hsT : Summable fun q => ∑ a, (T a K4 q + T a lE q) * ‖x q‖ ^ 2 :=
      summable_sum fun a _ => by
        have := (hsE a K4).add (hsE a lE)
        exact this.congr fun q => by ring
    have hs1 : Summable fun q => (regSymbol sys (gF L) p₀ q - dsymF sys L n p₀ q) * ‖x q‖ ^ 2 :=
      (hsμ.sub hsd).congr fun q => by ring
    calc ∑' q, (regSymbol sys (gF L) p₀ q - dsymF sys L n p₀ q) * ‖x q‖ ^ 2
        ≤ ∑' q, ∑ a, (T a K4 q + T a lE q) * ‖x q‖ ^ 2 := hs1.tsum_le_tsum hpt hsT
      _ = ∑ a, (∑' q, T a K4 q * ‖x q‖ ^ 2 + ∑' q, T a lE q * ‖x q‖ ^ 2) := by
          rw [Summable.tsum_finsetSum fun a _ => ((hsE a K4).add (hsE a lE)).congr fun q => by ring]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← (hsE a K4).tsum_add (hsE a lE)]
          congr 1; funext q; ring
      _ ≤ ∑ _a : Fin eta, (M ^ 2 * K4 ^ (-(3 : ℝ)) + M ^ 2 * lE ^ (-(3 : ℝ))) := by
          refine Finset.sum_le_sum fun a _ => add_le_add ?_ ?_
          · have h := tail_form_le sys x y hy a K4
            obtain ⟨h1, h2⟩ := htail a K4 hK4
            refine h.trans ?_
            have hK40 : 0 < K4 := by linarith
            have e : K4 ^ (-(3 : ℝ)) = K4 ^ (-(5 / 2 : ℝ)) * K4 ^ (-(1 / 2 : ℝ)) := by
              rw [← Real.rpow_add hK40]; norm_num
            rw [e]
            calc ‖tailMask (gF L) K4 a x‖ * ‖tailMask (gF L) K4 a y‖
                ≤ (M * K4 ^ (-(5 / 2 : ℝ))) * (M * K4 ^ (-(1 / 2 : ℝ))) :=
                  mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
              _ = _ := by ring
          · have h := tail_form_le sys x y hy a lE
            obtain ⟨h1, h2⟩ := htail a lE hlam
            refine h.trans ?_
            have hl0 : 0 < lE := by linarith
            have e : lE ^ (-(3 : ℝ)) = lE ^ (-(5 / 2 : ℝ)) * lE ^ (-(1 / 2 : ℝ)) := by
              rw [← Real.rpow_add hl0]; norm_num
            rw [e]
            calc ‖tailMask (gF L) lE a x‖ * ‖tailMask (gF L) lE a y‖
                ≤ (M * lE ^ (-(5 / 2 : ℝ))) * (M * lE ^ (-(1 / 2 : ℝ))) :=
                  mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
              _ = _ := by ring
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

omit [Fintype ν] in
/-- `⟪x, O x⟫ = Σ dsymF |x|²`. -/
lemma inner_Ofull_self (x : L2 eta) :
    ⟪x, Ofull sys L n p₀ x⟫_ℂ = ((∑' q, dsymF sys L n p₀ q * ‖x q‖ ^ 2 : ℝ) : ℂ) := by
  rw [lp.inner_eq_tsum, Complex.ofReal_tsum]
  refine tsum_congr fun q => ?_
  rw [Ofull_apply, RCLike.inner_apply, mul_assoc, RCLike.mul_conj]
  push_cast
  rfl

omit [Fintype ν] in
lemma tailMask_emb (a : Fin eta) (l : ℝ) (v : En eta n) :
    tailMask (gF L) l a (emb eta n v) = emb eta n (regTail L a l v) := by
  ext q
  rw [tailMask_apply]
  by_cases hq : q ∈ fourierConfigCube eta n
  · rcases Finset.mem_image.mp hq with ⟨p, _, rfl⟩
    simp only [emb, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply,
      finiteFourierLpEmbed_apply_index]
    rw [regTail_apply, kabs_eq_lattice]
    change (if l < gF L * Real.sqrt (latticeNormSq (finiteConfigLatticeIndex eta n p a)) then (1 : ℂ)
      else 0) * v.ofLp p = (if l < gF L * Real.sqrt (latticeNormSq (finiteConfigLatticeIndex eta n p a))
        then v.ofLp p else 0)
    split_ifs <;> simp
  · simp only [emb, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply]
    rw [finiteFourierLpEmbed_apply_not_mem_cube eta n _ q hq,
      finiteFourierLpEmbed_apply_not_mem_cube eta n _ q hq, mul_zero]

omit [Fintype ν] in
lemma emb_kin_apply (v : En eta n) (q : Cf eta) :
    emb eta n (FSSpectral.kin (sb eta n) (Asym sys L n) v) q = (Ek sys L q : ℂ) * emb eta n v q := by
  by_cases hq : q ∈ fourierConfigCube eta n
  · rcases Finset.mem_image.mp hq with ⟨p, _, rfl⟩
    simp only [emb, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply,
      finiteFourierLpEmbed_apply_index]
    rw [kin_apply', Asym_eq_Ek]
  · simp only [emb, LinearIsometry.coe_toContinuousLinearMap, finiteFourierLpIsometry_apply]
    rw [finiteFourierLpEmbed_apply_not_mem_cube eta n _ q hq,
      finiteFourierLpEmbed_apply_not_mem_cube eta n _ q hq, mul_zero]

omit [Fintype ν] in
/-- The register tails of a good cube state, on `ℓ²`. -/
lemma cube_tails {M : ℝ} {v : En eta n} (hv : IsGood sys L 1 M v) (a : Fin eta) (l : ℝ) (hl : 1 ≤ l) :
    ‖tailMask (gF L) l a (emb eta n v)‖ ≤ M * l ^ (-(5 / 2 : ℝ)) ∧
    ‖tailMask (gF L) l a (emb eta n (FSSpectral.kin (sb eta n) (Asym sys L n) v))‖ ≤
      M * l ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨h1, h2⟩ := hv.2 a l hl
  rw [one_mul] at h1 h2
  rw [tailMask_emb, norm_emb, tailMask_emb, norm_emb]
  refine ⟨h1, ?_⟩
  rw [← kin_regTail]
  exact (norm_kin_le_wt sys _).trans h2

end FSNormal
