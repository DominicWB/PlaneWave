import PlaneWave.Source.TaylorRemainder

/-!
# Flux/source build, block 5: the exact ledger of the retained rotations

Abstract form (any Hilbert space `E`, `FSConj`). Let `H' = A + V + ΔH` with
`ΔH = G + R + H₃ᶠ + D₄` (gapped second-order part, resonant residuals, third-order first-rotation
word, exact remainder), rotate by `Z₂ = Z_b + Z_m` with `[Z₂, A] = -G` and then by `Σ₃` with
`[Σ₃, A] = -(H₃^ret - H₃^res)`, `H₃^ret = [Z_b, V] + H₃ᶠ`. Then (`ledger_identity`)

`e^{Σ₃} e^{Z₂} H' e^{-Z₂} e^{-Σ₃} - (A + V)
   = R + H₃^res + D₄ + [Z_m, V] + [Z₂, ΔH] + R₂(Z₂, H') + [Σ₃, V] + [Σ₃, D₂] + R₂(Σ₃, H₂')`

with `D₂ = e^{Z₂} H' e^{-Z₂} - (A + V)` and the exact second-order Taylor remainders `R₂`;
nothing is counted twice.  `norm_inner_ledger_le` bounds `|⟪ΔH'' u, φ⟫|` term by term: the
residuals `R`, the mixed commutator `[Z_m, V]` and `[Σ₃, V]` through given pairing bounds, every
other term through vector bounds on `u` and operator norms only (the rotated intermediate vector
`e^{-rZ} u` enters only through `norm_cj_sub_tp_apply_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace

namespace FSConj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma cm_add_left (Z Z' X : E →L[ℂ] E) : cm (Z + Z') X = cm Z X + cm Z' X := by
  unfold cm; noncomm_ring

omit [CompleteSpace E] in
lemma cm_add_right (Z X Y : E →L[ℂ] E) : cm Z (X + Y) = cm Z X + cm Z Y := by
  unfold cm; noncomm_ring

omit [CompleteSpace E] in
lemma cm_neg_right (Z X : E →L[ℂ] E) : cm Z (-X) = -cm Z X := by
  unfold cm; noncomm_ring

omit [CompleteSpace E] in
lemma norm_cm_apply_le (Z X : E →L[ℂ] E) (u : E) :
    ‖cm Z X u‖ ≤ ‖Z‖ * ‖X u‖ + ‖X‖ * ‖Z u‖ := by
  unfold cm
  rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp]
  exact (norm_sub_le _ _).trans (add_le_add (Z.le_opNorm _) (X.le_opNorm _))

omit [CompleteSpace E] in
lemma tp_two_one (Z X : E →L[ℂ] E) : tp Z X 2 1 = X + cm Z X := by
  simp [tp, Finset.sum_range_succ, adk_succ]

omit [CompleteSpace E] in
/-- **The exact ledger of the two retained rotations.** -/
theorem ledger_identity (A V dH G R H3f D4 Zb Zm S3 R3 : E →L[ℂ] E)
    (hdH : dH = G + R + H3f + D4) (hA2 : cm (Zb + Zm) A = -G)
    (hA3 : cm S3 A = -(cm Zb V + H3f - R3)) :
    cj S3 1 (cj (Zb + Zm) 1 (A + V + dH)) - (A + V) =
      R + R3 + D4 + cm Zm V + cm (Zb + Zm) dH +
        (cj (Zb + Zm) 1 (A + V + dH) - (A + V + dH) - cm (Zb + Zm) (A + V + dH)) +
        cm S3 V + cm S3 (cj (Zb + Zm) 1 (A + V + dH) - (A + V)) +
        (cj S3 1 (cj (Zb + Zm) 1 (A + V + dH)) - cj (Zb + Zm) 1 (A + V + dH) -
          cm S3 (cj (Zb + Zm) 1 (A + V + dH))) := by
  set H2 := cj (Zb + Zm) 1 (A + V + dH)
  set H3 := cj S3 1 H2
  have h1 : cm S3 H2 = cm S3 A + cm S3 V + cm S3 (H2 - (A + V)) := by unfold cm; noncomm_ring
  have h2 : cm (Zb + Zm) (A + V + dH) =
      cm (Zb + Zm) A + cm Zb V + cm Zm V + cm (Zb + Zm) dH := by unfold cm; noncomm_ring
  rw [h1, h2, hA2, hA3]
  nth_rewrite 2 [hdH]
  abel

/-- The data of the ledger bound: operator norms, vector bounds on `u`, the bound on `‖φ‖` and
the three pairing bounds. -/
structure LedgerData where
  z : ℝ
  z3 : ℝ
  v0 : ℝ
  d0 : ℝ
  g0 : ℝ
  a0 : ℝ
  zb : ℝ
  zu : ℝ
  z3u : ℝ
  vu : ℝ
  du : ℝ
  gu : ℝ
  hfu : ℝ
  r3u : ℝ
  d4u : ℝ
  uu : ℝ
  zbu : ℝ
  f0 : ℝ
  pR : ℝ
  pM : ℝ
  pS : ℝ

namespace LedgerData

/-- The bound on the first remainder `R₂(Z₂, H')` applied to `u`. -/
noncomputable def r2a (D : LedgerData) : ℝ :=
  1 / 2 * (D.z * D.gu + D.g0 * D.zu + 4 * D.z ^ 2 * (D.v0 + D.d0) * D.uu +
    (2 * D.z * D.g0 + 4 * D.z ^ 2 * (D.v0 + D.d0)) * D.zu)

/-- The vector bound for `D₂ u`. -/
noncomputable def d2u (D : LedgerData) : ℝ :=
  D.du + D.gu + (D.z * (D.vu + D.du) + (D.v0 + D.d0) * D.zu) + D.r2a

/-- The operator bound for `D₂`. -/
noncomputable def d2o (D : LedgerData) : ℝ :=
  D.d0 + D.g0 + 2 * D.z * (D.v0 + D.d0) + (2 * D.z * D.g0 + 4 * D.z ^ 2 * (D.v0 + D.d0))

/-- The vector bound for `H₃^gap u`. -/
noncomputable def h3gu (D : LedgerData) : ℝ := D.zb * D.vu + D.v0 * D.zbu + D.hfu + D.r3u

/-- The operator bound for `H₃^gap = [A, Σ₃]`. -/
noncomputable def h3go (D : LedgerData) : ℝ := 2 * D.z3 * D.a0

/-- The bound on the second remainder `R₂(Σ₃, H₂')` applied to `u`. -/
noncomputable def r2b (D : LedgerData) : ℝ :=
  1 / 2 * (D.z3 * D.h3gu + D.h3go * D.z3u + 4 * D.z3 ^ 2 * (D.v0 + D.d2o) * D.uu +
    (2 * D.z3 * D.h3go + 4 * D.z3 ^ 2 * (D.v0 + D.d2o)) * D.z3u)

/-- **The ledger bound.** -/
noncomputable def bound (D : LedgerData) : ℝ :=
  D.pR + D.r3u * D.f0 + D.d4u * D.f0 + D.pM + (D.z * D.du + D.d0 * D.zu) * D.f0 +
    D.r2a * D.f0 + D.pS + (D.z3 * D.d2u + D.d2o * D.z3u) * D.f0 + D.r2b * D.f0

end LedgerData

/-- **The ledger pairing bound.** -/
theorem norm_inner_ledger_le {A V dH G R H3f D4 Zb Zm S3 R3 : E →L[ℂ] E}
    (hdH : dH = G + R + H3f + D4) (hA2 : cm (Zb + Zm) A = -G)
    (hA3 : cm S3 A = -(cm Zb V + H3f - R3))
    (hZ : Zb + Zm ∈ skewAdjoint (E →L[ℂ] E)) (hS3 : S3 ∈ skewAdjoint (E →L[ℂ] E))
    (u φ : E) (D : LedgerData)
    (hz : ‖Zb + Zm‖ ≤ D.z) (hz3 : ‖S3‖ ≤ D.z3) (hv0 : ‖V‖ ≤ D.v0) (hd0 : ‖dH‖ ≤ D.d0)
    (hg0 : ‖G‖ ≤ D.g0) (ha0 : ‖A‖ ≤ D.a0) (hzb : ‖Zb‖ ≤ D.zb)
    (hzu : ‖(Zb + Zm) u‖ ≤ D.zu) (hz3u : ‖S3 u‖ ≤ D.z3u) (hvu : ‖V u‖ ≤ D.vu)
    (hdu : ‖dH u‖ ≤ D.du) (hgu : ‖G u‖ ≤ D.gu) (hhfu : ‖H3f u‖ ≤ D.hfu) (hr3u : ‖R3 u‖ ≤ D.r3u)
    (hd4u : ‖D4 u‖ ≤ D.d4u) (huu : ‖u‖ ≤ D.uu) (hzbu : ‖Zb u‖ ≤ D.zbu) (hf0 : ‖φ‖ ≤ D.f0)
    (hpR : ‖⟪R u, φ⟫_ℂ‖ ≤ D.pR) (hpM : ‖⟪cm Zm V u, φ⟫_ℂ‖ ≤ D.pM)
    (hpS : ‖⟪cm S3 V u, φ⟫_ℂ‖ ≤ D.pS) :
    ‖⟪(cj S3 1 (cj (Zb + Zm) 1 (A + V + dH)) - (A + V)) u, φ⟫_ℂ‖ ≤ D.bound := by
  rw [ledger_identity A V dH G R H3f D4 Zb Zm S3 R3 hdH hA2 hA3]
  set Z := Zb + Zm with hZdef
  set H1 := A + V + dH with hH1
  set H2 := cj Z 1 H1 with hH2
  set D2 := H2 - (A + V) with hD2def
  have hz0 : 0 ≤ D.z := le_trans (norm_nonneg _) hz
  have hz30 : 0 ≤ D.z3 := le_trans (norm_nonneg _) hz3
  have hv00 : 0 ≤ D.v0 := le_trans (norm_nonneg _) hv0
  have hd00 : 0 ≤ D.d0 := le_trans (norm_nonneg _) hd0
  have hg00 : 0 ≤ D.g0 := le_trans (norm_nonneg _) hg0
  have ha00 : 0 ≤ D.a0 := le_trans (norm_nonneg _) ha0
  have hzu0 : 0 ≤ D.zu := le_trans (norm_nonneg _) hzu
  have hz3u0 : 0 ≤ D.z3u := le_trans (norm_nonneg _) hz3u
  have huu0 : 0 ≤ D.uu := le_trans (norm_nonneg _) huu
  have hf00 : 0 ≤ D.f0 := le_trans (norm_nonneg _) hf0
  have hin : ∀ (x : E) (c : ℝ), ‖x‖ ≤ c → ‖⟪x, φ⟫_ℂ‖ ≤ c * D.f0 := by
    intro x c hc
    exact (norm_inner_le_norm _ _).trans (mul_le_mul hc hf0 (norm_nonneg _)
      ((norm_nonneg _).trans hc))
  -- `[Z₂, H'] = -G + [Z₂, V + ΔH]`
  have hcmH1 : cm Z H1 = -G + cm Z (V + dH) := by
    have e : cm Z H1 = cm Z A + cm Z (V + dH) := by rw [hH1]; unfold cm; noncomm_ring
    rw [e, hA2]
  have hVd : ‖V + dH‖ ≤ D.v0 + D.d0 := (norm_add_le _ _).trans (add_le_add hv0 hd0)
  have hcc : ∀ (Y : E →L[ℂ] E) (c : ℝ), ‖Y‖ ≤ c → ‖cm Z (cm Z Y)‖ ≤ 4 * D.z ^ 2 * c := by
    intro Y c hc
    have hc0 : 0 ≤ c := (norm_nonneg _).trans hc
    have h1 : ‖cm Z Y‖ ≤ 2 * D.z * c :=
      (norm_cm_le' _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hz (by norm_num)) hc
        (norm_nonneg _) (by positivity))
    calc ‖cm Z (cm Z Y)‖ ≤ 2 * ‖Z‖ * ‖cm Z Y‖ := norm_cm_le' _ _
      _ ≤ 2 * D.z * (2 * D.z * c) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hz (by norm_num)) h1 (norm_nonneg _) (by positivity)
      _ = 4 * D.z ^ 2 * c := by ring
  -- the second-order commutator of `H'`
  have had2 : adk Z H1 2 = -cm Z G + cm Z (cm Z (V + dH)) := by
    rw [adk_succ, adk_succ, adk_zero, hcmH1, cm_add_right, cm_neg_right]
  have had2u : ‖adk Z H1 2 u‖ ≤ D.z * D.gu + D.g0 * D.zu + 4 * D.z ^ 2 * (D.v0 + D.d0) * D.uu := by
    rw [had2, add_apply, neg_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_neg]
      refine (norm_cm_apply_le _ _ _).trans (add_le_add ?_ ?_)
      · exact mul_le_mul hz hgu (norm_nonneg _) hz0
      · exact mul_le_mul hg0 hzu (norm_nonneg _) hg00
    · exact ((cm Z (cm Z (V + dH))).le_opNorm u).trans
        (mul_le_mul (hcc _ _ hVd) huu (norm_nonneg _) (by positivity))
  have had2o : ‖adk Z H1 2‖ ≤ 2 * D.z * D.g0 + 4 * D.z ^ 2 * (D.v0 + D.d0) := by
    rw [had2]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hcc _ _ hVd))
    rw [norm_neg]
    exact (norm_cm_le' _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hz (by norm_num)) hg0
      (norm_nonneg _) (by positivity))
  have hfac : (1 : ℝ) ^ 2 / ((Nat.factorial 2 : ℕ) : ℝ) = 1 / 2 := by norm_num [Nat.factorial]
  -- the first remainder
  have hR2a : ‖(H2 - H1 - cm Z H1) u‖ ≤ D.r2a := by
    have h := norm_cj_sub_tp_apply_le hZ 2 H1 (r := 1) ⟨zero_le_one, le_rfl⟩ u
    rw [tp_two_one, hfac] at h
    have e : cj Z 1 H1 - (H1 + cm Z H1) = H2 - H1 - cm Z H1 := by rw [hH2]; abel
    rw [e] at h
    refine h.trans ?_
    unfold LedgerData.r2a
    exact mul_le_mul_of_nonneg_left (add_le_add had2u
      (mul_le_mul had2o hzu (norm_nonneg _) (by positivity))) (by norm_num)
  have hR2ao : ‖H2 - H1 - cm Z H1‖ ≤ 2 * D.z * D.g0 + 4 * D.z ^ 2 * (D.v0 + D.d0) := by
    have h := norm_conj_taylor_le hZ H1
    rw [← cj_one] at h
    exact h.trans had2o
  -- `D₂ = ΔH - G + [Z₂, V + ΔH] + R₂`
  have hD2 : D2 = dH + -G + cm Z (V + dH) + (H2 - H1 - cm Z H1) := by
    rw [hD2def, hH1]
    have e : cm Z (A + V + dH) = -G + cm Z (V + dH) := by rw [← hH1]; exact hcmH1
    rw [e]; abel
  have hD2u : ‖D2 u‖ ≤ D.d2u := by
    rw [hD2, add_apply, add_apply, add_apply, neg_apply]
    unfold LedgerData.d2u
    have k1 : ‖cm Z (V + dH) u‖ ≤ D.z * (D.vu + D.du) + (D.v0 + D.d0) * D.zu := by
      refine (norm_cm_apply_le _ _ _).trans (add_le_add ?_ ?_)
      · rw [add_apply]
        exact mul_le_mul hz ((norm_add_le _ _).trans (add_le_add hvu hdu)) (norm_nonneg _) hz0
      · exact mul_le_mul hVd hzu (norm_nonneg _) (by positivity)
    have := norm_add₄_le (a := dH u) (b := -G u) (c := cm Z (V + dH) u)
      (d := (H2 - H1 - cm Z H1) u)
    rw [norm_neg] at this
    linarith
  have hD2o : ‖D2‖ ≤ D.d2o := by
    rw [hD2]
    unfold LedgerData.d2o
    have k1 : ‖cm Z (V + dH)‖ ≤ 2 * D.z * (D.v0 + D.d0) :=
      (norm_cm_le' _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hz (by norm_num)) hVd
        (norm_nonneg _) (by positivity))
    have := norm_add₄_le (a := dH) (b := -G) (c := cm Z (V + dH)) (d := H2 - H1 - cm Z H1)
    rw [norm_neg] at this
    linarith
  have hd2o0 : 0 ≤ D.d2o := (norm_nonneg _).trans hD2o
  -- the third-order gapped part `H₃^gap = -[Σ₃, A]`
  have hH3gu : ‖(cm Zb V + H3f - R3) u‖ ≤ D.h3gu := by
    unfold LedgerData.h3gu
    rw [sub_apply, add_apply]
    have k1 : ‖cm Zb V u‖ ≤ D.zb * D.vu + D.v0 * D.zbu := by
      refine (norm_cm_apply_le _ _ _).trans (add_le_add ?_ ?_)
      · exact mul_le_mul hzb hvu (norm_nonneg _) ((norm_nonneg _).trans hzb)
      · exact mul_le_mul hv0 hzbu (norm_nonneg _) hv00
    have := norm_sub_le (cm Zb V u + H3f u) (R3 u)
    have := norm_add_le (cm Zb V u) (H3f u)
    linarith
  have hH3go : ‖cm Zb V + H3f - R3‖ ≤ D.h3go := by
    have e : cm Zb V + H3f - R3 = -cm S3 A := by rw [hA3, neg_neg]
    rw [e, norm_neg]
    unfold LedgerData.h3go
    exact (norm_cm_le' _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hz3 (by norm_num)) ha0
      (norm_nonneg _) (by positivity))
  have hh3go0 : 0 ≤ D.h3go := (norm_nonneg _).trans hH3go
  -- the second-order commutator of `H₂'` under `Σ₃`
  have hcmH2 : cm S3 H2 = -(cm Zb V + H3f - R3) + cm S3 (V + D2) := by
    have e : cm S3 H2 = cm S3 A + cm S3 (V + D2) := by rw [hD2def]; unfold cm; noncomm_ring
    rw [e, hA3]
  have hVD2 : ‖V + D2‖ ≤ D.v0 + D.d2o := (norm_add_le _ _).trans (add_le_add hv0 hD2o)
  have hcc3 : ∀ (Y : E →L[ℂ] E) (c : ℝ), ‖Y‖ ≤ c → ‖cm S3 (cm S3 Y)‖ ≤ 4 * D.z3 ^ 2 * c := by
    intro Y c hc
    have hc0 : 0 ≤ c := (norm_nonneg _).trans hc
    have h1 : ‖cm S3 Y‖ ≤ 2 * D.z3 * c :=
      (norm_cm_le' _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hz3 (by norm_num)) hc
        (norm_nonneg _) (by positivity))
    calc ‖cm S3 (cm S3 Y)‖ ≤ 2 * ‖S3‖ * ‖cm S3 Y‖ := norm_cm_le' _ _
      _ ≤ 2 * D.z3 * (2 * D.z3 * c) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hz3 (by norm_num)) h1 (norm_nonneg _) (by positivity)
      _ = 4 * D.z3 ^ 2 * c := by ring
  have hadb : adk S3 H2 2 = -cm S3 (cm Zb V + H3f - R3) + cm S3 (cm S3 (V + D2)) := by
    rw [adk_succ, adk_succ, adk_zero, hcmH2, cm_add_right, cm_neg_right]
  have hadbu : ‖adk S3 H2 2 u‖ ≤ D.z3 * D.h3gu + D.h3go * D.z3u +
      4 * D.z3 ^ 2 * (D.v0 + D.d2o) * D.uu := by
    rw [hadb, add_apply, neg_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_neg]
      refine (norm_cm_apply_le _ _ _).trans (add_le_add ?_ ?_)
      · exact mul_le_mul hz3 hH3gu (norm_nonneg _) hz30
      · exact mul_le_mul hH3go hz3u (norm_nonneg _) hh3go0
    · exact ((cm S3 (cm S3 (V + D2))).le_opNorm u).trans
        (mul_le_mul (hcc3 _ _ hVD2) huu (norm_nonneg _) (by positivity))
  have hadbo : ‖adk S3 H2 2‖ ≤ 2 * D.z3 * D.h3go + 4 * D.z3 ^ 2 * (D.v0 + D.d2o) := by
    rw [hadb]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hcc3 _ _ hVD2))
    rw [norm_neg]
    exact (norm_cm_le' _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hz3 (by norm_num)) hH3go
      (norm_nonneg _) (by positivity))
  have hR2b : ‖(cj S3 1 H2 - H2 - cm S3 H2) u‖ ≤ D.r2b := by
    have h := norm_cj_sub_tp_apply_le hS3 2 H2 (r := 1) ⟨zero_le_one, le_rfl⟩ u
    rw [tp_two_one, hfac] at h
    have e : cj S3 1 H2 - (H2 + cm S3 H2) = cj S3 1 H2 - H2 - cm S3 H2 := by abel
    rw [e] at h
    refine h.trans ?_
    unfold LedgerData.r2b
    exact mul_le_mul_of_nonneg_left (add_le_add hadbu
      (mul_le_mul hadbo hz3u (norm_nonneg _) (by positivity))) (by norm_num)
  -- assemble
  simp only [add_apply, inner_add_left]
  have key : ∀ x1 x2 x3 x4 x5 x6 x7 x8 x9 : ℂ, ‖x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9‖ ≤
      ‖x1‖ + ‖x2‖ + ‖x3‖ + ‖x4‖ + ‖x5‖ + ‖x6‖ + ‖x7‖ + ‖x8‖ + ‖x9‖ := by
    intro x1 x2 x3 x4 x5 x6 x7 x8 x9
    have h1 := norm_add_le x1 x2
    have h2 := norm_add_le (x1 + x2) x3
    have h3 := norm_add_le (x1 + x2 + x3) x4
    have h4 := norm_add_le (x1 + x2 + x3 + x4) x5
    have h5 := norm_add_le (x1 + x2 + x3 + x4 + x5) x6
    have h6 := norm_add_le (x1 + x2 + x3 + x4 + x5 + x6) x7
    have h7 := norm_add_le (x1 + x2 + x3 + x4 + x5 + x6 + x7) x8
    have h8 := norm_add_le (x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8) x9
    linarith
  refine (key _ _ _ _ _ _ _ _ _).trans ?_
  have k1 := hin _ _ hr3u
  have k2 := hin _ _ hd4u
  have k3 := hin _ _ ((norm_cm_apply_le Z dH u).trans (add_le_add (mul_le_mul hz hdu (norm_nonneg _) hz0)
      (mul_le_mul hd0 hzu (norm_nonneg _) hd00)))
  have k4 := hin _ _ hR2a
  have k5 := hin _ _ ((norm_cm_apply_le S3 D2 u).trans (add_le_add (mul_le_mul hz3 hD2u (norm_nonneg _) hz30)
      (mul_le_mul hD2o hz3u (norm_nonneg _) hd2o0)))
  have k6 := hin _ _ hR2b
  unfold LedgerData.bound
  linarith

end FSConj
