import PlaneWave.FreeBoundary.CommutatorTransplant

/-!
# The cut initial state in `D(H_L²)`, part 6: the domain theorem

**The transplanted cut initial state is in `D(H_L²)`, with `L`-free bounds** (non-Born–Oppenheimer:
no clamped nuclei, arbitrary masses `m_i ≥ 1`). Let `H_∞ u = h`, `H_∞ h = k` (weakly), with weak
gradients `∇u = g`, `∇h = g'`, `∂_a g_b = g2 b a`, and `u/|x_i - x_j|`, `g_a/|x_i - x_j|` in `L²`.
For a mass-weighted cutoff `χ` (`DomCutoff`: derivative bound `D`, cancellation constant `C`) in
the retained region and `|C₀| ≤ c₀`, the transplant `φ = T(χ u)` satisfies `H_L φ = h₀`,
`H_L h₀ = h₁` with

`‖φ‖ ≤ N`, `‖h₀‖ ≤ Λ N`, `‖h₁‖ ≤ Λ² N`,

`N = ‖u‖ + ‖h‖ + ‖k‖ + Σ‖∂_a u‖ + Σ‖∂_a h‖ + Σ‖∂_a∂_b u‖ + Σ_{i<j}‖u/|x_i - x_j|‖` and
`Λ = 1 + c₀ + 6 (1 + 3η)² D + C Σ_{i<j} |q_i q_j|`.

* `dataNorm`, `domConst`, `pairWeight`;
* `norm_commTA_le`, `norm_commTB_le`, `norm_commH_le`: bounds for the commutator images;
* **`cut_state_domain`**: the theorem.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15

variable {eta : ℕ}

/-! ## The constants -/

section Constants

/-- The pair weight `Σ_{i<j} |q_i q_j|`. -/
noncomputable def pairWeight (q : Fin eta → ℝ) : ℝ :=
  ∑ p : FiniteElectronPair eta, |q p.1.1 * q p.1.2|

lemma pairWeight_nonneg (q : Fin eta → ℝ) : 0 ≤ pairWeight q :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The free-space data norm
`‖u‖ + ‖h‖ + ‖k‖ + Σ_a ‖g_a‖ + Σ_a ‖g'_a‖ + Σ_{a,b} ‖g2 b a‖ + Σ_{i<j} ‖Y_{ij}‖`. -/
noncomputable def dataNorm (u h k : FreeL2 eta) (g g' : Fin eta × Fin 3 → FreeL2 eta)
    (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
    (Y : FiniteElectronPair eta → FreeL2 eta) : ℝ :=
  ‖u‖ + ‖h‖ + ‖k‖ + ∑ a, ‖g a‖ + ∑ a, ‖g' a‖ + ∑ a, ∑ b, ‖g2 b a‖ + ∑ p, ‖Y p‖

/-- The domain constant `Λ = 1 + c₀ + 6 (1 + 3η)² D + C Σ_{i<j} |q_i q_j|`. -/
noncomputable def domConst (q : Fin eta → ℝ) (c₀ D C : ℝ) : ℝ :=
  1 + c₀ + 6 * (1 + (Fintype.card (Fin eta × Fin 3) : ℝ)) ^ 2 * D + pairWeight q * C

section DataNorm

variable (u h k : FreeL2 eta) (g g' : Fin eta × Fin 3 → FreeL2 eta)
  (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta) (Y : FiniteElectronPair eta → FreeL2 eta)

lemma dataNorm_parts :
    0 ≤ ∑ a, ‖g a‖ ∧ 0 ≤ ∑ a, ‖g' a‖ ∧ 0 ≤ ∑ a, ∑ b, ‖g2 b a‖ ∧ 0 ≤ ∑ p, ‖Y p‖ :=
  ⟨sum_nonneg fun _ _ => norm_nonneg _, sum_nonneg fun _ _ => norm_nonneg _,
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _, sum_nonneg fun _ _ => norm_nonneg _⟩

lemma le_dataNorm_u : ‖u‖ ≤ dataNorm u h k g g' g2 Y := by
  obtain ⟨h1, h2, h3, h4⟩ := dataNorm_parts g g' g2 Y
  unfold dataNorm
  linarith [norm_nonneg h, norm_nonneg k]

lemma le_dataNorm_h : ‖h‖ ≤ dataNorm u h k g g' g2 Y := by
  obtain ⟨h1, h2, h3, h4⟩ := dataNorm_parts g g' g2 Y
  unfold dataNorm
  linarith [norm_nonneg u, norm_nonneg k]

lemma le_dataNorm_k : ‖k‖ ≤ dataNorm u h k g g' g2 Y := by
  obtain ⟨h1, h2, h3, h4⟩ := dataNorm_parts g g' g2 Y
  unfold dataNorm
  linarith [norm_nonneg u, norm_nonneg h]

lemma le_dataNorm_g (a : Fin eta × Fin 3) : ‖g a‖ ≤ dataNorm u h k g g' g2 Y := by
  obtain ⟨h1, h2, h3, h4⟩ := dataNorm_parts g g' g2 Y
  have := Finset.single_le_sum (f := fun a => ‖g a‖) (fun b _ => norm_nonneg _) (Finset.mem_univ a)
  unfold dataNorm
  linarith [norm_nonneg u, norm_nonneg h, norm_nonneg k]

lemma le_dataNorm_g' (a : Fin eta × Fin 3) : ‖g' a‖ ≤ dataNorm u h k g g' g2 Y := by
  obtain ⟨h1, h2, h3, h4⟩ := dataNorm_parts g g' g2 Y
  have := Finset.single_le_sum (f := fun a => ‖g' a‖) (fun b _ => norm_nonneg _)
    (Finset.mem_univ a)
  unfold dataNorm
  linarith [norm_nonneg u, norm_nonneg h, norm_nonneg k]

lemma le_dataNorm_g2 (b a : Fin eta × Fin 3) : ‖g2 b a‖ ≤ dataNorm u h k g g' g2 Y := by
  obtain ⟨h1, h2, h3, h4⟩ := dataNorm_parts g g' g2 Y
  have e1 := Finset.single_le_sum (f := fun b => ‖g2 b a‖) (fun b _ => norm_nonneg _)
    (Finset.mem_univ b)
  have e2 := Finset.single_le_sum (f := fun a => ∑ b, ‖g2 b a‖)
    (fun a _ => sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  unfold dataNorm
  linarith [norm_nonneg u, norm_nonneg h, norm_nonneg k]

lemma le_dataNorm_Y (p : FiniteElectronPair eta) : ‖Y p‖ ≤ dataNorm u h k g g' g2 Y := by
  obtain ⟨h1, h2, h3, h4⟩ := dataNorm_parts g g' g2 Y
  have := Finset.single_le_sum (f := fun p => ‖Y p‖) (fun b _ => norm_nonneg _)
    (Finset.mem_univ p)
  unfold dataNorm
  linarith [norm_nonneg u, norm_nonneg h, norm_nonneg k]

lemma dataNorm_nonneg : 0 ≤ dataNorm u h k g g' g2 Y :=
  (norm_nonneg _).trans (le_dataNorm_u u h k g g' g2 Y)

end DataNorm

end Constants

/-! ## Norm bounds -/

section Norms

lemma norm_kc_le {m : Fin eta → ℝ} (hm : ∀ i, 1 ≤ m i) (a : Fin eta × Fin 3) :
    ‖kc m a‖ ≤ 1 / 2 := by
  have hm0 : 0 < m a.1 := lt_of_lt_of_le one_pos (hm a.1)
  unfold kc
  rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h2]
  have h3 : (m a.1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hm a.1)
  nlinarith

lemma norm_two_kc_le {m : Fin eta → ℝ} (hm : ∀ i, 1 ≤ m i) (a : Fin eta × Fin 3) :
    ‖2 * kc m a‖ ≤ 1 := by
  rw [norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  linarith [norm_kc_le hm a]

lemma norm_sum_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    [Fintype ι] (c : ι → ℂ) (x : ι → E) {α β : ℝ} (hc : ∀ i, ‖c i‖ ≤ α) (hx : ∀ i, ‖x i‖ ≤ β) :
    ‖∑ i, c i • x i‖ ≤ Fintype.card ι * (α * β) := by
  calc ‖∑ i, c i • x i‖ ≤ ∑ i, ‖c i • x i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, α * β := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul (hc i) (hx i) (norm_nonneg _) ((norm_nonneg _).trans (hc i))
    _ = Fintype.card ι * (α * β) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma norm_two_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (x : E) :
    ‖(2 : ℂ) • x‖ = 2 * ‖x‖ := by
  rw [norm_smul]
  norm_num

variable {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m)

lemma DomCutoff.norm_cutL2_D (W : BoxWeight eta L) (hW : W.B = X.D) (f : FreeL2 eta) {β : ℝ}
    (hf : ‖f‖ ≤ β) : ‖W.cutL2 hL f‖ ≤ X.D * β := by
  have := W.norm_cutL2_le hL f
  rw [hW] at this
  exact this.trans (mul_le_mul_of_nonneg_left hf X.D_nonneg)

/-- `‖T([K, χ] f)‖ ≤ 3η · (1/2) · 3 D β` if `‖f‖, ‖G_a‖ ≤ β`. -/
lemma DomCutoff.norm_commT_le' (hm : ∀ i, 1 ≤ m i) (f : FreeL2 eta)
    (G : Fin eta × Fin 3 → FreeL2 eta) {β : ℝ} (hf : ‖f‖ ≤ β) (hG : ∀ a, ‖G a‖ ≤ β) :
    ‖X.toCutoff.commT hL m f G‖ ≤ Fintype.card (Fin eta × Fin 3) * (1 / 2 * (3 * X.D * β)) := by
  have hβ : 0 ≤ β := (norm_nonneg _).trans hf
  rw [commT_eq]
  refine norm_sum_smul_le _ _ (norm_kc_le hm) (fun a => ?_)
  have h1 := X.norm_cutL2_D hL (X.toCutoff.d2W a) rfl f hf
  have h2 := X.norm_cutL2_D hL (X.toCutoff.d1W a) rfl (G a) (hG a)
  refine (norm_add_le _ _).trans ?_
  rw [norm_two_smul]
  linarith

lemma norm_commTA_le (hm : ∀ i, 1 ≤ m i) (u h : FreeL2 eta) (g : Fin eta × Fin 3 → FreeL2 eta)
    (a : Fin eta × Fin 3) {β : ℝ} (hu : ‖u‖ ≤ β) (hh : ‖h‖ ≤ β) (hg : ∀ b, ‖g b‖ ≤ β) :
    ‖commTA hL X u h g a‖ ≤
      X.D * β + Fintype.card (Fin eta × Fin 3) * (1 / 2 * (3 * X.D * β)) := by
  have hβ : 0 ≤ β := (norm_nonneg _).trans hu
  unfold commTA
  refine (norm_add_le _ _).trans (add_le_add (X.norm_cutL2_D hL _ rfl h hh) ?_)
  refine norm_sum_smul_le _ _ (norm_kc_le hm) (fun b => ?_)
  have h1 := X.norm_cutL2_D hL (X.w4 a a b b) rfl u hu
  have h2 := X.norm_cutL2_D hL (X.w3 a a b) rfl (g b) (hg b)
  refine (norm_add_le _ _).trans ?_
  rw [norm_two_smul]
  linarith

lemma norm_commTB_le (hm : ∀ i, 1 ≤ m i) (u : FreeL2 eta) (g g' : Fin eta × Fin 3 → FreeL2 eta)
    (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta) (a : Fin eta × Fin 3) {β : ℝ}
    (hu : ‖u‖ ≤ β) (hg : ∀ b, ‖g b‖ ≤ β) (hg' : ∀ b, ‖g' b‖ ≤ β)
    (hg2 : ∀ b c, ‖g2 b c‖ ≤ β) :
    ‖commTB hL X u g g' g2 a‖ ≤
      X.D * β + Fintype.card (Fin eta × Fin 3) * (1 / 2 * (9 * X.D * β)) := by
  have hβ : 0 ≤ β := (norm_nonneg _).trans hu
  unfold commTB
  refine (norm_add_le _ _).trans (add_le_add (X.norm_cutL2_D hL _ rfl (g' a) (hg' a)) ?_)
  refine norm_sum_smul_le _ _ (norm_kc_le hm) (fun b => ?_)
  set A := (X.w4 a a b b).cutL2 hL u
  set B := (X.w3 a a b).cutL2 hL (g b)
  set C' := (X.w4 a b b a).cutL2 hL u
  set D' := (X.w3 a b b).cutL2 hL (g a)
  set E := (X.w3 a b a).cutL2 hL (g b)
  set F := (X.w2 a b).cutL2 hL (g2 b a)
  have hA : ‖A‖ ≤ X.D * β := X.norm_cutL2_D hL _ rfl u hu
  have hB : ‖B‖ ≤ X.D * β := X.norm_cutL2_D hL _ rfl (g b) (hg b)
  have hC : ‖C'‖ ≤ X.D * β := X.norm_cutL2_D hL _ rfl u hu
  have hD : ‖D'‖ ≤ X.D * β := X.norm_cutL2_D hL _ rfl (g a) (hg a)
  have hE : ‖E‖ ≤ X.D * β := X.norm_cutL2_D hL _ rfl (g b) (hg b)
  have hF : ‖F‖ ≤ X.D * β := X.norm_cutL2_D hL _ rfl (g2 b a) (hg2 b a)
  have t1 := norm_add_le (-A - (2 : ℂ) • B + C' + D' + (2 : ℂ) • E) ((2 : ℂ) • F)
  have t2 := norm_add_le (-A - (2 : ℂ) • B + C' + D') ((2 : ℂ) • E)
  have t3 := norm_add_le (-A - (2 : ℂ) • B + C') D'
  have t4 := norm_add_le (-A - (2 : ℂ) • B) C'
  have t5 := norm_sub_le (-A) ((2 : ℂ) • B)
  rw [norm_neg] at t5
  rw [norm_two_smul] at t1 t2 t5
  linarith

lemma norm_commH_le (hm : ∀ i, 1 ≤ m i) (q : Fin eta → ℝ) (u h : FreeL2 eta)
    (g g' : Fin eta × Fin 3 → FreeL2 eta) (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
    (Y : FiniteElectronPair eta → FreeL2 eta) {β : ℝ}
    (hu : ‖u‖ ≤ β) (hh : ‖h‖ ≤ β) (hg : ∀ b, ‖g b‖ ≤ β) (hg' : ∀ b, ‖g' b‖ ≤ β)
    (hg2 : ∀ b c, ‖g2 b c‖ ≤ β) (hY : ∀ p, ‖Y p‖ ≤ β) :
    ‖commH hL X q u h g g' g2 Y‖ ≤
      Fintype.card (Fin eta × Fin 3) * (1 / 2 *
        (X.D * β + Fintype.card (Fin eta × Fin 3) * (1 / 2 * (3 * X.D * β)))) +
      Fintype.card (Fin eta × Fin 3) * (1 *
        (X.D * β + Fintype.card (Fin eta × Fin 3) * (1 / 2 * (9 * X.D * β)))) +
      pairWeight q * X.C * β := by
  have hβ : 0 ≤ β := (norm_nonneg _).trans hu
  have hD := X.D_nonneg
  unfold commH
  have e1 := norm_sum_smul_le (fun a => kc m a) (fun a => commTA hL X u h g a) (norm_kc_le hm)
    (fun a => norm_commTA_le hL X hm u h g a hu hh hg)
  have e2 := norm_sum_smul_le (fun a => 2 * kc m a) (fun a => commTB hL X u g g' g2 a)
    (norm_two_kc_le hm) (fun a => norm_commTB_le hL X hm u g g' g2 a hu hg hg' hg2)
  have e3 : ‖∑ p : FiniteElectronPair eta, (X.betaW q p).cutL2 hL (Y p)‖ ≤
      pairWeight q * X.C * β := by
    refine (norm_sum_le _ _).trans ?_
    unfold pairWeight
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => ?_
    have := (X.betaW q p).norm_cutL2_le hL (Y p)
    rw [X.betaW_B q p] at this
    refine this.trans (mul_le_mul_of_nonneg_left (hY p) ?_)
    exact mul_nonneg (abs_nonneg _) X.C_nonneg
  have t1 := norm_sub_le (∑ a : Fin eta × Fin 3, kc m a • commTA hL X u h g a +
    ∑ a : Fin eta × Fin 3, (2 * kc m a) • commTB hL X u g g' g2 a)
    (∑ p : FiniteElectronPair eta, (X.betaW q p).cutL2 hL (Y p))
  have t2 := norm_add_le (∑ a : Fin eta × Fin 3, kc m a • commTA hL X u h g a)
    (∑ a : Fin eta × Fin 3, (2 * kc m a) • commTB hL X u g g' g2 a)
  linarith

end Norms

/-! ## The domain theorem -/

section Domain

variable {ν : Type} [Fintype ν]

lemma domConst_bounds {n c₀ D F β : ℝ} (hn : 0 ≤ n) (hc₀ : 0 ≤ c₀) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hβ : 0 ≤ β) :
    (1 + c₀ + n * (1 / 2 * (3 * D))) * β ≤ (1 + c₀ + 6 * (1 + n) ^ 2 * D + F) * β ∧
      (1 + c₀ + n * (1 / 2 * (3 * D)) + c₀ * (1 + c₀ + n * (1 / 2 * (3 * D))) +
        (n * (1 / 2 * (D + n * (1 / 2 * (3 * D)))) + n * (1 * (D + n * (1 / 2 * (9 * D)))) + F) +
        c₀ * (n * (1 / 2 * (3 * D)))) * β ≤ (1 + c₀ + 6 * (1 + n) ^ 2 * D + F) ^ 2 * β := by
  constructor
  · refine mul_le_mul_of_nonneg_right ?_ hβ
    nlinarith [mul_nonneg hn hD, mul_nonneg (mul_nonneg hn hn) hD]
  · refine mul_le_mul_of_nonneg_right ?_ hβ
    have key : (1 + c₀ + 6 * (1 + n) ^ 2 * D + F) ^ 2 -
        (1 + c₀ + n * (1 / 2 * (3 * D)) + c₀ * (1 + c₀ + n * (1 / 2 * (3 * D))) +
          (n * (1 / 2 * (D + n * (1 / 2 * (3 * D)))) + n * (1 * (D + n * (1 / 2 * (9 * D)))) +
            F) + c₀ * (n * (1 / 2 * (3 * D)))) =
        (6 * (1 + n) ^ 2 * D) ^ 2 + F ^ 2 + 2 * (6 * (1 + n) ^ 2 * D) * F + 2 * c₀ * F + F +
          (12 + 21 * n + 27 / 4 * n ^ 2) * D + (12 + 21 * n + 12 * n ^ 2) * c₀ * D := by
      ring
    have hpos : 0 ≤ (6 * (1 + n) ^ 2 * D) ^ 2 + F ^ 2 + 2 * (6 * (1 + n) ^ 2 * D) * F +
        2 * c₀ * F + F + (12 + 21 * n + 27 / 4 * n ^ 2) * D +
        (12 + 21 * n + 12 * n ^ 2) * c₀ * D := by positivity
    linarith

/-- **`φ = T(χ u) ∈ D(H_L²)` with `L`-free bounds** (non-Born–Oppenheimer). Let `H_∞ u = h`,
`H_∞ h = k`, with weak gradients `∇u = g`, `∇h = g'`, `∂_a g_b = g2 b a`, and the Hardy functions
`Y_{ij} = u/|x_i - x_j|`, `Z_{ij,a} = ∂_a u/|x_i - x_j|` in `L²`. For a mass-weighted cutoff `χ` in
the retained region and `|C₀| ≤ c₀`: `H_L φ = h₀`, `H_L h₀ = h₁` with `‖φ‖ ≤ N`, `‖h₀‖ ≤ Λ N`,
`‖h₁‖ ≤ Λ² N` (`N = dataNorm`, `Λ = domConst`). -/
theorem cut_state_domain [IsEmpty ν] (sys : CoulombSystem eta ν) {L R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL : 0 < L) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {u h k : FreeL2 eta} {g g' : Fin eta × Fin 3 → FreeL2 eta}
    {g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta}
    {Y : FiniteElectronPair eta → FreeL2 eta}
    {Z : FiniteElectronPair eta → Fin eta × Fin 3 → FreeL2 eta}
    (hH : HasFreeHamiltonian sys P u h) (hH' : HasFreeHamiltonian sys P h k)
    (hg : HasWeakGrad u g) (hg' : HasWeakGrad h g') (hg2 : ∀ b, HasWeakGrad (g b) (g2 b))
    (hY : ∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * u r)
    (hZ : ∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * g a r)
    {c₀ : ℝ} (hc₀ : ‖zeroModeShift sys L θ‖ ≤ c₀) :
    ∃ h₀ h₁ : MolecularPositionL2 eta,
      HasGLHamiltonian sys L θ (X.toCutoff.chiW.cutL2 hL u) h₀ ∧
      HasGLHamiltonian sys L θ h₀ h₁ ∧
      ‖X.toCutoff.chiW.cutL2 hL u‖ ≤ dataNorm u h k g g' g2 Y ∧
      ‖h₀‖ ≤ domConst sys.charge c₀ X.D X.C * dataNorm u h k g g' g2 Y ∧
      ‖h₁‖ ≤ domConst sys.charge c₀ X.D X.C ^ 2 * dataNorm u h k g g' g2 Y := by
  set C₀ := zeroModeShift sys L θ with hC₀def
  set N := dataNorm u h k g g' g2 Y with hNdef
  -- the relations
  have hdom0 := transplant_hasGLHamiltonian sys hL hR0 hρ hone P hP hpos X.toCutoff hret hH hg
  have hTh := transplant_hasGLHamiltonian sys hL hR0 hρ hone P hP hpos X.toCutoff hret hH' hg'
  have hK : HasFreeWeakKinetic sys.mass u (h - pairL2 sys.charge Y) := by
    obtain ⟨v, hv, hKv⟩ := hH
    have e := hv.unique (hasL2PointwisePotential_pairL2 sys P hY)
    rw [← e]
    exact hKv
  have hC := commT_hasGLHamiltonian sys hL hR0 hρ hone P hP hpos X hret hK hg hg' hg2 hY hZ
  have hdom1 := (hTh.sub sys (hdom0.smul sys C₀)).add sys hC
  refine ⟨_, _, hdom0, hdom1, ?_⟩
  -- the bounds
  have hm := sys.one_le_mass
  have hN := dataNorm_nonneg u h k g g' g2 Y
  have hc0 : 0 ≤ c₀ := (norm_nonneg _).trans hc₀
  have hD := X.D_nonneg
  have bu := le_dataNorm_u u h k g g' g2 Y
  have bh := le_dataNorm_h u h k g g' g2 Y
  have bk := le_dataNorm_k u h k g g' g2 Y
  have bg := le_dataNorm_g u h k g g' g2 Y
  have bg' := le_dataNorm_g' u h k g g' g2 Y
  have bg2 := le_dataNorm_g2 u h k g g' g2 Y
  have bY := le_dataNorm_Y u h k g g' g2 Y
  have hchi : ∀ f : FreeL2 eta, ‖f‖ ≤ N → ‖X.toCutoff.chiW.cutL2 hL f‖ ≤ N := fun f hf => by
    have := X.toCutoff.chiW.norm_cutL2_le hL f
    have e : X.toCutoff.chiW.B = 1 := rfl
    rw [e, one_mul] at this
    exact this.trans hf
  have nφ := hchi u bu
  have nTh := hchi h bh
  have nTk := hchi k bk
  have nCu := X.norm_commT_le' hL hm u g bu bg
  have nCh := X.norm_commT_le' hL hm h g' bh bg'
  have nH := norm_commH_le hL X hm sys.charge u h g g' g2 Y bu bh bg bg' bg2 bY
  have hn : (0 : ℝ) ≤ Fintype.card (Fin eta × Fin 3) := Nat.cast_nonneg _
  have hF : 0 ≤ pairWeight sys.charge * X.C := mul_nonneg (pairWeight_nonneg _) X.C_nonneg
  obtain ⟨k1, k2⟩ := domConst_bounds hn hc0 hD hF hN
  have sm : ∀ x : MolecularPositionL2 eta, ∀ b : ℝ, ‖x‖ ≤ b → ‖C₀ • x‖ ≤ c₀ * b := fun x b hx => by
    rw [norm_smul]
    exact mul_le_mul hc₀ hx (norm_nonneg _) hc0
  -- `‖h₀‖`
  have n0 : ‖X.toCutoff.chiW.cutL2 hL h - C₀ • X.toCutoff.chiW.cutL2 hL u +
      X.toCutoff.commT hL sys.mass u g‖ ≤
      (1 + c₀ + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D))) * N := by
    have t1 := norm_add_le (X.toCutoff.chiW.cutL2 hL h - C₀ • X.toCutoff.chiW.cutL2 hL u)
      (X.toCutoff.commT hL sys.mass u g)
    have t2 := norm_sub_le (X.toCutoff.chiW.cutL2 hL h) (C₀ • X.toCutoff.chiW.cutL2 hL u)
    have t3 := sm _ _ nφ
    have e : (1 + c₀ + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D))) * N =
        N + c₀ * N + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D * N)) := by ring
    rw [e]
    linarith
  refine ⟨nφ, n0.trans (by simpa [domConst] using k1), ?_⟩
  -- `‖h₁‖`
  set h₀ := X.toCutoff.chiW.cutL2 hL h - C₀ • X.toCutoff.chiW.cutL2 hL u +
      X.toCutoff.commT hL sys.mass u g with hh₀
  have t1 := norm_add_le (X.toCutoff.chiW.cutL2 hL k - C₀ • X.toCutoff.chiW.cutL2 hL h +
    X.toCutoff.commT hL sys.mass h g' - C₀ • h₀)
    (commH hL X sys.charge u h g g' g2 Y - C₀ • X.toCutoff.commT hL sys.mass u g)
  have t2 := norm_sub_le (X.toCutoff.chiW.cutL2 hL k - C₀ • X.toCutoff.chiW.cutL2 hL h +
    X.toCutoff.commT hL sys.mass h g') (C₀ • h₀)
  have t3 := norm_add_le (X.toCutoff.chiW.cutL2 hL k - C₀ • X.toCutoff.chiW.cutL2 hL h)
    (X.toCutoff.commT hL sys.mass h g')
  have t4 := norm_sub_le (X.toCutoff.chiW.cutL2 hL k) (C₀ • X.toCutoff.chiW.cutL2 hL h)
  have t5 := norm_sub_le (commH hL X sys.charge u h g g' g2 Y)
    (C₀ • X.toCutoff.commT hL sys.mass u g)
  have s1 := sm _ _ nTh
  have s2 := sm _ _ n0
  have s3 := sm _ _ nCu
  have e : domConst sys.charge c₀ X.D X.C ^ 2 * N =
      (1 + c₀ + 6 * (1 + (Fintype.card (Fin eta × Fin 3) : ℝ)) ^ 2 * X.D +
        pairWeight sys.charge * X.C) ^ 2 * N := rfl
  rw [e]
  refine le_trans ?_ k2
  have e2 : (1 + c₀ + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D)) +
      c₀ * (1 + c₀ + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D))) +
      ((Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (X.D + (Fintype.card (Fin eta × Fin 3) : ℝ) *
        (1 / 2 * (3 * X.D)))) + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 * (X.D +
          (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (9 * X.D)))) +
        pairWeight sys.charge * X.C) +
      c₀ * ((Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D)))) * N =
      N + c₀ * N + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D * N)) +
        c₀ * ((1 + c₀ + (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D))) * N) +
        ((Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (X.D * N +
          (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D * N)))) +
          (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 * (X.D * N +
            (Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (9 * X.D * N)))) +
          pairWeight sys.charge * X.C * N) +
        c₀ * ((Fintype.card (Fin eta × Fin 3) : ℝ) * (1 / 2 * (3 * X.D * N))) := by ring
  rw [e2]
  linarith

end Domain

end FreeBoundary
