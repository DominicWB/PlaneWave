import PlaneWave.FluxBox.SharedComCases

/-!
# Flux route, stage 3, part 43: the `C × C` block — reduction to trilinear forms

* `Ỹ = Σ_j Ỹ_{ss_j} + Ỹ_r` kernelwise (`ytK_bfcK_split`, `inner_Yt_split`);
* the rest kernel by words (`norm_rK_le`): `|r^{FC}| ≤ Σ_{j₁,j₂} (|Ch3| + |Ch4| + |Ch2'| + [j₂ ≠ j₁](|Ch1| + |Ch2|))`;
* **the rest against the outer potential** (`norm_inner_W_Yr_le`):
  `|⟨W v, Ỹ_r v⟩| ≤ (4/3) Σ_f G(f) ω_F(f) Σ_b |r^{FC}(f,b)| |v_b|`, `G = 1_F Σ_{j₃} |W_{j₃}| |v|`;
* the middle split (`middle_split_le`) and the outer side (`sum_G_sq_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Split

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

omit [Fintype ν] in
lemma kop_add_sum {X : Type*} [Fintype X] {ι : Type*} (s : Finset ι) (κ : ι → X → X → ℂ)
    (κ' : X → X → ℂ) (v : EuclideanSpace ℂ X) :
    FSKernel.kop (fun q p => ∑ i ∈ s, κ i q p + κ' q p) v =
      ∑ i ∈ s, FSKernel.kop (κ i) v + FSKernel.kop κ' v := by
  ext q
  rw [WithLp.ofLp_add, WithLp.ofLp_sum, Pi.add_apply, Finset.sum_apply, FSKernel.kop_apply]
  simp only [FSKernel.kop_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

/-- `ỹ(b^{FC}) = Σ_j ỹ(ss_j) + ỹ(r^{FC})` kernelwise. -/
lemma ytK_bfcK_split (q p : Cfg eta N) :
    ytK sys L N n (bfcK sys L p₀ N n) q p =
      ∑ j, ytK sys L N n (ssK sys L p₀ N n j) q p + ytK sys L N n (rK sys L p₀ N n) q p := by
  have e : bfcK sys L p₀ N n = fun a b => ∑ j, ssK sys L p₀ N n j a b + rK sys L p₀ N n a b := by
    funext a b; unfold rK; ring
  rw [e, ytK_add, ytK_sum]

/-- **The split of the C×C pairing**: `⟨w, Ỹ v⟩ = Σ_j ⟨w, Ỹ_{ss_j} v⟩ + ⟨w, Ỹ_r v⟩`. -/
lemma inner_Yt_split (w v : En eta N) :
    ⟪w, FSKernel.kop (ytK sys L N n (bfcK sys L p₀ N n)) v⟫_ℂ =
      ∑ j, ⟪w, FSKernel.kop (ytK sys L N n (ssK sys L p₀ N n j)) v⟫_ℂ +
        ⟪w, FSKernel.kop (ytK sys L N n (rK sys L p₀ N n)) v⟫_ℂ := by
  have e : ytK sys L N n (bfcK sys L p₀ N n) = fun q p =>
      ∑ j, ytK sys L N n (ssK sys L p₀ N n j) q p + ytK sys L N n (rK sys L p₀ N n) q p := by
    funext q p; exact ytK_bfcK_split q p
  rw [e, kop_add_sum, inner_add_right, inner_sum]

variable (sys L p₀ N n) in
/-- The chain norms of the rest word `(j₂, j₁)`. -/
noncomputable def rwordN (j₂ j₁ : Ch eta) (q p : Cfg eta N) : ℝ :=
  ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q)) (fun d => ¬ InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (yj sys L p₀ N j₁) q p‖ +
    ‖chainK' (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) q p‖ +
    ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) q p‖ +
    (if j₂ = j₁ then 0 else
      ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun d => InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (wj sys L N j₁) q p‖ +
      ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) q p‖)

/-- **The rest kernel by words**. -/
lemma norm_rK_le (hL : 0 < L) (q p : Cfg eta N) :
    ‖rK sys L p₀ N n q p‖ ≤ ∑ j₁, ∑ j₂, rwordN sys L p₀ N n j₂ j₁ q p := by
  classical
  rw [rK_eq hL]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖∑ j₁, ∑ j₂, comK sys L p₀ N n j₂ j₁ q p‖ ≤ ∑ j₁, ∑ j₂,
      (‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q)) (fun d => ¬ InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (yj sys L p₀ N j₁) q p‖ +
      ‖chainK' (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) q p‖ +
      ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) q p‖) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j₁ _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j₂ _ => norm_comK_le j₂ j₁ q p))
  have h2 : ‖∑ j₁, ∑ j₂, (if j₂ = j₁ then 0 else flK sys L p₀ N n j₂ j₁ q p)‖ ≤ ∑ j₁, ∑ j₂,
      (if j₂ = j₁ then 0 else
        ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun d => InP (n : ℝ) (cidx N d))
          (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (wj sys L N j₁) q p‖ +
        ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
          (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
          (wj sys L N j₂) (wj sys L N j₁) q p‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j₁ _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j₂ _ => ?_))
    split_ifs
    · rw [norm_zero]
    · exact norm_flK_le j₂ j₁ q p
  unfold rwordN
  simp only [Finset.sum_add_distrib] at h1 h2 ⊢
  linarith

end Split

/-! ## The rest against the outer potential -/

section Rest

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

omit [Fintype ν] in
/-- `|ỹ(κ)(f,b)| ≤ (4/3) ω_F(f) |κ(f,b)|`. -/
lemma norm_ytK_le (hL : 0 < L) (hn : 1 ≤ n) (κ : Cfg eta N → Cfg eta N → ℂ) (f b : Cfg eta N) :
    ‖ytK sys L N n κ f b‖ ≤ 4 / 3 * farW sys L N n f * ‖κ f b‖ := by
  classical
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfw := farW_nonneg (sys := sys) (L := L) (n := n) f
  unfold ytK
  by_cases hfb : ¬ InQ (n : ℝ) (cidx N f) ∧ InC (n : ℝ) (cst sys) (cidx N b)
  · rw [if_pos hfb]
    have hgap := far_cold_gap' (sys := sys) hL hfb.1 hfb.2
    have hfar := Asym_ge_far (sys := sys) hL hfb.1
    have hA : 0 < Asym sys L N f := lt_of_lt_of_le (by positivity) hfar
    have hd : 0 < Asym sys L N f - Asym sys L N b := by linarith
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    have hw : farW sys L N n f = 1 / Asym sys L N f := by unfold farW; rw [if_neg hfb.1]
    rw [hw]
    have h1 : 1 / (Asym sys L N f - Asym sys L N b) ≤ 4 / 3 * (1 / Asym sys L N f) := by
      rw [div_le_iff₀ hd]
      field_simp
      linarith
    have hk := norm_nonneg (κ f b)
    calc ‖κ f b‖ / (Asym sys L N f - Asym sys L N b) =
        ‖κ f b‖ * (1 / (Asym sys L N f - Asym sys L N b)) := by ring
      _ ≤ ‖κ f b‖ * (4 / 3 * (1 / Asym sys L N f)) := mul_le_mul_of_nonneg_left h1 hk
      _ = 4 / 3 * (1 / Asym sys L N f) * ‖κ f b‖ := by ring
  · rw [if_neg hfb, norm_zero]
    positivity

omit [Fintype ν] in
lemma ytK_eq_zero_of_inQ {κ : Cfg eta N → Cfg eta N → ℂ} {f b : Cfg eta N} (hf : InQ (n : ℝ) (cidx N f)) :
    ytK sys L N n κ f b = 0 := by
  unfold ytK; rw [if_neg (fun h => h.1 hf)]

open Classical in
/-- **The rest of the C×C pairing as a trilinear form**. -/
theorem norm_inner_W_Yr_le (hL : 0 < L) (hn : 1 ≤ n) (v : En eta N) :
    ‖⟪FSKernel.kop (wNK sys L N) v, FSKernel.kop (ytK sys L N n (rK sys L p₀ N n)) v⟫_ℂ‖ ≤
      4 / 3 * ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else
        ∑ j₃, ∑ c, ‖wj sys L N j₃ f c‖ * ‖v.ofLp c‖) * farW sys L N n f *
          ∑ b, ‖rK sys L p₀ N n f b‖ * ‖v.ofLp b‖ := by
  classical
  rw [PiLp.inner_apply, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  rw [RCLike.inner_apply, norm_mul, RCLike.norm_conj]
  by_cases hf : InQ (n : ℝ) (cidx N f)
  · have h0 : (FSKernel.kop (ytK sys L N n (rK sys L p₀ N n)) v).ofLp f = 0 := by
      rw [FSKernel.kop_apply]
      exact Finset.sum_eq_zero fun b _ => by rw [ytK_eq_zero_of_inQ hf, mul_zero]
    rw [h0, norm_zero, zero_mul, if_pos hf]
    simp
  rw [if_neg hf]
  have hW : ‖(FSKernel.kop (wNK sys L N) v).ofLp f‖ ≤ ∑ j₃, ∑ c, ‖wj sys L N j₃ f c‖ * ‖v.ofLp c‖ := by
    rw [FSKernel.kop_apply]
    calc ‖∑ c, v.ofLp c * wNK sys L N f c‖ ≤ ∑ c, ‖v.ofLp c‖ * ‖wNK sys L N f c‖ :=
          (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => norm_mul _ _))
      _ ≤ ∑ c, ‖v.ofLp c‖ * ∑ j₃, ‖wj sys L N j₃ f c‖ := by
          refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [wNK_eq_sum_chPart hL f c]
          exact norm_sum_le _ _
      _ = ∑ j₃, ∑ c, ‖wj sys L N j₃ f c‖ * ‖v.ofLp c‖ := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j₃ _ => Finset.sum_congr rfl fun c _ => ?_
          rw [mul_comm]
  have hY : ‖(FSKernel.kop (ytK sys L N n (rK sys L p₀ N n)) v).ofLp f‖ ≤
      4 / 3 * farW sys L N n f * ∑ b, ‖rK sys L p₀ N n f b‖ * ‖v.ofLp b‖ := by
    rw [FSKernel.kop_apply, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul]
    have := norm_ytK_le (sys := sys) (L := L) hL hn (rK sys L p₀ N n) f b
    calc ‖v.ofLp b‖ * ‖ytK sys L N n (rK sys L p₀ N n) f b‖ ≤
        ‖v.ofLp b‖ * (4 / 3 * farW sys L N n f * ‖rK sys L p₀ N n f b‖) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = 4 / 3 * farW sys L N n f * (‖rK sys L p₀ N n f b‖ * ‖v.ofLp b‖) := by ring
  have hfw := farW_nonneg (sys := sys) (L := L) (n := n) f
  calc ‖(FSKernel.kop (ytK sys L N n (rK sys L p₀ N n)) v).ofLp f‖ *
        ‖(FSKernel.kop (wNK sys L N) v).ofLp f‖ ≤
      (4 / 3 * farW sys L N n f * ∑ b, ‖rK sys L p₀ N n f b‖ * ‖v.ofLp b‖) *
        (∑ j₃, ∑ c, ‖wj sys L N j₃ f c‖ * ‖v.ofLp c‖) :=
        mul_le_mul hY hW (norm_nonneg _) (by
          have := Finset.sum_nonneg fun b (_ : b ∈ Finset.univ) =>
            mul_nonneg (norm_nonneg (rK sys L p₀ N n f b)) (norm_nonneg (v.ofLp b))
          positivity)
    _ = _ := by ring

omit [Fintype ν] in
/-- **The middle split**: `Σ_f G ω_F h ≤ (n Σ G² + n⁵ Σ ω_F² h²)/(2n³)`. -/
lemma middle_split_le {ι : Type*} (s : Finset ι) (G w h : ι → ℝ) (hG : ∀ i, 0 ≤ G i)
    (hw : ∀ i, 0 ≤ w i) (hh : ∀ i, 0 ≤ h i) {m : ℝ} (hm : 0 < m) :
    ∑ i ∈ s, G i * w i * h i ≤
      (m * ∑ i ∈ s, G i ^ 2 + m ^ 5 * ∑ i ∈ s, w i ^ 2 * h i ^ 2) / (2 * m ^ 3) := by
  have hT0 : 0 ≤ ∑ i ∈ s, G i * w i * h i := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (hG i) (hw i)) (hh i)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s G (fun i => w i * h i)
  have e : ∀ i, G i * (w i * h i) = G i * w i * h i := fun i => by ring
  have e2 : ∀ i, (w i * h i) ^ 2 = w i ^ 2 * h i ^ 2 := fun i => by ring
  simp only [e, e2] at hcs
  exact le_of_sq_le_mul hT0 (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hcs hm

open Classical in
/-- **The outer side**: `Σ_f G² ≤ #ch Σ_{j₃} (64 c₃)² (277/n) L²_{j₃}(x)` for `x` on the cold ball. -/
theorem sum_G_sq_le (hL : 0 < L) (hn : 1 ≤ n) (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b)
    (hxC : ∀ b, x b ≠ 0 → InC (n : ℝ) (cst sys) (cidx N b)) :
    ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else ∑ j₃, ∑ c, ‖wj sys L N j₃ f c‖ * x c) ^ 2 ≤
      (Fintype.card (Ch eta) : ℝ) *
        ∑ j₃, (64 * chC sys L j₃) ^ 2 * (277 / n) * lineSq j₃ (fun _ => 1) x := by
  classical
  have hpt : ∀ f, (if InQ (n : ℝ) (cidx N f) then 0 else ∑ j₃, ∑ c, ‖wj sys L N j₃ f c‖ * x c) ^ 2 ≤
      (Fintype.card (Ch eta) : ℝ) * ∑ j₃,
        (if InQ (n : ℝ) (cidx N f) then 0 else ∑ c, ‖wj sys L N j₃ f c‖ * x c) ^ 2 := by
    intro f
    split_ifs
    · simp
    · have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Ch eta)))
        (f := fun j₃ => ∑ c, ‖wj sys L N j₃ f c‖ * x c)
      simpa using this
  refine (Finset.sum_le_sum fun f _ => hpt f).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun j₃ _ => sum_far_G_sq_le (sys := sys) hL hn j₃ x hx hxC

end Rest

end FSFlux
