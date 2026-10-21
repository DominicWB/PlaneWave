import PlaneWave.FluxBox.TrilinearReduction

/-!
# Flux route, stage 3, part 44: the `C × C` block — good-state bounds of the words

For the cold part `x = 1_C |u|` of a good state every line square of the C×C words is bounded by
`B_ψ(C₀) = 125 (log₂ 2N + 2) · 2√2 c_X^{3/2} C₀ · (1+η/2)^{1/2} M² (1 + 2η n_d)` (`good_C_psi`,
`good_C_one`, `good_C_coord`, `good_C_pi`, `good_C_fibre`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section GoodC

variable {sys : CoulombSystem eta ν} {L : ℝ} {N : ℕ}

variable (sys L) in
/-- The good-state bound of a line square with a weight `ψ² ≤ C₀ (1 + E)`. -/
noncomputable def Bpsi (N nd : ℕ) (M C₀ : ℝ) : ℝ :=
  125 * (Nat.log 2 (2 * N) + 2) * (2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * C₀ *
    ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd)))

omit [Fintype ν] in
lemma Bpsi_nonneg (hL : 0 < L) (N nd : ℕ) (M : ℝ) {C₀ : ℝ} (hC : 0 ≤ C₀) : 0 ≤ Bpsi sys L N nd M C₀ := by
  unfold Bpsi
  have := cXw_ge_one (sys := sys) hL
  positivity

omit [Fintype ν] in
lemma Bpsi_mono (hL : 0 < L) (N nd : ℕ) (M : ℝ) {C₀ C₁ : ℝ} (h : C₀ ≤ C₁) :
    Bpsi sys L N nd M C₀ ≤ Bpsi sys L N nd M C₁ := by
  unfold Bpsi
  have := cXw_ge_one (sys := sys) hL
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left h (by positivity)

omit [Fintype ν] in
open Classical in
lemma lineSq_mono_x (j : Ch eta) {Ω : Cf eta → ℝ} (hΩ : ∀ t, 0 ≤ Ω t) {x x' : Cfg eta N → ℝ}
    (hx : ∀ b, 0 ≤ x b) (hxx : ∀ b, x b ≤ x' b) : lineSq j Ω x ≤ lineSq j Ω x' := by
  unfold lineSq
  refine Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_ (hΩ t)
  have h0 : 0 ≤ lineSum j x t := lineSum_nonneg j hx t
  have h1 : lineSum j x t ≤ lineSum j x' t := by
    unfold lineSum
    exact Finset.sum_le_sum fun b _ => hxx b
  exact pow_le_pow_left₀ h0 h1 2

omit [Fintype ν] in
open Classical in
/-- **The cold part of a good state, weight `ψ`**. -/
theorem good_C_psi (hL : 0 < L) (hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) (S : Cfg eta N → Prop) (j : Ch eta)
    (ψ : Cfg eta N → ℝ) (hψ0 : ∀ p, 0 ≤ ψ p) {C₀ : ℝ} (hψ : ∀ p, ψ p ^ 2 ≤ C₀ * (1 + Asym sys L N p)) :
    lineSq j (fun _ => 1) (fun b => ψ b * (if S b then ‖u.ofLp b‖ else 0)) ≤ Bpsi sys L N nd M C₀ := by
  refine (lineSq_mono_x j (fun _ => zero_le_one) (fun b => mul_nonneg (hψ0 b) (by
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl)) (fun b => mul_le_mul_of_nonneg_left (by
      split_ifs
      · exact le_rfl
      · exact norm_nonneg _) (hψ0 b))).trans ?_
  exact lineSq_good_psi_le hL hN hnd hu j ψ hψ

omit [Fintype ν] in
open Classical in
theorem good_C_one (hL : 0 < L) (hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) (S : Cfg eta N → Prop) (j : Ch eta) :
    lineSq j (fun _ => 1) (fun b => if S b then ‖u.ofLp b‖ else 0) ≤ Bpsi sys L N nd M 1 := by
  have h := good_C_psi hL hN hnd hu S j (fun _ => 1) (fun _ => zero_le_one) (C₀ := 1)
    (fun p => by have := Asym_nonneg sys L N p; nlinarith)
  simpa using h

omit [Fintype ν] in
open Classical in
theorem good_C_coord (hL : 0 < L) (hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) (S : Cfg eta N → Prop) (j : Ch eta)
    {A : Finset (Fin eta)} (hAc : A.card ≤ 2) (hAj : ∀ σ, regSum A (tr j σ) = 0) :
    lineSq j (fun s => 1 + FSLattice.lsq (regSum A s)) (fun b => if S b then ‖u.ofLp b‖ else 0) ≤
      Bpsi sys L N nd M (2 * cXw sys L) := by
  set φ : Cf eta → ℝ := fun s => Real.sqrt (1 + FSLattice.lsq (regSum A s)) with hφ
  have hφsq : ∀ s, φ s ^ 2 = 1 + FSLattice.lsq (regSum A s) := fun s =>
    Real.sq_sqrt (by have := FSLattice.lsq_nonneg (regSum A s); linarith)
  have e : lineSq j (fun s => 1 + FSLattice.lsq (regSum A s)) (fun b => if S b then ‖u.ofLp b‖ else 0) =
      lineSq j (fun _ => 1) (fun b => φ (lab N j b) * (if S b then ‖u.ofLp b‖ else 0)) := by
    rw [lineSq_lab_mul]
    congr 1; funext s; rw [hφsq, one_mul]
  rw [e]
  apply good_C_psi hL hN hnd hu S j (fun b => φ (lab N j b)) (fun b => Real.sqrt_nonneg _)
  intro p
  simp only [hφsq]
  rw [regSum_lineLab hAj (cidx N p)]
  have := one_add_lsq_regSum_le (sys := sys) hL hAc p
  linarith

omit [Fintype ν] in
open Classical in
theorem good_C_pi (hL : 0 < L) (hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) (S : Cfg eta N → Prop) (j j' : Ch eta) :
    lineSq j (fun _ => 1) (fun b => piC j' (cidx N b) * (if S b then ‖u.ofLp b‖ else 0)) ≤
      Bpsi sys L N nd M (4 * mmax sys / gF L ^ 2) :=
  good_C_psi hL hN hnd hu S j _ (fun _ => piC_nonneg _ _) (fun p => piC_sq_le hL j' p)

omit [Fintype ν] in
open Classical in
/-- **The fibre weight of a good state**: `Σ_c w32(c_a)(1 + |c_t|²) x_c² ≤ B_ψ(2 c_X)`. -/
theorem good_C_fibre (hL : 0 < L) (_hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) (S : Cfg eta N → Prop) (a t : Fin eta) :
    ∑ c, w32 (cidx N c a) * (1 + FSLattice.lsq (cidx N c t)) * (if S c then ‖u.ofLp c‖ else 0) ^ 2 ≤
      Bpsi sys L N nd M (2 * cXw sys L) := by
  have hcm := crit_moment_box (sys := sys) hL hnd hu
  have hc1 := cXw_ge_one (sys := sys) hL
  set W := 2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * (2 * cXw sys L) with hW
  have hW0 : 0 ≤ W := by positivity
  have hpt : ∀ c, w32 (cidx N c a) * (1 + FSLattice.lsq (cidx N c t)) * (if S c then ‖u.ofLp c‖ else 0) ^ 2 ≤
      W * ((1 + Asym sys L N c) ^ 2 * Real.sqrt (1 + Asym sys L N c) * ‖u.ofLp c‖ ^ 2) := by
    intro c
    have hA : regSum {a} (cidx N c) = cidx N c a := by simp [regSum]
    have hT : regSum {t} (cidx N c) = cidx N c t := by simp [regSum]
    have h1 := one_add_lsq_regSum_le (sys := sys) hL (A := {t}) (by simp) c
    rw [hT] at h1
    have h1' : 1 + FSLattice.lsq (cidx N c t) ≤ 2 * cXw sys L * (1 + Asym sys L N c) := by linarith
    have h2 := weight5_le (sys := sys) hL (A := {a}) (by simp) c
      (add_nonneg zero_le_one (FSLattice.lsq_nonneg _)) h1'
    rw [hA] at h2
    have h3 : (if S c then ‖u.ofLp c‖ else 0) ^ 2 ≤ ‖u.ofLp c‖ ^ 2 := by
      split_ifs
      · exact le_rfl
      · rw [sq, mul_zero]; exact sq_nonneg _
    calc w32 (cidx N c a) * (1 + FSLattice.lsq (cidx N c t)) * (if S c then ‖u.ofLp c‖ else 0) ^ 2 =
        ((1 + FSLattice.lsq (cidx N c t)) * w32 (cidx N c a)) * (if S c then ‖u.ofLp c‖ else 0) ^ 2 := by
          ring
      _ ≤ (W * ((1 + Asym sys L N c) ^ 2 * Real.sqrt (1 + Asym sys L N c))) * ‖u.ofLp c‖ ^ 2 := by
          apply mul_le_mul _ h3 (sq_nonneg _) (by have := Asym_nonneg sys L N c; positivity)
          rw [hW]; linarith
      _ = _ := by ring
  calc ∑ c, w32 (cidx N c a) * (1 + FSLattice.lsq (cidx N c t)) * (if S c then ‖u.ofLp c‖ else 0) ^ 2 ≤
      ∑ c, W * ((1 + Asym sys L N c) ^ 2 * Real.sqrt (1 + Asym sys L N c) * ‖u.ofLp c‖ ^ 2) :=
        Finset.sum_le_sum fun c _ => hpt c
    _ = W * ∑ c, (1 + Asym sys L N c) ^ 2 * Real.sqrt (1 + Asym sys L N c) * ‖u.ofLp c‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ W * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd)) :=
        mul_le_mul_of_nonneg_left hcm hW0
    _ ≤ Bpsi sys L N nd M (2 * cXw sys L) := by
        unfold Bpsi
        rw [← hW]
        have h0 : 0 ≤ W * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd)) := by positivity
        have h1 : (1 : ℝ) ≤ 125 * (Nat.log 2 (2 * N) + 2) := by
          have := Nat.cast_nonneg (α := ℝ) (Nat.log 2 (2 * N)); linarith
        nlinarith

end GoodC

end FSFlux
