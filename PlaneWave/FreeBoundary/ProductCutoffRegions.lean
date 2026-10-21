import PlaneWave.FreeBoundary.ProductCutoffCancellation

/-!
# Clamped nuclei, part 9: the regions of the product cutoff and its scaling

The leakage regions of the product cutoff `χ = Π_i q(x_i)`: `χ = 1` on
`B¹ = {every |x_i| < 1}`, and `χ` and its first derivatives are locally constant off the shell
`S¹ = {some |x_i| ≥ 1, every |x_i| ≤ 2}`; `χ ≠ 0` only where every `|x_i| < 2`. Scaled by `s`
(`DomCutoff.scale`), it is flat near nuclei with `|P_ℓ| + δ ≤ s`.

* `prodChi_one`, `prodChi_dS`, `prodChi_ret`, `measurableSet_prodOne`, `measurableSet_prodShell`;
* **`scale_isFlatNear`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

variable {eta : ℕ}

/-- `B¹ = {every |x_i| < 1}`. -/
def prodOne : Set (Rcfg eta) := {r | ∀ i, ‖particle r i‖ < 1}

/-- `S¹ = {some |x_i| ≥ 1, every |x_i| ≤ 2}`. -/
def prodShell : Set (Rcfg eta) := {r | (∃ i, 1 ≤ ‖particle r i‖) ∧ ∀ i, ‖particle r i‖ ≤ 2}

lemma isOpen_prodOne : IsOpen (prodOne (eta := eta)) := by
  have h : (prodOne (eta := eta)) = ⋂ i, {r | ‖particle r i‖ < 1} := by
    ext r
    simp [prodOne]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_norm_particle i) continuous_const

lemma measurableSet_prodOne : MeasurableSet (prodOne (eta := eta)) :=
  isOpen_prodOne.measurableSet

lemma measurableSet_prodShell : MeasurableSet (prodShell (eta := eta)) := by
  have h : (prodShell (eta := eta)) =
      (⋃ i, {r | 1 ≤ ‖particle r i‖}) ∩ ⋂ i, {r | ‖particle r i‖ ≤ 2} := by
    ext r
    simp [prodShell]
  rw [h]
  exact (MeasurableSet.iUnion fun i => measurableSet_le measurable_const
    (continuous_norm_particle i).measurable).inter
    (MeasurableSet.iInter fun i => measurableSet_le (continuous_norm_particle i).measurable
      measurable_const)

lemma prodShell_subset : prodShell (eta := eta) ⊆ (prodOne (eta := eta))ᶜ := by
  intro r hr h
  obtain ⟨⟨i, hi⟩, -⟩ := hr
  exact absurd (h i) (not_lt.mpr hi)

lemma prodChi_one {r : Rcfg eta} (hr : r ∈ prodOne (eta := eta)) : prodChi r = 1 := by
  unfold prodChi
  refine Finset.prod_eq_one fun i _ => bumpQ.one_of_mem_closedBall ?_
  rw [mem_closedBall_zero_iff]
  exact (hr i).le

lemma prodChi_ret {r : Rcfg eta} (h : prodChi r ≠ 0) (i : Fin eta) : ‖particle r i‖ ≤ 2 :=
  (norm_particle_lt_of_prodChi_ne h i).le

lemma bumpQ_zero {x : E3} (hx : 2 ≤ ‖x‖) : bumpQ x = 0 := by
  have : x ∉ Function.support (bumpQ : E3 → ℝ) := by
    rw [bumpQ.support_eq]
    simpa [bumpQ] using hx
  simpa using this

/-- **The derivatives vanish off the shell**: `χ` is locally constant there. -/
lemma prodChi_dS {r : Rcfg eta} (hr : r ∉ prodShell (eta := eta)) (a : Fin eta × Fin 3) :
    dirD a (prodChi (eta := eta)) r = 0 ∧ dirD a (dirD a (prodChi (eta := eta))) r = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, (prodChi (eta := eta)) =ᶠ[𝓝 r] fun _ => c := by
    by_cases h1 : r ∈ prodOne (eta := eta)
    · exact ⟨1, Filter.eventually_of_mem (isOpen_prodOne.mem_nhds h1)
        fun r' hr' => prodChi_one hr'⟩
    · have h2 : ∃ k, 2 < ‖particle r k‖ := by
        by_contra hcon
        push Not at hcon
        apply hr
        refine ⟨?_, hcon⟩
        by_contra hcon2
        push Not at hcon2
        exact h1 hcon2
      obtain ⟨k, hk⟩ := h2
      refine ⟨0, Filter.eventually_of_mem
        ((continuous_norm_particle k).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hk))
        fun r' hr' => ?_⟩
      unfold prodChi
      exact Finset.prod_eq_zero (Finset.mem_univ k) (bumpQ_zero (le_of_lt hr'))
  have h1 := dirD_eventually_zero hc a
  exact ⟨h1.self_of_nhds, (dirD_eventually_zero h1 a).self_of_nhds⟩

namespace DomCutoff

variable {L : ℝ} {m : Fin eta → ℝ} (X : DomCutoff eta L m) {s : ℝ} (hs : 1 ≤ s)

/-- **The scaled product cutoff is flat near nuclei with `|P_ℓ| + δ ≤ s`.** -/
theorem scale_isFlatNear (hX : ∀ r, X.χ r = prodChi r) {ν : Type} (P : ν → E3) {δ : ℝ}
    (hP : ∀ l, ‖P l‖ + δ ≤ s) : IsFlatNear (X.scale hs).χ P δ := by
  intro r i l hr c
  have hs0 : 0 < s := by linarith
  change dirD (i, c) (fun r => X.χ (s⁻¹ • r)) r = 0
  rw [X.scale_d1 s⁻¹ (i, c)]
  beta_reduce
  have hχ : X.χ = prodChi := funext hX
  rw [hχ]
  have hlt : ‖particle (s⁻¹ • r) i‖ < 1 := by
    rw [particle_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0),
      inv_mul_lt_iff₀ hs0, mul_one]
    calc ‖particle r i‖ = ‖(particle r i - P l) + P l‖ := by rw [sub_add_cancel]
      _ ≤ ‖particle r i - P l‖ + ‖P l‖ := norm_add_le _ _
      _ < δ + ‖P l‖ := by linarith
      _ ≤ s := by linarith [hP l]
  rw [dirD_prodChi_flat hlt c, mul_zero]

end DomCutoff

end FreeBoundary
