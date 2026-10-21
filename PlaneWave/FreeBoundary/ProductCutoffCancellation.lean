import PlaneWave.FreeBoundary.ProductCutoff

/-!
# Clamped nuclei, part 8: the product cutoff as a mass-weighted cutoff

For equal masses `m_i = m₀ ≥ 1`, `χ = Π_i q(x_i)` (`prodChi`) is a `DomCutoff` at `L ≥ 8`. The
cancellation: `φ = ∂_{(i,c)}χ - ∂_{(j,c)}χ` vanishes where `x_i = x_j` (exchange symmetry), and
`φ` is `K`-Lipschitz (a compactly supported `C³` function), so at the configuration `r'` with
`x_i, x_j` both replaced by their midpoint, `|φ(r)| = |φ(r) - φ(r')| ≤ K ‖r - r'‖ ≤ K |x_i - x_j|`;
`C = 3K`.

* `norm_E3_le_sum`, `abs_sub_coord_le`;
* **`exists_prodCutoff`**: `∃ X : DomCutoff eta L m, X.χ = prodChi` for `L ≥ 8`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology NNReal
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

variable {eta : ℕ}

lemma norm_E3_le_sum (v : E3) : ‖v‖ ≤ ∑ c : Fin 3, |v c| := by
  have h0 : 0 ≤ ∑ c : Fin 3, |v c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).mp ?_
  rw [norm_sq_E3, Fin.sum_univ_three, Fin.sum_univ_three]
  have a0 := abs_nonneg (v 0)
  have a1 := abs_nonneg (v 1)
  have a2 := abs_nonneg (v 2)
  nlinarith [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2), mul_nonneg a0 a1, mul_nonneg a0 a2,
    mul_nonneg a1 a2]

lemma abs_sub_coord_le (r : Rcfg eta) (i j : Fin eta) (d : Fin 3) :
    |r (i, d) - r (j, d)| ≤ ‖particle r i - particle r j‖ := by
  have h2 : ((particle r i - particle r j) d) ^ 2 ≤ ‖particle r i - particle r j‖ ^ 2 := by
    rw [norm_sq_E3]
    exact Finset.single_le_sum (f := fun e : Fin 3 => ((particle r i - particle r j) e) ^ 2)
      (fun e _ => sq_nonneg _) (Finset.mem_univ d)
  have e : (particle r i - particle r j) d = r (i, d) - r (j, d) := rfl
  rw [e] at h2
  exact (sq_le_sq.mp h2).trans (le_of_eq (abs_of_nonneg (norm_nonneg _)))

/-- The configuration with `x_i`, `x_j` both replaced by their midpoint. -/
noncomputable def midCfg (i j : Fin eta) (r : Rcfg eta) : Rcfg eta :=
  fun a => if a.1 = i ∨ a.1 = j then (r (i, a.2) + r (j, a.2)) / 2 else r a

lemma particle_midCfg (i j : Fin eta) (r : Rcfg eta) :
    particle (midCfg i j r) i = particle (midCfg i j r) j := by
  ext d
  change midCfg i j r (i, d) = midCfg i j r (j, d)
  unfold midCfg
  simp

lemma norm_sub_midCfg_le (i j : Fin eta) (r : Rcfg eta) :
    ‖r - midCfg i j r‖ ≤ ‖particle r i - particle r j‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun a => ?_
  obtain ⟨k, d⟩ := a
  have hb := abs_sub_coord_le r i j d
  rw [Pi.sub_apply, Real.norm_eq_abs]
  unfold midCfg
  by_cases hk : k = i ∨ k = j
  · rw [if_pos hk]
    rcases hk with rfl | rfl
    · rw [show r (k, d) - (r (k, d) + r (j, d)) / 2 = (r (k, d) - r (j, d)) / 2 by ring, abs_div,
        abs_two]
      linarith [abs_nonneg (r (k, d) - r (j, d))]
    · rw [show r (k, d) - (r (i, d) + r (k, d)) / 2 = -((r (i, d) - r (k, d)) / 2) by ring,
        abs_neg, abs_div, abs_two]
      linarith [abs_nonneg (r (i, d) - r (k, d))]
  · rw [if_neg hk, sub_self, abs_zero]
    exact norm_nonneg _

/-- **The product cutoff is a mass-weighted cutoff at every `L ≥ 8`** for equal masses
`m₀ ≥ 1`. -/
theorem exists_prodCutoff (m : Fin eta → ℝ) {m₀ : ℝ} (hm : ∀ i, m i = m₀) (hm0 : 1 ≤ m₀)
    {L : ℝ} (hL : 8 ≤ L) : ∃ X : DomCutoff eta L m, ∀ r, X.χ r = prodChi r := by
  have hsm : ContDiff ℝ 4 (prodChi (eta := eta)) := contDiff_prodChi
  have hbox : ∀ r : Rcfg eta, prodChi r ≠ 0 → ∀ a, |r a| ≤ L / 4 := by
    intro r hr a
    have h1 := norm_particle_lt_of_prodChi_ne hr a.1
    have h2 := abs_coord_le_norm_particle r a.1 a.2
    linarith
  have hcs : HasCompactSupport (prodChi (eta := eta)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rcfg eta) 2) fun r hr => ?_
    by_contra hne
    apply hr
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro a
    rw [Real.norm_eq_abs]
    have h1 := norm_particle_lt_of_prodChi_ne hne a.1
    have h2 := abs_coord_le_norm_particle r a.1 a.2
    linarith
  obtain ⟨D, hD0, d1, d2, d3, d4⟩ := exists_chain_bound hsm hcs
  -- the Lipschitz constant of the differences
  have hc1 : ∀ a, ContDiff ℝ 3 (dirD a (prodChi (eta := eta))) := fun a =>
    contDiff_dirD_nat (n := 3) hsm a
  have hcs1 : ∀ a, HasCompactSupport (dirD a (prodChi (eta := eta))) := fun a =>
    (hasCompactSupport_chain hcs subset_rfl a).1
  obtain ⟨K, hK0, hK⟩ := exists_lipschitz_family
    (f := fun ijc : Fin eta × Fin eta × Fin 3 => fun r =>
      dirD (ijc.1, ijc.2.2) (prodChi (eta := eta)) r - dirD (ijc.2.1, ijc.2.2) prodChi r)
    (fun ijc => ((hc1 _).sub (hc1 _)).of_le (by norm_num))
    (fun ijc => (hcs1 _).sub (hcs1 _))
  have hdiff : Differentiable ℝ (prodChi (eta := eta)) := hsm.differentiable (by norm_num)
  have hzero : ∀ (i j : Fin eta) (c : Fin 3) (r : Rcfg eta), particle r i = particle r j →
      dirD (i, c) (prodChi (eta := eta)) r - dirD (j, c) prodChi r = 0 := by
    intro i j c r h
    rw [dirD_swap_sym hdiff (prodChi_freeSwap i j) c r, freeSwap_eq_self h, sub_self]
  have hm0' : 0 < m₀ := lt_of_lt_of_le one_pos hm0
  refine ⟨{ χ := prodChi
            smooth := hsm
            nonneg := prodChi_nonneg
            le_one := prodChi_le_one
            box := hbox
            D := D
            D_nonneg := hD0
            d1 := d1
            d2 := d2
            d3 := d3
            d4 := d4
            C := 3 * K
            C_nonneg := by positivity
            cancel := fun r i j => ?_ }, fun r => rfl⟩
  have hφ : ∀ c : Fin 3, |dirD (i, c) (prodChi (eta := eta)) r - dirD (j, c) prodChi r| ≤
      K * ‖particle r i - particle r j‖ := by
    intro c
    have h1 := hK (i, j, c) r (midCfg i j r)
    have h0 := hzero i j c (midCfg i j r) (particle_midCfg i j r)
    simp only at h1
    rw [h0, sub_zero] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (norm_sub_midCfg_le i j r) hK0)
  refine (norm_E3_le_sum _).trans ?_
  have e : ∀ c : Fin 3, (massGrad m prodChi i r - massGrad m prodChi j r) c =
      m₀⁻¹ * (dirD (i, c) (prodChi (eta := eta)) r - dirD (j, c) prodChi r) := by
    intro c
    change massGrad m prodChi i r c - massGrad m prodChi j r c = _
    rw [massGrad_apply, massGrad_apply, hm i, hm j]
    ring
  simp_rw [e]
  have hinv : m₀⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm0
  calc ∑ c : Fin 3, |m₀⁻¹ * (dirD (i, c) (prodChi (eta := eta)) r - dirD (j, c) prodChi r)|
      ≤ ∑ _c : Fin 3, K * ‖particle r i - particle r j‖ := Finset.sum_le_sum fun c _ => by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hm0')]
        calc m₀⁻¹ * |dirD (i, c) (prodChi (eta := eta)) r - dirD (j, c) prodChi r|
            ≤ 1 * |dirD (i, c) (prodChi (eta := eta)) r - dirD (j, c) prodChi r| :=
              mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
          _ ≤ K * ‖particle r i - particle r j‖ := by rw [one_mul]; exact hφ c
    _ = 3 * K * ‖particle r i - particle r j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end FreeBoundary
