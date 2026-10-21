import PlaneWave.Flux.FluxDressing

/-!
# Flux route, part 3: the exact split of `thm:flux2` and its assembly

* `Vb_split`: `V_b S w = R W(1_Q w) + 1_Q W(R w)` (the bulk-fed crossings of the potential);
* **`Gb_eq`**: `G_b(w, w) = 𝔊(δ, 1_Q w) + 𝔊(1_Q w, δ) = 2 Re 𝔊(δ, 1_Q w)`, `δ = R w`;
* **`flux2_split`** (the corrected split of `thm:flux2`, with `1 - Q = U_{K/4}`):
  `𝔊(w, w) - 𝔊(P w, P w) = G_nc(w) + G_b(w, w)`, `G_nc = 𝔊(δ, δ) + 2 Re 𝔊(δ, U_{K/4} P w)`;
* `flux_nc_gen` (`thm:flux` at a general threshold `λ = g m/4 ≥ 1`):
  `|𝔊(δ, U_λ P w)| ≤ √3 C_m η² M² (K^{-3/2} λ^{-1/2} + K^{-1/2} λ^{-3/2})`, and **`flux_nc4`**
  (`λ = K/4`): `|G_nc(w)| ≤ C M² K^{-2}`;
* `continuous_traj` (the exact trajectory is continuous in `H²`), and
* **`thm_flux2_of_phase`**: the assembly of `thm:flux2` from a phase bound
  `|𝔚(w_s, w_s)| ≤ C_φ Ξ² K^{-2+ε}` (`prop:phase`):
  `|∫₀ᵗ (𝔊(ψ, ψ) - 𝔊(Pψ, Pψ))| ≤ C Ξ² (K^{-3} + t K^{-2+ε})`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Split

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta) {n : ℕ}

omit [Fintype ν] in
lemma inner_eq_of_pt' (x x' v v' : L2 eta) (h : ∀ q, ⟪x q, v q⟫_ℂ = ⟪x' q, v' q⟫_ℂ) :
    ⟪x, v⟫_ℂ = ⟪x', v'⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  exact tsum_congr h

omit [Fintype ν] in
lemma stateMap_sub_trunc_apply (w : MolecularFourierH2 eta) (q : Cf eta) :
    Sm eta L (w - molecularH2Truncate n w) q =
      if q ∈ fourierConfigCube eta n then 0 else Sm eta L w q := by
  rw [map_sub, Sm, stateMap_truncate, lp.coeFn_sub, Pi.sub_apply, molecularH2Truncate_apply]
  split_ifs with hq
  · rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hq, sub_self]
  · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq, sub_zero]

omit [Fintype ν] in
lemma Ap_apply' (u : MolecularFourierH2 eta) (q : Cf eta) :
    Ap sys L p₀ u q = (regSymbol sys (gF L) p₀ q : ℂ) * Sm eta L u q := by
  rw [Ap, KinMult.h2_apply, Sm, molecularH2StateMap_apply]
  rfl

open Classical in
include hKernel in
/-- **`V_b = R W Q + Q W R`** on a state: `V_b S w = R W(1_Q w) + 1_Q W(R w)`. -/
theorem Vb_split (w : MolecularFourierH2 eta) :
    Vb sys L n hL (Sm eta L w) =
      (Wp sys L H (liftQ L n (Sm eta L w)) -
          molecularH2Truncate n (Wp sys L H (liftQ L n (Sm eta L w)))) +
        lpTruncate (Qs eta n) (Wp sys L H (w - molecularH2Truncate n w)) := by
  set x := Sm eta L w
  have hsub : Qs eta n ⊆ fourierConfigCube eta n := Qs_subset_cube (by omega)
  ext q
  rw [Vb_apply, lp.coeFn_add, Pi.add_apply, lp.coeFn_sub, Pi.sub_apply, molecularH2Truncate_apply,
    lpTruncate_apply]
  by_cases hqQ : q ∈ Qs eta n
  · -- `q ∈ Q`: only the second term, with `p ∉ P`
    have hqP : q ∈ fourierConfigCube eta n := hsub hqQ
    rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hqP, sub_self, zero_add, if_pos hqQ]
    have hW := potential_apply sys L H hKernel hL (w - molecularH2Truncate n w) q
    change _ = Wp sys L H (w - molecularH2Truncate n w) q
    rw [show Wp sys L H (w - molecularH2Truncate n w) q =
      coulombFourierPotentialH2 sys (2 * Real.pi / L) H (w - molecularH2Truncate n w) q from rfl, hW]
    refine tsum_congr fun p => ?_
    rw [← molecularH2StateMap_apply]
    change _ = Sm eta L (w - molecularH2Truncate n w) p * _
    rw [stateMap_sub_trunc_apply]
    unfold FSNormal.vbK
    have hiff : Cross (n : ℝ) q p ↔ p ∉ fourierConfigCube eta n := by
      rw [← inP_iff_mem_cube]
      constructor
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h
        · exact absurd ((mem_Qs.mp hqQ).inP (Nat.cast_nonneg n)) h
      · intro h; exact Or.inl ⟨mem_Qs.mp hqQ, h⟩
    by_cases hp : p ∈ fourierConfigCube eta n
    · rw [if_neg (fun h => (hiff.mp h) hp), if_pos hp]; ring
    · rw [if_pos (hiff.mpr hp), if_neg hp]; ring
  · rw [if_neg hqQ, add_zero]
    by_cases hqP : q ∈ fourierConfigCube eta n
    · -- `q ∈ P \ Q`: no crossing
      rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hqP, sub_self]
      have hqP' : InP (n : ℝ) q := (inP_iff_mem_cube n q).mpr hqP
      refine (tsum_congr fun p => ?_).trans tsum_zero
      unfold FSNormal.vbK
      rw [if_neg]
      · ring
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact hqQ (mem_Qs.mpr h)
        · exact h hqP'
    · -- `q ∉ P`: only the first term, with `p ∈ Q`
      rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hqP, sub_zero]
      have hqP' : ¬ InP (n : ℝ) q := fun h => hqP ((inP_iff_mem_cube n q).mp h)
      rw [potential_liftQ sys H hKernel hL n x q, tsum_eq_sum (s := Qs eta n)]
      · refine Finset.sum_congr rfl fun p hp => ?_
        unfold FSNormal.vbK
        rw [if_pos (show Cross (n : ℝ) q p from Or.inr ⟨hqP', mem_Qs.mp hp⟩)]; ring
      · intro p hp
        unfold FSNormal.vbK
        rw [if_neg]
        · ring
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact hqQ (mem_Qs.mpr h)
          · exact hp (mem_Qs.mpr h)

open Classical in
include hKernel in
/-- **The bulk-fed force**: `G_b(w, w) = 𝔊(δ, 1_Q w) + 𝔊(1_Q w, δ)`. -/
theorem Gb_eq (w : MolecularFourierH2 eta) :
    Gb sys hL p₀ n w w =
      Gf sys L H p₀ (w - molecularH2Truncate n w) (liftQ L n (Sm eta L w)) +
        Gf sys L H p₀ (liftQ L n (Sm eta L w)) (w - molecularH2Truncate n w) := by
  set x := Sm eta L w
  set δ := w - molecularH2Truncate n w
  set lq := liftQ L n x
  have hsub : Qs eta n ⊆ fourierConfigCube eta n := Qs_subset_cube (by omega)
  have hSlq : ∀ q, Sm eta L lq q = if q ∈ Qs eta n then x q else 0 := by
    intro q; rw [stateMap_liftQ, lpTruncate_apply]
  set WR := Wp sys L H lq - molecularH2Truncate n (Wp sys L H lq)
  set WQ := lpTruncate (Qs eta n) (Wp sys L H δ)
  have hV := Vb_split sys hL H hKernel (n := n) w
  -- the four pairings
  have e1 : ⟪WR, Ap sys L p₀ w⟫_ℂ = ⟪Wp sys L H lq, Ap sys L p₀ δ⟫_ℂ := by
    refine inner_eq_of_pt' _ _ _ _ fun q => ?_
    simp only [WR, lp.coeFn_sub, Pi.sub_apply, molecularH2Truncate_apply, Ap_apply',
      stateMap_sub_trunc_apply, δ]
    by_cases hq : q ∈ fourierConfigCube eta n
    · rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hq, if_pos hq, sub_self, mul_zero,
        inner_zero_left, inner_zero_right]
    · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq, if_neg hq, sub_zero]
  have e2 : ⟪WQ, Ap sys L p₀ w⟫_ℂ = ⟪Wp sys L H δ, Ap sys L p₀ lq⟫_ℂ := by
    refine inner_eq_of_pt' _ _ _ _ fun q => ?_
    simp only [WQ, lpTruncate_apply, Ap_apply', hSlq]
    by_cases hq : q ∈ Qs eta n
    · rw [if_pos hq, if_pos hq]
    · rw [if_neg hq, if_neg hq, mul_zero, inner_zero_left, inner_zero_right]
  have e3 : ⟪Ap sys L p₀ w, WR⟫_ℂ = ⟪Ap sys L p₀ δ, Wp sys L H lq⟫_ℂ := by
    rw [← inner_conj_symm, e1, inner_conj_symm]
  have e4 : ⟪Ap sys L p₀ w, WQ⟫_ℂ = ⟪Ap sys L p₀ lq, Wp sys L H δ⟫_ℂ := by
    rw [← inner_conj_symm, e2, inner_conj_symm]
  unfold Gb Gf
  rw [hV, inner_add_left, inner_add_right, e1, e2, e3, e4]
  ring

include hKernel in
/-- `Re G_b(w, w) = 2 Re 𝔊(δ, 1_Q w)`. -/
lemma Gb_re_eq (w : MolecularFourierH2 eta) :
    (Gb sys hL p₀ n w w).re =
      2 * (Gf sys L H p₀ (w - molecularH2Truncate n w) (liftQ L n (Sm eta L w))).re := by
  rw [Gb_eq sys hL H hKernel p₀ w, Gf_swap sys L H p₀ (w - molecularH2Truncate n w), Complex.add_re,
    Complex.conj_re]
  ring

/-- The hot part `U_λ P w = P w - 1_{Q_m} w` at the threshold `λ = g m/4`. -/
noncomputable def hotAm (L : ℝ) (n m : ℕ) (w : MolecularFourierH2 eta) : MolecularFourierH2 eta :=
  molecularH2Truncate n w - liftQ L m (Sm eta L w)

include hKernel in
/-- **The exact split of `thm:flux2`**: `𝔊(w, w) - 𝔊(P w, P w) = G_nc(w) + G_b(w, w)` with the
near-cutoff piece `G_nc(w) = 𝔊(δ, δ) + 2 Re 𝔊(δ, U_{K/4} P w)` (real parts). -/
theorem flux2_split (w : MolecularFourierH2 eta) :
    (Gf sys L H p₀ w w).re -
        (Gf sys L H p₀ (molecularH2Truncate n w) (molecularH2Truncate n w)).re =
      ((Gf sys L H p₀ (w - molecularH2Truncate n w) (w - molecularH2Truncate n w)).re +
          2 * (Gf sys L H p₀ (w - molecularH2Truncate n w) (hotAm L n n w)).re) +
        (Gb sys hL p₀ n w w).re := by
  have hsplit : w = molecularH2Truncate n w + (w - molecularH2Truncate n w) := by abel
  have hexp := Gf_expand_re sys L H p₀ (molecularH2Truncate n w) (w - molecularH2Truncate n w)
  rw [← hsplit] at hexp
  rw [hexp, Gb_re_eq sys hL H hKernel p₀ w]
  have ha : molecularH2Truncate n w = hotAm L n n w + liftQ L n (Sm eta L w) := by
    unfold hotAm; abel
  rw [ha, Gf_add_right, Complex.add_re]
  ring

end Split

/-! ## `thm:flux` at a general threshold -/

section GenThreshold

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta)

include hL in
omit [Fintype ν] in
/-- `‖P x - 1_{Q_m} x‖ ≤ Σ_a ‖1_{a, > g m/4} x‖` for `m ≤ 4n`. -/
lemma norm_trunc_sub_truncQm_le {n m : ℕ} (hm : m ≤ 4 * n) (x : L2 eta) :
    ‖molecularH2Truncate n x - lpTruncate (Qs eta m) x‖ ≤
      ∑ a : Fin eta, ‖tailMask (gF L) (gF L * m / 4) a x‖ := by
  classical
  have hsub := Qs_subset_cube (eta := eta) hm
  have h1 : ‖molecularH2Truncate n x - lpTruncate (Qs eta m) x‖ ≤
      1 * ‖x - lpTruncate (Qs eta m) x‖ := by
    refine l2_norm_le_of_le _ _ zero_le_one fun q => ?_
    rw [one_mul, lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply, molecularH2Truncate_apply,
      lpTruncate_apply]
    by_cases hq : q ∈ fourierConfigCube eta n
    · rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hq]
    · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq, if_neg (fun h => hq (hsub h))]
      simp
  have h2 := norm_sub_truncQ_le hL m x
  linarith

omit [Fintype ν] in
lemma stateMap_hotAm (n m : ℕ) (w : MolecularFourierH2 eta) :
    Sm eta L (hotAm L n m w) =
      molecularH2Truncate n (Sm eta L w) - lpTruncate (Qs eta m) (Sm eta L w) := by
  unfold hotAm
  rw [map_sub, stateMap_liftQ, Sm, stateMap_truncate]

omit [Fintype ν] in
lemma kinetic_hotAm (n m : ℕ) (w : MolecularFourierH2 eta) :
    coulombFourierKineticH2 sys (gF L) (hotAm L n m w) =
      molecularH2Truncate n (coulombFourierKineticH2 sys (gF L) w) -
        lpTruncate (Qs eta m) (coulombFourierKineticH2 sys (gF L) w) := by
  unfold hotAm
  rw [map_sub, kinetic_liftQ, kinetic_truncate]

include hKernel hL in
/-- **`thm:flux` at a general threshold** `λ = g m/4 ≥ 1`, `m ≤ 4n`, `K = g n ≥ 1`:
`|𝔊(δ, U_λ P w)| ≤ √3 C_m η² M² (K^{-3/2} λ^{-1/2} + K^{-1/2} λ^{-3/2})`. -/
theorem flux_nc_gen (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {n m : ℕ} (hm : m ≤ 4 * n) (hK : 1 ≤ gF L * n) (hlam : 1 ≤ gF L * m / 4) {M : ℝ}
    {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    ‖Gf sys L H p₀ (w - molecularH2Truncate n w) (hotAm L n m w)‖ ≤
      Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * (eta : ℝ) ^ 2 * M ^ 2 *
        ((gF L * n) ^ (-(3 / 2 : ℝ)) * (gF L * m / 4) ^ (-(1 / 2 : ℝ)) +
          (gF L * n) ^ (-(1 / 2 : ℝ)) * (gF L * m / 4) ^ (-(3 / 2 : ℝ))) := by
  set K := gF L * n with hKdef
  set lam := gF L * m / 4 with hlamdef
  have hK0 : 0 < K := by linarith
  have hl0 : 0 < lam := by linarith
  have hM := hF.nonneg
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  set δ := w - molecularH2Truncate n w
  set U := hotAm L n m w
  set x := (eta : ℝ) * M
  have hx : 0 ≤ x := by positivity
  have hSδ : ‖Sm eta L δ‖ ≤ x * K ^ (-(5 / 2 : ℝ)) := by
    rw [map_sub, Sm, stateMap_truncate]; exact fgood_R hF hL hK
  have hTδ : ‖coulombFourierKineticH2 sys (gF L) δ‖ ≤ x * K ^ (-(1 / 2 : ℝ)) := by
    rw [map_sub, kinetic_truncate]
    refine (PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) n _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n) a (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ ∑ _a : Fin eta, M * K ^ (-(1 / 2 : ℝ)) := Finset.sum_le_sum fun a _ => (hF.2 a _ hK).2
      _ = x * K ^ (-(1 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hSU : ‖Sm eta L U‖ ≤ x * lam ^ (-(5 / 2 : ℝ)) := by
    rw [stateMap_hotAm]
    refine (norm_trunc_sub_truncQm_le hL hm _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * m / 4) a (Sm eta L w)‖
        ≤ ∑ _a : Fin eta, M * lam ^ (-(5 / 2 : ℝ)) := Finset.sum_le_sum fun a _ => (hF.2 a _ hlam).1
      _ = x * lam ^ (-(5 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hTU : ‖coulombFourierKineticH2 sys (gF L) U‖ ≤ x * lam ^ (-(1 / 2 : ℝ)) := by
    rw [kinetic_hotAm]
    refine (norm_trunc_sub_truncQm_le hL hm _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * m / 4) a (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ ∑ _a : Fin eta, M * lam ^ (-(1 / 2 : ℝ)) := Finset.sum_le_sum fun a _ => (hF.2 a _ hlam).2
      _ = x * lam ^ (-(1 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hle : ∀ l : ℝ, 1 ≤ l → x * l ^ (-(5 / 2 : ℝ)) ≤ x * l ^ (-(1 / 2 : ℝ)) := fun l hl =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hl (by norm_num)) hx
  have hWδ := norm_W_le_of sys hL H hKernel Hunit hPeriodic δ hSδ hTδ (hle K hK)
  have hWU := norm_W_le_of sys hL H hKernel Hunit hPeriodic U hSU hTU (hle lam hlam)
  rw [sqrt_three_tail hx hK0] at hWδ
  rw [sqrt_three_tail hx hl0] at hWU
  have hAδ := (norm_Ap_le sys L p₀ δ).trans hTδ
  have hAU := (norm_Ap_le sys L p₀ U).trans hTU
  refine (norm_Gf_le sys L H p₀ δ U).trans ?_
  have hp1 := Real.rpow_nonneg hK0.le (-(1 / 2 : ℝ))
  have hp3 := Real.rpow_nonneg hK0.le (-(3 / 2 : ℝ))
  have hq1 := Real.rpow_nonneg hl0.le (-(1 / 2 : ℝ))
  have hq3 := Real.rpow_nonneg hl0.le (-(3 / 2 : ℝ))
  have hs3 := Real.sqrt_nonneg 3
  calc ‖Wp sys L H δ‖ * ‖Ap sys L p₀ U‖ + ‖Ap sys L p₀ δ‖ * ‖Wp sys L H U‖
      ≤ finiteCoulombPhysicalMassConstant sys L Hunit * (Real.sqrt 3 * x * K ^ (-(3 / 2 : ℝ))) *
            (x * lam ^ (-(1 / 2 : ℝ))) +
          x * K ^ (-(1 / 2 : ℝ)) * (finiteCoulombPhysicalMassConstant sys L Hunit *
            (Real.sqrt 3 * x * lam ^ (-(3 / 2 : ℝ)))) :=
        add_le_add (mul_le_mul hWδ hAU (norm_nonneg _) (by positivity))
          (mul_le_mul hAδ hWU (norm_nonneg _) (by positivity))
    _ = _ := by simp only [x]; ring

/-- The near-cutoff constant at `λ = K/4`: `√3 C_m η² (2 + 2 (2 + 8))`. -/
noncomputable def nc4C (sys : CoulombSystem eta ν) (L Hunit : ℝ) : ℝ :=
  22 * Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * (eta : ℝ) ^ 2

include hKernel hL in
/-- **The near-cutoff piece at `K/4`** (`thm:flux`, general-threshold form, as used by
`thm:flux2`): for `K = g n ≥ 4`, `|𝔊(δ, δ)| + 2 |𝔊(δ, U_{K/4} P w)| ≤ nc4C M² K^{-2}`. -/
theorem flux_nc4 (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {n : ℕ} (hK : 4 ≤ gF L * n) {M : ℝ} {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    ‖Gf sys L H p₀ (w - molecularH2Truncate n w) (w - molecularH2Truncate n w)‖ +
        2 * ‖Gf sys L H p₀ (w - molecularH2Truncate n w) (hotAm L n n w)‖ ≤
      nc4C sys L Hunit * M ^ 2 * (gF L * n) ^ (-(2 : ℝ)) := by
  set K := gF L * n with hKdef
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hM := hF.nonneg
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hlam : 1 ≤ gF L * n / 4 := by linarith
  have h2 := flux_nc_gen sys hL H hKernel p₀ Hunit hPeriodic (m := n) (by omega) hK1 hlam hF
  -- the `δ`–`δ` term as in `flux_nc`
  set δ := w - molecularH2Truncate n w
  set x := (eta : ℝ) * M
  have hx : 0 ≤ x := by positivity
  have hSδ : ‖Sm eta L δ‖ ≤ x * K ^ (-(5 / 2 : ℝ)) := by
    rw [map_sub, Sm, stateMap_truncate]; exact fgood_R hF hL hK1
  have hTδ : ‖coulombFourierKineticH2 sys (gF L) δ‖ ≤ x * K ^ (-(1 / 2 : ℝ)) := by
    rw [map_sub, kinetic_truncate]
    refine (PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) n _).trans ?_
    calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n) a (coulombFourierKineticH2 sys (gF L) w)‖
        ≤ ∑ _a : Fin eta, M * K ^ (-(1 / 2 : ℝ)) := Finset.sum_le_sum fun a _ => (hF.2 a _ hK1).2
      _ = x * K ^ (-(1 / 2 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hWδ := norm_W_le_of sys hL H hKernel Hunit hPeriodic δ hSδ hTδ
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hK1 (by norm_num)) hx)
  rw [sqrt_three_tail hx hK0] at hWδ
  have hAδ := (norm_Ap_le sys L p₀ δ).trans hTδ
  have hp := Real.rpow_nonneg hK0.le (-(1 / 2 : ℝ))
  have hq := Real.rpow_nonneg hK0.le (-(3 / 2 : ℝ))
  have h1 : ‖Gf sys L H p₀ δ δ‖ ≤
      2 * (finiteCoulombPhysicalMassConstant sys L Hunit * (Real.sqrt 3 * x * K ^ (-(3 / 2 : ℝ)))) *
        (x * K ^ (-(1 / 2 : ℝ))) := by
    refine (norm_Gf_le sys L H p₀ δ δ).trans ?_
    have := mul_le_mul hWδ hAδ (norm_nonneg _) (by positivity)
    have := mul_le_mul hAδ hWδ (norm_nonneg _) (by positivity)
    nlinarith
  -- the powers of `K/4`
  have hK4 : ∀ r : ℝ, (K / 4) ^ r = (4 : ℝ) ^ (-r) * K ^ r := fun r => by
    rw [div_eq_mul_inv, Real.mul_rpow hK0.le (by norm_num), Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num)]
    ring
  have h41 : (4 : ℝ) ^ (-(-(1 / 2 : ℝ))) = 2 := by
    rw [neg_neg, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have h43 : (4 : ℝ) ^ (-(-(3 / 2 : ℝ))) = 8 := by
    rw [neg_neg, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  rw [hK4, hK4, h41, h43] at h2
  have e1 : K ^ (-(3 / 2 : ℝ)) * K ^ (-(1 / 2 : ℝ)) = K ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hK0]; norm_num
  have e2 : K ^ (-(1 / 2 : ℝ)) * K ^ (-(3 / 2 : ℝ)) = K ^ (-(2 : ℝ)) := by
    rw [mul_comm, e1]
  have h2' : ‖Gf sys L H p₀ δ (hotAm L n n w)‖ ≤
      10 * Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * (eta : ℝ) ^ 2 * M ^ 2 *
        K ^ (-(2 : ℝ)) := by
    refine h2.trans (le_of_eq ?_)
    rw [show K ^ (-(3 / 2 : ℝ)) * (2 * K ^ (-(1 / 2 : ℝ))) +
        K ^ (-(1 / 2 : ℝ)) * (8 * K ^ (-(3 / 2 : ℝ))) =
        2 * (K ^ (-(3 / 2 : ℝ)) * K ^ (-(1 / 2 : ℝ))) + 8 * (K ^ (-(1 / 2 : ℝ)) * K ^ (-(3 / 2 : ℝ)))
      by ring, e1, e2]
    ring
  have h1' : ‖Gf sys L H p₀ δ δ‖ ≤
      2 * Real.sqrt 3 * finiteCoulombPhysicalMassConstant sys L Hunit * (eta : ℝ) ^ 2 * M ^ 2 *
        K ^ (-(2 : ℝ)) := by
    refine h1.trans (le_of_eq ?_)
    rw [← e1]; simp only [x]; ring
  unfold nc4C
  linarith

end GenThreshold

/-! ## The assembly of `thm:flux2` -/

section Assembly

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta)

include hKernel hL in
/-- The exact trajectory is continuous in `H²` (`‖u‖ ≤ m̄ (‖S u‖ + 2 ‖T u‖)`). -/
lemma continuous_traj (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) : Continuous (traj H D) := by
  have hS := continuous_S_traj H D
  have hT := continuous_T_traj sys hL H hKernel Hunit hPeriodic D
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 := hS.tendsto t
  have h2 := hT.tendsto t
  rw [tendsto_iff_norm_sub_tendsto_zero] at h1 h2
  have h3 : Tendsto (fun s => sys.maxMass * (‖Sm eta L (traj H D s) - Sm eta L (traj H D t)‖ +
      2 * ‖coulombFourierKineticH2 sys (gF L) (traj H D s) -
        coulombFourierKineticH2 sys (gF L) (traj H D t)‖)) (𝓝 t) (𝓝 0) := by
    have := (h1.add (h2.const_mul 2)).const_mul sys.maxMass
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) h3
  have := PlaneWaveDynamics.h2norm_le sys L (traj H D s - traj H D t)
  rw [map_sub, map_sub] at this
  exact this

omit [Fintype ν] in
lemma continuous_Gf {f g : ℝ → MolecularFourierH2 eta} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun s => Gf sys L H p₀ (f s) (g s) := by
  unfold Gf
  have hWf := (Wp sys L H).continuous.comp hf
  have hWg := (Wp sys L H).continuous.comp hg
  have hAf := (Ap sys L p₀).continuous.comp hf
  have hAg := (Ap sys L p₀).continuous.comp hg
  exact (continuous_const.mul (hWf.inner hAg)).sub (continuous_const.mul (hAf.inner hWg))

omit [Fintype ν] in
lemma continuous_trunc (n : ℕ) :
    Continuous (molecularH2Truncate n : MolecularFourierH2 eta → MolecularFourierH2 eta) := by
  classical
  have e : (molecularH2Truncate n : MolecularFourierH2 eta → MolecularFourierH2 eta) =
      ⇑(lpTruncateCLM (fourierConfigCube eta n)) := by
    funext u; rfl
  rw [e]; exact (lpTruncateCLM _).continuous

include hKernel hL in
/-- **`thm:flux2` from the phase bound**: if `|𝔚(w_s, w_s)| ≤ C_φ Ξ² K^{-2+ε}` (`prop:phase`),
then `|∫₀ᵗ (𝔊(ψ, ψ) - 𝔊(Pψ, Pψ))| ≤ C Ξ² (K^{-3} + t K^{-2+ε})` for `K ≥ 4`, `t ≥ 0`. -/
theorem thm_flux2_of_phase (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ε Cφ : ℝ} (hε : 0 ≤ ε) (hCφ : 0 ≤ Cφ)
    (hphase : ∀ (n : ℕ) (hn : 2 ≤ n), 4 ≤ Kc L n → ∀ (D : EvoData L H) (s : ℝ),
      |(Wf sys hL hn p₀ H (traj H D s) (traj H D s)).re| ≤ Cφ * D.Xi ^ 2 * Kc L n ^ (-2 + ε)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 2 ≤ n → 4 ≤ Kc L n → ∀ (D : EvoData L H) {t : ℝ}, 0 ≤ t →
      |∫ s in (0 : ℝ)..t, ((Gf sys L H p₀ (traj H D s) (traj H D s)).re -
          (Gf sys L H p₀ (molecularH2Truncate n (traj H D s))
            (molecularH2Truncate n (traj H D s))).re)| ≤
        C * D.Xi ^ 2 * (Kc L n ^ (-(3 : ℝ)) + t * Kc L n ^ (-2 + ε)) := by
  obtain ⟨C₁, hC₁, hel⟩ := thm_elim sys hL H hKernel p₀ Hunit hPeriodic
  have hc := cTr_nonneg sys hL Hunit
  set Cn := |nc4C sys L Hunit| * cTr sys L Hunit ^ 2
  have hCn : 0 ≤ Cn := by positivity
  refine ⟨C₁ + Cφ + Cn, by positivity, ?_⟩
  intro n hn hK4 D t ht
  have hK : 4 ≤ gF L * n := by rwa [Kc_eq] at hK4
  have hK1 : 1 ≤ Kc L n := by linarith
  have hK0 : 0 < Kc L n := by linarith
  have hΞ := D.Xi_nonneg
  set F : ℝ → ℝ := fun s => (Gf sys L H p₀ (traj H D s) (traj H D s)).re -
    (Gf sys L H p₀ (molecularH2Truncate n (traj H D s)) (molecularH2Truncate n (traj H D s))).re
  set G : ℝ → ℝ := fun s => (Gb sys hL p₀ n (traj H D s) (traj H D s)).re
  set Wr : ℝ → ℝ := fun s => (Wf sys hL hn p₀ H (traj H D s) (traj H D s)).re
  have hct := continuous_traj sys hL H hKernel Hunit hPeriodic D
  have hcF : Continuous F := by
    have hP := (continuous_trunc n).comp hct
    exact (Complex.continuous_re.comp (continuous_Gf sys H p₀ hct hct)).sub
      (Complex.continuous_re.comp (continuous_Gf sys H p₀ hP hP))
  have hcG : Continuous G :=
    Complex.continuous_re.comp (continuous_Gb_traj sys hL (n := n) H hKernel p₀ Hunit hPeriodic D)
  -- the near-cutoff piece, pointwise
  have hnc : ∀ s, ‖F s - G s‖ ≤ Cn * D.Xi ^ 2 * Kc L n ^ (-2 + ε) := by
    intro s
    obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D s
    have hw : traj H D s = w := traj_eq H D s w hw1
    have hsplit := flux2_split sys hL H hKernel p₀ (n := n) w
    have hb := flux_nc4 sys hL H hKernel p₀ Hunit hPeriodic hK hF
    have hFG : F s - G s = (Gf sys L H p₀ (w - molecularH2Truncate n w)
        (w - molecularH2Truncate n w)).re +
          2 * (Gf sys L H p₀ (w - molecularH2Truncate n w) (hotAm L n n w)).re := by
      simp only [F, G, hw]; rw [hsplit]; ring
    rw [Real.norm_eq_abs, hFG]
    have a1 := Complex.abs_re_le_norm (Gf sys L H p₀ (w - molecularH2Truncate n w)
      (w - molecularH2Truncate n w))
    have a2 := Complex.abs_re_le_norm (Gf sys L H p₀ (w - molecularH2Truncate n w) (hotAm L n n w))
    have hpow : Kc L n ^ (-(2 : ℝ)) ≤ Kc L n ^ (-2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
    have hnc' : nc4C sys L Hunit * (cTr sys L Hunit * D.Xi) ^ 2 * Kc L n ^ (-(2 : ℝ)) ≤
        Cn * D.Xi ^ 2 * Kc L n ^ (-2 + ε) := by
      have h1 : nc4C sys L Hunit ≤ |nc4C sys L Hunit| := le_abs_self _
      have hp0 := Real.rpow_nonneg hK0.le (-(2 : ℝ))
      calc nc4C sys L Hunit * (cTr sys L Hunit * D.Xi) ^ 2 * Kc L n ^ (-(2 : ℝ))
          ≤ |nc4C sys L Hunit| * (cTr sys L Hunit * D.Xi) ^ 2 * Kc L n ^ (-(2 : ℝ)) := by gcongr
        _ ≤ |nc4C sys L Hunit| * (cTr sys L Hunit * D.Xi) ^ 2 * Kc L n ^ (-2 + ε) := by gcongr
        _ = Cn * D.Xi ^ 2 * Kc L n ^ (-2 + ε) := by simp only [Cn]; ring
    rw [Kc_eq] at hnc'
    have := abs_add_le (Gf sys L H p₀ (w - molecularH2Truncate n w) (w - molecularH2Truncate n w)).re
      (2 * (Gf sys L H p₀ (w - molecularH2Truncate n w) (hotAm L n n w)).re)
    rw [abs_mul, abs_two] at this
    rw [Kc_eq]
    linarith
  -- integrate
  have hI : ∫ s in (0 : ℝ)..t, F s = (∫ s in (0 : ℝ)..t, (F s - G s)) + ∫ s in (0 : ℝ)..t, G s := by
    have hFG : Continuous fun s => F s - G s := hcF.sub hcG
    rw [← intervalIntegral.integral_add (hFG.intervalIntegrable 0 t) (hcG.intervalIntegrable 0 t)]
    congr 1; funext s; ring
  have hE := hel n hn hK1 D t
  have h1 : ‖∫ s in (0 : ℝ)..t, (F s - G s)‖ ≤ Cn * D.Xi ^ 2 * Kc L n ^ (-2 + ε) * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hnc s
  have h2 : ‖∫ s in (0 : ℝ)..t, Wr s‖ ≤ Cφ * D.Xi ^ 2 * Kc L n ^ (-2 + ε) * |t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => by
      rw [Real.norm_eq_abs]; exact hphase n hn hK4 D s
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at h1 h2
  change |(∫ s in (0 : ℝ)..t, G s) + ∫ s in (0 : ℝ)..t, Wr s| ≤ _ at hE
  change |∫ s in (0 : ℝ)..t, F s| ≤ _
  rw [hI]
  have hp3 := Real.rpow_nonneg hK0.le (-(3 : ℝ))
  have hpe := Real.rpow_nonneg hK0.le (-2 + ε)
  have e : (∫ s in (0 : ℝ)..t, (F s - G s)) + ∫ s in (0 : ℝ)..t, G s =
      (∫ s in (0 : ℝ)..t, (F s - G s)) + ((∫ s in (0 : ℝ)..t, G s) + ∫ s in (0 : ℝ)..t, Wr s) -
        ∫ s in (0 : ℝ)..t, Wr s := by ring
  rw [e]
  have a := abs_sub ((∫ s in (0 : ℝ)..t, (F s - G s)) +
    ((∫ s in (0 : ℝ)..t, G s) + ∫ s in (0 : ℝ)..t, Wr s)) (∫ s in (0 : ℝ)..t, Wr s)
  have b := abs_add_le (∫ s in (0 : ℝ)..t, (F s - G s))
    ((∫ s in (0 : ℝ)..t, G s) + ∫ s in (0 : ℝ)..t, Wr s)
  have hX : 0 ≤ D.Xi ^ 2 := sq_nonneg _
  have c1 : Cn * D.Xi ^ 2 * Kc L n ^ (-2 + ε) * t ≤ Cn * (D.Xi ^ 2 * (t * Kc L n ^ (-2 + ε))) := by
    nlinarith
  calc _ ≤ Cn * D.Xi ^ 2 * Kc L n ^ (-2 + ε) * t + C₁ * D.Xi ^ 2 * Kc L n ^ (-(3 : ℝ)) +
        Cφ * D.Xi ^ 2 * Kc L n ^ (-2 + ε) * t := by linarith
    _ ≤ (C₁ + Cφ + Cn) * D.Xi ^ 2 * (Kc L n ^ (-(3 : ℝ)) + t * Kc L n ^ (-2 + ε)) := by
        have : 0 ≤ D.Xi ^ 2 * Kc L n ^ (-(3 : ℝ)) := by positivity
        have : 0 ≤ D.Xi ^ 2 * (t * Kc L n ^ (-2 + ε)) := by positivity
        nlinarith

end Assembly

end FSFlux
