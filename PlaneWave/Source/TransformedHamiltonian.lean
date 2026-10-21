import PlaneWave.Source.BulkGenerator
import PlaneWave.Source.Conjugation

/-!
# Flux/source build, block 2d: the transformed Hamiltonian on `D(T)`

With the decoding map `S` (`D(T) = ran S`), the bulk generator `Σ = Σ_b` and its decoded form
`Σ_D` (`S Σ_D = Σ`, `dev/PlaneWave.Source.BulkGenerator.lean`):

* `SigG = Σ_D S`, the generator in graph-norm coordinates: `S Σ_G = Σ S` (`hSG`);
* `Zw = W Σ_D` (the bounded operator `W Σ_b`), and `Σ W = -Zw† S` on `H²` (`sig_W`), by the
  symmetry of `W` and `Σ† = -Σ`;
* the commutator `[H, Σ] = X₁ = V_b + Zw + Zw†` on `D(T)`: `H Σ_G - Σ H = X₁ S` (`hHG`), from
  `[T, Σ] = V_b`;
* **the conjugation** `e^{Σ} H e^{-Σ_G} = H + B S` with the bounded correction
  `B = -∫₀¹ e^{rΣ} X₁ e^{-rΣ} dr` (`conj_H`): `H̃ = U H U⁻¹ = H + B` on `D(T)`, `U = e^{Σ}`
  (eq:Htilde, `lem:bulk-weighted`); `e^{±Σ}` preserve `D(T)` (`stateMap_exp_SigG`);
* `B` is Hermitian on `D(T)` (`inner_Bcorr`);
* `dressed_hasDerivAt`: the dressed exact trajectory `ψ̃(t) = U ψ(t)` solves
  `ψ̃' = -i (H w + B ψ̃)` with `S w = ψ̃`, i.e. `i ψ̃' = H̃ ψ̃`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest NormedSpace

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- The decoding map `S : H² → ℓ²` as an operator on `ℓ²`. -/
noncomputable abbrev Sm (eta : ℕ) (L : ℝ) : L2 eta →L[ℂ] L2 eta := molecularH2StateMap eta (gF L)

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)

/-- The generator in graph-norm coordinates, `Σ_G = Σ_D S`. -/
noncomputable def SigG : L2 eta →L[ℂ] L2 eta := SigD sys L n hL (by omega) ∘L Sm eta L

include hn in
lemma hSG : Sm eta L * SigG sys hL hn = Sig sys L n hL hn * Sm eta L := by
  ext1 x
  simp only [mul_apply_eq_comp, SigG, ContinuousLinearMap.comp_apply]
  exact stateMap_SigD hL hn _

/-- `e^{±Σ}` preserve `D(T)`: `S e^{rΣ_G} = e^{rΣ} S`. -/
lemma stateMap_exp_SigG (r : ℂ) :
    Sm eta L * exp (r • SigG sys hL hn) = exp (r • Sig sys L n hL hn) * Sm eta L := by
  letI := (FSConj.ratAlg : NormedAlgebra ℚ (L2 eta →L[ℂ] L2 eta))
  have h : SemiconjBy (Sm eta L) (r • SigG sys hL hn) (r • Sig sys L n hL hn) := by
    unfold SemiconjBy
    rw [mul_smul_comm, hSG, smul_mul_assoc]
  exact h.exp_right

/-- The potential `W = H - T` on `H²`. -/
noncomputable abbrev Wp (L : ℝ) (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    L2 eta →L[ℂ] L2 eta := coulombFourierPotentialH2 sys (gF L) H

/-- `Zw = W Σ_D`, the bounded operator `W Σ_b`. -/
noncomputable def Zw : L2 eta →L[ℂ] L2 eta := Wp sys L H ∘L SigD sys L n hL (by omega)

variable (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

lemma adjoint_Sig : ContinuousLinearMap.adjoint (Sig sys L n hL hn) = -Sig sys L n hL hn := by
  have h := (Sig_skew_unitary (sys := sys) hL hn).1
  rw [skewAdjoint.mem_iff, ContinuousLinearMap.star_eq_adjoint] at h
  exact h

include hKernel in
/-- **`Σ W = -(W Σ_D)† S`** on `H²`. -/
theorem sig_W : Sig sys L n hL hn * Wp sys L H =
    -(ContinuousLinearMap.adjoint (Zw sys hL hn H) * Sm eta L) := by
  ext1 u
  refine ext_inner_right ℂ fun y => ?_
  simp only [mul_apply_eq_comp, neg_apply, inner_neg_left]
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_Sig, neg_apply,
    inner_neg_right, ContinuousLinearMap.adjoint_inner_left]
  congr 1
  rw [← stateMap_SigD hL hn y]
  have := potential_symm sys L H hKernel u (SigD sys L n hL (by omega) y)
  rw [Zw, ContinuousLinearMap.comp_apply]
  exact this.symm

/-- The commutator `[H, Σ] = X₁ = V_b + W Σ_D + (W Σ_D)†`. -/
noncomputable def X1 : L2 eta →L[ℂ] L2 eta :=
  Vb sys L n hL + Zw sys hL hn H + ContinuousLinearMap.adjoint (Zw sys hL hn H)

include hKernel in
/-- **`[H, Σ] = X₁` on `D(T)`**: `H Σ_G - Σ H = X₁ S`. -/
theorem hHG : H * SigG sys hL hn - Sig sys L n hL hn * H = X1 sys hL hn H * Sm eta L := by
  have hsplit : ∀ v, H v = coulombFourierKineticH2 sys (gF L) v + Wp sys L H v := fun v =>
    coulombFourierHamiltonianH2_decomposition sys (gF L) H v
  have hW := congrArg (fun A => A) (sig_W sys hL hn H hKernel)
  ext1 u
  have hWu : Sig sys L n hL hn (Wp sys L H u) =
      -(ContinuousLinearMap.adjoint (Zw sys hL hn H) (Sm eta L u)) := by
    have := congrArg (fun A : L2 eta →L[ℂ] L2 eta => A u) (sig_W sys hL hn H hKernel)
    simpa only [mul_apply_eq_comp, neg_apply] using this
  have hT := kinetic_comm (sys := sys) hL hn u
  simp only [sub_apply, mul_apply_eq_comp, SigG,
    ContinuousLinearMap.comp_apply, X1, add_apply]
  rw [hsplit, hsplit, map_add, hWu]
  have hZ : Wp sys L H (SigD sys L n hL (by omega) (Sm eta L u)) = Zw sys hL hn H (Sm eta L u) := rfl
  rw [hZ, ← hT]
  abel

/-- The bounded correction `B = -∫₀¹ e^{rΣ} X₁ e^{-rΣ} dr` of the transformed Hamiltonian. -/
noncomputable def Bcorr : L2 eta →L[ℂ] L2 eta := -FSConj.Bi (Sig sys L n hL hn) (X1 sys hL hn H)

include hKernel in
/-- **The conjugation on `D(T)`** (eq:Htilde): `e^{Σ} H e^{-Σ_G} = H + B S`. -/
theorem conj_H : exp (Sig sys L n hL hn) * H * exp (-SigG sys hL hn) =
    H + Bcorr sys hL hn H * Sm eta L := by
  rw [FSConj.conj_unbounded (hSG sys hL hn) (hHG sys hL hn H hKernel),
    Bcorr, neg_mul, sub_eq_add_neg]

lemma exp_Sig_unitary : exp (Sig sys L n hL hn) ∈ unitary (L2 eta →L[ℂ] L2 eta) :=
  (Sig_skew_unitary (sys := sys) hL hn).2

lemma adjoint_exp_Sig :
    ContinuousLinearMap.adjoint (exp (Sig sys L n hL hn)) = exp (-Sig sys L n hL hn) := by
  letI := (FSConj.ratAlg : NormedAlgebra ℚ (L2 eta →L[ℂ] L2 eta))
  rw [← ContinuousLinearMap.star_eq_adjoint, star_exp, ContinuousLinearMap.star_eq_adjoint,
    adjoint_Sig]

lemma adjoint_exp_neg_Sig :
    ContinuousLinearMap.adjoint (exp (-Sig sys L n hL hn)) = exp (Sig sys L n hL hn) := by
  letI := (FSConj.ratAlg : NormedAlgebra ℚ (L2 eta →L[ℂ] L2 eta))
  rw [← ContinuousLinearMap.star_eq_adjoint, star_exp, star_neg, ContinuousLinearMap.star_eq_adjoint,
    adjoint_Sig, neg_neg]

lemma exp_neg_SigG_apply (x : L2 eta) :
    Sm eta L (exp (-SigG sys hL hn) x) = exp (-Sig sys L n hL hn) (Sm eta L x) := by
  have := congrArg (fun A : L2 eta →L[ℂ] L2 eta => A x) (stateMap_exp_SigG sys hL hn (-1))
  simpa only [mul_apply_eq_comp, neg_one_smul] using this

lemma exp_SigG_apply (x : L2 eta) :
    Sm eta L (exp (SigG sys hL hn) x) = exp (Sig sys L n hL hn) (Sm eta L x) := by
  have := congrArg (fun A : L2 eta →L[ℂ] L2 eta => A x) (stateMap_exp_SigG sys hL hn 1)
  simpa only [mul_apply_eq_comp, one_smul] using this

lemma exp_neg_SigG_exp_SigG (x : L2 eta) :
    exp (-SigG sys hL hn) (exp (SigG sys hL hn) x) = x := by
  letI := (FSConj.ratAlg : NormedAlgebra ℚ (L2 eta →L[ℂ] L2 eta))
  have h : exp (-SigG sys hL hn) * exp (SigG sys hL hn) = 1 := by
    rw [← exp_add_of_commute (Commute.refl (SigG sys hL hn)).neg_left, neg_add_cancel, exp_zero]
  have := congrArg (fun A : L2 eta →L[ℂ] L2 eta => A x) h
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using this

/-- The symmetry of `H` on `H²` in the notation `S = Sm`. -/
lemma H_symm (hKernel' : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (x y : MolecularFourierH2 eta) : ⟪Sm eta L x, H y⟫_ℂ = ⟪H x, Sm eta L y⟫_ℂ :=
  coulombH2_symm sys L H hKernel' x y

include hKernel in
/-- **`B` is Hermitian on `D(T)`**: `⟪S x, B S y⟫ = ⟪B S x, S y⟫`. -/
theorem inner_Bcorr (x y : MolecularFourierH2 eta) :
    ⟪Sm eta L x, Bcorr sys hL hn H (Sm eta L y)⟫_ℂ =
      ⟪Bcorr sys hL hn H (Sm eta L x), Sm eta L y⟫_ℂ := by
  have hc := conj_H sys hL hn H hKernel
  have hB : ∀ z, Bcorr sys hL hn H (Sm eta L z) =
      exp (Sig sys L n hL hn) (H (exp (-SigG sys hL hn) z)) - H z := by
    intro z
    have := congrArg (fun A : L2 eta →L[ℂ] L2 eta => A z) hc
    simp only [mul_apply_eq_comp, add_apply] at this
    rw [this]; abel
  rw [hB, hB, inner_sub_right, inner_sub_left, H_symm sys H hKernel x y]
  congr 1
  set E := exp (Sig sys L n hL hn)
  set Em := exp (-Sig sys L n hL hn)
  set e := exp (-SigG sys hL hn)
  calc ⟪Sm eta L x, E (H (e y))⟫_ℂ = ⟪ContinuousLinearMap.adjoint E (Sm eta L x), H (e y)⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_left E _ _).symm
    _ = ⟪Sm eta L (e x), H (e y)⟫_ℂ := by rw [adjoint_exp_Sig, exp_neg_SigG_apply]
    _ = ⟪H (e x), Sm eta L (e y)⟫_ℂ := H_symm sys H hKernel _ _
    _ = ⟪H (e x), Em (Sm eta L y)⟫_ℂ := by rw [exp_neg_SigG_apply]
    _ = ⟪ContinuousLinearMap.adjoint Em (H (e x)), Sm eta L y⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_left Em _ _).symm ▸ rfl
    _ = ⟪E (H (e x)), Sm eta L y⟫_ℂ := by rw [adjoint_exp_neg_Sig]

/-! ## The dressed exact trajectory -/

include hKernel in
/-- **The transformed Schrödinger equation.** For the exact propagator `U` and the dressed
trajectory `ψ̃(t) = e^{Σ} U(t) S u₀`, there is `w` with `S w = ψ̃(t)` and
`ψ̃'(t) = -i (H w + B ψ̃(t))`. -/
theorem dressed_hasDerivAt
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      Sm eta L u' = U t (Sm eta L u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (Sm eta L u)) (-(Complex.I • U t (H u))) t)
    (u₀ : MolecularFourierH2 eta) (t : ℝ) :
    ∃ w : MolecularFourierH2 eta,
      Sm eta L w = exp (Sig sys L n hL hn) (U t (Sm eta L u₀)) ∧
      HasDerivAt (fun s => exp (Sig sys L n hL hn) (U s (Sm eta L u₀)))
        (-(Complex.I • (H w + Bcorr sys hL hn H (exp (Sig sys L n hL hn) (U t (Sm eta L u₀))))))
        t := by
  obtain ⟨u', hu'1, hu'2⟩ := hgraph t u₀
  set E := exp (Sig sys L n hL hn)
  refine ⟨exp (SigG sys hL hn) u', ?_, ?_⟩
  · rw [exp_SigG_apply]
    exact congrArg E hu'1
  · have hd := ((E.restrictScalars ℝ).hasFDerivAt (x := U t (Sm eta L u₀))).comp_hasDerivAt t
      (hderiv t u₀)
    have key : E (-(Complex.I • U t (H u₀))) =
        -(Complex.I • (H (exp (SigG sys hL hn) u') +
          Bcorr sys hL hn H (E (U t (Sm eta L u₀))))) := by
      rw [map_neg, map_smul, ← hu'2]
      congr 2
      have hc := congrArg (fun A : L2 eta →L[ℂ] L2 eta => A (exp (SigG sys hL hn) u'))
        (conj_H sys hL hn H hKernel)
      simp only [mul_apply_eq_comp, add_apply,
        exp_neg_SigG_exp_SigG] at hc
      rw [hc, exp_SigG_apply]
      congr 2
      exact congrArg E hu'1
    rw [← key]
    exact hd

end FSNormal
