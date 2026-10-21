import PlaneWave.Source.TransformedHamiltonian
import PlaneWave.Source.RetainedFlow

/-!
# Flux/source build, block 2e: the retained block, Duhamel, the assembly identity

The cube `ran P` is the Galerkin space `E_n` of block 1, embedded in `ℓ²` by
`emb = finiteFourierLpIsometry` with left inverse `ext = extractCLM`. With the correction `B` of
the transformed Hamiltonian (`dev/PlaneWave.Source.TransformedHamiltonian.lean`):

* `dH = P B P` on `E_n` is symmetric (`dH_symm`); the retained Hamiltonian is
  `P H̃ P = H_N + ΔH` with `ΔH = dH`, the `Hret` of block 1;
* for the exact propagator `U` and `u₀ ∈ H²`, the retained part `a(t) = P ψ̃(t)` of the dressed
  trajectory `ψ̃(t) = e^{Σ} U(t) S u₀` solves `a' = -i (H' a + f)` with the coupling
  `f(t) = P W R ψ̃(t) + P B R ψ̃(t)` (`aT_hasDerivAt`, `fT_eq`): `f = Ṽ_{PR} ψ̃_R`;
* **Duhamel** (`prop:nf`, second display), in weak form:
  `⟪a(t), v⟫ = ⟪e^{-iH't} a(0), v⟫ + i ∫₀ᵗ ⟪f(s), e^{iH'(t-s)} v⟫ ds` (`duhamel_weak`);
* **the assembly identity** (eq:nf-assembly) for a unitary `U` and a self-adjoint `O`
  (`assembly`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics NormedSpace FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The cube embedding -/

/-- The embedding `E_n ≅ ran P → ℓ²`. -/
noncomputable abbrev emb (eta n : ℕ) : En eta n →L[ℂ] L2 eta :=
  (finiteFourierLpIsometry eta n).toContinuousLinearMap

/-- The extraction `ℓ² → E_n` (`P` followed by the identification). -/
noncomputable abbrev ext (eta n : ℕ) : L2 eta →L[ℂ] En eta n := extractCLM n

omit [Fintype ν] in
lemma ext_emb (n : ℕ) (v : En eta n) : ext eta n (emb eta n v) = v := extract_embed n v

omit [Fintype ν] in
lemma emb_ext (n : ℕ) (x : L2 eta) : emb eta n (ext eta n x) = molecularH2Truncate n x :=
  emb_extractCLM n x

omit [Fintype ν] in
lemma inner_emb_emb (n : ℕ) (v w : En eta n) : ⟪emb eta n v, emb eta n w⟫_ℂ = ⟪v, w⟫_ℂ :=
  (finiteFourierLpIsometry eta n).inner_map_map v w

omit [Fintype ν] in
/-- `ext` is the adjoint of `emb`. -/
lemma inner_ext (n : ℕ) (x : L2 eta) (w : En eta n) :
    ⟪ext eta n x, w⟫_ℂ = ⟪x, emb eta n w⟫_ℂ := by
  calc ⟪ext eta n x, w⟫_ℂ = ⟪emb eta n (ext eta n x), emb eta n w⟫_ℂ := (inner_emb_emb n _ _).symm
    _ = ⟪molecularH2Truncate n x, emb eta n w⟫_ℂ := by rw [emb_ext]
    _ = conj ⟪emb eta n w, molecularH2Truncate n x⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj ⟪emb eta n w, x⟫_ℂ := by
        congr 1
        exact (finiteFourierLpEmbed_inner_truncate eta n w.ofLp x).symm
    _ = ⟪x, emb eta n w⟫_ℂ := inner_conj_symm _ _

omit [Fintype ν] in
lemma inner_ext' (n : ℕ) (x : L2 eta) (w : En eta n) :
    ⟪w, ext eta n x⟫_ℂ = ⟪emb eta n w, x⟫_ℂ := by
  rw [← inner_conj_symm, inner_ext, inner_conj_symm]

omit [Fintype ν] in
lemma emb_eq_stateMap (L : ℝ) (n : ℕ) (v : En eta n) :
    emb eta n v = Sm eta L (cubeLift (gF L) n v) :=
  (stateMap_cubeLift (gF L) n v).symm

/-! ## The retained correction `ΔH = P B P` -/

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-- The retained correction `ΔH = P B P` on `E_n`. -/
noncomputable def dH : En eta n →ₗ[ℂ] En eta n :=
  ((ext eta n) ∘L Bcorr sys hL hn H ∘L emb eta n).toLinearMap

lemma dH_apply (v : En eta n) : dH sys hL hn H v = ext eta n (Bcorr sys hL hn H (emb eta n v)) :=
  rfl

include hKernel in
/-- **`ΔH = P B P` is symmetric.** -/
theorem dH_symm : (dH sys hL hn H).IsSymmetric := by
  intro v w
  rw [dH_apply, dH_apply, inner_ext, inner_ext', emb_eq_stateMap L n v, emb_eq_stateMap L n w,
    inner_Bcorr sys hL hn H hKernel]

/-! ## The dressed trajectory and its retained part -/

variable (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (u₀ : MolecularFourierH2 eta)

/-- The dressed exact trajectory `ψ̃(t) = e^{Σ} U(t) S u₀`. -/
noncomputable def psiT (t : ℝ) : L2 eta := exp (Sig sys L n hL hn) (U t (Sm eta L u₀))

/-- Its retained part `a(t) = P ψ̃(t)` on `E_n`. -/
noncomputable def aT (t : ℝ) : En eta n := ext eta n (psiT sys hL hn U u₀ t)

/-- `P e^{Σ} U(t) H u₀`, the retained part of `H̃ ψ̃(t)`. -/
noncomputable def gT (t : ℝ) : En eta n := ext eta n (exp (Sig sys L n hL hn) (U t (H u₀)))

/-- The coupling `f(t) = P H̃ ψ̃(t) - H' a(t) = Ṽ_{PR} ψ̃_R(t)`. -/
noncomputable def fT (t : ℝ) : En eta n :=
  gT sys hL hn H U u₀ t - Hret sys L n (dH sys hL hn H) (aT sys hL hn U u₀ t)

lemma aT_hasDerivAt
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (Sm eta L u)) (-(Complex.I • U t (H u))) t)
    (t : ℝ) : HasDerivAt (aT sys hL hn U u₀) (-(Complex.I • gT sys hL hn H U u₀ t)) t := by
  set C : L2 eta →L[ℂ] En eta n := ext eta n ∘L exp (Sig sys L n hL hn)
  have hd := ((C.restrictScalars ℝ).hasFDerivAt (x := U t (Sm eta L u₀))).comp_hasDerivAt t
    (hderiv t u₀)
  have e : (C.restrictScalars ℝ) (-(Complex.I • U t (H u₀))) = -(Complex.I • gT sys hL hn H U u₀ t) := by
    simp only [ContinuousLinearMap.coe_restrictScalars', map_neg, map_smul]
    rfl
  rw [← e]
  exact hd

lemma continuous_aT (hcont : ∀ x, Continuous fun t => U t x) :
    Continuous (aT sys hL hn U u₀) :=
  (ext eta n).continuous.comp ((exp (Sig sys L n hL hn)).continuous.comp (hcont _))

lemma continuous_gT (hcont : ∀ x, Continuous fun t => U t x) :
    Continuous (gT sys hL hn H U u₀) :=
  (ext eta n).continuous.comp ((exp (Sig sys L n hL hn)).continuous.comp (hcont _))

lemma continuous_fT (hcont : ∀ x, Continuous fun t => U t x) :
    Continuous (fT sys hL hn H U u₀) := by
  unfold fT
  refine (continuous_gT sys hL hn H U u₀ hcont).sub ?_
  exact (LinearMap.continuous_of_finiteDimensional _).comp (continuous_aT sys hL hn U u₀ hcont)

include hKernel in
/-- `H w + B ψ̃(t) = e^{Σ} U(t) H u₀` for the (unique) `w` with `S w = ψ̃(t)`. -/
lemma dressed_H
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      Sm eta L u' = U t (Sm eta L u) ∧ H u' = U t (H u))
    (t : ℝ) (w : MolecularFourierH2 eta) (hw : Sm eta L w = psiT sys hL hn U u₀ t) :
    H w + Bcorr sys hL hn H (psiT sys hL hn U u₀ t) = exp (Sig sys L n hL hn) (U t (H u₀)) := by
  obtain ⟨u', hu'1, hu'2⟩ := hgraph t u₀
  have hw0 : Sm eta L (exp (SigG sys hL hn) u') = psiT sys hL hn U u₀ t := by
    rw [exp_SigG_apply, hu'1]; rfl
  have hww : w = exp (SigG sys hL hn) u' :=
    molecularH2StateMap_injective eta (gF L) (hw.trans hw0.symm)
  have hc := congrArg (fun A : L2 eta →L[ℂ] L2 eta => A (exp (SigG sys hL hn) u'))
    (conj_H sys hL hn H hKernel)
  simp only [mul_apply_eq_comp, add_apply, exp_neg_SigG_exp_SigG] at hc
  rw [hww, ← hw0, ← hc, hu'2]

include hKernel in
/-- **The coupling is `Ṽ_{PR} ψ̃_R`**: `f(t) = P W R ψ̃(t) + P B R ψ̃(t)`, where `R ψ̃ = S (w - P w)`
for the `w` with `S w = ψ̃(t)`. -/
theorem fT_eq
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      Sm eta L u' = U t (Sm eta L u) ∧ H u' = U t (H u))
    (t : ℝ) (w : MolecularFourierH2 eta) (hw : Sm eta L w = psiT sys hL hn U u₀ t) :
    fT sys hL hn H U u₀ t =
      ext eta n (Wp sys L H (w - molecularH2Truncate n w)) +
        ext eta n (Bcorr sys hL hn H (psiT sys hL hn U u₀ t -
          molecularH2Truncate n (psiT sys hL hn U u₀ t))) := by
  have hH := dressed_H sys hL hn H hKernel U u₀ hgraph t w hw
  have hext := extract_H_eq sys L H hKernel n w
  unfold fT gT
  rw [← hH, map_add, hext]
  have ha : ext eta n (Sm eta L w) = aT sys hL hn U u₀ t := by rw [hw]; rfl
  have hsplit : psiT sys hL hn U u₀ t = emb eta n (aT sys hL hn U u₀ t) +
      (psiT sys hL hn U u₀ t - molecularH2Truncate n (psiT sys hL hn U u₀ t)) := by
    rw [aT, emb_ext]; abel
  conv_lhs => rw [hsplit, map_add, map_add]
  have hd : ext eta n (Bcorr sys hL hn H (emb eta n (aT sys hL hn U u₀ t))) =
      dH sys hL hn H (aT sys hL hn U u₀ t) := rfl
  rw [hd]
  change finiteCoulombHamiltonian sys L n (ext eta n (Sm eta L w)) +
      ext eta n (Wp sys L H (w - molecularH2Truncate n w)) +
      (dH sys hL hn H (aT sys hL hn U u₀ t) + _) -
      (finiteCoulombHamiltonian sys L n (aT sys hL hn U u₀ t) + dH sys hL hn H (aT sys hL hn U u₀ t)) = _
  rw [ha]
  abel

/-! ## Duhamel for the retained part -/

/-- The flow of `H' = H_N + ΔH` is unitary: `⟪x, e^{iH'τ} y⟫ = ⟪e^{-iH'τ} x, y⟫`. -/
lemma inner_retFlow_adj {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) (τ : ℝ)
    (x y : En eta n) :
    ⟪x, retFlow sys L n hΔsym τ y⟫_ℂ = ⟪retFlow sys L n hΔsym (-τ) x, y⟫_ℂ := by
  set b := retBasis sys L n hΔsym
  have hL : ∀ z w : En eta n, ⟪z, w⟫_ℂ = ∑ i, ⟪z, b i⟫_ℂ * ⟪b i, w⟫_ℂ :=
    fun z w => (b.sum_inner_mul_inner z w).symm
  rw [hL, hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_retFlow, ← inner_conj_symm (retFlow sys L n hΔsym (-τ) x), inner_retFlow, map_mul,
    inner_conj_symm, ← Complex.exp_conj]
  have : (starRingEnd ℂ) (Complex.I * (retEig sys L n hΔsym i : ℂ) * ((-τ : ℝ) : ℂ)) =
      Complex.I * (retEig sys L n hΔsym i : ℂ) * (τ : ℂ) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  rw [this]; ring

/-- **Duhamel for the retained part** (`prop:nf`, second display), weak form:
`⟪a(t), v⟫ = ⟪e^{-iH't} a(0), v⟫ + i ∫₀ᵗ ⟪f(s), e^{iH'(t-s)} v⟫ ds` for any `a` with
`a' = -i (H' a + f)`. -/
theorem duhamel_weak_of {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric)
    (a f : ℝ → En eta n) (hf : Continuous f)
    (ha : ∀ s, HasDerivAt a (-(Complex.I • (Hret sys L n ΔH (a s) + f s))) s)
    (t : ℝ) (v : En eta n) :
    ⟪a t, v⟫_ℂ = ⟪retFlow sys L n hΔsym (-t) (a 0), v⟫_ℂ +
      Complex.I * ∫ s in (0 : ℝ)..t, ⟪f s, retFlow sys L n hΔsym (t - s) v⟫_ℂ := by
  set r : ℝ → En eta n := fun s => retFlow sys L n hΔsym (t - s) v
  have hr : ∀ s, HasDerivAt r (-(Complex.I • Hret sys L n ΔH (r s))) s := by
    intro s
    have h1 := hasDerivAt_retFlow sys L n hΔsym (t - s) v
    have h2 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h3 := h1.scomp s h2
    simpa [r, Function.comp_def, neg_one_smul] using h3
  have hsym := Hret_isSymmetric sys L n hΔsym
  have hφ : ∀ s, HasDerivAt (fun s => ⟪a s, r s⟫_ℂ) (Complex.I * ⟪f s, r s⟫_ℂ) s := by
    intro s
    have h := (ha s).inner ℂ (hr s)
    have e : ⟪a s, -(Complex.I • Hret sys L n ΔH (r s))⟫_ℂ +
        ⟪-(Complex.I • (Hret sys L n ΔH (a s) + f s)), r s⟫_ℂ = Complex.I * ⟪f s, r s⟫_ℂ := by
      rw [inner_neg_right, inner_neg_left, inner_smul_right, inner_smul_left, inner_add_left,
        hsym (a s) (r s), Complex.conj_I]
      ring
    exact h.congr_deriv e
  have hcont : Continuous fun s => Complex.I * ⟪f s, r s⟫_ℂ :=
    continuous_const.mul (hf.inner (continuous_retFlow sys L n hΔsym v |>.comp
      (continuous_const.sub continuous_id)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun s _ => hφ s) (hcont.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_const_mul] at hftc
  have h0 : ⟪a 0, r 0⟫_ℂ = ⟪retFlow sys L n hΔsym (-t) (a 0), v⟫_ℂ := by
    simp only [r, sub_zero]; exact inner_retFlow_adj sys hΔsym t (a 0) v
  have ht : ⟪a t, r t⟫_ℂ = ⟪a t, v⟫_ℂ := by simp only [r, sub_self, retFlow_zero]
  rw [ht, h0] at hftc
  rw [hftc]; ring

include hKernel in
/-- **Duhamel for the dressed exact trajectory.** -/
theorem duhamel_weak
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      Sm eta L u' = U t (Sm eta L u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (Sm eta L u)) (-(Complex.I • U t (H u))) t)
    (hcont : ∀ x, Continuous fun t => U t x) (t : ℝ) (v : En eta n) :
    ⟪aT sys hL hn U u₀ t, v⟫_ℂ =
      ⟪retFlow sys L n (dH_symm sys hL hn H hKernel) (-t) (aT sys hL hn U u₀ 0), v⟫_ℂ +
      Complex.I * ∫ s in (0 : ℝ)..t,
        ⟪fT sys hL hn H U u₀ s, retFlow sys L n (dH_symm sys hL hn H hKernel) (t - s) v⟫_ℂ := by
  have _hg := hgraph
  refine duhamel_weak_of sys (dH_symm sys hL hn H hKernel) _ _
    (continuous_fT sys hL hn H U u₀ hcont) (fun s => ?_) t v
  have h := aT_hasDerivAt sys hL hn H U u₀ hderiv s
  have e : gT sys hL hn H U u₀ s = Hret sys L n (dH sys hL hn H) (aT sys hL hn U u₀ s) +
      fT sys hL hn H U u₀ s := by unfold fT; abel
  rw [← e]; exact h

/-! ## The assembly identity -/

omit [Fintype ν] in
/-- **The assembly identity** (eq:nf-assembly). For a unitary `Ũ` on `ℓ²` (the dressing
`e^{Σ}`), a self-adjoint `O`, `ψ̃ = Ũ ψ`, `Ã = Ũ O Ũ*`, the retained part `a = P ψ̃`, the
exterior part `r = R ψ̃`, and any `ψ_N, χ ∈ E_n`:
`⟪ψ, O ψ⟫ - ⟪ψ_N, O ψ_N⟫ = [⟪χ, Oχ⟫ - ⟪ψ_N, Oψ_N⟫] + ⟪χ, (PÃP - O)χ⟫
  + [⟪a, PÃP a⟫ - ⟪χ, PÃP χ⟫] + ⟪r, Ã r⟫ + 2 Re ⟪a, Ã r⟫` (with `O = POP` on `E_n`). -/
theorem assembly (n : ℕ) {Ut : L2 eta →L[ℂ] L2 eta} (hU : Ut ∈ unitary (L2 eta →L[ℂ] L2 eta))
    {O : L2 eta →L[ℂ] L2 eta} (hO : IsSelfAdjoint O) (ψ : L2 eta) (ψN χ : En eta n) :
    let At := Ut * O * star Ut
    let a := ext eta n (Ut ψ)
    let r := Ut ψ - molecularH2Truncate n (Ut ψ)
    let On : En eta n →L[ℂ] En eta n := ext eta n ∘L O ∘L emb eta n
    let App : En eta n →L[ℂ] En eta n := ext eta n ∘L At ∘L emb eta n
    ⟪ψ, O ψ⟫_ℂ - ⟪ψN, On ψN⟫_ℂ =
      (⟪χ, On χ⟫_ℂ - ⟪ψN, On ψN⟫_ℂ) + ⟪χ, App χ - On χ⟫_ℂ + (⟪a, App a⟫_ℂ - ⟪χ, App χ⟫_ℂ) +
        ⟪r, At r⟫_ℂ + (⟪emb eta n a, At r⟫_ℂ + conj ⟪emb eta n a, At r⟫_ℂ) := by
  intro At a r On App
  -- `⟪ψ, O ψ⟫ = ⟪ψ̃, Ã ψ̃⟫`
  have hstar : star Ut * Ut = 1 := (Unitary.mem_iff.mp hU).1
  have hpres : ∀ x y, ⟪Ut x, Ut y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      ← mul_apply_eq_comp, hstar, one_apply_eq_self]
  have h1 : ⟪ψ, O ψ⟫_ℂ = ⟪Ut ψ, At (Ut ψ)⟫_ℂ := by
    have e : At (Ut ψ) = Ut (O ψ) := by
      simp only [At, mul_apply_eq_comp]
      have := congrArg (fun A : L2 eta →L[ℂ] L2 eta => A ψ) hstar
      simp only [mul_apply_eq_comp, one_apply_eq_self] at this
      rw [this]
    rw [e, hpres]
  -- `Ã` is self-adjoint
  have hAt : ∀ x y, ⟪At x, y⟫_ℂ = ⟪x, At y⟫_ℂ := by
    have hsa : IsSelfAdjoint At := by
      simp only [At]
      exact hO.conjugate Ut
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint, hsa.star_eq]
  -- split `ψ̃ = emb a + r`
  have hsplit : Ut ψ = emb eta n a + r := by
    simp only [a, r, emb_ext]; abel
  have hPP : ⟪emb eta n a, At (emb eta n a)⟫_ℂ = ⟪a, App a⟫_ℂ := by
    simp only [App, ContinuousLinearMap.comp_apply]
    rw [inner_ext']
  have hRP : ⟪r, At (emb eta n a)⟫_ℂ = conj ⟪emb eta n a, At r⟫_ℂ := by
    rw [← hAt, inner_conj_symm]
  rw [h1, hsplit, map_add, inner_add_left, inner_add_right, inner_add_right, hPP, hRP]
  rw [inner_sub_right]
  ring

end FSNormal
