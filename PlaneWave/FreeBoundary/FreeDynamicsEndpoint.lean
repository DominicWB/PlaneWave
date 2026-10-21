import PlaneWave.FreeBoundary.RegularityBridge

/-!
# `prop:free-dyn` in the form of the manuscript

`prop:free-dyn` bounds `|⟨ψ(t), χ(x_a) ψ(t)⟩ - ⟨ψ_g(t), O_g ψ_g(t)⟩|` by
`C [K⁻⁵ + t K⁻³] + C (1 + t) ε_leak`, with `C` uniform in `L`. The earlier statements carry the
factor `‖ψ(t)‖ + ‖ψ(0)‖`; along a solution curve of the free-space Hamiltonian the norm is
conserved, since `⟨f, H_∞ f⟩` is real: for the weak kinetic relation `K f = z`,
`⟨f, z⟩ = (1/2) Σ_a m_a⁻¹ ‖∂_a f‖²`.

* `inner_weak_kinetic`, `inner_hamiltonian_im`, **`norm_conserved`**: conservation of the norm;
* `dynConst`, `le_dynConst_form`, `dyn_mono_form`: the constant and the form of the bound;
* **`free_dyn_endpoint`** (any system, the domain condition (H_dom) as a hypothesis) and
  **`free_dyn_nbo_endpoint`** (no clamped nuclei, from the Hamiltonian relations): the bound
  `C [K⁻⁵ + t K⁻³] + C (1 + t) ε`, `0 ≤ ε ≤ 1`, with `C = freeDynConst …`, `freeDynConstNBO …`
  independent of `L`;
* `freeDynL0`, `quadCutoffL`, `isGridKernel_sharp`: the threshold
  `L₀ = max(8, 2π, 2R_f + 1, 16(R₀ + ρ))`, the explicit cutoff `F(Σ_i m_i |x_i|²/(L/8)²)` and the
  truncated kernel;
* **`free_dyn_uniform`**, **`free_dyn_nbo_uniform`**: one constant for every `L ≥ L₀`, with the
  explicit cutoff and its leakage regions, the cell observable and every kernel of the class.

Conventions. The constants read only the masses and charges of the particles and the charges of
the nuclei, not the positions of the nuclei (`freeDynConst_sysAt`); `free_dyn_uniform` is stated
for the molecule in the cell of size `L`, `sysAt sys P L`. The shape bounds
`D̄ = (quadCutoff8 _).D`, `C̄ = (quadCutoff8 _).C` are fixed numbers from the existence proof of the
shape (`exists_quadCutoff`), independent of `L`; the cutoff function itself is explicit. The grid
observable is `posObs a (chiRefl χ)`, the collocation of the reflected multiplier `χ(-·)`, which
matches the sign of the phases of `idft`. In (H_dom) the torus Hamiltonian is the `g_L`
Hamiltonian with the zero mode removed; it differs from `H_L` by the constant `C₀`, `|C₀| ≤ Q/4`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology FourierTransform SchwartzMap
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

open PlaneWaveGridG (gLgamma gLgamma_pos gLref gLNucData regParticlesOfG gLzU gLzU_nonneg gLAU
  gLGridCoupling)

namespace FreeBoundary

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Conservation of the norm -/

section Conservation

lemma inner_L2_eq (F G : FreeL2 eta) : ⟪F, G⟫_ℂ = ∫ x, conj (F x) * G x := by
  rw [MeasureTheory.L2.inner_def]
  exact integral_congr_ae (ae_of_all _ fun x => RCLike.inner_apply' _ _)

/-- **The weak kinetic energy**: if `K f = z` weakly and `g` is the weak gradient of `f`, then
`⟨f, z⟩ = (1/2) Σ_a m_a⁻¹ ‖g_a‖²`. -/
theorem inner_weak_kinetic {m : Fin eta → ℝ} {f z : FreeL2 eta} (hK : HasFreeWeakKinetic m f z)
    {g : Fin eta × Fin 3 → FreeL2 eta} (hg : HasWeakGrad f g) :
    ⟪f, z⟫_ℂ = (((1 / 2) * ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ‖g a‖ ^ 2 : ℝ) : ℂ) := by
  have hf := locInt_L2 f
  -- the identity for `f_n = ρ_n ⋆ f`
  have hn : ∀ n : ℕ, ⟪mollN n f, mollN n z⟫_ℂ =
      (((1 / 2) * ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ‖mollN n (g a)‖ ^ 2 : ℝ) : ℂ) := by
    intro n
    have hσ : ContDiff ℝ 3 (rhoN (eta := eta) n) := contDiff_rhoN n
    have hσc := hasCompactSupport_rhoN (eta := eta) n
    obtain ⟨d1, d2, -⟩ := moll_derivs hσ hσc f
    have hF : ContDiff ℝ 2 (moll (rhoN n) f) := contDiff_moll hσc (contDiff_rhoN n) hf
    have h0 : MemLp (moll (rhoN n) f) 2 volume := memLp_moll_k hσc hσ.continuous f
    have h1 : ∀ a, MemLp (dirD a (moll (rhoN n) f)) 2 volume := fun a => by
      rw [d1 a]
      exact memLp_moll_k ((rhoN_props n).1 a).1 ((rhoN_props n).1 a).2 f
    have h2 : ∀ a, MemLp (dirD a (dirD a (moll (rhoN n) f))) 2 volume := fun a => by
      rw [d2 a a]
      exact memLp_moll_k ((rhoN_props n).2 a a).1 ((rhoN_props n).2 a a).2 f
    have e1 := energy_one m hF h0 h1 h2
    have hKF : ∀ x, freeKinetic m (moll (rhoN n) f) x = moll (rhoN n) z x := fun x => by
      rw [freeKinetic_moll m hσc hσ f x, moll_kin_eq hK hσc (hσ.of_le (by norm_num)) x]
    have hd : ∀ a x, dirD a (moll (rhoN n) f) x = moll (rhoN n) (g a) x := fun a x => by
      rw [d1 a]
      exact moll_dirD_eq hg hσc (hσ.of_le (by norm_num)) a x
    simp_rw [hKF, hd] at e1
    rw [inner_L2_eq]
    have hl : ∫ x, conj (mollN n f x) * mollN n z x =
        ∫ x, conj (moll (rhoN n) f x) * moll (rhoN n) z x := by
      refine integral_congr_ae ?_
      filter_upwards [mollN_ae n f, mollN_ae n z] with x h1 h2
      rw [h1, h2]
    have hs : ∀ a, ∫ x, ‖moll (rhoN n) (g a) x‖ ^ 2 = ‖mollN n (g a)‖ ^ 2 := fun a =>
      (norm_sq_eq_of_ae (mollN_ae n (g a))).symm
    rw [hl, e1]
    simp_rw [hs]
  -- the limit
  have hL : Tendsto (fun n => ⟪mollN n f, mollN n z⟫_ℂ) atTop (𝓝 ⟪f, z⟫_ℂ) :=
    (tendsto_mollN f).inner (tendsto_mollN z)
  have hR : Tendsto (fun n : ℕ =>
      (((1 / 2) * ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ‖mollN n (g a)‖ ^ 2 : ℝ) : ℂ)) atTop
      (𝓝 (((1 / 2) * ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ‖g a‖ ^ 2 : ℝ) : ℂ)) := by
    have hs : Tendsto (fun n : ℕ => ∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ‖mollN n (g a)‖ ^ 2)
        atTop (𝓝 (∑ a : Fin eta × Fin 3, (m a.1)⁻¹ * ‖g a‖ ^ 2)) :=
      tendsto_finsetSum (f := fun a n => (m a.1)⁻¹ * ‖mollN n (g a)‖ ^ 2) Finset.univ
        fun a _ => (((tendsto_mollN (g a)).norm).pow 2).const_mul _
    exact (Complex.continuous_ofReal.tendsto _).comp (hs.const_mul (1 / 2))
  exact tendsto_nhds_unique (hL.congr hn) hR

/-- `⟨f, H_∞ f⟩` is real. -/
theorem inner_hamiltonian_im (sys : CoulombSystem eta ν) (P : ν → E3) {f h : FreeL2 eta}
    (hH : HasFreeHamiltonian sys P f h) : (⟪f, h⟫_ℂ).im = 0 := by
  obtain ⟨v, hv, hK⟩ := hH
  obtain ⟨g, -, hg, -⟩ := weak_kinetic_regularity (fun i => sys.mass_pos i) hK
  have e1 := inner_weak_kinetic hK hg
  have e2 : ⟪f, v⟫_ℂ = ((∫ x, freePot sys P x * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_L2_eq, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hv] with x hx
    rw [hx, ← mul_assoc, mul_comm (conj (f x)), mul_assoc, Complex.conj_mul']
    push_cast
    ring
  have e3 : h = (h - v) + v := by abel
  rw [e3, inner_add_right, e1, e2, Complex.add_im, Complex.ofReal_im, Complex.ofReal_im,
    add_zero]

/-- **Conservation of the norm** along a solution curve `i ψ' = H_∞ ψ`. -/
theorem norm_conserved (sys : CoulombSystem eta ν) (P : ν → E3) {ψ H : ℝ → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s)) (t : ℝ) : ‖ψ t‖ = ‖ψ 0‖ := by
  have hd : ∀ s, HasDerivAt (fun s => ⟪ψ s, ψ s⟫_ℂ) 0 s := by
    intro s
    have h := (hψd s).inner ℂ (hψd s)
    have hre := inner_hamiltonian_im sys P (hHam s)
    have h0 : ⟪ψ s, -(Complex.I • H s)⟫_ℂ + ⟪-(Complex.I • H s), ψ s⟫_ℂ = 0 := by
      have hw : ⟪H s, ψ s⟫_ℂ = ⟪ψ s, H s⟫_ℂ := by
        rw [← inner_conj_symm (H s) (ψ s)]
        apply Complex.ext
        · rw [Complex.conj_re]
        · rw [Complex.conj_im, hre, neg_zero]
      rw [inner_neg_right, inner_neg_left, inner_smul_right, inner_smul_left, Complex.conj_I, hw]
      ring
    rw [h0] at h
    exact h
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simp only [inner_self_eq_norm_sq_to_K] at hc
  have h2 : ‖ψ t‖ ^ 2 = ‖ψ 0‖ ^ 2 := by exact_mod_cast hc
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

end Conservation

/-! ## The form of the bound -/

section Form

/-- The constant `C = 1 + 2 N c + max(A₁ + (A₃ 3^{5/2} + N²) T, 0) + max(A₂, 0)` of the
manuscript's form, from grid constants `A = (A₁, A₂, A₃)`, a data norm `N`, the tail constant `T`
of the observable and the commutator constant `c`. -/
noncomputable def dynConst (A : ℝ × ℝ × ℝ) (N T c : ℝ) : ℝ :=
  1 + 2 * N * c + max (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * T) 0 + max A.2.1 0

/-- `ε² + n c ε t + A₁' K⁻⁵ + A₂ t K⁻³ ≤ C [K⁻⁵ + t K⁻³] + C (1 + t) ε` for `0 ≤ ε ≤ 1` and
`n ≤ 2N`. -/
lemma le_dynConst_form {A : ℝ × ℝ × ℝ} {N T c n ε t K : ℝ} (hN : 0 ≤ N) (hc : 0 ≤ c)
    (hn : n ≤ 2 * N) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) (hK : 0 < K) :
    ε ^ 2 + n * (c * ε * t) + ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * T) * (1 / K) ^ 5 +
        A.2.1 * t * (1 / K) ^ 3) ≤
      dynConst A N T c * ((1 / K) ^ 5 + t * (1 / K) ^ 3) + dynConst A N T c * (1 + t) * ε := by
  have hC : dynConst A N T c = 1 + 2 * N * c +
      max (A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * T) 0 + max A.2.1 0 := rfl
  rw [hC]
  set A1 := A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * T
  set A2 := A.2.1
  set k5 := (1 / K) ^ 5
  set k3 := (1 / K) ^ 3
  have hk5 : 0 ≤ k5 := by positivity
  have hk3 : 0 ≤ k3 := by positivity
  have hm1 : A1 ≤ max A1 0 := le_max_left _ _
  have hm1' : 0 ≤ max A1 0 := le_max_right _ _
  have hm2 : A2 ≤ max A2 0 := le_max_left _ _
  have hm2' : 0 ≤ max A2 0 := le_max_right _ _
  have hNc : 0 ≤ 2 * N * c := by positivity
  have e1 : ε ^ 2 ≤ ε := by nlinarith
  have e2 : n * (c * ε * t) ≤ 2 * N * c * (t * ε) := by
    have h0 : 0 ≤ c * ε * t := by positivity
    have := mul_le_mul_of_nonneg_right hn h0
    linarith
  have e3 : A1 * k5 ≤ max A1 0 * k5 := mul_le_mul_of_nonneg_right hm1 hk5
  have e4 : A2 * t * k3 ≤ max A2 0 * (t * k3) := by
    have := mul_le_mul_of_nonneg_right hm2 (mul_nonneg ht hk3)
    linarith
  have r1 : 0 ≤ (1 + 2 * N * c + max A2 0) * k5 := mul_nonneg (by linarith) hk5
  have r2 : 0 ≤ (1 + 2 * N * c + max A1 0) * (t * k3) :=
    mul_nonneg (by linarith) (mul_nonneg ht hk3)
  have r3 : 0 ≤ (2 * N * c + max A1 0 + max A2 0) * ε := mul_nonneg (by linarith) hε
  have r4 : 0 ≤ (1 + max A1 0 + max A2 0) * (t * ε) :=
    mul_nonneg (by linarith) (mul_nonneg ht hε)
  nlinarith [e1, e2, e3, e4, r1, r2, r3, r4]

/-- The bound with grid constants `A ≤ A'`, data `N ≤ N'` and commutator constant `c ≤ c'`, in the
manuscript's form. -/
lemma dyn_mono_form {A A' : ℝ × ℝ × ℝ} {N N' T c c' n ε t K : ℝ} (m1 : A.1 ≤ A'.1)
    (m2 : A.2.1 ≤ A'.2.1) (m3 : A.2.2 ≤ A'.2.2) (hN : 0 ≤ N) (hNN : N ≤ N') (hT : 0 ≤ T)
    (hcc : c ≤ c') (hc' : 0 ≤ c') (hn0 : 0 ≤ n) (hn : n ≤ 2 * N') (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ht : 0 ≤ t) (hK : 0 < K) :
    ε ^ 2 + n * (c * ε * t) + ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * T) * (1 / K) ^ 5 +
        A.2.1 * t * (1 / K) ^ 3) ≤
      dynConst A' N' T c' * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
        dynConst A' N' T c' * (1 + t) * ε := by
  have hN' : 0 ≤ N' := hN.trans hNN
  have hεt : 0 ≤ ε * t := mul_nonneg hε ht
  have hmid : ε ^ 2 + n * (c * ε * t) +
      ((A.1 + (A.2.2 * Real.sqrt 3 ^ 5 + N ^ 2) * T) * (1 / K) ^ 5 + A.2.1 * t * (1 / K) ^ 3) ≤
      ε ^ 2 + n * (c' * ε * t) +
        ((A'.1 + (A'.2.2 * Real.sqrt 3 ^ 5 + N' ^ 2) * T) * (1 / K) ^ 5 +
          A'.2.1 * t * (1 / K) ^ 3) := by
    gcongr
  exact hmid.trans (le_dynConst_form hN' hc' hn hε hε1 ht hK)

/-- The constant of `prop:free-dyn` for a system with the domain condition, data bound `𝒟` and
cutoff derivative bound `D̄`. -/
noncomputable def freeDynConst (sys : CoulombSystem eta ν) (V : ℝ) (F : 𝓢(E3, ℂ)) (Dbar 𝒟 : ℝ) :
    ℝ :=
  dynConst (gridConstsSharp_gLU sys V molecularCanonicalUnitHardyConstant (obsMomC (ftDecay F))
    (obsMomC (ftDecay F)) (obsMomD2 (ftDecay F)) (obsMomD4 (ftDecay F)) 𝒟 𝒟 𝒟 𝒟) 𝒟
    (obsTailC (ftDecay F) 5) ((Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2))

/-- The constant of `prop:free-dyn` without clamped nuclei, for `‖ψ₀‖ + ‖H_∞ ψ₀‖ + ‖H_∞² ψ₀‖ ≤ D`
and cutoff bounds `D̄`, `C̄`. -/
noncomputable def freeDynConstNBO (sys : CoulombSystem eta ν) (V : ℝ) (F : 𝓢(E3, ℂ))
    (Dbar Cbar D : ℝ) : ℝ :=
  dynConst (gridConstsSharp_gLU sys V molecularCanonicalUnitHardyConstant (obsMomC (ftDecay F))
    (obsMomC (ftDecay F)) (obsMomD2 (ftDecay F)) (obsMomD4 (ftDecay F)) (regConst sys * D)
    (domConst sys.charge (zeroWeight sys / 4) Dbar Cbar * (regConst sys * D))
    (domConst sys.charge (zeroWeight sys / 4) Dbar Cbar * (regConst sys * D))
    (domConst sys.charge (zeroWeight sys / 4) Dbar Cbar ^ 2 * (regConst sys * D)))
    (regConst sys * D) (obsTailC (ftDecay F) 5)
    ((Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2))

/-- The constant does not depend on the positions of the nuclei: it is the same for the molecule
in every cell (`sysAt sys P L`). -/
lemma freeDynConst_sysAt (sys : CoulombSystem eta ν) (P : ν → E3) (L V : ℝ) (F : 𝓢(E3, ℂ))
    (Dbar 𝒟 : ℝ) : freeDynConst (sysAt sys P L) V F Dbar 𝒟 = freeDynConst sys V F Dbar 𝒟 := rfl

lemma freeDynConstNBO_sysAt (sys : CoulombSystem eta ν) (P : ν → E3) (L V : ℝ) (F : 𝓢(E3, ℂ))
    (Dbar Cbar D : ℝ) :
    freeDynConstNBO (sysAt sys P L) V F Dbar Cbar D = freeDynConstNBO sys V F Dbar Cbar D := rfl

end Form

/-! ## The endpoints -/

section Endpoints

lemma obs_consts_nonneg (F : 𝓢(E3, ℂ)) :
    0 ≤ obsMomC (ftDecay F) ∧ 0 ≤ obsMomD2 (ftDecay F) ∧ 0 ≤ obsMomD4 (ftDecay F) ∧
      0 ≤ obsTailC (ftDecay F) 5 := by
  have hB : ∀ n, 0 ≤ ftDecay F n := ftDecay_nonneg F
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold obsMomC; have := hB 6; positivity
  · unfold obsMomD2; have := hB 8; positivity
  · unfold obsMomD4; have := hB 10; positivity
  · unfold obsTailC; have := hB 11; positivity

lemma hardyUnit_nonneg : 0 ≤ molecularCanonicalUnitHardyConstant := by
  unfold molecularCanonicalUnitHardyConstant
  positivity

/-- **`prop:free-dyn` in the manuscript's form** (any system; the domain condition (H_dom) as a
hypothesis, with `‖ψ₀‖, ‖φ₀‖, ‖H_L φ₀‖, ‖H_L² φ₀‖ ≤ 𝒟`): for `0 ≤ ε ≤ 1`,
`|⟨ψ(t), χ(x_a) ψ(t)⟩ - ⟨ψ_g(t), O_g ψ_g(t)⟩| ≤ C [K⁻⁵ + t K⁻³] + C (1 + t) ε` with
`C = freeDynConst sys V_θ F D̄ 𝒟`, which does not depend on `L`. -/
theorem free_dyn_endpoint (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : Cutoff eta L) (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Dbar : ℝ} (hD1 : X.D1 ≤ Dbar) (hD2 : X.D2 ≤ Dbar)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian sys L θ (X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0))
      h₀)
    (hdom1 : HasGLHamiltonian sys L θ h₀ h₁) {𝒟 : ℝ} (hψ0 : ‖ψ 0‖ ≤ 𝒟)
    (hn0 : ‖X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)‖ ≤ 𝒟) (hn1 : ‖h₀‖ ≤ 𝒟)
    (hn2 : ‖h₁‖ ≤ 𝒟)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
      let φ₀ := X.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConst sys (tv R θ) F Dbar 𝒟 * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConst sys (tv R θ) F Dbar 𝒟 * (1 + t) * ε := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_grid_gLU_schwartz_cell sys
    hL2 hθ hR hR0 hρ hone P hP hpos X hret hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0
    hleak1 hdom0 hdom1 a hf0 hf1 F hFf hfR hRL m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ φ₀ K ψg
  refine le_trans hbound ?_
  have h𝒟 : 0 ≤ 𝒟 := (norm_nonneg _).trans hψ0
  have hV := hθ.tv_nonneg
  obtain ⟨hC6, hD2, hD4, hT⟩ := obs_consts_nonneg F
  obtain ⟨m1, m2, m3⟩ := gridConstsSharp_gLU_mono_data sys hV hardyUnit_nonneg hC6 hC6 hD2 hD4
    (norm_nonneg φ₀) (norm_nonneg h₀) (norm_nonneg h₀) (norm_nonneg h₁) hn0 hn1 hn1 hn2
  have hcomm : X.commConst ≤ (Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2) := by
    unfold Cutoff.commConst
    have : X.D1 + X.D2 / 2 ≤ Dbar + Dbar / 2 := by linarith
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have hc' : 0 ≤ (Fintype.card (Fin eta × Fin 3) : ℝ) * (Dbar + Dbar / 2) := by
    rcases isEmpty_or_nonempty (Fin eta × Fin 3) with he | ⟨⟨a0⟩⟩
    · rw [Fintype.card_eq_zero, Nat.cast_zero, zero_mul]
    · have h1 : 0 ≤ X.D1 := (abs_nonneg _).trans (X.d1 0 a0)
      have h2 : 0 ≤ X.D2 := (abs_nonneg _).trans (X.d2 0 a0)
      have : 0 ≤ Dbar := h1.trans hD1
      positivity
  have hcons := norm_conserved sys P hψd hHam t
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  exact dyn_mono_form m1 m2 m3 (norm_nonneg _) hn0 hT hcomm hc' (by positivity)
    (by rw [hcons]; linarith) hε hε1 ht hKpos

/-- **`prop:free-dyn` in the manuscript's form without clamped nuclei**, from the Hamiltonian
relations: for `‖ψ₀‖ + ‖H_∞ ψ₀‖ + ‖H_∞² ψ₀‖ ≤ D` and `0 ≤ ε ≤ 1`, the error is at most
`C [K⁻⁵ + t K⁻³] + C (1 + t) ε` with `C = freeDynConstNBO sys V_θ F D̄ C̄ D`, independent of `L`. -/

theorem free_dyn_nbo_endpoint [IsEmpty ν] (sys : CoulombSystem eta ν) {L R R0 ρ : ℝ} {θ : ℝ → ℝ}
    (hL2 : 2 * Real.pi ≤ L) (hθ : Profile R θ) (hR : R ≤ L / 2) (hR0 : 0 ≤ R0) (hρ : 0 ≤ ρ)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    (X : DomCutoff eta L sys.mass)
    (hret : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ)
    {Dbar Cbar : ℝ} (hDbar : X.D ≤ Dbar) (hCbar : X.C ≤ Cbar)
    {Bone S : Set (Rcfg eta)} (hSm : MeasurableSet S) (hBm : MeasurableSet Bone)
    (hχB : ∀ r ∈ Bone, X.χ r = 1) (hSB : S ⊆ Boneᶜ)
    (hdS : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0)
    (hd2S : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in Boneᶜ, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in S, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    {Rf : ℝ} (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf) (hRL : 2 * Rf < L)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (lt_of_lt_of_le (by positivity) hL2) (continuous_of_schwartz F hFf) hfR hRL
      let φ₀ := X.toCutoff.chiW.cutL2 (lt_of_lt_of_le (by positivity) hL2) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConstNBO sys (tv R θ) F Dbar Cbar D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstNBO sys (tv R θ) F Dbar Cbar D * (1 + t) * ε := by
  have hL : 0 < L := lt_of_lt_of_le (by positivity) hL2
  obtain ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, hbound⟩ := free_dyn_grid_nbo_reg sys hL2 hθ hR
    hR0 hρ hone P hP hpos X hret hDbar hCbar hSm hBm hχB hSB hdS hd2S hψd hHam hgrad ht hε hleak0
    hleak1 hH1 a hf0 hf1 F hFf hfR hRL m hκ hm hK
  refine ⟨Ug, hg0, hgadd, hgcont, hgcomm, hgderiv, ?_⟩
  intro χ φ₀ K ψg
  refine le_trans hbound ?_
  have hreg := one_le_regConst sys
  have hdat : 0 ≤ ‖ψ 0‖ + ‖H 0‖ + ‖k‖ := by positivity
  have hD0 : 0 ≤ D := hdat.trans hD
  have hN0 : 0 ≤ regConst sys * (‖ψ 0‖ + ‖H 0‖ + ‖k‖) := by positivity
  have hNN : regConst sys * (‖ψ 0‖ + ‖H 0‖ + ‖k‖) ≤ regConst sys * D :=
    mul_le_mul_of_nonneg_left hD (by linarith)
  have hDb : 0 ≤ Dbar := X.D_nonneg.trans hDbar
  have hCb : 0 ≤ Cbar := X.C_nonneg.trans hCbar
  have hc₀ : 0 ≤ zeroWeight sys / 4 := by have := zeroWeight_nonneg sys; positivity
  have hΛ1 : 1 ≤ domConst sys.charge (zeroWeight sys / 4) Dbar Cbar :=
    one_le_domConst sys.charge hc₀ hDb hCb
  have hΛ0 : 0 ≤ domConst sys.charge (zeroWeight sys / 4) Dbar Cbar := by linarith
  have e1 := mul_le_mul_of_nonneg_left hNN hΛ0
  have e2 := mul_le_mul_of_nonneg_left hNN (pow_nonneg hΛ0 2)
  have hV := hθ.tv_nonneg
  obtain ⟨hC6, hD2, hD4, hT⟩ := obs_consts_nonneg F
  obtain ⟨m1, m2, m3⟩ := gridConstsSharp_gLU_mono_data sys hV hardyUnit_nonneg hC6 hC6 hD2 hD4
    hN0 (mul_nonneg hΛ0 hN0) (mul_nonneg hΛ0 hN0) (mul_nonneg (pow_nonneg hΛ0 2) hN0) hNN e1 e1
    e2
  have hcons := norm_conserved sys P hψd hHam t
  have hKpos : 0 < K := by
    have : (8 : ℝ) ≤ K := hK
    linarith
  have hn : ‖ψ t‖ + ‖ψ 0‖ ≤ 2 * (regConst sys * D) := by
    rw [hcons]
    have h1 : ‖ψ 0‖ ≤ D := by linarith only [hD, norm_nonneg (H 0), norm_nonneg k]
    have h2 : D ≤ regConst sys * D := by nlinarith only [hreg, hD0]
    linarith only [h1, h2]
  exact dyn_mono_form m1 m2 m3 hN0 hNN hT le_rfl (by positivity) (by positivity) hn hε hε1 ht
    hKpos

end Endpoints

/-! ## The explicit cutoff, the threshold and the kernel -/

section Explicit

/-- The threshold `L₀ = max(8, 2π, 2R_f + 1, 16(R₀ + ρ))`. -/
noncomputable def freeDynL0 (R0 ρ Rf : ℝ) : ℝ :=
  max (max 8 (2 * Real.pi)) (max (2 * Rf + 1) (16 * (R0 + ρ)))

variable {R0 ρ Rf L : ℝ}

lemma eight_le_of_freeDynL0 (hL : freeDynL0 R0 ρ Rf ≤ L) : 8 ≤ L :=
  ((le_max_left _ _).trans (le_max_left _ _)).trans hL

lemma pos_of_freeDynL0 (hL : freeDynL0 R0 ρ Rf ≤ L) : 0 < L := by
  have := eight_le_of_freeDynL0 hL
  linarith

lemma two_pi_le_of_freeDynL0 (hL : freeDynL0 R0 ρ Rf ≤ L) : 2 * Real.pi ≤ L :=
  ((le_max_right _ _).trans (le_max_left _ _)).trans hL

lemma two_Rf_lt_of_freeDynL0 (hL : freeDynL0 R0 ρ Rf ≤ L) : 2 * Rf < L := by
  have : 2 * Rf + 1 ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  linarith

lemma ret_of_freeDynL0 (hL : freeDynL0 R0 ρ Rf ≤ L) : L / 8 * (3 / 2) ≤ retainedRadius L R0 ρ := by
  have : 16 * (R0 + ρ) ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  unfold retainedRadius
  linarith

variable {m : Fin eta → ℝ} (hm : ∀ i, 1 ≤ m i)

/-- A cutoff at `L` as a cutoff at `L' = L`. -/
def DomCutoff.congrL {L L' : ℝ} (X : DomCutoff eta L m) (h : L = L') : DomCutoff eta L' m :=
  h ▸ X

omit hm in
lemma DomCutoff.congrL_χ {L L' : ℝ} (X : DomCutoff eta L m) (h : L = L') :
    (X.congrL h).χ = X.χ := by
  subst h
  rfl

omit hm in
lemma DomCutoff.congrL_D {L L' : ℝ} (X : DomCutoff eta L m) (h : L = L') :
    (X.congrL h).D = X.D := by
  subst h
  rfl

omit hm in
lemma DomCutoff.congrL_C {L L' : ℝ} (X : DomCutoff eta L m) (h : L = L') :
    (X.congrL h).C = X.C := by
  subst h
  rfl

/-- The shape `F(Σ_i m_i |x_i|²)` at `L = 8` (`exists_quadCutoff`). -/
noncomputable def quadCutoff8 : DomCutoff eta 8 m := Classical.choose (exists_quadCutoff m hm)

lemma quadCutoff8_χ (r : Rcfg eta) : (quadCutoff8 hm).χ r = quadProfile (massQ m r) :=
  Classical.choose_spec (exists_quadCutoff m hm) r

/-- **The cutoff at `L ≥ 8`**: `χ_L(r) = F(Σ_i m_i |x_i|² / (L/8)²)`, the shape at `8` scaled by
`L/8`; its bounds are those of the shape (`quadCutoffL_D_le`, `quadCutoffL_C_le`). -/
noncomputable def quadCutoffL (hL : 8 ≤ L) : DomCutoff eta L m :=
  ((quadCutoff8 hm).scale (s := L / 8) (by linarith)).congrL (by ring)

omit hm in
lemma massQ_smul (c : ℝ) (r : Rcfg eta) : massQ m (c • r) = c ^ 2 * massQ m r := by
  unfold massQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit hm in
lemma massQ_scaled (c : ℝ) (r : Rcfg eta) :
    massQ m (c⁻¹ • r) = massQ m r / c ^ 2 := by
  rw [massQ_smul, inv_pow, div_eq_inv_mul]

lemma quadCutoffL_χ (hL : 8 ≤ L) (r : Rcfg eta) :
    (quadCutoffL hm hL).χ r = quadProfile (massQ m r / (L / 8) ^ 2) := by
  unfold quadCutoffL
  rw [DomCutoff.congrL_χ, ← massQ_scaled]
  exact quadCutoff8_χ hm _

lemma quadCutoffL_D_le (hL : 8 ≤ L) : (quadCutoffL hm hL).D ≤ (quadCutoff8 hm).D := by
  unfold quadCutoffL
  rw [DomCutoff.congrL_D]
  exact (quadCutoff8 hm).scale_D_le _

lemma quadCutoffL_C_le (hL : 8 ≤ L) : (quadCutoffL hm hL).C ≤ (quadCutoff8 hm).C := by
  unfold quadCutoffL
  rw [DomCutoff.congrL_C]
  exact (quadCutoff8 hm).scale_C_le _

/-- `χ_L = 1` on `B^one_L = {Σ_i m_i |x_i|² < (L/8)²}`. -/
lemma quadCutoffL_one (hL : 8 ≤ L) :
    ∀ r ∈ {r : Rcfg eta | massQ m r < (L / 8) ^ 2}, (quadCutoffL hm hL).χ r = 1 := by
  intro r hr
  rw [quadCutoffL_χ]
  apply quadProfile_one
  rw [div_le_one (by positivity)]
  exact le_of_lt hr

lemma quadCutoffL_derivs (hL : 8 ≤ L) :
    ∀ r, r ∉ {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ m r ∧ massQ m r ≤ 2 * (L / 8) ^ 2} →
      ∀ a, dirD a (quadCutoffL hm hL).χ r = 0 ∧ dirD a (dirD a (quadCutoffL hm hL).χ) r = 0 := by
  intro r hr a
  have hs : 0 < L / 8 := by linarith
  have he : (quadCutoffL hm hL).χ = fun r => quadProfile (massQ m ((L / 8)⁻¹ • r)) := by
    funext r
    rw [quadCutoffL_χ, massQ_scaled]
  have h0 : massQ m ((L / 8)⁻¹ • r) < 1 ∨ 2 < massQ m ((L / 8)⁻¹ • r) := by
    rw [massQ_scaled]
    simp only [Set.mem_setOf_eq, not_and_or, not_le] at hr
    have hs2 : 0 < (L / 8) ^ 2 := by positivity
    rcases hr with h | h
    · exact Or.inl ((div_lt_one hs2).mpr h)
    · exact Or.inr ((lt_div_iff₀ hs2).mpr (by linarith))
  rw [he]
  have hG : Differentiable ℝ (fun r : Rcfg eta => quadProfile (massQ m r)) :=
    ((contDiff_quadProfile (n := 1)).comp (contDiff_massQ m (n := 1))).differentiable
      (by norm_num)
  have hdG : Differentiable ℝ (dirD a (fun r : Rcfg eta => quadProfile (massQ m r))) :=
    (contDiff_dirD_nat (n := 1) ((contDiff_quadProfile (n := 2)).comp
      (contDiff_massQ m (n := 2))) a).differentiable (by norm_num)
  have h1 := quad_dS m h0 a
  rw [dirD_scale' hG]
  refine ⟨by simp only [h1.1, mul_zero], ?_⟩
  rw [dirD_scale hdG]
  simp only [h1.2, mul_zero]

omit hm in
lemma cfgSq_le_massQ (hm : ∀ i, 1 ≤ m i) (r : Rcfg eta) : cfgSq r ≤ massQ m r := by
  unfold cfgSq massQ
  exact Finset.sum_le_sum fun b _ => by nlinarith [hm b.1, sq_nonneg (r b)]

/-- `χ_L` is supported where every `|x_i| ≤ (3/2) (L/8)`. -/
lemma quadCutoffL_ret (hL : 8 ≤ L) :
    ∀ r, (quadCutoffL hm hL).χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ L / 8 * (3 / 2) := by
  intro r hr i
  rw [quadCutoffL_χ] at hr
  have hs : 0 < L / 8 := by linarith
  have h1 : massQ m r / (L / 8) ^ 2 < 2 := by
    by_contra h'
    exact hr (quadProfile_zero (not_lt.mp h'))
  have hs2 : 0 < (L / 8) ^ 2 := by positivity
  have h2 : massQ m r < 2 * (L / 8) ^ 2 := by
    rw [div_lt_iff₀ hs2] at h1
    linarith
  have h3 : ‖particle r i‖ ^ 2 ≤ massQ m r :=
    (norm_particle_sq_le r i).trans (cfgSq_le_massQ hm r)
  have h4 : ‖particle r i‖ ^ 2 ≤ (L / 8 * (3 / 2)) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4

/-- The truncated kernel `ĝ_L 1_{|ν|∞ ≤ 2m}` is a kernel of the class. -/
lemma isGridKernel_sharp {R : ℝ} {θ : ℝ → ℝ} (hL : 0 < L) (hθ : Profile R θ) (m : ℕ) :
    PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m
      (PlaneWaveGridG.sharpKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m) :=
  PlaneWaveGridG.sharpKernel_isGridKernel (gLgamma_pos hL hθ.tv_nonneg).le
    (PlaneWaveGridG.gLref_neg L θ _) (PlaneWaveGridG.gLref_bound hL hθ) m

end Explicit

/-! ## One constant for all cells -/

section Uniform

/-- **`prop:free-dyn`, uniform in `L`** (any system, (H_dom) assumed): for the molecule (nuclei at
`P_ℓ ∈ B_{R₀}(0)`) in the cell of size `L ≥ L₀` (`sysAt sys P L`), every profile with `V_θ = V`,
the explicit cutoff `χ_L = F(Σ_i m_i |x_i|²/(L/8)²)` (leakage measured outside
`Σ_i m_i |x_i|² < (L/8)²` and on the shell `(L/8)² ≤ Σ_i m_i |x_i|² ≤ 2 (L/8)²`), the cell
observable and every kernel of the class, the error is at most `C [K⁻⁵ + t K⁻³] + C (1 + t) ε`
with `C = freeDynConst sys V F D 𝒟` (`D` the bound of the shape), independent of `L`. -/
theorem free_dyn_uniform (sys : CoulombSystem eta ν) {R0 ρ Rf V : ℝ} (hR0 : 0 ≤ R0)
    (hρ : 0 ≤ ρ) (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0) {L R : ℝ} {θ : ℝ → ℝ}
    (hL : freeDynL0 R0 ρ Rf ≤ L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hV : tv R θ = V)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r}, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2}, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {h₀ h₁ : MolecularPositionL2 eta}
    (hdom0 : HasGLHamiltonian (sysAt sys P L) L θ ((quadCutoffL sys.one_le_mass
      (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2 (pos_of_freeDynL0 hL) (ψ 0)) h₀)
    (hdom1 : HasGLHamiltonian (sysAt sys P L) L θ h₀ h₁) {𝒟 : ℝ} (hψ0 : ‖ψ 0‖ ≤ 𝒟)
    (hn0 : ‖(quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
      (pos_of_freeDynL0 hL) (ψ 0)‖ ≤ 𝒟) (hn1 : ‖h₀‖ ≤ 𝒟) (hn2 : ‖h₁‖ ≤ 𝒟)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf (sysAt sys P L).nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (pos_of_freeDynL0 hL) (continuous_of_schwartz F hFf) hfR
        (two_Rf_lt_of_freeDynL0 hL)
      let φ₀ := (quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
        (pos_of_freeDynL0 hL) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConst sys V F (quadCutoff8 sys.one_le_mass).D 𝒟 *
            ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConst sys V F (quadCutoff8 sys.one_le_mass).D 𝒟 * (1 + t) * ε := by
  subst hV
  have h8 := eight_le_of_freeDynL0 hL
  have hL2 := two_pi_le_of_freeDynL0 hL
  have hS : MeasurableSet {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2} :=
    (measurableSet_le measurable_const
      (contDiff_massQ sys.mass (n := 0)).continuous.measurable).inter
      (measurableSet_le (contDiff_massQ sys.mass (n := 0)).continuous.measurable measurable_const)
  have hB : MeasurableSet {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2} :=
    measurableSet_lt (contDiff_massQ sys.mass (n := 0)).continuous.measurable measurable_const
  have hSB : {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r ∧ massQ sys.mass r ≤ 2 * (L / 8) ^ 2} ⊆
      {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2}ᶜ := fun r hr h => by
    simp only [Set.mem_setOf_eq] at hr h
    linarith [hr.1]
  have hc : {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2}ᶜ =
      {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r} := by
    ext r
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  have hret : ∀ r, (quadCutoffL sys.one_le_mass h8).toCutoff.χ r ≠ 0 →
      ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ := fun r hr i =>
    (quadCutoffL_ret sys.one_le_mass h8 r hr i).trans (ret_of_freeDynL0 hL)
  have hD := quadCutoffL_D_le sys.one_le_mass h8
  exact free_dyn_endpoint (sysAt sys P L) hL2 hθ hR hR0 hρ hone P hP (fun l => rfl)
    (quadCutoffL sys.one_le_mass h8).toCutoff hret hD hD hS hB
    (quadCutoffL_one sys.one_le_mass h8)
    hSB (fun r hr a => (quadCutoffL_derivs sys.one_le_mass h8 r hr a).1)
    (fun r hr a => (quadCutoffL_derivs sys.one_le_mass h8 r hr a).2) hψd hHam hgrad ht hε hε1
    (fun s hs => by rw [hc]; exact hleak0 s hs) hleak1 hdom0 hdom1 hψ0 hn0 hn1 hn2 a hf0 hf1 F hFf
    hfR (two_Rf_lt_of_freeDynL0 hL) m hκ hm hK

/-- **`prop:free-dyn` without clamped nuclei, uniform in `L`**: as `free_dyn_uniform`, with the
domain condition proved; the data enter through `‖ψ₀‖ + ‖H_∞ ψ₀‖ + ‖H_∞² ψ₀‖ ≤ D`, and
`C = freeDynConstNBO sys V F D_s C_s D` (`D_s`, `C_s` the bounds of the shape). -/

theorem free_dyn_nbo_uniform [IsEmpty ν] (sys : CoulombSystem eta ν) {R0 ρ Rf V : ℝ} (hR0 : 0 ≤ R0)
    (hρ : 0 ≤ ρ) {L R : ℝ} {θ : ℝ → ℝ} (hL : freeDynL0 R0 ρ Rf ≤ L) (hθ : Profile R θ)
    (hR : R ≤ L / 2) (hV : tv R θ = V)
    (hone : ∀ r, 0 ≤ r → r ≤ L / 2 - ρ → θ r = 1)
    (P : ν → E3) (hP : ∀ l, ‖P l‖ ≤ R0)
    (hpos : ∀ l, sys.nuclei.position l = fun c => ((-(P l c) / L : ℝ) : UnitAddCircle))
    {ψ H : ℝ → FreeL2 eta} {grad : ℝ → Fin eta × Fin 3 → FreeL2 eta}
    (hψd : ∀ s, HasDerivAt ψ (-(Complex.I • H s)) s)
    (hHam : ∀ s, HasFreeHamiltonian sys P (ψ s) (H s))
    (hgrad : ∀ s, HasWeakGrad (ψ s) (grad s))
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hleak0 : ∀ s ∈ Icc 0 t, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r}, ‖ψ s r‖ ^ 2 ≤ ε ^ 2)
    (hleak1 : ∀ s ∈ Icc 0 t, ∫ r in {r | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2}, ∑ a, ‖grad s a r‖ ^ 2 ≤ ε ^ 2)
    {k : FreeL2 eta} (hH1 : HasFreeHamiltonian sys P (H 0) k) {D : ℝ}
    (hD : ‖ψ 0‖ + ‖H 0‖ + ‖k‖ ≤ D)
    (a : Fin eta) {f : E3 → ℝ} (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (F : 𝓢(E3, ℂ)) (hFf : ∀ y, F y = (f y : ℂ))
    (hfR : ∀ y, f y ≠ 0 → ‖y‖ ≤ Rf)
    (m : ℕ) {κ : Lat3 → ℝ}
    (hκ : PlaneWaveGridG.IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ)
    (hm : 8 ≤ m) (hK : 8 ≤ (2 * Real.pi / L) * m) :
    ∃ Ug : ℝ → EuclideanSpace ℂ (RCfg eta m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (RCfg eta m),
      (∀ x, Ug 0 x = x) ∧ (∀ s t x, Ug (s + t) x = Ug s (Ug t x)) ∧
      (∀ x, Continuous fun t => Ug t x) ∧
      (∀ t x, Ug t (Hpos (m := m) (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) x) = Hpos (regParticlesOf sys) (posNucleiOf sys.nuclei) κ
        (2 * Real.pi / L) (Ug t x)) ∧
      (∀ t x, HasDerivAt (fun s => Ug s x) (-(Complex.I • Ug t (Hpos (m := m)
        (regParticlesOf sys) (posNucleiOf sys.nuclei) κ (2 * Real.pi / L) x))) t) ∧
      let χ := cellObs (pos_of_freeDynL0 hL) (continuous_of_schwartz F hFf) hfR
        (two_Rf_lt_of_freeDynL0 hL)
      let φ₀ := (quadCutoffL sys.one_le_mass (eight_le_of_freeDynL0 hL)).toCutoff.chiW.cutL2
        (pos_of_freeDynL0 hL) (ψ 0)
      let K : ℝ := (2 * Real.pi / L) * m
      let ψg := Ug t (idft (regCoeff m ((molecularPositionSynthesis eta).symm φ₀)))
      ‖((∫ r, f (particle r a) * ‖ψ t r‖ ^ 2 : ℝ) : ℂ) - ⟪ψg, posObs a (chiRefl χ) ψg⟫_ℂ‖ ≤
        freeDynConstNBO sys V F (quadCutoff8 sys.one_le_mass).D (quadCutoff8 sys.one_le_mass).C
            D * ((1 / K) ^ 5 + t * (1 / K) ^ 3) +
          freeDynConstNBO sys V F (quadCutoff8 sys.one_le_mass).D (quadCutoff8 sys.one_le_mass).C
            D * (1 + t) * ε := by
  subst hV
  have h8 := eight_le_of_freeDynL0 hL
  have hL2 := two_pi_le_of_freeDynL0 hL
  have hS : MeasurableSet {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r ∧
      massQ sys.mass r ≤ 2 * (L / 8) ^ 2} :=
    (measurableSet_le measurable_const
      (contDiff_massQ sys.mass (n := 0)).continuous.measurable).inter
      (measurableSet_le (contDiff_massQ sys.mass (n := 0)).continuous.measurable measurable_const)
  have hB : MeasurableSet {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2} :=
    measurableSet_lt (contDiff_massQ sys.mass (n := 0)).continuous.measurable measurable_const
  have hSB : {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r ∧ massQ sys.mass r ≤ 2 * (L / 8) ^ 2} ⊆
      {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2}ᶜ := fun r hr h => by
    simp only [Set.mem_setOf_eq] at hr h
    linarith [hr.1]
  have hc : {r : Rcfg eta | massQ sys.mass r < (L / 8) ^ 2}ᶜ =
      {r : Rcfg eta | (L / 8) ^ 2 ≤ massQ sys.mass r} := by
    ext r
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  have hret : ∀ r, (quadCutoffL sys.one_le_mass h8).χ r ≠ 0 →
      ∀ i, ‖particle r i‖ ≤ retainedRadius L R0 ρ := fun r hr i =>
    (quadCutoffL_ret sys.one_le_mass h8 r hr i).trans (ret_of_freeDynL0 hL)
  exact free_dyn_nbo_endpoint sys hL2 hθ hR hR0 hρ hone P hP hpos
    (quadCutoffL sys.one_le_mass h8) hret (quadCutoffL_D_le sys.one_le_mass h8)
    (quadCutoffL_C_le sys.one_le_mass h8) hS hB (quadCutoffL_one sys.one_le_mass h8)
    hSB (fun r hr a => (quadCutoffL_derivs sys.one_le_mass h8 r hr a).1)
    (fun r hr a => (quadCutoffL_derivs sys.one_le_mass h8 r hr a).2) hψd hHam hgrad ht hε hε1
    (fun s hs => by rw [hc]; exact hleak0 s hs) hleak1 hH1 hD a hf0 hf1 F hFf hfR
    (two_Rf_lt_of_freeDynL0 hL) m hκ hm hK

end Uniform

end FreeBoundary
