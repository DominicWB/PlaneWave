import PlaneWave.Certificate
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Auxiliary clauses of the manuscript, part 1: Galerkin dynamics

Clauses of `app:dynamics` and `app:kinetic` that the release file does not state, proved from its
results.

* `coulomb_normlevel_full` — eq:normlevel of `prop:duhamel` for the full error
  `e(t) = ψ(t) - ψ_N(t) = δ(t) + η(t)`: the release's `coulomb_normlevel` bounds the Galerkin part
  `η(t)` only; the union bound over the registers (`norm_sub_truncate_le`) and the state tails at
  time `t` (`tails_at_time`) add `‖δ(t)‖ ≤ η_tot t_K`, i.e. `O(K^{-5/2})`.
* `cube_tails_all`, `cube_supTails_all` — `lem:disc-tails` on its whole stated range: the release's
  `cube_tails_rate` stops at `λ ≤ K`. For `K < λ < √3 K` the bounds follow from those at `K`
  (factor `6`); the Euclidean tails vanish for `λ ≥ √3 K` (`tailMask_cube_eq_zero`), and with the
  `∞`-norm restriction (`supTailMask`) the same estimates hold and vanish for `λ ≥ K`
  (`supTailMask_cube_eq_zero`, `norm_supTailMask_le`).
* `galerkin_flow_isSector`, `galerkin_trajectory_isSector` — the setting of `app:dynamics`:
  `ψ_N(t)` stays in `ran P ∩ S` for every exchange sector `S` of an admissible labelling. The
  Galerkin flow commutes with every linear map that commutes with `H_N` (`flow_commute`, from the
  uniqueness clause of `exists_finitePropagator`), in particular with the exchanges.
* `coulombPMap`, `coulombPMap_isSelfAdjoint` — `prop:F2`, `prop:nbo-KR`: the Hamiltonian of a
  periodic Coulomb system, as an operator on `ℓ²` with domain `S(H²)` (`S u ↦ H u`), is
  self-adjoint (`T† = T` for Mathlib's adjoint of a densely defined operator). From the symmetry
  on `H²` (`coulombH2_symm`), the density of the domain (`molecularFourierH2Domain_dense`) and the
  surjectivity of `H + c` (`H_add_shift_resolventG`).
-/

set_option autoImplicit false

open scoped InnerProductSpace
open PlaneWaveCertificate

namespace PlaneWaveDynamics

variable {eta : ℕ} {ν : Type} [Fintype ν]

section NormLevel

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

include hKernel hL hPeriodic in
/-- **eq:normlevel for the full error** (`prop:duhamel`). For `ψ₀ = S u₀ ∈ D(H²)` and the cube of
radius `n` (`K = g n`), the error `e(t) = ψ(t) - ψ_N(t)` of the Galerkin trajectory
`ψ_N(t) = e^{-iH_N t} P ψ₀` (embedded in `ℓ²`) satisfies
`‖e(t)‖ ≤ η_tot t_K + C_m √((η_tot t_K)(η_tot (t_K + 2B))) t`, with `B` the kinetic-tail bound and
`t_K = (2m̄/K²) B` the state-tail bound of `tails_at_time`. With `ρ = K^{-1/2}` this is
`O(K^{-5/2} + t K^{-3/2})`. -/
theorem coulomb_normlevel_full (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (hderiv : ∀ t u, HasDerivAt (fun s => U s (molecularH2StateMap eta (2 * Real.pi / L) u))
      (-(Complex.I • U t (H u))) t)
    (n : ℕ)
    (UN : ℝ → EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n)))
    (hN0 : ∀ x, UN 0 x = x) (hNadd : ∀ s t x, UN (s + t) x = UN s (UN t x))
    (hNcomm : ∀ t x, UN t (finiteCoulombHamiltonian sys L n x) =
      finiteCoulombHamiltonian sys L n (UN t x))
    (hNderiv : ∀ t x, HasDerivAt (fun s => UN s x)
      (-(Complex.I • UN t (finiteCoulombHamiltonian sys L n x))) t)
    (rho Blow Cs Bker : ℝ) (hK1 : 1 ≤ (2 * Real.pi / L) * n)
    (hRho : 0 ≤ rho) (hRhoScale : rho ^ 2 * ((2 * Real.pi / L) * n) = 1)
    (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (h2gK : 2 * (2 * Real.pi / L) ≤ (2 * Real.pi / L) * n)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    {t : ℝ} (ht : 0 ≤ t) :
    let K := (2 * Real.pi / L) * n
    let B := (2 * sys.maxMass / K ^ 2) * (2 * ‖H v₀‖ + 2 * relB sys L Hunit *
            ‖molecularH2StateMap eta (2 * Real.pi / L) v₀‖) +
          finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker
            (sys.maxMass * (‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ +
              2 * (2 * ‖H u₀‖ + 2 * relB sys L Hunit *
                ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖))) * rho
    let tK := (2 * sys.maxMass / K ^ 2) * B
    ‖U t (molecularH2StateMap eta (2 * Real.pi / L) u₀) -
        finiteFourierLpIsometry eta n
          (UN t (extractCLM n (molecularH2StateMap eta (2 * Real.pi / L) u₀)))‖ ≤
      eta * tK + finiteCoulombPhysicalMassConstant sys L Hunit *
        Real.sqrt ((eta * tK) * (eta * (tK + 2 * B))) * t := by
  intro K B tK
  have hη := coulomb_normlevel sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph hderiv n UN hN0
    hNadd hNcomm hNderiv rho Blow Cs Bker hK1 hRho hRhoScale hBlow hCs hBker h2gK hAmplitude
    hBkerScale hCsScale u₀ v₀ huv ht
  obtain ⟨u, hu1, hu2⟩ := hgraph t u₀
  set g := 2 * Real.pi / L with hg
  have hg0 : 0 < g := by positivity
  set ψ := U t (molecularH2StateMap eta g u₀) with hψ
  set ι := finiteFourierLpIsometry eta n
  have hsplit : ψ - ι (UN t (extractCLM n (molecularH2StateMap eta g u₀))) =
      (ψ - molecularH2Truncate n ψ) +
        ι (extractCLM n ψ - UN t (extractCLM n (molecularH2StateMap eta g u₀))) := by
    rw [map_sub, emb_extractCLM]
    abel
  have hδ : ‖ψ - molecularH2Truncate n ψ‖ ≤ eta * tK := by
    refine (norm_sub_truncate_le hg0 n ψ).trans ?_
    calc ∑ a : Fin eta, ‖tailMask g (g * n) a ψ‖ ≤ ∑ _a : Fin eta, tK :=
          Finset.sum_le_sum fun a _ => by
            have h := (tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph a K rho Blow Cs
              Bker hK1 hRho hRhoScale hBlow hCs hBker h2gK hAmplitude hBkerScale hCsScale u₀ v₀
              huv t u hu1 hu2).2
            rw [hu1] at h
            exact h
      _ = eta * tK := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ‖ψ - ι (UN t (extractCLM n (molecularH2StateMap eta g u₀)))‖
      = ‖(ψ - molecularH2Truncate n ψ) +
          ι (extractCLM n ψ - UN t (extractCLM n (molecularH2StateMap eta g u₀)))‖ := by
        rw [hsplit]
    _ ≤ ‖ψ - molecularH2Truncate n ψ‖ +
          ‖ι (extractCLM n ψ - UN t (extractCLM n (molecularH2StateMap eta g u₀)))‖ :=
        norm_add_le _ _
    _ = ‖ψ - molecularH2Truncate n ψ‖ +
          ‖extractCLM n ψ - UN t (extractCLM n (molecularH2StateMap eta g u₀))‖ := by
        rw [LinearIsometry.norm_map]
    _ ≤ _ := add_le_add hδ hη

end NormLevel

section SectorFlow

/-- **Flows commute with the commutant.** If `A` commutes with a symmetric `T` on a
finite-dimensional space, it commutes with every flow `U` of `T`
(`d/dt U(t)x = -i U(t) T x`, `U(t) T = T U(t)`, `U(0) = 1`). -/
theorem flow_commute {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {T : V →ₗ[ℂ] V} (hT : T.IsSymmetric) (A : V →ₗ[ℂ] V)
    (hAT : ∀ x, A (T x) = T (A x)) (UN : ℝ → V ≃ₗᵢ[ℂ] V) (hN0 : ∀ x, UN 0 x = x)
    (hNcomm : ∀ t x, UN t (T x) = T (UN t x))
    (hNderiv : ∀ t x, HasDerivAt (fun s => UN s x) (-(Complex.I • UN t (T x))) t)
    (t : ℝ) (x : V) : A (UN t x) = UN t (A x) := by
  obtain ⟨U₀, -, -, -, -, -, huniq⟩ := exists_finitePropagator hT
  have hsol : ∀ y s, HasDerivAt (fun s => UN s y) (-(Complex.I • T (UN s y))) s := fun y s => by
    have h := hNderiv s y
    rwa [hNcomm] at h
  have hA : ∀ s, HasDerivAt (fun s => A (UN s x)) (-(Complex.I • T (A (UN s x)))) s := by
    intro s
    have h := ((LinearMap.toContinuousLinearMap A).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
      (hNderiv s x)
    have e : ((LinearMap.toContinuousLinearMap A).restrictScalars ℝ)
        (-(Complex.I • (UN s) (T x))) = -(Complex.I • T (A (UN s x))) := by
      rw [ContinuousLinearMap.coe_restrictScalars', LinearMap.coe_toContinuousLinearMap', map_neg,
        map_smul, hNcomm, hAT]
    rw [e] at h
    exact h
  have h1 := huniq (fun s => A (UN s x)) hA t
  have h2 := huniq (fun s => UN s (A x)) (hsol (A x)) t
  simp only [hN0] at h1 h2
  rw [h1, h2]

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-- **The Galerkin flow preserves every exchange sector** of an admissible labelling. -/
theorem galerkin_flow_isSector (sys : CoulombSystem eta ν) {sgn : Fin eta → ℂ}
    {lab : Fin eta → ℕ} (hlab : sys.IsAdmissible lab) (L : ℝ) (n : ℕ)
    (UN : ℝ → EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n)))
    (hN0 : ∀ x, UN 0 x = x)
    (hNcomm : ∀ t x, UN t (finiteCoulombHamiltonian sys L n x) =
      finiteCoulombHamiltonian sys L n (UN t x))
    (hNderiv : ∀ t x, HasDerivAt (fun s => UN s x)
      (-(Complex.I • UN t (finiteCoulombHamiltonian sys L n x))) t)
    {u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n))}
    (hu : IsSectorVector sgn lab u) (t : ℝ) : IsSectorVector sgn lab (UN t u) := by
  rw [isSectorVector_iff_particlePermutation_swap] at hu ⊢
  intro i j hij hl
  have hs := hlab i j hl
  have hc := flow_commute (finiteCoulombHamiltonian_isSymmetric sys L n)
    (particlePermutationOperator (Equiv.swap i j))
    (fun x => (finiteCoulombHamiltonian_particlePermutation_commute sys L n (Equiv.swap i j)
      (sys.mass_swap hs) (sys.charge_swap hs) x).symm) UN hN0 hNcomm hNderiv t u
  rw [hc, hu i j hij hl, map_smul]

/-- **`ψ_N(t) ∈ ran P ∩ S`** (the setting of `app:dynamics`): for a datum `x` in an exchange
sector of an admissible labelling, the Galerkin trajectory `ψ_N(t) = e^{-iH_N t} P x` is a sector
vector of the cube; embedded in `ℓ²` it lies in the sector and in the range of `P`. -/
theorem galerkin_trajectory_isSector (sys : CoulombSystem eta ν) {sgn : Fin eta → ℂ}
    {lab : Fin eta → ℕ} (hlab : sys.IsAdmissible lab) (L : ℝ) (n : ℕ)
    (UN : ℝ → EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n)))
    (hN0 : ∀ x, UN 0 x = x)
    (hNcomm : ∀ t x, UN t (finiteCoulombHamiltonian sys L n x) =
      finiteCoulombHamiltonian sys L n (UN t x))
    (hNderiv : ∀ t x, HasDerivAt (fun s => UN s x)
      (-(Complex.I • UN t (finiteCoulombHamiltonian sys L n x))) t)
    {x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2} (hx : IsSectorCoeff sgn lab (fun p => x p))
    (t : ℝ) :
    IsSectorVector sgn lab (UN t (extractCLM n x)) ∧
      IsSectorCoeff sgn lab (fun p => finiteFourierLpIsometry eta n (UN t (extractCLM n x)) p) ∧
      molecularH2Truncate n (finiteFourierLpIsometry eta n (UN t (extractCLM n x))) =
        finiteFourierLpIsometry eta n (UN t (extractCLM n x)) := by
  have h0 : IsSectorVector sgn lab (extractCLM n x) :=
    fullCoeffVector_isSector _ (finiteFourierCoeffExtract_isSector n _ hx)
  have h1 := galerkin_flow_isSector sys hlab L n UN hN0 hNcomm hNderiv h0 t
  exact ⟨h1, (finiteFourierLpEmbed_isSector_iff sgn lab n _).2 h1, truncate_emb n _⟩

end SectorFlow

section SelfAdjoint

open scoped LinearPMap

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

omit [Fintype ν] in
variable (eta) in
/-- **The Hamiltonian as an operator on `ℓ²`**, with domain `S(H²)` and `S u ↦ H u`. -/
noncomputable def coulombPMap :
    lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →ₗ.[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 where
  domain := molecularFourierH2Domain eta (2 * Real.pi / L)
  toFun := molecularFourierDomainOperator (2 * Real.pi / L) H

omit [Fintype ν] in
lemma coulombPMap_apply_equiv (u : MolecularFourierH2 eta) :
    coulombPMap eta L H (molecularFourierH2DomainEquiv eta (2 * Real.pi / L) u) = H u :=
  molecularFourierDomainOperator_apply_equiv _ H u

include hKernel hL hPeriodic in
/-- **`prop:F2`, `prop:nbo-KR`: the Hamiltonian is self-adjoint** on its domain `S(H²)`. -/
theorem coulombPMap_isSelfAdjoint : IsSelfAdjoint (coulombPMap eta L H) := by
  set g := 2 * Real.pi / L with hg
  set A := coulombPMap eta L H with hA
  set S := molecularH2StateMap eta g with hS
  set e := molecularFourierH2DomainEquiv eta g with he
  have hdense : Dense (A.domain : Set (lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)) :=
    molecularFourierH2Domain_dense eta g
  have hrep : ∀ x : A.domain, ∃ u, e u = x := fun x => ⟨e.symm x, e.apply_symm_apply x⟩
  -- symmetry
  have hsymm : A.IsFormalAdjoint A := by
    intro x y
    obtain ⟨u, rfl⟩ := hrep x
    obtain ⟨u', rfl⟩ := hrep y
    rw [coulombPMap_apply_equiv, coulombPMap_apply_equiv, molecularFourierH2DomainEquiv_coe,
      molecularFourierH2DomainEquiv_coe]
    exact (coulombH2_symm sys L H hKernel u u').symm
  have hle1 : A ≤ A† := hsymm.le_adjoint hdense
  -- every vector of the adjoint domain is `S u` with `H u = A† y`
  set c : ℂ := (shiftC sys L Hunit : ℂ) with hc
  have hcc : (starRingEnd ℂ) c = c := Complex.conj_ofReal _
  set G := resolventG sys L H hKernel Hunit hL hPeriodic with hG
  have hHG : ∀ f, H (G f) + c • S (G f) = f := fun f =>
    H_add_shift_resolventG sys L H hKernel Hunit hL hPeriodic f
  have hkey : ∀ y : A†.domain, ∃ u : MolecularFourierH2 eta, S u = y ∧ H u = A† y := by
    intro y
    set z := A† y with hz
    set u := G (z + c • (y : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)) with hu
    have hu1 : H u + c • S u = z + c • (y : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :=
      hHG _
    have hadj : ∀ v : MolecularFourierH2 eta,
        ⟪z, S v⟫_ℂ = ⟪(y : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2), H v⟫_ℂ := fun v => by
      have h := LinearPMap.adjoint_isFormalAdjoint hdense y (e v)
      rw [coulombPMap_apply_equiv, molecularFourierH2DomainEquiv_coe] at h
      exact h
    have horth : ∀ v : MolecularFourierH2 eta,
        ⟪(y : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) - S u, H v + c • S v⟫_ℂ = 0 := by
      intro v
      have h0 : ⟪z + c • (y : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) - (H u + c • S u),
          S v⟫_ℂ = 0 := by rw [hu1, sub_self, inner_zero_left]
      rw [inner_sub_left, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, hcc,
        hadj v, ← coulombH2_symm sys L H hKernel u v] at h0
      rw [inner_sub_left, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right]
      linear_combination h0
    have hzero : (y : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) - S u = 0 := by
      have h := horth (G ((y : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) - S u))
      rw [hHG] at h
      exact inner_self_eq_zero.1 h
    have hSu : S u = y := (sub_eq_zero.1 hzero).symm
    refine ⟨u, hSu, ?_⟩
    rw [hSu] at hu1
    exact add_right_cancel hu1
  have hle2 : A† ≤ A := by
    refine ⟨fun y hy => ?_, fun y x hxy => ?_⟩
    · obtain ⟨u, hu1, -⟩ := hkey ⟨y, hy⟩
      exact ⟨u, hu1⟩
    · obtain ⟨u, hu1, hu2⟩ := hkey y
      have hx : x = e u := by
        apply Subtype.ext
        rw [molecularFourierH2DomainEquiv_coe, ← hxy]
        exact hu1.symm
      rw [hx, coulombPMap_apply_equiv, hu2]
  exact (LinearPMap.isSelfAdjoint_def).2 (le_antisymm hle2 hle1)

end SelfAdjoint

end PlaneWaveDynamics

namespace PlaneWaveKinetic

open PlaneWaveDynamics

variable {eta : ℕ} {ν : Type} [Fintype ν]

section SupTails

/-- The `∞`-norm of a lattice vector. -/
noncomputable def supNorm3 (v : Lattice3) : ℝ := max (max |(v 0 : ℝ)| |(v 1 : ℝ)|) |(v 2 : ℝ)|

lemma abs_coord_le_sqrt (v : Lattice3) (d : Fin 3) : |(v d : ℝ)| ≤ Real.sqrt (latticeNormSq v) := by
  apply Real.abs_le_sqrt
  unfold latticeNormSq
  fin_cases d <;> simp <;> nlinarith [sq_nonneg ((v 0 : ℤ) : ℝ), sq_nonneg ((v 1 : ℤ) : ℝ),
    sq_nonneg ((v 2 : ℤ) : ℝ)]

lemma supNorm3_le_sqrt (v : Lattice3) : supNorm3 v ≤ Real.sqrt (latticeNormSq v) :=
  max_le (max_le (abs_coord_le_sqrt v 0) (abs_coord_le_sqrt v 1)) (abs_coord_le_sqrt v 2)

/-- The `∞`-norm tail mask of register `r`: it keeps the configurations with `g ‖p_r‖_∞ > λ`. -/
noncomputable def supTailMask (g lam : ℝ) (r : Fin eta) :
    lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →L[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 :=
  diagCLM (fun p => if lam < g * supNorm3 (p r) then (1 : ℂ) else 0) 1 zero_le_one
    (fun p => by split_ifs <;> simp)

lemma supTailMask_apply (g lam : ℝ) (r : Fin eta)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (p : FourierConfig eta Lattice3) :
    supTailMask g lam r x p = (if lam < g * supNorm3 (p r) then (1 : ℂ) else 0) * x p :=
  rfl

/-- Pointwise domination of `ℓ²` vectors gives the norm bound. -/
lemma lp_norm_le_of_pointwise {x y : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}
    (h : ∀ p, ‖x p‖ ≤ ‖y p‖) : ‖x‖ ≤ ‖y‖ := by
  have hsq : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq]
    exact (l2_summable_sq x).tsum_le_tsum (fun p => pow_le_pow_left₀ (norm_nonneg _) (h p) 2)
      (l2_summable_sq y)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- The `∞`-norm tail is at most the Euclidean tail. -/
lemma norm_supTailMask_le {g : ℝ} (hg : 0 ≤ g) (lam : ℝ) (r : Fin eta)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    ‖supTailMask g lam r x‖ ≤ ‖tailMask g lam r x‖ := by
  refine lp_norm_le_of_pointwise fun p => ?_
  rw [supTailMask_apply, tailMask_apply]
  by_cases h1 : lam < g * supNorm3 (p r)
  · have h2 : lam < g * Real.sqrt (latticeNormSq (p r)) :=
      lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_left (supNorm3_le_sqrt _) hg)
    rw [if_pos h1, if_pos h2]
  · rw [if_neg h1, zero_mul, norm_zero]
    exact norm_nonneg _

/-- The Euclidean tails decrease in the threshold. -/
lemma norm_tailMask_anti (g : ℝ) {lam lam' : ℝ} (hl : lam ≤ lam') (r : Fin eta)
    (x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) :
    ‖tailMask g lam' r x‖ ≤ ‖tailMask g lam r x‖ := by
  refine lp_norm_le_of_pointwise fun p => ?_
  rw [tailMask_apply, tailMask_apply]
  by_cases h1 : lam' < g * Real.sqrt (latticeNormSq (p r))
  · rw [if_pos h1, if_pos (lt_of_le_of_lt hl h1)]
  · rw [if_neg h1, zero_mul, norm_zero]
    exact norm_nonneg _

/-- On the cube of radius `n`, `|p_r|² ≤ 3 n²` and `‖p_r‖_∞ ≤ n`. -/
lemma cube_coord_bounds {n : ℕ} {p : FourierConfig eta Lattice3}
    (hp : p ∈ fourierConfigCube eta n) (r : Fin eta) :
    latticeNormSq (p r) ≤ 3 * (n : ℝ) ^ 2 ∧ supNorm3 (p r) ≤ n := by
  rw [mem_fourierConfigCube_iff] at hp
  have hd : ∀ d : Fin 3, |((p r d : ℤ) : ℝ)| ≤ n := fun d => by
    obtain ⟨h1, h2⟩ := hp r d
    rw [abs_le]
    constructor
    · have : ((-(n : ℤ) : ℤ) : ℝ) ≤ ((p r d : ℤ) : ℝ) := Int.cast_le.2 h1
      push_cast at this
      exact this
    · have : ((p r d : ℤ) : ℝ) ≤ (((n : ℤ) : ℤ) : ℝ) := Int.cast_le.2 h2
      push_cast at this
      exact this
  have hsq : ∀ d : Fin 3, ((p r d : ℤ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := fun d => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hd d) 2
  refine ⟨?_, max_le (max_le (hd 0) (hd 1)) (hd 2)⟩
  unfold latticeNormSq
  linarith [hsq 0, hsq 1, hsq 2]

/-- A vector supported in the cube of radius `n` has no Euclidean tail beyond `√3 g n`. -/
lemma tailMask_cube_eq_zero {g : ℝ} (hg : 0 ≤ g) {n : ℕ} {lam : ℝ}
    (hlam : Real.sqrt 3 * (g * n) ≤ lam) (r : Fin eta)
    {x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2} (hx : molecularH2Truncate n x = x) :
    tailMask g lam r x = 0 := by
  classical
  ext p
  rw [tailMask_apply]
  by_cases hp : p ∈ fourierConfigCube eta n
  · have hle : g * Real.sqrt (latticeNormSq (p r)) ≤ lam := by
      have h1 := (cube_coord_bounds hp r).1
      have h2 : Real.sqrt (latticeNormSq (p r)) ≤ Real.sqrt 3 * n := by
        rw [show Real.sqrt 3 * (n : ℝ) = Real.sqrt (3 * (n : ℝ) ^ 2) by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (Nat.cast_nonneg n)]]
        exact Real.sqrt_le_sqrt h1
      calc g * Real.sqrt (latticeNormSq (p r)) ≤ g * (Real.sqrt 3 * n) :=
            mul_le_mul_of_nonneg_left h2 hg
        _ = Real.sqrt 3 * (g * n) := by ring
        _ ≤ lam := hlam
    rw [if_neg (not_lt.2 hle), zero_mul]
    rfl
  · have : x p = 0 := by
      rw [← hx, molecularH2Truncate_apply, cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ p hp]
    rw [this, mul_zero]
    rfl

/-- A vector supported in the cube of radius `n` has no `∞`-norm tail beyond `g n`. -/
lemma supTailMask_cube_eq_zero {g : ℝ} (hg : 0 ≤ g) {n : ℕ} {lam : ℝ} (hlam : g * n ≤ lam)
    (r : Fin eta) {x : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2}
    (hx : molecularH2Truncate n x = x) :
    supTailMask g lam r x = 0 := by
  classical
  ext p
  rw [supTailMask_apply]
  by_cases hp : p ∈ fourierConfigCube eta n
  · have hle : g * supNorm3 (p r) ≤ lam :=
      (mul_le_mul_of_nonneg_left (cube_coord_bounds hp r).2 hg).trans hlam
    rw [if_neg (not_lt.2 hle), zero_mul]
    rfl
  · have : x p = 0 := by
      rw [← hx, molecularH2Truncate_apply, cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ p hp]
    rw [this, mul_zero]
    rfl

end SupTails

/-- `√(1/K) ≤ 6 √(1/λ)` and `(1/K²) √(1/K) ≤ 6 (1/λ²) √(1/λ)` for `0 < K` and `0 < λ ≤ 2K`. -/
lemma tail_scale_le {K lam : ℝ} (hK0 : 0 < K) (hlam0 : 0 < lam) (hl2K : lam ≤ 2 * K) :
    Real.sqrt (1 / K) ≤ 6 * Real.sqrt (1 / lam) ∧
      1 / K ^ 2 * Real.sqrt (1 / K) ≤ 6 * (1 / lam ^ 2 * Real.sqrt (1 / lam)) := by
  set x := Real.sqrt (1 / K) with hxdef
  set y := Real.sqrt (1 / lam) with hydef
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hxy : x ≤ Real.sqrt 2 * y := by
    rw [hxdef, hydef, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    rw [show 2 * (1 / lam) = 2 / lam by ring, div_le_div_iff₀ hK0 hlam0]
    linarith
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hx2 : x ^ 2 = 1 / K := by rw [hxdef, Real.sq_sqrt (by positivity)]
  have hy2 : y ^ 2 = 1 / lam := by rw [hydef, Real.sq_sqrt (by positivity)]
  refine ⟨by nlinarith, ?_⟩
  have h5 := pow_le_pow_left₀ hx0 hxy 5
  have e : (Real.sqrt 2 * y) ^ 5 = (Real.sqrt 2 ^ 2) ^ 2 * Real.sqrt 2 * y ^ 5 := by ring
  rw [e, Real.sq_sqrt (by norm_num)] at h5
  have hy5 : 0 ≤ y ^ 5 := pow_nonneg hy0 5
  have hx5 : x ^ 5 ≤ 6 * y ^ 5 := by nlinarith
  have e1 : 1 / K ^ 2 * x = x ^ 5 := by rw [← one_div_pow, ← hx2]; ring
  have e2 : 1 / lam ^ 2 * y = y ^ 5 := by rw [← one_div_pow, ← hy2]; ring
  rw [e1, e2]
  exact hx5

section DiscTailsAll

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)

lemma discTailConst_nonneg (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    {Blow Cs Bker : ℝ} (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    {s0 hu hs hv : ℝ} (h0 : 0 ≤ s0) (h1 : 0 ≤ hu) (h2 : 0 ≤ hs) (h3 : 0 ≤ hv) :
    0 ≤ discTailConst sys L Hunit Blow Cs Bker s0 hu hs hv := by
  have hb := relB_nonneg sys L Hunit hC
  have hm : 0 ≤ sys.maxMass := by linarith [sys.one_le_maxMass]
  have hct : ∀ M : ℝ, 0 ≤ M → 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit Blow Cs Bker M :=
    fun M hM => finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker hM
  simp only [discTailConst]
  refine add_nonneg (add_nonneg (by positivity) (mul_nonneg hC (mul_nonneg (mul_nonneg
    (Nat.cast_nonneg _) (add_nonneg (by positivity) (hct _ (by positivity))))
    (Real.sqrt_nonneg _)))) (hct _ (by positivity))

omit [Fintype ν] in
/-- Cube support of the Galerkin trajectory and of its kinetic energy. -/
lemma cubeLift_supports (g : ℝ) (n : ℕ)
    (φ : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n))) :
    molecularH2Truncate n (molecularH2StateMap eta g (cubeLift g n φ)) =
        molecularH2StateMap eta g (cubeLift g n φ) ∧
      molecularH2Truncate n (coulombFourierKineticH2 sys g (cubeLift g n φ)) =
        coulombFourierKineticH2 sys g (cubeLift g n φ) := by
  refine ⟨?_, kinetic_cubeLift_truncate sys g n φ⟩
  rw [stateMap_cubeLift, truncate_emb]

include hKernel hL hPeriodic in
/-- **`lem:disc-tails` on its whole range.** In the setting of `cube_tails_rate`, for `K = g n ≥ 1`
and every threshold `λ ≥ max(1, 2g)` (no upper bound), the three tails of the Galerkin trajectory
are at most `6` times the bounds of `cube_tails_rate` at `λ`; they vanish for `λ ≥ √3 K`. -/
theorem cube_tails_all (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (n : ℕ)
    (UN : ℝ → EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n)))
    (hNcomm : ∀ t x, UN t (finiteCoulombHamiltonian sys L n x) =
      finiteCoulombHamiltonian sys L n (UN t x))
    (Blow Cs Bker : ℝ) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (s : ℝ) (a : Fin eta) (hK1 : 1 ≤ (2 * Real.pi / L) * n) {lam : ℝ} (hl1 : 1 ≤ lam)
    (h2g : 2 * (2 * Real.pi / L) ≤ lam) :
    let βN := discTailConst sys L Hunit Blow Cs Bker
      ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta (2 * Real.pi / L) v₀‖ ‖H v₀‖
    let l := cubeLift (2 * Real.pi / L) n
      (UN s (extractCLM n (molecularH2StateMap eta (2 * Real.pi / L) u₀)))
    (‖tailMask (2 * Real.pi / L) lam a (coulombFourierKineticH2 sys (2 * Real.pi / L) l)‖ ≤
        6 * (βN * Real.sqrt (1 / lam)) ∧
      ‖tailMask (2 * Real.pi / L) lam a (molecularH2StateMap eta (2 * Real.pi / L) l)‖ ≤
        6 * ((2 * sys.maxMass / lam ^ 2) * (βN * Real.sqrt (1 / lam))) ∧
      ‖tailMask (2 * Real.pi / L) lam a (molecularH2StateMap eta (2 * Real.pi / L) l +
        coulombFourierKineticH2 sys (2 * Real.pi / L) l)‖ ≤
        6 * ((1 + 2 * sys.maxMass) * βN * Real.sqrt (1 / lam))) ∧
    (Real.sqrt 3 * ((2 * Real.pi / L) * n) ≤ lam →
      tailMask (2 * Real.pi / L) lam a (coulombFourierKineticH2 sys (2 * Real.pi / L) l) = 0 ∧
      tailMask (2 * Real.pi / L) lam a (molecularH2StateMap eta (2 * Real.pi / L) l) = 0 ∧
      tailMask (2 * Real.pi / L) lam a (molecularH2StateMap eta (2 * Real.pi / L) l +
        coulombFourierKineticH2 sys (2 * Real.pi / L) l) = 0) := by
  intro βN l
  set g := 2 * Real.pi / L with hg
  have hg0 : 0 < g := by positivity
  set K := g * n with hK
  have hM := sys.one_le_maxMass
  have hβ : 0 ≤ βN := discTailConst_nonneg sys L Hunit hC hBlow hCs hBker (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hl1
  obtain ⟨hSt, hTt⟩ := cubeLift_supports sys g n
    (UN s (extractCLM n (molecularH2StateMap eta g u₀)))
  have hSTt : molecularH2Truncate n (molecularH2StateMap eta g l + coulombFourierKineticH2 sys g l) =
      molecularH2StateMap eta g l + coulombFourierKineticH2 sys g l := by
    rw [molecularH2Truncate_add, hSt, hTt]
  -- vanishing beyond `√3 K`
  have hvan : Real.sqrt 3 * K ≤ lam →
      tailMask g lam a (coulombFourierKineticH2 sys g l) = 0 ∧
      tailMask g lam a (molecularH2StateMap eta g l) = 0 ∧
      tailMask g lam a (molecularH2StateMap eta g l + coulombFourierKineticH2 sys g l) = 0 :=
    fun h => ⟨tailMask_cube_eq_zero hg0.le h a hTt, tailMask_cube_eq_zero hg0.le h a hSt,
      tailMask_cube_eq_zero hg0.le h a hSTt⟩
  refine ⟨?_, hvan⟩
  have hb1 : 0 ≤ βN * Real.sqrt (1 / lam) := mul_nonneg hβ (Real.sqrt_nonneg _)
  rcases le_or_gt lam K with hlK | hKl
  · -- the stated range
    obtain ⟨h1, h2, h3⟩ := cube_tails_rate sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph n UN
      hNcomm Blow Cs Bker hBlow hCs hBker hAmplitude hBkerScale hCsScale u₀ v₀ huv s a hl1 h2g hlK
    have hm2 : 0 ≤ 2 * sys.maxMass / lam ^ 2 := by positivity
    refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_⟩
    · linarith
    · have : 0 ≤ (2 * sys.maxMass / lam ^ 2) * (βN * Real.sqrt (1 / lam)) := mul_nonneg hm2 hb1
      linarith
    · have : 0 ≤ (1 + 2 * sys.maxMass) * βN * Real.sqrt (1 / lam) := by positivity
      linarith
  rcases le_or_gt (Real.sqrt 3 * K) lam with hvl | hlv
  · -- beyond `√3 K`: the tails vanish
    obtain ⟨e1, e2, e3⟩ := hvan hvl
    simp only [e1, e2, e3, norm_zero]
    have : 0 ≤ 2 * sys.maxMass / lam ^ 2 := by positivity
    refine ⟨by positivity, by positivity, by positivity⟩
  · -- `K < λ < √3 K`: compare with the bounds at `K`
    have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK1
    have h3 : Real.sqrt 3 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hn2 : 2 * g ≤ K := by
      -- `2 g ≤ λ < √3 g n`, so `n ≥ 2`
      have hgn : 2 * g < Real.sqrt 3 * (g * n) := lt_of_le_of_lt h2g hlv
      have hn : (1 : ℝ) < n := by
        by_contra hcon
        push Not at hcon
        have h1 : g * n ≤ g := by
          have := mul_le_mul_of_nonneg_left hcon hg0.le
          rwa [mul_one] at this
        have h2 : Real.sqrt 3 * (g * n) ≤ Real.sqrt 3 * g :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg 3)
        have h4 : Real.sqrt 3 * g < 2 * g := mul_lt_mul_of_pos_right h3 hg0
        linarith only [hgn, h2, h4]
      have hn' : (2 : ℝ) ≤ n := by
        have : 1 < n := by exact_mod_cast hn
        exact_mod_cast (show 2 ≤ n by omega)
      calc 2 * g = g * 2 := by ring
        _ ≤ g * n := mul_le_mul_of_nonneg_left hn' hg0.le
    obtain ⟨h1, h2, h3'⟩ := cube_tails_rate sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph n UN
      hNcomm Blow Cs Bker hBlow hCs hBker hAmplitude hBkerScale hCsScale u₀ v₀ huv s a hK1 hn2
      le_rfl
    have hKl' : K ≤ lam := hKl.le
    have hl2K : lam ≤ 2 * K := le_trans hlv.le (mul_le_mul_of_nonneg_right h3.le hK0.le)
    obtain ⟨hx6, hst⟩ := tail_scale_le hK0 hlam0 hl2K
    have hm : 0 ≤ 2 * sys.maxMass := mul_nonneg zero_le_two (zero_le_one.trans hM)
    refine ⟨?_, ?_, ?_⟩
    · calc _ ≤ ‖tailMask g K a (coulombFourierKineticH2 sys g l)‖ := norm_tailMask_anti g hKl' a _
        _ ≤ βN * Real.sqrt (1 / K) := h1
        _ ≤ βN * (6 * Real.sqrt (1 / lam)) := mul_le_mul_of_nonneg_left hx6 hβ
        _ = 6 * (βN * Real.sqrt (1 / lam)) := by ring
    · calc _ ≤ ‖tailMask g K a (molecularH2StateMap eta g l)‖ := norm_tailMask_anti g hKl' a _
        _ ≤ (2 * sys.maxMass / K ^ 2) * (βN * Real.sqrt (1 / K)) := h2
        _ = (2 * sys.maxMass * βN) * (1 / K ^ 2 * Real.sqrt (1 / K)) := by ring
        _ ≤ (2 * sys.maxMass * βN) * (6 * (1 / lam ^ 2 * Real.sqrt (1 / lam))) :=
          mul_le_mul_of_nonneg_left hst (mul_nonneg hm hβ)
        _ = 6 * ((2 * sys.maxMass / lam ^ 2) * (βN * Real.sqrt (1 / lam))) := by ring
    · calc _ ≤ ‖tailMask g K a (molecularH2StateMap eta g l + coulombFourierKineticH2 sys g l)‖ :=
          norm_tailMask_anti g hKl' a _
        _ ≤ (1 + 2 * sys.maxMass) * βN * Real.sqrt (1 / K) := h3'
        _ ≤ (1 + 2 * sys.maxMass) * βN * (6 * Real.sqrt (1 / lam)) :=
          mul_le_mul_of_nonneg_left hx6 (mul_nonneg (by linarith only [hm]) hβ)
        _ = 6 * ((1 + 2 * sys.maxMass) * βN * Real.sqrt (1 / lam)) := by ring

include hKernel hL hPeriodic in
/-- **`lem:disc-tails` with the `∞`-norm restriction**: the same bounds as `cube_tails_all` hold
for the `∞`-norm tails, which vanish for `λ ≥ K`. -/
theorem cube_supTails_all (hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) (h0 : ∀ x, U 0 x = x)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (n : ℕ)
    (UN : ℝ → EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode n)))
    (hNcomm : ∀ t x, UN t (finiteCoulombHamiltonian sys L n x) =
      finiteCoulombHamiltonian sys L n (UN t x))
    (Blow Cs Bker : ℝ) (hBlow : 0 ≤ Blow) (hCs : 0 ≤ Cs) (hBker : 0 ≤ Bker)
    (hAmplitude : 54 * Real.sqrt ((coulombCellAmplitude L) ^ 2) ≤ Blow * (2 * Real.pi / L))
    (hBkerScale : 432 * (coulombCellAmplitude L) ^ 2 * (2 * Real.pi / L) ≤ Bker ^ 2)
    (hCsScale : 1 + 108 / (2 * Real.pi / L) ^ 4 ≤ Cs ^ 2)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (s : ℝ) (a : Fin eta) (hK1 : 1 ≤ (2 * Real.pi / L) * n) {lam : ℝ} (hl1 : 1 ≤ lam)
    (h2g : 2 * (2 * Real.pi / L) ≤ lam) :
    let βN := discTailConst sys L Hunit Blow Cs Bker
      ‖molecularH2StateMap eta (2 * Real.pi / L) u₀‖ ‖H u₀‖
      ‖molecularH2StateMap eta (2 * Real.pi / L) v₀‖ ‖H v₀‖
    let l := cubeLift (2 * Real.pi / L) n
      (UN s (extractCLM n (molecularH2StateMap eta (2 * Real.pi / L) u₀)))
    (‖supTailMask (2 * Real.pi / L) lam a (coulombFourierKineticH2 sys (2 * Real.pi / L) l)‖ ≤
        6 * (βN * Real.sqrt (1 / lam)) ∧
      ‖supTailMask (2 * Real.pi / L) lam a (molecularH2StateMap eta (2 * Real.pi / L) l)‖ ≤
        6 * ((2 * sys.maxMass / lam ^ 2) * (βN * Real.sqrt (1 / lam))) ∧
      ‖supTailMask (2 * Real.pi / L) lam a (molecularH2StateMap eta (2 * Real.pi / L) l +
        coulombFourierKineticH2 sys (2 * Real.pi / L) l)‖ ≤
        6 * ((1 + 2 * sys.maxMass) * βN * Real.sqrt (1 / lam))) ∧
    ((2 * Real.pi / L) * n ≤ lam →
      supTailMask (2 * Real.pi / L) lam a (coulombFourierKineticH2 sys (2 * Real.pi / L) l) = 0 ∧
      supTailMask (2 * Real.pi / L) lam a (molecularH2StateMap eta (2 * Real.pi / L) l) = 0 ∧
      supTailMask (2 * Real.pi / L) lam a (molecularH2StateMap eta (2 * Real.pi / L) l +
        coulombFourierKineticH2 sys (2 * Real.pi / L) l) = 0) := by
  intro βN l
  have hg0 : 0 < 2 * Real.pi / L := by positivity
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := cube_tails_all sys L H hKernel Hunit hL hPeriodic hC U h0 hgraph n
    UN hNcomm Blow Cs Bker hBlow hCs hBker hAmplitude hBkerScale hCsScale u₀ v₀ huv s a hK1 hl1 h2g
  obtain ⟨hSt, hTt⟩ := cubeLift_supports sys (2 * Real.pi / L) n
    (UN s (extractCLM n (molecularH2StateMap eta (2 * Real.pi / L) u₀)))
  refine ⟨⟨(norm_supTailMask_le hg0.le _ _ _).trans h1, (norm_supTailMask_le hg0.le _ _ _).trans h2,
    (norm_supTailMask_le hg0.le _ _ _).trans h3⟩, fun h => ⟨supTailMask_cube_eq_zero hg0.le h a hTt,
    supTailMask_cube_eq_zero hg0.le h a hSt, supTailMask_cube_eq_zero hg0.le h a ?_⟩⟩
  rw [molecularH2Truncate_add, hSt, hTt]

end DiscTailsAll

end PlaneWaveKinetic
