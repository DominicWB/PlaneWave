import PlaneWave.FluxBox.BigBox

/-!
# Flux route, stage 2, part 2: the exact centre-of-mass split of the force

For every hop `k' ↦ k' + τ_j(θ)` of a channel `j` (`PlaneWave.Observable.SecondOrder`, `eq:com` in exact form),

  `A(k' + τ_j θ) - A(k') = λ_j (E(k' + τ_j θ) - E(k')) + c_j(k', θ)`,

`λ_j = μ_j/m_{p₀}` if `p₀ ∈ j` (`= 1` for the one-body channel of `p₀`) and `0` otherwise, and
`c_j(k', θ) = ± (g²/M̄_j) θ·Π_j(k')` for a pair `j ∋ p₀` (`+` if `p₀` leads), `0` otherwise
(`regL_hop`, `abs_comC_le`). On the box this gives, kernelwise,

  **`G_N = -i[T_N, Ŵ_N] + G_N^cm`**  (`GN_split`),

with the *flat potential* `Ŵ = Σ_j λ_j W_j` (`whK`, Hermitian) and the *centre-of-mass force*
`G^cm(q, p) = -i w(q, p) c_j(p, θ)` (`gcmK`), `|G^cm| ≤ |w| g² |θ| |Π_j| / M̄_j`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The exact identity on a hop -/

section Hop

variable (sys : CoulombSystem eta ν) (p₀ : Fin eta)

/-- The flat factor `λ_j = μ_j/m_{p₀}` of a channel moving `p₀` (`0` otherwise). -/
noncomputable def lamC (j : Ch eta) : ℝ := if p₀ ∈ moved j then muCh sys j / sys.mass p₀ else 0

/-- The centre-of-mass term `c_j(k', θ) = ± (g²/M̄_j) θ·Π_j(k')`. -/
noncomputable def comC (g : ℝ) : Ch eta → Cf eta → Lattice3 → ℝ
  | .inl _, _, _ => 0
  | .inr pr, k', θ =>
      if p₀ = pr.1.1 then
        g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) * ∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ))
      else if p₀ = pr.1.2 then
        -(g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
          ∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ)))
      else 0

omit [Fintype ν] in
lemma lamC_nonneg (j : Ch eta) : 0 ≤ lamC sys p₀ j := by
  unfold lamC
  split_ifs
  · have := muCh_pos sys j; have := sys.mass_pos p₀; positivity
  · exact le_rfl

omit [Fintype ν] in
lemma lamC_le_one (j : Ch eta) : lamC sys p₀ j ≤ 1 := by
  unfold lamC
  split_ifs with hp
  · have hm := sys.mass_pos p₀
    rw [div_le_one hm]
    cases j with
    | inl a =>
      have : p₀ = a := by simpa [moved] using hp
      subst this; exact le_rfl
    | inr pr =>
      have ha := sys.mass_pos pr.1.1
      have hb := sys.mass_pos pr.1.2
      simp only [moved, Finset.mem_insert, Finset.mem_singleton] at hp
      simp only [muCh]
      rw [div_le_iff₀ (by positivity)]
      rcases hp with rfl | rfl <;> nlinarith
  · exact zero_le_one

omit [Fintype ν] in
/-- **The exact centre-of-mass identity on a hop**:
`A(k' + τ_j θ) - A(k') = λ_j (E(k' + τ_j θ) - E(k')) + c_j(k', θ)`. -/
theorem regL_hop (g : ℝ) (j : Ch eta) (k' : Cf eta) (θ : Lattice3) :
    regL sys g p₀ (k' + tr j θ) - regL sys g p₀ k' =
      lamC sys p₀ j * (E sys.mass g (k' + tr j θ) - E sys.mass g k') + comC sys p₀ g j k' θ := by
  by_cases hp : p₀ ∈ moved j
  swap
  · have h0 : (k' + tr j θ) p₀ = k' p₀ := by
      rw [Pi.add_apply, tr_apply_not_moved j θ hp, add_zero]
    unfold regL lamC
    rw [h0, sub_self, if_neg hp, zero_mul, zero_add]
    cases j with
    | inl a =>
      rfl
    | inr pr =>
      have h1 : p₀ ≠ pr.1.1 := fun h => hp (by simp [moved, h])
      have h2 : p₀ ≠ pr.1.2 := fun h => hp (by simp [moved, h])
      simp only [comC, if_neg h1, if_neg h2]
  cases j with
  | inl a =>
    have ha : p₀ = a := by simpa [moved] using hp
    subst ha
    have e : regL sys g p₀ (k' + tr (.inl p₀) θ) - regL sys g p₀ k' =
        E sys.mass g (k' + tr (.inl p₀) θ) - E sys.mass g k' := by
      rw [show tr (.inl p₀ : Ch eta) θ = Pi.single p₀ θ from rfl, E_add_single_sub]
      unfold regL
      rw [FSNormal.add_single_self]
      ring
    rw [e]
    simp only [lamC, if_pos hp, muCh, div_self (sys.mass_pos p₀).ne', one_mul, comC, add_zero]
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    have ha := sys.mass_pos pr.1.1
    have hb := sys.mass_pos pr.1.2
    have hE := E_hop sys g (.inr pr) k' θ
    have e1 : (k' + tr (.inr pr) θ) pr.1.1 = k' pr.1.1 + θ := by
      simp [tr, Pi.single_eq_of_ne hne]
    have e2 : (k' + tr (.inr pr) θ) pr.1.2 = k' pr.1.2 + -θ := by
      simp [tr, Pi.single_eq_of_ne hne.symm, sub_eq_add_neg]
    simp only [lamC, if_pos hp]
    simp only [moved, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · simp only [comC, ↓reduceIte]
      rw [hE]
      unfold regL
      rw [e1]
      simp only [nsq, FSLattice.slabF, FSLattice.lsq, cCh, muCh, Pi.add_apply, Int.cast_add,
        Fin.sum_univ_three]
      field_simp
      ring
    · simp only [comC, if_neg hne.symm, ↓reduceIte]
      rw [hE]
      unfold regL
      rw [e2]
      simp only [nsq, FSLattice.slabF, FSLattice.lsq, cCh, muCh, Pi.add_apply, Pi.neg_apply,
        Int.cast_add, Int.cast_neg, Fin.sum_univ_three]
      field_simp
      ring

omit [Fintype ν] in
/-- `|c_j(k', θ)| ≤ g² |θ| |Π_j(k')| / M̄_j`. -/
lemma abs_comC_le (g : ℝ) (j : Ch eta) (k' : Cf eta) (θ : Lattice3) :
    |comC sys p₀ g j k' θ| ≤ g ^ 2 * FSChannel.rho θ * piC j k' / Mtot sys j := by
  have hR0 : 0 ≤ g ^ 2 * FSChannel.rho θ * piC j k' / Mtot sys j := by
    have := Mtot_pos sys j
    have := piC_nonneg j k'
    have := FSChannel.rho_nonneg θ
    positivity
  cases j with
  | inl a => simp only [comC, abs_zero]; exact hR0
  | inr pr =>
    have ha := sys.mass_pos pr.1.1
    have hb := sys.mass_pos pr.1.2
    have hdot := abs_dot_le θ (k' pr.1.1 + k' pr.1.2)
    have hsum : ∑ i, (θ i : ℝ) * (((k' pr.1.1 + k' pr.1.2) i : ℤ) : ℝ) =
        ∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, Int.cast_add]
    rw [hsum] at hdot
    have hM : Mtot sys (.inr pr) = sys.mass pr.1.1 + sys.mass pr.1.2 := rfl
    have hpi : piC (.inr pr) k' = FSChannel.rho (k' pr.1.1 + k' pr.1.2) := rfl
    have hc : 0 ≤ g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) := by positivity
    have key : |g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
        ∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ))| ≤
        g ^ 2 * FSChannel.rho θ * piC (.inr pr) k' / Mtot sys (.inr pr) := by
      rw [abs_mul, abs_of_nonneg hc, hM, hpi]
      calc g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
            |∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ))|
          ≤ g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
            (FSChannel.rho θ * FSChannel.rho (k' pr.1.1 + k' pr.1.2)) :=
            mul_le_mul_of_nonneg_left hdot hc
        _ = _ := by ring
    simp only [comC]
    split_ifs
    · exact key
    · rw [abs_neg]; exact key
    · rw [abs_zero]; exact hR0

end Hop

/-! ## The split on the box -/

section BoxSplit

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N : ℕ)

/-- The kernel of the box force `G_N`: `i w(q, p) (A(p) - A(q))`. -/
noncomputable def gK (q p : Cfg eta N) : ℂ :=
  Complex.I * wNK sys L N q p * ((Aproj sys L p₀ p - Aproj sys L p₀ q : ℝ) : ℂ)

/-- The kernel of the flat potential `Ŵ = Σ_j λ_j W_j` on the box. -/
noncomputable def whK (q p : Cfg eta N) : ℂ :=
  ∑ j, (lamC sys p₀ j : ℂ) * chPart N j (wNK sys L N) q p

/-- The kernel of the centre-of-mass force: `G^cm = G_N + i[T_N, Ŵ]` kernelwise. -/
noncomputable def gcmK (q p : Cfg eta N) : ℂ :=
  gK sys L p₀ N q p + Complex.I * ((Asym sys L N q - Asym sys L N p : ℝ) : ℂ) * whK sys L p₀ N q p

/-- The flat potential on the box. -/
noncomputable abbrev WhN : En eta N →ₗ[ℂ] En eta N := FSKernel.kop (whK sys L p₀ N)

/-- The centre-of-mass force on the box. -/
noncomputable abbrev GcmN : En eta N →ₗ[ℂ] En eta N := FSKernel.kop (gcmK sys L p₀ N)

variable {sys L p₀ N}

omit [Fintype ν] in
lemma kop_neg' (κ : Cfg eta N → Cfg eta N → ℂ) : -FSKernel.kop κ = FSKernel.kop (-κ) := by
  ext u q
  simp [Finset.sum_neg_distrib]

lemma GN_eq_kop (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    GN sys L p₀ N = FSKernel.kop (gK sys L p₀ N) := by
  have hW : WN sys L N = FSKernel.kop (wNK sys L N) := VN_eq_kop sys hL H hKernel
  unfold GN
  rw [hW, FSKernel.kop_dg, FSKernel.dg_kop, ← FSKernel.kop_sub, ← FSKernel.kop_smul]
  congr 1
  funext q p
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, gK]
  push_cast
  ring

/-- **The centre-of-mass split of the box force**: `G_N = -i[T_N, Ŵ_N] + G_N^cm`. -/
theorem GN_split (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    GN sys L p₀ N = -(Complex.I • (TN sys L N ∘ₗ WhN sys L p₀ N - WhN sys L p₀ N ∘ₗ TN sys L N)) +
      GcmN sys L p₀ N := by
  rw [GN_eq_kop hL H hKernel, FSKernel.kop_comm_dg, ← FSKernel.kop_smul, kop_neg',
    ← FSKernel.kop_add]
  congr 1
  funext q p
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, gcmK]
  push_cast
  ring

omit [Fintype ν] in
lemma tr_zero (j : Ch eta) : tr j (0 : Lattice3) = 0 := by
  cases j with
  | inl a => simp [tr]
  | inr pr => simp [tr]

/-- The potential kernel vanishes on the diagonal. -/
lemma potKernel_self_eq_zero (hL : 0 < L) (k : Cf eta) : potKernel sys L k k = 0 := by
  have h := norm_potKernel_le sys hL k k
  have h0 : potMaj sys L k k = 0 := by
    unfold potMaj
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold chMaj
    rw [if_pos (by show k = k + tr j (k (lead j) - k (lead j)); rw [sub_self, tr_zero, add_zero]),
      sub_self]
    simp [latticeNormSq]
  rw [h0] at h
  exact norm_le_zero_iff.mp h

/-- `wNK = Σ_j chPart_j wNK` (distinct configurations are joined by at most one channel; the
diagonal vanishes). -/
lemma wNK_eq_sum_chPart (hL : 0 < L) (q p : Cfg eta N) :
    wNK sys L N q p = ∑ j, chPart N j (wNK sys L N) q p := by
  classical
  by_cases h0 : wNK sys L N q p = 0
  · rw [h0]; symm
    exact Finset.sum_eq_zero fun j _ => by unfold chPart; split_ifs <;> simp [h0]
  obtain ⟨j, hj⟩ := exists_onCh_of_ne_zero (sys := sys) hL h0
  have hne : cidx N q ≠ cidx N p := by
    intro h
    apply h0
    unfold wNK
    rw [h]
    exact potKernel_self_eq_zero hL (cidx N p)
  rw [Finset.sum_eq_single j]
  · unfold chPart; rw [if_pos hj]
  · intro j' _ hj'
    unfold chPart
    rw [if_neg]
    intro h
    exact hj' (onCh_unique h hj hne)
  · intro h; exact absurd (Finset.mem_univ j) h

end BoxSplit

end FSFlux
