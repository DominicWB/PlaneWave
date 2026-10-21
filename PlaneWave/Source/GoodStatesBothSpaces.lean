import PlaneWave.Source.DressedState

/-!
# Flux/source build, block 4a: good states on both spaces

* `FGood sys L M w`: a full-space state `S w` with budget `M` (`‖S w‖ + ‖T w‖ ≤ M`, register tails
  `‖1_{a,>λ} S w‖ ≤ M λ^{-5/2}` and `‖1_{a,>λ} T w‖ ≤ M λ^{-1/2}` for `λ ≥ 1`);
* **`traj_fgood`**: the exact trajectory `ψ(t) = U(t) S u₀` (`u₀ ∈ D(H²)`, `H u₀ = S v₀`) is good with
  a budget fixed by `‖S u₀‖, ‖H u₀‖, ‖H v₀‖`, uniformly in `t` (`prop:dyn-boot`, from the release's
  `tails_at_time` at every threshold);
* `fgood_R`, `fgood_W`: `‖R ψ‖ ≤ η M K^{-5/2}`, `‖W (1 - P) ψ‖ ≤ √3 η C_m M K^{-3/2}`;
* `ext_good`: the cube part of a full-space good state is good on `E_n` (`IsGood`, block 1);
* `isGood_perturb`: a good state plus a vector `e` with `‖e‖ ≤ δ`, `‖(1+A) e‖ ≤ δ₁` is good with
  budget `M + (δ + δ₁)(1 + √3 K)³` (tails vanish beyond `√3 K` on the cube).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics NormedSpace FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Powers -/

lemma rpow_neg_half_eq {l : ℝ} (hl : 0 < l) : l ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt l := by
  rw [Real.rpow_neg hl.le, Real.sqrt_eq_rpow, inv_eq_one_div]

lemma rpow_neg_five_half_eq {l : ℝ} (hl : 0 < l) :
    l ^ (-(5 / 2 : ℝ)) = 1 / (l ^ 2 * Real.sqrt l) := by
  rw [Real.rpow_neg hl.le, show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hl,
    Real.sqrt_eq_rpow, inv_eq_one_div]
  norm_cast

lemma rpow_le_of_le_one {l : ℝ} (hl : 1 ≤ l) {a b : ℝ} (hab : a ≤ b) : l ^ a ≤ l ^ b :=
  Real.rpow_le_rpow_of_exponent_le hl hab

/-! ## Full-space good states -/

section Full

variable (sys : CoulombSystem eta ν) (L : ℝ)

/-- **A full-space good state** with budget `M`. -/
def FGood (M : ℝ) (w : MolecularFourierH2 eta) : Prop :=
  ‖Sm eta L w‖ + ‖coulombFourierKineticH2 sys (gF L) w‖ ≤ M ∧
    ∀ (a : Fin eta) (l : ℝ), 1 ≤ l →
      ‖tailMask (gF L) l a (Sm eta L w)‖ ≤ M * l ^ (-(5 / 2 : ℝ)) ∧
      ‖tailMask (gF L) l a (coulombFourierKineticH2 sys (gF L) w)‖ ≤ M * l ^ (-(1 / 2 : ℝ))

variable {sys L}

omit [Fintype ν] in
lemma FGood.nonneg {M : ℝ} {w : MolecularFourierH2 eta} (h : FGood sys L M w) : 0 ≤ M :=
  le_trans (by positivity) h.1

omit [Fintype ν] in
lemma norm_tailMask_le (g K : ℝ) (a : Fin eta) (x : L2 eta) : ‖tailMask g K a x‖ ≤ ‖x‖ := by
  have := l2_norm_le_of_le (tailMask g K a x) x zero_le_one fun p => by
    rw [tailMask_apply, one_mul]
    split_ifs <;> simp
  rwa [one_mul] at this

omit [Fintype ν] in
/-- `‖R ψ‖ ≤ η M K^{-5/2}` for `K = g n ≥ 1`. -/
lemma fgood_R {M : ℝ} {w : MolecularFourierH2 eta} (h : FGood sys L M w) (hL : 0 < L) {n : ℕ}
    (hK : 1 ≤ gF L * n) :
    ‖Sm eta L w - molecularH2Truncate n (Sm eta L w)‖ ≤ eta * M * (gF L * n) ^ (-(5 / 2 : ℝ)) := by
  refine (PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) n (Sm eta L w)).trans ?_
  calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n) a (Sm eta L w)‖
      ≤ ∑ _a : Fin eta, M * (gF L * n) ^ (-(5 / 2 : ℝ)) :=
        Finset.sum_le_sum fun a _ => (h.2 a _ hK).1
    _ = eta * M * (gF L * n) ^ (-(5 / 2 : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

variable (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel in
/-- `‖W (1 - P) w‖ ≤ √3 η C_m M K^{-3/2}` for a good `w` and `K = g n ≥ 1`. -/
lemma fgood_W (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {M : ℝ} {w : MolecularFourierH2 eta} (h : FGood sys L M w) {n : ℕ} (hK : 1 ≤ gF L * n) :
    ‖Wp sys L H (w - molecularH2Truncate n w)‖ ≤
      Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * M *
        (gF L * n) ^ (-(3 / 2 : ℝ)) := by
  set K := gF L * n
  have hK0 : 0 < K := by linarith
  have hM := h.nonneg
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hsq := potential_tail_sq_le sys L H hKernel Hunit hL hPeriodic n w
  have ht : ∀ a, ‖tailMask (2 * Real.pi / L) ((2 * Real.pi / L) * n) a
      (molecularH2StateMap eta (2 * Real.pi / L) w)‖ ≤ M * K ^ (-(5 / 2 : ℝ)) :=
    fun a => (h.2 a K hK).1
  have hτ : ∀ a, ‖tailMask (2 * Real.pi / L) ((2 * Real.pi / L) * n) a
      (coulombFourierKineticH2 sys (2 * Real.pi / L) w)‖ ≤ M * K ^ (-(1 / 2 : ℝ)) :=
    fun a => (h.2 a K hK).2
  have h52 : K ^ (-(5 / 2 : ℝ)) ≤ K ^ (-(1 / 2 : ℝ)) := rpow_le_of_le_one hK (by norm_num)
  have hA : ∑ a : Fin eta, ‖tailMask (2 * Real.pi / L) ((2 * Real.pi / L) * n) a
      (molecularH2StateMap eta (2 * Real.pi / L) w)‖ ≤ eta * (M * K ^ (-(5 / 2 : ℝ))) := by
    calc _ ≤ ∑ _a : Fin eta, M * K ^ (-(5 / 2 : ℝ)) := Finset.sum_le_sum fun a _ => ht a
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : ∑ a : Fin eta, (‖tailMask (2 * Real.pi / L) ((2 * Real.pi / L) * n) a
      (molecularH2StateMap eta (2 * Real.pi / L) w)‖ +
        2 * ‖tailMask (2 * Real.pi / L) ((2 * Real.pi / L) * n) a
          (coulombFourierKineticH2 sys (2 * Real.pi / L) w)‖) ≤
      eta * (3 * M * K ^ (-(1 / 2 : ℝ))) := by
    calc _ ≤ ∑ _a : Fin eta, 3 * M * K ^ (-(1 / 2 : ℝ)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          have := ht a; have := hτ a
          nlinarith [mul_le_mul_of_nonneg_left h52 hM]
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hprod : K ^ (-(5 / 2 : ℝ)) * K ^ (-(1 / 2 : ℝ)) = (K ^ (-(3 / 2 : ℝ))) ^ 2 := by
    rw [← Real.rpow_add hK0, ← Real.rpow_natCast, ← Real.rpow_mul hK0.le]; norm_num
  have h2 : ‖Wp sys L H (w - molecularH2Truncate n w)‖ ^ 2 ≤
      (Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * M *
        K ^ (-(3 / 2 : ℝ))) ^ 2 := by
    have e1 : (Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * M *
        K ^ (-(3 / 2 : ℝ))) ^ 2 = finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          ((eta * (M * K ^ (-(5 / 2 : ℝ)))) * (eta * (3 * M * K ^ (-(1 / 2 : ℝ))))) := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), ← hprod]
      ring
    rw [e1]
    refine hsq.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    exact mul_le_mul hA hB (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- The trajectory budget: `‖S u₀‖ + Ξ₀` and the tail constant `2 m̄ Ξ₁ + C_tail(M₂)`. -/
noncomputable def Mtraj (sys : CoulombSystem eta ν) (L Hunit : ℝ) (s0 hu hv sv : ℝ) : ℝ :=
  (1 + 2 * gF L) ^ 3 * (s0 + (2 * hu + 2 * relB sys L Hunit * s0)) +
    (1 + 2 * sys.maxMass) * (2 * sys.maxMass * (2 * hv + 2 * relB sys L Hunit * sv) +
      finiteCoulombPhysicalTailConstant sys L Hunit (molecularCanonicalLowConstant L)
        (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L)
        (sys.maxMass * (s0 + 2 * (2 * hu + 2 * relB sys L Hunit * s0))))

include hKernel in
/-- **The exact trajectory is good** (`prop:dyn-boot`): for `u₀ ∈ D(H²)` (`H u₀ = S v₀`), every
state `S u = U(t) S u₀` with `H u = U(t) H u₀` is good with the budget `Mtraj`. -/
theorem traj_fgood (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (U : ℝ → lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hgraph : ∀ t u, ∃ u' : MolecularFourierH2 eta,
      molecularH2StateMap eta (2 * Real.pi / L) u' =
        U t (molecularH2StateMap eta (2 * Real.pi / L) u) ∧ H u' = U t (H u))
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = molecularH2StateMap eta (2 * Real.pi / L) v₀)
    (t : ℝ) (u : MolecularFourierH2 eta)
    (hu1 : molecularH2StateMap eta (2 * Real.pi / L) u =
      U t (molecularH2StateMap eta (2 * Real.pi / L) u₀))
    (hu2 : H u = U t (H u₀)) :
    FGood sys L (Mtraj sys L Hunit ‖Sm eta L u₀‖ ‖H u₀‖ ‖H v₀‖ ‖Sm eta L v₀‖) u := by
  have hC := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hb := relB_nonneg sys L Hunit hC
  have hg := gF_pos hL
  have hm := sys.one_le_maxMass
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  set s0 := ‖Sm eta L u₀‖
  set Ξ₀ := 2 * ‖H u₀‖ + 2 * relB sys L Hunit * s0
  set Ξ₁ := 2 * ‖H v₀‖ + 2 * relB sys L Hunit * ‖Sm eta L v₀‖
  set Ct := finiteCoulombPhysicalTailConstant sys L Hunit (molecularCanonicalLowConstant L)
    (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L)
    (sys.maxMass * (s0 + 2 * Ξ₀))
  have hCt : 0 ≤ Ct := finiteCoulombPhysicalTailConstant_nonneg _ _ _ hBlow hCs hBker
    (mul_nonneg (by linarith) (by positivity))
  have hΞ₁ : 0 ≤ Ξ₁ := by positivity
  have hMt : Mtraj sys L Hunit s0 ‖H u₀‖ ‖H v₀‖ ‖Sm eta L v₀‖ =
      (1 + 2 * gF L) ^ 3 * (s0 + Ξ₀) + (1 + 2 * sys.maxMass) * (2 * sys.maxMass * Ξ₁ + Ct) := rfl
  -- the norms
  have hSu : ‖Sm eta L u‖ = s0 := by
    have e : Sm eta L u = U t (Sm eta L u₀) := hu1
    rw [e, LinearIsometryEquiv.norm_map]
  have hTu : ‖coulombFourierKineticH2 sys (gF L) u‖ ≤ Ξ₀ := by
    have h := kinetic_le_elliptic sys L H hKernel Hunit hL hPeriodic hC u
    rw [hu1, hu2, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
    exact h
  have hA0 : 0 ≤ s0 + Ξ₀ := by positivity
  have hcube : 1 ≤ (1 + 2 * gF L) ^ 3 := one_le_pow₀ (by linarith)
  have hcube' : s0 + Ξ₀ ≤ (1 + 2 * gF L) ^ 3 * (s0 + Ξ₀) := by
    have := mul_nonneg (sub_nonneg.mpr hcube) hA0
    linarith [show ((1 + 2 * gF L) ^ 3 - 1) * (s0 + Ξ₀) = (1 + 2 * gF L) ^ 3 * (s0 + Ξ₀) - (s0 + Ξ₀)
      by ring]
  have hX : 0 ≤ 2 * sys.maxMass * Ξ₁ + Ct := by positivity
  have hX2 : 2 * sys.maxMass * (2 * sys.maxMass * Ξ₁ + Ct) ≤
      (1 + 2 * sys.maxMass) * (2 * sys.maxMass * Ξ₁ + Ct) := by
    linarith [show (1 + 2 * sys.maxMass) * (2 * sys.maxMass * Ξ₁ + Ct) =
      (2 * sys.maxMass * Ξ₁ + Ct) + 2 * sys.maxMass * (2 * sys.maxMass * Ξ₁ + Ct) by ring]
  have hX1 : 2 * sys.maxMass * Ξ₁ + Ct ≤ (1 + 2 * sys.maxMass) * (2 * sys.maxMass * Ξ₁ + Ct) := by
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * sys.maxMass) hX
    linarith [show (1 + 2 * sys.maxMass) * (2 * sys.maxMass * Ξ₁ + Ct) =
      (2 * sys.maxMass * Ξ₁ + Ct) + 2 * sys.maxMass * (2 * sys.maxMass * Ξ₁ + Ct) by ring]
  have hP : 0 ≤ (1 + 2 * sys.maxMass) * (2 * sys.maxMass * Ξ₁ + Ct) := by positivity
  refine ⟨?_, fun a l hl => ?_⟩
  · rw [hMt, hSu]
    linarith
  have hl0 : 0 < l := by linarith
  by_cases hl2 : 2 * gF L ≤ l
  · -- the release's tails at threshold `l`
    have hρ : Real.sqrt (1 / l) ^ 2 * l = 1 := by
      rw [Real.sq_sqrt (by positivity)]; field_simp
    have h := tails_at_time sys L H hKernel Hunit hL hPeriodic hC U hgraph a l (Real.sqrt (1 / l))
      (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
      (molecularCanonicalKernelConstant L) hl (Real.sqrt_nonneg _) hρ hBlow hCs hBker hl2 hLow
      hKernelScale hSobolev u₀ v₀ huv t u hu1 hu2
    obtain ⟨hT, hS⟩ := h
    have hsq : Real.sqrt (1 / l) = l ^ (-(1 / 2 : ℝ)) := by
      rw [rpow_neg_half_eq hl0, Real.sqrt_div' 1 hl0.le, Real.sqrt_one]
    have hinv2 : 1 / l ^ 2 ≤ l ^ (-(1 / 2 : ℝ)) := by
      have : l ^ (-(2 : ℝ)) ≤ l ^ (-(1 / 2 : ℝ)) := rpow_le_of_le_one hl (by norm_num)
      rwa [Real.rpow_neg hl0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        ← one_div] at this
    have hB : (2 * sys.maxMass / l ^ 2) * Ξ₁ + Ct * Real.sqrt (1 / l) ≤
        (2 * sys.maxMass * Ξ₁ + Ct) * l ^ (-(1 / 2 : ℝ)) := by
      rw [hsq]
      have : 2 * sys.maxMass / l ^ 2 * Ξ₁ = 2 * sys.maxMass * Ξ₁ * (1 / l ^ 2) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hinv2 (by positivity : (0 : ℝ) ≤ 2 * sys.maxMass * Ξ₁)
      have e : (2 * sys.maxMass * Ξ₁ + Ct) * l ^ (-(1 / 2 : ℝ)) =
          2 * sys.maxMass * Ξ₁ * l ^ (-(1 / 2 : ℝ)) + Ct * l ^ (-(1 / 2 : ℝ)) := by ring
      linarith
    have hB0 : 0 ≤ (2 * sys.maxMass * Ξ₁ + Ct) * l ^ (-(1 / 2 : ℝ)) := by positivity
    have hMge : (1 + 2 * sys.maxMass) * (2 * sys.maxMass * Ξ₁ + Ct) ≤
        Mtraj sys L Hunit s0 ‖H u₀‖ ‖H v₀‖ ‖Sm eta L v₀‖ := by
      rw [hMt]
      have : 0 ≤ (1 + 2 * gF L) ^ 3 * (s0 + Ξ₀) := by positivity
      linarith
    constructor
    · -- `‖1_{>l} S u‖ ≤ (2m̄/l²) B`
      have h52 : 1 / l ^ 2 * l ^ (-(1 / 2 : ℝ)) = l ^ (-(5 / 2 : ℝ)) := by
        rw [rpow_neg_five_half_eq hl0, rpow_neg_half_eq hl0]; field_simp
      calc ‖tailMask (gF L) l a (Sm eta L u)‖ ≤ 2 * sys.maxMass / l ^ 2 *
            ((2 * sys.maxMass / l ^ 2) * Ξ₁ + Ct * Real.sqrt (1 / l)) := hS
        _ ≤ 2 * sys.maxMass / l ^ 2 * ((2 * sys.maxMass * Ξ₁ + Ct) * l ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hB (by positivity)
        _ = 2 * sys.maxMass * (2 * sys.maxMass * Ξ₁ + Ct) * l ^ (-(5 / 2 : ℝ)) := by
            rw [← h52]; ring
        _ ≤ Mtraj sys L Hunit s0 ‖H u₀‖ ‖H v₀‖ ‖Sm eta L v₀‖ * l ^ (-(5 / 2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            linarith
    · calc ‖tailMask (gF L) l a (coulombFourierKineticH2 sys (gF L) u)‖
          ≤ (2 * sys.maxMass / l ^ 2) * Ξ₁ + Ct * Real.sqrt (1 / l) := hT
        _ ≤ (2 * sys.maxMass * Ξ₁ + Ct) * l ^ (-(1 / 2 : ℝ)) := hB
        _ ≤ Mtraj sys L Hunit s0 ‖H u₀‖ ‖H v₀‖ ‖Sm eta L v₀‖ * l ^ (-(1 / 2 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            linarith
  · -- small thresholds: the norms
    push Not at hl2
    have hlow : ∀ e : ℝ, 0 ≤ e → e ≤ 3 → 1 ≤ (1 + 2 * gF L) ^ 3 * l ^ (-e) := by
      intro e he0 he3
      rw [Real.rpow_neg hl0.le]
      have hle : l ^ e ≤ (1 + 2 * gF L) ^ 3 := by
        calc l ^ e ≤ l ^ (3 : ℝ) := rpow_le_of_le_one hl he3
          _ = l ^ 3 := by norm_cast
          _ ≤ (1 + 2 * gF L) ^ 3 := pow_le_pow_left₀ hl0.le (by linarith) 3
      rw [← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hl0 _), one_mul]
      exact hle
    have hMge : (1 + 2 * gF L) ^ 3 * (s0 + Ξ₀) ≤ Mtraj sys L Hunit s0 ‖H u₀‖ ‖H v₀‖ ‖Sm eta L v₀‖ := by
      rw [hMt]
      have : 0 ≤ (1 + 2 * sys.maxMass) * (2 * sys.maxMass * Ξ₁ + Ct) := by positivity
      linarith
    constructor
    · calc ‖tailMask (gF L) l a (Sm eta L u)‖ ≤ ‖Sm eta L u‖ := norm_tailMask_le _ _ _ _
        _ = s0 := hSu
        _ ≤ (s0 + Ξ₀) * ((1 + 2 * gF L) ^ 3 * l ^ (-(5 / 2 : ℝ))) := by
            have := mul_le_mul_of_nonneg_left (hlow (5 / 2) (by norm_num) (by norm_num)) hA0
            have hs0 : s0 ≤ s0 + Ξ₀ := by linarith [show 0 ≤ Ξ₀ by positivity]
            linarith
        _ ≤ _ := by
            rw [← mul_assoc, mul_comm (s0 + Ξ₀)]
            exact mul_le_mul_of_nonneg_right hMge (by positivity)
    · calc ‖tailMask (gF L) l a (coulombFourierKineticH2 sys (gF L) u)‖
          ≤ ‖coulombFourierKineticH2 sys (gF L) u‖ := norm_tailMask_le _ _ _ _
        _ ≤ Ξ₀ := hTu
        _ ≤ (s0 + Ξ₀) * ((1 + 2 * gF L) ^ 3 * l ^ (-(1 / 2 : ℝ))) := by
            have := mul_le_mul_of_nonneg_left (hlow (1 / 2) (by norm_num) (by norm_num)) hA0
            have hs0 : Ξ₀ ≤ s0 + Ξ₀ := by linarith [show 0 ≤ s0 by positivity]
            linarith
        _ ≤ _ := by
            rw [← mul_assoc, mul_comm (s0 + Ξ₀)]
            exact mul_le_mul_of_nonneg_right hMge (by positivity)

end Full

/-! ## Good states on the cube -/

section Cube

variable (sys : CoulombSystem eta ν) {L : ℝ} {n : ℕ}

omit [Fintype ν] in
lemma Asym_eq_Ek (q : Cfg eta n) : Asym sys L n q = Ek sys L (finiteConfigLatticeIndex eta n q) := by
  rw [Asym, massKineticSymbol_eq_lattice_sum, Ek, E_eq_kineticSymbol, coulombKineticEnergySymbol]
  rfl

omit [Fintype ν] in
lemma kabs_le_cube (hL : 0 < L) (μ : FinitePlaneWaveMode n) :
    finitePlaneWaveKabs (2 * Real.pi / L) n μ ≤ Real.sqrt 3 * (gF L * n) := by
  rw [kabs_eq_lattice]
  have hg := gF_pos hL
  have hlat : latticeNormSq (finitePlaneWaveLatticeIndex n μ) ≤ 3 * (n : ℝ) ^ 2 := by
    unfold latticeNormSq
    have hb : ∀ i : Fin 3, ((finitePlaneWaveLatticeIndex n μ i : ℤ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      intro i
      obtain ⟨h1, h2⟩ := finitePlaneWaveLatticeIndex_coord_bounds n μ i
      have h1' : -(n : ℝ) ≤ ((finitePlaneWaveLatticeIndex n μ i : ℤ) : ℝ) := by exact_mod_cast h1
      have h2' : ((finitePlaneWaveLatticeIndex n μ i : ℤ) : ℝ) ≤ n := by exact_mod_cast h2
      nlinarith
    have := hb 0; have := hb 1; have := hb 2
    linarith
  have hs : Real.sqrt (latticeNormSq (finitePlaneWaveLatticeIndex n μ)) ≤ Real.sqrt 3 * n := by
    rw [show Real.sqrt 3 * n = Real.sqrt (3 * (n : ℝ) ^ 2) by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (Nat.cast_nonneg n)]]
    exact Real.sqrt_le_sqrt hlat
  calc gF L * Real.sqrt (latticeNormSq (finitePlaneWaveLatticeIndex n μ))
      ≤ gF L * (Real.sqrt 3 * n) := mul_le_mul_of_nonneg_left hs hg.le
    _ = Real.sqrt 3 * (gF L * n) := by ring

omit [Fintype ν] in
lemma wt_one_apply (v : En eta n) (q : Cfg eta n) :
    (FSSpectral.wt (sb eta n) (Asym sys L n) 1 v).ofLp q = ((1 + Asym sys L n q : ℝ) : ℂ) * v.ofLp q := by
  rw [FSSpectral.wt, fc_sb_apply, Real.rpow_one]

omit [Fintype ν] in
lemma wt_one_zero : FSSpectral.wt (sb eta n) (Asym sys L n) 1 (0 : En eta n) = 0 := by
  ext q; rw [wt_one_apply]; simp

omit [Fintype ν] in
lemma regTail_eq_zero_of_large (hL : 0 < L) (a : Fin eta) {l : ℝ} (hl : Real.sqrt 3 * (gF L * n) ≤ l)
    (v : En eta n) : regTail L a l v = 0 := by
  ext p
  rw [regTail_apply, if_neg (not_lt.mpr ((kabs_le_cube hL (p a)).trans hl))]
  rfl

omit [Fintype ν] in
lemma wt_regTail (a : Fin eta) (l : ℝ) (v : En eta n) :
    FSSpectral.wt (sb eta n) (Asym sys L n) 1 (regTail L a l v) =
      regTail L a l (FSSpectral.wt (sb eta n) (Asym sys L n) 1 v) := by
  ext p
  rw [wt_one_apply, regTail_apply, regTail_apply, wt_one_apply]
  split_ifs <;> simp

omit [Fintype ν] in
lemma ext_wt_one (w : MolecularFourierH2 eta) :
    FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L w)) =
      ext eta n (Sm eta L w + coulombFourierKineticH2 sys (gF L) w) := by
  ext q
  rw [wt_one_apply, extractCLM_apply, extractCLM_apply, lp.coeFn_add, Pi.add_apply,
    coulombFourierKineticH2_apply, Sm, molecularH2StateMap_apply, Asym_eq_Ek, Ek, E_eq_kineticSymbol]
  push_cast; ring

omit [Fintype ν] in
lemma regTail_ext (a : Fin eta) (l : ℝ) (x : L2 eta) :
    regTail L a l (ext eta n x) = ext eta n (tailMask (gF L) l a x) := by
  ext q
  rw [regTail_apply, extractCLM_apply, extractCLM_apply, tailMask_apply, kabs_eq_lattice]
  change (if l < gF L * Real.sqrt (latticeNormSq (finiteConfigLatticeIndex eta n q a)) then
    x (finiteConfigLatticeIndex eta n q) else 0) = _
  split_ifs <;> simp

omit [Fintype ν] in
lemma isGood_mono {M M' : ℝ} {u : En eta n} (h : IsGood sys L 1 M u) (hMM : M ≤ M') :
    IsGood sys L 1 M' u := by
  refine ⟨h.1.trans (by linarith), fun a l hl => ⟨(h.2 a l hl).1.trans ?_, (h.2 a l hl).2.trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
  · exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)

omit [Fintype ν] in
lemma isGood_add {M M' : ℝ} {u v : En eta n} (hu : IsGood sys L 1 M u) (hv : IsGood sys L 1 M' v) :
    IsGood sys L 1 (M + M') (u + v) := by
  have hw : ∀ x y : En eta n, FSSpectral.wt (sb eta n) (Asym sys L n) 1 (x + y) =
      FSSpectral.wt (sb eta n) (Asym sys L n) 1 x + FSSpectral.wt (sb eta n) (Asym sys L n) 1 y := by
    intro x y; ext q; rw [wt_one_apply, PiLp.add_apply, PiLp.add_apply, wt_one_apply, wt_one_apply]
    ring
  refine ⟨?_, fun a l hl => ⟨?_, ?_⟩⟩
  · have := hu.1; have := hv.1
    rw [hw]
    linarith [norm_add_le u v, norm_add_le (FSSpectral.wt (sb eta n) (Asym sys L n) 1 u)
      (FSSpectral.wt (sb eta n) (Asym sys L n) 1 v)]
  · rw [map_add]
    refine (norm_add_le _ _).trans ?_
    have := (hu.2 a l hl).1; have := (hv.2 a l hl).1
    simp only [one_mul] at *
    linarith
  · rw [map_add, hw]
    refine (norm_add_le _ _).trans ?_
    have := (hu.2 a l hl).2; have := (hv.2 a l hl).2
    simp only [one_mul] at *
    linarith

omit [Fintype ν] in
/-- **The cube part of a full-space good state is good**: budget `2M`. -/
theorem ext_good {M : ℝ} {w : MolecularFourierH2 eta} (hF : FGood sys L M w) :
    IsGood sys L 1 (2 * M) (ext eta n (Sm eta L w)) := by
  have hM := hF.nonneg
  refine ⟨?_, fun a l hl => ⟨?_, ?_⟩⟩
  · rw [ext_wt_one]
    have h1 := norm_ext_le (n := n) (Sm eta L w)
    have h2 := norm_ext_le (n := n) (Sm eta L w + coulombFourierKineticH2 sys (gF L) w)
    have h3 := norm_add_le (Sm eta L w) (coulombFourierKineticH2 sys (gF L) w)
    linarith [hF.1, norm_nonneg (coulombFourierKineticH2 sys (gF L) w)]
  · rw [regTail_ext, one_mul]
    refine (norm_ext_le _).trans ((hF.2 a l hl).1.trans ?_)
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
  · rw [wt_regTail, ext_wt_one, regTail_ext, one_mul]
    refine (norm_ext_le _).trans ?_
    rw [map_add]
    refine (norm_add_le _ _).trans ?_
    have h52 : l ^ (-(5 / 2 : ℝ)) ≤ l ^ (-(1 / 2 : ℝ)) := rpow_le_of_le_one hl (by norm_num)
    have := (hF.2 a l hl).1; have := (hF.2 a l hl).2
    nlinarith [mul_le_mul_of_nonneg_left h52 hM]

omit [Fintype ν] in
/-- **Goodness is stable under small perturbations**: `‖e‖ ≤ δ`, `‖(1+A) e‖ ≤ δ₁` give the budget
`M + (δ + δ₁)(1 + √3 K)³` (the tails of `e` vanish beyond `√3 K`). -/
theorem isGood_perturb (hL : 0 < L) {M δ δ₁ : ℝ} {u e : En eta n} (hu : IsGood sys L 1 M u)
    (he : ‖e‖ ≤ δ) (he1 : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 e‖ ≤ δ₁) :
    IsGood sys L 1 (M + (δ + δ₁) * (1 + Real.sqrt 3 * (gF L * n)) ^ 3) (u + e) := by
  set Kq := Real.sqrt 3 * (gF L * n)
  have hKq : 0 ≤ Kq := by have := gF_pos hL; positivity
  have hδ : 0 ≤ δ := le_trans (norm_nonneg _) he
  have hδ₁ : 0 ≤ δ₁ := le_trans (norm_nonneg _) he1
  have hpow : 1 ≤ (1 + Kq) ^ 3 := one_le_pow₀ (by linarith)
  -- `l^{-e} (1 + Kq)³ ≥ 1` for `1 ≤ l ≤ Kq`, `0 ≤ e ≤ 3`
  have hlow : ∀ (l e : ℝ), 1 ≤ l → l ≤ Kq → 0 ≤ e → e ≤ 3 → 1 ≤ (1 + Kq) ^ 3 * l ^ (-e) := by
    intro l e hl hlK he0 he3
    have hl0 : 0 < l := by linarith
    rw [Real.rpow_neg hl0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hl0 _), one_mul]
    calc l ^ e ≤ l ^ (3 : ℝ) := rpow_le_of_le_one hl he3
      _ = l ^ 3 := by norm_cast
      _ ≤ (1 + Kq) ^ 3 := pow_le_pow_left₀ hl0.le (by linarith) 3
  have he_good : IsGood sys L 1 ((δ + δ₁) * (1 + Kq) ^ 3) e := by
    refine ⟨?_, fun a l hl => ⟨?_, ?_⟩⟩
    · have : δ + δ₁ ≤ (δ + δ₁) * (1 + Kq) ^ 3 := le_mul_of_one_le_right (by positivity) hpow
      linarith
    · rw [one_mul]
      by_cases hlK : Kq ≤ l
      · rw [regTail_eq_zero_of_large hL a hlK, norm_zero]; positivity
      · push Not at hlK
        have h1 := hlow l (5 / 2) hl hlK.le (by norm_num) (by norm_num)
        calc ‖regTail L a l e‖ ≤ ‖e‖ := norm_regTail_le L a l e
          _ ≤ δ := he
          _ ≤ δ + δ₁ := by linarith
          _ ≤ (δ + δ₁) * ((1 + Kq) ^ 3 * l ^ (-(5 / 2 : ℝ))) := le_mul_of_one_le_right (by positivity) h1
          _ = _ := by ring
    · rw [one_mul]
      by_cases hlK : Kq ≤ l
      · rw [regTail_eq_zero_of_large hL a hlK, wt_one_zero, norm_zero]; positivity
      · push Not at hlK
        have h1 := hlow l (1 / 2) hl hlK.le (by norm_num) (by norm_num)
        rw [wt_regTail]
        calc ‖regTail L a l (FSSpectral.wt (sb eta n) (Asym sys L n) 1 e)‖
            ≤ ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 e‖ := norm_regTail_le L a l _
          _ ≤ δ₁ := he1
          _ ≤ δ + δ₁ := by linarith
          _ ≤ (δ + δ₁) * ((1 + Kq) ^ 3 * l ^ (-(1 / 2 : ℝ))) := le_mul_of_one_le_right (by positivity) h1
          _ = _ := by ring
  exact isGood_add sys hu he_good

end Cube

/-! ## Stability of good trajectories (`lem:good-stab`) -/

section Stab

variable (sys : CoulombSystem eta ν) {L : ℝ} {n : ℕ}

lemma retFlow_add_apply {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) (τ : ℝ)
    (x y : En eta n) :
    retFlow sys L n hΔsym τ (x + y) = retFlow sys L n hΔsym τ x + retFlow sys L n hΔsym τ y := by
  unfold retFlow FSSpectral.fc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_add_right, mul_add, add_smul]

lemma retFlow_sub_apply {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) (τ : ℝ)
    (x y : En eta n) :
    retFlow sys L n hΔsym τ (x - y) = retFlow sys L n hΔsym τ x - retFlow sys L n hΔsym τ y := by
  unfold retFlow FSSpectral.fc
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sub_right, mul_sub, sub_smul]

lemma Hret_retFlow {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) (τ : ℝ) (u : En eta n) :
    Hret sys L n ΔH (retFlow sys L n hΔsym τ u) = retFlow sys L n hΔsym τ (Hret sys L n ΔH u) := by
  have h1 := FSSpectral.apply_fc_of_eigen (retBasis sys L n hΔsym) (retEig sys L n hΔsym)
    (Hret sys L n ΔH) (retBasis_eigen sys L n hΔsym)
    (fun x => Complex.exp (Complex.I * (x : ℂ) * τ)) u
  have h2 := FSSpectral.eigen_fc_id (retBasis sys L n hΔsym) (retEig sys L n hΔsym)
    (Hret sys L n ΔH) (retBasis_eigen sys L n hΔsym) u
  unfold retFlow
  rw [h1, h2, FSSpectral.fc_comp]
  refine FSSpectral.fc_congr _ _ (fun i => mul_comm _ _) u

omit [Fintype ν] in
lemma kin_apply' (v : En eta n) (q : Cfg eta n) :
    (FSSpectral.kin (sb eta n) (Asym sys L n) v).ofLp q = (Asym sys L n q : ℂ) * v.ofLp q := by
  rw [FSSpectral.kin, fc_sb_apply]

omit [Fintype ν] in
lemma kin_regTail (a : Fin eta) (l : ℝ) (v : En eta n) :
    FSSpectral.kin (sb eta n) (Asym sys L n) (regTail L a l v) =
      regTail L a l (FSSpectral.kin (sb eta n) (Asym sys L n) v) := by
  ext p
  rw [kin_apply', regTail_apply, regTail_apply, kin_apply']
  split_ifs <;> simp

omit [Fintype ν] in
/-- On the register tail beyond `l`, `A ≥ l²/(2 m_a)`: `‖Q_{a,l} v‖ ≤ (2 m_a/l²) ‖A Q_{a,l} v‖`. -/
lemma regTail_le_kin (hL : 0 < L) (a : Fin eta) {l : ℝ} (hl : 0 < l) (v : En eta n) :
    ‖regTail L a l v‖ ≤ 2 * sys.mass a / l ^ 2 *
      ‖FSSpectral.kin (sb eta n) (Asym sys L n) (regTail L a l v)‖ := by
  have hm := sys.mass_pos a
  have h2 : ‖regTail L a l v‖ ^ 2 ≤ (2 * sys.mass a / l ^ 2 *
      ‖FSSpectral.kin (sb eta n) (Asym sys L n) (regTail L a l v)‖) ^ 2 := by
    rw [mul_pow, norm_sq_En, norm_sq_En, Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [kin_apply', regTail_apply]
    split_ifs with hp
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Asym_nonneg sys L n p)]
      have hk := kabs_nonneg (n := n) hL (p a)
      have hA : finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2 / (2 * sys.mass a) ≤
          Asym sys L n p := by
        unfold Asym massKineticSymbol
        have := Finset.single_le_sum (f := fun c => finitePlaneWaveKabs (2 * Real.pi / L) n (p c) ^ 2 /
          sys.mass c) (fun c _ => by have := sys.mass_pos c; positivity) (Finset.mem_univ a)
        have e : finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2 / (2 * sys.mass a) =
            1 / 2 * (finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2 / sys.mass a) := by
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left this (by norm_num)
      have hl2 : l ^ 2 < finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2 :=
        pow_lt_pow_left₀ hp hl.le two_ne_zero
      have hA' : l ^ 2 / (2 * sys.mass a) ≤ Asym sys L n p :=
        le_trans (div_le_div_of_nonneg_right hl2.le (by positivity)) hA
      have hfac : 1 ≤ 2 * sys.mass a / l ^ 2 * Asym sys L n p := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
        have := mul_le_mul_of_nonneg_left hA' (by positivity : (0 : ℝ) ≤ 2 * sys.mass a)
        rwa [mul_div_cancel₀ _ (by positivity : (2 * sys.mass a) ≠ 0)] at this
      have hfac2 : 1 ≤ (2 * sys.mass a / l ^ 2) ^ 2 * Asym sys L n p ^ 2 := by
        rw [← mul_pow]; exact one_le_pow₀ hfac
      calc ‖v.ofLp p‖ ^ 2 ≤ (2 * sys.mass a / l ^ 2) ^ 2 * Asym sys L n p ^ 2 * ‖v.ofLp p‖ ^ 2 :=
            le_mul_of_one_le_left (sq_nonneg _) hfac2
        _ = _ := by ring
    · simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

omit [Fintype ν] in
lemma ext_kinetic_cubeLift (v : En eta n) :
    ext eta n (coulombFourierKineticH2 sys (gF L) (cubeLift (gF L) n v)) =
      FSSpectral.kin (sb eta n) (Asym sys L n) v := by
  ext q
  rw [extractCLM_apply, coulombFourierKineticH2_apply, kin_apply', Asym_eq_Ek, Ek, E_eq_kineticSymbol]
  congr 1
  have h := congrArg (fun x : L2 eta => x (finiteConfigLatticeIndex eta n q))
    (stateMap_cubeLift (gF L) n v)
  simp only [molecularH2StateMap_apply, finiteFourierLpIsometry_apply,
    finiteFourierLpEmbed_apply_index] at h
  exact h

omit [Fintype ν] in
lemma norm_kinetic_cubeLift (v : En eta n) :
    ‖coulombFourierKineticH2 sys (gF L) (cubeLift (gF L) n v)‖ =
      ‖FSSpectral.kin (sb eta n) (Asym sys L n) v‖ := by
  rw [← ext_kinetic_cubeLift sys v]
  exact (norm_extract_of_truncate n _ (kinetic_cubeLift_truncate sys (gF L) n v)).symm

variable (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel in
/-- `P W` on the lift of a cube vector is the finite potential: `P W (cubeLift v) = W_N v`. -/
lemma ext_W_cubeLift (v : En eta n) :
    ext eta n (Wp sys L H (cubeLift (gF L) n v)) =
      finiteCoulombPotential sys (coulombCellAmplitude L) n v := by
  have h1 := finiteH_eq_extract sys L H hKernel n v
  have h2 := coulombFourierHamiltonianH2_decomposition sys (gF L) H (cubeLift (gF L) n v)
  have h3 := HN_eq_kin_add sys L n v
  have h4 := ext_kinetic_cubeLift sys (L := L) v
  change finiteCoulombHamiltonian sys L n v = ext eta n (H (cubeLift (gF L) n v)) at h1
  rw [h2, map_add, h4] at h1
  rw [h3] at h1
  exact (add_left_cancel h1).symm

include hKernel in
/-- **Potential tails on the cube** (`eq:lam-gen` for cube vectors): for `l ≥ max(1, 2g)` and
`M₂ ≥ m̄ (‖v‖ + 2 ‖A v‖)`, `‖Q_{a,l} W_N v‖ ≤ C_tail(M₂) l^{-1/2}`. -/
theorem regTail_WN_le (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (a : Fin eta) {l : ℝ} (hl1 : 1 ≤ l) (hl2 : 2 * gF L ≤ l) (v : En eta n) {M₂ : ℝ}
    (hM₂ : sys.maxMass * (‖v‖ + 2 * ‖FSSpectral.kin (sb eta n) (Asym sys L n) v‖) ≤ M₂) :
    ‖regTail L a l (finiteCoulombPotential sys (coulombCellAmplitude L) n v)‖ ≤
      finiteCoulombPhysicalTailConstant sys L Hunit (molecularCanonicalLowConstant L)
        (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L) M₂ *
        l ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨hBlow, hCs, hBker, hLow, hKernelScale, hSobolev⟩ :=
    molecularCanonicalTailConstants_spec L hL
  have hl0 : 0 < l := by linarith
  set u := cubeLift (gF L) n v
  have hu : ‖u‖ ≤ M₂ := by
    have h := h2norm_le sys L u
    have hS : ‖molecularH2StateMap eta (2 * Real.pi / L) u‖ = ‖v‖ := by
      rw [show molecularH2StateMap eta (2 * Real.pi / L) u = finiteFourierLpIsometry eta n v from
        stateMap_cubeLift (gF L) n v, LinearIsometry.norm_map]
    have hT : ‖coulombFourierKineticH2 sys (2 * Real.pi / L) u‖ =
        ‖FSSpectral.kin (sb eta n) (Asym sys L n) v‖ := norm_kinetic_cubeLift sys v
    rw [hS, hT] at h
    exact h.trans hM₂
  have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) hu
  have hρ : Real.sqrt (1 / l) ^ 2 * l = 1 := by
    rw [Real.sq_sqrt (by positivity)]; field_simp
  have h := potential_tail_le sys L H hKernel Hunit hL hPeriodic a l (Real.sqrt (1 / l))
    (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
    (molecularCanonicalKernelConstant L) M₂ hl1 (Real.sqrt_nonneg _) hρ hBlow hCs hBker hM₂0 hl2
    hLow hKernelScale hSobolev u hu
  have hsq : Real.sqrt (1 / l) = l ^ (-(1 / 2 : ℝ)) := by
    rw [rpow_neg_half_eq hl0, Real.sqrt_div' 1 hl0.le, Real.sqrt_one]
  rw [← ext_W_cubeLift sys H hKernel v, regTail_ext, ← hsq]
  exact (norm_ext_le _).trans h

/-- The flow constant `C_fl = C_rev (C_V + C_low + 2)` (`lem:retflow` at `s = 1`). -/
noncomputable def Cfl (sys : CoulombSystem eta ν) (L Hunit CΔ : ℝ) : ℝ :=
  Crev sys L Hunit CΔ * (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2)

lemma Cfl_nonneg (Hunit : ℝ) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) : 0 ≤ Cfl sys L Hunit CΔ := by
  unfold Cfl Crev
  have := CVret_nonneg sys Hunit hCΔ (L := L)
  have := (Clow_pos sys Hunit hCΔ (L := L)).le
  positivity

/-- `Θ(e^{iH'τ} u) ≤ C_fl Θ(u)`. -/
lemma theta_retFlow_le (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) (τ : ℝ) (u : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (retFlow sys L n hΔsym τ u)‖ ≤
      Cfl sys L Hunit CΔ * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
  have h := retflow sys Hunit hL hPeriodic hΔsym hCΔ hΔb (s := 1) ⟨zero_le_one, le_rfl⟩ τ u
  simpa only [Real.rpow_one, Cfl] using h

/-- The stability budget. -/
noncomputable def Mstab (sys : CoulombSystem eta ν) (L Hunit CΔ : ℝ) (n : ℕ)
    (Θ₀ Θv ε₀ α : ℝ) : ℝ :=
  2 * Cfl sys L Hunit CΔ * Θ₀ + (2 * sys.maxMass + 1) *
    (2 * sys.maxMass * Cfl sys L Hunit CΔ * Θv +
      (ε₀ + α * Cfl sys L Hunit CΔ * Θ₀) * (1 + Real.sqrt 3 * (gF L * n)) ^ 3 +
      (finiteCoulombPhysicalTailConstant sys L Hunit (molecularCanonicalLowConstant L)
        (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L)
        (3 * sys.maxMass * Cfl sys L Hunit CΔ * Θ₀) +
        Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) *
          Cfl sys L Hunit CΔ * Θ₀))

include hKernel in
/-- **`lem:good-stab`**: let `H' = H_N + ΔH` with `ΔH` symmetric, `‖ΔH v‖ ≤ C_Δ ‖v‖` and
`‖ΔH v‖ ≤ α ‖(1+A) v‖`, and let `χ₀ = P ψ₀ + r₀` with `ψ₀ = S u₀ ∈ D(H²)` (`H u₀ = S v₀`). With
`Θ(χ₀) ≤ Θ₀`, `‖P ψ₀‖ + ‖(1+A) P S v₀‖... ≤ Θv` (the `D(H²)` datum) and the defect
`e₀ = H_N r₀ + ΔH χ₀ - P W (1 - P) u₀`, `‖e₀‖ ≤ ε₀`, every state `e^{iH'τ} χ₀` is good with the
budget `Mstab`. -/
theorem good_stab (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) {α : ℝ} (hα0 : 0 ≤ α)
    (hα : ∀ v, ‖ΔH v‖ ≤ α * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖)
    (u₀ v₀ : MolecularFourierH2 eta) (huv : H u₀ = Sm eta L v₀) (r₀ : En eta n)
    {Θ₀ Θv ε₀ : ℝ}
    (hΘ₀ : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L u₀) + r₀)‖ ≤ Θ₀)
    (hΘv : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (ext eta n (Sm eta L v₀))‖ ≤ Θv)
    (hε₀ : ‖finiteCoulombHamiltonian sys L n r₀ + ΔH (ext eta n (Sm eta L u₀) + r₀) -
      ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀))‖ ≤ ε₀)
    (τ : ℝ) :
    IsGood sys L 1 (Mstab sys L Hunit CΔ n Θ₀ Θv ε₀ α)
      (retFlow sys L n hΔsym τ (ext eta n (Sm eta L u₀) + r₀)) := by
  set χ₀ := ext eta n (Sm eta L u₀) + r₀
  set χ := retFlow sys L n hΔsym τ χ₀
  set C := Cfl sys L Hunit CΔ
  set Θ := fun v : En eta n => ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖
  set A := FSSpectral.kin (sb eta n) (Asym sys L n)
  set WN := finiteCoulombPotential sys (coulombCellAmplitude L) n
  set Kq := Real.sqrt 3 * (gF L * n)
  have hC := Cfl_nonneg sys Hunit hCΔ (L := L)
  have hg := gF_pos hL
  have hm := sys.one_le_maxMass
  have hKq : 0 ≤ Kq := by positivity
  have hΘ₀0 : 0 ≤ Θ₀ := le_trans (norm_nonneg _) hΘ₀
  have hΘv0 : 0 ≤ Θv := le_trans (norm_nonneg _) hΘv
  have hε0 : 0 ≤ ε₀ := le_trans (norm_nonneg _) hε₀
  -- the norms along the flow
  have hΘχ : Θ χ ≤ C * Θ₀ :=
    (theta_retFlow_le sys Hunit hL hPeriodic hΔsym hCΔ hΔb τ χ₀).trans
      (mul_le_mul_of_nonneg_left hΘ₀ hC)
  have hχΘ : ‖χ‖ ≤ Θ χ := norm_le_wt sys L n zero_le_one χ
  have hAχ : ‖A χ‖ ≤ Θ χ := norm_kin_le_wt sys χ
  -- the decomposition `H' χ = f + e`
  set f := retFlow sys L n hΔsym τ (ext eta n (Sm eta L v₀))
  set e₀ := finiteCoulombHamiltonian sys L n r₀ + ΔH χ₀ -
    ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀))
  set e := retFlow sys L n hΔsym τ e₀
  have hHχ₀ : Hret sys L n ΔH χ₀ = ext eta n (Sm eta L v₀) + e₀ := by
    have hext : ext eta n (H u₀) = finiteCoulombHamiltonian sys L n (ext eta n (Sm eta L u₀)) +
        ext eta n (Wp sys L H (u₀ - molecularH2Truncate n u₀)) := extract_H_eq sys L H hKernel n u₀
    rw [huv] at hext
    rw [hext]
    have h1 : Hret sys L n ΔH χ₀ = finiteCoulombHamiltonian sys L n (ext eta n (Sm eta L u₀)) +
        finiteCoulombHamiltonian sys L n r₀ + ΔH χ₀ := by
      unfold Hret
      rw [LinearMap.add_apply, map_add]
    rw [h1]
    simp only [e₀]
    abel
  have hdec : Hret sys L n ΔH χ = f + e := by
    rw [Hret_retFlow, hHχ₀, retFlow_add_apply]
  have hΘf : Θ f ≤ C * Θv :=
    (theta_retFlow_le sys Hunit hL hPeriodic hΔsym hCΔ hΔb τ _).trans
      (mul_le_mul_of_nonneg_left hΘv hC)
  have he : ‖e‖ ≤ ε₀ := by rw [norm_retFlow]; exact hε₀
  have hAeq : A χ = f + e - WN χ - ΔH χ := by
    have := Hret_eq_kin_add sys L n ΔH χ
    rw [hdec] at this
    unfold Vret at this
    rw [LinearMap.add_apply] at this
    rw [this]; abel
  -- the tails of `A χ`
  have hBA : ∀ (a : Fin eta) (l : ℝ), 1 ≤ l → l < Kq →
      ‖regTail L a l (A χ)‖ ≤
        (2 * sys.maxMass * C * Θv + (ε₀ + α * C * Θ₀) * (1 + Kq) ^ 3 +
          (finiteCoulombPhysicalTailConstant sys L Hunit (molecularCanonicalLowConstant L)
            (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L)
            (3 * sys.maxMass * C * Θ₀) +
            Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) * C * Θ₀)) *
          l ^ (-(1 / 2 : ℝ)) := by
    intro a l hl hlK
    have hl0 : 0 < l := by linarith
    have hpow : 1 ≤ (1 + Kq) ^ 3 * l ^ (-(1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hl0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hl0 _), one_mul]
      calc l ^ (1 / 2 : ℝ) ≤ l ^ (3 : ℝ) := rpow_le_of_le_one hl (by norm_num)
        _ = l ^ 3 := by norm_cast
        _ ≤ (1 + Kq) ^ 3 := pow_le_pow_left₀ hl0.le (by linarith) 3
    have hinv : 1 / l ^ 2 ≤ l ^ (-(1 / 2 : ℝ)) := by
      have : l ^ (-(2 : ℝ)) ≤ l ^ (-(1 / 2 : ℝ)) := rpow_le_of_le_one hl (by norm_num)
      rwa [Real.rpow_neg hl0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        ← one_div] at this
    rw [hAeq, map_sub, map_sub, map_add]
    -- the four pieces
    have h1 : ‖regTail L a l f‖ ≤ 2 * sys.maxMass * C * Θv * l ^ (-(1 / 2 : ℝ)) := by
      refine (regTail_le_kin sys hL a hl0 f).trans ?_
      rw [kin_regTail]
      have hf1 : ‖regTail L a l (A f)‖ ≤ C * Θv :=
        (norm_regTail_le L a l _).trans ((norm_kin_le_wt sys f).trans hΘf)
      have hma := sys.mass_le_maxMass a
      calc 2 * sys.mass a / l ^ 2 * ‖regTail L a l (A f)‖ ≤ 2 * sys.maxMass * (1 / l ^ 2) * (C * Θv) := by
            rw [div_eq_mul_one_div (2 * sys.mass a)]
            gcongr
        _ ≤ 2 * sys.maxMass * l ^ (-(1 / 2 : ℝ)) * (C * Θv) := by gcongr
        _ = _ := by ring
    have h2 : ‖regTail L a l e‖ ≤ ε₀ * (1 + Kq) ^ 3 * l ^ (-(1 / 2 : ℝ)) := by
      refine (norm_regTail_le L a l e).trans (he.trans ?_)
      rw [mul_assoc]; exact le_mul_of_one_le_right hε0 hpow
    have h3 : ‖regTail L a l (WN χ)‖ ≤ (finiteCoulombPhysicalTailConstant sys L Hunit
        (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
        (molecularCanonicalKernelConstant L) (3 * sys.maxMass * C * Θ₀) +
        Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) * C * Θ₀) *
          l ^ (-(1 / 2 : ℝ)) := by
      obtain ⟨hBlow, hCs, hBker, -, -, -⟩ := molecularCanonicalTailConstants_spec L hL
      have hCt0 : 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit
          (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
          (molecularCanonicalKernelConstant L) (3 * sys.maxMass * C * Θ₀) :=
        finiteCoulombPhysicalTailConstant_nonneg _ _ _ hBlow hCs hBker (by positivity)
      have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
      have hlr : 0 ≤ l ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hl0.le _
      by_cases hl2 : 2 * gF L ≤ l
      · have h := regTail_WN_le sys H hKernel Hunit hL hPeriodic a hl hl2 χ (M₂ := 3 * sys.maxMass * C * Θ₀)
          (by
            have : ‖χ‖ + 2 * ‖A χ‖ ≤ 3 * (C * Θ₀) := by linarith
            calc sys.maxMass * (‖χ‖ + 2 * ‖A χ‖) ≤ sys.maxMass * (3 * (C * Θ₀)) :=
                  mul_le_mul_of_nonneg_left this (by linarith)
              _ = _ := by ring)
        refine h.trans ?_
        have : 0 ≤ Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) *
          C * Θ₀ * l ^ (-(1 / 2 : ℝ)) := by positivity
        have e : (finiteCoulombPhysicalTailConstant sys L Hunit
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) (3 * sys.maxMass * C * Θ₀) +
            Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) * C * Θ₀) *
              l ^ (-(1 / 2 : ℝ)) = finiteCoulombPhysicalTailConstant sys L Hunit
            (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
            (molecularCanonicalKernelConstant L) (3 * sys.maxMass * C * Θ₀) * l ^ (-(1 / 2 : ℝ)) +
            Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) *
              C * Θ₀ * l ^ (-(1 / 2 : ℝ)) := by ring
        linarith
      · push Not at hl2
        have hWN := (potential_le_wt sys Hunit n hL hPeriodic χ).trans
          (mul_le_mul_of_nonneg_left (wt_mono sys L n (by norm_num : (1 / 2 : ℝ) ≤ 1) χ)
            (by positivity))
        have hpow2 : 1 ≤ (1 + 2 * gF L) * l ^ (-(1 / 2 : ℝ)) := by
          rw [Real.rpow_neg hl0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hl0 _),
            one_mul]
          calc l ^ (1 / 2 : ℝ) ≤ l ^ (1 : ℝ) := rpow_le_of_le_one hl (by norm_num)
            _ = l := Real.rpow_one l
            _ ≤ 1 + 2 * gF L := by linarith
        calc ‖regTail L a l (WN χ)‖ ≤ ‖WN χ‖ := norm_regTail_le L a l _
          _ ≤ Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * Θ χ := hWN
          _ ≤ Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (C * Θ₀) :=
              mul_le_mul_of_nonneg_left hΘχ (by positivity)
          _ ≤ Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (C * Θ₀) *
                ((1 + 2 * gF L) * l ^ (-(1 / 2 : ℝ))) :=
              le_mul_of_one_le_right (by positivity) hpow2
          _ ≤ _ := by
              have e : (finiteCoulombPhysicalTailConstant sys L Hunit
                  (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
                  (molecularCanonicalKernelConstant L) (3 * sys.maxMass * C * Θ₀) +
                  Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) *
                    C * Θ₀) * l ^ (-(1 / 2 : ℝ)) = finiteCoulombPhysicalTailConstant sys L Hunit
                  (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
                  (molecularCanonicalKernelConstant L) (3 * sys.maxMass * C * Θ₀) *
                    l ^ (-(1 / 2 : ℝ)) +
                  Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (C * Θ₀) *
                    ((1 + 2 * gF L) * l ^ (-(1 / 2 : ℝ))) := by ring
              have : 0 ≤ finiteCoulombPhysicalTailConstant sys L Hunit
                  (molecularCanonicalLowConstant L) (molecularCanonicalSobolevConstant L)
                  (molecularCanonicalKernelConstant L) (3 * sys.maxMass * C * Θ₀) *
                    l ^ (-(1 / 2 : ℝ)) := mul_nonneg hCt0 hlr
              linarith
    have h4 : ‖regTail L a l (ΔH χ)‖ ≤ α * C * Θ₀ * (1 + Kq) ^ 3 * l ^ (-(1 / 2 : ℝ)) := by
      refine (norm_regTail_le L a l _).trans ((hα χ).trans ?_)
      calc α * Θ χ ≤ α * (C * Θ₀) := mul_le_mul_of_nonneg_left hΘχ hα0
        _ ≤ α * (C * Θ₀) * ((1 + Kq) ^ 3 * l ^ (-(1 / 2 : ℝ))) :=
            le_mul_of_one_le_right (by positivity) hpow
        _ = _ := by ring
    calc ‖regTail L a l f + regTail L a l e - regTail L a l (WN χ) - regTail L a l (ΔH χ)‖
        ≤ ‖regTail L a l f‖ + ‖regTail L a l e‖ + ‖regTail L a l (WN χ)‖ +
            ‖regTail L a l (ΔH χ)‖ := by
          refine (norm_sub_le _ _).trans ?_
          refine add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl
      _ ≤ _ := by
          have e : (2 * sys.maxMass * C * Θv + (ε₀ + α * C * Θ₀) * (1 + Kq) ^ 3 +
              (finiteCoulombPhysicalTailConstant sys L Hunit (molecularCanonicalLowConstant L)
                (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L)
                (3 * sys.maxMass * C * Θ₀) +
                Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) * C *
                  Θ₀)) * l ^ (-(1 / 2 : ℝ)) =
              2 * sys.maxMass * C * Θv * l ^ (-(1 / 2 : ℝ)) +
              ε₀ * (1 + Kq) ^ 3 * l ^ (-(1 / 2 : ℝ)) +
              (finiteCoulombPhysicalTailConstant sys L Hunit (molecularCanonicalLowConstant L)
                (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L)
                (3 * sys.maxMass * C * Θ₀) +
                Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) * C *
                  Θ₀) * l ^ (-(1 / 2 : ℝ)) +
              α * C * Θ₀ * (1 + Kq) ^ 3 * l ^ (-(1 / 2 : ℝ)) := by ring
          linarith
  -- assemble
  have hBA0 : 0 ≤ 2 * sys.maxMass * C * Θv + (ε₀ + α * C * Θ₀) * (1 + Kq) ^ 3 +
      (finiteCoulombPhysicalTailConstant sys L Hunit (molecularCanonicalLowConstant L)
        (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L)
        (3 * sys.maxMass * C * Θ₀) +
        Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) * C * Θ₀) := by
    obtain ⟨hBlow, hCs, hBker, -, -, -⟩ := molecularCanonicalTailConstants_spec L hL
    have := finiteCoulombPhysicalTailConstant_nonneg sys L Hunit hBlow hCs hBker
      (by positivity : (0 : ℝ) ≤ 3 * sys.maxMass * C * Θ₀)
    have := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
    positivity
  set BA := 2 * sys.maxMass * C * Θv + (ε₀ + α * C * Θ₀) * (1 + Kq) ^ 3 +
      (finiteCoulombPhysicalTailConstant sys L Hunit (molecularCanonicalLowConstant L)
        (molecularCanonicalSobolevConstant L) (molecularCanonicalKernelConstant L)
        (3 * sys.maxMass * C * Θ₀) +
        Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * (1 + 2 * gF L) * C * Θ₀)
  have hM : Mstab sys L Hunit CΔ n Θ₀ Θv ε₀ α = 2 * C * Θ₀ + (2 * sys.maxMass + 1) * BA := rfl
  rw [hM]
  refine ⟨?_, fun a l hl => ?_⟩
  · have : 0 ≤ (2 * sys.maxMass + 1) * BA := by positivity
    have := hχΘ; have := hΘχ
    linarith
  have hl0 : 0 < l := by linarith
  by_cases hlK : Kq ≤ l
  · rw [regTail_eq_zero_of_large hL a hlK, norm_zero, wt_one_zero, norm_zero]
    exact ⟨by positivity, by positivity⟩
  push Not at hlK
  have hA := hBA a l hl hlK
  have hmass := sys.mass_le_maxMass a
  have hinv : 1 / l ^ 2 * l ^ (-(1 / 2 : ℝ)) = l ^ (-(5 / 2 : ℝ)) := by
    rw [rpow_neg_five_half_eq hl0, rpow_neg_half_eq hl0]; field_simp
  have hT : ‖regTail L a l χ‖ ≤ 2 * sys.maxMass * BA * l ^ (-(5 / 2 : ℝ)) := by
    refine (regTail_le_kin sys hL a hl0 χ).trans ?_
    rw [kin_regTail]
    calc 2 * sys.mass a / l ^ 2 * ‖regTail L a l (A χ)‖
        ≤ 2 * sys.maxMass * (1 / l ^ 2) * (BA * l ^ (-(1 / 2 : ℝ))) := by
          rw [div_eq_mul_one_div (2 * sys.mass a)]
          gcongr
      _ = 2 * sys.maxMass * BA * (1 / l ^ 2 * l ^ (-(1 / 2 : ℝ))) := by ring
      _ = _ := by rw [hinv]
  have h52 : l ^ (-(5 / 2 : ℝ)) ≤ l ^ (-(1 / 2 : ℝ)) := rpow_le_of_le_one hl (by norm_num)
  have hlr : 0 ≤ l ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hl0.le _
  constructor
  · rw [one_mul]
    refine hT.trans ?_
    have h1 : 0 ≤ 2 * C * Θ₀ * l ^ (-(5 / 2 : ℝ)) := by positivity
    have h2 : 0 ≤ BA * l ^ (-(5 / 2 : ℝ)) := mul_nonneg hBA0 hlr
    have e : (2 * C * Θ₀ + (2 * sys.maxMass + 1) * BA) * l ^ (-(5 / 2 : ℝ)) =
        2 * C * Θ₀ * l ^ (-(5 / 2 : ℝ)) + 2 * sys.maxMass * BA * l ^ (-(5 / 2 : ℝ)) +
          BA * l ^ (-(5 / 2 : ℝ)) := by ring
    linarith
  · rw [one_mul]
    have hw : FSSpectral.wt (sb eta n) (Asym sys L n) 1 (regTail L a l χ) =
        regTail L a l χ + A (regTail L a l χ) := by
      ext q; rw [wt_one_apply, PiLp.add_apply, kin_apply']; push_cast; ring
    rw [hw, show A (regTail L a l χ) = regTail L a l (A χ) from kin_regTail sys a l χ]
    refine (norm_add_le _ _).trans ?_
    have h1 : 0 ≤ 2 * C * Θ₀ * l ^ (-(1 / 2 : ℝ)) := by
      have := Real.rpow_nonneg hl0.le (-(1 / 2 : ℝ)); positivity
    have h2 := mul_le_mul_of_nonneg_left h52 (by positivity : (0 : ℝ) ≤ 2 * sys.maxMass * BA)
    have e : (2 * C * Θ₀ + (2 * sys.maxMass + 1) * BA) * l ^ (-(1 / 2 : ℝ)) =
        2 * C * Θ₀ * l ^ (-(1 / 2 : ℝ)) + 2 * sys.maxMass * BA * l ^ (-(1 / 2 : ℝ)) +
          BA * l ^ (-(1 / 2 : ℝ)) := by ring
    have e2 : 2 * sys.maxMass * BA * l ^ (-(5 / 2 : ℝ)) = 2 * sys.maxMass * BA * l ^ (-(5 / 2 : ℝ)) := rfl
    linarith

end Stab

end FSNormal
