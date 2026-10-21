import PlaneWave.FluxBox.CommutatorCrossChannel

/-!
# Flux route, stage 2, part 20: the commutator `[W, Y₂]` at the target rate

Assembly of `PlaneWave.FluxBox.CommutatorSamePair` (same pair) and `PlaneWave.FluxBox.CommutatorCrossChannel` (cross channels):

* `norm_inner_W_Y2_le`: `|⟨u, W Y₂ u⟩| ≤ Σ_{j'} Σ_j Σ_{a,c,b} |u_a| w_{j'}(a,c) y2M_j(c,b) |u_b|`;
* the weights of the cross bound (`cross_weight_le`, `cross_weight_pi_le`):
  `(1+|ξ|²)(1+|ζ|²)^{1/2} ≤ 2√2 c_X^{3/2} (1+A)^{3/2}`, `|Π_j|² (1+|ξ|²)(1+|ζ|²)^{1/2} ≤ 4√2 c_X^{5/2} (1+A)^{5/2}`;
* `cross_good`: the cross-channel term on a good state, with the critical moment on the bulk end;
* **`norm_comm_WY2_good`**: `|Re⟨u, i[W, Y₂] u⟩| ≤ 2 C_{WY} M²`,
  `C_{WY} = Σ_j c_j C_j Λ_{2N} 125(log₂ N + 2) √2 c_X²
    + Σ_{j',j} c_{j'} C_j Λ_{2N}² √(2√2 c_X^{3/2}) √(4√2 c_X^{5/2}) √((1+η/2)^{1/2}(1 + 2η n_d))`,
  `C_j ~ n⁻³`, `Λ_{2N} ~ log N`: the commutator is at `n⁻³` up to logarithms.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Assembly

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

omit [Fintype ν] in
lemma sum4_comm {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℝ) :
    ∑ a, ∑ c, ∑ x, ∑ y, F a c x y = ∑ x, ∑ y, ∑ a, ∑ c, F a c x y := by
  calc ∑ a, ∑ c, ∑ x, ∑ y, F a c x y = ∑ a, ∑ x, ∑ c, ∑ y, F a c x y :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ c, ∑ y, F a c x y := Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ y, ∑ c, F a c x y :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ a, ∑ c, F a c x y :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm

/-- The composite bound: `|⟨u, W Y₂ u⟩| ≤ Σ_{j',j} Σ_{a,c,b} |u_a| w_{j'} y2M_j |u_b|`. -/
theorem norm_inner_W_Y2_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) (u : En eta N) :
    ‖⟪u, WN sys L N (Y2N sys L p₀ N n u)⟫_ℂ‖ ≤ ∑ j', ∑ j, ∑ a, ∑ c, ∑ b,
      ‖u.ofLp a‖ * wM sys L N j' a c * y2M sys L N n j c b * ‖u.ofLp b‖ := by
  have hW : WN sys L N = FSKernel.kop (wNK sys L N) := VN_eq_kop sys hL H hKernel
  rw [hW]
  refine (norm_inner_kop_le₂ _ u _).trans ?_
  have hv : ∀ c, ‖(Y2N sys L p₀ N n u).ofLp c‖ ≤ ∑ b, ‖u.ofLp b‖ * ∑ j, y2M sys L N n j c b := by
    intro c
    rw [FSKernel.kop_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_y2K_le hL H hKernel hn c b) (norm_nonneg _)
  have hpt : ∀ a c, ‖u.ofLp a‖ * ‖(Y2N sys L p₀ N n u).ofLp c‖ * ‖wNK sys L N a c‖ ≤
      ∑ j', ∑ j, ∑ b, ‖u.ofLp a‖ * wM sys L N j' a c * y2M sys L N n j c b * ‖u.ofLp b‖ := by
    intro a c
    have h1 := norm_wNK_le_sum_wM (sys := sys) hL a c
    calc ‖u.ofLp a‖ * ‖(Y2N sys L p₀ N n u).ofLp c‖ * ‖wNK sys L N a c‖ ≤
        ‖u.ofLp a‖ * (∑ b, ‖u.ofLp b‖ * ∑ j, y2M sys L N n j c b) * ∑ j', wM sys L N j' a c :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hv c) (norm_nonneg _)) h1 (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _)
              (Finset.sum_nonneg fun j _ => y2M_nonneg hL j c b)))
      _ = ∑ j', ∑ j, ∑ b, ‖u.ofLp a‖ * wM sys L N j' a c * y2M sys L N n j c b * ‖u.ofLp b‖ := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
  refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => hpt a c).trans (le_of_eq ?_)
  exact sum4_comm (fun a c j' j => ∑ b, ‖u.ofLp a‖ * wM sys L N j' a c *
    y2M sys L N n j c b * ‖u.ofLp b‖)

omit [Fintype ν] in
lemma cXw_ge_one (hL : 0 < L) : 1 ≤ cXw sys L := by
  unfold cXw
  have : 0 ≤ 2 * mmax sys / gF L ^ 2 := by have := one_le_mmax sys; have := gF_pos hL; positivity
  linarith

omit [Fintype ν] in
lemma one_add_Xall_le (hL : 0 < L) (q : Cfg eta N) :
    1 + Xall q ≤ cXw sys L * (1 + Asym sys L N q) := by
  have h2 := Xall_le_Asym (sys := sys) hL q
  have hA0 := FSGalerkin.Asym_nonneg sys L N q
  unfold cXw
  have : 0 ≤ 2 * mmax sys / gF L ^ 2 := by have := one_le_mmax sys; have := gF_pos hL; positivity
  nlinarith

omit [Fintype ν] in
/-- The weight of the cross bound: `(1+|ξ|²)(1+|ζ|²)^{1/2} ≤ 2√2 c_X^{3/2} (1+A)^{3/2}`. -/
lemma cross_weight_le (hL : 0 < L) {Aξ Aζ : Finset (Fin eta)} (hcξ : Aξ.card ≤ 2)
    (hcζ : Aζ.card ≤ 2) (q : Cfg eta N) :
    (1 + FSLattice.lsq (regSum Aξ (cidx N q))) * Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N q)))
      ≤ 2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) *
        ((1 + Asym sys L N q) * Real.sqrt (1 + Asym sys L N q)) := by
  have hX := one_add_Xall_le (sys := sys) hL q
  have hX0 := Xall_nonneg q
  have hA0 := FSGalerkin.Asym_nonneg sys L N q
  have hc1 := cXw_ge_one (sys := sys) hL
  have h1 : 1 + FSLattice.lsq (regSum Aξ (cidx N q)) ≤ 2 * (cXw sys L * (1 + Asym sys L N q)) := by
    have := lsq_regSum_le_Xall Aξ hcξ q; linarith
  have h2 : Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N q))) ≤
      Real.sqrt 2 * (Real.sqrt (cXw sys L) * Real.sqrt (1 + Asym sys L N q)) := by
    rw [← Real.sqrt_mul (by linarith), ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    have := lsq_regSum_le_Xall Aζ hcζ q
    nlinarith
  calc (1 + FSLattice.lsq (regSum Aξ (cidx N q))) *
        Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N q))) ≤
      2 * (cXw sys L * (1 + Asym sys L N q)) *
        (Real.sqrt 2 * (Real.sqrt (cXw sys L) * Real.sqrt (1 + Asym sys L N q))) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

omit [Fintype ν] in
/-- The bulk-end weight: `|Π_j|² (1+|ξ|²)(1+|ζ|²)^{1/2} ≤ 4√2 c_X^{5/2} (1+A)^{5/2}`. -/
lemma cross_weight_pi_le (hL : 0 < L) {Aξ Aζ : Finset (Fin eta)} (hcξ : Aξ.card ≤ 2)
    (hcζ : Aζ.card ≤ 2) (j : Ch eta) (q : Cfg eta N) :
    piC j (cidx N q) ^ 2 * ((1 + FSLattice.lsq (regSum Aξ (cidx N q))) *
      Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N q)))) ≤
      4 * Real.sqrt 2 * (cXw sys L ^ 2 * Real.sqrt (cXw sys L)) *
        ((1 + Asym sys L N q) ^ 2 * Real.sqrt (1 + Asym sys L N q)) := by
  have hX := one_add_Xall_le (sys := sys) hL q
  have hX0 := Xall_nonneg q
  have hA0 := FSGalerkin.Asym_nonneg sys L N q
  have hc1 := cXw_ge_one (sys := sys) hL
  have hpi : piC j (cidx N q) ^ 2 ≤ 2 * (cXw sys L * (1 + Asym sys L N q)) := by
    have h1 := piC_le_sqrt j (cidx N q)
    have h2 := movS_le_Xall j q
    have h3 := pow_le_pow_left₀ (piC_nonneg j _) h1 2
    rw [Real.sq_sqrt (by have := movS_nonneg j (cidx N q); positivity)] at h3
    unfold movS at h2
    linarith
  have hw := cross_weight_le (sys := sys) hL hcξ hcζ q
  have hw0 : 0 ≤ (1 + FSLattice.lsq (regSum Aξ (cidx N q))) *
      Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N q))) := by
    have := FSLattice.lsq_nonneg (regSum Aξ (cidx N q)); positivity
  calc piC j (cidx N q) ^ 2 * ((1 + FSLattice.lsq (regSum Aξ (cidx N q))) *
        Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N q)))) ≤
      2 * (cXw sys L * (1 + Asym sys L N q)) *
        (2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) *
          ((1 + Asym sys L N q) * Real.sqrt (1 + Asym sys L N q))) :=
        mul_le_mul hpi hw hw0 (by positivity)
    _ = _ := by ring

/-- The cross constant `√(2√2 c_X^{3/2}) √(4√2 c_X^{5/2})`. -/
noncomputable def cWc (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  Real.sqrt (2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L))) *
    Real.sqrt (4 * Real.sqrt 2 * (cXw sys L ^ 2 * Real.sqrt (cXw sys L)))

omit [Fintype ν] in
lemma cWc_nonneg : 0 ≤ cWc sys L := by unfold cWc; positivity

open Classical in
/-- **The cross-channel term on a good state** (`j' ≠ j`). -/
theorem cross_good (hL : 0 < L) (hN : 1 ≤ N) {j' j : Ch eta} (hjj : j' ≠ j) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) :
    ∑ a, ∑ c, ∑ b, ‖u.ofLp a‖ * wM sys L N j' a c * y2M sys L N n j c b * ‖u.ofLp b‖ ≤
      chC sys L j' * y2C sys L n j * LamS (2 * N) ^ 2 * cWc sys L *
        (M * Real.sqrt (∑ b, (if InQ (n : ℝ) (cidx N b) then
          (1 + Asym sys L N b) ^ 2 * Real.sqrt (1 + Asym sys L N b) * ‖u.ofLp b‖ ^ 2 else 0))) := by
  classical
  have hC' := chC_nonneg sys hL j'
  have hY := y2C_nonneg (sys := sys) (n := n) hL j
  have hL0 := LamS_nonneg (2 * N)
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  have hwt : ∑ x, (1 + Asym sys L N x) ^ 2 * ‖u.ofLp x‖ ^ 2 ≤ M ^ 2 := by
    have h := hu.1
    have hW : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖ ≤ M := by
      linarith [norm_nonneg u]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hW 2
    rw [norm_sq_wt] at h2
    refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) h2
    rw [Real.rpow_one]
  cases j with
  | inl x =>
    -- one-body dressings vanish (`Π = 0`)
    have h0 : ∀ c b, y2M sys L N n (.inl x) c b = 0 := fun c b => by
      unfold y2M; split_ifs
      · simp [piC]
      · rfl
    have hR : 0 ≤ chC sys L j' * y2C sys L n (.inl x) * LamS (2 * N) ^ 2 * cWc sys L *
        (M * Real.sqrt (∑ b, (if InQ (n : ℝ) (cidx N b) then
          (1 + Asym sys L N b) ^ 2 * Real.sqrt (1 + Asym sys L N b) * ‖u.ofLp b‖ ^ 2 else 0))) := by
      have := cWc_nonneg (sys := sys) (L := L)
      positivity
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun b _ => by rw [h0, mul_zero, zero_mul])) hR
  | inr pr =>
    obtain ⟨Aξ, Aζ, ε₁, ε₂, hcξ, hcζ, hε₁, hε₂, hξj, hξj', hζj, hζj'⟩ := exists_coords hjj
    refine (cross_le hL hN hcξ hcζ hε₁ hε₂ hξj hξj' hζj hζj' u).trans ?_
    set K := chC sys L j' * y2C sys L n (.inr pr) * LamS (2 * N) ^ 2
    have hK : 0 ≤ K := by positivity
    have hA : ∑ a, (1 + FSLattice.lsq (regSum Aξ (cidx N a))) *
        Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N a))) * ‖u.ofLp a‖ ^ 2 ≤
        2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * M ^ 2 := by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hwt (by
        have := cXw_ge_one (sys := sys) hL; positivity))
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      have hw := cross_weight_le (sys := sys) hL hcξ hcζ a
      have hA0 := FSGalerkin.Asym_nonneg sys L N a
      have hs : Real.sqrt (1 + Asym sys L N a) ≤ 1 + Asym sys L N a := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      have h3 : (1 + Asym sys L N a) * Real.sqrt (1 + Asym sys L N a) ≤ (1 + Asym sys L N a) ^ 2 := by
        rw [sq]; exact mul_le_mul_of_nonneg_left hs (by linarith)
      have hc := cXw_ge_one (sys := sys) hL
      calc (1 + FSLattice.lsq (regSum Aξ (cidx N a))) *
            Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N a))) * ‖u.ofLp a‖ ^ 2 ≤
          2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) *
            ((1 + Asym sys L N a) * Real.sqrt (1 + Asym sys L N a)) * ‖u.ofLp a‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hw (sq_nonneg _)
        _ ≤ 2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) *
            (1 + Asym sys L N a) ^ 2 * ‖u.ofLp a‖ ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by ring
    have hB : ∑ b, (if InQ (n : ℝ) (cidx N b) then piC (.inr pr) (cidx N b) ^ 2 *
        ((1 + FSLattice.lsq (regSum Aξ (cidx N b))) *
          Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N b)))) * ‖u.ofLp b‖ ^ 2 else 0) ≤
        4 * Real.sqrt 2 * (cXw sys L ^ 2 * Real.sqrt (cXw sys L)) *
          ∑ b, (if InQ (n : ℝ) (cidx N b) then
            (1 + Asym sys L N b) ^ 2 * Real.sqrt (1 + Asym sys L N b) * ‖u.ofLp b‖ ^ 2 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun b _ => ?_
      split_ifs
      · have hw := cross_weight_pi_le (sys := sys) hL hcξ hcζ (.inr pr) b
        calc piC (.inr pr) (cidx N b) ^ 2 * ((1 + FSLattice.lsq (regSum Aξ (cidx N b))) *
              Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N b)))) * ‖u.ofLp b‖ ^ 2 ≤
            4 * Real.sqrt 2 * (cXw sys L ^ 2 * Real.sqrt (cXw sys L)) *
              ((1 + Asym sys L N b) ^ 2 * Real.sqrt (1 + Asym sys L N b)) * ‖u.ofLp b‖ ^ 2 :=
              mul_le_mul_of_nonneg_right hw (sq_nonneg _)
          _ = _ := by ring
      · simp
    have hsA := Real.sqrt_le_sqrt hA
    have hsB := Real.sqrt_le_sqrt hB
    rw [Real.sqrt_mul (by have := cXw_ge_one (sys := sys) hL; positivity), Real.sqrt_sq hM]
      at hsA
    rw [Real.sqrt_mul (by have := cXw_ge_one (sys := sys) hL; positivity)] at hsB
    calc K * (Real.sqrt (∑ a, (1 + FSLattice.lsq (regSum Aξ (cidx N a))) *
            Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N a))) * ‖u.ofLp a‖ ^ 2) *
          Real.sqrt (∑ b, (if InQ (n : ℝ) (cidx N b) then piC (.inr pr) (cidx N b) ^ 2 *
            ((1 + FSLattice.lsq (regSum Aξ (cidx N b))) *
              Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N b)))) * ‖u.ofLp b‖ ^ 2 else 0))) ≤
        K * ((Real.sqrt (2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L))) * M) *
          (Real.sqrt (4 * Real.sqrt 2 * (cXw sys L ^ 2 * Real.sqrt (cXw sys L))) *
            Real.sqrt (∑ b, (if InQ (n : ℝ) (cidx N b) then
              (1 + Asym sys L N b) ^ 2 * Real.sqrt (1 + Asym sys L N b) * ‖u.ofLp b‖ ^ 2
                else 0)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hsA hsB (Real.sqrt_nonneg _) (by positivity)) hK
      _ = _ := by unfold cWc; ring

/-- The constant of `[W, Y₂]`. -/
noncomputable def CWY (sys : CoulombSystem eta ν) (L : ℝ) (N n nd : ℕ) : ℝ :=
  (∑ j : Ch eta, chC sys L j * y2C sys L n j * LamS (2 * N) * (125 * (Nat.log 2 N + 2)) *
      (Real.sqrt 2 * cXw sys L ^ 2)) +
    (∑ j' : Ch eta, ∑ j : Ch eta, chC sys L j' * y2C sys L n j * LamS (2 * N) ^ 2 * cWc sys L) *
      Real.sqrt ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * (1 + 2 * eta * nd))

/-- **`[W, Y₂]` at the target rate**: `|Re⟨u, i[W, Y₂] u⟩| ≤ 2 C_{WY} M²` on a good box state. -/
theorem norm_comm_WY2_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) (hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * ((n : ℝ) / 4) ≤ 2 ^ nd) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) :
    |(⟪u, (Complex.I • (WN sys L N ∘ₗ Y2N sys L p₀ N n - Y2N sys L p₀ N n ∘ₗ WN sys L N)) u⟫_ℂ).re|
      ≤ 2 * (CWY sys L N n nd * M ^ 2) := by
  classical
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  have hwt : ∑ x, (1 + Asym sys L N x) ^ 2 * ‖u.ofLp x‖ ^ 2 ≤ M ^ 2 := by
    have h := hu.1
    have hW : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖ ≤ M := by
      linarith [norm_nonneg u]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hW 2
    rw [norm_sq_wt] at h2
    refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) h2
    rw [Real.rpow_one]
  -- `|Re⟨u, i[W,Y]u⟩| ≤ 2 |⟨u, W Y u⟩|`
  have hWs := WN_symm (sys := sys) (L := L) (N := N)
  have hYs := Y2N_symm (p₀ := p₀) (N := N) (n := n) hL H hKernel
  have hre : |(⟪u, (Complex.I • (WN sys L N ∘ₗ Y2N sys L p₀ N n -
      Y2N sys L p₀ N n ∘ₗ WN sys L N)) u⟫_ℂ).re| ≤ 2 * ‖⟪u, WN sys L N (Y2N sys L p₀ N n u)⟫_ℂ‖ := by
    rw [LinearMap.smul_apply, inner_smul_right, LinearMap.sub_apply, inner_sub_right,
      LinearMap.comp_apply, LinearMap.comp_apply]
    have e : ⟪u, Y2N sys L p₀ N n (WN sys L N u)⟫_ℂ = conj ⟪u, WN sys L N (Y2N sys L p₀ N n u)⟫_ℂ := by
      rw [← hYs u, inner_conj_symm, hWs]
    rw [e]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_conj]
    linarith
  refine hre.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  refine (norm_inner_W_Y2_le hL H hKernel hn u).trans ?_
  -- the critical moment
  have hcm := crit_moment_le hL hnd hu
  set CM := ∑ b, (if InQ (n : ℝ) (cidx N b) then
    (1 + Asym sys L N b) ^ 2 * Real.sqrt (1 + Asym sys L N b) * ‖u.ofLp b‖ ^ 2 else 0) with hCM
  have hsCM : Real.sqrt CM ≤ M * Real.sqrt ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * (1 + 2 * eta * nd)) := by
    have := Real.sqrt_le_sqrt hcm
    rw [show (1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd) =
      M ^ 2 * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * (1 + 2 * eta * nd)) by ring,
      Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM] at this
    exact this
  have hterm : ∀ j' j, ∑ a, ∑ c, ∑ b, ‖u.ofLp a‖ * wM sys L N j' a c * y2M sys L N n j c b *
      ‖u.ofLp b‖ ≤
      (if j' = j then chC sys L j * y2C sys L n j * LamS (2 * N) * (125 * (Nat.log 2 N + 2)) *
        (Real.sqrt 2 * cXw sys L ^ 2) * M ^ 2 else 0) +
      chC sys L j' * y2C sys L n j * LamS (2 * N) ^ 2 * cWc sys L *
        (M * (M * Real.sqrt ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * (1 + 2 * eta * nd)))) := by
    intro j' j
    have hC' := chC_nonneg sys hL j'
    have hY := y2C_nonneg (sys := sys) (n := n) hL j
    have hL0 := LamS_nonneg (2 * N)
    have hcw := cWc_nonneg (sys := sys) (L := L)
    by_cases hjj : j' = j
    · rw [if_pos hjj]
      subst hjj
      have hs := same_pair_le (sys := sys) (n := n) hL hN j' u
      have hpos : 0 ≤ chC sys L j' * y2C sys L n j' * LamS (2 * N) ^ 2 * cWc sys L *
          (M * (M * Real.sqrt ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * (1 + 2 * eta * nd)))) := by
        positivity
      have hs' : chC sys L j' * y2C sys L n j' * LamS (2 * N) * (125 * (Nat.log 2 N + 2)) *
          (Real.sqrt 2 * cXw sys L ^ 2) * ∑ q, (1 + Asym sys L N q) ^ 2 * ‖u.ofLp q‖ ^ 2 ≤
          chC sys L j' * y2C sys L n j' * LamS (2 * N) * (125 * (Nat.log 2 N + 2)) *
            (Real.sqrt 2 * cXw sys L ^ 2) * M ^ 2 :=
        mul_le_mul_of_nonneg_left hwt (by positivity)
      linarith
    · rw [if_neg hjj, zero_add]
      refine (cross_good (n := n) hL hN hjj hu).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsCM hM
  refine (Finset.sum_le_sum fun j' _ => Finset.sum_le_sum fun j _ => hterm j' j).trans
    (le_of_eq ?_)
  simp only [Finset.sum_add_distrib]
  have e1 : ∑ j' : Ch eta, ∑ j : Ch eta, (if j' = j then chC sys L j * y2C sys L n j *
      LamS (2 * N) * (125 * (Nat.log 2 N + 2)) * (Real.sqrt 2 * cXw sys L ^ 2) * M ^ 2 else 0) =
      ∑ j : Ch eta, chC sys L j * y2C sys L n j * LamS (2 * N) * (125 * (Nat.log 2 N + 2)) *
        (Real.sqrt 2 * cXw sys L ^ 2) * M ^ 2 := by
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  rw [e1]
  unfold CWY
  rw [add_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Assembly

end FSFlux
