import PlaneWave.FluxBox.CommutatorSamePair

/-!
# Flux route, stage 2, part 19: the commutator `[W, Y₂]`, the cross-channel part

For channels `j' ≠ j` (`W` on `j'`, `Y₂` on `j`), the composite `a ← c ← b` (`c` one hop of `j` from `b`,
`a` one hop of `j'` from `c`) is controlled in two **independent lattice coordinates**:

* `ξ = Σ_{c ∈ A_ξ} k_c`, moved by `j` (`ξ(τ_j(τ)) = ε₁ τ`) and not by `j'`;
* `ζ = Σ_{c ∈ A_ζ} k_c`, moved by `j'` (`ζ(τ_{j'}(σ)) = ε₂ σ`) and not by `j`
  (`exists_coords`: a register moved by one channel only, or `k_p + k_s` when `j'` is a one-body
  channel on a register of the pair `j = (p, s)`).

**The weighted Schur bound** (`cross_le`) with the product weight `h = (1 + |ξ|²)⁻¹ (1 + |ζ|²)^{-1/2}`:
every row and column sum of the composite factorizes into one-hop sums, and each one-hop sum is
decoupled by `a² b ≤ (2/3) a³ + (1/3) b³` into the two radial sums `Σ |x|⁻³` and `Σ (1+|x|²)^{-3/2}`
over the box (`sum_dec1`, `sum_dec2`, both `≤ Λ_{2N}`):

  `Σ_{a,c,b} |u_a| w_{j'}(a,c) y2M_j(c,b) |u_b| ≤ c_{j'} C_j Λ_{2N}²
      (Σ_a (1+|ξ|²)(1+|ζ|²)^{1/2} |u_a|²)^{1/2} (Σ_{b ∈ Q} |Π_j|² (1+|ξ|²)(1+|ζ|²)^{1/2} |u_b|²)^{1/2}`.

The Π weight sits on the bulk end, where the critical moment applies (`PlaneWave.FluxBox.CommutatorTargetRate`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Register coordinates -/

section Coords

/-- The total momentum of a set of registers. -/
def regSum (A : Finset (Fin eta)) (k : Cf eta) : Lattice3 := ∑ c ∈ A, k c

lemma regSum_add (A : Finset (Fin eta)) (k k' : Cf eta) :
    regSum A (k + k') = regSum A k + regSum A k' := by
  unfold regSum
  rw [← Finset.sum_add_distrib]
  rfl

lemma regSum_coord (A : Finset (Fin eta)) (k : Cf eta) (i : Fin 3) :
    ((regSum A k i : ℤ) : ℝ) = ∑ c ∈ A, ((k c i : ℤ) : ℝ) := by
  unfold regSum
  rw [Finset.sum_apply]
  push_cast
  rfl

lemma lsq_regSum_le (A : Finset (Fin eta)) (hA : A.card ≤ 2) (k : Cf eta) :
    FSLattice.lsq (regSum A k) ≤ 2 * ∑ c ∈ A, FSLattice.lsq (k c) := by
  have hi : ∀ i : Fin 3, ((regSum A k i : ℤ) : ℝ) ^ 2 ≤ 2 * ∑ c ∈ A, ((k c i : ℤ) : ℝ) ^ 2 := by
    intro i
    rw [regSum_coord]
    have h := sq_sum_le_card_mul_sum_sq (s := A) (f := fun c => ((k c i : ℤ) : ℝ))
    have hc : (A.card : ℝ) ≤ 2 := by exact_mod_cast hA
    have h0 : 0 ≤ ∑ c ∈ A, ((k c i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc (∑ c ∈ A, ((k c i : ℤ) : ℝ)) ^ 2 ≤ (A.card : ℝ) * ∑ c ∈ A, ((k c i : ℤ) : ℝ) ^ 2 := h
      _ ≤ 2 * ∑ c ∈ A, ((k c i : ℤ) : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hc h0
  have e : ∑ c ∈ A, FSLattice.lsq (k c) = ∑ c ∈ A, ((k c 0 : ℤ) : ℝ) ^ 2 +
      ∑ c ∈ A, ((k c 1 : ℤ) : ℝ) ^ 2 + ∑ c ∈ A, ((k c 2 : ℤ) : ℝ) ^ 2 := by
    unfold FSLattice.lsq
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [e]
  unfold FSLattice.lsq
  linarith [hi 0, hi 1, hi 2]

lemma lsq_regSum_le_Xall {N : ℕ} (A : Finset (Fin eta)) (hA : A.card ≤ 2) (q : Cfg eta N) :
    FSLattice.lsq (regSum A (cidx N q)) ≤ 2 * Xall q := by
  refine (lsq_regSum_le A hA _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  unfold Xall
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun c _ _ => FSLattice.lsq_nonneg _)

lemma lsq_regSum_box {N : ℕ} (A : Finset (Fin eta)) (hA : A.card ≤ 2) (q : Cfg eta N) :
    FSLattice.lsq (regSum A (cidx N q)) ≤ 3 * ((2 * N : ℕ) : ℝ) ^ 2 := by
  refine (lsq_regSum_le A hA _).trans ?_
  have h1 : ∑ c ∈ A, FSLattice.lsq (cidx N q c) ≤ ∑ _c ∈ A, 3 * (N : ℝ) ^ 2 :=
    Finset.sum_le_sum fun c _ => lsq_cidx_le q c
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have hc : (A.card : ℝ) ≤ 2 := by exact_mod_cast hA
  have h2 : (A.card : ℝ) * (3 * (N : ℝ) ^ 2) ≤ 2 * (3 * (N : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  push_cast
  nlinarith

lemma card_moved_le (j : Ch eta) : (moved j).card ≤ 2 := by
  cases j with
  | inl a => simp [moved]
  | inr pr => exact Finset.card_le_two

lemma card_moved_pair (pr : FiniteElectronPair eta) : (moved (.inr pr : Ch eta)).card = 2 := by
  have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
  simp only [moved]
  exact Finset.card_pair hne

/-- A moved register sees the transfer with a fixed sign. -/
lemma tr_single_coord (j : Ch eta) {x : Fin eta} (hx : x ∈ moved j) :
    ∃ ε : ℤ, ε ≠ 0 ∧ ∀ τ : Lattice3, tr j τ x = ε • τ := by
  cases j with
  | inl a =>
    simp only [moved, Finset.mem_singleton] at hx
    subst hx
    exact ⟨1, one_ne_zero, fun τ => by simp [tr]⟩
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    simp only [moved, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, one_ne_zero, fun τ => by simp [tr, Pi.single_eq_of_ne hne]⟩
    · exact ⟨-1, by norm_num, fun τ => by simp [tr, Pi.single_eq_of_ne hne.symm]⟩

/-- **The independent coordinates** of a cross-channel composite (`j' ≠ j = (p, s)`). -/
lemma exists_coords {j' : Ch eta} {pr : FiniteElectronPair eta} (hjj : j' ≠ .inr pr) :
    ∃ (Aξ Aζ : Finset (Fin eta)) (ε₁ ε₂ : ℤ), Aξ.card ≤ 2 ∧ Aζ.card ≤ 2 ∧ ε₁ ≠ 0 ∧ ε₂ ≠ 0 ∧
      (∀ τ, regSum Aξ (tr (.inr pr) τ) = ε₁ • τ) ∧ (∀ σ, regSum Aξ (tr j' σ) = 0) ∧
      (∀ τ, regSum Aζ (tr (.inr pr) τ) = 0) ∧ (∀ σ, regSum Aζ (tr j' σ) = ε₂ • σ) := by
  classical
  have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
  -- the ξ register
  obtain ⟨x, hxj, hxj'⟩ : ∃ x ∈ moved (.inr pr : Ch eta), x ∉ moved j' := by
    by_contra h
    push Not at h
    apply hjj
    apply moved_inj
    symm
    apply Finset.eq_of_subset_of_card_le (fun x hx => h x hx)
    rw [card_moved_pair]
    exact card_moved_le j'
  obtain ⟨ε₁, hε₁, hx⟩ := tr_single_coord (.inr pr) hxj
  have hξ1 : ∀ τ, regSum {x} (tr (.inr pr) τ) = ε₁ • τ := fun τ => by
    simp only [regSum, Finset.sum_singleton]; exact hx τ
  have hξ2 : ∀ σ, regSum {x} (tr j' σ) = 0 := fun σ => by
    simp only [regSum, Finset.sum_singleton]; exact tr_apply_not_moved j' σ hxj'
  by_cases hz : ∃ z ∈ moved j', z ∉ moved (.inr pr : Ch eta)
  · obtain ⟨z, hzj', hzj⟩ := hz
    obtain ⟨ε₂, hε₂, hzc⟩ := tr_single_coord j' hzj'
    refine ⟨{x}, {z}, ε₁, ε₂, by simp, by simp, hε₁, hε₂, hξ1, hξ2, fun τ => ?_, fun σ => ?_⟩
    · simp only [regSum, Finset.sum_singleton]; exact tr_apply_not_moved _ τ hzj
    · simp only [regSum, Finset.sum_singleton]; exact hzc σ
  · push Not at hz
    cases j' with
    | inr pr' =>
      exfalso
      apply hjj
      apply moved_inj
      apply Finset.eq_of_subset_of_card_le (fun z hz' => hz z hz')
      rw [card_moved_pair, card_moved_pair]
    | inl t =>
      have ht : t ∈ moved (.inr pr : Ch eta) := hz t (by simp [moved])
      refine ⟨{x}, moved (.inr pr), ε₁, 1, by simp, card_moved_le _, hε₁, one_ne_zero, hξ1, hξ2,
        fun τ => ?_, fun σ => ?_⟩
      · simp only [regSum, moved]
        rw [Finset.sum_pair hne]
        simp [tr, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
      · simp only [regSum, moved]
        rw [Finset.sum_pair hne]
        simp only [moved, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl
        · simp [tr, Pi.single_eq_of_ne hne.symm]
        · simp [tr, Pi.single_eq_of_ne hne]

end Coords

/-! ## The decoupled one-hop sums -/

section Dec

omit [Fintype ν] in
lemma inv_sqrt_cube {l : ℝ} (hl : 0 ≤ l) :
    (1 / Real.sqrt (1 + l)) ^ 3 = ((1 + l) * Real.sqrt (1 + l))⁻¹ := by
  have hs : 0 < Real.sqrt (1 + l) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt (1 + l) ^ 2 = 1 + l := Real.sq_sqrt (by linarith)
  have e : (1 + l) * Real.sqrt (1 + l) = Real.sqrt (1 + l) ^ 3 := by
    calc (1 + l) * Real.sqrt (1 + l) = Real.sqrt (1 + l) ^ 2 * Real.sqrt (1 + l) := by rw [hs2]
      _ = Real.sqrt (1 + l) ^ 3 := by ring
  rw [e, div_pow, one_pow, one_div]

omit [Fintype ν] in
lemma inv_sqrt_sq {l : ℝ} (hl : 0 ≤ l) : (1 / Real.sqrt (1 + l)) ^ 2 = 1 / (1 + l) := by
  rw [div_pow, Real.sq_sqrt (by linarith), one_pow]

omit [Fintype ν] in
lemma LamS_ge (m : ℕ) : 125 * ((Nat.log 2 m : ℝ) + 2) ≤ LamS m := by
  unfold LamS
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
    rwa [Real.sqrt_one] at this
  have h0 : (0 : ℝ) ≤ 125 * ((Nat.log 2 m : ℝ) + 2) := by positivity
  nlinarith

omit [Fintype ν] in
/-- `Σ_{i ∈ T} |τ_i|⁻¹ (1 + |ξ_i|²)⁻¹ ≤ Λ_m` over injective images. -/
lemma sum_dec1 {ι : Type*} (T : Finset ι) (τ ξ : ι → Lattice3) (hτ : Set.InjOn τ T)
    (hξ : Set.InjOn ξ T) {m : ℕ} (hm : 1 ≤ m) (h0 : ∀ i ∈ T, τ i ≠ 0)
    (hτb : ∀ i ∈ T, FSLattice.lsq (τ i) ≤ 3 * (m : ℝ) ^ 2)
    (hξb : ∀ i ∈ T, FSLattice.lsq (ξ i) ≤ 3 * (m : ℝ) ^ 2) :
    ∑ i ∈ T, 1 / FSChannel.rho (τ i) * (1 / (1 + FSLattice.lsq (ξ i))) ≤ LamS m := by
  have hpt : ∀ i ∈ T, 1 / FSChannel.rho (τ i) * (1 / (1 + FSLattice.lsq (ξ i))) ≤
      1 / 3 * (1 / FSChannel.rho (τ i) ^ 3) + 2 / 3 * (w32 (ξ i))⁻¹ := by
    intro i _
    have hl := FSLattice.lsq_nonneg (ξ i)
    have key := amgm_sq_mul_le (a := 1 / Real.sqrt (1 + FSLattice.lsq (ξ i)))
      (b := 1 / FSChannel.rho (τ i)) (by positivity)
      (div_nonneg zero_le_one (FSChannel.rho_nonneg _))
    rw [inv_sqrt_sq hl, inv_sqrt_cube hl, div_pow, one_pow] at key
    unfold w32
    linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := sum_inv_rho_cube_image_le T τ hτ hm h0 hτb
  have h2 := sum_inv_w32_image_le T ξ hξ hm hξb
  have h3 := LamS_ge m
  linarith

omit [Fintype ν] in
/-- `Σ_{i ∈ T} |σ_i|⁻² (1 + |ζ_i|²)^{-1/2} ≤ Λ_m` over injective images. -/
lemma sum_dec2 {ι : Type*} (T : Finset ι) (σ ζ : ι → Lattice3) (hσ : Set.InjOn σ T)
    (hζ : Set.InjOn ζ T) {m : ℕ} (hm : 1 ≤ m) (h0 : ∀ i ∈ T, σ i ≠ 0)
    (hσb : ∀ i ∈ T, FSLattice.lsq (σ i) ≤ 3 * (m : ℝ) ^ 2)
    (hζb : ∀ i ∈ T, FSLattice.lsq (ζ i) ≤ 3 * (m : ℝ) ^ 2) :
    ∑ i ∈ T, 1 / FSLattice.lsq (σ i) * (1 / Real.sqrt (1 + FSLattice.lsq (ζ i))) ≤ LamS m := by
  have hpt : ∀ i ∈ T, 1 / FSLattice.lsq (σ i) * (1 / Real.sqrt (1 + FSLattice.lsq (ζ i))) ≤
      2 / 3 * (1 / FSChannel.rho (σ i) ^ 3) + 1 / 3 * (w32 (ζ i))⁻¹ := by
    intro i _
    have hl := FSLattice.lsq_nonneg (ζ i)
    have key := amgm_sq_mul_le (a := 1 / FSChannel.rho (σ i))
      (b := 1 / Real.sqrt (1 + FSLattice.lsq (ζ i)))
      (div_nonneg zero_le_one (FSChannel.rho_nonneg _)) (by positivity)
    rw [inv_sqrt_cube hl, div_pow, div_pow, one_pow, one_pow, FSChannel.rho_sq] at key
    unfold w32
    linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := sum_inv_rho_cube_image_le T σ hσ hm h0 hσb
  have h2 := sum_inv_w32_image_le T ζ hζ hm hζb
  have h3 := LamS_ge m
  linarith

end Dec

/-! ## The cross-channel Schur bound -/

section Cross

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

variable (sys L N n) in
open Classical in
/-- The dressing majorant without its pair momentum. -/
noncomputable def ypM (j : Ch eta) (c b : Cfg eta N) : ℝ :=
  if OnCh j (cidx N c) (cidx N b) ∧ c ≠ b ∧ InQ (n : ℝ) (cidx N c) ∧ InQ (n : ℝ) (cidx N b) then
    y2C sys L n j / FSChannel.rho (chT N j c b)
  else 0

lemma ypM_nonneg (hL : 0 < L) (j : Ch eta) (c b : Cfg eta N) : 0 ≤ ypM sys L N n j c b := by
  unfold ypM
  split_ifs
  · exact div_nonneg (y2C_nonneg hL j) (FSChannel.rho_nonneg _)
  · exact le_rfl

lemma y2M_eq_ypM (j : Ch eta) (c b : Cfg eta N) :
    y2M sys L N n j c b = ypM sys L N n j c b * piC j (cidx N b) := by
  unfold y2M ypM
  split_ifs
  · ring
  · ring

omit [Fintype ν] in
/-- On a hop the transfer is not zero. -/
lemma chT_ne_zero {j : Ch eta} {q p : Cfg eta N} (h : OnCh j (cidx N q) (cidx N p)) (hne : q ≠ p) :
    chT N j q p ≠ 0 := by
  intro h0
  have := one_le_lsq_chT h hne
  rw [h0] at this
  exact absurd this (by norm_num [FSLattice.lsq])

omit [Fintype ν] in
/-- The output side of a hop is determined by the transfer. -/
lemma chT_injOn' (j : Ch eta) (q : Cfg eta N) :
    Set.InjOn (fun p => chT N j q p) {p | OnCh j (cidx N q) (cidx N p)} := by
  intro p hp p' hp' h
  have h1 : OnCh j (cidx N p) (cidx N q) := onCh_symm hp
  have h2 : OnCh j (cidx N p') (cidx N q) := onCh_symm hp'
  apply chT_injOn j q h1 h2
  have h' : chT N j q p = chT N j q p' := h
  show chT N j p q = chT N j p' q
  unfold chT at h' ⊢
  have : cidx N p (lead j) = cidx N p' (lead j) := by
    have := congrArg (fun x => cidx N q (lead j) - x) h'
    simp only [sub_sub_cancel] at this
    exact this
  rw [this]

omit [Fintype ν] in
lemma smul_injective_of_ne {ε : ℤ} (hε : ε ≠ 0) : Function.Injective fun τ : Lattice3 => ε • τ := by
  intro τ τ' h
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hε this

omit [Fintype ν] in
/-- On a hop, a coordinate changes by its action on the transfer. -/
lemma regSum_onCh {j : Ch eta} {A : Finset (Fin eta)} {q p : Cfg eta N}
    (h : OnCh j (cidx N q) (cidx N p)) :
    regSum A (cidx N q) = regSum A (cidx N p) + regSum A (tr j (chT N j q p)) := by
  have e : cidx N q = cidx N p + tr j (chT N j q p) := h
  rw [e, regSum_add]

open Classical in
/-- **The cross-channel Schur bound** (independent coordinates `ξ`, `ζ`). -/
theorem cross_le (hL : 0 < L) (hN : 1 ≤ N) {j' j : Ch eta} {Aξ Aζ : Finset (Fin eta)} {ε₁ ε₂ : ℤ}
    (hcξ : Aξ.card ≤ 2) (hcζ : Aζ.card ≤ 2) (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0)
    (hξj : ∀ τ, regSum Aξ (tr j τ) = ε₁ • τ) (hξj' : ∀ σ, regSum Aξ (tr j' σ) = 0)
    (hζj : ∀ τ, regSum Aζ (tr j τ) = 0) (hζj' : ∀ σ, regSum Aζ (tr j' σ) = ε₂ • σ)
    (u : En eta N) :
    ∑ a, ∑ c, ∑ b, ‖u.ofLp a‖ * wM sys L N j' a c * y2M sys L N n j c b * ‖u.ofLp b‖ ≤
      chC sys L j' * y2C sys L n j * LamS (2 * N) ^ 2 *
        (Real.sqrt (∑ a, (1 + FSLattice.lsq (regSum Aξ (cidx N a))) *
            Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N a))) * ‖u.ofLp a‖ ^ 2) *
          Real.sqrt (∑ b, (if InQ (n : ℝ) (cidx N b) then piC j (cidx N b) ^ 2 *
            ((1 + FSLattice.lsq (regSum Aξ (cidx N b))) *
              Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N b)))) * ‖u.ofLp b‖ ^ 2 else 0))) := by
  classical
  have h2N : 1 ≤ 2 * N := by omega
  set ξ : Cfg eta N → Lattice3 := fun q => regSum Aξ (cidx N q) with hξdef
  set ζ : Cfg eta N → Lattice3 := fun q => regSum Aζ (cidx N q) with hζdef
  set X : Cfg eta N → ℝ := fun q => 1 + FSLattice.lsq (ξ q) with hXdef
  set Z : Cfg eta N → ℝ := fun q => Real.sqrt (1 + FSLattice.lsq (ζ q)) with hZdef
  have hX : ∀ q, 0 < X q := fun q => by
    simp only [hXdef]; have := FSLattice.lsq_nonneg (ξ q); linarith
  have hZ : ∀ q, 0 < Z q := fun q => by
    simp only [hZdef]; exact Real.sqrt_pos.mpr (by have := FSLattice.lsq_nonneg (ζ q); linarith)
  set h : Cfg eta N → ℝ := fun q => 1 / (X q * Z q) with hhdef
  have hh : ∀ q, 0 < h q := fun q => by simp only [hhdef]; have := hX q; have := hZ q; positivity
  -- relations along the hops
  have R1 : ∀ a c, OnCh j' (cidx N a) (cidx N c) → ξ a = ξ c := by
    intro a c hac
    simp only [hξdef]
    rw [regSum_onCh hac, hξj', add_zero]
  have R2 : ∀ c b, OnCh j (cidx N c) (cidx N b) → ζ c = ζ b := by
    intro c b hcb
    simp only [hζdef]
    rw [regSum_onCh hcb, hζj, add_zero]
  have R3 : ∀ c b, OnCh j (cidx N c) (cidx N b) → ξ c = ξ b + ε₁ • chT N j c b := by
    intro c b hcb
    simp only [hξdef]
    rw [regSum_onCh hcb, hξj]
  have R4 : ∀ a c, OnCh j' (cidx N a) (cidx N c) → ζ a = ζ c + ε₂ • chT N j' a c := by
    intro a c hac
    simp only [hζdef]
    rw [regSum_onCh hac, hζj']
  have hξb : ∀ q, FSLattice.lsq (ξ q) ≤ 3 * ((2 * N : ℕ) : ℝ) ^ 2 := fun q => lsq_regSum_box Aξ hcξ q
  have hζb : ∀ q, FSLattice.lsq (ζ q) ≤ 3 * ((2 * N : ℕ) : ℝ) ^ 2 := fun q => lsq_regSum_box Aζ hcζ q
  have hC' := chC_nonneg sys hL j'
  have hY := y2C_nonneg (sys := sys) (n := n) hL j
  -- the four one-hop sums
  have Y0 : ∀ c, ∑ b, ypM sys L N n j c b * (1 / X b) ≤ y2C sys L n j * LamS (2 * N) := by
    intro c
    set T := Finset.univ.filter (fun b : Cfg eta N => OnCh j (cidx N c) (cidx N b) ∧ c ≠ b ∧
      InQ (n : ℝ) (cidx N c) ∧ InQ (n : ℝ) (cidx N b)) with hT
    have e : ∑ b, ypM sys L N n j c b * (1 / X b) = y2C sys L n j *
        ∑ b ∈ T, 1 / FSChannel.rho (chT N j c b) * (1 / (1 + FSLattice.lsq (ξ b))) := by
      rw [Finset.mul_sum, hT, Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold ypM
      split_ifs
      · simp only [hXdef]; ring
      · ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hY
    have hτinj : Set.InjOn (fun b => chT N j c b) T := fun b hb b' hb' hbb =>
      chT_injOn' j c (Finset.mem_filter.mp hb).2.1 (Finset.mem_filter.mp hb').2.1 hbb
    apply sum_dec1 T (fun b => chT N j c b) ξ hτinj _ h2N
    · intro b hb; exact chT_ne_zero (Finset.mem_filter.mp hb).2.1 (Finset.mem_filter.mp hb).2.2.1
    · intro b _; exact lsq_chT_box2 j c b
    · intro b _; exact hξb b
    · intro b hb b' hb' hbb
      apply hτinj hb hb'
      have e1 := R3 c b (Finset.mem_filter.mp hb).2.1
      have e2 := R3 c b' (Finset.mem_filter.mp hb').2.1
      have : ε₁ • chT N j c b = ε₁ • chT N j c b' := by
        have hbb' : ξ b = ξ b' := hbb
        rw [hbb'] at e1
        exact add_left_cancel (e1.symm.trans e2)
      exact smul_injective_of_ne hε₁ this
  have Y0' : ∀ b, ∑ c, ypM sys L N n j c b * (1 / X c) ≤ y2C sys L n j * LamS (2 * N) := by
    intro b
    set T := Finset.univ.filter (fun c : Cfg eta N => OnCh j (cidx N c) (cidx N b) ∧ c ≠ b ∧
      InQ (n : ℝ) (cidx N c) ∧ InQ (n : ℝ) (cidx N b)) with hT
    have e : ∑ c, ypM sys L N n j c b * (1 / X c) = y2C sys L n j *
        ∑ c ∈ T, 1 / FSChannel.rho (chT N j c b) * (1 / (1 + FSLattice.lsq (ξ c))) := by
      rw [Finset.mul_sum, hT, Finset.sum_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      unfold ypM
      split_ifs
      · simp only [hXdef]; ring
      · ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hY
    have hτinj : Set.InjOn (fun c => chT N j c b) T := fun c hc c' hc' hcc =>
      chT_injOn j b (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp hc').2.1 hcc
    apply sum_dec1 T (fun c => chT N j c b) ξ hτinj _ h2N
    · intro c hc; exact chT_ne_zero (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp hc).2.2.1
    · intro c _; exact lsq_chT_box2 j c b
    · intro c _; exact hξb c
    · intro c hc c' hc' hcc
      apply hτinj hc hc'
      have e1 := R3 c b (Finset.mem_filter.mp hc).2.1
      have e2 := R3 c' b (Finset.mem_filter.mp hc').2.1
      have hcc' : ξ c = ξ c' := hcc
      rw [hcc'] at e1
      exact smul_injective_of_ne hε₁ (add_left_cancel (e1.symm.trans e2))
  have W0 : ∀ a, ∑ c, wM sys L N j' a c * (1 / Z c) ≤ chC sys L j' * LamS (2 * N) := by
    intro a
    set T := Finset.univ.filter (fun c : Cfg eta N => OnCh j' (cidx N a) (cidx N c) ∧ a ≠ c) with hT
    have e : ∑ c, wM sys L N j' a c * (1 / Z c) = chC sys L j' *
        ∑ c ∈ T, 1 / FSLattice.lsq (chT N j' a c) *
          (1 / Real.sqrt (1 + FSLattice.lsq (ζ c))) := by
      rw [Finset.mul_sum, hT, Finset.sum_filter]
      refine Finset.sum_congr rfl fun c _ => ?_
      unfold wM
      split_ifs
      · simp only [hZdef]; ring
      · ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hC'
    have hσinj : Set.InjOn (fun c => chT N j' a c) T := fun c hc c' hc' hcc =>
      chT_injOn' j' a (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp hc').2.1 hcc
    apply sum_dec2 T (fun c => chT N j' a c) ζ hσinj _ h2N
    · intro c hc; exact chT_ne_zero (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp hc).2.2
    · intro c _; exact lsq_chT_box2 j' a c
    · intro c _; exact hζb c
    · intro c hc c' hc' hcc
      apply hσinj hc hc'
      have e1 := R4 a c (Finset.mem_filter.mp hc).2.1
      have e2 := R4 a c' (Finset.mem_filter.mp hc').2.1
      have hcc' : ζ c = ζ c' := hcc
      rw [hcc'] at e1
      have : ε₂ • chT N j' a c = ε₂ • chT N j' a c' := add_left_cancel (e1.symm.trans e2)
      exact smul_injective_of_ne hε₂ this
  have W0' : ∀ c, ∑ a, wM sys L N j' a c * (1 / Z a) ≤ chC sys L j' * LamS (2 * N) := by
    intro c
    set T := Finset.univ.filter (fun a : Cfg eta N => OnCh j' (cidx N a) (cidx N c) ∧ a ≠ c) with hT
    have e : ∑ a, wM sys L N j' a c * (1 / Z a) = chC sys L j' *
        ∑ a ∈ T, 1 / FSLattice.lsq (chT N j' a c) *
          (1 / Real.sqrt (1 + FSLattice.lsq (ζ a))) := by
      rw [Finset.mul_sum, hT, Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      unfold wM
      split_ifs
      · simp only [hZdef]; ring
      · ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hC'
    have hσinj : Set.InjOn (fun a => chT N j' a c) T := fun a ha a' ha' haa =>
      chT_injOn j' c (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha').2.1 haa
    apply sum_dec2 T (fun a => chT N j' a c) ζ hσinj _ h2N
    · intro a ha; exact chT_ne_zero (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
    · intro a _; exact lsq_chT_box2 j' a c
    · intro a _; exact hζb a
    · intro a ha a' ha' haa
      apply hσinj ha ha'
      have e1 := R4 a c (Finset.mem_filter.mp ha).2.1
      have e2 := R4 a' c (Finset.mem_filter.mp ha').2.1
      have haa' : ζ a = ζ a' := haa
      rw [haa'] at e1
      exact smul_injective_of_ne hε₂ (add_left_cancel (e1.symm.trans e2))
  -- the composite kernel and its weighted sums
  set K : Cfg eta N → Cfg eta N → ℝ := fun a b => ∑ c, wM sys L N j' a c * ypM sys L N n j c b
    with hKdef
  have hK0 : ∀ a b, 0 ≤ K a b := fun a b =>
    Finset.sum_nonneg fun c _ => mul_nonneg (wM_nonneg hL j' a c) (ypM_nonneg hL j c b)
  set K₀ := chC sys L j' * y2C sys L n j * LamS (2 * N) ^ 2 with hK₀
  have hL0 := LamS_nonneg (2 * N)
  have C3 : ∀ a, ∑ b, K a b * h b ≤ K₀ := by
    intro a
    have e : ∑ b, K a b * h b = ∑ c, wM sys L N j' a c * (1 / Z c) *
        ∑ b, ypM sys L N n j c b * (1 / X b) := by
      simp only [hKdef, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hy : ypM sys L N n j c b = 0
      · rw [hy]; ring
      have hcb : OnCh j (cidx N c) (cidx N b) := by
        unfold ypM at hy; split_ifs at hy with hh
        · exact hh.1
        · exact absurd rfl hy
      have hZ' : Z b = Z c := by simp only [hZdef]; rw [R2 c b hcb]
      simp only [hhdef]
      rw [hZ']
      have := hX b; have := hZ c
      field_simp
    rw [e]
    calc ∑ c, wM sys L N j' a c * (1 / Z c) * ∑ b, ypM sys L N n j c b * (1 / X b) ≤
        ∑ c, wM sys L N j' a c * (1 / Z c) * (y2C sys L n j * LamS (2 * N)) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (Y0 c)
            (mul_nonneg (wM_nonneg hL j' a c) (by have := hZ c; positivity))
      _ = (∑ c, wM sys L N j' a c * (1 / Z c)) * (y2C sys L n j * LamS (2 * N)) := by
          rw [Finset.sum_mul]
      _ ≤ chC sys L j' * LamS (2 * N) * (y2C sys L n j * LamS (2 * N)) :=
          mul_le_mul_of_nonneg_right (W0 a) (by positivity)
      _ = K₀ := by rw [hK₀]; ring
  have C4 : ∀ b, ∑ a, K a b * h a ≤ K₀ := by
    intro b
    have e : ∑ a, K a b * h a = ∑ c, ypM sys L N n j c b * (1 / X c) *
        ∑ a, wM sys L N j' a c * (1 / Z a) := by
      simp only [hKdef, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hw : wM sys L N j' a c = 0
      · rw [hw]; ring
      have hac : OnCh j' (cidx N a) (cidx N c) := by
        unfold wM at hw; split_ifs at hw with hh
        · exact hh.1
        · exact absurd rfl hw
      have hX' : X a = X c := by simp only [hXdef]; rw [R1 a c hac]
      simp only [hhdef]
      rw [hX']
      have := hX c; have := hZ a
      field_simp
    rw [e]
    calc ∑ c, ypM sys L N n j c b * (1 / X c) * ∑ a, wM sys L N j' a c * (1 / Z a) ≤
        ∑ c, ypM sys L N n j c b * (1 / X c) * (chC sys L j' * LamS (2 * N)) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (W0' c)
            (mul_nonneg (ypM_nonneg hL j c b) (by have := hX c; positivity))
      _ = (∑ c, ypM sys L N n j c b * (1 / X c)) * (chC sys L j' * LamS (2 * N)) := by
          rw [Finset.sum_mul]
      _ ≤ y2C sys L n j * LamS (2 * N) * (chC sys L j' * LamS (2 * N)) :=
          mul_le_mul_of_nonneg_right (Y0' b) (by positivity)
      _ = K₀ := by rw [hK₀]; ring
  -- the vectors
  set x : Cfg eta N → ℝ := fun a => ‖u.ofLp a‖ with hxdef
  set y : Cfg eta N → ℝ := fun b => if InQ (n : ℝ) (cidx N b) then piC j (cidx N b) * ‖u.ofLp b‖
    else 0 with hydef
  -- the left side as a form of `K`
  have hlhs : ∑ a, ∑ c, ∑ b, ‖u.ofLp a‖ * wM sys L N j' a c * y2M sys L N n j c b * ‖u.ofLp b‖ =
      ∑ a, ∑ b, x a * y b * K a b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hKdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [y2M_eq_ypM]
    by_cases hb : InQ (n : ℝ) (cidx N b)
    · simp only [hxdef, hydef, if_pos hb]; ring
    · have : ypM sys L N n j c b = 0 := by unfold ypM; rw [if_neg (fun hh => hb hh.2.2.2)]
      simp only [hxdef, hydef, if_neg hb, this]; ring
  rw [hlhs]
  -- Cauchy–Schwarz with the weight
  set K' : Cfg eta N → Cfg eta N → ℝ := fun a b => K a b * h a * h b with hK'def
  have hK'0 : ∀ a b, 0 ≤ K' a b := fun a b => by
    simp only [hK'def]; have := hK0 a b; have := hh a; have := hh b; positivity
  have hcs := sum_kernel_cs K' hK'0 (fun a => x a / h a) (fun b => y b / h b)
  have e1 : ∑ a, ∑ b, x a / h a * (y b / h b) * K' a b = ∑ a, ∑ b, x a * y b * K a b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hK'def]
    have := hh a; have := hh b
    field_simp
  have e2 : ∑ a, ∑ b, (x a / h a) ^ 2 * K' a b = ∑ a, x a ^ 2 / h a * ∑ b, K a b * h b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hK'def]
    have := hh a
    field_simp
  have e3 : ∑ a, ∑ b, (y b / h b) ^ 2 * K' a b = ∑ b, y b ^ 2 / h b * ∑ a, K a b * h a := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hK'def]
    have := hh b
    field_simp
  rw [e1, e2, e3] at hcs
  have hA : ∑ a, x a ^ 2 / h a * ∑ b, K a b * h b ≤ K₀ * ∑ a, x a ^ 2 / h a := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [mul_comm K₀]
    exact mul_le_mul_of_nonneg_left (C3 a) (by have := hh a; positivity)
  have hB : ∑ b, y b ^ 2 / h b * ∑ a, K a b * h a ≤ K₀ * ∑ b, y b ^ 2 / h b := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [mul_comm K₀]
    exact mul_le_mul_of_nonneg_left (C4 b) (by have := hh b; positivity)
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  have hxs : ∑ a, x a ^ 2 / h a = ∑ a, (1 + FSLattice.lsq (regSum Aξ (cidx N a))) *
      Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N a))) * ‖u.ofLp a‖ ^ 2 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hxdef, hhdef, hXdef, hZdef, hξdef, hζdef]
    field_simp
  have hys : ∑ b, y b ^ 2 / h b = ∑ b, (if InQ (n : ℝ) (cidx N b) then piC j (cidx N b) ^ 2 *
      ((1 + FSLattice.lsq (regSum Aξ (cidx N b))) *
        Real.sqrt (1 + FSLattice.lsq (regSum Aζ (cidx N b)))) * ‖u.ofLp b‖ ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hydef, hhdef, hXdef, hZdef, hξdef, hζdef]
    split_ifs
    · field_simp
    · simp
  calc ∑ a, ∑ b, x a * y b * K a b ≤
      Real.sqrt (∑ a, x a ^ 2 / h a * ∑ b, K a b * h b) *
        Real.sqrt (∑ b, y b ^ 2 / h b * ∑ a, K a b * h a) := hcs
    _ ≤ Real.sqrt (K₀ * ∑ a, x a ^ 2 / h a) * Real.sqrt (K₀ * ∑ b, y b ^ 2 / h b) :=
        mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = K₀ * (Real.sqrt (∑ a, x a ^ 2 / h a) * Real.sqrt (∑ b, y b ^ 2 / h b)) := by
        rw [Real.sqrt_mul hK₀0, Real.sqrt_mul hK₀0,
          show Real.sqrt K₀ * Real.sqrt (∑ a, x a ^ 2 / h a) * (Real.sqrt K₀ *
            Real.sqrt (∑ b, y b ^ 2 / h b)) = (Real.sqrt K₀ * Real.sqrt K₀) *
              (Real.sqrt (∑ a, x a ^ 2 / h a) * Real.sqrt (∑ b, y b ^ 2 / h b)) by ring,
          Real.mul_self_sqrt hK₀0]
    _ = _ := by rw [hxs, hys, hK₀]

end Cross

end FSFlux
