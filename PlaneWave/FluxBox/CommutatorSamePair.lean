import PlaneWave.FluxBox.SecondDressing

/-!
# Flux route, stage 2, part 18: the commutator `[W, Y₂]`, the same-pair part

`Re⟨u, i[W, Y₂] u⟩ = -2 Im⟨W u, Y₂ u⟩`, and `|⟨u, W Y₂ u⟩| ≤ Σ_{a,c,b} |u_a| |w(a,c)| |y₂(c,b)| |u_b|`.
The potential is split by channels, `|w(a, c)| ≤ Σ_{j'} w_{j'}(a, c)`, `w_{j'} = 1{a on j' from c, a ≠ c}
c_{j'}/|σ|²` (`norm_wNK_le_sum_wM`), and the dressing by its majorant `y2M` (`PlaneWave.FluxBox.SecondDressing`).

* The lattice tools: `|ν|⁻³ ≤ 2√2 (1 + |ν|²)^{-3/2}` (`inv_rho_cube_le`), the sums over injective images
  of the box (`sum_inv_rho_cube_image_le`, `sum_inv_w32_image_le`: `≤ 2√2 · 125 (log₂ m + 2)` and
  `≤ 125 (log₂ m + 2)` for transfers with `|x|² ≤ 3 m²`), and the decoupling inequality
  `a² b ≤ (2/3) a³ + (1/3) b³` (`amgm_sq_mul_le`), which reduces every convolution sum of the round to
  these two radial sums (no dyadic decomposition of a convolution is needed).
* **The same-pair part** (`j' = j`): for `a, b` on the channel, `Σ_c w_j(a,c) y2M_j(c,b) ≤
  c_j C_j |Π_j(b)| Λ_N`, `Λ_N = 2√2 · 125 (log₂(2N) + 2)` (`sum_wM_y2M_same`), and the fibre trace bound
  on the box gives `Σ_{a,c,b} |u_a| w_j y2M_j |u_b| ≤ c_j C_j Λ_N 125 (log₂ N + 2) √2 c_X² Σ (1+A)² |u|²`
  (`same_pair_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Lattice tools -/

section Tools

omit [Fintype ν] in
/-- `|ν|⁻³ ≤ 2√2 (1 + |ν|²)^{-3/2}` for `ν ≠ 0`. -/
lemma inv_rho_cube_le {x : Lattice3} (hx : x ≠ 0) :
    1 / FSChannel.rho x ^ 3 ≤ 2 * Real.sqrt 2 * (w32 x)⁻¹ := by
  have hl : 1 ≤ FSLattice.lsq x := one_le_latticeNormSq hx
  have hρ : 0 < FSChannel.rho x := Real.sqrt_pos.mpr (by linarith)
  have hρ2 : FSChannel.rho x ^ 2 = FSLattice.lsq x := FSChannel.rho_sq x
  have hw : 0 < w32 x := w32_pos x
  have hkey : w32 x ≤ 2 * Real.sqrt 2 * FSChannel.rho x ^ 3 := by
    unfold w32
    have h1 : 1 + FSLattice.lsq x ≤ 2 * FSLattice.lsq x := by linarith
    have h2 : Real.sqrt (1 + FSLattice.lsq x) ≤ Real.sqrt 2 * FSChannel.rho x := by
      unfold FSChannel.rho
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt h1
    have h3 := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    calc (1 + FSLattice.lsq x) * Real.sqrt (1 + FSLattice.lsq x) ≤
        2 * FSLattice.lsq x * (Real.sqrt 2 * FSChannel.rho x) := h3
      _ = 2 * Real.sqrt 2 * FSChannel.rho x ^ 3 := by rw [← hρ2]; ring
  rw [show 2 * Real.sqrt 2 * (w32 x)⁻¹ = 2 * Real.sqrt 2 / w32 x by ring,
    div_le_div_iff₀ (by positivity) hw, one_mul]
  exact hkey

/-- The constant `Λ_m = 2√2 · 125 (log₂ m + 2)`. -/
noncomputable def LamS (m : ℕ) : ℝ := 2 * Real.sqrt 2 * (125 * (Nat.log 2 m + 2))

lemma LamS_nonneg (m : ℕ) : 0 ≤ LamS m := by unfold LamS; positivity

omit [Fintype ν] in
/-- `Σ (1 + |x|²)^{-3/2}` over an injective image of transfers with `|x|² ≤ 3 m²`. -/
lemma sum_inv_w32_image_le {ι : Type*} (F : Finset ι) (f : ι → Lattice3) (hf : Set.InjOn f F)
    {m : ℕ} (hm : 1 ≤ m) (hle : ∀ i ∈ F, FSLattice.lsq (f i) ≤ 3 * (m : ℝ) ^ 2) :
    ∑ i ∈ F, (w32 (f i))⁻¹ ≤ 125 * (Nat.log 2 m + 2) := by
  rw [← Finset.sum_image (f := fun x => (w32 x)⁻¹) hf]
  apply sum_box_inv32_le hm
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact hle i hi

omit [Fintype ν] in
/-- `Σ |x|⁻³` over an injective image of nonzero transfers with `|x|² ≤ 3 m²`. -/
lemma sum_inv_rho_cube_image_le {ι : Type*} (F : Finset ι) (f : ι → Lattice3) (hf : Set.InjOn f F)
    {m : ℕ} (hm : 1 ≤ m) (h0 : ∀ i ∈ F, f i ≠ 0)
    (hle : ∀ i ∈ F, FSLattice.lsq (f i) ≤ 3 * (m : ℝ) ^ 2) :
    ∑ i ∈ F, 1 / FSChannel.rho (f i) ^ 3 ≤ LamS m := by
  calc ∑ i ∈ F, 1 / FSChannel.rho (f i) ^ 3 ≤ ∑ i ∈ F, 2 * Real.sqrt 2 * (w32 (f i))⁻¹ :=
        Finset.sum_le_sum fun i hi => inv_rho_cube_le (h0 i hi)
    _ = 2 * Real.sqrt 2 * ∑ i ∈ F, (w32 (f i))⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.sqrt 2 * (125 * (Nat.log 2 m + 2)) :=
        mul_le_mul_of_nonneg_left (sum_inv_w32_image_le F f hf hm hle) (by positivity)
    _ = LamS m := rfl

omit [Fintype ν] in
/-- The decoupling inequality `a² b ≤ (2/3) a³ + (1/3) b³` (`a, b ≥ 0`). -/
lemma amgm_sq_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 * b ≤ 2 / 3 * a ^ 3 + 1 / 3 * b ^ 3 := by
  nlinarith [mul_nonneg (sq_nonneg (a - b)) (by positivity : 0 ≤ 2 * a + b)]

omit [Fintype ν] in
/-- Box transfers: `|θ|² ≤ 3 (2N)²`. -/
lemma lsq_chT_box2 {N : ℕ} (j : Ch eta) (q p : Cfg eta N) :
    FSLattice.lsq (chT N j q p) ≤ 3 * ((2 * N : ℕ) : ℝ) ^ 2 := by
  have hq : InP (N : ℝ) (cidx N q) := inP_of_mem_cube (finiteConfigLatticeIndex_mem_cube eta N q)
  have hp : InP (N : ℝ) (cidx N p) := inP_of_mem_cube (finiteConfigLatticeIndex_mem_cube eta N p)
  have hc : ∀ i, ((chT N j q p i : ℤ) : ℝ) ^ 2 ≤ ((2 * N : ℕ) : ℝ) ^ 2 := by
    intro i
    have h1 := hq (lead j) i
    have h2 := hp (lead j) i
    have e : ((chT N j q p i : ℤ) : ℝ) =
        ((cidx N q (lead j) i : ℤ) : ℝ) - ((cidx N p (lead j) i : ℤ) : ℝ) := by
      unfold chT; rw [Pi.sub_apply, Int.cast_sub]
    rw [e]
    have h3 : |((cidx N q (lead j) i : ℤ) : ℝ) - ((cidx N p (lead j) i : ℤ) : ℝ)| ≤ 2 * N := by
      have := abs_sub ((cidx N q (lead j) i : ℤ) : ℝ) ((cidx N p (lead j) i : ℤ) : ℝ)
      linarith
    have h4 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    rw [sq_abs] at h4
    push_cast
    linarith
  unfold FSLattice.lsq
  linarith [hc 0, hc 1, hc 2]

end Tools

/-! ## The channel split of the potential -/

section WSplit

variable (sys : CoulombSystem eta ν) (L : ℝ) (N : ℕ)

open Classical in
/-- The channel majorant of the potential: `w_j(a, c) = 1{a on j from c, a ≠ c} c_j/|σ|²`. -/
noncomputable def wM (j : Ch eta) (a c : Cfg eta N) : ℝ :=
  if OnCh j (cidx N a) (cidx N c) ∧ a ≠ c then chC sys L j / FSLattice.lsq (chT N j a c) else 0

variable {sys L N}

lemma wM_nonneg (hL : 0 < L) (j : Ch eta) (a c : Cfg eta N) : 0 ≤ wM sys L N j a c := by
  unfold wM
  split_ifs
  · exact div_nonneg (chC_nonneg sys hL j) (FSLattice.lsq_nonneg _)
  · exact le_rfl

/-- `|w(a, c)| ≤ Σ_j w_j(a, c)`. -/
lemma norm_wNK_le_sum_wM (hL : 0 < L) (a c : Cfg eta N) :
    ‖wNK sys L N a c‖ ≤ ∑ j, wM sys L N j a c := by
  classical
  rw [wNK_eq_sum_chPart hL a c]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  unfold chPart wM
  by_cases hj : OnCh j (cidx N a) (cidx N c)
  · rw [if_pos hj]
    by_cases hac : a = c
    · rw [hac, wNK_self hL c, norm_zero]
      exact le_of_eq (by rw [if_neg (fun h => h.2 rfl)])
    · rw [if_pos ⟨hj, hac⟩]
      exact norm_wNK_chan_le hL hj hac
  · rw [if_neg hj, norm_zero, if_neg (fun h => hj h.1)]

end WSplit

/-! ## The same-pair part -/

section SamePair

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

open Classical in
/-- **The same-pair composite**: for `a, b`,
`Σ_c w_j(a, c) y2M_j(c, b) ≤ 1{a on j from b} c_j C_j |Π_j(b)| Λ_{2N}`. -/
lemma sum_wM_y2M_same (hL : 0 < L) (hN : 1 ≤ N) (j : Ch eta) (a b : Cfg eta N) :
    ∑ c, wM sys L N j a c * y2M sys L N n j c b ≤
      (if OnCh j (cidx N a) (cidx N b) then
        chC sys L j * y2C sys L n j * piC j (cidx N b) * LamS (2 * N) else 0) := by
  classical
  have hC := chC_nonneg sys hL j
  have hY := y2C_nonneg (sys := sys) (n := n) hL j
  have hpi := piC_nonneg j (cidx N b)
  have h2N : 1 ≤ 2 * N := by omega
  -- the support
  have hsupp : ∀ c, wM sys L N j a c * y2M sys L N n j c b ≠ 0 →
      OnCh j (cidx N a) (cidx N c) ∧ a ≠ c ∧ OnCh j (cidx N c) (cidx N b) ∧ c ≠ b := by
    intro c h
    unfold wM y2M at h
    split_ifs at h with h1 h2
    · exact ⟨h1.1, h1.2, h2.1, h2.2.1⟩
    · simp at h
    · simp at h
    · simp at h
  by_cases hab : OnCh j (cidx N a) (cidx N b)
  swap
  · rw [if_neg hab]
    refine le_of_eq (Finset.sum_eq_zero fun c _ => ?_)
    by_contra h
    obtain ⟨h1, -, h2, -⟩ := hsupp c h
    exact hab (onCh_comp h1 h2)
  rw [if_pos hab]
  -- termwise decoupling
  have hpt : ∀ c, wM sys L N j a c * y2M sys L N n j c b ≤
      chC sys L j * y2C sys L n j * piC j (cidx N b) *
        (2 / 3 * (if OnCh j (cidx N a) (cidx N c) ∧ a ≠ c then
            1 / FSChannel.rho (chT N j a c) ^ 3 else 0) +
          1 / 3 * (if OnCh j (cidx N c) (cidx N b) ∧ c ≠ b then
            1 / FSChannel.rho (chT N j c b) ^ 3 else 0)) := by
    intro c
    by_cases h : wM sys L N j a c * y2M sys L N n j c b = 0
    · rw [h]
      apply mul_nonneg (by positivity)
      apply add_nonneg <;> apply mul_nonneg (by norm_num) <;> split_ifs <;>
        first | exact le_rfl | exact div_nonneg zero_le_one (pow_nonneg (FSChannel.rho_nonneg _) 3)
    obtain ⟨h1, h1', h2, h2'⟩ := hsupp c h
    have hQ : InQ (n : ℝ) (cidx N c) ∧ InQ (n : ℝ) (cidx N b) := by
      unfold y2M at h
      split_ifs at h with hh
      · exact ⟨hh.2.2.1, hh.2.2.2⟩
      · simp at h
    unfold wM y2M
    rw [if_pos ⟨h1, h1'⟩, if_pos ⟨h2, h2', hQ.1, hQ.2⟩, if_pos ⟨h1, h1'⟩, if_pos ⟨h2, h2'⟩]
    set s := FSChannel.rho (chT N j a c)
    set t := FSChannel.rho (chT N j c b)
    have hs2 : s ^ 2 = FSLattice.lsq (chT N j a c) := FSChannel.rho_sq _
    have hs1 : 1 ≤ s := by
      have hl := one_le_lsq_chT h1 h1'
      nlinarith [FSChannel.rho_nonneg (chT N j a c)]
    have ht1 : 1 ≤ t := by
      have hl := one_le_lsq_chT h2 h2'
      have := FSChannel.rho_sq (chT N j c b)
      nlinarith [FSChannel.rho_nonneg (chT N j c b)]
    have key := amgm_sq_mul_le (a := 1 / s) (b := 1 / t) (by positivity) (by positivity)
    rw [← hs2]
    calc chC sys L j / s ^ 2 * (y2C sys L n j * piC j (cidx N b) / t) =
        chC sys L j * y2C sys L n j * piC j (cidx N b) * ((1 / s) ^ 2 * (1 / t)) := by
          field_simp
      _ ≤ chC sys L j * y2C sys L n j * piC j (cidx N b) *
          (2 / 3 * (1 / s) ^ 3 + 1 / 3 * (1 / t) ^ 3) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum fun c _ => hpt c).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the two radial sums
  have hS1 : ∑ c, (if OnCh j (cidx N a) (cidx N c) ∧ a ≠ c then
      1 / FSChannel.rho (chT N j a c) ^ 3 else 0) ≤ LamS (2 * N) := by
    rw [← Finset.sum_filter]
    apply sum_inv_rho_cube_image_le _ _ _ h2N
    · intro c hc
      have hc' := (Finset.mem_filter.mp hc).2
      intro h0
      apply hc'.2
      apply finiteConfigLatticeIndex_injective eta N
      have e : finiteConfigLatticeIndex eta N a = cidx N c + tr j (chT N j a c) := hc'.1
      rw [e, h0]
      cases j with
      | inl x => simp [tr]
      | inr pr => simp [tr]
    · intro c _; exact lsq_chT_box2 j a c
    · intro c hc c' hc' h
      have h1 : OnCh j (cidx N c) (cidx N a) := onCh_symm (Finset.mem_filter.mp hc).2.1
      have h2 : OnCh j (cidx N c') (cidx N a) := onCh_symm (Finset.mem_filter.mp hc').2.1
      apply chT_injOn j a h1 h2
      have h' : chT N j a c = chT N j a c' := h
      show chT N j c a = chT N j c' a
      unfold chT at h' ⊢
      have : cidx N c (lead j) = cidx N c' (lead j) := by
        have := congrArg (fun x => cidx N a (lead j) - x) h'
        simp only [sub_sub_cancel] at this
        exact this
      rw [this]
  have hS2 : ∑ c, (if OnCh j (cidx N c) (cidx N b) ∧ c ≠ b then
      1 / FSChannel.rho (chT N j c b) ^ 3 else 0) ≤ LamS (2 * N) := by
    rw [← Finset.sum_filter]
    apply sum_inv_rho_cube_image_le _ _ _ h2N
    · intro c hc
      have hc' := (Finset.mem_filter.mp hc).2
      intro h0
      apply hc'.2
      apply finiteConfigLatticeIndex_injective eta N
      have e : finiteConfigLatticeIndex eta N c = cidx N b + tr j (chT N j c b) := hc'.1
      rw [e, h0]
      cases j with
      | inl x => simp [tr]
      | inr pr => simp [tr]
    · intro c _; exact lsq_chT_box2 j c b
    · intro c hc c' hc' h
      exact chT_injOn j b (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp hc').2.1 h
  have hL0 := LamS_nonneg (2 * N)
  linarith

/-- **The same-pair part of `W Y₂`**:
`Σ_{a,c,b} |u_a| w_j(a,c) y2M_j(c,b) |u_b| ≤ c_j C_j Λ_{2N} 125 (log₂ N + 2) √2 c_X² Σ (1+A)² |u|²`. -/
theorem same_pair_le (hL : 0 < L) (hN : 1 ≤ N) (j : Ch eta) (u : En eta N) :
    ∑ a, ∑ c, ∑ b, ‖u.ofLp a‖ * wM sys L N j a c * y2M sys L N n j c b * ‖u.ofLp b‖ ≤
      chC sys L j * y2C sys L n j * LamS (2 * N) * (125 * (Nat.log 2 N + 2)) *
        (Real.sqrt 2 * cXw sys L ^ 2) * ∑ q, (1 + Asym sys L N q) ^ 2 * ‖u.ofLp q‖ ^ 2 := by
  classical
  have hC := chC_nonneg sys hL j
  have hY := y2C_nonneg (sys := sys) (n := n) hL j
  have hL0 := LamS_nonneg (2 * N)
  set K := chC sys L j * y2C sys L n j * LamS (2 * N) with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 : ∀ a b, ∑ c, ‖u.ofLp a‖ * wM sys L N j a c * y2M sys L N n j c b * ‖u.ofLp b‖ ≤
      K * (if OnCh j (cidx N a) (cidx N b) then
        ‖u.ofLp a‖ * ‖u.ofLp b‖ * piC j (cidx N b) else 0) := by
    intro a b
    have e : ∑ c, ‖u.ofLp a‖ * wM sys L N j a c * y2M sys L N n j c b * ‖u.ofLp b‖ =
        ‖u.ofLp a‖ * ‖u.ofLp b‖ * ∑ c, wM sys L N j a c * y2M sys L N n j c b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e]
    have h := mul_le_mul_of_nonneg_left (sum_wM_y2M_same (sys := sys) (n := n) hL hN j a b)
      (by positivity : 0 ≤ ‖u.ofLp a‖ * ‖u.ofLp b‖)
    refine h.trans (le_of_eq ?_)
    split_ifs
    · rw [hK]; ring
    · ring
  have e2 : ∑ a, ∑ c, ∑ b, ‖u.ofLp a‖ * wM sys L N j a c * y2M sys L N n j c b * ‖u.ofLp b‖ =
      ∑ a, ∑ b, ∑ c, ‖u.ofLp a‖ * wM sys L N j a c * y2M sys L N n j c b * ‖u.ofLp b‖ :=
    Finset.sum_congr rfl fun a _ => Finset.sum_comm
  rw [e2]
  refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h1 a b).trans ?_
  simp_rw [← Finset.mul_sum]
  have htr := chan_trace_le hN j (fun q => ‖u.ofLp q‖) (fun q => piC j (cidx N q))
    (fun q => piC_nonneg j _) (fun q p h => piC_onCh h)
  have hW : ∑ q, wl j q * piC j (cidx N q) * ‖u.ofLp q‖ ^ 2 ≤
      Real.sqrt 2 * cXw sys L ^ 2 * ∑ q, (1 + Asym sys L N q) ^ 2 * ‖u.ofLp q‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have hw := wl_piC_le (sys := sys) hL j q
    calc wl j q * piC j (cidx N q) * ‖u.ofLp q‖ ^ 2 ≤
        Real.sqrt 2 * cXw sys L ^ 2 * (1 + Asym sys L N q) ^ 2 * ‖u.ofLp q‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hw (sq_nonneg _)
      _ = _ := by ring
  calc K * ∑ a, ∑ b, (if OnCh j (cidx N a) (cidx N b) then
        ‖u.ofLp a‖ * ‖u.ofLp b‖ * piC j (cidx N b) else 0) ≤
      K * (125 * (Nat.log 2 N + 2) * ∑ q, wl j q * piC j (cidx N q) * ‖u.ofLp q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left htr hK0
    _ ≤ K * (125 * (Nat.log 2 N + 2) * (Real.sqrt 2 * cXw sys L ^ 2 *
        ∑ q, (1 + Asym sys L N q) ^ 2 * ‖u.ofLp q‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW (by positivity)) hK0
    _ = _ := by ring

end SamePair

end FSFlux
