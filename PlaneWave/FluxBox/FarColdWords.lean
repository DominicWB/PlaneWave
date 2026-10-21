import PlaneWave.FluxBox.ThirdDressing

/-!
# Flux route, stage 3, part 22: the words of the far–cold kernel

The far–cold kernel `b^{FC}` of `PlaneWave.FluxBox.ThirdDressing` is split by the channels of its two hops
(`j₁` the first hop, from the cold input; `j₂` the second, to the far output):

  `b^{FC} = Σ_{j₂} Σ_{j₁} b_{j₂ j₁}`                                          (`bfcK_eq_sum`),
  `b_{j₂ j₁} = fl_{j₂ j₁} + com_{j₂ j₁}`,
  `fl_{j₂ j₁} = λ_{j₁} R W_{j₂} P W_{j₁} Π_C + (λ_{j₂} - λ_{j₁}) F' W_{j₂} R W_{j₁} Π_C`,
  `com_{j₂ j₁} = F W_{j₂} R Y_{j₁} Π_C - R Y_{j₂} W_{j₁} Π_C - F' Y_{j₂} R W_{j₁} Π_C`.

On the diagonal the `F'` chains cancel: `fl_{jj} = λ_j R W_j P W_j Π_C` (`flK_diag`), the
**same-channel flat word** `ss_j`. The rest of `b^{FC}` is `r^{FC} = b^{FC} - Σ_j ss_j`
(`rK_eq`: the com words and the off-diagonal flat words).

* the far–cold dressing of a kernel (`ytK`): `-κ(q,p)/(E(q) - E(p))` on `F × C`;
  `y₃ = ỹ + ỹ*` with `ỹ = ytK b^{FC}` (`y3K_eq`), and `ytK` is linear;
* `re_comm_eq`: for symmetric `W, Y`, `Re⟨u, i[W, Y] u⟩ = -2 Im⟨W u, Y u⟩`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Bilinearity of the chain kernels -/

section Bilin

variable {X : Type*} [Fintype X] (S₁ S₂ S₃ : X → Prop)

omit [Fintype ν] in
lemma chainK_sum_left {ι : Type*} (s : Finset ι) (κ₂ : ι → X → X → ℂ) (κ₁ : X → X → ℂ) (q p : X) :
    chainK S₁ S₂ S₃ (fun a b => ∑ i ∈ s, κ₂ i a b) κ₁ q p =
      ∑ i ∈ s, chainK S₁ S₂ S₃ (κ₂ i) κ₁ q p := by
  classical
  unfold chainK
  split_ifs
  · simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  · simp

omit [Fintype ν] in
lemma chainK_sum_right {ι : Type*} (s : Finset ι) (κ₂ : X → X → ℂ) (κ₁ : ι → X → X → ℂ) (q p : X) :
    chainK S₁ S₂ S₃ κ₂ (fun a b => ∑ i ∈ s, κ₁ i a b) q p =
      ∑ i ∈ s, chainK S₁ S₂ S₃ κ₂ (κ₁ i) q p := by
  classical
  unfold chainK
  split_ifs
  · have e : ∀ d, κ₂ q d * (if S₂ d then ∑ i ∈ s, κ₁ i d p else 0) =
        ∑ i ∈ s, κ₂ q d * (if S₂ d then κ₁ i d p else 0) := by
      intro d
      split_ifs
      · rw [Finset.mul_sum]
      · simp
    simp_rw [e]
    exact Finset.sum_comm
  · simp

omit [Fintype ν] in
lemma chainK_smul_left (c : ℂ) (κ₂ κ₁ : X → X → ℂ) (q p : X) :
    chainK S₁ S₂ S₃ (fun a b => c * κ₂ a b) κ₁ q p = c * chainK S₁ S₂ S₃ κ₂ κ₁ q p := by
  classical
  unfold chainK
  split_ifs
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  · simp

omit [Fintype ν] in
lemma chainK_smul_right (c : ℂ) (κ₂ κ₁ : X → X → ℂ) (q p : X) :
    chainK S₁ S₂ S₃ κ₂ (fun a b => c * κ₁ a b) q p = c * chainK S₁ S₂ S₃ κ₂ κ₁ q p := by
  classical
  unfold chainK
  split_ifs
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> ring
  · simp

omit [Fintype ν] in
lemma chainK'_sum_left {ι : Type*} (s : Finset ι) (κ₂ : ι → X → X → ℂ) (κ₁ : X → X → ℂ) (q p : X) :
    chainK' S₁ S₃ (fun a b => ∑ i ∈ s, κ₂ i a b) κ₁ q p =
      ∑ i ∈ s, chainK' S₁ S₃ (κ₂ i) κ₁ q p := by
  classical
  unfold chainK'
  split_ifs
  · simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  · simp

omit [Fintype ν] in
lemma chainK'_sum_right {ι : Type*} (s : Finset ι) (κ₂ : X → X → ℂ) (κ₁ : ι → X → X → ℂ) (q p : X) :
    chainK' S₁ S₃ κ₂ (fun a b => ∑ i ∈ s, κ₁ i a b) q p =
      ∑ i ∈ s, chainK' S₁ S₃ κ₂ (κ₁ i) q p := by
  classical
  unfold chainK'
  split_ifs
  · simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  · simp

end Bilin

/-! ## The channel parts -/

section Parts

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N : ℕ)

/-- The Coulomb kernel on channel `j`. -/
noncomputable def wj (j : Ch eta) (q p : Cfg eta N) : ℂ := chPart N j (wNK sys L N) q p

/-- The com dressing on channel `j`. -/
noncomputable def yj (j : Ch eta) (q p : Cfg eta N) : ℂ :=
  ycKc (sys := sys) (L := L) (p₀ := p₀) (N := N) j q p

variable {sys L p₀ N}

lemma wNK_eq_fun (hL : 0 < L) : wNK sys L N = fun a b => ∑ j, wj sys L N j a b := by
  funext a b
  exact wNK_eq_sum_chPart hL a b

lemma whK_eq_fun : whK sys L p₀ N = fun a b => ∑ j, (lamC sys p₀ j : ℂ) * wj sys L N j a b := rfl

lemma ycK_eq_fun (hL : 0 < L) : ycK sys L p₀ N = fun a b => ∑ j, yj sys L p₀ N j a b := by
  funext a b
  exact ycK_eq_sum hL a b

end Parts

/-! ## The words -/

section Words

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ)

/-- The flat word `fl_{j₂ j₁} = λ_{j₁} R W_{j₂} P W_{j₁} Π_C + (λ_{j₂} - λ_{j₁}) F' W_{j₂} R W_{j₁} Π_C`. -/
noncomputable def flK (j₂ j₁ : Ch eta) (q p : Cfg eta N) : ℂ :=
  (lamC sys p₀ j₁ : ℂ) *
      chainK (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun d => InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (wj sys L N j₁) q p +
    ((lamC sys p₀ j₂ : ℂ) - (lamC sys p₀ j₁ : ℂ)) *
      chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) q p

/-- The com word `com_{j₂ j₁} = F W_{j₂} R Y_{j₁} Π_C - R Y_{j₂} W_{j₁} Π_C - F' Y_{j₂} R W_{j₁} Π_C`. -/
noncomputable def comK (j₂ j₁ : Ch eta) (q p : Cfg eta N) : ℂ :=
  chainK (fun q => ¬ InQ (n : ℝ) (cidx N q)) (fun d => ¬ InP (n : ℝ) (cidx N d))
      (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (yj sys L p₀ N j₁) q p -
    chainK' (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
      (yj sys L p₀ N j₂) (wj sys L N j₁) q p -
    chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
      (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
      (yj sys L p₀ N j₂) (wj sys L N j₁) q p

/-- The same-channel flat word `ss_j = λ_j R W_j P W_j Π_C`. -/
noncomputable def ssK (j : Ch eta) (q p : Cfg eta N) : ℂ :=
  (lamC sys p₀ j : ℂ) *
    chainK (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun d => InP (n : ℝ) (cidx N d))
      (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j) (wj sys L N j) q p

/-- The rest of the far–cold kernel: `r^{FC} = b^{FC} - Σ_j ss_j`. -/
noncomputable def rK (q p : Cfg eta N) : ℂ :=
  bfcK sys L p₀ N n q p - ∑ j, ssK sys L p₀ N n j q p

variable {sys L p₀ N n}

/-- **The word decomposition** `b^{FC} = Σ_{j₂} Σ_{j₁} (fl_{j₂ j₁} + com_{j₂ j₁})`. -/
theorem bfcK_eq_sum (hL : 0 < L) (q p : Cfg eta N) :
    bfcK sys L p₀ N n q p =
      ∑ j₁, ∑ j₂, (flK sys L p₀ N n j₂ j₁ q p + comK sys L p₀ N n j₂ j₁ q p) := by
  unfold bfcK
  rw [whK_eq_fun, wNK_eq_fun hL, ycK_eq_fun hL]
  simp only [chainK_sum_left, chainK_sum_right, chainK_smul_left, chainK_smul_right,
    chainK'_sum_left, chainK'_sum_right]
  unfold flK comK
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, Finset.mul_sum]
  ring

/-- **On the diagonal the `F'` chains cancel**: `fl_{jj} = ss_j`. -/
lemma flK_diag (j : Ch eta) (q p : Cfg eta N) :
    flK sys L p₀ N n j j q p = ssK sys L p₀ N n j q p := by
  unfold flK ssK
  ring

/-- **The rest of the far–cold kernel**: the com words and the off-diagonal flat words. -/
theorem rK_eq (hL : 0 < L) (q p : Cfg eta N) :
    rK sys L p₀ N n q p =
      ∑ j₁, ∑ j₂, comK sys L p₀ N n j₂ j₁ q p +
        ∑ j₁, ∑ j₂, (if j₂ = j₁ then 0 else flK sys L p₀ N n j₂ j₁ q p) := by
  classical
  unfold rK
  rw [bfcK_eq_sum hL]
  simp only [Finset.sum_add_distrib]
  have e : ∀ j₁, ∑ j₂, flK sys L p₀ N n j₂ j₁ q p =
      ssK sys L p₀ N n j₁ q p + ∑ j₂, (if j₂ = j₁ then 0 else flK sys L p₀ N n j₂ j₁ q p) := by
    intro j₁
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₁), ← Finset.add_sum_erase _ _ (Finset.mem_univ j₁),
      if_pos rfl, flK_diag, zero_add]
    congr 1
    refine Finset.sum_congr rfl fun j₂ hj₂ => ?_
    rw [if_neg (Finset.ne_of_mem_erase hj₂)]
  simp only [e, Finset.sum_add_distrib]
  ring

end Words

/-! ## The far–cold dressing of a kernel -/

section Dress

variable (sys : CoulombSystem eta ν) (L : ℝ) (N n : ℕ)

open Classical in
/-- The far–cold dressing `-κ(q,p)/(E(q) - E(p))` on `F × C`. -/
noncomputable def ytK (κ : Cfg eta N → Cfg eta N → ℂ) (q p : Cfg eta N) : ℂ :=
  if ¬ InQ (n : ℝ) (cidx N q) ∧ InC (n : ℝ) (cst sys) (cidx N p) then
    -κ q p / ((Asym sys L N q - Asym sys L N p : ℝ) : ℂ) else 0

variable {sys L N n}

omit [Fintype ν] in
lemma ytK_add (κ κ' : Cfg eta N → Cfg eta N → ℂ) (q p : Cfg eta N) :
    ytK sys L N n (fun a b => κ a b + κ' a b) q p = ytK sys L N n κ q p + ytK sys L N n κ' q p := by
  unfold ytK
  split_ifs
  · ring
  · ring

omit [Fintype ν] in
lemma ytK_sub (κ κ' : Cfg eta N → Cfg eta N → ℂ) (q p : Cfg eta N) :
    ytK sys L N n (fun a b => κ a b - κ' a b) q p = ytK sys L N n κ q p - ytK sys L N n κ' q p := by
  unfold ytK
  split_ifs
  · ring
  · ring

omit [Fintype ν] in
lemma ytK_sum {ι : Type*} (s : Finset ι) (κ : ι → Cfg eta N → Cfg eta N → ℂ) (q p : Cfg eta N) :
    ytK sys L N n (fun a b => ∑ i ∈ s, κ i a b) q p = ∑ i ∈ s, ytK sys L N n (κ i) q p := by
  unfold ytK
  split_ifs
  · rw [← Finset.sum_neg_distrib, Finset.sum_div]
  · simp

omit [Fintype ν] in
lemma ytK_supp {κ : Cfg eta N → Cfg eta N → ℂ} {q p : Cfg eta N} (h : ytK sys L N n κ q p ≠ 0) :
    ¬ InQ (n : ℝ) (cidx N q) ∧ InC (n : ℝ) (cst sys) (cidx N p) := by
  unfold ytK at h
  by_contra hc
  exact h (if_neg hc)

/-- **The third dressing as `ỹ + ỹ*`**, `ỹ = ytK b^{FC}`. -/
theorem y3K_eq (hL : 0 < L) {p₀ : Fin eta}
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 1 ≤ n) (q p : Cfg eta N) :
    y3K sys L p₀ N n q p =
      ytK sys L N n (bfcK sys L p₀ N n) q p + conj (ytK sys L N n (bfcK sys L p₀ N n) p q) := by
  classical
  have hQC : ∀ {r : Cfg eta N}, InC (n : ℝ) (cst sys) (cidx N r) → InQ (n : ℝ) (cidx N r) :=
    fun h => inC_imp_inQ' h
  by_cases h1 : ¬ InQ (n : ℝ) (cidx N q) ∧ InC (n : ℝ) (cst sys) (cidx N p)
  · have h2 : ¬ (¬ InQ (n : ℝ) (cidx N p) ∧ InC (n : ℝ) (cst sys) (cidx N q)) :=
      fun h => h.1 (hQC h1.2)
    unfold ytK
    rw [if_pos h1, if_neg h2, map_zero, add_zero, y3K_far_cold hL H hKernel hn h1.1 h1.2]
  · by_cases h2 : ¬ InQ (n : ℝ) (cidx N p) ∧ InC (n : ℝ) (cst sys) (cidx N q)
    · unfold ytK
      rw [if_neg h1, if_pos h2, zero_add, y3K_conj p q, y3K_far_cold hL H hKernel hn h2.1 h2.2]
    · unfold ytK
      rw [if_neg h1, if_neg h2, map_zero, add_zero]
      by_contra h0
      rcases y3K_supp hL H hKernel h0 with h | h
      · exact h1 h
      · exact h2 ⟨h.2, h.1⟩

end Dress

/-! ## The commutator form -/

section CommForm

variable {X : Type*} [Fintype X]

omit [Fintype ν] in
/-- `Re⟨u, i[W, Y] u⟩ = -2 Im⟨W u, Y u⟩` for symmetric `W, Y`. -/
lemma re_comm_eq {W Y : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X} (hW : W.IsSymmetric)
    (hY : Y.IsSymmetric) (u : EuclideanSpace ℂ X) :
    (⟪u, (Complex.I • (W ∘ₗ Y - Y ∘ₗ W)) u⟫_ℂ).re = -2 * (⟪W u, Y u⟫_ℂ).im := by
  rw [LinearMap.smul_apply, inner_smul_right, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, inner_sub_right, ← hW u (Y u), ← hY u (W u), ← inner_conj_symm (Y u) (W u),
    mul_sub]
  exact re_I_sub _

end CommForm

end FSFlux
