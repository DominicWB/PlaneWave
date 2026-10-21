import PlaneWave.FluxBox.CentreOfMassSplit

/-!
# Flux route, stage 2, part 3: lattice tools for the box

* `sum_tail_inv_sq_le`: `Σ_{ν ∈ S, |ν| > R} |ν|⁻⁴ ≤ 250/R` (`R ≥ 1`);
* translation invariance of the potential kernel (`potKernel_add_add`), so that the box kernels
  of `W_N` and `Ŵ_N` are convolution kernels: `wNK q p = wL (q - p)`, `whK q p = whL (q - p)`;
* **the box reflection identity** (`comm_conv_eq`): for convolution kernels on the box,
  `[κ_f, κ_{f'}](q, p) = Σ_{x ∈ B_N} h(x) - Σ_{x ∈ σ B_N} h(x)`, `h(x) = f(q - x) f'(x - p)`,
  `σ x = q + p - x` (on the whole lattice convolutions commute);
* **`norm_comm_conv_form_le`**: for an even majorant `M` of `f` and `f'`,
  `|⟨v, [κ_f, κ_{f'}] v⟩| ≤ 2 Σ_{y ∈ B_{3N} ∖ B_N} (Σ_q |v_q| M(q - y))²`;
* the box commutator `e_bd(v) = ⟨v, i[W_N, Ŵ_N] v⟩` and its bound (`abs_ebd_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSLattice

open Finset FSChannel

/-! ## The lattice tail `Σ |ν|⁻⁴` -/

/-- One dyadic Euclidean shell: `Σ_{ν ∈ S, lam < |ν| ≤ 2 lam} |ν|⁻⁴ ≤ 125 lam⁻¹` (`lam ≥ 1`). -/
lemma sum_shell_inv_sq_le (S : Finset L3) {lam : ℝ} (hlam : 1 ≤ lam) :
    ∑ ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lsq ν ^ 2 ≤
      125 / lam := by
  have hlam0 : 0 < lam := by linarith
  have hsub : S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2) ⊆
      (box ⌈2 * lam⌉₊).filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2) := by
    intro ν hν
    rw [mem_filter] at hν ⊢
    exact ⟨box_mono (Nat.floor_le_ceil _) (mem_box_floor_of_lsq_le (by linarith) hν.2.2), hν.2⟩
  have hcard : ((S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2)).card : ℝ) ≤
      125 * lam ^ 3 :=
    (Nat.cast_le.mpr (card_le_card hsub)).trans (card_euclid_shell_le hlam)
  calc ∑ ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lsq ν ^ 2
      ≤ ∑ _ν ∈ S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2), 1 / lam ^ 4 := by
        apply sum_le_sum
        intro ν hν
        rw [mem_filter] at hν
        have h1 : lam ^ 4 ≤ lsq ν ^ 2 := by
          rw [show lam ^ 4 = (lam ^ 2) ^ 2 by ring]
          exact pow_le_pow_left₀ (by positivity) hν.2.1.le 2
        exact one_div_le_one_div_of_le (by positivity) h1
    _ = (S.filter (fun ν => lam ^ 2 < lsq ν ∧ lsq ν ≤ (2 * lam) ^ 2)).card * (1 / lam ^ 4) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 125 * lam ^ 3 * (1 / lam ^ 4) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 125 / lam := by field_simp

/-- The dyadic shells `R < |ν| ≤ 2^J R`: `125 R⁻¹ + 250 (2R)⁻¹ ≤ 250 R⁻¹`. -/
lemma sum_dyadic_inv_sq_le (S : Finset L3) (J : ℕ) :
    ∀ R : ℝ, 1 ≤ R →
      ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * R) ^ 2), 1 / lsq ν ^ 2 ≤
        250 / R := by
  induction J with
  | zero =>
    intro R hR
    have hR0 : 0 < R := by linarith
    have : S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ 0 * R) ^ 2) = ∅ := by
      apply filter_false_of_mem
      intro ν _ h
      rw [pow_zero, one_mul] at h
      exact absurd h.2 (not_le.mpr h.1)
    rw [this, sum_empty]
    positivity
  | succ J ih =>
    intro R hR
    have hR0 : 0 < R := by linarith
    have h1 := sum_shell_inv_sq_le S hR
    have h2 := ih (2 * R) (by linarith)
    have e : (2 : ℝ) ^ (J + 1) * R = 2 ^ J * (2 * R) := by ring
    have hsplit :
        ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ (J + 1) * R) ^ 2), 1 / lsq ν ^ 2 ≤
          ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 * R) ^ 2), 1 / lsq ν ^ 2 +
            ∑ ν ∈ S.filter (fun ν => (2 * R) ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * (2 * R)) ^ 2),
              1 / lsq ν ^ 2 := by
      rw [sum_filter, sum_filter, sum_filter, ← sum_add_distrib, e]
      apply sum_le_sum
      intro ν _
      have hnn : 0 ≤ 1 / lsq ν ^ 2 := by have := lsq_nonneg ν; positivity
      by_cases hc1 : R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * (2 * R)) ^ 2
      · by_cases hc2 : lsq ν ≤ (2 * R) ^ 2
        · rw [if_pos hc1, if_pos ⟨hc1.1, hc2⟩]
          split_ifs <;> linarith
        · rw [if_pos hc1, if_neg (fun h => hc2 h.2), if_pos ⟨not_le.mp hc2, hc1.2⟩]
          linarith
      · rw [if_neg hc1]
        split_ifs <;> linarith
    calc _ ≤ _ := hsplit
      _ ≤ 125 / R + 250 / (2 * R) := add_le_add h1 h2
      _ = 250 / R := by field_simp; ring

/-- **Lattice tail sum.** `Σ_{ν ∈ S, |ν| > R} |ν|⁻⁴ ≤ 250 R⁻¹` for `R ≥ 1`. -/
theorem sum_tail_inv_sq_le (S : Finset L3) {R : ℝ} (hR : 1 ≤ R) :
    ∑ ν ∈ S.filter (fun ν => R ^ 2 < lsq ν), 1 / lsq ν ^ 2 ≤ 250 / R := by
  obtain ⟨N, hN⟩ := exists_box S
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, 3 * (N : ℝ) ^ 2 < 2 ^ J := pow_unbounded_of_one_lt _ (by norm_num)
  have hfilt : S.filter (fun ν => R ^ 2 < lsq ν) =
      S.filter (fun ν => R ^ 2 < lsq ν ∧ lsq ν ≤ (2 ^ J * R) ^ 2) := by
    apply filter_congr
    intro ν hν
    refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
    have h1 := lsq_le_of_mem_box (hN hν)
    have h2 : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    have h3 : (2 : ℝ) ^ J ≤ 2 ^ J * R := le_mul_of_one_le_right (by positivity) hR
    have h4 : (1 : ℝ) ≤ 2 ^ J * R := h2.trans h3
    have h5 : 2 ^ J * R ≤ (2 ^ J * R) ^ 2 := by nlinarith
    linarith
  rw [hfilt]
  exact sum_dyadic_inv_sq_le S J R hR

end FSLattice

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Translation invariance of the potential kernel -/

section Translation

variable (sys : CoulombSystem eta ν) (L : ℝ)

omit [Fintype ν] in
lemma latticeSub_add_add (a b c : Lattice3) : latticeSub (a + c) (b + c) = latticeSub a b := by
  funext i
  simp only [latticeSub_apply, Pi.add_apply]
  ring

omit [Fintype ν] in
lemma latticeCoulombKernel_add_add (C : ℝ) (a b c : Lattice3) :
    latticeCoulombKernel C (a + c) (b + c) = latticeCoulombKernel C a b := by
  unfold latticeCoulombKernel
  rw [latticeSub_add_add]

omit [Fintype ν] in
lemma latticeElectronNuclearKernel_add_add (data : FiniteBONuclearData ν) (gamma : ℝ) (ell : ν)
    (a b c : Lattice3) :
    latticeElectronNuclearKernel data gamma ell (a + c) (b + c) =
      latticeElectronNuclearKernel data gamma ell a b := by
  unfold latticeElectronNuclearKernel
  rw [latticeSub_add_add, latticeCoulombKernel_add_add]

omit [Fintype ν] in
lemma latticeReferenceConfigurationKernel_add_add (i : Fin eta)
    (kernel : Lattice3 → Lattice3 → ℂ) (hk : ∀ a b c, kernel (a + c) (b + c) = kernel a b)
    (q p s : Cf eta) :
    latticeReferenceConfigurationKernel i kernel (q + s) (p + s) =
      latticeReferenceConfigurationKernel i kernel q p := by
  classical
  unfold latticeReferenceConfigurationKernel
  have hc : (∀ k : Fin eta, k ≠ i → (q + s) k = (p + s) k) ↔ (∀ k : Fin eta, k ≠ i → q k = p k) := by
    simp only [Pi.add_apply, add_left_inj]
  by_cases h : ∀ k : Fin eta, k ≠ i → q k = p k
  · rw [if_pos (hc.mpr h), if_pos h, Pi.add_apply, Pi.add_apply, hk]
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h]

omit [Fintype ν] in
lemma latticeElectronPairConfigurationKernel_add_add (i j : Fin eta) (C : ℝ) (q p s : Cf eta) :
    latticeElectronPairConfigurationKernel i j C (q + s) (p + s) =
      latticeElectronPairConfigurationKernel i j C q p := by
  classical
  unfold latticeElectronPairConfigurationKernel
  have hc1 : (∀ k : Fin eta, k ≠ i → k ≠ j → (q + s) k = (p + s) k) ↔
      (∀ k : Fin eta, k ≠ i → k ≠ j → q k = p k) := by
    simp only [Pi.add_apply, add_left_inj]
  have hc2 : (q + s) i + (q + s) j = (p + s) i + (p + s) j ↔ q i + q j = p i + p j := by
    simp only [Pi.add_apply]
    rw [show q i + s i + (q j + s j) = (q i + q j) + (s i + s j) by abel,
      show p i + s i + (p j + s j) = (p i + p j) + (s i + s j) by abel, add_left_inj]
  by_cases h : (∀ k : Fin eta, k ≠ i → k ≠ j → q k = p k) ∧ q i + q j = p i + p j
  · rw [if_pos ⟨hc1.mpr h.1, hc2.mpr h.2⟩, if_pos h, Pi.add_apply, Pi.add_apply,
      latticeCoulombKernel_add_add]
  · rw [if_neg (fun h' => h ⟨hc1.mp h'.1, hc2.mp h'.2⟩), if_neg h]

/-- **Translation invariance of the potential kernel.** -/
lemma potKernel_add_add (q p s : Cf eta) : potKernel sys L (q + s) (p + s) = potKernel sys L q p := by
  unfold potKernel coulombLatticeNuclearKernel coulombLatticePairKernel
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun ell _ => ?_
    exact latticeReferenceConfigurationKernel_add_add i _
      (fun a b c => latticeElectronNuclearKernel_add_add _ _ ell a b c) q p s
  · refine Finset.sum_congr rfl fun pr _ => ?_
    rw [latticeElectronPairConfigurationKernel_add_add]

/-- The lattice potential as a function of the transfer. -/
noncomputable def wL (d : Cf eta) : ℂ := potKernel sys L d 0

lemma potKernel_eq_wL (q p : Cf eta) : potKernel sys L q p = wL sys L (q - p) := by
  unfold wL
  have := potKernel_add_add sys L (q - p) 0 p
  rw [sub_add_cancel, zero_add] at this
  exact this

omit [Fintype ν] in
lemma onCh_add_add_iff (j : Ch eta) (q p s : Cf eta) : OnCh j (q + s) (p + s) ↔ OnCh j q p := by
  unfold OnCh
  have e : (q + s) (lead j) - (p + s) (lead j) = q (lead j) - p (lead j) := by
    simp only [Pi.add_apply]; abel
  rw [e, show p + s + tr j (q (lead j) - p (lead j)) = (p + tr j (q (lead j) - p (lead j))) + s by
    abel, add_left_inj]

omit [Fintype ν] in
lemma onCh_iff_sub (j : Ch eta) (q p : Cf eta) : OnCh j q p ↔ OnCh j (q - p) 0 := by
  have := onCh_add_add_iff j (q - p) 0 p
  rw [sub_add_cancel, zero_add] at this
  exact this

end Translation

/-! ## Convolution kernels on the box and the reflection identity -/

section Reflection

variable {N : ℕ}

/-- A convolution kernel on the box: `κ_f(q, p) = f(q - p)`. -/
noncomputable def convK (N : ℕ) (f : Cf eta → ℂ) (q p : Cfg eta N) : ℂ := f (cidx N q - cidx N p)

omit [Fintype ν] in
lemma sum_cfg_eq_sum_cube (N : ℕ) {β : Type*} [AddCommMonoid β] (F : Cf eta → β) :
    ∑ r : Cfg eta N, F (cidx N r) = ∑ x ∈ fourierConfigCube eta N, F x := by
  classical
  unfold fourierConfigCube
  rw [Finset.sum_image]
  intro x _ y _ h
  exact finiteConfigLatticeIndex_injective eta N h

omit [Fintype ν] in
lemma kmul_convK (f f' : Cf eta → ℂ) (q p : Cfg eta N) :
    kmul N (convK N f) (convK N f') q p =
      ∑ x ∈ fourierConfigCube eta N, f (cidx N q - x) * f' (x - cidx N p) := by
  unfold kmul convK
  exact sum_cfg_eq_sum_cube N (fun x => f (cidx N q - x) * f' (x - cidx N p))

/-- The reflection `σ x = a + b - x`. -/
def refl (a b x : Cf eta) : Cf eta := a + b - x

omit [Fintype ν] in
lemma refl_refl (a b x : Cf eta) : refl a b (refl a b x) = x := by unfold refl; abel

omit [Fintype ν] in
lemma refl_injective (a b : Cf eta) : Function.Injective (refl a b) := fun x y h => by
  have := congrArg (refl a b) h
  rwa [refl_refl, refl_refl] at this

omit [Fintype ν] in
/-- **The box reflection identity**: `[κ_f, κ_{f'}](q, p) = Σ_{B_N} h - Σ_{σ B_N} h`. -/
theorem comm_conv_eq (f f' : Cf eta → ℂ) (q p : Cfg eta N) :
    kmul N (convK N f) (convK N f') q p - kmul N (convK N f') (convK N f) q p =
      ∑ x ∈ fourierConfigCube eta N, f (cidx N q - x) * f' (x - cidx N p) -
        ∑ x ∈ (fourierConfigCube eta N).image (refl (cidx N q) (cidx N p)),
          f (cidx N q - x) * f' (x - cidx N p) := by
  classical
  rw [kmul_convK, kmul_convK, Finset.sum_image (fun x _ y _ h => refl_injective _ _ h)]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold refl
  rw [show cidx N q - (cidx N q + cidx N p - x) = x - cidx N p by abel,
    show cidx N q + cidx N p - x - cidx N p = cidx N q - x by abel]
  ring

omit [Fintype ν] in
lemma refl_mem_cube3 (q p : Cfg eta N) {x : Cf eta} (hx : x ∈ fourierConfigCube eta N) :
    refl (cidx N q) (cidx N p) x ∈ fourierConfigCube eta (3 * N) := by
  rw [← inP_iff_mem_cube] at hx ⊢
  have hq := (inP_iff_mem_cube N (cidx N q)).mpr (finiteConfigLatticeIndex_mem_cube eta N q)
  have hp := (inP_iff_mem_cube N (cidx N p)).mpr (finiteConfigLatticeIndex_mem_cube eta N p)
  intro c i
  have h1 := abs_le.mp (hq c i)
  have h2 := abs_le.mp (hp c i)
  have h3 := abs_le.mp (hx c i)
  simp only [refl, Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub]
  push_cast
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

omit [Fintype ν] in
/-- **The box commutator of convolution kernels lives outside the box**:
`|[κ_f, κ_{f'}](q, p)| ≤ 2 Σ_{y ∈ B_{3N} ∖ B_N} M(q - y) M(y - p)` for a majorant `M` of `f, f'`. -/
theorem norm_comm_conv_le (f f' : Cf eta → ℂ) (M : Cf eta → ℝ) (hM0 : ∀ d, 0 ≤ M d)
    (hf : ∀ d, ‖f d‖ ≤ M d) (hf' : ∀ d, ‖f' d‖ ≤ M d) (q p : Cfg eta N) :
    ‖kmul N (convK N f) (convK N f') q p - kmul N (convK N f') (convK N f) q p‖ ≤
      2 * ∑ y ∈ fourierConfigCube eta (3 * N) \ fourierConfigCube eta N,
        M (cidx N q - y) * M (y - cidx N p) := by
  classical
  rw [comm_conv_eq]
  set A := fourierConfigCube eta N
  set σ := refl (cidx N q) (cidx N p)
  set B := A.image σ
  set h : Cf eta → ℂ := fun x => f (cidx N q - x) * f' (x - cidx N p)
  set T := fourierConfigCube eta (3 * N) \ A
  set m : Cf eta → ℝ := fun y => M (cidx N q - y) * M (y - cidx N p)
  have hm0 : ∀ y, 0 ≤ m y := fun y => mul_nonneg (hM0 _) (hM0 _)
  have e1 := Finset.sum_inter_add_sum_sdiff A B h
  have e2 := Finset.sum_inter_add_sum_sdiff B A h
  rw [Finset.inter_comm] at e2
  have hsplit : ∑ x ∈ A, h x - ∑ x ∈ B, h x = ∑ x ∈ A \ B, h x - ∑ x ∈ B \ A, h x := by
    rw [← e1, ← e2]; ring
  rw [hsplit]
  have hBA : B \ A ⊆ T := by
    intro y hy
    rw [Finset.mem_sdiff] at hy ⊢
    obtain ⟨hyB, hyA⟩ := hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hyB
    exact ⟨refl_mem_cube3 q p hx, hyA⟩
  have hAB : (A \ B).image σ ⊆ B \ A := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_sdiff] at hx ⊢
    refine ⟨Finset.mem_image_of_mem σ hx.1, fun hσA => hx.2 ?_⟩
    rw [← refl_refl (cidx N q) (cidx N p) x]
    exact Finset.mem_image_of_mem σ hσA
  have hterm1 : ∀ y, ‖h y‖ ≤ m y := fun y => by
    simp only [h, m, norm_mul]
    exact mul_le_mul (hf _) (hf' _) (norm_nonneg _) (hM0 _)
  have hterm2 : ∀ y, ‖h (σ y)‖ ≤ m y := fun y => by
    simp only [h, m, σ, refl, norm_mul]
    rw [show cidx N q - (cidx N q + cidx N p - y) = y - cidx N p by abel,
      show cidx N q + cidx N p - y - cidx N p = cidx N q - y by abel]
    calc ‖f (y - cidx N p)‖ * ‖f' (cidx N q - y)‖ ≤ M (y - cidx N p) * M (cidx N q - y) :=
          mul_le_mul (hf _) (hf' _) (norm_nonneg _) (hM0 _)
      _ = M (cidx N q - y) * M (y - cidx N p) := mul_comm _ _
  have hA1 : ∑ x ∈ A \ B, ‖h x‖ ≤ ∑ y ∈ B \ A, m y := by
    calc ∑ x ∈ A \ B, ‖h x‖ = ∑ x ∈ A \ B, ‖h (σ (σ x))‖ := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [show σ (σ x) = x from refl_refl _ _ x]
      _ = ∑ y ∈ (A \ B).image σ, ‖h (σ y)‖ :=
          (Finset.sum_image (f := fun y => ‖h (σ y)‖)
            (fun x _ y _ hxy => refl_injective (cidx N q) (cidx N p) hxy)).symm
      _ ≤ ∑ y ∈ B \ A, ‖h (σ y)‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hAB fun _ _ _ => norm_nonneg _
      _ ≤ ∑ y ∈ B \ A, m y := Finset.sum_le_sum fun y _ => hterm2 y
  have hB1 : ∑ x ∈ B \ A, ‖h x‖ ≤ ∑ y ∈ B \ A, m y := Finset.sum_le_sum fun y _ => hterm1 y
  have hT : ∑ y ∈ B \ A, m y ≤ ∑ y ∈ T, m y :=
    Finset.sum_le_sum_of_subset_of_nonneg hBA fun y _ _ => hm0 y
  calc ‖∑ x ∈ A \ B, h x - ∑ x ∈ B \ A, h x‖
      ≤ ‖∑ x ∈ A \ B, h x‖ + ‖∑ x ∈ B \ A, h x‖ := norm_sub_le _ _
    _ ≤ ∑ x ∈ A \ B, ‖h x‖ + ∑ x ∈ B \ A, ‖h x‖ := add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
    _ ≤ 2 * ∑ y ∈ T, m y := by linarith

omit [Fintype ν] in
/-- **The form of a box commutator of convolution kernels**: for an even majorant `M`,
`|⟨v, [κ_f, κ_{f'}] v⟩| ≤ 2 Σ_{y ∈ B_{3N} ∖ B_N} (Σ_q |v_q| M(q - y))²`. -/
theorem norm_comm_conv_form_le (f f' : Cf eta → ℂ) (M : Cf eta → ℝ) (hM0 : ∀ d, 0 ≤ M d)
    (hMe : ∀ d, M (-d) = M d) (hf : ∀ d, ‖f d‖ ≤ M d) (hf' : ∀ d, ‖f' d‖ ≤ M d) (v : En eta N) :
    ‖⟪v, FSKernel.kop (fun q p => kmul N (convK N f) (convK N f') q p -
        kmul N (convK N f') (convK N f) q p) v⟫_ℂ‖ ≤
      2 * ∑ y ∈ fourierConfigCube eta (3 * N) \ fourierConfigCube eta N,
        (∑ q, ‖v.ofLp q‖ * M (cidx N q - y)) ^ 2 := by
  classical
  set T := fourierConfigCube eta (3 * N) \ fourierConfigCube eta N
  set F : Cfg eta N → Cf eta → ℝ := fun q y => ‖v.ofLp q‖ * M (cidx N q - y)
  refine (norm_inner_kop_le' _ v).trans ?_
  have key : ∀ q p, ‖v.ofLp q‖ * ‖v.ofLp p‖ *
      (2 * ∑ y ∈ T, M (cidx N q - y) * M (y - cidx N p)) = 2 * ∑ y ∈ T, F q y * F p y := by
    intro q p
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [show y - cidx N p = -(cidx N p - y) by abel, hMe]
    simp only [F]
    ring
  calc ∑ q, ∑ p, ‖v.ofLp q‖ * ‖v.ofLp p‖ *
        ‖kmul N (convK N f) (convK N f') q p - kmul N (convK N f') (convK N f) q p‖
      ≤ ∑ q, ∑ p, ‖v.ofLp q‖ * ‖v.ofLp p‖ *
          (2 * ∑ y ∈ T, M (cidx N q - y) * M (y - cidx N p)) := by
        refine Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun p _ => ?_
        exact mul_le_mul_of_nonneg_left (norm_comm_conv_le f f' M hM0 hf hf' q p) (by positivity)
    _ = ∑ q, ∑ p, 2 * ∑ y ∈ T, F q y * F p y := by
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => key q p
    _ = 2 * ∑ q, ∑ p, ∑ y ∈ T, F q y * F p y := by
        simp_rw [← Finset.mul_sum]
    _ = 2 * ∑ y ∈ T, (∑ q, F q y) ^ 2 := by
        congr 1
        calc ∑ q, ∑ p, ∑ y ∈ T, F q y * F p y = ∑ q, ∑ y ∈ T, ∑ p, F q y * F p y :=
              Finset.sum_congr rfl fun q _ => Finset.sum_comm
          _ = ∑ y ∈ T, ∑ q, ∑ p, F q y * F p y := Finset.sum_comm
          _ = ∑ y ∈ T, (∑ q, F q y) ^ 2 :=
              Finset.sum_congr rfl fun y _ => by rw [sq, Finset.sum_mul_sum]

end Reflection

/-! ## The box commutator `e_bd = ⟨v, i[W_N, Ŵ_N] v⟩` -/

section BoxComm

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) {N : ℕ}

open Classical in
/-- The lattice kernel of the flat potential. -/
noncomputable def whL (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (d : Cf eta) : ℂ :=
  ∑ j, (lamC sys p₀ j : ℂ) * (if OnCh j d 0 then wL sys L d else 0)

/-- The even majorant `M(d) = Σ_j [d ∈ τ_j] c_j/|d_j|²`. -/
noncomputable def Mp (sys : CoulombSystem eta ν) (L : ℝ) (d : Cf eta) : ℝ := potMaj sys L d 0

/-- The box commutator `e_bd(v) = ⟨v, i[W_N, Ŵ_N] v⟩`. -/
noncomputable def ebd (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (v : En eta N) : ℂ :=
  ⟪v, (Complex.I • (WN sys L N ∘ₗ WhN sys L p₀ N - WhN sys L p₀ N ∘ₗ WN sys L N)) v⟫_ℂ

variable {sys L p₀}

lemma wNK_eq_convK : wNK sys L N = convK N (wL sys L) := by
  funext q p
  unfold wNK convK
  exact potKernel_eq_wL sys L _ _

lemma whK_eq_convK : whK sys L p₀ N = convK N (whL sys L p₀) := by
  funext q p
  unfold whK convK whL chPart
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  by_cases h : OnCh j (cidx N q) (cidx N p)
  · rw [if_pos h, if_pos ((onCh_iff_sub j _ _).mp h)]
    unfold wNK
    exact potKernel_eq_wL sys L _ _
  · rw [if_neg h, if_neg (fun h' => h ((onCh_iff_sub j _ _).mpr h'))]

lemma Mp_nonneg (hL : 0 < L) (d : Cf eta) : 0 ≤ Mp sys L d := potMaj_nonneg sys hL d 0

lemma Mp_neg (d : Cf eta) : Mp sys L (-d) = Mp sys L d := by
  unfold Mp potMaj
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold chMaj
  have h1 : OnCh j (-d) 0 ↔ OnCh j d 0 := by
    rw [onCh_iff_sub j d 0, sub_zero]
    constructor
    · intro h
      have h2 := onCh_symm h
      rw [onCh_iff_sub, zero_sub, neg_neg] at h2
      exact h2
    · intro h
      have h2 := onCh_symm h
      rw [onCh_iff_sub, zero_sub] at h2
      exact h2
  by_cases h : OnCh j d 0
  · rw [if_pos (h1.mpr h), if_pos h]
    congr 1
    simp [latticeNormSq]
  · rw [if_neg (fun h' => h (h1.mp h')), if_neg h]

lemma norm_wL_le (hL : 0 < L) (d : Cf eta) : ‖wL sys L d‖ ≤ Mp sys L d :=
  norm_potKernel_le sys hL d 0

lemma norm_whL_le (hL : 0 < L) (d : Cf eta) : ‖whL sys L p₀ d‖ ≤ Mp sys L d := by
  classical
  by_cases hd : d = 0
  · subst hd
    have h0 : wL sys L 0 = 0 := potKernel_self_eq_zero hL 0
    unfold whL
    simp only [h0, ite_self, mul_zero, Finset.sum_const_zero, norm_zero]
    exact Mp_nonneg hL 0
  by_cases hj : ∃ j, OnCh j d 0
  · obtain ⟨j, hj⟩ := hj
    have e : whL sys L p₀ d = (lamC sys p₀ j : ℂ) * wL sys L d := by
      unfold whL
      rw [Finset.sum_eq_single j]
      · rw [if_pos hj]
      · intro j' _ hj'
        rw [if_neg (fun h => hj' (onCh_unique h hj hd)), mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lamC_nonneg sys p₀ j)]
    calc lamC sys p₀ j * ‖wL sys L d‖ ≤ 1 * ‖wL sys L d‖ :=
          mul_le_mul_of_nonneg_right (lamC_le_one sys p₀ j) (norm_nonneg _)
      _ ≤ Mp sys L d := by rw [one_mul]; exact norm_wL_le hL d
  · push Not at hj
    have e : whL sys L p₀ d = 0 := by
      unfold whL
      exact Finset.sum_eq_zero fun j _ => by rw [if_neg (hj j), mul_zero]
    rw [e, norm_zero]
    exact Mp_nonneg hL d

/-- **The box commutator lives outside the box**:
`|e_bd(v)| ≤ 2 Σ_{y ∈ B_{3N} ∖ B_N} (Σ_q |v_q| M(q - y))²`. -/
theorem norm_ebd_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (v : En eta N) :
    ‖ebd sys L p₀ v‖ ≤ 2 * ∑ y ∈ fourierConfigCube eta (3 * N) \ fourierConfigCube eta N,
      (∑ q, ‖v.ofLp q‖ * Mp sys L (cidx N q - y)) ^ 2 := by
  have hW : WN sys L N = FSKernel.kop (convK N (wL sys L)) := by
    rw [← wNK_eq_convK]; exact VN_eq_kop sys hL H hKernel
  have hWh : WhN sys L p₀ N = FSKernel.kop (convK N (whL sys L p₀)) := by
    unfold WhN; rw [whK_eq_convK]
  have hcomm : WN sys L N ∘ₗ WhN sys L p₀ N - WhN sys L p₀ N ∘ₗ WN sys L N =
      FSKernel.kop (fun q p => kmul N (convK N (wL sys L)) (convK N (whL sys L p₀)) q p -
        kmul N (convK N (whL sys L p₀)) (convK N (wL sys L)) q p) := by
    rw [hW, hWh, kop_kmul, kop_kmul, ← FSKernel.kop_sub]
    rfl
  unfold ebd
  rw [hcomm, LinearMap.smul_apply, inner_smul_right, norm_mul, Complex.norm_I, one_mul]
  exact norm_comm_conv_form_le _ _ (Mp sys L) (Mp_nonneg hL) Mp_neg (norm_wL_le hL)
    (norm_whL_le hL) v

end BoxComm

end FSFlux
