import PlaneWave.FluxBox.CommutatorTargetRate

/-!
# Flux route, stage 3, part 21: the third dressing `Y₃`

Round 3 eliminates the far–cold operator `N^{FC}` of `PlaneWave.FluxBox.ComRemainderClasses` (`n^{FC} + cm^{FC} = Re⟨u, N^{FC} u⟩`).

* **The gap** (`far_cold_gap`, `far_cold_gap'`): `E(f) ≥ g²n²/(32 m_max)` on `F = ¬Q`,
  `E(b) ≤ g²n²/(128 m_max)` on the cold ball (`c_*² = 1/(64(η+1) m_max)`), so
  `E(f) - E(b) ≥ 3 g²n²/(128 m_max)` and `≥ (3/4) E(f)`.
* **The kernel of `B^{FC}`** (`BFC_eq_kop`): the six chains of `PlaneWave.FluxBox.ComRemainderClasses` as explicit two-hop sums
  (`chainK`, `chainK'`, `bfcK`), supported on far outputs and cold inputs (`bfcK_supp`);
  `xFCK = -i b^{FC}` (`xFCK_eq`).
* **`Y₃ = divK_E(-i N^{FC})`** (`comm_Y3N`: `i[T, Y₃] = N^{FC}`, `Y3N_symm`); on `F × C` the kernel is
  `ỹ(f, b) = -b^{FC}(f, b)/(E(f) - E(b))` (`y3K_far_cold`).
* **`ledger_fc`**: `∫ Re⟨u, N^{FC} u⟩ = [Re⟨u, Y₃ u⟩] - ∫ Re⟨u, i[W, Y₃] u⟩ - ∫ e_{Y₃}`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The far–cold gap -/

section Gap

variable {sys : CoulombSystem eta ν} {L : ℝ} {N : ℕ}

omit [Fintype ν] in
lemma Asym_eq_sum (q : Cfg eta N) :
    Asym sys L N q = ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (cidx N q c) := by
  rw [Asym_eq_Ek]; rfl

omit [Fintype ν] in
/-- On the cold ball, `E ≤ g²n²/(128 m_max)`. -/
lemma Asym_le_cold (hL : 0 < L) {n : ℕ} {q : Cfg eta N} (hq : InC (n : ℝ) (cst sys) (cidx N q)) :
    Asym sys L N q ≤ gF L ^ 2 * (n : ℝ) ^ 2 / (128 * mmax sys) := by
  rw [Asym_eq_sum]
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hcs := cst_sq sys
  have hterm : ∀ c ∈ Finset.univ, gF L ^ 2 / (2 * sys.mass c) * nsq (cidx N q c) ≤
      gF L ^ 2 / 2 * (cst sys * n) ^ 2 := by
    intro c _
    have h1 : nsq (cidx N q c) ≤ (cst sys * n) ^ 2 := hq c
    have h2 := sys.one_le_mass c
    have h0 := nsq_nonneg (cidx N q c)
    calc gF L ^ 2 / (2 * sys.mass c) * nsq (cidx N q c) ≤ gF L ^ 2 / 2 * nsq (cidx N q c) := by
          apply mul_le_mul_of_nonneg_right _ h0
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow, hcs]
  have hm0 : 0 < mmax sys := by linarith
  have he : (0 : ℝ) ≤ eta := Nat.cast_nonneg eta
  have h1 : (eta : ℝ) * (gF L ^ 2 / 2 * (1 / (1024 * ((eta + 1) * mmax sys)) * (n : ℝ) ^ 2)) =
      gF L ^ 2 * (n : ℝ) ^ 2 / (128 * mmax sys) * (eta / (eta + 1) / 16) := by
    field_simp; ring
  rw [h1]
  have h2 : (eta : ℝ) / (eta + 1) / 16 ≤ 1 := by
    have : (eta : ℝ) / (eta + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have h3 : 0 ≤ gF L ^ 2 * (n : ℝ) ^ 2 / (128 * mmax sys) := by positivity
  nlinarith

omit [Fintype ν] in
/-- On the far region, `E ≥ g²n²/(32 m_max)`. -/
lemma Asym_ge_far (hL : 0 < L) {n : ℕ} {q : Cfg eta N} (hq : ¬ InQ (n : ℝ) (cidx N q)) :
    gF L ^ 2 * (n : ℝ) ^ 2 / (32 * mmax sys) ≤ Asym sys L N q := by
  simp only [InQ, not_forall, not_le] at hq
  obtain ⟨c, hc⟩ := hq
  rw [Asym_eq_sum]
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hmc := mass_le_mmax sys c
  have hmc0 := sys.mass_pos c
  have h1 := Finset.single_le_sum (f := fun c => gF L ^ 2 / (2 * sys.mass c) * nsq (cidx N q c))
    (fun c _ => by have := sys.mass_pos c; have := nsq_nonneg (cidx N q c); positivity)
    (Finset.mem_univ c)
  refine le_trans ?_ h1
  show gF L ^ 2 * (n : ℝ) ^ 2 / (32 * mmax sys) ≤ gF L ^ 2 / (2 * sys.mass c) * nsq (cidx N q c)
  have h2 : gF L ^ 2 * (n : ℝ) ^ 2 / (32 * mmax sys) = gF L ^ 2 / (2 * mmax sys) * ((n : ℝ) / 4) ^ 2 := by
    field_simp; ring
  rw [h2]
  apply mul_le_mul _ hc.le (by positivity) (by positivity)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

omit [Fintype ν] in
/-- **The far–cold gap**: `E(f) - E(b) ≥ 3 g²n²/(128 m_max)`. -/
lemma far_cold_gap (hL : 0 < L) {n : ℕ} {f b : Cfg eta N} (hf : ¬ InQ (n : ℝ) (cidx N f))
    (hb : InC (n : ℝ) (cst sys) (cidx N b)) :
    3 * gF L ^ 2 * (n : ℝ) ^ 2 / (128 * mmax sys) ≤ Asym sys L N f - Asym sys L N b := by
  have h1 := Asym_ge_far (sys := sys) hL hf
  have h2 := Asym_le_cold (sys := sys) hL hb
  have e : gF L ^ 2 * (n : ℝ) ^ 2 / (32 * mmax sys) =
      3 * gF L ^ 2 * (n : ℝ) ^ 2 / (128 * mmax sys) + gF L ^ 2 * (n : ℝ) ^ 2 / (128 * mmax sys) := by
    have := one_le_mmax sys
    field_simp; ring
  linarith

omit [Fintype ν] in
/-- The growing form of the gap: `E(f) - E(b) ≥ (3/4) E(f)`. -/
lemma far_cold_gap' (hL : 0 < L) {n : ℕ} {f b : Cfg eta N} (hf : ¬ InQ (n : ℝ) (cidx N f))
    (hb : InC (n : ℝ) (cst sys) (cidx N b)) :
    3 / 4 * Asym sys L N f ≤ Asym sys L N f - Asym sys L N b := by
  have h1 := Asym_ge_far (sys := sys) hL hf
  have h2 := Asym_le_cold (sys := sys) hL hb
  have e : gF L ^ 2 * (n : ℝ) ^ 2 / (128 * mmax sys) =
      1 / 4 * (gF L ^ 2 * (n : ℝ) ^ 2 / (32 * mmax sys)) := by
    have := one_le_mmax sys
    field_simp; ring
  linarith

omit [Fintype ν] in
lemma inC_imp_inQ' {n : ℕ} {q : Cfg eta N} (h : InC (n : ℝ) (cst sys) (cidx N q)) :
    InQ (n : ℝ) (cidx N q) :=
  inC_imp_inQ (Nat.cast_nonneg n) (cst_pos sys).le (by linarith [cst_le sys]) h

end Gap

/-! ## The kernel of the far–cold chains -/

section Chains

variable {X : Type*} [Fintype X]

open Classical in
/-- The kernel of the chain `Π_{S₁} κ₂ Π_{S₂} κ₁ Π_{S₃}`. -/
noncomputable def chainK (S₁ S₂ S₃ : X → Prop) (κ₂ κ₁ : X → X → ℂ) (q p : X) : ℂ :=
  if S₁ q ∧ S₃ p then ∑ d, κ₂ q d * (if S₂ d then κ₁ d p else 0) else 0

open Classical in
/-- The kernel of the chain `Π_{S₁} κ₂ κ₁ Π_{S₃}`. -/
noncomputable def chainK' (S₁ S₃ : X → Prop) (κ₂ κ₁ : X → X → ℂ) (q p : X) : ℂ :=
  if S₁ q ∧ S₃ p then ∑ d, κ₂ q d * κ₁ d p else 0

lemma chain_apply (S₁ S₂ S₃ : X → Prop) (κ₂ κ₁ : X → X → ℂ) (v : EuclideanSpace ℂ X) (q : X) :
    (FSKernel.res S₁ (FSKernel.kop κ₂ (FSKernel.res S₂ (FSKernel.kop κ₁ (FSKernel.res S₃ v))))).ofLp q =
      ∑ p, v.ofLp p * chainK S₁ S₂ S₃ κ₂ κ₁ q p := by
  classical
  unfold chainK
  rw [FSKernel.res_apply]
  by_cases h1 : S₁ q
  · rw [if_pos h1, FSKernel.kop_apply]
    have e : ∀ d, (FSKernel.res S₂ (FSKernel.kop κ₁ (FSKernel.res S₃ v))).ofLp d * κ₂ q d =
        ∑ p, v.ofLp p * (if S₃ p then κ₂ q d * (if S₂ d then κ₁ d p else 0) else 0) := by
      intro d
      rw [FSKernel.res_apply]
      by_cases h2 : S₂ d
      · rw [if_pos h2, FSKernel.kop_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [FSKernel.res_apply]
        by_cases h3 : S₃ p
        · rw [if_pos h3, if_pos h3, if_pos h2]; ring
        · rw [if_neg h3, if_neg h3]; ring
      · rw [if_neg h2, zero_mul]
        symm
        exact Finset.sum_eq_zero fun p _ => by split_ifs <;> simp_all
    rw [Finset.sum_congr rfl fun d _ => e d, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    by_cases h3 : S₃ p
    · rw [if_pos ⟨h1, h3⟩]
      exact Finset.sum_congr rfl fun d _ => by rw [if_pos h3]
    · rw [if_neg (fun h => h3 h.2)]
      exact Finset.sum_eq_zero fun d _ => by rw [if_neg h3]
  · rw [if_neg h1]
    symm
    exact Finset.sum_eq_zero fun p _ => by rw [if_neg (fun h => h1 h.1), mul_zero]

lemma chain_apply' (S₁ S₃ : X → Prop) (κ₂ κ₁ : X → X → ℂ) (v : EuclideanSpace ℂ X) (q : X) :
    (FSKernel.res S₁ (FSKernel.kop κ₂ (FSKernel.kop κ₁ (FSKernel.res S₃ v)))).ofLp q =
      ∑ p, v.ofLp p * chainK' S₁ S₃ κ₂ κ₁ q p := by
  classical
  unfold chainK'
  rw [FSKernel.res_apply]
  by_cases h1 : S₁ q
  · rw [if_pos h1, FSKernel.kop_apply]
    have e : ∀ d, (FSKernel.kop κ₁ (FSKernel.res S₃ v)).ofLp d * κ₂ q d =
        ∑ p, v.ofLp p * (if S₃ p then κ₂ q d * κ₁ d p else 0) := by
      intro d
      rw [FSKernel.kop_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [FSKernel.res_apply]
      by_cases h3 : S₃ p
      · rw [if_pos h3, if_pos h3]; ring
      · rw [if_neg h3, if_neg h3]; ring
    rw [Finset.sum_congr rfl fun d _ => e d, Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    by_cases h3 : S₃ p
    · rw [if_pos ⟨h1, h3⟩]
      exact Finset.sum_congr rfl fun d _ => by rw [if_pos h3]
    · rw [if_neg (fun h => h3 h.2)]
      exact Finset.sum_eq_zero fun d _ => by rw [if_neg h3]
  · rw [if_neg h1]
    symm
    exact Finset.sum_eq_zero fun p _ => by rw [if_neg (fun h => h1 h.1), mul_zero]

end Chains

section BFCKernel

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ)

/-- The kernel of `B^{FC}`: the six far–cold chains. -/
noncomputable def bfcK (q p : Cfg eta N) : ℂ :=
  chainK (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun d => InP (n : ℝ) (cidx N d))
      (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wNK sys L N) (whK sys L p₀ N) q p -
    chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
      (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
      (wNK sys L N) (whK sys L p₀ N) q p +
    chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
      (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
      (whK sys L p₀ N) (wNK sys L N) q p +
    chainK (fun q => ¬ InQ (n : ℝ) (cidx N q)) (fun d => ¬ InP (n : ℝ) (cidx N d))
      (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wNK sys L N) (ycK sys L p₀ N) q p -
    chainK' (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
      (ycK sys L p₀ N) (wNK sys L N) q p -
    chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
      (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
      (ycK sys L p₀ N) (wNK sys L N) q p

variable {sys L p₀ N n}

/-- **`B^{FC}` is the kernel operator of `b^{FC}`**. -/
theorem BFC_eq_kop (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    BFC sys L p₀ N n = FSKernel.kop (bfcK sys L p₀ N n) := by
  have hW : WN sys L N = FSKernel.kop (wNK sys L N) := VN_eq_kop sys hL H hKernel
  refine LinearMap.ext fun v => ?_
  ext q
  unfold BFC
  rw [hW]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, PiLp.sub_apply,
    PiLp.add_apply]
  rw [chain_apply, chain_apply, chain_apply, chain_apply, chain_apply', chain_apply,
    FSKernel.kop_apply]
  unfold bfcK
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- `x^{FC} = -i b^{FC}`. -/
lemma xFCK_eq (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (q p : Cfg eta N) : xFCK sys L p₀ N n q p = -Complex.I * bfcK sys L p₀ N n q p := by
  unfold xFCK
  rw [BFC_eq_kop hL H hKernel, ← FSKernel.kop_smul, matK_kop]
  rfl

omit [Fintype ν] in
lemma chainK_supp {X : Type*} [Fintype X] {S₁ S₂ S₃ : X → Prop} {κ₂ κ₁ : X → X → ℂ} {q p : X}
    (h : chainK S₁ S₂ S₃ κ₂ κ₁ q p ≠ 0) : S₁ q ∧ S₃ p := by
  classical
  unfold chainK at h
  by_contra hc
  exact h (if_neg hc)

omit [Fintype ν] in
lemma chainK'_supp {X : Type*} [Fintype X] {S₁ S₃ : X → Prop} {κ₂ κ₁ : X → X → ℂ} {q p : X}
    (h : chainK' S₁ S₃ κ₂ κ₁ q p ≠ 0) : S₁ q ∧ S₃ p := by
  classical
  unfold chainK' at h
  by_contra hc
  exact h (if_neg hc)

/-- **The support of `b^{FC}`**: far output, cold input. -/
lemma bfcK_supp {q p : Cfg eta N} (h : bfcK sys L p₀ N n q p ≠ 0) :
    ¬ InQ (n : ℝ) (cidx N q) ∧ InC (n : ℝ) (cst sys) (cidx N p) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hPQ : ¬ InP (n : ℝ) (cidx N q) → ¬ InQ (n : ℝ) (cidx N q) := fun h hq =>
    h (inQ_imp_inP hn0 hq)
  by_contra hc
  apply h
  unfold bfcK
  have z1 : ∀ {S₂ : Cfg eta N → Prop} {κ₂ κ₁ : Cfg eta N → Cfg eta N → ℂ},
      chainK (fun q => ¬ InP (n : ℝ) (cidx N q)) S₂ (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        κ₂ κ₁ q p = 0 := by
    intro S₂ κ₂ κ₁
    by_contra h0
    obtain ⟨h1, h3⟩ := chainK_supp h0
    exact hc ⟨hPQ h1, h3⟩
  have z2 : ∀ {S₂ : Cfg eta N → Prop} {κ₂ κ₁ : Cfg eta N → Cfg eta N → ℂ},
      chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q)) S₂
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) κ₂ κ₁ q p = 0 := by
    intro S₂ κ₂ κ₁
    by_contra h0
    obtain ⟨h1, h3⟩ := chainK_supp h0
    exact hc ⟨h1.2, h3⟩
  have z3 : ∀ {S₂ : Cfg eta N → Prop} {κ₂ κ₁ : Cfg eta N → Cfg eta N → ℂ},
      chainK (fun q => ¬ InQ (n : ℝ) (cidx N q)) S₂ (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        κ₂ κ₁ q p = 0 := by
    intro S₂ κ₂ κ₁
    by_contra h0
    obtain ⟨h1, h3⟩ := chainK_supp h0
    exact hc ⟨h1, h3⟩
  have z4 : ∀ {κ₂ κ₁ : Cfg eta N → Cfg eta N → ℂ},
      chainK' (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        κ₂ κ₁ q p = 0 := by
    intro κ₂ κ₁
    by_contra h0
    obtain ⟨h1, h3⟩ := chainK'_supp h0
    exact hc ⟨hPQ h1, h3⟩
  rw [z1, z2, z2, z3, z4, z2]
  ring

end BFCKernel

/-! ## The third dressing -/

section Y3

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ)

/-- The kernel of the third dressing `Y₃ = N^{FC}/(iω)`. -/
noncomputable def y3K (q p : Cfg eta N) : ℂ :=
  FSKernel.divK (Asym sys L N) (fun q p => -Complex.I * nFCK sys L p₀ N n q p) q p

/-- The third dressing on the box. -/
noncomputable abbrev Y3N : En eta N →ₗ[ℂ] En eta N := FSKernel.kop (y3K sys L p₀ N n)

variable {sys L p₀ N n}

/-- The far–cold kernel joins far and cold configurations only. -/
lemma nFCK_supp (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {q p : Cfg eta N} (h : nFCK sys L p₀ N n q p ≠ 0) :
    (¬ InQ (n : ℝ) (cidx N q) ∧ InC (n : ℝ) (cst sys) (cidx N p)) ∨
      (InC (n : ℝ) (cst sys) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N p)) := by
  unfold nFCK at h
  rw [xFCK_eq hL H hKernel, xFCK_eq hL H hKernel] at h
  by_cases h1 : bfcK sys L p₀ N n q p = 0
  · rw [h1, mul_zero, zero_add] at h
    have h2 : bfcK sys L p₀ N n p q ≠ 0 := by
      intro h0; rw [h0, mul_zero, map_zero] at h; exact h rfl
    obtain ⟨a, b⟩ := bfcK_supp h2
    exact Or.inr ⟨b, a⟩
  · exact Or.inl (bfcK_supp h1)

/-- On `F × C` the far–cold kernel is `-i b^{FC}`. -/
lemma nFCK_far_cold (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {q p : Cfg eta N} (hp : InC (n : ℝ) (cst sys) (cidx N p)) :
    nFCK sys L p₀ N n q p = -Complex.I * bfcK sys L p₀ N n q p := by
  unfold nFCK
  rw [xFCK_eq hL H hKernel, xFCK_eq hL H hKernel]
  have h0 : bfcK sys L p₀ N n p q = 0 := by
    by_contra h
    exact (bfcK_supp h).1 (inC_imp_inQ' hp)
  rw [h0, mul_zero, map_zero, add_zero]

/-- **The third homological equation** `i[T_N, Y₃] = N^{FC}`. -/
theorem comm_Y3N (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 1 ≤ n) :
    Complex.I • (TN sys L N ∘ₗ Y3N sys L p₀ N n - Y3N sys L p₀ N n ∘ₗ TN sys L N) =
      NFC sys L p₀ N n := by
  have hg := gF_pos hL
  have hgap : ∀ q p, Asym sys L N q = Asym sys L N p →
      -Complex.I * nFCK sys L p₀ N n q p = 0 := by
    intro q p hqp
    by_contra h
    have h' : nFCK sys L p₀ N n q p ≠ 0 := by intro h0; rw [h0, mul_zero] at h; exact h rfl
    have hm := one_le_mmax sys
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hpos : 0 < 3 * gF L ^ 2 * (n : ℝ) ^ 2 / (128 * mmax sys) := by positivity
    rcases nFCK_supp hL H hKernel h' with ⟨hq, hp⟩ | ⟨hq, hp⟩
    · have := far_cold_gap (sys := sys) hL hq hp
      linarith
    · have := far_cold_gap (sys := sys) hL hp hq
      linarith
  have h := FSKernel.comm_divK (Asym sys L N) (fun q p => -Complex.I * nFCK sys L p₀ N n q p) hgap
  have e : Y3N sys L p₀ N n = FSKernel.kop (FSKernel.divK (Asym sys L N)
      (fun q p => -Complex.I * nFCK sys L p₀ N n q p)) := rfl
  rw [e]
  change Complex.I • (FSKernel.dg (fun q => (Asym sys L N q : ℂ)) ∘ₗ _ - _ ∘ₗ
    FSKernel.dg (fun q => (Asym sys L N q : ℂ))) = _
  rw [h, ← FSKernel.kop_smul]
  congr 1
  funext q p
  simp only [Pi.smul_apply, smul_eq_mul]
  have hI : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [← mul_assoc, hI, one_mul]

lemma y3K_conj (q p : Cfg eta N) : y3K sys L p₀ N n p q = conj (y3K sys L p₀ N n q p) := by
  unfold y3K FSKernel.divK
  dsimp only
  by_cases h : Asym sys L N q = Asym sys L N p
  · rw [if_pos h.symm, if_pos h]; simp
  · rw [if_neg (Ne.symm h), if_neg h, nFCK_conj q p, map_div₀, map_mul, map_neg,
      Complex.conj_I, Complex.conj_ofReal]
    have hd : ((Asym sys L N q - Asym sys L N p : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr h
    have hd' : ((Asym sys L N p - Asym sys L N q : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (Ne.symm h)
    rw [div_eq_div_iff hd' hd]
    push_cast
    ring

lemma Y3N_symm : (Y3N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N).IsSymmetric :=
  FSKernel.kop_symm _ fun q p => y3K_conj q p

/-- **The third dressing on `F × C`**: `ỹ(f, b) = -b^{FC}(f, b)/(E(f) - E(b))`. -/
lemma y3K_far_cold (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 1 ≤ n) {f b : Cfg eta N} (hf : ¬ InQ (n : ℝ) (cidx N f))
    (hb : InC (n : ℝ) (cst sys) (cidx N b)) :
    y3K sys L p₀ N n f b = -bfcK sys L p₀ N n f b /
      ((Asym sys L N f - Asym sys L N b : ℝ) : ℂ) := by
  have hg := gF_pos hL
  have hgap := far_cold_gap (sys := sys) hL hf hb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := one_le_mmax sys
  have hpos : 0 < 3 * gF L ^ 2 * (n : ℝ) ^ 2 / (128 * mmax sys) := by positivity
  have hne : Asym sys L N f ≠ Asym sys L N b := by intro h; rw [h, sub_self] at hgap; linarith
  unfold y3K FSKernel.divK
  dsimp only
  rw [if_neg hne, nFCK_far_cold hL H hKernel hb]
  congr 1
  have hI : -Complex.I * -Complex.I = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
  rw [← mul_assoc, hI]
  ring

/-- `ỹ` vanishes off `F × C` and `C × F`. -/
lemma y3K_supp (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {q p : Cfg eta N} (h : y3K sys L p₀ N n q p ≠ 0) :
    (¬ InQ (n : ℝ) (cidx N q) ∧ InC (n : ℝ) (cst sys) (cidx N p)) ∨
      (InC (n : ℝ) (cst sys) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N p)) := by
  apply nFCK_supp hL H hKernel
  intro h0
  apply h
  unfold y3K FSKernel.divK
  dsimp only
  split_ifs
  · rfl
  · rw [h0, mul_zero, zero_div]

end Y3

/-! ## The far–cold ledger -/

section Ledger

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta) {N : ℕ} (n : ℕ)

include hL hKernel in
/-- **The far–cold ledger**: along the exact evolution,
`∫₀ᵗ Re⟨u, N^{FC} u⟩ = [Re⟨u, Y₃ u⟩]₀ᵗ - ∫₀ᵗ Re⟨u, i[W, Y₃] u⟩ - ∫₀ᵗ e_{Y₃}`. -/
theorem ledger_fc (hn : 1 ≤ n) (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, (⟪ub H D N s, NFC sys L p₀ N n (ub H D N s)⟫_ℂ).re =
      ((⟪ub H D N t, Y3N sys L p₀ N n (ub H D N t)⟫_ℂ).re -
          (⟪ub H D N 0, Y3N sys L p₀ N n (ub H D N 0)⟫_ℂ).re) -
        (∫ s in (0 : ℝ)..t, (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y3N sys L p₀ N n -
          Y3N sys L p₀ N n ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re) -
        ∫ s in (0 : ℝ)..t, eY sys H D (Y3N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N) s := by
  have hE := elim_box sys hL H hKernel (N := N) Hunit hPeriodic D (Y3N sys L p₀ N n)
    Y3N_symm t
  rw [comm_Y3N hL H hKernel hn] at hE
  exact hE

end Ledger

end FSFlux
