import PlaneWave.Source.AssemblyIdentity

/-!
# Flux/source build, block 3a: Hardy on `ℓ²` and the bound `‖V_b‖ ≤ C K`

* `potential_form_bound`: **the mass-weighted Hardy bound on the full space**,
  `‖W u‖² ≤ C_m² Σ_p (1 + 2E(p)) |(S u)(p)|²` for every `u ∈ H²` (from the release's uniform
  finite bound by truncation limits, as for its `potential_sq_le`);
* finitely supported vectors in the Euclidean bulk block `Q` (`Qs`), their weighted lifts
  `liftQ` (`S (liftQ x) = 1_Q x`) and `W (liftQ x)(q) = Σ_{p ∈ Q} x(p) w(q, p)`;
* `norm_Vb_le`: `‖V_b‖ ≤ 2 C_m (1 + η g² n²/16)^{1/2}`, i.e. `C K` (`lem:bulk-weighted`:
  "`‖W Q‖ ≤ C K` by Hardy, whence `‖V_b‖ ≤ C K`").
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics NormedSpace FluxSourceTest

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Hardy on `ℓ²` -/

variable (sys : CoulombSystem eta ν) {L : ℝ}

omit [Fintype ν] in
lemma one_add_two_Ek_le_weight (L : ℝ) (q : Cf eta) :
    1 + 2 * Ek sys L q ≤ molecularFourierH2Weight eta (gF L) q := by
  have h := two_mul_coulombKineticEnergySymbol_le sys (gF L) q
  rw [Ek, E_eq_kineticSymbol]
  linarith

omit [Fintype ν] in
lemma one_le_one_add_two_Ek (L : ℝ) (q : Cf eta) : 1 ≤ 1 + 2 * Ek sys L q := by
  have := E_nonneg (g := gF L) (fun c => sys.mass_pos c) q
  linarith

omit [Fintype ν] in
/-- The form weight of a vector of `D(T)` is summable. -/
lemma summable_form (u : MolecularFourierH2 eta) :
    Summable fun q => (1 + 2 * Ek sys L q) * ‖Sm eta L u q‖ ^ 2 := by
  refine (l2_summable_sq u).of_nonneg_of_le
    (fun q => mul_nonneg (by linarith [one_le_one_add_two_Ek sys L q]) (sq_nonneg _)) fun q => ?_
  have hw := molecularFourierH2Weight_ge_one eta (gF L) q
  have h1 := one_add_two_Ek_le_weight sys L q
  have h2 := molecularH2Coeff_weight_mass (gF L) u q
  rw [Sm, molecularH2StateMap_apply]
  have h3 : (1 + 2 * Ek sys L q) ≤ molecularFourierH2Weight eta (gF L) q ^ 2 := by nlinarith
  calc (1 + 2 * Ek sys L q) * ‖molecularH2Coeff (gF L) u q‖ ^ 2
      ≤ molecularFourierH2Weight eta (gF L) q ^ 2 * ‖molecularH2Coeff (gF L) u q‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    _ = ‖u q‖ ^ 2 := h2

omit [Fintype ν] in
/-- The finite form weight of a cube extraction is a partial sum of the full one. -/
lemma weightedNormSq_extract_le_tsum (count : ℕ) (c : Cf eta → ℂ)
    (hs : Summable fun q => (1 + 2 * Ek sys L q) * ‖c q‖ ^ 2) :
    weightedNormSq (fun p => 1 + massKineticSymbol sys.mass (finitePlaneWaveKabs (gF L) count) p)
        (fullCoeffVector (finiteFourierCoeffExtract count c)) ≤
      ∑' q, (1 + 2 * Ek sys L q) * ‖c q‖ ^ 2 := by
  classical
  set F : Cf eta → ℝ := fun q => (1 + 2 * Ek sys L q) * ‖c q‖ ^ 2 with hF
  have hF0 : ∀ q, 0 ≤ F q := fun q =>
    mul_nonneg (by linarith [one_le_one_add_two_Ek sys L q]) (sq_nonneg _)
  have hfin : weightedNormSq (fun p => 1 + massKineticSymbol sys.mass
      (finitePlaneWaveKabs (gF L) count) p) (fullCoeffVector (finiteFourierCoeffExtract count c)) =
      ∑ q ∈ fourierConfigCube eta count, F q := by
    unfold weightedNormSq fourierConfigCube
    rw [Finset.sum_image (fun p _ q _ h => finiteConfigLatticeIndex_injective eta count h)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [fullCoeffVector_apply]
    rw [massKineticSymbol_eq_lattice_sum]
    simp only [hF, finiteFourierCoeffExtract, Ek, E_eq_kineticSymbol, coulombKineticEnergySymbol]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hfin]
  exact hs.sum_le_tsum _ (fun q _ => hF0 q)

variable (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel in
/-- **Hardy on the full space**: `‖W u‖² ≤ C_m² Σ_p (1 + 2E(p)) |(S u)(p)|²` for `u ∈ H²`. -/
theorem potential_form_bound (Hunit : ℝ) (hL : 0 < L)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (u : MolecularFourierH2 eta) :
    ‖Wp sys L H u‖ ^ 2 ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
      ∑' q, (1 + 2 * Ek sys L q) * ‖Sm eta L u q‖ ^ 2 := by
  set C := finiteCoulombPhysicalMassConstant sys L Hunit
  set W := Wp sys L H
  set B : ℝ := ∑' q, (1 + 2 * Ek sys L q) * ‖Sm eta L u q‖ ^ 2
  -- the form weight of a truncation is at most that of `u`
  have hBN : ∀ N, ∑' q, (1 + 2 * Ek sys L q) * ‖Sm eta L (molecularH2Truncate N u) q‖ ^ 2 ≤ B := by
    intro N
    refine (summable_form sys (molecularH2Truncate N u)).tsum_le_tsum (fun q => ?_)
      (summable_form sys u)
    refine mul_le_mul_of_nonneg_left ?_ (by linarith [one_le_one_add_two_Ek sys L q])
    rw [Sm, molecularH2StateMap_truncate, lpTruncate_apply]
    split_ifs
    · exact le_rfl
    · rw [norm_zero]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
  -- finite compressions
  have hfin : ∀ N count, N ≤ count →
      ‖molecularH2Truncate count (W (molecularH2Truncate N u))‖ ^ 2 ≤ C ^ 2 * B := by
    intro N count hc
    rw [show W = coulombFourierPotentialH2 sys (2 * Real.pi / L) H from rfl,
      truncate_potential_eq sys L H hKernel N count hc u,
      finiteFourierLpEmbed_norm_eq_fullCoeffVector]
    have hmass := finiteCoulombPotential_physical_massBound sys L Hunit count hL hPeriodic
      (fullCoeffVector (finiteFourierCoeffExtract count
          (molecularH2Coeff (2 * Real.pi / L) (molecularH2Truncate N u))))
    have hw := weightedNormSq_extract_le_tsum sys (L := L) count
      (molecularH2Coeff (gF L) (molecularH2Truncate N u))
      (by simpa only [Sm, molecularH2StateMap_apply] using summable_form sys (molecularH2Truncate N u))
    have hw' := hw.trans (by simpa only [Sm, molecularH2StateMap_apply] using hBN N)
    calc ‖fullCoeffVector (finiteCoulombPotential sys (coulombCellAmplitude L) count
          (fullCoeffVector (finiteFourierCoeffExtract count
            (molecularH2Coeff (2 * Real.pi / L) (molecularH2Truncate N u))))).ofLp‖ ^ 2
        = ‖finiteCoulombPotential sys (coulombCellAmplitude L) count
          (fullCoeffVector (finiteFourierCoeffExtract count
            (molecularH2Coeff (2 * Real.pi / L) (molecularH2Truncate N u))))‖ ^ 2 := rfl
      _ ≤ C ^ 2 * weightedNormSq
            (fun p => 1 + massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) count) p)
            (fullCoeffVector (finiteFourierCoeffExtract count
              (molecularH2Coeff (2 * Real.pi / L) (molecularH2Truncate N u)))) := hmass
      _ ≤ C ^ 2 * B := mul_le_mul_of_nonneg_left hw' (sq_nonneg _)
  -- remove the output truncation
  have hN : ∀ N, ‖W (molecularH2Truncate N u)‖ ^ 2 ≤ C ^ 2 * B := by
    intro N
    have ht := (molecularH2Truncate_tendsto (W (molecularH2Truncate N u))).norm.pow 2
    exact le_of_tendsto ht (eventually_atTop.mpr ⟨N, fun count hc => hfin N count hc⟩)
  -- remove the input truncation
  have hL1 : Tendsto (fun N => ‖W (molecularH2Truncate N u)‖ ^ 2) atTop (𝓝 (‖W u‖ ^ 2)) :=
    ((W.continuous.tendsto u).comp (molecularH2Truncate_tendsto u)).norm.pow 2
  exact le_of_tendsto hL1 (Eventually.of_forall hN)

/-! ## Finitely supported vectors in the bulk block -/

open Classical in
/-- The configurations of the Euclidean bulk block `Q` (every register `|k_a| ≤ n/4`). -/
noncomputable def Qs (eta n : ℕ) : Finset (Cf eta) := (Qf eta n).filter fun k => InQ (n : ℝ) k

omit [Fintype ν] in
lemma mem_Qs {n : ℕ} {k : Cf eta} : k ∈ Qs eta n ↔ InQ (n : ℝ) k := by
  classical
  unfold Qs
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_Qbox_of_inQ (Nat.cast_nonneg n) h, h⟩⟩

/-- The weighted lift of the `Q`-part of a vector: `S (liftQ x) = 1_Q x`. -/
noncomputable def liftQ (L : ℝ) (n : ℕ) (x : L2 eta) : MolecularFourierH2 eta :=
  ∑ p ∈ Qs eta n, x p • wdelta (gF L) p

omit [Fintype ν] in
lemma stateMap_liftQ (n : ℕ) (x : L2 eta) :
    Sm eta L (liftQ L n x) = lpTruncate (Qs eta n) x := by
  classical
  unfold liftQ lpTruncate
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, Sm, stateMap_wdelta, ev, ← lp.single_smul, smul_eq_mul, mul_one]

include hKernel in
lemma potential_liftQ (hL : 0 < L) (n : ℕ) (x : L2 eta) (q : Cf eta) :
    Wp sys L H (liftQ L n x) q = ∑ p ∈ Qs eta n, x p * potKernel sys L q p := by
  unfold liftQ
  rw [map_sum, lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [show Wp sys L H (wdelta (gF L) p) q = potKernel sys L q p from
    potential_wdelta sys L H hKernel hL p q]

omit [Fintype ν] in
lemma form_liftQ_le (n : ℕ) (x : L2 eta) :
    ∑' q, (1 + 2 * Ek sys L q) * ‖Sm eta L (liftQ L n x) q‖ ^ 2 ≤
      (1 + eta * gF L ^ 2 * n ^ 2 / 16) * ‖x‖ ^ 2 := by
  classical
  have hzero : ∀ q ∉ Qs eta n, (1 + 2 * Ek sys L q) * ‖Sm eta L (liftQ L n x) q‖ ^ 2 = 0 := by
    intro q hq
    rw [stateMap_liftQ, lpTruncate_apply, if_neg hq]; simp
  rw [tsum_eq_sum hzero]
  calc ∑ q ∈ Qs eta n, (1 + 2 * Ek sys L q) * ‖Sm eta L (liftQ L n x) q‖ ^ 2
      ≤ ∑ q ∈ Qs eta n, (1 + eta * gF L ^ 2 * n ^ 2 / 16) * ‖x q‖ ^ 2 := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [stateMap_liftQ, lpTruncate_apply, if_pos hq]
        have := Ek_le_of_inQ (sys := sys) (L := L) (mem_Qs.mp hq)
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = (1 + eta * gF L ^ 2 * n ^ 2 / 16) * ∑ q ∈ Qs eta n, ‖x q‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 + eta * gF L ^ 2 * n ^ 2 / 16) * ‖x‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← tsum_sq_coord x]
        exact (summable_sq_coord x).sum_le_tsum _ fun _ _ => sq_nonneg _

include hKernel in
/-- `‖W 1_Q x‖ ≤ C_m (1 + η g² n²/16)^{1/2} ‖x‖`: the potential on the bulk block is `O(K)`. -/
theorem norm_W_liftQ_le (Hunit : ℝ) (hL : 0 < L)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (n : ℕ) (x : L2 eta) :
    ‖Wp sys L H (liftQ L n x)‖ ≤ finiteCoulombPhysicalMassConstant sys L Hunit *
      Real.sqrt (1 + eta * gF L ^ 2 * n ^ 2 / 16) * ‖x‖ := by
  have hC : 0 ≤ finiteCoulombPhysicalMassConstant sys L Hunit :=
    finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have h1 := potential_form_bound sys H hKernel Hunit hL hPeriodic (liftQ L n x)
  have h2 := form_liftQ_le sys (L := L) n x
  have h3 : ‖Wp sys L H (liftQ L n x)‖ ^ 2 ≤ (finiteCoulombPhysicalMassConstant sys L Hunit *
      Real.sqrt (1 + eta * gF L ^ 2 * n ^ 2 / 16) * ‖x‖) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    calc _ ≤ _ := h1
      _ ≤ finiteCoulombPhysicalMassConstant sys L Hunit ^ 2 *
          ((1 + eta * gF L ^ 2 * n ^ 2 / 16) * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

/-! ## `‖V_b‖ ≤ C K` -/

omit [Fintype ν] in
lemma not_inP_of_cross_inQ {n : ℕ} {q p : Cf eta} (hc : Cross (n : ℝ) q p) (hq : InQ (n : ℝ) q) :
    ¬ InP (n : ℝ) p := by
  rcases hc with ⟨-, hp⟩ | ⟨hq', -⟩
  · exact hp
  · exact absurd (hq.inP (Nat.cast_nonneg n)) hq'

omit [Fintype ν] in
lemma inQ_not_cross_left {n : ℕ} {q p : Cf eta} (hq : InQ (n : ℝ) q) :
    Cross (n : ℝ) q p ↔ ¬ InP (n : ℝ) p := by
  constructor
  · exact fun h => not_inP_of_cross_inQ h hq
  · exact fun hp => Or.inl ⟨hq, hp⟩

open Classical in
include hKernel in
/-- The coordinates of `V_b x` outside `Q`: `(V_b x)(q) = [q ∉ P] (W 1_Q x)(q)`. -/
lemma Vb_apply_out (hL : 0 < L) (n : ℕ) (x : L2 eta) {q : Cf eta} (hq : ¬ InQ (n : ℝ) q) :
    Vb sys L n hL x q = if InP (n : ℝ) q then 0 else Wp sys L H (liftQ L n x) q := by
  classical
  rw [Vb_apply]
  split_ifs with hqP
  · refine (tsum_congr fun p => ?_).trans tsum_zero
    unfold vbK
    rw [if_neg]
    · simp
    rintro (⟨h1, -⟩ | ⟨h1, -⟩)
    · exact hq h1
    · exact h1 hqP
  · rw [potential_liftQ sys H hKernel hL]
    have hz : ∀ p ∉ Qs eta n, vbK sys L n q p * x p = 0 := by
      intro p hp
      unfold vbK
      rw [if_neg]
      · simp
      rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact hq h1
      · exact hp (mem_Qs.mpr h2)
    rw [tsum_eq_sum hz]
    refine Finset.sum_congr rfl fun p hp => ?_
    unfold vbK
    have hc : Cross (n : ℝ) q p := Or.inr ⟨hqP, mem_Qs.mp hp⟩
    rw [if_pos hc, mul_comm]

omit [Fintype ν] in
lemma inP_iff_mem_cube (n : ℕ) (p : Cf eta) : InP (n : ℝ) p ↔ p ∈ fourierConfigCube eta n := by
  rw [mem_fourierConfigCube_iff]
  unfold InP
  refine forall_congr' fun c => forall_congr' fun i => ?_
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : ((-(n : ℤ) : ℤ) : ℝ) ≤ ((p c i : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have : ((p c i : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  · rintro ⟨h1, h2⟩
    constructor
    · have : ((-(n : ℤ) : ℤ) : ℝ) ≤ ((p c i : ℤ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    · have : ((p c i : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h2
      push_cast at this; linarith

open Classical in
omit [Fintype ν] in
lemma sub_truncate_apply (n : ℕ) (x : L2 eta) (p : Cf eta) :
    (x - molecularH2Truncate n x) p = if InP (n : ℝ) p then 0 else x p := by
  rw [lp.coeFn_sub, Pi.sub_apply, molecularH2Truncate_apply]
  by_cases hp : InP (n : ℝ) p
  · rw [if_pos hp, cubicLatticeCoeffTruncate_eq_of_mem n _ p ((inP_iff_mem_cube n p).mp hp), sub_self]
  · rw [if_neg hp, cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ p
      (fun h => hp ((inP_iff_mem_cube n p).mpr h)), sub_zero]

omit [Fintype ν] in
lemma norm_sub_truncate_le (n : ℕ) (x : L2 eta) : ‖x - molecularH2Truncate n x‖ ≤ ‖x‖ := by
  have := l2_norm_le_of_le (x - molecularH2Truncate n x) x zero_le_one fun p => by
    rw [sub_truncate_apply, one_mul]
    split_ifs
    · rw [norm_zero]; exact norm_nonneg _
    · exact le_rfl
  rwa [one_mul] at this

omit [Fintype ν] in
lemma summable_norm_mul_of_sq {ι : Type*} {f g : ι → ℂ} (hf : Summable fun i => ‖f i‖ ^ 2)
    (hg : Summable fun i => ‖g i‖ ^ 2) : Summable fun i => ‖f i‖ * ‖g i‖ :=
  ((hf.add hg).mul_left (1 / 2)).of_nonneg_of_le (fun _ => by positivity) fun i => by
    nlinarith [sq_nonneg (‖f i‖ - ‖g i‖)]

open Classical in
include hKernel in
/-- Duality on the bulk block: `⟪y, V_b x⟫ = ⟪W 1_Q y, R x⟫` for `y` supported in `Q`. -/
lemma inner_Vb_of_supp (hL : 0 < L) (n : ℕ) (x y : L2 eta)
    (hy : ∀ q ∉ Qs eta n, y q = 0) :
    ⟪y, Vb sys L n hL x⟫_ℂ = ⟪Wp sys L H (liftQ L n y), x - molecularH2Truncate n x⟫_ℂ := by
  classical
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hz : ∀ q ∉ Qs eta n, ⟪y q, Vb sys L n hL x q⟫_ℂ = 0 := by
    intro q hq; rw [hy q hq]; simp
  rw [tsum_eq_sum hz]
  set F : Cf eta → Cf eta → ℂ := fun q p =>
    (if InP (n : ℝ) p then 0 else potKernel sys L q p * x p) * conj (y q) with hF
  have hrow : ∀ q ∈ Qs eta n, ⟪y q, Vb sys L n hL x q⟫_ℂ = ∑' p, F q p := by
    intro q hq
    rw [Vb_apply, RCLike.inner_apply, ← tsum_mul_right]
    refine tsum_congr fun p => ?_
    simp only [hF]
    unfold vbK
    by_cases hp : InP (n : ℝ) p
    · rw [if_neg (fun h => (inQ_not_cross_left (mem_Qs.mp hq)).mp h hp), if_pos hp]; simp
    · rw [if_pos ((inQ_not_cross_left (mem_Qs.mp hq)).mpr hp), if_neg hp]
  have hsumm : ∀ q ∈ Qs eta n, Summable (F q) := by
    intro q _
    refine Summable.of_norm_bounded (((summable_norm_mul_of_sq (summable_potKernel_sq_row sys hL q)
      (summable_sq_coord x)).mul_right ‖y q‖)) fun p => ?_
    simp only [hF, norm_mul, Complex.norm_conj]
    split_ifs
    · simp only [norm_zero, zero_mul]; positivity
    · rw [norm_mul]
  rw [Finset.sum_congr rfl hrow, ← Summable.tsum_finsetSum hsumm]
  refine tsum_congr fun p => ?_
  rw [potential_liftQ sys H hKernel hL, sub_truncate_apply, RCLike.inner_apply, map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [hF]
  rw [map_mul, potKernel_conj' (sys := sys) hL q p, Complex.conj_conj]
  split_ifs <;> ring

open Classical in
include hKernel in
/-- **`‖V_b‖ ≤ C K`.** -/
theorem norm_Vb_le (Hunit : ℝ) (hL : 0 < L)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (n : ℕ) (x : L2 eta) :
    ‖Vb sys L n hL x‖ ≤ 2 * (finiteCoulombPhysicalMassConstant sys L Hunit *
      Real.sqrt (1 + eta * gF L ^ 2 * n ^ 2 / 16)) * ‖x‖ := by
  classical
  set M := finiteCoulombPhysicalMassConstant sys L Hunit *
    Real.sqrt (1 + eta * gF L ^ 2 * n ^ 2 / 16)
  have hM : 0 ≤ M := mul_nonneg (finiteCoulombPhysicalMassConstant_nonneg sys L Hunit)
    (Real.sqrt_nonneg _)
  set v := Vb sys L n hL x
  set Bv := lpTruncate (Qs eta n) v
  set A := v - Bv
  have hBq : ∀ q, Bv q = if q ∈ Qs eta n then v q else 0 := fun q => lpTruncate_apply _ _ _
  have hBsupp : ∀ q ∉ Qs eta n, Bv q = 0 := fun q hq => by rw [hBq, if_neg hq]
  have hAq : ∀ q, A q = if q ∈ Qs eta n then 0 else v q := by
    intro q
    simp only [A, lp.coeFn_sub, Pi.sub_apply, hBq]
    split_ifs <;> simp
  -- the outgoing orientation
  have hA : ‖A‖ ≤ M * ‖x‖ := by
    have h := l2_norm_le_of_le A (Wp sys L H (liftQ L n x)) zero_le_one fun q => by
      rw [hAq, one_mul]
      split_ifs with hq
      · rw [norm_zero]; exact norm_nonneg _
      · rw [Vb_apply_out sys H hKernel hL n x (fun h => hq (mem_Qs.mpr h))]
        split_ifs
        · rw [norm_zero]; exact norm_nonneg _
        · exact le_rfl
    rw [one_mul] at h
    exact h.trans (norm_W_liftQ_le sys H hKernel Hunit hL hPeriodic n x)
  -- the incoming orientation, by duality
  have hB : ‖Bv‖ ≤ M * ‖x‖ := by
    have hdisj : ⟪Bv, A⟫_ℂ = 0 := by
      rw [lp.inner_eq_tsum]
      refine (tsum_congr fun q => ?_).trans tsum_zero
      by_cases hq : q ∈ Qs eta n
      · rw [hAq, if_pos hq]; simp
      · rw [hBsupp q hq]; simp
    have hdual := inner_Vb_of_supp sys H hKernel hL n x Bv hBsupp
    have hvs : v = Bv + A := by simp only [A]; abel
    rw [show Vb sys L n hL x = v from rfl, hvs, inner_add_right, hdisj, add_zero] at hdual
    have h1 : ‖Bv‖ ^ 2 ≤ M * ‖Bv‖ * ‖x‖ := by
      have := congrArg norm hdual
      have hn : ‖⟪Bv, Bv⟫_ℂ‖ = ‖Bv‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K, norm_pow]; simp
      rw [hn] at this
      rw [this]
      refine (norm_inner_le_norm _ _).trans ?_
      exact mul_le_mul (norm_W_liftQ_le sys H hKernel Hunit hL hPeriodic n Bv)
        (norm_sub_truncate_le n x) (norm_nonneg _) (by positivity)
    by_cases h0 : ‖Bv‖ = 0
    · rw [h0]; positivity
    · have hpos : 0 < ‖Bv‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  calc ‖v‖ = ‖A + Bv‖ := by simp only [A]; rw [sub_add_cancel]
    _ ≤ ‖A‖ + ‖Bv‖ := norm_add_le _ _
    _ ≤ 2 * M * ‖x‖ := by linarith

end FSNormal
