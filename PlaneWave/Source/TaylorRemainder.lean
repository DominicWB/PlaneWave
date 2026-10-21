import PlaneWave.Source.PotentialTails

/-!
# Flux/source build, block 5: vector Taylor expansions and the first-rotation remainder

**Vector Taylor bounds** (`FSConj`, any skew-adjoint `Z` on a Hilbert space): with the iterated
commutators `ad_Z^k X` (`adk`) and the Taylor polynomial `tp Z X k r = Σ_{j<k} r^j/j! ad^j X` of
`e^{rZ} X e^{-rZ}`,

* `norm_cj_sub_tp_apply_le`:
  `‖(e^{rZ} X e^{-rZ} - tp_k(r)) u‖ ≤ r^k/k! (‖ad^k X u‖ + ‖ad^k X‖ ‖Z u‖)` on `[0, 1]`;
* `norm_Bi_sub_bp_apply_le`: the averaged version
  `‖(∫₀¹ e^{rZ} X e^{-rZ} dr - Σ_{j<k} ad^j X/(j+1)!) u‖ ≤ (‖ad^k X u‖ + ‖ad^k X‖ ‖Z u‖)/(k+1)!`.

The rotated vector `e^{-rZ} u` is never asserted to be good: only `u` and the operator norm of
the `k`-th commutator enter (`lem:bounded-observable-higher`, "a generator on an already rotated
datum is controlled by its operator commutator").
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin NormedSpace
  MeasureTheory

namespace FSConj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The iterated commutator `ad_Z^k X`. -/
def adk (Z X : E →L[ℂ] E) : ℕ → E →L[ℂ] E
  | 0 => X
  | k + 1 => cm Z (adk Z X k)

omit [CompleteSpace E] in
@[simp] lemma adk_zero (Z X : E →L[ℂ] E) : adk Z X 0 = X := rfl

omit [CompleteSpace E] in
lemma adk_succ (Z X : E →L[ℂ] E) (k : ℕ) : adk Z X (k + 1) = cm Z (adk Z X k) := rfl

omit [CompleteSpace E] in
lemma adk_succ' (Z X : E →L[ℂ] E) (k : ℕ) : adk Z X (k + 1) = adk Z (cm Z X) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [adk_succ, ih, adk_succ]

omit [CompleteSpace E] in
lemma norm_cm_le' (Z X : E →L[ℂ] E) : ‖cm Z X‖ ≤ 2 * ‖Z‖ * ‖X‖ := by
  unfold cm
  calc ‖Z * X - X * Z‖ ≤ ‖Z * X‖ + ‖X * Z‖ := norm_sub_le _ _
    _ ≤ ‖Z‖ * ‖X‖ + ‖X‖ * ‖Z‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖Z‖ * ‖X‖ := by ring

omit [CompleteSpace E] in
lemma norm_adk_le (Z X : E →L[ℂ] E) (k : ℕ) : ‖adk Z X k‖ ≤ (2 * ‖Z‖) ^ k * ‖X‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [adk_succ]
    calc ‖cm Z (adk Z X k)‖ ≤ 2 * ‖Z‖ * ‖adk Z X k‖ := norm_cm_le' _ _
      _ ≤ 2 * ‖Z‖ * ((2 * ‖Z‖) ^ k * ‖X‖) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (2 * ‖Z‖) ^ (k + 1) * ‖X‖ := by ring

omit [CompleteSpace E] in
lemma adk_add (Z X Y : E →L[ℂ] E) (k : ℕ) : adk Z (X + Y) k = adk Z X k + adk Z Y k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [adk_succ, adk_succ, adk_succ, ih]; unfold cm; noncomm_ring

/-- The Taylor polynomial `Σ_{j<k} r^j/j! ad_Z^j X` of `e^{rZ} X e^{-rZ}`. -/
noncomputable def tp (Z X : E →L[ℂ] E) (k : ℕ) (r : ℝ) : E →L[ℂ] E :=
  ∑ j ∈ Finset.range k, (((r ^ j / (j.factorial : ℝ) : ℝ)) : ℂ) • adk Z X j

omit [CompleteSpace E] in
lemma tp_zero (Z X : E →L[ℂ] E) (r : ℝ) : tp Z X 0 r = 0 := by simp [tp]

omit [CompleteSpace E] in
lemma tp_succ_at_zero (Z X : E →L[ℂ] E) (k : ℕ) : tp Z X (k + 1) 0 = X := by
  rw [tp, Finset.sum_range_succ']
  simp

lemma hasDerivAt_tp (Z X : E →L[ℂ] E) (k : ℕ) (r : ℝ) :
    HasDerivAt (fun r => tp Z X (k + 1) r) (tp Z (cm Z X) k r) r := by
  have hsplit : (fun r => tp Z X (k + 1) r) = fun r =>
      (∑ j ∈ Finset.range k, (((r ^ (j + 1) / ((j + 1).factorial : ℝ) : ℝ)) : ℂ) • adk Z X (j + 1)) +
        X := by
    funext r
    rw [tp, Finset.sum_range_succ']
    simp
  rw [hsplit]
  have hterm : ∀ j ∈ Finset.range k, HasDerivAt
      (fun r : ℝ => (((r ^ (j + 1) / ((j + 1).factorial : ℝ) : ℝ)) : ℂ) • adk Z X (j + 1))
      ((((r ^ j / (j.factorial : ℝ) : ℝ)) : ℂ) • adk Z (cm Z X) j) r := by
    intro j _
    have h1 : HasDerivAt (fun r : ℝ => r ^ (j + 1) / ((j + 1).factorial : ℝ))
        (((j + 1 : ℕ) : ℝ) * r ^ j / ((j + 1).factorial : ℝ)) r := by
      simpa using (hasDerivAt_pow (j + 1) r).div_const ((j + 1).factorial : ℝ)
    have h2 := h1.ofReal_comp.smul_const (adk Z X (j + 1))
    refine h2.congr_deriv ?_
    rw [adk_succ']
    congr 1
    have hf : (j.factorial : ℝ) ≠ 0 := by positivity
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  have hsum := HasDerivAt.fun_sum hterm
  have hc : HasDerivAt (fun _ : ℝ => X) 0 r := hasDerivAt_const r X
  refine (hsum.add hc).congr_deriv ?_
  rw [add_zero, tp]

lemma continuous_tp (Z X : E →L[ℂ] E) (k : ℕ) : Continuous fun r => tp Z X k r := by
  unfold tp
  refine continuous_finsetSum _ fun j _ => ?_
  exact (Complex.continuous_ofReal.comp ((continuous_pow j).div_const _)).smul continuous_const

/-- **The vector Taylor bound** for the conjugate on `[0, 1]`:
`‖(e^{rZ} X e^{-rZ} - tp_k(r)) u‖ ≤ r^k/k! (‖ad^k X u‖ + ‖ad^k X‖ ‖Z u‖)`. -/
theorem norm_cj_sub_tp_apply_le {Z : E →L[ℂ] E} (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (k : ℕ)
    (X : E →L[ℂ] E) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) (u : E) :
    ‖(cj Z r X - tp Z X k r) u‖ ≤
      r ^ k / k.factorial * (‖adk Z X k u‖ + ‖adk Z X k‖ * ‖Z u‖) := by
  induction k generalizing X r with
  | zero =>
    rw [tp_zero, sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul, adk_zero]
    have e : cj Z r X u = ex Z r (X (ex Z (-r) u)) := by
      simp only [cj, mul_apply_eq_comp]
    rw [e, norm_ex_apply hZ]
    have h1 : ‖X (ex Z (-r) u) - X u‖ ≤ ‖X‖ * ‖Z u‖ := by
      rw [← map_sub]
      refine (X.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      refine (norm_ex_sub_apply_le hZ (-r) u).trans ?_
      rw [abs_neg, abs_of_nonneg hr.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hr.2
    have h2 : ‖X (ex Z (-r) u)‖ ≤ ‖X u‖ + ‖X (ex Z (-r) u) - X u‖ := by
      have := norm_add_le (X u) (X (ex Z (-r) u) - X u)
      rwa [add_sub_cancel] at this
    linarith
  | succ k ih =>
    set B := ‖adk Z X (k + 1) u‖ + ‖adk Z X (k + 1)‖ * ‖Z u‖ with hB
    have hB0 : 0 ≤ B := by positivity
    have hf : ∀ ρ, HasDerivAt (fun ρ => (cj Z ρ X - tp Z X (k + 1) ρ) u)
        ((cj Z ρ (cm Z X) - tp Z (cm Z X) k ρ) u) ρ := by
      intro ρ
      have h1 := (hasDerivAt_cj (Z := Z) X ρ).sub (hasDerivAt_tp Z X k ρ)
      have h2 := ((ContinuousLinearMap.apply ℂ E u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
        ρ h1
      simpa [Function.comp_def] using h2
    have hbound : ∀ ρ ∈ Set.Ico (0 : ℝ) r,
        ‖(cj Z ρ (cm Z X) - tp Z (cm Z X) k ρ) u‖ ≤ ρ ^ k / k.factorial * B := by
      intro ρ hρ
      have h := ih (cm Z X) (r := ρ) ⟨hρ.1, hρ.2.le.trans hr.2⟩
      rwa [← adk_succ'] at h
    have h0 : ‖(cj Z 0 X - tp Z X (k + 1) 0) u‖ ≤
        (0 : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) * B := by
      rw [cj_zero, tp_succ_at_zero, sub_self]; simp
    have hB' : ∀ ρ, HasDerivAt (fun ρ : ℝ => ρ ^ (k + 1) / ((k + 1).factorial : ℝ) * B)
        (ρ ^ k / (k.factorial : ℝ) * B) ρ := by
      intro ρ
      have := ((hasDerivAt_pow (k + 1) ρ).div_const ((k + 1).factorial : ℝ)).mul_const B
      refine this.congr_deriv ?_
      have hf : (k.factorial : ℝ) ≠ 0 := by positivity
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := r)
      (f := fun ρ => (cj Z ρ X - tp Z X (k + 1) ρ) u)
      (fun ρ _ => (hf ρ).continuousAt.continuousWithinAt) (fun ρ _ => (hf ρ).hasDerivWithinAt)
      h0 hB' hbound ⟨hr.1, le_rfl⟩
    simpa only [Nat.cast_add, Nat.cast_one] using this

/-- The averaged Taylor polynomial `Σ_{j<k} ad^j X/(j+1)!` of `∫₀¹ e^{rZ} X e^{-rZ} dr`. -/
noncomputable def bp (Z X : E →L[ℂ] E) (k : ℕ) : E →L[ℂ] E :=
  ∑ j ∈ Finset.range k, (((1 / ((j + 1).factorial : ℝ) : ℝ)) : ℂ) • adk Z X j

lemma integral_tp (Z X : E →L[ℂ] E) (k : ℕ) : ∫ r in (0 : ℝ)..1, tp Z X k r = bp Z X k := by
  unfold tp bp
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_div, integral_pow]
    congr 2
    have hf : (j.factorial : ℝ) ≠ 0 := by positivity
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · intro j _
    exact ((Complex.continuous_ofReal.comp ((continuous_pow j).div_const _)).smul
      continuous_const).intervalIntegrable 0 1

/-- **The averaged vector Taylor bound**:
`‖(Bi Z X - Σ_{j<k} ad^j X/(j+1)!) u‖ ≤ (‖ad^k X u‖ + ‖ad^k X‖ ‖Z u‖)/(k+1)!`. -/
theorem norm_Bi_sub_bp_apply_le {Z : E →L[ℂ] E} (hZ : Z ∈ skewAdjoint (E →L[ℂ] E)) (k : ℕ)
    (X : E →L[ℂ] E) (u : E) :
    ‖(Bi Z X - bp Z X k) u‖ ≤
      1 / ((k + 1).factorial : ℝ) * (‖adk Z X k u‖ + ‖adk Z X k‖ * ‖Z u‖) := by
  set B := ‖adk Z X k u‖ + ‖adk Z X k‖ * ‖Z u‖ with hB
  have hB0 : 0 ≤ B := by positivity
  have hint : IntervalIntegrable (fun r => cj Z r X - tp Z X k r) volume 0 1 :=
    ((continuous_cj X).sub (continuous_tp Z X k)).intervalIntegrable 0 1
  have e1 : Bi Z X - bp Z X k = ∫ r in (0 : ℝ)..1, (cj Z r X - tp Z X k r) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_cj X 0 1)
      ((continuous_tp Z X k).intervalIntegrable 0 1), integral_tp]
    rfl
  have e2 : (Bi Z X - bp Z X k) u = ∫ r in (0 : ℝ)..1, (cj Z r X - tp Z X k r) u := by
    rw [e1, ContinuousLinearMap.intervalIntegral_apply hint]
  rw [e2]
  have hg : IntervalIntegrable (fun r : ℝ => r ^ k / (k.factorial : ℝ) * B) volume 0 1 :=
    (((continuous_pow k).div_const _).mul continuous_const).intervalIntegrable 0 1
  have hle := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (f := fun r => (cj Z r X - tp Z X k r) u) (g := fun r => r ^ k / (k.factorial : ℝ) * B)
    (Filter.Eventually.of_forall fun r hr =>
      norm_cj_sub_tp_apply_le hZ k X ⟨hr.1.le, hr.2⟩ u) hg
  refine hle.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div, integral_pow]
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

omit [CompleteSpace E] in
lemma bp_three (Z X : E →L[ℂ] E) :
    bp Z X 3 = X + (1 / 2 : ℂ) • cm Z X + (1 / 6 : ℂ) • cm Z (cm Z X) := by
  simp only [bp, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, adk_zero, adk_succ]
  norm_num [Nat.factorial]

omit [CompleteSpace E] in
lemma adk_two (Z X : E →L[ℂ] E) : adk Z X 2 = Z * Z * X - 2 • (Z * X * Z) + X * Z * Z := by
  simp only [adk_succ, adk_zero, cm]; noncomm_ring

omit [CompleteSpace E] in
lemma adk_three (Z X : E →L[ℂ] E) :
    adk Z X 3 = Z * Z * Z * X - 3 • (Z * Z * X * Z) + 3 • (Z * X * Z * Z) - X * Z * Z * Z := by
  simp only [adk_succ, adk_zero, cm]; noncomm_ring

end FSConj

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

/-! ## Block structure of `Σ_b` and `V_b` -/

open Classical in
/-- `V_b` maps `ran R` into `ran Q ⊂ ran P`. -/
lemma Vb_trunc_of_R (y : L2 eta) (hy : molecularH2Truncate n y = 0) :
    molecularH2Truncate n (Vb sys L n hL y) = Vb sys L n hL y := by
  ext q
  rw [molecularH2Truncate_apply]
  by_cases hq : q ∈ fourierConfigCube eta n
  · rw [cubicLatticeCoeffTruncate_eq_of_mem n _ q hq]
  · rw [cubicLatticeCoeffTruncate_eq_zero_of_not_mem n _ q hq, Vb_apply]
    have hqP : ¬ InP (n : ℝ) q := fun h => hq ((inP_iff_mem_cube n q).mp h)
    symm
    refine (tsum_congr fun p => ?_).trans tsum_zero
    unfold vbK
    split_ifs with hc
    · rcases hc with ⟨hq', -⟩ | ⟨-, hp⟩
      · exact absurd (hq'.inP (Nat.cast_nonneg n)) hqP
      · have hpP : p ∈ fourierConfigCube eta n :=
          (inP_iff_mem_cube n p).mp (hp.inP (Nat.cast_nonneg n))
        have := congrArg (fun z : L2 eta => z p) hy
        simp only [molecularH2Truncate_apply, cubicLatticeCoeffTruncate_eq_of_mem n _ p hpP,
          lp.coeFn_zero, Pi.zero_apply] at this
        rw [this, mul_zero]
    · rw [zero_mul]

open Classical in
/-- `Σ_b` maps `ran R` into `ran Q ⊂ ran P`. -/
lemma sig_trunc_of_R (y : L2 eta) (hy : molecularH2Truncate n y = 0) :
    molecularH2Truncate n (Sig sys L n hL hn y) = Sig sys L n hL hn y := by
  have h := sig_exterior sys hL hn y
  have hQ : lpTruncate (Qs eta n) y = 0 := by
    ext q
    rw [lpTruncate_apply, lp.coeFn_zero, Pi.zero_apply]
    split_ifs with hq
    · have hqP : q ∈ fourierConfigCube eta n :=
        (inP_iff_mem_cube n q).mp ((mem_Qs.mp hq).inP (Nat.cast_nonneg n))
      have := congrArg (fun z : L2 eta => z q) hy
      simp only [molecularH2Truncate_apply, cubicLatticeCoeffTruncate_eq_of_mem n _ q hqP,
        lp.coeFn_zero, Pi.zero_apply] at this
      exact this
    · rfl
  rw [hQ, map_zero, sub_eq_zero] at h
  exact h.symm

/-- `Σ_b` maps `ran P` into `ran R`. -/
lemma trunc_sig_of_P (x : L2 eta) (hx : molecularH2Truncate n x = x) :
    molecularH2Truncate n (Sig sys L n hL hn x) = 0 := by
  rw [sig_interior sys hL hn x, hx, sub_self, map_zero]

/-- **`P ad²_{Σ_b}(V_b) P = 0`**: every word of `[Σ_b, [Σ_b, V_b]]` leaves the cube. -/
theorem ext_ad2_Vb (v : En eta n) :
    ext eta n (FSConj.adk (Sig sys L n hL hn) (Vb sys L n hL) 2 (emb eta n v)) = 0 := by
  set Sg := Sig sys L n hL hn
  set V := Vb sys L n hL
  set e := emb eta n v
  have he : molecularH2Truncate n e = e := trunc_emb v
  -- the three words
  have w1 : molecularH2Truncate n (Sg (Sg (V e))) = 0 := by
    have h1 := PVbP sys hL e he
    have h2 := sig_trunc_of_R sys hL hn (V e) h1
    exact trunc_sig_of_P sys hL hn _ h2
  have w2 : molecularH2Truncate n (Sg (V (Sg e))) = 0 := by
    have h1 := trunc_sig_of_P sys hL hn e he
    have h2 := Vb_trunc_of_R sys hL (Sg e) h1
    exact trunc_sig_of_P sys hL hn _ h2
  have w3 : molecularH2Truncate n (V (Sg (Sg e))) = 0 := by
    have h1 := trunc_sig_of_P sys hL hn e he
    have h2 := sig_trunc_of_R sys hL hn (Sg e) h1
    exact PVbP sys hL _ h2
  have hext : ∀ x : L2 eta, molecularH2Truncate n x = 0 → ext eta n x = 0 := by
    intro x hx; rw [← extract_truncate n, hx, map_zero]
  rw [FSConj.adk_two]
  simp only [sub_apply, add_apply, mul_apply_eq_comp, smul_apply, map_sub,
    map_add, map_nsmul]
  rw [hext _ w1, hext _ w2, hext _ w3]
  simp

/-! ## The first-rotation expansion of `ΔH = P B P` -/

/-- The third-order retained word of the first rotation, `P H^{(3)} P = -½ P [Σ_b, Z] P`. -/
noncomputable def H3first : En eta n →L[ℂ] En eta n :=
  (-(1 / 2 : ℂ)) • (ext eta n ∘L FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) ∘L emb eta n)

/-- The fourth- and higher-order remainder of `P B P`:
`-P ((1/6) [Σ_b, [Σ_b, Z]] + R₄) P`, `R₄ = Bi Σ X₁ - (X₁ + ½[Σ, X₁] + ⅙[Σ, [Σ, X₁]])`. -/
noncomputable def DH4 : En eta n →L[ℂ] En eta n :=
  -(ext eta n ∘L ((1 / 6 : ℂ) • FSConj.adk (Sig sys L n hL hn) (Zsym sys hL hn H) 2 +
    (FSConj.Bi (Sig sys L n hL hn) (X1 sys hL hn H) -
      FSConj.bp (Sig sys L n hL hn) (X1 sys hL hn H) 3)) ∘L emb eta n)

/-- **The first-rotation ledger**: `ΔH = H₂^bb + H₂^mix + P H^{(3)} P + ΔH_{≥4}` (the full
`H₂^{PP}` of eq:H2PP, its third-order successor, and the exact remainder). -/
theorem dH_decomp (v : En eta n) :
    dH sys hL hn H v = Hbb sys hL hn v + Hmix sys hL hn H v + H3first sys hL hn H v +
      DH4 sys hL hn H v := by
  set Sg := Sig sys L n hL hn
  set V := Vb sys L n hL
  set Z := Zsym sys hL hn H
  set e := emb eta n v
  have hX : X1 sys hL hn H = V + Z := by simp only [X1, Z, Zsym, V]; abel
  have hV0 : ext eta n (V e) = 0 := by
    have h := PVbP sys hL (n := n) e (trunc_emb v)
    rw [← extract_truncate n, h, map_zero]
  have hV2 := ext_ad2_Vb sys hL hn v
  set X := X1 sys hL hn H
  set R := FSConj.Bi Sg X - FSConj.bp Sg X 3
  have e1 : dH sys hL hn H v = -ext eta n (X e) - (1 / 2 : ℂ) • ext eta n (FSConj.cm Sg X e) -
      (1 / 6 : ℂ) • ext eta n (FSConj.cm Sg (FSConj.cm Sg X) e) - ext eta n (R e) := by
    have hBi : FSConj.Bi Sg X = FSConj.bp Sg X 3 + R := by simp only [R]; abel
    rw [dH_apply, Bcorr, neg_apply, hBi, add_apply, FSConj.bp_three]
    simp only [add_apply, smul_apply, map_add, map_smul, map_neg]
    abel
  have e2 : ext eta n (X e) = ext eta n (Z e) := by
    rw [hX, add_apply, map_add, hV0, zero_add]
  have e3 : ext eta n (FSConj.cm Sg X e) = ext eta n (FSConj.cm Sg V e) + ext eta n (FSConj.cm Sg Z e) := by
    rw [hX, cm_add, add_apply, map_add]
  have e4 : ext eta n (FSConj.cm Sg (FSConj.cm Sg X) e) = ext eta n (FSConj.cm Sg (FSConj.cm Sg Z) e) := by
    have h2V : ext eta n (FSConj.cm Sg (FSConj.cm Sg V) e) = 0 := hV2
    rw [hX, cm_add, cm_add, add_apply, map_add, h2V, zero_add]
  have hbb : Hbb sys hL hn v = (1 / 2 : ℂ) • ext eta n (FSConj.cm Sg V e) := by
    simp only [Hbb, smul_apply, ContinuousLinearMap.comp_apply]; rfl
  have hmix : Hmix sys hL hn H v = -ext eta n (Z e) - ext eta n (FSConj.cm Sg V e) := by
    simp only [Hmix, ContinuousLinearMap.comp_apply, sub_apply, neg_apply, map_sub, map_neg]; rfl
  have h3 : H3first sys hL hn H v = -(1 / 2 : ℂ) • ext eta n (FSConj.cm Sg Z e) := by
    simp only [H3first, smul_apply, ContinuousLinearMap.comp_apply]; rfl
  have h4 : DH4 sys hL hn H v = -((1 / 6 : ℂ) • ext eta n (FSConj.cm Sg (FSConj.cm Sg Z) e) +
      ext eta n (R e)) := by
    simp only [DH4, neg_apply, ContinuousLinearMap.comp_apply, add_apply, smul_apply, map_add,
      map_smul]; rfl
  rw [e1, e2, e3, e4, hbb, hmix, h3, h4]
  module

/-! ## Vector bounds on cube vectors -/

/-- `‖Z v‖ ≤ z_c Θ(v)` with `z_c = 2 C_m a₁ + A_σ √2 C_m`. -/
noncomputable def zc (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  2 * finiteCoulombPhysicalMassConstant sys L Hunit * a1c sys L n +
    Asig sys L n * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit)

include hKernel in
lemma norm_Zsym_emb_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖Zsym sys hL hn H (emb eta n v)‖ ≤
      zc sys L Hunit n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  have h1 := norm_Zw_emb_le sys hL hn H hKernel Hunit hPeriodic v
  have h2 := norm_Zw_adj_emb_le sys hL hn H hKernel Hunit hPeriodic v
  unfold Zsym zc
  rw [add_apply]
  refine (norm_add_le _ _).trans ?_
  linarith

/-- The relative constant of `‖ΔH_{≥4} v‖ ≤ α₄ Θ(v)`, `α₄ = O(K^{-3})`. -/
noncomputable def alpha4 (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  1 / 6 * (Asig sys L n ^ 2 * zc sys L Hunit n +
      3 * (Asig sys L n * (2 * CZ sys L Hunit n) * (2 * a0c sys L n))) +
    1 / 24 * (Asig sys L n ^ 3 * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit) +
      7 * (Asig sys L n ^ 2 * CV sys L Hunit n * (2 * a0c sys L n)) +
      (2 * Asig sys L n) ^ 2 * (2 * Asig sys L n) * (2 * CZ sys L Hunit n) +
      (2 * Asig sys L n) ^ 3 * CX sys L Hunit n * (2 * a0c sys L n))

include hKernel in
/-- **The first-rotation remainder on cube vectors**: `‖ΔH_{≥4} v‖ ≤ α₄ Θ(v)`.  The words of
commutator degree three in `V_b` are bounded word by word (`Σ_b³ V_b`, `Σ_b² V_b Σ_b`, ...), using
`‖V_b v‖ ≤ √2 C_m Θ(v)` and `‖Σ_b v‖ ≤ 2 a₀ Θ(v)`; the rest has operator norm `O(K^{-3})`. -/
theorem norm_DH4_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖DH4 sys hL hn H v‖ ≤ alpha4 sys L Hunit n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  set Sg := Sig sys L n hL hn
  set V := Vb sys L n hL
  set Z := Zsym sys hL hn H
  set X := X1 sys hL hn H
  set e := emb eta n v
  set Θ := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖
  set A := Asig sys L n
  have hA : ‖Sg‖ ≤ A := norm_Sig_le hL hn
  have hA0 : 0 ≤ A := Asig_nonneg hL
  have hΘ0 : 0 ≤ Θ := norm_nonneg _
  have he : ‖e‖ ≤ Θ := by rw [norm_emb]; exact norm_le_wt sys L n zero_le_one v
  have hZ : ‖Z‖ ≤ 2 * CZ sys L Hunit n := norm_Zsym_le sys hL hn H Hunit hPeriodic hKernel
  have hZ0 : 0 ≤ CZ sys L Hunit n := CZ_nonneg sys Hunit
  have hVo : ‖V‖ ≤ CV sys L Hunit n := opNorm_Vb_le sys hL H hKernel Hunit hPeriodic
  have hV0 : 0 ≤ CV sys L Hunit n := CV_nonneg sys Hunit
  have hXo : ‖X‖ ≤ CX sys L Hunit n := norm_X1_le sys hL hn H hKernel Hunit hPeriodic
  have hX0 : 0 ≤ CX sys L Hunit n := le_trans (norm_nonneg _) hXo
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have ha0 := a0c_nonneg sys (L := L) (n := n)
  have ha1 := a1c_nonneg sys (L := L) (n := n)
  have hzc : 0 ≤ zc sys L Hunit n := by unfold zc; positivity
  have hZe : ‖Z e‖ ≤ zc sys L Hunit n * Θ := norm_Zsym_emb_le sys hL hn H hKernel Hunit hPeriodic v
  have hSe : ‖Sg e‖ ≤ 2 * a0c sys L n * Θ := norm_sig_emb_le' sys hL hn v
  have hVe : ‖V e‖ ≤ Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * Θ :=
    norm_Vb_emb_le sys hL H hKernel Hunit hPeriodic v
  have hop : ∀ (T : L2 eta →L[ℂ] L2 eta) (x : L2 eta), ‖T x‖ ≤ ‖T‖ * ‖x‖ := fun T x => T.le_opNorm x
  -- `ad² Z`
  have h2Z : ‖FSConj.adk Sg Z 2 e‖ ≤ A ^ 2 * (zc sys L Hunit n * Θ) +
      3 * (A * (2 * CZ sys L Hunit n) * (2 * a0c sys L n * Θ)) := by
    rw [FSConj.adk_two]
    simp only [sub_apply, add_apply, mul_apply_eq_comp, two_nsmul]
    have k1 : ‖Sg (Sg (Z e))‖ ≤ A ^ 2 * (zc sys L Hunit n * Θ) := by
      calc ‖Sg (Sg (Z e))‖ ≤ A * (A * (zc sys L Hunit n * Θ)) :=
            (hop _ _).trans (mul_le_mul hA ((hop _ _).trans (mul_le_mul hA hZe (norm_nonneg _) hA0))
              (norm_nonneg _) hA0)
        _ = _ := by ring
    have k2 : ‖Sg (Z (Sg e))‖ ≤ A * (2 * CZ sys L Hunit n) * (2 * a0c sys L n * Θ) := by
      calc ‖Sg (Z (Sg e))‖ ≤ A * (2 * CZ sys L Hunit n * (2 * a0c sys L n * Θ)) :=
            (hop _ _).trans (mul_le_mul hA ((hop _ _).trans (mul_le_mul hZ hSe (norm_nonneg _)
              (by positivity))) (norm_nonneg _) hA0)
        _ = _ := by ring
    have k3 : ‖Z (Sg (Sg e))‖ ≤ A * (2 * CZ sys L Hunit n) * (2 * a0c sys L n * Θ) := by
      calc ‖Z (Sg (Sg e))‖ ≤ 2 * CZ sys L Hunit n * (A * (2 * a0c sys L n * Θ)) :=
            (hop _ _).trans (mul_le_mul hZ ((hop _ _).trans (mul_le_mul hA hSe (norm_nonneg _) hA0))
              (norm_nonneg _) (by positivity))
        _ = _ := by ring
    calc ‖Sg (Sg (Z e)) - (Sg (Z (Sg e)) + Sg (Z (Sg e))) + Z (Sg (Sg e))‖
        ≤ ‖Sg (Sg (Z e))‖ + (‖Sg (Z (Sg e))‖ + ‖Sg (Z (Sg e))‖) + ‖Z (Sg (Sg e))‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
            (add_le_add le_rfl (norm_add_le _ _))) le_rfl)
      _ ≤ _ := by linarith
  -- `ad³ V_b`
  have h3V : ‖FSConj.adk Sg V 3 e‖ ≤ A ^ 3 * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * Θ) +
      7 * (A ^ 2 * CV sys L Hunit n * (2 * a0c sys L n * Θ)) := by
    rw [FSConj.adk_three]
    simp only [sub_apply, add_apply, mul_apply_eq_comp, smul_apply]
    set s3 := 2 * a0c sys L n * Θ
    have hs3 : 0 ≤ s3 := by positivity
    have k1 : ‖Sg (Sg (Sg (V e)))‖ ≤ A ^ 3 * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * Θ) := by
      calc ‖Sg (Sg (Sg (V e)))‖ ≤ A * (A * (A * (Real.sqrt 2 *
            finiteCoulombPhysicalMassConstant sys L Hunit * Θ))) :=
            (hop _ _).trans (mul_le_mul hA ((hop _ _).trans (mul_le_mul hA ((hop _ _).trans
              (mul_le_mul hA hVe (norm_nonneg _) hA0)) (norm_nonneg _) hA0)) (norm_nonneg _) hA0)
        _ = _ := by ring
    have k2 : ‖Sg (Sg (V (Sg e)))‖ ≤ A ^ 2 * CV sys L Hunit n * s3 := by
      calc ‖Sg (Sg (V (Sg e)))‖ ≤ A * (A * (CV sys L Hunit n * s3)) :=
            (hop _ _).trans (mul_le_mul hA ((hop _ _).trans (mul_le_mul hA ((hop _ _).trans
              (mul_le_mul hVo hSe (norm_nonneg _) hV0)) (norm_nonneg _) hA0)) (norm_nonneg _) hA0)
        _ = _ := by ring
    have k3 : ‖Sg (V (Sg (Sg e)))‖ ≤ A ^ 2 * CV sys L Hunit n * s3 := by
      calc ‖Sg (V (Sg (Sg e)))‖ ≤ A * (CV sys L Hunit n * (A * s3)) :=
            (hop _ _).trans (mul_le_mul hA ((hop _ _).trans (mul_le_mul hVo ((hop _ _).trans
              (mul_le_mul hA hSe (norm_nonneg _) hA0)) (norm_nonneg _) hV0)) (norm_nonneg _) hA0)
        _ = _ := by ring
    have k4 : ‖V (Sg (Sg (Sg e)))‖ ≤ A ^ 2 * CV sys L Hunit n * s3 := by
      calc ‖V (Sg (Sg (Sg e)))‖ ≤ CV sys L Hunit n * (A * (A * s3)) :=
            (hop _ _).trans (mul_le_mul hVo ((hop _ _).trans (mul_le_mul hA ((hop _ _).trans
              (mul_le_mul hA hSe (norm_nonneg _) hA0)) (norm_nonneg _) hA0)) (norm_nonneg _) hV0)
        _ = _ := by ring
    have k2' : ‖(3 : ℕ) • Sg (Sg (V (Sg e)))‖ ≤ 3 * (A ^ 2 * CV sys L Hunit n * s3) :=
      norm_nsmul_le.trans (by push_cast; linarith)
    have k3' : ‖(3 : ℕ) • Sg (V (Sg (Sg e)))‖ ≤ 3 * (A ^ 2 * CV sys L Hunit n * s3) :=
      norm_nsmul_le.trans (by push_cast; linarith)
    calc ‖Sg (Sg (Sg (V e))) - 3 • Sg (Sg (V (Sg e))) + 3 • Sg (V (Sg (Sg e))) - V (Sg (Sg (Sg e)))‖
        ≤ ‖Sg (Sg (Sg (V e)))‖ + ‖3 • Sg (Sg (V (Sg e)))‖ + ‖3 • Sg (V (Sg (Sg e)))‖ +
            ‖V (Sg (Sg (Sg e)))‖ := by
          refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := by linarith
  -- the remainder `R₄`
  have hR : ‖(FSConj.Bi Sg X - FSConj.bp Sg X 3) e‖ ≤ 1 / 24 *
      (A ^ 3 * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit * Θ) +
        7 * (A ^ 2 * CV sys L Hunit n * (2 * a0c sys L n * Θ)) +
        (2 * A) ^ 2 * (2 * A) * (2 * CZ sys L Hunit n) * Θ +
        (2 * A) ^ 3 * CX sys L Hunit n * (2 * a0c sys L n * Θ)) := by
    have hskew := (Sig_skew_unitary (sys := sys) hL hn).1
    have h := FSConj.norm_Bi_sub_bp_apply_le hskew 3 X e
    have hf : ((3 + 1).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    have hXV : X = V + Z := by simp only [X, X1, Z, Zsym, V]; abel
    have hadk : FSConj.adk Sg X 3 e = FSConj.adk Sg V 3 e + FSConj.adk Sg Z 3 e := by
      rw [hXV, FSConj.adk_add, add_apply]
    have hZ3 : ‖FSConj.adk Sg Z 3 e‖ ≤ (2 * A) ^ 2 * (2 * A) * (2 * CZ sys L Hunit n) * Θ := by
      refine (hop _ _).trans ?_
      have := FSConj.norm_adk_le Sg Z 3
      calc ‖FSConj.adk Sg Z 3‖ * ‖e‖ ≤ (2 * ‖Sg‖) ^ 3 * ‖Z‖ * Θ :=
            mul_le_mul this he (norm_nonneg _) (by positivity)
        _ ≤ (2 * A) ^ 3 * (2 * CZ sys L Hunit n) * Θ := by gcongr
        _ = _ := by ring
    have hX3 : ‖FSConj.adk Sg X 3‖ * ‖Sg e‖ ≤ (2 * A) ^ 3 * CX sys L Hunit n * (2 * a0c sys L n * Θ) := by
      have := FSConj.norm_adk_le Sg X 3
      calc ‖FSConj.adk Sg X 3‖ * ‖Sg e‖ ≤ (2 * ‖Sg‖) ^ 3 * ‖X‖ * (2 * a0c sys L n * Θ) :=
            mul_le_mul this hSe (norm_nonneg _) (by positivity)
        _ ≤ (2 * A) ^ 3 * CX sys L Hunit n * (2 * a0c sys L n * Θ) := by gcongr
    rw [hadk]
    have := norm_add_le (FSConj.adk Sg V 3 e) (FSConj.adk Sg Z 3 e)
    linarith
  -- assemble
  simp only [DH4, neg_apply, norm_neg, ContinuousLinearMap.comp_apply, add_apply,
    smul_apply]
  refine (norm_ext_le _).trans ((norm_add_le _ _).trans ?_)
  rw [norm_smul]
  have h6 : ‖(1 / 6 : ℂ)‖ = 1 / 6 := by norm_num
  rw [h6]
  have : 1 / 6 * ‖FSConj.adk Sg Z 2 e‖ ≤ 1 / 6 * (A ^ 2 * (zc sys L Hunit n * Θ) +
      3 * (A * (2 * CZ sys L Hunit n) * (2 * a0c sys L n * Θ))) :=
    mul_le_mul_of_nonneg_left h2Z (by norm_num)
  calc 1 / 6 * ‖FSConj.adk Sg Z 2 e‖ + ‖(FSConj.Bi Sg X - FSConj.bp Sg X 3) e‖ ≤ _ :=
        add_le_add this hR
    _ = alpha4 sys L Hunit n * Θ := by unfold alpha4; ring

/-- `‖P H^{(3)} P v‖ ≤ α₃ Θ(v)`, `α₃ = O(K^{-2})`. -/
noncomputable def alpha3 (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  1 / 2 * (Asig sys L n * zc sys L Hunit n + 2 * CZ sys L Hunit n * (2 * a0c sys L n))

include hKernel in
theorem norm_H3first_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖H3first sys hL hn H v‖ ≤ alpha3 sys L Hunit n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  set Sg := Sig sys L n hL hn
  set Z := Zsym sys hL hn H
  set e := emb eta n v
  have hA : ‖Sg‖ ≤ Asig sys L n := norm_Sig_le hL hn
  have hA0 : 0 ≤ Asig sys L n := Asig_nonneg hL
  have hZ : ‖Z‖ ≤ 2 * CZ sys L Hunit n := norm_Zsym_le sys hL hn H Hunit hPeriodic hKernel
  have hZe := norm_Zsym_emb_le sys hL hn H hKernel Hunit hPeriodic v
  have hSe := norm_sig_emb_le' sys hL hn v
  have hZ0 := CZ_nonneg sys Hunit (L := L) (n := n)
  simp only [H3first, smul_apply, ContinuousLinearMap.comp_apply, norm_smul]
  have h2 : ‖(-(1 / 2 : ℂ))‖ = 1 / 2 := by norm_num
  rw [h2]
  have hcm : ‖FSConj.cm Sg Z e‖ ≤ Asig sys L n * (zc sys L Hunit n *
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖) +
      2 * CZ sys L Hunit n * (2 * a0c sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖) := by
    unfold FSConj.cm
    rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (Sg.le_opNorm _).trans (mul_le_mul hA hZe (norm_nonneg _) hA0)
    · exact (Z.le_opNorm _).trans (mul_le_mul hZ hSe (norm_nonneg _) (by positivity))
  calc 1 / 2 * ‖ext eta n (FSConj.cm Sg Z e)‖ ≤ 1 / 2 * ‖FSConj.cm Sg Z e‖ :=
        mul_le_mul_of_nonneg_left (norm_ext_le _) (by norm_num)
    _ ≤ 1 / 2 * (Asig sys L n * (zc sys L Hunit n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖) +
        2 * CZ sys L Hunit n * (2 * a0c sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖)) :=
        mul_le_mul_of_nonneg_left hcm (by norm_num)
    _ = _ := by unfold alpha3; ring

/-- `‖H₂^bb v‖ ≤ α_bb Θ(v)`, `α_bb = O(K^{-1})`. -/
noncomputable def alphaBB (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ) : ℝ :=
  1 / 2 * (Asig sys L n * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit) +
    CV sys L Hunit n * (2 * a0c sys L n))

include hKernel in
theorem norm_Hbb_wt_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) :
    ‖Hbb sys hL hn v‖ ≤ alphaBB sys L Hunit n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  set Sg := Sig sys L n hL hn
  set V := Vb sys L n hL
  set e := emb eta n v
  have hA : ‖Sg‖ ≤ Asig sys L n := norm_Sig_le hL hn
  have hA0 : 0 ≤ Asig sys L n := Asig_nonneg hL
  have hVo : ‖V‖ ≤ CV sys L Hunit n := opNorm_Vb_le sys hL H hKernel Hunit hPeriodic
  have hV0 : 0 ≤ CV sys L Hunit n := CV_nonneg sys Hunit
  have hVe := norm_Vb_emb_le sys hL H hKernel Hunit hPeriodic v
  have hSe := norm_sig_emb_le' sys hL hn v
  simp only [Hbb, smul_apply, ContinuousLinearMap.comp_apply, norm_smul]
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h2]
  have hcm : ‖(Sg * V - V * Sg) e‖ ≤ Asig sys L n * (Real.sqrt 2 *
      finiteCoulombPhysicalMassConstant sys L Hunit * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖) +
      CV sys L Hunit n * (2 * a0c sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖) := by
    rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (Sg.le_opNorm _).trans (mul_le_mul hA hVe (norm_nonneg _) hA0)
    · exact (V.le_opNorm _).trans (mul_le_mul hVo hSe (norm_nonneg _) hV0)
  calc 1 / 2 * ‖ext eta n ((Sg * V - V * Sg) e)‖ ≤ 1 / 2 * ‖(Sg * V - V * Sg) e‖ :=
        mul_le_mul_of_nonneg_left (norm_ext_le _) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hcm (by norm_num)
    _ = _ := by unfold alphaBB; ring

include hKernel in
/-- The operator bound `‖H₂^bb‖ ≤ A_σ C_V`. -/
theorem norm_Hbb_op_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) : ‖Hbb sys hL hn v‖ ≤ Asig sys L n * CV sys L Hunit n * ‖v‖ := by
  have hA : ‖Sig sys L n hL hn‖ ≤ Asig sys L n := norm_Sig_le hL hn
  have hA0 : 0 ≤ Asig sys L n := Asig_nonneg hL
  have hVo := opNorm_Vb_le sys hL H hKernel Hunit hPeriodic (n := n)
  have hV0 : 0 ≤ CV sys L Hunit n := CV_nonneg sys Hunit
  have hc : ‖Sig sys L n hL hn * Vb sys L n hL - Vb sys L n hL * Sig sys L n hL hn‖ ≤
      2 * Asig sys L n * CV sys L Hunit n :=
    (norm_cm_le _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hVo
      (norm_nonneg _) (by positivity))
  simp only [Hbb, smul_apply, ContinuousLinearMap.comp_apply, norm_smul]
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h2]
  calc 1 / 2 * ‖ext eta n ((Sig sys L n hL hn * Vb sys L n hL - Vb sys L n hL * Sig sys L n hL hn)
        (emb eta n v))‖ ≤ 1 / 2 * (2 * Asig sys L n * CV sys L Hunit n * ‖v‖) := by
        refine mul_le_mul_of_nonneg_left ((norm_ext_le _).trans (((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right hc (norm_nonneg _))).trans (le_of_eq ?_))) (by norm_num)
        rw [norm_emb]
    _ = _ := by ring

include hKernel in
/-- The operator bound `‖P H^{(3)} P‖ ≤ 2 A_σ C_Z`. -/
theorem norm_H3first_op_le (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (v : En eta n) : ‖H3first sys hL hn H v‖ ≤ 2 * Asig sys L n * CZ sys L Hunit n * ‖v‖ := by
  have hA : ‖Sig sys L n hL hn‖ ≤ Asig sys L n := norm_Sig_le hL hn
  have hA0 : 0 ≤ Asig sys L n := Asig_nonneg hL
  have hZ := norm_Zsym_le sys hL hn H Hunit hPeriodic hKernel
  have hZ0 := CZ_nonneg sys Hunit (L := L) (n := n)
  have hc : ‖FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H)‖ ≤
      2 * Asig sys L n * (2 * CZ sys L Hunit n) :=
    (norm_cm_le _ _).trans (mul_le_mul (mul_le_mul_of_nonneg_left hA (by norm_num)) hZ
      (norm_nonneg _) (by positivity))
  simp only [H3first, smul_apply, ContinuousLinearMap.comp_apply, norm_smul]
  have h2 : ‖(-(1 / 2 : ℂ))‖ = 1 / 2 := by norm_num
  rw [h2]
  calc 1 / 2 * ‖ext eta n (FSConj.cm (Sig sys L n hL hn) (Zsym sys hL hn H) (emb eta n v))‖
      ≤ 1 / 2 * (2 * Asig sys L n * (2 * CZ sys L Hunit n) * ‖v‖) := by
        refine mul_le_mul_of_nonneg_left ((norm_ext_le _).trans (((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right hc (norm_nonneg _))).trans (le_of_eq ?_))) (by norm_num)
        rw [norm_emb]
    _ = _ := by ring

end FSNormal
