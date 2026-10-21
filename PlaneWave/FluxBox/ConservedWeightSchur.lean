import PlaneWave.FluxBox.ClassHardy

/-!
# Flux route, stage 3, part 24: conserved-weight Schur, radial and ball sums, moments

* `sum_sq_le_conserved`: Schur's test with a weight constant along the support (real form);
  `sum_sq_yj_le`: the com dressing on a channel, `Σ_f (Σ_d |y_j(f,d)| v_d)² ≤ Σ_d r_j(d)² v_d²`;
* radial sums `Σ 1/max(R², |x|²)^k ≤ 277 R^{3-2k}` (`k = 2, 3`), along the lines of a channel;
* the shifted ball sum `Σ_{|θ - c| ≤ R} 1/|θ|² ≤ 81 R`;
* same-line convolutions: `L_j(K x) ≤ S L_j(x)` when the columns of `K` are `≤ S`;
* moments: weights of degree `≤ 5` against `(1 + A)^{5/2}`, and the line squares of a good state.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Schur with a conserved weight, real form -/

section SchurReal

variable {X : Type*} [Fintype X]

omit [Fintype ν] in
/-- **Schur's test with a conserved weight** (real form): if `0 ≤ K`, `r` is constant along the
support of `K`, and the rows and columns of `K` are bounded by `r`, then
`Σ_q (Σ_p K x)² ≤ Σ_p r² x²`. -/
theorem sum_sq_le_conserved (K : X → X → ℝ) (r : X → ℝ) (x : X → ℝ)
    (hK0 : ∀ q p, 0 ≤ K q p) (hr0 : ∀ q, 0 ≤ r q)
    (hcons : ∀ q p, K q p ≠ 0 → r q = r p)
    (hrow : ∀ q, ∑ p, K q p ≤ r q) (hcol : ∀ p, ∑ q, K q p ≤ r p) :
    ∑ q, (∑ p, K q p * x p) ^ 2 ≤ ∑ p, r p ^ 2 * x p ^ 2 := by
  have hq : ∀ q, (∑ p, K q p * x p) ^ 2 ≤ r q * ∑ p, K q p * x p ^ 2 := by
    intro q
    have h2 : (∑ p, K q p * x p) ^ 2 ≤ (∑ p, K q p) * ∑ p, K q p * x p ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => hK0 q p)
        (fun p _ => by have := hK0 q p; positivity) (fun p _ => le_of_eq (by ring))
    exact h2.trans (mul_le_mul_of_nonneg_right (hrow q) (Finset.sum_nonneg fun p _ => by
      have := hK0 q p; positivity))
  calc ∑ q, (∑ p, K q p * x p) ^ 2 ≤ ∑ q, r q * ∑ p, K q p * x p ^ 2 :=
        Finset.sum_le_sum fun q _ => hq q
    _ = ∑ p, x p ^ 2 * ∑ q, K q p * r q := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = ∑ p, x p ^ 2 * (r p * ∑ q, K q p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        by_cases h : K q p = 0
        · rw [h]; ring
        · rw [hcons q p h]; ring
    _ ≤ ∑ p, x p ^ 2 * (r p * r p) := by
        gcongr with p
        · exact hr0 p
        · exact hcol p
    _ = ∑ p, r p ^ 2 * x p ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => ?_; ring

end SchurReal

/-! ## The com dressing on a channel -/

section YBound

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

/-- **The com dressing on a channel, positive form**:
`Σ_f (Σ_d |y_j(f,d)| v_d)² ≤ Σ_d r_j(d)² v_d²`, `r_j = C_j Λ_N |Π_j|` conserved on `j`-hops. -/
theorem sum_sq_yj_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (j : Ch eta) (v : Cfg eta N → ℝ) :
    ∑ f, (∑ d, ‖yj sys L p₀ N j f d‖ * v d) ^ 2 ≤
      ∑ d, rY (sys := sys) (L := L) j d ^ 2 * v d ^ 2 := by
  classical
  apply sum_sq_le_conserved _ _ v (fun _ _ => norm_nonneg _) (fun q => rY_nonneg hL j q)
  · intro q p h
    have hj : OnCh j (cidx N q) (cidx N p) := by
      by_contra hj; apply h; unfold yj ycKc; rw [if_neg hj, norm_zero]
    unfold rY
    rw [piC_onCh hj]
  · intro q
    have h := row_ycK_le (sys := sys) (p₀ := p₀) hL j q
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold yj ycKc
    by_cases hj : OnCh j (cidx N p) (cidx N q)
    · rw [if_pos (onCh_symm hj), if_pos hj, ycK_conj hL H hKernel p q, Complex.norm_conj]
    · rw [if_neg (fun h => hj (onCh_symm h)), if_neg hj, norm_zero]
  · intro p
    have h := row_ycK_le (sys := sys) (p₀ := p₀) hL j p
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold yj ycKc
    split_ifs <;> simp

end YBound

/-! ## Radial sums -/

section Radial

omit [Fintype ν] in
/-- `Σ_{x ∈ S} 1/max(R², |x|²)² ≤ 277/R` for `R ≥ 1`. -/
lemma sum_inv_max_sq_le (S : Finset Lattice3) {R : ℝ} (hR : 1 ≤ R) :
    ∑ x ∈ S, 1 / max (R ^ 2) (FSLattice.lsq x) ^ 2 ≤ 277 / R := by
  classical
  have hR0 : 0 < R := by linarith
  rw [← Finset.sum_filter_add_sum_filter_not S (fun x => FSLattice.lsq x ≤ R ^ 2)]
  have h1 : ∑ x ∈ S.filter (fun x => FSLattice.lsq x ≤ R ^ 2),
      1 / max (R ^ 2) (FSLattice.lsq x) ^ 2 ≤ 27 / R := by
    have e : ∀ x ∈ S.filter (fun x => FSLattice.lsq x ≤ R ^ 2),
        1 / max (R ^ 2) (FSLattice.lsq x) ^ 2 = 1 / R ^ 4 := by
      intro x hx
      rw [max_eq_left (Finset.mem_filter.mp hx).2]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul]
    have hc := card_ball_le (S.filter (fun x => FSLattice.lsq x ≤ R ^ 2)) (Y := R ^ 2)
      (by positivity) (fun x hx => (Finset.mem_filter.mp hx).2)
    rw [Real.sqrt_sq hR0.le] at hc
    have h27 : (2 * R + 1) ^ 3 ≤ 27 * R ^ 3 := by
      have h3 : 2 * R + 1 ≤ 3 * R := by linarith
      calc (2 * R + 1) ^ 3 ≤ (3 * R) ^ 3 := pow_le_pow_left₀ (by positivity) h3 3
        _ = 27 * R ^ 3 := by ring
    calc ((S.filter (fun x => FSLattice.lsq x ≤ R ^ 2)).card : ℝ) * (1 / R ^ 4) ≤
        27 * R ^ 3 * (1 / R ^ 4) := mul_le_mul_of_nonneg_right (hc.trans h27) (by positivity)
      _ = 27 / R := by field_simp
  have h2 : ∑ x ∈ S.filter (fun x => ¬ FSLattice.lsq x ≤ R ^ 2),
      1 / max (R ^ 2) (FSLattice.lsq x) ^ 2 ≤ 250 / R := by
    have e : ∀ x ∈ S.filter (fun x => ¬ FSLattice.lsq x ≤ R ^ 2),
        1 / max (R ^ 2) (FSLattice.lsq x) ^ 2 = 1 / FSLattice.lsq x ^ 2 := by
      intro x hx
      rw [max_eq_right (le_of_lt (not_le.mp (Finset.mem_filter.mp hx).2))]
    rw [Finset.sum_congr rfl e]
    have h := FSLattice.sum_tail_inv_sq_le S hR
    have hf : S.filter (fun x => ¬ FSLattice.lsq x ≤ R ^ 2) =
        S.filter (fun x => R ^ 2 < FSLattice.lsq x) :=
      Finset.filter_congr fun x _ => not_le
    rw [hf]
    exact h
  have e : 27 / R + 250 / R = 277 / R := by ring
  linarith

omit [Fintype ν] in
/-- `Σ_{x ∈ S} 1/max(R², |x|²)³ ≤ 277/R³` for `R ≥ 1`. -/
lemma sum_inv_max_cube_le (S : Finset Lattice3) {R : ℝ} (hR : 1 ≤ R) :
    ∑ x ∈ S, 1 / max (R ^ 2) (FSLattice.lsq x) ^ 3 ≤ 277 / R ^ 3 := by
  have hR0 : 0 < R := by linarith
  have hpt : ∀ x ∈ S, 1 / max (R ^ 2) (FSLattice.lsq x) ^ 3 ≤
      1 / R ^ 2 * (1 / max (R ^ 2) (FSLattice.lsq x) ^ 2) := by
    intro x _
    have hm : R ^ 2 ≤ max (R ^ 2) (FSLattice.lsq x) := le_max_left _ _
    have hm0 : 0 < max (R ^ 2) (FSLattice.lsq x) := lt_of_lt_of_le (by positivity) hm
    rw [div_mul_div_comm, one_mul, pow_succ]
    apply one_div_le_one_div_of_le (by positivity)
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  calc 1 / R ^ 2 * ∑ x ∈ S, 1 / max (R ^ 2) (FSLattice.lsq x) ^ 2 ≤ 1 / R ^ 2 * (277 / R) :=
        mul_le_mul_of_nonneg_left (sum_inv_max_sq_le S hR) (by positivity)
    _ = 277 / R ^ 3 := by field_simp

variable {N : ℕ}

omit [Fintype ν] in
open Classical in
/-- **The radial line sums**: `Σ_{p on the j-line of q} 1/max(R², |ζ_p - z₀|²)² ≤ 277/R`. -/
lemma lineSum_inv_max_sq_le {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    (q : Cfg eta N) {R : ℝ} (hR : 1 ≤ R) (z₀ : Lattice3) :
    ∑ p ∈ Finset.univ.filter (fun p => lab N j p = lab N j q),
      1 / max (R ^ 2) (FSLattice.lsq (regSum A (cidx N p) - z₀)) ^ 2 ≤ 277 / R := by
  set F := Finset.univ.filter (fun p : Cfg eta N => lab N j p = lab N j q)
  have hinj : Set.InjOn (fun p => regSum A (cidx N p) - z₀) F := by
    intro p hp p' hp' h
    have h1 : lab N j p = lab N j p' :=
      (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm
    exact coord_injOn hA (lab_eq_iff.mp h1) (sub_left_injective h)
  rw [← Finset.sum_image (f := fun x => 1 / max (R ^ 2) (FSLattice.lsq x) ^ 2) hinj]
  exact sum_inv_max_sq_le _ hR

omit [Fintype ν] in
open Classical in
/-- `Σ_{p on the j-line of q} 1/max(R², |ζ_p - z₀|²)³ ≤ 277/R³`. -/
lemma lineSum_inv_max_cube_le {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    (q : Cfg eta N) {R : ℝ} (hR : 1 ≤ R) (z₀ : Lattice3) :
    ∑ p ∈ Finset.univ.filter (fun p => lab N j p = lab N j q),
      1 / max (R ^ 2) (FSLattice.lsq (regSum A (cidx N p) - z₀)) ^ 3 ≤ 277 / R ^ 3 := by
  set F := Finset.univ.filter (fun p : Cfg eta N => lab N j p = lab N j q)
  have hinj : Set.InjOn (fun p => regSum A (cidx N p) - z₀) F := by
    intro p hp p' hp' h
    have h1 : lab N j p = lab N j p' :=
      (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm
    exact coord_injOn hA (lab_eq_iff.mp h1) (sub_left_injective h)
  rw [← Finset.sum_image (f := fun x => 1 / max (R ^ 2) (FSLattice.lsq x) ^ 3) hinj]
  exact sum_inv_max_cube_le _ hR

end Radial

/-! ## The shifted ball sum -/

section Ball

omit [Fintype ν] in
/-- **The shifted ball sum**: `Σ_{θ ∈ T} 1/|θ|² ≤ 81 R` if every `θ ∈ T` has `|θ - c₀| ≤ R`. -/
lemma sum_inv_lsq_shifted_le (T : Finset Lattice3) (c₀ : Lattice3) {R : ℝ} (hR : 1 ≤ R)
    (hT : ∀ θ ∈ T, FSLattice.lsq (θ - c₀) ≤ R ^ 2) : ∑ θ ∈ T, 1 / FSLattice.lsq θ ≤ 81 * R := by
  classical
  have hR0 : 0 < R := by linarith
  rw [← Finset.sum_filter_add_sum_filter_not T (fun θ => FSLattice.lsq θ ≤ (3 * R) ^ 2)]
  have h1 : ∑ θ ∈ T.filter (fun θ => FSLattice.lsq θ ≤ (3 * R) ^ 2), 1 / FSLattice.lsq θ ≤
      78 * R := by
    have hsub : (T.filter (fun θ => FSLattice.lsq θ ≤ (3 * R) ^ 2)).filter (fun θ => θ ≠ 0) ⊆
        (FSLattice.box ⌊3 * R⌋₊).filter (fun θ => θ ≠ 0 ∧ FSLattice.lsq θ ≤ (3 * R) ^ 2) := by
      intro θ hθ
      rw [Finset.mem_filter] at hθ ⊢
      have h3 := (Finset.mem_filter.mp hθ.1).2
      exact ⟨FSLattice.mem_box_floor_of_lsq_le (by positivity) h3, hθ.2, h3⟩
    have e : ∑ θ ∈ T.filter (fun θ => FSLattice.lsq θ ≤ (3 * R) ^ 2), 1 / FSLattice.lsq θ =
        ∑ θ ∈ (T.filter (fun θ => FSLattice.lsq θ ≤ (3 * R) ^ 2)).filter (fun θ => θ ≠ 0),
          1 / FSLattice.lsq θ := by
      refine (Finset.sum_filter_of_ne fun θ _ h => ?_).symm
      intro h0
      apply h
      rw [h0]
      simp [FSLattice.lsq]
    rw [e]
    calc ∑ θ ∈ (T.filter (fun θ => FSLattice.lsq θ ≤ (3 * R) ^ 2)).filter (fun θ => θ ≠ 0),
          1 / FSLattice.lsq θ ≤
        ∑ θ ∈ (FSLattice.box ⌊3 * R⌋₊).filter (fun θ => θ ≠ 0 ∧ FSLattice.lsq θ ≤ (3 * R) ^ 2),
          1 / FSLattice.lsq θ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun θ _ _ =>
            div_nonneg zero_le_one (FSLattice.lsq_nonneg θ)
      _ ≤ 26 * (3 * R) := FSLattice.sum_inv_lsq_ball_le' (by positivity) _
      _ = 78 * R := by ring
  have h2 : ∑ θ ∈ T.filter (fun θ => ¬ FSLattice.lsq θ ≤ (3 * R) ^ 2), 1 / FSLattice.lsq θ ≤
      3 * R := by
    have hpt : ∀ θ ∈ T.filter (fun θ => ¬ FSLattice.lsq θ ≤ (3 * R) ^ 2),
        1 / FSLattice.lsq θ ≤ 1 / (9 * R ^ 2) := by
      intro θ hθ
      have h := not_le.mp (Finset.mem_filter.mp hθ).2
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hinj : Set.InjOn (fun θ : Lattice3 => θ - c₀)
        (T.filter (fun θ => ¬ FSLattice.lsq θ ≤ (3 * R) ^ 2)) :=
      fun a _ b _ h => sub_left_injective h
    have hc := card_ball_le ((T.filter (fun θ => ¬ FSLattice.lsq θ ≤ (3 * R) ^ 2)).image
      (fun θ => θ - c₀)) (Y := R ^ 2) (by positivity) (by
        intro τ hτ
        obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hτ
        exact hT θ (Finset.mem_filter.mp hθ).1)
    rw [Finset.card_image_of_injOn hinj, Real.sqrt_sq hR0.le] at hc
    have h27 : (2 * R + 1) ^ 3 ≤ 27 * R ^ 3 := by
      have h3 : 2 * R + 1 ≤ 3 * R := by linarith
      calc (2 * R + 1) ^ 3 ≤ (3 * R) ^ 3 := pow_le_pow_left₀ (by positivity) h3 3
        _ = 27 * R ^ 3 := by ring
    calc ((T.filter (fun θ => ¬ FSLattice.lsq θ ≤ (3 * R) ^ 2)).card : ℝ) * (1 / (9 * R ^ 2)) ≤
        27 * R ^ 3 * (1 / (9 * R ^ 2)) := mul_le_mul_of_nonneg_right (hc.trans h27) (by positivity)
      _ = 3 * R := by field_simp; ring
  linarith

end Ball

/-! ## Same-line convolutions -/

section Conv

variable {N : ℕ}

omit [Fintype ν] in
open Classical in
/-- **Same-line convolutions**: if `K(d, b) ≠ 0` only on the `j`-lines and the columns of `K` are
`≤ S`, then `L_j(K x) ≤ S L_j(x)`. -/
theorem lineSum_conv_le (j : Ch eta) (K : Cfg eta N → Cfg eta N → ℝ) (hK0 : ∀ d b, 0 ≤ K d b)
    (x : Cfg eta N → ℝ) (hx : ∀ p, 0 ≤ x p) {S : ℝ}
    (hK : ∀ d b, K d b ≠ 0 → lab N j d = lab N j b) (hS : ∀ b, ∑ d, K d b ≤ S) (t : Cf eta) :
    lineSum j (fun d => ∑ b, K d b * x b) t ≤ S * lineSum j x t := by
  classical
  unfold lineSum
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hb : lab N j b = t
  · rw [if_pos hb]
    have h1 : ∑ d ∈ Finset.univ.filter (fun d => lab N j d = t), K d b * x b ≤
        (∑ d, K d b) * x b := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (hx b)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun d _ _ => hK0 d b
    calc ∑ d ∈ Finset.univ.filter (fun d => lab N j d = t), K d b * x b ≤ (∑ d, K d b) * x b := h1
      _ ≤ S * x b := mul_le_mul_of_nonneg_right (hS b) (hx b)
  · rw [if_neg hb]
    apply le_of_eq
    refine Finset.sum_eq_zero fun d hd => ?_
    have hd' := (Finset.mem_filter.mp hd).2
    by_cases h0 : K d b = 0
    · rw [h0, zero_mul]
    · exact absurd ((hK d b h0).symm.trans hd') hb

omit [Fintype ν] in
/-- `L²_j(K x; Ω) ≤ S² L²_j(x; Ω)` for a same-line kernel with columns `≤ S`. -/
theorem lineSq_conv_le (j : Ch eta) {Ω : Cf eta → ℝ} (hΩ : ∀ t, 0 ≤ Ω t)
    (K : Cfg eta N → Cfg eta N → ℝ) (hK0 : ∀ d b, 0 ≤ K d b)
    (x : Cfg eta N → ℝ) (hx : ∀ p, 0 ≤ x p) {S : ℝ}
    (hK : ∀ d b, K d b ≠ 0 → lab N j d = lab N j b) (hS : ∀ b, ∑ d, K d b ≤ S) :
    lineSq j Ω (fun d => ∑ b, K d b * x b) ≤ S ^ 2 * lineSq j Ω x := by
  unfold lineSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hv0 : ∀ d, 0 ≤ ∑ b, K d b * x b := fun d =>
    Finset.sum_nonneg fun b _ => mul_nonneg (hK0 d b) (hx b)
  have h1 := lineSum_conv_le j K hK0 x hx hK hS t
  have h2 := pow_le_pow_left₀ (lineSum_nonneg j hv0 t) h1 2
  rw [mul_pow] at h2
  calc Ω t * lineSum j (fun d => ∑ b, K d b * x b) t ^ 2 ≤ Ω t * (S ^ 2 * lineSum j x t ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (hΩ t)
    _ = S ^ 2 * (Ω t * lineSum j x t ^ 2) := by ring

end Conv

/-! ## Moments -/

section Moments

variable {sys : CoulombSystem eta ν} {L : ℝ} {N : ℕ}

omit [Fintype ν] in
/-- A coordinate is bounded by the energy: `1 + |ζ|² ≤ 2 c_X (1 + A)`. -/
lemma one_add_lsq_regSum_le (hL : 0 < L) {A : Finset (Fin eta)} (hA : A.card ≤ 2) (q : Cfg eta N) :
    1 + FSLattice.lsq (regSum A (cidx N q)) ≤ 2 * (cXw sys L * (1 + Asym sys L N q)) := by
  have hX := one_add_Xall_le (sys := sys) hL q
  have hX0 := Xall_nonneg q
  have := lsq_regSum_le_Xall A hA q
  linarith

omit [Fintype ν] in
/-- **Weights of degree `≤ 5`**: if `Ω ≤ C₀ (1 + A)`, then
`Ω w32(ζ) ≤ 2√2 c_X^{3/2} C₀ (1 + A)^{5/2}`. -/
lemma weight5_le (hL : 0 < L) {A : Finset (Fin eta)} (hA : A.card ≤ 2) (q : Cfg eta N)
    {Ω C₀ : ℝ} (hΩ0 : 0 ≤ Ω) (hΩ : Ω ≤ C₀ * (1 + Asym sys L N q)) :
    Ω * w32 (regSum A (cidx N q)) ≤
      2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * C₀ *
        ((1 + Asym sys L N q) ^ 2 * Real.sqrt (1 + Asym sys L N q)) := by
  have h1 := one_add_lsq_regSum_le (sys := sys) hL hA q
  have hA0 := FSGalerkin.Asym_nonneg sys L N q
  have hc1 := cXw_ge_one (sys := sys) hL
  have hl0 := FSLattice.lsq_nonneg (regSum A (cidx N q))
  have hw : w32 (regSum A (cidx N q)) ≤
      2 * (cXw sys L * (1 + Asym sys L N q)) *
        (Real.sqrt 2 * (Real.sqrt (cXw sys L) * Real.sqrt (1 + Asym sys L N q))) := by
    unfold w32
    apply mul_le_mul h1 _ (Real.sqrt_nonneg _) (by positivity)
    rw [← Real.sqrt_mul (by linarith), ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hC0 : 0 ≤ C₀ := by
    by_contra h
    push Not at h
    have : C₀ * (1 + Asym sys L N q) < 0 := mul_neg_of_neg_of_pos h (by linarith)
    linarith
  calc Ω * w32 (regSum A (cidx N q)) ≤ (C₀ * (1 + Asym sys L N q)) *
        (2 * (cXw sys L * (1 + Asym sys L N q)) *
          (Real.sqrt 2 * (Real.sqrt (cXw sys L) * Real.sqrt (1 + Asym sys L N q)))) :=
        mul_le_mul hΩ hw (by unfold w32; positivity) (by positivity)
    _ = _ := by ring

end Moments

end FSFlux
