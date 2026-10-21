import PlaneWave.KineticCompletion.FirstRotationWords

/-!
# Kinetic completion, part 4: quarter-power weights for the same-channel generator

`lem:weighted` of the completion note, for every `|α| ≤ 1/2`: with `E = 1 + A`,
`‖E^α Σ₃^sp v‖ ≤ C_W(n) ‖E^α v‖`, `C_W(n) = 5 C_Σ3(n) + Σ_j farC_j(n) = O(n⁻³ log⁴ n)`
(`norm_wt_Sig3sp_le`), and the weighted completion hypothesis of `thm:src3` on good states of
budget `M` follows (`weighted_Sig3sp_good`):
`‖E^{-1/4} Σ₃^sp W_N u‖ + ‖E^{1/4} Σ₃^sp u‖ ≤ C_W(n)(√2 C_m + 1) M`, using
`‖W_N u‖ ≤ √2 C_m ‖(1 + A) u‖` in place of the form bound `‖E^{-1/4} W_N E^{-1/4}‖ ≤ C`.

Schur's test with the test function `E^{-1/2}` reduces the conjugated kernel
`σ₃(q,p) (E(q)/E(p))^α` to the column sums `Σ_q |σ₃(q,p)| (E(p)/E(q))^β`, `β = 1/2 ± α ∈ [0, 1]`
(`col_sig3_weighted`): `(E(p)/E(q))^β ≤ 1 + E(p)/E(q)`, the comparable energies are bounded by
the Schur sums of `Σ₃^sp` (`col_sig3_le`), and in the far region `4E(q) < E(p)`:

* the mismatch exceeds `(3/4) E(p)`;
* completing the square on the channel fibre, `A(q) ≥ (g²/2μ) |θ + c|²` (`asym_ge_qd`), so the
  transfer is long, `(g²/2μ)|θ|² > E(p)/8`, and `|σ₃(q,p)| ≤ (4/3) B_j (J_n + 4) √(8a)/E(p)^{3/2}`;
* the lattice sum `Σ_θ (1 + a|θ + c|²)⁻¹ ≤ 7 (1 + 1/a)(27 + 26 R)` over `|θ + c| < R`
  (`sum_inv_qd_le`, by comparison with the unshifted box sum), with `R² = E(p)/(4a)`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSLattice

/-- **A shifted lattice sum**: `Σ_{θ : |θ + c| < R} (1 + a |θ + c|²)⁻¹ ≤ 7 (1 + 1/a)(27 + 26 R)`. -/
theorem sum_inv_qd_le (c : Fin 3 → ℝ) {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (T : Finset L3) :
    ∑ θ ∈ T.filter (fun θ => qd c θ < R ^ 2), 1 / (1 + a * qd c θ) ≤
      7 * (1 + 1 / a) * (27 + 26 * R) := by
  classical
  set z₀ : L3 := fun i => ⌊-c i⌋
  set N := ⌈R⌉₊
  set T' := T.filter (fun θ => qd c θ < R ^ 2)
  have hN : R ≤ N := Nat.le_ceil R
  have hN1 : (N : ℝ) ≤ R + 1 := (Nat.ceil_lt_add_one hR).le
  -- every point is a point of the box about `z₀`
  have hbox : ∀ θ ∈ T', θ - z₀ ∈ box N := by
    intro θ hθ
    have hq := (Finset.mem_filter.mp hθ).2
    rw [mem_box]
    intro i
    have h1 : ((θ i : ℝ) + c i) ^ 2 ≤ qd c θ :=
      Finset.single_le_sum (f := fun i => ((θ i : ℝ) + c i) ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    have h2 : |(θ i : ℝ) + c i| < N := by
      rw [← Real.sqrt_sq_eq_abs]
      calc Real.sqrt (((θ i : ℝ) + c i) ^ 2) < Real.sqrt ((N : ℝ) ^ 2) := by
            apply Real.sqrt_lt_sqrt (sq_nonneg _)
            have : R ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ hR hN 2
            linarith
        _ = N := Real.sqrt_sq (Nat.cast_nonneg N)
    have hf1 := Int.floor_le (-c i)
    have hf2 := Int.lt_floor_add_one (-c i)
    rw [abs_lt] at h2
    have e : ((θ - z₀) i : ℝ) = (θ i : ℝ) - ⌊-c i⌋ := by simp [z₀]
    have h3 : -(N : ℝ) < ((θ - z₀) i : ℝ) := by rw [e]; linarith
    have h4 : ((θ - z₀) i : ℝ) < N + 1 := by rw [e]; linarith
    constructor
    · exact_mod_cast h3.le
    · have : (θ - z₀) i < (N : ℤ) + 1 := by exact_mod_cast h4
      omega
  -- the weights compare with those of the box
  have hw : ∀ θ ∈ T', 1 / (1 + a * qd c θ) ≤ 7 * (1 + 1 / a) * (1 / (1 + lsq (θ - z₀))) := by
    intro θ _
    have hq0 := qd_nonneg c θ
    have hl : lsq (θ - z₀) ≤ 2 * qd c θ + 6 := by
      have hcoord : ∀ i, (((θ - z₀) i : ℤ) : ℝ) ^ 2 ≤ 2 * ((θ i : ℝ) + c i) ^ 2 + 2 := by
        intro i
        have hf1 := Int.floor_le (-c i)
        have hf2 := Int.lt_floor_add_one (-c i)
        have e : ((θ - z₀) i : ℝ) = ((θ i : ℝ) + c i) - (c i + ⌊-c i⌋) := by simp [z₀]; ring
        rw [e]
        have hb : (c i + ⌊-c i⌋) ^ 2 ≤ 1 := by
          have h1 : -1 < c i + ⌊-c i⌋ := by linarith
          have h2 : c i + ⌊-c i⌋ ≤ 0 := by linarith
          nlinarith
        nlinarith [sq_nonneg (((θ i : ℝ) + c i) + (c i + ⌊-c i⌋))]
      have e1 : lsq (θ - z₀) = ∑ i, (((θ - z₀) i : ℤ) : ℝ) ^ 2 := lsq_eq_sum _
      have e2 : qd c θ = ∑ i, ((θ i : ℝ) + c i) ^ 2 := rfl
      rw [e1, e2, Fin.sum_univ_three, Fin.sum_univ_three]
      linarith [hcoord 0, hcoord 1, hcoord 2]
    have hl0 := lsq_nonneg (θ - z₀)
    rw [div_le_iff₀ (by positivity), mul_comm, ← mul_assoc, ← div_eq_mul_one_div]
    rw [le_div_iff₀ (by positivity)]
    have : (1 + lsq (θ - z₀)) ≤ 7 * (1 + qd c θ) := by linarith
    have h2 : 1 + qd c θ ≤ (1 + 1 / a) * (1 + a * qd c θ) := by
      have : 0 ≤ qd c θ * a := by positivity
      field_simp
      nlinarith
    nlinarith
  calc ∑ θ ∈ T', 1 / (1 + a * qd c θ)
      ≤ ∑ θ ∈ T', 7 * (1 + 1 / a) * (1 / (1 + lsq (θ - z₀))) := Finset.sum_le_sum hw
    _ = 7 * (1 + 1 / a) * ∑ w ∈ T'.image (fun θ => θ - z₀), 1 / (1 + lsq w) := by
        rw [← Finset.mul_sum, Finset.sum_image (fun x _ y _ h => sub_left_injective h)]
    _ ≤ 7 * (1 + 1 / a) * ∑ w ∈ box N, 1 / (1 + lsq w) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (fun w hw => by
          obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hw; exact hbox θ hθ)
          (fun w _ _ => by have := lsq_nonneg w; positivity)
    _ ≤ 7 * (1 + 1 / a) * (1 + 26 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_box_inv_le N) (by positivity)
    _ ≤ 7 * (1 + 1 / a) * (27 + 26 * R) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

end FSLattice

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]
variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

/-! ## Completing the square on a channel fibre -/

omit [Fintype ν] in
/-- The kinetic energy dominates the drift of every channel: `(g²/2μ_j) |c_j|² ≤ A`. -/
lemma asym_ge_drift (hL : 0 < L) (j : Ch eta) (p : Cfg eta n) :
    gF L ^ 2 / (2 * muCh sys j) * ∑ i, (cCh sys j (cidx n p) i) ^ 2 ≤ Asym sys L n p := by
  rw [Asym_eq_Ek]
  unfold Ek E
  have hg := gF_pos hL
  have hterm : ∀ c, 0 ≤ gF L ^ 2 / (2 * sys.mass c) * nsq (finiteConfigLatticeIndex eta n p c) :=
    fun c => by have := sys.mass_pos c; have := nsq_nonneg (finiteConfigLatticeIndex eta n p c); positivity
  cases j with
  | inl a =>
    have hm := sys.mass_pos a
    calc gF L ^ 2 / (2 * muCh sys (.inl a)) * ∑ i, (cCh sys (.inl a) (cidx n p) i) ^ 2
        = gF L ^ 2 / (2 * sys.mass a) * nsq (finiteConfigLatticeIndex eta n p a) := by
          simp only [muCh, cCh, nsq, Fin.sum_univ_three]
      _ ≤ ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (finiteConfigLatticeIndex eta n p c) :=
          Finset.single_le_sum (f := fun c => gF L ^ 2 / (2 * sys.mass c) *
            nsq (finiteConfigLatticeIndex eta n p c)) (fun c _ => hterm c) (Finset.mem_univ a)
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    have ha := sys.mass_pos pr.1.1
    have hb := sys.mass_pos pr.1.2
    set k := finiteConfigLatticeIndex eta n p
    have key : ∀ x y : ℝ, gF L ^ 2 / (2 * muCh sys (.inr pr)) *
        (muCh sys (.inr pr) * (x / sys.mass pr.1.1 - y / sys.mass pr.1.2)) ^ 2 ≤
        gF L ^ 2 / (2 * sys.mass pr.1.1) * x ^ 2 + gF L ^ 2 / (2 * sys.mass pr.1.2) * y ^ 2 := by
      intro x y
      have e : gF L ^ 2 / (2 * muCh sys (.inr pr)) *
          (muCh sys (.inr pr) * (x / sys.mass pr.1.1 - y / sys.mass pr.1.2)) ^ 2 =
          gF L ^ 2 / (2 * sys.mass pr.1.1) * x ^ 2 + gF L ^ 2 / (2 * sys.mass pr.1.2) * y ^ 2 -
            gF L ^ 2 * (x + y) ^ 2 / (2 * (sys.mass pr.1.1 + sys.mass pr.1.2)) := by
        simp only [muCh]; field_simp; ring
      rw [e]
      have : 0 ≤ gF L ^ 2 * (x + y) ^ 2 / (2 * (sys.mass pr.1.1 + sys.mass pr.1.2)) := by
        positivity
      linarith
    have hsum : gF L ^ 2 / (2 * muCh sys (.inr pr)) * ∑ i, (cCh sys (.inr pr) (cidx n p) i) ^ 2 ≤
        gF L ^ 2 / (2 * sys.mass pr.1.1) * nsq (k pr.1.1) +
          gF L ^ 2 / (2 * sys.mass pr.1.2) * nsq (k pr.1.2) := by
      rw [Finset.mul_sum]
      have hc : ∀ i, cCh sys (.inr pr) (cidx n p) i = muCh sys (.inr pr) *
          ((k pr.1.1 i : ℝ) / sys.mass pr.1.1 - (k pr.1.2 i : ℝ) / sys.mass pr.1.2) := fun i => rfl
      simp only [hc, nsq, Fin.sum_univ_three]
      have h0 := key (k pr.1.1 0) (k pr.1.2 0)
      have h1 := key (k pr.1.1 1) (k pr.1.2 1)
      have h2 := key (k pr.1.1 2) (k pr.1.2 2)
      linarith
    refine hsum.trans ?_
    rw [← Finset.sum_pair hne (f := fun c => gF L ^ 2 / (2 * sys.mass c) *
      nsq (finiteConfigLatticeIndex eta n p c))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun c _ _ => hterm c)

omit [Fintype ν] in
/-- **Completing the square**: on channel `j` from `p`, `A(q) ≥ (g²/2μ_j) |θ + c|²`. -/
lemma asym_ge_qd (hL : 0 < L) {j : Ch eta} {q p : Cfg eta n} (hj : OnCh j (cidx n q) (cidx n p)) :
    gF L ^ 2 / (2 * muCh sys j) * FSLattice.qd (cCh sys j (cidx n p)) (chT n j q p) ≤
      Asym sys L n q := by
  have h1 := Asym_hop (sys := sys) (L := L) hj
  have h2 := asym_ge_drift (sys := sys) hL j p
  have h3 := FSLattice.qd_eq (cCh sys j (cidx n p)) (chT n j q p)
  rw [h3, mul_add]
  linarith

/-! ## The far region -/

omit [Fintype ν] in
/-- **The far region** `4 E(q) < E(p)` on channel `j` from `p` (`E = 1 + A`): the mismatch exceeds
`(3/4) E(p)`, the transfer is long, `a |θ|² > E(p)/8`, and `|θ + c|² < E(p)/(4a)`,
`a = g²/(2μ_j)`. -/
lemma far_facts (hL : 0 < L) {j : Ch eta} {q p : Cfg eta n} (hj : OnCh j (cidx n q) (cidx n p))
    (hfar : 4 * (1 + Asym sys L n q) < 1 + Asym sys L n p) :
    3 / 4 * (1 + Asym sys L n p) < Asym sys L n p - Asym sys L n q ∧
    (1 + Asym sys L n p) / 8 < gF L ^ 2 / (2 * muCh sys j) * FSLattice.lsq (chT n j q p) ∧
    FSLattice.qd (cCh sys j (cidx n p)) (chT n j q p) <
      (1 + Asym sys L n p) / (4 * (gF L ^ 2 / (2 * muCh sys j))) := by
  set a := gF L ^ 2 / (2 * muCh sys j) with ha_def
  have ha : 0 < a := by have := gF_pos hL; have := muCh_pos sys j; positivity
  set c := cCh sys j (cidx n p)
  set θ := chT n j q p
  have h1 := Asym_hop (sys := sys) (L := L) hj
  have h2 := asym_ge_qd (sys := sys) hL hj
  have h3 := FSLattice.qd_eq c θ
  have hAq := Asym_nonneg (sys := sys) (L := L) q
  have hq0 := FSLattice.qd_nonneg c θ
  refine ⟨by linarith, ?_, ?_⟩
  · have hc : ∀ i, c i ^ 2 ≤ 2 * ((θ i : ℝ)) ^ 2 + 2 * ((θ i : ℝ) + c i) ^ 2 := fun i => by
      nlinarith [sq_nonneg (((θ i : ℝ) + c i) + (θ i : ℝ))]
    have hsum : ∑ i, c i ^ 2 ≤ 2 * FSLattice.lsq θ + 2 * FSLattice.qd c θ := by
      have e1 : FSLattice.lsq θ = ∑ i, ((θ i : ℤ) : ℝ) ^ 2 := FSLattice.lsq_eq_sum θ
      have e2 : FSLattice.qd c θ = ∑ i, ((θ i : ℝ) + c i) ^ 2 := rfl
      rw [e1, e2, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
      linarith [hc 0, hc 1, hc 2]
    have hsl : a * FSLattice.slabF c θ = Asym sys L n q - Asym sys L n p := h1.symm
    have hX : 3 / 4 * (1 + Asym sys L n p) < a * ∑ i, c i ^ 2 := by
      have : a * ∑ i, c i ^ 2 = a * FSLattice.qd c θ - a * FSLattice.slabF c θ := by
        rw [h3]; ring
      rw [this, hsl]
      have : 0 ≤ a * FSLattice.qd c θ := by positivity
      linarith
    have hY : a * FSLattice.qd c θ < (1 + Asym sys L n p) / 4 := by linarith
    have : a * ∑ i, c i ^ 2 ≤ 2 * (a * FSLattice.lsq θ) + 2 * (a * FSLattice.qd c θ) := by
      have := mul_le_mul_of_nonneg_left hsum ha.le
      linarith
    linarith
  · rw [lt_div_iff₀ (by positivity)]
    linarith

/-- **The far kernel bound**: in the far region, `|σ₃(q,p)| (E(p)/E(q)) ≤
(4/3) B_j (J_n + 4) √(8a) E(p)^{-1/2} (1 + a |θ + c|²)⁻¹`. -/
lemma far_kernel_le (hL : 0 < L) (hn : 2 ≤ n) {j : Ch eta} {q p : Cfg eta n}
    (hj : OnCh j (cidx n q) (cidx n p)) (hg : gapC sys L n q p)
    (hfar : 4 * (1 + Asym sys L n q) < 1 + Asym sys L n p) :
    ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| *
        ((1 + Asym sys L n p) / (1 + Asym sys L n q)) ≤
      4 / 3 * Bh3 sys L n j * (Jn sys n + 4) * Real.sqrt (8 * (gF L ^ 2 / (2 * muCh sys j))) /
        Real.sqrt (1 + Asym sys L n p) *
          (1 / (1 + gF L ^ 2 / (2 * muCh sys j) *
            FSLattice.qd (cCh sys j (cidx n p)) (chT n j q p))) := by
  set a := gF L ^ 2 / (2 * muCh sys j) with ha_def
  have ha : 0 < a := by have := gF_pos hL; have := muCh_pos sys j; positivity
  obtain ⟨hgap, hlong, -⟩ := far_facts (sys := sys) hL hj hfar
  set E := 1 + Asym sys L n p
  set Eq := 1 + Asym sys L n q
  set θ := chT n j q p
  set c := cCh sys j (cidx n p)
  have hAq := Asym_nonneg (sys := sys) (L := L) q
  have hE : 1 ≤ E := by have := Asym_nonneg (sys := sys) (L := L) p; simp only [E]; linarith
  have hqp : q ≠ p := hg.1
  -- the kernel bound with the logarithm below the cap
  have hfl := floor_of_gapC hL hj hg
  have hcap := slabF_cap_cube (sys := sys) hL hj
  have hρ1 : 1 ≤ FSChannel.rho θ := FSLattice.one_le_rho (one_le_lsq_chT hj hqp)
  have hρc : FSChannel.rho θ < 2 ^ (Jn sys n + 1 + 1) := by
    have : 2 * FSChannel.rho θ < 2 ^ (Jn sys n + 1 + 1) * 2 := lt_of_le_of_lt hfl hcap
    linarith
  have hlog := FSLattice.log_ceil_le hρc
  have hlog' : ((Nat.log 2 ⌈FSChannel.rho θ⌉₊ : ℕ) : ℝ) + 2 ≤ Jn sys n + 4 := by
    have : ((Nat.log 2 ⌈FSChannel.rho θ⌉₊ : ℕ) : ℝ) ≤ Jn sys n + 1 + 1 := by exact_mod_cast hlog
    linarith
  have hB := Bh3_nonneg (sys := sys) (n := n) hL j
  have hh : ‖h3spK sys L n q p‖ ≤ Bh3 sys L n j * (Jn sys n + 4) / FSChannel.rho θ := by
    refine (norm_h3spK_le (sys := sys) hL hn hj hqp).trans ?_
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hB
    exact div_le_div_of_nonneg_right hlog' (by linarith)
  -- the long transfer
  have hρ : Real.sqrt (E / (8 * a)) < FSChannel.rho θ := by
    unfold FSChannel.rho
    apply Real.sqrt_lt_sqrt (by positivity)
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hsE : 0 < Real.sqrt E := Real.sqrt_pos.mpr (by linarith)
  have hinvρ : 1 / FSChannel.rho θ ≤ Real.sqrt (8 * a) / Real.sqrt E := by
    have h1 : Real.sqrt (E / (8 * a)) = Real.sqrt E / Real.sqrt (8 * a) :=
      Real.sqrt_div' E (by positivity)
    rw [h1] at hρ
    have hs8 : 0 < Real.sqrt (8 * a) := Real.sqrt_pos.mpr (by positivity)
    rw [div_le_div_iff₀ (by linarith) hsE, one_mul]
    rw [div_lt_iff₀ hs8] at hρ
    linarith
  -- the energies
  have hEq : 1 + a * FSLattice.qd c θ ≤ Eq := by
    have := asym_ge_qd (sys := sys) hL hj; simp only [Eq]; linarith
  have hq1 : 0 < 1 + a * FSLattice.qd c θ := by
    have := FSLattice.qd_nonneg c θ; positivity
  have habs : |Asym sys L n q - Asym sys L n p| = Asym sys L n p - Asym sys L n q := by
    rw [abs_sub_comm, abs_of_pos (by linarith)]
  rw [habs]
  have hEq0 : 0 < Eq := by linarith
  have hd0 : 0 < Asym sys L n p - Asym sys L n q := by linarith
  calc ‖h3spK sys L n q p‖ / (Asym sys L n p - Asym sys L n q) * (E / Eq)
      ≤ (Bh3 sys L n j * (Jn sys n + 4) / FSChannel.rho θ) / (3 / 4 * E) *
          (E / (1 + a * FSLattice.qd c θ)) := by
        apply mul_le_mul _ (div_le_div_of_nonneg_left (by linarith) hq1 hEq) (by positivity)
          (by have := Jn sys n; positivity)
        exact div_le_div₀ (by have := Jn sys n; positivity) hh (by positivity) hgap.le
    _ = 4 / 3 * Bh3 sys L n j * (Jn sys n + 4) * (1 / FSChannel.rho θ) *
          (1 / (1 + a * FSLattice.qd c θ)) := by
        field_simp
    _ ≤ 4 / 3 * Bh3 sys L n j * (Jn sys n + 4) * (Real.sqrt (8 * a) / Real.sqrt E) *
          (1 / (1 + a * FSLattice.qd c θ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hinvρ (by have := Jn sys n; positivity)
    _ = _ := by ring

/-! ## The weighted columns of `Σ₃^sp` -/

/-- `x^β ≤ 1 + x` for `x > 0`, `0 ≤ β ≤ 1`. -/
lemma rpow_le_one_add {x β : ℝ} (hx : 0 < x) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) : x ^ β ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · have := Real.rpow_le_one hx.le h hβ0; linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hβ1
    rw [Real.rpow_one] at this; linarith

omit [Fintype ν] in
lemma one_add_asym_pos (q : Cfg eta n) : 0 < 1 + Asym sys L n q := by
  have := Asym_nonneg (sys := sys) (L := L) q; linarith

open Classical in
/-- The entries of `Σ₃^sp` by channel. -/
lemma norm_sig3K_le_sum (q p : Cfg eta n) :
    ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) q p‖ ≤
      ∑ j : Ch eta, if OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p then
        ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| else 0 := by
  have hnn : 0 ≤ ∑ j : Ch eta, if OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p then
      ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| else 0 :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  unfold FSKernel.divK h3gK
  split_ifs with hA hg
  · rw [norm_zero]; exact hnn
  · obtain ⟨j, hj, -⟩ := hg.2
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun j : Ch eta =>
      if OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p then
        ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| else 0)
      (fun j _ => by split_ifs <;> positivity) (Finset.mem_univ j))
    exact (if_pos ⟨hj, hg⟩).symm
  · rw [zero_div, norm_zero]; exact hnn

variable (sys L n) in
/-- The far constant of channel `j`. -/
noncomputable def farC (j : Ch eta) : ℝ :=
  4 / 3 * Bh3 sys L n j * (Jn sys n + 4) * Real.sqrt (8 * (gF L ^ 2 / (2 * muCh sys j))) *
    (7 * (1 + 1 / (gF L ^ 2 / (2 * muCh sys j))) *
      (27 + 13 / Real.sqrt (gF L ^ 2 / (2 * muCh sys j))))

variable (sys L n) in
/-- `C_W = 5 C_Σ3 + Σ_j farC_j = O(n⁻³ log⁴ n)`. -/
noncomputable def CW : ℝ := 5 * CS3 sys L n + ∑ j : Ch eta, farC sys L n j

lemma farC_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ farC sys L n j := by
  unfold farC
  have := Bh3_nonneg (sys := sys) (n := n) hL j
  have := gF_pos hL
  have := muCh_pos sys j
  have : (0 : ℝ) ≤ Jn sys n := Nat.cast_nonneg _
  positivity

lemma CW_nonneg (hL : 0 < L) : 0 ≤ CW sys L n := by
  unfold CW
  have := CS3_nonneg (sys := sys) (n := n) hL
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => farC_nonneg (sys := sys) (n := n) hL j
  linarith

open Classical in
/-- The far part of one channel of a column of `Σ₃^sp`. -/
lemma col_far_chan_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (p : Cfg eta n) :
    ∑ q ∈ Finset.univ.filter (fun q => OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p ∧
        4 * (1 + Asym sys L n q) < 1 + Asym sys L n p),
      ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| *
        ((1 + Asym sys L n p) / (1 + Asym sys L n q)) ≤ farC sys L n j := by
  set a := gF L ^ 2 / (2 * muCh sys j) with ha_def
  have ha : 0 < a := by have := gF_pos hL; have := muCh_pos sys j; positivity
  set T := Finset.univ.filter (fun q => OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p ∧
    4 * (1 + Asym sys L n q) < 1 + Asym sys L n p)
  set E := 1 + Asym sys L n p
  set c := cCh sys j (cidx n p)
  have hE : 1 ≤ E := by have := Asym_nonneg (sys := sys) (L := L) p; simp only [E]; linarith
  have hsE : 0 < Real.sqrt E := Real.sqrt_pos.mpr (by linarith)
  set K := 4 / 3 * Bh3 sys L n j * (Jn sys n + 4) * Real.sqrt (8 * a)
  have hK : 0 ≤ K := by
    have := Bh3_nonneg (sys := sys) (n := n) hL j
    have : (0 : ℝ) ≤ Jn sys n := Nat.cast_nonneg _
    positivity
  have hterm : ∀ q ∈ T, ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| *
      ((1 + Asym sys L n p) / (1 + Asym sys L n q)) ≤
      K / Real.sqrt E * (1 / (1 + a * FSLattice.qd c (chT n j q p))) := by
    intro q hq
    obtain ⟨hj, hg, hfar⟩ := (Finset.mem_filter.mp hq).2
    exact far_kernel_le (sys := sys) hL hn hj hg hfar
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hinj : Set.InjOn (fun q => chT n j q p) T := fun q hq q' hq' h =>
    chT_injOn j p (Finset.mem_filter.mp hq).2.1 (Finset.mem_filter.mp hq').2.1 h
  rw [← Finset.sum_image (f := fun θ => 1 / (1 + a * FSLattice.qd c θ)) hinj]
  set Θ := T.image (fun q => chT n j q p)
  set R := Real.sqrt (E / (4 * a))
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = E / (4 * a) := Real.sq_sqrt (by positivity)
  have hfilt : Θ.filter (fun θ => FSLattice.qd c θ < R ^ 2) = Θ := by
    apply Finset.filter_true_of_mem
    intro θ hθ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hθ
    obtain ⟨hj, -, hfar⟩ := (Finset.mem_filter.mp hq).2
    rw [hRsq]
    exact (far_facts (sys := sys) hL hj hfar).2.2
  have hs := FSLattice.sum_inv_qd_le c ha hR Θ
  rw [hfilt] at hs
  have hR' : R / Real.sqrt E = 1 / (2 * Real.sqrt a) := by
    simp only [R]
    rw [Real.sqrt_div' E (by positivity), Real.sqrt_mul (by norm_num),
      show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have := Real.sqrt_pos.mpr ha
    field_simp
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  calc K / Real.sqrt E * ∑ θ ∈ Θ, 1 / (1 + a * FSLattice.qd c θ)
      ≤ K / Real.sqrt E * (7 * (1 + 1 / a) * (27 + 26 * R)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = K * (7 * (1 + 1 / a)) * (27 / Real.sqrt E + 26 * (R / Real.sqrt E)) := by
        field_simp
    _ ≤ K * (7 * (1 + 1 / a)) * (27 + 13 / Real.sqrt a) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [hR']
        have h1 : 27 / Real.sqrt E ≤ 27 := by
          rw [div_le_iff₀ hsE]
          have : 1 ≤ Real.sqrt E := by
            rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hE
          nlinarith
        have h2 : 26 * (1 / (2 * Real.sqrt a)) = 13 / Real.sqrt a := by field_simp; ring
        linarith
    _ = farC sys L n j := by unfold farC; simp only [K, ha_def]; ring

/-- **The weighted columns of `Σ₃^sp`**: `Σ_q |σ₃(q,p)| (E(p)/E(q))^β ≤ C_W` for `0 ≤ β ≤ 1`. -/
theorem col_sig3_weighted (hL : 0 < L) (hn : 2 ≤ n) (p : Cfg eta n) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) :
    ∑ q, ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) q p‖ *
      ((1 + Asym sys L n p) / (1 + Asym sys L n q)) ^ β ≤ CW sys L n := by
  classical
  set σ := FSKernel.divK (Asym sys L n) (h3gK sys L n)
  set r : Cfg eta n → ℝ := fun q => (1 + Asym sys L n p) / (1 + Asym sys L n q)
  have hr : ∀ q, 0 < r q := fun q => div_pos (one_add_asym_pos p) (one_add_asym_pos q)
  -- each term splits into a comparable and a far part
  have hterm : ∀ q, ‖σ q p‖ * r q ^ β ≤ 5 * ‖σ q p‖ +
      (if 4 * (1 + Asym sys L n q) < 1 + Asym sys L n p then ‖σ q p‖ * r q else 0) := by
    intro q
    have h1 := rpow_le_one_add (hr q) hβ0 hβ1
    have hσ := norm_nonneg (σ q p)
    split_ifs with hf
    · nlinarith
    · push Not at hf
      have hr4 : r q ≤ 4 := by
        simp only [r]
        rw [div_le_iff₀ (one_add_asym_pos q)]
        linarith
      nlinarith
  have hfar : ∑ q, (if 4 * (1 + Asym sys L n q) < 1 + Asym sys L n p then ‖σ q p‖ * r q else 0) ≤
      ∑ j : Ch eta, farC sys L n j := by
    have hent : ∀ q, (if 4 * (1 + Asym sys L n q) < 1 + Asym sys L n p then ‖σ q p‖ * r q else 0) ≤
        ∑ j : Ch eta, if OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p ∧
          4 * (1 + Asym sys L n q) < 1 + Asym sys L n p then
          ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| * r q else 0 := by
      intro q
      split_ifs with hf
      · have h := norm_sig3K_le_sum (sys := sys) (L := L) q p
        calc ‖σ q p‖ * r q ≤ (∑ j : Ch eta, if OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p then
              ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| else 0) * r q :=
              mul_le_mul_of_nonneg_right h (hr q).le
          _ = _ := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => ?_
              by_cases hj : OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p
              · rw [if_pos hj, if_pos ⟨hj.1, hj.2, hf⟩]
              · rw [if_neg hj, if_neg (fun h => hj ⟨h.1, h.2.1⟩), zero_mul]
      · exact Finset.sum_nonneg fun j _ => by split_ifs <;> [exact mul_nonneg (by positivity) (hr q).le; exact le_rfl]
    calc ∑ q, (if 4 * (1 + Asym sys L n q) < 1 + Asym sys L n p then ‖σ q p‖ * r q else 0)
        ≤ ∑ q, ∑ j : Ch eta, (if OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p ∧
            4 * (1 + Asym sys L n q) < 1 + Asym sys L n p then
            ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| * r q else 0) :=
          Finset.sum_le_sum fun q _ => hent q
      _ = ∑ j : Ch eta, ∑ q ∈ Finset.univ.filter (fun q => OnCh j (cidx n q) (cidx n p) ∧
            gapC sys L n q p ∧ 4 * (1 + Asym sys L n q) < 1 + Asym sys L n p),
            ‖h3spK sys L n q p‖ / |Asym sys L n q - Asym sys L n p| * r q := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.sum_filter _ _).symm
      _ ≤ ∑ j : Ch eta, farC sys L n j :=
          Finset.sum_le_sum fun j _ => col_far_chan_le (sys := sys) hL hn j p
  have hcol := col_sig3_le (sys := sys) hL hn p
  calc ∑ q, ‖σ q p‖ * r q ^ β
      ≤ ∑ q, (5 * ‖σ q p‖ +
          (if 4 * (1 + Asym sys L n q) < 1 + Asym sys L n p then ‖σ q p‖ * r q else 0)) :=
        Finset.sum_le_sum fun q _ => hterm q
    _ = 5 * ∑ q, ‖σ q p‖ +
          ∑ q, (if 4 * (1 + Asym sys L n q) < 1 + Asym sys L n p then ‖σ q p‖ * r q else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 5 * CS3 sys L n + ∑ j : Ch eta, farC sys L n j := by
        have : 5 * ∑ q, ‖σ q p‖ ≤ 5 * CS3 sys L n := by linarith
        linarith
    _ = CW sys L n := rfl

/-! ## Conjugation by the quarter-power weights -/

/-- Schur's test for a kernel conjugated by a weight `e`, with the test function `h`. -/
theorem norm_conj_kop_le {X : Type*} [Fintype X] (κ : X → X → ℂ) (e h : X → ℝ)
    (he : ∀ x, 0 < e x) (hh : ∀ x, 0 < h x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrow : ∀ q, ∑ p, ‖κ q p‖ * (e q / e p) * h p ≤ a * h q)
    (hcol : ∀ p, ∑ q, ‖κ q p‖ * (e q / e p) * h q ≤ b * h p) (v : EuclideanSpace ℂ X) :
    ‖FSKernel.dg (fun q => (e q : ℂ)) (FSKernel.kop κ v)‖ ≤
      Real.sqrt (a * b) * ‖FSKernel.dg (fun q => (e q : ℂ)) v‖ := by
  have hw := FSLattice.wschur Finset.univ Finset.univ
    (fun q p => κ q p * ((e q / e p : ℝ) : ℂ)) h h (fun p _ => hh p) ha
    (fun q _ => by
      have e1 : ∑ p, ‖κ q p * ((e q / e p : ℝ) : ℂ)‖ * h p = ∑ p, ‖κ q p‖ * (e q / e p) * h p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (he q) (he p))]
      rw [e1]; exact hrow q)
    (fun p _ => by
      have e1 : ∑ q, ‖κ q p * ((e q / e p : ℝ) : ℂ)‖ * h q = ∑ q, ‖κ q p‖ * (e q / e p) * h q := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos (he q) (he p))]
      rw [e1]; exact hcol p)
    (fun p => (e p : ℂ) * v.ofLp p)
  have e1 : ‖FSKernel.dg (fun q => (e q : ℂ)) (FSKernel.kop κ v)‖ ^ 2 =
      ∑ q, ‖∑ p, κ q p * ((e q / e p : ℝ) : ℂ) * ((e p : ℂ) * v.ofLp p)‖ ^ 2 := by
    rw [FSKernel.norm_sq_eq]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [FSKernel.dg_apply, FSKernel.kop_apply, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : (e p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (he p).ne'
    push_cast
    field_simp
  have e2 : ‖FSKernel.dg (fun q => (e q : ℂ)) v‖ ^ 2 = ∑ p, ‖(e p : ℂ) * v.ofLp p‖ ^ 2 := by
    rw [FSKernel.norm_sq_eq]; rfl
  have h2 : ‖FSKernel.dg (fun q => (e q : ℂ)) (FSKernel.kop κ v)‖ ^ 2 ≤
      (Real.sqrt (a * b) * ‖FSKernel.dg (fun q => (e q : ℂ)) v‖) ^ 2 := by
    rw [e1, mul_pow, Real.sq_sqrt (mul_nonneg ha hb), e2]
    exact hw
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

lemma rpow_ratio_row {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (α : ℝ) :
    x ^ α / y ^ α * y ^ (-(1 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) * (x / y) ^ (α + 1 / 2) := by
  rw [Real.div_rpow hx.le hy.le, Real.rpow_add hx, Real.rpow_add hy, Real.rpow_neg hx.le,
    Real.rpow_neg hy.le]
  have h1 := Real.rpow_pos_of_pos hx (1 / 2 : ℝ)
  have h2 := Real.rpow_pos_of_pos hy (1 / 2 : ℝ)
  have h3 := Real.rpow_pos_of_pos hx α
  have h4 := Real.rpow_pos_of_pos hy α
  field_simp

lemma rpow_ratio_col {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (α : ℝ) :
    x ^ α / y ^ α * x ^ (-(1 / 2 : ℝ)) = y ^ (-(1 / 2 : ℝ)) * (y / x) ^ (1 / 2 - α) := by
  rw [Real.div_rpow hy.le hx.le, Real.rpow_sub hy, Real.rpow_sub hx, Real.rpow_neg hx.le,
    Real.rpow_neg hy.le]
  have h1 := Real.rpow_pos_of_pos hx (1 / 2 : ℝ)
  have h2 := Real.rpow_pos_of_pos hy (1 / 2 : ℝ)
  have h3 := Real.rpow_pos_of_pos hx α
  have h4 := Real.rpow_pos_of_pos hy α
  field_simp

lemma norm_sig3K_symm (hL : 0 < L) (q p : Cfg eta n) :
    ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) p q‖ =
      ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) q p‖ := by
  rw [sig3K_skew hL q p, norm_neg, Complex.norm_conj]

/-- **`lem:weighted`** (eq:weightedconj): `‖E^α Σ₃^sp v‖ ≤ C_W ‖E^α v‖` for `|α| ≤ 1/2`. -/
theorem norm_wt_Sig3sp_le (hL : 0 < L) (hn : 2 ≤ n) {α : ℝ} (hα1 : -(1 / 2) ≤ α)
    (hα2 : α ≤ 1 / 2) (v : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) α (Sig3sp sys L n v)‖ ≤
      CW sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) α v‖ := by
  rw [wt_eq_dg (sys := sys) (L := L), wt_eq_dg (sys := sys) (L := L)]
  have hE : ∀ q, 0 < 1 + Asym sys L n q := fun q => one_add_asym_pos q
  have hCW := CW_nonneg (sys := sys) (n := n) hL
  have h := norm_conj_kop_le (FSKernel.divK (Asym sys L n) (h3gK sys L n))
    (fun q => (1 + Asym sys L n q) ^ α) (fun q => (1 + Asym sys L n q) ^ (-(1 / 2 : ℝ)))
    (fun q => Real.rpow_pos_of_pos (hE q) α) (fun q => Real.rpow_pos_of_pos (hE q) _) hCW hCW
    (fun q => by
      have e1 : ∑ p, ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) q p‖ *
          ((1 + Asym sys L n q) ^ α / (1 + Asym sys L n p) ^ α) *
            (1 + Asym sys L n p) ^ (-(1 / 2 : ℝ)) =
          (1 + Asym sys L n q) ^ (-(1 / 2 : ℝ)) *
            ∑ p, ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) p q‖ *
              ((1 + Asym sys L n q) / (1 + Asym sys L n p)) ^ (α + 1 / 2) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [mul_assoc, rpow_ratio_row (hE q) (hE p) α, norm_sig3K_symm hL q p]
        ring
      rw [e1, mul_comm (CW sys L n)]
      exact mul_le_mul_of_nonneg_left (col_sig3_weighted hL hn q (by linarith) (by linarith))
        (Real.rpow_pos_of_pos (hE q) _).le)
    (fun p => by
      have e1 : ∑ q, ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) q p‖ *
          ((1 + Asym sys L n q) ^ α / (1 + Asym sys L n p) ^ α) *
            (1 + Asym sys L n q) ^ (-(1 / 2 : ℝ)) =
          (1 + Asym sys L n p) ^ (-(1 / 2 : ℝ)) *
            ∑ q, ‖FSKernel.divK (Asym sys L n) (h3gK sys L n) q p‖ *
              ((1 + Asym sys L n p) / (1 + Asym sys L n q)) ^ (1 / 2 - α) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [mul_assoc, rpow_ratio_col (hE q) (hE p) α]
        ring
      rw [e1, mul_comm (CW sys L n)]
      exact mul_le_mul_of_nonneg_left (col_sig3_weighted hL hn p (by linarith) (by linarith))
        (Real.rpow_pos_of_pos (hE p) _).le)
    v
  rw [Real.sqrt_mul_self hCW] at h
  exact h

omit [Fintype ν] in
lemma norm_wt_neg_le {s : ℝ} (hs : s ≤ 0) (v : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) s v‖ ≤ ‖v‖ := by
  rw [wt_eq_dg (sys := sys) (L := L)]
  have h := FSKernel.norm_dg_le (fun q => (((1 + Asym sys L n q) ^ s : ℝ) : ℂ)) zero_le_one
    (fun q => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos
        (one_add_asym_pos q) s)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by
        have := Asym_nonneg (sys := sys) (L := L) q; linarith) hs) v
  simpa using h

/-- **The weighted completion hypothesis** (eq:completionweighted, on good states):
`‖E^{-1/4} Σ₃^sp W_N u‖ + ‖E^{1/4} Σ₃^sp u‖ ≤ C_W (√2 C_m + 1) M`. -/
theorem weighted_Sig3sp_good (hL : 0 < L) (hn : 2 ≤ n) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) {M : ℝ} {u : En eta n}
    (hu : IsGood sys L 1 M u) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (Sig3sp sys L n (VN sys L n u))‖ +
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (Sig3sp sys L n u)‖ ≤
      CW sys L n * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit + 1) * M := by
  have hCW := CW_nonneg (sys := sys) (n := n) hL
  have hCm := finiteCoulombPhysicalMassConstant_nonneg sys L Hunit
  have hW : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    linarith
  have h1 := norm_wt_Sig3sp_le (sys := sys) hL hn (α := -(1 / 4)) (by norm_num) (by norm_num)
    (VN sys L n u)
  have h1' := norm_wt_neg_le (sys := sys) (L := L) (s := -(1 / 4)) (by norm_num) (VN sys L n u)
  have h1'' := norm_VN_apply_le sys hL Hunit hPeriodic u
  have h2 := norm_wt_Sig3sp_le (sys := sys) hL hn (α := 1 / 4) (by norm_num) (by norm_num) u
  have h2' := wt_mono sys L n (by norm_num : (1 / 4 : ℝ) ≤ 1) u
  calc ‖FSSpectral.wt (sb eta n) (Asym sys L n) (-(1 / 4)) (Sig3sp sys L n (VN sys L n u))‖ +
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 4) (Sig3sp sys L n u)‖
      ≤ CW sys L n * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit *
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖) +
        CW sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
        apply add_le_add
        · exact h1.trans (mul_le_mul_of_nonneg_left (h1'.trans h1'') hCW)
        · exact h2.trans (mul_le_mul_of_nonneg_left h2' hCW)
    _ = CW sys L n * (Real.sqrt 2 * finiteCoulombPhysicalMassConstant sys L Hunit + 1) *
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hW (by positivity)

end FSNormal
