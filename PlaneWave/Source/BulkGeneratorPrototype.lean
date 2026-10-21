import PlaneWave.Certificate
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Flux/source scoping prototype: the bulk generator of the block normal form

Prototype of the scoping pass for the flux and source sections (`app:flux`, `app:source`), see
`dev/propagator_plan.md`, section "Flux and source sections: scoping pass".  It formalises the
operator-theoretic layer under the block normal form of `thm:src3` (manuscript lines 7875–7912)
and the gap lemma `lem:gap` (eq:gap):

* `gap`, `lattice_gap`: `lem:gap`, in an abstract real inner-product space and on the lattice;
* `tailFn_summable_and_le`: `Σ_{ν ∈ ℤ³, |ν| > R} |ν|⁻⁴ ≤ 104/R` for `R ≥ 1`;
* `SchurBound`, `HSBound`: Schur's test and the Hilbert–Schmidt test for kernel operators on
  `ℓ²(ι)`, the kernel operator as a bounded operator, its adjoint, and
  `SchurBound.exp_mem_unitary` (an anti-Hermitian kernel gives a skew-adjoint operator whose
  exponential is unitary);
* `bulkGenerator`: the generator `Σ_b = V_b/ω` of one interaction pair on `ℓ²(ℤ^{3η})` is
  bounded, `‖Σ_b‖ ≤ 20 c_w μ_ab/g² · 416/(3s)` (the manuscript's `C μ_pb/K`), skew-adjoint,
  `e^{Σ_b}` is unitary, and `[T, Σ_b] = V_b` holds kernel by kernel;
* `vbK_hs`, `E_mul_sigma`, `decS_sigmaGraph`, `exp_sigma_preserves_domain`: `V_b` is bounded
  (Hilbert–Schmidt, as every bulk-fed crossing has one end in the finite block `Q`),
  `(1 + E) Σ_b c = Σ_b ((1 + E) c) + V_b c` on `D(T)`, and `e^{Σ_b}` maps `D(T)` into itself
  (`e^{Σ_b} S = S e^{Σ'}` with `S = (1 + E)⁻¹` and `Σ' = Σ_b + V_b S` bounded);
* `bulkGenerator_release`: the same for the release file's types (`Lattice3`, `latticeNormSq`,
  `FourierConfig`, `coulombKineticEnergySymbol` of a `CoulombSystem`) and the Coulomb
  coefficients `c/|ν|²`.

Local names: `L3` is `Lattice3`, `nsq` is `latticeNormSq` (`nsq_eq_latticeNormSq` is `rfl`),
`Cfg eta` is `FourierConfig eta Lattice3`, `E m g` is the kinetic energy
`Σ_c g²|k_c|²/(2 m_c)` (`E_eq_kineticSymbol`).  Cutoffs are in lattice units: the cube `P` has
half-width `s` (`K = g s`), the bulk block `Q` is the Euclidean ball of radius `s/4` in every
register.
-/

set_option autoImplicit false

/-! ## Part Gap

Prototype: `lem:gap` (uniform off-resonance of bulk-fed transfers), eq:gap.
-/

open scoped RealInnerProductSpace

namespace FluxSourceTest

/-- The real-variable core of `lem:gap`.  `ip = ⟪k_p, ν⟫`, `ib = ⟪k_b, ν⟫`, `n = ‖ν‖`,
`P = ‖k_p‖²`, `x = 1/M_p`, `y = 1/m_b`. -/
lemma gap_core {K n P ip ib x y : ℝ} (hK : 0 < K) (hn : 0 ≤ n) (hx : 0 < x) (hy : 0 < y)
    (hP : P ≤ K ^ 2 / 16) (hip_lo : -(K / 4 * n) ≤ ip) (hip_hi : ip ≤ K / 4 * n)
    (hib : ib ≤ K / 4 * n) (hexit : K ^ 2 < P + 2 * ip + n ^ 2) :
    3 * K / 4 < n ∧
      3 * K ^ 2 / 32 * (x + y) ≤ (2 * ip + n ^ 2) * x / 2 + (n ^ 2 - 2 * ib) * y / 2 ∧
      n ^ 2 / 20 * (x + y) ≤ (2 * ip + n ^ 2) * x / 2 + (n ^ 2 - 2 * ib) * y / 2 := by
  have hn34 : 3 * K / 4 < n := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  refine ⟨hn34, ?_⟩
  -- the lower bound `ω ≥ (2 ip + n²) x / 2 + (n² - n K / 2) y / 2`
  have hω : (2 * ip + n ^ 2) * x / 2 + (n ^ 2 - K / 2 * n) * y / 2 ≤
      (2 * ip + n ^ 2) * x / 2 + (n ^ 2 - 2 * ib) * y / 2 := by
    have : (n ^ 2 - K / 2 * n) ≤ (n ^ 2 - 2 * ib) := by linarith
    nlinarith
  rcases le_or_gt n (5 * K / 4) with hcase | hcase
  · -- `3K/4 < n ≤ 5K/4`: the exit condition bounds `ip` from below
    have hip2 : 15 * K ^ 2 / 16 - n ^ 2 < 2 * ip := by linarith
    have hA : 15 * K ^ 2 / 32 * x ≤ (2 * ip + n ^ 2) * x / 2 := by nlinarith
    have hB : 3 * K ^ 2 / 32 * y ≤ (n ^ 2 - K / 2 * n) * y / 2 := by
      have : 3 * K ^ 2 / 16 ≤ n ^ 2 - K / 2 * n := by nlinarith
      nlinarith
    have h1 : 3 * K ^ 2 / 32 * (x + y) ≤
        (2 * ip + n ^ 2) * x / 2 + (n ^ 2 - 2 * ib) * y / 2 := by nlinarith
    refine ⟨h1, ?_⟩
    have : n ^ 2 / 20 ≤ 3 * K ^ 2 / 32 := by nlinarith
    nlinarith
  · -- `n > 5K/4`: the trivial bound `ip ≥ -K n / 4` suffices
    have hA : (n ^ 2 - K / 2 * n) * x / 2 ≤ (2 * ip + n ^ 2) * x / 2 := by nlinarith
    have hsum : (n ^ 2 - K / 2 * n) * (x + y) / 2 ≤
        (2 * ip + n ^ 2) * x / 2 + (n ^ 2 - 2 * ib) * y / 2 := by nlinarith
    have hq1 : 15 * K ^ 2 / 16 ≤ n ^ 2 - K / 2 * n := by nlinarith
    have hq2 : 3 * n ^ 2 / 5 ≤ n ^ 2 - K / 2 * n := by nlinarith
    constructor
    · nlinarith
    · nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The kinetic mismatch of the transfer `ν` on the pair `(p, b)`:
`ω_ν(k) = (2 k_p·ν + |ν|²)/(2 M_p) + (|ν|² − 2 k_b·ν)/(2 m_b)`. -/
noncomputable def mismatch (M m : ℝ) (kp kb ν : E) : ℝ :=
  (2 * ⟪kp, ν⟫ + ‖ν‖ ^ 2) / (2 * M) + (‖ν‖ ^ 2 - 2 * ⟪kb, ν⟫) / (2 * m)

lemma mismatch_eq (M m : ℝ) (kp kb ν : E) :
    mismatch M m kp kb ν = (‖kp + ν‖ ^ 2 - ‖kp‖ ^ 2) / (2 * M) +
      (‖kb - ν‖ ^ 2 - ‖kb‖ ^ 2) / (2 * m) := by
  unfold mismatch
  rw [norm_add_sq_real, norm_sub_sq_real]
  ring

/-- The exchange `(k_p, M_p) ↔ (-k_b, m_b)` leaves the mismatch invariant. -/
lemma mismatch_swap (M m : ℝ) (kp kb ν : E) :
    mismatch m M (-kb) (-kp) ν = mismatch M m kp kb ν := by
  unfold mismatch
  simp only [inner_neg_left]
  ring

/-- `lem:gap`, first exit case. -/
lemma gap_of_exit_p {M m K : ℝ} (hM : 0 < M) (hm : 0 < m) (hK : 0 < K) {kp kb ν : E}
    (hkp : ‖kp‖ ≤ K / 4) (hkb : ‖kb‖ ≤ K / 4) (hexit : K < ‖kp + ν‖) :
    3 * K / 4 < ‖ν‖ ∧ 3 * K ^ 2 / 32 * (1 / M + 1 / m) ≤ mismatch M m kp kb ν ∧
      ‖ν‖ ^ 2 / 20 * (1 / M + 1 / m) ≤ mismatch M m kp kb ν := by
  have hn : 0 ≤ ‖ν‖ := norm_nonneg ν
  have hcs_p : |⟪kp, ν⟫| ≤ K / 4 * ‖ν‖ :=
    (abs_real_inner_le_norm kp ν).trans (mul_le_mul_of_nonneg_right hkp hn)
  have hcs_b : ⟪kb, ν⟫ ≤ K / 4 * ‖ν‖ :=
    (real_inner_le_norm kb ν).trans (mul_le_mul_of_nonneg_right hkb hn)
  have hP : ‖kp‖ ^ 2 ≤ K ^ 2 / 16 := by
    have := norm_nonneg kp
    nlinarith
  have hexit2 : K ^ 2 < ‖kp‖ ^ 2 + 2 * ⟪kp, ν⟫ + ‖ν‖ ^ 2 := by
    rw [← norm_add_sq_real]
    exact pow_lt_pow_left₀ hexit hK.le two_ne_zero
  obtain ⟨h1, h2, h3⟩ := gap_core (x := 1 / M) (y := 1 / m) hK hn (by positivity) (by positivity)
    hP (neg_le_of_abs_le hcs_p) (le_of_abs_le hcs_p) hcs_b hexit2
  have hω : mismatch M m kp kb ν =
      (2 * ⟪kp, ν⟫ + ‖ν‖ ^ 2) * (1 / M) / 2 + (‖ν‖ ^ 2 - 2 * ⟪kb, ν⟫) * (1 / m) / 2 := by
    unfold mismatch
    field_simp
  rw [hω]
  exact ⟨h1, h2, h3⟩

/-- **`lem:gap`** (eq:gap): if both momenta of the pair are at most `K/4` and the transfer takes
one of them beyond `K`, then `‖ν‖ > 3K/4` and the mismatch is at least `3K²/(32 μ)` and at least
`‖ν‖²/(20 μ)`, where `μ⁻¹ = M⁻¹ + m⁻¹`. -/
theorem gap {M m K : ℝ} (hM : 0 < M) (hm : 0 < m) (hK : 0 < K) {kp kb ν : E}
    (hkp : ‖kp‖ ≤ K / 4) (hkb : ‖kb‖ ≤ K / 4) (hexit : K < ‖kp + ν‖ ∨ K < ‖kb - ν‖) :
    3 * K / 4 < ‖ν‖ ∧ 3 * K ^ 2 / 32 * (1 / M + 1 / m) ≤ mismatch M m kp kb ν ∧
      ‖ν‖ ^ 2 / 20 * (1 / M + 1 / m) ≤ mismatch M m kp kb ν := by
  rcases hexit with h | h
  · exact gap_of_exit_p hM hm hK hkp hkb h
  · have h' : K < ‖-kb + ν‖ := by
      rw [show -kb + ν = -(kb - ν) by abel, norm_neg]
      exact h
    have := gap_of_exit_p (kp := -kb) (kb := -kp) (ν := ν) hm hM hK (by rwa [norm_neg])
      (by rwa [norm_neg]) h'
    rw [mismatch_swap, add_comm (1 / m)] at this
    exact this

end FluxSourceTest

/-! ## Part LatticeTail

Prototype: the lattice tail sum `Σ_{ν ∈ ℤ³, |ν| > R} |ν|⁻⁴ ≤ 104 / R` for `R ≥ 1`.
-/

namespace FluxSourceTest

/-- The integer lattice `ℤ³` (as `Lattice3` of the release file). -/
abbrev L3 := Fin 3 → ℤ

/-- Squared Euclidean length (as `latticeNormSq` of the release file). -/
def nsq (ν : L3) : ℝ := (ν 0 : ℝ) ^ 2 + (ν 1 : ℝ) ^ 2 + (ν 2 : ℝ) ^ 2

lemma nsq_nonneg (ν : L3) : 0 ≤ nsq ν := by unfold nsq; positivity

/-- The cube `{ν : ‖ν‖_∞ ≤ N}`. -/
noncomputable def box (N : ℕ) : Finset L3 := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

lemma mem_box {N : ℕ} {ν : L3} : ν ∈ box N ↔ ∀ i, -(N : ℤ) ≤ ν i ∧ ν i ≤ N := by
  simp [box, Fintype.mem_piFinset]

lemma card_box (N : ℕ) : (box N).card = (2 * N + 1) ^ 3 := by
  simp only [box, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

lemma box_subset_succ (N : ℕ) : box N ⊆ box (N + 1) := by
  intro ν hν
  rw [mem_box] at hν ⊢
  intro i
  have := hν i
  push_cast
  constructor <;> linarith [this.1, this.2]

lemma exists_box (s : Finset L3) : ∃ N : ℕ, s ⊆ box N := by
  refine ⟨s.sup fun ν => (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs, fun ν hν => ?_⟩
  have hle : (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs ≤
      s.sup fun ν => (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs :=
    Finset.le_sup (f := fun ν => (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs) hν
  rw [mem_box]
  intro i
  have hi : (ν i).natAbs ≤ (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs := by
    fin_cases i <;> simp <;> omega
  have h1 : ν i ≤ ((ν i).natAbs : ℤ) := Int.le_natAbs
  have h2 : -ν i ≤ ((ν i).natAbs : ℤ) := by
    have := Int.le_natAbs (a := -ν i); rwa [Int.natAbs_neg] at this
  have h3 : ((ν i).natAbs : ℤ) ≤
      ((s.sup fun ν => (ν 0).natAbs + (ν 1).natAbs + (ν 2).natAbs : ℕ) : ℤ) := by
    exact_mod_cast hi.trans hle
  constructor <;> linarith

lemma card_shell (N : ℕ) : ((box (N + 1)) \ box N).card ≤ 26 * (N + 1) ^ 2 := by
  rw [Finset.card_sdiff_of_subset (box_subset_succ N), card_box, card_box]
  have h : (2 * (N + 1) + 1) ^ 3 - (2 * N + 1) ^ 3 = 24 * (N + 1) ^ 2 + 2 := by
    have : (2 * N + 1) ^ 3 ≤ (2 * (N + 1) + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    zify [this]
    ring
  rw [h]
  have h1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (Nat.succ_pos N)
  linarith

/-- On the shell `box (N+1) \ box N`: `(N+1)² ≤ |ν|² ≤ 3 (N+1)²`. -/
lemma nsq_shell {N : ℕ} {ν : L3} (hν : ν ∈ (box (N + 1)) \ box N) :
    ((N : ℝ) + 1) ^ 2 ≤ nsq ν ∧ nsq ν ≤ 3 * ((N : ℝ) + 1) ^ 2 := by
  rw [Finset.mem_sdiff, mem_box, mem_box] at hν
  obtain ⟨hin, hout⟩ := hν
  have hsq : ∀ i, (ν i : ℝ) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by
    intro i
    obtain ⟨h1, h2⟩ := hin i
    have h1' : -((N : ℝ) + 1) ≤ ν i := by
      have : (-((N : ℤ) + 1) : ℤ) ≤ ν i := by push_cast at h1; linarith
      exact_mod_cast this
    have h2' : (ν i : ℝ) ≤ (N : ℝ) + 1 := by
      have : ν i ≤ (N : ℤ) + 1 := by push_cast at h2; linarith
      exact_mod_cast this
    nlinarith
  push Not at hout
  obtain ⟨i, hi⟩ := hout
  have hbig : ((N : ℝ) + 1) ^ 2 ≤ (ν i : ℝ) ^ 2 := by
    by_cases hlo : -(N : ℤ) ≤ ν i
    · have : (N : ℤ) + 1 ≤ ν i := by have := hi hlo; omega
      have : (N : ℝ) + 1 ≤ ν i := by exact_mod_cast this
      nlinarith
    · have : ν i ≤ -(N : ℤ) - 1 := by omega
      have : (ν i : ℝ) ≤ -(N : ℝ) - 1 := by exact_mod_cast this
      nlinarith
  have h0 := sq_nonneg (ν 0 : ℝ)
  have h1 := sq_nonneg (ν 1 : ℝ)
  have h2 := sq_nonneg (ν 2 : ℝ)
  unfold nsq
  constructor
  · fin_cases i <;> simp at hbig <;> linarith
  · linarith [hsq 0, hsq 1, hsq 2]

/-- The tail function: `|ν|⁻⁴` beyond the radius `R`. -/
noncomputable def tailFn (R : ℝ) (ν : L3) : ℝ := if R ^ 2 < nsq ν then (nsq ν)⁻¹ ^ 2 else 0

lemma tailFn_nonneg (R : ℝ) (ν : L3) : 0 ≤ tailFn R ν := by
  unfold tailFn; split_ifs <;> positivity

lemma tailFn_le_shell {R : ℝ} (N : ℕ) {ν : L3} (hν : ν ∈ (box (N + 1)) \ box N) :
    tailFn R ν ≤ if R ^ 2 < 3 * ((N : ℝ) + 1) ^ 2 then (((N : ℝ) + 1) ^ 2)⁻¹ ^ 2 else 0 := by
  obtain ⟨hlo, hhi⟩ := nsq_shell hν
  unfold tailFn
  have hpos : 0 < ((N : ℝ) + 1) ^ 2 := by positivity
  split_ifs with h1 h2
  · exact pow_le_pow_left₀ (inv_nonneg.mpr (nsq_nonneg ν)) (inv_anti₀ hpos hlo) 2
  · exact absurd (h1.trans_le hhi) h2
  · positivity
  · exact le_refl _

lemma box_zero : box 0 = {0} := by
  ext ν
  rw [mem_box, Finset.mem_singleton]
  constructor
  · intro h; funext i; have := h i; simp at this ⊢; omega
  · rintro rfl; intro i; simp

lemma sum_box_tailFn_le (R : ℝ) (N : ℕ) :
    ∑ ν ∈ box N, tailFn R ν ≤
      ∑ j ∈ Finset.range N,
        if R ^ 2 < 3 * ((j : ℝ) + 1) ^ 2 then 26 / ((j : ℝ) + 1) ^ 2 else 0 := by
  induction N with
  | zero =>
    rw [box_zero, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty]
    unfold tailFn
    have : nsq 0 = 0 := by simp [nsq]
    rw [this, if_neg (by nlinarith)]
  | succ N ih =>
    have hsplit : box (N + 1) = box N ∪ ((box (N + 1)) \ box N) :=
      (Finset.union_sdiff_of_subset (box_subset_succ N)).symm
    rw [hsplit, Finset.sum_union Finset.disjoint_sdiff, Finset.sum_range_succ]
    refine add_le_add ih ?_
    calc ∑ ν ∈ box (N + 1) \ box N, tailFn R ν
        ≤ ∑ _ν ∈ box (N + 1) \ box N,
            (if R ^ 2 < 3 * ((N : ℝ) + 1) ^ 2 then (((N : ℝ) + 1) ^ 2)⁻¹ ^ 2 else 0) :=
          Finset.sum_le_sum fun ν hν => tailFn_le_shell N hν
      _ = ((box (N + 1)) \ box N).card *
            (if R ^ 2 < 3 * ((N : ℝ) + 1) ^ 2 then (((N : ℝ) + 1) ^ 2)⁻¹ ^ 2 else 0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (26 * ((N : ℝ) + 1) ^ 2) *
            (if R ^ 2 < 3 * ((N : ℝ) + 1) ^ 2 then (((N : ℝ) + 1) ^ 2)⁻¹ ^ 2 else 0) := by
          refine mul_le_mul_of_nonneg_right ?_ (by split_ifs <;> positivity)
          exact_mod_cast card_shell N
      _ = if R ^ 2 < 3 * ((N : ℝ) + 1) ^ 2 then 26 / ((N : ℝ) + 1) ^ 2 else 0 := by
          split_ifs
          · field_simp
          · ring

/-- Telescoping: with `t n = 1/(n - 1/2)`, `Σ_{j < M, J ≤ j+1} (t (j+1) - t (j+2))` is
`t J - t (M+1)` if `J ≤ M` and `0` otherwise. -/
lemma telescope (J : ℕ) (hJ : 1 ≤ J) (M : ℕ) :
    ∑ j ∈ Finset.range M, (if J ≤ j + 1 then
      (1 / ((j : ℝ) + 1 - 1 / 2) - 1 / ((j : ℝ) + 2 - 1 / 2)) else 0) =
      if J ≤ M then 1 / ((J : ℝ) - 1 / 2) - 1 / ((M : ℝ) + 1 - 1 / 2) else 0 := by
  induction M with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    rw [if_neg (by omega)]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h1 : J ≤ M
    · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]
      push_cast; ring
    · by_cases h2 : J = M + 1
      · subst h2
        rw [if_neg h1, if_pos le_rfl, if_pos le_rfl]
        push_cast; ring
      · rw [if_neg h1, if_neg (by omega), if_neg (by omega)]
        simp

/-- The sum of `1/(j+1)²` over the `j < N` with `3 (j+1)² > R²` is at most `4/R` for `R ≥ 1`. -/
lemma sum_shell_bound {R : ℝ} (hR : 1 ≤ R) (N : ℕ) :
    ∑ j ∈ Finset.range N, (if R ^ 2 < 3 * ((j : ℝ) + 1) ^ 2 then 1 / ((j : ℝ) + 1) ^ 2 else 0)
      ≤ 4 / R := by
  set J : ℕ := ⌈R / 2⌉₊ with hJ
  have hJpos : 1 ≤ J := Nat.one_le_iff_ne_zero.mpr (by
    rw [hJ]; exact (Nat.ceil_pos.mpr (by linarith)).ne')
  have hRJ : R / 2 ≤ J := Nat.le_ceil _
  have hactive : ∀ j : ℕ, R ^ 2 < 3 * ((j : ℝ) + 1) ^ 2 → J ≤ j + 1 := by
    intro j hj
    by_contra hcon
    have hlt : j + 1 < J := by omega
    have : ((j : ℝ) + 1) < R / 2 := by
      have := Nat.lt_ceil.mp hlt
      push_cast at this
      linarith
    nlinarith
  have hterm : ∀ j ∈ Finset.range N,
      (if R ^ 2 < 3 * ((j : ℝ) + 1) ^ 2 then 1 / ((j : ℝ) + 1) ^ 2 else 0) ≤
        (if J ≤ j + 1 then
          (1 / ((j : ℝ) + 1 - 1 / 2) - 1 / ((j : ℝ) + 2 - 1 / 2)) else 0) := by
    intro j _
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hkey : 1 / ((j : ℝ) + 1) ^ 2 ≤
        1 / ((j : ℝ) + 1 - 1 / 2) - 1 / ((j : ℝ) + 2 - 1 / 2) := by
      have ha : (0 : ℝ) < (j : ℝ) + 1 - 1 / 2 := by linarith
      have hb : (0 : ℝ) < (j : ℝ) + 2 - 1 / 2 := by linarith
      rw [div_sub_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    split_ifs with h1 h2
    · exact hkey
    · exact absurd (hactive j h1) h2
    · exact le_trans (by positivity) hkey
    · exact le_refl _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [telescope J hJpos]
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJpos
  split_ifs
  · have h1 : 0 ≤ 1 / ((N : ℝ) + 1 - 1 / 2) := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      exact div_nonneg zero_le_one (by linarith)
    have h2 : 1 / ((J : ℝ) - 1 / 2) ≤ 4 / R := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  · positivity

/-- **The lattice tail sum**: for `R ≥ 1`, `Σ_{ν ∈ ℤ³, |ν| > R} |ν|⁻⁴ ≤ 104 / R`; in particular
the tail function is summable. -/
theorem tailFn_summable_and_le {R : ℝ} (hR : 1 ≤ R) :
    Summable (tailFn R) ∧ ∑' ν, tailFn R ν ≤ 104 / R := by
  have hfin : ∀ s : Finset L3, ∑ ν ∈ s, tailFn R ν ≤ 104 / R := by
    intro s
    obtain ⟨N, hN⟩ := exists_box s
    calc ∑ ν ∈ s, tailFn R ν ≤ ∑ ν ∈ box N, tailFn R ν :=
          Finset.sum_le_sum_of_subset_of_nonneg hN fun ν _ _ => tailFn_nonneg R ν
      _ ≤ ∑ j ∈ Finset.range N,
            if R ^ 2 < 3 * ((j : ℝ) + 1) ^ 2 then 26 / ((j : ℝ) + 1) ^ 2 else 0 :=
          sum_box_tailFn_le R N
      _ = 26 * ∑ j ∈ Finset.range N,
            (if R ^ 2 < 3 * ((j : ℝ) + 1) ^ 2 then 1 / ((j : ℝ) + 1) ^ 2 else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> ring
      _ ≤ 26 * (4 / R) := mul_le_mul_of_nonneg_left (sum_shell_bound hR N) (by norm_num)
      _ = 104 / R := by ring
  have hs : Summable (tailFn R) :=
    summable_of_sum_le (fun ν => tailFn_nonneg R ν) hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

end FluxSourceTest

/-! ## Part Schur

Prototype: kernel operators on `ℓ²(ι)` and Schur's test.
-/

open scoped ComplexConjugate lp ENNReal NNReal InnerProductSpace

namespace FluxSourceTest

variable {ι : Type*}

/-- Schur bounds for a kernel `κ` (output index first): every row sum of `|κ|` is at most `A`,
every column sum at most `B`. -/
structure SchurBound (κ : ι → ι → ℂ) (A B : ℝ) : Prop where
  row_summable : ∀ i, Summable fun j => ‖κ i j‖
  row_le : ∀ i, ∑' j, ‖κ i j‖ ≤ A
  col_summable : ∀ j, Summable fun i => ‖κ i j‖
  col_le : ∀ j, ∑' i, ‖κ i j‖ ≤ B

/-- The kernel applied to a vector, coordinatewise. -/
noncomputable def kerApply (κ : ι → ι → ℂ) (u : ι → ℂ) (i : ι) : ℂ :=
  ∑' j, κ i j * u j

section Coord

variable (u : lp (fun _ : ι => ℂ) 2)

lemma norm_coord_le (j : ι) : ‖u j‖ ≤ ‖u‖ :=
  lp.norm_apply_le_norm (by norm_num) u j

lemma summable_sq_coord : Summable fun j => ‖u j‖ ^ 2 := by
  have := (lp.memℓp u).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa using this

lemma tsum_sq_coord : ∑' j, ‖u j‖ ^ 2 = ‖u‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) u
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
  exact this.symm

end Coord

namespace SchurBound

variable {κ : ι → ι → ℂ} {A B : ℝ}

lemma A_nonneg [Nonempty ι] (h : SchurBound κ A B) : 0 ≤ A :=
  (tsum_nonneg fun _ => norm_nonneg _).trans (h.row_le (Classical.arbitrary ι))

lemma B_nonneg [Nonempty ι] (h : SchurBound κ A B) : 0 ≤ B :=
  (tsum_nonneg fun _ => norm_nonneg _).trans (h.col_le (Classical.arbitrary ι))

variable (h : SchurBound κ A B) (u : lp (fun _ : ι => ℂ) 2)
include h

lemma summable_row_mul_norm (i : ι) : Summable fun j => ‖κ i j‖ * ‖u j‖ :=
  ((h.row_summable i).mul_right ‖u‖).of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun j => mul_le_mul_of_nonneg_left (norm_coord_le u j) (norm_nonneg _))

lemma summable_row_mul_sq (i : ι) : Summable fun j => ‖κ i j‖ * ‖u j‖ ^ 2 :=
  ((h.row_summable i).mul_right (‖u‖ ^ 2)).of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
    (fun j => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_coord_le u j) 2) (norm_nonneg _))

lemma summable_row_apply (i : ι) : Summable fun j => κ i j * u j :=
  Summable.of_norm ((h.summable_row_mul_norm u i).congr fun _ => (norm_mul _ _).symm)

/-- Cauchy–Schwarz in the row: `|Σ_j κ_ij u_j|² ≤ A Σ_j |κ_ij| |u_j|²`. -/
lemma norm_kerApply_sq_le (i : ι) :
    ‖kerApply κ u i‖ ^ 2 ≤ A * ∑' j, ‖κ i j‖ * ‖u j‖ ^ 2 := by
  have h1 : ‖kerApply κ u i‖ ≤ ∑' j, ‖κ i j‖ * ‖u j‖ := by
    unfold kerApply
    refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
    · exact (h.summable_row_mul_norm u i).congr fun j => (norm_mul _ _).symm
    · exact tsum_congr fun j => norm_mul _ _
  -- write `|κ| |u| = √|κ| · (√|κ| |u|)` and apply Hölder with `p = q = 2`
  have hf : ∀ j, 0 ≤ Real.sqrt ‖κ i j‖ := fun _ => Real.sqrt_nonneg _
  have hg : ∀ j, 0 ≤ Real.sqrt ‖κ i j‖ * ‖u j‖ := fun _ => mul_nonneg (Real.sqrt_nonneg _)
    (norm_nonneg _)
  have hf2 : Summable fun j => Real.sqrt ‖κ i j‖ ^ (2 : ℝ) := by
    refine (h.row_summable i).congr fun j => ?_
    rw [Real.rpow_two, Real.sq_sqrt (norm_nonneg _)]
  have hg2 : Summable fun j => (Real.sqrt ‖κ i j‖ * ‖u j‖) ^ (2 : ℝ) := by
    refine (h.summable_row_mul_sq u i).congr fun j => ?_
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (norm_nonneg _)]
  have hH := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2)
    Real.HolderConjugate.two_two hf hg hf2 hg2
  have heq : ∀ j, Real.sqrt ‖κ i j‖ * (Real.sqrt ‖κ i j‖ * ‖u j‖) = ‖κ i j‖ * ‖u j‖ := by
    intro j
    rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
  simp only [heq] at hH
  have hrow : ∑' j, Real.sqrt ‖κ i j‖ ^ (2 : ℝ) = ∑' j, ‖κ i j‖ :=
    tsum_congr fun j => by rw [Real.rpow_two, Real.sq_sqrt (norm_nonneg _)]
  have hsq : ∑' j, (Real.sqrt ‖κ i j‖ * ‖u j‖) ^ (2 : ℝ) = ∑' j, ‖κ i j‖ * ‖u j‖ ^ 2 :=
    tsum_congr fun j => by rw [Real.rpow_two, mul_pow, Real.sq_sqrt (norm_nonneg _)]
  rw [hrow, hsq] at hH
  have hS0 : 0 ≤ ∑' j, ‖κ i j‖ := tsum_nonneg fun _ => norm_nonneg _
  have hT0 : 0 ≤ ∑' j, ‖κ i j‖ * ‖u j‖ ^ 2 :=
    tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hn0 : 0 ≤ ‖kerApply κ u i‖ := norm_nonneg _
  calc ‖kerApply κ u i‖ ^ 2
      ≤ ((∑' j, ‖κ i j‖) ^ (1 / 2 : ℝ) * (∑' j, ‖κ i j‖ * ‖u j‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hn0 (h1.trans hH) 2
    _ = (∑' j, ‖κ i j‖) * ∑' j, ‖κ i j‖ * ‖u j‖ ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hS0,
          ← Real.rpow_mul hT0]
        norm_num
    _ ≤ A * ∑' j, ‖κ i j‖ * ‖u j‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (h.row_le i) hT0

/-- The double sum `Σ_{i,j} |κ_ij| |u_j|²` (indexed by `(j, i)`) is summable. -/
lemma summable_double : Summable fun x : ι × ι => ‖κ x.2 x.1‖ * ‖u x.1‖ ^ 2 := by
  have hslice : ∀ j, Summable fun i => ‖κ i j‖ * ‖u j‖ ^ 2 :=
    fun j => (h.col_summable j).mul_right _
  have hout : Summable fun j => ∑' i, ‖κ i j‖ * ‖u j‖ ^ 2 := by
    refine ((summable_sq_coord u).mul_left B).of_nonneg_of_le
      (fun j => tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)) fun j => ?_
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (h.col_le j) (sq_nonneg _)
  exact (summable_prod_of_nonneg fun x => mul_nonneg (norm_nonneg _) (sq_nonneg _)).2
    ⟨hslice, hout⟩

lemma summable_kerApply_sq [Nonempty ι] : (Summable fun i => ‖kerApply κ u i‖ ^ 2) ∧
    ∑' i, ‖kerApply κ u i‖ ^ 2 ≤ A * B * ‖u‖ ^ 2 := by
  have hd := h.summable_double u
  -- the swapped double sum is summable as well
  have hd' : Summable fun x : ι × ι => ‖κ x.1 x.2‖ * ‖u x.2‖ ^ 2 :=
    (Equiv.prodComm ι ι).summable_iff.mpr hd |>.congr fun x => rfl
  have hrowsum : Summable fun i => ∑' j, ‖κ i j‖ * ‖u j‖ ^ 2 := hd'.prod
  have hle : ∀ i, ‖kerApply κ u i‖ ^ 2 ≤ A * ∑' j, ‖κ i j‖ * ‖u j‖ ^ 2 :=
    h.norm_kerApply_sq_le u
  have hs : Summable fun i => ‖kerApply κ u i‖ ^ 2 :=
    (hrowsum.mul_left A).of_nonneg_of_le (fun _ => sq_nonneg _) hle
  refine ⟨hs, ?_⟩
  have hswap : ∑' i, ∑' j, ‖κ i j‖ * ‖u j‖ ^ 2 = ∑' j, ∑' i, ‖κ i j‖ * ‖u j‖ ^ 2 := by
    rw [← hd'.tsum_prod, ← hd.tsum_prod]
    exact ((Equiv.prodComm ι ι).tsum_eq _).symm.trans rfl
  have hcol : ∑' j, ∑' i, ‖κ i j‖ * ‖u j‖ ^ 2 ≤ B * ‖u‖ ^ 2 := by
    rw [← tsum_sq_coord u, ← tsum_mul_left]
    refine hd.prod.tsum_le_tsum (fun j => ?_) ((summable_sq_coord u).mul_left B)
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (h.col_le j) (sq_nonneg _)
  calc ∑' i, ‖kerApply κ u i‖ ^ 2 ≤ ∑' i, A * ∑' j, ‖κ i j‖ * ‖u j‖ ^ 2 :=
        hs.tsum_le_tsum hle (hrowsum.mul_left A)
    _ = A * ∑' j, ∑' i, ‖κ i j‖ * ‖u j‖ ^ 2 := by rw [tsum_mul_left, hswap]
    _ ≤ A * (B * ‖u‖ ^ 2) := mul_le_mul_of_nonneg_left hcol h.A_nonneg
    _ = A * B * ‖u‖ ^ 2 := by ring

lemma memℓp_kerApply [Nonempty ι] : Memℓp (kerApply κ u) 2 := by
  refine memℓp_gen ?_
  simpa using (h.summable_kerApply_sq u).1

end SchurBound

/-! ### The kernel operator, its adjoint, and the unitary exponential -/

/-- The conjugate-transposed kernel. -/
def adjKernel (κ : ι → ι → ℂ) : ι → ι → ℂ := fun i j => conj (κ j i)

namespace SchurBound

variable {κ : ι → ι → ℂ} {A B : ℝ}

lemma adj (h : SchurBound κ A B) : SchurBound (adjKernel κ) B A where
  row_summable i := by simpa [adjKernel] using h.col_summable i
  row_le i := by simpa [adjKernel] using h.col_le i
  col_summable j := by simpa [adjKernel] using h.row_summable j
  col_le j := by simpa [adjKernel] using h.row_le j

variable (h : SchurBound κ A B)
include h

lemma norm_kerApply_le [Nonempty ι] (u : lp (fun _ : ι => ℂ) 2) :
    ‖(⟨kerApply κ u, h.memℓp_kerApply u⟩ : lp (fun _ : ι => ℂ) 2)‖ ≤
      Real.sqrt (A * B) * ‖u‖ := by
  set f : lp (fun _ : ι => ℂ) 2 := ⟨kerApply κ u, h.memℓp_kerApply u⟩
  have hsq : ‖f‖ ^ 2 ≤ A * B * ‖u‖ ^ 2 := by
    rw [← tsum_sq_coord f]
    exact (h.summable_kerApply_sq u).2
  have hAB : 0 ≤ A * B := mul_nonneg h.A_nonneg h.B_nonneg
  calc ‖f‖ = Real.sqrt (‖f‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (A * B * ‖u‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (A * B) * ‖u‖ := by
        rw [Real.sqrt_mul hAB, Real.sqrt_sq (norm_nonneg _)]

lemma kerApply_add (u v : lp (fun _ : ι => ℂ) 2) :
    kerApply κ ⇑(u + v) = kerApply κ ⇑u + kerApply κ ⇑v := by
  funext i
  simp only [kerApply, Pi.add_apply, lp.coeFn_add, mul_add]
  exact (h.summable_row_apply u i).tsum_add (h.summable_row_apply v i)

omit h in
lemma kerApply_smul (c : ℂ) (u : lp (fun _ : ι => ℂ) 2) :
    kerApply κ ⇑(c • u) = c • kerApply κ ⇑u := by
  funext i
  simp only [kerApply, Pi.smul_apply, lp.coeFn_smul, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

/-- The kernel operator as a continuous linear map on `ℓ²`, with `‖·‖ ≤ √(AB)` (Schur's test). -/
noncomputable def toCLM [Nonempty ι] : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨kerApply κ u, h.memℓp_kerApply u⟩
      map_add' := fun u v => lp.ext (h.kerApply_add u v)
      map_smul' := fun c u => lp.ext (kerApply_smul c u) }
    (Real.sqrt (A * B)) h.norm_kerApply_le

lemma toCLM_apply [Nonempty ι] (u : lp (fun _ : ι => ℂ) 2) (i : ι) : h.toCLM u i = kerApply κ u i := rfl

lemma norm_toCLM_le [Nonempty ι] : ‖h.toCLM‖ ≤ Real.sqrt (A * B) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

/-- The adjoint of the kernel operator is the operator of the conjugate-transposed kernel. -/
lemma inner_toCLM [Nonempty ι] (u v : lp (fun _ : ι => ℂ) 2) :
    inner ℂ (h.toCLM u) v = inner ℂ u (h.adj.toCLM v) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  -- the double series `F i j = conj κ_ij · conj u_j · v_i`
  set F : ι → ι → ℂ := fun i j => conj (κ i j) * conj (u j) * v i with hF
  have hnormF : ∀ i j, ‖F i j‖ ≤ (‖κ i j‖ * ‖u j‖ ^ 2 + ‖κ i j‖ * ‖v i‖ ^ 2) / 2 := by
    intro i j
    simp only [hF, norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (κ i j), sq_nonneg (‖u j‖ - ‖v i‖), norm_nonneg (u j), norm_nonneg (v i),
      mul_nonneg (norm_nonneg (κ i j)) (sq_nonneg (‖u j‖ - ‖v i‖))]
  have hs1 : Summable fun x : ι × ι => ‖κ x.1 x.2‖ * ‖u x.2‖ ^ 2 :=
    (Equiv.prodComm ι ι).summable_iff.mpr (h.summable_double u) |>.congr fun x => rfl
  have hs2 : Summable fun x : ι × ι => ‖κ x.1 x.2‖ * ‖v x.1‖ ^ 2 :=
    (h.adj.summable_double v).congr fun x => by simp [adjKernel]
  have hFs : Summable (Function.uncurry F) := by
    exact Summable.of_norm_bounded ((hs1.add hs2).div_const 2) fun x => hnormF x.1 x.2
  have hrow : ∀ i, Summable (F i) := fun i => hFs.prod_factor i
  have hcol : ∀ j, Summable fun i => F i j := fun j => hFs.prod_symm.prod_factor j
  -- left side
  have hL : ∀ i, inner ℂ (h.toCLM u i) (v i) = ∑' j, F i j := by
    intro i
    rw [toCLM_apply, kerApply, RCLike.inner_apply, starRingEnd_apply, tsum_star,
      ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [hF, star_mul', starRingEnd_apply]
    ring
  -- right side
  have hR : ∀ j, inner ℂ (u j) (h.adj.toCLM v j) = ∑' i, F i j := by
    intro j
    rw [toCLM_apply, kerApply, RCLike.inner_apply, ← tsum_mul_right]
    refine tsum_congr fun i => ?_
    simp only [hF, adjKernel]
    ring
  simp only [hL, hR]
  exact (hFs.tsum_comm' hrow hcol).symm

lemma adjoint_toCLM [Nonempty ι] : ContinuousLinearMap.adjoint h.toCLM = h.adj.toCLM := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [← inner_conj_symm, ← h.inner_toCLM y x, inner_conj_symm]

end SchurBound

/-- A kernel operator whose kernel is anti-Hermitian (`conj κ_ji = -κ_ij`) is skew-adjoint, and its
exponential is unitary. -/
theorem SchurBound.exp_mem_unitary [Nonempty ι] {κ : ι → ι → ℂ} {A B : ℝ}
    (h : SchurBound κ A B) (hanti : ∀ i j, conj (κ j i) = -κ i j) :
    h.toCLM ∈ skewAdjoint (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) ∧
      NormedSpace.exp h.toCLM ∈ unitary (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) := by
  have hskew : h.toCLM ∈ skewAdjoint (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) := by
    rw [skewAdjoint.mem_iff, ContinuousLinearMap.star_eq_adjoint, h.adjoint_toCLM]
    ext u i
    rw [SchurBound.toCLM_apply, show (-h.toCLM) u = -(h.toCLM u) from rfl, lp.coeFn_neg,
      Pi.neg_apply, SchurBound.toCLM_apply, kerApply, kerApply, ← tsum_neg]
    refine tsum_congr fun j => ?_
    simp only [adjKernel, hanti]
    ring
  refine ⟨hskew, ?_⟩
  letI : NormedAlgebra ℚ (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) :=
    .restrictScalars ℚ ℂ _
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hskew

end FluxSourceTest

/-! ## Part Bulk

Prototype: the bulk generator `Σ_b` of the block normal form (manuscript lines 7875–7893) for one
interaction pair `(a, b)` on the `η`-particle momentum lattice: its kernel, the gap that makes it
well defined (`lem:gap`), Schur's bound `‖Σ_b‖ ≤ C μ_ab c_w / (g² s)`, anti-Hermiticity, the
unitarity of `e^{Σ_b}`, and the exact intertwining `[T, Σ_b] = V_b` at the level of kernels.
-/

open scoped ComplexConjugate

namespace FluxSourceTest

/-! ## Lattice dot product and Cauchy–Schwarz -/

/-- Dot product of lattice vectors. -/
def ldot (x y : L3) : ℝ := (x 0 : ℝ) * y 0 + (x 1 : ℝ) * y 1 + (x 2 : ℝ) * y 2

lemma nsq_add (x y : L3) : nsq (x + y) = nsq x + 2 * ldot x y + nsq y := by
  unfold nsq ldot; push_cast [Pi.add_apply]; ring

lemma nsq_sub (x y : L3) : nsq (x - y) = nsq x - 2 * ldot x y + nsq y := by
  unfold nsq ldot; push_cast [Pi.sub_apply]; ring

lemma nsq_neg (x : L3) : nsq (-x) = nsq x := by
  unfold nsq; push_cast [Pi.neg_apply]; ring

lemma ldot_sq_le (x y : L3) : ldot x y ^ 2 ≤ nsq x * nsq y := by
  unfold ldot nsq
  nlinarith [sq_nonneg ((x 0 : ℝ) * y 1 - (x 1 : ℝ) * y 0),
    sq_nonneg ((x 0 : ℝ) * y 2 - (x 2 : ℝ) * y 0), sq_nonneg ((x 1 : ℝ) * y 2 - (x 2 : ℝ) * y 1)]

lemma abs_ldot_le (x y : L3) : |ldot x y| ≤ Real.sqrt (nsq x) * Real.sqrt (nsq y) := by
  rw [← Real.sqrt_mul (nsq_nonneg x), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (ldot_sq_le x y)

lemma coord_sq_le_nsq (x : L3) (i : Fin 3) : (x i : ℝ) ^ 2 ≤ nsq x := by
  unfold nsq
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0 : ℝ), sq_nonneg (x 1 : ℝ), sq_nonneg (x 2 : ℝ)]

/-! ## `lem:gap` on the lattice -/

/-- **`lem:gap` (eq:gap) on the lattice**, in lattice units: if both momenta of the pair have
Euclidean length at most `s/4` and the transfer takes one of them beyond Euclidean length `s`,
then `|ν| > 3s/4` and the mismatch is at least `|ν|²/(20 μ)`, `μ⁻¹ = m_p⁻¹ + m_b⁻¹`. -/
theorem lattice_gap {mp mb s : ℝ} (hmp : 0 < mp) (hmb : 0 < mb) (hs : 0 < s) {kp kb ν : L3}
    (hkp : nsq kp ≤ (s / 4) ^ 2) (hkb : nsq kb ≤ (s / 4) ^ 2)
    (hexit : s ^ 2 < nsq (kp + ν) ∨ s ^ 2 < nsq (kb - ν)) :
    (3 * s / 4) ^ 2 < nsq ν ∧
      nsq ν / 20 * (1 / mp + 1 / mb) ≤
        (nsq (kp + ν) - nsq kp) / (2 * mp) + (nsq (kb - ν) - nsq kb) / (2 * mb) := by
  set n := Real.sqrt (nsq ν) with hn
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hn2 : n ^ 2 = nsq ν := Real.sq_sqrt (nsq_nonneg ν)
  have hsp : Real.sqrt (nsq kp) ≤ s / 4 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, hkp⟩
  have hsb : Real.sqrt (nsq kb) ≤ s / 4 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, hkb⟩
  have hcp : |ldot kp ν| ≤ s / 4 * n :=
    (abs_ldot_le kp ν).trans (mul_le_mul_of_nonneg_right hsp hn0)
  have hcb : |ldot kb ν| ≤ s / 4 * n :=
    (abs_ldot_le kb ν).trans (mul_le_mul_of_nonneg_right hsb hn0)
  have hP : nsq kp ≤ s ^ 2 / 16 := by nlinarith
  have hPb : nsq kb ≤ s ^ 2 / 16 := by nlinarith
  have hx : 0 < 1 / mp := by positivity
  have hy : 0 < 1 / mb := by positivity
  have hmis : (nsq (kp + ν) - nsq kp) / (2 * mp) + (nsq (kb - ν) - nsq kb) / (2 * mb) =
      (2 * ldot kp ν + n ^ 2) * (1 / mp) / 2 + (n ^ 2 - 2 * ldot kb ν) * (1 / mb) / 2 := by
    rw [nsq_add, nsq_sub, hn2]
    field_simp
    ring
  rcases hexit with h | h
  · rw [nsq_add, ← hn2] at h
    obtain ⟨h1, -, h3⟩ := gap_core (K := s) (x := 1 / mp) (y := 1 / mb) hs hn0 hx hy hP
      (neg_le_of_abs_le hcp) (le_of_abs_le hcp) (le_of_abs_le hcb) h
    refine ⟨?_, ?_⟩
    · rw [← hn2]; nlinarith
    · rw [hmis, ← hn2]; exact h3
  · rw [nsq_sub, ← hn2] at h
    -- the mirrored configuration `(k_p, m_p) ↔ (-k_b, m_b)`
    have h' : s ^ 2 < nsq kb + 2 * (-ldot kb ν) + n ^ 2 := by linarith
    obtain ⟨h1, -, h3⟩ := gap_core (K := s) (x := 1 / mb) (y := 1 / mp) (ip := -ldot kb ν)
      (ib := -ldot kp ν) hs hn0 hy hx hPb (by linarith [le_of_abs_le hcb])
      (by linarith [neg_le_of_abs_le hcb]) (by linarith [neg_le_of_abs_le hcp]) h'
    refine ⟨?_, ?_⟩
    · rw [← hn2]; nlinarith
    · rw [hmis, ← hn2]; linarith

/-! ## Configurations, the pair transfer, the zones -/

/-- `η`-particle lattice configurations (`FourierConfig eta Lattice3` of the release file). -/
abbrev Cfg (eta : ℕ) := Fin eta → L3

variable {eta : ℕ} (a b : Fin eta)

/-- The pair transfer on `(a, b)`: `k_a ↦ k_a + ν`, `k_b ↦ k_b - ν`. -/
def shift (k : Cfg eta) (ν : L3) : Cfg eta :=
  fun c => if c = a then k c + ν else if c = b then k c - ν else k c

variable {a b}

lemma shift_apply_a (k : Cfg eta) (ν : L3) : shift a b k ν a = k a + ν := by
  simp [shift]

lemma shift_apply_b (hab : a ≠ b) (k : Cfg eta) (ν : L3) : shift a b k ν b = k b - ν := by
  simp [shift, hab.symm]

lemma shift_apply_of_ne {c : Fin eta} (hca : c ≠ a) (hcb : c ≠ b) (k : Cfg eta) (ν : L3) :
    shift a b k ν c = k c := by
  simp [shift, hca, hcb]

lemma shift_shift (hab : a ≠ b) (k : Cfg eta) (ν ν' : L3) :
    shift a b (shift a b k ν) ν' = shift a b k (ν + ν') := by
  funext c
  by_cases hca : c = a
  · subst hca; simp only [shift_apply_a]; abel
  · by_cases hcb : c = b
    · subst hcb; simp only [shift_apply_b hab]; abel
    · simp only [shift_apply_of_ne hca hcb]

lemma shift_zero (k : Cfg eta) : shift a b k 0 = k := by
  funext c; simp [shift]

lemma shift_neg_cancel (hab : a ≠ b) (k : Cfg eta) (ν : L3) :
    shift a b (shift a b k ν) (-ν) = k := by
  rw [shift_shift hab, add_neg_cancel, shift_zero]

lemma shift_injective (k : Cfg eta) : Function.Injective (shift a b k) := by
  intro ν ν' h
  have := congrFun h a
  simp only [shift_apply_a] at this
  exact add_left_cancel this

lemma shift_sub_a (k : Cfg eta) (ν : L3) : shift a b k ν a - k a = ν := by
  rw [shift_apply_a]; abel

/-- `p` is a pair transfer of `q` iff `q` is the reverse transfer of `p`. -/
lemma isShift_symm (hab : a ≠ b) {p q : Cfg eta} :
    p = shift a b q (p a - q a) ↔ q = shift a b p (q a - p a) := by
  have key : ∀ {p q : Cfg eta}, p = shift a b q (p a - q a) → q = shift a b p (q a - p a) := by
    intro p q h
    set ν := p a - q a with hν
    have e : q a - p a = -ν := by rw [hν]; abel
    rw [e]
    calc q = shift a b (shift a b q ν) (-ν) := (shift_neg_cancel hab q ν).symm
      _ = shift a b p (-ν) := by rw [← h]
  exact ⟨key, key⟩

variable (s : ℝ)

/-- The Galerkin cube `P` (all coordinates at most `s` in absolute value; `s` is the cube size in
lattice units, `K = g s`). -/
def InP (k : Cfg eta) : Prop := ∀ c i, |((k c i : ℤ) : ℝ)| ≤ s

/-- The bulk block `Q` (every register of Euclidean length at most `s/4`). -/
def InQ (k : Cfg eta) : Prop := ∀ c, nsq (k c) ≤ (s / 4) ^ 2

/-- A bulk-fed crossing: one end in `Q`, the other outside `P`. -/
def Cross (q p : Cfg eta) : Prop := (InQ s q ∧ ¬ InP s p) ∨ (¬ InP s q ∧ InQ s p)

variable {s}

lemma Cross.symm {q p : Cfg eta} (h : Cross s q p) : Cross s p q := by
  rcases h with h | h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

lemma InQ.inP (hs : 0 ≤ s) {k : Cfg eta} (h : InQ s k) : InP s k := by
  intro c i
  have h1 := coord_sq_le_nsq (k c) i
  have h2 := h c
  have : |((k c i : ℤ) : ℝ)| ≤ s / 4 := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_iff.mpr ⟨by linarith, h1.trans h2⟩
  linarith

/-- Leaving the cube from the bulk block means leaving the Euclidean ball of radius `s` in one
of the two moved registers. -/
lemma exit_of_shift (hab : a ≠ b) (hs : 0 ≤ s) {q : Cfg eta} {ν : L3} (hq : InQ s q)
    (hp : ¬ InP s (shift a b q ν)) : s ^ 2 < nsq (q a + ν) ∨ s ^ 2 < nsq (q b - ν) := by
  unfold InP at hp
  push Not at hp
  obtain ⟨c, i, hci⟩ := hp
  have hsq : ∀ x : L3, s < |((x i : ℤ) : ℝ)| → s ^ 2 < nsq x := by
    intro x hx
    have := coord_sq_le_nsq x i
    have h2 : s ^ 2 < ((x i : ℤ) : ℝ) ^ 2 := by
      rw [← sq_abs (((x i : ℤ) : ℝ))]
      exact pow_lt_pow_left₀ hx hs two_ne_zero
    linarith
  by_cases hca : c = a
  · subst hca; rw [shift_apply_a] at hci; exact Or.inl (hsq _ hci)
  · by_cases hcb : c = b
    · subst hcb; rw [shift_apply_b hab] at hci; exact Or.inr (hsq _ hci)
    · rw [shift_apply_of_ne hca hcb] at hci
      exact absurd (hq.inP hs c i) (not_le.mpr hci)

/-! ## Kinetic energy and the mismatch of a pair transfer -/

variable (m : Fin eta → ℝ) (g : ℝ)

/-- The kinetic energy `E(k) = Σ_c g² |k_c|² / (2 m_c)` (physical momentum `g k_c`). -/
noncomputable def E (k : Cfg eta) : ℝ := ∑ c, g ^ 2 / (2 * m c) * nsq (k c)

variable {m g}

lemma E_shift_sub (hab : a ≠ b) (k : Cfg eta) (ν : L3) :
    E m g (shift a b k ν) - E m g k =
      g ^ 2 * ((nsq (k a + ν) - nsq (k a)) / (2 * m a) + (nsq (k b - ν) - nsq (k b)) / (2 * m b)) := by
  unfold E
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_add_of_mem a b (Finset.mem_univ a) (Finset.mem_univ b) hab]
  · rw [shift_apply_a, shift_apply_b hab]
    ring
  · intro c _ hc
    rw [shift_apply_of_ne hc.1 hc.2, sub_self]

/-- **The gap of a bulk-fed crossing**: `|E(q ⊕ ν) - E(q)| ≥ g² |ν|² (m_a⁻¹ + m_b⁻¹)/20` and
`|ν| > 3s/4`, in either orientation. -/
theorem energy_gap (hab : a ≠ b) (hm : ∀ c, 0 < m c) (hs : 0 < s) {q : Cfg eta} {ν : L3}
    (hc : Cross s q (shift a b q ν)) :
    (3 * s / 4) ^ 2 < nsq ν ∧
      g ^ 2 * (nsq ν / 20 * (1 / m a + 1 / m b)) ≤ |E m g (shift a b q ν) - E m g q| := by
  -- the orientation `Q → outside P`
  have hQ : ∀ {q : Cfg eta} {ν : L3}, InQ s q → ¬ InP s (shift a b q ν) →
      (3 * s / 4) ^ 2 < nsq ν ∧
        g ^ 2 * (nsq ν / 20 * (1 / m a + 1 / m b)) ≤ E m g (shift a b q ν) - E m g q := by
    intro q ν hq hp
    obtain ⟨h1, h2⟩ := lattice_gap (hm a) (hm b) hs (hq a) (hq b) (exit_of_shift hab hs.le hq hp)
    refine ⟨h1, ?_⟩
    rw [E_shift_sub hab]
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg g)
  rcases hc with ⟨hq, hp⟩ | ⟨hq, hp⟩
  · obtain ⟨h1, h2⟩ := hQ hq hp
    exact ⟨h1, h2.trans (le_abs_self _)⟩
  · -- the reverse orientation: apply the first one at `p = q ⊕ ν` with `-ν`
    have hq' : ¬ InP s (shift a b (shift a b q ν) (-ν)) := by rwa [shift_neg_cancel hab]
    obtain ⟨h1, h2⟩ := hQ hp hq'
    rw [shift_neg_cancel hab, nsq_neg] at *
    refine ⟨h1, ?_⟩
    rw [abs_sub_comm]
    exact h2.trans (le_abs_self _)

/-! ## The kernels of `Σ_b` and `V_b` -/

variable (a b s m g) (w : L3 → ℝ)

open Classical in
/-- The kernel of the bulk generator `Σ_b` for the pair `(a, b)`: on a bulk-fed crossing
`q → p = q ⊕ ν`, the Coulomb coefficient `w ν` divided by the kinetic mismatch `E p - E q`. -/
noncomputable def sigmaK (p q : Cfg eta) : ℂ :=
  if p = shift a b q (p a - q a) ∧ Cross s q p then ((w (p a - q a) / (E m g p - E m g q) : ℝ) : ℂ)
  else 0

open Classical in
/-- The kernel of the bulk-fed crossings `V_b` for the pair `(a, b)`. -/
noncomputable def vbK (p q : Cfg eta) : ℂ :=
  if p = shift a b q (p a - q a) ∧ Cross s q p then ((w (p a - q a) : ℝ) : ℂ) else 0

variable {a b s m g w}

open Classical in
lemma sigmaK_shift (k : Cfg eta) (ν : L3) :
    sigmaK a b s m g w (shift a b k ν) k =
      if Cross s k (shift a b k ν) then
        ((w ν / (E m g (shift a b k ν) - E m g k) : ℝ) : ℂ) else 0 := by
  unfold sigmaK
  rw [shift_sub_a]
  simp only [true_and]

/-- **`[T, Σ_b] = V_b`** on kernels: `(E p - E q) σ(p, q) = v_b(p, q)` (the mismatch that the
dressing divides out; `eq:Sigma`). -/
theorem commutator_kernel (hab : a ≠ b) (hm : ∀ c, 0 < m c) (hg : g ≠ 0) (hs : 0 < s)
    (p q : Cfg eta) :
    ((E m g p - E m g q : ℝ) : ℂ) * sigmaK a b s m g w p q = vbK a b s w p q := by
  unfold sigmaK vbK
  split_ifs with h
  · obtain ⟨hp, hc⟩ := h
    have hne : E m g p - E m g q ≠ 0 := by
      have hc' : Cross s q (shift a b q (p a - q a)) := by rwa [← hp]
      obtain ⟨h1, h2⟩ := energy_gap hab hm hs hc'
      rw [← hp] at h2
      have hpos : 0 < g ^ 2 * (nsq (p a - q a) / 20 * (1 / m a + 1 / m b)) := by
        have := hm a; have := hm b
        have : 0 < nsq (p a - q a) := lt_of_le_of_lt (sq_nonneg _) h1
        positivity
      exact abs_pos.mp (hpos.trans_le h2)
    rw [← Complex.ofReal_mul, mul_div_cancel₀ _ hne]
  · rw [mul_zero]

/-- **Anti-Hermiticity**: `conj σ(q, p) = -σ(p, q)` (`Σ_b† = -Σ_b`), for an even coefficient. -/
theorem sigmaK_anti (hab : a ≠ b) (hw : ∀ ν, w (-ν) = w ν) (p q : Cfg eta) :
    conj (sigmaK a b s m g w q p) = -sigmaK a b s m g w p q := by
  unfold sigmaK
  by_cases hpq : p = shift a b q (p a - q a)
  · have hqp : q = shift a b p (q a - p a) := (isShift_symm hab).mp hpq
    have hν : q a - p a = -(p a - q a) := by abel
    by_cases hc : Cross s q p
    · rw [if_pos ⟨hqp, hc.symm⟩, if_pos ⟨hpq, hc⟩, Complex.conj_ofReal, hν, hw,
        show E m g q - E m g p = -(E m g p - E m g q) by ring, div_neg, Complex.ofReal_neg]
    · have hc' : ¬ Cross s p q := fun h => hc h.symm
      rw [if_neg (fun h => hc' h.2), if_neg (fun h => hc h.2)]
      simp
  · have hqp : ¬ q = shift a b p (q a - p a) := fun h => hpq ((isShift_symm hab).mpr h)
    rw [if_neg (fun h => hqp h.1), if_neg (fun h => hpq h.1)]
    simp

/-- The pointwise bound of a single element: `|σ(q ⊕ ν, q)| ≤ 20 c_w μ_ab / g² · |ν|⁻⁴`, and it
vanishes unless `|ν| > 3s/4`. -/
theorem norm_sigmaK_shift_le (hab : a ≠ b) (hm : ∀ c, 0 < m c) (hg : g ≠ 0) (hs : 0 < s)
    {cw : ℝ} (hcw : 0 ≤ cw) (hwb : ∀ ν, |w ν| ≤ cw / nsq ν) (k : Cfg eta) (ν : L3) :
    ‖sigmaK a b s m g w (shift a b k ν) k‖ ≤
      20 * cw / (g ^ 2 * (1 / m a + 1 / m b)) * tailFn (3 * s / 4) ν := by
  rw [sigmaK_shift]
  have hma := hm a
  have hmb := hm b
  have hμ : 0 < 1 / m a + 1 / m b := by positivity
  have hg2 : 0 < g ^ 2 := by positivity
  split_ifs with hc
  · obtain ⟨h1, h2⟩ := energy_gap hab hm hs hc
    have hnsq : 0 < nsq ν := lt_of_le_of_lt (sq_nonneg _) h1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div]
    unfold tailFn
    rw [if_pos h1]
    have hden : 0 < g ^ 2 * (nsq ν / 20 * (1 / m a + 1 / m b)) := by positivity
    calc |w ν| / |E m g (shift a b k ν) - E m g k|
        ≤ (cw / nsq ν) / (g ^ 2 * (nsq ν / 20 * (1 / m a + 1 / m b))) :=
          div_le_div₀ (by positivity) (hwb ν) hden h2
      _ = 20 * cw / (g ^ 2 * (1 / m a + 1 / m b)) * (nsq ν)⁻¹ ^ 2 := by
          field_simp
  · rw [norm_zero]
    exact mul_nonneg (by positivity) (tailFn_nonneg _ _)

/-! ## Schur's test: `Σ_b` is bounded, `‖Σ_b‖ ≤ 20 c_w μ_ab/g² · 416/(3s)` -/

/-- The common row/column bound. -/
noncomputable def schurConst (m : Fin eta → ℝ) (g s cw : ℝ) (a b : Fin eta) : ℝ :=
  20 * cw / (g ^ 2 * (1 / m a + 1 / m b)) * (416 / (3 * s))

theorem sigmaK_schur (hab : a ≠ b) (hm : ∀ c, 0 < m c) (hg : g ≠ 0) (hs : 4 / 3 ≤ s)
    {cw : ℝ} (hcw : 0 ≤ cw) (hwb : ∀ ν, |w ν| ≤ cw / nsq ν) (hw : ∀ ν, w (-ν) = w ν) :
    SchurBound (sigmaK a b s m g w) (schurConst m g s cw a b) (schurConst m g s cw a b) := by
  have hs0 : 0 < s := by linarith
  have hR : (1 : ℝ) ≤ 3 * s / 4 := by linarith
  obtain ⟨hsum, htail⟩ := tailFn_summable_and_le hR
  have hma := hm a
  have hmb := hm b
  set C0 := 20 * cw / (g ^ 2 * (1 / m a + 1 / m b)) with hC0
  have hC0nn : 0 ≤ C0 := by positivity
  have hdom : Summable fun ν => C0 * tailFn (3 * s / 4) ν := hsum.mul_left C0
  have hbound : C0 * ∑' ν, tailFn (3 * s / 4) ν ≤ schurConst m g s cw a b := by
    unfold schurConst
    rw [← hC0]
    refine mul_le_mul_of_nonneg_left (htail.trans_eq ?_) hC0nn
    field_simp
    ring
  -- columns: reindex the outputs `p = q ⊕ ν` by `ν`
  have hcol_supp : ∀ q : Cfg eta, Function.support (fun p => ‖sigmaK a b s m g w p q‖) ⊆
      Set.range (shift a b q) := by
    intro q p hp
    simp only [Function.mem_support, ne_eq, norm_eq_zero] at hp
    unfold sigmaK at hp
    split_ifs at hp with h
    · exact ⟨p a - q a, h.1.symm⟩
    · exact absurd rfl hp
  have hcol_eq : ∀ q : Cfg eta, (fun ν => ‖sigmaK a b s m g w (shift a b q ν) q‖) =
      (fun p => ‖sigmaK a b s m g w p q‖) ∘ shift a b q := fun q => rfl
  have hcol_le : ∀ q ν, ‖sigmaK a b s m g w (shift a b q ν) q‖ ≤ C0 * tailFn (3 * s / 4) ν :=
    fun q ν => norm_sigmaK_shift_le hab hm hg hs0 hcw hwb q ν
  have hcol_summ : ∀ q : Cfg eta, Summable fun ν => ‖sigmaK a b s m g w (shift a b q ν) q‖ :=
    fun q => hdom.of_nonneg_of_le (fun _ => norm_nonneg _) (hcol_le q)
  -- rows: reindex the inputs `q = p ⊕ ν'`, and use anti-Hermiticity
  have hrow_supp : ∀ p : Cfg eta, Function.support (fun q => ‖sigmaK a b s m g w p q‖) ⊆
      Set.range (shift a b p) := by
    intro p q hq
    simp only [Function.mem_support, ne_eq, norm_eq_zero] at hq
    unfold sigmaK at hq
    split_ifs at hq with h
    · exact ⟨q a - p a, ((isShift_symm hab).mp h.1).symm⟩
    · exact absurd rfl hq
  have hrow_norm : ∀ p ν, ‖sigmaK a b s m g w p (shift a b p ν)‖ =
      ‖sigmaK a b s m g w (shift a b p ν) p‖ := by
    intro p ν
    rw [← norm_neg, ← sigmaK_anti hab hw, Complex.norm_conj]
  have hrow_le : ∀ p ν, ‖sigmaK a b s m g w p (shift a b p ν)‖ ≤ C0 * tailFn (3 * s / 4) ν :=
    fun p ν => (hrow_norm p ν).trans_le (hcol_le p ν)
  have hrow_summ : ∀ p : Cfg eta, Summable fun ν => ‖sigmaK a b s m g w p (shift a b p ν)‖ :=
    fun p => hdom.of_nonneg_of_le (fun _ => norm_nonneg _) (hrow_le p)
  refine
    { row_summable := fun p => ?_
      row_le := fun p => ?_
      col_summable := fun q => ?_
      col_le := fun q => ?_ }
  · exact ((shift_injective p).summable_iff fun q hq => by
      by_contra hne; exact hq (hrow_supp p hne)).mp (hrow_summ p)
  · rw [← (shift_injective p).tsum_eq (hrow_supp p)]
    exact ((hrow_summ p).tsum_le_tsum (hrow_le p) hdom).trans
      ((tsum_mul_left).le.trans hbound)
  · exact ((shift_injective q).summable_iff fun p hp => by
      by_contra hne; exact hp (hcol_supp q hne)).mp (hcol_summ q)
  · rw [← (shift_injective q).tsum_eq (hcol_supp q)]
    exact ((hcol_summ q).tsum_le_tsum (hcol_le q) hdom).trans
      ((tsum_mul_left).le.trans hbound)

/-! ## The prototype statement -/

/-- **The bulk generator of the block normal form, one pair.**  For an even Coulomb-type
coefficient `|w ν| ≤ c_w / |ν|²`, the operator `Σ_b` with kernel `w ν / (E(q ⊕ ν) - E(q))` on the
bulk-fed crossings (bulk block `Q` ↔ outside the cube `P`) is a bounded operator on
`ℓ²(ℤ^{3η})` with `‖Σ_b‖ ≤ 20 c_w μ_ab/g² · 416/(3s)` (the manuscript's `C μ_pb / K` with
`K = g s` and `c_w ∝ 1/g²`), it is skew-adjoint, `e^{Σ_b}` is unitary, and its kernel satisfies
the intertwining identity `[T, Σ_b] = V_b` exactly. -/
theorem bulkGenerator (hab : a ≠ b) (hm : ∀ c, 0 < m c) (hg : g ≠ 0) (hs : 4 / 3 ≤ s)
    {cw : ℝ} (hcw : 0 ≤ cw) (hwb : ∀ ν, |w ν| ≤ cw / nsq ν) (hw : ∀ ν, w (-ν) = w ν) :
    ∃ Sig : lp (fun _ : Cfg eta => ℂ) 2 →L[ℂ] lp (fun _ : Cfg eta => ℂ) 2,
      (∀ u p, Sig u p = ∑' q, sigmaK a b s m g w p q * u q) ∧
      ‖Sig‖ ≤ schurConst m g s cw a b ∧
      Sig ∈ skewAdjoint (lp (fun _ : Cfg eta => ℂ) 2 →L[ℂ] lp (fun _ : Cfg eta => ℂ) 2) ∧
      NormedSpace.exp Sig ∈ unitary (lp (fun _ : Cfg eta => ℂ) 2 →L[ℂ] lp (fun _ : Cfg eta => ℂ) 2) ∧
      (∀ p q, ((E m g p - E m g q : ℝ) : ℂ) * sigmaK a b s m g w p q = vbK a b s w p q) := by
  have hS := sigmaK_schur hab hm hg hs hcw hwb hw
  have hconst : 0 ≤ schurConst m g s cw a b := by
    unfold schurConst
    have := hm a; have := hm b
    have : 0 < s := by linarith
    positivity
  obtain ⟨hskew, hunit⟩ := hS.exp_mem_unitary (sigmaK_anti hab hw)
  refine ⟨hS.toCLM, fun u p => rfl, ?_, hskew, hunit,
    commutator_kernel hab hm hg (by linarith)⟩
  refine hS.norm_toCLM_le.trans (le_of_eq ?_)
  rw [Real.sqrt_mul_self hconst]

end FluxSourceTest

/-! ## Part Domain

Prototype, continued: the domain question of the block normal form.  `V_b` is bounded
(Hilbert–Schmidt, since every bulk-fed crossing has one end in the finite block `Q`), the exact
identity `(1 + E) Σ_b c = Σ_b ((1 + E) c) + V_b c` holds on `D(T)`, and hence `e^{Σ_b}` maps
`D(T) = {c : (1 + E) c ∈ ℓ²}` into itself: `e^{Σ_b} S = S e^{Σ'}` with `S = (1 + E)⁻¹` and the
bounded operator `Σ' = Σ_b + V_b S` (the generator read in graph-norm coordinates).
-/

open scoped ComplexConjugate

namespace FluxSourceTest

/-! ## Hilbert–Schmidt kernels -/

section HS

variable {ι : Type*}

/-- A Hilbert–Schmidt bound for a kernel. -/
structure HSBound (κ : ι → ι → ℂ) (C : ℝ) : Prop where
  summable : Summable fun x : ι × ι => ‖κ x.1 x.2‖ ^ 2
  le : ∑' x : ι × ι, ‖κ x.1 x.2‖ ^ 2 ≤ C

namespace HSBound

variable {κ : ι → ι → ℂ} {C : ℝ} (h : HSBound κ C)
include h

lemma row_summable_sq (i : ι) : Summable fun j => ‖κ i j‖ ^ 2 := h.summable.prod_factor i

lemma summable_row_mul_norm (u : lp (fun _ : ι => ℂ) 2) (i : ι) :
    Summable fun j => ‖κ i j‖ * ‖u j‖ := by
  have := Real.summable_mul_of_Lp_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := fun j => ‖κ i j‖) (g := fun j => ‖u j‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (by simpa [Real.rpow_two] using h.row_summable_sq i)
    (by simpa [Real.rpow_two] using summable_sq_coord u)
  exact this

lemma norm_kerApply_sq_le (u : lp (fun _ : ι => ℂ) 2) (i : ι) :
    ‖kerApply κ u i‖ ^ 2 ≤ (∑' j, ‖κ i j‖ ^ 2) * ‖u‖ ^ 2 := by
  have h1 : ‖kerApply κ u i‖ ≤ ∑' j, ‖κ i j‖ * ‖u j‖ := by
    unfold kerApply
    refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
    · exact (h.summable_row_mul_norm u i).congr fun j => (norm_mul _ _).symm
    · exact tsum_congr fun j => norm_mul _ _
  have hH := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := fun j => ‖κ i j‖) (g := fun j => ‖u j‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (by simpa [Real.rpow_two] using h.row_summable_sq i)
    (by simpa [Real.rpow_two] using summable_sq_coord u)
  simp only [Real.rpow_two] at hH
  rw [tsum_sq_coord u] at hH
  have hA : 0 ≤ ∑' j, ‖κ i j‖ ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hn : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  calc ‖kerApply κ u i‖ ^ 2 ≤ ((∑' j, ‖κ i j‖ ^ 2) ^ (1 / 2 : ℝ) * (‖u‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h1.trans hH) 2
    _ = (∑' j, ‖κ i j‖ ^ 2) * ‖u‖ ^ 2 := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hA,
          ← Real.rpow_mul hn]
        norm_num

lemma summable_kerApply_sq (u : lp (fun _ : ι => ℂ) 2) :
    (Summable fun i => ‖kerApply κ u i‖ ^ 2) ∧ ∑' i, ‖kerApply κ u i‖ ^ 2 ≤ C * ‖u‖ ^ 2 := by
  have hrows : Summable fun i => ∑' j, ‖κ i j‖ ^ 2 := h.summable.prod
  have hs : Summable fun i => ‖kerApply κ u i‖ ^ 2 :=
    (hrows.mul_right (‖u‖ ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _) (h.norm_kerApply_sq_le u)
  refine ⟨hs, ?_⟩
  calc ∑' i, ‖kerApply κ u i‖ ^ 2 ≤ ∑' i, (∑' j, ‖κ i j‖ ^ 2) * ‖u‖ ^ 2 :=
        hs.tsum_le_tsum (h.norm_kerApply_sq_le u) (hrows.mul_right _)
    _ = (∑' x : ι × ι, ‖κ x.1 x.2‖ ^ 2) * ‖u‖ ^ 2 := by
        rw [tsum_mul_right, h.summable.tsum_prod' (fun i => h.row_summable_sq i)]
    _ ≤ C * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_right h.le (sq_nonneg _)

lemma memℓp_kerApply (u : lp (fun _ : ι => ℂ) 2) : Memℓp (kerApply κ u) 2 := by
  refine memℓp_gen ?_
  simpa using (h.summable_kerApply_sq u).1

lemma C_nonneg : 0 ≤ C := (tsum_nonneg fun _ => sq_nonneg _).trans h.le

lemma norm_kerApply_le (u : lp (fun _ : ι => ℂ) 2) :
    ‖(⟨kerApply κ u, h.memℓp_kerApply u⟩ : lp (fun _ : ι => ℂ) 2)‖ ≤ Real.sqrt C * ‖u‖ := by
  set f : lp (fun _ : ι => ℂ) 2 := ⟨kerApply κ u, h.memℓp_kerApply u⟩
  have hsq : ‖f‖ ^ 2 ≤ C * ‖u‖ ^ 2 := by
    rw [← tsum_sq_coord f]
    exact (h.summable_kerApply_sq u).2
  calc ‖f‖ = Real.sqrt (‖f‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (C * ‖u‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt C * ‖u‖ := by rw [Real.sqrt_mul h.C_nonneg, Real.sqrt_sq (norm_nonneg _)]

lemma kerApply_add (u v : lp (fun _ : ι => ℂ) 2) :
    kerApply κ ⇑(u + v) = kerApply κ ⇑u + kerApply κ ⇑v := by
  funext i
  simp only [kerApply, Pi.add_apply, lp.coeFn_add, mul_add]
  have hu : Summable fun j => κ i j * u j :=
    Summable.of_norm ((h.summable_row_mul_norm u i).congr fun _ => (norm_mul _ _).symm)
  have hv : Summable fun j => κ i j * v j :=
    Summable.of_norm ((h.summable_row_mul_norm v i).congr fun _ => (norm_mul _ _).symm)
  exact hu.tsum_add hv

/-- The Hilbert–Schmidt kernel operator. -/
noncomputable def toCLM : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨kerApply κ u, h.memℓp_kerApply u⟩
      map_add' := fun u v => lp.ext (h.kerApply_add u v)
      map_smul' := fun c u => lp.ext (SchurBound.kerApply_smul c u) }
    (Real.sqrt C) h.norm_kerApply_le

lemma toCLM_apply (u : lp (fun _ : ι => ℂ) 2) (i : ι) : h.toCLM u i = kerApply κ u i := rfl

end HSBound

end HS

/-! ## The bulk block is finite -/

variable {eta : ℕ} {a b : Fin eta} {s : ℝ} {m : Fin eta → ℝ} {g : ℝ} {w : L3 → ℝ}

/-- A finite set of configurations containing the bulk block `Q`. -/
noncomputable def Qbox (eta : ℕ) (s : ℝ) : Finset (Cfg eta) :=
  Fintype.piFinset fun _ => box ⌈s / 4⌉₊

lemma mem_Qbox_of_inQ (hs : 0 ≤ s) {k : Cfg eta} (hk : InQ s k) : k ∈ Qbox eta s := by
  rw [Qbox, Fintype.mem_piFinset]
  intro c
  rw [mem_box]
  intro i
  have h1 := coord_sq_le_nsq (k c) i
  have h2 := hk c
  have habs : |((k c i : ℤ) : ℝ)| ≤ s / 4 := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_iff.mpr ⟨by linarith, h1.trans h2⟩
  have hceil : s / 4 ≤ (⌈s / 4⌉₊ : ℝ) := Nat.le_ceil _
  have hle : |((k c i : ℤ) : ℝ)| ≤ (⌈s / 4⌉₊ : ℝ) := habs.trans hceil
  rw [abs_le] at hle
  constructor
  · have : (-(⌈s / 4⌉₊ : ℤ) : ℝ) ≤ ((k c i : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : ((k c i : ℤ) : ℝ) ≤ ((⌈s / 4⌉₊ : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-! ## `V_b` is Hilbert–Schmidt -/

open Classical in
lemma vbK_shift (k : Cfg eta) (ν : L3) :
    ‖vbK a b s w (shift a b k ν) k‖ ≤ if Cross s k (shift a b k ν) then |w ν| else 0 := by
  unfold vbK
  rw [shift_sub_a]
  simp only [true_and]
  split_ifs <;> simp

/-- Columns of `V_b` have finite `ℓ²` norm: `Σ_p |v_b(p, q)|² ≤ c_w² Σ_{|ν|>3s/4} |ν|⁻⁴`. -/
lemma vbK_col (hab : a ≠ b) (hm : ∀ c, 0 < m c) (hs : 4 / 3 ≤ s) {cw : ℝ}
    (hwb : ∀ ν, |w ν| ≤ cw / nsq ν) (q : Cfg eta) :
    (Summable fun p => ‖vbK a b s w p q‖ ^ 2) ∧
      ∑' p, ‖vbK a b s w p q‖ ^ 2 ≤ cw ^ 2 * ∑' ν, tailFn (3 * s / 4) ν := by
  classical
  have hs0 : 0 < s := by linarith
  obtain ⟨hsum, -⟩ := tailFn_summable_and_le (R := 3 * s / 4) (by linarith)
  have hsupp : Function.support (fun p => ‖vbK a b s w p q‖ ^ 2) ⊆ Set.range (shift a b q) := by
    intro p hp
    simp only [Function.mem_support, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true,
      norm_eq_zero] at hp
    unfold vbK at hp
    split_ifs at hp with h
    · exact ⟨p a - q a, h.1.symm⟩
    · exact absurd rfl hp
  have hle : ∀ ν, ‖vbK a b s w (shift a b q ν) q‖ ^ 2 ≤ cw ^ 2 * tailFn (3 * s / 4) ν := by
    intro ν
    have h0 := vbK_shift (a := a) (b := b) (s := s) (w := w) q ν
    split_ifs at h0 with hc
    · obtain ⟨h1, -⟩ := energy_gap (m := m) (g := 1) hab hm hs0 hc
      have hnsq : 0 < nsq ν := lt_of_le_of_lt (sq_nonneg _) h1
      unfold tailFn
      rw [if_pos h1]
      have hw := hwb ν
      calc ‖vbK a b s w (shift a b q ν) q‖ ^ 2 ≤ |w ν| ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h0 2
        _ ≤ (cw / nsq ν) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hw 2
        _ = cw ^ 2 * (nsq ν)⁻¹ ^ 2 := by rw [div_pow, inv_pow]; ring
    · have : ‖vbK a b s w (shift a b q ν) q‖ = 0 := le_antisymm h0 (norm_nonneg _)
      rw [this]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_nonneg (sq_nonneg _) (tailFn_nonneg _ _)
  have hdom : Summable fun ν => cw ^ 2 * tailFn (3 * s / 4) ν := hsum.mul_left _
  have hs' : Summable fun ν => ‖vbK a b s w (shift a b q ν) q‖ ^ 2 :=
    hdom.of_nonneg_of_le (fun _ => sq_nonneg _) hle
  refine ⟨((shift_injective q).summable_iff fun p hp => by
      by_contra hne; exact hp (hsupp hne)).mp hs', ?_⟩
  rw [← (shift_injective q).tsum_eq hsupp, ← tsum_mul_left]
  exact hs'.tsum_le_tsum hle hdom

/-- `V_b` is symmetric (for an even coefficient). -/
lemma vbK_symm (hab : a ≠ b) (hw : ∀ ν, w (-ν) = w ν) (p q : Cfg eta) :
    vbK a b s w q p = vbK a b s w p q := by
  unfold vbK
  by_cases hpq : p = shift a b q (p a - q a)
  · have hqp : q = shift a b p (q a - p a) := (isShift_symm hab).mp hpq
    have hν : q a - p a = -(p a - q a) := by abel
    by_cases hc : Cross s q p
    · rw [if_pos ⟨hqp, hc.symm⟩, if_pos ⟨hpq, hc⟩, hν, hw]
    · have hc' : ¬ Cross s p q := fun h => hc h.symm
      rw [if_neg (fun h => hc' h.2), if_neg (fun h => hc h.2)]
  · have hqp : ¬ q = shift a b p (q a - p a) := fun h => hpq ((isShift_symm hab).mpr h)
    rw [if_neg (fun h => hqp h.1), if_neg (fun h => hpq h.1)]

/-- A nonzero element of `V_b` has one end in the bulk block. -/
lemma vbK_ne_zero_mem (hs : 0 ≤ s) {p q : Cfg eta} (h : vbK a b s w p q ≠ 0) :
    q ∈ Qbox eta s ∨ p ∈ Qbox eta s := by
  unfold vbK at h
  split_ifs at h with hc
  · rcases hc.2 with ⟨hq, -⟩ | ⟨-, hp⟩
    · exact Or.inl (mem_Qbox_of_inQ hs hq)
    · exact Or.inr (mem_Qbox_of_inQ hs hp)
  · exact absurd rfl h

/-- **`V_b` is Hilbert–Schmidt**, with `‖V_b‖²_HS ≤ 2 #Q c_w² Σ_{|ν|>3s/4} |ν|⁻⁴`. -/
theorem vbK_hs (hab : a ≠ b) (hm : ∀ c, 0 < m c) (hs : 4 / 3 ≤ s) {cw : ℝ}
    (hwb : ∀ ν, |w ν| ≤ cw / nsq ν) (hw : ∀ ν, w (-ν) = w ν) :
    HSBound (vbK a b s w) (2 * ((Qbox eta s).card * (cw ^ 2 * ∑' ν, tailFn (3 * s / 4) ν))) := by
  classical
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hcol := fun q => vbK_col (a := a) (b := b) (w := w) hab hm hs hwb q
  set T := cw ^ 2 * ∑' ν, tailFn (3 * s / 4) ν
  -- `F x = [x.2 ∈ Q] |v_b x|²` is summable with sum `≤ #Q · T`
  set F : Cfg eta × Cfg eta → ℝ := fun x =>
    if x.2 ∈ Qbox eta s then ‖vbK a b s w x.1 x.2‖ ^ 2 else 0 with hF
  have hF0 : ∀ x, 0 ≤ F x := fun x => by simp only [hF]; split_ifs <;> positivity
  have hFrow : ∀ p, Summable fun q => F (p, q) := fun p =>
    summable_of_ne_finset_zero (s := Qbox eta s) fun q hq => by simp [hF, hq]
  have hFrow_eq : ∀ p, ∑' q, F (p, q) = ∑ q ∈ Qbox eta s, ‖vbK a b s w p q‖ ^ 2 := by
    intro p
    rw [tsum_eq_sum (s := Qbox eta s) (fun q hq => by simp [hF, hq])]
    exact Finset.sum_congr rfl fun q hq => by simp [hF, hq]
  have hFouter : Summable fun p => ∑' q, F (p, q) := by
    simp only [hFrow_eq]
    exact summable_sum fun q _ => (hcol q).1
  have hFs : Summable F := (summable_prod_of_nonneg hF0).2 ⟨hFrow, hFouter⟩
  have hFle : ∑' x, F x ≤ (Qbox eta s).card * T := by
    rw [hFs.tsum_prod' hFrow]
    simp only [hFrow_eq]
    rw [Summable.tsum_finsetSum fun q _ => (hcol q).1]
    calc ∑ q ∈ Qbox eta s, ∑' p, ‖vbK a b s w p q‖ ^ 2 ≤ ∑ _q ∈ Qbox eta s, T :=
          Finset.sum_le_sum fun q _ => (hcol q).2
      _ = (Qbox eta s).card * T := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the swapped function covers the other orientation
  have hFs' : Summable fun x : Cfg eta × Cfg eta => F (x.2, x.1) :=
    (Equiv.prodComm _ _).summable_iff.mpr hFs |>.congr fun x => rfl
  have hFle' : ∑' x : Cfg eta × Cfg eta, F (x.2, x.1) ≤ (Qbox eta s).card * T := by
    have : ∑' x : Cfg eta × Cfg eta, F (x.2, x.1) = ∑' x, F x :=
      (Equiv.prodComm (Cfg eta) (Cfg eta)).tsum_eq F
    rw [this]; exact hFle
  have hdom : ∀ x : Cfg eta × Cfg eta, ‖vbK a b s w x.1 x.2‖ ^ 2 ≤ F x + F (x.2, x.1) := by
    intro x
    by_cases h0 : vbK a b s w x.1 x.2 = 0
    · rw [h0, norm_zero]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact add_nonneg (hF0 _) (hF0 _)
    · rcases vbK_ne_zero_mem hs0 h0 with hq | hp
      · have : F x = ‖vbK a b s w x.1 x.2‖ ^ 2 := by simp [hF, hq]
        rw [this]; exact le_add_of_nonneg_right (hF0 _)
      · have : F (x.2, x.1) = ‖vbK a b s w x.1 x.2‖ ^ 2 := by
          simp only [hF, hp, if_true]
          rw [vbK_symm hab hw]
        rw [this]; exact le_add_of_nonneg_left (hF0 _)
  have hsumm : Summable fun x : Cfg eta × Cfg eta => ‖vbK a b s w x.1 x.2‖ ^ 2 :=
    (hFs.add hFs').of_nonneg_of_le (fun _ => sq_nonneg _) hdom
  refine ⟨hsumm, ?_⟩
  calc ∑' x : Cfg eta × Cfg eta, ‖vbK a b s w x.1 x.2‖ ^ 2
      ≤ ∑' x : Cfg eta × Cfg eta, (F x + F (x.2, x.1)) := hsumm.tsum_le_tsum hdom (hFs.add hFs')
    _ = ∑' x, F x + ∑' x : Cfg eta × Cfg eta, F (x.2, x.1) := hFs.tsum_add hFs'
    _ ≤ (Qbox eta s).card * T + (Qbox eta s).card * T := add_le_add hFle hFle'
    _ = 2 * ((Qbox eta s).card * T) := by ring

/-! ## `D(T)` is invariant: `(1 + E) Σ_b c = Σ_b ((1 + E) c) + V_b c` -/

lemma E_nonneg (hm : ∀ c, 0 < m c) (k : Cfg eta) : 0 ≤ E m g k := by
  unfold E
  exact Finset.sum_nonneg fun c _ => mul_nonneg (by have := hm c; positivity) (nsq_nonneg _)

/-- The coordinate identity behind `[T, Σ_b] = V_b` on `D(T)`. -/
theorem E_mul_sigma (hab : a ≠ b) (hm : ∀ c, 0 < m c) (hg : g ≠ 0) (hs : 4 / 3 ≤ s) {cw : ℝ}
    (hcw : 0 ≤ cw) (hwb : ∀ ν, |w ν| ≤ cw / nsq ν) (hw : ∀ ν, w (-ν) = w ν)
    (c ec : lp (fun _ : Cfg eta => ℂ) 2) (hec : ∀ k, ec k = ((E m g k : ℝ) : ℂ) * c k)
    (p : Cfg eta) :
    ((E m g p : ℝ) : ℂ) * (sigmaK_schur hab hm hg hs hcw hwb hw).toCLM c p =
      (sigmaK_schur hab hm hg hs hcw hwb hw).toCLM ec p + (vbK_hs hab hm hs hwb hw).toCLM c p := by
  set hS := sigmaK_schur hab hm hg hs hcw hwb hw
  set hV := vbK_hs (a := a) (b := b) (w := w) hab hm hs hwb hw
  rw [SchurBound.toCLM_apply, SchurBound.toCLM_apply, HSBound.toCLM_apply, kerApply, kerApply,
    kerApply, ← tsum_mul_left]
  have h1 : Summable fun q => sigmaK a b s m g w p q * ec q := hS.summable_row_apply ec p
  have h2 : Summable fun q => vbK a b s w p q * c q :=
    Summable.of_norm ((hV.summable_row_mul_norm c p).congr fun _ => (norm_mul _ _).symm)
  rw [← h1.tsum_add h2]
  refine tsum_congr fun q => ?_
  rw [hec, ← commutator_kernel hab hm hg (by linarith) p q]
  push_cast
  ring

/-! ## Graph-norm coordinates: `e^{Σ_b}` preserves `D(T)` -/

section Graph

variable (m g)

open Classical in
/-- The diagonal kernel `f(E(p))` (used with `f = (1 + E)⁻¹` and `f = E/(1 + E)`). -/
noncomputable def diagK (f : ℝ → ℝ) (p q : Cfg eta) : ℂ :=
  if p = q then ((f (E m g p) : ℝ) : ℂ) else 0

variable {m g}

lemma diagK_schur {f : ℝ → ℝ} (hf : ∀ k : Cfg eta, |f (E m g k)| ≤ 1) :
    SchurBound (diagK m g f) 1 1 := by
  classical
  have hrow : ∀ p : Cfg eta, (Summable fun q => ‖diagK m g f p q‖) ∧
      ∑' q, ‖diagK m g f p q‖ ≤ 1 := by
    intro p
    have hz : ∀ q ∉ ({p} : Finset (Cfg eta)), ‖diagK m g f p q‖ = 0 := by
      intro q hq
      rw [Finset.mem_singleton] at hq
      simp [diagK, Ne.symm hq]
    refine ⟨summable_of_ne_finset_zero hz, ?_⟩
    rw [tsum_eq_sum hz, Finset.sum_singleton]
    simpa [diagK] using hf p
  have hcol : ∀ q : Cfg eta, (Summable fun p => ‖diagK m g f p q‖) ∧
      ∑' p, ‖diagK m g f p q‖ ≤ 1 := by
    intro q
    have hz : ∀ p ∉ ({q} : Finset (Cfg eta)), ‖diagK m g f p q‖ = 0 := by
      intro p hp
      rw [Finset.mem_singleton] at hp
      simp [diagK, hp]
    refine ⟨summable_of_ne_finset_zero hz, ?_⟩
    rw [tsum_eq_sum hz, Finset.sum_singleton]
    simpa [diagK] using hf q
  exact ⟨fun p => (hrow p).1, fun p => (hrow p).2, fun q => (hcol q).1, fun q => (hcol q).2⟩

lemma diagK_apply {f : ℝ → ℝ} (hf : ∀ k : Cfg eta, |f (E m g k)| ≤ 1)
    (v : lp (fun _ : Cfg eta => ℂ) 2) (p : Cfg eta) :
    (diagK_schur hf).toCLM v p = ((f (E m g p) : ℝ) : ℂ) * v p := by
  classical
  rw [SchurBound.toCLM_apply, kerApply]
  have hz : ∀ q ∉ ({p} : Finset (Cfg eta)), diagK m g f p q * v q = 0 := by
    intro q hq
    rw [Finset.mem_singleton] at hq
    simp [diagK, Ne.symm hq]
  rw [tsum_eq_sum hz, Finset.sum_singleton]
  simp [diagK]

variable (hm : ∀ c, 0 < m c)
include hm

lemma inv_one_add_le (k : Cfg eta) : |(fun x : ℝ => (1 + x)⁻¹) (E m g k)| ≤ 1 := by
  have := E_nonneg (g := g) hm k
  rw [abs_of_pos (by positivity)]
  exact inv_le_one_of_one_le₀ (by linarith)

lemma div_one_add_le (k : Cfg eta) : |(fun x : ℝ => x / (1 + x)) (E m g k)| ≤ 1 := by
  have := E_nonneg (g := g) hm k
  rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
  linarith

/-- `S = (1 + E)⁻¹`: the decoding map from graph-norm coordinates to `D(T)`. -/
noncomputable def decS : lp (fun _ : Cfg eta => ℂ) 2 →L[ℂ] lp (fun _ : Cfg eta => ℂ) 2 :=
  (diagK_schur (m := m) (g := g) (f := fun x : ℝ => (1 + x)⁻¹)
    (inv_one_add_le (m := m) (g := g) hm)).toCLM

/-- `E S = E (1 + E)⁻¹`. -/
noncomputable def decES : lp (fun _ : Cfg eta => ℂ) 2 →L[ℂ] lp (fun _ : Cfg eta => ℂ) 2 :=
  (diagK_schur (m := m) (g := g) (f := fun x : ℝ => x / (1 + x))
    (div_one_add_le (m := m) (g := g) hm)).toCLM

lemma decS_apply (v : lp (fun _ : Cfg eta => ℂ) 2) (p : Cfg eta) :
    decS (g := g) hm v p = (((1 + E m g p)⁻¹ : ℝ) : ℂ) * v p :=
  diagK_apply (f := fun x : ℝ => (1 + x)⁻¹) (inv_one_add_le (m := m) (g := g) hm) v p

lemma decES_apply (v : lp (fun _ : Cfg eta => ℂ) 2) (p : Cfg eta) :
    decES (g := g) hm v p = ((E m g p / (1 + E m g p) : ℝ) : ℂ) * v p :=
  diagK_apply (f := fun x : ℝ => x / (1 + x)) (div_one_add_le (m := m) (g := g) hm) v p

/-- `D(T) = ran S`: a vector with `(1 + E) c ∈ ℓ²` is `S` of that vector. -/
lemma mem_range_decS (c v : lp (fun _ : Cfg eta => ℂ) 2)
    (hv : ∀ k, v k = ((1 + E m g k : ℝ) : ℂ) * c k) : decS (g := g) hm v = c := by
  ext p
  rw [decS_apply, hv]
  have : (1 + E m g p) ≠ 0 := by have := E_nonneg (g := g) hm p; positivity
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ this, Complex.ofReal_one, one_mul]

end Graph

variable (hab : a ≠ b) (hm : ∀ c, 0 < m c) (hg : g ≠ 0) (hs : 4 / 3 ≤ s) {cw : ℝ}
  (hcw : 0 ≤ cw) (hwb : ∀ ν, |w ν| ≤ cw / nsq ν) (hw : ∀ ν, w (-ν) = w ν)

/-- The generator in graph-norm coordinates: `Σ' = Σ_b + V_b S`. -/
noncomputable def sigmaGraph : lp (fun _ : Cfg eta => ℂ) 2 →L[ℂ] lp (fun _ : Cfg eta => ℂ) 2 :=
  (sigmaK_schur hab hm hg hs hcw hwb hw).toCLM +
    (vbK_hs (a := a) (b := b) (w := w) hab hm hs hwb hw).toCLM ∘L decS (g := g) hm

include hab hm hg hs hcw hwb hw in
/-- **Intertwining**: `S Σ' = Σ_b S`, i.e. `(1 + E) Σ_b c = Σ_b ((1 + E) c) + V_b c` on `D(T)`. -/
theorem decS_sigmaGraph :
    decS (g := g) hm ∘L sigmaGraph hab hm hg hs hcw hwb hw =
      (sigmaK_schur hab hm hg hs hcw hwb hw).toCLM ∘L decS (g := g) hm := by
  set Sig := (sigmaK_schur hab hm hg hs hcw hwb hw).toCLM
  set Vb := (vbK_hs (a := a) (b := b) (w := w) hab hm hs hwb hw).toCLM
  set S := decS (g := g) hm
  set ES := decES (g := g) hm
  ext v p
  simp only [ContinuousLinearMap.comp_apply]
  -- the identity of `E_mul_sigma` at `c = S v`, `ec = E S v`
  have hid := E_mul_sigma hab hm hg hs hcw hwb hw (S v) (ES v) (fun k => by
    rw [decES_apply, decS_apply, ← mul_assoc, ← Complex.ofReal_mul, div_eq_mul_inv]) p
  -- `S v + E S v = v`
  have hsum : S v + ES v = v := by
    ext k
    rw [lp.coeFn_add, Pi.add_apply, decS_apply, decES_apply, ← add_mul, ← Complex.ofReal_add]
    have : (1 + E m g k) ≠ 0 := by have := E_nonneg (g := g) hm k; positivity
    have h1 : (1 + E m g k)⁻¹ + E m g k / (1 + E m g k) = 1 := by field_simp
    rw [h1, Complex.ofReal_one, one_mul]
  have hlin : Sig (S v) p + Sig (ES v) p = Sig v p := by
    have h := map_add Sig (S v) (ES v)
    rw [hsum] at h
    rw [h]
    rfl
  have hne : (1 + E m g p) ≠ 0 := by have := E_nonneg (g := g) hm p; positivity
  have hneC : ((1 + E m g p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
  -- `(1 + E p) · (Σ_b S v)(p) = (Σ_b v)(p) + (V_b S v)(p)`
  have key : ((1 + E m g p : ℝ) : ℂ) * Sig (S v) p = Sig v p + Vb (S v) p := by
    rw [Complex.ofReal_add, Complex.ofReal_one, add_mul, one_mul, hid, ← hlin]
    ring
  rw [decS_apply]
  show _ * (sigmaGraph hab hm hg hs hcw hwb hw v p) = _
  have hsplit : sigmaGraph hab hm hg hs hcw hwb hw v p = Sig v p + Vb (S v) p := rfl
  rw [hsplit, ← key, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hne, Complex.ofReal_one, one_mul]

include hab hm hg hs hcw hwb hw in
/-- **`e^{Σ_b}` preserves `D(T)`**: `e^{Σ_b} S = S e^{Σ'}`; so `e^{Σ_b}` maps
`D(T) = ran S = {c : (1 + E) c ∈ ℓ²}` into itself, with `(1 + E) e^{Σ_b} c = e^{Σ'} ((1 + E) c)`. -/
theorem exp_sigma_preserves_domain (v : lp (fun _ : Cfg eta => ℂ) 2) :
    NormedSpace.exp (sigmaK_schur hab hm hg hs hcw hwb hw).toCLM (decS (g := g) hm v) =
      decS (g := g) hm (NormedSpace.exp (sigmaGraph hab hm hg hs hcw hwb hw) v) := by
  letI : NormedAlgebra ℚ (lp (fun _ : Cfg eta => ℂ) 2 →L[ℂ] lp (fun _ : Cfg eta => ℂ) 2) :=
    .restrictScalars ℚ ℂ _
  have hsc : SemiconjBy (decS (g := g) hm) (sigmaGraph hab hm hg hs hcw hwb hw)
      (sigmaK_schur hab hm hg hs hcw hwb hw).toCLM :=
    decS_sigmaGraph hab hm hg hs hcw hwb hw
  have := congrArg (fun X => X v) hsc.exp_right
  exact this.symm

end FluxSourceTest

/-! ## Part Bridge

Bridge: the prototype's objects are the release file's objects.  `L3`, `Cfg eta`, `nsq` and the
kinetic energy `E` with the masses of a `CoulombSystem` are `Lattice3`, `FourierConfig eta Lattice3`,
`latticeNormSq` and `coulombKineticEnergySymbol`; the generator acts on the release file's `ℓ²`
space of Fourier coefficients, with the Coulomb coefficients `c / |ν|²`.
-/

open PlaneWaveCertificate

namespace FluxSourceTest

lemma nsq_eq_latticeNormSq : nsq = latticeNormSq := rfl

lemma E_eq_kineticSymbol {eta : ℕ} {ν : Type*} (sys : CoulombSystem eta ν) (g : ℝ)
    (p : FourierConfig eta Lattice3) :
    E sys.mass g p = coulombKineticEnergySymbol sys g p := by
  unfold E coulombKineticEnergySymbol
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsq_eq_latticeNormSq]
  have := sys.mass_pos i
  field_simp

/-- The bulk generator for the Coulomb coefficient `c / |ν|²` of the pair `(a, b)`, on the
release file's `ℓ²(FourierConfig eta Lattice3)`, with the masses of the system. -/
theorem bulkGenerator_release {eta : ℕ} {ν : Type*} (sys : CoulombSystem eta ν) {a b : Fin eta}
    (hab : a ≠ b) {g s : ℝ} (hg : g ≠ 0) (hs : 4 / 3 ≤ s) (c : ℝ) :
    ∃ Sig : lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →L[ℂ]
        lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2,
      (∀ u p, Sig u p = ∑' q, sigmaK a b s sys.mass g (fun ν => c / latticeNormSq ν) p q * u q) ∧
      ‖Sig‖ ≤ schurConst sys.mass g s |c| a b ∧
      Sig ∈ skewAdjoint (lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →L[ℂ]
        lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) ∧
      NormedSpace.exp Sig ∈ unitary (lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2 →L[ℂ]
        lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2) ∧
      (∀ p q, ((coulombKineticEnergySymbol sys g p - coulombKineticEnergySymbol sys g q : ℝ) : ℂ) *
          sigmaK a b s sys.mass g (fun ν => c / latticeNormSq ν) p q =
        vbK a b s (fun ν => c / latticeNormSq ν) p q) := by
  have hwb : ∀ ν, |c / latticeNormSq ν| ≤ |c| / nsq ν := by
    intro ν
    rw [abs_div, abs_of_nonneg (latticeNormSq_nonneg ν), nsq_eq_latticeNormSq]
  have hw : ∀ ν, c / latticeNormSq (-ν) = c / latticeNormSq ν := by
    intro ν
    rw [← nsq_eq_latticeNormSq, nsq_neg]
  obtain ⟨Sig, h1, h2, h3, h4, h5⟩ :=
    bulkGenerator (a := a) (b := b) (s := s) (m := sys.mass) (g := g)
      (w := fun ν => c / latticeNormSq ν) hab sys.mass_pos hg hs (abs_nonneg c) hwb hw
  refine ⟨Sig, h1, h2, h3, h4, fun p q => ?_⟩
  rw [← E_eq_kineticSymbol, ← E_eq_kineticSymbol]
  exact h5 p q

end FluxSourceTest
