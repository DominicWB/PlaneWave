import PlaneWave.Source.BulkGeneratorPrototype
import PlaneWave.Source.LatticeSums
import Mathlib.Algebra.Order.Chebyshev

/-!
# Flux/source build, block 2a: channels and the potential on `ℓ²(ℤ^{3η})`

The full coefficient space is the release's `ℓ² = lp (FourierConfig eta Lattice3 → ℂ) 2`, with
`D(T)` the range of the decoding map `S = molecularH2StateMap` and the potential
`W = coulombFourierPotentialH2 = H - T` on the weighted coordinates.  This file supplies:

* the **channels** of the Coulomb kernel: one-body hops of a register (the nuclear terms) and pair
  hops (`Ch`, `tr`, `OnCh`); every nonzero element of the potential kernel lies on a channel, and
  `|w(q, p)| ≤ Σ_j [q = p + τ_j(ν)] c_j/|ν|²` (`norm_potKernel_le`);
* channel reindexing of row and column sums (`tsum_row`, `tsum_col` and their summability forms);
* the rows and columns of the kernel are square-summable;
* **the potential on `D(T)`**: `(W u)(q) = Σ_p (S u)(p) w(q, p)` for every `u` (`potential_apply`);
* the kernel is Hermitian, `w(p, q) = conj w(q, p)` (`potKernel_conj`), from the symmetry of `W`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics

namespace FSNormal

variable {eta : ℕ}

/-- Configurations of the full momentum lattice. -/
abbrev Cf (eta : ℕ) := FourierConfig eta Lattice3

/-- The full coefficient space `ℓ²(ℤ^{3η})`. -/
noncomputable abbrev L2 (eta : ℕ) := lp (fun _ : Cf eta => ℂ) 2

/-! ## Channels -/

/-- Channel labels: one-body hops of a register (nuclear terms) and pair hops. -/
abbrev Ch (eta : ℕ) := Fin eta ⊕ FiniteElectronPair eta

/-- The register whose momentum change labels the transfer. -/
def lead : Ch eta → Fin eta
  | .inl a => a
  | .inr pr => pr.1.1

/-- The configuration transfer of a channel with lattice transfer `ν`: `ν e_a`, or
`ν e_a - ν e_b` for the pair `(a, b)`. -/
def tr : Ch eta → Lattice3 → Cf eta
  | .inl a, ν => Pi.single a ν
  | .inr pr, ν => Pi.single pr.1.1 ν - Pi.single pr.1.2 ν

lemma tr_lead (j : Ch eta) (ν : Lattice3) : tr j ν (lead j) = ν := by
  cases j with
  | inl a => simp [tr, lead]
  | inr pr =>
    have h : pr.1.2 ≠ pr.1.1 := (ne_of_lt pr.2).symm
    simp [tr, lead, Pi.single_eq_of_ne' h]

/-- `q` is reached from `p` by one hop of channel `j`. -/
def OnCh (j : Ch eta) (q p : Cf eta) : Prop := q = p + tr j (q (lead j) - p (lead j))

lemma onCh_of_eq {j : Ch eta} {q p : Cf eta} {ν : Lattice3} (h : q = p + tr j ν) :
    OnCh j q p := by
  have e : q (lead j) - p (lead j) = ν := by
    rw [h, Pi.add_apply, tr_lead]; abel
  unfold OnCh; rw [e]; exact h

lemma onCh_sub (j : Ch eta) (q : Cf eta) (ν : Lattice3) : OnCh j q (q - tr j ν) :=
  onCh_of_eq (by abel)

lemma onCh_add (j : Ch eta) (p : Cf eta) (ν : Lattice3) : OnCh j (p + tr j ν) p :=
  onCh_of_eq rfl

lemma lead_sub_tr (j : Ch eta) (q : Cf eta) (ν : Lattice3) :
    q (lead j) - (q - tr j ν) (lead j) = ν := by
  rw [Pi.sub_apply, tr_lead]; abel

lemma lead_add_tr (j : Ch eta) (p : Cf eta) (ν : Lattice3) :
    (p + tr j ν) (lead j) - p (lead j) = ν := by
  rw [Pi.add_apply, tr_lead]; abel

lemma sub_tr_injective (j : Ch eta) (q : Cf eta) : Function.Injective fun ν => q - tr j ν := by
  intro ν ν' h
  have := congrFun h (lead j)
  simp only [Pi.sub_apply, tr_lead] at this
  exact sub_right_injective this

lemma add_tr_injective (j : Ch eta) (p : Cf eta) : Function.Injective fun ν => p + tr j ν := by
  intro ν ν' h
  have := congrFun h (lead j)
  simp only [Pi.add_apply, tr_lead] at this
  exact add_left_cancel this

/-- On a channel the input is the output minus the transfer. -/
lemma eq_sub_of_onCh {j : Ch eta} {q p : Cf eta} (h : OnCh j q p) :
    p = q - tr j (q (lead j) - p (lead j)) :=
  eq_sub_of_add_eq h.symm

/-- The symmetric form: `OnCh j q p ↔ OnCh j p q` (the reverse hop has transfer `-ν`). -/
lemma onCh_symm {j : Ch eta} {q p : Cf eta} (h : OnCh j q p) : OnCh j p q := by
  apply onCh_of_eq (ν := -(q (lead j) - p (lead j)))
  have e := eq_sub_of_onCh h
  have hneg : ∀ ν, tr j (-ν) = -tr j ν := by
    intro ν
    cases j with
    | inl a => simp only [tr, Pi.single_neg]
    | inr pr => simp only [tr, Pi.single_neg]; abel
  rw [hneg, ← sub_eq_add_neg]; exact e

/-! ## Reindexing along a channel -/

open Classical in
/-- Row sums along a channel are sums over the transfer. -/
lemma tsum_row (j : Ch eta) (q : Cf eta) (F : Cf eta → ℝ) :
    ∑' p, (if OnCh j q p then F p else 0) = ∑' ν, F (q - tr j ν) := by
  have hsupp : Function.support (fun p => if OnCh j q p then F p else 0) ⊆
      Set.range fun ν => q - tr j ν := by
    intro p hp
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hp
    exact ⟨_, (eq_sub_of_onCh hp.1).symm⟩
  rw [← (sub_tr_injective j q).tsum_eq hsupp]
  exact tsum_congr fun ν => by simp [onCh_sub]

open Classical in
lemma summable_row_iff (j : Ch eta) (q : Cf eta) (F : Cf eta → ℝ) :
    (Summable fun p => if OnCh j q p then F p else 0) ↔ Summable fun ν => F (q - tr j ν) := by
  have h := (sub_tr_injective j q).summable_iff
    (f := fun p => if OnCh j q p then F p else 0) (fun p hp => by
      by_contra hne
      simp only [ite_eq_right_iff, not_forall] at hne
      exact hp ⟨_, (eq_sub_of_onCh hne.1).symm⟩)
  rw [← h]
  exact summable_congr fun ν => by simp [onCh_sub]

open Classical in
/-- Column sums along a channel are sums over the transfer. -/
lemma tsum_col (j : Ch eta) (p : Cf eta) (F : Cf eta → ℝ) :
    ∑' q, (if OnCh j q p then F q else 0) = ∑' ν, F (p + tr j ν) := by
  have hsupp : Function.support (fun q => if OnCh j q p then F q else 0) ⊆
      Set.range fun ν => p + tr j ν := by
    intro q hq
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hq
    exact ⟨_, hq.1.symm⟩
  rw [← (add_tr_injective j p).tsum_eq hsupp]
  exact tsum_congr fun ν => by simp [onCh_add]

open Classical in
lemma summable_col_iff (j : Ch eta) (p : Cf eta) (F : Cf eta → ℝ) :
    (Summable fun q => if OnCh j q p then F q else 0) ↔ Summable fun ν => F (p + tr j ν) := by
  have h := (add_tr_injective j p).summable_iff
    (f := fun q => if OnCh j q p then F q else 0) (fun q hq => by
      by_contra hne
      simp only [ite_eq_right_iff, not_forall] at hne
      exact hq ⟨_, hne.1.symm⟩)
  rw [← h]
  exact summable_congr fun ν => by simp [onCh_add]

/-! ## Lattice sums -/

lemma one_le_latticeNormSq {ν : Lattice3} (hν : ν ≠ 0) : 1 ≤ latticeNormSq ν := by
  obtain ⟨i, hi⟩ : ∃ i, ν i ≠ 0 := by
    by_contra h
    push Not at h
    exact hν (funext h)
  have h1 : (1 : ℝ) ≤ ((ν i : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (ν i) ^ 2 := by
      have := Int.one_le_abs hi
      nlinarith [sq_abs (ν i)]
    exact_mod_cast this
  have h2 : ((ν i : ℤ) : ℝ) ^ 2 ≤ latticeNormSq ν := FluxSourceTest.coord_sq_le_nsq ν i
  linarith

/-- `|ν|⁻⁴ ≤ 4 (1 + |ν|²)^{-2}` (both sides vanish or are comparable). -/
lemma inv4_le_weight (ν : Lattice3) :
    (latticeNormSq ν)⁻¹ ^ 2 ≤ 4 * (1 + FSLattice.lsq ν) ^ (-(2 : ℝ)) := by
  have hl : FSLattice.lsq ν = latticeNormSq ν := rfl
  rw [hl, Real.rpow_neg (by linarith [latticeNormSq_nonneg ν]),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  by_cases h0 : ν = 0
  · subst h0
    have : latticeNormSq (0 : Lattice3) = 0 := by simp [latticeNormSq]
    rw [this]; simp
  · have h1 := one_le_latticeNormSq h0
    have hpos : 0 < latticeNormSq ν := by linarith
    rw [inv_pow]
    have key : (1 + latticeNormSq ν) ^ 2 / 4 ≤ latticeNormSq ν ^ 2 := by nlinarith
    calc (latticeNormSq ν ^ 2)⁻¹ ≤ ((1 + latticeNormSq ν) ^ 2 / 4)⁻¹ :=
          inv_anti₀ (by positivity) key
      _ = 4 * ((1 + latticeNormSq ν) ^ 2)⁻¹ := by rw [inv_div, div_eq_mul_inv]

/-- `ν ↦ |ν|⁻⁴` is summable over `ℤ³` (with `0⁻¹ = 0`). -/
lemma summable_inv4 : Summable fun ν : Lattice3 => (latticeNormSq ν)⁻¹ ^ 2 :=
  ((FSLattice.summable_weight (s := 2) (by norm_num)).mul_left 4).of_nonneg_of_le
    (fun _ => by positivity) inv4_le_weight

/-! ## The potential kernel and its channel majorant -/

open Classical in
/-- The channel majorant `[q = p + τ_j(ν)] c / |ν|²`. -/
noncomputable def chMaj (j : Ch eta) (c : ℝ) (q p : Cf eta) : ℝ :=
  if OnCh j q p then c / latticeNormSq (q (lead j) - p (lead j)) else 0

lemma chMaj_nonneg (j : Ch eta) {c : ℝ} (hc : 0 ≤ c) (q p : Cf eta) : 0 ≤ chMaj j c q p := by
  unfold chMaj; split_ifs
  · exact div_nonneg hc (latticeNormSq_nonneg _)
  · exact le_rfl

variable {ν : Type} [Fintype ν]

/-- The coefficient constants of the channels: `|Z_a| Σ_ℓ Z_ℓ γ` for the nuclear hops of `a`,
`|Z_a Z_b| γ` for the pair `(a, b)`, `γ = 1/(π L)`. -/
noncomputable def chC (sys : CoulombSystem eta ν) (L : ℝ) : Ch eta → ℝ
  | .inl a => |sys.charge a| * (∑ ell, sys.nuclei.charge ell) * coulombCellAmplitude L
  | .inr pr => |sys.charge pr.1.1 * sys.charge pr.1.2| * coulombCellAmplitude L

lemma chC_nonneg (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (j : Ch eta) :
    0 ≤ chC sys L j := by
  have hγ : 0 ≤ coulombCellAmplitude L := by unfold coulombCellAmplitude; positivity
  cases j with
  | inl a =>
    have : 0 ≤ ∑ ell, sys.nuclei.charge ell :=
      Finset.sum_nonneg fun ell _ => sys.nuclei.charge_nonneg ell
    simp only [chC]; positivity
  | inr pr => simp only [chC]; positivity

/-- The total channel majorant. -/
noncomputable def potMaj (sys : CoulombSystem eta ν) (L : ℝ) (q p : Cf eta) : ℝ :=
  ∑ j : Ch eta, chMaj j (chC sys L j) q p

lemma potMaj_nonneg (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (q p : Cf eta) :
    0 ≤ potMaj sys L q p :=
  Finset.sum_nonneg fun j _ => chMaj_nonneg j (chC_nonneg sys hL j) q p

lemma norm_latticeCoulombKernel_le {L : ℝ} (hL : 0 < L) (x y : Lattice3) :
    ‖latticeCoulombKernel (coulombCellAmplitude L ^ 2) x y‖ ≤
      coulombCellAmplitude L / latticeNormSq (x - y) := by
  have hγ : 0 ≤ coulombCellAmplitude L := by unfold coulombCellAmplitude; positivity
  rw [latticeCoulombKernel_of_amplitude_sq _ hγ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hγ (latticeNormSq_nonneg _))]
  rfl

/-- The nuclear part of the kernel lies on the one-body channels. -/
lemma norm_nuclear_le (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (q p : Cf eta) :
    ‖coulombLatticeNuclearKernel sys (coulombCellAmplitude L) q p‖ ≤
      ∑ a : Fin eta, chMaj (.inl a) (chC sys L (.inl a)) q p := by
  classical
  unfold coulombLatticeNuclearKernel
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  unfold chMaj chC
  by_cases hs : ∀ k : Fin eta, k ≠ a → q k = p k
  · have hon : OnCh (.inl a) q p := by
      apply onCh_of_eq (ν := q a - p a)
      funext k
      by_cases hk : k = a
      · subst hk; simp [tr]
      · simp [tr, Pi.single_eq_of_ne hk, hs k hk]
    rw [if_pos hon]
    simp only [lead]
    have hterm : ∀ ell : ν, ‖latticeReferenceConfigurationKernel a
        (latticeElectronNuclearKernel sys.nuclei (coulombCellAmplitude L) ell) q p‖ ≤
        sys.nuclei.charge ell * (coulombCellAmplitude L / latticeNormSq (q a - p a)) := by
      intro ell
      unfold latticeReferenceConfigurationKernel
      rw [if_pos hs]
      unfold latticeElectronNuclearKernel
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sys.nuclei.charge_nonneg ell), norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (sys.nuclei.charge_nonneg ell)
      have hc : ‖UnitAddTorus.mFourier (latticeSub (q a) (p a)) (sys.nuclei.position ell)‖ ≤ 1 :=
        (ContinuousMap.norm_coe_le_norm _ _).trans UnitAddTorus.mFourier_norm.le
      calc _ ≤ 1 * ‖latticeCoulombKernel (coulombCellAmplitude L ^ 2) (q a) (p a)‖ :=
            mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact norm_latticeCoulombKernel_le hL _ _
    calc |sys.charge a| * ‖∑ ell, latticeReferenceConfigurationKernel a
          (latticeElectronNuclearKernel sys.nuclei (coulombCellAmplitude L) ell) q p‖
        ≤ |sys.charge a| * ∑ ell, sys.nuclei.charge ell *
            (coulombCellAmplitude L / latticeNormSq (q a - p a)) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun ell _ =>
            hterm ell)) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  · have hz : ∀ ell : ν, latticeReferenceConfigurationKernel a
        (latticeElectronNuclearKernel sys.nuclei (coulombCellAmplitude L) ell) q p = 0 := by
      intro ell
      unfold latticeReferenceConfigurationKernel
      rw [if_neg hs]
    simp only [hz, Finset.sum_const_zero, norm_zero, mul_zero]
    split_ifs
    · have hγ : 0 ≤ coulombCellAmplitude L := by unfold coulombCellAmplitude; positivity
      have : 0 ≤ ∑ ell, sys.nuclei.charge ell :=
        Finset.sum_nonneg fun ell _ => sys.nuclei.charge_nonneg ell
      exact div_nonneg (by positivity) (latticeNormSq_nonneg _)
    · exact le_rfl

/-- The pair part of the kernel lies on the pair channels. -/
lemma norm_pair_le (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (q p : Cf eta) :
    ‖coulombLatticePairKernel sys (coulombCellAmplitude L) q p‖ ≤
      ∑ pr : FiniteElectronPair eta, chMaj (.inr pr) (chC sys L (.inr pr)) q p := by
  classical
  unfold coulombLatticePairKernel
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun pr _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold chMaj chC
  have hγ : 0 ≤ coulombCellAmplitude L := by unfold coulombCellAmplitude; positivity
  unfold latticeElectronPairConfigurationKernel
  split_ifs with h hon hon
  · simp only [lead]
    have := norm_latticeCoulombKernel_le hL (q pr.1.1) (p pr.1.1)
    calc _ ≤ |sys.charge pr.1.1 * sys.charge pr.1.2| *
            (coulombCellAmplitude L / latticeNormSq (q pr.1.1 - p pr.1.1)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  · exfalso; apply hon
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    apply onCh_of_eq (ν := q pr.1.1 - p pr.1.1)
    funext k
    by_cases hk1 : k = pr.1.1
    · subst hk1; simp [tr, Pi.single_eq_of_ne hne]
    · by_cases hk2 : k = pr.1.2
      · subst hk2
        simp only [tr, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne' hne]
        linear_combination h.2
      · simp [tr, Pi.single_eq_of_ne hk1, Pi.single_eq_of_ne hk2, h.1 k hk1 hk2]
  · simp only [norm_zero, mul_zero]
    exact div_nonneg (by positivity) (latticeNormSq_nonneg _)
  · simp

/-- **The channel majorant of the potential kernel.** -/
theorem norm_potKernel_le (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (q p : Cf eta) :
    ‖potKernel sys L q p‖ ≤ potMaj sys L q p := by
  unfold potKernel potMaj
  rw [Fintype.sum_sum_type]
  exact (norm_add_le _ _).trans (add_le_add (norm_nuclear_le sys hL q p) (norm_pair_le sys hL q p))

/-! ## Square-summable rows and columns -/

lemma summable_chMaj_sq_row (j : Ch eta) (c : ℝ) (q : Cf eta) :
    Summable fun p => chMaj j c q p ^ 2 := by
  classical
  have e : (fun p => chMaj j c q p ^ 2) = fun p =>
      if OnCh j q p then (c / latticeNormSq (q (lead j) - p (lead j))) ^ 2 else 0 := by
    funext p; unfold chMaj; split_ifs <;> simp
  rw [e, summable_row_iff]
  refine (summable_inv4.mul_left (c ^ 2)).congr fun ν => ?_
  rw [lead_sub_tr, div_pow, div_eq_mul_inv, inv_pow]

lemma summable_chMaj_sq_col (j : Ch eta) (c : ℝ) (p : Cf eta) :
    Summable fun q => chMaj j c q p ^ 2 := by
  classical
  have e : (fun q => chMaj j c q p ^ 2) = fun q =>
      if OnCh j q p then (c / latticeNormSq (q (lead j) - p (lead j))) ^ 2 else 0 := by
    funext q; unfold chMaj; split_ifs <;> simp
  rw [e, summable_col_iff]
  refine (summable_inv4.mul_left (c ^ 2)).congr fun ν => ?_
  rw [lead_add_tr, div_pow, div_eq_mul_inv, inv_pow]

lemma sq_potMaj_le (sys : CoulombSystem eta ν) (L : ℝ) (q p : Cf eta) :
    potMaj sys L q p ^ 2 ≤ Fintype.card (Ch eta) * ∑ j : Ch eta, chMaj j (chC sys L j) q p ^ 2 := by
  unfold potMaj
  exact sq_sum_le_card_mul_sum_sq

lemma summable_potKernel_sq_row (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (q : Cf eta) :
    Summable fun p => ‖potKernel sys L q p‖ ^ 2 := by
  have hs : Summable fun p => (Fintype.card (Ch eta) : ℝ) *
      ∑ j : Ch eta, chMaj j (chC sys L j) q p ^ 2 :=
    (summable_sum fun j _ => summable_chMaj_sq_row j _ q).mul_left _
  refine hs.of_nonneg_of_le (fun _ => sq_nonneg _) fun p => ?_
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_potKernel_le sys hL q p) 2).trans
    (sq_potMaj_le sys L q p)

lemma summable_potKernel_sq_col (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (p : Cf eta) :
    Summable fun q => ‖potKernel sys L q p‖ ^ 2 := by
  have hs : Summable fun q => (Fintype.card (Ch eta) : ℝ) *
      ∑ j : Ch eta, chMaj j (chC sys L j) q p ^ 2 :=
    (summable_sum fun j _ => summable_chMaj_sq_col j _ p).mul_left _
  refine hs.of_nonneg_of_le (fun _ => sq_nonneg _) fun q => ?_
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_potKernel_le sys hL q p) 2).trans
    (sq_potMaj_le sys L q p)

/-- A product of two square-summable sequences is summable. -/
lemma summable_mul_of_sq {ι : Type*} {f g : ι → ℂ} (hf : Summable fun i => ‖f i‖ ^ 2)
    (hg : Summable fun i => ‖g i‖ ^ 2) : Summable fun i => f i * g i := by
  refine Summable.of_norm_bounded ((hf.add hg).mul_left (1 / 2)) fun i => ?_
  rw [norm_mul]
  nlinarith [sq_nonneg (‖f i‖ - ‖g i‖)]

/-! ## The potential on `D(T)` -/

variable (sys : CoulombSystem eta ν) (L : ℝ)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

lemma summable_coeff_potKernel (hL : 0 < L) (u : MolecularFourierH2 eta) (q : Cf eta) :
    Summable fun p => molecularH2Coeff (2 * Real.pi / L) u p * potKernel sys L q p :=
  summable_mul_of_sq (summable_stateMap_sq _ u) (summable_potKernel_sq_row sys hL q)

include hKernel in
/-- **The potential on `D(T)`**: `(W u)(q) = Σ_p (S u)(p) w(q, p)` for every `u ∈ H²`. -/
theorem potential_apply (hL : 0 < L) (u : MolecularFourierH2 eta) (q : Cf eta) :
    coulombFourierPotentialH2 sys (2 * Real.pi / L) H u q =
      ∑' p, molecularH2Coeff (2 * Real.pi / L) u p * potKernel sys L q p := by
  set W := coulombFourierPotentialH2 sys (2 * Real.pi / L) H
  have hs := summable_coeff_potKernel sys L hL u q
  -- the cube partial sums converge to the series
  have hcube : Tendsto (fun N => fourierConfigCube eta N) atTop atTop :=
    tendsto_atTop_finset_of_monotone (fourierConfigCube_mono eta)
      fun p => exists_mem_fourierConfigCube p
  have h1 := hs.hasSum.comp hcube
  -- the partial sums are `W` of the truncations
  have hpart : ∀ N, (∑ p ∈ fourierConfigCube eta N,
      molecularH2Coeff (2 * Real.pi / L) u p * potKernel sys L q p) =
      W (molecularH2Truncate N u) q := by
    intro N
    rw [coulombFourierPotentialH2_core sys L H hKernel N u q]
    rfl
  -- and those converge to `W u q`
  have h2 : Tendsto (fun N => W (molecularH2Truncate N u) q) atTop (𝓝 (W u q)) := by
    have hW := (W.continuous.tendsto u).comp (molecularH2Truncate_tendsto u)
    rw [tendsto_iff_norm_sub_tendsto_zero] at hW ⊢
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hW
    have := FluxSourceTest.norm_coord_le (W (molecularH2Truncate N u) - W u) q
    simpa only [Function.comp_apply, lp.coeFn_sub, Pi.sub_apply] using this
  simp only [Function.comp_def, hpart] at h1
  exact tendsto_nhds_unique h2 h1

/-! ## Basis vectors and the Hermitian kernel -/

/-- The lattice basis vector `e_p ∈ ℓ²`. -/
noncomputable def ev (p : Cf eta) : L2 eta := lp.single 2 p (1 : ℂ)

/-- Weighted coordinates of `e_p`: `S (δ_p) = e_p`. -/
noncomputable def wdelta (g : ℝ) (p : Cf eta) : MolecularFourierH2 eta :=
  lp.single 2 p ((molecularFourierH2Weight eta g p : ℝ) : ℂ)

omit [Fintype ν] in
lemma coeff_wdelta (g : ℝ) (p r : Cf eta) :
    molecularH2Coeff g (wdelta g p) r = if r = p then 1 else 0 := by
  classical
  unfold molecularH2Coeff wdelta
  rw [lp.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h
    have := molecularFourierH2Weight_pos eta g r
    exact div_self (Complex.ofReal_ne_zero.mpr this.ne')
  · simp

omit [Fintype ν] in
lemma stateMap_wdelta (g : ℝ) (p : Cf eta) : molecularH2StateMap eta g (wdelta g p) = ev p := by
  classical
  ext r
  rw [molecularH2StateMap_apply, coeff_wdelta, ev, lp.single_apply, Pi.single_apply]

include hKernel in
lemma potential_wdelta (hL : 0 < L) (p q : Cf eta) :
    coulombFourierPotentialH2 sys (2 * Real.pi / L) H (wdelta (2 * Real.pi / L) p) q =
      potKernel sys L q p := by
  classical
  rw [potential_apply sys L H hKernel hL]
  simp_rw [coeff_wdelta, ite_mul, one_mul, zero_mul]
  rw [tsum_ite_eq]

omit [Fintype ν] in
lemma inner_ev_left (p : Cf eta) (x : L2 eta) : ⟪ev p, x⟫_ℂ = x p := by
  rw [ev, lp.inner_single_left]; simp

include hKernel in
/-- **The kernel is Hermitian**: `w(p, q) = conj w(q, p)`, from the symmetry of `W`. -/
theorem potKernel_conj (hL : 0 < L) (q p : Cf eta) :
    potKernel sys L p q = conj (potKernel sys L q p) := by
  have h := potential_symm sys L H hKernel (wdelta (2 * Real.pi / L) q) (wdelta (2 * Real.pi / L) p)
  rw [stateMap_wdelta, stateMap_wdelta, inner_ev_left, ← inner_conj_symm, inner_ev_left,
    potential_wdelta sys L H hKernel hL, potential_wdelta sys L H hKernel hL] at h
  rw [h, Complex.conj_conj]

end FSNormal
