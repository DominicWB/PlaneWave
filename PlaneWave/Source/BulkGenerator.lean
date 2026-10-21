import PlaneWave.Source.ChannelPotentials

/-!
# Flux/source build, block 2b: the bulk generator `Σ_b` for all channels

On `ℓ²(ℤ^{3η})`, with the cube `P` (`InP n`, `‖k_a‖_∞ ≤ n` in lattice units), the bulk block `Q`
(`InQ n`, every register of Euclidean length at most `n/4`) and the bulk-fed crossings
(`Cross n`, one end in `Q` and the other outside `P`):

* `channel_gap` (`lem:gap` for every channel, the one-body hops being the infinite-mass limit of
  the pair hops): a crossing on channel `j` with transfer `ν` has `|ν| > 3n/4` and
  `|E(q) - E(p)| ≥ c_gap |ν|²`, `c_gap = g²/(20 m_top)`, `m_top = 1 + Σ_a m_a`;
* the kernel `σ(q, p) = w(q, p)/(E(q) - E(p))` on the crossings (eq:Sigma), its channel majorant
  `|σ| ≤ Σ_j (c_j/c_gap) |ν_j|⁻⁴ [|ν_j| > 3n/4]`, Schur's bound `‖Σ_b‖ ≤ A_σ`,
  `A_σ = Σ_j (c_j/c_gap) · 416/(3n)` (the manuscript's `C/K`), anti-Hermiticity, and the unitary
  `U = e^{Σ_b}` (`sig_skew`, `U_unitary`);
* `V_b` (kernel `w · [crossing]`), Hilbert–Schmidt; `(E(q) - E(p)) σ(q, p) = v_b(q, p)`;
* the decoded generator `Σ_D` (kernel `(1 + |k|²)(q) σ(q, p)`, Hilbert–Schmidt) with
  `S Σ_D = Σ_b`: `Σ_b` maps `ℓ²` into `D(T)` boundedly;
* `kinetic_comm`: `T Σ_D S u - Σ_b T u = V_b S u` for every `u ∈ H²` (`[T, Σ_b] = V_b` on `D(T)`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Masses and the uniform gap constant -/

/-- An upper bound for every mass. -/
noncomputable def mtop (sys : CoulombSystem eta ν) : ℝ := 1 + ∑ a, sys.mass a

omit [Fintype ν] in
lemma mass_le_mtop (sys : CoulombSystem eta ν) (a : Fin eta) : sys.mass a ≤ mtop sys := by
  unfold mtop
  have := Finset.single_le_sum (f := sys.mass) (fun b _ => (sys.mass_pos b).le) (Finset.mem_univ a)
  linarith

omit [Fintype ν] in
lemma one_le_mtop (sys : CoulombSystem eta ν) : 1 ≤ mtop sys := by
  unfold mtop
  have := Finset.sum_nonneg (s := Finset.univ) fun b (_ : b ∈ Finset.univ) => (sys.mass_pos b).le
  linarith

/-- The uniform gap constant `g²/(20 m_top)`. -/
noncomputable def cgap (sys : CoulombSystem eta ν) (g : ℝ) : ℝ := g ^ 2 / (20 * mtop sys)

omit [Fintype ν] in
lemma cgap_pos (sys : CoulombSystem eta ν) {g : ℝ} (hg : g ≠ 0) : 0 < cgap sys g := by
  unfold cgap; have := one_le_mtop sys; positivity

/-! ## The one-body gap -/

lemma add_single_self (k : Cf eta) (a : Fin eta) (x : Lattice3) :
    (k + Pi.single a x : Cf eta) a = k a + x := by
  simp

lemma add_single_ne (k : Cf eta) {a c : Fin eta} (h : c ≠ a) (x : Lattice3) :
    (k + Pi.single a x : Cf eta) c = k c := by
  simp [Pi.single_eq_of_ne h]

lemma E_add_single_sub (m : Fin eta → ℝ) (g : ℝ) (k : Cf eta) (a : Fin eta) (x : Lattice3) :
    E m g (k + Pi.single a x) - E m g k = g ^ 2 / (2 * m a) * (nsq (k a + x) - nsq (k a)) := by
  unfold E
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
  · rw [add_single_self]; ring
  · intro c _ hc; rw [add_single_ne k hc, sub_self]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- The real inequality behind the one-body gap. -/
lemma one_gap_core {s : ℝ} (hs : 0 < s) {k x : L3} (hk : nsq k ≤ (s / 4) ^ 2)
    (hx : s ^ 2 < nsq (k + x)) : (3 * s / 4) ^ 2 < nsq x ∧ 3 / 5 * nsq x ≤ nsq (k + x) - nsq k := by
  set X := Real.sqrt (nsq x) with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = nsq x := Real.sq_sqrt (nsq_nonneg x)
  have hk' : Real.sqrt (nsq k) ≤ s / 4 := Real.sqrt_le_iff.mpr ⟨by linarith, hk⟩
  have hc : |ldot k x| ≤ s / 4 * X :=
    (abs_ldot_le k x).trans (mul_le_mul_of_nonneg_right hk' hX0)
  have hsum := nsq_add k x
  have hlo := neg_le_of_abs_le hc
  have hhi := le_of_abs_le hc
  have hk0 := nsq_nonneg k
  have hk2 : nsq k ≤ s ^ 2 / 16 := by nlinarith
  have hup : nsq (k + x) ≤ s ^ 2 / 16 + s / 2 * X + X ^ 2 := by
    rw [hsum, hX2]; linarith
  have h1 : s ^ 2 < (s / 4 + X) ^ 2 := by
    have e : (s / 4 + X) ^ 2 = s ^ 2 / 16 + s / 2 * X + X ^ 2 := by ring
    rw [e]; linarith
  have h2 : s < s / 4 + X := (pow_lt_pow_iff_left₀ hs.le (by positivity) two_ne_zero).mp h1
  have h3 : 3 * s / 4 < X := by linarith
  refine ⟨?_, ?_⟩
  · rw [← hX2]
    exact pow_lt_pow_left₀ h3 (by linarith) two_ne_zero
  · have hdiff : nsq (k + x) - nsq k = 2 * ldot k x + X ^ 2 := by rw [hsum, hX2]; ring
    rw [← hX2, hdiff]
    by_cases hbig : 5 * s / 4 ≤ X
    · have hp : 0 ≤ X * (2 / 5 * X - s / 2) := mul_nonneg hX0 (by linarith)
      nlinarith
    · push Not at hbig
      have hX2' : X ^ 2 < (5 * s / 4) ^ 2 := pow_lt_pow_left₀ hbig hX0 two_ne_zero
      have : 15 * s ^ 2 / 16 < 2 * ldot k x + X ^ 2 := by
        rw [← hdiff]; linarith
      nlinarith

/-- The one-body gap in the orientation `Q → outside P`. -/
lemma one_gap_Q {s : ℝ} (hs : 0 < s) {k : Cf eta} {a : Fin eta} {y : Lattice3}
    (hk : InQ s k) (hp : ¬ InP s (k + Pi.single a y : Cf eta)) :
    (3 * s / 4) ^ 2 < nsq y ∧ 3 / 5 * nsq y ≤ nsq (k a + y) - nsq (k a) := by
  apply one_gap_core hs (hk a)
  unfold InP at hp
  push Not at hp
  obtain ⟨c, i, hci⟩ := hp
  by_cases hca : c = a
  · subst hca
    rw [add_single_self] at hci
    have h1 := coord_sq_le_nsq (k c + y) i
    have h2 : s ^ 2 < (((k c + y) i : ℤ) : ℝ) ^ 2 := by
      have := pow_lt_pow_left₀ hci hs.le two_ne_zero
      rwa [sq_abs] at this
    linarith
  · rw [add_single_ne k hca] at hci
    exact absurd (hk.inP hs.le c i) (not_le.mpr hci)

lemma add_single_add_neg (p : Cf eta) (a : Fin eta) (x : Lattice3) :
    ((p + Pi.single a x : Cf eta) + Pi.single a (-x) : Cf eta) = p := by
  rw [add_assoc, ← Pi.single_add, add_neg_cancel, Pi.single_zero, add_zero]

/-- **The one-body gap** (the infinite-mass limit of `lem:gap`): a crossing by a one-body hop has
transfer `|ν| > 3s/4` and mismatch at least `(3/5) g² |ν|²/(2 m_a)`. -/
theorem energy_gap_one {m : Fin eta → ℝ} {g s : ℝ} (hm : ∀ c, 0 < m c) (hs : 0 < s)
    {q p : Cf eta} {a : Fin eta} {x : Lattice3} (hq : q = p + Pi.single a x) (hc : Cross s q p) :
    (3 * s / 4) ^ 2 < nsq x ∧ g ^ 2 * (3 / 5 * nsq x) / (2 * m a) ≤ |E m g q - E m g p| := by
  have hma := hm a
  have hcoef : 0 ≤ g ^ 2 / (2 * m a) := by positivity
  rcases hc with ⟨hqQ, hp⟩ | ⟨hqP, hpQ⟩
  · -- output in `Q`, input outside `P`: reverse the hop
    have hrev : (q + Pi.single a (-x) : Cf eta) = p := by rw [hq]; exact add_single_add_neg p a x
    obtain ⟨h1, h2⟩ := one_gap_Q hs hqQ (show ¬ InP s (q + Pi.single a (-x) : Cf eta) by rwa [hrev])
    rw [nsq_neg] at h1 h2
    refine ⟨h1, ?_⟩
    have hE := E_add_single_sub m g q a (-x)
    rw [hrev] at hE
    rw [abs_sub_comm, hE]
    calc g ^ 2 * (3 / 5 * nsq x) / (2 * m a) = g ^ 2 / (2 * m a) * (3 / 5 * nsq x) := by ring
      _ ≤ g ^ 2 / (2 * m a) * (nsq (q a + -x) - nsq (q a)) := mul_le_mul_of_nonneg_left h2 hcoef
      _ ≤ _ := le_abs_self _
  · obtain ⟨h1, h2⟩ := one_gap_Q hs hpQ (show ¬ InP s (p + Pi.single a x : Cf eta) by rwa [← hq])
    refine ⟨h1, ?_⟩
    rw [hq, E_add_single_sub]
    calc g ^ 2 * (3 / 5 * nsq x) / (2 * m a) = g ^ 2 / (2 * m a) * (3 / 5 * nsq x) := by ring
      _ ≤ g ^ 2 / (2 * m a) * (nsq (p a + x) - nsq (p a)) := mul_le_mul_of_nonneg_left h2 hcoef
      _ ≤ _ := le_abs_self _

/-! ## The gap on every channel -/

lemma tr_pair_eq_shift (pr : FiniteElectronPair eta) (p : Cf eta) (x : Lattice3) :
    p + tr (.inr pr) x = shift pr.1.1 pr.1.2 p x := by
  have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
  funext c
  by_cases h1 : c = pr.1.1
  · subst h1
    rw [shift_apply_a]
    simp [tr, Pi.single_eq_of_ne hne]
  · by_cases h2 : c = pr.1.2
    · subst h2
      rw [shift_apply_b hne]
      simp [tr, Pi.single_eq_of_ne' hne, sub_eq_add_neg]
    · rw [shift_apply_of_ne h1 h2]
      simp [tr, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]

omit [Fintype ν] in
/-- **`lem:gap` on every channel.** A crossing on channel `j` with transfer `ν` has `|ν| > 3s/4`
and `|E(q) - E(p)| ≥ c_gap |ν|²`. -/
theorem channel_gap (sys : CoulombSystem eta ν) {g s : ℝ} (hg : g ≠ 0) (hs : 0 < s)
    {j : Ch eta} {q p : Cf eta} (hon : OnCh j q p) (hc : Cross s q p) :
    (3 * s / 4) ^ 2 < nsq (q (lead j) - p (lead j)) ∧
      cgap sys g * nsq (q (lead j) - p (lead j)) ≤ |E sys.mass g q - E sys.mass g p| := by
  have hm : ∀ c, 0 < sys.mass c := fun c => sys.mass_pos c
  set x := q (lead j) - p (lead j)
  have hx0 := nsq_nonneg x
  have hg2 : 0 < g ^ 2 := by positivity
  have hmt := one_le_mtop sys
  cases j with
  | inl a =>
    have hq : q = p + Pi.single a x := hon
    obtain ⟨h1, h2⟩ := energy_gap_one (g := g) hm hs hq hc
    refine ⟨h1, le_trans ?_ h2⟩
    have hma := hm a
    have hle := mass_le_mtop sys a
    unfold cgap
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hg2.le hx0, mul_nonneg (mul_nonneg hg2.le hx0) (sub_nonneg.mpr hle)]
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    have hq : q = shift pr.1.1 pr.1.2 p x := by rw [← tr_pair_eq_shift]; exact hon
    rw [hq] at hc ⊢
    obtain ⟨h1, h2⟩ := energy_gap (g := g) hne hm hs hc.symm
    refine ⟨h1, le_trans ?_ h2⟩
    have hma := hm pr.1.1
    have hle := mass_le_mtop sys pr.1.1
    have hmb := hm pr.1.2
    have h3 : 1 / mtop sys ≤ 1 / sys.mass pr.1.1 + 1 / sys.mass pr.1.2 := by
      have : 1 / mtop sys ≤ 1 / sys.mass pr.1.1 := one_div_le_one_div_of_le hma hle
      have : 0 ≤ 1 / sys.mass pr.1.2 := by positivity
      linarith
    unfold cgap
    calc g ^ 2 / (20 * mtop sys) * nsq x = g ^ 2 * (nsq x / 20 * (1 / mtop sys)) := by
          field_simp
      _ ≤ g ^ 2 * (nsq x / 20 * (1 / sys.mass pr.1.1 + 1 / sys.mass pr.1.2)) := by
          gcongr

/-! ## The kernel of `Σ_b` -/

/-- `g = 2π/L`. -/
noncomputable def gF (L : ℝ) : ℝ := 2 * Real.pi / L

lemma gF_pos {L : ℝ} (hL : 0 < L) : 0 < gF L := by unfold gF; positivity

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

/-- The kinetic energy `E(k) = Σ_c g² |k_c|²/(2 m_c)`. -/
noncomputable abbrev Ek (k : Cf eta) : ℝ := E sys.mass (gF L) k

open Classical in
/-- **The kernel of the bulk generator** (eq:Sigma): `σ(q, p) = w(q, p)/(E(q) - E(p))` on the
bulk-fed crossings. -/
noncomputable def sigK (q p : Cf eta) : ℂ :=
  if Cross (n : ℝ) q p then potKernel sys L q p / ((Ek sys L q - Ek sys L p : ℝ) : ℂ) else 0

open Classical in
/-- The kernel of `V_b`: the potential kernel on the crossings. -/
noncomputable def vbK (q p : Cf eta) : ℂ :=
  if Cross (n : ℝ) q p then potKernel sys L q p else 0

open Classical in
/-- The channel majorant of `σ`. -/
noncomputable def sigMaj (j : Ch eta) (q p : Cf eta) : ℝ :=
  if OnCh j q p then chC sys L j / cgap sys (gF L) * tailFn (3 * n / 4) (q (lead j) - p (lead j))
  else 0

variable {sys L n}

lemma sigMaj_nonneg (hL : 0 < L) (j : Ch eta) (q p : Cf eta) : 0 ≤ sigMaj sys L n j q p := by
  unfold sigMaj
  split_ifs
  · exact mul_nonneg (div_nonneg (chC_nonneg sys hL j) (cgap_pos sys (gF_pos hL).ne').le)
      (tailFn_nonneg _ _)
  · exact le_rfl

lemma exists_onCh_of_ne_zero (hL : 0 < L) {q p : Cf eta} (h : potKernel sys L q p ≠ 0) :
    ∃ j, OnCh j q p := by
  by_contra hno
  push Not at hno
  have : potMaj sys L q p = 0 := by
    unfold potMaj
    refine Finset.sum_eq_zero fun j _ => ?_
    unfold chMaj; rw [if_neg (hno j)]
  have h0 := norm_potKernel_le sys hL q p
  rw [this] at h0
  exact h (norm_le_zero_iff.mp h0)

/-- On a crossing with a nonzero coefficient the mismatch is at least `c_gap (3n/4)²`. -/
lemma gap_of_ne_zero (hL : 0 < L) (hn : 0 < n) {q p : Cf eta} (hc : Cross (n : ℝ) q p)
    (h : potKernel sys L q p ≠ 0) :
    cgap sys (gF L) * (3 * n / 4) ^ 2 ≤ |Ek sys L q - Ek sys L p| := by
  obtain ⟨j, hj⟩ := exists_onCh_of_ne_zero hL h
  obtain ⟨h1, h2⟩ := channel_gap sys (gF_pos hL).ne' (by exact_mod_cast hn) hj hc
  exact le_trans (mul_le_mul_of_nonneg_left h1.le (cgap_pos sys (gF_pos hL).ne').le) h2

/-- **The commutator kernel** `(E(q) - E(p)) σ(q, p) = v_b(q, p)` (`[T, Σ_b] = V_b`). -/
theorem comm_kernel (hL : 0 < L) (hn : 0 < n) (q p : Cf eta) :
    ((Ek sys L q - Ek sys L p : ℝ) : ℂ) * sigK sys L n q p = vbK sys L n q p := by
  unfold sigK vbK
  split_ifs with hc
  · by_cases h0 : potKernel sys L q p = 0
    · rw [h0, zero_div, mul_zero]
    · have hg := gap_of_ne_zero hL hn hc h0
      have hpos : 0 < cgap sys (gF L) * (3 * n / 4) ^ 2 := by
        have := cgap_pos sys (gF_pos hL).ne'
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      have hne : Ek sys L q - Ek sys L p ≠ 0 := abs_pos.mp (hpos.trans_le hg)
      rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hne)]
  · rw [mul_zero]

/-- The channel majorant of `σ`. -/
theorem norm_sigK_le (hL : 0 < L) (hn : 0 < n) (q p : Cf eta) :
    ‖sigK sys L n q p‖ ≤ ∑ j : Ch eta, sigMaj sys L n j q p := by
  have hsum0 : 0 ≤ ∑ j : Ch eta, sigMaj sys L n j q p :=
    Finset.sum_nonneg fun j _ => sigMaj_nonneg hL j q p
  unfold sigK
  split_ifs with hc
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    refine (div_le_div_of_nonneg_right (norm_potKernel_le sys hL q p) (abs_nonneg _)).trans ?_
    unfold potMaj
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    unfold chMaj sigMaj
    split_ifs with hon
    · obtain ⟨h1, h2⟩ := channel_gap sys (gF_pos hL).ne' (by exact_mod_cast hn) hon hc
      set x := q (lead j) - p (lead j)
      have hx : 0 < nsq x := lt_of_le_of_lt (sq_nonneg _) h1
      have hcg := cgap_pos sys (gF_pos hL).ne'
      have hcj := chC_nonneg sys hL j
      have hlat : latticeNormSq x = nsq x := rfl
      rw [hlat]
      unfold tailFn
      rw [if_pos h1]
      calc chC sys L j / nsq x / |Ek sys L q - Ek sys L p|
          ≤ chC sys L j / nsq x / (cgap sys (gF L) * nsq x) :=
            div_le_div_of_nonneg_left (div_nonneg hcj hx.le) (by positivity) h2
        _ = chC sys L j / cgap sys (gF L) * (nsq x)⁻¹ ^ 2 := by
            field_simp
    · simp
  · rw [norm_zero]; exact hsum0

/-! ## Schur's bound -/

omit [Fintype ν] in
/-- Schur's test from a finite family of majorants. -/
lemma schur_of_maj {ι : Type*} {κ : Cf eta → Cf eta → ℂ} {M : ι → Cf eta → Cf eta → ℝ}
    (s : Finset ι) (hle : ∀ q p, ‖κ q p‖ ≤ ∑ j ∈ s, M j q p) (A : ι → ℝ)
    (hrs : ∀ j q, Summable (M j q)) (hrt : ∀ j q, ∑' p, M j q p ≤ A j)
    (hcs : ∀ j p, Summable fun q => M j q p) (hct : ∀ j p, ∑' q, M j q p ≤ A j) :
    SchurBound κ (∑ j ∈ s, A j) (∑ j ∈ s, A j) := by
  have hr : ∀ q, Summable fun p => ∑ j ∈ s, M j q p := fun q => summable_sum fun j _ => hrs j q
  have hc : ∀ p, Summable fun q => ∑ j ∈ s, M j q p := fun p => summable_sum fun j _ => hcs j p
  have hr' : ∀ q, Summable fun p => ‖κ q p‖ := fun q =>
    (hr q).of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => hle q p)
  have hc' : ∀ p, Summable fun q => ‖κ q p‖ := fun p =>
    (hc p).of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hle q p)
  refine ⟨hr', fun q => ?_, hc', fun p => ?_⟩
  · calc ∑' p, ‖κ q p‖ ≤ ∑' p, ∑ j ∈ s, M j q p := (hr' q).tsum_le_tsum (fun p => hle q p) (hr q)
      _ = ∑ j ∈ s, ∑' p, M j q p := Summable.tsum_finsetSum fun j _ => hrs j q
      _ ≤ ∑ j ∈ s, A j := Finset.sum_le_sum fun j _ => hrt j q
  · calc ∑' q, ‖κ q p‖ ≤ ∑' q, ∑ j ∈ s, M j q p := (hc' p).tsum_le_tsum (fun q => hle q p) (hc p)
      _ = ∑ j ∈ s, ∑' q, M j q p := Summable.tsum_finsetSum fun j _ => hcs j p
      _ ≤ ∑ j ∈ s, A j := Finset.sum_le_sum fun j _ => hct j p

/-- The Schur constant `A_σ = Σ_j (c_j/c_gap) · 416/(3n)`. -/
noncomputable def Asig (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  ∑ j : Ch eta, chC sys L j / cgap sys (gF L) * (416 / (3 * n))

lemma Asig_nonneg (hL : 0 < L) : 0 ≤ Asig sys L n := by
  unfold Asig
  refine Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg (chC_nonneg sys hL j)
    (cgap_pos sys (gF_pos hL).ne').le) (by positivity)

lemma tail_bound (hn : 2 ≤ n) :
    Summable (tailFn (3 * n / 4)) ∧ ∑' x, tailFn (3 * n / 4) x ≤ 416 / (3 * n) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : (1 : ℝ) ≤ 3 * n / 4 := by linarith
  obtain ⟨h1, h2⟩ := tailFn_summable_and_le hR
  refine ⟨h1, h2.trans_eq ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma summable_sigMaj_row (hn : 2 ≤ n) (j : Ch eta) (q : Cf eta) :
    Summable fun p => sigMaj sys L n j q p := by
  classical
  have e : (fun p => sigMaj sys L n j q p) = fun p => if OnCh j q p then
      chC sys L j / cgap sys (gF L) * tailFn (3 * n / 4) (q (lead j) - p (lead j)) else 0 := rfl
  rw [e, summable_row_iff]
  simp only [lead_sub_tr]
  exact (tail_bound hn).1.mul_left _

lemma tsum_sigMaj_row (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (q : Cf eta) :
    ∑' p, sigMaj sys L n j q p ≤ chC sys L j / cgap sys (gF L) * (416 / (3 * n)) := by
  classical
  have e : (fun p => sigMaj sys L n j q p) = fun p => if OnCh j q p then
      chC sys L j / cgap sys (gF L) * tailFn (3 * n / 4) (q (lead j) - p (lead j)) else 0 := rfl
  rw [show (∑' p, sigMaj sys L n j q p) = ∑' p, (fun p => sigMaj sys L n j q p) p from rfl, e,
    tsum_row]
  simp only [lead_sub_tr]
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tail_bound hn).2
    (div_nonneg (chC_nonneg sys hL j) (cgap_pos sys (gF_pos hL).ne').le)

lemma summable_sigMaj_col (hn : 2 ≤ n) (j : Ch eta) (p : Cf eta) :
    Summable fun q => sigMaj sys L n j q p := by
  classical
  have e : (fun q => sigMaj sys L n j q p) = fun q => if OnCh j q p then
      chC sys L j / cgap sys (gF L) * tailFn (3 * n / 4) (q (lead j) - p (lead j)) else 0 := rfl
  rw [e, summable_col_iff]
  simp only [lead_add_tr]
  exact (tail_bound hn).1.mul_left _

lemma tsum_sigMaj_col (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (p : Cf eta) :
    ∑' q, sigMaj sys L n j q p ≤ chC sys L j / cgap sys (gF L) * (416 / (3 * n)) := by
  classical
  have e : (fun q => sigMaj sys L n j q p) = fun q => if OnCh j q p then
      chC sys L j / cgap sys (gF L) * tailFn (3 * n / 4) (q (lead j) - p (lead j)) else 0 := rfl
  rw [show (∑' q, sigMaj sys L n j q p) = ∑' q, (fun q => sigMaj sys L n j q p) q from rfl, e,
    tsum_col]
  simp only [lead_add_tr]
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tail_bound hn).2
    (div_nonneg (chC_nonneg sys hL j) (cgap_pos sys (gF_pos hL).ne').le)

/-- **Schur's bound for `Σ_b`.** -/
theorem sigK_schur (hL : 0 < L) (hn : 2 ≤ n) :
    SchurBound (sigK sys L n) (Asig sys L n) (Asig sys L n) :=
  schur_of_maj Finset.univ (fun q p => norm_sigK_le hL (by omega) q p)
    (fun j => chC sys L j / cgap sys (gF L) * (416 / (3 * n)))
    (fun j q => summable_sigMaj_row hn j q) (fun j q => tsum_sigMaj_row hL hn j q)
    (fun j p => summable_sigMaj_col hn j p) (fun j p => tsum_sigMaj_col hL hn j p)

/-! ## Anti-Hermiticity and the unitary `U = e^{Σ_b}` -/

omit [Fintype ν] in
lemma cross_symm_iff (s : ℝ) (q p : Cf eta) : Cross s q p ↔ Cross s p q :=
  ⟨Cross.symm, Cross.symm⟩

/-- The potential kernel is Hermitian (the operator `H` exists for every cell). -/
theorem potKernel_conj' (hL : 0 < L) (q p : Cf eta) :
    potKernel sys L p q = conj (potKernel sys L q p) := by
  obtain ⟨H, hKernel, -⟩ := exists_coulombFourierH2Operator sys L
    molecularCanonicalUnitHardyConstant hL canonicalPeriodicCoulombHardyBound_explicit
  exact potKernel_conj sys L H hKernel hL q p

/-- **`Σ_b† = -Σ_b`** on kernels. -/
theorem sigK_anti (hL : 0 < L) (q p : Cf eta) :
    conj (sigK sys L n p q) = -sigK sys L n q p := by
  unfold sigK
  rw [cross_symm_iff (n : ℝ) p q]
  split_ifs with hc
  · rw [map_div₀, Complex.conj_ofReal, ← potKernel_conj' hL, ← div_neg, ← Complex.ofReal_neg,
      neg_sub]
  · simp

/-- The bulk generator `Σ_b`. -/
noncomputable def Sig (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 2 ≤ n) :
    L2 eta →L[ℂ] L2 eta :=
  (sigK_schur (sys := sys) (L := L) (n := n) hL hn).toCLM

lemma Sig_apply (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) (q : Cf eta) :
    Sig sys L n hL hn x q = ∑' p, sigK sys L n q p * x p := rfl

/-- `‖Σ_b‖ ≤ A_σ`. -/
theorem norm_Sig_le (hL : 0 < L) (hn : 2 ≤ n) : ‖Sig sys L n hL hn‖ ≤ Asig sys L n := by
  refine (sigK_schur (sys := sys) hL hn).norm_toCLM_le.trans (le_of_eq ?_)
  rw [Real.sqrt_mul_self (Asig_nonneg hL)]

/-- **`Σ_b` is skew-adjoint and `U = e^{Σ_b}` is unitary.** -/
theorem Sig_skew_unitary (hL : 0 < L) (hn : 2 ≤ n) :
    Sig sys L n hL hn ∈ skewAdjoint (L2 eta →L[ℂ] L2 eta) ∧
      NormedSpace.exp (Sig sys L n hL hn) ∈ unitary (L2 eta →L[ℂ] L2 eta) :=
  (sigK_schur (sys := sys) hL hn).exp_mem_unitary fun q p => sigK_anti hL q p

/-! ## Hilbert–Schmidt kernels with one end in a finite set -/

omit [Fintype ν] in
/-- A kernel with one end in a finite set, whose rows and columns at that set are
square-summable, is Hilbert–Schmidt. -/
theorem hs_of_finite_end {κ : Cf eta → Cf eta → ℂ} (F : Finset (Cf eta))
    (hsupp : ∀ q p, κ q p ≠ 0 → q ∈ F ∨ p ∈ F)
    (hrow : ∀ q ∈ F, Summable fun p => ‖κ q p‖ ^ 2)
    (hcol : ∀ p ∈ F, Summable fun q => ‖κ q p‖ ^ 2) :
    HSBound κ (∑' x : Cf eta × Cf eta, ‖κ x.1 x.2‖ ^ 2) := by
  classical
  set f₁ : Cf eta × Cf eta → ℝ := fun x => if x.2 ∈ F then ‖κ x.1 x.2‖ ^ 2 else 0
  set f₂ : Cf eta × Cf eta → ℝ := fun x => if x.1 ∈ F then ‖κ x.1 x.2‖ ^ 2 else 0
  have hf₁0 : ∀ x, 0 ≤ f₁ x := fun x => by simp only [f₁]; split_ifs <;> positivity
  have hf₂0 : ∀ x, 0 ≤ f₂ x := fun x => by simp only [f₂]; split_ifs <;> positivity
  have hs₁ : Summable f₁ := by
    refine (summable_prod_of_nonneg hf₁0).2 ⟨fun q => ?_, ?_⟩
    · exact summable_of_ne_finset_zero (s := F) fun p hp => by simp [f₁, hp]
    · have e : (fun q => ∑' p, f₁ (q, p)) = fun q => ∑ p ∈ F, ‖κ q p‖ ^ 2 := by
        funext q
        rw [tsum_eq_sum (s := F) (fun p hp => by simp [f₁, hp])]
        exact Finset.sum_congr rfl fun p hp => by simp [f₁, hp]
      rw [e]
      exact summable_sum fun p hp => hcol p hp
  have hs₂' : Summable fun x : Cf eta × Cf eta => f₂ (x.2, x.1) := by
    refine (summable_prod_of_nonneg fun x => hf₂0 _).2 ⟨fun p => ?_, ?_⟩
    · exact summable_of_ne_finset_zero (s := F) fun q hq => by simp [f₂, hq]
    · have e : (fun p => ∑' q, f₂ (q, p)) = fun p => ∑ q ∈ F, ‖κ q p‖ ^ 2 := by
        funext p
        rw [tsum_eq_sum (s := F) (fun q hq => by simp [f₂, hq])]
        exact Finset.sum_congr rfl fun q hq => by simp [f₂, hq]
      exact e ▸ summable_sum fun q hq => hrow q hq
  have hs₂ : Summable f₂ :=
    ((Equiv.prodComm (Cf eta) (Cf eta)).summable_iff.mpr hs₂').congr fun x => rfl
  have hdom : ∀ x : Cf eta × Cf eta, ‖κ x.1 x.2‖ ^ 2 ≤ f₁ x + f₂ x := by
    intro x
    by_cases h0 : κ x.1 x.2 = 0
    · rw [h0, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact add_nonneg (hf₁0 x) (hf₂0 x)
    · rcases hsupp x.1 x.2 h0 with h | h
      · have : f₂ x = ‖κ x.1 x.2‖ ^ 2 := by simp [f₂, h]
        rw [this]; exact le_add_of_nonneg_left (hf₁0 x)
      · have : f₁ x = ‖κ x.1 x.2‖ ^ 2 := by simp [f₁, h]
        rw [this]; exact le_add_of_nonneg_right (hf₂0 x)
  exact ⟨(hs₁.add hs₂).of_nonneg_of_le (fun _ => sq_nonneg _) hdom, le_rfl⟩

/-- The finite set containing the bulk block. -/
noncomputable abbrev Qf (eta n : ℕ) : Finset (Cf eta) := Qbox eta (n : ℝ)

omit [Fintype ν] in
lemma cross_mem (n : ℕ) {q p : Cf eta} (hc : Cross (n : ℝ) q p) :
    q ∈ Qf eta n ∨ p ∈ Qf eta n := by
  rcases hc with ⟨hq, -⟩ | ⟨-, hp⟩
  · exact Or.inl (mem_Qbox_of_inQ (Nat.cast_nonneg n) hq)
  · exact Or.inr (mem_Qbox_of_inQ (Nat.cast_nonneg n) hp)

/-! ## `V_b` -/

/-- `V_b` is Hilbert–Schmidt. -/
theorem vbK_hs (hL : 0 < L) :
    HSBound (vbK sys L n) (∑' x : Cf eta × Cf eta, ‖vbK sys L n x.1 x.2‖ ^ 2) := by
  classical
  refine hs_of_finite_end (Qf eta n) (fun q p h => ?_) (fun q _ => ?_) (fun p _ => ?_)
  · unfold vbK at h
    split_ifs at h with hc
    · exact cross_mem n hc
    · exact absurd rfl h
  · refine (summable_potKernel_sq_row sys hL q).of_nonneg_of_le (fun _ => sq_nonneg _) fun p => ?_
    unfold vbK; split_ifs <;> simp
  · refine (summable_potKernel_sq_col sys hL p).of_nonneg_of_le (fun _ => sq_nonneg _) fun q => ?_
    unfold vbK; split_ifs <;> simp

/-- The bulk-fed crossings `V_b = RWQ + QWR` as a bounded operator. -/
noncomputable def Vb (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (hL : 0 < L) :
    L2 eta →L[ℂ] L2 eta :=
  (vbK_hs (sys := sys) (L := L) (n := n) hL).toCLM

lemma Vb_apply (hL : 0 < L) (x : L2 eta) (q : Cf eta) :
    Vb sys L n hL x q = ∑' p, vbK sys L n q p * x p := rfl

/-! ## The decoded generator `Σ_D` (`ran Σ_b ⊂ D(T)`) -/

omit [Fintype ν] in
/-- The kinetic energy on the bulk block is at most `E_Q = η g² n²/32`. -/
lemma Ek_le_of_inQ {k : Cf eta} (hk : InQ (n : ℝ) k) :
    Ek sys L k ≤ eta * gF L ^ 2 * n ^ 2 / 32 := by
  unfold Ek E
  have hterm : ∀ c ∈ (Finset.univ : Finset (Fin eta)),
      gF L ^ 2 / (2 * sys.mass c) * nsq (k c) ≤ gF L ^ 2 * n ^ 2 / 32 := by
    intro c _
    have hm := sys.one_le_mass c
    have hk' := hk c
    have hg := sq_nonneg (gF L)
    have h0 := nsq_nonneg (k c)
    calc gF L ^ 2 / (2 * sys.mass c) * nsq (k c) ≤ gF L ^ 2 / 2 * nsq (k c) := by
          gcongr; linarith
      _ ≤ gF L ^ 2 / 2 * ((n : ℝ) / 4) ^ 2 := by gcongr
      _ = gF L ^ 2 * n ^ 2 / 32 := by ring
  calc ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (k c) ≤ ∑ _c : Fin eta, gF L ^ 2 * n ^ 2 / 32 :=
        Finset.sum_le_sum hterm
    _ = eta * gF L ^ 2 * n ^ 2 / 32 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

omit [Fintype ν] in
lemma weight_le_E (k : Cf eta) :
    molecularFourierH2Weight eta (gF L) k ≤ 2 * mtop sys * (1 + Ek sys L k) := by
  unfold molecularFourierH2Weight Ek E
  have hmt := one_le_mtop sys
  have hterm : ∀ c ∈ (Finset.univ : Finset (Fin eta)),
      gF L ^ 2 * latticeNormSq (k c) ≤ 2 * mtop sys * (gF L ^ 2 / (2 * sys.mass c) * nsq (k c)) := by
    intro c _
    have hm := sys.mass_pos c
    have hle := mass_le_mtop sys c
    have h0 : 0 ≤ gF L ^ 2 * nsq (k c) := mul_nonneg (sq_nonneg _) (nsq_nonneg _)
    rw [show latticeNormSq (k c) = nsq (k c) from rfl]
    rw [show 2 * mtop sys * (gF L ^ 2 / (2 * sys.mass c) * nsq (k c)) =
      mtop sys / sys.mass c * (gF L ^ 2 * nsq (k c)) by field_simp]
    have : 1 ≤ mtop sys / sys.mass c := (one_le_div hm).mpr hle
    nlinarith
  have key : ∑ c, gF L ^ 2 * latticeNormSq (k c) ≤
      2 * mtop sys * ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (k c) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm
  have hE0 : 0 ≤ ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (k c) :=
    Finset.sum_nonneg fun c _ => mul_nonneg (by have := sys.mass_pos c; positivity) (nsq_nonneg _)
  have h2 : 0 ≤ 2 * mtop sys * ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (k c) := by positivity
  calc 1 + ∑ c, gF L ^ 2 * latticeNormSq (k c)
      ≤ 1 + 2 * mtop sys * ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (k c) := by linarith
    _ ≤ 2 * mtop sys * (1 + ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (k c)) := by
        rw [mul_add, mul_one]; linarith

/-- The constant of the decoded generator: `w(q) |σ(q, p)| ≤ M_D |w(q, p)|`. -/
noncomputable def MD (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  2 * mtop sys * ((1 + eta * gF L ^ 2 * n ^ 2 / 32) / (cgap sys (gF L) * (3 * n / 4) ^ 2) + 1)

omit [Fintype ν] in
lemma MD_nonneg (hL : 0 < L) : 0 ≤ MD sys L n := by
  have hmt := one_le_mtop sys
  have hcg := cgap_pos sys (gF_pos hL).ne'
  unfold MD; positivity

lemma weight_mul_sigK_le (hL : 0 < L) (hn : 0 < n) (q p : Cf eta) :
    ‖((molecularFourierH2Weight eta (gF L) q : ℝ) : ℂ) * sigK sys L n q p‖ ≤
      MD sys L n * ‖potKernel sys L q p‖ := by
  have hw := molecularFourierH2Weight_pos eta (gF L) q
  have hmt := one_le_mtop sys
  have hcg := cgap_pos sys (gF_pos hL).ne'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw.le]
  unfold sigK
  split_ifs with hc
  · by_cases h0 : potKernel sys L q p = 0
    · rw [h0]; simp
    · have hg := gap_of_ne_zero hL hn hc h0
      set D := |Ek sys L q - Ek sys L p|
      have hD : 0 < D := lt_of_lt_of_le (by positivity) hg
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      -- `E(q) ≤ E_Q + D` at either end of the crossing
      have hEQ : Ek sys L q ≤ eta * gF L ^ 2 * n ^ 2 / 32 + D := by
        rcases hc with ⟨hq, -⟩ | ⟨-, hp⟩
        · have := Ek_le_of_inQ (sys := sys) (L := L) hq
          have : 0 ≤ D := abs_nonneg _
          linarith
        · have := Ek_le_of_inQ (sys := sys) (L := L) hp
          have : Ek sys L q - Ek sys L p ≤ D := le_abs_self _
          linarith
      have hwq := weight_le_E (sys := sys) (L := L) q
      have hEp : 0 ≤ Ek sys L q := E_nonneg (fun c => sys.mass_pos c) q
      set EQ := eta * gF L ^ 2 * n ^ 2 / 32
      have hEQ0 : 0 ≤ EQ := by positivity
      set c0 := cgap sys (gF L) * (3 * n / 4) ^ 2
      have hc0 : 0 < c0 := by positivity
      have hw' : molecularFourierH2Weight eta (gF L) q / D ≤ MD sys L n := by
        rw [div_le_iff₀ hD]
        have h1 : 1 + EQ ≤ (1 + EQ) / c0 * D := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
          nlinarith
        have : MD sys L n * D = 2 * mtop sys * ((1 + EQ) / c0 * D) + 2 * mtop sys * D := by
          unfold MD; ring
        rw [this]
        nlinarith
      calc molecularFourierH2Weight eta (gF L) q * (‖potKernel sys L q p‖ / D)
          = molecularFourierH2Weight eta (gF L) q / D * ‖potKernel sys L q p‖ := by ring
        _ ≤ MD sys L n * ‖potKernel sys L q p‖ :=
            mul_le_mul_of_nonneg_right hw' (norm_nonneg _)
  · simp only [norm_zero, mul_zero]
    exact mul_nonneg (MD_nonneg hL) (norm_nonneg _)

/-- The kernel of `Σ_D = S⁻¹ Σ_b`. -/
noncomputable def sigDK (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (q p : Cf eta) : ℂ :=
  ((molecularFourierH2Weight eta (gF L) q : ℝ) : ℂ) * sigK sys L n q p

theorem sigDK_hs (hL : 0 < L) (hn : 0 < n) :
    HSBound (sigDK sys L n) (∑' x : Cf eta × Cf eta, ‖sigDK sys L n x.1 x.2‖ ^ 2) := by
  classical
  have hdom := weight_mul_sigK_le (sys := sys) hL hn
  refine hs_of_finite_end (Qf eta n) (fun q p h => ?_) (fun q _ => ?_) (fun p _ => ?_)
  · unfold sigDK sigK at h
    split_ifs at h with hc
    · exact cross_mem n hc
    · simp at h
  · refine ((summable_potKernel_sq_row sys hL q).mul_left (MD sys L n ^ 2)).of_nonneg_of_le
      (fun _ => sq_nonneg _) fun p => ?_
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hdom q p) 2
  · refine ((summable_potKernel_sq_col sys hL p).mul_left (MD sys L n ^ 2)).of_nonneg_of_le
      (fun _ => sq_nonneg _) fun q => ?_
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hdom q p) 2

/-- The decoded generator `Σ_D : ℓ² → H²` with `S Σ_D = Σ_b`. -/
noncomputable def SigD (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (hL : 0 < L) (hn : 0 < n) :
    L2 eta →L[ℂ] MolecularFourierH2 eta :=
  (sigDK_hs (sys := sys) (L := L) (n := n) hL hn).toCLM

/-- **`ran Σ_b ⊂ D(T)`**: `S Σ_D = Σ_b`. -/
theorem stateMap_SigD (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) :
    molecularH2StateMap eta (gF L) (SigD sys L n hL (by omega) x) = Sig sys L n hL hn x := by
  ext q
  rw [molecularH2StateMap_apply, Sig_apply]
  unfold molecularH2Coeff SigD
  rw [HSBound.toCLM_apply, kerApply]
  unfold sigDK
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  have hw : ((molecularFourierH2Weight eta (gF L) q : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (molecularFourierH2Weight_pos eta (gF L) q).ne'
  rw [mul_div_cancel_left₀ _ hw]

/-! ## `[T, Σ_b] = V_b` on `D(T)` -/

lemma gF_eq (L : ℝ) : gF L = 2 * Real.pi / L := rfl

omit [Fintype ν] in
lemma kinetic_apply' (u : MolecularFourierH2 eta) (q : Cf eta) :
    coulombFourierKineticH2 sys (gF L) u q =
      ((Ek sys L q : ℝ) : ℂ) * molecularH2StateMap eta (gF L) u q := by
  rw [coulombFourierKineticH2_apply, molecularH2StateMap_apply, Ek, E_eq_kineticSymbol]

/-- **`[T, Σ_b] = V_b` on `D(T)`**: `T Σ_D S u - Σ_b T u = V_b S u` for every `u ∈ H²`. -/
theorem kinetic_comm (hL : 0 < L) (hn : 2 ≤ n) (u : MolecularFourierH2 eta) :
    coulombFourierKineticH2 sys (gF L) (SigD sys L n hL (by omega) (molecularH2StateMap eta (gF L) u)) -
      Sig sys L n hL hn (coulombFourierKineticH2 sys (gF L) u) =
      Vb sys L n hL (molecularH2StateMap eta (gF L) u) := by
  have hn0 : 0 < n := by omega
  have hS := sigK_schur (sys := sys) hL hn
  ext q
  rw [lp.coeFn_sub, Pi.sub_apply, kinetic_apply', stateMap_SigD hL hn, Sig_apply, Sig_apply,
    Vb_apply]
  have h1 : Summable fun p => sigK sys L n q p * molecularH2StateMap eta (gF L) u p :=
    hS.summable_row_apply _ q
  have h2 : Summable fun p => sigK sys L n q p * coulombFourierKineticH2 sys (gF L) u p :=
    hS.summable_row_apply _ q
  rw [← tsum_mul_left, ← (h1.mul_left ((Ek sys L q : ℝ) : ℂ)).tsum_sub h2]
  refine tsum_congr fun p => ?_
  rw [kinetic_apply', ← comm_kernel hL hn0 q p]
  push_cast
  ring

end FSNormal
