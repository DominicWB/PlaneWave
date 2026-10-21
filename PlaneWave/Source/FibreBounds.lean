import PlaneWave.Source.HardyBound

/-!
# Flux/source build, block 3b: the fibre bounds of the bulk generator

`lem:bulk-weighted`, eq:bulk-weighted-op and eq:bulk-weighted-state, for the bulk-fed part
`S = R Σ_b Q`:

* `fibre_gram` (abstract): for a kernel whose two inputs can share an output only when they lie
  on the same fibre, `Σ_q w(q) (Σ_{p∈F} x_p κ(q,p))² ≤ M N Σ_p W_p x_p²`, where `M` bounds the
  weighted column sums and `N` the fibre sums of `1/W`;
* the fibres of a channel (`onCh_trans`), their counts in `Q` (`card_fibre_le`, at most
  `(2⌈n/4⌉+1)³`) and weighted sums (`fibre_weight_le`, `Σ (1 + |p'|²)^{-2s} ≤ Z_{2s}`);
* the columns of `σ` with the weights `1` and `1 + 2E`: `Σ_q |σ(q,p)|² ≤ M₀ ∝ n⁻⁵`,
  `Σ_q (1+2E(q)) |σ(q,p)|² ≤ M₁ ∝ n⁻³` (`col_sig_le`, `col_sig_weighted_le`);
* **`form_sig_Q_le`** (eq:bulk-weighted-op, `‖E^{1/2} S‖ ≤ C`):
  `Σ_q (1+2E(q)) |(Σ_b 1_Q x)(q)|² ≤ C ‖x‖²` with `C` independent of `n`;
* **`norm_sig_Q_state_le`, `form_sig_Q_state_le`** (eq:bulk-weighted-state, `j = 0, 1`):
  `‖Σ_b 1_Q u‖² ≤ C n⁻⁵ Σ_{p∈Q} (1+|p|²)^{2s} |u_p|²` and the same with weight `1 + 2E` and `n⁻³`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics NormedSpace FluxSourceTest

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The abstract fibre Gram bound -/

omit [Fintype ν] in
lemma amgm_weighted {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) :
    x * y ≤ (a * x ^ 2 / b + b * y ^ 2 / a) / 2 := by
  have h : 0 ≤ (a * x - b * y) ^ 2 / (a * b) := by positivity
  have e : (a * x - b * y) ^ 2 / (a * b) = a * x ^ 2 / b + b * y ^ 2 / a - 2 * (x * y) := by
    field_simp; ring
  linarith

omit [Fintype ν] in
/-- **The fibre Gram bound.** Let `κ ≥ 0` be a kernel from the finite set `F` such that two
inputs reach a common output only if they are related, `R` symmetric. If the `w`-weighted
column sums are at most `M` and the `R`-fibre sums of `1/W` at most `N`, then
`Σ_q w(q) (Σ_{p∈F} x_p κ(q,p))² ≤ M N Σ_{p∈F} W_p x_p²`. -/
theorem fibre_gram {ι : Type*} (F : Finset ι) (κ : ι → ι → ℝ) (_hκ : ∀ q p, 0 ≤ κ q p)
    (w : ι → ℝ) (hw : ∀ q, 0 ≤ w q) (R : ι → ι → Prop) [DecidableRel R]
    (hRs : ∀ p p', R p p' → R p' p)
    (hrel : ∀ q, ∀ p ∈ F, ∀ p' ∈ F, κ q p ≠ 0 → κ q p' ≠ 0 → R p p')
    {M : ℝ} (hcs : ∀ p ∈ F, Summable fun q => w q * κ q p ^ 2)
    (hcol : ∀ p ∈ F, ∑' q, w q * κ q p ^ 2 ≤ M)
    (W : ι → ℝ) (hW : ∀ p, 0 < W p) {N : ℝ}
    (hN : ∀ p ∈ F, ∑ p' ∈ F.filter (R p), (W p')⁻¹ ≤ N)
    (x : ι → ℝ) (hx : ∀ p, 0 ≤ x p) :
    (Summable fun q => w q * (∑ p ∈ F, x p * κ q p) ^ 2) ∧
      ∑' q, w q * (∑ p ∈ F, x p * κ q p) ^ 2 ≤ M * N * ∑ p ∈ F, W p * x p ^ 2 := by
  classical
  -- the pointwise majorant
  set T : ι → ℝ := fun q => ∑ p ∈ F, ∑ p' ∈ F, (if R p p' then x p * x p' else 0) *
    ((κ q p ^ 2 + κ q p' ^ 2) / 2) with hT
  have hpt : ∀ q, (∑ p ∈ F, x p * κ q p) ^ 2 ≤ T q := by
    intro q
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun p' hp' => ?_
    by_cases hr : R p p'
    · rw [if_pos hr]
      have := two_mul_le_add_sq (κ q p) (κ q p')
      have hxx : 0 ≤ x p * x p' := mul_nonneg (hx p) (hx p')
      nlinarith
    · rw [if_neg hr, zero_mul]
      by_cases h1 : κ q p = 0
      · rw [h1]; simp
      · by_cases h2 : κ q p' = 0
        · rw [h2]; simp
        · exact absurd (hrel q p hp p' hp' h1 h2) hr
  have hT0 : ∀ q, 0 ≤ T q := fun q => (sq_nonneg _).trans (hpt q)
  -- the majorant is summable, with the column bound
  have hcs' : ∀ p ∈ F, ∀ p' ∈ F, Summable fun q => w q * ((if R p p' then x p * x p' else 0) *
      ((κ q p ^ 2 + κ q p' ^ 2) / 2)) := by
    intro p hp p' hp'
    have := ((hcs p hp).add (hcs p' hp')).mul_left ((if R p p' then x p * x p' else 0) / 2)
    refine this.congr fun q => ?_
    ring
  have hwT : (fun q => w q * T q) = fun q => ∑ p ∈ F, ∑ p' ∈ F, w q *
      ((if R p p' then x p * x p' else 0) * ((κ q p ^ 2 + κ q p' ^ 2) / 2)) := by
    funext q; simp only [hT, Finset.mul_sum]
  have hsT : Summable fun q => w q * T q := by
    rw [hwT]
    exact summable_sum fun p hp => summable_sum fun p' hp' => hcs' p hp p' hp'
  have hsum : Summable fun q => w q * (∑ p ∈ F, x p * κ q p) ^ 2 :=
    hsT.of_nonneg_of_le (fun q => mul_nonneg (hw q) (sq_nonneg _))
      (fun q => mul_le_mul_of_nonneg_left (hpt q) (hw q))
  refine ⟨hsum, ?_⟩
  have h1 : ∑' q, w q * (∑ p ∈ F, x p * κ q p) ^ 2 ≤ ∑' q, w q * T q :=
    hsum.tsum_le_tsum (fun q => mul_le_mul_of_nonneg_left (hpt q) (hw q)) hsT
  have h2 : ∑' q, w q * T q ≤ ∑ p ∈ F, ∑ p' ∈ F, (if R p p' then x p * x p' else 0) * M := by
    rw [hwT, Summable.tsum_finsetSum fun p hp => summable_sum fun p' hp' => hcs' p hp p' hp']
    refine Finset.sum_le_sum fun p hp => ?_
    rw [Summable.tsum_finsetSum fun p' hp' => hcs' p hp p' hp']
    refine Finset.sum_le_sum fun p' hp' => ?_
    have e : (fun q => w q * ((if R p p' then x p * x p' else 0) * ((κ q p ^ 2 + κ q p' ^ 2) / 2))) =
        fun q => (if R p p' then x p * x p' else 0) / 2 * (w q * κ q p ^ 2 + w q * κ q p' ^ 2) := by
      funext q; ring
    rw [e, tsum_mul_left, (hcs p hp).tsum_add (hcs p' hp')]
    have hc0 : 0 ≤ (if R p p' then x p * x p' else 0) := by
      split_ifs
      · exact mul_nonneg (hx p) (hx p')
      · exact le_rfl
    have := add_le_add (hcol p hp) (hcol p' hp')
    calc (if R p p' then x p * x p' else 0) / 2 * (∑' q, w q * κ q p ^ 2 + ∑' q, w q * κ q p' ^ 2)
        ≤ (if R p p' then x p * x p' else 0) / 2 * (M + M) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (if R p p' then x p * x p' else 0) * M := by ring
  -- the fibre sum
  rcases F.eq_empty_or_nonempty with hF | hF
  · subst hF; simp
  have hM : 0 ≤ M := by
    obtain ⟨p, hp⟩ := hF
    exact (tsum_nonneg fun q => mul_nonneg (hw q) (sq_nonneg _)).trans (hcol p hp)
  have h3 : ∑ p ∈ F, ∑ p' ∈ F, (if R p p' then x p * x p' else 0) ≤
      N * ∑ p ∈ F, W p * x p ^ 2 := by
    have hpp : ∀ p ∈ F, ∀ p' ∈ F, (if R p p' then x p * x p' else 0) ≤
        (if R p p' then W p * x p ^ 2 / W p' else 0) / 2 +
          (if R p' p then W p' * x p' ^ 2 / W p else 0) / 2 := by
      intro p _ p' _
      by_cases hr : R p p'
      · simp only [hr, hRs p p' hr, if_true]
        have := amgm_weighted (x := x p) (y := x p') (hW p) (hW p')
        linarith
      · simp only [hr, if_false]
        have : 0 ≤ (if R p' p then W p' * x p' ^ 2 / W p else 0) := by
          split_ifs
          · exact div_nonneg (mul_nonneg (hW p').le (sq_nonneg _)) (hW p).le
          · exact le_rfl
        linarith
    have hswap : ∑ p ∈ F, ∑ p' ∈ F, (if R p' p then W p' * x p' ^ 2 / W p else 0) =
        ∑ p ∈ F, ∑ p' ∈ F, (if R p p' then W p * x p ^ 2 / W p' else 0) := Finset.sum_comm
    have hrow : ∀ p ∈ F, ∑ p' ∈ F, (if R p p' then W p * x p ^ 2 / W p' else 0) ≤
        W p * x p ^ 2 * N := by
      intro p hp
      rw [← Finset.sum_filter]
      calc ∑ p' ∈ F.filter (R p), W p * x p ^ 2 / W p'
          = W p * x p ^ 2 * ∑ p' ∈ F.filter (R p), (W p')⁻¹ := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ ≤ W p * x p ^ 2 * N :=
            mul_le_mul_of_nonneg_left (hN p hp) (mul_nonneg (hW p).le (sq_nonneg _))
    calc ∑ p ∈ F, ∑ p' ∈ F, (if R p p' then x p * x p' else 0)
        ≤ ∑ p ∈ F, ∑ p' ∈ F, ((if R p p' then W p * x p ^ 2 / W p' else 0) / 2 +
            (if R p' p then W p' * x p' ^ 2 / W p else 0) / 2) :=
          Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun p' hp' => hpp p hp p' hp'
      _ = ∑ p ∈ F, ∑ p' ∈ F, (if R p p' then W p * x p ^ 2 / W p' else 0) := by
          simp only [Finset.sum_add_distrib, ← Finset.sum_div, hswap]; ring
      _ ≤ ∑ p ∈ F, W p * x p ^ 2 * N := Finset.sum_le_sum hrow
      _ = N * ∑ p ∈ F, W p * x p ^ 2 := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  calc ∑' q, w q * (∑ p ∈ F, x p * κ q p) ^ 2 ≤ ∑' q, w q * T q := h1
    _ ≤ ∑ p ∈ F, ∑ p' ∈ F, (if R p p' then x p * x p' else 0) * M := h2
    _ = M * ∑ p ∈ F, ∑ p' ∈ F, (if R p p' then x p * x p' else 0) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ M * (N * ∑ p ∈ F, W p * x p ^ 2) := mul_le_mul_of_nonneg_left h3 hM
    _ = M * N * ∑ p ∈ F, W p * x p ^ 2 := by ring

end FSNormal

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Fibres of a channel -/

lemma tr_sub (j : Ch eta) (a b : Lattice3) : tr j (a - b) = tr j a - tr j b := by
  cases j with
  | inl c => simp only [tr, Pi.single_sub]
  | inr pr => simp only [tr, Pi.single_sub]; abel

/-- Two inputs reaching a common output on channel `j` lie on the same fibre. -/
lemma onCh_trans {j : Ch eta} {q p p' : Cf eta} (h1 : OnCh j q p) (h2 : OnCh j q p') :
    OnCh j p' p := by
  have e1 : q = p + tr j (q (lead j) - p (lead j)) := h1
  have e2 : q = p' + tr j (q (lead j) - p' (lead j)) := h2
  generalize q (lead j) - p (lead j) = ν₁ at e1
  generalize q (lead j) - p' (lead j) = ν₂ at e2
  apply onCh_of_eq (ν := ν₁ - ν₂)
  rw [tr_sub]
  have : p' = q - tr j ν₂ := by rw [e2]; abel
  rw [this, e1]; abel

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ}

open Classical in
/-- The channel-`j` part of `|σ|`. -/
noncomputable def kapJ (j : Ch eta) (q p : Cf eta) : ℝ :=
  if OnCh j q p then ‖sigK sys L n q p‖ else 0

lemma kapJ_nonneg (j : Ch eta) (q p : Cf eta) : 0 ≤ kapJ sys (L := L) (n := n) j q p := by
  unfold kapJ; split_ifs <;> positivity

lemma kapJ_le (j : Ch eta) (q p : Cf eta) :
    kapJ sys (L := L) (n := n) j q p ≤ ‖sigK sys L n q p‖ := by
  unfold kapJ; split_ifs <;> simp

include hL in
lemma norm_sigK_le_kapJ (q p : Cf eta) :
    ‖sigK sys L n q p‖ ≤ ∑ j : Ch eta, kapJ sys (L := L) (n := n) j q p := by
  classical
  by_cases h0 : sigK sys L n q p = 0
  · rw [h0, norm_zero]; exact Finset.sum_nonneg fun j _ => kapJ_nonneg sys j q p
  · have hpot : potKernel sys L q p ≠ 0 := by
      intro hp; apply h0; unfold sigK; split_ifs <;> simp [hp]
    obtain ⟨j, hj⟩ := exists_onCh_of_ne_zero hL hpot
    calc ‖sigK sys L n q p‖ = kapJ sys (L := L) (n := n) j q p := by unfold kapJ; rw [if_pos hj]
      _ ≤ ∑ j' : Ch eta, kapJ sys (L := L) (n := n) j' q p :=
        Finset.single_le_sum (f := fun j' => kapJ sys (L := L) (n := n) j' q p)
          (fun j' _ => kapJ_nonneg sys j' q p) (Finset.mem_univ j)

/-! ## Weighted columns of `σ` -/

omit [Fintype ν] in
lemma nsq_add_le (x y : L3) : nsq (x + y) ≤ 2 * nsq x + 2 * nsq y := by
  unfold nsq; push_cast [Pi.add_apply]
  nlinarith [sq_nonneg ((x 0 : ℝ) - y 0), sq_nonneg ((x 1 : ℝ) - y 1), sq_nonneg ((x 2 : ℝ) - y 2)]

omit [Fintype ν] in
lemma E_add_le (m : Fin eta → ℝ) (hm : ∀ c, 0 < m c) (g : ℝ) (p k : Cf eta) :
    E m g (p + k) ≤ 2 * E m g p + 2 * E m g k := by
  unfold E
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  have h := nsq_add_le (p c) (k c)
  have hc : 0 ≤ g ^ 2 / (2 * m c) := by have := hm c; positivity
  rw [Pi.add_apply]
  nlinarith

omit [Fintype ν] in
lemma E_tr_le (j : Ch eta) (x : Lattice3) :
    E sys.mass (gF L) (tr j x) ≤ gF L ^ 2 * nsq x := by
  classical
  have hterm : ∀ c, gF L ^ 2 / (2 * sys.mass c) * nsq (tr j x c) ≤ gF L ^ 2 / 2 * nsq (tr j x c) := by
    intro c
    have := sys.one_le_mass c
    gcongr
    · exact nsq_nonneg _
    · linarith
  have hsum : ∑ c, nsq (tr j x c) ≤ 2 * nsq x := by
    cases j with
    | inl a =>
      rw [Finset.sum_eq_single a]
      · simp only [tr, Pi.single_eq_same]; linarith [nsq_nonneg x]
      · intro c _ hc; simp only [tr, Pi.single_eq_of_ne hc]; simp [nsq]
      · intro h; exact absurd (Finset.mem_univ a) h
    | inr pr =>
      have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ pr.1.1),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ pr.1.2⟩)]
      have hz : ∑ c ∈ (Finset.univ.erase pr.1.1).erase pr.1.2, nsq (tr (.inr pr) x c) = 0 := by
        refine Finset.sum_eq_zero fun c hc => ?_
        have h1 : c ≠ pr.1.2 := (Finset.mem_erase.mp hc).1
        have h2 : c ≠ pr.1.1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
        simp only [tr, Pi.sub_apply, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, sub_zero]
        simp [nsq]
      rw [hz, add_zero]
      simp only [tr, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne,
        Pi.single_eq_of_ne hne.symm, sub_zero, zero_sub, nsq_neg]
      linarith
  unfold E
  calc ∑ c, gF L ^ 2 / (2 * sys.mass c) * nsq (tr j x c) ≤ ∑ c, gF L ^ 2 / 2 * nsq (tr j x c) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = gF L ^ 2 / 2 * ∑ c, nsq (tr j x c) := by rw [Finset.mul_sum]
    _ ≤ gF L ^ 2 / 2 * (2 * nsq x) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = gF L ^ 2 * nsq x := by ring

/-- The weight constant `c₁ = 1 + (η + 4) g²`: `1 + 2E(p + τ_j(ν)) ≤ c₁ |ν|²` for `p ∈ Q` and
`|ν| > 3n/4`. -/
noncomputable def c1E (eta : ℕ) (L : ℝ) : ℝ := 1 + (eta + 4) * gF L ^ 2

omit [Fintype ν] in
lemma weight_tr_le {p : Cf eta} (hp : InQ (n : ℝ) p) (j : Ch eta) {x : Lattice3}
    (hx : (3 * n / 4 : ℝ) ^ 2 < nsq x) :
    1 + 2 * Ek sys L (p + tr j x) ≤ c1E eta L * nsq x := by
  have h1 := E_add_le sys.mass (fun c => sys.mass_pos c) (gF L) p (tr j x)
  have h2 := E_tr_le sys (L := L) j x
  have h3 := Ek_le_of_inQ (sys := sys) (L := L) hp
  have hx1 : (1 : ℝ) ≤ nsq x := by
    by_contra h
    push Not at h
    have h0 : x ≠ 0 := by
      intro h0; subst h0; simp [nsq] at hx; nlinarith
    exact absurd (one_le_latticeNormSq h0) (by rw [show latticeNormSq x = nsq x from rfl]; linarith)
  have hn2 : (n : ℝ) ^ 2 ≤ 16 / 9 * nsq x := by nlinarith
  have hg : 0 ≤ gF L ^ 2 := sq_nonneg _
  have heta : (0 : ℝ) ≤ eta := Nat.cast_nonneg _
  unfold c1E
  rw [Ek] at *
  have : eta * gF L ^ 2 * n ^ 2 / 32 ≤ eta * gF L ^ 2 * nsq x / 18 := by
    have := mul_le_mul_of_nonneg_left hn2 (mul_nonneg heta hg)
    nlinarith
  nlinarith


/-! ## The columns of `σ` -/

/-- `Σ_j (c_j/c_gap)²`. -/
noncomputable def cSig2 (sys : CoulombSystem eta ν) (L : ℝ) : ℝ :=
  ∑ j : Ch eta, (chC sys L j / cgap sys (gF L)) ^ 2

/-- The unweighted column constant `M₀ = #Ch · cSig2 · (3n/4)⁻⁴ · 416/(3n)`. -/
noncomputable def M0 (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Fintype.card (Ch eta) * cSig2 sys L * ((3 * n / 4 : ℝ) ^ 2)⁻¹ ^ 2 * (416 / (3 * n))

/-- The weighted column constant `M₁ = #Ch · cSig2 · c₁ · (3n/4)⁻² · 416/(3n)`. -/
noncomputable def M1 (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Fintype.card (Ch eta) * cSig2 sys L * c1E eta L * ((3 * n / 4 : ℝ) ^ 2)⁻¹ * (416 / (3 * n))

omit [Fintype ν] in
lemma tailFn_sq_le {R : ℝ} (hR : 0 < R) (x : L3) : tailFn R x ^ 2 ≤ (R ^ 2)⁻¹ ^ 2 * tailFn R x := by
  unfold tailFn
  split_ifs with h
  · have hx : 0 < nsq x := lt_trans (by positivity) h
    have h1 : (nsq x)⁻¹ ≤ (R ^ 2)⁻¹ := inv_anti₀ (by positivity) h.le
    have h2 : (nsq x)⁻¹ ^ 2 ≤ (R ^ 2)⁻¹ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : 0 ≤ (nsq x)⁻¹ ^ 2 := by positivity
    nlinarith
  · simp

omit [Fintype ν] in
lemma nsq_mul_tailFn_sq_le {R : ℝ} (hR : 0 < R) (x : L3) :
    nsq x * tailFn R x ^ 2 ≤ (R ^ 2)⁻¹ * tailFn R x := by
  unfold tailFn
  split_ifs with h
  · have hx : 0 < nsq x := lt_trans (by positivity) h
    have h1 : (nsq x)⁻¹ ≤ (R ^ 2)⁻¹ := inv_anti₀ (by positivity) h.le
    have e : nsq x * ((nsq x)⁻¹ ^ 2) ^ 2 = (nsq x)⁻¹ * (nsq x)⁻¹ ^ 2 := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · simp

include hL in
lemma sq_norm_sigK_le (hn : 0 < n) (q p : Cf eta) :
    ‖sigK sys L n q p‖ ^ 2 ≤ Fintype.card (Ch eta) * ∑ j : Ch eta, sigMaj sys L n j q p ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sigK_le hL hn q p) 2).trans sq_sum_le_card_mul_sum_sq

include hL in
/-- `Σ_q |σ(q, p)|² ≤ M₀` (`∝ n⁻⁵`). -/
theorem col_sig_le (hn : 2 ≤ n) (p : Cf eta) :
    (Summable fun q => ‖sigK sys L n q p‖ ^ 2) ∧ ∑' q, ‖sigK sys L n q p‖ ^ 2 ≤ M0 sys L n := by
  classical
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hR : (0 : ℝ) < 3 * n / 4 := by positivity
  set R := (3 * n / 4 : ℝ)
  have hcj : ∀ j, 0 ≤ chC sys L j / cgap sys (gF L) := fun j =>
    div_nonneg (chC_nonneg sys hL j) (cgap_pos sys (gF_pos hL).ne').le
  -- the majorant columns
  have hmaj : ∀ j, (Summable fun q => sigMaj sys L n j q p ^ 2) ∧
      ∑' q, sigMaj sys L n j q p ^ 2 ≤
        (chC sys L j / cgap sys (gF L)) ^ 2 * ((R ^ 2)⁻¹ ^ 2 * (416 / (3 * n))) := by
    intro j
    have e : (fun q => sigMaj sys L n j q p ^ 2) = fun q => if OnCh j q p then
        (chC sys L j / cgap sys (gF L)) ^ 2 * tailFn R (q (lead j) - p (lead j)) ^ 2 else 0 := by
      funext q; unfold sigMaj; split_ifs <;> ring
    have hb : ∀ x, (chC sys L j / cgap sys (gF L)) ^ 2 * tailFn R x ^ 2 ≤
        (chC sys L j / cgap sys (gF L)) ^ 2 * ((R ^ 2)⁻¹ ^ 2 * tailFn R x) := fun x =>
      mul_le_mul_of_nonneg_left (tailFn_sq_le hR x) (sq_nonneg _)
    have hs : Summable fun x => (chC sys L j / cgap sys (gF L)) ^ 2 * tailFn R x ^ 2 :=
      (((tail_bound hn).1.mul_left ((R ^ 2)⁻¹ ^ 2)).mul_left _).of_nonneg_of_le
        (fun x => by positivity) hb
    refine ⟨?_, ?_⟩
    · rw [e, summable_col_iff]; simpa only [lead_add_tr] using hs
    · rw [e, tsum_col]
      simp only [lead_add_tr]
      calc ∑' x, (chC sys L j / cgap sys (gF L)) ^ 2 * tailFn R x ^ 2
          ≤ ∑' x, (chC sys L j / cgap sys (gF L)) ^ 2 * ((R ^ 2)⁻¹ ^ 2 * tailFn R x) :=
            hs.tsum_le_tsum hb (((tail_bound hn).1.mul_left _).mul_left _)
        _ = (chC sys L j / cgap sys (gF L)) ^ 2 * ((R ^ 2)⁻¹ ^ 2 * ∑' x, tailFn R x) := by
            rw [tsum_mul_left, tsum_mul_left]
        _ ≤ _ := by
            gcongr
            exact (tail_bound hn).2
  have hs : Summable fun q => (Fintype.card (Ch eta) : ℝ) * ∑ j : Ch eta, sigMaj sys L n j q p ^ 2 :=
    (summable_sum fun j _ => (hmaj j).1).mul_left _
  have hle := fun q => sq_norm_sigK_le sys hL (L := L) (n := n) hn0 q p
  refine ⟨hs.of_nonneg_of_le (fun _ => sq_nonneg _) hle, ?_⟩
  calc ∑' q, ‖sigK sys L n q p‖ ^ 2 ≤ ∑' q, (Fintype.card (Ch eta) : ℝ) *
        ∑ j : Ch eta, sigMaj sys L n j q p ^ 2 :=
        (hs.of_nonneg_of_le (fun _ => sq_nonneg _) hle).tsum_le_tsum hle hs
    _ = Fintype.card (Ch eta) * ∑ j : Ch eta, ∑' q, sigMaj sys L n j q p ^ 2 := by
        rw [tsum_mul_left, Summable.tsum_finsetSum fun j _ => (hmaj j).1]
    _ ≤ Fintype.card (Ch eta) * ∑ j : Ch eta,
          (chC sys L j / cgap sys (gF L)) ^ 2 * ((R ^ 2)⁻¹ ^ 2 * (416 / (3 * n))) := by
        gcongr with j
        exact (hmaj j).2
    _ = M0 sys L n := by
        unfold M0 cSig2
        rw [← Finset.sum_mul]; ring

include hL in
/-- `Σ_q (1 + 2E(q)) |σ(q, p)|² ≤ M₁` (`∝ n⁻³`) for `p ∈ Q`. -/
theorem col_sig_weighted_le (hn : 2 ≤ n) {p : Cf eta} (hp : InQ (n : ℝ) p) :
    (Summable fun q => (1 + 2 * Ek sys L q) * ‖sigK sys L n q p‖ ^ 2) ∧
      ∑' q, (1 + 2 * Ek sys L q) * ‖sigK sys L n q p‖ ^ 2 ≤ M1 sys L n := by
  classical
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hR : (0 : ℝ) < 3 * n / 4 := by positivity
  set R := (3 * n / 4 : ℝ)
  have hc1 : 0 ≤ c1E eta L := by unfold c1E; positivity
  have hw0 : ∀ q, 0 ≤ 1 + 2 * Ek sys L q := fun q => by
    linarith [one_le_one_add_two_Ek sys L q]
  have hmaj : ∀ j, (Summable fun q => (1 + 2 * Ek sys L q) * sigMaj sys L n j q p ^ 2) ∧
      ∑' q, (1 + 2 * Ek sys L q) * sigMaj sys L n j q p ^ 2 ≤
        (chC sys L j / cgap sys (gF L)) ^ 2 * (c1E eta L * ((R ^ 2)⁻¹ * (416 / (3 * n)))) := by
    intro j
    have e : (fun q => (1 + 2 * Ek sys L q) * sigMaj sys L n j q p ^ 2) = fun q => if OnCh j q p then
        (chC sys L j / cgap sys (gF L)) ^ 2 *
          ((1 + 2 * Ek sys L q) * tailFn R (q (lead j) - p (lead j)) ^ 2) else 0 := by
      funext q; unfold sigMaj; split_ifs <;> ring
    have hb : ∀ x, (chC sys L j / cgap sys (gF L)) ^ 2 *
        ((1 + 2 * Ek sys L (p + tr j x)) * tailFn R x ^ 2) ≤
        (chC sys L j / cgap sys (gF L)) ^ 2 * (c1E eta L * ((R ^ 2)⁻¹ * tailFn R x)) := by
      intro x
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      by_cases hx : R ^ 2 < nsq x
      · have h1 := weight_tr_le sys (L := L) hp j hx
        have h2 := nsq_mul_tailFn_sq_le hR x
        calc (1 + 2 * Ek sys L (p + tr j x)) * tailFn R x ^ 2 ≤ c1E eta L * nsq x * tailFn R x ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
          _ = c1E eta L * (nsq x * tailFn R x ^ 2) := by ring
          _ ≤ c1E eta L * ((R ^ 2)⁻¹ * tailFn R x) := mul_le_mul_of_nonneg_left h2 hc1
      · have : tailFn R x = 0 := by unfold tailFn; rw [if_neg hx]
        rw [this]; simp
    have hs0 : Summable fun x => (chC sys L j / cgap sys (gF L)) ^ 2 *
        (c1E eta L * ((R ^ 2)⁻¹ * tailFn R x)) :=
      (((tail_bound hn).1.mul_left _).mul_left _).mul_left _
    have hs : Summable fun x => (chC sys L j / cgap sys (gF L)) ^ 2 *
        ((1 + 2 * Ek sys L (p + tr j x)) * tailFn R x ^ 2) :=
      hs0.of_nonneg_of_le (fun x => mul_nonneg (sq_nonneg _) (mul_nonneg (hw0 _) (sq_nonneg _))) hb
    refine ⟨?_, ?_⟩
    · rw [e, summable_col_iff]; simpa only [lead_add_tr] using hs
    · rw [e, tsum_col]
      simp only [lead_add_tr]
      calc ∑' x, (chC sys L j / cgap sys (gF L)) ^ 2 *
            ((1 + 2 * Ek sys L (p + tr j x)) * tailFn R x ^ 2)
          ≤ ∑' x, (chC sys L j / cgap sys (gF L)) ^ 2 * (c1E eta L * ((R ^ 2)⁻¹ * tailFn R x)) :=
            hs.tsum_le_tsum hb hs0
        _ = (chC sys L j / cgap sys (gF L)) ^ 2 * (c1E eta L * ((R ^ 2)⁻¹ * ∑' x, tailFn R x)) := by
            rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]
        _ ≤ _ := by
            gcongr
            exact (tail_bound hn).2
  have hs : Summable fun q => (Fintype.card (Ch eta) : ℝ) *
      ∑ j : Ch eta, (1 + 2 * Ek sys L q) * sigMaj sys L n j q p ^ 2 :=
    (summable_sum fun j _ => (hmaj j).1).mul_left _
  have hle : ∀ q, (1 + 2 * Ek sys L q) * ‖sigK sys L n q p‖ ^ 2 ≤ (Fintype.card (Ch eta) : ℝ) *
      ∑ j : Ch eta, (1 + 2 * Ek sys L q) * sigMaj sys L n j q p ^ 2 := by
    intro q
    calc (1 + 2 * Ek sys L q) * ‖sigK sys L n q p‖ ^ 2 ≤ (1 + 2 * Ek sys L q) *
          (Fintype.card (Ch eta) * ∑ j : Ch eta, sigMaj sys L n j q p ^ 2) :=
          mul_le_mul_of_nonneg_left (sq_norm_sigK_le sys hL hn0 q p) (hw0 q)
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; ring_nf
  refine ⟨hs.of_nonneg_of_le (fun q => mul_nonneg (hw0 q) (sq_nonneg _)) hle, ?_⟩
  calc ∑' q, (1 + 2 * Ek sys L q) * ‖sigK sys L n q p‖ ^ 2 ≤ ∑' q, (Fintype.card (Ch eta) : ℝ) *
        ∑ j : Ch eta, (1 + 2 * Ek sys L q) * sigMaj sys L n j q p ^ 2 :=
        (hs.of_nonneg_of_le (fun q => mul_nonneg (hw0 q) (sq_nonneg _)) hle).tsum_le_tsum hle hs
    _ = Fintype.card (Ch eta) * ∑ j : Ch eta, ∑' q, (1 + 2 * Ek sys L q) * sigMaj sys L n j q p ^ 2 := by
        rw [tsum_mul_left, Summable.tsum_finsetSum fun j _ => (hmaj j).1]
    _ ≤ Fintype.card (Ch eta) * ∑ j : Ch eta,
          (chC sys L j / cgap sys (gF L)) ^ 2 * (c1E eta L * ((R ^ 2)⁻¹ * (416 / (3 * n)))) := by
        gcongr with j
        exact (hmaj j).2
    _ = M1 sys L n := by
        unfold M1 cSig2
        rw [← Finset.sum_mul]; ring


/-! ## Fibres in the bulk block -/

omit [Fintype ν] in
lemma lead_inj_on_fibre {j : Ch eta} {p p₁ p₂ : Cf eta} (h1 : OnCh j p₁ p) (h2 : OnCh j p₂ p)
    (h : p₁ (lead j) = p₂ (lead j)) : p₁ = p₂ := by
  have e1 : p₁ = p + tr j (p₁ (lead j) - p (lead j)) := h1
  have e2 : p₂ = p + tr j (p₂ (lead j) - p (lead j)) := h2
  calc p₁ = p + tr j (p₁ (lead j) - p (lead j)) := e1
    _ = p + tr j (p₂ (lead j) - p (lead j)) := by rw [h]
    _ = p₂ := e2.symm

open Classical in
omit [Fintype ν] in
/-- A fibre of a channel meets `Q` in at most `(2⌈n/4⌉ + 1)³` configurations. -/
lemma card_fibre_le (n : ℕ) (j : Ch eta) (p : Cf eta) :
    ((((Qs eta n).filter fun p' => OnCh j p' p).card : ℕ) : ℝ) ≤
      (2 * ⌈(n : ℝ) / 4⌉₊ + 1 : ℝ) ^ 3 := by
  classical
  have hinj : Set.InjOn (fun p' : Cf eta => p' (lead j))
      ((Qs eta n).filter fun p' => OnCh j p' p) := by
    intro a ha b hb hab
    exact lead_inj_on_fibre (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  have hmaps : ∀ p' ∈ (Qs eta n).filter (fun p' => OnCh j p' p),
      p' (lead j) ∈ box ⌈(n : ℝ) / 4⌉₊ := by
    intro p' hp'
    have hQ := mem_Qs.mp (Finset.mem_filter.mp hp').1
    have := mem_Qbox_of_inQ (Nat.cast_nonneg (n : ℕ)) hQ
    exact Fintype.mem_piFinset.mp this (lead j)
  have h := Finset.card_le_card_of_injOn _ (fun a ha => hmaps a ha) hinj
  rw [card_box] at h
  exact_mod_cast h

/-- The lattice `H¹` norm `|p|² = Σ_c |p_c|²` of a configuration. -/
noncomputable def lsqC (p : Cf eta) : ℝ := ∑ c, nsq (p c)

omit [Fintype ν] in
lemma lsqC_nonneg (p : Cf eta) : 0 ≤ lsqC p := Finset.sum_nonneg fun _ _ => nsq_nonneg _

open Classical in
omit [Fintype ν] in
/-- The fibre sums of the weight `(1 + |p|²)^{-2s}` are at most `Z_{2s}` for `s > 3/4`. -/
lemma fibre_weight_le (n : ℕ) (j : Ch eta) (p : Cf eta) {s : ℝ} (hs : 3 / 4 < s) :
    ∑ p' ∈ (Qs eta n).filter (fun p' => OnCh j p' p), ((1 + lsqC p') ^ (2 * s))⁻¹ ≤
      1 + 26 * (1 + 1 / (2 * (2 * s) - 3)) := by
  classical
  have hinj : Set.InjOn (fun p' : Cf eta => p' (lead j))
      ((Qs eta n).filter fun p' => OnCh j p' p) := by
    intro a ha b hb hab
    exact lead_inj_on_fibre (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
  have hterm : ∀ p' ∈ (Qs eta n).filter (fun p' => OnCh j p' p),
      ((1 + lsqC p') ^ (2 * s))⁻¹ ≤ (1 + FSLattice.lsq (p' (lead j))) ^ (-(2 * s)) := by
    intro p' _
    rw [Real.rpow_neg (by linarith [FSLattice.lsq_nonneg (p' (lead j))])]
    refine inv_anti₀ (Real.rpow_pos_of_pos (by linarith [FSLattice.lsq_nonneg (p' (lead j))]) _)
      (Real.rpow_le_rpow (by linarith [FSLattice.lsq_nonneg (p' (lead j))]) ?_ (by linarith))
    have : FSLattice.lsq (p' (lead j)) ≤ lsqC p' := by
      unfold lsqC
      exact Finset.single_le_sum (f := fun c => nsq (p' c)) (fun _ _ => nsq_nonneg _)
        (Finset.mem_univ (lead j))
    linarith
  calc ∑ p' ∈ (Qs eta n).filter (fun p' => OnCh j p' p), ((1 + lsqC p') ^ (2 * s))⁻¹
      ≤ ∑ p' ∈ (Qs eta n).filter (fun p' => OnCh j p' p),
          (1 + FSLattice.lsq (p' (lead j))) ^ (-(2 * s)) := Finset.sum_le_sum hterm
    _ = ∑ μ ∈ ((Qs eta n).filter (fun p' => OnCh j p' p)).image (fun p' => p' (lead j)),
          (1 + FSLattice.lsq μ) ^ (-(2 * s)) :=
        (Finset.sum_image (f := fun μ => (1 + FSLattice.lsq μ) ^ (-(2 * s))) hinj).symm
    _ ≤ _ := FSLattice.sum_weight_le (by linarith) _

/-! ## The Gram bounds for `Σ_b 1_Q` -/

open Classical in
lemma Sig_truncQ_apply (hn : 2 ≤ n) (x : L2 eta) (q : Cf eta) :
    Sig sys L n hL hn (lpTruncate (Qs eta n) x) q = ∑ p ∈ Qs eta n, sigK sys L n q p * x p := by
  rw [Sig_apply, tsum_eq_sum (s := Qs eta n)]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [lpTruncate_apply, if_pos hp]
  · intro p hp
    rw [lpTruncate_apply, if_neg hp, mul_zero]

open Classical in
include hL in
/-- **The Gram bound for `Σ_b 1_Q`**, for an output weight `w`, a column bound `M` and fibre
sums `N` of `1/W`. -/
theorem gram_sig_Q (hn : 2 ≤ n) {w : Cf eta → ℝ} (hw : ∀ q, 0 ≤ w q) {M : ℝ}
    (hcs : ∀ p ∈ Qs eta n, Summable fun q => w q * ‖sigK sys L n q p‖ ^ 2)
    (hcol : ∀ p ∈ Qs eta n, ∑' q, w q * ‖sigK sys L n q p‖ ^ 2 ≤ M)
    (W : Cf eta → ℝ) (hW : ∀ p, 0 < W p) {N : ℝ}
    (hN : ∀ j, ∀ p ∈ Qs eta n,
      ∑ p' ∈ (Qs eta n).filter (fun p' => OnCh j p' p), (W p')⁻¹ ≤ N)
    (x : L2 eta) :
    (Summable fun q => w q * ‖Sig sys L n hL hn (lpTruncate (Qs eta n) x) q‖ ^ 2) ∧
      ∑' q, w q * ‖Sig sys L n hL hn (lpTruncate (Qs eta n) x) q‖ ^ 2 ≤
        Fintype.card (Ch eta) ^ 2 * M * N * ∑ p ∈ Qs eta n, W p * ‖x p‖ ^ 2 := by
  classical
  set F := Qs eta n
  set G : Ch eta → Cf eta → ℝ := fun j q => ∑ p ∈ F, ‖x p‖ * kapJ sys (L := L) (n := n) j q p
  -- the per-channel Gram bounds
  have hj : ∀ j : Ch eta, (Summable fun q => w q * G j q ^ 2) ∧
      ∑' q, w q * G j q ^ 2 ≤ M * N * ∑ p ∈ F, W p * ‖x p‖ ^ 2 := by
    intro j
    refine fibre_gram F (kapJ sys (L := L) (n := n) j) (fun q p => kapJ_nonneg sys j q p) w hw
      (fun p p' => OnCh j p' p) (fun p p' h => onCh_symm h) ?_ (fun p hp => ?_) (fun p hp => ?_)
      W hW (fun p hp => hN j p hp) (fun p => ‖x p‖) (fun p => norm_nonneg _)
    · intro q p _ p' _ h1 h2
      have o1 : OnCh j q p := by by_contra h; exact h1 (by unfold kapJ; rw [if_neg h])
      have o2 : OnCh j q p' := by by_contra h; exact h2 (by unfold kapJ; rw [if_neg h])
      exact onCh_trans o1 o2
    · refine (hcs p hp).of_nonneg_of_le (fun q => mul_nonneg (hw q) (sq_nonneg _)) fun q => ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (kapJ_nonneg sys j q p)
        (kapJ_le sys j q p) 2) (hw q)
    · refine le_trans ?_ (hcol p hp)
      refine ((hcs p hp).of_nonneg_of_le (fun q => mul_nonneg (hw q) (sq_nonneg _)) fun q => ?_)
        |>.tsum_le_tsum (fun q => ?_) (hcs p hp)
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (kapJ_nonneg sys j q p)
          (kapJ_le sys j q p) 2) (hw q)
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (kapJ_nonneg sys j q p)
          (kapJ_le sys j q p) 2) (hw q)
  -- pointwise
  have hpt : ∀ q, w q * ‖Sig sys L n hL hn (lpTruncate F x) q‖ ^ 2 ≤
      Fintype.card (Ch eta) * ∑ j : Ch eta, w q * G j q ^ 2 := by
    intro q
    rw [Sig_truncQ_apply sys hL hn x q]
    have h1 : ‖∑ p ∈ F, sigK sys L n q p * x p‖ ≤ ∑ j : Ch eta, G j q := by
      refine (norm_sum_le _ _).trans ?_
      simp only [G]
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun p _ => ?_
      rw [norm_mul, ← Finset.mul_sum, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_sigK_le_kapJ sys hL q p) (norm_nonneg _)
    have h2 : (∑ j : Ch eta, G j q) ^ 2 ≤ Fintype.card (Ch eta) * ∑ j : Ch eta, G j q ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h0 : 0 ≤ ∑ j : Ch eta, G j q :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun p _ =>
        mul_nonneg (norm_nonneg _) (kapJ_nonneg sys j q p)
    calc w q * ‖∑ p ∈ F, sigK sys L n q p * x p‖ ^ 2 ≤ w q * (∑ j : Ch eta, G j q) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (hw q)
      _ ≤ w q * (Fintype.card (Ch eta) * ∑ j : Ch eta, G j q ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (hw q)
      _ = Fintype.card (Ch eta) * ∑ j : Ch eta, w q * G j q ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hs : Summable fun q => (Fintype.card (Ch eta) : ℝ) * ∑ j : Ch eta, w q * G j q ^ 2 :=
    (summable_sum fun j _ => (hj j).1).mul_left _
  have hs' := hs.of_nonneg_of_le (fun q => mul_nonneg (hw q) (sq_nonneg _)) hpt
  refine ⟨hs', ?_⟩
  calc ∑' q, w q * ‖Sig sys L n hL hn (lpTruncate F x) q‖ ^ 2
      ≤ ∑' q, (Fintype.card (Ch eta) : ℝ) * ∑ j : Ch eta, w q * G j q ^ 2 :=
        hs'.tsum_le_tsum hpt hs
    _ = Fintype.card (Ch eta) * ∑ j : Ch eta, ∑' q, w q * G j q ^ 2 := by
        rw [tsum_mul_left, Summable.tsum_finsetSum fun j _ => (hj j).1]
    _ ≤ Fintype.card (Ch eta) * ∑ _j : Ch eta, M * N * ∑ p ∈ F, W p * ‖x p‖ ^ 2 := by
        gcongr with j
        exact (hj j).2
    _ = Fintype.card (Ch eta) ^ 2 * M * N * ∑ p ∈ F, W p * ‖x p‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

omit [Fintype ν] in
lemma sum_Qs_sq_le (n : ℕ) (x : L2 eta) : ∑ p ∈ Qs eta n, ‖x p‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [← tsum_sq_coord x]
  exact (summable_sq_coord x).sum_le_tsum _ fun _ _ => sq_nonneg _

include hL in
/-- **eq:bulk-weighted-op** (`‖E^{1/2} S‖ ≤ C`): `Σ_q (1+2E(q)) |(Σ_b 1_Q x)(q)|² ≤ C_op ‖x‖²`,
`C_op = #Ch² M₁ (2⌈n/4⌉+1)³`, bounded uniformly in `n`. -/
theorem form_sig_Q_le (hn : 2 ≤ n) (x : L2 eta) :
    (Summable fun q => (1 + 2 * Ek sys L q) *
        ‖Sig sys L n hL hn (lpTruncate (Qs eta n) x) q‖ ^ 2) ∧
      ∑' q, (1 + 2 * Ek sys L q) * ‖Sig sys L n hL hn (lpTruncate (Qs eta n) x) q‖ ^ 2 ≤
        Fintype.card (Ch eta) ^ 2 * M1 sys L n * (2 * ⌈(n : ℝ) / 4⌉₊ + 1 : ℝ) ^ 3 * ‖x‖ ^ 2 := by
  classical
  have hw : ∀ q, 0 ≤ 1 + 2 * Ek sys L q := fun q => by linarith [one_le_one_add_two_Ek sys L q]
  obtain ⟨h1, h2⟩ := gram_sig_Q sys hL hn hw
    (fun p hp => (col_sig_weighted_le sys hL hn (mem_Qs.mp hp)).1)
    (fun p hp => (col_sig_weighted_le sys hL hn (mem_Qs.mp hp)).2)
    (fun _ => 1) (fun _ => one_pos)
    (fun j p _ => by
      simp only [inv_one, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact card_fibre_le n j p) x
  refine ⟨h1, h2.trans ?_⟩
  simp only [one_mul]
  have hM : 0 ≤ Fintype.card (Ch eta) ^ 2 * M1 sys L n * (2 * ⌈(n : ℝ) / 4⌉₊ + 1 : ℝ) ^ 3 := by
    have : 0 ≤ M1 sys L n := by
      unfold M1 cSig2 c1E
      have : 0 ≤ ∑ j : Ch eta, (chC sys L j / cgap sys (gF L)) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      positivity
    positivity
  exact mul_le_mul_of_nonneg_left (sum_Qs_sq_le n x) hM

/-- The state weight `(1 + |p|²)^{2s}`. -/
noncomputable def Ws (s : ℝ) (p : Cf eta) : ℝ := (1 + lsqC p) ^ (2 * s)

omit [Fintype ν] in
lemma Ws_pos (s : ℝ) (p : Cf eta) : 0 < Ws s p :=
  Real.rpow_pos_of_pos (by linarith [lsqC_nonneg p]) _

include hL in
/-- **eq:bulk-weighted-state, `j = 0`**: `‖Σ_b 1_Q u‖² ≤ #Ch² M₀ Z_{2s} Σ_{p∈Q} (1+|p|²)^{2s} |u_p|²`
(`M₀ ∝ n⁻⁵`, so `‖S u‖ ≤ C K^{-5/2} ‖E^s u‖`). -/
theorem norm_sig_Q_state_le (hn : 2 ≤ n) {s : ℝ} (hs : 3 / 4 < s) (u : L2 eta) :
    ∑' q, ‖Sig sys L n hL hn (lpTruncate (Qs eta n) u) q‖ ^ 2 ≤
      Fintype.card (Ch eta) ^ 2 * M0 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3))) *
        ∑ p ∈ Qs eta n, Ws s p * ‖u p‖ ^ 2 := by
  have h := (gram_sig_Q sys hL hn (w := fun _ => 1) (fun _ => zero_le_one)
    (fun p _ => by simpa only [one_mul] using (col_sig_le sys hL hn p).1)
    (fun p _ => by simpa only [one_mul] using (col_sig_le sys hL hn p).2)
    (Ws s) (Ws_pos s) (fun j p _ => fibre_weight_le n j p hs) u).2
  simpa only [one_mul] using h

include hL in
/-- **eq:bulk-weighted-state, `j = 1`**: the same with the output weight `1 + 2E` and `M₁ ∝ n⁻³`
(`‖E^{1/2} S u‖ ≤ C K^{-3/2} ‖E^s u‖`). -/
theorem form_sig_Q_state_le (hn : 2 ≤ n) {s : ℝ} (hs : 3 / 4 < s) (u : L2 eta) :
    (Summable fun q => (1 + 2 * Ek sys L q) *
        ‖Sig sys L n hL hn (lpTruncate (Qs eta n) u) q‖ ^ 2) ∧
      ∑' q, (1 + 2 * Ek sys L q) * ‖Sig sys L n hL hn (lpTruncate (Qs eta n) u) q‖ ^ 2 ≤
        Fintype.card (Ch eta) ^ 2 * M1 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3))) *
          ∑ p ∈ Qs eta n, Ws s p * ‖u p‖ ^ 2 := by
  have hw : ∀ q, 0 ≤ 1 + 2 * Ek sys L q := fun q => by linarith [one_le_one_add_two_Ek sys L q]
  exact gram_sig_Q sys hL hn hw
    (fun p hp => (col_sig_weighted_le sys hL hn (mem_Qs.mp hp)).1)
    (fun p hp => (col_sig_weighted_le sys hL hn (mem_Qs.mp hp)).2)
    (Ws s) (Ws_pos s) (fun j p _ => fibre_weight_le n j p hs) u

end FSNormal
