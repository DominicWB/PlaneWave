import PlaneWave.Source.TruncatedObservable
import PlaneWave.Source.KernelOperators

/-!
# Flux/source build, block 5: the bulk block `H₂^bb` (`lem:h2`)

`H₂^bb = ½ P[Σ_b, V_b]P` on `E_n`, through its kernel on the full lattice,

  `h(k, k') = ½ (Σ_r σ(k, r) v_b(r, k') - Σ_r v_b(k, r) σ(r, k'))`.

* `same_channel` (`lem:h2`, the structure claim): if `k, k' ∈ Q`, `r ∉ P`, `r` is one hop of
  channel `j'` from `k'` and `k` one hop of channel `j` from `r`, then `j = j'`. The proof
  compares the sets of moved registers: the escaped register forces both transfers to exceed
  `3s/4`, so every register moved by either hop has momentum above `s/2` in between and must be
  restored by the other hop.
* `norm_hbK_le` (`lem:h2`, the kernel bound): for `k, k' ∈ Q`,
  `|h(k, k')| ≤ Σ_j 1{k on channel j from k'} c_j²/c_gap · 611·64/(27 n³)`, by the same-channel
  structure and the flat sum `Σ_{|μ| > 3n/4} |μ|⁻⁴ |θ - μ|⁻² ≤ 611 (4/(3n))³`.
* `Hbb_eq_kop`: the operator `½ ext ∘ [Σ_b, V_b] ∘ emb` is the kernel operator of `h ∘ idx`;
  `hbK_conj` (Hermitian kernel), `hbK_eq_zero_of_not_inQ` (support in `Q × Q`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Moved registers -/

/-- The registers moved by a hop of channel `j`. -/
def moved : Ch eta → Finset (Fin eta)
  | .inl a => {a}
  | .inr pr => {pr.1.1, pr.1.2}

lemma tr_apply_not_moved (j : Ch eta) (x : Lattice3) {c : Fin eta} (hc : c ∉ moved j) :
    tr j x c = 0 := by
  cases j with
  | inl a =>
    simp only [moved, Finset.mem_singleton] at hc
    simp [tr, Pi.single_eq_of_ne hc]
  | inr pr =>
    simp only [moved, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    simp [tr, Pi.single_eq_of_ne hc.1, Pi.single_eq_of_ne hc.2]

lemma tr_apply_moved (j : Ch eta) (x : Lattice3) {c : Fin eta} (hc : c ∈ moved j) :
    tr j x c = x ∨ tr j x c = -x := by
  cases j with
  | inl a =>
    simp only [moved, Finset.mem_singleton] at hc
    subst hc
    left; simp [tr]
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    simp only [moved, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · left; simp [tr, Pi.single_eq_of_ne hne]
    · right; simp [tr, Pi.single_eq_of_ne hne.symm]

lemma moved_inj {j j' : Ch eta} (h : moved j = moved j') : j = j' := by
  cases j with
  | inl a =>
    cases j' with
    | inl a' =>
      simp only [moved, Finset.singleton_inj] at h
      rw [h]
    | inr pr =>
      exfalso
      have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
      have h1 : pr.1.1 ∈ moved (.inl a : Ch eta) := by rw [h]; simp [moved]
      have h2 : pr.1.2 ∈ moved (.inl a : Ch eta) := by rw [h]; simp [moved]
      simp only [moved, Finset.mem_singleton] at h1 h2
      exact hne (h1.trans h2.symm)
  | inr pr =>
    cases j' with
    | inl a' =>
      exfalso
      have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
      have h1 : pr.1.1 ∈ moved (.inl a' : Ch eta) := by rw [← h]; simp [moved]
      have h2 : pr.1.2 ∈ moved (.inl a' : Ch eta) := by rw [← h]; simp [moved]
      simp only [moved, Finset.mem_singleton] at h1 h2
      exact hne (h1.trans h2.symm)
    | inr pr' =>
      have hlt := pr.2
      have hlt' := pr'.2
      have h1 : pr.1.1 ∈ moved (.inr pr' : Ch eta) := by rw [← h]; simp [moved]
      have h2 : pr.1.2 ∈ moved (.inr pr' : Ch eta) := by rw [← h]; simp [moved]
      have h3 : pr'.1.1 ∈ moved (.inr pr : Ch eta) := by rw [h]; simp [moved]
      have h4 : pr'.1.2 ∈ moved (.inr pr : Ch eta) := by rw [h]; simp [moved]
      simp only [moved, Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3 h4
      rw [Fin.lt_def] at hlt hlt'
      simp only [Fin.ext_iff] at h1 h2 h3 h4
      have e1 : pr.1.1 = pr'.1.1 := Fin.ext (by omega)
      have e2 : pr.1.2 = pr'.1.2 := Fin.ext (by omega)
      congr 1
      exact Subtype.ext (Prod.ext e1 e2)

/-! ## The same-channel lemma -/

open FSChannel in
lemma abs_coord_le_rho (x : Lattice3) (i : Fin 3) : |((x i : ℤ) : ℝ)| ≤ rho x := by
  unfold rho
  exact Real.abs_le_sqrt (FSLattice.sq_le_lsq x i)

open FSChannel in
lemma rho_le_of_inQ {s : ℝ} (hs : 0 ≤ s) {k : Cf eta} (hk : InQ s k) (c : Fin eta) :
    rho (k c) ≤ s / 4 := by
  unfold rho
  rw [Real.sqrt_le_left (by positivity)]
  exact hk c

open FSChannel in
lemma rho_neg' (x : Lattice3) : rho (-x) = rho x := by
  unfold rho
  congr 1
  simp [FSLattice.lsq]

open FSChannel in
/-- `|z| ≤ |y| + |x|` when `y = x ± z`. -/
lemma rho_le_of_pm {x y z : Lattice3} (h : y = x + z ∨ y = x + -z) : rho z ≤ rho y + rho x := by
  rcases h with h | h
  · have := rho_add_le y (-x)
    rw [rho_neg'] at this
    have e : y + -x = z := by rw [h]; abel
    rwa [e] at this
  · have := rho_add_le x (-y)
    rw [rho_neg'] at this
    have e : x + -y = z := by rw [h]; abel
    rw [e] at this
    linarith

lemma abs_coord_le_of_pm {x y z : Lattice3} (h : y = x + z ∨ y = x + -z) (i : Fin 3) :
    |((y i : ℤ) : ℝ)| - |((x i : ℤ) : ℝ)| ≤ |((z i : ℤ) : ℝ)| := by
  rcases h with h | h
  · have e : ((y i : ℤ) : ℝ) = (x i : ℝ) + (z i : ℝ) := by rw [h, Pi.add_apply]; push_cast; ring
    rw [e]
    have := abs_add_le (x i : ℝ) (z i : ℝ)
    linarith
  · have e : ((y i : ℤ) : ℝ) = (x i : ℝ) - (z i : ℝ) := by
      rw [h, Pi.add_apply, Pi.neg_apply]; push_cast; ring
    rw [e]
    have := abs_sub (x i : ℝ) (z i : ℝ)
    linarith

/-- The moved coordinates of a hop. -/
lemma hop_apply {j : Ch eta} {q p : Cf eta} (h : OnCh j q p) (c : Fin eta) :
    (c ∉ moved j → q c = p c) ∧
      (c ∈ moved j → q c = p c + (q (lead j) - p (lead j)) ∨
        q c = p c + -(q (lead j) - p (lead j))) := by
  have hq : q c = p c + tr j (q (lead j) - p (lead j)) c := by
    have := congrFun h c
    rwa [Pi.add_apply] at this
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [hq, tr_apply_not_moved j _ hc, add_zero]
  · rcases tr_apply_moved j (q (lead j) - p (lead j)) hc with h1 | h1
    · left; rw [hq, h1]
    · right; rw [hq, h1]

/-- The moved coordinates of a hop with transfer `z`. -/
lemma hop_apply' {j : Ch eta} {q p : Cf eta} {z : Lattice3} (h : q = p + tr j z) (c : Fin eta) :
    (c ∉ moved j → q c = p c) ∧ (c ∈ moved j → q c = p c + z ∨ q c = p c + -z) := by
  have hq : q c = p c + tr j z c := by
    have := congrFun h c
    rwa [Pi.add_apply] at this
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rw [hq, tr_apply_not_moved j _ hc, add_zero]
  · rcases tr_apply_moved j z hc with h1 | h1
    · left; rw [hq, h1]
    · right; rw [hq, h1]

open FSChannel in
/-- **The same-channel lemma** (`lem:h2`): a bulk-to-bulk excursion `k' → r → k` with
`k, k' ∈ Q` and `r ∉ P` uses one channel twice. -/
theorem same_channel {s : ℝ} (hs : 0 < s) {k k' r : Cf eta} (hk : InQ s k) (hk' : InQ s k')
    (hr : ¬ InP s r) {j j' : Ch eta} (h1 : OnCh j k r) (h2 : OnCh j' r k') : j = j' := by
  set z := k (lead j) - r (lead j)
  set z' := r (lead j') - k' (lead j')
  have e1 : k = r + tr j z := h1
  have e2 : r = k' + tr j' z' := h2
  -- the escaped coordinate
  simp only [InP, not_forall, not_le] at hr
  obtain ⟨c, i, hci⟩ := hr
  have hk'c : |((k' c i : ℤ) : ℝ)| ≤ s / 4 :=
    (abs_coord_le_rho (k' c) i).trans (rho_le_of_inQ hs.le hk' c)
  have hkc : |((k c i : ℤ) : ℝ)| ≤ s / 4 :=
    (abs_coord_le_rho (k c) i).trans (rho_le_of_inQ hs.le hk c)
  have hcj' : c ∈ moved j' := by
    by_contra hc
    have := (hop_apply' e2 c).1 hc
    rw [this] at hci
    linarith
  have hcj : c ∈ moved j := by
    by_contra hc
    have := (hop_apply' e1 c).1 hc
    rw [this] at hkc
    linarith
  have hz' : 3 * s / 4 < rho z' := by
    have h := abs_coord_le_of_pm ((hop_apply' e2 c).2 hcj') i
    have := abs_coord_le_rho z' i
    linarith
  have hz : 3 * s / 4 < rho z := by
    have h' : |((r c i : ℤ) : ℝ)| - |((k c i : ℤ) : ℝ)| ≤ |((z i : ℤ) : ℝ)| := by
      rcases (hop_apply' e1 c).2 hcj with e | e
      · have e' : r c = k c + -z := by rw [e]; abel
        exact abs_coord_le_of_pm (Or.inr e') i
      · have e' : r c = k c + z := by rw [e]; abel
        exact abs_coord_le_of_pm (Or.inl e') i
    have := abs_coord_le_rho z i
    linarith
  -- every register moved by `j'` has momentum above `s/2` in `r`
  have hsub1 : moved j' ⊆ moved j := by
    intro c' hc'
    by_contra hc
    have hrk : rho z' ≤ rho (r c') + rho (k' c') := rho_le_of_pm ((hop_apply' e2 c').2 hc')
    have := (hop_apply' e1 c').1 hc
    have hkc' := rho_le_of_inQ hs.le hk c'
    have hk'c' := rho_le_of_inQ hs.le hk' c'
    rw [← this] at hrk
    linarith
  have hsub2 : moved j ⊆ moved j' := by
    intro c' hc'
    by_contra hc
    have hrk : rho z ≤ rho (k c') + rho (r c') := rho_le_of_pm ((hop_apply' e1 c').2 hc')
    have := (hop_apply' e2 c').1 hc
    have hkc' := rho_le_of_inQ hs.le hk c'
    have hk'c' := rho_le_of_inQ hs.le hk' c'
    rw [this] at hrk
    linarith
  exact moved_inj (Finset.Subset.antisymm hsub2 hsub1)

/-! ## The kernel of `H₂^bb` -/

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

/-- The kernel of `H₂^bb = ½ P[Σ_b, V_b]P` on the full lattice. -/
noncomputable def hbK (k k' : Cf eta) : ℂ :=
  (1 / 2 : ℂ) * ((∑' r, sigK sys L n k r * vbK sys L n r k') -
    ∑' r, vbK sys L n k r * sigK sys L n r k')

/-- The total potential coefficient `Σ_j c_j`. -/
noncomputable def Cpot (sys : CoulombSystem eta ν) (L : ℝ) : ℝ := ∑ j : Ch eta, chC sys L j

variable {sys L n}

lemma Cpot_nonneg (hL : 0 < L) : 0 ≤ Cpot sys L :=
  Finset.sum_nonneg fun j _ => chC_nonneg sys hL j

omit [Fintype ν] in
lemma chMaj_le (j : Ch eta) {c : ℝ} (hc : 0 ≤ c) (q p : Cf eta) : chMaj j c q p ≤ c := by
  unfold chMaj
  split_ifs with h
  · by_cases h0 : q (lead j) - p (lead j) = 0
    · rw [h0, show latticeNormSq (0 : Lattice3) = 0 by simp [latticeNormSq], div_zero]; exact hc
    · exact div_le_self hc (one_le_latticeNormSq h0)
  · exact hc

lemma norm_vbK_le (hL : 0 < L) (q p : Cf eta) : ‖vbK sys L n q p‖ ≤ Cpot sys L := by
  unfold vbK
  split_ifs
  · refine (norm_potKernel_le sys hL q p).trans ?_
    unfold potMaj Cpot
    exact Finset.sum_le_sum fun j _ => chMaj_le j (chC_nonneg sys hL j) q p
  · rw [norm_zero]; exact Cpot_nonneg hL

lemma summable_sigK_vbK (hL : 0 < L) (hn : 2 ≤ n) (k k' : Cf eta) :
    Summable fun r => sigK sys L n k r * vbK sys L n r k' := by
  refine Summable.of_norm_bounded (((sigK_schur (sys := sys) hL hn).row_summable k).mul_right (Cpot sys L))
    fun r => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_vbK_le hL r k') (norm_nonneg _)

lemma summable_vbK_sigK (hL : 0 < L) (hn : 2 ≤ n) (k k' : Cf eta) :
    Summable fun r => vbK sys L n k r * sigK sys L n r k' := by
  refine Summable.of_norm_bounded (((sigK_schur (sys := sys) hL hn).col_summable k').mul_left (Cpot sys L))
    fun r => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_vbK_le hL k r) (norm_nonneg _)

lemma vbK_eq_zero_of_inP (hk : InP (n : ℝ) k) (hk' : InP (n : ℝ) k') : vbK sys L n k k' = 0 := by
  unfold vbK
  rw [if_neg]
  rintro (⟨-, h⟩ | ⟨h, -⟩)
  · exact h hk'
  · exact h hk

lemma sigK_eq_zero_of_not_cross {k k' : Cf eta} (h : ¬ Cross (n : ℝ) k k') :
    sigK sys L n k k' = 0 := by
  unfold sigK; rw [if_neg h]

lemma vbK_eq_zero_of_not_cross {k k' : Cf eta} (h : ¬ Cross (n : ℝ) k k') :
    vbK sys L n k k' = 0 := by
  unfold vbK; rw [if_neg h]

omit [Fintype ν] in
/-- Inside `P`, a crossing needs both ends in `Q`... more precisely: an end in `P \ Q` has no
crossing partner. -/
lemma not_cross_of_inP_not_inQ {k k' : Cf eta} (hk : InP (n : ℝ) k) (hkq : ¬ InQ (n : ℝ) k) :
    ¬ Cross (n : ℝ) k k' ∧ ¬ Cross (n : ℝ) k' k := by
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hkq h
    · exact h hk
  · rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact h hk
    · exact hkq h

/-- `H₂^bb` vanishes off `Q × Q` (inside `P`). -/
theorem hbK_eq_zero_of_not_inQ {k k' : Cf eta} (hk : InP (n : ℝ) k) (hk' : InP (n : ℝ) k')
    (h : ¬ (InQ (n : ℝ) k ∧ InQ (n : ℝ) k')) : hbK sys L n k k' = 0 := by
  unfold hbK
  rw [not_and_or] at h
  rcases h with h | h
  · have e1 : ∀ r, sigK sys L n k r * vbK sys L n r k' = 0 := fun r => by
      rw [sigK_eq_zero_of_not_cross (not_cross_of_inP_not_inQ (k' := r) hk h).1, zero_mul]
    have e2 : ∀ r, vbK sys L n k r * sigK sys L n r k' = 0 := fun r => by
      rw [vbK_eq_zero_of_not_cross (not_cross_of_inP_not_inQ (k' := r) hk h).1, zero_mul]
    simp [e1, e2]
  · have e1 : ∀ r, sigK sys L n k r * vbK sys L n r k' = 0 := fun r => by
      rw [vbK_eq_zero_of_not_cross (not_cross_of_inP_not_inQ (k' := r) hk' h).2, mul_zero]
    have e2 : ∀ r, vbK sys L n k r * sigK sys L n r k' = 0 := fun r => by
      rw [sigK_eq_zero_of_not_cross (not_cross_of_inP_not_inQ (k' := r) hk' h).2, mul_zero]
    simp [e1, e2]

/-- **The kernel is Hermitian**: `h(k', k) = conj h(k, k')`. -/
theorem hbK_conj (hL : 0 < L) (k k' : Cf eta) :
    hbK sys L n k' k = conj (hbK sys L n k k') := by
  have hv : ∀ q p, conj (vbK sys L n q p) = vbK sys L n p q := by
    intro q p
    unfold vbK
    rw [cross_symm_iff (n : ℝ) p q]
    split_ifs
    · rw [potKernel_conj' (sys := sys) hL p q, Complex.conj_conj]
    · simp
  have hs' : ∀ q p, conj (sigK sys L n q p) = -sigK sys L n p q := fun q p =>
    sigK_anti (sys := sys) (n := n) hL p q
  unfold hbK
  rw [map_mul, map_sub, Complex.conj_tsum, Complex.conj_tsum]
  simp only [map_mul, map_div₀, map_one, map_ofNat]
  have e1 : ∀ r, conj (sigK sys L n k r) * conj (vbK sys L n r k') =
      -(vbK sys L n k' r * sigK sys L n r k) := by
    intro r; rw [hs', hv]; ring
  have e2 : ∀ r, conj (vbK sys L n k r) * conj (sigK sys L n r k') =
      -(sigK sys L n k' r * vbK sys L n r k) := by
    intro r; rw [hs', hv]; ring
  simp only [e1, e2, tsum_neg]
  ring

/-! ## The kernel bound -/

omit [Fintype ν] in
lemma tr_add (j : Ch eta) (a b : Lattice3) : tr j (a + b) = tr j a + tr j b := by
  cases j with
  | inl c => simp only [tr, Pi.single_add]
  | inr pr => simp only [tr, Pi.single_add]; abel

omit [Fintype ν] in
/-- Two hops of one channel compose to a hop of that channel. -/
lemma onCh_comp {j : Ch eta} {k r k' : Cf eta} (h1 : OnCh j k r) (h2 : OnCh j r k') :
    OnCh j k k' := by
  apply onCh_of_eq (ν := (k (lead j) - r (lead j)) + (r (lead j) - k' (lead j)))
  rw [tr_add, show k' + (tr j (k (lead j) - r (lead j)) + tr j (r (lead j) - k' (lead j))) =
    (k' + tr j (r (lead j) - k' (lead j))) + tr j (k (lead j) - r (lead j)) by abel, ← h2]
  exact h1

omit [Fintype ν] in
lemma tailFn_mul_eq (R : ℝ) (μ : Lattice3) (y : ℝ) :
    tailFn R μ * y = if R ^ 2 < FSLattice.lsq μ then 1 / FSLattice.lsq μ ^ 2 * y else 0 := by
  have hl : nsq μ = FSLattice.lsq μ := rfl
  unfold tailFn
  rw [hl]
  split_ifs
  · rw [inv_pow, one_div]
  · rw [zero_mul]

omit [Fintype ν] in
lemma latticeNormSq_eq_lsq (x : Lattice3) : latticeNormSq x = FSLattice.lsq x := rfl

omit [Fintype ν] in
/-- The flat sum as a lattice series, input form:
`Σ_ν t_R(θ - ν) |ν|⁻² ≤ 611/R³` (`t_R(x) = 1{|x| > R}|x|⁻⁴`). -/
lemma flat_tsum_in_le (θ : Lattice3) {R : ℝ} (hR : 1 ≤ R) :
    ∑' x : Lattice3, tailFn R (θ - x) * (1 / latticeNormSq x) ≤ 611 / R ^ 3 := by
  refine Real.tsum_le_of_sum_le (fun x => mul_nonneg (tailFn_nonneg _ _)
    (by have := latticeNormSq_nonneg x; positivity)) fun S => ?_
  have hinj : Set.InjOn (fun x : Lattice3 => θ - x) S := fun a _ b _ h => sub_right_injective h
  have e : ∑ x ∈ S, tailFn R (θ - x) * (1 / latticeNormSq x) =
      ∑ μ ∈ S.image (fun x => θ - x), tailFn R μ * (1 / FSLattice.lsq (θ - μ)) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [sub_sub_cancel]; rfl
  rw [e]
  have e2 : ∑ μ ∈ S.image (fun x => θ - x), tailFn R μ * (1 / FSLattice.lsq (θ - μ)) =
      ∑ μ ∈ (S.image (fun x => θ - x)).filter (fun μ => R ^ 2 < FSLattice.lsq μ),
        1 / FSLattice.lsq μ ^ 2 * (1 / FSLattice.lsq (θ - μ)) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun μ _ => tailFn_mul_eq R μ _
  rw [e2]
  exact FSLattice.flat_sum_le _ θ hR

omit [Fintype ν] in
/-- The flat sum, output form: `Σ_ν t_R(ν) |θ - ν|⁻² ≤ 611/R³`. -/
lemma flat_tsum_out_le (θ : Lattice3) {R : ℝ} (hR : 1 ≤ R) :
    ∑' x : Lattice3, tailFn R x * (1 / latticeNormSq (θ - x)) ≤ 611 / R ^ 3 := by
  refine Real.tsum_le_of_sum_le (fun x => mul_nonneg (tailFn_nonneg _ _)
    (by have := latticeNormSq_nonneg (θ - x); positivity)) fun S => ?_
  have e2 : ∑ x ∈ S, tailFn R x * (1 / latticeNormSq (θ - x)) =
      ∑ μ ∈ S.filter (fun μ => R ^ 2 < FSLattice.lsq μ),
        1 / FSLattice.lsq μ ^ 2 * (1 / FSLattice.lsq (θ - μ)) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun μ _ => tailFn_mul_eq R μ _
  rw [e2]
  exact FSLattice.flat_sum_le _ θ hR

/-- The kernel constant of channel `j`: `c_j²/c_gap · 611 · 64/27`. -/
noncomputable def chb (sys : CoulombSystem eta ν) (L : ℝ) (j : Ch eta) : ℝ :=
  chC sys L j ^ 2 / cgap sys (gF L) * (611 * 64 / 27)

lemma chb_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ chb sys L j := by
  unfold chb
  have := cgap_pos sys (gF_pos hL).ne'
  positivity

lemma three_n_four_ge (hn : 2 ≤ n) : (1 : ℝ) ≤ 3 * n / 4 := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma flat_const_eq (hn : 2 ≤ n) (c : ℝ) :
    c * (611 / (3 * (n : ℝ) / 4) ^ 3) = c * (611 * 64 / 27) / (n : ℝ) ^ 3 := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < n := by linarith
  field_simp
  ring

/-- The first excursion order, pointwise: only the diagonal channel pairs survive. -/
lemma norm_sigK_vbK_le (hL : 0 < L) (hn : 2 ≤ n) {k k' : Cf eta} (hk : InQ (n : ℝ) k)
    (hk' : InQ (n : ℝ) k') (r : Cf eta) :
    ‖sigK sys L n k r‖ * ‖vbK sys L n r k'‖ ≤
      ∑ j, sigMaj sys L n j k r * chMaj j (chC sys L j) r k' := by
  have hsum0 : 0 ≤ ∑ j, sigMaj sys L n j k r * chMaj j (chC sys L j) r k' :=
    Finset.sum_nonneg fun j _ => mul_nonneg (sigMaj_nonneg hL j k r)
      (chMaj_nonneg j (chC_nonneg sys hL j) r k')
  by_cases hs0 : sigK sys L n k r = 0
  · rw [hs0, norm_zero, zero_mul]; exact hsum0
  by_cases hv0 : vbK sys L n r k' = 0
  · rw [hv0, norm_zero, mul_zero]; exact hsum0
  have hcross : Cross (n : ℝ) k r := by
    by_contra h; exact hs0 (sigK_eq_zero_of_not_cross h)
  have hr : ¬ InP (n : ℝ) r := not_inP_of_cross_inQ hcross hk
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 := norm_sigK_le (sys := sys) (n := n) hL (by omega) k r
  have h2 : ‖vbK sys L n r k'‖ ≤ ∑ j, chMaj j (chC sys L j) r k' := by
    unfold vbK
    split_ifs
    · exact norm_potKernel_le sys hL r k'
    · rw [norm_zero]
      exact Finset.sum_nonneg fun j _ => chMaj_nonneg j (chC_nonneg sys hL j) r k'
  calc ‖sigK sys L n k r‖ * ‖vbK sys L n r k'‖
      ≤ (∑ j, sigMaj sys L n j k r) * ∑ j, chMaj j (chC sys L j) r k' :=
        mul_le_mul h1 h2 (norm_nonneg _) (Finset.sum_nonneg fun j _ => sigMaj_nonneg hL j k r)
    _ = ∑ j, ∑ j', sigMaj sys L n j k r * chMaj j' (chC sys L j') r k' := Finset.sum_mul_sum _ _ _ _
    _ = ∑ j, sigMaj sys L n j k r * chMaj j (chC sys L j) r k' := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_eq_single j (fun j' _ hj' => ?_) (by simp)
        by_cases ha : OnCh j k r
        · by_cases hb : OnCh j' r k'
          · exact absurd (same_channel hn0 hk hk' hr ha hb).symm hj'
          · unfold chMaj; rw [if_neg hb, mul_zero]
        · unfold sigMaj; rw [if_neg ha, zero_mul]

/-- The second excursion order, pointwise. -/
lemma norm_vbK_sigK_le (hL : 0 < L) (hn : 2 ≤ n) {k k' : Cf eta} (hk : InQ (n : ℝ) k)
    (hk' : InQ (n : ℝ) k') (r : Cf eta) :
    ‖vbK sys L n k r‖ * ‖sigK sys L n r k'‖ ≤
      ∑ j, chMaj j (chC sys L j) k r * sigMaj sys L n j r k' := by
  have hsum0 : 0 ≤ ∑ j, chMaj j (chC sys L j) k r * sigMaj sys L n j r k' :=
    Finset.sum_nonneg fun j _ => mul_nonneg (chMaj_nonneg j (chC_nonneg sys hL j) k r)
      (sigMaj_nonneg hL j r k')
  by_cases hs0 : sigK sys L n r k' = 0
  · rw [hs0, norm_zero, mul_zero]; exact hsum0
  by_cases hv0 : vbK sys L n k r = 0
  · rw [hv0, norm_zero, zero_mul]; exact hsum0
  have hcross : Cross (n : ℝ) r k' := by
    by_contra h; exact hs0 (sigK_eq_zero_of_not_cross h)
  have hr : ¬ InP (n : ℝ) r := not_inP_of_cross_inQ ((cross_symm_iff _ r k').mp hcross) hk'
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 := norm_sigK_le (sys := sys) (n := n) hL (by omega) r k'
  have h2 : ‖vbK sys L n k r‖ ≤ ∑ j, chMaj j (chC sys L j) k r := by
    unfold vbK
    split_ifs
    · exact norm_potKernel_le sys hL k r
    · rw [norm_zero]
      exact Finset.sum_nonneg fun j _ => chMaj_nonneg j (chC_nonneg sys hL j) k r
  calc ‖vbK sys L n k r‖ * ‖sigK sys L n r k'‖
      ≤ (∑ j, chMaj j (chC sys L j) k r) * ∑ j, sigMaj sys L n j r k' :=
        mul_le_mul h2 h1 (norm_nonneg _)
          (Finset.sum_nonneg fun j _ => chMaj_nonneg j (chC_nonneg sys hL j) k r)
    _ = ∑ j, ∑ j', chMaj j (chC sys L j) k r * sigMaj sys L n j' r k' := Finset.sum_mul_sum _ _ _ _
    _ = ∑ j, chMaj j (chC sys L j) k r * sigMaj sys L n j r k' := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_eq_single j (fun j' _ hj' => ?_) (by simp)
        by_cases ha : OnCh j k r
        · by_cases hb : OnCh j' r k'
          · exact absurd (same_channel hn0 hk hk' hr ha hb).symm hj'
          · unfold sigMaj; rw [if_neg hb, mul_zero]
        · unfold chMaj; rw [if_neg ha, zero_mul]

lemma summable_sigMaj_chMaj (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (k k' : Cf eta) :
    Summable fun r => sigMaj sys L n j k r * chMaj j (chC sys L j) r k' :=
  ((summable_sigMaj_row (sys := sys) (L := L) hn j k).mul_right (chC sys L j)).of_nonneg_of_le
    (fun r => mul_nonneg (sigMaj_nonneg hL j k r) (chMaj_nonneg j (chC_nonneg sys hL j) r k'))
    (fun r => mul_le_mul_of_nonneg_left (chMaj_le j (chC_nonneg sys hL j) r k')
      (sigMaj_nonneg hL j k r))

lemma summable_chMaj_sigMaj (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (k k' : Cf eta) :
    Summable fun r => chMaj j (chC sys L j) k r * sigMaj sys L n j r k' :=
  ((summable_sigMaj_col (sys := sys) (L := L) hn j k').mul_left (chC sys L j)).of_nonneg_of_le
    (fun r => mul_nonneg (chMaj_nonneg j (chC_nonneg sys hL j) k r) (sigMaj_nonneg hL j r k'))
    (fun r => mul_le_mul_of_nonneg_right (chMaj_le j (chC_nonneg sys hL j) k r)
      (sigMaj_nonneg hL j r k'))

open Classical in
/-- The channel sum of the first order. -/
lemma tsum_sigMaj_chMaj_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (k k' : Cf eta) :
    ∑' r, sigMaj sys L n j k r * chMaj j (chC sys L j) r k' ≤
      if OnCh j k k' then chC sys L j ^ 2 / cgap sys (gF L) * (611 / (3 * (n : ℝ) / 4) ^ 3)
      else 0 := by
  have e : (fun r => sigMaj sys L n j k r * chMaj j (chC sys L j) r k') = fun r =>
      if OnCh j r k' then sigMaj sys L n j k r * (chC sys L j / latticeNormSq (r (lead j) - k' (lead j)))
      else 0 := by
    funext r
    unfold chMaj
    split_ifs <;> simp
  rw [e, tsum_col]
  simp only [lead_add_tr]
  have hcg := cgap_pos sys (gF_pos hL).ne'
  have hc := chC_nonneg sys hL j
  split_ifs with hkk
  · -- the flat sum
    set θ := k (lead j) - k' (lead j)
    have hterm : ∀ x : Lattice3, sigMaj sys L n j k (k' + tr j x) * (chC sys L j / latticeNormSq x) ≤
        chC sys L j ^ 2 / cgap sys (gF L) * (tailFn (3 * n / 4) (θ - x) * (1 / latticeNormSq x)) := by
      intro x
      unfold sigMaj
      have hlead : k (lead j) - (k' + tr j x) (lead j) = θ - x := by
        rw [Pi.add_apply, tr_lead]; simp only [θ]; abel
      split_ifs
      · rw [hlead]
        exact le_of_eq (by ring)
      · rw [zero_mul]
        have := latticeNormSq_nonneg x
        have := tailFn_nonneg (3 * (n : ℝ) / 4) (θ - x)
        positivity
    have hs : Summable fun x : Lattice3 => tailFn (3 * n / 4) (θ - x) * (1 / latticeNormSq x) := by
      have hs1 := (summable_col_iff j k' (fun r => sigMaj sys L n j k r *
        (chC sys L j / latticeNormSq (r (lead j) - k' (lead j))))).mp (by
          have := summable_sigMaj_chMaj (sys := sys) hL hn j k k'
          rwa [e] at this)
      -- the flat-sum series is summable as a series of nonnegative terms with bounded partial sums
      refine summable_of_sum_le (fun x => mul_nonneg (tailFn_nonneg _ _)
        (by have := latticeNormSq_nonneg x; positivity)) (c := 611 / (3 * (n : ℝ) / 4) ^ 3)
        fun S => ?_
      have h := flat_tsum_in_le θ (three_n_four_ge hn)
      -- partial sums are bounded by the same argument as the series bound
      have hinj : Set.InjOn (fun x : Lattice3 => θ - x) S := fun a _ b _ h => sub_right_injective h
      have e1 : ∑ x ∈ S, tailFn (3 * n / 4) (θ - x) * (1 / latticeNormSq x) =
          ∑ μ ∈ (S.image (fun x => θ - x)).filter (fun μ => (3 * (n : ℝ) / 4) ^ 2 < FSLattice.lsq μ),
            1 / FSLattice.lsq μ ^ 2 * (1 / FSLattice.lsq (θ - μ)) := by
        rw [Finset.sum_filter, Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [sub_sub_cancel, latticeNormSq_eq_lsq]
        exact tailFn_mul_eq _ _ _
      rw [e1]
      exact FSLattice.flat_sum_le _ θ (three_n_four_ge hn)
    have hs2 : Summable fun x : Lattice3 => sigMaj sys L n j k (k' + tr j x) *
        (chC sys L j / latticeNormSq x) :=
      (hs.mul_left (chC sys L j ^ 2 / cgap sys (gF L))).of_nonneg_of_le
        (fun x => mul_nonneg (sigMaj_nonneg hL j k _) (by have := latticeNormSq_nonneg x; positivity))
        hterm
    calc ∑' x, sigMaj sys L n j k (k' + tr j x) * (chC sys L j / latticeNormSq x)
        ≤ ∑' x, chC sys L j ^ 2 / cgap sys (gF L) *
            (tailFn (3 * n / 4) (θ - x) * (1 / latticeNormSq x)) :=
          hs2.tsum_le_tsum hterm (hs.mul_left _)
      _ = chC sys L j ^ 2 / cgap sys (gF L) *
            ∑' x, tailFn (3 * n / 4) (θ - x) * (1 / latticeNormSq x) := tsum_mul_left
      _ ≤ chC sys L j ^ 2 / cgap sys (gF L) * (611 / (3 * (n : ℝ) / 4) ^ 3) :=
          mul_le_mul_of_nonneg_left (flat_tsum_in_le θ (three_n_four_ge hn)) (by positivity)
  · -- off the channel orbit every term vanishes
    have h0 : ∀ x : Lattice3, sigMaj sys L n j k (k' + tr j x) *
        (chC sys L j / latticeNormSq x) = 0 := by
      intro x
      unfold sigMaj
      rw [if_neg, zero_mul]
      intro hon
      exact hkk (onCh_comp hon (onCh_add j k' x))
    simp only [h0, tsum_zero, le_refl]

open Classical in
/-- The channel sum of the second order. -/
lemma tsum_chMaj_sigMaj_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (k k' : Cf eta) :
    ∑' r, chMaj j (chC sys L j) k r * sigMaj sys L n j r k' ≤
      if OnCh j k k' then chC sys L j ^ 2 / cgap sys (gF L) * (611 / (3 * (n : ℝ) / 4) ^ 3)
      else 0 := by
  have e : (fun r => chMaj j (chC sys L j) k r * sigMaj sys L n j r k') = fun r =>
      if OnCh j r k' then chMaj j (chC sys L j) k r *
        (chC sys L j / cgap sys (gF L) * tailFn (3 * n / 4) (r (lead j) - k' (lead j)))
      else 0 := by
    funext r
    unfold sigMaj
    split_ifs <;> simp
  rw [e, tsum_col]
  simp only [lead_add_tr]
  have hcg := cgap_pos sys (gF_pos hL).ne'
  have hc := chC_nonneg sys hL j
  split_ifs with hkk
  · set θ := k (lead j) - k' (lead j)
    have hterm : ∀ x : Lattice3, chMaj j (chC sys L j) k (k' + tr j x) *
        (chC sys L j / cgap sys (gF L) * tailFn (3 * n / 4) x) ≤
        chC sys L j ^ 2 / cgap sys (gF L) * (tailFn (3 * n / 4) x * (1 / latticeNormSq (θ - x))) := by
      intro x
      unfold chMaj
      have hlead : k (lead j) - (k' + tr j x) (lead j) = θ - x := by
        rw [Pi.add_apply, tr_lead]; simp only [θ]; abel
      split_ifs
      · rw [hlead]
        exact le_of_eq (by ring)
      · rw [zero_mul]
        have := latticeNormSq_nonneg (θ - x)
        have := tailFn_nonneg (3 * (n : ℝ) / 4) x
        positivity
    have hs : Summable fun x : Lattice3 => tailFn (3 * n / 4) x * (1 / latticeNormSq (θ - x)) := by
      refine summable_of_sum_le (fun x => mul_nonneg (tailFn_nonneg _ _)
        (by have := latticeNormSq_nonneg (θ - x); positivity)) (c := 611 / (3 * (n : ℝ) / 4) ^ 3)
        fun S => ?_
      have e1 : ∑ x ∈ S, tailFn (3 * n / 4) x * (1 / latticeNormSq (θ - x)) =
          ∑ μ ∈ S.filter (fun μ => (3 * (n : ℝ) / 4) ^ 2 < FSLattice.lsq μ),
            1 / FSLattice.lsq μ ^ 2 * (1 / FSLattice.lsq (θ - μ)) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun μ _ => tailFn_mul_eq _ μ _
      rw [e1]
      exact FSLattice.flat_sum_le _ θ (three_n_four_ge hn)
    have hs2 : Summable fun x : Lattice3 => chMaj j (chC sys L j) k (k' + tr j x) *
        (chC sys L j / cgap sys (gF L) * tailFn (3 * n / 4) x) :=
      (hs.mul_left (chC sys L j ^ 2 / cgap sys (gF L))).of_nonneg_of_le
        (fun x => mul_nonneg (chMaj_nonneg j hc _ _)
          (mul_nonneg (by positivity) (tailFn_nonneg _ _)))
        hterm
    calc ∑' x, chMaj j (chC sys L j) k (k' + tr j x) *
          (chC sys L j / cgap sys (gF L) * tailFn (3 * n / 4) x)
        ≤ ∑' x, chC sys L j ^ 2 / cgap sys (gF L) *
            (tailFn (3 * n / 4) x * (1 / latticeNormSq (θ - x))) :=
          hs2.tsum_le_tsum hterm (hs.mul_left _)
      _ = chC sys L j ^ 2 / cgap sys (gF L) *
            ∑' x, tailFn (3 * n / 4) x * (1 / latticeNormSq (θ - x)) := tsum_mul_left
      _ ≤ chC sys L j ^ 2 / cgap sys (gF L) * (611 / (3 * (n : ℝ) / 4) ^ 3) :=
          mul_le_mul_of_nonneg_left (flat_tsum_out_le θ (three_n_four_ge hn)) (by positivity)
  · have h0 : ∀ x : Lattice3, chMaj j (chC sys L j) k (k' + tr j x) *
        (chC sys L j / cgap sys (gF L) * tailFn (3 * n / 4) x) = 0 := by
      intro x
      unfold chMaj
      rw [if_neg, zero_mul]
      intro hon
      exact hkk (onCh_comp hon (onCh_add j k' x))
    simp only [h0, tsum_zero, le_refl]

open Classical in
/-- **The kernel bound of `lem:h2`**: for `k, k' ∈ Q`,
`|h(k, k')| ≤ Σ_j 1{k on channel j from k'} chb_j / n³`, `chb_j = c_j²/c_gap · 611·64/27`. -/
theorem norm_hbK_le (hL : 0 < L) (hn : 2 ≤ n) {k k' : Cf eta} (hk : InQ (n : ℝ) k)
    (hk' : InQ (n : ℝ) k') :
    ‖hbK sys L n k k'‖ ≤ ∑ j, (if OnCh j k k' then chb sys L j else 0) / (n : ℝ) ^ 3 := by
  set B := ∑ j : Ch eta, if OnCh j k k' then
    chC sys L j ^ 2 / cgap sys (gF L) * (611 / (3 * (n : ℝ) / 4) ^ 3) else 0
  have hT1 : ∑' r, ‖sigK sys L n k r‖ * ‖vbK sys L n r k'‖ ≤ B := by
    have hsum : ∀ j, Summable fun r => sigMaj sys L n j k r * chMaj j (chC sys L j) r k' :=
      fun j => summable_sigMaj_chMaj hL hn j k k'
    have hs1 : Summable fun r => ‖sigK sys L n k r‖ * ‖vbK sys L n r k'‖ := by
      have := (summable_sigK_vbK (sys := sys) hL hn k k').norm
      simpa only [norm_mul] using this
    calc ∑' r, ‖sigK sys L n k r‖ * ‖vbK sys L n r k'‖
        ≤ ∑' r, ∑ j, sigMaj sys L n j k r * chMaj j (chC sys L j) r k' :=
          hs1.tsum_le_tsum (fun r => norm_sigK_vbK_le hL hn hk hk' r)
            (summable_sum fun j _ => hsum j)
      _ = ∑ j, ∑' r, sigMaj sys L n j k r * chMaj j (chC sys L j) r k' :=
          Summable.tsum_finsetSum fun j _ => hsum j
      _ ≤ B := Finset.sum_le_sum fun j _ => tsum_sigMaj_chMaj_le hL hn j k k'
  have hT2 : ∑' r, ‖vbK sys L n k r‖ * ‖sigK sys L n r k'‖ ≤ B := by
    have hsum : ∀ j, Summable fun r => chMaj j (chC sys L j) k r * sigMaj sys L n j r k' :=
      fun j => summable_chMaj_sigMaj hL hn j k k'
    have hs1 : Summable fun r => ‖vbK sys L n k r‖ * ‖sigK sys L n r k'‖ := by
      have := (summable_vbK_sigK (sys := sys) hL hn k k').norm
      simpa only [norm_mul] using this
    calc ∑' r, ‖vbK sys L n k r‖ * ‖sigK sys L n r k'‖
        ≤ ∑' r, ∑ j, chMaj j (chC sys L j) k r * sigMaj sys L n j r k' :=
          hs1.tsum_le_tsum (fun r => norm_vbK_sigK_le hL hn hk hk' r)
            (summable_sum fun j _ => hsum j)
      _ = ∑ j, ∑' r, chMaj j (chC sys L j) k r * sigMaj sys L n j r k' :=
          Summable.tsum_finsetSum fun j _ => hsum j
      _ ≤ B := Finset.sum_le_sum fun j _ => tsum_chMaj_sigMaj_le hL hn j k k'
  have hA : ‖∑' r, sigK sys L n k r * vbK sys L n r k'‖ ≤
      ∑' r, ‖sigK sys L n k r‖ * ‖vbK sys L n r k'‖ := by
    have := norm_tsum_le_tsum_norm (summable_sigK_vbK (sys := sys) hL hn k k').norm
    simpa only [norm_mul] using this
  have hB : ‖∑' r, vbK sys L n k r * sigK sys L n r k'‖ ≤
      ∑' r, ‖vbK sys L n k r‖ * ‖sigK sys L n r k'‖ := by
    have := norm_tsum_le_tsum_norm (summable_vbK_sigK (sys := sys) hL hn k k').norm
    simpa only [norm_mul] using this
  have hfin : B = ∑ j, (if OnCh j k k' then chb sys L j else 0) / (n : ℝ) ^ 3 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · unfold chb; exact flat_const_eq hn _
    · simp
  calc ‖hbK sys L n k k'‖ = ‖(1 / 2 : ℂ)‖ * ‖(∑' r, sigK sys L n k r * vbK sys L n r k') -
        ∑' r, vbK sys L n k r * sigK sys L n r k'‖ := by unfold hbK; rw [norm_mul]
    _ ≤ 1 / 2 * (‖∑' r, sigK sys L n k r * vbK sys L n r k'‖ +
          ‖∑' r, vbK sys L n k r * sigK sys L n r k'‖) := by
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
        rw [this]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ 1 / 2 * (B + B) := by gcongr; exacts [hA.trans hT1, hB.trans hT2]
    _ = B := by ring
    _ = _ := hfin

/-! ## The operator `H₂^bb` on `E_n` and its kernel -/

omit [Fintype ν] in
/-- `emb v = Σ_p v_p e_{idx p}`. -/
lemma emb_eq_sum (v : En eta n) :
    emb eta n v = ∑ p, v.ofLp p • ev (finiteConfigLatticeIndex eta n p) := by
  classical
  show finiteFourierLpEmbed eta n v.ofLp = _
  unfold finiteFourierLpEmbed lpFiniteEmbed
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ev, ← lp.single_smul, smul_eq_mul, mul_one]
  congr
  funext a b
  exact Subsingleton.elim _ _

omit [Fintype ν] in
lemma ev_apply (p r : Cf eta) : ev p r = if r = p then 1 else 0 := by
  classical
  rw [ev, lp.single_apply, Pi.single_apply]

lemma Vb_ev (hL : 0 < L) (p r : Cf eta) : Vb sys L n hL (ev p) r = vbK sys L n r p := by
  classical
  rw [Vb_apply]
  rw [tsum_eq_single p (fun k hk => by rw [ev_apply, if_neg hk, mul_zero])]
  rw [ev_apply, if_pos rfl, mul_one]

lemma Sig_ev (hL : 0 < L) (hn : 2 ≤ n) (p r : Cf eta) :
    Sig sys L n hL hn (ev p) r = sigK sys L n r p := by
  classical
  rw [Sig_apply]
  rw [tsum_eq_single p (fun k hk => by rw [ev_apply, if_neg hk, mul_zero])]
  rw [ev_apply, if_pos rfl, mul_one]

variable (sys) in
/-- **`H₂^bb = ½ P[Σ_b, V_b]P`** on `E_n`. -/
noncomputable def Hbb (hL : 0 < L) (hn : 2 ≤ n) : En eta n →L[ℂ] En eta n :=
  (1 / 2 : ℂ) • (ext eta n ∘L (Sig sys L n hL hn * Vb sys L n hL -
    Vb sys L n hL * Sig sys L n hL hn) ∘L emb eta n)

/-- The cube kernel of `H₂^bb`. -/
noncomputable def hbC (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (q p : Cfg eta n) : ℂ :=
  hbK sys L n (finiteConfigLatticeIndex eta n q) (finiteConfigLatticeIndex eta n p)

/-- **`H₂^bb` is the kernel operator of `h`.** -/
theorem Hbb_apply (hL : 0 < L) (hn : 2 ≤ n) (v : En eta n) (q : Cfg eta n) :
    (Hbb sys hL hn v).ofLp q = ∑ p, v.ofLp p * hbC sys L n q p := by
  set iq := finiteConfigLatticeIndex eta n q
  have h1 : ∀ x : L2 eta, (ext eta n x).ofLp q = x iq := fun x => rfl
  have hSV : (Sig sys L n hL hn (Vb sys L n hL (emb eta n v))) iq =
      ∑ p, v.ofLp p * ∑' r, sigK sys L n iq r * vbK sys L n r (finiteConfigLatticeIndex eta n p) := by
    rw [emb_eq_sum, map_sum, map_sum, lp.coeFn_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Sig_apply]
    congr 1
    exact tsum_congr fun r => by rw [Vb_ev]
  have hVS : (Vb sys L n hL (Sig sys L n hL hn (emb eta n v))) iq =
      ∑ p, v.ofLp p * ∑' r, vbK sys L n iq r * sigK sys L n r (finiteConfigLatticeIndex eta n p) := by
    rw [emb_eq_sum, map_sum, map_sum, lp.coeFn_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Vb_apply]
    congr 1
    exact tsum_congr fun r => by rw [Sig_ev]
  have e : (Hbb sys hL hn v).ofLp q = (1 / 2 : ℂ) * ((Sig sys L n hL hn (Vb sys L n hL
      (emb eta n v))) iq - (Vb sys L n hL (Sig sys L n hL hn (emb eta n v))) iq) := by
    rfl
  rw [e, hSV, hVS, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold hbC hbK
  ring

theorem Hbb_eq_kop (hL : 0 < L) (hn : 2 ≤ n) :
    (Hbb sys hL hn : En eta n →ₗ[ℂ] En eta n) = FSKernel.kop (hbC sys L n) := by
  ext v q
  rw [FSKernel.kop_apply]
  exact Hbb_apply hL hn v q

/-- `H₂^bb` is symmetric. -/
theorem Hbb_symm (hL : 0 < L) (hn : 2 ≤ n) :
    (Hbb sys hL hn : En eta n →ₗ[ℂ] En eta n).IsSymmetric := by
  rw [Hbb_eq_kop hL hn]
  exact FSKernel.kop_symm _ fun q p => hbK_conj hL _ _

end FSNormal
