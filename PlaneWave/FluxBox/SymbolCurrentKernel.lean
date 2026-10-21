import PlaneWave.FluxBox.ComRemainderClasses

/-!
# Flux route, stage 2, part 15: the kernel of the symbol current

The Lean version of `lem:com` and of the kernel bound of `prop:zsym`, for the com dressing only
(the flat factor `μ/M_p` of the text's dressed symbol cancels from the antisymmetrized bracket):

* `comC_onCh` (the pair momentum is conserved by a hop), `comC_add`, `comC_sub`;
* `bulk_gap`: a hop from `Q` out of `P` has `E(r) - E(q) ≥ g²|θ|²/(6μ_j)`, hence is gapped;
* `ycK_bulk_eq`: on such a hop `y(r, q) = -w(r, q) c_j(q, θ)/(E(r) - E(q))`;
* the kernel `zaK` of `Z_a = Π_Q i(W R Y - Y R W) Π_Q` (`ZaN_eq_kop`);
* **`norm_zaK_le`**: for `q, q' ∈ Q` on a channel `j`,
  `|z(q', q)| ≤ c_j² |Π_j|/M̄_j · 611 (4/(3n))³ (6 μ_j |τ| + 36 μ_j² |ϖ| (4/(3n))/g²)`,
  `τ` the outer transfer and `ϖ = E(q') - E(q)` the outer mismatch; `z = 0` off the channels.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The com coefficient on a hop -/

section ComC

variable (sys : CoulombSystem eta ν) (p₀ : Fin eta) (g : ℝ)

omit [Fintype ν] in
/-- The pair momentum is conserved by a hop: `c_j(k₁, x) = c_j(k, x)` for `k₁` on `j` from `k`. -/
lemma comC_onCh {j : Ch eta} {k₁ k : Cf eta} (h : OnCh j k₁ k) (x : Lattice3) :
    comC sys p₀ g j k₁ x = comC sys p₀ g j k x := by
  cases j with
  | inl a => rfl
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    have e : k₁ = k + tr (.inr pr) (k₁ (lead (.inr pr)) - k (lead (.inr pr))) := h
    set θ := k₁ (lead (.inr pr)) - k (lead (.inr pr))
    have hs : ∀ i, ((k₁ pr.1.1 i : ℤ) : ℝ) + ((k₁ pr.1.2 i : ℤ) : ℝ) =
        ((k pr.1.1 i : ℤ) : ℝ) + ((k pr.1.2 i : ℤ) : ℝ) := by
      intro i
      have e1 : k₁ pr.1.1 = k pr.1.1 + θ := by rw [e]; simp [tr, Pi.single_eq_of_ne hne]
      have e2 : k₁ pr.1.2 = k pr.1.2 + -θ := by rw [e]; simp [tr, Pi.single_eq_of_ne hne.symm]
      rw [e1, e2]
      simp only [Pi.add_apply, Pi.neg_apply, Int.cast_add, Int.cast_neg]
      ring
    simp only [comC]
    split_ifs <;> simp only [hs]

omit [Fintype ν] in
lemma comC_add (j : Ch eta) (k : Cf eta) (x y : Lattice3) :
    comC sys p₀ g j k (x + y) = comC sys p₀ g j k x + comC sys p₀ g j k y := by
  cases j with
  | inl a => simp [comC]
  | inr pr =>
    simp only [comC]
    split_ifs
    · rw [← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Int.cast_add]; ring
    · rw [← neg_add, ← mul_add, ← Finset.sum_add_distrib]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Int.cast_add]; ring
    · ring

omit [Fintype ν] in
lemma comC_neg (j : Ch eta) (k : Cf eta) (x : Lattice3) :
    comC sys p₀ g j k (-x) = -comC sys p₀ g j k x := by
  have h := comC_add sys p₀ g j k x (-x)
  rw [add_neg_cancel] at h
  have h0 : comC sys p₀ g j k 0 = 0 := by
    have := comC_add sys p₀ g j k 0 0
    simp only [add_zero] at this
    linarith
  rw [h0] at h
  linarith

omit [Fintype ν] in
lemma comC_sub (j : Ch eta) (k : Cf eta) (x y : Lattice3) :
    comC sys p₀ g j k (x - y) = comC sys p₀ g j k x - comC sys p₀ g j k y := by
  rw [sub_eq_add_neg, comC_add, comC_neg, ← sub_eq_add_neg]

end ComC

/-! ## The bulk-fed hops -/

section BulkHop

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

omit [Fintype ν] in
/-- **The bulk gap**: a hop from `q ∈ Q` to `r ∉ P` has `E(r) - E(q) ≥ g²|θ|²/(6μ_j)`. -/
lemma bulk_gap (hL : 0 < L) {n : ℕ} {j : Ch eta} {r q : Cfg eta N}
    (hj : OnCh j (cidx N r) (cidx N q)) (hr : ¬ InP (n : ℝ) (cidx N r)) (hq : InQ (n : ℝ) (cidx N q)) :
    gF L ^ 2 * FSChannel.rho (chT N j r q) ^ 2 / (6 * muCh sys j) ≤ Asym sys L N r - Asym sys L N q := by
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set θ := chT N j r q
  set ρ := FSChannel.rho θ
  have hρ : 3 * n / 4 < ρ := rho_gt_of_bulk_out hj hr hq
  have hρ0 : 0 ≤ ρ := FSChannel.rho_nonneg θ
  have hρsq : ρ ^ 2 = FSLattice.lsq θ := FSChannel.rho_sq θ
  have hcsq : ∑ i, cCh sys j (cidx N q) i ^ 2 ≤ (n / 4 : ℝ) ^ 2 :=
    cCh_sq_le sys j (cidx N q) (fun c _ => hq c)
  have hdot := FSLattice.dot_sq_le (cCh sys j (cidx N q)) θ
  have ht : |∑ i, (θ i : ℝ) * cCh sys j (cidx N q) i| ≤ ρ * (n / 4) := by
    rw [← Real.sqrt_sq (abs_nonneg _), sq_abs]
    rw [show ρ * (n / 4 : ℝ) = Real.sqrt ((ρ * (n / 4)) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    rw [mul_pow, hρsq]
    exact hdot.trans (mul_le_mul_of_nonneg_left hcsq (FSLattice.lsq_nonneg θ))
  have hF : ρ ^ 2 / 3 ≤ FSLattice.slabF (cCh sys j (cidx N q)) θ := by
    have e : FSLattice.slabF (cCh sys j (cidx N q)) θ =
        FSLattice.lsq θ + 2 * ∑ i, (θ i : ℝ) * cCh sys j (cidx N q) i := rfl
    rw [e, ← hρsq]
    have h1 : ρ * (n / 4) ≤ ρ ^ 2 / 3 := by nlinarith
    rw [abs_le] at ht
    linarith [ht.1]
  rw [Asym_hop hj]
  calc gF L ^ 2 * ρ ^ 2 / (6 * muCh sys j) = gF L ^ 2 / (2 * muCh sys j) * (ρ ^ 2 / 3) := by
        field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hF (by positivity)

omit [Fintype ν] in
/-- A bulk-fed hop is gapped (`n ≥ 8`). -/
lemma gapC_of_bulk (hL : 0 < L) {n : ℕ} (hn : 8 ≤ n) {j : Ch eta} {r q : Cfg eta N}
    (hj : OnCh j (cidx N r) (cidx N q)) (hr : ¬ InP (n : ℝ) (cidx N r)) (hq : InQ (n : ℝ) (cidx N q)) :
    gapC sys L N r q := by
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hne : r ≠ q := by
    intro h; rw [h] at hr; exact hr (inQ_imp_inP (Nat.cast_nonneg n) hq)
  refine ⟨hne, j, hj, ?_⟩
  have hgap := bulk_gap (sys := sys) hL hj hr hq
  have hρ := rho_gt_of_bulk_out hj hr hq
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hρ6 : 6 ≤ FSChannel.rho (chT N j r q) := by linarith
  have hρ0 : 0 ≤ FSChannel.rho (chT N j r q) := FSChannel.rho_nonneg _
  have h1 : gF L ^ 2 * FSChannel.rho (chT N j r q) / muCh sys j ≤
      gF L ^ 2 * FSChannel.rho (chT N j r q) ^ 2 / (6 * muCh sys j) := by
    rw [div_le_div_iff₀ hμ (by positivity)]
    have h0 : 0 ≤ gF L ^ 2 * FSChannel.rho (chT N j r q) * muCh sys j := by positivity
    have key := mul_le_mul_of_nonneg_left hρ6 h0
    calc gF L ^ 2 * FSChannel.rho (chT N j r q) * (6 * muCh sys j) =
        gF L ^ 2 * FSChannel.rho (chT N j r q) * muCh sys j * 6 := by ring
      _ ≤ gF L ^ 2 * FSChannel.rho (chT N j r q) * muCh sys j * FSChannel.rho (chT N j r q) := key
      _ = gF L ^ 2 * FSChannel.rho (chT N j r q) ^ 2 * muCh sys j := by ring
  calc gF L ^ 2 * FSChannel.rho (chT N j r q) / muCh sys j ≤ _ := h1
    _ ≤ Asym sys L N r - Asym sys L N q := hgap
    _ ≤ |Asym sys L N r - Asym sys L N q| := le_abs_self _

/-- **The dressing on a bulk-fed hop**: `y(r, q) = -w(r, q) c_j(q, θ)/(E(r) - E(q))`. -/
lemma ycK_bulk_eq (hL : 0 < L) {n : ℕ} (hn : 8 ≤ n) {j : Ch eta} {r q : Cfg eta N}
    (hj : OnCh j (cidx N r) (cidx N q)) (hr : ¬ InP (n : ℝ) (cidx N r)) (hq : InQ (n : ℝ) (cidx N q)) :
    ycK sys L p₀ N r q = -(wNK sys L N r q * (comC sys p₀ (gF L) j (cidx N q) (chT N j r q) : ℂ)) /
      ((Asym sys L N r - Asym sys L N q : ℝ) : ℂ) := by
  have hgap := gapC_of_bulk (sys := sys) hL hn hj hr hq
  have hE := gapC_ne hL hgap
  unfold ycK FSKernel.divK
  dsimp only
  rw [if_neg hE]
  unfold gcmGap
  rw [if_pos hgap, gcmK_eq hL hj]
  congr 1
  have hI : -Complex.I * -Complex.I = -1 := by rw [neg_mul_neg, Complex.I_mul_I]
  rw [show -Complex.I * (-Complex.I * wNK sys L N r q *
    (comC sys p₀ (gF L) j (cidx N q) (chT N j r q) : ℂ)) =
    (-Complex.I * -Complex.I) * (wNK sys L N r q * (comC sys p₀ (gF L) j (cidx N q) (chT N j r q) : ℂ)) by
      ring, hI]
  ring


/-- The dressing vanishes off the channels. -/
lemma ycK_eq_zero_of_wNK {q p : Cfg eta N} (h : wNK sys L N q p = 0) : ycK sys L p₀ N q p = 0 := by
  unfold ycK FSKernel.divK
  dsimp only
  split_ifs with hE
  · rfl
  · unfold gcmGap
    split_ifs
    · rw [gcmK_eq_zero h, mul_zero, zero_div]
    · rw [mul_zero, zero_div]

/-- The transposed bulk dressing: `y(q, r) = -w(q, r) c_j(q, θ)/(E(r) - E(q))`, `θ = r - q`. -/
lemma ycK_bulk_eq' (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {n : ℕ} (hn : 8 ≤ n) {j : Ch eta} {q r : Cfg eta N}
    (hj : OnCh j (cidx N r) (cidx N q)) (hr : ¬ InP (n : ℝ) (cidx N r)) (hq : InQ (n : ℝ) (cidx N q)) :
    ycK sys L p₀ N q r = -(wNK sys L N q r * (comC sys p₀ (gF L) j (cidx N q) (chT N j r q) : ℂ)) /
      ((Asym sys L N r - Asym sys L N q : ℝ) : ℂ) := by
  rw [ycK_conj hL H hKernel r q, ycK_bulk_eq hL hn hj hr hq, map_div₀, map_neg, map_mul,
    Complex.conj_ofReal, Complex.conj_ofReal, ← wNK_conj hL r q]

omit [Fintype ν] in
lemma bulk_gap_pos (hL : 0 < L) {n : ℕ} {j : Ch eta} {r q : Cfg eta N}
    (hj : OnCh j (cidx N r) (cidx N q)) (hr : ¬ InP (n : ℝ) (cidx N r)) (hq : InQ (n : ℝ) (cidx N q)) :
    0 < Asym sys L N r - Asym sys L N q := by
  have h := bulk_gap (sys := sys) hL hj hr hq
  have hρ := rho_gt_of_bulk_out hj hr hq
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hρ0 : 0 < FSChannel.rho (chT N j r q) := by linarith
  have : 0 < gF L ^ 2 * FSChannel.rho (chT N j r q) ^ 2 / (6 * muCh sys j) := by positivity
  linarith

end BulkHop

/-! ## The kernel of the symbol current -/

section ZaKernel

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ)

open Classical in
/-- The kernel of `Z_a = Π_Q i(W R Y - Y R W) Π_Q`. -/
noncomputable def zaK (q' q : Cfg eta N) : ℂ :=
  if InQ (n : ℝ) (cidx N q') ∧ InQ (n : ℝ) (cidx N q) then
    Complex.I * ∑ r, (if ¬ InP (n : ℝ) (cidx N r) then
      wNK sys L N q' r * ycK sys L p₀ N r q - ycK sys L p₀ N q' r * wNK sys L N r q else 0)
  else 0

/-- The kernel constant of `Z_a` on channel `j` before the flat sum:
`c_j² |Π_j|/M̄_j (6 μ_j |τ| + 36 μ_j² |ϖ|/(g² (3n/4)))`. -/
noncomputable def zaA (j : Ch eta) (q' q : Cfg eta N) : ℝ :=
  chC sys L j ^ 2 * (piC j (cidx N q) / Mtot sys j) *
    (6 * muCh sys j * FSChannel.rho (chT N j q' q) +
      36 * muCh sys j ^ 2 * |Asym sys L N q' - Asym sys L N q| / (gF L ^ 2 * (3 * n / 4)))

variable {sys L p₀ N n}

/-- `Z_a = kop zaK`. -/
theorem ZaN_eq_kop (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    ZaN sys L p₀ N n = FSKernel.kop (zaK sys L p₀ N n) := by
  classical
  have hW : WN sys L N = FSKernel.kop (wNK sys L N) := VN_eq_kop sys hL H hKernel
  refine LinearMap.ext fun v => ?_
  ext q'
  unfold ZaN zaK
  rw [hW]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply, FSKernel.res_apply,
    FSKernel.kop_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  by_cases hq' : InQ (n : ℝ) (cidx N q')
  swap
  · simp [hq']
  simp only [hq', if_true, true_and]
  calc _ = ∑ r, ∑ p, Complex.I * (if ¬ InP (n : ℝ) (cidx N r) then
          (if InQ (n : ℝ) (cidx N p) then v.ofLp p else 0) *
            (ycK sys L p₀ N r p * wNK sys L N q' r - wNK sys L N r p * ycK sys L p₀ N q' r) else 0) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases hr : InP (n : ℝ) (cidx N r)
        · simp [hr]
        · simp only [hr, not_false_eq_true, if_true]
          rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
    _ = ∑ p, ∑ r, Complex.I * (if ¬ InP (n : ℝ) (cidx N r) then
          (if InQ (n : ℝ) (cidx N p) then v.ofLp p else 0) *
            (ycK sys L p₀ N r p * wNK sys L N q' r - wNK sys L N r p * ycK sys L p₀ N q' r) else 0) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hp : InQ (n : ℝ) (cidx N p)
        · simp only [hp, if_true]
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          split_ifs <;> ring
        · simp [hp]

/-- The excursion term on a channel: `w(q', r) y(r, q) - y(q', r) w(r, q) =
w(q', r) w(r, q) (a'/d₂ - b/d₁)`. -/
lemma zaK_term_eq (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) {j : Ch eta} {q' r q : Cfg eta N}
    (hq' : InQ (n : ℝ) (cidx N q')) (hq : InQ (n : ℝ) (cidx N q))
    (hr : ¬ InP (n : ℝ) (cidx N r)) (h1 : OnCh j (cidx N r) (cidx N q))
    (h2 : OnCh j (cidx N r) (cidx N q')) :
    wNK sys L N q' r * ycK sys L p₀ N r q - ycK sys L p₀ N q' r * wNK sys L N r q =
      wNK sys L N q' r * wNK sys L N r q *
        ((comC sys p₀ (gF L) j (cidx N q') (chT N j r q') / (Asym sys L N r - Asym sys L N q') -
          comC sys p₀ (gF L) j (cidx N q) (chT N j r q) / (Asym sys L N r - Asym sys L N q) : ℝ) : ℂ) := by
  rw [ycK_bulk_eq hL hn h1 hr hq, ycK_bulk_eq' hL H hKernel hn h2 hr hq']
  have hd1 := bulk_gap_pos (sys := sys) hL h1 hr hq
  have hd2 := bulk_gap_pos (sys := sys) hL h2 hr hq'
  have hd1' : ((Asym sys L N r : ℝ) : ℂ) - ((Asym sys L N q : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast hd1.ne'
  have hd2' : ((Asym sys L N r : ℝ) : ℂ) - ((Asym sys L N q' : ℝ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast hd2.ne'
  push_cast
  field_simp
  ring

omit [Fintype ν] in
/-- The bracket identity `a'/d₂ - b/d₁ = -c/d₁ + a' ϖ/(d₁ d₂)` for `a' - b = -c`, `ϖ = d₁ - d₂`. -/
lemma bracket_eq {a' b c ϖ d₁ d₂ : ℝ} (h1 : d₁ ≠ 0) (h2 : d₂ ≠ 0) (hab : a' - b = -c)
    (hϖ : ϖ = d₁ - d₂) : a' / d₂ - b / d₁ = -c / d₁ + a' * ϖ / (d₁ * d₂) := by
  have hb : b = a' + c := by linarith
  rw [hb, hϖ]
  field_simp
  ring

omit [Fintype ν] in
/-- The bracket bound. -/
lemma bracket_le {c a' ϖ d₁ d₂ l₁ l₂ ρτ ρ₂ g μ Pm R : ℝ}
    (hg : 0 < g) (hμ : 0 < μ) (hl₁ : 0 < l₁) (hR : 0 < R) (hPm : 0 ≤ Pm) (hρτ : 0 ≤ ρτ)
    (hd₁ : g ^ 2 * l₁ / (6 * μ) ≤ d₁) (hd₂ : g ^ 2 * l₂ / (6 * μ) ≤ d₂)
    (hc : |c| ≤ g ^ 2 * ρτ * Pm) (ha : |a'| ≤ g ^ 2 * ρ₂ * Pm) (hρ₂ : ρ₂ ^ 2 = l₂) (hρR : R ≤ ρ₂) :
    |-c / d₁ + a' * ϖ / (d₁ * d₂)| ≤ Pm * (6 * μ * ρτ + 36 * μ ^ 2 * |ϖ| / (g ^ 2 * R)) / l₁ := by
  have hρ₂0 : 0 < ρ₂ := lt_of_lt_of_le hR hρR
  have hl₂ : 0 < l₂ := by rw [← hρ₂]; positivity
  have hd₁0 : 0 < d₁ := lt_of_lt_of_le (by positivity) hd₁
  have hd₂0 : 0 < d₂ := lt_of_lt_of_le (by positivity) hd₂
  have hϖ := abs_nonneg ϖ
  have e1 : |-c / d₁| ≤ 6 * μ * ρτ * Pm / l₁ := by
    rw [abs_div, abs_neg, abs_of_pos hd₁0, div_le_div_iff₀ hd₁0 hl₁]
    calc |c| * l₁ ≤ g ^ 2 * ρτ * Pm * l₁ := mul_le_mul_of_nonneg_right hc hl₁.le
      _ = 6 * μ * ρτ * Pm * (g ^ 2 * l₁ / (6 * μ)) := by field_simp
      _ ≤ 6 * μ * ρτ * Pm * d₁ := mul_le_mul_of_nonneg_left hd₁ (by positivity)
  have e2 : |a' * ϖ / (d₁ * d₂)| ≤ 36 * μ ^ 2 * Pm * |ϖ| / (g ^ 2 * R * l₁) := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hd₁0 hd₂0),
      div_le_div_iff₀ (mul_pos hd₁0 hd₂0) (by positivity)]
    have hdd : g ^ 2 * l₁ / (6 * μ) * (g ^ 2 * l₂ / (6 * μ)) ≤ d₁ * d₂ :=
      mul_le_mul hd₁ hd₂ (by positivity) hd₁0.le
    have hgR : g ^ 2 * R * l₁ ≤ g ^ 2 * ρ₂ * l₁ := by
      have : g ^ 2 * R ≤ g ^ 2 * ρ₂ := mul_le_mul_of_nonneg_left hρR (by positivity)
      exact mul_le_mul_of_nonneg_right this hl₁.le
    calc |a'| * |ϖ| * (g ^ 2 * R * l₁) ≤ g ^ 2 * ρ₂ * Pm * |ϖ| * (g ^ 2 * ρ₂ * l₁) :=
          mul_le_mul (mul_le_mul_of_nonneg_right ha hϖ) hgR (by positivity) (by positivity)
      _ = 36 * μ ^ 2 * Pm * |ϖ| * (g ^ 2 * l₁ / (6 * μ) * (g ^ 2 * l₂ / (6 * μ))) := by
          rw [← hρ₂]; field_simp; ring
      _ ≤ 36 * μ ^ 2 * Pm * |ϖ| * (d₁ * d₂) := mul_le_mul_of_nonneg_left hdd (by positivity)
  calc |-c / d₁ + a' * ϖ / (d₁ * d₂)| ≤ |-c / d₁| + |a' * ϖ / (d₁ * d₂)| := abs_add_le _ _
    _ ≤ 6 * μ * ρτ * Pm / l₁ + 36 * μ ^ 2 * Pm * |ϖ| / (g ^ 2 * R * l₁) := add_le_add e1 e2
    _ = Pm * (6 * μ * ρτ + 36 * μ ^ 2 * |ϖ| / (g ^ 2 * R)) / l₁ := by field_simp

lemma zaA_nonneg (hL : 0 < L) (j : Ch eta) (q' q : Cfg eta N) : 0 ≤ zaA sys L N n j q' q := by
  unfold zaA
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hM := Mtot_pos sys j
  have hpi := piC_nonneg j (cidx N q)
  have hcC := chC_nonneg sys hL j
  have hρ := FSChannel.rho_nonneg (chT N j q' q)
  positivity

/-- **The termwise bound** of a bulk excursion `q → r → q'` on channel `j`:
`|w(q', r) y(r, q) - y(q', r) w(r, q)| ≤ A_j(q', q) |θ₁|⁻⁴ |τ - θ₁|⁻²`, `θ₁ = r - q`. -/
lemma norm_zaK_term_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) {j : Ch eta} {q' r q : Cfg eta N}
    (hq' : InQ (n : ℝ) (cidx N q')) (hq : InQ (n : ℝ) (cidx N q))
    (hr : ¬ InP (n : ℝ) (cidx N r)) (h1 : OnCh j (cidx N r) (cidx N q))
    (h2 : OnCh j (cidx N r) (cidx N q')) :
    ‖wNK sys L N q' r * ycK sys L p₀ N r q - ycK sys L p₀ N q' r * wNK sys L N r q‖ ≤
      zaA sys L N n j q' q * (1 / FSLattice.lsq (chT N j r q) ^ 2 *
        (1 / FSLattice.lsq (chT N j q' q - chT N j r q))) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hM := Mtot_pos sys j
  have hpi := piC_nonneg j (cidx N q)
  have hcC := chC_nonneg sys hL j
  have hq'P : InP (n : ℝ) (cidx N q') := inQ_imp_inP hn0 hq'
  have hqP : InP (n : ℝ) (cidx N q) := inQ_imp_inP hn0 hq
  have hrq : r ≠ q := fun h => hr (h ▸ hqP)
  have hq'r : q' ≠ r := fun h => hr (h ▸ hq'P)
  have hq'q : OnCh j (cidx N q') (cidx N q) := onCh_comp (onCh_symm h2) h1
  have hT : chT N j q' q - chT N j r q = chT N j q' r := by unfold chT; abel
  have hT2 : chT N j r q' - chT N j r q = -chT N j q' q := by unfold chT; abel
  have hl₂e : FSLattice.lsq (chT N j q' r) = FSLattice.lsq (chT N j r q') := by
    unfold chT; exact FSChannel.lsq_sub_comm _ _
  rw [zaK_term_eq hL H hKernel hn hq' hq hr h1 h2, hT, hl₂e]
  -- the pieces
  set a' := comC sys p₀ (gF L) j (cidx N q') (chT N j r q') with ha'
  set b := comC sys p₀ (gF L) j (cidx N q) (chT N j r q) with hb
  set c := comC sys p₀ (gF L) j (cidx N q) (chT N j q' q) with hc
  set d₁ := Asym sys L N r - Asym sys L N q with hd₁
  set d₂ := Asym sys L N r - Asym sys L N q' with hd₂
  set ϖ := Asym sys L N q' - Asym sys L N q with hϖ
  set l₁ := FSLattice.lsq (chT N j r q) with hl₁
  set l₂ := FSLattice.lsq (chT N j r q') with hl₂
  have ha'q : a' = comC sys p₀ (gF L) j (cidx N q) (chT N j r q') := comC_onCh sys p₀ (gF L) hq'q _
  have hab : a' - b = -c := by
    rw [ha'q, hb, ← comC_sub, hT2, comC_neg]
  have hd₁0 := bulk_gap_pos (sys := sys) hL h1 hr hq
  have hd₂0 := bulk_gap_pos (sys := sys) hL h2 hr hq'
  have hX : a' / d₂ - b / d₁ = -c / d₁ + a' * ϖ / (d₁ * d₂) :=
    bracket_eq hd₁0.ne' hd₂0.ne' hab (by rw [hϖ, hd₁, hd₂]; ring)
  have hρ₁ := FSChannel.rho_sq (chT N j r q)
  have hρ₂ := FSChannel.rho_sq (chT N j r q')
  have hgap₁ := bulk_gap (sys := sys) hL h1 hr hq
  have hgap₂ := bulk_gap (sys := sys) hL h2 hr hq'
  rw [hρ₁] at hgap₁
  rw [hρ₂] at hgap₂
  have hρR := rho_gt_of_bulk_out h2 hr hq'
  have hl₁0 : 0 < l₁ := lt_of_lt_of_le one_pos (one_le_lsq_chT h1 hrq)
  have hcb : |c| ≤ gF L ^ 2 * FSChannel.rho (chT N j q' q) * (piC j (cidx N q) / Mtot sys j) := by
    have := abs_comC_le sys p₀ (gF L) j (cidx N q) (chT N j q' q)
    rw [mul_div_assoc] at this; exact this
  have hab' : |a'| ≤ gF L ^ 2 * FSChannel.rho (chT N j r q') * (piC j (cidx N q) / Mtot sys j) := by
    have := abs_comC_le sys p₀ (gF L) j (cidx N q) (chT N j r q')
    rw [mul_div_assoc] at this; rw [ha'q]; exact this
  have hR0 : (0 : ℝ) < 3 * n / 4 := by positivity
  have hbr := bracket_le (ϖ := ϖ) hg hμ hl₁0 hR0 (div_nonneg hpi hM.le) (FSChannel.rho_nonneg _) hgap₁ hgap₂
    hcb hab' hρ₂ hρR.le
  rw [← hX] at hbr
  have hw1 : ‖wNK sys L N q' r‖ ≤ chC sys L j / l₂ := by
    have := norm_wNK_chan_le (sys := sys) hL (onCh_symm h2) hq'r
    rwa [hl₂e] at this
  have hw2 : ‖wNK sys L N r q‖ ≤ chC sys L j / l₁ := norm_wNK_chan_le hL h1 hrq
  have hl₂0 : 0 < l₂ := by
    have := one_le_lsq_chT (onCh_symm h2) hq'r
    rw [hl₂e] at this
    linarith
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖wNK sys L N q' r‖ * ‖wNK sys L N r q‖ * |a' / d₂ - b / d₁| ≤
      chC sys L j / l₂ * (chC sys L j / l₁) *
        ((piC j (cidx N q) / Mtot sys j) * (6 * muCh sys j * FSChannel.rho (chT N j q' q) +
          36 * muCh sys j ^ 2 * |ϖ| / (gF L ^ 2 * (3 * n / 4))) / l₁) := by
        apply mul_le_mul (mul_le_mul hw1 hw2 (norm_nonneg _) (by positivity)) hbr (abs_nonneg _)
          (by positivity)
    _ = _ := by
        unfold zaA
        rw [hϖ]
        field_simp

open Classical in
/-- **The kernel bound of the symbol current** (`lem:com`, `prop:zsym`): for `n ≥ 8`,
`|z(q', q)| ≤ Σ_j 1{q' on j from q} A_j(q', q) · 611 (4/(3n))³`. -/
theorem norm_zaK_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) (q' q : Cfg eta N) :
    ‖zaK sys L p₀ N n q' q‖ ≤ ∑ j, (if OnCh j (cidx N q') (cidx N q) then
      zaA sys L N n j q' q * (611 / (3 * n / 4) ^ 3) else 0) := by
  classical
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hR : (1 : ℝ) ≤ 3 * n / 4 := by linarith
  have hA : ∀ j, 0 ≤ zaA sys L N n j q' q := fun j => zaA_nonneg hL j q' q
  have hB : 0 ≤ ∑ j, (if OnCh j (cidx N q') (cidx N q) then
      zaA sys L N n j q' q * (611 / (3 * n / 4) ^ 3) else 0) := by
    refine Finset.sum_nonneg fun j _ => ?_
    split_ifs
    · exact mul_nonneg (hA j) (by positivity)
    · exact le_rfl
  unfold zaK
  split_ifs with hQ
  swap
  · rw [norm_zero]; exact hB
  obtain ⟨hq', hq⟩ := hQ
  rw [norm_mul, Complex.norm_I, one_mul]
  set f : Ch eta → Cfg eta N → ℝ := fun j r =>
    if OnCh j (cidx N q') (cidx N q) ∧ (OnCh j (cidx N r) (cidx N q) ∧ ¬ InP (n : ℝ) (cidx N r)) then
      zaA sys L N n j q' q * (1 / FSLattice.lsq (chT N j r q) ^ 2 *
        (1 / FSLattice.lsq (chT N j q' q - chT N j r q))) else 0 with hf
  have hf0 : ∀ j r, 0 ≤ f j r := by
    intro j r
    simp only [hf]
    split_ifs
    · exact mul_nonneg (hA j) (mul_nonneg (div_nonneg zero_le_one (sq_nonneg _))
        (div_nonneg zero_le_one (FSLattice.lsq_nonneg _)))
    · exact le_rfl
  have hterm : ∀ r, ‖(if ¬ InP (n : ℝ) (cidx N r) then
      wNK sys L N q' r * ycK sys L p₀ N r q - ycK sys L p₀ N q' r * wNK sys L N r q else 0)‖ ≤
      ∑ j, f j r := by
    intro r
    by_cases hr : InP (n : ℝ) (cidx N r)
    · rw [if_neg (not_not_intro hr), norm_zero]; exact Finset.sum_nonneg fun j _ => hf0 j r
    rw [if_pos hr]
    by_cases h1 : wNK sys L N q' r = 0
    · rw [h1, ycK_eq_zero_of_wNK h1, zero_mul, zero_mul, sub_zero, norm_zero]
      exact Finset.sum_nonneg fun j _ => hf0 j r
    by_cases h2 : wNK sys L N r q = 0
    · rw [h2, ycK_eq_zero_of_wNK h2, mul_zero, mul_zero, sub_zero, norm_zero]
      exact Finset.sum_nonneg fun j _ => hf0 j r
    obtain ⟨j₁, hj₁⟩ := exists_onCh_of_ne_zero (sys := sys) hL
      (show potKernel sys L (cidx N q') (cidx N r) ≠ 0 from h1)
    obtain ⟨j₂, hj₂⟩ := exists_onCh_of_ne_zero (sys := sys) hL
      (show potKernel sys L (cidx N r) (cidx N q) ≠ 0 from h2)
    have hjj : j₁ = j₂ := same_channel hn0 hq' hq hr hj₁ hj₂
    rw [← hjj] at hj₂
    have hq'q : OnCh j₁ (cidx N q') (cidx N q) := onCh_comp hj₁ hj₂
    refine le_trans ?_ (Finset.single_le_sum (fun j _ => hf0 j r) (Finset.mem_univ j₁))
    simp only [hf, if_pos (show OnCh j₁ (cidx N q') (cidx N q) ∧
      (OnCh j₁ (cidx N r) (cidx N q) ∧ ¬ InP (n : ℝ) (cidx N r)) from ⟨hq'q, hj₂, hr⟩)]
    exact norm_zaK_term_le hL H hKernel hn hq' hq hr hj₂ (onCh_symm hj₁)
  calc ‖∑ r, (if ¬ InP (n : ℝ) (cidx N r) then
        wNK sys L N q' r * ycK sys L p₀ N r q - ycK sys L p₀ N q' r * wNK sys L N r q else 0)‖ ≤
      ∑ r, ‖(if ¬ InP (n : ℝ) (cidx N r) then
        wNK sys L N q' r * ycK sys L p₀ N r q - ycK sys L p₀ N q' r * wNK sys L N r q else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r, ∑ j, f j r := Finset.sum_le_sum fun r _ => hterm r
    _ = ∑ j, ∑ r, f j r := Finset.sum_comm
    _ ≤ _ := by
      refine Finset.sum_le_sum fun j _ => ?_
      by_cases hj : OnCh j (cidx N q') (cidx N q)
      · rw [if_pos hj]
        set T := Finset.univ.filter
          (fun r : Cfg eta N => OnCh j (cidx N r) (cidx N q) ∧ ¬ InP (n : ℝ) (cidx N r)) with hTdef
        have e : ∑ r, f j r = zaA sys L N n j q' q * ∑ r ∈ T,
            (1 / FSLattice.lsq (chT N j r q) ^ 2 * (1 / FSLattice.lsq (chT N j q' q - chT N j r q))) := by
          rw [Finset.mul_sum, hTdef, Finset.sum_filter]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp only [hf, hj, true_and]
        rw [e]
        apply mul_le_mul_of_nonneg_left _ (hA j)
        have hinj : Set.InjOn (fun r => chT N j r q) T := fun r hr r' hr' h =>
          chT_injOn j q (Finset.mem_filter.mp hr).2.1 (Finset.mem_filter.mp hr').2.1 h
        rw [← Finset.sum_image (f := fun μ => 1 / FSLattice.lsq μ ^ 2 *
          (1 / FSLattice.lsq (chT N j q' q - μ))) hinj]
        have hfilt : (T.image fun r => chT N j r q).filter
            (fun μ => (3 * n / 4 : ℝ) ^ 2 < FSLattice.lsq μ) = T.image fun r => chT N j r q := by
          refine Finset.filter_true_of_mem fun μ hμ => ?_
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hμ
          obtain ⟨hon, hrP⟩ := (Finset.mem_filter.mp hr).2
          have hρ := rho_gt_of_bulk_out hon hrP hq
          rw [← FSChannel.rho_sq]
          have : (0 : ℝ) ≤ 3 * n / 4 := by positivity
          nlinarith
        rw [← hfilt]
        exact FSLattice.flat_sum_le _ _ hR
      · rw [if_neg hj]
        exact le_of_eq (Finset.sum_eq_zero fun r _ => by simp only [hf, hj, false_and, if_false])

end ZaKernel

end FSFlux
