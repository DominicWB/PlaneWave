import PlaneWave.Flux.PhaseTools

/-!
# Flux route, part 5: the bulk block of `prop:phase`

The bulk block of the dressed composite `C₁ = W Y₁` (`Y₁ = R Y Q`) is the finite form

  `⟨W 1_Q ψ, Y 1_Q ψ⟩ = Σ_{k', k ∈ Q} conj ψ(k') c₁(k', k) ψ(k)`,
  `c₁(k', k) = Σ_{k''} w(k', k'') Y(k'', k)`                              (`inner_Wlq_YQ`).

Only its imaginary part enters `𝔚` (eq:herm), and that sees the anti-Hermitian kernel

  `c₁(k', k) - conj c₁(k, k') = Σ_{k'' ∉ P} w(k', k'') w(k'', k) (s(k'', k) - s(k'', k'))`
                                                                            (`cK_antiherm`),

with the dressed symbol `s` (both ends in `Q`: the intermediate sets of an element and of its
transpose coincide). By the same-channel lemma both hops use one channel, and by `sY_diff_le`
and eq:flatbd (`flat_tsum2_le`) `|c₁(k', k) - conj c₁(k, k')| ≤ c_j² C_Δ |τ|/n · 455/(3n/4)`
(`norm_cK_antiherm_le`, eq:asymbd). The fibre bound `fibre_grad_le` (eq:paird-grad on `Q`)
then gives **`bulk_im_le`**:

  `|Im ⟨W 1_Q ψ, Y 1_Q ψ⟩| ≤ C n⁻² Z_{2s} (Σ_Q (1+|p|²)^{2s+1} |ψ_p|² + Σ_Q (1+|p|²)^{2s} |ψ_p|²)`.

This holds for the model with fixed nuclei as well (the one-body channels have a constant
dressed symbol, so their anti-Hermitian part vanishes; no reality of the kernels is used).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Bulk

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (p₀ : Fin eta)

/-- The composite kernel of `W Y₁`: `c₁(k', k) = Σ_{k''} w(k', k'') Y(k'', k)`. -/
noncomputable def cK (k' k : Cf eta) : ℂ := ∑' k'', potKernel sys L k' k'' * yK sys L n p₀ k'' k

variable {sys L n}

lemma summable_yK_sq_col (hL : 0 < L) (hn : 2 ≤ n) (p : Cf eta) :
    Summable fun q => ‖yK sys L n p₀ q p‖ ^ 2 := by
  have hj : ∀ j : Ch eta, Summable fun q => kapY (sys := sys) (L := L) (n := n) p₀ j q p ^ 2 :=
    fun j => (col_kapY p₀ hL hn j p).1
  refine ((summable_sum (s := Finset.univ) fun j _ => hj j).mul_left
    (Fintype.card (Ch eta) : ℝ)).of_nonneg_of_le (fun q => sq_nonneg _) fun q => ?_
  have h1 := norm_yK_le_kapY (sys := sys) (n := n) p₀ hL q p
  have h0 : 0 ≤ ∑ j : Ch eta, kapY (sys := sys) (L := L) (n := n) p₀ j q p :=
    Finset.sum_nonneg fun j _ => kapY_nonneg (sys := sys) p₀ j q p
  calc ‖yK sys L n p₀ q p‖ ^ 2 ≤ (∑ j : Ch eta, kapY (sys := sys) (L := L) (n := n) p₀ j q p) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ Fintype.card (Ch eta) * ∑ j : Ch eta, kapY (sys := sys) (L := L) (n := n) p₀ j q p ^ 2 :=
        sq_sum_le_card_mul_sum_sq

lemma summable_cK_term (hL : 0 < L) (hn : 2 ≤ n) (k' k : Cf eta) :
    Summable fun k'' => potKernel sys L k' k'' * yK sys L n p₀ k'' k :=
  summable_mul_of_sq (summable_potKernel_sq_row sys hL k') (summable_yK_sq_col p₀ hL hn k)

variable (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

open Classical in
include hKernel in
/-- **The bulk block as a finite form**:
`⟨W 1_Q ψ, Y 1_Q ψ⟩ = Σ_{k', k ∈ Q} conj ψ(k') c₁(k', k) ψ(k)`. -/
theorem inner_Wlq_YQ (hL : 0 < L) (hn : 2 ≤ n) (x : L2 eta) :
    ⟪Wp sys L H (liftQ L n x), Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)⟫_ℂ =
      ∑ k' ∈ Qs eta n, ∑ k ∈ Qs eta n, conj (x k') * cK sys L n p₀ k' k * x k := by
  rw [lp.inner_eq_tsum]
  have hterm : ∀ k'', ⟪(Wp sys L H (liftQ L n x) : Cf eta → ℂ) k'',
      (Yop sys hL hn p₀ (lpTruncate (Qs eta n) x) : Cf eta → ℂ) k''⟫_ℂ =
      ∑ k' ∈ Qs eta n, ∑ k ∈ Qs eta n,
        conj (x k') * (potKernel sys L k' k'' * yK sys L n p₀ k'' k) * x k := by
    intro k''
    rw [RCLike.inner_apply', potential_liftQ sys H hKernel hL n x k'',
      Yop_truncQ_apply (sys := sys) p₀ hL hn x k'',
      map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← potKernel_conj' hL k'' k']
    ring
  rw [tsum_congr hterm]
  have hs : ∀ k' k, Summable fun k'' =>
      conj (x k') * (potKernel sys L k' k'' * yK sys L n p₀ k'' k) * x k :=
    fun k' k => ((summable_cK_term (sys := sys) p₀ hL hn k' k).mul_left _).mul_right _
  rw [Summable.tsum_finsetSum fun k' _ => summable_sum fun k _ => hs k' k]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [Summable.tsum_finsetSum fun k _ => hs k' k]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold cK
  rw [tsum_mul_right, tsum_mul_left]

omit [Fintype ν] in
/-- On `Q`, the crossings from `p` are the configurations outside the cube. -/
lemma cross_iff_of_inQ {q p : Cf eta} (hp : InQ (n : ℝ) p) : Cross (n : ℝ) q p ↔ ¬ InP (n : ℝ) q := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
    · exact absurd (hp.inP (Nat.cast_nonneg n)) h2
    · exact h1
  · intro h; exact Or.inr ⟨h, hp⟩

open Classical in
/-- **The anti-Hermitian part of the bulk kernel**: for `k, k' ∈ Q`,
`c₁(k', k) - conj c₁(k, k') = Σ_{k'' ∉ P} w(k', k'') w(k'', k) (s(k'', k) - s(k'', k'))`. -/
theorem cK_antiherm (hL : 0 < L) (hn : 2 ≤ n) {k k' : Cf eta} (hk : InQ (n : ℝ) k)
    (hk' : InQ (n : ℝ) k') :
    cK sys L n p₀ k' k - conj (cK sys L n p₀ k k') =
      ∑' k'', (if ¬ InP (n : ℝ) k'' then potKernel sys L k' k'' * potKernel sys L k'' k *
        ((sY sys L p₀ k'' k - sY sys L p₀ k'' k' : ℝ) : ℂ) else 0) := by
  unfold cK
  rw [Complex.conj_tsum]
  have h1 := summable_cK_term (sys := sys) p₀ hL hn k' k
  have h2 : Summable fun k'' => conj (potKernel sys L k k'' * yK sys L n p₀ k'' k') :=
    Complex.summable_conj.mpr (summable_cK_term (sys := sys) p₀ hL hn k k')
  rw [← h1.tsum_sub h2]
  refine tsum_congr fun k'' => ?_
  rw [yK_eq, yK_eq, cross_iff_of_inQ hk, cross_iff_of_inQ hk']
  by_cases hr : InP (n : ℝ) k''
  · rw [if_neg (not_not.mpr hr), if_neg (not_not.mpr hr), if_neg (not_not.mpr hr)]
    simp
  · rw [if_pos hr, if_pos hr, if_pos hr, map_mul, map_mul, ← potKernel_conj' hL k k'',
      ← potKernel_conj' hL k'' k', Complex.conj_ofReal]
    push_cast
    ring

/-- The channel bound of the potential kernel: `|w(q, p)| ≤ c_j |ν|⁻²` on a hop of channel `j`
with transfer `ν ≠ 0`. -/
lemma norm_potKernel_le_ch (hL : 0 < L) {j : Ch eta} {q p : Cf eta} (hj : OnCh j q p)
    (hqp : q ≠ p) :
    ‖potKernel sys L q p‖ ≤ chC sys L j / nsq (q (lead j) - p (lead j)) := by
  classical
  refine (norm_potKernel_le sys hL q p).trans (le_of_eq ?_)
  unfold potMaj
  rw [Finset.sum_eq_single j]
  · unfold chMaj; rw [if_pos hj]; rfl
  · intro j' _ hj'
    unfold chMaj
    rw [if_neg]
    intro hon
    exact hj' (onCh_unique hon hj hqp)
  · intro h; exact absurd (Finset.mem_univ j) h

open Classical in
variable (sys L n) in
/-- The majorant of the anti-Hermitian bulk kernel. -/
noncomputable def bulkMaj (k' k : Cf eta) : ℝ :=
  ∑ j : Ch eta, if OnCh j k' k then chC sys L j ^ 2 * cDel sys L p₀ *
    Real.sqrt (nsq (k' (lead j) - k (lead j))) / n * (455 / (3 * n / 4)) else 0

lemma bulkMaj_nonneg (hL : 0 < L) (k' k : Cf eta) : 0 ≤ bulkMaj sys L n p₀ k' k := by
  classical
  unfold bulkMaj
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · have hcD : 0 ≤ cDel sys L p₀ := by
      unfold cDel cE
      have := cgap_pos sys (gF_pos hL).ne'
      have := sys.mass_pos p₀
      have : 0 ≤ ∑ c : Fin eta, gF L ^ 2 / (2 * sys.mass c) :=
        Finset.sum_nonneg fun c _ => by have := sys.mass_pos c; positivity
      positivity
    have := chC_nonneg sys hL j
    positivity
  · exact le_rfl

open Classical in
/-- **eq:asymbd**: for `k, k' ∈ Q`,
`|c₁(k', k) - conj c₁(k, k')| ≤ Σ_j 1{k' ~_j k} c_j² C_Δ |τ_j|/n · 455/(3n/4)`. -/
theorem norm_cK_antiherm_le (hL : 0 < L) (hn : 2 ≤ n) {k k' : Cf eta} (hk : InQ (n : ℝ) k)
    (hk' : InQ (n : ℝ) k') :
    ‖cK sys L n p₀ k' k - conj (cK sys L n p₀ k k')‖ ≤ bulkMaj sys L n p₀ k' k := by
  classical
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hR : (1 : ℝ) ≤ 3 * n / 4 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [cK_antiherm p₀ hL hn hk hk']
  set f : Cf eta → ℂ := fun k'' => if ¬ InP (n : ℝ) k'' then
    potKernel sys L k' k'' * potKernel sys L k'' k *
      ((sY sys L p₀ k'' k - sY sys L p₀ k'' k' : ℝ) : ℂ) else 0
  -- the channel majorant over the intermediate configuration
  set τ : Ch eta → Lattice3 := fun j => k' (lead j) - k (lead j)
  set cj : Ch eta → ℝ := fun j => chC sys L j ^ 2 * cDel sys L p₀ * Real.sqrt (nsq (τ j)) / n
  have hcj : ∀ j, 0 ≤ cj j := by
    intro j
    have hcD : 0 ≤ cDel sys L p₀ := by
      unfold cDel cE
      have := cgap_pos sys (gF_pos hL).ne'
      have := sys.mass_pos p₀
      have : 0 ≤ ∑ c : Fin eta, gF L ^ 2 / (2 * sys.mass c) :=
        Finset.sum_nonneg fun c _ => by have := sys.mass_pos c; positivity
      positivity
    have := chC_nonneg sys hL j
    simp only [cj]; positivity
  set F : Ch eta → Lattice3 → ℝ := fun j μ =>
    if (3 * n / 4 : ℝ) ^ 2 < lsq μ then 1 / lsq μ * (1 / lsq (τ j - μ)) else 0
  have hF0 : ∀ j μ, 0 ≤ F j μ := by
    intro j μ; simp only [F]; split_ifs
    · have := lsq_nonneg μ; have := lsq_nonneg (τ j - μ); positivity
    · exact le_rfl
  set maj : Cf eta → ℝ := fun k'' => ∑ j : Ch eta,
    if OnCh j k' k then (if OnCh j k'' k then cj j * F j (k'' (lead j) - k (lead j)) else 0) else 0
  have hmaj0 : ∀ k'', 0 ≤ maj k'' := by
    intro k''; refine Finset.sum_nonneg fun j _ => ?_
    split_ifs
    · exact mul_nonneg (hcj j) (hF0 j _)
    · exact le_rfl
    · exact le_rfl
  -- termwise
  have hpt : ∀ k'', ‖f k''‖ ≤ maj k'' := by
    intro k''
    by_cases hr : InP (n : ℝ) k''
    · have : f k'' = 0 := by simp only [f]; rw [if_neg (not_not.mpr hr)]
      rw [this, norm_zero]; exact hmaj0 k''
    · have hf : f k'' = potKernel sys L k' k'' * potKernel sys L k'' k *
          ((sY sys L p₀ k'' k - sY sys L p₀ k'' k' : ℝ) : ℂ) := by
        simp only [f]; rw [if_pos hr]
      rw [hf]
      by_cases h0 : potKernel sys L k' k'' = 0 ∨ potKernel sys L k'' k = 0
      · rcases h0 with h0 | h0
        · rw [h0, zero_mul, zero_mul, norm_zero]; exact hmaj0 k''
        · rw [h0, mul_zero, zero_mul, norm_zero]; exact hmaj0 k''
      · push Not at h0
        obtain ⟨j₁, hj₁⟩ := exists_onCh_of_ne_zero hL h0.1
        obtain ⟨j₂, hj₂⟩ := exists_onCh_of_ne_zero hL h0.2
        have hjj := same_channel (by exact_mod_cast hn0) hk' hk hr hj₁ hj₂
        subst hjj
        set j := j₁
        have hkk : OnCh j k' k := onCh_trans hj₂ (onCh_symm hj₁)
        have hc2 : Cross (n : ℝ) k'' k := Or.inr ⟨hr, hk⟩
        obtain ⟨g1, -⟩ := channel_gap sys (gF_pos hL).ne' hnr hj₂ hc2
        have hne1 : k' ≠ k'' := by
          intro h; apply hr; rw [← h]; exact hk'.inP (Nat.cast_nonneg n)
        have hne2 : k'' ≠ k := by
          intro h; apply hr; rw [h]; exact hk.inP (Nat.cast_nonneg n)
        have hw1 := norm_potKernel_le_ch (sys := sys) hL hj₁ hne1
        have hw2 := norm_potKernel_le_ch (sys := sys) hL hj₂ hne2
        have hs := sY_diff_le (sys := sys) p₀ hL hn0 hk hk' hr hj₂ (onCh_symm hj₁)
        have e1 : k' (lead j) - k'' (lead j) = τ j - (k'' (lead j) - k (lead j)) := by
          simp only [τ]; abel
        rw [e1] at hw1
        set ν := k'' (lead j) - k (lead j)
        have hν0 : 0 < nsq ν := lt_of_le_of_lt (sq_nonneg _) g1
        have hmaj : cj j * F j ν ≤ maj k'' := by
          have := Finset.single_le_sum (f := fun j' : Ch eta =>
            if OnCh j' k' k then (if OnCh j' k'' k then cj j' * F j' (k'' (lead j') - k (lead j'))
              else 0) else 0)
            (fun j' _ => by
              show 0 ≤ (if OnCh j' k' k then (if OnCh j' k'' k then
                cj j' * F j' (k'' (lead j') - k (lead j')) else 0) else 0)
              split_ifs
              · exact mul_nonneg (hcj j') (hF0 j' _)
              · exact le_rfl
              · exact le_rfl) (Finset.mem_univ j)
          simp only [if_pos hkk, if_pos hj₂] at this
          exact this
        refine le_trans ?_ hmaj
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hFv : F j ν = 1 / nsq ν * (1 / nsq (τ j - ν)) := by
          simp only [F]; rw [if_pos (by exact g1)]; rfl
        rw [hFv]
        have hcj' : cj j = chC sys L j ^ 2 * (cDel sys L p₀ * Real.sqrt (nsq (τ j)) / n) := by
          simp only [cj]; ring
        rw [hcj']
        have hch := chC_nonneg sys hL j
        calc ‖potKernel sys L k' k''‖ * ‖potKernel sys L k'' k‖ *
              |sY sys L p₀ k'' k - sY sys L p₀ k'' k'|
            ≤ chC sys L j / nsq (τ j - ν) * (chC sys L j / nsq ν) *
                (cDel sys L p₀ * Real.sqrt (nsq (τ j)) / n) := by
              refine mul_le_mul (mul_le_mul hw1 hw2 (norm_nonneg _)
                (div_nonneg hch (nsq_nonneg _))) hs (abs_nonneg _)
                (mul_nonneg (div_nonneg hch (nsq_nonneg _)) (div_nonneg hch (nsq_nonneg _)))
          _ = chC sys L j ^ 2 * (cDel sys L p₀ * Real.sqrt (nsq (τ j)) / n) *
                (1 / nsq ν * (1 / nsq (τ j - ν))) := by ring
  -- the majorant series
  have hsF : ∀ j, Summable (F j) ∧ ∑' μ, F j μ ≤ 455 / (3 * n / 4) := fun j => flat_tsum2_le (τ j) hR
  have hsj : ∀ j, Summable fun k'' => (if OnCh j k' k then
      (if OnCh j k'' k then cj j * F j (k'' (lead j) - k (lead j)) else 0) else 0) := by
    intro j
    split_ifs
    · rw [summable_col_iff]
      simp only [lead_add_tr]
      exact (hsF j).1.mul_left _
    · exact summable_zero
  have hsmaj : Summable maj := summable_sum fun j _ => hsj j
  have hsf : Summable fun k'' => ‖f k''‖ := hsmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hpt
  calc ‖∑' k'', f k''‖ ≤ ∑' k'', ‖f k''‖ := norm_tsum_le_tsum_norm hsf
    _ ≤ ∑' k'', maj k'' := hsf.tsum_le_tsum hpt hsmaj
    _ = ∑ j : Ch eta, ∑' k'', (if OnCh j k' k then
          (if OnCh j k'' k then cj j * F j (k'' (lead j) - k (lead j)) else 0) else 0) :=
        Summable.tsum_finsetSum fun j _ => hsj j
    _ ≤ bulkMaj sys L n p₀ k' k := by
        unfold bulkMaj
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs with hkk
        · rw [tsum_col, tsum_mul_left]
          simp only [lead_add_tr]
          have := mul_le_mul_of_nonneg_left (hsF j).2 (hcj j)
          simp only [cj] at this ⊢
          linarith
        · simp

/-! ## The fibre gradient bound and the bulk estimate -/

omit [Fintype ν] in
lemma sqrt_nsq_sub_le (k k' : Cf eta) (a : Fin eta) :
    Real.sqrt (nsq (k' a - k a)) ≤ Real.sqrt (lsqC k') + Real.sqrt (lsqC k) := by
  have h1 := rho_add_le (k' a) (-(k a))
  rw [← sub_eq_add_neg, rho_neg'] at h1
  have h2 : rho (k' a) ≤ Real.sqrt (lsqC k') := by
    unfold rho
    apply Real.sqrt_le_sqrt
    unfold lsqC
    exact Finset.single_le_sum (f := fun c => nsq (k' c)) (fun _ _ => nsq_nonneg _)
      (Finset.mem_univ a)
  have h3 : rho (k a) ≤ Real.sqrt (lsqC k) := by
    unfold rho
    apply Real.sqrt_le_sqrt
    unfold lsqC
    exact Finset.single_le_sum (f := fun c => nsq (k c)) (fun _ _ => nsq_nonneg _)
      (Finset.mem_univ a)
  change rho (k' a - k a) ≤ _
  linarith

open Classical in
omit [Fintype ν] in
/-- **eq:paird-grad on the bulk block** (fibre form): for `s > 3/4`,
`Σ_{k' ~_j k} |x(k')| |τ| |x(k)| ≤ Z_{2s} (Σ_Q (1+|p|²)^{2s+1} |x_p|² + Σ_Q (1+|p|²)^{2s} |x_p|²)`. -/
theorem fibre_grad_le (j : Ch eta) {s : ℝ} (hs : 3 / 4 < s) (x : Cf eta → ℂ) :
    ∑ k' ∈ Qs eta n, ∑ k ∈ Qs eta n, (if OnCh j k' k then
        ‖x k'‖ * Real.sqrt (nsq (k' (lead j) - k (lead j))) * ‖x k‖ else 0) ≤
      (1 + 26 * (1 + 1 / (2 * (2 * s) - 3))) *
        (∑ p ∈ Qs eta n, Ws (s + 1 / 2) p * ‖x p‖ ^ 2 + ∑ p ∈ Qs eta n, Ws s p * ‖x p‖ ^ 2) := by
  classical
  set N : ℝ := 1 + 26 * (1 + 1 / (2 * (2 * s) - 3))
  set F := Qs eta n
  have hN1 : ∀ k' ∈ F, ∑ k ∈ F.filter (fun k => OnCh j k' k), (Ws s k)⁻¹ ≤ N := by
    intro k' _
    have e : F.filter (fun k => OnCh j k' k) = F.filter (fun k => OnCh j k k') :=
      Finset.filter_congr fun k _ => ⟨onCh_symm, onCh_symm⟩
    rw [e]
    exact fibre_weight_le n j k' hs
  have hN2 : ∀ k ∈ F, ∑ k' ∈ F.filter (fun k' => OnCh j k' k), (Ws s k')⁻¹ ≤ N :=
    fun k _ => fibre_weight_le n j k hs
  set f : Cf eta → ℝ := fun p => Real.sqrt (lsqC p) * ‖x p‖
  set g : Cf eta → ℝ := fun p => ‖x p‖
  have hA := fibre_amgm F (fun k' k => OnCh j k' k) (Ws s) (Ws_pos s) hN1 hN2 f g
  have hB := fibre_amgm F (fun k' k => OnCh j k' k) (Ws s) (Ws_pos s) hN1 hN2 g f
  have hpt : ∀ k' k, (if OnCh j k' k then
      ‖x k'‖ * Real.sqrt (nsq (k' (lead j) - k (lead j))) * ‖x k‖ else 0) ≤
      (if OnCh j k' k then f k' * g k else 0) + (if OnCh j k' k then g k' * f k else 0) := by
    intro k' k
    split_ifs
    · have h := sqrt_nsq_sub_le k k' (lead j)
      have hx1 := norm_nonneg (x k')
      have hx2 := norm_nonneg (x k)
      simp only [f, g]
      nlinarith [mul_nonneg hx1 hx2]
    · simp
  have hWs : ∀ p, Ws s p * f p ^ 2 ≤ Ws (s + 1 / 2) p * ‖x p‖ ^ 2 := by
    intro p
    have hl := lsqC_nonneg p
    have hb : 0 < 1 + lsqC p := by linarith
    have e : Ws (s + 1 / 2) p = Ws s p * (1 + lsqC p) := by
      unfold Ws
      rw [show 2 * (s + 1 / 2) = 2 * s + 1 by ring, Real.rpow_add hb, Real.rpow_one]
    rw [e]
    simp only [f]
    rw [mul_pow, Real.sq_sqrt hl]
    have := (Ws_pos s p).le
    nlinarith [sq_nonneg ‖x p‖]
  have hsum : ∑ p ∈ F, Ws s p * f p ^ 2 ≤ ∑ p ∈ F, Ws (s + 1 / 2) p * ‖x p‖ ^ 2 :=
    Finset.sum_le_sum fun p _ => hWs p
  calc _ ≤ ∑ k' ∈ F, ∑ k ∈ F, ((if OnCh j k' k then f k' * g k else 0) +
        (if OnCh j k' k then g k' * f k else 0)) :=
        Finset.sum_le_sum fun k' _ => Finset.sum_le_sum fun k _ => hpt k' k
    _ = ∑ k' ∈ F, ∑ k ∈ F, (if OnCh j k' k then f k' * g k else 0) +
          ∑ k' ∈ F, ∑ k ∈ F, (if OnCh j k' k then g k' * f k else 0) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ N / 2 * (∑ p ∈ F, Ws s p * f p ^ 2 + ∑ p ∈ F, Ws s p * g p ^ 2) +
          N / 2 * (∑ p ∈ F, Ws s p * g p ^ 2 + ∑ p ∈ F, Ws s p * f p ^ 2) := add_le_add hA hB
    _ = N * (∑ p ∈ F, Ws s p * f p ^ 2 + ∑ p ∈ F, Ws s p * ‖x p‖ ^ 2) := by simp only [g]; ring
    _ ≤ N * (∑ p ∈ F, Ws (s + 1 / 2) p * ‖x p‖ ^ 2 + ∑ p ∈ F, Ws s p * ‖x p‖ ^ 2) := by
        have hN : 0 ≤ N := by
          have : 0 < 2 * (2 * s) - 3 := by linarith
          positivity
        gcongr

omit [Fintype ν] in
/-- The imaginary part of a finite form sees only the anti-Hermitian part of its kernel. -/
lemma abs_im_form_le {ι : Type*} (F : Finset ι) (x : ι → ℂ) (c : ι → ι → ℂ) :
    |(∑ k' ∈ F, ∑ k ∈ F, conj (x k') * c k' k * x k).im| ≤
      1 / 2 * ∑ k' ∈ F, ∑ k ∈ F, ‖x k'‖ * ‖c k' k - conj (c k k')‖ * ‖x k‖ := by
  set Z := ∑ k' ∈ F, ∑ k ∈ F, conj (x k') * c k' k * x k
  have hconj : conj Z = ∑ k' ∈ F, ∑ k ∈ F, conj (x k') * conj (c k k') * x k := by
    simp only [Z, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hdiff : Z - conj Z = ∑ k' ∈ F, ∑ k ∈ F, conj (x k') * (c k' k - conj (c k k')) * x k := by
    rw [hconj, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hnorm : ‖Z - conj Z‖ = 2 * |Z.im| := by
    rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_two]
  have hle : ‖Z - conj Z‖ ≤ ∑ k' ∈ F, ∑ k ∈ F, ‖x k'‖ * ‖c k' k - conj (c k k')‖ * ‖x k‖ := by
    rw [hdiff]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k' _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj]
  rw [hnorm] at hle
  linarith

variable (sys L n) in
/-- The bulk constant `C_b = Σ_j c_j² C_Δ · 455 · 4/3`. -/
noncomputable def cBulk : ℝ := ∑ j : Ch eta, chC sys L j ^ 2 * cDel sys L p₀ * (455 * 4 / 3)

open Classical in
include hKernel in
/-- **The bulk block of `prop:phase`**: for `s > 3/4`,
`|Im ⟨W 1_Q ψ, Y 1_Q ψ⟩| ≤ (C_b Z_{2s}/(2 n²)) (Σ_Q (1+|p|²)^{2s+1} |ψ_p|² + Σ_Q (1+|p|²)^{2s} |ψ_p|²)`. -/
theorem bulk_im_le (hL : 0 < L) (hn : 2 ≤ n) {s : ℝ} (hs : 3 / 4 < s) (x : L2 eta) :
    |(⟪Wp sys L H (liftQ L n x), Yop sys hL hn p₀ (lpTruncate (Qs eta n) x)⟫_ℂ).im| ≤
      cBulk sys L p₀ / (2 * n ^ 2) * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3))) *
        (∑ p ∈ Qs eta n, Ws (s + 1 / 2) p * ‖x p‖ ^ 2 + ∑ p ∈ Qs eta n, Ws s p * ‖x p‖ ^ 2) := by
  classical
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [inner_Wlq_YQ p₀ H hKernel hL hn x]
  refine (abs_im_form_le _ _ _).trans ?_
  set F := Qs eta n
  set N : ℝ := 1 + 26 * (1 + 1 / (2 * (2 * s) - 3))
  set B := ∑ p ∈ F, Ws (s + 1 / 2) p * ‖x p‖ ^ 2 + ∑ p ∈ F, Ws s p * ‖x p‖ ^ 2
  have hpt : ∀ k' ∈ F, ∀ k ∈ F, ‖x k'‖ * ‖cK sys L n p₀ k' k - conj (cK sys L n p₀ k k')‖ * ‖x k‖ ≤
      ‖x k'‖ * bulkMaj sys L n p₀ k' k * ‖x k‖ := by
    intro k' hk' k hk
    have h := norm_cK_antiherm_le (sys := sys) p₀ hL hn (mem_Qs.mp hk) (mem_Qs.mp hk')
    have := norm_nonneg (x k')
    have := norm_nonneg (x k)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (norm_nonneg _)) (norm_nonneg _)
  have hexp : ∀ k' k, ‖x k'‖ * bulkMaj sys L n p₀ k' k * ‖x k‖ =
      ∑ j : Ch eta, chC sys L j ^ 2 * cDel sys L p₀ * (455 * 4 / 3) / n ^ 2 *
        (if OnCh j k' k then ‖x k'‖ * Real.sqrt (nsq (k' (lead j) - k (lead j))) * ‖x k‖ else 0) := by
    intro k' k
    unfold bulkMaj
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · field_simp
    · ring
  have hfib : ∀ j : Ch eta, ∑ k' ∈ F, ∑ k ∈ F, (if OnCh j k' k then
      ‖x k'‖ * Real.sqrt (nsq (k' (lead j) - k (lead j))) * ‖x k‖ else 0) ≤ N * B :=
    fun j => fibre_grad_le j hs x
  have hcj : ∀ j : Ch eta, 0 ≤ chC sys L j ^ 2 * cDel sys L p₀ * (455 * 4 / 3) / n ^ 2 := by
    intro j
    have hcD : 0 ≤ cDel sys L p₀ := by
      unfold cDel cE
      have := cgap_pos sys (gF_pos hL).ne'
      have := sys.mass_pos p₀
      have : 0 ≤ ∑ c : Fin eta, gF L ^ 2 / (2 * sys.mass c) :=
        Finset.sum_nonneg fun c _ => by have := sys.mass_pos c; positivity
      positivity
    positivity
  calc 1 / 2 * ∑ k' ∈ F, ∑ k ∈ F, ‖x k'‖ * ‖cK sys L n p₀ k' k - conj (cK sys L n p₀ k k')‖ * ‖x k‖
      ≤ 1 / 2 * ∑ k' ∈ F, ∑ k ∈ F, ‖x k'‖ * bulkMaj sys L n p₀ k' k * ‖x k‖ := by
        gcongr with k' hk' k hk
        exact norm_cK_antiherm_le (sys := sys) p₀ hL hn (mem_Qs.mp hk) (mem_Qs.mp hk')
    _ = 1 / 2 * ∑ j : Ch eta, chC sys L j ^ 2 * cDel sys L p₀ * (455 * 4 / 3) / n ^ 2 *
          ∑ k' ∈ F, ∑ k ∈ F, (if OnCh j k' k then
            ‖x k'‖ * Real.sqrt (nsq (k' (lead j) - k (lead j))) * ‖x k‖ else 0) := by
        congr 1
        simp_rw [hexp]
        rw [Finset.sum_congr rfl (fun k' _ => Finset.sum_comm), Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k' _ => ?_
        rw [Finset.mul_sum]
    _ ≤ 1 / 2 * ∑ j : Ch eta, chC sys L j ^ 2 * cDel sys L p₀ * (455 * 4 / 3) / n ^ 2 * (N * B) := by
        gcongr with j
        · exact hcj j
        · exact hfib j
    _ = cBulk sys L p₀ / (2 * n ^ 2) * N * B := by
        unfold cBulk
        rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.sum_mul]
        ring

end Bulk

end FSFlux
