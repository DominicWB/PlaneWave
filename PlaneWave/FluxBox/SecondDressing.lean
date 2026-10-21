import PlaneWave.FluxBox.KineticFloor

/-!
# Flux route, stage 2, part 17: the second dressing `Y₂`

The part of the symbol current above the kinetic floor is eliminated by

  `Y₂ = divK_E(-i z^>)`,  `i[T, Y₂] = Z^>`                                  (`comm_Y2N`),

`Y₂` symmetric (`Y2N_symm`). On a pair above the floor, `|ϖ| ≥ g²|τ|²/(8μ_j)` turns the kernel
bound of `PlaneWave.FluxBox.SymbolCurrentKernel` into

  `|y₂(q', q)| ≤ Σ_j 1{q' on j from q, q' ≠ q, q, q' ∈ Q} 84 μ_j² c_j² |Π_j(q)| /(g² M̄_j |τ|) · 611 (4/(3n))³`
                                                                            (`norm_y2K_le`).

* The fibre trace bound on the box restricted to `Q` (`chan_trace_Q_le`, from `fibre_amgm` and the
  cube sum of `(1 + |x|²)^{-3/2}`) gives the endpoint
  `|⟨u, Y₂ u⟩| ≤ Σ_j C_j 125 (log₂ n + 2) √2 c_X² M²` (`norm_Y2_form_good`), `C_j ~ n⁻³`.
* The crude operator bound `‖Y₂ v‖ ≤ R₂ ‖v‖`, `R₂ = Σ_j C_j (n/2)(n + 1)³ ~ n` (`norm_Y2N_le`), for
  the out-of-box term `e_{Y₂}`.
* **`ledger_za`**: `∫ Re⟨u, Z_a u⟩ = ∫ Re⟨u, Z^≤ u⟩ + [Re⟨u, Y₂ u⟩] - ∫ Re⟨u, i[W, Y₂] u⟩ - ∫ e_{Y₂}`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The second dressing -/

section Y2

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ)

/-- The kernel of the second dressing `Y₂ = Z^>/(iω)`. -/
noncomputable def y2K (q' q : Cfg eta N) : ℂ :=
  FSKernel.divK (Asym sys L N) (fun q' q => -Complex.I * zaGt sys L p₀ N n q' q) q' q

/-- The second dressing on the box. -/
noncomputable abbrev Y2N : En eta N →ₗ[ℂ] En eta N := FSKernel.kop (y2K sys L p₀ N n)

variable {sys L p₀ N n}

omit [Fintype ν] in
/-- Above the kinetic floor the mismatch does not vanish. -/
lemma kinC_ne (hL : 0 < L) {q' q : Cfg eta N} (h : kinC sys L N q' q) :
    Asym sys L N q' ≠ Asym sys L N q := by
  obtain ⟨hne, j, hj, hfl⟩ := h
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hl := one_le_lsq_chT hj hne
  intro heq
  rw [heq, sub_self, abs_zero] at hfl
  have hl0 : 0 < FSLattice.lsq (chT N j q' q) := by linarith
  have : 0 < gF L ^ 2 * FSLattice.lsq (chT N j q' q) / (8 * muCh sys j) := by positivity
  linarith

/-- **The second homological equation** `i[T_N, Y₂] = Z^>`. -/
theorem comm_Y2N (hL : 0 < L) :
    Complex.I • (TN sys L N ∘ₗ Y2N sys L p₀ N n - Y2N sys L p₀ N n ∘ₗ TN sys L N) =
      FSKernel.kop (zaGt sys L p₀ N n) := by
  have h := FSKernel.comm_divK (Asym sys L N) (fun q p => -Complex.I * zaGt sys L p₀ N n q p) (by
    intro q p hqp
    unfold zaGt
    split_ifs with hk
    · exact absurd hqp (kinC_ne hL hk)
    · simp)
  have e : Y2N sys L p₀ N n = FSKernel.kop (FSKernel.divK (Asym sys L N)
      (fun q p => -Complex.I * zaGt sys L p₀ N n q p)) := rfl
  rw [e]
  change Complex.I • (FSKernel.dg (fun q => (Asym sys L N q : ℂ)) ∘ₗ _ - _ ∘ₗ
    FSKernel.dg (fun q => (Asym sys L N q : ℂ))) = _
  rw [h, ← FSKernel.kop_smul]
  congr 1
  funext q p
  simp only [Pi.smul_apply, smul_eq_mul]
  have hI : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [← mul_assoc, hI, one_mul]

lemma y2K_conj (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (q' q : Cfg eta N) : y2K sys L p₀ N n q q' = conj (y2K sys L p₀ N n q' q) := by
  unfold y2K FSKernel.divK
  dsimp only
  by_cases h : Asym sys L N q' = Asym sys L N q
  · rw [if_pos h.symm, if_pos h]; simp
  · rw [if_neg (Ne.symm h), if_neg h, zaGt_conj hL H hKernel q' q, map_div₀, map_mul, map_neg,
      Complex.conj_I, Complex.conj_ofReal]
    have hd : ((Asym sys L N q' - Asym sys L N q : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr h
    have hd' : ((Asym sys L N q - Asym sys L N q' : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (Ne.symm h)
    rw [div_eq_div_iff hd' hd]
    push_cast
    ring

lemma Y2N_symm (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    (Y2N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N).IsSymmetric :=
  FSKernel.kop_symm _ fun q p => y2K_conj (p₀ := p₀) (n := n) hL H hKernel q p

end Y2

/-! ## The kernel bound of `Y₂` -/

section Y2Kernel

variable (sys : CoulombSystem eta ν) (L : ℝ) (N n : ℕ)

/-- The kernel constant of `Y₂`: `84 μ_j² c_j²/(g² M̄_j) · 611 (4/(3n))³`. -/
noncomputable def y2C (j : Ch eta) : ℝ :=
  84 * muCh sys j ^ 2 * chC sys L j ^ 2 / (gF L ^ 2 * Mtot sys j) * (611 / (3 * n / 4) ^ 3)

open Classical in
/-- The majorant of `y₂` on channel `j`. -/
noncomputable def y2M (j : Ch eta) (q' q : Cfg eta N) : ℝ :=
  if OnCh j (cidx N q') (cidx N q) ∧ q' ≠ q ∧ InQ (n : ℝ) (cidx N q') ∧ InQ (n : ℝ) (cidx N q) then
    y2C sys L n j * piC j (cidx N q) / FSChannel.rho (chT N j q' q)
  else 0

variable {sys L N n}

lemma y2C_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ y2C sys L n j := by
  unfold y2C
  have := muCh_pos sys j; have := Mtot_pos sys j; have := chC_nonneg sys hL j; have := gF_pos hL
  positivity

lemma y2M_nonneg (hL : 0 < L) (j : Ch eta) (q' q : Cfg eta N) : 0 ≤ y2M sys L N n j q' q := by
  unfold y2M
  split_ifs
  · have := y2C_nonneg (sys := sys) (n := n) hL j
    have := piC_nonneg j (cidx N q)
    have := FSChannel.rho_nonneg (chT N j q' q)
    positivity
  · exact le_rfl

lemma y2M_symm (j : Ch eta) (q' q : Cfg eta N) : y2M sys L N n j q' q = y2M sys L N n j q q' := by
  classical
  unfold y2M
  by_cases h : OnCh j (cidx N q') (cidx N q)
  · have h' := onCh_symm h
    rw [piC_onCh h, chT_swap j q' q]
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨-, hne, hq', hq⟩; exact ⟨h', hne.symm, hq, hq'⟩
    · rintro ⟨-, hne, hq, hq'⟩; exact ⟨h, hne.symm, hq', hq⟩
  · have h' : ¬ OnCh j (cidx N q) (cidx N q') := fun h' => h (onCh_symm h')
    rw [if_neg (fun hh => h hh.1), if_neg (fun hh => h' hh.1)]

omit [Fintype ν] in
/-- The arithmetic of the dressed bound: above the floor
`6μρ + 36μ²ϖ/(g²R) ≤ 84 μ² ϖ/(g²ρ)` (`ρ ≤ R`). -/
lemma y2_arith {μ g ρ R ϖ : ℝ} (hμ : 0 < μ) (hg : 0 < g) (hρ : 0 < ρ) (hρR : ρ ≤ R)
    (hfl : g ^ 2 * ρ ^ 2 / (8 * μ) ≤ ϖ) :
    6 * μ * ρ + 36 * μ ^ 2 * ϖ / (g ^ 2 * R) ≤ 84 * μ ^ 2 * ϖ / (g ^ 2 * ρ) := by
  have hϖ0 : 0 ≤ ϖ := le_trans (by positivity) hfl
  have hR : 0 < R := lt_of_lt_of_le hρ hρR
  have h1 : 6 * μ * ρ ≤ 48 * μ ^ 2 * ϖ / (g ^ 2 * ρ) := by
    rw [le_div_iff₀ (by positivity)]
    have : g ^ 2 * ρ ^ 2 ≤ 8 * μ * ϖ := by
      rw [div_le_iff₀ (by positivity)] at hfl; linarith
    nlinarith
  have h2 : 36 * μ ^ 2 * ϖ / (g ^ 2 * R) ≤ 36 * μ ^ 2 * ϖ / (g ^ 2 * ρ) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hρR (by positivity))
  have e : 48 * μ ^ 2 * ϖ / (g ^ 2 * ρ) + 36 * μ ^ 2 * ϖ / (g ^ 2 * ρ) =
      84 * μ ^ 2 * ϖ / (g ^ 2 * ρ) := by ring
  linarith

/-- **The kernel bound of the second dressing**: `|y₂(q', q)| ≤ Σ_j M_j(q', q)`. -/
theorem norm_y2K_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {p₀ : Fin eta} (hn : 8 ≤ n) (q' q : Cfg eta N) :
    ‖y2K sys L p₀ N n q' q‖ ≤ ∑ j, y2M sys L N n j q' q := by
  classical
  have hM0 : 0 ≤ ∑ j, y2M sys L N n j q' q := Finset.sum_nonneg fun j _ => y2M_nonneg hL j q' q
  unfold y2K FSKernel.divK
  dsimp only
  split_ifs with hE
  · rw [norm_zero]; exact hM0
  unfold zaGt
  split_ifs with hk
  swap
  · rw [mul_zero, zero_div, norm_zero]; exact hM0
  by_cases hQ : InQ (n : ℝ) (cidx N q') ∧ InQ (n : ℝ) (cidx N q)
  swap
  · have : zaK sys L p₀ N n q' q = 0 := by unfold zaK; rw [if_neg hQ]
    rw [this, mul_zero, zero_div, norm_zero]; exact hM0
  obtain ⟨hq', hq⟩ := hQ
  have hd : 0 < |Asym sys L N q' - Asym sys L N q| := abs_pos.mpr (sub_ne_zero.mpr hE)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_neg, Complex.norm_I, one_mul,
    div_le_iff₀ hd]
  refine (norm_zaK_le hL H hKernel hn q' q).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with hj
  swap
  · exact mul_nonneg (y2M_nonneg hL j q' q) hd.le
  obtain ⟨hne, j₁, hj₁, hfl⟩ := hk
  have hne' : cidx N q' ≠ cidx N q := fun h => hne (finiteConfigLatticeIndex_injective eta N h)
  have hjj : j₁ = j := onCh_unique hj₁ hj hne'
  rw [hjj] at hfl
  have hcond : OnCh j (cidx N q') (cidx N q) ∧ q' ≠ q ∧ InQ (n : ℝ) (cidx N q') ∧
      InQ (n : ℝ) (cidx N q) := ⟨hj, hne, hq', hq⟩
  unfold y2M
  rw [if_pos hcond]
  -- the arithmetic
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hMt := Mtot_pos sys j
  have hpi := piC_nonneg j (cidx N q)
  have hcC := chC_nonneg sys hL j
  set ρ := FSChannel.rho (chT N j q' q) with hρdef
  have hρsq : ρ ^ 2 = FSLattice.lsq (chT N j q' q) := FSChannel.rho_sq _
  have hρ1 : 1 ≤ ρ := by
    have hl := one_le_lsq_chT hj hne
    rw [← hρsq] at hl
    nlinarith [FSChannel.rho_nonneg (chT N j q' q)]
  have hρ0 : 0 < ρ := by linarith
  have hρn : ρ ≤ 3 * n / 4 := by
    have hl := lsq_chT_le_box (j := j) hq' hq
    rw [← hρsq] at hl
    nlinarith
  rw [← hρsq] at hfl
  have key := y2_arith hμ hg hρ0 hρn hfl
  unfold zaA y2C
  rw [← hρdef]
  set ϖ := |Asym sys L N q' - Asym sys L N q|
  have hc : 0 ≤ chC sys L j ^ 2 * (piC j (cidx N q) / Mtot sys j) * (611 / (3 * n / 4) ^ 3) := by
    positivity
  calc chC sys L j ^ 2 * (piC j (cidx N q) / Mtot sys j) *
        (6 * muCh sys j * ρ + 36 * muCh sys j ^ 2 * ϖ / (gF L ^ 2 * (3 * n / 4))) *
        (611 / (3 * n / 4) ^ 3) =
      chC sys L j ^ 2 * (piC j (cidx N q) / Mtot sys j) * (611 / (3 * n / 4) ^ 3) *
        (6 * muCh sys j * ρ + 36 * muCh sys j ^ 2 * ϖ / (gF L ^ 2 * (3 * n / 4))) := by ring
    _ ≤ chC sys L j ^ 2 * (piC j (cidx N q) / Mtot sys j) * (611 / (3 * n / 4) ^ 3) *
        (84 * muCh sys j ^ 2 * ϖ / (gF L ^ 2 * ρ)) := mul_le_mul_of_nonneg_left key hc
    _ = _ := by field_simp

end Y2Kernel

/-! ## The fibre trace bound on the bulk ball -/

section TraceQ

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

omit [Fintype ν] in
/-- The ball count: `#T ≤ (2√Y + 1)³` when every `τ ∈ T` has `|τ|² ≤ Y`. -/
lemma card_ball_le (T : Finset Lattice3) {Y : ℝ} (hY : 0 ≤ Y)
    (hT : ∀ τ ∈ T, FSLattice.lsq τ ≤ Y) : (T.card : ℝ) ≤ (2 * Real.sqrt Y + 1) ^ 3 := by
  have hsub : T ⊆ FSLattice.box ⌊Real.sqrt Y⌋₊ := fun τ hτ =>
    FSLattice.mem_box_floor_of_lsq_le (Real.sqrt_nonneg Y)
      (by rw [Real.sq_sqrt hY]; exact hT τ hτ)
  have h1 := Finset.card_le_card hsub
  rw [FSLattice.card_box] at h1
  have h1' : (T.card : ℝ) ≤ ((2 * ⌊Real.sqrt Y⌋₊ + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast h1
  have hfl := Nat.floor_le (Real.sqrt_nonneg Y)
  have h2 : ((2 * ⌊Real.sqrt Y⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt Y + 1 := by
    push_cast; linarith
  exact h1'.trans (pow_le_pow_left₀ (by positivity) h2 3)

omit [Fintype ν] in
/-- On the bulk ball the pair momentum is at most `n/2`. -/
lemma piC_le_of_inQ {j : Ch eta} {k : Cf eta} (hk : InQ (n : ℝ) k) : piC j k ≤ n / 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  cases j with
  | inl a => simp only [piC]; positivity
  | inr pr =>
    simp only [piC]
    have h1 := FSChannel.rho_add_le (k pr.1.1) (k pr.1.2)
    have h2 := rho_le_of_inQ hn hk pr.1.1
    have h3 := rho_le_of_inQ hn hk pr.1.2
    linarith

omit [Fintype ν] in
open Classical in
/-- The fibre sums of `1/wl` over the bulk ball of the box. -/
lemma fibre_wl_Q_le (hn : 1 ≤ n) (j : Ch eta) (q : Cfg eta N) :
    ∑ p ∈ (Finset.univ.filter (fun p : Cfg eta N => InQ (n : ℝ) (cidx N p))).filter
      (fun p => OnCh j (cidx N q) (cidx N p)), (wl j p)⁻¹ ≤ 125 * (Nat.log 2 n + 2) := by
  classical
  set F := (Finset.univ.filter (fun p : Cfg eta N => InQ (n : ℝ) (cidx N p))).filter
      (fun p => OnCh j (cidx N q) (cidx N p))
  have hinj : Set.InjOn (fun p : Cfg eta N => cidx N p (lead j)) F := by
    intro p hp p' hp' h
    have h1 : OnCh j (cidx N p) (cidx N q) := onCh_symm (Finset.mem_filter.mp hp).2
    have h2 : OnCh j (cidx N p') (cidx N q) := onCh_symm (Finset.mem_filter.mp hp').2
    apply chT_injOn j q h1 h2
    show cidx N p (lead j) - cidx N q (lead j) = cidx N p' (lead j) - cidx N q (lead j)
    rw [show cidx N p (lead j) = cidx N p' (lead j) from h]
  have e : ∑ p ∈ F, (wl j p)⁻¹ = ∑ x ∈ F.image (fun p : Cfg eta N => cidx N p (lead j)), (w32 x)⁻¹ := by
    rw [Finset.sum_image hinj]; rfl
  rw [e]
  apply sum_box_inv32_le hn
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  have hpQ : InQ (n : ℝ) (cidx N p) := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have h1 : FSLattice.lsq (cidx N p (lead j)) ≤ ((n : ℝ) / 4) ^ 2 := hpQ (lead j)
  have : ((n : ℝ) / 4) ^ 2 ≤ 3 * (n : ℝ) ^ 2 := by nlinarith [sq_nonneg (n : ℝ)]
  linarith

omit [Fintype ν] in
open Classical in
/-- **The fibre trace bound on the bulk ball** (fibre-constant weight `c`):
`Σ_{q, p ∈ Q on j} f_q f_p c_p ≤ 125 (log₂ n + 2) Σ_{q ∈ Q} wl_j(q) c_q f_q²`. -/
theorem chan_trace_Q_le (hn : 1 ≤ n) (j : Ch eta) (f c : Cfg eta N → ℝ)
    (hc : ∀ q, 0 ≤ c q) (hcc : ∀ q p, OnCh j (cidx N q) (cidx N p) → c q = c p) :
    ∑ q, ∑ p, (if OnCh j (cidx N q) (cidx N p) ∧ InQ (n : ℝ) (cidx N q) ∧ InQ (n : ℝ) (cidx N p)
      then f q * f p * c p else 0) ≤
      125 * (Nat.log 2 n + 2) *
        ∑ q, (if InQ (n : ℝ) (cidx N q) then wl j q * c q * f q ^ 2 else 0) := by
  classical
  set F := Finset.univ.filter (fun q : Cfg eta N => InQ (n : ℝ) (cidx N q)) with hF
  set g : Cfg eta N → ℝ := fun q => f q * Real.sqrt (c q) with hg
  have hlhs : ∑ q, ∑ p, (if OnCh j (cidx N q) (cidx N p) ∧ InQ (n : ℝ) (cidx N q) ∧
      InQ (n : ℝ) (cidx N p) then f q * f p * c p else 0) =
      ∑ q ∈ F, ∑ p ∈ F, (if OnCh j (cidx N q) (cidx N p) then g q * g p else 0) := by
    rw [hF, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : InQ (n : ℝ) (cidx N q)
    · rw [if_pos hq, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : InQ (n : ℝ) (cidx N p)
      · rw [if_pos hp]
        by_cases h : OnCh j (cidx N q) (cidx N p)
        · rw [if_pos ⟨h, hq, hp⟩, if_pos h]
          simp only [hg]
          rw [hcc q p h]
          have hs := Real.mul_self_sqrt (hc p)
          calc f q * f p * c p = f q * f p * (Real.sqrt (c p) * Real.sqrt (c p)) := by rw [hs]
            _ = f q * Real.sqrt (c p) * (f p * Real.sqrt (c p)) := by ring
        · rw [if_neg (fun hh => h hh.1), if_neg h]
      · rw [if_neg hp, if_neg (fun hh => hp hh.2.2)]
    · rw [if_neg hq]
      exact Finset.sum_eq_zero fun p _ => if_neg (fun hh => hq hh.2.1)
  rw [hlhs]
  have h := FSFlux.fibre_amgm F (fun q p => OnCh j (cidx N q) (cidx N p)) (wl j)
    (fun q => w32_pos _) (N := 125 * (Nat.log 2 n + 2))
    (fun q _ => fibre_wl_Q_le hn j q)
    (fun p _ => by
      have e : F.filter (fun q => OnCh j (cidx N q) (cidx N p)) =
          F.filter (fun q => OnCh j (cidx N p) (cidx N q)) := by
        ext q; simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨h.1, onCh_symm h.2⟩, fun h => ⟨h.1, onCh_symm h.2⟩⟩
      rw [e]; exact fibre_wl_Q_le hn j p)
    g g
  refine h.trans (le_of_eq ?_)
  have e : ∀ q, wl j q * g q ^ 2 = wl j q * c q * f q ^ 2 := fun q => by
    simp only [hg]
    rw [mul_pow, Real.sq_sqrt (hc q)]; ring
  simp only [e]
  rw [hF, Finset.sum_filter]
  ring

omit [Fintype ν] in
/-- The trace weight: `wl_j(q) |Π_j(q)| ≤ √2 c_X² (1 + A)²`. -/
lemma wl_piC_le (hL : 0 < L) (j : Ch eta) (q : Cfg eta N) :
    wl j q * piC j (cidx N q) ≤ Real.sqrt 2 * cXw sys L ^ 2 * (1 + Asym sys L N q) ^ 2 := by
  have hg := gF_pos hL
  have hA0 := FSGalerkin.Asym_nonneg sys L N q
  have hX0 := Xall_nonneg q
  have hc1 : 1 ≤ cXw sys L := by
    unfold cXw
    have : 0 ≤ 2 * mmax sys / gF L ^ 2 := by have := one_le_mmax sys; positivity
    linarith
  have hXA : 1 + Xall q ≤ cXw sys L * (1 + Asym sys L N q) := by
    have h2 := Xall_le_Asym (sys := sys) hL q
    unfold cXw
    have : 0 ≤ 2 * mmax sys / gF L ^ 2 := by have := one_le_mmax sys; positivity
    nlinarith
  -- `wl ≤ (1 + X)^{3/2}`
  have hl : FSLattice.lsq (cidx N q (lead j)) ≤ Xall q := nsq_le_Xall q (lead j)
  have hl0 := FSLattice.lsq_nonneg (cidx N q (lead j))
  have hw : wl j q ≤ (1 + Xall q) * Real.sqrt (1 + Xall q) := by
    unfold wl w32
    exact mul_le_mul (by linarith) (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
      (by linarith)
  -- `|Π| ≤ √2 √(1 + X)`
  have hpi : piC j (cidx N q) ≤ Real.sqrt 2 * Real.sqrt (1 + Xall q) := by
    have h1 := piC_le_sqrt j (cidx N q)
    have h2 : 2 * movS j (cidx N q) ≤ 2 * (1 + Xall q) := by
      have := movS_le_Xall j q; linarith
    rw [← Real.sqrt_mul (by norm_num)]
    exact h1.trans (Real.sqrt_le_sqrt h2)
  have hpi0 := piC_nonneg j (cidx N q)
  have hs := Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 + Xall q by linarith)
  calc wl j q * piC j (cidx N q) ≤ (1 + Xall q) * Real.sqrt (1 + Xall q) *
        (Real.sqrt 2 * Real.sqrt (1 + Xall q)) :=
        mul_le_mul hw hpi hpi0 (by positivity)
    _ = Real.sqrt 2 * (1 + Xall q) ^ 2 := by
        rw [show (1 + Xall q) * Real.sqrt (1 + Xall q) * (Real.sqrt 2 * Real.sqrt (1 + Xall q)) =
          Real.sqrt 2 * (1 + Xall q) * (Real.sqrt (1 + Xall q) * Real.sqrt (1 + Xall q)) by ring,
          hs]
        ring
    _ ≤ Real.sqrt 2 * (cXw sys L * (1 + Asym sys L N q)) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hXA 2) (Real.sqrt_nonneg _)
    _ = _ := by ring

end TraceQ

/-! ## The endpoint and the operator bound of `Y₂` -/

section Y2Bounds

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

/-- The endpoint constant of `Y₂`. -/
noncomputable def CY2 (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  ∑ j : Ch eta, y2C sys L n j * (125 * (Nat.log 2 n + 2)) * (Real.sqrt 2 * cXw sys L ^ 2)

open Classical in
/-- **The endpoint of the second dressing**: `|⟨u, Y₂ u⟩| ≤ C_{Y₂} Σ_q (1 + A)² |u_q|²`. -/
theorem norm_Y2_form_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) (u : En eta N) :
    ‖⟪u, Y2N sys L p₀ N n u⟫_ℂ‖ ≤ CY2 sys L n * ∑ q, (1 + Asym sys L N q) ^ 2 * ‖u.ofLp q‖ ^ 2 := by
  classical
  have hn1 : 1 ≤ n := by omega
  refine (norm_inner_kop_le₂ _ u u).trans ?_
  -- channelwise
  have hpt : ∀ a b, ‖u.ofLp a‖ * ‖u.ofLp b‖ * ‖y2K sys L p₀ N n a b‖ ≤
      ∑ j, y2C sys L n j * (if OnCh j (cidx N a) (cidx N b) ∧ InQ (n : ℝ) (cidx N a) ∧
        InQ (n : ℝ) (cidx N b) then ‖u.ofLp a‖ * ‖u.ofLp b‖ * piC j (cidx N b) else 0) := by
    intro a b
    refine (mul_le_mul_of_nonneg_left (norm_y2K_le hL H hKernel hn a b) (by positivity)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    unfold y2M
    split_ifs with h1 h2 h2
    · obtain ⟨hj, hne, ha, hb⟩ := h1
      have hρ1 : 1 ≤ FSChannel.rho (chT N j a b) := by
        have hl := one_le_lsq_chT hj hne
        have hsq := FSChannel.rho_sq (chT N j a b)
        nlinarith [FSChannel.rho_nonneg (chT N j a b)]
      have hC := y2C_nonneg (sys := sys) (n := n) hL j
      have hpi := piC_nonneg j (cidx N b)
      have hdiv : y2C sys L n j * piC j (cidx N b) / FSChannel.rho (chT N j a b) ≤
          y2C sys L n j * piC j (cidx N b) :=
        div_le_self (by positivity) hρ1
      calc ‖u.ofLp a‖ * ‖u.ofLp b‖ * (y2C sys L n j * piC j (cidx N b) / FSChannel.rho (chT N j a b))
          ≤ ‖u.ofLp a‖ * ‖u.ofLp b‖ * (y2C sys L n j * piC j (cidx N b)) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = _ := by ring
    · exact absurd ⟨h1.1, h1.2.2.1, h1.2.2.2⟩ h2
    · rw [mul_zero]
      have := y2C_nonneg (sys := sys) (n := n) hL j
      have := piC_nonneg j (cidx N b)
      positivity
    · rw [mul_zero, mul_zero]
  refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b).trans ?_
  rw [sum3_comm (fun a b j => y2C sys L n j * (if OnCh j (cidx N a) (cidx N b) ∧
      InQ (n : ℝ) (cidx N a) ∧ InQ (n : ℝ) (cidx N b) then
        ‖u.ofLp a‖ * ‖u.ofLp b‖ * piC j (cidx N b) else 0))]
  have h2 : ∀ j, ∑ a, ∑ b, y2C sys L n j * (if OnCh j (cidx N a) (cidx N b) ∧
      InQ (n : ℝ) (cidx N a) ∧ InQ (n : ℝ) (cidx N b) then
        ‖u.ofLp a‖ * ‖u.ofLp b‖ * piC j (cidx N b) else 0) ≤
      y2C sys L n j * (125 * (Nat.log 2 n + 2)) * (Real.sqrt 2 * cXw sys L ^ 2) *
        ∑ q, (1 + Asym sys L N q) ^ 2 * ‖u.ofLp q‖ ^ 2 := by
    intro j
    have hC := y2C_nonneg (sys := sys) (n := n) hL j
    simp_rw [← Finset.mul_sum]
    rw [mul_assoc (y2C sys L n j), mul_assoc (y2C sys L n j)]
    apply mul_le_mul_of_nonneg_left _ hC
    have htr := chan_trace_Q_le hn1 j (fun q => ‖u.ofLp q‖) (fun q => piC j (cidx N q))
      (fun q => piC_nonneg j _) (fun q p h => piC_onCh h)
    refine htr.trans ?_
    rw [mul_assoc (125 * ((Nat.log 2 n : ℝ) + 2))]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    split_ifs
    · have hw := wl_piC_le (sys := sys) hL j q
      calc wl j q * piC j (cidx N q) * ‖u.ofLp q‖ ^ 2 ≤
          Real.sqrt 2 * cXw sys L ^ 2 * (1 + Asym sys L N q) ^ 2 * ‖u.ofLp q‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hw (sq_nonneg _)
        _ = _ := by ring
    · positivity
  calc ∑ j, ∑ a, ∑ b, y2C sys L n j * (if OnCh j (cidx N a) (cidx N b) ∧
        InQ (n : ℝ) (cidx N a) ∧ InQ (n : ℝ) (cidx N b) then
          ‖u.ofLp a‖ * ‖u.ofLp b‖ * piC j (cidx N b) else 0) ≤
      ∑ j, y2C sys L n j * (125 * (Nat.log 2 n + 2)) * (Real.sqrt 2 * cXw sys L ^ 2) *
        ∑ q, (1 + Asym sys L N q) ^ 2 * ‖u.ofLp q‖ ^ 2 := Finset.sum_le_sum fun j _ => h2 j
    _ = _ := by unfold CY2; rw [Finset.sum_mul]

/-- **The endpoint on a good state**: `|⟨u, Y₂ u⟩| ≤ C_{Y₂} M²`, `C_{Y₂} ~ n⁻³ log n`. -/
theorem norm_Y2_form_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖⟪u, Y2N sys L p₀ N n u⟫_ℂ‖ ≤ CY2 sys L n * M ^ 2 := by
  have hC : 0 ≤ CY2 sys L n := by
    unfold CY2
    refine Finset.sum_nonneg fun j _ => ?_
    have := y2C_nonneg (sys := sys) (n := n) hL j
    positivity
  have hwt : ∑ x, (1 + Asym sys L N x) ^ 2 * ‖u.ofLp x‖ ^ 2 ≤ M ^ 2 := by
    have h := hu.1
    have hW : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖ ≤ M := by
      linarith [norm_nonneg u]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hW 2
    rw [norm_sq_wt] at h2
    refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) h2
    rw [Real.rpow_one]
  exact (norm_Y2_form_le hL H hKernel hn u).trans (mul_le_mul_of_nonneg_left hwt hC)

/-- The crude row constant of `Y₂`: `R₂ = Σ_j C_j (n/2)(n + 1)³`. -/
noncomputable def RY2 (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  ∑ j : Ch eta, y2C sys L n j * ((n : ℝ) / 2) * ((n : ℝ) + 1) ^ 3

open Classical in
lemma sum_y2M_le (hL : 0 < L) (j : Ch eta) (q : Cfg eta N) :
    ∑ q', y2M sys L N n j q' q ≤ y2C sys L n j * ((n : ℝ) / 2) * ((n : ℝ) + 1) ^ 3 := by
  classical
  have hC := y2C_nonneg (sys := sys) (n := n) hL j
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hq : InQ (n : ℝ) (cidx N q)
  swap
  · refine le_trans (le_of_eq (Finset.sum_eq_zero fun q' _ => ?_)) (by positivity)
    unfold y2M; rw [if_neg (fun h => hq h.2.2.2)]
  set T := Finset.univ.filter (fun q' : Cfg eta N => OnCh j (cidx N q') (cidx N q) ∧ q' ≠ q ∧
      InQ (n : ℝ) (cidx N q') ∧ InQ (n : ℝ) (cidx N q)) with hT
  have hpt : ∀ q', y2M sys L N n j q' q ≤
      (if q' ∈ T then y2C sys L n j * ((n : ℝ) / 2) else 0) := by
    intro q'
    unfold y2M
    split_ifs with h1 h2 h2
    · obtain ⟨hj, hne, hq', -⟩ := h1
      have hρ1 : 1 ≤ FSChannel.rho (chT N j q' q) := by
        have hl := one_le_lsq_chT hj hne
        have hsq := FSChannel.rho_sq (chT N j q' q)
        nlinarith [FSChannel.rho_nonneg (chT N j q' q)]
      have hpi := piC_le_of_inQ (j := j) hq
      have hpi0 := piC_nonneg j (cidx N q)
      calc y2C sys L n j * piC j (cidx N q) / FSChannel.rho (chT N j q' q) ≤
          y2C sys L n j * piC j (cidx N q) := div_le_self (by positivity) hρ1
        _ ≤ y2C sys L n j * ((n : ℝ) / 2) := mul_le_mul_of_nonneg_left hpi hC
    · exact absurd (by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h1⟩) h2
    · positivity
    · exact le_rfl
  refine (Finset.sum_le_sum fun q' _ => hpt q').trans ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hinj : Set.InjOn (fun q' => chT N j q' q) T := fun a ha b hb h =>
    chT_injOn j q (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp hb).2.1 h
  have hcard : (T.card : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by
    rw [← Finset.card_image_of_injOn hinj]
    have h := card_ball_le (T.image fun q' => chT N j q' q) (Y := (n : ℝ) ^ 2 / 4) (by positivity)
      (fun τ hτ => by
        obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hτ
        obtain ⟨-, -, hq'Q, -⟩ := (Finset.mem_filter.mp hq').2
        exact lsq_chT_le_box hq'Q hq)
    have hs : Real.sqrt ((n : ℝ) ^ 2 / 4) = n / 2 := by
      rw [show (n : ℝ) ^ 2 / 4 = (n / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    rw [hs] at h
    calc _ ≤ (2 * ((n : ℝ) / 2) + 1) ^ 3 := h
      _ = _ := by ring
  calc (T.card : ℝ) * (y2C sys L n j * ((n : ℝ) / 2)) ≤
      ((n : ℝ) + 1) ^ 3 * (y2C sys L n j * ((n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

/-- **The crude operator bound** `‖Y₂ v‖ ≤ R₂ ‖v‖` (for the out-of-box term). -/
theorem norm_Y2N_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) (v : En eta N) : ‖Y2N sys L p₀ N n v‖ ≤ RY2 sys L n * ‖v‖ := by
  have hR : 0 ≤ RY2 sys L n := by
    unfold RY2
    refine Finset.sum_nonneg fun j _ => ?_
    have := y2C_nonneg (sys := sys) (n := n) hL j
    positivity
  have h := norm_kop_le_weight (y2K sys L p₀ N n) (fun q p => ∑ j, y2M sys L N n j q p)
    (fun _ => RY2 sys L n) (fun q p => Finset.sum_nonneg fun j _ => y2M_nonneg hL j q p)
    (fun q p => norm_y2K_le hL H hKernel hn q p) (fun _ => hR) (fun _ _ _ => rfl)
    (fun q => by
      rw [Finset.sum_comm]
      unfold RY2
      refine Finset.sum_le_sum fun j _ => ?_
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => y2M_symm j q p)) ?_
      exact sum_y2M_le hL j q)
    (fun p => by
      rw [Finset.sum_comm]
      unfold RY2
      exact Finset.sum_le_sum fun j _ => sum_y2M_le hL j p) v
  have e : ∑ p, RY2 sys L n ^ 2 * ‖v.ofLp p‖ ^ 2 = (RY2 sys L n * ‖v‖) ^ 2 := by
    rw [← Finset.mul_sum, mul_pow, FSKernel.norm_sq_eq]
  rw [e] at h
  by_contra hc
  have := pow_lt_pow_left₀ (not_le.mp hc) (by positivity) two_ne_zero
  linarith

end Y2Bounds

/-! ## The ledger of the symbol current -/

section Ledger

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
  (p₀ : Fin eta) {N : ℕ} (n : ℕ)

include hL hKernel in
/-- **The symbol-current ledger**: along the exact evolution,
`∫₀ᵗ Re⟨u, Z_a u⟩ = ∫₀ᵗ Re⟨u, Z^≤ u⟩ + [Re⟨u, Y₂ u⟩]₀ᵗ - ∫₀ᵗ Re⟨u, i[W, Y₂] u⟩ - ∫₀ᵗ e_{Y₂}`. -/
theorem ledger_za (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (D : EvoData L H) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, (⟪ub H D N s, ZaN sys L p₀ N n (ub H D N s)⟫_ℂ).re =
      (∫ s in (0 : ℝ)..t, (⟪ub H D N s, FSKernel.kop (zaLe sys L p₀ N n) (ub H D N s)⟫_ℂ).re) +
        ((⟪ub H D N t, Y2N sys L p₀ N n (ub H D N t)⟫_ℂ).re -
          (⟪ub H D N 0, Y2N sys L p₀ N n (ub H D N 0)⟫_ℂ).re) -
        (∫ s in (0 : ℝ)..t, (⟪ub H D N s, (Complex.I • (WN sys L N ∘ₗ Y2N sys L p₀ N n -
          Y2N sys L p₀ N n ∘ₗ WN sys L N)) (ub H D N s)⟫_ℂ).re) -
        ∫ s in (0 : ℝ)..t, eY sys H D (Y2N sys L p₀ N n : En eta N →ₗ[ℂ] En eta N) s := by
  have hE := elim_box sys hL H hKernel (N := N) Hunit hPeriodic D (Y2N sys L p₀ N n)
    (Y2N_symm hL H hKernel) t
  rw [comm_Y2N hL] at hE
  have hsplit : ∀ s, (⟪ub H D N s, ZaN sys L p₀ N n (ub H D N s)⟫_ℂ).re =
      (⟪ub H D N s, FSKernel.kop (zaLe sys L p₀ N n) (ub H D N s)⟫_ℂ).re +
        (⟪ub H D N s, FSKernel.kop (zaGt sys L p₀ N n) (ub H D N s)⟫_ℂ).re := by
    intro s
    rw [ZaN_split hL H hKernel, LinearMap.add_apply, inner_add_right, Complex.add_re]
  rw [intervalIntegral.integral_congr (fun s _ => hsplit s)]
  have hc1 := continuous_form_ub H (N := N) D (FSKernel.kop (zaLe sys L p₀ N n))
  have hc2 := continuous_form_ub H (N := N) D (FSKernel.kop (zaGt sys L p₀ N n))
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable 0 t) (hc2.intervalIntegrable 0 t), hE]
  ring

end Ledger

end FSFlux
