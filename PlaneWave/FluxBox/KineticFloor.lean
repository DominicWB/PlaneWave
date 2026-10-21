import PlaneWave.FluxBox.SymbolCurrentKernel

/-!
# Flux route, stage 2, part 16: the kinetic floor and the pinned symbol current

The symbol current `Z_a` (`PlaneWave.FluxBox.SymbolCurrentKernel`) is split by the **kinetic floor** `|F_c(τ)| ≥ |τ|²/4`,
equivalently `|E(q') - E(q)| ≥ g²|τ|²/(8 μ_j)` (`kinC`, symmetric):

  `z = z^≤ + z^>`,  `z^> = 1{kinC} z` (to be eliminated by `Y₂ = divK_E(-i z^>)`, `PlaneWave.FluxBox.SecondDressing`).

Below the floor the hop is pinned at both ends (`pin_register`): some moved register of `q`
and of `q'` has `|k_c|² > (9/64)|τ|²`, and the mismatch is small, so the kernel bound of
`PlaneWave.FluxBox.SymbolCurrentKernel` becomes `|z^≤(q', q)| ≤ 9 μ_j c_j² |Π_j|/M̄_j · |τ| · 611 (4/(3n))³` on the pinned
pairs (`norm_zaLe_le`, through the symmetric majorant `zLeM`). The ball count
(`sum_rho_ball_le`) bounds its columns by `C (1 + X)^{5/2}`, and the symmetric Schur bound
(`sum_sym_kernel_le`) gives

  `|⟨u, Z^≤ u⟩| ≤ C_Z n⁻³ Σ_{q ∈ Q} (1 + A)^{5/2} |u_q|²`               (`norm_form_zaLe_le`).

The **critical moment** (`crit_moment_le`, from the borderline dyadic moment
`FSDatum.moment_quarter_le_of_tails` and the weighted tails of a good state) is
`Σ_{q ∈ Q} (1 + A)^{5/2} |u_q|² ≤ (1 + η/2)^{1/2} M² (1 + 2η n_d)` with `K/4 ≤ 2^{n_d}`, so
`|⟨u, Z^≤ u⟩| ≤ C n⁻³ M² (1 + log K)` (`norm_form_zaLe_good`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The kinetic floor -/

section KinFloor

variable (sys : CoulombSystem eta ν) (L : ℝ) (N : ℕ)

/-- **The kinetic floor** on a hop: `|E(q) - E(p)| ≥ g²|θ|²/(8 μ_j)` (`|F_c(θ)| ≥ |θ|²/4`). -/
def kinC (q p : Cfg eta N) : Prop :=
  q ≠ p ∧ ∃ j : Ch eta, OnCh j (cidx N q) (cidx N p) ∧
    gF L ^ 2 * FSLattice.lsq (chT N j q p) / (8 * muCh sys j) ≤ |Asym sys L N q - Asym sys L N p|

variable {sys L N}

omit [Fintype ν] in
lemma lsq_chT_swap (j : Ch eta) (q p : Cfg eta N) :
    FSLattice.lsq (chT N j p q) = FSLattice.lsq (chT N j q p) := by
  unfold chT; exact FSChannel.lsq_sub_comm _ _

omit [Fintype ν] in
lemma kinC_symm {q p : Cfg eta N} (h : kinC sys L N q p) : kinC sys L N p q := by
  obtain ⟨hne, j, hj, hfl⟩ := h
  refine ⟨hne.symm, j, onCh_symm hj, ?_⟩
  rw [lsq_chT_swap, abs_sub_comm]
  exact hfl

omit [Fintype ν] in
lemma kinC_comm (q p : Cfg eta N) : kinC sys L N q p ↔ kinC sys L N p q :=
  ⟨kinC_symm, kinC_symm⟩

omit [Fintype ν] in
/-- Below the kinetic floor the mismatch is small. -/
lemma energy_lt_of_not_kinC {j : Ch eta} {q p : Cfg eta N} (hj : OnCh j (cidx N q) (cidx N p))
    (hne : q ≠ p) (h : ¬ kinC sys L N q p) :
    |Asym sys L N q - Asym sys L N p| <
      gF L ^ 2 * FSLattice.lsq (chT N j q p) / (8 * muCh sys j) := by
  by_contra hc
  exact h ⟨hne, j, hj, not_lt.mp hc⟩

omit [Fintype ν] in
/-- Below the kinetic floor the hop is pinned: `|F_c(θ)| < |θ|²/4`. -/
lemma pinned_of_not_kinC (hL : 0 < L) {j : Ch eta} {q p : Cfg eta N}
    (hj : OnCh j (cidx N q) (cidx N p)) (hne : q ≠ p) (h : ¬ kinC sys L N q p) :
    |FSLattice.slabF (cCh sys j (cidx N p)) (chT N j q p)| < FSLattice.lsq (chT N j q p) / 4 := by
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hlt := energy_lt_of_not_kinC hj hne h
  rw [Asym_hop hj, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))] at hlt
  have e : gF L ^ 2 * FSLattice.lsq (chT N j q p) / (8 * muCh sys j) =
      gF L ^ 2 / (2 * muCh sys j) * (FSLattice.lsq (chT N j q p) / 4) := by
    field_simp; ring
  rw [e] at hlt
  exact lt_of_mul_lt_mul_left hlt (by positivity)

/-- The squared momenta of the registers moved by `j`. -/
noncomputable def movS (j : Ch eta) (k : Cf eta) : ℝ := ∑ c ∈ moved j, nsq (k c)

omit [Fintype ν] in
lemma movS_nonneg (j : Ch eta) (k : Cf eta) : 0 ≤ movS j k :=
  Finset.sum_nonneg fun _ _ => nsq_nonneg _

omit [Fintype ν] in
/-- Pinning at the input: `(9/64)|θ|² < S_j(p)`. -/
lemma pin_movS (hL : 0 < L) {j : Ch eta} {q p : Cfg eta N}
    (hj : OnCh j (cidx N q) (cidx N p)) (hne : q ≠ p) (h : ¬ kinC sys L N q p) :
    9 / 64 * FSLattice.lsq (chT N j q p) < movS j (cidx N p) := by
  obtain ⟨c, hc, hlt⟩ := pin_register sys j (cidx N p) (chT N j q p) (pinned_of_not_kinC hL hj hne h)
  exact lt_of_lt_of_le hlt (Finset.single_le_sum (f := fun c => nsq (cidx N p c))
    (fun c _ => nsq_nonneg _) hc)

omit [Fintype ν] in
lemma movS_le_Xall (j : Ch eta) (q : Cfg eta N) : movS j (cidx N q) ≤ Xall q := by
  unfold movS Xall
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun c _ _ => FSLattice.lsq_nonneg _)

omit [Fintype ν] in
/-- On the box: `|τ|² ≤ n²/4` for a hop between two points of `Q`. -/
lemma lsq_chT_le_box {n : ℕ} {j : Ch eta} {q p : Cfg eta N} (hq : InQ (n : ℝ) (cidx N q))
    (hp : InQ (n : ℝ) (cidx N p)) : FSLattice.lsq (chT N j q p) ≤ (n : ℝ) ^ 2 / 4 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : FSChannel.rho (chT N j q p) ≤
      FSChannel.rho (cidx N q (lead j)) + FSChannel.rho (cidx N p (lead j)) := by
    have := FSChannel.rho_add_le (cidx N q (lead j)) (-(cidx N p (lead j)))
    rw [rho_neg'] at this
    unfold chT
    rwa [sub_eq_add_neg]
  have h2 := rho_le_of_inQ hn hq (lead j)
  have h3 := rho_le_of_inQ hn hp (lead j)
  have h4 : FSChannel.rho (chT N j q p) ≤ n / 2 := by linarith
  rw [← FSChannel.rho_sq]
  have := FSChannel.rho_nonneg (chT N j q p)
  nlinarith

end KinFloor

/-! ## The split of the symbol current -/

section Split

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ)

open Classical in
/-- The pinned part `z^≤ = 1{¬ kinC} z` of the symbol current. -/
noncomputable def zaLe (q' q : Cfg eta N) : ℂ :=
  if kinC sys L N q' q then 0 else zaK sys L p₀ N n q' q

open Classical in
/-- The part `z^> = 1{kinC} z` above the kinetic floor. -/
noncomputable def zaGt (q' q : Cfg eta N) : ℂ :=
  if kinC sys L N q' q then zaK sys L p₀ N n q' q else 0

variable {sys L p₀ N n}

lemma zaLe_add_zaGt (q' q : Cfg eta N) :
    zaLe sys L p₀ N n q' q + zaGt sys L p₀ N n q' q = zaK sys L p₀ N n q' q := by
  unfold zaLe zaGt
  split_ifs <;> simp

theorem ZaN_split (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    ZaN sys L p₀ N n = FSKernel.kop (zaLe sys L p₀ N n) + FSKernel.kop (zaGt sys L p₀ N n) := by
  rw [ZaN_eq_kop hL H hKernel, ← FSKernel.kop_add]
  congr 1
  funext q' q
  exact (zaLe_add_zaGt q' q).symm

/-- **The symbol current is Hermitian**: `z(q, q') = conj z(q', q)`. -/
lemma zaK_conj (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (q' q : Cfg eta N) : zaK sys L p₀ N n q q' = conj (zaK sys L p₀ N n q' q) := by
  unfold zaK
  by_cases h : InQ (n : ℝ) (cidx N q') ∧ InQ (n : ℝ) (cidx N q)
  · rw [if_pos ⟨h.2, h.1⟩, if_pos h, map_mul, Complex.conj_I, map_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : InP (n : ℝ) (cidx N r)
    · simp [hr]
    · rw [if_pos hr, if_pos hr, map_sub, map_mul, map_mul, ← wNK_conj hL q' r, ← wNK_conj hL r q,
        ← ycK_conj hL H hKernel r q, ← ycK_conj hL H hKernel q' r]
      ring
  · rw [if_neg (fun h' => h ⟨h'.2, h'.1⟩), if_neg h, map_zero]

lemma zaLe_conj (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (q' q : Cfg eta N) : zaLe sys L p₀ N n q q' = conj (zaLe sys L p₀ N n q' q) := by
  unfold zaLe
  rw [kinC_comm q q']
  split_ifs
  · simp
  · exact zaK_conj hL H hKernel q' q

lemma zaGt_conj (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (q' q : Cfg eta N) : zaGt sys L p₀ N n q q' = conj (zaGt sys L p₀ N n q' q) := by
  unfold zaGt
  rw [kinC_comm q q']
  split_ifs
  · exact zaK_conj hL H hKernel q' q
  · simp

lemma zaA_self (q : Cfg eta N) (j : Ch eta) : zaA sys L N n j q q = 0 := by
  unfold zaA
  have h0 : chT N j q q = 0 := by unfold chT; exact sub_self _
  rw [h0, sub_self, abs_zero]
  have : FSChannel.rho (0 : Lattice3) = 0 := by
    unfold FSChannel.rho; simp [FSLattice.lsq]
  rw [this]
  ring

/-- The diagonal of the symbol current vanishes. -/
lemma zaK_self (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) (q : Cfg eta N) : zaK sys L p₀ N n q q = 0 := by
  classical
  have h := norm_zaK_le (p₀ := p₀) hL H hKernel hn q q
  have e : ∑ j, (if OnCh j (cidx N q) (cidx N q) then
      zaA sys L N n j q q * (611 / (3 * n / 4) ^ 3) else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [zaA_self, zero_mul, ite_self]
  rw [e] at h
  exact norm_le_zero_iff.mp h

end Split

/-! ## The pinned kernel bound -/

section Pinned

variable (sys : CoulombSystem eta ν) (L : ℝ) (N n : ℕ)

/-- The pinned kernel constant `9 μ_j c_j²/M̄_j · 611 (4/(3n))³`. -/
noncomputable def zLeC (j : Ch eta) : ℝ :=
  9 * muCh sys j * chC sys L j ^ 2 / Mtot sys j * (611 / (3 * n / 4) ^ 3)

open Classical in
/-- **The symmetric pinned majorant** of `z^≤` on channel `j`. -/
noncomputable def zLeM (j : Ch eta) (q' q : Cfg eta N) : ℝ :=
  if OnCh j (cidx N q') (cidx N q) ∧ q' ≠ q ∧ InQ (n : ℝ) (cidx N q') ∧ InQ (n : ℝ) (cidx N q) ∧
      9 / 64 * FSLattice.lsq (chT N j q' q) < movS j (cidx N q) ∧
      9 / 64 * FSLattice.lsq (chT N j q' q) < movS j (cidx N q') then
    zLeC sys L n j * piC j (cidx N q) * FSChannel.rho (chT N j q' q)
  else 0

variable {sys L N n}

lemma zLeC_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ zLeC sys L n j := by
  unfold zLeC
  have := muCh_pos sys j; have := Mtot_pos sys j; have := chC_nonneg sys hL j
  positivity

lemma zLeM_nonneg (hL : 0 < L) (j : Ch eta) (q' q : Cfg eta N) : 0 ≤ zLeM sys L N n j q' q := by
  unfold zLeM
  split_ifs
  · exact mul_nonneg (mul_nonneg (zLeC_nonneg hL j) (piC_nonneg j _)) (FSChannel.rho_nonneg _)
  · exact le_rfl

lemma zLeM_symm (j : Ch eta) (q' q : Cfg eta N) : zLeM sys L N n j q' q = zLeM sys L N n j q q' := by
  classical
  unfold zLeM
  rw [lsq_chT_swap j q' q]
  by_cases h : OnCh j (cidx N q') (cidx N q)
  · have h' := onCh_symm h
    rw [piC_onCh h, chT_swap j q' q]
    apply if_congr _ rfl rfl
    constructor
    · rintro ⟨-, hne, hq', hq, h1, h2⟩; exact ⟨h', hne.symm, hq, hq', h2, h1⟩
    · rintro ⟨-, hne, hq, hq', h2, h1⟩; exact ⟨h, hne.symm, hq', hq, h1, h2⟩
  · have h' : ¬ OnCh j (cidx N q) (cidx N q') := fun h' => h (onCh_symm h')
    rw [if_neg (fun hh => h hh.1), if_neg (fun hh => h' hh.1)]

/-- **The pinned kernel bound**: `|z^≤(q', q)| ≤ Σ_j M_j(q', q)`. -/
theorem norm_zaLe_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {p₀ : Fin eta} (hn : 8 ≤ n) (q' q : Cfg eta N) :
    ‖zaLe sys L p₀ N n q' q‖ ≤ ∑ j, zLeM sys L N n j q' q := by
  classical
  have hM0 : 0 ≤ ∑ j, zLeM sys L N n j q' q := Finset.sum_nonneg fun j _ => zLeM_nonneg hL j q' q
  unfold zaLe
  split_ifs with hk
  · rw [norm_zero]; exact hM0
  by_cases hQ : InQ (n : ℝ) (cidx N q') ∧ InQ (n : ℝ) (cidx N q)
  swap
  · have : zaK sys L p₀ N n q' q = 0 := by unfold zaK; rw [if_neg hQ]
    rw [this, norm_zero]; exact hM0
  by_cases hqq : q' = q
  · rw [hqq, zaK_self hL H hKernel hn q, norm_zero]
    exact Finset.sum_nonneg fun j _ => zLeM_nonneg hL j q q
  obtain ⟨hq', hq⟩ := hQ
  refine (norm_zaK_le hL H hKernel hn q' q).trans (Finset.sum_le_sum fun j _ => ?_)
  split_ifs with hj
  swap
  · exact zLeM_nonneg hL j q' q
  -- the pinned pair
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hMt := Mtot_pos sys j
  have hpi := piC_nonneg j (cidx N q)
  have hcC := chC_nonneg sys hL j
  have hpin1 := pin_movS hL hj hqq hk
  have hpin2 := pin_movS hL (onCh_symm hj) (Ne.symm hqq) (fun h => hk (kinC_symm h))
  rw [lsq_chT_swap] at hpin2
  have hcond : OnCh j (cidx N q') (cidx N q) ∧ q' ≠ q ∧ InQ (n : ℝ) (cidx N q') ∧
      InQ (n : ℝ) (cidx N q) ∧ 9 / 64 * FSLattice.lsq (chT N j q' q) < movS j (cidx N q) ∧
      9 / 64 * FSLattice.lsq (chT N j q' q) < movS j (cidx N q') :=
    ⟨hj, hqq, hq', hq, hpin1, hpin2⟩
  unfold zLeM
  rw [if_pos hcond]
  -- `zaA ≤ 9 μ c² |Π|/M̄ |τ|`
  have hE := energy_lt_of_not_kinC hj hqq hk
  set ρ := FSChannel.rho (chT N j q' q) with hρdef
  have hρ0 : 0 ≤ ρ := FSChannel.rho_nonneg _
  have hρsq : ρ ^ 2 = FSLattice.lsq (chT N j q' q) := FSChannel.rho_sq _
  have hρn : ρ ≤ n / 2 := by
    have hl := lsq_chT_le_box (j := j) hq' hq
    rw [← hρsq] at hl
    nlinarith
  rw [← hρsq] at hE
  have hw : 36 * muCh sys j ^ 2 * |Asym sys L N q' - Asym sys L N q| / (gF L ^ 2 * (3 * n / 4)) ≤
      3 * muCh sys j * ρ := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 36 * muCh sys j ^ 2 * |Asym sys L N q' - Asym sys L N q| ≤
        36 * muCh sys j ^ 2 * (gF L ^ 2 * ρ ^ 2 / (8 * muCh sys j)) :=
      mul_le_mul_of_nonneg_left hE.le (by positivity)
    have h2 : 36 * muCh sys j ^ 2 * (gF L ^ 2 * ρ ^ 2 / (8 * muCh sys j)) =
        9 / 2 * muCh sys j * gF L ^ 2 * ρ * ρ := by field_simp; ring
    have h3 : 9 / 2 * muCh sys j * gF L ^ 2 * ρ * ρ ≤ 9 / 2 * muCh sys j * gF L ^ 2 * ρ * (n / 2) :=
      mul_le_mul_of_nonneg_left hρn (by positivity)
    have h4 : 9 / 2 * muCh sys j * gF L ^ 2 * ρ * (n / 2) =
        3 * muCh sys j * ρ * (gF L ^ 2 * (3 * n / 4)) := by ring
    linarith
  have hA : zaA sys L N n j q' q ≤ chC sys L j ^ 2 * (piC j (cidx N q) / Mtot sys j) *
      (9 * muCh sys j * ρ) := by
    unfold zaA
    rw [← hρdef]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  calc zaA sys L N n j q' q * (611 / (3 * n / 4) ^ 3) ≤
      chC sys L j ^ 2 * (piC j (cidx N q) / Mtot sys j) * (9 * muCh sys j * ρ) *
        (611 / (3 * n / 4) ^ 3) := mul_le_mul_of_nonneg_right hA (by positivity)
    _ = zLeC sys L n j * piC j (cidx N q) * ρ := by unfold zLeC; field_simp

end Pinned

/-! ## The columns of the pinned majorant -/

section Columns

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

omit [Fintype ν] in
/-- **The ball sum**: `Σ_{τ ∈ T} |τ| ≤ √Y (2√Y + 1)³` when every `τ ∈ T` has `|τ|² ≤ Y`. -/
lemma sum_rho_ball_le (T : Finset Lattice3) {Y : ℝ} (hY : 0 ≤ Y)
    (hT : ∀ τ ∈ T, FSLattice.lsq τ ≤ Y) :
    ∑ τ ∈ T, FSChannel.rho τ ≤ Real.sqrt Y * (2 * Real.sqrt Y + 1) ^ 3 := by
  have hsub : T ⊆ FSLattice.box ⌊Real.sqrt Y⌋₊ := fun τ hτ =>
    FSLattice.mem_box_floor_of_lsq_le (Real.sqrt_nonneg Y)
      (by rw [Real.sq_sqrt hY]; exact hT τ hτ)
  have hcard : (T.card : ℝ) ≤ (2 * Real.sqrt Y + 1) ^ 3 := by
    have h1 := Finset.card_le_card hsub
    rw [FSLattice.card_box] at h1
    have h1' : (T.card : ℝ) ≤ ((2 * ⌊Real.sqrt Y⌋₊ + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast h1
    have hfl := Nat.floor_le (Real.sqrt_nonneg Y)
    have h2 : ((2 * ⌊Real.sqrt Y⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt Y + 1 := by
      push_cast; linarith
    exact h1'.trans (pow_le_pow_left₀ (by positivity) h2 3)
  calc ∑ τ ∈ T, FSChannel.rho τ ≤ ∑ τ ∈ T, Real.sqrt Y :=
        Finset.sum_le_sum fun τ hτ => Real.sqrt_le_sqrt (hT τ hτ)
    _ = T.card * Real.sqrt Y := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * Real.sqrt Y + 1) ^ 3 * Real.sqrt Y :=
        mul_le_mul_of_nonneg_right hcard (Real.sqrt_nonneg Y)
    _ = _ := by ring

open Classical in
/-- **The columns of the pinned majorant**:
`Σ_{q'} M_j(q', q) ≤ 1_Q(q) C_j |Π_j(q)| √Y (2√Y + 1)³`, `Y = (64/9) S_j(q)`. -/
lemma sum_zLeM_le (j : Ch eta) (q : Cfg eta N) :
    ∑ q', zLeM sys L N n j q' q ≤
      (if InQ (n : ℝ) (cidx N q) then zLeC sys L n j * piC j (cidx N q) *
        (Real.sqrt (64 / 9 * movS j (cidx N q)) *
          (2 * Real.sqrt (64 / 9 * movS j (cidx N q)) + 1) ^ 3) else 0) := by
  by_cases hq : InQ (n : ℝ) (cidx N q)
  swap
  · rw [if_neg hq]
    exact le_of_eq (Finset.sum_eq_zero fun q' _ => by
      unfold zLeM; rw [if_neg (fun h => hq h.2.2.2.1)])
  rw [if_pos hq]
  set T := Finset.univ.filter (fun q' : Cfg eta N => OnCh j (cidx N q') (cidx N q) ∧ q' ≠ q ∧
      InQ (n : ℝ) (cidx N q') ∧ InQ (n : ℝ) (cidx N q) ∧
      9 / 64 * FSLattice.lsq (chT N j q' q) < movS j (cidx N q) ∧
      9 / 64 * FSLattice.lsq (chT N j q' q) < movS j (cidx N q')) with hT
  have e : ∑ q', zLeM sys L N n j q' q =
      zLeC sys L n j * piC j (cidx N q) * ∑ q' ∈ T, FSChannel.rho (chT N j q' q) := by
    rw [Finset.mul_sum, hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q' _ => ?_
    unfold zLeM
    split_ifs <;> simp
  rw [e]
  have hC : 0 ≤ zLeC sys L n j * piC j (cidx N q) := by
    by_cases hL : 0 < L
    · exact mul_nonneg (zLeC_nonneg hL j) (piC_nonneg j _)
    · -- `zLeC` is a product of squares and positive constants in any case
      unfold zLeC
      have := muCh_pos sys j; have := Mtot_pos sys j; have := piC_nonneg j (cidx N q)
      positivity
  apply mul_le_mul_of_nonneg_left _ hC
  have hinj : Set.InjOn (fun q' => chT N j q' q) T := fun a ha b hb h =>
    chT_injOn j q (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp hb).2.1 h
  rw [← Finset.sum_image (f := fun τ => FSChannel.rho τ) hinj]
  apply sum_rho_ball_le _ (by have := movS_nonneg j (cidx N q); positivity)
  intro τ hτ
  obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hτ
  have h := (Finset.mem_filter.mp hq').2.2.2.2.2.1
  linarith

omit [Fintype ν] in
/-- The column weight: `|Π| √Y (2√Y + 1)³ ≤ √2 (8/3)(19/3)³ (1 + S)² √(1 + S)`. -/
lemma col_weight_le (j : Ch eta) (k : Cf eta) :
    piC j k * (Real.sqrt (64 / 9 * movS j k) * (2 * Real.sqrt (64 / 9 * movS j k) + 1) ^ 3) ≤
      Real.sqrt 2 * (8 / 3) * (19 / 3) ^ 3 * ((1 + movS j k) ^ 2 * Real.sqrt (1 + movS j k)) := by
  set S := movS j k with hS
  have hS0 : 0 ≤ S := movS_nonneg j k
  have hpi : piC j k ≤ Real.sqrt 2 * Real.sqrt S := by
    have := piC_le_sqrt j k
    rwa [Real.sqrt_mul (by norm_num)] at this
  have hY : Real.sqrt (64 / 9 * S) = 8 / 3 * Real.sqrt S := by
    rw [Real.sqrt_mul (by norm_num), show (64 / 9 : ℝ) = (8 / 3) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [hY]
  set s := Real.sqrt S
  set t := Real.sqrt (1 + S)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg S
  have hst : s ≤ t := Real.sqrt_le_sqrt (by linarith)
  have ht1 : 1 ≤ t := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + S by linarith)
    rwa [Real.sqrt_one] at this
  have ht2 : t ^ 2 = 1 + S := Real.sq_sqrt (by linarith)
  have hpi0 := piC_nonneg j k
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  calc piC j k * (8 / 3 * s * (2 * (8 / 3 * s) + 1) ^ 3) ≤
      (Real.sqrt 2 * s) * (8 / 3 * s * (2 * (8 / 3 * s) + 1) ^ 3) :=
        mul_le_mul_of_nonneg_right hpi (by positivity)
    _ ≤ (Real.sqrt 2 * t) * (8 / 3 * t * (16 / 3 * t + t) ^ 3) := by
        have h3 : 2 * (8 / 3 * s) + 1 ≤ 16 / 3 * t + t := by linarith
        have h4 : (2 * (8 / 3 * s) + 1) ^ 3 ≤ (16 / 3 * t + t) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h3 3
        apply mul_le_mul (mul_le_mul_of_nonneg_left hst h2) _ (by positivity) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hst (by norm_num)) h4 (by positivity)
          (by positivity)
    _ = Real.sqrt 2 * (8 / 3) * (19 / 3) ^ 3 * ((t ^ 2) ^ 2 * t) := by ring
    _ = _ := by rw [ht2]

omit [Fintype ν] in
/-- `(1 + S)² √(1 + S) ≤ c_X² √c_X (1 + A)² √(1 + A)`. -/
lemma movS_weight_le (hL : 0 < L) (j : Ch eta) (q : Cfg eta N) :
    (1 + movS j (cidx N q)) ^ 2 * Real.sqrt (1 + movS j (cidx N q)) ≤
      cXw sys L ^ 2 * Real.sqrt (cXw sys L) *
        ((1 + Asym sys L N q) ^ 2 * Real.sqrt (1 + Asym sys L N q)) := by
  have hg := gF_pos hL
  have hA0 := FSGalerkin.Asym_nonneg sys L N q
  have hm := one_le_mmax sys
  have hc1 : 1 ≤ cXw sys L := by
    unfold cXw
    have : 0 ≤ 2 * mmax sys / gF L ^ 2 := by positivity
    linarith
  have hS0 := movS_nonneg j (cidx N q)
  have h1 : 1 + movS j (cidx N q) ≤ cXw sys L * (1 + Asym sys L N q) := by
    have h2 := (movS_le_Xall j q).trans (Xall_le_Asym (sys := sys) hL q)
    unfold cXw
    have : 0 ≤ 2 * mmax sys / gF L ^ 2 := by positivity
    nlinarith
  have hsq : Real.sqrt (1 + movS j (cidx N q)) ≤
      Real.sqrt (cXw sys L) * Real.sqrt (1 + Asym sys L N q) := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt h1
  calc (1 + movS j (cidx N q)) ^ 2 * Real.sqrt (1 + movS j (cidx N q)) ≤
      (cXw sys L * (1 + Asym sys L N q)) ^ 2 *
        (Real.sqrt (cXw sys L) * Real.sqrt (1 + Asym sys L N q)) :=
        mul_le_mul (pow_le_pow_left₀ (by linarith) h1 2) hsq (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

end Columns

/-! ## The form of the pinned current -/

section Form

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

omit [Fintype ν] in
/-- **The symmetric Schur bound**: for a symmetric nonnegative `K` with column sums `≤ ω`,
`Σ_{a,b} |x_a| |x_b| K(a, b) ≤ Σ_b ω_b x_b²`. -/
lemma sum_sym_kernel_le {X : Type*} [Fintype X] (K : X → X → ℝ) (hK : ∀ a b, 0 ≤ K a b)
    (hsym : ∀ a b, K a b = K b a) (ω : X → ℝ) (hcol : ∀ b, ∑ a, K a b ≤ ω b) (x : X → ℝ) :
    ∑ a, ∑ b, |x a| * |x b| * K a b ≤ ∑ b, ω b * x b ^ 2 := by
  have h1 : ∀ a b, |x a| * |x b| * K a b ≤ x a ^ 2 * K a b / 2 + x b ^ 2 * K a b / 2 := by
    intro a b
    have h := two_mul_le_add_sq |x a| |x b|
    rw [sq_abs, sq_abs] at h
    have := mul_le_mul_of_nonneg_right h (hK a b)
    linarith
  have e1 : ∑ a, ∑ b, x a ^ 2 * K a b = ∑ a, x a ^ 2 * ∑ b, K b a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [hsym]
  have e2 : ∑ a, ∑ b, x b ^ 2 * K a b = ∑ b, x b ^ 2 * ∑ a, K a b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
  have b1 : ∑ a, x a ^ 2 * ∑ b, K b a ≤ ∑ a, ω a * x a ^ 2 :=
    Finset.sum_le_sum fun a _ => by
      rw [mul_comm (ω a)]; exact mul_le_mul_of_nonneg_left (hcol a) (sq_nonneg _)
  have b2 : ∑ b, x b ^ 2 * ∑ a, K a b ≤ ∑ b, ω b * x b ^ 2 :=
    Finset.sum_le_sum fun b _ => by
      rw [mul_comm (ω b)]; exact mul_le_mul_of_nonneg_left (hcol b) (sq_nonneg _)
  calc ∑ a, ∑ b, |x a| * |x b| * K a b ≤
      ∑ a, ∑ b, (x a ^ 2 * K a b / 2 + x b ^ 2 * K a b / 2) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h1 a b
    _ = (∑ a, ∑ b, x a ^ 2 * K a b) / 2 + (∑ a, ∑ b, x b ^ 2 * K a b) / 2 := by
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    _ ≤ (∑ b, ω b * x b ^ 2) / 2 + (∑ b, ω b * x b ^ 2) / 2 := by
        rw [e1, e2]; linarith
    _ = _ := by ring

/-- The constant of the pinned form, `C_Z = Σ_j zLeC_j √2 (8/3)(19/3)³ c_X² √c_X`. -/
noncomputable def CZle (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  ∑ j : Ch eta, zLeC sys L n j * (Real.sqrt 2 * (8 / 3) * (19 / 3) ^ 3) *
    (cXw sys L ^ 2 * Real.sqrt (cXw sys L))

open Classical in
/-- **The form of the pinned current**:
`|⟨u, Z^≤ u⟩| ≤ C_Z Σ_{q ∈ Q} (1 + A)² √(1 + A) |u_q|²`. -/
theorem norm_form_zaLe_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) (u : En eta N) :
    ‖⟪u, FSKernel.kop (zaLe sys L p₀ N n) u⟫_ℂ‖ ≤ CZle sys L n *
      ∑ q, (if InQ (n : ℝ) (cidx N q) then
        (1 + Asym sys L N q) ^ 2 * Real.sqrt (1 + Asym sys L N q) * ‖u.ofLp q‖ ^ 2 else 0) := by
  set K : Cfg eta N → Cfg eta N → ℝ := fun a b => ∑ j, zLeM sys L N n j a b with hKdef
  set W : Cfg eta N → ℝ := fun q => if InQ (n : ℝ) (cidx N q) then
    (1 + Asym sys L N q) ^ 2 * Real.sqrt (1 + Asym sys L N q) else 0 with hWdef
  have hK0 : ∀ a b, 0 ≤ K a b := fun a b => Finset.sum_nonneg fun j _ => zLeM_nonneg hL j a b
  have hKs : ∀ a b, K a b = K b a := fun a b =>
    Finset.sum_congr rfl fun j _ => zLeM_symm j a b
  have hcol : ∀ b, ∑ a, K a b ≤ CZle sys L n * W b := by
    intro b
    rw [Finset.sum_comm]
    unfold CZle
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => (sum_zLeM_le j b).trans ?_
    by_cases hb : InQ (n : ℝ) (cidx N b)
    · rw [if_pos hb]
      simp only [hWdef, if_pos hb]
      have h1 := col_weight_le j (cidx N b)
      have h2 := movS_weight_le (sys := sys) hL j b
      have hC := zLeC_nonneg (sys := sys) (n := n) hL j
      calc zLeC sys L n j * piC j (cidx N b) * (Real.sqrt (64 / 9 * movS j (cidx N b)) *
            (2 * Real.sqrt (64 / 9 * movS j (cidx N b)) + 1) ^ 3) =
          zLeC sys L n j * (piC j (cidx N b) * (Real.sqrt (64 / 9 * movS j (cidx N b)) *
            (2 * Real.sqrt (64 / 9 * movS j (cidx N b)) + 1) ^ 3)) := by ring
        _ ≤ zLeC sys L n j * (Real.sqrt 2 * (8 / 3) * (19 / 3) ^ 3 *
            ((1 + movS j (cidx N b)) ^ 2 * Real.sqrt (1 + movS j (cidx N b)))) :=
          mul_le_mul_of_nonneg_left h1 hC
        _ ≤ zLeC sys L n j * (Real.sqrt 2 * (8 / 3) * (19 / 3) ^ 3 *
            (cXw sys L ^ 2 * Real.sqrt (cXw sys L) *
              ((1 + Asym sys L N b) ^ 2 * Real.sqrt (1 + Asym sys L N b)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) hC
        _ = _ := by ring
    · rw [if_neg hb]
      simp only [hWdef, if_neg hb, mul_zero]
      exact le_rfl
  have hform := norm_inner_kop_le₂ (zaLe sys L p₀ N n) u u
  have hpt : ∀ a b, ‖u.ofLp a‖ * ‖u.ofLp b‖ * ‖zaLe sys L p₀ N n a b‖ ≤
      |‖u.ofLp a‖| * |‖u.ofLp b‖| * K a b := by
    intro a b
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (norm_zaLe_le hL H hKernel hn a b) (by positivity)
  have hsch := sum_sym_kernel_le K hK0 hKs (fun b => CZle sys L n * W b) hcol (fun q => ‖u.ofLp q‖)
  calc ‖⟪u, FSKernel.kop (zaLe sys L p₀ N n) u⟫_ℂ‖ ≤
      ∑ a, ∑ b, ‖u.ofLp a‖ * ‖u.ofLp b‖ * ‖zaLe sys L p₀ N n a b‖ := hform
    _ ≤ ∑ a, ∑ b, |‖u.ofLp a‖| * |‖u.ofLp b‖| * K a b :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
    _ ≤ ∑ b, CZle sys L n * W b * ‖u.ofLp b‖ ^ 2 := hsch
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [hWdef]
        split_ifs <;> ring

end Form

/-! ## The critical moment -/

section Moment

variable {sys : CoulombSystem eta ν} {L : ℝ} {N : ℕ}

omit [Fintype ν] in
lemma kabs_le_of_inQ (hL : 0 < L) {n : ℕ} {q : Cfg eta N} (hq : InQ (n : ℝ) (cidx N q))
    (c : Fin eta) : finitePlaneWaveKabs (2 * Real.pi / L) N (q c) ≤ gF L * ((n : ℝ) / 4) := by
  have hg := gF_pos hL
  have e := kabs_sq_eq (n := N) L (q c)
  have hk0 := kabs_nonneg (n := N) hL (q c)
  have hgl : gL L = gF L := rfl
  rw [hgl] at e
  have h1 : FSLattice.lsq (cidx N q c) ≤ ((n : ℝ) / 4) ^ 2 := hq c
  have h2 : finitePlaneWaveKabs (2 * Real.pi / L) N (q c) ^ 2 ≤ (gF L * ((n : ℝ) / 4)) ^ 2 := by
    rw [e, mul_pow]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  by_contra h
  have h3 := pow_lt_pow_left₀ (not_le.mp h) (by positivity) two_ne_zero
  linarith

omit [Fintype ν] in
open Classical in
/-- **The critical moment on the bulk ball**: for a good box state,
`Σ_{q ∈ Q} (1 + A)² √(1 + A) |u_q|² ≤ (1 + η/2)^{1/2} M² (1 + 2η n_d)` when `K/4 ≤ 2^{n_d}`. -/
theorem crit_moment_le (hL : 0 < L) {n nd : ℕ} (hnd : gF L * ((n : ℝ) / 4) ≤ 2 ^ nd) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) :
    ∑ q, (if InQ (n : ℝ) (cidx N q) then
      (1 + Asym sys L N q) ^ 2 * Real.sqrt (1 + Asym sys L N q) * ‖u.ofLp q‖ ^ 2 else 0) ≤
      (1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd) := by
  classical
  have hg := gF_pos hL
  have hM : 0 ≤ M := by
    have h := hu.1
    have := norm_nonneg u
    have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
    linarith
  set A' : Cfg eta N → ℝ := fun x => if InQ (n : ℝ) (cidx N x) then Asym sys L N x else 0 with hA'
  set k' : Fin eta → Cfg eta N → ℝ := fun a x =>
    if InQ (n : ℝ) (cidx N x) then finitePlaneWaveKabs (2 * Real.pi / L) N (x a) else 0 with hk'
  set w' : Cfg eta N → ℝ := fun x =>
    if InQ (n : ℝ) (cidx N x) then (1 + Asym sys L N x) ^ 2 * ‖u.ofLp x‖ ^ 2 else 0 with hw'
  have hA0 : ∀ x, 0 ≤ A' x := fun x => by
    simp only [hA']; split_ifs
    · exact FSGalerkin.Asym_nonneg sys L N x
    · exact le_rfl
  have hw0 : ∀ x, 0 ≤ w' x := fun x => by
    simp only [hw']; split_ifs
    · positivity
    · exact le_rfl
  have hAk : ∀ x (R : ℝ), 0 ≤ R → (∀ a, k' a x ≤ R) → A' x ≤ (eta : ℝ) / 2 * R ^ 2 := by
    intro x R hR hx
    simp only [hA']
    split_ifs with hq
    · refine Asym_le_of_kabs_le sys hL x R hR fun a => ?_
      have := hx a
      simp only [hk', if_pos hq] at this
      exact this
    · positivity
  have hkn : ∀ x, A' x ≤ (eta : ℝ) / 2 * (gF L * ((n : ℝ) / 4)) ^ 2 → ∀ a, k' a x ≤ (2 : ℝ) ^ nd := by
    intro x _ a
    simp only [hk']
    split_ifs with hq
    · exact (kabs_le_of_inQ hL hq a).trans hnd
    · positivity
  have hwt : ∑ x, (1 + Asym sys L N x) ^ 2 * ‖u.ofLp x‖ ^ 2 ≤ M ^ 2 := by
    have h := hu.1
    have hW : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖ ≤ M := by
      linarith [norm_nonneg u]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hW 2
    rw [norm_sq_wt] at h2
    refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) h2
    rw [Real.rpow_one]
  have hw1 : ∑ x, w' x ≤ M ^ 2 := by
    refine le_trans (Finset.sum_le_sum fun x _ => ?_) hwt
    simp only [hw']
    split_ifs
    · exact le_rfl
    · positivity
  have htail : ∀ a (l : ℝ), 1 ≤ l → ∑ x, (if l < k' a x then w' x else 0) ≤ M ^ 2 / l := by
    intro a l hl
    have h := (hu.2 a l hl).2
    have hl0 : 0 < l := by linarith
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [norm_sq_wt] at h2
    have heq : (∑ p, ((1 + Asym sys L N p) ^ (1 : ℝ)) ^ 2 * ‖(regTail L a l u).ofLp p‖ ^ 2) =
        ∑ p, if l < finitePlaneWaveKabs (2 * Real.pi / L) N (p a) then
          (1 + Asym sys L N p) ^ 2 * ‖u.ofLp p‖ ^ 2 else 0 := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [regTail_apply, Real.rpow_one]
      split_ifs <;> simp
    rw [heq] at h2
    have h3 : (1 * M * l ^ (-(1 / 2 : ℝ))) ^ 2 = M ^ 2 / l := by
      rw [one_mul, mul_pow, ← Real.rpow_natCast (l ^ (-(1 / 2 : ℝ))), ← Real.rpow_mul hl0.le]
      norm_num
      rw [Real.rpow_neg_one, div_eq_mul_inv]
    rw [h3] at h2
    refine le_trans (Finset.sum_le_sum fun x _ => ?_) h2
    simp only [hk', hw']
    by_cases hq : InQ (n : ℝ) (cidx N x)
    · simp only [hq, if_true]
      exact le_rfl
    · simp only [hq, if_false]
      split_ifs
      · positivity
      · exact le_rfl
      · positivity
      · exact le_rfl
  have key := FSDatum.moment_quarter_le_of_tails (η := eta) A' k' w' (cA := (eta : ℝ) / 2)
    (E₀ := (eta : ℝ) / 2 * (gF L * ((n : ℝ) / 4)) ^ 2) (T := M) nd (by positivity) hA0 hw0 hAk hkn
    hw1 htail
  refine le_trans (le_of_eq ?_) key
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hq : InQ (n : ℝ) (cidx N x)
  · have hAx : A' x ≤ (eta : ℝ) / 2 * (gF L * ((n : ℝ) / 4)) ^ 2 :=
      hAk x _ (by positivity) fun a => by
        simp only [hk', if_pos hq]; exact kabs_le_of_inQ hL hq a
    rw [if_pos hq, if_pos hAx]
    simp only [hA', hw', if_pos hq]
    rw [Real.sqrt_eq_rpow]
    ring
  · rw [if_neg hq]
    simp only [hA', hw', if_neg hq]
    simp

end Moment

/-! ## The pinned current on a good state -/

section Good

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

/-- **The pinned symbol current at the target rate**:
`|⟨u, Z^≤ u⟩| ≤ C_Z (1 + η/2)^{1/2} M² (1 + 2η n_d)`, with `C_Z ~ n⁻³` (`zLeC`). -/
theorem norm_form_zaLe_good (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 8 ≤ n) {nd : ℕ} (hnd : gF L * ((n : ℝ) / 4) ≤ 2 ^ nd) {M : ℝ} {u : En eta N}
    (hu : IsGood sys L 1 M u) :
    ‖⟪u, FSKernel.kop (zaLe sys L p₀ N n) u⟫_ℂ‖ ≤
      CZle sys L n * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd)) := by
  have hC : 0 ≤ CZle sys L n := by
    unfold CZle
    refine Finset.sum_nonneg fun j _ => ?_
    have := zLeC_nonneg (sys := sys) (n := n) hL j
    have : 0 ≤ cXw sys L := by
      unfold cXw; have := gF_pos hL; have := one_le_mmax sys; positivity
    positivity
  exact (norm_form_zaLe_le hL H hKernel hn u).trans
    (mul_le_mul_of_nonneg_left (crit_moment_le hL hnd hu) hC)

end Good

end FSFlux
