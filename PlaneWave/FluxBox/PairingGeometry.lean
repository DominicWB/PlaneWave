import PlaneWave.FluxBox.ReflectionLatticeSums

/-!
# Flux route, stage 3, part 35: the same-channel word — geometry of the pairing

For cold `b, c` on one `j`-line (transfer `θ_c = chT c b`) and `θ` a transfer from `b`:

* the **weight** `wgt_j(k) = Σ_{r moved by j} |k_r|` controls the drift: `Σ_i |c_j(k)_i| ≤ 3 wgt_j(k)`
  (`sum_abs_cCh_le`);
* **far transfers** (`lsq_ge_of_notP`, `lsq_ge_of_notP'`): `b + θ ∉ P` or `c - θ ∉ P` force
  `|θ| ≥ n/2`; then `e_b(θ), e_c(-θ) ≥ (g²/8m) |θ|²` (`eL_ge`, `eL_neg_ge`) and
  `|e_b(θ) - e_c(-θ)| ≤ 6 g² |θ| (wgt(b) + wgt(c))` (`eL_sub_le`);
* **layers** (`layer_of`): where `[b + t ∈ P] ≠ [c - t ∈ P]`, some moved register `r` and coordinate `i`
  have `n - w < |b_{r,i} ± t_i| ≤ n + w`, `w = |b_{r,i} + c_{r,i}|`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Masses, drifts and weights -/

section Drift

variable {sys : CoulombSystem eta ν}

omit [Fintype ν] in
lemma half_le_muCh (j : Ch eta) : 1 / 2 ≤ muCh sys j := by
  cases j with
  | inl a => have := sys.one_le_mass a; simp only [muCh]; linarith
  | inr pr =>
    simp only [muCh]
    have h1 := sys.one_le_mass pr.1.1
    have h2 := sys.one_le_mass pr.1.2
    rw [le_div_iff₀ (by linarith)]
    nlinarith

omit [Fintype ν] in
lemma muCh_le_mmax' (j : Ch eta) : muCh sys j ≤ mmax sys := by
  cases j with
  | inl a => simp only [muCh]; exact mass_le_mmax sys a
  | inr pr =>
    simp only [muCh]
    have h1 := sys.one_le_mass pr.1.1
    have h2 := sys.one_le_mass pr.1.2
    have h3 := mass_le_mmax sys pr.1.1
    rw [div_le_iff₀ (by linarith)]
    nlinarith

/-- The weight of a configuration on the registers moved by `j`. -/
noncomputable def wgt (j : Ch eta) (k : Cf eta) : ℝ := ∑ r ∈ moved j, FSChannel.rho (k r)

omit [Fintype ν] in
lemma wgt_nonneg (j : Ch eta) (k : Cf eta) : 0 ≤ wgt j k :=
  Finset.sum_nonneg fun _ _ => FSChannel.rho_nonneg _

omit [Fintype ν] in
lemma abs_coord_le_rho'' (k : Lattice3) (i : Fin 3) : |((k i : ℤ) : ℝ)| ≤ FSChannel.rho k :=
  abs_coord_le_rho k i

omit [Fintype ν] in
/-- `Σ_i |c_j(k)_i| ≤ 3 wgt_j(k)`. -/
lemma sum_abs_cCh_le (j : Ch eta) (k : Cf eta) : ∑ i, |cCh sys j k i| ≤ 3 * wgt j k := by
  cases j with
  | inl a =>
    simp only [cCh, wgt, moved, Finset.sum_singleton]
    have h : ∀ i, |((k a i : ℤ) : ℝ)| ≤ FSChannel.rho (k a) := fun i => abs_coord_le_rho (k a) i
    rw [Fin.sum_univ_three]
    linarith [h 0, h 1, h 2]
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    simp only [wgt, moved]
    rw [Finset.sum_pair hne]
    have h1 := sys.one_le_mass pr.1.1
    have h2 := sys.one_le_mass pr.1.2
    set m1 := sys.mass pr.1.1
    set m2 := sys.mass pr.1.2
    have hμ1 : m1 * m2 / (m1 + m2) / m1 ≤ 1 := by
      rw [div_div, div_le_one (by positivity)]; nlinarith
    have hμ2 : m1 * m2 / (m1 + m2) / m2 ≤ 1 := by
      rw [div_div, div_le_one (by positivity)]; nlinarith
    have hpt : ∀ i, |cCh sys (.inr pr) k i| ≤ |((k pr.1.1 i : ℤ) : ℝ)| + |((k pr.1.2 i : ℤ) : ℝ)| := by
      intro i
      simp only [cCh, muCh]
      have e : m1 * m2 / (m1 + m2) * ((k pr.1.1 i : ℝ) / m1 - (k pr.1.2 i : ℝ) / m2) =
          (m1 * m2 / (m1 + m2) / m1) * (k pr.1.1 i : ℝ) - (m1 * m2 / (m1 + m2) / m2) * (k pr.1.2 i : ℝ) := by
        field_simp
      rw [e]
      have hp1 : 0 ≤ m1 * m2 / (m1 + m2) / m1 := by positivity
      have hp2 : 0 ≤ m1 * m2 / (m1 + m2) / m2 := by positivity
      calc |(m1 * m2 / (m1 + m2) / m1) * (k pr.1.1 i : ℝ) - (m1 * m2 / (m1 + m2) / m2) * (k pr.1.2 i : ℝ)| ≤
          |(m1 * m2 / (m1 + m2) / m1) * (k pr.1.1 i : ℝ)| + |(m1 * m2 / (m1 + m2) / m2) * (k pr.1.2 i : ℝ)| :=
          abs_sub _ _
        _ ≤ |((k pr.1.1 i : ℤ) : ℝ)| + |((k pr.1.2 i : ℤ) : ℝ)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hp1, abs_of_nonneg hp2]
          have := abs_nonneg ((k pr.1.1 i : ℤ) : ℝ)
          have := abs_nonneg ((k pr.1.2 i : ℤ) : ℝ)
          nlinarith
    calc ∑ i, |cCh sys (.inr pr) k i| ≤ ∑ i : Fin 3, (|((k pr.1.1 i : ℤ) : ℝ)| + |((k pr.1.2 i : ℤ) : ℝ)|) :=
          Finset.sum_le_sum fun i _ => hpt i
      _ ≤ 3 * (FSChannel.rho (k pr.1.1) + FSChannel.rho (k pr.1.2)) := by
          rw [Fin.sum_univ_three]
          have a0 := abs_coord_le_rho (k pr.1.1) 0
          have a1 := abs_coord_le_rho (k pr.1.1) 1
          have a2 := abs_coord_le_rho (k pr.1.1) 2
          have b0 := abs_coord_le_rho (k pr.1.2) 0
          have b1 := abs_coord_le_rho (k pr.1.2) 1
          have b2 := abs_coord_le_rho (k pr.1.2) 2
          linarith

omit [Fintype ν] in
lemma cCh_add (j : Ch eta) (k k' : Cf eta) (i : Fin 3) :
    cCh sys j (k + k') i = cCh sys j k i + cCh sys j k' i := by
  cases j with
  | inl a => simp [cCh]
  | inr pr => simp only [cCh, Pi.add_apply]; push_cast; ring

omit [Fintype ν] in
lemma abs_sum_mul_le (θ : Lattice3) (c : Fin 3 → ℝ) :
    |∑ i, ((θ i : ℤ) : ℝ) * c i| ≤ FSChannel.rho θ * ∑ i, |c i| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_coord_le_rho θ i) (abs_nonneg _)

omit [Fintype ν] in
lemma slabF_ge (θ : Lattice3) (c : Fin 3 → ℝ) :
    FSLattice.lsq θ - 2 * (FSChannel.rho θ * ∑ i, |c i|) ≤ FSLattice.slabF c θ := by
  unfold FSLattice.slabF
  have := abs_sum_mul_le θ c
  have := neg_abs_le (∑ i, ((θ i : ℤ) : ℝ) * c i)
  linarith

end Drift

/-! ## Cold configurations and far transfers -/

section Far

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

omit [Fintype ν] in
lemma wgt_cold (j : Ch eta) {k : Cf eta} (hk : InC (n : ℝ) (cst sys) k) :
    wgt j k ≤ 2 * (cst sys * n) := by
  unfold wgt
  have hcard : (moved j).card ≤ 2 := by
    cases j with
    | inl a => simp [moved]
    | inr pr => simp only [moved]; exact Finset.card_le_two
  calc ∑ r ∈ moved j, FSChannel.rho (k r) ≤ ∑ _r ∈ moved j, cst sys * n :=
        Finset.sum_le_sum fun r _ => rho_le_of_inC hk r
    _ = (moved j).card * (cst sys * n) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (cst sys * n) := by
        have : ((moved j).card : ℝ) ≤ 2 := by exact_mod_cast hcard
        have := cst_mul_nonneg (sys := sys) (n := n)
        nlinarith

/-- The sign of a moved register: `tr_j τ r = ε_r τ`. -/
def sgnR (j : Ch eta) (r : Fin eta) : ℤ :=
  match j with
  | .inl _ => 1
  | .inr pr => if r = pr.1.1 then 1 else -1

omit [Fintype ν] in
lemma sgnR_sign (j : Ch eta) (r : Fin eta) : sgnR j r = 1 ∨ sgnR j r = -1 := by
  cases j with
  | inl a => left; rfl
  | inr pr => simp only [sgnR]; split_ifs <;> simp

omit [Fintype ν] in
lemma tr_apply_sgn (j : Ch eta) {r : Fin eta} (hr : r ∈ moved j) (τ : Lattice3) :
    tr j τ r = sgnR j r • τ := by
  cases j with
  | inl a =>
    simp only [moved, Finset.mem_singleton] at hr
    subst hr
    simp [tr, sgnR]
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    simp only [moved, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · simp [tr, sgnR, Pi.single_eq_of_ne hne]
    · simp [tr, sgnR, hne.symm]

omit [Fintype ν] in
lemma coord_tr (j : Ch eta) {r : Fin eta} (hr : r ∈ moved j) (τ : Lattice3) (i : Fin 3) :
    (tr j τ r i : ℤ) = sgnR j r * τ i := by
  rw [tr_apply_sgn j hr τ]; rfl

omit [Fintype ν] in
/-- **A far transfer from cold**: `b + tr_j θ ∉ P` with `b` cold forces `|θ| ≥ n/2`. -/
lemma lsq_ge_of_notP {j : Ch eta} {k : Cf eta} (hk : InC (n : ℝ) (cst sys) k) {θ : Lattice3}
    (h : ¬ InP (n : ℝ) (k + tr j θ)) : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ := by
  simp only [InP, not_forall, not_le] at h
  obtain ⟨r, i, hri⟩ := h
  have hcs := cst_le32 sys
  have hc0 := cst_pos sys
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hkr : |((k r i : ℤ) : ℝ)| ≤ cst sys * n := (abs_coord_le_rho (k r) i).trans (rho_le_of_inC hk r)
  by_cases hr : r ∈ moved j
  · have e : ((k + tr j θ) r i : ℤ) = k r i + sgnR j r * θ i := by
      rw [Pi.add_apply, Pi.add_apply, coord_tr j hr θ i]
    rw [e] at hri
    push_cast at hri
    have hθi : (n : ℝ) / 2 ≤ |((θ i : ℤ) : ℝ)| := by
      have h1 := abs_add_le ((k r i : ℤ) : ℝ) ((sgnR j r : ℝ) * ((θ i : ℤ) : ℝ))
      have h2 : |(sgnR j r : ℝ) * ((θ i : ℤ) : ℝ)| = |((θ i : ℤ) : ℝ)| := by
        rcases sgnR_sign j r with h | h <;> rw [h] <;> simp
      nlinarith
    have h3 := sq_coord_le_lsq θ i
    have h4 : ((n : ℝ) / 2) ^ 2 ≤ ((θ i : ℤ) : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hθi 2
      rwa [sq_abs] at this
    linarith
  · have e : ((k + tr j θ) r i : ℤ) = k r i := by
      rw [Pi.add_apply, Pi.add_apply, tr_apply_not_moved j θ hr]; simp
    rw [e] at hri
    nlinarith

omit [Fintype ν] in
lemma tr_neg' (j : Ch eta) (θ : Lattice3) : tr j (-θ) = -tr j θ := by
  have h := tr_sub j 0 θ
  rw [tr_zero, zero_sub, zero_sub] at h
  exact h

omit [Fintype ν] in
/-- `c - tr_j θ ∉ P` with `c` cold forces `|θ| ≥ n/2`. -/
lemma lsq_ge_of_notP' {j : Ch eta} {k : Cf eta} (hk : InC (n : ℝ) (cst sys) k) {θ : Lattice3}
    (h : ¬ InP (n : ℝ) (k - tr j θ)) : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ := by
  have e : k - tr j θ = k + tr j (-θ) := by rw [tr_neg', sub_eq_add_neg]
  rw [e] at h
  have := lsq_ge_of_notP hk h
  rwa [lsq_neg] at this

omit [Fintype ν] in
lemma rho_ge_of_lsq {R : ℝ} {θ : Lattice3} (h : R ^ 2 ≤ FSLattice.lsq θ) : R ≤ FSChannel.rho θ := by
  unfold FSChannel.rho; exact Real.le_sqrt_of_sq_le h

omit [Fintype ν] in
/-- On far transfers the slab form of a cold drift is `≥ |θ|²/4`. -/
lemma slabF_cold_ge (j : Ch eta) {k : Cf eta} (hk : InC (n : ℝ) (cst sys) k) {θ : Lattice3}
    (hθ : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ) :
    FSLattice.lsq θ / 4 ≤ FSLattice.slabF (cCh sys j k) θ := by
  have h1 := slabF_ge θ (cCh sys j k)
  have h2 := sum_abs_cCh_le (sys := sys) j k
  have h3 := wgt_cold j hk
  have hρ : (n : ℝ) / 2 ≤ FSChannel.rho θ := rho_ge_of_lsq hθ
  have hρ0 : 0 ≤ FSChannel.rho θ := FSChannel.rho_nonneg θ
  have hcs := cst_le32 sys
  have hc0 := (cst_pos sys).le
  have hl : FSLattice.lsq θ = FSChannel.rho θ ^ 2 := lsq_eq_rho_sq θ
  have hsum : ∑ i, |cCh sys j k i| ≤ 6 * (cst sys * n) := by linarith
  have hn : (n : ℝ) ≤ 2 * FSChannel.rho θ := by linarith
  have h4 : 2 * (FSChannel.rho θ * ∑ i, |cCh sys j k i|) ≤ 3 / 4 * FSLattice.lsq θ := by
    calc 2 * (FSChannel.rho θ * ∑ i, |cCh sys j k i|) ≤
          2 * (FSChannel.rho θ * (6 * (cst sys * n))) := by gcongr
      _ ≤ 2 * (FSChannel.rho θ * (6 * (cst sys * (2 * FSChannel.rho θ)))) := by gcongr
      _ = 24 * cst sys * FSChannel.rho θ ^ 2 := by ring
      _ ≤ 3 / 4 * FSLattice.lsq θ := by
          rw [hl]; nlinarith [sq_nonneg (FSChannel.rho θ)]
  linarith

omit [Fintype ν] in
/-- **The energy of a far transfer from cold**: `e_k(θ) ≥ (g²/8m) |θ|²`. -/
lemma eL_ge (j : Ch eta) {k : Cf eta} (hk : InC (n : ℝ) (cst sys) k) {θ : Lattice3}
    (hθ : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ) :
    gF L ^ 2 / (8 * mmax sys) * FSLattice.lsq θ ≤ eL sys L j k θ := by
  unfold eL
  have h1 := slabF_cold_ge j hk hθ
  have hμ := muCh_pos sys j
  have hμm := muCh_le_mmax' (sys := sys) j
  have hm1 := one_le_mmax (sys := sys)
  have hg : 0 ≤ gF L ^ 2 := sq_nonneg _
  have hl := FSLattice.lsq_nonneg θ
  calc gF L ^ 2 / (8 * mmax sys) * FSLattice.lsq θ ≤
        gF L ^ 2 / (2 * muCh sys j) * (FSLattice.lsq θ / 4) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left hμm (mul_nonneg hg hl)
        nlinarith
    _ ≤ _ := by gcongr

omit [Fintype ν] in
lemma eL_pos (j : Ch eta) {k : Cf eta} (hk : InC (n : ℝ) (cst sys) k) {θ : Lattice3}
    (hθ : ((n : ℝ) / 2) ^ 2 ≤ FSLattice.lsq θ) (hn : 1 ≤ n) (hL : 0 < L) : 0 < eL sys L j k θ := by
  refine lt_of_lt_of_le ?_ (eL_ge j hk hθ)
  have hm1 := one_le_mmax (sys := sys)
  have hg : 0 < gF L := by unfold gF; positivity
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : 0 < FSLattice.lsq θ := lt_of_lt_of_le (by positivity) hθ
  positivity

omit [Fintype ν] in
/-- **The two energies of the pairing**: `|e_k(θ) - e_{k'}(-θ)| ≤ 6 g² |θ| (wgt k + wgt k')`. -/
lemma eL_sub_le (j : Ch eta) (k k' : Cf eta) (θ : Lattice3) :
    |eL sys L j k θ - eL sys L j k' (-θ)| ≤
      6 * gF L ^ 2 * FSChannel.rho θ * (wgt j k + wgt j k') := by
  have e : eL sys L j k θ - eL sys L j k' (-θ) =
      gF L ^ 2 / muCh sys j * ∑ i, ((θ i : ℤ) : ℝ) * (cCh sys j k i + cCh sys j k' i) := by
    have hμ := (muCh_pos sys j).ne'
    unfold eL FSLattice.slabF
    rw [lsq_neg]
    simp only [Pi.neg_apply, Int.cast_neg, Fin.sum_univ_three]
    field_simp
    ring
  rw [e, abs_mul]
  have hμ := muCh_pos sys j
  have hμ2 := half_le_muCh (sys := sys) j
  have h1 : |gF L ^ 2 / muCh sys j| ≤ 2 * gF L ^ 2 := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hμ]; nlinarith [sq_nonneg (gF L)]
  have h2 := abs_sum_mul_le θ (fun i => cCh sys j k i + cCh sys j k' i)
  have h3 : ∑ i, |cCh sys j k i + cCh sys j k' i| ≤ 3 * (wgt j k + wgt j k') := by
    have := sum_abs_cCh_le (sys := sys) j k
    have := sum_abs_cCh_le (sys := sys) j k'
    calc ∑ i, |cCh sys j k i + cCh sys j k' i| ≤ ∑ i, (|cCh sys j k i| + |cCh sys j k' i|) :=
          Finset.sum_le_sum fun i _ => abs_add_le _ _
      _ = ∑ i, |cCh sys j k i| + ∑ i, |cCh sys j k' i| := Finset.sum_add_distrib
      _ ≤ _ := by linarith
  have hρ := FSChannel.rho_nonneg θ
  calc |gF L ^ 2 / muCh sys j| * |∑ i, ((θ i : ℤ) : ℝ) * (cCh sys j k i + cCh sys j k' i)| ≤
      (2 * gF L ^ 2) * (FSChannel.rho θ * (3 * (wgt j k + wgt j k'))) :=
        mul_le_mul h1 (h2.trans (mul_le_mul_of_nonneg_left h3 hρ)) (abs_nonneg _) (by positivity)
    _ = _ := by ring

omit [Fintype ν] in
lemma onCh_apply_not_moved {j : Ch eta} {c b : Cf eta} (h : OnCh j c b) {r : Fin eta}
    (hr : r ∉ moved j) : c r = b r := by
  rw [h, Pi.add_apply, tr_apply_not_moved j _ hr, add_zero]

omit [Fintype ν] in
/-- **The layer of a disagreement**: if `[b + tr θ ∈ P_s] ≠ [c - tr θ ∈ P_s]` for `c` on the `j`-line
of `b`, some moved register `r` and coordinate `i` have `s - w < |b_{r,i} + ε_r θ_i| ≤ s + w`,
`w = |b_{r,i} + c_{r,i}|`. -/
lemma layer_of {j : Ch eta} {b c : Cf eta} (hcb : OnCh j c b) {s : ℝ} {θ : Lattice3}
    (h : ¬ (InP s (b + tr j θ) ↔ InP s (c - tr j θ))) :
    ∃ r ∈ moved j, ∃ i : Fin 3,
      s - |((b r i + c r i : ℤ) : ℝ)| < |((b r i + sgnR j r * θ i : ℤ) : ℝ)| ∧
      |((b r i + sgnR j r * θ i : ℤ) : ℝ)| ≤ s + |((b r i + c r i : ℤ) : ℝ)| := by
  have eb : ∀ r ∈ moved j, ∀ i, ((((b + tr j θ) r i : ℤ)) : ℝ) = ((b r i + sgnR j r * θ i : ℤ) : ℝ) := by
    intro r hr i
    rw [Pi.add_apply, Pi.add_apply, coord_tr j hr θ i]
  have ec : ∀ r ∈ moved j, ∀ i, ((((c - tr j θ) r i : ℤ)) : ℝ) =
      ((b r i + c r i : ℤ) : ℝ) - ((b r i + sgnR j r * θ i : ℤ) : ℝ) := by
    intro r hr i
    rw [Pi.sub_apply, Pi.sub_apply, coord_tr j hr θ i]
    push_cast; ring
  have enb : ∀ r, r ∉ moved j → (b + tr j θ) r = b r := fun r hr => by
    rw [Pi.add_apply, tr_apply_not_moved j θ hr, add_zero]
  have enc : ∀ r, r ∉ moved j → (c - tr j θ) r = b r := fun r hr => by
    rw [Pi.sub_apply, tr_apply_not_moved j θ hr, sub_zero, onCh_apply_not_moved hcb hr]
  by_cases hb : InP s (b + tr j θ)
  · have hc : ¬ InP s (c - tr j θ) := fun hc => h ⟨fun _ => hc, fun _ => hb⟩
    simp only [InP, not_forall, not_le] at hc
    obtain ⟨r, i, hri⟩ := hc
    by_cases hr : r ∈ moved j
    · refine ⟨r, hr, i, ?_, ?_⟩
      · have hbi := hb r i
        rw [ec r hr i] at hri
        have := abs_sub ((b r i + c r i : ℤ) : ℝ) ((b r i + sgnR j r * θ i : ℤ) : ℝ)
        linarith
      · have hbi := hb r i
        rw [eb r hr i] at hbi
        have := abs_nonneg ((b r i + c r i : ℤ) : ℝ)
        linarith
    · exfalso
      have := hb r i
      rw [enb r hr] at this; rw [enc r hr] at hri; linarith
  · have hc : InP s (c - tr j θ) := by
      by_contra hc; exact h ⟨fun hb' => absurd hb' hb, fun hc' => absurd hc' hc⟩
    simp only [InP, not_forall, not_le] at hb
    obtain ⟨r, i, hri⟩ := hb
    by_cases hr : r ∈ moved j
    · refine ⟨r, hr, i, ?_, ?_⟩
      · rw [eb r hr i] at hri
        have := abs_nonneg ((b r i + c r i : ℤ) : ℝ)
        linarith
      · have hci := hc r i
        rw [ec r hr i] at hci
        rw [eb r hr i] at hri
        have := abs_sub_abs_le_abs_sub ((b r i + sgnR j r * θ i : ℤ) : ℝ) ((b r i + c r i : ℤ) : ℝ)
        rw [abs_sub_comm] at hci
        linarith
    · exfalso
      have := hc r i
      rw [enc r hr] at this; rw [enb r hr] at hri; linarith

omit [Fintype ν] in
/-- Two cold configurations on one line differ by a short transfer. -/
lemma rho_sub_cold_le {k k' : Cf eta} (hk : InC (n : ℝ) (cst sys) k) (hk' : InC (n : ℝ) (cst sys) k')
    (r : Fin eta) : FSChannel.rho (k r - k' r) ≤ 2 * (cst sys * n) := by
  have h1 := FSChannel.rho_add_le (k r) (-k' r)
  rw [rho_neg', ← sub_eq_add_neg] at h1
  have := rho_le_of_inC hk r
  have := rho_le_of_inC hk' r
  linarith

omit [Fintype ν] in
lemma lsq_sub_ge_of_small {α θ : Lattice3} (h : 2 * FSChannel.rho α ≤ FSChannel.rho θ) :
    FSLattice.lsq θ / 4 ≤ FSLattice.lsq (α - θ) := by
  have h1 := rho_sub_ge θ α
  have h2 : FSChannel.rho (θ - α) = FSChannel.rho (α - θ) := by rw [← rho_neg' (α - θ), neg_sub]
  have hα := FSChannel.rho_nonneg α
  have hρ : FSChannel.rho θ / 2 ≤ FSChannel.rho (α - θ) := by linarith
  rw [lsq_eq_rho_sq θ, lsq_eq_rho_sq (α - θ)]
  have h0 : 0 ≤ FSChannel.rho θ / 2 := by have := FSChannel.rho_nonneg θ; linarith
  have := pow_le_pow_left₀ h0 hρ 2
  nlinarith

end Far

end FSFlux
