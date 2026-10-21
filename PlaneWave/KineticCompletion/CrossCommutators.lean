import PlaneWave.KineticCompletion.InverseMismatch

/-!
# Kinetic completion, part 2: directional derivatives and the cross commutators

The directional coordinate of a configuration, `y_d(k) = Σ_a d_a k_a` (`dsum`), changes along a
hop of channel `j` by `(d · ℓ_j) θ` (`dsum_tr`, `dl`): it is conserved when `d · ℓ_j = 0` and is
the hop's transfer when `d · ℓ_j = 1`. With the weight `Λ_d = (1 + |y_d|²)^{1/2}` (`lam`):

* `exists_dir`: for distinct channels `j ≠ k` there is `d` with `d · ℓ_j = 1`, `d · ℓ_k = 0` and
  `Σ_a |d_a| ≤ 2` (`lem:transverse`);
* `lam_mul_le`: `Λ_d Λ_e ≤ c_Λ (1 + A)` for such `d`, `e`, `c_Λ = 1 + 8 m_top/g²`;
* **`norm_Zj_le`** (eq:Zdirection): `‖Z_j u‖ ≤ C_Z(j) ‖Λ_d u‖` for `d · ℓ_j = 1`, where `Z_j` is the
  channel-`j` part of `Σ₂^bb` and `C_Z(j) = (chbT/n³)(2μ_j/g²)(C_D + 44000)(J_n + 3)² = O(n⁻³ log² n)`:
  Schur's test with the weight `Λ_d⁻¹` and the lattice sums `inv_mismatch_row`, `inv_mismatch_col`
  of `PlaneWave.KineticCompletion.InverseMismatch` (uniform in the centre of the hop);
* **`dir_hardy`** (eq:directionHardy): the channel-`k` Coulomb majorant obeys Hardy's inequality
  relative to `Λ_e` for `e · ℓ_k = 1` on every finite set of configurations (on each channel fibre
  `y_e` is a lattice coordinate, and the release's finite-support lattice Hardy inequality applies);
* **`norm_crossX_le`** (lem:crosscomm): the multi-channel part of `[Σ₂^bb, W_N]` obeys
  `‖Σ_{j ≠ k} (Z_j W_k - W_j Z_k) u‖ ≤ C_X(n) ‖(1 + A) u‖`, `C_X(n) = O(n⁻³ log² n)`.
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Directional coordinates -/

/-- The directional coordinate `y_d(k) = Σ_a d_a k_a`. -/
def dsum (d : Fin eta → ℤ) (k : Cf eta) : Lattice3 := ∑ a, d a • k a

/-- `d · ℓ_j`: the change of `y_d` per unit transfer of channel `j`. -/
def dl (d : Fin eta → ℤ) : Ch eta → ℤ
  | .inl a => d a
  | .inr pr => d pr.1.1 - d pr.1.2

lemma dsum_add (d : Fin eta → ℤ) (k k' : Cf eta) : dsum d (k + k') = dsum d k + dsum d k' := by
  unfold dsum
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

lemma dsum_sub (d : Fin eta → ℤ) (k k' : Cf eta) : dsum d (k - k') = dsum d k - dsum d k' := by
  unfold dsum
  simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

lemma dsum_single (d : Fin eta → ℤ) (a : Fin eta) (θ : Lattice3) :
    dsum d (Pi.single a θ) = d a • θ := by
  unfold dsum
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, smul_zero])
    (fun h => absurd (Finset.mem_univ a) h), Pi.single_eq_same]

lemma dsum_tr (d : Fin eta → ℤ) (j : Ch eta) (θ : Lattice3) : dsum d (tr j θ) = dl d j • θ := by
  cases j with
  | inl a => exact dsum_single d a θ
  | inr pr =>
    show dsum d (Pi.single pr.1.1 θ - Pi.single pr.1.2 θ) = (d pr.1.1 - d pr.1.2) • θ
    rw [dsum_sub, dsum_single, dsum_single, sub_smul]

/-- Along a channel with `d · ℓ_j = 1` the coordinate moves by the transfer. -/
lemma dsum_onCh_one {d : Fin eta → ℤ} {j : Ch eta} (hd : dl d j = 1) {k k' : Cf eta}
    (h : OnCh j k k') : dsum d k = dsum d k' + (k (lead j) - k' (lead j)) := by
  have e : k = k' + tr j (k (lead j) - k' (lead j)) := h
  conv_lhs => rw [e]
  rw [dsum_add, dsum_tr, hd, one_smul]

/-- Along a channel with `d · ℓ_j = 0` the coordinate is conserved. -/
lemma dsum_onCh_zero {d : Fin eta → ℤ} {j : Ch eta} (hd : dl d j = 0) {k k' : Cf eta}
    (h : OnCh j k k') : dsum d k = dsum d k' := by
  have e : k = k' + tr j (k (lead j) - k' (lead j)) := h
  conv_lhs => rw [e]
  rw [dsum_add, dsum_tr, hd, zero_smul, add_zero]

/-- The directional weight `Λ_d(k) = (1 + |y_d(k)|²)^{1/2}`. -/
noncomputable def lam (d : Fin eta → ℤ) (k : Cf eta) : ℝ :=
  Real.sqrt (1 + FSLattice.lsq (dsum d k))

lemma lam_pos (d : Fin eta → ℤ) (k : Cf eta) : 0 < lam d k :=
  Real.sqrt_pos.mpr (by have := FSLattice.lsq_nonneg (dsum d k); linarith)

lemma lam_sq (d : Fin eta → ℤ) (k : Cf eta) : lam d k ^ 2 = 1 + FSLattice.lsq (dsum d k) :=
  Real.sq_sqrt (by have := FSLattice.lsq_nonneg (dsum d k); linarith)

lemma lam_onCh_zero {d : Fin eta → ℤ} {j : Ch eta} (hd : dl d j = 0) {k k' : Cf eta}
    (h : OnCh j k k') : lam d k = lam d k' := by
  unfold lam; rw [dsum_onCh_zero hd h]

/-! ## Transverse directions -/

/-- `‖d‖₁ = Σ_a |d_a|`. -/
def l1 (d : Fin eta → ℤ) : ℤ := ∑ a, |d a|

lemma l1_single (a : Fin eta) (s : ℤ) : l1 (Pi.single a s : Fin eta → ℤ) = |s| := by
  unfold l1
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, abs_zero])
    (fun h => absurd (Finset.mem_univ a) h), Pi.single_eq_same]

lemma l1_add_le (d d' : Fin eta → ℤ) : l1 (d + d') ≤ l1 d + l1 d' := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => abs_add_le _ _

/-- **Transverse directions** (`lem:transverse`): for distinct channels `j ≠ k` there is an integer
vector `d` with `d · ℓ_j = 1`, `d · ℓ_k = 0` and `Σ_a |d_a| ≤ 2`. -/
theorem exists_dir (j k : Ch eta) (hjk : j ≠ k) :
    ∃ d : Fin eta → ℤ, dl d j = 1 ∧ dl d k = 0 ∧ l1 d ≤ 2 := by
  classical
  have hs1 : ∀ a : Fin eta, l1 (Pi.single a (1 : ℤ)) ≤ 2 := fun a => by rw [l1_single]; norm_num
  have hsn : ∀ a : Fin eta, l1 (Pi.single a (-1 : ℤ)) ≤ 2 := fun a => by rw [l1_single]; norm_num
  have hss : ∀ a b : Fin eta, l1 (Pi.single a (1 : ℤ) + Pi.single b 1) ≤ 2 := fun a b =>
    (l1_add_le _ _).trans (by rw [l1_single, l1_single]; norm_num)
  cases j with
  | inl a =>
    cases k with
    | inl b =>
      have hab : a ≠ b := fun h => hjk (by rw [h])
      exact ⟨Pi.single a 1, by simp [dl], by simp [dl, Pi.single_eq_of_ne hab.symm], hs1 a⟩
    | inr pr =>
      have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
      by_cases h1 : a = pr.1.1
      · subst h1
        refine ⟨Pi.single pr.1.1 1 + Pi.single pr.1.2 1, ?_, ?_, hss _ _⟩
        · simp [dl, Pi.single_eq_of_ne hne]
        · simp [dl, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
      · by_cases h2 : a = pr.1.2
        · subst h2
          refine ⟨Pi.single pr.1.2 1 + Pi.single pr.1.1 1, ?_, ?_, hss _ _⟩
          · simp [dl, Pi.single_eq_of_ne hne.symm]
          · simp [dl, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
        · refine ⟨Pi.single a 1, by simp [dl], ?_, hs1 a⟩
          simp [dl, Pi.single_eq_of_ne (Ne.symm h1), Pi.single_eq_of_ne (Ne.symm h2)]
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    cases k with
    | inl c =>
      by_cases h1 : c = pr.1.1
      · subst h1
        refine ⟨Pi.single pr.1.2 (-1), ?_, ?_, hsn _⟩
        · simp [dl, Pi.single_eq_of_ne hne]
        · simp [dl, Pi.single_eq_of_ne hne]
      · refine ⟨Pi.single pr.1.1 1, ?_, ?_, hs1 _⟩
        · simp [dl, Pi.single_eq_of_ne hne.symm]
        · simp [dl, Pi.single_eq_of_ne h1]
    | inr pr' =>
      have hne' : pr'.1.1 ≠ pr'.1.2 := ne_of_lt pr'.2
      by_cases h1 : pr.1.1 ≠ pr'.1.1 ∧ pr.1.1 ≠ pr'.1.2
      · refine ⟨Pi.single pr.1.1 1, ?_, ?_, hs1 _⟩
        · simp [dl, Pi.single_eq_of_ne hne.symm]
        · simp [dl, Pi.single_eq_of_ne (Ne.symm h1.1), Pi.single_eq_of_ne (Ne.symm h1.2)]
      · by_cases h2 : pr.1.2 ≠ pr'.1.1 ∧ pr.1.2 ≠ pr'.1.2
        · refine ⟨Pi.single pr.1.2 (-1), ?_, ?_, hsn _⟩
          · simp [dl, Pi.single_eq_of_ne hne]
          · simp [dl, Pi.single_eq_of_ne (Ne.symm h2.1), Pi.single_eq_of_ne (Ne.symm h2.2)]
        · exfalso
          apply hjk
          push Not at h1 h2
          have hlt := pr.2
          have hlt' := pr'.2
          have e : pr = pr' := by
            apply Subtype.ext
            apply Prod.ext
            · rcases (Classical.em (pr.1.1 = pr'.1.1)) with h | h
              · exact h
              · have h1' := h1 h
                rcases (Classical.em (pr.1.2 = pr'.1.1)) with h' | h'
                · exfalso
                  have : pr.1.2 < pr.1.1 := by rw [h', h1']; exact hlt'
                  exact absurd hlt (not_lt.mpr this.le)
                · exact absurd h1' (by
                    intro h3
                    have := h2 h'
                    rw [h3] at hne
                    exact hne this.symm)
            · rcases (Classical.em (pr.1.2 = pr'.1.2)) with h | h
              · exact h
              · exfalso
                have h2' : pr.1.2 = pr'.1.1 := by
                  by_contra hc; exact h (h2 hc)
                rcases (Classical.em (pr.1.1 = pr'.1.1)) with h3 | h3
                · rw [h3] at hne; exact hne h2'.symm
                · have h1' := h1 h3
                  have : pr.1.2 < pr.1.1 := by rw [h2', h1']; exact hlt'
                  exact absurd hlt (not_lt.mpr this.le)
          rw [e]

/-! ## The kinetic bound for two directions -/

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

omit [Fintype ν] in
/-- Cauchy–Schwarz for the directional coordinate:
`|y_d(k)|² ≤ (Σ_a |d_a|) Σ_a |d_a| |k_a|²`. -/
lemma lsq_dsum_cs (d : Fin eta → ℤ) (k : Cf eta) :
    FSLattice.lsq (dsum d k) ≤ (∑ a, |(d a : ℝ)|) * ∑ a, |(d a : ℝ)| * FSLattice.lsq (k a) := by
  have hcoord : ∀ i : Fin 3, ((dsum d k i : ℤ) : ℝ) ^ 2 ≤
      (∑ a, |(d a : ℝ)|) * ∑ a, |(d a : ℝ)| * ((k a i : ℤ) : ℝ) ^ 2 := by
    intro i
    have e : ((dsum d k i : ℤ) : ℝ) = ∑ a, (d a : ℝ) * ((k a i : ℤ) : ℝ) := by
      simp [dsum, Finset.sum_apply]
    rw [e]
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
      (r := fun a => (d a : ℝ) * ((k a i : ℤ) : ℝ)) (f := fun a => |(d a : ℝ)|)
      (g := fun a => |(d a : ℝ)| * ((k a i : ℤ) : ℝ) ^ 2) (fun a _ => abs_nonneg _)
      (fun a _ => by positivity) (fun a _ => by
        apply le_of_eq
        rw [mul_pow, ← mul_assoc, ← sq, sq_abs])
  have e1 : FSLattice.lsq (dsum d k) = ∑ i : Fin 3, ((dsum d k i : ℤ) : ℝ) ^ 2 :=
    FSLattice.lsq_eq_sum _
  have e2 : ∀ a, FSLattice.lsq (k a) = ∑ i : Fin 3, ((k a i : ℤ) : ℝ) ^ 2 := fun a =>
    FSLattice.lsq_eq_sum _
  rw [e1]
  calc ∑ i : Fin 3, ((dsum d k i : ℤ) : ℝ) ^ 2
      ≤ ∑ i : Fin 3, (∑ a, |(d a : ℝ)|) * ∑ a, |(d a : ℝ)| * ((k a i : ℤ) : ℝ) ^ 2 :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = (∑ a, |(d a : ℝ)|) * ∑ a, |(d a : ℝ)| * FSLattice.lsq (k a) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [e2, Finset.mul_sum]

omit [Fintype ν] in
lemma sum_abs_le_of_l1 {d : Fin eta → ℤ} (hd : l1 d ≤ 2) : ∑ a, |(d a : ℝ)| ≤ 2 := by
  have h : ((l1 d : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hd
  simpa [l1] using h

omit [Fintype ν] in
/-- `|y_d(k)|² ≤ 4 Σ_a |k_a|²` when `Σ_a |d_a| ≤ 2`. -/
lemma lsq_dsum_le (d : Fin eta → ℤ) (hd : l1 d ≤ 2) (k : Cf eta) :
    FSLattice.lsq (dsum d k) ≤ 4 * ∑ a, FSLattice.lsq (k a) := by
  have hl1 := sum_abs_le_of_l1 hd
  have hda : ∀ a, |(d a : ℝ)| ≤ 2 := fun a =>
    (Finset.single_le_sum (f := fun a => |(d a : ℝ)|) (fun a _ => abs_nonneg _)
      (Finset.mem_univ a)).trans hl1
  refine (lsq_dsum_cs d k).trans ?_
  calc (∑ a, |(d a : ℝ)|) * ∑ a, |(d a : ℝ)| * FSLattice.lsq (k a)
      ≤ 2 * ∑ a, 2 * FSLattice.lsq (k a) := by
        apply mul_le_mul hl1 (Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_right (hda a) (FSLattice.lsq_nonneg _))
          (Finset.sum_nonneg fun a _ => by have := FSLattice.lsq_nonneg (k a); positivity)
          (by norm_num)
    _ = 4 * ∑ a, FSLattice.lsq (k a) := by rw [← Finset.mul_sum]; ring

omit [Fintype ν] in
/-- On the bulk block, `|y_d(k)| ≤ n/2` when `Σ_a |d_a| ≤ 2`. -/
lemma lsq_dsum_le_of_inQ {d : Fin eta → ℤ} (hd : l1 d ≤ 2) {n : ℕ} {k : Cf eta}
    (hk : InQ (n : ℝ) k) : FSLattice.lsq (dsum d k) ≤ ((n : ℝ) / 2) ^ 2 := by
  have hl1 := sum_abs_le_of_l1 hd
  refine (lsq_dsum_cs d k).trans ?_
  have h2 : ∑ a, |(d a : ℝ)| * FSLattice.lsq (k a) ≤ ∑ a, |(d a : ℝ)| * ((n : ℝ) / 4) ^ 2 :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hk a) (abs_nonneg _)
  rw [← Finset.sum_mul] at h2
  have h3 : 0 ≤ ∑ a, |(d a : ℝ)| * FSLattice.lsq (k a) :=
    Finset.sum_nonneg fun a _ => by have := FSLattice.lsq_nonneg (k a); positivity
  calc (∑ a, |(d a : ℝ)|) * ∑ a, |(d a : ℝ)| * FSLattice.lsq (k a)
      ≤ 2 * ((∑ a, |(d a : ℝ)|) * ((n : ℝ) / 4) ^ 2) :=
        mul_le_mul hl1 h2 h3 (by norm_num)
    _ ≤ 2 * (2 * ((n : ℝ) / 4) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right hl1 (sq_nonneg _)
    _ = ((n : ℝ) / 2) ^ 2 := by ring

variable (sys) in
/-- `c_Λ = 1 + 8 m_top/g²`. -/
noncomputable def cLam (L : ℝ) : ℝ := 1 + 8 * mtop sys / gF L ^ 2

omit [Fintype ν] in
lemma cLam_pos (L : ℝ) : 0 < cLam sys L := by
  unfold cLam
  have := one_le_mtop sys
  have : 0 ≤ 8 * mtop sys / gF L ^ 2 := by positivity
  linarith

omit [Fintype ν] in
/-- The kinetic energy dominates the register momenta: `Σ_a |k_a|² ≤ (2 m_top/g²) A`. -/
lemma sum_lsq_le_Asym (hL : 0 < L) (q : Cfg eta n) :
    ∑ a, FSLattice.lsq (cidx n q a) ≤ 2 * mtop sys / gF L ^ 2 * Asym sys L n q := by
  rw [Asym_eq_Ek]
  unfold Ek E
  have hg := gF_pos hL
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have hm := sys.mass_pos a
  have hmt := mass_le_mtop sys a
  have hl : FSLattice.lsq (cidx n q a) = nsq (finiteConfigLatticeIndex eta n q a) := rfl
  rw [hl]
  have h0 := nsq_nonneg (finiteConfigLatticeIndex eta n q a)
  rw [← mul_assoc]
  have hc : 1 ≤ 2 * mtop sys / gF L ^ 2 * (gF L ^ 2 / (2 * sys.mass a)) := by
    rw [show 2 * mtop sys / gF L ^ 2 * (gF L ^ 2 / (2 * sys.mass a)) = mtop sys / sys.mass a by
      field_simp]
    rw [le_div_iff₀ hm]; linarith
  nlinarith

omit [Fintype ν] in
/-- **`Λ_d Λ_e ≤ c_Λ (1 + A)`** (`lem:transverse`, last clause). -/
lemma lam_mul_le (hL : 0 < L) {d e : Fin eta → ℤ} (hd : l1 d ≤ 2) (he : l1 e ≤ 2)
    (q : Cfg eta n) :
    lam d (cidx n q) * lam e (cidx n q) ≤ cLam sys L * (1 + Asym sys L n q) := by
  have h1 := lsq_dsum_le d hd (cidx n q)
  have h2 := lsq_dsum_le e he (cidx n q)
  have h3 := sum_lsq_le_Asym (sys := sys) hL q
  have hA := Asym_nonneg (sys := sys) (L := L) q
  have hamgm : lam d (cidx n q) * lam e (cidx n q) ≤
      (lam d (cidx n q) ^ 2 + lam e (cidx n q) ^ 2) / 2 := by
    nlinarith [sq_nonneg (lam d (cidx n q) - lam e (cidx n q))]
  rw [lam_sq, lam_sq] at hamgm
  refine hamgm.trans ?_
  unfold cLam
  have hg := gF_pos hL
  have hX : 0 ≤ 8 * mtop sys / gF L ^ 2 * Asym sys L n q := by
    have := one_le_mtop sys; positivity
  have e : 8 * mtop sys / gF L ^ 2 * Asym sys L n q = 4 * (2 * mtop sys / gF L ^ 2 * Asym sys L n q) := by
    ring
  have hY : 0 ≤ 8 * mtop sys / gF L ^ 2 := by have := one_le_mtop sys; positivity
  have e2 : (1 + 8 * mtop sys / gF L ^ 2) * (1 + Asym sys L n q) =
      1 + Asym sys L n q + 8 * mtop sys / gF L ^ 2 + 8 * mtop sys / gF L ^ 2 * Asym sys L n q := by
    ring
  rw [e2]
  linarith

/-! ## Schur's test with a weight on the cube -/

/-- Schur's test with the weight `w⁻¹`: rows `w(q) Σ_p |κ(q,p)|/w(p)² ≤ a` and columns
`Σ_q |κ(q,p)|/w(q) ≤ b` give `‖kop κ u‖ ≤ √(ab) ‖w u‖`. -/
theorem norm_kop_le_wt {X : Type*} [Fintype X] (κ : X → X → ℂ) (w : X → ℝ) (hw : ∀ x, 0 < w x)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrow : ∀ q, w q * ∑ p, ‖κ q p‖ / w p ^ 2 ≤ a) (hcol : ∀ p, ∑ q, ‖κ q p‖ / w q ≤ b)
    (u : EuclideanSpace ℂ X) :
    ‖FSKernel.kop κ u‖ ≤ Real.sqrt (a * b) * ‖FSKernel.dg (fun q => (w q : ℂ)) u‖ := by
  have h := FSLattice.wschur Finset.univ Finset.univ (fun q p => κ q p * ((w p)⁻¹ : ℂ))
    (fun q => (w q)⁻¹) (fun p => (w p)⁻¹) (fun p _ => inv_pos.mpr (hw p)) ha
    (fun q _ => by
      have hq := hw q
      have e : ∑ p, ‖κ q p * ((w p)⁻¹ : ℂ)‖ * (w p)⁻¹ = ∑ p, ‖κ q p‖ / w p ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        have hp := hw p
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        field_simp
      rw [e]
      have h1 := hrow q
      rw [← le_div_iff₀' hq] at h1
      rwa [div_eq_mul_inv] at h1)
    (fun p _ => by
      have hp := hw p
      have e : ∑ q, ‖κ q p * ((w p)⁻¹ : ℂ)‖ * (w q)⁻¹ = (w p)⁻¹ * ∑ q, ‖κ q p‖ / w q := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
        ring
      rw [e, mul_comm b]
      exact mul_le_mul_of_nonneg_left (hcol p) (inv_nonneg.mpr hp.le))
    (fun p => (w p : ℂ) * u.ofLp p)
  have e1 : ‖FSKernel.kop κ u‖ ^ 2 =
      ∑ q, ‖∑ p, κ q p * ((w p)⁻¹ : ℂ) * ((w p : ℂ) * u.ofLp p)‖ ^ 2 := by
    rw [FSKernel.norm_sq_eq]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [FSKernel.kop_apply]
    congr 2
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp : (w p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hw p).ne'
    field_simp
  have e2 : ‖FSKernel.dg (fun q => (w q : ℂ)) u‖ ^ 2 = ∑ p, ‖(w p : ℂ) * u.ofLp p‖ ^ 2 := by
    rw [FSKernel.norm_sq_eq]
    rfl
  have h2 : ‖FSKernel.kop κ u‖ ^ 2 ≤
      (Real.sqrt (a * b) * ‖FSKernel.dg (fun q => (w q : ℂ)) u‖) ^ 2 := by
    rw [e1, mul_pow, Real.sq_sqrt (mul_nonneg ha hb), e2]
    exact h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- A kernel operator commutes with a diagonal weight that is constant along its support. -/
lemma kop_dg_comm {X : Type*} [Fintype X] (κ : X → X → ℂ) (w : X → ℂ)
    (h : ∀ q p, κ q p ≠ 0 → w q = w p) (u : EuclideanSpace ℂ X) :
    FSKernel.kop κ (FSKernel.dg w u) = FSKernel.dg w (FSKernel.kop κ u) := by
  ext q
  rw [FSKernel.kop_apply, FSKernel.dg_apply, FSKernel.kop_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [FSKernel.dg_apply]
  by_cases h0 : κ q p = 0
  · rw [h0]; ring
  · rw [h q p h0]; ring

/-! ## The second retained generator relative to one direction -/

open Classical in
/-- A column of the channel-`j` part of `Σ₂^bb` against a function of the transfer. -/
lemma col_sgK_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) (p : Cfg eta n) (f : Lattice3 → ℝ)
    (hf : ∀ θ, 0 ≤ f θ) :
    ∑ q, ‖chPart n j (sgK sys L n) q p‖ * f (chT n j q p) ≤
      chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) *
        ∑ θ ∈ (Finset.univ.filter (fun q => OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p)).image
          (fun q => chT n j q p), 1 / |FSLattice.slabF (cCh sys j (cidx n p)) θ| * f θ := by
  set T := Finset.univ.filter (fun q => OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p) with hT
  have hzero : ∀ q ∈ (Finset.univ : Finset (Cfg eta n)), q ∉ T →
      ‖chPart n j (sgK sys L n) q p‖ * f (chT n j q p) = 0 := by
    intro q _ hq
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hq
    unfold chPart
    split_ifs with hj
    · by_cases h0 : sgK sys L n q p = 0
      · rw [h0, norm_zero, zero_mul]
      · exact absurd (sgK_ne_zero h0).1 (hq hj)
    · rw [norm_zero, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ T) hzero]
  have hinj : Set.InjOn (fun q => chT n j q p) T := fun q hq q' hq' h =>
    chT_injOn j p (Finset.mem_filter.mp hq).2.1 (Finset.mem_filter.mp hq').2.1 h
  rw [Finset.sum_image hinj, Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  obtain ⟨hj, hg⟩ := (Finset.mem_filter.mp hq).2
  have hfl := floor_of_gapC hL hj hg
  have hρ1 : 1 ≤ FSChannel.rho (chT n j q p) := FSLattice.one_le_rho (one_le_lsq_chT hj hg.1)
  have hF0 : 0 < |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)| := by linarith
  have hμ := muCh_pos sys j
  have hgL := gF_pos hL
  have hk : ‖chPart n j (sgK sys L n) q p‖ ≤ chbT sys L / (n : ℝ) ^ 3 *
      (2 * muCh sys j / gF L ^ 2) * (1 / |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)|) := by
    unfold chPart
    rw [if_pos hj]
    refine (norm_sgK_le hL hn q p).trans (le_of_eq ?_)
    rw [mismatch_eq hL hj]
    field_simp
  calc ‖chPart n j (sgK sys L n) q p‖ * f (chT n j q p)
      ≤ chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) *
          (1 / |FSLattice.slabF (cCh sys j (cidx n p)) (chT n j q p)|) * f (chT n j q p) :=
        mul_le_mul_of_nonneg_right hk (hf _)
    _ = _ := by ring

variable (sys L n) in
/-- `C_Z(j) = (chbT/n³)(2μ_j/g²)(C_D + 44000)(J_n + 3)²`. -/
noncomputable def CZd (j : Ch eta) : ℝ :=
  chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) *
    ((FSLattice.CD + 44000) * ((Jn sys n : ℝ) + 3) ^ 2)

lemma CZd_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ CZd sys L n j := by
  unfold CZd FSLattice.CD
  have := chbT_nonneg (sys := sys) hL
  have := muCh_pos sys j
  positivity

omit [Fintype ν] in
open Classical in
lemma coreHyp_image (hL : 0 < L) (j : Ch eta) (p : Cfg eta n) :
    ∀ θ ∈ (Finset.univ.filter (fun q => OnCh j (cidx n q) (cidx n p) ∧ gapC sys L n q p)).image
      (fun q => chT n j q p), FSLattice.CoreHyp (cCh sys j (cidx n p)) (Jn sys n + 1) θ := by
  intro θ hθ
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hθ
  obtain ⟨hj, hg⟩ := (Finset.mem_filter.mp hq).2
  exact ⟨one_le_lsq_chT hj hg.1, floor_of_gapC hL hj hg, slabF_cap_cube hL hj⟩

/-- **eq:Zdirection**: `‖Z_j u‖ ≤ C_Z(j) ‖Λ_d u‖` for `d · ℓ_j = 1`. -/
theorem norm_Zj_le (hL : 0 < L) (hn : 2 ≤ n) (j : Ch eta) {d : Fin eta → ℤ} (hd : dl d j = 1)
    (u : En eta n) :
    ‖FSKernel.kop (chPart n j (sgK sys L n)) u‖ ≤
      CZd sys L n j * ‖FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u‖ := by
  classical
  have hCZ := CZd_nonneg (sys := sys) (n := n) hL j
  have hJ : ((Jn sys n + 1 : ℕ) : ℝ) + 2 = (Jn sys n : ℝ) + 3 := by push_cast; ring
  have hpre : 0 ≤ chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) := by
    have := chbT_nonneg (sys := sys) hL
    have := muCh_pos sys j
    positivity
  -- the transfer moves the directional coordinate
  have hlam : ∀ q p, OnCh j (cidx n q) (cidx n p) →
      lam d (cidx n q) = Real.sqrt (1 + FSLattice.lsq (dsum d (cidx n p) + chT n j q p)) := by
    intro q p h
    unfold lam
    rw [dsum_onCh_one hd h]
    rfl
  have hrow : ∀ q, lam d (cidx n q) * ∑ p, ‖chPart n j (sgK sys L n) q p‖ / lam d (cidx n p) ^ 2 ≤
      CZd sys L n j := by
    intro q
    have e : ∑ p, ‖chPart n j (sgK sys L n) q p‖ / lam d (cidx n p) ^ 2 =
        ∑ p, ‖chPart n j (sgK sys L n) p q‖ *
          (1 / (1 + FSLattice.lsq (dsum d (cidx n q) + chT n j p q))) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      have hn' : ‖chPart n j (sgK sys L n) q p‖ = ‖chPart n j (sgK sys L n) p q‖ := by
        rw [← norm_neg (chPart n j (sgK sys L n) p q), ← chPart_sgK_conj hL, Complex.norm_conj]
      rw [hn']
      by_cases h : OnCh j (cidx n p) (cidx n q)
      · rw [lam_sq, dsum_onCh_one hd h, div_eq_mul_one_div]
        rfl
      · unfold chPart
        rw [if_neg h, norm_zero, zero_div, zero_mul]
    rw [e]
    have h1 := col_sgK_le (sys := sys) hL hn j q (fun θ => 1 / (1 + FSLattice.lsq (dsum d (cidx n q) + θ)))
      (fun θ => by have := FSLattice.lsq_nonneg (dsum d (cidx n q) + θ); positivity)
    have h2 := FSLattice.inv_mismatch_row (cCh sys j (cidx n q)) (dsum d (cidx n q)) _
      (coreHyp_image (sys := sys) hL j q)
    rw [hJ] at h2
    have hl0 : 0 ≤ lam d (cidx n q) := (lam_pos d _).le
    calc lam d (cidx n q) * ∑ p, ‖chPart n j (sgK sys L n) p q‖ *
          (1 / (1 + FSLattice.lsq (dsum d (cidx n q) + chT n j p q)))
        ≤ lam d (cidx n q) * (chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) *
            ∑ θ ∈ (Finset.univ.filter (fun p => OnCh j (cidx n p) (cidx n q) ∧
              gapC sys L n p q)).image (fun p => chT n j p q),
              1 / |FSLattice.slabF (cCh sys j (cidx n q)) θ| *
                (1 / (1 + FSLattice.lsq (dsum d (cidx n q) + θ)))) :=
          mul_le_mul_of_nonneg_left h1 hl0
      _ = chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) *
            (Real.sqrt (1 + FSLattice.lsq (dsum d (cidx n q))) *
            ∑ θ ∈ (Finset.univ.filter (fun p => OnCh j (cidx n p) (cidx n q) ∧
              gapC sys L n p q)).image (fun p => chT n j p q),
              1 / |FSLattice.slabF (cCh sys j (cidx n q)) θ| *
                (1 / (1 + FSLattice.lsq (dsum d (cidx n q) + θ)))) := by
          unfold lam; ring
      _ ≤ chbT sys L / (n : ℝ) ^ 3 * (2 * muCh sys j / gF L ^ 2) *
            (FSLattice.CD * ((Jn sys n : ℝ) + 3) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hpre
      _ ≤ CZd sys L n j := by
          unfold CZd
          apply mul_le_mul_of_nonneg_left _ hpre
          have : (0 : ℝ) ≤ ((Jn sys n : ℝ) + 3) ^ 2 := by positivity
          nlinarith
  have hcol : ∀ p, ∑ q, ‖chPart n j (sgK sys L n) q p‖ / lam d (cidx n q) ≤ CZd sys L n j := by
    intro p
    have e : ∑ q, ‖chPart n j (sgK sys L n) q p‖ / lam d (cidx n q) =
        ∑ q, ‖chPart n j (sgK sys L n) q p‖ *
          (1 / Real.sqrt (1 + FSLattice.lsq (dsum d (cidx n p) + chT n j q p))) := by
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases h : OnCh j (cidx n q) (cidx n p)
      · rw [hlam q p h]; ring
      · unfold chPart
        rw [if_neg h, norm_zero, zero_div, zero_mul]
    rw [e]
    have h1 := col_sgK_le (sys := sys) hL hn j p
      (fun θ => 1 / Real.sqrt (1 + FSLattice.lsq (dsum d (cidx n p) + θ))) (fun θ => by positivity)
    have h2 := FSLattice.inv_mismatch_col (cCh sys j (cidx n p)) (dsum d (cidx n p)) _
      (coreHyp_image (sys := sys) hL j p)
    rw [hJ] at h2
    refine h1.trans ?_
    unfold CZd
    exact mul_le_mul_of_nonneg_left h2 hpre
  have h := norm_kop_le_wt (chPart n j (sgK sys L n)) (fun q => lam d (cidx n q))
    (fun q => lam_pos d _) hCZ hCZ hrow hcol u
  rwa [Real.sqrt_mul_self hCZ] at h

/-! ## Directional Hardy -/

/-- The finite-support unit lattice Hardy inequality from the canonical periodic one. -/
lemma finite_hardy (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) :
    HasFiniteSupportUnitLatticeCoulombHardyBound Hunit := by
  have hPotential : HasUnitTorus3CoulombPotentialH1L2Bound
      canonicalUnitTorus3CoulombPotential.toPotentialRealization Hunit := hPeriodic
  have hProduct := unitTorus3CoulombProductH1L2Bound_of_potential
    canonicalUnitTorus3CoulombPotential.toPotentialRealization Hunit hPotential
  have hPartial := unitTorus3CoulombFourierPartialSumH1L2Bound_of_product
    canonicalUnitTorus3CoulombPotential.toPotentialRealization.toProductRealization Hunit hProduct
  exact finiteSupportUnitLatticeCoulombHardyBound_of_fourierPartialSums Hunit hPartial

lemma unitKernel_eq (x : Lattice3) :
    unitLatticeCoulombKernel x = ((1 / latticeNormSq x : ℝ) : ℂ) := by
  unfold unitLatticeCoulombKernel latticeCoulombSquareWeight
  congr 1
  rw [← one_div_pow, Real.sqrt_sq (by have := latticeNormSq_nonneg x; positivity)]

/-- The fibre key of channel `k` along the direction `e`. -/
def fkey (k : Ch eta) (e : Fin eta → ℤ) (S : Cf eta) : Cf eta := S - tr k (dsum e S)

lemma fkey_eq_of_onCh {k : Ch eta} {e : Fin eta → ℤ} (he : dl e k = 1) {R S : Cf eta}
    (h : OnCh k R S) : fkey k e R = fkey k e S := by
  unfold fkey
  have e1 : R = S + tr k (R (lead k) - S (lead k)) := h
  rw [dsum_onCh_one he h, tr_add]
  generalize R (lead k) - S (lead k) = θ at e1 ⊢
  rw [e1]
  abel

lemma onCh_of_fkey_eq {k : Ch eta} {e : Fin eta → ℤ} {R S : Cf eta}
    (h : fkey k e R = fkey k e S) :
    OnCh k R S ∧ R (lead k) - S (lead k) = dsum e R - dsum e S := by
  unfold fkey at h
  have e1 : R = S + tr k (dsum e R - dsum e S) := by
    rw [tr_sub]
    have h2 : R = S - tr k (dsum e S) + tr k (dsum e R) := by rw [← h]; abel
    calc R = S - tr k (dsum e S) + tr k (dsum e R) := h2
      _ = S + (tr k (dsum e R) - tr k (dsum e S)) := by abel
  refine ⟨onCh_of_eq e1, ?_⟩
  have h3 := lead_add_tr k S (dsum e R - dsum e S)
  rwa [← e1] at h3

lemma dsum_inj_of_fkey {k : Ch eta} {e : Fin eta → ℤ} {R S : Cf eta}
    (h : fkey k e R = fkey k e S) (h' : dsum e R = dsum e S) : R = S := by
  unfold fkey at h
  rw [h'] at h
  exact sub_left_injective h

/-- **Directional Hardy on a finite set of configurations** (eq:directionHardy): for
`e · ℓ_k = 1`, `Σ_{R ∈ F} (Σ_{S ∈ F} chMaj_k(R,S) f(S))² ≤ c² H² Σ_{S ∈ F} (1 + |y_e(S)|²) f(S)²`. -/
theorem dir_hardy (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (k : Ch eta) {e : Fin eta → ℤ} (he : dl e k = 1) (c : ℝ)
    (F : Finset (Cf eta)) (f : Cf eta → ℝ) (hf : ∀ S, 0 ≤ f S) :
    ∑ R ∈ F, (∑ S ∈ F, chMaj k c R S * f S) ^ 2 ≤
      c ^ 2 * Hunit ^ 2 * ∑ S ∈ F, (1 + FSLattice.lsq (dsum e S)) * f S ^ 2 := by
  classical
  have hFin := finite_hardy Hunit hPeriodic
  set K := F.image (fkey k e)
  have hfib : ∀ κ ∈ K,
      ∑ R ∈ F.filter (fun R => fkey k e R = κ), (∑ S ∈ F, chMaj k c R S * f S) ^ 2 ≤
        c ^ 2 * Hunit ^ 2 *
          ∑ S ∈ F.filter (fun S => fkey k e S = κ), (1 + FSLattice.lsq (dsum e S)) * f S ^ 2 := by
    intro κ _
    set Fκ := F.filter (fun R => fkey k e R = κ) with hFκ
    have hin : ∀ R ∈ Fκ, ∑ S ∈ F, chMaj k c R S * f S =
        c * ∑ S ∈ Fκ, (1 / latticeNormSq (dsum e R - dsum e S)) * f S := by
      intro R hR
      have hRk := (Finset.mem_filter.mp hR).2
      rw [Finset.mul_sum, ← Finset.sum_subset (Finset.filter_subset _ F) (fun S _ hS => by
        have hne : fkey k e S ≠ κ := fun h => hS (Finset.mem_filter.mpr ⟨by assumption, h⟩)
        unfold chMaj
        rw [if_neg (fun hon => hne ((fkey_eq_of_onCh he hon).symm.trans hRk)), zero_mul])]
      refine Finset.sum_congr rfl fun S hS => ?_
      have hSk := (Finset.mem_filter.mp hS).2
      obtain ⟨hon, htr⟩ := onCh_of_fkey_eq (hRk.trans hSk.symm)
      unfold chMaj
      rw [if_pos hon, htr]
      ring
    have hinj : Function.Injective (fun S : Fκ => dsum e S.1) := by
      intro S S' h
      apply Subtype.ext
      exact dsum_inj_of_fkey ((Finset.mem_filter.mp S.2).2.trans (Finset.mem_filter.mp S'.2).2.symm) h
    have h := hFin Fκ (fun S => dsum e S.1) hinj (fun S => ((f S.1 : ℝ) : ℂ))
    unfold finiteSupportUnitLatticeCoulombOutputSq finiteSupportLatticeH1Sq
      finiteSupportUnitLatticeCoulombAction at h
    simp_rw [unitKernel_eq] at h
    rw [Finset.sum_coe_sort Fκ (fun q => ‖∑ p : Fκ, ((f p.1 : ℝ) : ℂ) *
      ((1 / latticeNormSq (latticeSub (dsum e q) (dsum e p.1)) : ℝ) : ℂ)‖ ^ 2)] at h
    rw [Finset.sum_coe_sort Fκ (fun p => (1 + latticeNormSq (dsum e p)) * ‖((f p : ℝ) : ℂ)‖ ^ 2)] at h
    have hsum : ∀ R ∈ Fκ, ‖∑ p : Fκ, ((f p.1 : ℝ) : ℂ) *
        ((1 / latticeNormSq (latticeSub (dsum e R) (dsum e p.1)) : ℝ) : ℂ)‖ ^ 2 =
        (∑ S ∈ Fκ, (1 / latticeNormSq (dsum e R - dsum e S)) * f S) ^ 2 := by
      intro R _
      rw [Finset.sum_coe_sort Fκ (fun p => ((f p : ℝ) : ℂ) *
        ((1 / latticeNormSq (latticeSub (dsum e R) (dsum e p)) : ℝ) : ℂ))]
      have hnn : 0 ≤ ∑ S ∈ Fκ, (1 / latticeNormSq (dsum e R - dsum e S)) * f S :=
        Finset.sum_nonneg fun S _ => mul_nonneg (by
          have := latticeNormSq_nonneg (dsum e R - dsum e S); positivity) (hf S)
      rw [show (∑ p ∈ Fκ, ((f p : ℝ) : ℂ) *
          ((1 / latticeNormSq (latticeSub (dsum e R) (dsum e p)) : ℝ) : ℂ)) =
          ((∑ S ∈ Fκ, (1 / latticeNormSq (dsum e R - dsum e S)) * f S : ℝ) : ℂ) by
        push_cast
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [FSFlux.latticeSub_eq_sub]
        ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    rw [Finset.sum_congr rfl hsum] at h
    have hH : ∀ S ∈ Fκ, (1 + latticeNormSq (dsum e S)) * ‖((f S : ℝ) : ℂ)‖ ^ 2 =
        (1 + FSLattice.lsq (dsum e S)) * f S ^ 2 := by
      intro S _
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rfl
    rw [Finset.sum_congr rfl hH] at h
    calc ∑ R ∈ Fκ, (∑ S ∈ F, chMaj k c R S * f S) ^ 2
        = ∑ R ∈ Fκ, c ^ 2 * (∑ S ∈ Fκ, (1 / latticeNormSq (dsum e R - dsum e S)) * f S) ^ 2 := by
          refine Finset.sum_congr rfl fun R hR => ?_
          rw [hin R hR, mul_pow]
      _ = c ^ 2 * ∑ R ∈ Fκ, (∑ S ∈ Fκ, (1 / latticeNormSq (dsum e R - dsum e S)) * f S) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ c ^ 2 * (Hunit ^ 2 * ∑ S ∈ Fκ, (1 + FSLattice.lsq (dsum e S)) * f S ^ 2) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg c)
      _ = _ := by ring
  have hmaps : ∀ x ∈ F, fkey k e x ∈ K := fun x hx => Finset.mem_image_of_mem _ hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, ← Finset.sum_fiberwise_of_maps_to hmaps,
    Finset.mul_sum]
  exact Finset.sum_le_sum hfib

/-- **Directional Hardy on the cube**: if `|κ(q,p)| ≤ chMaj_k c (q,p)` and `e · ℓ_k = 1`, then
`‖kop κ v‖ ≤ c |H| ‖Λ_e v‖`. -/
theorem norm_kop_hardy (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (k : Ch eta) {e : Fin eta → ℤ} (he : dl e k = 1) {c : ℝ} (hc : 0 ≤ c)
    (κ : Cfg eta n → Cfg eta n → ℂ) (hκ : ∀ q p, ‖κ q p‖ ≤ chMaj k c (cidx n q) (cidx n p))
    (v : En eta n) :
    ‖FSKernel.kop κ v‖ ≤ c * |Hunit| * ‖FSKernel.dg (fun q => (lam e (cidx n q) : ℂ)) v‖ := by
  classical
  set F := (Finset.univ : Finset (Cfg eta n)).image (cidx n) with hF
  have hinj : Function.Injective (cidx n : Cfg eta n → Cf eta) :=
    finiteConfigLatticeIndex_injective eta n
  set f : Cf eta → ℝ := fun S => if h : ∃ p, cidx n p = S then ‖v.ofLp h.choose‖ else 0 with hfdef
  have hf : ∀ p, f (cidx n p) = ‖v.ofLp p‖ := by
    intro p
    have h : ∃ p', cidx n p' = cidx n p := ⟨p, rfl⟩
    simp only [hfdef, dif_pos h]
    rw [hinj h.choose_spec]
  have hf0 : ∀ S, 0 ≤ f S := fun S => by
    simp only [hfdef]; split_ifs <;> positivity
  have h := dir_hardy Hunit hPeriodic k he c F f hf0
  have hconv1 : ∑ R ∈ F, (∑ S ∈ F, chMaj k c R S * f S) ^ 2 =
      ∑ q, (∑ p, chMaj k c (cidx n q) (cidx n p) * ‖v.ofLp p‖) ^ 2 := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    simp only [hf]
  have hconv2 : ∑ S ∈ F, (1 + FSLattice.lsq (dsum e S)) * f S ^ 2 =
      ∑ p, (1 + FSLattice.lsq (dsum e (cidx n p))) * ‖v.ofLp p‖ ^ 2 := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    simp only [hf]
  rw [hconv1, hconv2] at h
  have h2 : ‖FSKernel.kop κ v‖ ^ 2 ≤
      (c * |Hunit| * ‖FSKernel.dg (fun q => (lam e (cidx n q) : ℂ)) v‖) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs, FSKernel.norm_sq_eq, FSKernel.norm_sq_eq]
    calc ∑ q, ‖(FSKernel.kop κ v).ofLp q‖ ^ 2
        ≤ ∑ q, (∑ p, chMaj k c (cidx n q) (cidx n p) * ‖v.ofLp p‖) ^ 2 := by
          refine Finset.sum_le_sum fun q _ => ?_
          apply pow_le_pow_left₀ (norm_nonneg _)
          rw [FSKernel.kop_apply]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hκ q p) (norm_nonneg _)
      _ ≤ c ^ 2 * Hunit ^ 2 * ∑ p, (1 + FSLattice.lsq (dsum e (cidx n p))) * ‖v.ofLp p‖ ^ 2 := h
      _ = c ^ 2 * Hunit ^ 2 *
            ∑ q, ‖(FSKernel.dg (fun q => (lam e (cidx n q) : ℂ)) v).ofLp q‖ ^ 2 := by
          congr 1
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [FSKernel.dg_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (lam_pos _ _), mul_pow, lam_sq]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

omit [Fintype ν] in
/-- `‖Λ_e Λ_d u‖ ≤ c_Λ ‖(1 + A) u‖`. -/
lemma norm_lam2_le (hL : 0 < L) {d e : Fin eta → ℤ} (hd : l1 d ≤ 2) (he : l1 e ≤ 2)
    (u : En eta n) :
    ‖FSKernel.dg (fun q => (lam e (cidx n q) : ℂ))
        (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)‖ ≤
      cLam sys L * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
  rw [wt_eq_dg (sys := sys) (L := L)]
  have hc := cLam_pos (sys := sys) L
  have h2 : ‖FSKernel.dg (fun q => (lam e (cidx n q) : ℂ))
        (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)‖ ^ 2 ≤
      (cLam sys L * ‖FSKernel.dg (fun q => (((1 + Asym sys L n q) ^ (1 : ℝ) : ℝ) : ℂ)) u‖) ^ 2 := by
    rw [mul_pow, FSKernel.norm_sq_eq, FSKernel.norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    simp only [FSKernel.dg_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.rpow_one]
    have hA := Asym_nonneg (sys := sys) (L := L) q
    rw [abs_of_pos (lam_pos _ _), abs_of_pos (lam_pos _ _), abs_of_pos (by linarith : (0:ℝ) < 1 + Asym sys L n q)]
    have hm := lam_mul_le (sys := sys) hL hd he q
    have h0 : 0 ≤ lam e (cidx n q) * lam d (cidx n q) := by
      have := lam_pos e (cidx n q); have := lam_pos d (cidx n q); positivity
    calc (lam e (cidx n q) * (lam d (cidx n q) * ‖u.ofLp q‖)) ^ 2
        = (lam d (cidx n q) * lam e (cidx n q)) ^ 2 * ‖u.ofLp q‖ ^ 2 := by ring
      _ ≤ (cLam sys L * (1 + Asym sys L n q)) ^ 2 * ‖u.ofLp q‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact pow_le_pow_left₀ (by linarith) hm 2
      _ = cLam sys L ^ 2 * ((1 + Asym sys L n q) * ‖u.ofLp q‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-! ## The cross commutators -/

variable (sys L n) in
/-- The kernel of the multi-channel part of `[Σ₂^bb, W_N]`. -/
noncomputable def crossK (q p : Cfg eta n) : ℂ :=
  ∑ j, ∑ k, if j = k then 0 else
    (kmul n (chPart n j (sgK sys L n)) (chPart n k (wNK sys L n)) q p -
      kmul n (chPart n j (wNK sys L n)) (chPart n k (sgK sys L n)) q p)

variable (sys L n) in
/-- `C_X(n) = Σ_{j,k} (C_Z(j) c_k + c_j C_Z(k)) |H| c_Λ`. -/
noncomputable def kcCX (Hunit : ℝ) : ℝ :=
  ∑ j : Ch eta, ∑ k : Ch eta, (CZd sys L n j * chC sys L k + chC sys L j * CZd sys L n k) *
    |Hunit| * cLam sys L

lemma kcCX_nonneg (hL : 0 < L) (Hunit : ℝ) : 0 ≤ kcCX sys L n Hunit := by
  unfold kcCX
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
  have := CZd_nonneg (sys := sys) (n := n) hL j
  have := CZd_nonneg (sys := sys) (n := n) hL k
  have := chC_nonneg sys hL j
  have := chC_nonneg sys hL k
  have := cLam_pos (sys := sys) L
  positivity

omit [Fintype ν] in
lemma kop_sum2 {ι : Type*} [Fintype ι] (F : ι → ι → Cfg eta n → Cfg eta n → ℂ) (u : En eta n) :
    FSKernel.kop (fun q p => ∑ j, ∑ k, F j k q p) u = ∑ j, ∑ k, FSKernel.kop (F j k) u := by
  ext q
  simp only [FSKernel.kop_apply, WithLp.ofLp_sum, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

omit [Fintype ν] in
lemma onCh_of_chPart_ne {κ : Cfg eta n → Cfg eta n → ℂ} {j : Ch eta} {q p : Cfg eta n}
    (h : chPart n j κ q p ≠ 0) : OnCh j (cidx n q) (cidx n p) := by
  unfold chPart at h
  by_contra h'
  exact h (if_neg h')

/-- **lem:crosscomm**: the multi-channel part of `[Σ₂^bb, W_N]` obeys
`‖Σ_{j ≠ k} (Z_j W_k - W_j Z_k) u‖ ≤ C_X(n) ‖(1 + A) u‖`. -/
theorem norm_crossX_le (hL : 0 < L) (hn : 2 ≤ n) (Hunit : ℝ)
    (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit) (u : En eta n) :
    ‖FSKernel.kop (crossK sys L n) u‖ ≤
      kcCX sys L n Hunit * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ := by
  classical
  set W1 := ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖
  have hpair : ∀ j k : Ch eta, ‖FSKernel.kop (fun q p => if j = k then 0 else
      (kmul n (chPart n j (sgK sys L n)) (chPart n k (wNK sys L n)) q p -
        kmul n (chPart n j (wNK sys L n)) (chPart n k (sgK sys L n)) q p)) u‖ ≤
      (CZd sys L n j * chC sys L k + chC sys L j * CZd sys L n k) * |Hunit| * cLam sys L * W1 := by
    intro j k
    have hcl := cLam_pos (sys := sys) L
    have hW0 : 0 ≤ W1 := norm_nonneg _
    by_cases hjk : j = k
    · simp only [hjk, if_true]
      have : FSKernel.kop (fun (_ _ : Cfg eta n) => (0 : ℂ)) u = 0 := by
        ext q; simp
      rw [this, norm_zero]
      have := CZd_nonneg (sys := sys) (n := n) hL k
      have := chC_nonneg sys hL k
      positivity
    · simp only [hjk, if_false]
      obtain ⟨d, hdj, hdk, hd1⟩ := exists_dir j k hjk
      obtain ⟨e, hek, hej, he1⟩ := exists_dir k j (Ne.symm hjk)
      have hsplit : FSKernel.kop (fun q p =>
          kmul n (chPart n j (sgK sys L n)) (chPart n k (wNK sys L n)) q p -
            kmul n (chPart n j (wNK sys L n)) (chPart n k (sgK sys L n)) q p) u =
          FSKernel.kop (chPart n j (sgK sys L n)) (FSKernel.kop (chPart n k (wNK sys L n)) u) -
            FSKernel.kop (chPart n j (wNK sys L n)) (FSKernel.kop (chPart n k (sgK sys L n)) u) := by
        rw [show (fun q p => kmul n (chPart n j (sgK sys L n)) (chPart n k (wNK sys L n)) q p -
            kmul n (chPart n j (wNK sys L n)) (chPart n k (sgK sys L n)) q p) =
            kmul n (chPart n j (sgK sys L n)) (chPart n k (wNK sys L n)) -
            kmul n (chPart n j (wNK sys L n)) (chPart n k (sgK sys L n)) from rfl,
          FSKernel.kop_sub, ← kop_kmul, ← kop_kmul]
        rfl
      rw [hsplit]
      have hWk : ∀ q p, ‖chPart n k (wNK sys L n) q p‖ ≤ chMaj k (chC sys L k) (cidx n q) (cidx n p) :=
        fun q p => by
          unfold chPart wNK
          split_ifs with h
          · rw [← lcp_of_onCh (κ := potKernel sys L) h]; exact norm_lcp_pot_le hL k _ _
          · rw [norm_zero]; exact chMaj_nonneg k (chC_nonneg sys hL k) _ _
      have hWj : ∀ q p, ‖chPart n j (wNK sys L n) q p‖ ≤ chMaj j (chC sys L j) (cidx n q) (cidx n p) :=
        fun q p => by
          unfold chPart wNK
          split_ifs with h
          · rw [← lcp_of_onCh (κ := potKernel sys L) h]; exact norm_lcp_pot_le hL j _ _
          · rw [norm_zero]; exact chMaj_nonneg j (chC_nonneg sys hL j) _ _
      -- `Z_j W_k u`
      have h1 : ‖FSKernel.kop (chPart n j (sgK sys L n)) (FSKernel.kop (chPart n k (wNK sys L n)) u)‖ ≤
          CZd sys L n j * chC sys L k * |Hunit| * cLam sys L * W1 := by
        refine (norm_Zj_le hL hn j hdj _).trans ?_
        rw [← kop_dg_comm _ _ (fun q p h => by
          rw [lam_onCh_zero hdk (onCh_of_chPart_ne h)])]
        have h2 := norm_kop_hardy Hunit hPeriodic k hek (chC_nonneg sys hL k) _ hWk
          (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)
        have h3 := norm_lam2_le (sys := sys) hL hd1 he1 u
        have hZ := CZd_nonneg (sys := sys) (n := n) hL j
        calc CZd sys L n j * ‖FSKernel.kop (chPart n k (wNK sys L n))
              (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)‖
            ≤ CZd sys L n j * (chC sys L k * |Hunit| * (cLam sys L * W1)) :=
              mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by
                have := chC_nonneg sys hL k; positivity))) hZ
          _ = _ := by ring
      -- `W_j Z_k u`
      have h2 : ‖FSKernel.kop (chPart n j (wNK sys L n)) (FSKernel.kop (chPart n k (sgK sys L n)) u)‖ ≤
          chC sys L j * CZd sys L n k * |Hunit| * cLam sys L * W1 := by
        refine (norm_kop_hardy Hunit hPeriodic j hdj (chC_nonneg sys hL j) _ hWj _).trans ?_
        rw [← kop_dg_comm _ _ (fun q p h => by
          rw [lam_onCh_zero hdk (onCh_of_chPart_ne h)])]
        have h3 := norm_Zj_le (sys := sys) hL hn k hek (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)
        have h4 := norm_lam2_le (sys := sys) hL hd1 he1 u
        have hZ := CZd_nonneg (sys := sys) (n := n) hL k
        have hc := chC_nonneg sys hL j
        calc chC sys L j * |Hunit| * ‖FSKernel.kop (chPart n k (sgK sys L n))
              (FSKernel.dg (fun q => (lam d (cidx n q) : ℂ)) u)‖
            ≤ chC sys L j * |Hunit| * (CZd sys L n k * (cLam sys L * W1)) :=
              mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 hZ)) (by positivity)
          _ = _ := by ring
      calc _ ≤ _ := norm_sub_le _ _
        _ ≤ CZd sys L n j * chC sys L k * |Hunit| * cLam sys L * W1 +
              chC sys L j * CZd sys L n k * |Hunit| * cLam sys L * W1 := add_le_add h1 h2
        _ = _ := by ring
  have e : FSKernel.kop (crossK sys L n) u = ∑ j, ∑ k, FSKernel.kop (fun q p => if j = k then 0 else
      (kmul n (chPart n j (sgK sys L n)) (chPart n k (wNK sys L n)) q p -
        kmul n (chPart n j (wNK sys L n)) (chPart n k (sgK sys L n)) q p)) u :=
    kop_sum2 (fun j k q p => if j = k then 0 else
      (kmul n (chPart n j (sgK sys L n)) (chPart n k (wNK sys L n)) q p -
        kmul n (chPart n j (wNK sys L n)) (chPart n k (sgK sys L n)) q p)) u
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  unfold kcCX
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => hpair j k

end FSNormal
