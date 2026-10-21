import PlaneWave.Source.BulkBlock

/-!
# Flux/source build, block 5: the bulk rotation `Σ₂^bb`

Kinematics of a hop and the bulk second-order generator.

* `E_hop`: a hop of channel `j` with transfer `θ` from `k'` changes the kinetic energy by
  `(g²/2μ_j) F_c(θ)`, `F_c(θ) = |θ|² + 2θ·c`, with the channel's reduced mass `μ_j` and drift
  `c = μ_j (k'_a/m_a - k'_b/m_b)` (one-body hops: `μ_j = m_a`, `c = k'_a`).
* `cCh_sq_le`, `pin_register` (`lem:pin`): `|c|² ≤ max_{c ∈ moved} |k'_c|²`; so a hop in a low
  layer `|F_c(θ)| < |θ|²/4` starts from a configuration with a moved register of momentum
  `> 3|θ|/8`.
* On the cube: the outer-mismatch floor `|E(q) - E(p)| ≥ g²|θ|/μ_j` (`gapC`, the text's
  `|ω_τ(k)| ≥ ‖τ‖/μ_pb` in lattice units `g = 1`), the split `H₂^bb = H₂^{bb,gap} + H₂^{bb,res}`
  and the generator `Σ₂^bb = H₂^{bb,gap}/ω` (`Sig2bb`, entrywise division by the mismatch), with
  `[A, Σ₂^bb] = H₂^{bb,gap}` (`comm_Sig2bb`) and `Σ₂^bb` skew-adjoint (`inner_Sig2bb`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Kinematics of a hop -/

/-- The reduced mass of a channel (`m_a` for a one-body hop). -/
noncomputable def muCh (sys : CoulombSystem eta ν) : Ch eta → ℝ
  | .inl a => sys.mass a
  | .inr pr => sys.mass pr.1.1 * sys.mass pr.1.2 / (sys.mass pr.1.1 + sys.mass pr.1.2)

/-- The drift `c = μ_j v` of a hop of channel `j` from the configuration `k'`. -/
noncomputable def cCh (sys : CoulombSystem eta ν) : Ch eta → Cf eta → Fin 3 → ℝ
  | .inl a, k', i => (k' a i : ℝ)
  | .inr pr, k', i => muCh sys (.inr pr) *
      ((k' pr.1.1 i : ℝ) / sys.mass pr.1.1 - (k' pr.1.2 i : ℝ) / sys.mass pr.1.2)

omit [Fintype ν] in
lemma muCh_pos (sys : CoulombSystem eta ν) (j : Ch eta) : 0 < muCh sys j := by
  cases j with
  | inl a => exact sys.mass_pos a
  | inr pr =>
    have := sys.mass_pos pr.1.1
    have := sys.mass_pos pr.1.2
    simp only [muCh]
    positivity

omit [Fintype ν] in
lemma nsq_add_sub (x θ : Lattice3) : nsq (x + θ) - nsq x =
    FSLattice.slabF (fun i => (x i : ℝ)) θ := by
  simp only [nsq, FSLattice.slabF, FSLattice.lsq, Pi.add_apply, Int.cast_add, Fin.sum_univ_three]
  ring

omit [Fintype ν] in
/-- **The mismatch of a hop**: `E(k' + τ_j(θ)) - E(k') = (g²/2μ_j) F_c(θ)`. -/
theorem E_hop (sys : CoulombSystem eta ν) (g : ℝ) (j : Ch eta) (k' : Cf eta) (θ : Lattice3) :
    E sys.mass g (k' + tr j θ) - E sys.mass g k' =
      g ^ 2 / (2 * muCh sys j) * FSLattice.slabF (cCh sys j k') θ := by
  cases j with
  | inl a =>
    have ht : tr (.inl a : Ch eta) θ = Pi.single a θ := rfl
    have hc : cCh sys (.inl a) k' = fun i => (k' a i : ℝ) := by funext i; rfl
    have hm : muCh sys (.inl a) = sys.mass a := rfl
    rw [ht, E_add_single_sub, nsq_add_sub, hc, hm]
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    have ha := sys.mass_pos pr.1.1
    have hb := sys.mass_pos pr.1.2
    unfold E
    rw [← Finset.sum_sub_distrib]
    rw [Fintype.sum_eq_add pr.1.1 pr.1.2 hne (fun c hc => by
      have : (k' + tr (.inr pr) θ) c = k' c := by
        have h0 := tr_apply_not_moved (.inr pr : Ch eta) θ (c := c) (by
          simp only [moved, Finset.mem_insert, Finset.mem_singleton, not_or]; exact hc)
        rw [Pi.add_apply, h0, add_zero]
      rw [this, sub_self])]
    have e1 : (k' + tr (.inr pr) θ) pr.1.1 = k' pr.1.1 + θ := by
      simp [tr, Pi.single_eq_of_ne hne]
    have e2 : (k' + tr (.inr pr) θ) pr.1.2 = k' pr.1.2 + -θ := by
      simp [tr, Pi.single_eq_of_ne hne.symm, sub_eq_add_neg]
    rw [e1, e2]
    simp only [nsq, FSLattice.slabF, FSLattice.lsq, cCh, muCh, Pi.add_apply, Pi.neg_apply,
      Int.cast_add, Int.cast_neg, Fin.sum_univ_three]
    field_simp
    ring

omit [Fintype ν] in
/-- `|c|² ≤ X` when every moved register has `|k'_c|² ≤ X`. -/
theorem cCh_sq_le (sys : CoulombSystem eta ν) (j : Ch eta) (k' : Cf eta) {X : ℝ}
    (h : ∀ c ∈ moved j, nsq (k' c) ≤ X) : ∑ i, cCh sys j k' i ^ 2 ≤ X := by
  cases j with
  | inl a =>
    have := h a (by simp [moved])
    simp only [cCh, nsq, Fin.sum_univ_three] at this ⊢
    linarith
  | inr pr =>
    have ha := sys.mass_pos pr.1.1
    have hb := sys.mass_pos pr.1.2
    have hx := h pr.1.1 (by simp [moved])
    have hy := h pr.1.2 (by simp [moved])
    set α := muCh sys (.inr pr) / sys.mass pr.1.1
    set β := muCh sys (.inr pr) / sys.mass pr.1.2
    have hα : 0 ≤ α := by have := muCh_pos sys (.inr pr); positivity
    have hβ : 0 ≤ β := by have := muCh_pos sys (.inr pr); positivity
    have hαβ : α + β = 1 := by
      simp only [α, β, muCh]; field_simp; ring
    have he : ∀ i, cCh sys (.inr pr) k' i = α * (k' pr.1.1 i : ℝ) - β * (k' pr.1.2 i : ℝ) := by
      intro i; simp only [cCh, α, β]; ring
    simp only [he, Fin.sum_univ_three]
    simp only [nsq] at hx hy
    set x0 := (k' pr.1.1 0 : ℝ); set x1 := (k' pr.1.1 1 : ℝ); set x2 := (k' pr.1.1 2 : ℝ)
    set y0 := (k' pr.1.2 0 : ℝ); set y1 := (k' pr.1.2 1 : ℝ); set y2 := (k' pr.1.2 2 : ℝ)
    have key : (α * x0 - β * y0) ^ 2 + (α * x1 - β * y1) ^ 2 + (α * x2 - β * y2) ^ 2 ≤
        α * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) + β * (y0 ^ 2 + y1 ^ 2 + y2 ^ 2) := by
      have hβ' : β = 1 - α := by linarith
      rw [hβ']
      have hα1 : α ≤ 1 := by linarith
      nlinarith [mul_nonneg hα (sub_nonneg.mpr hα1), sq_nonneg (x0 + y0), sq_nonneg (x1 + y1),
        sq_nonneg (x2 + y2)]
    calc _ ≤ α * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) + β * (y0 ^ 2 + y1 ^ 2 + y2 ^ 2) := key
      _ ≤ α * X + β * X := by gcongr
      _ = X := by rw [← add_mul, hαβ, one_mul]

omit [Fintype ν] in
/-- **Pinning** (`lem:pin`): a hop in a low layer `|F_c(θ)| < |θ|²/4` starts from a configuration
with a moved register of momentum `|k'_c|² > (9/64)|θ|²`. -/
theorem pin_register (sys : CoulombSystem eta ν) (j : Ch eta) (k' : Cf eta) (θ : Lattice3)
    (h : |FSLattice.slabF (cCh sys j k') θ| < FSLattice.lsq θ / 4) :
    ∃ c ∈ moved j, 9 / 64 * FSLattice.lsq θ < nsq (k' c) := by
  by_contra hno
  push Not at hno
  have h1 := cCh_sq_le sys j k' hno
  have h2 := FSLattice.pin_core (cCh sys j k') θ h
  linarith

/-! ## The bulk split on the cube -/

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

/-- The configuration index of a cube configuration. -/
noncomputable abbrev cidx (q : Cfg eta n) : Cf eta := finiteConfigLatticeIndex eta n q

/-- The lattice transfer of channel `j` between cube configurations. -/
noncomputable def chT (j : Ch eta) (q p : Cfg eta n) : Lattice3 :=
  cidx n q (lead j) - cidx n p (lead j)

/-- **The outer-mismatch floor** (`lem:res2`): `q ≠ p` joined by a channel `j` with
`|E(q) - E(p)| ≥ g² |θ|/μ_j`. -/
def gapC (q p : Cfg eta n) : Prop :=
  q ≠ p ∧ ∃ j : Ch eta, OnCh j (cidx n q) (cidx n p) ∧
    gF L ^ 2 * FSChannel.rho (chT n j q p) / muCh sys j ≤ |Asym sys L n q - Asym sys L n p|

open Classical in
/-- The gapped part of the bulk kernel. -/
noncomputable def hgapK (q p : Cfg eta n) : ℂ := if gapC sys L n q p then hbC sys L n q p else 0

open Classical in
/-- The resonant part of the bulk kernel. -/
noncomputable def hresK (q p : Cfg eta n) : ℂ := if gapC sys L n q p then 0 else hbC sys L n q p

/-- `H₂^{bb,gap}` on `E_n`. -/
noncomputable def Hgap : En eta n →ₗ[ℂ] En eta n := FSKernel.kop (hgapK sys L n)

/-- `H₂^{bb,res}` on `E_n`. -/
noncomputable def Hres : En eta n →ₗ[ℂ] En eta n := FSKernel.kop (hresK sys L n)

/-- **The bulk rotation** `Σ₂^bb = H₂^{bb,gap}/ω`. -/
noncomputable def Sig2bb : En eta n →ₗ[ℂ] En eta n :=
  FSKernel.kop (FSKernel.divK (Asym sys L n) (hgapK sys L n))

variable {sys L n}

lemma hgapK_add_hresK (q p : Cfg eta n) :
    hgapK sys L n q p + hresK sys L n q p = hbC sys L n q p := by
  unfold hgapK hresK
  split_ifs <;> simp

theorem Hbb_split (hL : 0 < L) (hn : 2 ≤ n) :
    (Hbb sys hL hn : En eta n →ₗ[ℂ] En eta n) = Hgap sys L n + Hres sys L n := by
  rw [Hbb_eq_kop, Hgap, Hres, ← FSKernel.kop_add]
  congr 1
  funext q p
  exact (hgapK_add_hresK q p).symm

omit [Fintype ν] in
lemma chT_swap (j : Ch eta) (q p : Cfg eta n) : FSChannel.rho (chT n j p q) = FSChannel.rho (chT n j q p) := by
  unfold chT
  rw [show cidx n p (lead j) - cidx n q (lead j) = -(cidx n q (lead j) - cidx n p (lead j)) by abel,
    rho_neg']

omit [Fintype ν] in
lemma gapC_symm {q p : Cfg eta n} (h : gapC sys L n q p) : gapC sys L n p q := by
  obtain ⟨hne, j, hj, hfl⟩ := h
  refine ⟨hne.symm, j, onCh_symm hj, ?_⟩
  rw [chT_swap, abs_sub_comm]
  exact hfl

omit [Fintype ν] in
lemma gapC_comm (q p : Cfg eta n) : gapC sys L n q p ↔ gapC sys L n p q :=
  ⟨gapC_symm, gapC_symm⟩

lemma hbC_conj (hL : 0 < L) (q p : Cfg eta n) : hbC sys L n p q = conj (hbC sys L n q p) :=
  hbK_conj hL _ _

lemma hgapK_conj (hL : 0 < L) (q p : Cfg eta n) : hgapK sys L n p q = conj (hgapK sys L n q p) := by
  unfold hgapK
  rw [gapC_comm p q]
  split_ifs
  · exact hbC_conj hL q p
  · simp

lemma hresK_conj (hL : 0 < L) (q p : Cfg eta n) : hresK sys L n p q = conj (hresK sys L n q p) := by
  unfold hresK
  rw [gapC_comm p q]
  split_ifs
  · simp
  · exact hbC_conj hL q p

omit [Fintype ν] in
/-- On the gapped elements the mismatch does not vanish. -/
lemma gapC_ne (hL : 0 < L) {q p : Cfg eta n} (h : gapC sys L n q p) :
    Asym sys L n q ≠ Asym sys L n p := by
  obtain ⟨hne, j, hj, hfl⟩ := h
  intro heq
  rw [heq, sub_self, abs_zero] at hfl
  have hθ : chT n j q p ≠ 0 := by
    intro h0
    apply hne
    apply finiteConfigLatticeIndex_injective eta n
    have := hj
    unfold OnCh at this
    rw [show cidx n q (lead j) - cidx n p (lead j) = chT n j q p from rfl, h0] at this
    have htr : tr j (0 : Lattice3) = 0 := by
      cases j with
      | inl a => simp [tr]
      | inr pr => simp [tr]
    rw [htr, add_zero] at this
    exact this
  have hr : 0 < FSChannel.rho (chT n j q p) := by
    unfold FSChannel.rho
    apply Real.sqrt_pos.mpr
    have := one_le_latticeNormSq hθ
    have e : latticeNormSq (chT n j q p) = FSLattice.lsq (chT n j q p) := rfl
    linarith
  have hg := gF_pos hL
  have hm := muCh_pos sys j
  have : 0 < gF L ^ 2 * FSChannel.rho (chT n j q p) / muCh sys j := by positivity
  linarith

/-- **The homological equation** `[A, Σ₂^bb] = H₂^{bb,gap}`. -/
theorem comm_Sig2bb (hL : 0 < L) :
    FSKernel.dg (fun q => (Asym sys L n q : ℂ)) ∘ₗ Sig2bb sys L n -
      Sig2bb sys L n ∘ₗ FSKernel.dg (fun q => (Asym sys L n q : ℂ)) = Hgap sys L n := by
  unfold Sig2bb Hgap
  apply FSKernel.comm_divK
  intro q p hqp
  unfold hgapK
  split_ifs with h
  · exact absurd hqp (gapC_ne hL h)
  · rfl

/-- The kernel of `Σ₂^bb` is skew-Hermitian. -/
lemma sig2bbK_skew (hL : 0 < L) (q p : Cfg eta n) :
    FSKernel.divK (Asym sys L n) (hgapK sys L n) p q =
      -conj (FSKernel.divK (Asym sys L n) (hgapK sys L n) q p) := by
  unfold FSKernel.divK
  by_cases h : Asym sys L n q = Asym sys L n p
  · rw [if_pos h.symm, if_pos h]; simp
  · rw [if_neg (Ne.symm h), if_neg h, hgapK_conj hL q p, map_div₀, Complex.conj_ofReal,
      ← div_neg, ← Complex.ofReal_neg, neg_sub]

/-- **`Σ₂^bb` is skew-adjoint**: `⟪Σ u, v⟫ = -⟪u, Σ v⟫`. -/
theorem inner_Sig2bb (hL : 0 < L) (u v : En eta n) :
    ⟪Sig2bb sys L n u, v⟫_ℂ = -⟪u, Sig2bb sys L n v⟫_ℂ :=
  FSKernel.kop_skew _ (fun q p => sig2bbK_skew hL q p) u v

theorem Hgap_symm (hL : 0 < L) : (Hgap sys L n).IsSymmetric :=
  FSKernel.kop_symm _ fun q p => hgapK_conj hL q p

theorem Hres_symm (hL : 0 < L) : (Hres sys L n).IsSymmetric :=
  FSKernel.kop_symm _ fun q p => hresK_conj hL q p

end FSNormal
