import PlaneWave.FluxBox.SharedComDegenerate

/-!
# Flux route, stage 3, part 42: the shared com words — the case analysis

For the pair `j₂ ∋ a, t` and `j₁` moving `a` but not `t`, every outer channel `j₃` either admits a
**common coordinate** `ζ = regSum A` (a coordinate of `j₂` killed by `j₁` and `j₃`: `{t}`, `{t, u}` or
`{a, s}`), or is **degenerate** (`j₃ = j₂`; `j₁ = (a)`, `j₃ = (t)`; `j₁ = (a, s)`, `j₃ = (t, s)`), and
then `t` is moved by `j₃` and the label `clr a t` (registers `a, t` cleared) or `clrs a t s` (their
sum collected on `s`) is killed by the three channels and injective with `(k_a, k_t)` on its fibres
(`shared_cases`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Labels

/-- Clearing the registers `a, t`. -/
def clr (a t : Fin eta) (k : Cf eta) : Cf eta := k - Pi.single a (k a) - Pi.single t (k t)

/-- Clearing the registers `a, t` and collecting their sum on `s`. -/
def clrs (a t s : Fin eta) (k : Cf eta) : Cf eta := clr a t k + Pi.single s (k a + k t)

lemma clr_add (a t : Fin eta) (k v : Cf eta) : clr a t (k + v) = clr a t k + clr a t v := by
  unfold clr
  simp only [Pi.add_apply, Pi.single_add]
  abel

lemma clrs_add (a t s : Fin eta) (k v : Cf eta) : clrs a t s (k + v) = clrs a t s k + clrs a t s v := by
  unfold clrs
  rw [clr_add]
  simp only [Pi.add_apply, Pi.single_add]
  abel

lemma clr_apply_of_ne {a t r : Fin eta} (hra : r ≠ a) (hrt : r ≠ t) (k : Cf eta) : clr a t k r = k r := by
  unfold clr
  simp [hra, hrt]

lemma clr_eq_zero_of_supp {a t : Fin eta} (hat : a ≠ t) {v : Cf eta}
    (hv : ∀ r, r ≠ a → r ≠ t → v r = 0) : clr a t v = 0 := by
  funext r
  by_cases hra : r = a
  · subst hra
    unfold clr
    simp [hat]
  · by_cases hrt : r = t
    · subst hrt
      unfold clr
      simp [hra]
    · rw [clr_apply_of_ne hra hrt]; exact hv r hra hrt

lemma clrs_eq_zero_of_supp {a t s : Fin eta} (hat : a ≠ t) (has : a ≠ s) (hts : t ≠ s) {v : Cf eta}
    (hv : ∀ r, r ≠ a → r ≠ t → r ≠ s → v r = 0) (hsum : v a + v t + v s = 0) :
    clrs a t s v = 0 := by
  funext r
  unfold clrs clr
  by_cases hra : r = a
  · subst hra
    simp [hat, has]
  · by_cases hrt : r = t
    · subst hrt
      simp [hra, hts]
    · by_cases hrs : r = s
      · subst hrs
        simp [hra, hrt]
        rw [← hsum]; abel
      · simp [hra, hrt, hrs]
        exact hv r hra hrt hrs

lemma clr_inj {a t : Fin eta} {k k' : Cf eta} (h : clr a t k = clr a t k') (ha : k a = k' a)
    (ht : k t = k' t) : k = k' := by
  funext r
  by_cases hra : r = a
  · rw [hra, ha]
  by_cases hrt : r = t
  · rw [hrt, ht]
  have := congrFun h r
  rwa [clr_apply_of_ne hra hrt, clr_apply_of_ne hra hrt] at this

lemma clrs_inj {a t s : Fin eta} (has : a ≠ s) (hts : t ≠ s) {k k' : Cf eta}
    (h : clrs a t s k = clrs a t s k') (ha : k a = k' a) (ht : k t = k' t) : k = k' := by
  funext r
  by_cases hra : r = a
  · rw [hra, ha]
  by_cases hrt : r = t
  · rw [hrt, ht]
  have h1 := congrFun h r
  unfold clrs at h1
  simp only [Pi.add_apply] at h1
  rw [clr_apply_of_ne hra hrt, clr_apply_of_ne hra hrt] at h1
  by_cases hrs : r = s
  · subst hrs
    simp only [Pi.single_eq_same] at h1
    rw [ha, ht] at h1
    exact add_right_cancel h1
  · simp only [Pi.single_apply, hrs, if_false, add_zero] at h1
    exact h1

end Labels

/-! ## Channels and labels -/

section ChLabels

lemma tr_eq_zero_of_not_moved' (j : Ch eta) (σ : Lattice3) {r : Fin eta} (hr : r ∉ moved j) :
    tr j σ r = 0 := tr_apply_not_moved j σ hr

/-- A pair hop conserves the total momentum of any set of registers containing the pair. -/
lemma sum_tr_pair_eq_zero (pr : FiniteElectronPair eta) (σ : Lattice3) {S : Finset (Fin eta)}
    (hS : moved (.inr pr : Ch eta) ⊆ S) : ∑ r ∈ S, tr (.inr pr) σ r = 0 := by
  classical
  have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
  rw [← Finset.sum_subset hS (fun r _ hr => tr_apply_not_moved _ σ hr)]
  simp only [moved]
  rw [Finset.sum_pair hne]
  simp [tr, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]

lemma kill_clr {a t : Fin eta} (hat : a ≠ t) {j : Ch eta} (h : ∀ r ∈ moved j, r = a ∨ r = t)
    (k : Cf eta) (σ : Lattice3) : clr a t (k + tr j σ) = clr a t k := by
  have h0 : clr a t (tr j σ) = 0 := by
    apply clr_eq_zero_of_supp hat
    intro r hra hrt
    apply tr_apply_not_moved
    intro hr
    rcases h r hr with h1 | h1
    · exact hra h1
    · exact hrt h1
  rw [clr_add, h0, add_zero]

lemma kill_clrs {a t s : Fin eta} (hat : a ≠ t) (has : a ≠ s) (hts : t ≠ s)
    {pr : FiniteElectronPair eta} (h : ∀ r ∈ moved (.inr pr : Ch eta), r = a ∨ r = t ∨ r = s)
    (k : Cf eta) (σ : Lattice3) : clrs a t s (k + tr (.inr pr) σ) = clrs a t s k := by
  classical
  have hv : ∀ r, r ≠ a → r ≠ t → r ≠ s → tr (.inr pr) σ r = 0 := by
    intro r hra hrt hrs
    apply tr_apply_not_moved
    intro hr
    rcases h r hr with h1 | h1 | h1
    · exact hra h1
    · exact hrt h1
    · exact hrs h1
  have hsum : tr (.inr pr) σ a + tr (.inr pr) σ t + tr (.inr pr) σ s = 0 := by
    have hS : moved (.inr pr : Ch eta) ⊆ {a, t, s} := by
      intro r hr
      rcases h r hr with h1 | h1 | h1 <;> simp [h1]
    have := sum_tr_pair_eq_zero pr σ hS
    rw [Finset.sum_insert (by simp [hat, has]), Finset.sum_pair hts] at this
    rw [← this]; abel
  have h0 : clrs a t s (tr (.inr pr) σ) = 0 := clrs_eq_zero_of_supp hat has hts hv hsum
  rw [clrs_add, h0, add_zero]

end ChLabels

/-! ## The case analysis -/

section Cases

lemma pair_other (pr : FiniteElectronPair eta) {x : Fin eta} (hx : x ∈ moved (.inr pr : Ch eta)) :
    ∃ y, y ≠ x ∧ ∀ r, r ∈ moved (.inr pr : Ch eta) ↔ r = x ∨ r = y := by
  have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
  simp only [moved, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with rfl | rfl
  · exact ⟨pr.1.2, hne.symm, fun r => Iff.rfl⟩
  · exact ⟨pr.1.1, hne, fun r => Or.comm⟩

lemma one_moved {a' a : Fin eta} (h : a ∈ moved (.inl a' : Ch eta)) : a = a' := by
  simpa [moved] using h

lemma coord_single_of_moved (j : Ch eta) {x : Fin eta} (hx : x ∈ moved j) :
    ∃ ε : ℤ, IsCoord j {x} ε := by
  obtain ⟨ε, hε, h⟩ := tr_single_coord' j hx
  exact ⟨ε, by simp, hε, fun τ => by simp only [regSum, Finset.sum_singleton]; exact h τ⟩

lemma regSum_single_tr_zero (j : Ch eta) {x : Fin eta} (hx : x ∉ moved j) (σ : Lattice3) :
    regSum {x} (tr j σ) = 0 := by
  simp only [regSum, Finset.sum_singleton]; exact tr_apply_not_moved j σ hx

lemma regSum_pair_tr_zero_of_not {j : Ch eta} {x y : Fin eta} (hxy : x ≠ y) (hx : x ∉ moved j)
    (hy : y ∉ moved j) (σ : Lattice3) : regSum {x, y} (tr j σ) = 0 := by
  simp only [regSum]
  rw [Finset.sum_pair hxy, tr_apply_not_moved j σ hx, tr_apply_not_moved j σ hy, add_zero]

lemma regSum_pair_tr_zero_own (pr : FiniteElectronPair eta) {x y : Fin eta} (hxy : x ≠ y)
    (hx : x ∈ moved (.inr pr : Ch eta)) (hy : y ∈ moved (.inr pr : Ch eta)) (σ : Lattice3) :
    regSum {x, y} (tr (.inr pr) σ) = 0 := by
  have hS : moved (.inr pr : Ch eta) ⊆ {x, y} := by
    intro r hr
    obtain ⟨z, hzx, hz⟩ := pair_other pr hx
    have hy' := (hz y).mp hy
    rcases (hz r).mp hr with h | h
    · simp [h]
    · rcases hy' with h' | h'
      · exact absurd h' hxy.symm
      · simp [h, ← h']
  have := sum_tr_pair_eq_zero pr σ hS
  simpa [regSum] using this

/-- A coordinate of `j₂` on `{x, y}` with `x` moved and `y` not moved by `j₂`. -/
lemma coord_pair_of (j : Ch eta) {x y : Fin eta} (hxy : x ≠ y) (hx : x ∈ moved j) (hy : y ∉ moved j) :
    ∃ ε : ℤ, IsCoord j {x, y} ε := by
  obtain ⟨ε, hε, h⟩ := tr_single_coord' j hx
  refine ⟨ε, ?_, hε, fun τ => ?_⟩
  · exact (Finset.card_insert_le _ _).trans (by simp)
  · simp only [regSum]
    rw [Finset.sum_pair hxy, h τ, tr_apply_not_moved j τ hy, add_zero]

/-- **The shared case analysis**: a common coordinate, or a degenerate triple with a label. -/
theorem shared_cases {j₁ j₃ : Ch eta} {pr : FiniteElectronPair eta} {a t : Fin eta}
    (ha2 : a ∈ moved (.inr pr : Ch eta)) (ht2 : t ∈ moved (.inr pr : Ch eta)) (hat : a ≠ t)
    (ha1 : a ∈ moved j₁) (ht1 : t ∉ moved j₁) :
    (∃ (A : Finset (Fin eta)) (ε : ℤ), IsCoord (.inr pr) A ε ∧ (∀ σ, regSum A (tr j₁ σ) = 0) ∧
        (∀ σ, regSum A (tr j₃ σ) = 0)) ∨
      (t ∈ moved j₃ ∧ ∃ ℓ : Cf eta → Cf eta, (∀ k σ, ℓ (k + tr j₁ σ) = ℓ k) ∧
        (∀ k σ, ℓ (k + tr (.inr pr) σ) = ℓ k) ∧ (∀ k σ, ℓ (k + tr j₃ σ) = ℓ k) ∧
        (∀ k k', ℓ k = ℓ k' → k a = k' a → k t = k' t → k = k')) := by
  classical
  have hm2 : ∀ r ∈ moved (.inr pr : Ch eta), r = a ∨ r = t := by
    intro r hr
    obtain ⟨z, hza, hz⟩ := pair_other pr ha2
    have ht' := (hz t).mp ht2
    rcases (hz r).mp hr with h | h
    · exact Or.inl h
    · rcases ht' with h' | h'
      · exact absurd h' hat.symm
      · exact Or.inr (h.trans h'.symm)
  by_cases ht3 : t ∈ moved j₃
  swap
  · -- the coordinate `{t}`
    obtain ⟨ε, hε⟩ := coord_single_of_moved _ ht2
    exact Or.inl ⟨{t}, ε, hε, regSum_single_tr_zero j₁ ht1, regSum_single_tr_zero j₃ ht3⟩
  cases j₁ with
  | inl a' =>
    have ha' := one_moved ha1
    subst ha'
    have hk1 : ∀ r ∈ moved (.inl a : Ch eta), r = a ∨ r = t := fun r hr => Or.inl (one_moved hr)
    cases j₃ with
    | inl t' =>
      have ht' := one_moved ht3
      subst ht'
      refine Or.inr ⟨ht3, clr a t, kill_clr hat hk1, kill_clr hat hm2, kill_clr hat
        (fun r hr => Or.inr (one_moved hr)), fun k k' h h1 h2 => clr_inj h h1 h2⟩
    | inr pr₃ =>
      obtain ⟨u, hut, hu⟩ := pair_other pr₃ ht3
      by_cases hua : u = a
      · subst hua
        refine Or.inr ⟨ht3, clr u t, kill_clr hat hk1, kill_clr hat hm2, kill_clr hat
          (fun r hr => by rcases (hu r).mp hr with h | h <;> simp [h]), fun k k' h h1 h2 => clr_inj h h1 h2⟩
      · have hu2 : u ∉ moved (.inr pr : Ch eta) := fun h => by
          rcases hm2 u h with h' | h'
          · exact hua h'
          · exact hut h'
        obtain ⟨ε, hε⟩ := coord_pair_of (.inr pr) hut.symm ht2 hu2
        refine Or.inl ⟨{t, u}, ε, hε, regSum_pair_tr_zero_of_not hut.symm
          (fun h => by have := one_moved h; exact hat this.symm)
          (fun h => hua (one_moved h)), regSum_pair_tr_zero_own pr₃ hut.symm ht3 ((hu u).mpr (Or.inr rfl))⟩
  | inr pr₁ =>
    obtain ⟨s, hsa, hs⟩ := pair_other pr₁ ha1
    have hst : s ≠ t := fun h => ht1 ((hs t).mpr (Or.inr h.symm))
    have hs2 : s ∉ moved (.inr pr : Ch eta) := fun h => by
      rcases hm2 s h with h' | h'
      · exact hsa h'
      · exact hst h'
    have hk1 : ∀ r ∈ moved (.inr pr₁ : Ch eta), r = a ∨ r = t ∨ r = s := fun r hr => by
      rcases (hs r).mp hr with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    -- the coordinate `{a, s}`
    obtain ⟨εa, hεa⟩ := coord_pair_of (.inr pr) hsa.symm ha2 hs2
    have hA1 : ∀ σ, regSum {a, s} (tr (.inr pr₁) σ) = 0 :=
      regSum_pair_tr_zero_own pr₁ hsa.symm ha1 ((hs s).mpr (Or.inr rfl))
    cases j₃ with
    | inl t' =>
      have ht' := one_moved ht3
      subst ht'
      exact Or.inl ⟨{a, s}, εa, hεa, hA1, regSum_pair_tr_zero_of_not hsa.symm
        (fun h => hat (one_moved h)) (fun h => hst (one_moved h))⟩
    | inr pr₃ =>
      obtain ⟨u, hut, hu⟩ := pair_other pr₃ ht3
      by_cases hua : u = a ∨ u = s
      · have hk3 : ∀ r ∈ moved (.inr pr₃ : Ch eta), r = a ∨ r = t ∨ r = s := fun r hr => by
          rcases (hu r).mp hr with h | h
          · exact Or.inr (Or.inl h)
          · rcases hua with h' | h'
            · exact Or.inl (h.trans h')
            · exact Or.inr (Or.inr (h.trans h'))
        have hm2' : ∀ r ∈ moved (.inr pr : Ch eta), r = a ∨ r = t ∨ r = s := fun r hr => by
          rcases hm2 r hr with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        refine Or.inr ⟨ht3, clrs a t s, kill_clrs hat hsa.symm hst.symm hk1,
          kill_clrs hat hsa.symm hst.symm hm2', kill_clrs hat hsa.symm hst.symm hk3,
          fun k k' h h1 h2 => clrs_inj hsa.symm hst.symm h h1 h2⟩
      · push Not at hua
        have ha3 : a ∉ moved (.inr pr₃ : Ch eta) := fun h => by
          rcases (hu a).mp h with h' | h'
          · exact hat h'
          · exact hua.1 h'.symm
        have hs3 : s ∉ moved (.inr pr₃ : Ch eta) := fun h => by
          rcases (hu s).mp h with h' | h'
          · exact hst h'
          · exact hua.2 h'.symm
        exact Or.inl ⟨{a, s}, εa, hεa, hA1, regSum_pair_tr_zero_of_not hsa.symm ha3 hs3⟩

end Cases

end FSFlux
