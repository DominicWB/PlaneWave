import PlaneWave.FluxBox.FarColdWords

/-!
# Flux route, stage 3, part 23: Hardy on classes and the line tools

The tools of the third round (`flux3_blueprint.md` §2c).

* `hardy_classes`: the unit lattice Coulomb kernel acting within the classes of a map `cl`,
  in a coordinate `ξ` injective on each class, is bounded from the `H¹` weight `1 + |ξ|²`
  (from the release's `HasFiniteSupportUnitLatticeCoulombHardyBound`, class by class);
  `hardy_classes_dual`: its dual, `Σ_t (1 + |ξ_t|²)⁻¹ (K L)_t² ≤ H² Σ L²`.
* line labels: `lineLab j k = k - tr_j(k_lead)` is constant exactly on the `j`-lines
  (`onCh_iff_lineLab`), and additive;
* coordinates: `IsCoord j A ε` (`regSum A ∘ tr_j = ε •`, `ε = ±1`); every channel has one
  (`coord_lead`), and for `j ≠ j'` there is one killed by `j'` (`exists_coord_ne`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Hardy on classes -/

section HardyClasses

omit [Fintype ν] in
lemma unitK_eq (a b : Lattice3) :
    unitLatticeCoulombKernel (latticeSub a b) = ((1 / FSLattice.lsq (a - b) : ℝ) : ℂ) := by
  rw [unitLatticeCoulombKernel_eq_inv_normSq, latticeSub_eq_sub]
  rfl

omit [Fintype ν] in
/-- **Hardy on classes**: for `ξ` injective on each class of `cl`,
`Σ_t (Σ_{s ~ t} L_s/|ξ_t - ξ_s|²)² ≤ H² Σ_s (1 + |ξ_s|²) L_s²`. -/
theorem hardy_classes {ι κ : Type} [DecidableEq κ] {Hunit : ℝ}
    (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (T : Finset ι) (cl : ι → κ) (ξ : ι → Lattice3)
    (hξ : ∀ s ∈ T, ∀ t ∈ T, cl s = cl t → ξ s = ξ t → s = t) (L : ι → ℝ) :
    ∑ t ∈ T, (∑ s ∈ T.filter (fun s => cl s = cl t), L s / FSLattice.lsq (ξ t - ξ s)) ^ 2 ≤
      Hunit ^ 2 * ∑ s ∈ T, (1 + FSLattice.lsq (ξ s)) * L s ^ 2 := by
  classical
  set C := T.image cl
  have hmaps : ∀ t ∈ T, cl t ∈ C := fun t ht => Finset.mem_image_of_mem cl ht
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, ← Finset.sum_fiberwise_of_maps_to hmaps,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  set S := T.filter (fun t => cl t = c) with hSdef
  have hS : ∀ t ∈ S, T.filter (fun s => cl s = cl t) = S := by
    intro t ht
    rw [(Finset.mem_filter.mp ht).2]
  rw [Finset.sum_congr rfl fun t ht => by rw [hS t ht]]
  have hinj : Function.Injective (fun s : S => ξ s.1) := by
    intro a b h
    apply Subtype.ext
    have ha := Finset.mem_filter.mp a.2
    have hb := Finset.mem_filter.mp b.2
    exact hξ a.1 ha.1 b.1 hb.1 (ha.2.trans hb.2.symm) h
  have h := hH S (fun s => ξ s.1) hinj (fun s => (L s.1 : ℂ))
  unfold finiteSupportUnitLatticeCoulombOutputSq finiteSupportUnitLatticeCoulombAction
    finiteSupportLatticeH1Sq at h
  simp only [unitK_eq] at h
  have e1 : ∀ q : S, ‖∑ p : S, (L p.1 : ℂ) * ((1 / FSLattice.lsq (ξ q.1 - ξ p.1) : ℝ) : ℂ)‖ ^ 2 =
      (∑ p ∈ S, L p / FSLattice.lsq (ξ q.1 - ξ p)) ^ 2 := by
    intro q
    rw [← Finset.sum_coe_sort S (fun p => L p / FSLattice.lsq (ξ q.1 - ξ p))]
    have : ∑ p : S, (L p.1 : ℂ) * ((1 / FSLattice.lsq (ξ q.1 - ξ p.1) : ℝ) : ℂ) =
        ((∑ p : S, L p.1 / FSLattice.lsq (ξ q.1 - ξ p.1) : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have e2 : ∀ p : S, (1 + latticeNormSq (ξ p.1)) * ‖(L p.1 : ℂ)‖ ^ 2 =
      (1 + FSLattice.lsq (ξ p.1)) * L p.1 ^ 2 := by
    intro p
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rfl
  simp only [e1, e2] at h
  rw [Finset.sum_coe_sort S (fun t => (∑ p ∈ S, L p / FSLattice.lsq (ξ t - ξ p)) ^ 2),
    Finset.sum_coe_sort S (fun p => (1 + FSLattice.lsq (ξ p)) * L p ^ 2)] at h
  exact h

omit [Fintype ν] in
/-- **The dual Hardy on classes**: `Σ_t (1 + |ξ_t|²)⁻¹ (Σ_{s ~ t} L_s/|ξ_t - ξ_s|²)² ≤ H² Σ_s L_s²`. -/
theorem hardy_classes_dual {ι κ : Type} [DecidableEq κ] {Hunit : ℝ}
    (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (T : Finset ι) (cl : ι → κ) (ξ : ι → Lattice3)
    (hξ : ∀ s ∈ T, ∀ t ∈ T, cl s = cl t → ξ s = ξ t → s = t) (L : ι → ℝ) :
    ∑ t ∈ T, (∑ s ∈ T.filter (fun s => cl s = cl t), L s / FSLattice.lsq (ξ t - ξ s)) ^ 2 /
        (1 + FSLattice.lsq (ξ t)) ≤ Hunit ^ 2 * ∑ s ∈ T, L s ^ 2 := by
  classical
  set G : ι → ℝ := fun t => ∑ s ∈ T.filter (fun s => cl s = cl t), L s / FSLattice.lsq (ξ t - ξ s)
    with hG
  set D : ι → ℝ := fun t => 1 + FSLattice.lsq (ξ t) with hD
  have hD0 : ∀ t, 0 < D t := fun t => by
    simp only [hD]; linarith [FSLattice.lsq_nonneg (ξ t)]
  set y : ι → ℝ := fun t => G t / D t with hy
  set S := ∑ t ∈ T, G t ^ 2 / D t with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun t _ => div_nonneg (sq_nonneg _) (hD0 t).le
  -- S = Σ_s L_s (K y)_s
  set Gy : ι → ℝ := fun s => ∑ t ∈ T.filter (fun t => cl t = cl s), y t / FSLattice.lsq (ξ s - ξ t)
    with hGy
  have hswap : S = ∑ s ∈ T, L s * Gy s := by
    have e1 : S = ∑ t ∈ T, y t * G t := by
      refine Finset.sum_congr rfl fun t _ => ?_
      show G t ^ 2 / D t = G t / D t * G t
      rw [div_mul_eq_mul_div, sq]
    rw [e1]
    simp only [hG, hGy, Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    by_cases h : cl s = cl t
    · rw [if_pos h, if_pos h.symm, FSChannel.lsq_sub_comm (ξ t) (ξ s)]
      ring
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
      ring
  -- Cauchy–Schwarz and Hardy for `y`
  have hCS : S ≤ Real.sqrt (∑ s ∈ T, L s ^ 2) * Real.sqrt (∑ s ∈ T, Gy s ^ 2) := by
    rw [hswap]
    exact Real.sum_mul_le_sqrt_mul_sqrt T L Gy
  have hHy := hardy_classes hH T cl ξ hξ y
  have hDy : ∑ s ∈ T, (1 + FSLattice.lsq (ξ s)) * y s ^ 2 = S := by
    refine Finset.sum_congr rfl fun t _ => ?_
    show D t * (G t / D t) ^ 2 = G t ^ 2 / D t
    have := (hD0 t).ne'
    rw [div_pow]
    field_simp
  rw [hDy] at hHy
  have hGy2 : ∑ s ∈ T, Gy s ^ 2 ≤ Hunit ^ 2 * S := hHy
  have h1 : Real.sqrt (∑ s ∈ T, Gy s ^ 2) ≤ |Hunit| * Real.sqrt S := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt hGy2
  set a := Real.sqrt (∑ s ∈ T, L s ^ 2)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have h2 : S ≤ a * (|Hunit| * Real.sqrt S) := hCS.trans (mul_le_mul_of_nonneg_left h1 ha)
  have hsS := Real.sq_sqrt hS0
  have hs0 := Real.sqrt_nonneg S
  have hH0 := abs_nonneg Hunit
  have h3 : Real.sqrt S ≤ a * |Hunit| := by
    by_cases hz : Real.sqrt S = 0
    · rw [hz]; positivity
    · have hpos : 0 < Real.sqrt S := lt_of_le_of_ne hs0 (Ne.symm hz)
      have : Real.sqrt S * Real.sqrt S ≤ a * |Hunit| * Real.sqrt S := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  have h4 : S ≤ (a * |Hunit|) ^ 2 := by
    rw [← hsS]; exact pow_le_pow_left₀ hs0 h3 2
  have ha2 : a ^ 2 = ∑ s ∈ T, L s ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun s _ => sq_nonneg _)
  calc S ≤ (a * |Hunit|) ^ 2 := h4
    _ = Hunit ^ 2 * a ^ 2 := by rw [mul_pow, sq_abs]; ring
    _ = Hunit ^ 2 * ∑ s ∈ T, L s ^ 2 := by rw [ha2]

end HardyClasses

/-! ## Line labels and coordinates -/

section Labels

/-- The label of the `j`-line through `k`: `k - tr_j(k_lead)`. -/
def lineLab (j : Ch eta) (k : Cf eta) : Cf eta := k - tr j (k (lead j))

omit [Fintype ν] in
lemma lineLab_add (j : Ch eta) (k k' : Cf eta) :
    lineLab j (k + k') = lineLab j k + lineLab j k' := by
  unfold lineLab
  rw [Pi.add_apply, tr_add]
  abel

omit [Fintype ν] in
lemma lineLab_sub (j : Ch eta) (k k' : Cf eta) :
    lineLab j (k - k') = lineLab j k - lineLab j k' := by
  unfold lineLab
  rw [Pi.sub_apply, tr_sub]
  abel

omit [Fintype ν] in
lemma lineLab_tr (j : Ch eta) (τ : Lattice3) : lineLab j (tr j τ) = 0 := by
  unfold lineLab
  rw [tr_lead]
  abel

omit [Fintype ν] in
/-- **The line labels**: `q, p` are joined by a hop of `j` iff they have the same `j`-label. -/
lemma onCh_iff_lineLab (j : Ch eta) (q p : Cf eta) : OnCh j q p ↔ lineLab j q = lineLab j p := by
  constructor
  · intro h
    have e : q = p + tr j (q (lead j) - p (lead j)) := h
    generalize q (lead j) - p (lead j) = θ at e
    rw [e, lineLab_add, lineLab_tr, add_zero]
  · intro h
    unfold lineLab at h
    unfold OnCh
    rw [tr_sub]
    calc q = (q - tr j (q (lead j))) + tr j (q (lead j)) := by abel
      _ = (p - tr j (p (lead j))) + tr j (q (lead j)) := by rw [h]
      _ = p + (tr j (q (lead j)) - tr j (p (lead j))) := by abel

omit [Fintype ν] in
lemma regSum_sub (A : Finset (Fin eta)) (k k' : Cf eta) :
    regSum A (k - k') = regSum A k - regSum A k' := by
  unfold regSum
  rw [← Finset.sum_sub_distrib]
  rfl

omit [Fintype ν] in
lemma regSum_zero (A : Finset (Fin eta)) : regSum A (0 : Cf eta) = 0 := by
  unfold regSum
  simp

omit [Fintype ν] in
/-- A coordinate killed by `tr_j` is constant on the `j`-lines. -/
lemma regSum_lineLab {j : Ch eta} {A : Finset (Fin eta)} (hA : ∀ σ, regSum A (tr j σ) = 0)
    (k : Cf eta) : regSum A (lineLab j k) = regSum A k := by
  unfold lineLab
  rw [regSum_sub, hA, sub_zero]

/-- **A coordinate of the channel `j`**: a set of at most two registers on which the hops of
`j` act as `ε •`, `ε = ±1`. -/
structure IsCoord (j : Ch eta) (A : Finset (Fin eta)) (ε : ℤ) : Prop where
  card : A.card ≤ 2
  sign : ε = 1 ∨ ε = -1
  act : ∀ τ, regSum A (tr j τ) = ε • τ

omit [Fintype ν] in
lemma IsCoord.ne_zero {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (h : IsCoord j A ε) : ε ≠ 0 := by
  rcases h.sign with rfl | rfl <;> norm_num

omit [Fintype ν] in
lemma lsq_sign_smul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (τ : Lattice3) :
    FSLattice.lsq (ε • τ) = FSLattice.lsq τ := by
  rcases hε with rfl | rfl
  · rw [one_smul]
  · rw [neg_smul, one_smul, lsq_neg]

omit [Fintype ν] in
lemma sign_mul_self {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : ε * ε = 1 := by
  rcases hε with rfl | rfl <;> norm_num

omit [Fintype ν] in
/-- The lead register is a coordinate of every channel. -/
lemma coord_lead (j : Ch eta) : IsCoord j {lead j} 1 where
  card := by simp
  sign := Or.inl rfl
  act := fun τ => by
    simp only [regSum, Finset.sum_singleton, one_smul]
    exact tr_lead j τ

omit [Fintype ν] in
/-- A moved register sees the transfer with a sign `±1`. -/
lemma tr_single_coord' (j : Ch eta) {x : Fin eta} (hx : x ∈ moved j) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ τ : Lattice3, tr j τ x = ε • τ := by
  cases j with
  | inl a =>
    simp only [moved, Finset.mem_singleton] at hx
    subst hx
    exact ⟨1, Or.inl rfl, fun τ => by simp [tr]⟩
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    simp only [moved, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, Or.inl rfl, fun τ => by simp [tr, Pi.single_eq_of_ne hne]⟩
    · exact ⟨-1, Or.inr rfl, fun τ => by simp [tr, Pi.single_eq_of_ne hne.symm]⟩

omit [Fintype ν] in
/-- **The transverse coordinate**: for `j ≠ j'` there is a coordinate of `j` killed by `j'`. -/
lemma exists_coord_ne {j j' : Ch eta} (hjj : j ≠ j') :
    ∃ (A : Finset (Fin eta)) (ε : ℤ), IsCoord j A ε ∧ ∀ σ, regSum A (tr j' σ) = 0 := by
  classical
  by_cases hx : ∃ x ∈ moved j, x ∉ moved j'
  · obtain ⟨x, hxj, hxj'⟩ := hx
    obtain ⟨ε, hε, hxc⟩ := tr_single_coord' j hxj
    refine ⟨{x}, ε, ⟨by simp, hε, fun τ => ?_⟩, fun σ => ?_⟩
    · simp only [regSum, Finset.sum_singleton]; exact hxc τ
    · simp only [regSum, Finset.sum_singleton]; exact tr_apply_not_moved j' σ hxj'
  · push Not at hx
    cases j with
    | inr pr =>
      exfalso
      apply hjj
      apply moved_inj
      apply Finset.eq_of_subset_of_card_le (fun z hz => hx z hz)
      rw [card_moved_pair]
      exact card_moved_le j'
    | inl a =>
      have ha : a ∈ moved j' := hx a (by simp [moved])
      cases j' with
      | inl b =>
        exfalso
        simp only [moved, Finset.mem_singleton] at ha
        exact hjj (by rw [ha])
      | inr pr =>
        have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
        refine ⟨moved (.inr pr), 1, ⟨card_moved_le _, Or.inl rfl, fun τ => ?_⟩, fun σ => ?_⟩
        · simp only [regSum, moved]
          rw [Finset.sum_pair hne]
          simp only [moved, Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · simp [tr, Pi.single_eq_of_ne hne.symm]
          · simp [tr, Pi.single_eq_of_ne hne]
        · simp only [regSum, moved]
          rw [Finset.sum_pair hne]
          simp [tr, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]

omit [Fintype ν] in
/-- Along a hop of `j` a coordinate of `j` moves by `ε θ`. -/
lemma IsCoord.onCh {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε) {q p : Cf eta}
    (h : OnCh j q p) : regSum A q = regSum A p + ε • (q (lead j) - p (lead j)) := by
  have e : q = p + tr j (q (lead j) - p (lead j)) := h
  generalize q (lead j) - p (lead j) = θ at e ⊢
  rw [e, regSum_add, hA.act]

end Labels

/-! ## Lines in the box -/

section Lines

variable {N : ℕ}

/-- The label of the `j`-line through a box configuration. -/
noncomputable abbrev lab (N : ℕ) (j : Ch eta) (q : Cfg eta N) : Cf eta := lineLab j (cidx N q)

omit [Fintype ν] in
lemma lab_eq_iff {j : Ch eta} {q p : Cfg eta N} :
    lab N j q = lab N j p ↔ OnCh j (cidx N q) (cidx N p) :=
  (onCh_iff_lineLab j _ _).symm

/-- The labels of the `j`-lines meeting the box. -/
noncomputable def labs (N : ℕ) (j : Ch eta) : Finset (Cf eta) := Finset.univ.image (lab N j)

open Classical in
/-- The `j`-line sum `L_j(x)(t) = Σ_{lab p = t} x_p`. -/
noncomputable def lineSum (j : Ch eta) (x : Cfg eta N → ℝ) (t : Cf eta) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => lab N j p = t), x p

/-- The weighted line square `Σ_ℓ Ω(ℓ) L_j(x)(ℓ)²`. -/
noncomputable def lineSq (j : Ch eta) (Ω : Cf eta → ℝ) (x : Cfg eta N → ℝ) : ℝ :=
  ∑ t ∈ labs N j, Ω t * lineSum j x t ^ 2

omit [Fintype ν] in
lemma lineSum_nonneg (j : Ch eta) {x : Cfg eta N → ℝ} (hx : ∀ p, 0 ≤ x p) (t : Cf eta) :
    0 ≤ lineSum j x t := by
  classical
  unfold lineSum
  exact Finset.sum_nonneg fun p _ => hx p

omit [Fintype ν] in
lemma lineSq_nonneg (j : Ch eta) {Ω : Cf eta → ℝ} (hΩ : ∀ t, 0 ≤ Ω t) (x : Cfg eta N → ℝ) :
    0 ≤ lineSq j Ω x := by
  unfold lineSq
  exact Finset.sum_nonneg fun t _ => mul_nonneg (hΩ t) (sq_nonneg _)

omit [Fintype ν] in
open Classical in
/-- Sums over the box by `j`-lines. -/
lemma sum_by_lines (j : Ch eta) {β : Type*} [AddCommMonoid β] (F : Cfg eta N → β) :
    ∑ p, F p = ∑ t ∈ labs N j, ∑ p ∈ Finset.univ.filter (fun p => lab N j p = t), F p :=
  (Finset.sum_fiberwise_of_maps_to (fun p _ => Finset.mem_image_of_mem (lab N j) (Finset.mem_univ p))
    F).symm

omit [Fintype ν] in
/-- Weighted Cauchy–Schwarz: `(Σ x)² ≤ (Σ ω⁻¹)(Σ ω x²)` for `ω > 0`. -/
lemma sq_sum_le_inv_mul {ι : Type*} (F : Finset ι) (x ω : ι → ℝ) (hω : ∀ i, 0 < ω i) :
    (∑ i ∈ F, x i) ^ 2 ≤ (∑ i ∈ F, (ω i)⁻¹) * ∑ i ∈ F, ω i * x i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq F (fun i => Real.sqrt (ω i)⁻¹)
    (fun i => Real.sqrt (ω i) * x i)
  have e1 : ∀ i, Real.sqrt (ω i)⁻¹ * (Real.sqrt (ω i) * x i) = x i := fun i => by
    rw [← mul_assoc, ← Real.sqrt_mul (inv_nonneg.mpr (hω i).le), inv_mul_cancel₀ (hω i).ne',
      Real.sqrt_one, one_mul]
  have e2 : ∀ i, Real.sqrt (ω i)⁻¹ ^ 2 = (ω i)⁻¹ := fun i =>
    Real.sq_sqrt (inv_nonneg.mpr (hω i).le)
  have e3 : ∀ i, (Real.sqrt (ω i) * x i) ^ 2 = ω i * x i ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hω i).le]
  simp only [e1, e2, e3] at h
  exact h

omit [Fintype ν] in
open Classical in
/-- **The line Cauchy–Schwarz**: `Σ_ℓ Ω L_j(x)² ≤ S Σ_p Ω ω x_p²` when every line has
`Σ ω⁻¹ ≤ S`. -/
theorem lineSq_le (j : Ch eta) {Ω : Cf eta → ℝ} (hΩ : ∀ t, 0 ≤ Ω t) (x : Cfg eta N → ℝ)
    (ω : Cfg eta N → ℝ) (hω : ∀ p, 0 < ω p) {S : ℝ}
    (hS : ∀ q : Cfg eta N,
      ∑ p ∈ Finset.univ.filter (fun p => lab N j p = lab N j q), (ω p)⁻¹ ≤ S) :
    lineSq j Ω x ≤ S * ∑ p, Ω (lab N j p) * ω p * x p ^ 2 := by
  classical
  unfold lineSq
  rw [sum_by_lines j (fun p => Ω (lab N j p) * ω p * x p ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun t ht => ?_
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
  set F := Finset.univ.filter (fun p => lab N j p = lab N j q)
  have h1 := sq_sum_le_inv_mul F x ω hω
  have h2 := hS q
  have h3 : 0 ≤ ∑ p ∈ F, ω p * x p ^ 2 :=
    Finset.sum_nonneg fun p _ => mul_nonneg (hω p).le (sq_nonneg _)
  have e : ∑ p ∈ F, Ω (lab N j p) * ω p * x p ^ 2 = Ω (lab N j q) * ∑ p ∈ F, ω p * x p ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.mp hp).2]
    ring
  rw [e]
  have h4 : lineSum j x (lab N j q) ^ 2 ≤ S * ∑ p ∈ F, ω p * x p ^ 2 :=
    h1.trans (mul_le_mul_of_nonneg_right h2 h3)
  calc Ω (lab N j q) * lineSum j x (lab N j q) ^ 2 ≤
      Ω (lab N j q) * (S * ∑ p ∈ F, ω p * x p ^ 2) := mul_le_mul_of_nonneg_left h4 (hΩ _)
    _ = S * (Ω (lab N j q) * ∑ p ∈ F, ω p * x p ^ 2) := by ring

omit [Fintype ν] in
/-- A coordinate of `j` is injective on each `j`-line. -/
lemma coord_injOn {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    {q p : Cfg eta N} (h : OnCh j (cidx N q) (cidx N p)) (he : regSum A (cidx N q) = regSum A (cidx N p)) :
    q = p := by
  have h1 := hA.onCh h
  rw [he, left_eq_add] at h1
  have h0 : cidx N q (lead j) - cidx N p (lead j) = 0 := by
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact absurd h2 hA.ne_zero
    · exact h2
  apply finiteConfigLatticeIndex_injective eta N
  have e : cidx N q = cidx N p + tr j (cidx N q (lead j) - cidx N p (lead j)) := h
  rw [h0, tr_zero, add_zero] at e
  exact e

omit [Fintype ν] in
/-- On a `j`-hop the coordinate difference has the length of the transfer. -/
lemma coord_lsq {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    {q p : Cfg eta N} (h : OnCh j (cidx N q) (cidx N p)) :
    FSLattice.lsq (regSum A (cidx N q) - regSum A (cidx N p)) = FSLattice.lsq (chT N j q p) := by
  rw [hA.onCh h, add_sub_cancel_left, lsq_sign_smul hA.sign]
  rfl

omit [Fintype ν] in
open Classical in
/-- **The line sums of `(1 + |ζ|²)^{-3/2}`**: `≤ 125 (log₂(2N) + 2)` for a coordinate `ζ` of `j`. -/
lemma lineSum_inv_w32_le (hN : 1 ≤ N) {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ}
    (hA : IsCoord j A ε) (q : Cfg eta N) :
    ∑ p ∈ Finset.univ.filter (fun p => lab N j p = lab N j q), (w32 (regSum A (cidx N p)))⁻¹ ≤
      125 * (Nat.log 2 (2 * N) + 2) := by
  apply sum_inv_w32_image_le _ (fun p => regSum A (cidx N p)) _ (by omega)
  · intro p _
    exact lsq_regSum_box A hA.card p
  · intro p hp p' hp' he
    have h1 : lab N j p = lab N j p' :=
      (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm
    exact coord_injOn hA (lab_eq_iff.mp h1) he

omit [Fintype ν] in
open Classical in
/-- **The long-hop line bound**: if `0 ≤ K(f, d) ≤ κ(f)` on the `j`-line of `f` and `K = 0` off
it, then `Σ_f (Σ_d K x)² ≤ A L²_j(x)` with `A ≥ Σ_{line} κ²`. -/
theorem long_line_le (j : Ch eta) (x : Cfg eta N → ℝ) (hx : ∀ p, 0 ≤ x p)
    (K : Cfg eta N → Cfg eta N → ℝ) (hK0 : ∀ f d, 0 ≤ K f d) (κ : Cfg eta N → ℝ)
    (hK : ∀ f d, K f d ≤ if lab N j f = lab N j d then κ f else 0) {A : ℝ}
    (hA : ∀ q : Cfg eta N, ∑ f ∈ Finset.univ.filter (fun f => lab N j f = lab N j q), κ f ^ 2 ≤ A) :
    ∑ f, (∑ d, K f d * x d) ^ 2 ≤ A * lineSq j (fun _ => 1) x := by
  classical
  have hκ : ∀ f, 0 ≤ κ f := fun f => by
    have := hK f f
    rw [if_pos rfl] at this
    exact (hK0 f f).trans this
  have hpt : ∀ f, (∑ d, K f d * x d) ^ 2 ≤ κ f ^ 2 * lineSum j x (lab N j f) ^ 2 := by
    intro f
    have h0 : 0 ≤ ∑ d, K f d * x d := Finset.sum_nonneg fun d _ => mul_nonneg (hK0 f d) (hx d)
    have h1 : ∑ d, K f d * x d ≤ κ f * lineSum j x (lab N j f) := by
      unfold lineSum
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_le_sum fun d _ => ?_
      have := hK f d
      by_cases h : lab N j d = lab N j f
      · rw [if_pos h.symm] at this
        rw [if_pos h]
        exact mul_le_mul_of_nonneg_right this (hx d)
      · rw [if_neg (fun h' => h h'.symm)] at this
        rw [if_neg h]
        have := hK0 f d
        have : K f d = 0 := le_antisymm (by assumption) this
        rw [this, zero_mul]
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 h1 2
  refine (Finset.sum_le_sum fun f _ => hpt f).trans ?_
  rw [sum_by_lines j (fun f => κ f ^ 2 * lineSum j x (lab N j f) ^ 2)]
  unfold lineSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t ht => ?_
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
  have e : ∑ f ∈ Finset.univ.filter (fun f => lab N j f = lab N j q),
      κ f ^ 2 * lineSum j x (lab N j f) ^ 2 =
      (∑ f ∈ Finset.univ.filter (fun f => lab N j f = lab N j q), κ f ^ 2) *
        lineSum j x (lab N j q) ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [(Finset.mem_filter.mp hf).2]
  rw [e, one_mul]
  exact mul_le_mul_of_nonneg_right (hA q) (sq_nonneg _)

end Lines

/-! ## Hardy on lines -/

section LineHardy

variable {N : ℕ}

omit [Fintype ν] in
open Classical in
/-- **Hardy on the `j`-lines**, with a weight `Ω` constant on the lines and a coordinate `ζ` of `j`:
`Σ_q Ω (Σ_{p ~_j q} x_p/|θ|²)² ≤ H² Σ_p Ω (1 + |ζ_p|²) x_p²`. -/
theorem line_hardy {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    (Ω : Cf eta → ℝ) (hΩ : ∀ t, 0 ≤ Ω t) (x : Cfg eta N → ℝ) :
    ∑ q, Ω (lab N j q) * (∑ p, if OnCh j (cidx N q) (cidx N p) then
        x p / FSLattice.lsq (chT N j q p) else 0) ^ 2 ≤
      Hunit ^ 2 * ∑ p, Ω (lab N j p) * (1 + FSLattice.lsq (regSum A (cidx N p))) * x p ^ 2 := by
  classical
  have h := hardy_classes hH Finset.univ (lab N j) (fun p => regSum A (cidx N p))
    (fun s _ t _ hst he => coord_injOn hA (lab_eq_iff.mp hst) he)
    (fun p => Real.sqrt (Ω (lab N j p)) * x p)
  beta_reduce at h
  have e1 : ∀ q, Ω (lab N j q) * (∑ p, if OnCh j (cidx N q) (cidx N p) then
      x p / FSLattice.lsq (chT N j q p) else 0) ^ 2 =
      (∑ s ∈ Finset.univ.filter (fun s => lab N j s = lab N j q),
        Real.sqrt (Ω (lab N j s)) * x s /
          FSLattice.lsq (regSum A (cidx N q) - regSum A (cidx N s))) ^ 2 := by
    intro q
    rw [Finset.sum_filter]
    have hs : ∀ s, (if lab N j s = lab N j q then Real.sqrt (Ω (lab N j s)) * x s /
        FSLattice.lsq (regSum A (cidx N q) - regSum A (cidx N s)) else 0) =
        Real.sqrt (Ω (lab N j q)) * (if OnCh j (cidx N q) (cidx N s) then
          x s / FSLattice.lsq (chT N j q s) else 0) := by
      intro s
      by_cases hs : OnCh j (cidx N q) (cidx N s)
      · have hl : lab N j s = lab N j q := (lab_eq_iff.mpr hs).symm
        rw [if_pos hl, if_pos hs, hl, coord_lsq hA hs]
        ring
      · rw [if_neg (fun h => hs (lab_eq_iff.mp h.symm)), if_neg hs, mul_zero]
    rw [Finset.sum_congr rfl fun s _ => hs s, ← Finset.mul_sum, mul_pow, Real.sq_sqrt (hΩ _)]
  have e2 : ∀ p, (1 + FSLattice.lsq (regSum A (cidx N p))) * (Real.sqrt (Ω (lab N j p)) * x p) ^ 2 =
      Ω (lab N j p) * (1 + FSLattice.lsq (regSum A (cidx N p))) * x p ^ 2 := by
    intro p
    rw [mul_pow, Real.sq_sqrt (hΩ _)]
    ring
  simp only [e2] at h
  rw [Finset.sum_congr rfl fun q _ => e1 q]
  exact h

omit [Fintype ν] in
open Classical in
/-- **The dual Hardy on the `j`-lines**:
`Σ_q Ω (1 + |ζ_q|²)⁻¹ (Σ_{p ~_j q} x_p/|θ|²)² ≤ H² Σ_p Ω x_p²`. -/
theorem line_hardy_dual {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε)
    (Ω : Cf eta → ℝ) (hΩ : ∀ t, 0 ≤ Ω t) (x : Cfg eta N → ℝ) :
    ∑ q, Ω (lab N j q) * (∑ p, if OnCh j (cidx N q) (cidx N p) then
        x p / FSLattice.lsq (chT N j q p) else 0) ^ 2 / (1 + FSLattice.lsq (regSum A (cidx N q))) ≤
      Hunit ^ 2 * ∑ p, Ω (lab N j p) * x p ^ 2 := by
  classical
  have h := hardy_classes_dual hH Finset.univ (lab N j) (fun p => regSum A (cidx N p))
    (fun s _ t _ hst he => coord_injOn hA (lab_eq_iff.mp hst) he)
    (fun p => Real.sqrt (Ω (lab N j p)) * x p)
  beta_reduce at h
  have e1 : ∀ q, Ω (lab N j q) * (∑ p, if OnCh j (cidx N q) (cidx N p) then
      x p / FSLattice.lsq (chT N j q p) else 0) ^ 2 / (1 + FSLattice.lsq (regSum A (cidx N q))) =
      (∑ s ∈ Finset.univ.filter (fun s => lab N j s = lab N j q),
        Real.sqrt (Ω (lab N j s)) * x s /
          FSLattice.lsq (regSum A (cidx N q) - regSum A (cidx N s))) ^ 2 /
        (1 + FSLattice.lsq (regSum A (cidx N q))) := by
    intro q
    congr 1
    rw [Finset.sum_filter]
    have hs : ∀ s, (if lab N j s = lab N j q then Real.sqrt (Ω (lab N j s)) * x s /
        FSLattice.lsq (regSum A (cidx N q) - regSum A (cidx N s)) else 0) =
        Real.sqrt (Ω (lab N j q)) * (if OnCh j (cidx N q) (cidx N s) then
          x s / FSLattice.lsq (chT N j q s) else 0) := by
      intro s
      by_cases hs : OnCh j (cidx N q) (cidx N s)
      · have hl : lab N j s = lab N j q := (lab_eq_iff.mpr hs).symm
        rw [if_pos hl, if_pos hs, hl, coord_lsq hA hs]
        ring
      · rw [if_neg (fun h => hs (lab_eq_iff.mp h.symm)), if_neg hs, mul_zero]
    rw [Finset.sum_congr rfl fun s _ => hs s, ← Finset.mul_sum, mul_pow, Real.sq_sqrt (hΩ _)]
  have e2 : ∀ p, (Real.sqrt (Ω (lab N j p)) * x p) ^ 2 = Ω (lab N j p) * x p ^ 2 := by
    intro p
    rw [mul_pow, Real.sq_sqrt (hΩ _)]
  simp only [e2] at h
  rw [Finset.sum_congr rfl fun q _ => e1 q]
  exact h

end LineHardy

/-! ## The transverse Hardy -/

section Transverse

variable {N : ℕ}

/-- The transverse class of a `j`-label under the hops of `j'` (coordinate `A'`, sign `ε'`). -/
def tcl (j j' : Ch eta) (A' : Finset (Fin eta)) (ε' : ℤ) (t : Cf eta) : Cf eta :=
  t - lineLab j (tr j' (ε' • regSum A' t))

omit [Fintype ν] in
lemma regSum_lineLab_tr {j j' : Ch eta} {A' : Finset (Fin eta)} {ε' : ℤ} (hA' : IsCoord j' A' ε')
    (hA'j : ∀ σ, regSum A' (tr j σ) = 0) (τ : Lattice3) :
    regSum A' (lineLab j (tr j' τ)) = ε' • τ := by
  rw [regSum_lineLab hA'j, hA'.act]

omit [Fintype ν] in
/-- The transverse class is invariant under the `j'`-translates of the labels. -/
lemma tcl_add {j j' : Ch eta} {A' : Finset (Fin eta)} {ε' : ℤ} (hA' : IsCoord j' A' ε')
    (hA'j : ∀ σ, regSum A' (tr j σ) = 0) (t : Cf eta) (τ : Lattice3) :
    tcl j j' A' ε' (t + lineLab j (tr j' τ)) = tcl j j' A' ε' t := by
  unfold tcl
  rw [regSum_add, regSum_lineLab_tr hA' hA'j, smul_add, smul_smul, sign_mul_self hA'.sign, one_smul,
    tr_add, lineLab_add]
  abel

omit [Fintype ν] in
lemma tcl_inj {j j' : Ch eta} {A' : Finset (Fin eta)} {ε' : ℤ} {s t : Cf eta}
    (h : tcl j j' A' ε' s = tcl j j' A' ε' t) (he : regSum A' s = regSum A' t) : s = t := by
  unfold tcl at h
  rw [he] at h
  exact sub_left_injective h

omit [Fintype ν] in
open Classical in
/-- **The transverse Hardy**: the hops of `j'` acting on the `j`-line sums, in a coordinate `ξ'`
of `j'` killed by `j`: `Σ_t (Σ_{s ~ t} L_s/|ξ'_t - ξ'_s|²)² ≤ H² Σ_s (1 + |ξ'_s|²) L_s²`. -/
theorem trans_hardy {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    {j j' : Ch eta} {A' : Finset (Fin eta)} {ε' : ℤ} (T : Finset (Cf eta)) (L : Cf eta → ℝ) :
    ∑ t ∈ T, (∑ s ∈ T.filter (fun s => tcl j j' A' ε' s = tcl j j' A' ε' t),
        L s / FSLattice.lsq (regSum A' t - regSum A' s)) ^ 2 ≤
      Hunit ^ 2 * ∑ s ∈ T, (1 + FSLattice.lsq (regSum A' s)) * L s ^ 2 :=
  hardy_classes hH T (tcl j j' A' ε') (regSum A') (fun _ _ _ _ h he => tcl_inj h he) L

omit [Fintype ν] in
open Classical in
/-- **A hop on the transverse family**: the `j`-line sums of `|W_{j'}| x` are dominated by the
transverse Coulomb action on the `j`-line sums of `x`. -/
theorem lineSum_hop_le {j j' : Ch eta} {A' : Finset (Fin eta)} {ε' : ℤ} (hA' : IsCoord j' A' ε')
    (hA'j : ∀ σ, regSum A' (tr j σ) = 0) (x : Cfg eta N → ℝ) (hx : ∀ p, 0 ≤ x p) (t : Cf eta) :
    lineSum j (fun d => ∑ b, if OnCh j' (cidx N d) (cidx N b) then
        x b / FSLattice.lsq (chT N j' d b) else 0) t ≤
      ∑ s ∈ (labs N j).filter (fun s => tcl j j' A' ε' s = tcl j j' A' ε' t),
        lineSum j x s / FSLattice.lsq (regSum A' t - regSum A' s) := by
  classical
  unfold lineSum
  rw [Finset.sum_comm]
  -- the bound for a fixed input `b`
  have hb : ∀ b, ∑ d ∈ Finset.univ.filter (fun d => lab N j d = t),
      (if OnCh j' (cidx N d) (cidx N b) then x b / FSLattice.lsq (chT N j' d b) else 0) ≤
      x b * (if tcl j j' A' ε' (lab N j b) = tcl j j' A' ε' t then
        1 / FSLattice.lsq (regSum A' t - regSum A' (lab N j b)) else 0) := by
    intro b
    rw [← Finset.sum_filter]
    set D := (Finset.univ.filter (fun d => lab N j d = t)).filter
      (fun d => OnCh j' (cidx N d) (cidx N b)) with hD
    have hval : ∀ d ∈ D, x b / FSLattice.lsq (chT N j' d b) =
        x b * (1 / FSLattice.lsq (regSum A' t - regSum A' (lab N j b))) ∧
        tcl j j' A' ε' (lab N j b) = tcl j j' A' ε' t := by
      intro d hd
      have hd1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
      have hd2 := (Finset.mem_filter.mp hd).2
      have e1 : regSum A' t = regSum A' (cidx N d) := by
        rw [← hd1]; exact regSum_lineLab hA'j _
      have e2 : regSum A' (lab N j b) = regSum A' (cidx N b) := regSum_lineLab hA'j _
      refine ⟨?_, ?_⟩
      · rw [e1, e2, coord_lsq hA' hd2]
        ring
      · have e3 : cidx N d = cidx N b + tr j' (cidx N d (lead j') - cidx N b (lead j')) := hd2
        rw [← hd1]
        show tcl j j' A' ε' (lineLab j (cidx N b)) = tcl j j' A' ε' (lineLab j (cidx N d))
        rw [e3, lineLab_add, tcl_add hA' hA'j]
    have hcard : D.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro d hd d' hd'
      have hd1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
      have hd2 := (Finset.mem_filter.mp hd).2
      have hd1' := (Finset.mem_filter.mp (Finset.mem_filter.mp hd').1).2
      have hd2' := (Finset.mem_filter.mp hd').2
      have h12 : OnCh j' (cidx N d) (cidx N d') := onCh_comp hd2 (onCh_symm hd2')
      apply coord_injOn hA' h12
      rw [← regSum_lineLab hA'j (cidx N d), ← regSum_lineLab hA'j (cidx N d')]
      show regSum A' (lab N j d) = regSum A' (lab N j d')
      rw [hd1, hd1']
    by_cases hc : tcl j j' A' ε' (lab N j b) = tcl j j' A' ε' t
    · rw [if_pos hc, Finset.sum_congr rfl fun d hd => (hval d hd).1, Finset.sum_const, nsmul_eq_mul]
      have h0 : 0 ≤ x b * (1 / FSLattice.lsq (regSum A' t - regSum A' (lab N j b))) :=
        mul_nonneg (hx b) (div_nonneg zero_le_one (FSLattice.lsq_nonneg _))
      calc (D.card : ℝ) * (x b * (1 / FSLattice.lsq (regSum A' t - regSum A' (lab N j b)))) ≤
          1 * (x b * (1 / FSLattice.lsq (regSum A' t - regSum A' (lab N j b)))) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) h0
        _ = _ := one_mul _
    · rw [if_neg hc, mul_zero]
      have hD0 : D = ∅ := Finset.eq_empty_of_forall_notMem fun d hd => hc (hval d hd).2
      rw [hD0, Finset.sum_empty]
  refine (Finset.sum_le_sum fun b _ => hb b).trans (le_of_eq ?_)
  rw [sum_by_lines j (fun b => x b * (if tcl j j' A' ε' (lab N j b) = tcl j j' A' ε' t then
      1 / FSLattice.lsq (regSum A' t - regSum A' (lab N j b)) else 0)), Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : ∀ b ∈ Finset.univ.filter (fun b => lab N j b = s),
      x b * (if tcl j j' A' ε' (lab N j b) = tcl j j' A' ε' t then
        1 / FSLattice.lsq (regSum A' t - regSum A' (lab N j b)) else 0) =
      x b * (if tcl j j' A' ε' s = tcl j j' A' ε' t then
        1 / FSLattice.lsq (regSum A' t - regSum A' s) else 0) := by
    intro b hb
    rw [(Finset.mem_filter.mp hb).2]
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul]
  split_ifs
  · ring
  · ring

omit [Fintype ν] in
open Classical in
/-- **The transverse action at a point**: a `j'`-hop acting on a function of the `j`-labels. -/
theorem hop_lineSum_le {j j' : Ch eta} {A' : Finset (Fin eta)} {ε' : ℤ} (hA' : IsCoord j' A' ε')
    (hA'j : ∀ σ, regSum A' (tr j σ) = 0) (x : Cfg eta N → ℝ) (hx : ∀ p, 0 ≤ x p) (f : Cfg eta N) :
    ∑ d, (if OnCh j' (cidx N f) (cidx N d) then
        lineSum j x (lab N j d) / FSLattice.lsq (chT N j' f d) else 0) ≤
      ∑ s ∈ (labs N j).filter (fun s => tcl j j' A' ε' s = tcl j j' A' ε' (lab N j f)),
        lineSum j x s / FSLattice.lsq (regSum A' (lab N j f) - regSum A' s) := by
  classical
  rw [← Finset.sum_filter]
  set D := Finset.univ.filter (fun d => OnCh j' (cidx N f) (cidx N d))
  have hinj : Set.InjOn (lab N j) D := by
    intro d hd d' hd' h
    have h1 := (Finset.mem_filter.mp hd).2
    have h2 := (Finset.mem_filter.mp hd').2
    have h12 : OnCh j' (cidx N d) (cidx N d') := onCh_comp (onCh_symm h1) h2
    apply coord_injOn hA' h12
    rw [← regSum_lineLab hA'j (cidx N d), ← regSum_lineLab hA'j (cidx N d')]
    exact congrArg (regSum A') h
  have hval : ∀ d ∈ D, lineSum j x (lab N j d) / FSLattice.lsq (chT N j' f d) =
      lineSum j x (lab N j d) / FSLattice.lsq (regSum A' (lab N j f) - regSum A' (lab N j d)) := by
    intro d hd
    have h1 := (Finset.mem_filter.mp hd).2
    rw [regSum_lineLab hA'j, regSum_lineLab hA'j, coord_lsq hA' h1]
  rw [Finset.sum_congr rfl hval]
  rw [← Finset.sum_image (f := fun s => lineSum j x s /
    FSLattice.lsq (regSum A' (lab N j f) - regSum A' s)) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ d), ?_⟩
    have h1 := (Finset.mem_filter.mp hd).2
    have e3 : cidx N d = cidx N f + tr j' (cidx N d (lead j') - cidx N f (lead j')) := onCh_symm h1
    show tcl j j' A' ε' (lineLab j (cidx N d)) = tcl j j' A' ε' (lineLab j (cidx N f))
    rw [e3, lineLab_add, tcl_add hA' hA'j]
  · intro s _ _
    exact div_nonneg (lineSum_nonneg j hx s) (FSLattice.lsq_nonneg _)

omit [Fintype ν] in
open Classical in
/-- **The transverse Hardy for a hop**: `L²_j(|W_{j'}| x) ≤ H² L²_j(x; 1 + |ξ'|²)`. -/
theorem lineSq_hop_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    {j j' : Ch eta} {A' : Finset (Fin eta)} {ε' : ℤ} (hA' : IsCoord j' A' ε')
    (hA'j : ∀ σ, regSum A' (tr j σ) = 0) (x : Cfg eta N → ℝ) (hx : ∀ p, 0 ≤ x p) :
    lineSq j (fun _ => 1) (fun d => ∑ b, if OnCh j' (cidx N d) (cidx N b) then
        x b / FSLattice.lsq (chT N j' d b) else 0) ≤
      Hunit ^ 2 * lineSq j (fun s => 1 + FSLattice.lsq (regSum A' s)) x := by
  classical
  unfold lineSq
  have hv0 : ∀ d, 0 ≤ ∑ b, (if OnCh j' (cidx N d) (cidx N b) then
      x b / FSLattice.lsq (chT N j' d b) else 0) := fun d =>
    Finset.sum_nonneg fun b _ => by
      split_ifs
      · exact div_nonneg (hx b) (FSLattice.lsq_nonneg _)
      · exact le_rfl
  calc ∑ t ∈ labs N j, 1 * lineSum j (fun d => ∑ b, if OnCh j' (cidx N d) (cidx N b) then
        x b / FSLattice.lsq (chT N j' d b) else 0) t ^ 2 ≤
      ∑ t ∈ labs N j, (∑ s ∈ (labs N j).filter (fun s => tcl j j' A' ε' s = tcl j j' A' ε' t),
        lineSum j x s / FSLattice.lsq (regSum A' t - regSum A' s)) ^ 2 := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [one_mul]
        exact pow_le_pow_left₀ (lineSum_nonneg j hv0 t) (lineSum_hop_le hA' hA'j x hx t) 2
    _ ≤ Hunit ^ 2 * ∑ s ∈ labs N j, (1 + FSLattice.lsq (regSum A' s)) * lineSum j x s ^ 2 :=
        trans_hardy hH (labs N j) (lineSum j x)

omit [Fintype ν] in
open Classical in
/-- **The transverse Hardy at the points**: for `κ` with line sums `Σ_{line} κ² ≤ A`,
`Σ_f κ_f² (Σ_{d ~_{j'} f} L_j(x)(d)/|θ|²)² ≤ A H² L²_j(x; 1 + |ξ'|²)`. -/
theorem hop_lineSum_sq_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    {j j' : Ch eta} {A' : Finset (Fin eta)} {ε' : ℤ} (hA' : IsCoord j' A' ε')
    (hA'j : ∀ σ, regSum A' (tr j σ) = 0) (x : Cfg eta N → ℝ) (hx : ∀ p, 0 ≤ x p)
    (κ : Cfg eta N → ℝ) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ q : Cfg eta N, ∑ f ∈ Finset.univ.filter (fun f => lab N j f = lab N j q), κ f ^ 2 ≤ A) :
    ∑ f, κ f ^ 2 * (∑ d, if OnCh j' (cidx N f) (cidx N d) then
        lineSum j x (lab N j d) / FSLattice.lsq (chT N j' f d) else 0) ^ 2 ≤
      A * (Hunit ^ 2 * lineSq j (fun s => 1 + FSLattice.lsq (regSum A' s)) x) := by
  classical
  set G : Cf eta → ℝ := fun t => ∑ s ∈ (labs N j).filter (fun s => tcl j j' A' ε' s = tcl j j' A' ε' t),
    lineSum j x s / FSLattice.lsq (regSum A' t - regSum A' s) with hG
  have hpt : ∀ f, κ f ^ 2 * (∑ d, if OnCh j' (cidx N f) (cidx N d) then
      lineSum j x (lab N j d) / FSLattice.lsq (chT N j' f d) else 0) ^ 2 ≤
      κ f ^ 2 * G (lab N j f) ^ 2 := by
    intro f
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply pow_le_pow_left₀ _ (hop_lineSum_le hA' hA'j x hx f) 2
    exact Finset.sum_nonneg fun d _ => by
      split_ifs
      · exact div_nonneg (lineSum_nonneg j hx _) (FSLattice.lsq_nonneg _)
      · exact le_rfl
  refine (Finset.sum_le_sum fun f _ => hpt f).trans ?_
  rw [sum_by_lines j (fun f => κ f ^ 2 * G (lab N j f) ^ 2)]
  have h1 : ∀ t ∈ labs N j, ∑ f ∈ Finset.univ.filter (fun f => lab N j f = t),
      κ f ^ 2 * G (lab N j f) ^ 2 ≤ A * G t ^ 2 := by
    intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    have e : ∑ f ∈ Finset.univ.filter (fun f => lab N j f = lab N j q), κ f ^ 2 * G (lab N j f) ^ 2 =
        (∑ f ∈ Finset.univ.filter (fun f => lab N j f = lab N j q), κ f ^ 2) * G (lab N j q) ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun f hf => ?_
      rw [(Finset.mem_filter.mp hf).2]
    rw [e]
    exact mul_le_mul_of_nonneg_right (hA q) (sq_nonneg _)
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hA0
  exact trans_hardy hH (labs N j) (lineSum j x)

end Transverse

end FSFlux
