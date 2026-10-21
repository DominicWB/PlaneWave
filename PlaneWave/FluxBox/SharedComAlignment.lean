import PlaneWave.FluxBox.PairingTrace

/-!
# Flux route, stage 3, part 39: the shared com words — alignment and Hardy twice

* **Alignment** (`norm_yj_align_le`): on a pair `j = (a, b)` the com symbol is
  `(g²/M̄) θ·(d_a + d_b) = (g²/m_t) (θ·d_t ± θ·c_j(d))` for either register `t` of the pair, and
  `θ·c_j(d) = (μ/g²) ω - |θ|²/2` (`ω = E(f) - E(d)`); with the floor `|ω| ≥ g²|θ|/μ`:
  `|y_j(f,d)| ≤ c_j (1 + 3|d_t|)/|θ|² + (c_j/2)/|θ|`. The first part (the **A-part**) is a Coulomb
  hop with the weight of one register; the second (the **I-part**) has no growth.
* **Hardy twice on ℤ³** (`inv_rho_le_conv`, `hardy_twice_Z3`): `1/|θ| ≤ 16 Σ_z 1/(|θ - z|²|z|²)`
  over a box around the segment, hence
  `Σ_x (1+|x|²)⁻¹ (Σ_y u_y/|x - y|)² ≤ 16² H⁴ Σ_y (1+|y|²) u_y²`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The alignment of the com dressing -/

section Align

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

omit [Fintype ν] in
lemma abs_dot_le_three (θ k : Lattice3) :
    |∑ i, ((θ i : ℤ) : ℝ) * ((k i : ℤ) : ℝ)| ≤ 3 * (FSChannel.rho θ * FSChannel.rho k) := by
  have h := abs_sum_mul_le θ (fun i => ((k i : ℤ) : ℝ))
  have h2 : ∑ i, |((k i : ℤ) : ℝ)| ≤ 3 * FSChannel.rho k := by
    rw [Fin.sum_univ_three]
    linarith [abs_coord_le_rho k 0, abs_coord_le_rho k 1, abs_coord_le_rho k 2]
  have hρ := FSChannel.rho_nonneg θ
  calc |∑ i, ((θ i : ℤ) : ℝ) * ((k i : ℤ) : ℝ)| ≤ FSChannel.rho θ * ∑ i, |((k i : ℤ) : ℝ)| := h
    _ ≤ FSChannel.rho θ * (3 * FSChannel.rho k) := mul_le_mul_of_nonneg_left h2 hρ
    _ = 3 * (FSChannel.rho θ * FSChannel.rho k) := by ring

omit [Fintype ν] in
/-- **The algebra of the alignment**: for either register `t` of the pair,
`|c^{cm}_j(k, θ)| ≤ (g²/m_t) (3|θ||k_t| + |θ·c_j(k)|)`. -/
lemma abs_comC_align (g : ℝ) (pr : FiniteElectronPair eta) (k : Cf eta) (θ : Lattice3) {t : Fin eta}
    (ht : t = pr.1.1 ∨ t = pr.1.2) :
    |comC sys p₀ g (.inr pr) k θ| ≤ g ^ 2 / sys.mass t *
      (3 * (FSChannel.rho θ * FSChannel.rho (k t)) +
        |∑ i, ((θ i : ℤ) : ℝ) * cCh sys (.inr pr) k i|) := by
  have ha := sys.mass_pos pr.1.1
  have hb := sys.mass_pos pr.1.2
  set X := g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
    ∑ i, ((θ i : ℤ) : ℝ) * (((k pr.1.1 i : ℤ) : ℝ) + ((k pr.1.2 i : ℤ) : ℝ)) with hX
  have hcomC : |comC sys p₀ g (.inr pr) k θ| ≤ |X| := by
    simp only [comC]
    split_ifs
    · exact le_rfl
    · rw [abs_neg]
    · rw [abs_zero]; exact abs_nonneg _
  refine hcomC.trans ?_
  have hd := abs_dot_le_three θ (k t)
  have hc0 : 0 ≤ |∑ i, ((θ i : ℤ) : ℝ) * cCh sys (.inr pr) k i| := abs_nonneg _
  have hmt := sys.mass_pos t
  have hg : 0 ≤ g ^ 2 / sys.mass t := by positivity
  rcases ht with rfl | rfl
  · -- `t = a`: `X = (g²/m_a)(θ·k_a - θ·c)`
    have e : X = g ^ 2 / sys.mass pr.1.1 * (∑ i, ((θ i : ℤ) : ℝ) * ((k pr.1.1 i : ℤ) : ℝ) -
        ∑ i, ((θ i : ℤ) : ℝ) * cCh sys (.inr pr) k i) := by
      simp only [hX, cCh, muCh, Fin.sum_univ_three]
      field_simp
      ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ g ^ 2 / sys.mass pr.1.1)]
    apply mul_le_mul_of_nonneg_left _ hg
    calc |∑ i, ((θ i : ℤ) : ℝ) * ((k pr.1.1 i : ℤ) : ℝ) - ∑ i, ((θ i : ℤ) : ℝ) * cCh sys (.inr pr) k i| ≤
        |∑ i, ((θ i : ℤ) : ℝ) * ((k pr.1.1 i : ℤ) : ℝ)| + |∑ i, ((θ i : ℤ) : ℝ) * cCh sys (.inr pr) k i| :=
          abs_sub _ _
      _ ≤ _ := by linarith
  · -- `t = b`: `X = (g²/m_b)(θ·k_b + θ·c)`
    have e : X = g ^ 2 / sys.mass pr.1.2 * (∑ i, ((θ i : ℤ) : ℝ) * ((k pr.1.2 i : ℤ) : ℝ) +
        ∑ i, ((θ i : ℤ) : ℝ) * cCh sys (.inr pr) k i) := by
      simp only [hX, cCh, muCh, Fin.sum_univ_three]
      field_simp
      ring
    rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ g ^ 2 / sys.mass pr.1.2)]
    apply mul_le_mul_of_nonneg_left _ hg
    calc |∑ i, ((θ i : ℤ) : ℝ) * ((k pr.1.2 i : ℤ) : ℝ) + ∑ i, ((θ i : ℤ) : ℝ) * cCh sys (.inr pr) k i| ≤
        |∑ i, ((θ i : ℤ) : ℝ) * ((k pr.1.2 i : ℤ) : ℝ)| + |∑ i, ((θ i : ℤ) : ℝ) * cCh sys (.inr pr) k i| :=
          abs_add_le _ _
      _ ≤ _ := by linarith

/-- **The alignment bound of the com dressing**: for a register `t` moved by `j`,
`|y_j(f,d)| ≤ c_j (1 + 3|d_t|)/|θ|² + (c_j/2)/|θ|`. -/
theorem norm_yj_align_le (hL : 0 < L) {j : Ch eta} {t : Fin eta} (ht : t ∈ moved j) (f d : Cfg eta N) :
    ‖yj sys L p₀ N j f d‖ ≤
      chC sys L j * (1 + 3 * FSChannel.rho (cidx N d t)) / FSLattice.lsq (chT N j f d) +
        chC sys L j / 2 / FSChannel.rho (chT N j f d) := by
  classical
  have hc := chC_nonneg sys hL j
  have hdt := FSChannel.rho_nonneg (cidx N d t)
  have hR : 0 ≤ chC sys L j * (1 + 3 * FSChannel.rho (cidx N d t)) / FSLattice.lsq (chT N j f d) +
      chC sys L j / 2 / FSChannel.rho (chT N j f d) := by
    have := FSLattice.lsq_nonneg (chT N j f d)
    have := FSChannel.rho_nonneg (chT N j f d)
    positivity
  unfold yj ycKc
  split_ifs with hj
  swap
  · rw [norm_zero]; exact hR
  by_cases hne : f = d
  · subst hne; unfold ycK FSKernel.divK; rw [if_pos rfl, norm_zero]; exact hR
  unfold ycK FSKernel.divK
  split_ifs with hE
  · rw [norm_zero]; exact hR
  dsimp only
  unfold gcmGap
  split_ifs with hg
  swap
  · rw [mul_zero, zero_div, norm_zero]; exact hR
  rw [gcmK_eq hL hj]
  rw [norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul, norm_mul, norm_mul, norm_neg,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
  set θ := chT N j f d with hθ
  set D := cidx N d with hD
  have hl1 : 1 ≤ FSLattice.lsq θ := one_le_lsq_chT hj hne
  have hl : 0 < FSLattice.lsq θ := by linarith
  have hr : 0 < FSChannel.rho θ := rho_pos_of_lsq_pos hl
  have hlr : FSLattice.lsq θ = FSChannel.rho θ ^ 2 := lsq_eq_rho_sq θ
  have hw := norm_wNK_chan_le (sys := sys) hL hj hne
  have hfl := gapC_onCh hg hj
  have hω := Asym_hop (sys := sys) (L := L) hj
  have hg0 := gF_pos hL
  have hμ := muCh_pos sys j
  set Om := |Asym sys L N f - Asym sys L N d| with hOm
  have hOm0 : 0 < gF L ^ 2 * FSChannel.rho θ / muCh sys j := by positivity
  have hOmp : 0 < Om := lt_of_lt_of_le hOm0 hfl
  -- the com symbol on the pair
  cases j with
  | inl a =>
    have h0 : comC sys p₀ (gF L) (.inl a) D θ = 0 := rfl
    rw [h0, abs_zero, mul_zero, zero_div]; exact hR
  | inr pr =>
    have ht' : t = pr.1.1 ∨ t = pr.1.2 := by simpa [moved] using ht
    have hal := abs_comC_align (sys := sys) (p₀ := p₀) (gF L) pr D θ ht'
    have hmt := sys.mass_pos t
    have hμt : muCh sys (.inr pr) ≤ sys.mass t := by
      have h1 := sys.mass_pos pr.1.1
      have h2 := sys.mass_pos pr.1.2
      simp only [muCh]
      rw [div_le_iff₀ (by linarith)]
      rcases ht' with rfl | rfl <;> nlinarith
    -- `θ·c = (μ/g²) ω - |θ|²/2`
    have hS : |∑ i, ((θ i : ℤ) : ℝ) * cCh sys (.inr pr) D i| ≤
        muCh sys (.inr pr) / gF L ^ 2 * Om + FSLattice.lsq θ / 2 := by
      have e : ∑ i, ((θ i : ℤ) : ℝ) * cCh sys (.inr pr) D i =
          muCh sys (.inr pr) / gF L ^ 2 * (Asym sys L N f - Asym sys L N d) - FSLattice.lsq θ / 2 := by
        rw [hω]
        unfold FSLattice.slabF
        field_simp
        ring
      rw [e]
      calc |muCh sys (.inr pr) / gF L ^ 2 * (Asym sys L N f - Asym sys L N d) - FSLattice.lsq θ / 2| ≤
          |muCh sys (.inr pr) / gF L ^ 2 * (Asym sys L N f - Asym sys L N d)| + |FSLattice.lsq θ / 2| :=
            abs_sub _ _
        _ = muCh sys (.inr pr) / gF L ^ 2 * Om + FSLattice.lsq θ / 2 := by
            rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ muCh sys (.inr pr) / gF L ^ 2),
              abs_of_nonneg (by linarith : 0 ≤ FSLattice.lsq θ / 2)]
    -- the bracket
    have hB : |comC sys p₀ (gF L) (.inr pr) D θ| / Om ≤ 1 + 3 * FSChannel.rho (D t) + FSChannel.rho θ / 2 := by
      rw [div_le_iff₀ hOmp]
      have h1 : |comC sys p₀ (gF L) (.inr pr) D θ| ≤ gF L ^ 2 / sys.mass t *
          (3 * (FSChannel.rho θ * FSChannel.rho (D t)) + (muCh sys (.inr pr) / gF L ^ 2 * Om +
            FSLattice.lsq θ / 2)) := by
        refine hal.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        linarith
      -- `g² ρ ≤ μ Om`
      have h2 : gF L ^ 2 * FSChannel.rho θ ≤ muCh sys (.inr pr) * Om := by
        rw [div_le_iff₀ hμ] at hfl; linarith
      have h3 : gF L ^ 2 / sys.mass t * (3 * (FSChannel.rho θ * FSChannel.rho (D t))) ≤
          3 * FSChannel.rho (D t) * Om := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hmt]
        have : gF L ^ 2 * FSChannel.rho θ * FSChannel.rho (D t) ≤ muCh sys (.inr pr) * Om * FSChannel.rho (D t) :=
          mul_le_mul_of_nonneg_right h2 hdt
        have : muCh sys (.inr pr) * Om * FSChannel.rho (D t) ≤ sys.mass t * Om * FSChannel.rho (D t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμt hOmp.le) hdt
        nlinarith
      have h4 : gF L ^ 2 / sys.mass t * (muCh sys (.inr pr) / gF L ^ 2 * Om) ≤ Om := by
        have e : gF L ^ 2 / sys.mass t * (muCh sys (.inr pr) / gF L ^ 2 * Om) =
            muCh sys (.inr pr) / sys.mass t * Om := by field_simp
        rw [e]
        have : muCh sys (.inr pr) / sys.mass t ≤ 1 := by rw [div_le_one hmt]; exact hμt
        nlinarith
      have h5 : gF L ^ 2 / sys.mass t * (FSLattice.lsq θ / 2) ≤ FSChannel.rho θ / 2 * Om := by
        rw [hlr]
        have e : gF L ^ 2 / sys.mass t * (FSChannel.rho θ ^ 2 / 2) =
            FSChannel.rho θ / 2 * (gF L ^ 2 * FSChannel.rho θ / sys.mass t) := by
          field_simp
        rw [e]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ hmt]
        have : muCh sys (.inr pr) * Om ≤ sys.mass t * Om :=
          mul_le_mul_of_nonneg_right hμt hOmp.le
        nlinarith
      calc |comC sys p₀ (gF L) (.inr pr) D θ| ≤ gF L ^ 2 / sys.mass t *
          (3 * (FSChannel.rho θ * FSChannel.rho (D t)) + (muCh sys (.inr pr) / gF L ^ 2 * Om +
            FSLattice.lsq θ / 2)) := h1
        _ = gF L ^ 2 / sys.mass t * (3 * (FSChannel.rho θ * FSChannel.rho (D t))) +
            gF L ^ 2 / sys.mass t * (muCh sys (.inr pr) / gF L ^ 2 * Om) +
            gF L ^ 2 / sys.mass t * (FSLattice.lsq θ / 2) := by ring
        _ ≤ 3 * FSChannel.rho (D t) * Om + Om + FSChannel.rho θ / 2 * Om := by linarith
        _ = (1 + 3 * FSChannel.rho (D t) + FSChannel.rho θ / 2) * Om := by ring
    have hwn := norm_nonneg (wNK sys L N f d)
    calc ‖wNK sys L N f d‖ * |comC sys p₀ (gF L) (.inr pr) D θ| / Om =
        ‖wNK sys L N f d‖ * (|comC sys p₀ (gF L) (.inr pr) D θ| / Om) := by ring
      _ ≤ chC sys L (.inr pr) / FSLattice.lsq θ * (1 + 3 * FSChannel.rho (D t) + FSChannel.rho θ / 2) :=
          mul_le_mul hw hB (div_nonneg (abs_nonneg _) hOmp.le) (by positivity)
      _ = chC sys L (.inr pr) * (1 + 3 * FSChannel.rho (D t)) / FSLattice.lsq θ +
            chC sys L (.inr pr) / 2 / FSChannel.rho θ := by
          rw [hlr]; field_simp

end Align

/-! ## Hardy twice on `ℤ³` -/

section HardyTwice

omit [Fintype ν] in
lemma lsq_add_le_two (a b : Lattice3) :
    FSLattice.lsq (a + b) ≤ 2 * FSLattice.lsq a + 2 * FSLattice.lsq b := by
  have h := FSChannel.rho_add_le a b
  have h0 := FSChannel.rho_nonneg (a + b)
  rw [lsq_eq_rho_sq (a + b), lsq_eq_rho_sq a, lsq_eq_rho_sq b]
  have := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (FSChannel.rho a - FSChannel.rho b)]

omit [Fintype ν] in
/-- The translated box `x + B_m` has `(2m+1)³` points, each with `|z - x|² ≤ 3m²`. -/
lemma lsq_sub_le_box {x z : Lattice3} {m : ℕ} (h : ∀ i, |((z i - x i : ℤ) : ℝ)| ≤ (m : ℝ)) :
    FSLattice.lsq (x - z) ≤ 3 * (m : ℝ) ^ 2 := by
  have e : ∀ i, (((x - z) i : ℤ) : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
    intro i
    have hi := h i
    have : (((x - z) i : ℤ) : ℝ) = -((z i - x i : ℤ) : ℝ) := by simp
    rw [this, neg_sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hi 2
  unfold FSLattice.lsq
  linarith [e 0, e 1, e 2]

omit [Fintype ν] in
open Classical in
/-- **`1/|θ|` below a convolution of two Coulomb kernels**: for `x ≠ y` and `Z` containing the box of
radius `m = ⌊|x - y|/4⌋ + 1` around `x`, `1/|x - y| ≤ 32 Σ_{z ∈ Z} 1/(|x - z|² |z - y|²)`. -/
theorem inv_rho_le_conv (Z : Finset Lattice3) {x y : Lattice3} (hxy : x ≠ y)
    (hZ : ∀ z : Lattice3, (∀ i, |((z i - x i : ℤ) : ℝ)| ≤
      ((⌊FSChannel.rho (x - y) / 4⌋₊ + 1 : ℕ) : ℝ)) → z ∈ Z) :
    1 / FSChannel.rho (x - y) ≤
      32 * ∑ z ∈ Z, 1 / (FSLattice.lsq (x - z) * FSLattice.lsq (z - y)) := by
  classical
  set D := FSChannel.rho (x - y) with hD
  set m : ℕ := ⌊D / 4⌋₊ + 1 with hm
  have hl1 : 1 ≤ FSLattice.lsq (x - y) := one_le_latticeNormSq (sub_ne_zero.mpr hxy)
  have hD1 : 1 ≤ D := by
    rw [hD]; unfold FSChannel.rho; rw [Real.le_sqrt (by norm_num) (FSLattice.lsq_nonneg _)]; simpa using hl1
  have hD0 : 0 < D := by linarith
  have hlD : FSLattice.lsq (x - y) = D ^ 2 := lsq_eq_rho_sq (x - y)
  have hm1 : (1 : ℝ) ≤ m := by simp [hm]
  have hmD : (m : ℝ) ≤ D / 4 + 1 := by
    simp only [hm]; push_cast
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ D / 4)
    linarith
  have hDm : D < 4 * m := by
    simp only [hm]; push_cast
    have := Nat.lt_floor_add_one (D / 4)
    linarith
  -- the translated box
  set B : Finset Lattice3 := (FSLattice.box m).image (fun w => x + w) with hB
  have hBcard : B.card = (2 * m + 1) ^ 3 := by
    rw [hB, Finset.card_image_of_injective _ (add_right_injective x), FSLattice.card_box]
  have hBmem : ∀ z ∈ B, ∀ i, |((z i - x i : ℤ) : ℝ)| ≤ (m : ℝ) := by
    intro z hz i
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have := (FSLattice.mem_box.mp hw) i
    have e : (((x + w) i - x i : ℤ) : ℝ) = ((w i : ℤ) : ℝ) := by simp
    rw [e, abs_le]
    constructor
    · have : (-(m : ℤ) : ℝ) ≤ ((w i : ℤ) : ℝ) := by exact_mod_cast this.1
      push_cast at this; linarith
    · exact_mod_cast this.2
  have hBZ : B ⊆ Z := fun z hz => hZ z (hBmem z hz)
  -- the good terms
  have hB'card : (2 * m + 1) ^ 3 - 2 ≤ ((B.erase x).erase y).card := by
    have h1 := Finset.pred_card_le_card_erase (s := B.erase x) (a := y)
    have h2 := Finset.pred_card_le_card_erase (s := B) (a := x)
    rw [hBcard] at h2
    generalize (2 * m + 1) ^ 3 = K at h2 ⊢
    generalize ((B.erase x).erase y).card = c2 at h1 ⊢
    generalize (B.erase x).card = c1 at h1 h2
    omega
  set B' := (B.erase x).erase y with hB'
  set lo : ℝ := 1 / (3 * (m : ℝ) ^ 2 * (6 * (m : ℝ) ^ 2 + 2 * D ^ 2)) with hlo
  have hterm : ∀ z ∈ B', lo ≤ 1 / (FSLattice.lsq (x - z) * FSLattice.lsq (z - y)) := by
    intro z hz
    have hzy : z ≠ y := Finset.ne_of_mem_erase hz
    have hzB : z ∈ B.erase x := Finset.mem_of_mem_erase hz
    have hzx : z ≠ x := Finset.ne_of_mem_erase hzB
    have hzB' : z ∈ B := Finset.mem_of_mem_erase hzB
    have h1 := lsq_sub_le_box (hBmem z hzB')
    have h1' : 1 ≤ FSLattice.lsq (x - z) := one_le_latticeNormSq (sub_ne_zero.mpr hzx.symm)
    have h2' : 1 ≤ FSLattice.lsq (z - y) := one_le_latticeNormSq (sub_ne_zero.mpr hzy)
    have h2 : FSLattice.lsq (z - y) ≤ 6 * (m : ℝ) ^ 2 + 2 * D ^ 2 := by
      have e : z - y = -(x - z) + (x - y) := by abel
      rw [e]
      refine (lsq_add_le_two _ _).trans ?_
      rw [lsq_neg, hlD]
      linarith
    rw [hlo]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul h1 h2 (by linarith) (by positivity)
  have hsum : ((B'.card : ℕ) : ℝ) * lo ≤
      ∑ z ∈ Z, 1 / (FSLattice.lsq (x - z) * FSLattice.lsq (z - y)) := by
    have hnn : ∀ z, 0 ≤ 1 / (FSLattice.lsq (x - z) * FSLattice.lsq (z - y)) := fun z =>
      div_nonneg zero_le_one (mul_nonneg (FSLattice.lsq_nonneg _) (FSLattice.lsq_nonneg _))
    calc ((B'.card : ℕ) : ℝ) * lo = ∑ _z ∈ B', lo := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ B', 1 / (FSLattice.lsq (x - z) * FSLattice.lsq (z - y)) := Finset.sum_le_sum hterm
      _ ≤ ∑ z ∈ Z, 1 / (FSLattice.lsq (x - z) * FSLattice.lsq (z - y)) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            ((Finset.erase_subset _ _).trans ((Finset.erase_subset _ _).trans hBZ))
            fun z _ _ => hnn z
  -- the count
  have hcnt : 8 * (m : ℝ) ^ 3 ≤ ((B'.card : ℕ) : ℝ) := by
    have h3 : 8 * m ^ 3 ≤ (2 * m + 1) ^ 3 - 2 := by
      have : 1 ≤ m := by simp [hm]
      have e : (2 * m + 1) ^ 3 = 8 * m ^ 3 + 12 * m ^ 2 + 6 * m + 1 := by ring
      rw [e]; omega
    exact_mod_cast h3.trans hB'card
  have hlo0 : 0 < lo := by rw [hlo]; positivity
  have key : 1 / D ≤ 32 * (8 * (m : ℝ) ^ 3 * lo) := by
    have hD2 : D ^ 2 ≤ 16 * (m : ℝ) ^ 2 := by nlinarith
    have hden : 3 * (m : ℝ) ^ 2 * (6 * (m : ℝ) ^ 2 + 2 * D ^ 2) ≤ 114 * (m : ℝ) ^ 4 := by nlinarith
    have hden0 : 0 < 3 * (m : ℝ) ^ 2 * (6 * (m : ℝ) ^ 2 + 2 * D ^ 2) := by positivity
    rw [hlo, mul_one_div, mul_div_assoc', div_le_div_iff₀ hD0 hden0, one_mul]
    have h114 : 114 * (m : ℝ) ≤ 256 * D := by nlinarith
    have hm0 : 0 ≤ (m : ℝ) ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h114 hm0]
  calc 1 / D ≤ 32 * (8 * (m : ℝ) ^ 3 * lo) := key
    _ ≤ 32 * (((B'.card : ℕ) : ℝ) * lo) := by gcongr
    _ ≤ 32 * ∑ z ∈ Z, 1 / (FSLattice.lsq (x - z) * FSLattice.lsq (z - y)) := by gcongr

omit [Fintype ν] in
open Classical in
/-- **Hardy twice on `ℤ³`**: for `u ≥ 0` on a finite set `X`, outputs on `X'`, and `Z` containing the
boxes of `inv_rho_le_conv`,
`Σ_{x∈X'} (Σ_{y∈X} u_y/|x - y|)²/(1+|x|²) ≤ 32² H⁴ Σ_{y∈X} (1+|y|²) u_y²`. -/
theorem hardy_twice_Z3 {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (X X' Z : Finset Lattice3) (u : Lattice3 → ℝ) (hu : ∀ y, 0 ≤ u y)
    (hZ : ∀ x ∈ X', ∀ y ∈ X, x ≠ y → ∀ z : Lattice3, (∀ i, |((z i - x i : ℤ) : ℝ)| ≤
      ((⌊FSChannel.rho (x - y) / 4⌋₊ + 1 : ℕ) : ℝ)) → z ∈ Z) :
    ∑ x ∈ X', (∑ y ∈ X, u y / FSChannel.rho (x - y)) ^ 2 / (1 + FSLattice.lsq x) ≤
      32 ^ 2 * Hunit ^ 4 * ∑ y ∈ X, (1 + FSLattice.lsq y) * u y ^ 2 := by
  classical
  set W : Lattice3 → ℝ := fun z => ∑ y ∈ X, u y / FSLattice.lsq (z - y) with hW
  have hW0 : ∀ z, 0 ≤ W z := fun z => Finset.sum_nonneg fun y _ =>
    div_nonneg (hu y) (FSLattice.lsq_nonneg _)
  -- step 1: the pointwise domination
  have hstep1 : ∀ x ∈ X', ∑ y ∈ X, u y / FSChannel.rho (x - y) ≤
      32 * ∑ z ∈ Z, W z / FSLattice.lsq (x - z) := by
    intro x hx
    have hpt : ∀ y ∈ X, u y / FSChannel.rho (x - y) ≤
        32 * ∑ z ∈ Z, u y * (1 / (FSLattice.lsq (x - z) * FSLattice.lsq (z - y))) := by
      intro y hy
      by_cases hxy : x = y
      · rw [hxy, sub_self, show FSChannel.rho (0 : Lattice3) = 0 by
          unfold FSChannel.rho; rw [lsq_zero', Real.sqrt_zero], div_zero]
        exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun z _ => mul_nonneg (hu y)
          (div_nonneg zero_le_one (mul_nonneg (FSLattice.lsq_nonneg _) (FSLattice.lsq_nonneg _))))
      · have h := inv_rho_le_conv Z hxy (hZ x hx y hy hxy)
        rw [← Finset.mul_sum, div_eq_mul_one_div]
        calc u y * (1 / FSChannel.rho (x - y)) ≤
            u y * (32 * ∑ z ∈ Z, 1 / (FSLattice.lsq (x - z) * FSLattice.lsq (z - y))) :=
              mul_le_mul_of_nonneg_left h (hu y)
          _ = 32 * (u y * ∑ z ∈ Z, 1 / (FSLattice.lsq (x - z) * FSLattice.lsq (z - y))) := by ring
    refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [hW]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  -- step 2: the dual Hardy
  have hstep2 : ∑ x ∈ X', (∑ z ∈ Z, W z / FSLattice.lsq (x - z)) ^ 2 / (1 + FSLattice.lsq x) ≤
      Hunit ^ 2 * ∑ z ∈ Z, W z ^ 2 := by
    have h := hardy_classes_dual hH (Z ∪ X') (fun _ => ()) id (fun s _ t _ _ he => he)
      (fun z => if z ∈ Z then W z else 0)
    simp only [Finset.filter_true, id] at h
    have e1 : ∀ t, ∑ s ∈ Z ∪ X', (if s ∈ Z then W s else 0) / FSLattice.lsq (t - s) =
        ∑ z ∈ Z, W z / FSLattice.lsq (t - z) := by
      intro t
      rw [← Finset.sum_subset (Finset.subset_union_left (s₂ := X'))]
      · refine Finset.sum_congr rfl fun z hz => ?_
        rw [if_pos hz]
      · intro z _ hz
        rw [if_neg hz, zero_div]
    have e2 : ∑ s ∈ Z ∪ X', (if s ∈ Z then W s else 0) ^ 2 = ∑ z ∈ Z, W z ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_union_left (s₂ := X'))]
      · refine Finset.sum_congr rfl fun z hz => ?_
        rw [if_pos hz]
      · intro z _ hz
        rw [if_neg hz]; ring
    simp only [e1, e2] at h
    refine le_trans ?_ h
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
    intro x _ _
    exact div_nonneg (sq_nonneg _) (by have := FSLattice.lsq_nonneg x; linarith)
  -- step 3: the Hardy
  have hstep3 : ∑ z ∈ Z, W z ^ 2 ≤ Hunit ^ 2 * ∑ y ∈ X, (1 + FSLattice.lsq y) * u y ^ 2 := by
    have h := hardy_classes hH (Z ∪ X) (fun _ => ()) id (fun s _ t _ _ he => he)
      (fun y => if y ∈ X then u y else 0)
    simp only [Finset.filter_true, id] at h
    have e1 : ∀ t, ∑ s ∈ Z ∪ X, (if s ∈ X then u s else 0) / FSLattice.lsq (t - s) = W t := by
      intro t
      simp only [hW]
      rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := Z))]
      · refine Finset.sum_congr rfl fun y hy => ?_
        rw [if_pos hy]
      · intro y _ hy
        rw [if_neg hy, zero_div]
    have e2 : ∑ s ∈ Z ∪ X, (1 + FSLattice.lsq s) * (if s ∈ X then u s else 0) ^ 2 =
        ∑ y ∈ X, (1 + FSLattice.lsq y) * u y ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := Z))]
      · refine Finset.sum_congr rfl fun y hy => ?_
        rw [if_pos hy]
      · intro y _ hy
        rw [if_neg hy]; ring
    simp only [e1, e2] at h
    refine le_trans ?_ h
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun z _ _ => sq_nonneg _
  -- assemble
  calc ∑ x ∈ X', (∑ y ∈ X, u y / FSChannel.rho (x - y)) ^ 2 / (1 + FSLattice.lsq x) ≤
      ∑ x ∈ X', (32 * ∑ z ∈ Z, W z / FSLattice.lsq (x - z)) ^ 2 / (1 + FSLattice.lsq x) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have h0 : 0 ≤ ∑ y ∈ X, u y / FSChannel.rho (x - y) := Finset.sum_nonneg fun y _ =>
          div_nonneg (hu y) (FSChannel.rho_nonneg _)
        have hd : 0 < 1 + FSLattice.lsq x := by have := FSLattice.lsq_nonneg x; linarith
        exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 (hstep1 x hx) 2) hd.le
    _ = 32 ^ 2 * ∑ x ∈ X', (∑ z ∈ Z, W z / FSLattice.lsq (x - z)) ^ 2 / (1 + FSLattice.lsq x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ 32 ^ 2 * (Hunit ^ 2 * (Hunit ^ 2 * ∑ y ∈ X, (1 + FSLattice.lsq y) * u y ^ 2)) := by
        gcongr
        exact hstep2.trans (mul_le_mul_of_nonneg_left hstep3 (sq_nonneg _))
    _ = 32 ^ 2 * Hunit ^ 4 * ∑ y ∈ X, (1 + FSLattice.lsq y) * u y ^ 2 := by ring

end HardyTwice

/-! ## Hardy twice on lines -/

section LineTwice

variable {N : ℕ}

omit [Fintype ν] in
lemma rho_regSum_le_4N {A : Finset (Fin eta)} (hA : A.card ≤ 2) (q : Cfg eta N) :
    FSChannel.rho (regSum A (cidx N q)) ≤ 4 * N := by
  have h := lsq_regSum_box A hA q
  push_cast at h
  unfold FSChannel.rho
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (N : ℝ)]

omit [Fintype ν] in
lemma mem_box_of_near {N : ℕ} {x' y' z : Lattice3} (hx : FSChannel.rho x' ≤ 4 * N)
    (hy : FSChannel.rho y' ≤ 4 * N)
    (hz : ∀ i, |((z i - x' i : ℤ) : ℝ)| ≤ ((⌊FSChannel.rho (x' - y') / 4⌋₊ + 1 : ℕ) : ℝ)) :
    z ∈ FSLattice.box (6 * N + 1) := by
  rw [FSLattice.mem_box]
  intro i
  have h1 := hz i
  have h2 : FSChannel.rho (x' - y') ≤ 8 * N := by
    have := FSChannel.rho_add_le x' (-y')
    rw [rho_neg', ← sub_eq_add_neg] at this
    linarith
  have h3 : (((⌊FSChannel.rho (x' - y') / 4⌋₊ + 1 : ℕ) : ℝ)) ≤ 2 * N + 1 := by
    push_cast
    have := Nat.floor_le (by have := FSChannel.rho_nonneg (x' - y'); positivity :
      (0 : ℝ) ≤ FSChannel.rho (x' - y') / 4)
    linarith
  have h4 : |((x' i : ℤ) : ℝ)| ≤ 4 * N := (abs_coord_le_rho x' i).trans hx
  have h5 : |((z i : ℤ) : ℝ)| ≤ 6 * N + 1 := by
    have e : ((z i : ℤ) : ℝ) = ((z i - x' i : ℤ) : ℝ) + ((x' i : ℤ) : ℝ) := by push_cast; ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith)
  rw [abs_le] at h5
  constructor
  · have : ((-(6 * N + 1 : ℕ) : ℤ) : ℝ) ≤ ((z i : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : ((z i : ℤ) : ℝ) ≤ (((6 * N + 1 : ℕ) : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

omit [Fintype ν] in
open Classical in
/-- **Hardy twice on the `j`-lines**: for a coordinate `ζ` of `j` and `x ≥ 0`,
`Σ_q (Σ_{p ~_j q} x_p/|θ|)²/(1 + |ζ_q|²) ≤ 32² H⁴ Σ_p (1 + |ζ_p|²) x_p²`. -/
theorem line_hardy_twice {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    {j : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j A ε) (x : Cfg eta N → ℝ)
    (hx : ∀ p, 0 ≤ x p) :
    ∑ q, (∑ p, if OnCh j (cidx N q) (cidx N p) then x p / FSChannel.rho (chT N j q p) else 0) ^ 2 /
        (1 + FSLattice.lsq (regSum A (cidx N q))) ≤
      32 ^ 2 * Hunit ^ 4 * ∑ p, (1 + FSLattice.lsq (regSum A (cidx N p))) * x p ^ 2 := by
  classical
  set ζ : Cfg eta N → Lattice3 := fun q => regSum A (cidx N q) with hζ
  rw [sum_by_lines j, sum_by_lines j (fun p => (1 + FSLattice.lsq (regSum A (cidx N p))) * x p ^ 2),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  set S := Finset.univ.filter (fun p : Cfg eta N => lab N j p = t) with hS
  have hinj : Set.InjOn ζ ↑S := by
    intro q hq p hp he
    have hq' := (Finset.mem_filter.mp hq).2
    have hp' := (Finset.mem_filter.mp hp).2
    exact coord_injOn hA (lab_eq_iff.mp (hq'.trans hp'.symm)) he
  set X := S.image ζ with hX
  set u : Lattice3 → ℝ := fun a => ∑ p ∈ S, if ζ p = a then x p else 0 with hu
  have hu0 : ∀ a, 0 ≤ u a := fun a => Finset.sum_nonneg fun p _ => by
    split_ifs
    · exact hx p
    · exact le_rfl
  have hu_val : ∀ p ∈ S, u (ζ p) = x p := by
    intro p hp
    simp only [hu]
    rw [Finset.sum_eq_single p]
    · rw [if_pos rfl]
    · intro p' hp' hne
      rw [if_neg (fun h => hne (hinj hp' hp h))]
    · intro h; exact absurd hp h
  -- the inner sums on the line
  have hinner : ∀ q ∈ S, (∑ p, if OnCh j (cidx N q) (cidx N p) then
      x p / FSChannel.rho (chT N j q p) else 0) = ∑ a ∈ X, u a / FSChannel.rho (ζ q - a) := by
    intro q hq
    rw [hX, Finset.sum_image hinj]
    have hq' := (Finset.mem_filter.mp hq).2
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => lab N j p = t)]
    have h0 : ∑ p ∈ Finset.univ.filter (fun p => ¬ lab N j p = t), (if OnCh j (cidx N q) (cidx N p) then
        x p / FSChannel.rho (chT N j q p) else 0) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp' := (Finset.mem_filter.mp hp).2
      rw [if_neg (fun h => hp' ((lab_eq_iff.mpr h).symm.trans hq'))]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := (Finset.mem_filter.mp hp).2
    have hqp : OnCh j (cidx N q) (cidx N p) := lab_eq_iff.mp (hq'.trans hp'.symm)
    rw [if_pos hqp, hu_val p hp]
    congr 1
    unfold FSChannel.rho
    rw [coord_lsq hA hqp]
  have hZ : ∀ x' ∈ X, ∀ y' ∈ X, x' ≠ y' → ∀ z : Lattice3, (∀ i, |((z i - x' i : ℤ) : ℝ)| ≤
      ((⌊FSChannel.rho (x' - y') / 4⌋₊ + 1 : ℕ) : ℝ)) → z ∈ FSLattice.box (6 * N + 1) := by
    intro x' hx' y' hy' _ z hz
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx'
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hy'
    exact mem_box_of_near (rho_regSum_le_4N hA.card q) (rho_regSum_le_4N hA.card p) hz
  have h := hardy_twice_Z3 hH X X (FSLattice.box (6 * N + 1)) u hu0 hZ
  calc ∑ q ∈ S, (∑ p, if OnCh j (cidx N q) (cidx N p) then
        x p / FSChannel.rho (chT N j q p) else 0) ^ 2 / (1 + FSLattice.lsq (regSum A (cidx N q))) =
      ∑ q ∈ S, (∑ a ∈ X, u a / FSChannel.rho (ζ q - a)) ^ 2 / (1 + FSLattice.lsq (ζ q)) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [hinner q hq]
    _ = ∑ b ∈ X, (∑ a ∈ X, u a / FSChannel.rho (b - a)) ^ 2 / (1 + FSLattice.lsq b) := by
        rw [hX, Finset.sum_image hinj]
    _ ≤ 32 ^ 2 * Hunit ^ 4 * ∑ a ∈ X, (1 + FSLattice.lsq a) * u a ^ 2 := h
    _ = 32 ^ 2 * Hunit ^ 4 * ∑ p ∈ S, (1 + FSLattice.lsq (regSum A (cidx N p))) * x p ^ 2 := by
        rw [hX, Finset.sum_image hinj]
        congr 1
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [hu_val p hp]

end LineTwice

end FSFlux
