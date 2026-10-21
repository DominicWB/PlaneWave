import PlaneWave.FluxBox.FarColdGeometry

/-!
# Flux route, stage 3, part 26: the far–cold dressing and its three shapes

`ỹ = ytK κ` is `-κ/(E(f) - E(b))` on `F × C`; with the gap `E(f) - E(b) ≥ (3/4) E(f)`,
`‖kop ỹ v‖² ≤ Σ_f ((4/3) ω_F(f))² (Σ_{b ∈ C} |κ(f,b)| |v_b|)²`, `ω_F(f) = 1{f ∈ F}/E(f)`
(`norm_sq_kop_ytK_le`). The two-hop words are bounded through three shapes, for `x ≥ 0`:

* **L1-W** (first hop on the `j₁`-lines with `K₁(d,b) ≤ κ₁(d)`, second a Coulomb hop of `j₂`):
  `Σ_f ω_F² (Σ_d K₂ Σ_b K₁ x)² ≤ (2048 m²/g⁴) n⁻² c₂² H² A₁ L²_{j₁}(x)` (dual line Hardy on the
  `j₂`-lines, `ω_F² ≤ C n⁻² (1 + |ζ₂|²)⁻¹`, then `long_line_le`);
* **L1-Y** (second hop the com dressing `y_{j₂}`): `≤ (2048 m²/g⁴) n⁻² (C_{j₂} Λ_N)² A₁ L²_{j₁}(x)`
  (`ω_F² ≤ C n⁻² (n² + |Π₂|²)⁻¹`, the conserved weight, `sum_sq_yj_le`);
* **L2** (second hop long from the short ball: `ω_F K₂ ≤ κ₂(f)` on the `j₂`-lines):
  `≤ A₂ L²_{j₂}(K₁ x)`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Dress

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

variable (sys L N n) in
open Classical in
/-- The far energy weight `ω_F(f) = 1{f ∈ F}/E(f)`. -/
noncomputable def farW (f : Cfg eta N) : ℝ :=
  if InQ (n : ℝ) (cidx N f) then 0 else 1 / Asym sys L N f

omit [Fintype ν] in
lemma farW_nonneg (f : Cfg eta N) : 0 ≤ farW sys L N n f := by
  unfold farW
  split_ifs
  · exact le_rfl
  · exact div_nonneg zero_le_one (FSGalerkin.Asym_nonneg sys L N f)

omit [Fintype ν] in
/-- The far weight against the coordinates of a channel: `ω_F(f) ≤ (32 m/g²)/max(n², |ζ|²)`. -/
lemma farW_le_max (hL : 0 < L) (hn : 1 ≤ n) {A : Finset (Fin eta)} (hA : A.card ≤ 2)
    (f : Cfg eta N) :
    farW sys L N n f ≤ 32 * mmax sys / gF L ^ 2 /
      max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) := by
  unfold farW
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : 0 < max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  split_ifs with hf
  · positivity
  · have h1 := Asym_ge_far_max (sys := sys) hL hA hf
    calc 1 / Asym sys L N f ≤
        1 / (gF L ^ 2 / (32 * mmax sys) * max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f)))) :=
          one_div_le_one_div_of_le (by positivity) h1
      _ = 32 * mmax sys / gF L ^ 2 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) := by
          field_simp

omit [Fintype ν] in
/-- `ω_F² ≤ (2048 m²/g⁴)/(n² (1 + |ζ|²))`. -/
lemma farW_sq_le_coord (hL : 0 < L) (hn : 1 ≤ n) {A : Finset (Fin eta)} (hA : A.card ≤ 2)
    (f : Cfg eta N) :
    farW sys L N n f ^ 2 ≤ 2048 * mmax sys ^ 2 / gF L ^ 4 /
      ((n : ℝ) ^ 2 * (1 + FSLattice.lsq (regSum A (cidx N f)))) := by
  have h1 := farW_le_max (sys := sys) hL hn hA f
  have h0 := farW_nonneg (sys := sys) (L := L) (n := n) f
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set l := FSLattice.lsq (regSum A (cidx N f))
  have hl := FSLattice.lsq_nonneg (regSum A (cidx N f))
  set M := max ((n : ℝ) ^ 2) l
  have hM1 : (n : ℝ) ^ 2 ≤ M := le_max_left _ _
  have hM2 : l ≤ M := le_max_right _ _
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hM0 : 0 < M := by linarith
  have h2 : farW sys L N n f ^ 2 ≤ (32 * mmax sys / gF L ^ 2 / M) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : (n : ℝ) ^ 2 * (1 + l) ≤ 2 * M ^ 2 := by nlinarith
  calc farW sys L N n f ^ 2 ≤ (32 * mmax sys / gF L ^ 2 / M) ^ 2 := h2
    _ = 1024 * mmax sys ^ 2 / gF L ^ 4 / M ^ 2 := by field_simp; ring
    _ ≤ 2048 * mmax sys ^ 2 / gF L ^ 4 / ((n : ℝ) ^ 2 * (1 + l)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : 0 ≤ mmax sys ^ 2 / gF L ^ 4 := by positivity
        have e1 : 1024 * mmax sys ^ 2 / gF L ^ 4 * ((n : ℝ) ^ 2 * (1 + l)) =
            512 * (mmax sys ^ 2 / gF L ^ 4) * (2 * ((n : ℝ) ^ 2 * (1 + l))) := by ring
        have e2 : 2048 * mmax sys ^ 2 / gF L ^ 4 * M ^ 2 =
            512 * (mmax sys ^ 2 / gF L ^ 4) * (4 * M ^ 2) := by ring
        rw [e1, e2]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

omit [Fintype ν] in
/-- `ω_F² ≤ (2048 m²/g⁴)/(n² (n² + |Π_j|²))`. -/
lemma farW_sq_le_pi (hL : 0 < L) (hn : 1 ≤ n) (j : Ch eta) (f : Cfg eta N) :
    farW sys L N n f ^ 2 ≤ 2048 * mmax sys ^ 2 / gF L ^ 4 /
      ((n : ℝ) ^ 2 * ((n : ℝ) ^ 2 + piC j (cidx N f) ^ 2)) := by
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := piC_nonneg j (cidx N f)
  unfold farW
  split_ifs with hf
  · rw [sq, mul_zero]; positivity
  · have h1 := Asym_ge_far (sys := sys) hL hf
    have h2 := Asym_ge_piC (sys := sys) hL j f
    set A := Asym sys L N f
    set π := piC j (cidx N f)
    have hA : gF L ^ 2 / (64 * mmax sys) * ((n : ℝ) ^ 2 + π ^ 2) ≤ A := by
      have e1 : gF L ^ 2 * (n : ℝ) ^ 2 / (32 * mmax sys) = 2 * (gF L ^ 2 / (64 * mmax sys)) * (n : ℝ) ^ 2 := by
        field_simp; ring
      have e2 : gF L ^ 2 / (4 * mmax sys) * π ^ 2 = 16 * (gF L ^ 2 / (64 * mmax sys)) * π ^ 2 := by
        field_simp; ring
      have hc : 0 ≤ gF L ^ 2 / (64 * mmax sys) := by positivity
      nlinarith [sq_nonneg π]
    have hA' : gF L ^ 2 / (32 * mmax sys) * (n : ℝ) ^ 2 ≤ A := by
      have e1 : gF L ^ 2 * (n : ℝ) ^ 2 / (32 * mmax sys) = gF L ^ 2 / (32 * mmax sys) * (n : ℝ) ^ 2 := by
        ring
      linarith
    have hApos : 0 < A := lt_of_lt_of_le (by positivity) hA'
    have hprod : gF L ^ 2 / (32 * mmax sys) * (n : ℝ) ^ 2 *
        (gF L ^ 2 / (64 * mmax sys) * ((n : ℝ) ^ 2 + π ^ 2)) ≤ A * A :=
      mul_le_mul hA' hA (by positivity) hApos.le
    have key : (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 + π ^ 2) ≤ 2048 * mmax sys ^ 2 / gF L ^ 4 * (A * A) := by
      have h3 := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 2048 * mmax sys ^ 2 / gF L ^ 4)
      have e : (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 + π ^ 2) = 2048 * mmax sys ^ 2 / gF L ^ 4 *
          (gF L ^ 2 / (32 * mmax sys) * (n : ℝ) ^ 2 *
            (gF L ^ 2 / (64 * mmax sys) * ((n : ℝ) ^ 2 + π ^ 2))) := by
        field_simp; ring
      rw [e]
      exact h3
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul, sq A]
    exact key

omit [Fintype ν] in
open Classical in
/-- **The far–cold dressing of a kernel**:
`‖kop (ytK κ) v‖² ≤ Σ_f ((4/3) ω_F(f))² (Σ_{b ∈ C} |κ(f,b)| |v_b|)²`. -/
theorem norm_sq_kop_ytK_le (hL : 0 < L) (hn : 1 ≤ n) (κ : Cfg eta N → Cfg eta N → ℂ)
    (v : En eta N) :
    ‖FSKernel.kop (ytK sys L N n κ) v‖ ^ 2 ≤
      ∑ f, (4 / 3 * farW sys L N n f) ^ 2 *
        (∑ b, if InC (n : ℝ) (cst sys) (cidx N b) then ‖κ f b‖ * ‖v.ofLp b‖ else 0) ^ 2 := by
  rw [FSKernel.norm_sq_eq]
  refine Finset.sum_le_sum fun f _ => ?_
  rw [FSKernel.kop_apply, ← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [norm_mul]
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfw := farW_nonneg (sys := sys) (L := L) (n := n) f
  unfold ytK
  by_cases hfb : ¬ InQ (n : ℝ) (cidx N f) ∧ InC (n : ℝ) (cst sys) (cidx N b)
  · rw [if_pos hfb, if_pos hfb.2]
    have hgap := far_cold_gap' (sys := sys) hL hfb.1 hfb.2
    have hfar := Asym_ge_far (sys := sys) hL hfb.1
    have hA : 0 < Asym sys L N f := lt_of_lt_of_le (by positivity) hfar
    have hd : 0 < Asym sys L N f - Asym sys L N b := by linarith
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
    have hw : farW sys L N n f = 1 / Asym sys L N f := by unfold farW; rw [if_neg hfb.1]
    rw [hw]
    have h1 : 1 / (Asym sys L N f - Asym sys L N b) ≤ 4 / 3 * (1 / Asym sys L N f) := by
      rw [div_le_iff₀ hd]
      field_simp
      linarith
    have hk := norm_nonneg (κ f b)
    have hv := norm_nonneg (v.ofLp b)
    calc ‖v.ofLp b‖ * (‖κ f b‖ / (Asym sys L N f - Asym sys L N b)) =
        ‖κ f b‖ * ‖v.ofLp b‖ * (1 / (Asym sys L N f - Asym sys L N b)) := by ring
      _ ≤ ‖κ f b‖ * ‖v.ofLp b‖ * (4 / 3 * (1 / Asym sys L N f)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 / 3 * (1 / Asym sys L N f) * (‖κ f b‖ * ‖v.ofLp b‖) := by ring
  · rw [if_neg hfb, norm_zero, mul_zero]
    split_ifs <;> positivity

end Dress

/-! ## The three shapes -/

section Shapes

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

omit [Fintype ν] in
open Classical in
/-- **Shape L1-W**: a first hop on the `j₁`-lines dominated by `κ₁(d)`, then a Coulomb hop of `j₂`:
`Σ_f ω_F² (Σ_d K₂ Σ_b K₁ x)² ≤ (2048 m²/g⁴) n⁻² c₂² H² A₁ L²_{j₁}(x)`. -/
theorem shape_L1W {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {j₁ j₂ : Ch eta} {A₂ : Finset (Fin eta)} {ε₂ : ℤ}
    (hA₂ : IsCoord j₂ A₂ ε₂) (K₂ K₁ : Cfg eta N → Cfg eta N → ℝ) (hK₂0 : ∀ f d, 0 ≤ K₂ f d)
    (hK₁0 : ∀ d b, 0 ≤ K₁ d b) {c₂ : ℝ} (_hc₂ : 0 ≤ c₂)
    (hK₂ : ∀ f d, K₂ f d ≤
      if OnCh j₂ (cidx N f) (cidx N d) then c₂ / FSLattice.lsq (chT N j₂ f d) else 0)
    (κ₁ : Cfg eta N → ℝ) (hK₁ : ∀ d b, K₁ d b ≤ if lab N j₁ d = lab N j₁ b then κ₁ d else 0)
    {A₁ : ℝ} (hA₁ : ∀ q : Cfg eta N,
      ∑ d ∈ Finset.univ.filter (fun d => lab N j₁ d = lab N j₁ q), κ₁ d ^ 2 ≤ A₁)
    (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ d, K₂ f d * ∑ b, K₁ d b * x b) ^ 2 ≤
      2048 * mmax sys ^ 2 / gF L ^ 4 / (n : ℝ) ^ 2 * c₂ ^ 2 * Hunit ^ 2 *
        (A₁ * lineSq j₁ (fun _ => 1) x) := by
  classical
  set v : Cfg eta N → ℝ := fun d => ∑ b, K₁ d b * x b with hv
  have hv0 : ∀ d, 0 ≤ v d := fun d => Finset.sum_nonneg fun b _ => mul_nonneg (hK₁0 d b) (hx b)
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set CE := 2048 * mmax sys ^ 2 / gF L ^ 4 with hCE
  have hCE0 : 0 ≤ CE := by positivity
  have hpt : ∀ f, farW sys L N n f ^ 2 * (∑ d, K₂ f d * v d) ^ 2 ≤
      CE / (n : ℝ) ^ 2 * c₂ ^ 2 * ((∑ d, if OnCh j₂ (cidx N f) (cidx N d) then
        v d / FSLattice.lsq (chT N j₂ f d) else 0) ^ 2 /
          (1 + FSLattice.lsq (regSum A₂ (cidx N f)))) := by
    intro f
    have h1 := farW_sq_le_coord (sys := sys) hL hn hA₂.card f
    have h2 : ∑ d, K₂ f d * v d ≤ c₂ * ∑ d, if OnCh j₂ (cidx N f) (cidx N d) then
        v d / FSLattice.lsq (chT N j₂ f d) else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun d _ => ?_
      have := hK₂ f d
      split_ifs at this ⊢ with h
      · calc K₂ f d * v d ≤ c₂ / FSLattice.lsq (chT N j₂ f d) * v d :=
              mul_le_mul_of_nonneg_right this (hv0 d)
          _ = c₂ * (v d / FSLattice.lsq (chT N j₂ f d)) := by ring
      · have h0 : K₂ f d = 0 := le_antisymm this (hK₂0 f d)
        rw [h0, zero_mul, mul_zero]
    have h3 : 0 ≤ ∑ d, K₂ f d * v d := Finset.sum_nonneg fun d _ => mul_nonneg (hK₂0 f d) (hv0 d)
    have h4 := pow_le_pow_left₀ h3 h2 2
    have hl := FSLattice.lsq_nonneg (regSum A₂ (cidx N f))
    have hfw0 := sq_nonneg (farW sys L N n f)
    calc farW sys L N n f ^ 2 * (∑ d, K₂ f d * v d) ^ 2 ≤
        CE / ((n : ℝ) ^ 2 * (1 + FSLattice.lsq (regSum A₂ (cidx N f)))) *
          (c₂ * ∑ d, if OnCh j₂ (cidx N f) (cidx N d) then
            v d / FSLattice.lsq (chT N j₂ f d) else 0) ^ 2 :=
          mul_le_mul h1 h4 (sq_nonneg _) (by positivity)
      _ = _ := by field_simp
  refine (Finset.sum_le_sum fun f _ => hpt f).trans ?_
  rw [← Finset.mul_sum]
  have hHd := line_hardy_dual hH hA₂ (fun _ => (1 : ℝ)) (fun _ => zero_le_one) v
  simp only [one_mul] at hHd
  have hll := long_line_le j₁ x hx K₁ hK₁0 κ₁ hK₁ hA₁
  calc CE / (n : ℝ) ^ 2 * c₂ ^ 2 * ∑ f, (∑ d, if OnCh j₂ (cidx N f) (cidx N d) then
        v d / FSLattice.lsq (chT N j₂ f d) else 0) ^ 2 /
          (1 + FSLattice.lsq (regSum A₂ (cidx N f))) ≤
      CE / (n : ℝ) ^ 2 * c₂ ^ 2 * (Hunit ^ 2 * ∑ d, v d ^ 2) :=
        mul_le_mul_of_nonneg_left hHd (by positivity)
    _ ≤ CE / (n : ℝ) ^ 2 * c₂ ^ 2 * (Hunit ^ 2 * (A₁ * lineSq j₁ (fun _ => 1) x)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hll (sq_nonneg _)
    _ = _ := by ring

/-- **Shape L1-Y**: a first hop on the `j₁`-lines dominated by `κ₁(d)`, then the com dressing
`y_{j₂}`: `Σ_f ω_F² (Σ_d |y_{j₂}| Σ_b K₁ x)² ≤ (2048 m²/g⁴) n⁻² (C_{j₂} Λ_N)² A₁ L²_{j₁}(x)`. -/
theorem shape_L1Y (hL : 0 < L) (hn : 1 ≤ n)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {j₁ : Ch eta} (j₂ : Ch eta) (K₁ : Cfg eta N → Cfg eta N → ℝ) (hK₁0 : ∀ d b, 0 ≤ K₁ d b)
    (κ₁ : Cfg eta N → ℝ) (hK₁ : ∀ d b, K₁ d b ≤ if lab N j₁ d = lab N j₁ b then κ₁ d else 0)
    {A₁ : ℝ} (hA₁ : ∀ q : Cfg eta N,
      ∑ d ∈ Finset.univ.filter (fun d => lab N j₁ d = lab N j₁ q), κ₁ d ^ 2 ≤ A₁)
    (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, K₁ d b * x b) ^ 2 ≤
      2048 * mmax sys ^ 2 / gF L ^ 4 / (n : ℝ) ^ 2 * (CYc sys L j₂ * LamB sys N) ^ 2 *
        (A₁ * lineSq j₁ (fun _ => 1) x) := by
  classical
  set v : Cfg eta N → ℝ := fun d => ∑ b, K₁ d b * x b with hv
  have hv0 : ∀ d, 0 ≤ v d := fun d => Finset.sum_nonneg fun b _ => mul_nonneg (hK₁0 d b) (hx b)
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set CE := 2048 * mmax sys ^ 2 / gF L ^ 4 with hCE
  have hCE0 : 0 ≤ CE := by positivity
  set D : Cfg eta N → ℝ := fun q => Real.sqrt ((n : ℝ) ^ 2 + piC j₂ (cidx N q) ^ 2) with hD
  have hD0 : ∀ q, 0 < D q := fun q => Real.sqrt_pos.mpr (by
    have := sq_nonneg (piC j₂ (cidx N q)); positivity)
  have hDsq : ∀ q, D q ^ 2 = (n : ℝ) ^ 2 + piC j₂ (cidx N q) ^ 2 := fun q =>
    Real.sq_sqrt (by have := sq_nonneg (piC j₂ (cidx N q)); positivity)
  set v' : Cfg eta N → ℝ := fun d => v d / D d with hv'
  have hpt : ∀ f, farW sys L N n f ^ 2 * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * v d) ^ 2 ≤
      CE / (n : ℝ) ^ 2 * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * v' d) ^ 2 := by
    intro f
    have h1 := farW_sq_le_pi (sys := sys) hL hn j₂ f
    have h2 : ∑ d, ‖yj sys L p₀ N j₂ f d‖ * v d = D f * ∑ d, ‖yj sys L p₀ N j₂ f d‖ * v' d := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases h0 : yj sys L p₀ N j₂ f d = 0
      · rw [h0, norm_zero, zero_mul, zero_mul, mul_zero]
      · have hj : OnCh j₂ (cidx N f) (cidx N d) := by
          by_contra hj; apply h0; unfold yj ycKc; rw [if_neg hj]
        have hDe : D f = D d := by simp only [hD]; rw [piC_onCh hj]
        simp only [hv']
        rw [hDe]
        have := (hD0 d).ne'
        field_simp
    rw [h2, mul_pow, hDsq]
    have h3 := sq_nonneg (∑ d, ‖yj sys L p₀ N j₂ f d‖ * v' d)
    have h4 := sq_nonneg (piC j₂ (cidx N f))
    calc farW sys L N n f ^ 2 * (((n : ℝ) ^ 2 + piC j₂ (cidx N f) ^ 2) *
          (∑ d, ‖yj sys L p₀ N j₂ f d‖ * v' d) ^ 2) ≤
        CE / ((n : ℝ) ^ 2 * ((n : ℝ) ^ 2 + piC j₂ (cidx N f) ^ 2)) *
          (((n : ℝ) ^ 2 + piC j₂ (cidx N f) ^ 2) * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * v' d) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = CE / (n : ℝ) ^ 2 * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * v' d) ^ 2 := by
          have : 0 < (n : ℝ) ^ 2 + piC j₂ (cidx N f) ^ 2 := by positivity
          field_simp
  refine (Finset.sum_le_sum fun f _ => hpt f).trans ?_
  rw [← Finset.mul_sum]
  have hY := sum_sq_yj_le (p₀ := p₀) hL H hKernel j₂ v'
  have hY2 : ∑ d, rY (sys := sys) (L := L) j₂ d ^ 2 * v' d ^ 2 ≤
      (CYc sys L j₂ * LamB sys N) ^ 2 * ∑ d, v d ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    unfold rY
    simp only [hv']
    rw [div_pow, hDsq]
    have hpi := sq_nonneg (piC j₂ (cidx N d))
    have hc := sq_nonneg (CYc sys L j₂ * LamB sys N)
    have hvd := sq_nonneg (v d)
    have h5 : piC j₂ (cidx N d) ^ 2 ≤ (n : ℝ) ^ 2 + piC j₂ (cidx N d) ^ 2 := by
      have := sq_nonneg (n : ℝ); linarith
    have h6 : 0 < (n : ℝ) ^ 2 + piC j₂ (cidx N d) ^ 2 := by positivity
    rw [mul_pow, mul_div_assoc']
    rw [div_le_iff₀ h6]
    nlinarith [mul_le_mul_of_nonneg_left h5 (mul_nonneg hc hvd)]
  have hll := long_line_le j₁ x hx K₁ hK₁0 κ₁ hK₁ hA₁
  calc CE / (n : ℝ) ^ 2 * ∑ f, (∑ d, ‖yj sys L p₀ N j₂ f d‖ * v' d) ^ 2 ≤
      CE / (n : ℝ) ^ 2 * ((CYc sys L j₂ * LamB sys N) ^ 2 * ∑ d, v d ^ 2) :=
        mul_le_mul_of_nonneg_left (hY.trans hY2) (by positivity)
    _ ≤ CE / (n : ℝ) ^ 2 * ((CYc sys L j₂ * LamB sys N) ^ 2 * (A₁ * lineSq j₁ (fun _ => 1) x)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hll (sq_nonneg _)
    _ = _ := by ring

omit [Fintype ν] in
open Classical in
/-- **Shape L2**: a second hop dominated, from the support of `v`, by `κ₂(f)` on the `j₂`-lines:
`Σ_f ω_F² (Σ_d K₂ v)² ≤ A₂ L²_{j₂}(v)`. -/
theorem shape_L2 (j₂ : Ch eta) (K₂ : Cfg eta N → Cfg eta N → ℝ) (hK₂0 : ∀ f d, 0 ≤ K₂ f d)
    (v : Cfg eta N → ℝ) (hv : ∀ d, 0 ≤ v d) (S : Cfg eta N → Prop) (hvS : ∀ d, v d ≠ 0 → S d)
    (κ₂ : Cfg eta N → ℝ) (hκ₂0 : ∀ f, 0 ≤ κ₂ f)
    (hK₂ : ∀ f d, S d → farW sys L N n f * K₂ f d ≤ if lab N j₂ f = lab N j₂ d then κ₂ f else 0)
    {A₂ : ℝ} (hA₂ : ∀ q : Cfg eta N,
      ∑ f ∈ Finset.univ.filter (fun f => lab N j₂ f = lab N j₂ q), κ₂ f ^ 2 ≤ A₂) :
    ∑ f, farW sys L N n f ^ 2 * (∑ d, K₂ f d * v d) ^ 2 ≤ A₂ * lineSq j₂ (fun _ => 1) v := by
  classical
  set K : Cfg eta N → Cfg eta N → ℝ := fun f d => if S d then farW sys L N n f * K₂ f d else 0
    with hK
  have hK0 : ∀ f d, 0 ≤ K f d := fun f d => by
    simp only [hK]; split_ifs
    · exact mul_nonneg (farW_nonneg f) (hK₂0 f d)
    · exact le_rfl
  have hKb : ∀ f d, K f d ≤ if lab N j₂ f = lab N j₂ d then κ₂ f else 0 := by
    intro f d
    simp only [hK]
    split_ifs with h1 h2 h2
    · have := hK₂ f d h1; rwa [if_pos h2] at this
    · have := hK₂ f d h1; rwa [if_neg h2] at this
    · exact hκ₂0 f
    · exact le_rfl
  have hll := long_line_le j₂ v hv K hK0 κ₂ hKb hA₂
  refine le_trans (le_of_eq ?_) hll
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← mul_pow]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [hK]
  by_cases h : v d = 0
  · rw [h]; ring
  · rw [if_pos (hvS d h)]; ring

end Shapes

end FSFlux
