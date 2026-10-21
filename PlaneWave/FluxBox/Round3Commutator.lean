import PlaneWave.FluxBox.FarColdDressingCold

/-!
# Flux route, stage 3, part 31: the round-3 commutator outside `C × C`

With `Ỹ = kop(ytK b^{FC})` (`Yt`) and `Ỹ* ` (`Ytd`), `Y₃ = Ỹ + Ỹ*` (`Y3N_eq_add`), and

  `⟨W u, Y₃ u⟩ = ⟨W u_C, Ỹ u_C⟩ + ⟨W u_{¬C}, Ỹ u⟩ + ⟨Ỹ W u, u_F⟩`   (`inner_W_Y3_split`),

so `|Re⟨u, i[W,Y₃]u⟩ + 2 Im⟨W u_C, Ỹ u_C⟩| ≤ 2‖W u_{¬C}‖ ‖Ỹ u‖ + 2‖Ỹ W u‖ ‖u_F‖`
(`abs_comm_Y3_sub_CC_le`). The endpoint is `|⟨u, Y₃ u⟩| ≤ 2 ‖u_F‖ ‖Ỹ u‖` (`abs_inner_Y3_le`).

**P3** (`lineSq_CWu_good_le`): `Σ_j L²_j(1_C |W u|) ≤ #ch³ B₃` for a good `u`, `B₃ ~ n² log N M²`:
a hop landing on the cold ball has columns `≤ 81 c_j (c_* n + 1)` (`sum_wj_cold_col_le`, same channel)
or goes through transverse Hardy (`lineSq_CW_cross_le`), the weight `1 + |ξ|²` costing the critical
moment on the whole box (`lineSq_good_weight_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Restrictions -/

section Res

variable {X : Type*} [Fintype X]

omit [Fintype ν] in
lemma res_kop_of_rows (κ : X → X → ℂ) (P : X → Prop) (hκ : ∀ q p, κ q p ≠ 0 → P q)
    (u : EuclideanSpace ℂ X) : FSKernel.res P (FSKernel.kop κ u) = FSKernel.kop κ u := by
  classical
  ext q
  rw [FSKernel.res_apply]
  by_cases hq : P q
  · rw [if_pos hq]
  · rw [if_neg hq, FSKernel.kop_apply]
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    have : κ q p = 0 := by by_contra h; exact hq (hκ q p h)
    rw [this, mul_zero]

omit [Fintype ν] [Fintype X] in
lemma res_add_not (S : X → Prop) (u : EuclideanSpace ℂ X) :
    FSKernel.res S u + FSKernel.res (fun q => ¬ S q) u = u := by
  classical
  ext q
  rw [PiLp.add_apply, FSKernel.res_apply, FSKernel.res_apply]
  by_cases h : S q
  · rw [if_pos h, if_neg (not_not_intro h), add_zero]
  · rw [if_neg h, if_pos h, zero_add]

omit [Fintype ν] in
lemma inner_res_comm (S : X → Prop) (u v : EuclideanSpace ℂ X) :
    ⟪FSKernel.res S u, v⟫_ℂ = ⟪u, FSKernel.res S v⟫_ℂ := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [FSKernel.res_apply, Pi.star_apply, RCLike.star_def]
  split_ifs <;> simp

end Res

/-! ## The split of the commutator -/

section Split

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

variable (sys L p₀ N n) in
/-- `Ỹ = Π_F Y₃ Π_C`, the far–cold dressing. -/
noncomputable abbrev Yt : En eta N →ₗ[ℂ] En eta N := FSKernel.kop (ytK sys L N n (bfcK sys L p₀ N n))

variable (sys L p₀ N n) in
/-- `Ỹ*`. -/
noncomputable abbrev Ytd : En eta N →ₗ[ℂ] En eta N :=
  FSKernel.kop (fun q p => conj (ytK sys L N n (bfcK sys L p₀ N n) p q))

/-- `Y₃ = Ỹ + Ỹ*`. -/
lemma Y3N_eq_add (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 1 ≤ n) : Y3N sys L p₀ N n = Yt sys L p₀ N n + Ytd sys L p₀ N n := by
  rw [← FSKernel.kop_add]
  show FSKernel.kop (y3K sys L p₀ N n) = _
  congr 1
  funext q p
  rw [Pi.add_apply, Pi.add_apply]
  exact y3K_eq hL H hKernel hn q p

lemma inner_Ytd (x y : En eta N) : ⟪x, Ytd sys L p₀ N n y⟫_ℂ = ⟪Yt sys L p₀ N n x, y⟫_ℂ :=
  (FSKernel.inner_kop _ x y).symm

lemma Yt_res_C (v : En eta N) :
    Yt sys L p₀ N n v = Yt sys L p₀ N n (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) v) :=
  FSKernel.kop_res_of_cols (ytK sys L N n (bfcK sys L p₀ N n))
    (fun p => InC (n : ℝ) (cst sys) (cidx N p))
    (fun _ _ h => (ytK_supp (κ := bfcK sys L p₀ N n) h).2) v

lemma res_F_Yt (v : En eta N) :
    FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) (Yt sys L p₀ N n v) = Yt sys L p₀ N n v :=
  res_kop_of_rows (ytK sys L N n (bfcK sys L p₀ N n)) (fun q => ¬ InQ (n : ℝ) (cidx N q))
    (fun _ _ h => (ytK_supp (κ := bfcK sys L p₀ N n) h).1) v

lemma inner_Yt_left (x y : En eta N) :
    ⟪Yt sys L p₀ N n x, y⟫_ℂ =
      ⟪Yt sys L p₀ N n x, FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) y⟫_ℂ := by
  rw [← inner_res_comm, res_F_Yt]

lemma inner_Yt_right (x y : En eta N) :
    ⟪x, Yt sys L p₀ N n y⟫_ℂ =
      ⟪FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) x, Yt sys L p₀ N n y⟫_ℂ := by
  rw [inner_res_comm, res_F_Yt]

open Classical in
/-- **The split**: `⟨W u, Y₃ u⟩ = ⟨W u_C, Ỹ u_C⟩ + ⟨W u_{¬C}, Ỹ u⟩ + ⟨Ỹ W u, u_F⟩`. -/
theorem inner_W_Y3_split (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 1 ≤ n) (u : En eta N) :
    ⟪WN sys L N u, Y3N sys L p₀ N n u⟫_ℂ =
      ⟪WN sys L N (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u),
          Yt sys L p₀ N n (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u)⟫_ℂ +
        ⟪WN sys L N (FSKernel.res (fun p => ¬ InC (n : ℝ) (cst sys) (cidx N p)) u),
          Yt sys L p₀ N n u⟫_ℂ +
        ⟪Yt sys L p₀ N n (WN sys L N u), FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) u⟫_ℂ := by
  rw [Y3N_eq_add hL H hKernel hn, LinearMap.add_apply, inner_add_right, inner_Ytd, inner_Yt_left]
  congr 1
  have h2 : WN sys L N u = WN sys L N (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u) +
      WN sys L N (FSKernel.res (fun p => ¬ InC (n : ℝ) (cst sys) (cidx N p)) u) := by
    rw [← map_add, res_add_not]
  rw [h2, inner_add_left, ← Yt_res_C]

open Classical in
/-- **The commutator outside `C × C`**:
`|Re⟨u, i[W,Y₃]u⟩ + 2 Im⟨W u_C, Ỹ u_C⟩| ≤ 2‖W u_{¬C}‖ ‖Ỹ u‖ + 2‖Ỹ W u‖ ‖u_F‖`. -/
theorem abs_comm_Y3_sub_CC_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 1 ≤ n) (u : En eta N) :
    |(⟪u, (Complex.I • (WN sys L N ∘ₗ Y3N sys L p₀ N n - Y3N sys L p₀ N n ∘ₗ WN sys L N)) u⟫_ℂ).re +
        2 * (⟪WN sys L N (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u),
          Yt sys L p₀ N n (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u)⟫_ℂ).im| ≤
      2 * (‖WN sys L N (FSKernel.res (fun p => ¬ InC (n : ℝ) (cst sys) (cidx N p)) u)‖ *
          ‖Yt sys L p₀ N n u‖) +
        2 * (‖Yt sys L p₀ N n (WN sys L N u)‖ * ‖FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) u‖) := by
  rw [re_comm_eq WN_symm Y3N_symm u, inner_W_Y3_split hL H hKernel hn u, Complex.add_im,
    Complex.add_im]
  set a := ⟪WN sys L N (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u),
          Yt sys L p₀ N n (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u)⟫_ℂ
  set b := ⟪WN sys L N (FSKernel.res (fun p => ¬ InC (n : ℝ) (cst sys) (cidx N p)) u),
          Yt sys L p₀ N n u⟫_ℂ
  set c := ⟪Yt sys L p₀ N n (WN sys L N u), FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) u⟫_ℂ
  have hb := (Complex.abs_im_le_norm b).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
  have hc := (Complex.abs_im_le_norm c).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
  have e : -2 * (a.im + b.im + c.im) + 2 * a.im = -2 * b.im - 2 * c.im := by ring
  rw [e]
  have := abs_le.mp (show |b.im| ≤ _ from hb)
  have := abs_le.mp (show |c.im| ≤ _ from hc)
  rw [abs_le]
  constructor <;> linarith

open Classical in
/-- **The endpoint**: `|⟨u, Y₃ u⟩| ≤ 2 ‖u_F‖ ‖Ỹ u‖`. -/
theorem abs_inner_Y3_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 1 ≤ n) (u : En eta N) :
    ‖⟪u, Y3N sys L p₀ N n u⟫_ℂ‖ ≤
      2 * (‖FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) u‖ * ‖Yt sys L p₀ N n u‖) := by
  rw [Y3N_eq_add hL H hKernel hn, LinearMap.add_apply, inner_add_right, inner_Ytd, inner_Yt_right,
    inner_Yt_left]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) u)
    (Yt sys L p₀ N n u)
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (Yt sys L p₀ N n u)
    (FSKernel.res (fun q => ¬ InQ (n : ℝ) (cidx N q)) u)
  linarith

/-- `‖Y₃ u‖ ≤ ‖Ỹ u‖ + ‖Ỹ* u‖`. -/
lemma norm_Y3N_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (hn : 1 ≤ n) (u : En eta N) :
    ‖Y3N sys L p₀ N n u‖ ≤ ‖Yt sys L p₀ N n u‖ + ‖Ytd sys L p₀ N n u‖ := by
  rw [Y3N_eq_add hL H hKernel hn, LinearMap.add_apply]
  exact norm_add_le _ _

/-- `‖Ỹ* u‖ ≤ B ‖u‖` when `‖Ỹ x‖ ≤ B ‖x‖` for all `x`. -/
lemma norm_Ytd_le {B : ℝ} (hB : ∀ x : En eta N, ‖Yt sys L p₀ N n x‖ ≤ B * ‖x‖) (u : En eta N) :
    ‖Ytd sys L p₀ N n u‖ ≤ B * ‖u‖ := by
  by_cases hu : u = 0
  · rw [hu, map_zero]; simp
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hB0 : 0 ≤ B := by
    by_contra hneg
    have h1 : B * ‖u‖ < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hu0
    linarith [norm_nonneg (Yt sys L p₀ N n u), hB u]
  set y := Ytd sys L p₀ N n u
  by_cases hy : y = 0
  · rw [hy, norm_zero]; positivity
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h1 : ‖y‖ ^ 2 = ‖⟪y, y⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K]; simp
  have h2 : ⟪y, y⟫_ℂ = ⟪Yt sys L p₀ N n y, u⟫_ℂ := inner_Ytd y u
  have h3 := norm_inner_le_norm (𝕜 := ℂ) (Yt sys L p₀ N n y) u
  have h4 := hB y
  have h5 : ‖y‖ ^ 2 ≤ B * ‖y‖ * ‖u‖ := by
    rw [h1, h2]
    exact h3.trans (mul_le_mul_of_nonneg_right h4 (norm_nonneg u))
  have h6 : ‖y‖ * ‖y‖ ≤ ‖y‖ * (B * ‖u‖) := by nlinarith
  exact le_of_mul_le_mul_left h6 hy0

end Split

/-! ## Line squares of hops landing on the cold ball -/

section P3Lines

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

open Classical in
/-- **Columns of a hop landing on the cold ball**: `Σ_{b ∈ C} |w_j(b,a)| ≤ 81 c_j (c_* n + 1)`. -/
lemma sum_wj_cold_col_le (hL : 0 < L) (j : Ch eta) (a : Cfg eta N) :
    ∑ b, (if InC (n : ℝ) (cst sys) (cidx N b) then ‖wj sys L N j b a‖ else 0) ≤
      81 * (cst sys * n + 1) * chC sys L j := by
  classical
  have hc := chC_nonneg sys hL j
  set T := Finset.univ.filter (fun b : Cfg eta N => InC (n : ℝ) (cst sys) (cidx N b) ∧
    OnCh j (cidx N b) (cidx N a))
  have h1 : ∑ b, (if InC (n : ℝ) (cst sys) (cidx N b) then ‖wj sys L N j b a‖ else 0) ≤
      ∑ b ∈ T, chC sys L j / FSLattice.lsq (chT N j b a) := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun b _ => ?_
    have hw := norm_wj_le (sys := sys) hL j b a
    split_ifs with h1 h2 h2
    · rwa [if_pos h2.2] at hw
    · rw [if_neg (fun h => h2 ⟨h1, h⟩)] at hw
      exact hw
    · exact absurd h2.1 h1
    · exact le_rfl
  refine h1.trans ?_
  have hinj : Set.InjOn (fun b => chT N j b a) T := fun b hb b' hb' h =>
    chT_injOn j a (Finset.mem_filter.mp hb).2.2 (Finset.mem_filter.mp hb').2.2 h
  rw [← Finset.sum_image (f := fun θ => chC sys L j / FSLattice.lsq θ) hinj]
  have e : ∑ θ ∈ T.image (fun b => chT N j b a), chC sys L j / FSLattice.lsq θ =
      chC sys L j * ∑ θ ∈ T.image (fun b => chT N j b a), 1 / FSLattice.lsq θ := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun θ _ => ?_; ring
  rw [e, mul_comm (81 * (cst sys * n + 1))]
  apply mul_le_mul_of_nonneg_left _ hc
  have hR : (1 : ℝ) ≤ cst sys * n + 1 := by have := cst_mul_nonneg (sys := sys) (n := n); linarith
  apply sum_inv_lsq_shifted_le _ (-(cidx N a (lead j))) hR
  intro θ hθ
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hθ
  have hbC := (Finset.mem_filter.mp hb).2.1
  have e2 : chT N j b a - -cidx N a (lead j) = cidx N b (lead j) := by
    unfold chT; abel
  rw [e2]
  have h3 : FSLattice.lsq (cidx N b (lead j)) ≤ (cst sys * n) ^ 2 := hbC (lead j)
  have h4 : 0 ≤ cst sys * n := cst_mul_nonneg
  nlinarith

open Classical in
/-- **A hop landing on the cold ball on its own lines**:
`L²_j(1_C |W_j| y) ≤ (81 (c_* n + 1) c_j)² L²_j(y)`. -/
lemma lineSq_CW_same_le (hL : 0 < L) (j : Ch eta) (y : Cfg eta N → ℝ) (hy : ∀ p, 0 ≤ y p) :
    lineSq j (fun _ => 1) (fun b => ∑ a, (if InC (n : ℝ) (cst sys) (cidx N b) then
      ‖wj sys L N j b a‖ else 0) * y a) ≤
      (81 * (cst sys * n + 1) * chC sys L j) ^ 2 * lineSq j (fun _ => 1) y := by
  apply lineSq_conv_le j (fun _ => zero_le_one) _ (fun b a => by split_ifs <;> simp) y hy
  · intro b a h
    have hw := norm_wj_le (sys := sys) hL j b a
    by_contra hlab
    apply h
    have hj : ¬ OnCh j (cidx N b) (cidx N a) := fun h' => hlab (lab_eq_iff.mpr h')
    rw [if_neg hj] at hw
    have : ‖wj sys L N j b a‖ = 0 := le_antisymm hw (norm_nonneg _)
    split_ifs <;> simp [this]
  · exact sum_wj_cold_col_le hL j

open Classical in
/-- **A hop landing on the cold ball across the lines** (transverse Hardy). -/
lemma lineSq_CW_cross_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) {j j₃ : Ch eta} {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j₃ A ε)
    (hAj : ∀ σ, regSum A (tr j σ) = 0) (y : Cfg eta N → ℝ) (hy : ∀ p, 0 ≤ y p) :
    lineSq j (fun _ => 1) (fun b => ∑ a, (if InC (n : ℝ) (cst sys) (cidx N b) then
      ‖wj sys L N j₃ b a‖ else 0) * y a) ≤
      chC sys L j₃ ^ 2 * (Hunit ^ 2 * lineSq j (fun s => 1 + FSLattice.lsq (regSum A s)) y) := by
  have hc := chC_nonneg sys hL j₃
  have hpt : ∀ b, ∑ a, (if InC (n : ℝ) (cst sys) (cidx N b) then ‖wj sys L N j₃ b a‖ else 0) * y a ≤
      chC sys L j₃ * ∑ a, (if OnCh j₃ (cidx N b) (cidx N a) then
        y a / FSLattice.lsq (chT N j₃ b a) else 0) := by
    intro b
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have hw := norm_wj_le (sys := sys) hL j₃ b a
    split_ifs at hw ⊢ with h1 h2 h2
    · calc ‖wj sys L N j₃ b a‖ * y a ≤ chC sys L j₃ / FSLattice.lsq (chT N j₃ b a) * y a :=
            mul_le_mul_of_nonneg_right hw (hy a)
        _ = chC sys L j₃ * (y a / FSLattice.lsq (chT N j₃ b a)) := by ring
    · have : ‖wj sys L N j₃ b a‖ = 0 := le_antisymm hw (norm_nonneg _)
      rw [this, zero_mul, mul_zero]
    · rw [zero_mul]; exact mul_nonneg hc (div_nonneg (hy a) (FSLattice.lsq_nonneg _))
    · rw [zero_mul, mul_zero]
  have hv0 : ∀ b, 0 ≤ ∑ a, (if InC (n : ℝ) (cst sys) (cidx N b) then
      ‖wj sys L N j₃ b a‖ else 0) * y a :=
    fun b => Finset.sum_nonneg fun a _ => mul_nonneg (by split_ifs <;> simp) (hy a)
  have h1 := lineSq_mono j (fun _ => zero_le_one) hv0 hpt
  rw [lineSq_smul] at h1
  refine h1.trans ?_
  exact mul_le_mul_of_nonneg_left (lineSq_hop_le hH hA hAj y hy) (sq_nonneg _)

omit [Fintype ν] in
open Classical in
/-- Line squares of a finite sum: `L²_j(Σ_i v_i) ≤ #s Σ_i L²_j(v_i)`. -/
lemma lineSq_sum_le (j : Ch eta) {Ω : Cf eta → ℝ} (hΩ : ∀ t, 0 ≤ Ω t) {ι : Type*} (s : Finset ι)
    (v : ι → Cfg eta N → ℝ) :
    lineSq j Ω (fun p => ∑ i ∈ s, v i p) ≤ (s.card : ℝ) * ∑ i ∈ s, lineSq j Ω (v i) := by
  unfold lineSq lineSum
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_comm]
  rw [← Finset.mul_sum, mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (hΩ t)
  exact sq_sum_le_card_mul_sum_sq

omit [Fintype ν] in
/-- All box configurations are in the bulk ball of radius `2N` (`InQ (8N)`). -/
lemma inQ_box (q : Cfg eta N) : InQ ((8 * N : ℕ) : ℝ) (cidx N q) := by
  intro c
  have h := lsq_cidx_le q c
  show FSLattice.lsq (cidx N q c) ≤ (((8 * N : ℕ) : ℝ) / 4) ^ 2
  push_cast
  have : (8 * (N : ℝ) / 4) ^ 2 = 4 * (N : ℝ) ^ 2 := by ring
  rw [this]
  nlinarith [sq_nonneg (N : ℝ)]

omit [Fintype ν] in
/-- **The critical moment on the whole box**:
`Σ (1 + E)² √(1 + E) |u|² ≤ (1 + η/2)^{1/2} M² (1 + 2η n_d)` when `2 g N ≤ 2^{n_d}`. -/
lemma crit_moment_box (hL : 0 < L) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) :
    ∑ q, (1 + Asym sys L N q) ^ 2 * Real.sqrt (1 + Asym sys L N q) * ‖u.ofLp q‖ ^ 2 ≤
      (1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd) := by
  classical
  have hnd' : gF L * (((8 * N : ℕ) : ℝ) / 4) ≤ 2 ^ nd := by
    push_cast
    have : (8 * (N : ℝ) / 4) = 2 * N := by ring
    rw [this]; exact hnd
  have h := crit_moment_le hL hnd' hu
  refine le_of_eq_of_le (Finset.sum_congr rfl fun q _ => ?_) h
  rw [if_pos (inQ_box q)]

variable (sys L) in
/-- The weight constant of `1 + |ξ|²` against `w32`: `2√2 c_X^{3/2} · 2 c_X`. -/
noncomputable def W5c : ℝ := 2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * (2 * cXw sys L)

omit [Fintype ν] in
lemma W5c_nonneg (hL : 0 < L) : 0 ≤ W5c sys L := by
  unfold W5c
  have := cXw_ge_one (sys := sys) hL
  positivity

omit [Fintype ν] in
open Classical in
/-- **The weighted line squares of a good state**:
`L²_j(|u|; 1 + |ξ|²) ≤ 125 (log₂ 2N + 2) W₅ (1 + η/2)^{1/2} M² (1 + 2η n_d)` for `ξ` a coordinate
constant on the `j`-lines. -/
theorem lineSq_good_weight_le (hL : 0 < L) (hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd)
    {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) {j : Ch eta} {A : Finset (Fin eta)}
    (hAc : A.card ≤ 2) (hAj : ∀ σ, regSum A (tr j σ) = 0) :
    lineSq j (fun s => 1 + FSLattice.lsq (regSum A s)) (fun b => ‖u.ofLp b‖) ≤
      125 * (Nat.log 2 (2 * N) + 2) *
        (W5c sys L * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd))) := by
  have h := lineSq_le j (Ω := fun s => 1 + FSLattice.lsq (regSum A s))
    (fun t => add_nonneg zero_le_one (FSLattice.lsq_nonneg _))
    (fun b => ‖u.ofLp b‖) (fun p => w32 (regSum {lead j} (cidx N p))) (fun p => w32_pos _)
    (fun q => lineSum_inv_w32_le hN (coord_lead j) q)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hcm := crit_moment_box (sys := sys) hL hnd hu
  have hW := W5c_nonneg (sys := sys) hL
  calc ∑ p, (1 + FSLattice.lsq (regSum A (lab N j p))) * w32 (regSum {lead j} (cidx N p)) *
        ‖u.ofLp p‖ ^ 2 ≤
      ∑ p, W5c sys L * ((1 + Asym sys L N p) ^ 2 * Real.sqrt (1 + Asym sys L N p) * ‖u.ofLp p‖ ^ 2) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have e : regSum A (lab N j p) = regSum A (cidx N p) := regSum_lineLab hAj (cidx N p)
        rw [e]
        have h1 := one_add_lsq_regSum_le (sys := sys) hL hAc p
        have h1' : 1 + FSLattice.lsq (regSum A (cidx N p)) ≤ (2 * cXw sys L) * (1 + Asym sys L N p) := by
          rw [mul_assoc]; exact h1
        have h2 := weight5_le (sys := sys) hL (coord_lead j).card p
          (add_nonneg zero_le_one (FSLattice.lsq_nonneg _)) h1'
        have e2 : W5c sys L * ((1 + Asym sys L N p) ^ 2 * Real.sqrt (1 + Asym sys L N p) *
            ‖u.ofLp p‖ ^ 2) = 2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) *
              (2 * cXw sys L) * ((1 + Asym sys L N p) ^ 2 * Real.sqrt (1 + Asym sys L N p)) *
              ‖u.ofLp p‖ ^ 2 := by unfold W5c; ring
        rw [e2]
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = W5c sys L * ∑ p, (1 + Asym sys L N p) ^ 2 * Real.sqrt (1 + Asym sys L N p) * ‖u.ofLp p‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcm hW

end P3Lines

/-! ## P3: the cold-landing potential of a good state in line squares -/

section P3

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

/-- The pointwise potential: `|(W v)_b| ≤ Σ_{j₃} Σ_a |w_{j₃}(b,a)| |v_a|`. -/
lemma norm_WN_apply_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (v : En eta N) (b : Cfg eta N) :
    ‖(WN sys L N v).ofLp b‖ ≤ ∑ j₃, ∑ a, ‖wj sys L N j₃ b a‖ * ‖v.ofLp a‖ := by
  have hW : WN sys L N = FSKernel.kop (wNK sys L N) := VN_eq_kop sys hL H hKernel
  rw [hW, FSKernel.kop_apply]
  calc ‖∑ a, v.ofLp a * wNK sys L N b a‖ ≤ ∑ a, ‖v.ofLp a‖ * ‖wNK sys L N b a‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => norm_mul _ _))
    _ ≤ ∑ a, ‖v.ofLp a‖ * ∑ j₃, ‖wj sys L N j₃ b a‖ := by
        refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [wNK_eq_sum_chPart hL b a]
        exact norm_sum_le _ _
    _ = ∑ j₃, ∑ a, ‖wj sys L N j₃ b a‖ * ‖v.ofLp a‖ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j₃ _ => ?_
        refine Finset.sum_congr rfl fun a _ => ?_
        ring

variable (sys L) in
/-- The channel-constant sum `Σ_j c_j`. -/
noncomputable def cSum : ℝ := ∑ j : Ch eta, chC sys L j

lemma chC_le_cSum (hL : 0 < L) (j : Ch eta) : chC sys L j ≤ cSum sys L :=
  Finset.single_le_sum (f := fun j => chC sys L j) (fun j _ => chC_nonneg sys hL j) (Finset.mem_univ j)

lemma cSum_nonneg (hL : 0 < L) : 0 ≤ cSum sys L :=
  Finset.sum_nonneg fun j _ => chC_nonneg sys hL j

variable (sys L) in
/-- The P3 line-square constant
`B₃ = (81 (c_* n + 1) c_Σ)² 125 (log₂ 2N + 2) 4 c_X² M² + c_Σ² H² 125 (log₂ 2N + 2) W₅ crit`. -/
noncomputable def B3 (Hunit : ℝ) (N n nd : ℕ) (M : ℝ) : ℝ :=
  (81 * (cst sys * n + 1) * cSum sys L) ^ 2 * (125 * (Nat.log 2 (2 * N) + 2) * (4 * cXw sys L ^ 2 * M ^ 2)) +
    cSum sys L ^ 2 * (Hunit ^ 2 * (125 * (Nat.log 2 (2 * N) + 2) *
      (W5c sys L * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd)))))

open Classical in
/-- **P3 line squares**: for a good `u`, `Σ_j L²_j(1_C |W u|) ≤ #ch³ B₃`. -/
theorem lineSq_CWu_good_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ∑ j, lineSq j (fun _ => 1) (fun b => if InC (n : ℝ) (cst sys) (cidx N b) then
      ‖(WN sys L N u).ofLp b‖ else 0) ≤
      (Fintype.card (Ch eta) : ℝ) ^ 3 * B3 sys L Hunit N n nd M := by
  set v3 : Ch eta → Cfg eta N → ℝ := fun j₃ b => ∑ a, (if InC (n : ℝ) (cst sys) (cidx N b) then
      ‖wj sys L N j₃ b a‖ else 0) * ‖u.ofLp a‖ with hv3
  have hy : ∀ p, 0 ≤ ‖u.ofLp p‖ := fun p => norm_nonneg _
  have hx0 : ∀ b, 0 ≤ (if InC (n : ℝ) (cst sys) (cidx N b) then ‖(WN sys L N u).ofLp b‖ else 0) :=
    fun b => by split_ifs <;> simp
  have hxle : ∀ b, (if InC (n : ℝ) (cst sys) (cidx N b) then ‖(WN sys L N u).ofLp b‖ else 0) ≤
      ∑ j₃, v3 j₃ b := by
    intro b
    simp only [hv3]
    split_ifs with hb
    · exact norm_WN_apply_le hL H hKernel u b
    · simp
  have hB0 : ∀ j j₃, lineSq j (fun _ => 1) (v3 j₃) ≤ B3 sys L Hunit N n nd M := by
    intro j j₃
    have hcS := cSum_nonneg (sys := sys) hL
    have hlog : (0 : ℝ) ≤ 125 * (Nat.log 2 (2 * N) + 2) := by positivity
    have hgood := lineSq_good_le hL hN hu (fun _ => True) j
    have hgood' : lineSq j (fun _ => 1) (fun b => ‖u.ofLp b‖) ≤
        125 * (Nat.log 2 (2 * N) + 2) * (4 * cXw sys L ^ 2 * M ^ 2) := by
      refine le_of_eq_of_le ?_ hgood
      congr 1
      funext b
      rw [if_pos trivial]
    have hcrit0 : 0 ≤ (1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd) := by
      have : (0 : ℝ) ≤ (1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
      positivity
    have hW := W5c_nonneg (sys := sys) hL
    have hT1 : 0 ≤ (81 * (cst sys * n + 1) * cSum sys L) ^ 2 *
        (125 * (Nat.log 2 (2 * N) + 2) * (4 * cXw sys L ^ 2 * M ^ 2)) := by positivity
    have hT2 : 0 ≤ cSum sys L ^ 2 * (Hunit ^ 2 * (125 * (Nat.log 2 (2 * N) + 2) *
        (W5c sys L * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd))))) := by
      positivity
    have hc := chC_le_cSum (sys := sys) hL
    have hc0 := fun j => chC_nonneg sys hL j
    have hcs : 0 ≤ cst sys * n + 1 := by have := cst_mul_nonneg (sys := sys) (n := n); linarith
    unfold B3
    by_cases hj : j₃ = j
    · subst hj
      have h1 := lineSq_CW_same_le (sys := sys) (n := n) hL j₃ (fun b => ‖u.ofLp b‖) hy
      refine (h1.trans ?_).trans (le_add_of_nonneg_right hT2)
      apply mul_le_mul _ hgood' (lineSq_nonneg _ (fun _ => zero_le_one) _) (by positivity)
      apply pow_le_pow_left₀ (by have := hc0 j₃; positivity)
      exact mul_le_mul_of_nonneg_left (hc j₃) (by positivity)
    · obtain ⟨A, ε, hA, hAj⟩ := exists_coord_ne hj
      have h1 := lineSq_CW_cross_le (sys := sys) (n := n) hH hL hA hAj (fun b => ‖u.ofLp b‖) hy
      have h2 := lineSq_good_weight_le (sys := sys) hL hN hnd hu hA.card hAj
      refine (h1.trans ?_).trans (le_add_of_nonneg_left hT1)
      apply mul_le_mul (pow_le_pow_left₀ (hc0 j₃) (hc j₃) 2) _
        (mul_nonneg (sq_nonneg _) (lineSq_nonneg _
          (fun t => add_nonneg zero_le_one (FSLattice.lsq_nonneg _)) _)) (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  calc ∑ j, lineSq j (fun _ => 1) (fun b => if InC (n : ℝ) (cst sys) (cidx N b) then
        ‖(WN sys L N u).ofLp b‖ else 0) ≤
      ∑ j : Ch eta, (Fintype.card (Ch eta) : ℝ) * ∑ j₃, lineSq j (fun _ => 1) (v3 j₃) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 := lineSq_mono j (fun _ => zero_le_one) hx0 hxle
        refine h1.trans ?_
        have h2 := lineSq_sum_le j (fun _ => zero_le_one) Finset.univ v3
        rw [Finset.card_univ] at h2
        exact h2
    _ ≤ ∑ j : Ch eta, (Fintype.card (Ch eta) : ℝ) * ∑ _j₃ : Ch eta, B3 sys L Hunit N n nd M := by
        refine Finset.sum_le_sum fun j _ => ?_
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum fun j₃ _ => hB0 j j₃
    _ = (Fintype.card (Ch eta) : ℝ) ^ 3 * B3 sys L Hunit N n nd M := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
        ring

end P3

end FSFlux
