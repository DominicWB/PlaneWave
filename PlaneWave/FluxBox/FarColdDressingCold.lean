import PlaneWave.FluxBox.FarColdColdInputs

/-!
# Flux route, stage 3, part 30: the far–cold dressing against cold inputs (P2)

**`norm_sq_Yt_cold_le`**: for every `v`,
`‖Ỹ v‖² ≤ K_{P2} n⁻³ Σ_j L²_j(x)`, `x = 1_C |v|`, `Ỹ = ytK b^{FC}` the far–cold part of `Y₃`:
the kernel of `b^{FC}` is split into the five chains of every word `(j₂, j₁)` (`norm_bfcK_le`,
`|λ| ≤ 1`), Cauchy–Schwarz over the words, and the word bounds of `PlaneWave.FluxBox.FarColdColdInputs`.

**`lineSq_good_le`**: for a good box state and any region `S`, `L²_j(1_S |u|) ≤ 125 (log₂ 2N + 2) 4 c_X² M²`
(`lineSq_le` with the weight `w32(ζ)`, `w32 ≤ (1 + |ζ|²)² ≤ 4 c_X² (1 + E)²`).
Hence `‖Ỹ u‖² ≤ C n⁻³ log N M²` (`norm_sq_Yt_good_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The kernel of `b^{FC}` by chains -/

section KernelSplit

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

omit [Fintype ν] in
lemma norm_lamC_le (j : Ch eta) : ‖((lamC sys p₀ j : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [lamC_nonneg sys p₀ j], lamC_le_one sys p₀ j⟩

omit [Fintype ν] in
lemma norm_lamC_sub_le (j₂ j₁ : Ch eta) :
    ‖((lamC sys p₀ j₂ : ℝ) : ℂ) - ((lamC sys p₀ j₁ : ℝ) : ℂ)‖ ≤ 1 := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  have := lamC_nonneg sys p₀ j₁
  have := lamC_nonneg sys p₀ j₂
  have := lamC_le_one sys p₀ j₁
  have := lamC_le_one sys p₀ j₂
  constructor <;> linarith

/-- `|fl_{j₂ j₁}| ≤ |Ch1| + |Ch2|`. -/
lemma norm_flK_le (j₂ j₁ : Ch eta) (q p : Cfg eta N) :
    ‖flK sys L p₀ N n j₂ j₁ q p‖ ≤
      ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun d => InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (wj sys L N j₁) q p‖ +
      ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) q p‖ := by
  unfold flK
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 := norm_lamC_le (sys := sys) (p₀ := p₀) j₁
  have h2 := norm_lamC_sub_le (sys := sys) (p₀ := p₀) j₂ j₁
  have e1 := norm_nonneg (chainK (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun d => InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (wj sys L N j₁) q p)
  have e2 := norm_nonneg (chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) q p)
  have := mul_le_mul_of_nonneg_right h1 e1
  have := mul_le_mul_of_nonneg_right h2 e2
  linarith

/-- `|com_{j₂ j₁}| ≤ |Ch3| + |Ch4| + |Ch2'|`. -/
lemma norm_comK_le (j₂ j₁ : Ch eta) (q p : Cfg eta N) :
    ‖comK sys L p₀ N n j₂ j₁ q p‖ ≤
      ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q)) (fun d => ¬ InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (yj sys L p₀ N j₁) q p‖ +
      ‖chainK' (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) q p‖ +
      ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) q p‖ := by
  unfold comK
  refine (norm_sub_le _ _).trans ?_
  have := norm_sub_le (chainK (fun q => ¬ InQ (n : ℝ) (cidx N q)) (fun d => ¬ InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (yj sys L p₀ N j₁) q p)
      (chainK' (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) q p)
  linarith

variable (sys L p₀ N n) in
/-- The five chain norms of the word `(j₂, j₁)`. -/
noncomputable def wordN (j₂ j₁ : Ch eta) (q p : Cfg eta N) : ℝ :=
  ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun d => InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (wj sys L N j₁) q p‖ +
    ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) q p‖ +
    ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q)) (fun d => ¬ InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (yj sys L p₀ N j₁) q p‖ +
    ‖chainK' (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) q p‖ +
    ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) q p‖

/-- **The kernel of `b^{FC}` by chains**: `|b^{FC}| ≤ Σ_{j₁, j₂} (five chain norms)`. -/
lemma norm_bfcK_le (hL : 0 < L) (q p : Cfg eta N) :
    ‖bfcK sys L p₀ N n q p‖ ≤ ∑ j₁, ∑ j₂, wordN sys L p₀ N n j₂ j₁ q p := by
  rw [bfcK_eq_sum hL]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j₁ _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j₂ _ => ?_)
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_flK_le (sys := sys) (L := L) (p₀ := p₀) (n := n) j₂ j₁ q p
  have h2 := norm_comK_le (sys := sys) (L := L) (p₀ := p₀) (n := n) j₂ j₁ q p
  unfold wordN
  linarith

end KernelSplit

/-! ## Cauchy–Schwarz over the words -/

section CS

omit [Fintype ν] in
lemma sq_five_le (a b c d e : ℝ) :
    (a + b + c + d + e) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d), sq_nonneg (c - e),
    sq_nonneg (d - e)]

omit [Fintype ν] in
lemma sq_double_sum_le {ι : Type*} [Fintype ι] (T : ι → ι → ℝ) :
    (∑ i, ∑ k, T i k) ^ 2 ≤ (Fintype.card ι : ℝ) ^ 2 * ∑ i, ∑ k, T i k ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun i => ∑ k, T i k)
  have h2 : ∀ i, (∑ k, T i k) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ k, T i k ^ 2 := fun i => by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun k => T i k)
    simpa [Finset.card_univ] using this
  rw [Finset.card_univ] at h1
  have hc : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  calc (∑ i, ∑ k, T i k) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (∑ k, T i k) ^ 2 := by exact_mod_cast h1
    _ ≤ (Fintype.card ι : ℝ) * ∑ i, (Fintype.card ι : ℝ) * ∑ k, T i k ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h2 i) hc
    _ = (Fintype.card ι : ℝ) ^ 2 * ∑ i, ∑ k, T i k ^ 2 := by
        rw [← Finset.mul_sum]; ring

end CS

/-! ## P2: the far–cold dressing against cold inputs -/

section P2

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

variable (sys L) in
/-- The constant of the word `(j₂, j₁)`. -/
noncomputable def Kw (Hunit : ℝ) (N : ℕ) (j₂ j₁ : Ch eta) : ℝ :=
  (2 * KW1 sys L Hunit (chC sys L j₂) (chC sys L j₁ * (1 / cst sys ^ 2)) +
      2 * KL2 sys L Hunit (2048 * mmax sys * chC sys L j₂ / gF L ^ 2) j₁) +
    KW1 sys L Hunit (chC sys L j₂) (chC sys L j₁ * (1 / cst sys ^ 2)) +
    KW1 sys L Hunit (chC sys L j₂) (cY3 sys L j₁) +
    (2 * KY1 sys L N j₂ (chC sys L j₁ * (1 / cst sys ^ 2)) +
      2 * KL2 sys L Hunit (cYb sys L j₂) j₁) +
    KY1 sys L N j₂ (chC sys L j₁ * (1 / cst sys ^ 2))

lemma Kw_nonneg (hL : 0 < L) (Hunit : ℝ) (N : ℕ) (j₂ j₁ : Ch eta) : 0 ≤ Kw sys L Hunit N j₂ j₁ := by
  unfold Kw
  have := KW1_nonneg (sys := sys) hL Hunit (chC sys L j₂) (chC sys L j₁ * (1 / cst sys ^ 2))
  have := KW1_nonneg (sys := sys) hL Hunit (chC sys L j₂) (cY3 sys L j₁)
  have := KY1_nonneg (sys := sys) hL N j₂ (chC sys L j₁ * (1 / cst sys ^ 2))
  have := KL2_nonneg (sys := sys) (L := L) Hunit (2048 * mmax sys * chC sys L j₂ / gF L ^ 2) j₁
  have := KL2_nonneg (sys := sys) (L := L) Hunit (cYb sys L j₂) j₁
  linarith

variable (sys L) in
/-- **The P2 constant** `(160/9) #ch² Σ_{j₁,j₂} K_{j₂ j₁}`. -/
noncomputable def KP2 (Hunit : ℝ) (N : ℕ) : ℝ :=
  160 / 9 * (Fintype.card (Ch eta) : ℝ) ^ 2 * ∑ j₁, ∑ j₂, Kw sys L Hunit N j₂ j₁

lemma KP2_nonneg (hL : 0 < L) (Hunit : ℝ) (N : ℕ) : 0 ≤ KP2 sys L Hunit N := by
  unfold KP2
  have := Finset.sum_nonneg fun j₁ (_ : j₁ ∈ Finset.univ) =>
    Finset.sum_nonneg fun j₂ (_ : j₂ ∈ Finset.univ) => Kw_nonneg (sys := sys) hL Hunit N j₂ j₁
  positivity

/-- **The word sum against cold inputs**: `Σ_f ω_F² (Σ_b wordN x)² ≤ K_w n⁻³ (L²_{j₁} + L²_{j₂})`
(five times the sum of the five chain bounds). -/
theorem word_sq_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit) (hL : 0 < L)
    (hn : 1 ≤ n)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (j₂ j₁ : Ch eta) (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b)
    (hxC : ∀ b, x b ≠ 0 → InC (n : ℝ) (cst sys) (cidx N b)) :
    ∑ f, farW sys L N n f ^ 2 * (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2 ≤
      5 * (Kw sys L Hunit N j₂ j₁ / (n : ℝ) ^ 3 *
        (lineSq j₁ (fun _ => 1) x + lineSq j₂ (fun _ => 1) x)) := by
  classical
  have h1 := P2_ch1 (sys := sys) hH hL hn j₂ j₁ x hx hxC
  have h2 := P2_ch2fl (sys := sys) hH hL hn j₂ j₁ x hx
  have h3 := P2_ch3 (sys := sys) (p₀ := p₀) hH hL hn j₂ j₁ x hx
  have h4 := P2_ch4 (sys := sys) (p₀ := p₀) hH hL hn H hKernel j₂ j₁ x hx hxC
  have h5 := P2_ch2com (sys := sys) (p₀ := p₀) hL hn H hKernel j₂ j₁ x hx
  set S1 := fun f => ∑ b, ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q)) (fun d => InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b
  set S2 := fun f => ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b
  set S3 := fun f => ∑ b, ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q)) (fun d => ¬ InP (n : ℝ) (cidx N d))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (wj sys L N j₂) (yj sys L p₀ N j₁) f b‖ * x b
  set S4 := fun f => ∑ b, ‖chainK' (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b
  set S5 := fun f => ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b
  have hsplit : ∀ f, ∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b = S1 f + S2 f + S3 f + S4 f + S5 f := by
    intro f
    simp only [S1, S2, S3, S4, S5]
    unfold wordN
    simp only [add_mul, Finset.sum_add_distrib]
  have hpt : ∀ f, farW sys L N n f ^ 2 * (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2 ≤
      5 * (farW sys L N n f ^ 2 * S1 f ^ 2 + farW sys L N n f ^ 2 * S2 f ^ 2 +
        farW sys L N n f ^ 2 * S3 f ^ 2 + farW sys L N n f ^ 2 * S4 f ^ 2 +
        farW sys L N n f ^ 2 * S5 f ^ 2) := by
    intro f
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left (sq_five_le (S1 f) (S2 f) (S3 f) (S4 f) (S5 f))
      (sq_nonneg (farW sys L N n f))
    linarith
  refine (Finset.sum_le_sum fun f _ => hpt f).trans ?_
  rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  unfold Kw
  have hD : (0 : ℝ) < (n : ℝ) ^ 3 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  set Lx := lineSq j₁ (fun _ => 1) x + lineSq j₂ (fun _ => 1) x
  have e : ∀ a b c d e : ℝ, (a + b + c + d + e) / (n : ℝ) ^ 3 * Lx =
      a / (n : ℝ) ^ 3 * Lx + b / (n : ℝ) ^ 3 * Lx + c / (n : ℝ) ^ 3 * Lx + d / (n : ℝ) ^ 3 * Lx +
        e / (n : ℝ) ^ 3 * Lx := by
    intro a b c d e; ring
  rw [e]
  linarith

open Classical in
/-- **P2**: `‖Ỹ v‖² ≤ K_{P2} n⁻³ Σ_j L²_j(1_C |v|)`. -/
theorem norm_sq_Yt_cold_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (v : En eta N) :
    ‖FSKernel.kop (ytK sys L N n (bfcK sys L p₀ N n)) v‖ ^ 2 ≤
      KP2 sys L Hunit N / (n : ℝ) ^ 3 *
        ∑ j, lineSq j (fun _ => 1) (fun b => if InC (n : ℝ) (cst sys) (cidx N b) then ‖v.ofLp b‖ else 0) := by
  set x : Cfg eta N → ℝ := fun b => if InC (n : ℝ) (cst sys) (cidx N b) then ‖v.ofLp b‖ else 0 with hxdef
  have hx : ∀ b, 0 ≤ x b := fun b => by
    simp only [hxdef]; split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  have hxC : ∀ b, x b ≠ 0 → InC (n : ℝ) (cst sys) (cidx N b) := fun b hb => by
    by_contra h; apply hb; simp only [hxdef]; rw [if_neg h]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have h0 := norm_sq_kop_ytK_le (sys := sys) hL hn (bfcK sys L p₀ N n) v
  -- the inner sums against `x`
  have hin : ∀ f, (∑ b, if InC (n : ℝ) (cst sys) (cidx N b) then
      ‖bfcK sys L p₀ N n f b‖ * ‖v.ofLp b‖ else 0) = ∑ b, ‖bfcK sys L p₀ N n f b‖ * x b := by
    intro f
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hxdef]
    split_ifs
    · rfl
    · rw [mul_zero]
  have hW : ∀ f, ∑ b, ‖bfcK sys L p₀ N n f b‖ * x b ≤
      ∑ j₁, ∑ j₂, ∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b := by
    intro f
    calc ∑ b, ‖bfcK sys L p₀ N n f b‖ * x b ≤
        ∑ b, (∑ j₁, ∑ j₂, wordN sys L p₀ N n j₂ j₁ f b) * x b :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (norm_bfcK_le hL f b) (hx b)
      _ = ∑ j₁, ∑ j₂, ∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j₁ _ => ?_
          rw [Finset.sum_comm]
  have hpt : ∀ f, (4 / 3 * farW sys L N n f) ^ 2 * (∑ b, ‖bfcK sys L p₀ N n f b‖ * x b) ^ 2 ≤
      16 / 9 * ((Fintype.card (Ch eta) : ℝ) ^ 2 *
        ∑ j₁, ∑ j₂, farW sys L N n f ^ 2 * (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2) := by
    intro f
    have h1 : 0 ≤ ∑ b, ‖bfcK sys L p₀ N n f b‖ * x b :=
      Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hx b)
    have h2 := pow_le_pow_left₀ h1 (hW f) 2
    have h3 := sq_double_sum_le (fun j₁ j₂ => ∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b)
    have h4 := h2.trans h3
    have hf := sq_nonneg (farW sys L N n f)
    have e : ∑ j₁, ∑ j₂, farW sys L N n f ^ 2 * (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2 =
        farW sys L N n f ^ 2 * ∑ j₁, ∑ j₂, (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [Finset.mul_sum]
    rw [e, mul_pow]
    have := mul_le_mul_of_nonneg_left h4 hf
    have e2 : (4 / 3 : ℝ) ^ 2 = 16 / 9 := by norm_num
    rw [e2]
    have e3 : 16 / 9 * ((Fintype.card (Ch eta) : ℝ) ^ 2 * (farW sys L N n f ^ 2 *
        ∑ j₁, ∑ j₂, (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2)) =
        16 / 9 * (farW sys L N n f ^ 2 * ((Fintype.card (Ch eta) : ℝ) ^ 2 *
        ∑ j₁, ∑ j₂, (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2)) := by ring
    rw [e3]
    have e4 : 16 / 9 * farW sys L N n f ^ 2 * (∑ b, ‖bfcK sys L p₀ N n f b‖ * x b) ^ 2 =
        16 / 9 * (farW sys L N n f ^ 2 * (∑ b, ‖bfcK sys L p₀ N n f b‖ * x b) ^ 2) := by ring
    rw [e4]
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  refine h0.trans ?_
  simp only [hin]
  refine (Finset.sum_le_sum fun f _ => hpt f).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  -- swap the sums and apply the word bounds
  have hswap : ∑ f, ∑ j₁, ∑ j₂, farW sys L N n f ^ 2 * (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2 =
      ∑ j₁, ∑ j₂, ∑ f, farW sys L N n f ^ 2 * (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.sum_comm]
  rw [hswap]
  have hT : ∀ j, 0 ≤ lineSq j (fun _ => 1) x := fun j => lineSq_nonneg j (fun _ => zero_le_one) x
  have hLL : ∀ j₁ j₂ : Ch eta, lineSq j₁ (fun _ => 1) x + lineSq j₂ (fun _ => 1) x ≤
      2 * ∑ j, lineSq j (fun _ => 1) x := by
    intro j₁ j₂
    have h1 := Finset.single_le_sum (fun j _ => hT j) (Finset.mem_univ j₁)
    have h2 := Finset.single_le_sum (fun j _ => hT j) (Finset.mem_univ j₂)
    linarith
  have hword : ∀ j₁ j₂, ∑ f, farW sys L N n f ^ 2 * (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2 ≤
      10 * Kw sys L Hunit N j₂ j₁ / (n : ℝ) ^ 3 * ∑ j, lineSq j (fun _ => 1) x := by
    intro j₁ j₂
    refine (word_sq_le hH hL hn H hKernel j₂ j₁ x hx hxC).trans ?_
    have hK := Kw_nonneg (sys := sys) hL Hunit N j₂ j₁
    have := mul_le_mul_of_nonneg_left (hLL j₁ j₂) (div_nonneg hK hD.le)
    have e : 10 * Kw sys L Hunit N j₂ j₁ / (n : ℝ) ^ 3 * ∑ j, lineSq j (fun _ => 1) x =
        5 * (Kw sys L Hunit N j₂ j₁ / (n : ℝ) ^ 3 * (2 * ∑ j, lineSq j (fun _ => 1) x)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  have hsum : ∑ j₁, ∑ j₂, ∑ f, farW sys L N n f ^ 2 * (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2 ≤
      ∑ j₁, ∑ j₂, 10 * Kw sys L Hunit N j₂ j₁ / (n : ℝ) ^ 3 * ∑ j, lineSq j (fun _ => 1) x :=
    Finset.sum_le_sum fun j₁ _ => Finset.sum_le_sum fun j₂ _ => hword j₁ j₂
  have hc : (0 : ℝ) ≤ (Fintype.card (Ch eta) : ℝ) ^ 2 := by positivity
  calc 16 / 9 * ((Fintype.card (Ch eta) : ℝ) ^ 2 *
        ∑ j₁, ∑ j₂, ∑ f, farW sys L N n f ^ 2 * (∑ b, wordN sys L p₀ N n j₂ j₁ f b * x b) ^ 2) ≤
      16 / 9 * ((Fintype.card (Ch eta) : ℝ) ^ 2 *
        ∑ j₁, ∑ j₂, 10 * Kw sys L Hunit N j₂ j₁ / (n : ℝ) ^ 3 * ∑ j, lineSq j (fun _ => 1) x) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hsum hc
    _ = KP2 sys L Hunit N / (n : ℝ) ^ 3 * ∑ j, lineSq j (fun _ => 1) x := by
        have e : ∑ j₁, ∑ j₂, 10 * Kw sys L Hunit N j₂ j₁ / (n : ℝ) ^ 3 * ∑ j, lineSq j (fun _ => 1) x =
            10 / (n : ℝ) ^ 3 * (∑ j, lineSq j (fun _ => 1) x) * ∑ j₁, ∑ j₂, Kw sys L Hunit N j₂ j₁ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j₂ _ => ?_
          ring
        rw [e]
        unfold KP2
        ring

end P2

/-! ## Line squares of good states -/

section GoodLines

variable {sys : CoulombSystem eta ν} {L : ℝ} {N : ℕ}

omit [Fintype ν] in
lemma good_wt_sq_le {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ∑ x, (1 + Asym sys L N x) ^ 2 * ‖u.ofLp x‖ ^ 2 ≤ M ^ 2 := by
  have h := hu.1
  have hW : ‖FSSpectral.wt (sb eta N) (Asym sys L N) 1 u‖ ≤ M := by
    linarith [norm_nonneg u]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hW 2
  rw [norm_sq_wt] at h2
  refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) h2
  rw [Real.rpow_one]

omit [Fintype ν] in
lemma good_M_nonneg {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) : 0 ≤ M := by
  have h := hu.1
  have := norm_nonneg u
  have := norm_nonneg (FSSpectral.wt (sb eta N) (Asym sys L N) 1 u)
  linarith

omit [Fintype ν] in
/-- `w32(ζ) ≤ (1 + |ζ|²)² ≤ 4 c_X² (1 + E)²`. -/
lemma w32_le_wt (hL : 0 < L) {A : Finset (Fin eta)} (hA : A.card ≤ 2) (q : Cfg eta N) :
    w32 (regSum A (cidx N q)) ≤ 4 * cXw sys L ^ 2 * (1 + Asym sys L N q) ^ 2 := by
  have h1 := one_add_lsq_regSum_le (sys := sys) hL hA q
  set l := 1 + FSLattice.lsq (regSum A (cidx N q)) with hl
  have hl1 : 1 ≤ l := by have := FSLattice.lsq_nonneg (regSum A (cidx N q)); linarith
  have hs : Real.sqrt l ≤ l := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hw : w32 (regSum A (cidx N q)) = l * Real.sqrt l := rfl
  rw [hw]
  have h2 : l * Real.sqrt l ≤ l * l := mul_le_mul_of_nonneg_left hs (by linarith)
  have h3 : l * l ≤ (2 * (cXw sys L * (1 + Asym sys L N q))) ^ 2 := by
    rw [← sq]; exact pow_le_pow_left₀ (by linarith) h1 2
  have e : (2 * (cXw sys L * (1 + Asym sys L N q))) ^ 2 =
      4 * cXw sys L ^ 2 * (1 + Asym sys L N q) ^ 2 := by ring
  linarith

omit [Fintype ν] in
open Classical in
/-- **Line squares of a good state** on any region: `L²_j(1_S |u|) ≤ 125 (log₂ 2N + 2) 4 c_X² M²`. -/
theorem lineSq_good_le (hL : 0 < L) (hN : 1 ≤ N) {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u)
    (S : Cfg eta N → Prop) (j : Ch eta) :
    lineSq j (fun _ => 1) (fun b => if S b then ‖u.ofLp b‖ else 0) ≤
      125 * (Nat.log 2 (2 * N) + 2) * (4 * cXw sys L ^ 2 * M ^ 2) := by
  have h := lineSq_le j (fun _ => zero_le_one) (fun b => if S b then ‖u.ofLp b‖ else 0)
    (fun p => w32 (regSum {lead j} (cidx N p))) (fun p => w32_pos _)
    (fun q => lineSum_inv_w32_le hN (coord_lead j) q)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hwt := good_wt_sq_le hu
  calc ∑ p, (1 : ℝ) * w32 (regSum {lead j} (cidx N p)) * (if S p then ‖u.ofLp p‖ else 0) ^ 2 ≤
      ∑ p, 4 * cXw sys L ^ 2 * ((1 + Asym sys L N p) ^ 2 * ‖u.ofLp p‖ ^ 2) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have h1 := w32_le_wt (sys := sys) hL (coord_lead j).card p
        have hw0 := (w32_pos (regSum {lead j} (cidx N p))).le
        have h2 : (if S p then ‖u.ofLp p‖ else 0) ^ 2 ≤ ‖u.ofLp p‖ ^ 2 := by
          split_ifs
          · exact le_rfl
          · rw [sq, mul_zero]; exact sq_nonneg _
        rw [one_mul]
        calc w32 (regSum {lead j} (cidx N p)) * (if S p then ‖u.ofLp p‖ else 0) ^ 2 ≤
            (4 * cXw sys L ^ 2 * (1 + Asym sys L N p) ^ 2) * ‖u.ofLp p‖ ^ 2 :=
              mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
          _ = _ := by ring
    _ = 4 * cXw sys L ^ 2 * ∑ p, (1 + Asym sys L N p) ^ 2 * ‖u.ofLp p‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 4 * cXw sys L ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hwt (by positivity)

end GoodLines

/-! ## P2 for good states -/

section P2Good

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

/-- **P2 for a good box state**:
`‖Ỹ u‖² ≤ K_{P2} n⁻³ #ch 125 (log₂ 2N + 2) 4 c_X² M²`. -/
theorem norm_sq_Yt_good_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) (hN : 1 ≤ N)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) :
    ‖FSKernel.kop (ytK sys L N n (bfcK sys L p₀ N n)) u‖ ^ 2 ≤
      KP2 sys L Hunit N / (n : ℝ) ^ 3 * ((Fintype.card (Ch eta) : ℝ) *
        (125 * (Nat.log 2 (2 * N) + 2) * (4 * cXw sys L ^ 2 * M ^ 2))) := by
  classical
  refine (norm_sq_Yt_cold_le hH hL hn H hKernel u).trans ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (KP2_nonneg hL Hunit N) (by positivity))
  calc ∑ j, lineSq j (fun _ => 1)
        (fun b => if InC (n : ℝ) (cst sys) (cidx N b) then ‖u.ofLp b‖ else 0) ≤
      ∑ _j : Ch eta, 125 * (Nat.log 2 (2 * N) + 2) * (4 * cXw sys L ^ 2 * M ^ 2) :=
        Finset.sum_le_sum fun j _ =>
          lineSq_good_le hL hN hu (fun b => InC (n : ℝ) (cst sys) (cidx N b)) j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end P2Good

end FSFlux
