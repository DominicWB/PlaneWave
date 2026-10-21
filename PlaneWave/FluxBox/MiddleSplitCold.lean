import PlaneWave.FluxBox.WordsGoodStates

/-!
# Flux route, stage 3, part 45: the `C × C` block — the middle-split words on cold inputs

* `pi_const_or_shared`: the pair momentum `π_{j₂}` is conserved by the hops of `j₁`, or `j₂` is a pair
  sharing exactly one register with `j₁` (the shared com words of `PlaneWave.FluxBox.SharedComCoordinate`–`PlaneWave.FluxBox.SharedComCases`);
* `GoodX`: the line-square bounds of a cold input (`goodX_res`: the cold part of a good state);
* the trilinear form `TriF x h = Σ_f G(f) ω_F(f) h(f)`, `G = 1_F Σ_{j₃} |W_{j₃}| x`, and the middle split
  on cold inputs (`tri_mid`: `TriF x h ≤ (Γ₀ + Φ)/(2n³)` when `n⁵ Σ_f ω_F² h² ≤ Φ`);
* the middle-split words: `tri_ch3` (M3), `tri_ch4S` (M4), `tri_ch1` (M1), `tri_ch2fl` (M2),
  `tri_ch4L_ns` (M5).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section PiConst

omit [Fintype ν] in
/-- **The pair momentum along a hop**: `π_{j₂}` is conserved by the hops of `j₁`, or `j₂ = (a, t)`
with `a` moved by `j₁` and `t` not. -/
lemma pi_const_or_shared (j₁ j₂ : Ch eta) :
    (∀ (k : Cf eta) (τ : Lattice3), piC j₂ (k + tr j₁ τ) = piC j₂ k) ∨
    (∃ (pr : FiniteElectronPair eta) (a t : Fin eta), j₂ = .inr pr ∧ a ∈ moved (.inr pr : Ch eta) ∧
      t ∈ moved (.inr pr : Ch eta) ∧ a ≠ t ∧ a ∈ moved j₁ ∧ t ∉ moved j₁) := by
  classical
  cases j₂ with
  | inl c => exact Or.inl fun k τ => rfl
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    have h1 : pr.1.1 ∈ moved (.inr pr : Ch eta) := by simp [moved]
    have h2 : pr.1.2 ∈ moved (.inr pr : Ch eta) := by simp [moved]
    by_cases ha : pr.1.1 ∈ moved j₁
    · by_cases hb : pr.1.2 ∈ moved j₁
      · left
        have hj : j₁ = .inr pr := by
          apply moved_inj
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro z hz
            simp only [moved, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact ha
            · exact hb
          · rw [card_moved_pair]; exact card_moved_le j₁
        subst hj
        intro k τ
        exact piC_hop _ k τ
      · exact Or.inr ⟨pr, pr.1.1, pr.1.2, rfl, h1, h2, hne, ha, hb⟩
    · by_cases hb : pr.1.2 ∈ moved j₁
      · exact Or.inr ⟨pr, pr.1.2, pr.1.1, rfl, h2, h1, hne.symm, hb, ha⟩
      · left
        intro k τ
        simp only [piC, Pi.add_apply, tr_apply_not_moved j₁ τ ha, tr_apply_not_moved j₁ τ hb,
          add_zero]

end PiConst

/-! ## Cold inputs -/

section GoodX

/-- **The line-square bounds of a cold input** used by the `C × C` words. -/
structure GoodX (sys : CoulombSystem eta ν) (n : ℕ) {N : ℕ} (x : Cfg eta N → ℝ) (B₁ Bπ Bc : ℝ) :
    Prop where
  nonneg : ∀ b, 0 ≤ x b
  cold : ∀ b, x b ≠ 0 → InC (n : ℝ) (cst sys) (cidx N b)
  h1 : 0 ≤ B₁
  hπ : 0 ≤ Bπ
  hc : 0 ≤ Bc
  one : ∀ j : Ch eta, lineSq j (fun _ => 1) x ≤ B₁
  pi : ∀ j j' : Ch eta, lineSq j (fun _ => 1) (fun b => piC j' (cidx N b) * x b) ≤ Bπ
  coord : ∀ (j : Ch eta) (A : Finset (Fin eta)), A.card ≤ 2 → (∀ σ, regSum A (tr j σ) = 0) →
    lineSq j (fun s => 1 + FSLattice.lsq (regSum A s)) x ≤ Bc
  fibre : ∀ a t : Fin eta, ∑ c, w32 (cidx N c a) * (1 + FSLattice.lsq (cidx N c t)) * x c ^ 2 ≤ Bc

variable {sys : CoulombSystem eta ν} {L : ℝ} {N : ℕ}

omit [Fintype ν] in
/-- **The cold part of a good state is a good cold input**, with
`B₁ = B_ψ(1)`, `B_π = B_ψ(4m/g²)`, `B_c = B_ψ(2c_X)`. -/
theorem goodX_res (hL : 0 < L) (hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u) (n : ℕ) :
    GoodX sys n (fun c => ‖(FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u).ofLp c‖)
      (Bpsi sys L N nd M 1) (Bpsi sys L N nd M (4 * mmax sys / gF L ^ 2))
      (Bpsi sys L N nd M (2 * cXw sys L)) := by
  classical
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hc := cXw_ge_one (sys := sys) hL
  have e : (fun c => ‖(FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u).ofLp c‖) =
      fun c => if InC (n : ℝ) (cst sys) (cidx N c) then ‖u.ofLp c‖ else 0 := by
    funext c; rw [FSKernel.res_apply]; split_ifs <;> simp
  rw [e]
  refine ⟨fun b => ?_, fun b hb => ?_, Bpsi_nonneg hL N nd M zero_le_one,
    Bpsi_nonneg hL N nd M (by positivity), Bpsi_nonneg hL N nd M (by positivity),
    fun j => ?_, fun j j' => ?_, fun j A hA hAj => ?_, fun a t => ?_⟩
  · dsimp only
    split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  · by_contra h
    apply hb
    dsimp only
    rw [if_neg h]
  · exact good_C_one hL hN hnd hu _ j
  · exact good_C_pi hL hN hnd hu _ j j'
  · exact good_C_coord hL hN hnd hu _ j hA hAj
  · exact good_C_fibre hL hN hnd hu _ a t

end GoodX

/-! ## The trilinear form and the middle split -/

section Tri

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

variable (sys L N n) in
open Classical in
/-- The outer side `G(f) = 1_F(f) Σ_{j₃} Σ_c |w_{j₃}(f,c)| x_c`. -/
noncomputable def Gout (x : Cfg eta N → ℝ) (f : Cfg eta N) : ℝ :=
  if InQ (n : ℝ) (cidx N f) then 0 else ∑ j₃, ∑ c, ‖wj sys L N j₃ f c‖ * x c

variable (sys L N n) in
/-- The trilinear form `Tri(h) = Σ_f G(f) ω_F(f) h(f)`. -/
noncomputable def TriF (x h : Cfg eta N → ℝ) : ℝ :=
  ∑ f, Gout sys L N n x f * farW sys L N n f * h f

lemma Gout_nonneg {x : Cfg eta N → ℝ} (hx : ∀ b, 0 ≤ x b) (f : Cfg eta N) :
    0 ≤ Gout sys L N n x f := by
  unfold Gout
  split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg fun j₃ _ => Finset.sum_nonneg fun c _ => mul_nonneg (norm_nonneg _) (hx c)

lemma TriF_mono {x : Cfg eta N → ℝ} (hx : ∀ b, 0 ≤ x b) {h h' : Cfg eta N → ℝ}
    (hh : ∀ f, h f ≤ h' f) : TriF sys L N n x h ≤ TriF sys L N n x h' := by
  unfold TriF
  exact Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (hh f)
    (mul_nonneg (Gout_nonneg hx f) (farW_nonneg f))

lemma TriF_nonneg {x : Cfg eta N → ℝ} (hx : ∀ b, 0 ≤ x b) {h : Cfg eta N → ℝ} (hh : ∀ f, 0 ≤ h f) :
    0 ≤ TriF sys L N n x h := by
  unfold TriF
  exact Finset.sum_nonneg fun f _ => mul_nonneg (mul_nonneg (Gout_nonneg hx f) (farW_nonneg f)) (hh f)

lemma TriF_sum {ι : Type*} (s : Finset ι) (x : Cfg eta N → ℝ) (h : ι → Cfg eta N → ℝ) :
    TriF sys L N n x (fun f => ∑ i ∈ s, h i f) = ∑ i ∈ s, TriF sys L N n x (h i) := by
  unfold TriF
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]

lemma TriF_le4 {x : Cfg eta N → ℝ} (hx : ∀ b, 0 ≤ x b) {H a b c d : Cfg eta N → ℝ}
    (hpt : ∀ f, H f ≤ a f + b f + c f + d f) :
    TriF sys L N n x H ≤
      TriF sys L N n x a + TriF sys L N n x b + TriF sys L N n x c + TriF sys L N n x d := by
  refine (TriF_mono hx hpt).trans (le_of_eq ?_)
  unfold TriF
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

lemma TriF_le6 {x : Cfg eta N → ℝ} (hx : ∀ b, 0 ≤ x b) {H a b c d e g : Cfg eta N → ℝ}
    (hpt : ∀ f, H f ≤ a f + b f + c f + d f + e f + g f) :
    TriF sys L N n x H ≤
      TriF sys L N n x a + TriF sys L N n x b + TriF sys L N n x c + TriF sys L N n x d +
        TriF sys L N n x e + TriF sys L N n x g := by
  refine (TriF_mono hx hpt).trans (le_of_eq ?_)
  unfold TriF
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

open Classical in
/-- `Tri` by outer channels. -/
lemma TriF_eq_sum (x h : Cfg eta N → ℝ) :
    TriF sys L N n x h = ∑ j₃, ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else
      ∑ c, ‖wj sys L N j₃ f c‖ * x c) * farW sys L N n f * h f := by
  unfold TriF Gout
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  congr 2
  split_ifs
  · simp
  · rfl

variable (sys L) in
/-- The outer constant `Γ₀ = #ch Σ_{j₃} (64 c₃)² 277 B₁`. -/
noncomputable def GamC (B₁ : ℝ) : ℝ :=
  (Fintype.card (Ch eta) : ℝ) * ∑ j₃ : Ch eta, (64 * chC sys L j₃) ^ 2 * 277 * B₁

lemma GamC_nonneg (hL : 0 < L) {B₁ : ℝ} (hB : 0 ≤ B₁) : 0 ≤ GamC sys L B₁ := by
  unfold GamC
  refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j₃ _ => ?_)
  have := chC_nonneg sys hL j₃
  positivity

omit [Fintype ν] in
lemma cc_n5_div_mul {m : ℝ} (hm : 0 < m) (K X : ℝ) : m ^ 5 * (K / m ^ 5 * X) = K * X := by
  field_simp

/-- **The middle split on cold inputs**: if `n⁵ Σ_f ω_F² h² ≤ Φ`, then `Tri(h) ≤ (Γ₀ + Φ)/(2n³)`. -/
theorem tri_mid (hL : 0 < L) (hn : 1 ≤ n) {x : Cfg eta N → ℝ} {B₁ Bπ Bc : ℝ}
    (hX : GoodX sys n x B₁ Bπ Bc) (h : Cfg eta N → ℝ) (hh : ∀ f, 0 ≤ h f) {Φ : ℝ}
    (hΦ : (n : ℝ) ^ 5 * ∑ f, farW sys L N n f ^ 2 * h f ^ 2 ≤ Φ) :
    TriF sys L N n x h ≤ (GamC sys L B₁ + Φ) / 2 / (n : ℝ) ^ 3 := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hms := middle_split_le Finset.univ (Gout sys L N n x) (farW sys L N n) h
    (Gout_nonneg hX.nonneg) (fun f => farW_nonneg f) hh hn0
  have hGs : ∑ f, Gout sys L N n x f ^ 2 ≤ (Fintype.card (Ch eta) : ℝ) *
      ∑ j₃, (64 * chC sys L j₃) ^ 2 * (277 / n) * lineSq j₃ (fun _ => 1) x :=
    sum_G_sq_le (sys := sys) hL hn x hX.nonneg hX.cold
  have hΓ : (n : ℝ) * ∑ f, Gout sys L N n x f ^ 2 ≤ GamC sys L B₁ := by
    refine (mul_le_mul_of_nonneg_left hGs hn0.le).trans ?_
    unfold GamC
    rw [mul_left_comm, Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    refine Finset.sum_le_sum fun j₃ _ => ?_
    have hc := chC_nonneg sys hL j₃
    have e : (n : ℝ) * ((64 * chC sys L j₃) ^ 2 * (277 / n) * lineSq j₃ (fun _ => 1) x) =
        (64 * chC sys L j₃) ^ 2 * 277 * lineSq j₃ (fun _ => 1) x := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left (hX.one j₃) (by positivity)
  unfold TriF
  refine hms.trans ?_
  rw [div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

end Tri

/-! ## The middle-split words -/

section Words

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

/-- **M3** (`Ch3`) on cold inputs. -/
theorem tri_ch3 {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {x : Cfg eta N → ℝ} {B₁ Bπ Bc : ℝ} (hX : GoodX sys n x B₁ Bπ Bc)
    (j₂ j₁ : Ch eta) :
    TriF sys L N n x (fun f => ∑ b, ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (yj sys L p₀ N j₁) f b‖ * x b) ≤
      (GamC sys L B₁ + KW1 sys L Hunit (chC sys L j₂) (cY3' sys L j₁) * Bπ) / 2 / (n : ℝ) ^ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine tri_mid hL hn hX _
    (fun f => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hX.nonneg b)) ?_
  have h := Phi_ch3 (sys := sys) (p₀ := p₀) hH hL hn j₂ j₁ x hX.nonneg
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  rw [cc_n5_div_mul hn0]
  exact mul_le_mul_of_nonneg_left (hX.pi j₁ j₁) (KW1_nonneg hL _ _ _)

variable (sys L) in
/-- The M4 constant: `(8 c_Y)² 277 ((26 c_* c₁)² B_π + (4 c_*)² c₁² H² B_c)`. -/
noncomputable def KC4S (Hunit : ℝ) (j₂ j₁ : Ch eta) (Bπ Bc : ℝ) : ℝ :=
  (8 * cYb sys L j₂) ^ 2 * 277 * (26 * cst sys * chC sys L j₁) ^ 2 * Bπ +
    (8 * cYb sys L j₂) ^ 2 * 277 * (4 * cst sys) ^ 2 * (chC sys L j₁ ^ 2 * (Hunit ^ 2 * Bc))

open Classical in
/-- **M4** (the short first hop then the com hop) on cold inputs. -/
theorem tri_ch4S {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {x : Cfg eta N → ℝ} {B₁ Bπ Bc : ℝ} (hX : GoodX sys n x B₁ Bπ Bc)
    (j₂ j₁ : Ch eta) :
    TriF sys L N n x (fun f => ∑ d, (if ¬ InP (n : ℝ) (cidx N f) then ‖yj sys L p₀ N j₂ f d‖ else 0) *
        ∑ b, WS sys L N n j₁ d b * x b) ≤
      (GamC sys L B₁ + KC4S sys L Hunit j₂ j₁ Bπ Bc) / 2 / (n : ℝ) ^ 3 := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine tri_mid hL hn hX _ (fun f => Finset.sum_nonneg fun d _ => mul_nonneg
    (by split_ifs <;> first | exact norm_nonneg _ | exact le_rfl)
    (Finset.sum_nonneg fun b _ => mul_nonneg (WS_nonneg hL j₁ d b) (hX.nonneg b))) ?_
  have hY := cYb_nonneg (sys := sys) hL j₂
  have hc₁ := chC_nonneg sys hL j₁
  have hcs := cst_pos sys
  have hP0 : 0 ≤ (8 * cYb sys L j₂) ^ 2 * 277 * (26 * cst sys * chC sys L j₁) ^ 2 * Bπ :=
    mul_nonneg (by positivity) hX.hπ
  have hP1 : 0 ≤ (8 * cYb sys L j₂) ^ 2 * 277 * (4 * cst sys) ^ 2 *
      (chC sys L j₁ ^ 2 * (Hunit ^ 2 * Bc)) :=
    mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hX.hc))
  unfold KC4S
  by_cases hj : j₂ = j₁
  · rw [hj] at hP0 hP1 ⊢
    have h := Phi_ch4_short_same (sys := sys) (p₀ := p₀) hL hn j₁ x hX.nonneg
    refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
    rw [cc_n5_div_mul hn0]
    have := mul_le_mul_of_nonneg_left (hX.pi j₁ j₁)
      (show 0 ≤ (8 * cYb sys L j₁) ^ 2 * 277 * (26 * cst sys * chC sys L j₁) ^ 2 by positivity)
    linarith
  · obtain ⟨A₁, ε₁, hA₁, hA₁k⟩ := exists_coord_ne (Ne.symm hj)
    have h := Phi_ch4_short_cross (sys := sys) (p₀ := p₀) hH hL hn hA₁ hA₁k x hX.nonneg
    refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
    rw [cc_n5_div_mul hn0]
    have hc := hX.coord j₂ A₁ hA₁.card hA₁k
    have : (8 * cYb sys L j₂) ^ 2 * 277 * (4 * cst sys) ^ 2 * (chC sys L j₁ ^ 2 *
        (Hunit ^ 2 * lineSq j₂ (fun s => 1 + FSLattice.lsq (regSum A₁ s)) x)) ≤
        (8 * cYb sys L j₂) ^ 2 * 277 * (4 * cst sys) ^ 2 * (chC sys L j₁ ^ 2 * (Hunit ^ 2 * Bc)) := by
      gcongr
    linarith

variable (sys L) in
/-- The M1 constant. -/
noncomputable def KC1 (Hunit : ℝ) (j₂ j₁ : Ch eta) (Bc : ℝ) : ℝ :=
  2 * ((32 * mmax sys * chC sys L j₂ * chC sys L j₁ / (gF L ^ 2 * cst sys ^ 2)) ^ 2 * 277 *
      Hunit ^ 2 * Bc) +
    2 * ((2048 * mmax sys * chC sys L j₂ / gF L ^ 2) ^ 2 * 277 * (chC sys L j₁ ^ 2 * (Hunit ^ 2 * Bc)))

omit [Fintype ν] in
lemma cc_n5_two {m : ℝ} (hm : 0 < m) (K₁ X₁ K₂ X₂ : ℝ) :
    m ^ 5 * (2 * (K₁ / m ^ 5 * X₁) + 2 * (K₂ * (277 / m ^ 5) * X₂)) =
      2 * (K₁ * X₁) + 2 * (K₂ * 277 * X₂) := by
  field_simp

/-- **M1** (flat mixed `Ch1`, `j₂ ≠ j₁`) on cold inputs. -/
theorem tri_ch1 {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {x : Cfg eta N → ℝ} {B₁ Bπ Bc : ℝ} (hX : GoodX sys n x B₁ Bπ Bc)
    {j₂ j₁ : Ch eta} (hj : j₂ ≠ j₁) :
    TriF sys L N n x (fun f => ∑ b, ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun d => InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b) ≤
      (GamC sys L B₁ + KC1 sys L Hunit j₂ j₁ Bc) / 2 / (n : ℝ) ^ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine tri_mid hL hn hX _
    (fun f => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hX.nonneg b)) ?_
  obtain ⟨A₁, ε₁, hA₁, hA₁k⟩ := exists_coord_ne hj.symm
  obtain ⟨A₂, ε₂, hA₂, hA₂k⟩ := exists_coord_ne hj
  have h := Phi_ch1_mixed (sys := sys) hH hL hn hA₁ hA₁k hA₂ hA₂k x hX.nonneg
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  have hc1 := hX.coord j₁ A₂ hA₂.card hA₂k
  have hc2 := hX.coord j₂ A₁ hA₁.card hA₁k
  rw [cc_n5_two hn0]
  unfold KC1
  have := gF_pos hL
  have := cst_pos sys
  gcongr

variable (sys L) in
/-- The M2 constant. -/
noncomputable def KC2 (Hunit : ℝ) (j₂ j₁ : Ch eta) (Bc : ℝ) : ℝ :=
  (32 * mmax sys * chC sys L j₂ * chC sys L j₁ / (gF L ^ 2 * cst sys ^ 2)) ^ 2 * 277 * Hunit ^ 2 * Bc

/-- **M2** (flat mixed `Ch2`, `j₂ ≠ j₁`) on cold inputs. -/
theorem tri_ch2fl {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {x : Cfg eta N → ℝ} {B₁ Bπ Bc : ℝ} (hX : GoodX sys n x B₁ Bπ Bc)
    {j₂ j₁ : Ch eta} (hj : j₂ ≠ j₁) :
    TriF sys L N n x (fun f => ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b) ≤
      (GamC sys L B₁ + KC2 sys L Hunit j₂ j₁ Bc) / 2 / (n : ℝ) ^ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine tri_mid hL hn hX _
    (fun f => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hX.nonneg b)) ?_
  obtain ⟨A₂, ε₂, hA₂, hA₂k⟩ := exists_coord_ne hj
  have h := Phi_ch2fl_mixed (sys := sys) hH hL hn hA₂ hA₂k x hX.nonneg
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  rw [cc_n5_div_mul hn0]
  unfold KC2
  exact mul_le_mul_of_nonneg_left (hX.coord j₁ A₂ hA₂.card hA₂k) (by positivity)

/-- **M5** (the long first hop then the com hop, `π₂` constant on the `j₁`-lines) on cold inputs. -/
theorem tri_ch4L_ns (hL : 0 < L) (hn : 1 ≤ n)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {x : Cfg eta N → ℝ} {B₁ Bπ Bc : ℝ} (hX : GoodX sys n x B₁ Bπ Bc) (j₂ j₁ : Ch eta)
    (hπ : ∀ (k : Cf eta) (τ : Lattice3), piC j₂ (k + tr j₁ τ) = piC j₂ k) :
    TriF sys L N n x (fun f => ∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ≤
      (GamC sys L B₁ + KY1 sys L N j₂ (chC sys L j₁ * (1 / cst sys ^ 2)) * Bπ) / 2 /
        (n : ℝ) ^ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine tri_mid hL hn hX _ (fun f => Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun b _ => mul_nonneg (WL_nonneg hL j₁ d b) (hX.nonneg b))) ?_
  have h := Phi_y_long_ns (sys := sys) (p₀ := p₀) hL hn H hKernel j₂ j₁ hπ x hX.nonneg
  refine (mul_le_mul_of_nonneg_left h (by positivity)).trans ?_
  rw [cc_n5_div_mul hn0]
  exact mul_le_mul_of_nonneg_left (hX.pi j₁ j₂) (KY1_nonneg hL _ _ _)

end Words

end FSFlux
