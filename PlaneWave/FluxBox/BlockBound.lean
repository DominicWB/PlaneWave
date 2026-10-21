import PlaneWave.FluxBox.MiddleSplitCold

/-!
# Flux route, stage 3, part 46: the `C × C` block — the shared words, the rest and the block bound

* the shared com words on cold inputs: a common coordinate (`tri_shared_X`, constant `KCsh`) or the
  degenerate case (`tri_deg_X`, constant `KCdeg`, from `kap0_Kfib_le`: `κ₀ K_fib ≤ KCdeg/n³`);
* the long com word `R Y₂ W₁^L` (`tri_ch4L`): `π₂` conserved on the `j₁`-lines (M5) or shared;
* the rest word `(j₂, j₁)` (`tri_rword_le`) and **the rest of the C×C pairing** (`cc_rest_le`:
  `|⟨W v, Ỹ_r v⟩| ≤ KCrest/n³` for a good cold input `v`);
* **the C×C block of a good state** (`abs_im_CC_good_le`):
  `|Im⟨W u_C, Ỹ u_C⟩| ≤ KCC/n³`, `KCC = Σ_j K_ss B_ss/2 + KCrest` (`≲ log² N M² (1 + η n_d)`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

section Shared

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

variable (sys L) in
/-- The constant of a shared com word with a common coordinate. -/
noncomputable def KCsh (Hunit : ℝ) (j₁ j₂ j₃ : Ch eta) : ℝ :=
  ((64 * chC sys L j₃) ^ 2 * 277 + (32 * mmax sys / gF L ^ 2) ^ 2 *
    (chC sys L j₁ * (1 / cst sys ^ 2)) ^ 2 * 277 *
      (36 * chC sys L j₂ ^ 2 * Hunit ^ 2 + 2 * (chC sys L j₂ / 2) ^ 2 * (32 ^ 2 * Hunit ^ 4))) / 2

lemma KCsh_nonneg (hL : 0 < L) (Hunit : ℝ) (j₁ j₂ j₃ : Ch eta) :
    0 ≤ KCsh sys L Hunit j₁ j₂ j₃ := by
  unfold KCsh
  have := gF_pos hL
  have := cst_pos sys
  positivity

omit [Fintype ν] in
lemma cc_alg_shared {m : ℝ} (hm : 0 < m) {a b c d₁ d₂ X₃ X₁ X₂ B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (h3 : X₃ ≤ B) (h1 : X₁ ≤ B) (h2 : X₂ ≤ B) :
    (m * (a * (277 / m) * X₃) + m ^ 5 * (b / m ^ 4 * (c * (277 / m)) * (d₁ * X₁ + d₂ * X₂))) /
        (2 * m ^ 3) ≤ (a * 277 + b * c * 277 * (d₁ + d₂)) / 2 * B / m ^ 3 := by
  have e : (m * (a * (277 / m) * X₃) + m ^ 5 * (b / m ^ 4 * (c * (277 / m)) * (d₁ * X₁ + d₂ * X₂))) /
      (2 * m ^ 3) = (a * 277 * X₃ + b * c * 277 * (d₁ * X₁ + d₂ * X₂)) / 2 / m ^ 3 := by
    field_simp
  rw [e]
  have e2 : (a * 277 + b * c * 277 * (d₁ + d₂)) / 2 * B / m ^ 3 =
      (a * 277 * B + b * c * 277 * (d₁ * B + d₂ * B)) / 2 / m ^ 3 := by ring
  rw [e2]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by norm_num)
  gcongr

open Classical in
/-- **A shared com word with a common coordinate**, on cold inputs. -/
theorem tri_shared_X {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {j₁ j₂ j₃ : Ch eta} {t : Fin eta} (ht : t ∈ moved j₂)
    (ht1 : t ∉ moved j₁) {A : Finset (Fin eta)} {ε : ℤ} (hA : IsCoord j₂ A ε)
    (hA1 : ∀ σ, regSum A (tr j₁ σ) = 0) (hA3 : ∀ σ, regSum A (tr j₃ σ) = 0)
    {x : Cfg eta N → ℝ} {B₁ Bπ Bc : ℝ} (hX : GoodX sys n x B₁ Bπ Bc) :
    ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else ∑ c, ‖wj sys L N j₃ f c‖ * x c) *
        farW sys L N n f * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ≤
      KCsh sys L Hunit j₁ j₂ j₃ * Bc / (n : ℝ) ^ 3 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine (tri_shared_le (p₀ := p₀) hH hL hn ht ht1 hA hA1 hA3 x hX.nonneg hX.cold).trans ?_
  have h3 := hX.coord j₃ A hA.card hA3
  have h1t := hX.coord j₁ {t} (by simp) (regSum_single_tr_zero j₁ ht1)
  have h1A := hX.coord j₁ A hA.card hA1
  have hg := gF_pos hL
  have hcs := cst_pos sys
  unfold KCsh
  exact cc_alg_shared hn0 (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) h3 h1t h1A

variable (sys L) in
/-- The constant of a degenerate shared com word. -/
noncomputable def KCdeg (N : ℕ) (j₁ j₂ j₃ : Ch eta) : ℝ :=
  32 * mmax sys / gF L ^ 2 * (chC sys L j₁ / cst sys ^ 2) * chC sys L j₃ *
    (17728 * chC sys L j₂ + chC sys L j₂ * LamS (2 * N)) * (250 * (Nat.log 2 (2 * N) + 2))

lemma KCdeg_nonneg (hL : 0 < L) (N : ℕ) (j₁ j₂ j₃ : Ch eta) : 0 ≤ KCdeg sys L N j₁ j₂ j₃ := by
  unfold KCdeg
  have := gF_pos hL
  have := cst_pos sys
  have := chC_nonneg sys hL j₁
  have := chC_nonneg sys hL j₂
  have := chC_nonneg sys hL j₃
  have := LamS_nonneg (2 * N)
  have := one_le_mmax sys
  positivity

/-- **The degenerate constant**: `κ₀ K_fib ≤ KCdeg/n³` for `1 ≤ n ≤ N`. -/
lemma kap0_Kfib_le (hL : 0 < L) (hn : 1 ≤ n) (hnN : n ≤ N) (j₁ j₂ j₃ : Ch eta) :
    kap0 sys L N n j₁ j₂ j₃ * Kfib sys n ≤ KCdeg sys L N j₁ j₂ j₃ / (n : ℝ) ^ 3 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hcs := cst_pos sys
  have hc32 := cst_le32 sys
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hc₁ := chC_nonneg sys hL j₁
  have hc₂ := chC_nonneg sys hL j₂
  have hc₃ := chC_nonneg sys hL j₃
  have hLS := LamS_nonneg (2 * N)
  have hbr : 4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) * (277 / ((n : ℝ) / 8)) +
      chC sys L j₂ * LamS (2 * N) ≤ 17728 * chC sys L j₂ + chC sys L j₂ * LamS (2 * N) := by
    have h1 : (1 + 3 * (cst sys * n)) * (277 / ((n : ℝ) / 8)) ≤ 4432 := by
      have e : (1 + 3 * (cst sys * n)) * (277 / ((n : ℝ) / 8)) =
          2216 * (1 + 3 * (cst sys * n)) / n := by
        field_simp
        ring
      rw [e, div_le_iff₀ hn0]
      nlinarith
    have h2 : 4 * chC sys L j₂ * (1 + 3 * (cst sys * n)) * (277 / ((n : ℝ) / 8)) ≤
        4 * chC sys L j₂ * 4432 := by
      rw [mul_assoc (4 * chC sys L j₂)]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hlog : (Nat.log 2 (⌊cst sys * n⌋₊ + 1) : ℝ) ≤ Nat.log 2 (2 * N) := by
    have hfl : ⌊cst sys * n⌋₊ + 1 ≤ 2 * N := by
      have h1 : (⌊cst sys * n⌋₊ : ℝ) ≤ cst sys * n := Nat.floor_le (by positivity)
      have h3 : (⌊cst sys * n⌋₊ : ℝ) ≤ N := by
        have : (n : ℝ) ≤ N := by exact_mod_cast hnN
        nlinarith
      have h4 : ⌊cst sys * n⌋₊ ≤ N := by exact_mod_cast h3
      omega
    exact_mod_cast Nat.log_mono_right hfl
  have hfib : Kfib sys n ≤ 250 * ((Nat.log 2 (2 * N) : ℝ) + 2) * n := by
    unfold Kfib
    have h1 : 1 + 26 * (cst sys * n) ≤ 2 * n := by nlinarith
    calc 125 * ((Nat.log 2 (⌊cst sys * n⌋₊ + 1) : ℝ) + 2) * (1 + 26 * (cst sys * n)) ≤
        125 * ((Nat.log 2 (2 * N) : ℝ) + 2) * (2 * n) := by
          apply mul_le_mul _ h1 (by positivity) (by positivity)
          linarith
      _ = 250 * ((Nat.log 2 (2 * N) : ℝ) + 2) * n := by ring
  have hk : kap0 sys L N n j₁ j₂ j₃ ≤ 32 * mmax sys / gF L ^ 2 / (n : ℝ) ^ 2 *
      (chC sys L j₁ / (cst sys * n) ^ 2) * chC sys L j₃ *
      (17728 * chC sys L j₂ + chC sys L j₂ * LamS (2 * N)) := by
    unfold kap0
    exact mul_le_mul_of_nonneg_left hbr (by positivity)
  have hK0 := Kfib_nonneg (sys := sys) n
  calc kap0 sys L N n j₁ j₂ j₃ * Kfib sys n ≤ (32 * mmax sys / gF L ^ 2 / (n : ℝ) ^ 2 *
      (chC sys L j₁ / (cst sys * n) ^ 2) * chC sys L j₃ *
      (17728 * chC sys L j₂ + chC sys L j₂ * LamS (2 * N))) *
        (250 * ((Nat.log 2 (2 * N) : ℝ) + 2) * n) :=
        mul_le_mul hk hfib hK0 (by positivity)
    _ = KCdeg sys L N j₁ j₂ j₃ / (n : ℝ) ^ 3 := by
        unfold KCdeg
        field_simp

open Classical in
/-- **A degenerate shared com word**, on cold inputs. -/
theorem tri_deg_X (hL : 0 < L) (hn : 8 ≤ n) (hnN : n ≤ N) {j₁ j₂ j₃ : Ch eta} {a t : Fin eta}
    (ht2 : t ∈ moved j₂) (ht3 : t ∈ moved j₃) (ht1 : t ∉ moved j₁) (ℓ : Cf eta → Cf eta)
    (hℓ1 : ∀ k σ, ℓ (k + tr j₁ σ) = ℓ k) (hℓ2 : ∀ k σ, ℓ (k + tr j₂ σ) = ℓ k)
    (hℓ3 : ∀ k σ, ℓ (k + tr j₃ σ) = ℓ k)
    (hinj : ∀ k k' : Cf eta, ℓ k = ℓ k' → k a = k' a → k t = k' t → k = k')
    {x : Cfg eta N → ℝ} {B₁ Bπ Bc : ℝ} (hX : GoodX sys n x B₁ Bπ Bc) :
    ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else ∑ c, ‖wj sys L N j₃ f c‖ * x c) *
        farW sys L N n f * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ≤
      KCdeg sys L N j₁ j₂ j₃ * Bc / (n : ℝ) ^ 3 := by
  have hN : 1 ≤ N := by omega
  have hn1 : 1 ≤ n := by omega
  refine (tri_deg_le (p₀ := p₀) hL hn hN ht2 ht3 ht1 ℓ hℓ1 hℓ2 hℓ3 hinj x hX.nonneg hX.cold).trans ?_
  have hk0 := kap0_nonneg (sys := sys) hL hn1 N j₁ j₂ j₃
  have hKf := Kfib_nonneg (sys := sys) n
  have hkk := kap0_Kfib_le (sys := sys) hL hn1 hnN j₁ j₂ j₃
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hX.fibre a t) hKf) hk0).trans ?_
  rw [← mul_assoc]
  have := mul_le_mul_of_nonneg_right hkk hX.hc
  rw [div_mul_eq_mul_div] at this
  exact this

variable (sys L) in
/-- The constant of the long com word `R Y₂ W₁^L`. -/
noncomputable def KC4L (N : ℕ) (Hunit : ℝ) (j₂ j₁ : Ch eta) (B₁ Bπ Bc : ℝ) : ℝ :=
  (GamC sys L B₁ + KY1 sys L N j₂ (chC sys L j₁ * (1 / cst sys ^ 2)) * Bπ) / 2 +
    ∑ j₃ : Ch eta, (KCsh sys L Hunit j₁ j₂ j₃ + KCdeg sys L N j₁ j₂ j₃) * Bc

/-- **The long com word** `R Y₂ W₁^L` on cold inputs: `π₂` conserved on the `j₁`-lines (M5), or a
shared word (common coordinate or degenerate, for every outer channel). -/
theorem tri_ch4L {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 8 ≤ n) (hnN : n ≤ N)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {x : Cfg eta N → ℝ} {B₁ Bπ Bc : ℝ} (hX : GoodX sys n x B₁ Bπ Bc) (j₂ j₁ : Ch eta) :
    TriF sys L N n x (fun f => ∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ≤
      KC4L sys L N Hunit j₂ j₁ B₁ Bπ Bc / (n : ℝ) ^ 3 := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : 0 ≤ (GamC sys L B₁ + KY1 sys L N j₂ (chC sys L j₁ * (1 / cst sys ^ 2)) * Bπ) / 2 := by
    have := GamC_nonneg (sys := sys) hL hX.h1
    have := KY1_nonneg (sys := sys) hL N j₂ (chC sys L j₁ * (1 / cst sys ^ 2))
    have := hX.hπ
    positivity
  have hB : ∀ j₂' : Ch eta,
      0 ≤ ∑ j₃ : Ch eta, (KCsh sys L Hunit j₁ j₂' j₃ + KCdeg sys L N j₁ j₂' j₃) * Bc :=
    fun j₂' => Finset.sum_nonneg fun j₃ _ => mul_nonneg (add_nonneg (KCsh_nonneg hL _ _ _ _)
      (KCdeg_nonneg hL _ _ _ _)) hX.hc
  rcases pi_const_or_shared j₁ j₂ with hπ | ⟨pr, a, t, rfl, ha2, ht2, hat, ha1, ht1⟩
  · refine (tri_ch4L_ns (p₀ := p₀) hL hn1 H hKernel hX j₂ j₁ hπ).trans ?_
    unfold KC4L
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [hB j₂]
  · rw [TriF_eq_sum]
    have hper : ∀ j₃ : Ch eta, ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else
          ∑ c, ‖wj sys L N j₃ f c‖ * x c) * farW sys L N n f *
          (∑ d, ‖yj sys L p₀ N (.inr pr) f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ≤
        (KCsh sys L Hunit j₁ (.inr pr) j₃ + KCdeg sys L N j₁ (.inr pr) j₃) * Bc / (n : ℝ) ^ 3 := by
      intro j₃
      have hs := KCsh_nonneg (sys := sys) hL Hunit j₁ (.inr pr) j₃
      have hd := KCdeg_nonneg (sys := sys) hL N j₁ (.inr pr) j₃
      have hc := hX.hc
      rcases shared_cases (j₃ := j₃) ha2 ht2 hat ha1 ht1 with
        ⟨A, ε, hA, hA1, hA3⟩ | ⟨ht3, ℓ, hℓ1, hℓ2, hℓ3, hinj⟩
      · refine (tri_shared_X (p₀ := p₀) hH hL hn1 ht2 ht1 hA hA1 hA3 hX).trans ?_
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      · refine (tri_deg_X (p₀ := p₀) hL hn hnN ht2 ht3 ht1 ℓ hℓ1 hℓ2 hℓ3 hinj hX).trans ?_
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
    refine (Finset.sum_le_sum fun j₃ _ => hper j₃).trans ?_
    rw [← Finset.sum_div]
    unfold KC4L
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith

end Shared

/-! ## The rest words and the C×C block -/

section Rest

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

variable (sys L) in
/-- The constant of the rest word `(j₂, j₁)`. -/
noncomputable def KCword (N : ℕ) (Hunit : ℝ) (j₂ j₁ : Ch eta) (B₁ Bπ Bc : ℝ) : ℝ :=
  (GamC sys L B₁ + KW1 sys L Hunit (chC sys L j₂) (cY3' sys L j₁) * Bπ) / 2 +
    (GamC sys L B₁ + KC4S sys L Hunit j₂ j₁ Bπ Bc) / 2 + 2 * KC4L sys L N Hunit j₂ j₁ B₁ Bπ Bc +
    (if j₂ = j₁ then 0 else
      (GamC sys L B₁ + KC1 sys L Hunit j₂ j₁ Bc) / 2 + (GamC sys L B₁ + KC2 sys L Hunit j₂ j₁ Bc) / 2)

open Classical in
/-- **The rest word `(j₂, j₁)`** on cold inputs: `Tri(Σ_b |r_{j₂ j₁}(·,b)| x_b) ≤ KCword/n³`. -/
theorem tri_rword_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 8 ≤ n) (hnN : n ≤ N)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    {x : Cfg eta N → ℝ} {B₁ Bπ Bc : ℝ} (hX : GoodX sys n x B₁ Bπ Bc) (j₂ j₁ : Ch eta) :
    TriF sys L N n x (fun f => ∑ b, rwordN sys L p₀ N n j₂ j₁ f b * x b) ≤
      KCword sys L N Hunit j₂ j₁ B₁ Bπ Bc / (n : ℝ) ^ 3 := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hx := hX.nonneg
  have T3 := tri_ch3 (p₀ := p₀) hH hL hn1 hX j₂ j₁
  have T4S := tri_ch4S (p₀ := p₀) hH hL hn1 hX j₂ j₁
  have T4L := tri_ch4L (p₀ := p₀) hH hL hn hnN H hKernel hX j₂ j₁
  set h3 : Cfg eta N → ℝ := fun f => ∑ b, ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (yj sys L p₀ N j₁) f b‖ * x b with hh3
  set h4S : Cfg eta N → ℝ := fun f => ∑ d,
        (if ¬ InP (n : ℝ) (cidx N f) then ‖yj sys L p₀ N j₂ f d‖ else 0) *
        ∑ b, WS sys L N n j₁ d b * x b with hh4S
  set h4L : Cfg eta N → ℝ := fun f => ∑ d, ‖yj sys L p₀ N j₂ f d‖ *
        ∑ b, WL sys L N n j₁ d b * x b with hh4L
  -- the `Ch4` word: long and short first hops
  have h4 : ∀ f, ∑ b, ‖chainK' (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b ≤
      h4L f + h4S f := by
    intro f
    have h := chain'_sum_le (fun q => ¬ InP (n : ℝ) (cidx N q))
      (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (yj sys L p₀ N j₂) (wj sys L N j₁) x hx
      (fun f d => if ¬ InP (n : ℝ) (cidx N f) then ‖yj sys L p₀ N j₂ f d‖ else 0)
      (fun d b => WL sys L N n j₁ d b + WS sys L N n j₁ d b)
      (fun f d => by split_ifs <;> first | exact norm_nonneg _ | exact le_rfl)
      (fun d b => add_nonneg (WL_nonneg hL j₁ d b) (WS_nonneg hL j₁ d b))
      (fun f d hf => by rw [if_pos hf])
      (fun d b hb _ => norm_wj_le_split hL j₁ hb) f
    refine h.trans ?_
    simp only [hh4L, hh4S]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun d _ => ?_
    have hvL : 0 ≤ ∑ b, WL sys L N n j₁ d b * x b :=
      Finset.sum_nonneg fun b _ => mul_nonneg (WL_nonneg hL j₁ d b) (hx b)
    have hK : (if ¬ InP (n : ℝ) (cidx N f) then ‖yj sys L p₀ N j₂ f d‖ else 0) ≤
        ‖yj sys L p₀ N j₂ f d‖ := by
      split_ifs <;> first | exact le_rfl | exact norm_nonneg _
    have e : ∑ b, (WL sys L N n j₁ d b + WS sys L N n j₁ d b) * x b =
        ∑ b, WL sys L N n j₁ d b * x b + ∑ b, WS sys L N n j₁ d b * x b := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => add_mul _ _ _
    rw [e, mul_add]
    have := mul_le_mul_of_nonneg_right hK hvL
    linarith
  -- the `Ch2'` word: the first hop is long
  have h2y : ∀ f, ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b ≤ h4L f := by
    intro f
    exact chain_sum_le _ _ _ (yj sys L p₀ N j₂) (wj sys L N j₁) x hx
      (fun f d => ‖yj sys L p₀ N j₂ f d‖) (WL sys L N n j₁)
      (fun f d => norm_nonneg _) (WL_nonneg hL j₁)
      (fun f d _ _ => le_rfl) (fun d b hd hb _ => norm_wj_notP_le hL j₁ hb hd) f
  by_cases hj : j₂ = j₁
  · have hpt : ∀ f, ∑ b, rwordN sys L p₀ N n j₂ j₁ f b * x b ≤ h3 f + h4L f + h4S f + h4L f := by
      intro f
      have e : ∑ b, rwordN sys L p₀ N n j₂ j₁ f b * x b = h3 f +
          ∑ b, ‖chainK' (fun q => ¬ InP (n : ℝ) (cidx N q))
            (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b +
          ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
            (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
            (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b := by
        simp only [rwordN, if_pos hj, add_zero, add_mul, Finset.sum_add_distrib, hh3]
      rw [e]
      have := h4 f
      have := h2y f
      linarith
    refine (TriF_le4 hx hpt).trans ?_
    have e : KCword sys L N Hunit j₂ j₁ B₁ Bπ Bc / (n : ℝ) ^ 3 =
        (GamC sys L B₁ + KW1 sys L Hunit (chC sys L j₂) (cY3' sys L j₁) * Bπ) / 2 / (n : ℝ) ^ 3 +
        KC4L sys L N Hunit j₂ j₁ B₁ Bπ Bc / (n : ℝ) ^ 3 +
        (GamC sys L B₁ + KC4S sys L Hunit j₂ j₁ Bπ Bc) / 2 / (n : ℝ) ^ 3 +
        KC4L sys L N Hunit j₂ j₁ B₁ Bπ Bc / (n : ℝ) ^ 3 := by
      unfold KCword
      rw [if_pos hj]
      ring
    rw [e]
    linarith
  · have T1 := tri_ch1 hH hL hn1 hX hj
    have T2 := tri_ch2fl hH hL hn1 hX hj
    set h1 : Cfg eta N → ℝ := fun f => ∑ b, ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun d => InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b with hh1
    set h2fl : Cfg eta N → ℝ := fun f => ∑ b,
        ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b with hh2fl
    have hpt : ∀ f, ∑ b, rwordN sys L p₀ N n j₂ j₁ f b * x b ≤
        h3 f + h4L f + h4S f + h4L f + h1 f + h2fl f := by
      intro f
      have e : ∑ b, rwordN sys L p₀ N n j₂ j₁ f b * x b = h3 f +
          ∑ b, ‖chainK' (fun q => ¬ InP (n : ℝ) (cidx N q))
            (fun p => InC (n : ℝ) (cst sys) (cidx N p)) (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b +
          ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
            (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
            (yj sys L p₀ N j₂) (wj sys L N j₁) f b‖ * x b + (h1 f + h2fl f) := by
        simp only [rwordN, if_neg hj, add_mul, Finset.sum_add_distrib, hh3, hh1, hh2fl]
      rw [e]
      have := h4 f
      have := h2y f
      linarith
    refine (TriF_le6 hx hpt).trans ?_
    have e : KCword sys L N Hunit j₂ j₁ B₁ Bπ Bc / (n : ℝ) ^ 3 =
        (GamC sys L B₁ + KW1 sys L Hunit (chC sys L j₂) (cY3' sys L j₁) * Bπ) / 2 / (n : ℝ) ^ 3 +
        KC4L sys L N Hunit j₂ j₁ B₁ Bπ Bc / (n : ℝ) ^ 3 +
        (GamC sys L B₁ + KC4S sys L Hunit j₂ j₁ Bπ Bc) / 2 / (n : ℝ) ^ 3 +
        KC4L sys L N Hunit j₂ j₁ B₁ Bπ Bc / (n : ℝ) ^ 3 +
        (GamC sys L B₁ + KC1 sys L Hunit j₂ j₁ Bc) / 2 / (n : ℝ) ^ 3 +
        (GamC sys L B₁ + KC2 sys L Hunit j₂ j₁ Bc) / 2 / (n : ℝ) ^ 3 := by
      unfold KCword
      rw [if_neg hj]
      ring
    rw [e]
    linarith

variable (sys L) in
/-- The constant of the rest of the C×C pairing. -/
noncomputable def KCrest (N : ℕ) (Hunit : ℝ) (B₁ Bπ Bc : ℝ) : ℝ :=
  4 / 3 * ∑ j₁ : Ch eta, ∑ j₂ : Ch eta, KCword sys L N Hunit j₂ j₁ B₁ Bπ Bc

/-- **The rest of the C×C pairing** on a good cold input: `|⟨W v, Ỹ_r v⟩| ≤ KCrest/n³`. -/
theorem cc_rest_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 8 ≤ n) (hnN : n ≤ N)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (v : En eta N) {B₁ Bπ Bc : ℝ} (hX : GoodX sys n (fun c => ‖v.ofLp c‖) B₁ Bπ Bc) :
    ‖⟪FSKernel.kop (wNK sys L N) v, FSKernel.kop (ytK sys L N n (rK sys L p₀ N n)) v⟫_ℂ‖ ≤
      KCrest sys L N Hunit B₁ Bπ Bc / (n : ℝ) ^ 3 := by
  classical
  have hn1 : 1 ≤ n := by omega
  refine (norm_inner_W_Yr_le hL hn1 v).trans ?_
  have e1 : ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else
      ∑ j₃, ∑ c, ‖wj sys L N j₃ f c‖ * ‖v.ofLp c‖) * farW sys L N n f *
        ∑ b, ‖rK sys L p₀ N n f b‖ * ‖v.ofLp b‖ =
      TriF sys L N n (fun c => ‖v.ofLp c‖) (fun f => ∑ b, ‖rK sys L p₀ N n f b‖ * ‖v.ofLp b‖) := rfl
  rw [e1]
  have hpt : ∀ f, ∑ b, ‖rK sys L p₀ N n f b‖ * ‖v.ofLp b‖ ≤
      ∑ j₁, ∑ j₂, ∑ b, rwordN sys L p₀ N n j₂ j₁ f b * ‖v.ofLp b‖ := by
    intro f
    calc ∑ b, ‖rK sys L p₀ N n f b‖ * ‖v.ofLp b‖ ≤
        ∑ b, (∑ j₁, ∑ j₂, rwordN sys L p₀ N n j₂ j₁ f b) * ‖v.ofLp b‖ :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (norm_rK_le hL f b) (norm_nonneg _)
      _ = ∑ j₁, ∑ j₂, ∑ b, rwordN sys L p₀ N n j₂ j₁ f b * ‖v.ofLp b‖ := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j₁ _ => ?_
          rw [Finset.sum_comm]
  refine (mul_le_mul_of_nonneg_left (TriF_mono hX.nonneg hpt) (by norm_num)).trans ?_
  rw [TriF_sum]
  unfold KCrest
  rw [mul_div_assoc, Finset.sum_div]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine Finset.sum_le_sum fun j₁ _ => ?_
  rw [TriF_sum, Finset.sum_div]
  exact Finset.sum_le_sum fun j₂ _ => tri_rword_le hH hL hn hnN H hKernel hX j₂ j₁

variable (sys L) in
/-- The constant of the C×C block of a good state. -/
noncomputable def KCC (N nd : ℕ) (M Hunit : ℝ) : ℝ :=
  ∑ j : Ch eta, Kss sys L j / 2 * Bss sys L N nd M +
    KCrest sys L N Hunit (Bpsi sys L N nd M 1) (Bpsi sys L N nd M (4 * mmax sys / gF L ^ 2))
      (Bpsi sys L N nd M (2 * cXw sys L))

/-- **The C×C block of a good state**: `|Im⟨W u_C, Ỹ u_C⟩| ≤ KCC/n³`, where
`KCC = Σ_j K_ss B_ss/2 + KCrest(B_ψ(1), B_ψ(4m/g²), B_ψ(2c_X))` (`≲ log² N M² (1 + η n_d)`). -/
theorem abs_im_CC_good_le {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 8 ≤ n) (hnN : n ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd) {M : ℝ}
    {u : En eta N} (hu : IsGood sys L 1 M u)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    |(⟪WN sys L N (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u),
        Yt sys L p₀ N n (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u)⟫_ℂ).im| ≤
      KCC sys L N nd M Hunit / (n : ℝ) ^ 3 := by
  classical
  have hN : 1 ≤ N := by omega
  have hW : WN sys L N = FSKernel.kop (wNK sys L N) := VN_eq_kop sys hL H hKernel
  have hX := goodX_res hL hN hnd hu n
  have hss : ∀ j, |(⟪FSKernel.kop (wNK sys L N) (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u),
      FSKernel.kop (ytK sys L N n (ssK sys L p₀ N n j))
        (FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u)⟫_ℂ).im| ≤
      Kss sys L j / (n : ℝ) ^ 3 / 2 * Bss sys L N nd M :=
    fun j => abs_im_W_Yss_good_le hL (by omega) hnN hnd hu j
  have hrest := cc_rest_le (p₀ := p₀) hH hL hn hnN H hKernel _ hX
  set v := FSKernel.res (fun p => InC (n : ℝ) (cst sys) (cidx N p)) u with hv
  rw [hW]
  have e : ⟪FSKernel.kop (wNK sys L N) v, Yt sys L p₀ N n v⟫_ℂ = ⟪FSKernel.kop (wNK sys L N) v,
      FSKernel.kop (ytK sys L N n (bfcK sys L p₀ N n)) v⟫_ℂ := rfl
  rw [e, inner_Yt_split, Complex.add_im, Complex.im_sum]
  have hr2 := (Complex.abs_im_le_norm _).trans hrest
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => hss j)) hr2).trans (le_of_eq ?_)
  unfold KCC
  rw [add_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Rest

end FSFlux
