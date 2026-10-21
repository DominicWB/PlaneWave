import PlaneWave.FluxBox.Flux3

/-!
# `lem:obs3`, restated for the same-pair class

The text's `lem:obs3` (marked there as not used) assumes `ΔA_p(θ) = ΔA_p(τ)` on two-pair elements,
which fails when the `W`-hop moves `p`, and rests on two-pair kernel bounds that are not proved
(`propagator_plan.md`, readiness review, note 9). It is restated here for the same-pair generator
`Σ₃^sp` of `PlaneWave.SamePair.ThirdGenerator`:

* `obs3K`, the kernel of `[Σ₃^sp, A_{p₀}]` (`comm_Sig3sp_Aproj`), and **`norm_obs3K_le`**: on the
  gapped same-pair elements, `|ΔA_{p₀}| ≤ |ΔE| (1 + |Π_j|)` (`obs_hop_le` and the floor), so
  `|obs3K(q,p)| ≤ (1 + |Π_j|) |h₃(q,p)| ≤ B_j (J_n + 4) (1 + |Π_j|)` on the channel of the element;
* **`obs3sp`**: `|⟨u, [Σ₃^sp, A_{p₀}] u⟩| ≤ C_obs3(n) ‖(1 + A) u‖²` on `E_n`
  (the fibre trace bound `chan_trace_le`, as for `lem:obs2`), **`obs3sp_good`** (`≤ C_obs3(n) M²`),
  `C_obs3 = Σ_j B_j (J_n + 4) · 125 (⌊log₂ n⌋ + 2) · 3κ² = O(n⁻³ log³ n)` (`pl_Cobs3`), and
  **`lem_obs3_sp`**: `|⟨u, [Σ₃^sp, A_{p₀}] u⟩| ≤ C_ε M² K^{-3+ε}`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The kernel of `[Σ₃^sp, A_{p₀}]` -/

section Kernel3

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (p₀ : Fin eta)

/-- The kernel of `[Σ₃^sp, A_{p₀}] = Σ₃^sp A_{p₀} - A_{p₀} Σ₃^sp`. -/
noncomputable def obs3K (q p : Cfg eta n) : ℂ :=
  ((Aproj sys L p₀ p - Aproj sys L p₀ q : ℝ) : ℂ) * FSKernel.divK (Asym sys L n) (h3gK sys L n) q p

open Classical in
/-- The majorant of `obs3K` on channel `j`. -/
noncomputable def obs3Maj (j : Ch eta) (q p : Cfg eta n) : ℝ :=
  if p₀ ∈ moved j ∧ OnCh j (cidx n q) (cidx n p) then
    Bh3 sys L n j * (Jn sys n + 4) * (1 + piC j (cidx n p)) else 0

variable {sys L n p₀}

theorem comm_Sig3sp_Aproj :
    Sig3sp sys L n ∘ₗ FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) -
      FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) ∘ₗ Sig3sp sys L n =
      FSKernel.kop (obs3K sys L n p₀) := by
  have h := FSKernel.kop_comm_dg (fun q => (Aproj sys L p₀ q : ℂ))
    (FSKernel.divK (Asym sys L n) (h3gK sys L n))
  have h2 : Sig3sp sys L n = FSKernel.kop (FSKernel.divK (Asym sys L n) (h3gK sys L n)) := rfl
  rw [h2, ← neg_sub, h]
  ext u q
  simp only [LinearMap.neg_apply, FSKernel.kop_apply, PiLp.neg_apply, obs3K]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  push_cast
  ring

lemma obs3Maj_nonneg (hL : 0 < L) (j : Ch eta) (q p : Cfg eta n) :
    0 ≤ obs3Maj sys L n p₀ j q p := by
  unfold obs3Maj
  have := Bh3_nonneg (sys := sys) (n := n) hL j
  have := piC_nonneg j (cidx n p)
  split_ifs
  · positivity
  · exact le_rfl

/-- **The kernel bound**: `|obs3K(q, p)| ≤ Σ_j [p₀ moved, q ~_j p] B_j (J_n + 4) (1 + |Π_j|)`. -/
theorem norm_obs3K_le (hL : 0 < L) (hn : 2 ≤ n) (q p : Cfg eta n) :
    ‖obs3K sys L n p₀ q p‖ ≤ ∑ j, obs3Maj sys L n p₀ j q p := by
  classical
  have hsum0 : 0 ≤ ∑ j, obs3Maj sys L n p₀ j q p :=
    Finset.sum_nonneg fun j _ => obs3Maj_nonneg hL j q p
  by_cases hgap : gapC sys L n q p
  swap
  · have h0 : FSKernel.divK (Asym sys L n) (h3gK sys L n) q p = 0 := by
      unfold FSKernel.divK h3gK
      split_ifs <;> simp
    unfold obs3K
    rw [h0, mul_zero, norm_zero]
    exact hsum0
  obtain ⟨hne, j, hj, hfl⟩ := hgap
  have hgap' : gapC sys L n q p := ⟨hne, j, hj, hfl⟩
  have hA : Asym sys L n q ≠ Asym sys L n p := gapC_ne hL hgap'
  have hs : FSKernel.divK (Asym sys L n) (h3gK sys L n) q p =
      h3spK sys L n q p / ((Asym sys L n q - Asym sys L n p : ℝ) : ℂ) := by
    unfold FSKernel.divK h3gK
    rw [if_neg hA, if_pos hgap']
  have hk : cidx n q = cidx n p + tr j (chT n j q p) := hj
  by_cases hpm : p₀ ∈ moved j
  · have hob := obs_hop_le sys (gF L) p₀ j (cidx n p) (chT n j q p)
    rw [← hk, ← Aproj_eq, ← Aproj_eq] at hob
    have eA : ∀ r : Cfg eta n, E sys.mass (gF L) (cidx n r) = Asym sys L n r := fun r =>
      (Asym_eq_Ek (sys := sys) (L := L) r).symm
    rw [eA, eA] at hob
    have hμ := muCh_pos sys j
    have hg2 := gF_pos hL
    have hMt := Mtot_pos sys j
    have hpi0 := piC_nonneg j (cidx n p)
    have hρ0 := FSChannel.rho_nonneg (chT n j q p)
    have hfl' : gF L ^ 2 * FSChannel.rho (chT n j q p) ≤
        muCh sys j * |Asym sys L n q - Asym sys L n p| := by
      rw [div_le_iff₀ hμ] at hfl; linarith
    have hpart : gF L ^ 2 * FSChannel.rho (chT n j q p) * piC j (cidx n p) / Mtot sys j ≤
        |Asym sys L n q - Asym sys L n p| * piC j (cidx n p) := by
      calc gF L ^ 2 * FSChannel.rho (chT n j q p) * piC j (cidx n p) / Mtot sys j
          ≤ muCh sys j * |Asym sys L n q - Asym sys L n p| * piC j (cidx n p) / Mtot sys j := by
            gcongr
        _ = |Asym sys L n q - Asym sys L n p| * (muCh sys j / Mtot sys j * piC j (cidx n p)) := by
            ring
        _ ≤ |Asym sys L n q - Asym sys L n p| * piC j (cidx n p) :=
            mul_le_mul_of_nonneg_left (mu_piC_le sys j _) (abs_nonneg _)
    have hΔ : |Aproj sys L p₀ p - Aproj sys L p₀ q| ≤
        |Asym sys L n q - Asym sys L n p| * (1 + piC j (cidx n p)) := by
      rw [abs_sub_comm]; nlinarith
    have hpos : 0 < |Asym sys L n q - Asym sys L n p| := abs_pos.mpr (sub_ne_zero.mpr hA)
    -- the same-pair kernel below the cube cap
    have hρ1 : 1 ≤ FSChannel.rho (chT n j q p) := FSLattice.one_le_rho (one_le_lsq_chT hj hne)
    have hfl2 := floor_of_gapC hL hj hgap'
    have hcap := slabF_cap_cube (sys := sys) hL hj
    have hρc : FSChannel.rho (chT n j q p) < 2 ^ (Jn sys n + 1 + 1) := by
      have : 2 * FSChannel.rho (chT n j q p) < 2 ^ (Jn sys n + 1 + 1) * 2 := lt_of_le_of_lt hfl2 hcap
      linarith
    have hlog := FSLattice.log_ceil_le hρc
    have hlog' : ((Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ : ℕ) : ℝ) + 2 ≤ Jn sys n + 4 := by
      have : ((Nat.log 2 ⌈FSChannel.rho (chT n j q p)⌉₊ : ℕ) : ℝ) ≤ Jn sys n + 1 + 1 := by
        exact_mod_cast hlog
      linarith
    have hB := Bh3_nonneg (sys := sys) (n := n) hL j
    have hh := norm_h3spK_le (sys := sys) hL hn hj hne
    have hX : ‖h3spK sys L n q p‖ ≤ Bh3 sys L n j * (Jn sys n + 4) := by
      refine hh.trans (mul_le_mul_of_nonneg_left ?_ hB)
      rw [div_le_iff₀ (by linarith)]
      have h0 : (0 : ℝ) ≤ Jn sys n + 4 := by positivity
      nlinarith
    have hval : obs3Maj sys L n p₀ j q p = Bh3 sys L n j * (Jn sys n + 4) * (1 + piC j (cidx n p)) := by
      unfold obs3Maj; rw [if_pos ⟨hpm, hj⟩]
    refine le_trans ?_ (le_trans (le_of_eq hval.symm) (Finset.single_le_sum
      (f := fun j => obs3Maj sys L n p₀ j q p) (fun j _ => obs3Maj_nonneg hL j q p)
      (Finset.mem_univ j)))
    unfold obs3K
    rw [hs, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    calc |Aproj sys L p₀ p - Aproj sys L p₀ q| * (‖h3spK sys L n q p‖ /
          |Asym sys L n q - Asym sys L n p|)
        ≤ |Asym sys L n q - Asym sys L n p| * (1 + piC j (cidx n p)) *
            (Bh3 sys L n j * (Jn sys n + 4) / |Asym sys L n q - Asym sys L n p|) := by
          gcongr
      _ = Bh3 sys L n j * (Jn sys n + 4) * (1 + piC j (cidx n p)) := by field_simp
  · have h1 : cidx n q p₀ = cidx n p p₀ := by
      rw [hk, Pi.add_apply, tr_apply_not_moved j _ hpm, add_zero]
    have h2 : Aproj sys L p₀ q = Aproj sys L p₀ p := by
      rw [Aproj_eq, Aproj_eq]; unfold regL; rw [h1]
    unfold obs3K
    rw [h2, sub_self, Complex.ofReal_zero, zero_mul, norm_zero]
    exact hsum0

end Kernel3

/-! ## The form bound -/

section Obs3

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ} {p₀ : Fin eta}

variable (sys L) in
/-- The constant of the same-pair `lem:obs3`:
`C_obs3 = Σ_j B_j (J_n + 4) · 125 (⌊log₂ n⌋ + 2) · 3κ²`, `O(n⁻³ log³ n)`. -/
noncomputable def Cobs3 (n : ℕ) : ℝ :=
  (∑ j : Ch eta, Bh3 sys L n j * (Jn sys n + 4)) * (125 * (Nat.log 2 n + 2)) * (3 * kapW sys L ^ 2)

lemma Cobs3_nonneg (hL : 0 < L) (n : ℕ) : 0 ≤ Cobs3 sys L n := by
  unfold Cobs3
  have := Finset.sum_nonneg fun j (_ : j ∈ (Finset.univ : Finset (Ch eta))) =>
    mul_nonneg (Bh3_nonneg (sys := sys) (n := n) hL j) (by positivity : (0 : ℝ) ≤ Jn sys n + 4)
  positivity

/-- **`lem:obs3`, same pair** (restated): `|⟨u, [Σ₃^sp, A_{p₀}] u⟩| ≤ C_obs3(n) ‖(1 + A) u‖²` on `E_n`. -/
theorem obs3sp (hL : 0 < L) (hn : 2 ≤ n) (u : En eta n) :
    ‖⟪u, (Sig3sp sys L n ∘ₗ FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) -
      FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) ∘ₗ Sig3sp sys L n) u⟫_ℂ‖ ≤
      Cobs3 sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 := by
  classical
  rw [comm_Sig3sp_Aproj]
  refine (norm_inner_kop_le' _ u).trans ?_
  have hn1 : 1 ≤ n := by omega
  set N := (125 * (Nat.log 2 n + 2) : ℝ)
  have hN0 : 0 ≤ N := by positivity
  have h1 : ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * ‖obs3K sys L n p₀ q p‖ ≤
      ∑ j : Ch eta, ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obs3Maj sys L n p₀ j q p := by
    calc ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * ‖obs3K sys L n p₀ q p‖
        ≤ ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * ∑ j, obs3Maj sys L n p₀ j q p :=
          Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left (norm_obs3K_le hL hn q p) (by positivity)
      _ = ∑ j : Ch eta, ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obs3Maj sys L n p₀ j q p := by
          simp_rw [Finset.mul_sum]
          exact sum3_comm (fun q p j => ‖u.ofLp q‖ * ‖u.ofLp p‖ * obs3Maj sys L n p₀ j q p)
  refine h1.trans ?_
  have h2 : ∀ j : Ch eta, ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obs3Maj sys L n p₀ j q p ≤
      Bh3 sys L n j * (Jn sys n + 4) * N * (3 * kapW sys L ^ 2) *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 := by
    intro j
    have hB := Bh3_nonneg (sys := sys) (n := n) hL j
    have hBJ : 0 ≤ Bh3 sys L n j * (Jn sys n + 4) := by positivity
    have hc : ∀ q p, OnCh j (cidx n q) (cidx n p) →
        1 + piC j (cidx n q) = 1 + piC j (cidx n p) := fun q p h => by rw [piC_onCh h]
    have hpt : ∀ q p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obs3Maj sys L n p₀ j q p ≤
        Bh3 sys L n j * (Jn sys n + 4) * (if OnCh j (cidx n q) (cidx n p) then
          ‖u.ofLp q‖ * ‖u.ofLp p‖ * (1 + piC j (cidx n p)) else 0) := by
      intro q p
      unfold obs3Maj
      split_ifs with h1 h2 h2
      · exact le_of_eq (by ring)
      · exact absurd h1.2 h2
      · rw [mul_zero]
        have := piC_nonneg j (cidx n p)
        positivity
      · rw [mul_zero, mul_zero]
    calc ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obs3Maj sys L n p₀ j q p
        ≤ ∑ q, ∑ p, Bh3 sys L n j * (Jn sys n + 4) * (if OnCh j (cidx n q) (cidx n p) then
            ‖u.ofLp q‖ * ‖u.ofLp p‖ * (1 + piC j (cidx n p)) else 0) :=
          Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun p _ => hpt q p
      _ = Bh3 sys L n j * (Jn sys n + 4) * ∑ q, ∑ p, (if OnCh j (cidx n q) (cidx n p) then
            ‖u.ofLp q‖ * ‖u.ofLp p‖ * (1 + piC j (cidx n p)) else 0) := by
          rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
      _ ≤ Bh3 sys L n j * (Jn sys n + 4) *
            (N * ∑ q, wl j q * (1 + piC j (cidx n q)) * ‖u.ofLp q‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (chan_trace_le hn1 j (fun q => ‖u.ofLp q‖)
            (fun q => 1 + piC j (cidx n q))
            (fun q => by linarith [piC_nonneg j (cidx n q)]) hc) hBJ
      _ ≤ Bh3 sys L n j * (Jn sys n + 4) * (N * ∑ q, 3 * kapW sys L ^ 2 * (1 + Asym sys L n q) ^ 2 *
            ‖u.ofLp q‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun q _ => ?_) hN0) hBJ
          exact mul_le_mul_of_nonneg_right (wl_pi_le (sys := sys) hL j q) (sq_nonneg _)
      _ = Bh3 sys L n j * (Jn sys n + 4) * N * (3 * kapW sys L ^ 2) *
            ∑ q, (1 + Asym sys L n q) ^ 2 * ‖u.ofLp q‖ ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => by ring
      _ = _ := by
          congr 1
          rw [norm_sq_wt]
          refine Finset.sum_congr rfl fun q _ => by rw [Real.rpow_one]
  calc ∑ j : Ch eta, ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obs3Maj sys L n p₀ j q p
      ≤ ∑ j : Ch eta, Bh3 sys L n j * (Jn sys n + 4) * N * (3 * kapW sys L ^ 2) *
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 := Finset.sum_le_sum fun j _ => h2 j
    _ = Cobs3 sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 := by
        unfold Cobs3
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]

/-- **`lem:obs3`, same pair, on good states**: `|⟨u, [Σ₃^sp, A_{p₀}] u⟩| ≤ C_obs3(n) M²`. -/
theorem obs3sp_good (hL : 0 < L) (hn : 2 ≤ n) {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) :
    ‖⟪u, (Sig3sp sys L n ∘ₗ FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) -
      FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) ∘ₗ Sig3sp sys L n) u⟫_ℂ‖ ≤
      Cobs3 sys L n * M ^ 2 := by
  refine (obs3sp hL hn u).trans ?_
  have hw : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ≤ M := by
    have := hu.1
    have := norm_nonneg u
    simp only [one_mul] at *
    linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw 2) (Cobs3_nonneg hL n)

end Obs3

end FSNormal

namespace FSAsymp

open FSNormal PL

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ}

theorem pl_Cobs3 (heta : 0 < eta) : PL (fun n => Cobs3 sys L n) (-3) := by
  have hlog : PL (fun n => (Nat.log 2 n : ℝ)) 0 := by
    have h := natlog_of_le (x := fun n => (n : ℝ)) (c := 1) 1 ⟨1, fun n hn => by
      refine ⟨by exact_mod_cast hn, by rw [pow_one, one_mul]⟩⟩
    exact h.congr ⟨0, fun n _ => by simp⟩
  have hS := PL.sum (p := -3) (Finset.univ : Finset (Ch eta))
    (F := fun j n => Bh3 sys L n j * ((Jn sys n : ℝ) + 4))
    (fun j _ => ((pl_Bh3 sys (L := L) heta j).mul ((pl_Jn sys heta).add' (const 4))).mono
      (by norm_num))
  have h := (hS.mul ((hlog.add' (const 2)).const_mul 125)).mul_const (3 * kapW sys L ^ 2)
  refine (h.mono (by norm_num)).congr ⟨0, fun n _ => ?_⟩
  unfold Cobs3
  ring

end FSAsymp

namespace FSNormal

open FSAsymp

variable {eta : ℕ} {ν : Type} [Fintype ν] {sys : CoulombSystem eta ν} {L : ℝ}

/-- **`lem:obs3`, same pair, at the target rate**: for every `ε > 0` there is `C_ε` with
`|⟨u, [Σ₃^sp, A_{p₀}] u⟩| ≤ C_ε M² K^{-3+ε}` for every good `u ∈ E_n` (`n ≥ 2`, `K = g n`). -/
theorem lem_obs3_sp (heta : 0 < eta) (hL : 0 < L) (p₀ : Fin eta) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ {M : ℝ} {u : En eta n}, IsGood sys L 1 M u →
      ‖⟪u, (Sig3sp sys L n ∘ₗ FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) -
        FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) ∘ₗ Sig3sp sys L n) u⟫_ℂ‖ ≤
        C * M ^ 2 * Kc L n ^ (-3 + ε) := by
  obtain ⟨C₁, hC₁, h₁⟩ := FSFlux.PL_final_all (pl_Cobs3 sys (L := L) heta) hε
  have hg := gF_pos hL
  have hgp : 0 < gF L ^ (3 - ε) := Real.rpow_pos_of_pos hg _
  refine ⟨C₁ * gF L ^ (3 - ε), by positivity, fun n hn M u hu => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hK : (n : ℝ) ^ (-3 + ε) = gF L ^ (3 - ε) * Kc L n ^ (-3 + ε) := by
    rw [Kc_eq, Real.mul_rpow hg.le hn0.le, ← mul_assoc, ← Real.rpow_add hg]
    norm_num
  have hb := obs3sp_good (p₀ := p₀) hL hn hu
  have hc := h₁ n hn1
  rw [hK] at hc
  have hM := sq_nonneg M
  calc _ ≤ Cobs3 sys L n * M ^ 2 := hb
    _ ≤ (C₁ * (gF L ^ (3 - ε) * Kc L n ^ (-3 + ε))) * M ^ 2 :=
        mul_le_mul_of_nonneg_right ((le_abs_self _).trans hc) hM
    _ = C₁ * gF L ^ (3 - ε) * M ^ 2 * Kc L n ^ (-3 + ε) := by ring

end FSNormal
