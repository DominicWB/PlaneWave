import PlaneWave.Source.TimeAveragedHotContent
import PlaneWave.Source.WeightedMoments

/-!
# Flux/source build, block 1b: good states and the truncated datum

On the Galerkin space `E_n`:

* `IsGood sys L Cg Ξ u` (eq:good-state, with the constant `C` made explicit as `Cg`):
  `‖u‖ + Θ(u) ≤ Cg Ξ`, `‖Q⁽²⁾_{a,λ} u‖ ≤ Cg Ξ λ^{-5/2}` and `‖ℰ Q⁽²⁾_{a,λ} u‖ ≤ Cg Ξ λ^{-1/2}`
  for every register `a` and `λ ≥ 1`, with `Θ(u) = ‖(1+A) u‖`, `ℰ = 1 + A`;
* `Kc L n = g n` (the cutoff `K`), `mmax` (`m_max`, at least one), `E0 = K²/(4096 m_max)`;
* `datum p₀ v = A_{p₀}^E v = A_{p₀} Q 1{A ≤ E₀} v` (`lem:bulkobsE`), with `A_{p₀} = |k_{p₀}|²/(2 m_{p₀})`
  the kinetic observable of the projectile register `p₀` and `Q = Π_a 1{|k_a| ≤ K/4}`;
* `datum_support`: `1{A > E₀} A_{p₀}^E v = 0`; `norm_datum_le`: `‖A_{p₀}^E v‖ ≤ Θ(v)`;
* `wt_datum_sq_le` (`cor:spectail`, weighted norms): for a good `v` and `r' > 1/4`,
  `‖(1+A)^{r'} A_{p₀}^E v‖² ≤ C_{r'} Cg² Ξ² Λ^{4r'-1}` with `Λ = (2 m_max E₀)^{1/2} = K/√2048`,
  from the dyadic moment bound `FSDatum.moment_le_of_tails` (`dev/PlaneWave.Source.WeightedMoments.lean`).
-/

set_option autoImplicit false

open scoped InnerProductSpace Real
open PlaneWaveCertificate

namespace FSGalerkin

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type*}

/-! ## Good states -/

section Good

variable [Fintype ν] (sys : CoulombSystem eta ν) (L : ℝ) {n : ℕ}

/-- **A good state with budget `Ξ`** (eq:good-state), with the constant `Cg`. -/
def IsGood (Cg Ξ : ℝ) (u : En eta n) : Prop :=
  ‖u‖ + ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ≤ Cg * Ξ ∧
  ∀ (a : Fin eta) (l : ℝ), 1 ≤ l →
    ‖regTail L a l u‖ ≤ Cg * Ξ * l ^ (-(5 / 2 : ℝ)) ∧
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 (regTail L a l u)‖ ≤ Cg * Ξ * l ^ (-(1 / 2 : ℝ))

end Good

/-! ## Scales -/

section Scales

variable [Fintype ν] (sys : CoulombSystem eta ν)

/-- The cutoff `K = g n` (`g = 2π/L`). -/
noncomputable def Kc (L : ℝ) (n : ℕ) : ℝ := gL L * n

/-- `m_max`, the largest mass (at least one). -/
noncomputable def mmax (sys : CoulombSystem eta ν) : ℝ := max 1 (⨆ a, sys.mass a)

omit [Fintype ν] in
lemma one_le_mmax : 1 ≤ mmax sys := le_max_left _ _

omit [Fintype ν] in
lemma mass_le_mmax (a : Fin eta) : sys.mass a ≤ mmax sys :=
  (le_ciSup (Set.finite_range _).bddAbove a).trans (le_max_right _ _)

/-- The total-kinetic truncation scale `E₀ = K²/(4096 m_max)`. -/
noncomputable def E0 (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Kc L n ^ 2 / (4096 * mmax sys)

end Scales

/-! ## The truncated datum -/

section Datum

variable [Fintype ν] (sys : CoulombSystem eta ν) (L : ℝ) {n : ℕ} (p₀ : Fin eta)

/-- The kinetic observable of the projectile register, `A_{p₀} = |k_{p₀}|²/(2 m_{p₀})`. -/
noncomputable def Aproj (p : Cfg eta n) : ℝ :=
  finitePlaneWaveKabs (2 * Real.pi / L) n (p p₀) ^ 2 / (2 * sys.mass p₀)

/-- The symbol of `A_{p₀}^E = A_{p₀} Q 1{A ≤ E₀}`. -/
noncomputable def datumSym (p : Cfg eta n) : ℝ :=
  if (∀ a, finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ≤ Kc L n / 4) ∧
      Asym sys L n p ≤ E0 sys L n then Aproj sys L p₀ p else 0

/-- **The datum `A_{p₀}^E v`.** -/
noncomputable def datum (v : En eta n) : En eta n :=
  cfgMul (fun p => (datumSym sys L p₀ p : ℂ)) v

omit [Fintype ν] in
lemma Aproj_nonneg (p : Cfg eta n) : 0 ≤ Aproj sys L p₀ p := by
  unfold Aproj; have := sys.mass_pos p₀; positivity

omit [Fintype ν] in
/-- `A_{p₀} ≤ A`. -/
lemma Aproj_le_Asym (p : Cfg eta n) : Aproj sys L p₀ p ≤ Asym sys L n p := by
  unfold Aproj Asym massKineticSymbol
  have h := Finset.single_le_sum (f := fun a => finitePlaneWaveKabs (2 * Real.pi / L) n (p a) ^ 2 /
    sys.mass a) (fun a _ => by have := sys.mass_pos a; positivity) (Finset.mem_univ p₀)
  have hm := sys.mass_pos p₀
  have : finitePlaneWaveKabs (2 * Real.pi / L) n (p p₀) ^ 2 / (2 * sys.mass p₀) =
      1 / 2 * (finitePlaneWaveKabs (2 * Real.pi / L) n (p p₀) ^ 2 / sys.mass p₀) := by
    field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

omit [Fintype ν] in
lemma datumSym_nonneg (p : Cfg eta n) : 0 ≤ datumSym sys L p₀ p := by
  unfold datumSym; split_ifs
  · exact Aproj_nonneg sys L p₀ p
  · exact le_rfl

omit [Fintype ν] in
/-- `0 ≤ A_{p₀}^E ≤ A 1{A ≤ E₀}`. -/
lemma datumSym_le (p : Cfg eta n) :
    datumSym sys L p₀ p ≤ if Asym sys L n p ≤ E0 sys L n then Asym sys L n p else 0 := by
  unfold datumSym
  split_ifs with h1 h2
  · exact Aproj_le_Asym sys L p₀ p
  · exact absurd h1.2 h2
  · exact Asym_nonneg sys L n p
  · exact le_rfl

omit [Fintype ν] in
lemma datum_apply (v : En eta n) (p : Cfg eta n) :
    (datum sys L p₀ v).ofLp p = (datumSym sys L p₀ p : ℂ) * v.ofLp p := rfl

omit [Fintype ν] in
/-- **Kinetic support of the datum**: `1{A > E₀} A_{p₀}^E v = 0`. -/
lemma datum_support (v : En eta n) (p : Cfg eta n) (hp : E0 sys L n < Asym sys L n p) :
    (datum sys L p₀ v).ofLp p = 0 := by
  rw [datum_apply]
  have : datumSym sys L p₀ p = 0 := by
    unfold datumSym; rw [if_neg]; intro h; linarith [h.2]
  rw [this]; simp

omit [Fintype ν] in
/-- `‖(1+A)^{r} A_{p₀}^E v‖² ≤ Σ_{A ≤ E₀} (1+A)^{2r+2} |v|²` for `r ≥ 0`. -/
lemma wt_datum_sq_le_moment {r : ℝ} (v : En eta n) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) r (datum sys L p₀ v)‖ ^ 2 ≤
      ∑ p, if Asym sys L n p ≤ E0 sys L n then
        (1 + Asym sys L n p) ^ (2 * (r + 1)) * ‖v.ofLp p‖ ^ 2 else 0 := by
  rw [norm_sq_wt]
  refine Finset.sum_le_sum fun p _ => ?_
  have hA0 := Asym_nonneg sys L n p
  have h1 : 0 < 1 + Asym sys L n p := by linarith
  rw [datum_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (datumSym_nonneg sys L p₀ p), mul_pow]
  have hle := datumSym_le sys L p₀ p
  split_ifs with h
  · rw [if_pos h] at hle
    have hd0 := datumSym_nonneg sys L p₀ p
    have hd : datumSym sys L p₀ p ^ 2 ≤ (1 + Asym sys L n p) ^ 2 :=
      pow_le_pow_left₀ hd0 (by linarith) 2
    have hpow : ((1 + Asym sys L n p) ^ r) ^ 2 * (1 + Asym sys L n p) ^ 2 =
        (1 + Asym sys L n p) ^ (2 * (r + 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul h1.le, ← Real.rpow_add h1]
      congr 1
      push_cast
      ring
    calc ((1 + Asym sys L n p) ^ r) ^ 2 * (datumSym sys L p₀ p ^ 2 * ‖v.ofLp p‖ ^ 2)
        ≤ ((1 + Asym sys L n p) ^ r) ^ 2 * ((1 + Asym sys L n p) ^ 2 * ‖v.ofLp p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd (sq_nonneg _))
            (sq_nonneg _)
      _ = _ := by rw [← hpow]; ring
  · rw [if_neg h] at hle
    have : datumSym sys L p₀ p = 0 := le_antisymm hle (datumSym_nonneg sys L p₀ p)
    rw [this]
    simp

omit [Fintype ν] in
/-- `‖A_{p₀}^E v‖ ≤ Θ(v) = ‖(1+A) v‖`. -/
lemma norm_datum_le (v : En eta n) :
    ‖datum sys L p₀ v‖ ≤ ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  have h2 : ‖datum sys L p₀ v‖ ^ 2 ≤ ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ ^ 2 := by
    rw [norm_sq_En, norm_sq_wt]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [datum_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (datumSym_nonneg sys L p₀ p), mul_pow, Real.rpow_one]
    have hle := datumSym_le sys L p₀ p
    have hA0 := Asym_nonneg sys L n p
    have hd0 := datumSym_nonneg sys L p₀ p
    have hd : datumSym sys L p₀ p ≤ 1 + Asym sys L n p := by
      split_ifs at hle <;> linarith
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd0 hd 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The dyadic constant `C_r = (1 + η/2)^{2r} (1 + 32 η 4^{4r-5}/(2^{4r-5} - 1))` with `r = r' + 1`. -/
noncomputable def momentConst (eta : ℕ) (r : ℝ) : ℝ :=
  (1 + (eta : ℝ) / 2) ^ (2 * r) *
    (1 + 32 * eta * (4 : ℝ) ^ (4 * r - 5) / ((2 : ℝ) ^ (4 * r - 5) - 1))

/-- The momentum scale `Λ = (2 m_max E₀)^{1/2}` of the truncated datum. -/
noncomputable def Lam (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (2 * mmax sys * E0 sys L n)

omit [Fintype ν] in
/-- **`cor:spectail`, weighted norms of the datum**: for a good `v` and `r' > 1/4`,
`‖(1+A)^{r'} A_{p₀}^E v‖² ≤ C_{r'+1} (Cg Ξ)² Λ^{4r'-1}`, provided `Λ ≥ 1`. -/
theorem wt_datum_sq_le (hL : 0 < L) {Cg Ξ r' : ℝ} (hCgΞ : 0 ≤ Cg * Ξ) (hr' : 1 / 4 < r')
    (hΛ : 1 ≤ Lam sys L n) (v : En eta n) (hv : IsGood sys L Cg Ξ v) :
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) r' (datum sys L p₀ v)‖ ^ 2 ≤
      momentConst eta (r' + 1) * (Cg * Ξ) ^ 2 * Lam sys L n ^ (4 * r' - 1) := by
  refine (wt_datum_sq_le_moment sys L p₀ v).trans ?_
  have hm := fun a => sys.mass_pos a
  have hkab := fun (μ : FinitePlaneWaveMode n) => kabs_nonneg hL μ
  have key := FSDatum.moment_le_of_tails (η := eta) (Asym sys L n)
    (fun a x => finitePlaneWaveKabs (2 * Real.pi / L) n (x a)) v.ofLp
    (cA := (eta : ℝ) / 2) (E₀ := E0 sys L n) (Λ := Lam sys L n) (T := Cg * Ξ) (r := r' + 1)
    (by positivity) (Asym_nonneg sys L n) hΛ (by linarith) hCgΞ
    (fun x R hR hx => by
      -- `A ≤ (η/2) R²` when every register momentum is at most `R`
      unfold Asym massKineticSymbol
      have h1 : ∀ a ∈ Finset.univ, finitePlaneWaveKabs (2 * Real.pi / L) n (x a) ^ 2 / sys.mass a ≤
          R ^ 2 := by
        intro a _
        have hk := hx a
        have hk0 := hkab (x a)
        have hsq : finitePlaneWaveKabs (2 * Real.pi / L) n (x a) ^ 2 ≤ R ^ 2 :=
          pow_le_pow_left₀ hk0 hk 2
        rw [div_le_iff₀ (hm a)]
        nlinarith [sys.one_le_mass a, sq_nonneg R]
      have h2 := Finset.sum_le_sum h1
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
      nlinarith)
    (fun x hx a => by
      -- every register momentum is at most `Λ` on `A ≤ E₀`
      have hc := component_sq_le_mass_mul_massKineticSymbol hm
        (finitePlaneWaveKabs (2 * Real.pi / L) n) x a
      have hA : massKineticSymbol sys.mass (finitePlaneWaveKabs (2 * Real.pi / L) n) x =
          2 * Asym sys L n x := by unfold Asym; ring
      rw [hA] at hc
      have hma := mass_le_mmax sys a
      have hE0 : 0 ≤ E0 sys L n := by
        unfold E0; have := one_le_mmax sys; positivity
      have hsq : finitePlaneWaveKabs (2 * Real.pi / L) n (x a) ^ 2 ≤ 2 * mmax sys * E0 sys L n := by
        have hA0 := Asym_nonneg sys L n x
        have h := mul_le_mul hma (show 2 * Asym sys L n x ≤ 2 * E0 sys L n by linarith)
          (by linarith) (by linarith [one_le_mmax sys])
        linarith
      unfold Lam
      exact Real.le_sqrt_of_sq_le hsq)
    (by
      have h := hv.1
      have hn : ‖v‖ ≤ Cg * Ξ := by linarith [norm_nonneg (FSSpectral.wt (sb eta n) (Asym sys L n) 1 v)]
      rw [← norm_sq_En]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2)
    (fun a l hl => by
      have h := (hv.2 a l hl).1
      rw [← norm_sq_regTail]
      have hl0 : 0 < l := by linarith
      calc ‖regTail L a l v‖ ^ 2 ≤ (Cg * Ξ * l ^ (-(5 / 2 : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = (Cg * Ξ) ^ 2 / l ^ 5 := by
            rw [mul_pow, ← Real.rpow_natCast (l ^ (-(5 / 2 : ℝ))), ← Real.rpow_mul hl0.le]
            rw [show (-(5 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -((5 : ℕ) : ℝ) by norm_num,
              Real.rpow_neg hl0.le, Real.rpow_natCast]
            field_simp)
  refine key.trans (le_of_eq ?_)
  unfold momentConst
  rw [show 4 * (r' + 1) - 5 = 4 * r' - 1 by ring]

end Datum

end FSGalerkin
