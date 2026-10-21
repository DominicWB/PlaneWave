import PlaneWave.SamePair.Package

/-!
# `lem:obs2` (restated): the second-order observable correction

On the cube `E_n`, with `A_{p₀}` the kinetic energy of the projectile register (`Aproj`):

* `obsK`, the kernel of `[Σ₂^bb, A_{p₀}]` (`comm_Sig2bb_Aproj`);
* **`obs_hop_le`** (eq:com in bound form, lattice units): for a hop of channel `j` moving `p₀`,
  `|ΔA_{p₀}| ≤ |ΔE| + g² |θ| |Π_j| / M̄_j` (`ΔA_{p₀} - (μ_j/m_{p₀}) ΔE = ± (g²/M̄_j) θ·Π_j`, the
  pair momentum `Π_j` conserved by the hop; `ΔA_{p₀} = ΔE` for the one-body channel of `p₀`, and
  `ΔA_{p₀} = 0` for channels not moving `p₀`);
* with the formal floor `g²|θ|/μ_j ≤ |ΔE|` of the gapped elements: `|obsK(q,p)| ≤
  (1 + |Π_j|) chbT n⁻³` (`norm_obsK_le`), the flat part and the centre-of-mass part at once;
* the fibre trace bound `chan_trace_le` (`lem:paird` with the weight `(1 + |k_lead|²)^{3/2}`, whose
  fibre sums over the cube are `≤ 125 (⌊log₂ n⌋ + 2)`, `sum_box_inv32_le`) and the weight bound
  `(1 + |k_lead|²)^{3/2} (1 + |Π_j|) ≤ 3 κ² (1 + A)²` (`wl_pi_le`);
* **`obs2`**: `|⟨u, [Σ₂^bb, A_{p₀}] u⟩| ≤ C_obs2(n) ‖(1 + A) u‖²` for every cube state, and
  **`obs2_good`**: `≤ C_obs2(n) M²` for every good state (`IsGood 1 M u`), with
  `C_obs2(n) = #Ch · chbT n⁻³ · 125 (⌊log₂ n⌋ + 2) · 3 κ² = O(n⁻³ log n)` (`pl_Cobs2`): the
  `C_ε Ξ² K^{-3+ε}` of `lem:obs2`, with a logarithm instead of `K^ε`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## eq:com in bound form -/

section Com

variable (sys : CoulombSystem eta ν)

/-- The pair momentum `|k_a + k_b|` of a pair channel (`0` for a one-body channel). -/
noncomputable def piC : Ch eta → Cf eta → ℝ
  | .inl _, _ => 0
  | .inr pr, k => FSChannel.rho (k pr.1.1 + k pr.1.2)

/-- The total mass `M̄ = m_a + m_b` of a pair channel (`1` for a one-body channel). -/
noncomputable def Mtot : Ch eta → ℝ
  | .inl _ => 1
  | .inr pr => sys.mass pr.1.1 + sys.mass pr.1.2

/-- The lattice symbol of `A_{p₀}`: `g² |k_{p₀}|²/(2 m_{p₀})`. -/
noncomputable def regL (g : ℝ) (p₀ : Fin eta) (k : Cf eta) : ℝ :=
  g ^ 2 / (2 * sys.mass p₀) * nsq (k p₀)

omit [Fintype ν] in
lemma piC_nonneg (j : Ch eta) (k : Cf eta) : 0 ≤ piC j k := by
  cases j with
  | inl a => exact le_rfl
  | inr pr => exact FSChannel.rho_nonneg _

omit [Fintype ν] in
lemma Mtot_pos (j : Ch eta) : 0 < Mtot sys j := by
  cases j with
  | inl a => simp [Mtot]
  | inr pr =>
    have := sys.mass_pos pr.1.1
    have := sys.mass_pos pr.1.2
    simp only [Mtot]; linarith

omit [Fintype ν] in
lemma mu_piC_le (j : Ch eta) (k : Cf eta) : muCh sys j / Mtot sys j * piC j k ≤ piC j k := by
  cases j with
  | inl a => simp [piC]
  | inr pr =>
    have ha := sys.mass_pos pr.1.1
    have hb := sys.mass_pos pr.1.2
    have h0 := piC_nonneg (.inr pr) k
    have h1 : muCh sys (.inr pr) / Mtot sys (.inr pr) ≤ 1 := by
      simp only [muCh, Mtot]
      rw [div_le_one (by positivity), div_le_iff₀ (by positivity)]
      nlinarith
    calc muCh sys (.inr pr) / Mtot sys (.inr pr) * piC (.inr pr) k ≤ 1 * piC (.inr pr) k :=
          mul_le_mul_of_nonneg_right h1 h0
      _ = _ := one_mul _

omit [Fintype ν] in
/-- The pair momentum is conserved by a hop of its channel. -/
lemma piC_hop (j : Ch eta) (k' : Cf eta) (θ : Lattice3) : piC j (k' + tr j θ) = piC j k' := by
  cases j with
  | inl a => rfl
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    simp only [piC]
    congr 1
    simp only [tr, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne,
      Pi.single_eq_of_ne hne.symm]
    abel

omit [Fintype ν] in
lemma piC_onCh {j : Ch eta} {k k' : Cf eta} (h : OnCh j k k') : piC j k = piC j k' := by
  rw [show k = k' + tr j (k (lead j) - k' (lead j)) from h, piC_hop]

omit [Fintype ν] in
/-- Cauchy–Schwarz on the lattice: `|θ·w| ≤ |θ| |w|`. -/
lemma abs_dot_le (θ w : Lattice3) :
    |∑ i, (θ i : ℝ) * (w i : ℝ)| ≤ FSChannel.rho θ * FSChannel.rho w := by
  unfold FSChannel.rho
  rw [← Real.sqrt_mul (FSLattice.lsq_nonneg θ)]
  apply Real.abs_le_sqrt
  rw [FSLattice.lsq_eq_sum, FSLattice.lsq_eq_sum]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

omit [Fintype ν] in
/-- **eq:com in bound form**: `|ΔA_{p₀}| ≤ |ΔE| + g² |θ| |Π_j| / M̄_j` for every hop. -/
theorem obs_hop_le (g : ℝ) (p₀ : Fin eta) (j : Ch eta) (k' : Cf eta) (θ : Lattice3) :
    |regL sys g p₀ (k' + tr j θ) - regL sys g p₀ k'| ≤
      |E sys.mass g (k' + tr j θ) - E sys.mass g k'| +
        g ^ 2 * FSChannel.rho θ * piC j k' / Mtot sys j := by
  have hR0 : 0 ≤ g ^ 2 * FSChannel.rho θ * piC j k' / Mtot sys j := by
    have := Mtot_pos sys j
    have := piC_nonneg j k'
    have := FSChannel.rho_nonneg θ
    positivity
  by_cases hp : p₀ ∈ moved j
  swap
  · have h0 : (k' + tr j θ) p₀ = k' p₀ := by
      rw [Pi.add_apply, tr_apply_not_moved j θ hp, add_zero]
    unfold regL
    rw [h0, sub_self, abs_zero]
    have := abs_nonneg (E sys.mass g (k' + tr j θ) - E sys.mass g k')
    linarith
  cases j with
  | inl a =>
    have ha : p₀ = a := by simpa [moved] using hp
    subst ha
    have e : regL sys g p₀ (k' + tr (.inl p₀) θ) - regL sys g p₀ k' =
        E sys.mass g (k' + tr (.inl p₀) θ) - E sys.mass g k' := by
      rw [show tr (.inl p₀ : Ch eta) θ = Pi.single p₀ θ from rfl, E_add_single_sub]
      unfold regL
      rw [add_single_self]
      ring
    rw [e]
    linarith
  | inr pr =>
    have hne : pr.1.1 ≠ pr.1.2 := ne_of_lt pr.2
    have ha := sys.mass_pos pr.1.1
    have hb := sys.mass_pos pr.1.2
    have hE := E_hop sys g (.inr pr) k' θ
    have e1 : (k' + tr (.inr pr) θ) pr.1.1 = k' pr.1.1 + θ := by
      simp [tr, Pi.single_eq_of_ne hne]
    have e2 : (k' + tr (.inr pr) θ) pr.1.2 = k' pr.1.2 + -θ := by
      simp [tr, Pi.single_eq_of_ne hne.symm, sub_eq_add_neg]
    have hdot := abs_dot_le θ (k' pr.1.1 + k' pr.1.2)
    have hsum : ∑ i, (θ i : ℝ) * (((k' pr.1.1 + k' pr.1.2) i : ℤ) : ℝ) =
        ∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.add_apply, Int.cast_add]
    rw [hsum] at hdot
    have hM : Mtot sys (.inr pr) = sys.mass pr.1.1 + sys.mass pr.1.2 := rfl
    have hpi : piC (.inr pr) k' = FSChannel.rho (k' pr.1.1 + k' pr.1.2) := rfl
    have hmu0 : 0 ≤ muCh sys (.inr pr) := (muCh_pos sys _).le
    simp only [moved, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · -- `p₀ = a`
      have hid : regL sys g pr.1.1 (k' + tr (.inr pr) θ) - regL sys g pr.1.1 k' =
          muCh sys (.inr pr) / sys.mass pr.1.1 *
              (E sys.mass g (k' + tr (.inr pr) θ) - E sys.mass g k') +
            g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
              ∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ)) := by
        rw [hE]
        unfold regL
        rw [e1]
        simp only [nsq, FSLattice.slabF, FSLattice.lsq, cCh, muCh, Pi.add_apply, Int.cast_add,
          Fin.sum_univ_three]
        field_simp
        ring
      have hμ : muCh sys (.inr pr) / sys.mass pr.1.1 ≤ 1 := by
        simp only [muCh]
        rw [div_le_one ha, div_le_iff₀ (by positivity)]
        nlinarith
      rw [hid, hM, hpi]
      calc |muCh sys (.inr pr) / sys.mass pr.1.1 *
              (E sys.mass g (k' + tr (.inr pr) θ) - E sys.mass g k') +
            g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
              ∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ))|
          ≤ |muCh sys (.inr pr) / sys.mass pr.1.1 *
              (E sys.mass g (k' + tr (.inr pr) θ) - E sys.mass g k')| +
            |g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
              ∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ))| := abs_add_le _ _
        _ ≤ 1 * |E sys.mass g (k' + tr (.inr pr) θ) - E sys.mass g k'| +
            g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
              (FSChannel.rho θ * FSChannel.rho (k' pr.1.1 + k' pr.1.2)) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ muCh sys (.inr pr) / sys.mass pr.1.1),
              abs_of_nonneg (by positivity : 0 ≤ g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2))]
            gcongr
        _ = _ := by ring
    · -- `p₀ = b`
      have hid : regL sys g pr.1.2 (k' + tr (.inr pr) θ) - regL sys g pr.1.2 k' =
          muCh sys (.inr pr) / sys.mass pr.1.2 *
              (E sys.mass g (k' + tr (.inr pr) θ) - E sys.mass g k') -
            g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
              ∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ)) := by
        rw [hE]
        unfold regL
        rw [e2]
        simp only [nsq, FSLattice.slabF, FSLattice.lsq, cCh, muCh, Pi.add_apply, Pi.neg_apply,
          Int.cast_add, Int.cast_neg, Fin.sum_univ_three]
        field_simp
        ring
      have hμ : muCh sys (.inr pr) / sys.mass pr.1.2 ≤ 1 := by
        simp only [muCh]
        rw [div_le_one hb, div_le_iff₀ (by positivity)]
        nlinarith
      rw [hid, hM, hpi]
      calc |muCh sys (.inr pr) / sys.mass pr.1.2 *
              (E sys.mass g (k' + tr (.inr pr) θ) - E sys.mass g k') -
            g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
              ∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ))|
          ≤ |muCh sys (.inr pr) / sys.mass pr.1.2 *
              (E sys.mass g (k' + tr (.inr pr) θ) - E sys.mass g k')| +
            |g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
              ∑ i, (θ i : ℝ) * ((k' pr.1.1 i : ℝ) + (k' pr.1.2 i : ℝ))| := abs_sub _ _
        _ ≤ 1 * |E sys.mass g (k' + tr (.inr pr) θ) - E sys.mass g k'| +
            g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2) *
              (FSChannel.rho θ * FSChannel.rho (k' pr.1.1 + k' pr.1.2)) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ muCh sys (.inr pr) / sys.mass pr.1.2),
              abs_of_nonneg (by positivity : 0 ≤ g ^ 2 / (sys.mass pr.1.1 + sys.mass pr.1.2))]
            gcongr
        _ = _ := by ring

end Com

/-! ## The kernel of `[Σ₂^bb, A_{p₀}]` -/

section Kernel

variable (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) (p₀ : Fin eta)

/-- The kernel of `[Σ₂^bb, A_{p₀}] = Σ₂^bb A_{p₀} - A_{p₀} Σ₂^bb`. -/
noncomputable def obsK (q p : Cfg eta n) : ℂ :=
  ((Aproj sys L p₀ p - Aproj sys L p₀ q : ℝ) : ℂ) * sgK sys L n q p

open Classical in
/-- The majorant of `obsK` on channel `j`. -/
noncomputable def obsMaj (j : Ch eta) (q p : Cfg eta n) : ℝ :=
  if p₀ ∈ moved j ∧ OnCh j (cidx n q) (cidx n p) then
    chbT sys L / (n : ℝ) ^ 3 * (1 + piC j (cidx n p)) else 0

variable {sys L n p₀}

omit [Fintype ν] in
lemma Aproj_eq (q : Cfg eta n) : Aproj sys L p₀ q = regL sys (gF L) p₀ (cidx n q) := by
  unfold Aproj regL
  rw [kabs_eq_lattice, mul_pow, Real.sq_sqrt (latticeNormSq_nonneg _)]
  have e : (2 * Real.pi / L) = gF L := rfl
  rw [e]
  change gF L ^ 2 * nsq (cidx n q p₀) / (2 * sys.mass p₀) = _
  ring

theorem comm_Sig2bb_Aproj :
    Sig2bb sys L n ∘ₗ FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) -
      FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) ∘ₗ Sig2bb sys L n =
      FSKernel.kop (obsK sys L n p₀) := by
  have h := FSKernel.kop_comm_dg (fun q => (Aproj sys L p₀ q : ℂ)) (sgK sys L n)
  have h2 : Sig2bb sys L n = FSKernel.kop (sgK sys L n) := rfl
  rw [h2, ← neg_sub, h]
  ext u q
  simp only [LinearMap.neg_apply, FSKernel.kop_apply, PiLp.neg_apply, obsK]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  push_cast
  ring

lemma obsMaj_nonneg (hL : 0 < L) (j : Ch eta) (q p : Cfg eta n) :
    0 ≤ obsMaj sys L n p₀ j q p := by
  unfold obsMaj
  have := chbT_nonneg (sys := sys) hL
  have := piC_nonneg j (cidx n p)
  split_ifs
  · positivity
  · exact le_rfl

/-- **The kernel bound**: `|obsK(q, p)| ≤ Σ_j [p₀ moved, q ~_j p] (1 + |Π_j|) chbT n⁻³`. -/
theorem norm_obsK_le (hL : 0 < L) (hn : 2 ≤ n) (q p : Cfg eta n) :
    ‖obsK sys L n p₀ q p‖ ≤ ∑ j, obsMaj sys L n p₀ j q p := by
  classical
  have hsum0 : 0 ≤ ∑ j, obsMaj sys L n p₀ j q p :=
    Finset.sum_nonneg fun j _ => obsMaj_nonneg hL j q p
  by_cases h0 : sgK sys L n q p = 0
  · unfold obsK; rw [h0, mul_zero, norm_zero]; exact hsum0
  obtain ⟨hg, -, -⟩ := sgK_ne_zero h0
  obtain ⟨hne, j, hj, hfl⟩ := hg
  have hgap : gapC sys L n q p := ⟨hne, j, hj, hfl⟩
  have hA : Asym sys L n q ≠ Asym sys L n p := gapC_ne hL hgap
  have hs : sgK sys L n q p = hbC sys L n q p / ((Asym sys L n q - Asym sys L n p : ℝ) : ℂ) := by
    unfold sgK FSKernel.divK hgapK
    rw [if_neg hA, if_pos hgap]
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
    have hb := norm_hbC_le (sys := sys) hL hn q p
    have hval : obsMaj sys L n p₀ j q p = chbT sys L / (n : ℝ) ^ 3 * (1 + piC j (cidx n p)) := by
      unfold obsMaj; rw [if_pos ⟨hpm, hj⟩]
    refine le_trans ?_ (le_trans (le_of_eq hval.symm) (Finset.single_le_sum
      (f := fun j => obsMaj sys L n p₀ j q p) (fun j _ => obsMaj_nonneg hL j q p)
      (Finset.mem_univ j)))
    unfold obsK
    rw [hs, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    calc |Aproj sys L p₀ p - Aproj sys L p₀ q| * (‖hbC sys L n q p‖ /
          |Asym sys L n q - Asym sys L n p|)
        ≤ |Asym sys L n q - Asym sys L n p| * (1 + piC j (cidx n p)) *
            (chbT sys L / (n : ℝ) ^ 3 / |Asym sys L n q - Asym sys L n p|) := by
          gcongr
      _ = chbT sys L / (n : ℝ) ^ 3 * (1 + piC j (cidx n p)) := by field_simp
  · have h1 : cidx n q p₀ = cidx n p p₀ := by
      rw [hk, Pi.add_apply, tr_apply_not_moved j _ hpm, add_zero]
    have h2 : Aproj sys L p₀ q = Aproj sys L p₀ p := by
      rw [Aproj_eq, Aproj_eq]; unfold regL; rw [h1]
    unfold obsK
    rw [h2, sub_self, Complex.ofReal_zero, zero_mul, norm_zero]
    exact hsum0

end Kernel

/-! ## The fibre trace bound -/

section Trace

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ}

omit [Fintype ν] in
/-- Coordinates of cube configurations: `|k_c|² ≤ 3 n²`. -/
lemma lsq_cidx_le (p : Cfg eta n) (c : Fin eta) : FSLattice.lsq (cidx n p c) ≤ 3 * (n : ℝ) ^ 2 := by
  have hp : InP (n : ℝ) (cidx n p) := inP_of_mem_cube (finiteConfigLatticeIndex_mem_cube eta n p)
  have hc : ∀ i, ((cidx n p c i : ℤ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := fun i => by
    have h1 := hp c i
    have h2 := sq_abs ((cidx n p c i : ℤ) : ℝ)
    have h3 : |((cidx n p c i : ℤ) : ℝ)| ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    linarith
  unfold FSLattice.lsq
  linarith [hc 0, hc 1, hc 2]

/-- The weight `(1 + |x|²)^{3/2}`. -/
noncomputable def w32 (x : Lattice3) : ℝ := (1 + FSLattice.lsq x) * Real.sqrt (1 + FSLattice.lsq x)

omit [Fintype ν] in
lemma w32_pos (x : Lattice3) : 0 < w32 x := by
  unfold w32
  have := FSLattice.lsq_nonneg x
  have : 0 < Real.sqrt (1 + FSLattice.lsq x) := Real.sqrt_pos.mpr (by linarith)
  positivity

omit [Fintype ν] in
/-- **The cube sum of `(1 + |x|²)^{-3/2}`**: `≤ 125 (⌊log₂ n⌋ + 2)` over transfers with
`|x|² ≤ 3 n²`. -/
theorem sum_box_inv32_le (hn : 1 ≤ n) (S : Finset Lattice3)
    (hS : ∀ x ∈ S, FSLattice.lsq x ≤ 3 * (n : ℝ) ^ 2) :
    ∑ x ∈ S, (w32 x)⁻¹ ≤ 125 * (Nat.log 2 n + 2) := by
  classical
  have hnn : ∀ x ∈ S, 0 ≤ (w32 x)⁻¹ := fun x _ => (inv_pos.mpr (w32_pos x)).le
  set I := Nat.log 2 n + 1
  have hshell : ∀ x ∈ S, ∃ i ≤ I, (4 : ℝ) ^ i ≤ 1 + FSLattice.lsq x ∧
      1 + FSLattice.lsq x ≤ 4 ^ (i + 1) := by
    intro x hx
    have h1 : (1 : ℝ) ≤ 1 + FSLattice.lsq x := by linarith [FSLattice.lsq_nonneg x]
    obtain ⟨i, hi1, hi2⟩ := exists_shell h1
    refine ⟨i, ?_, hi1, hi2⟩
    by_contra h
    push Not at h
    have hk : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have hk' : (n : ℝ) < 2 ^ (Nat.log 2 n + 1) := by exact_mod_cast hk
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1' : (n : ℝ) ^ 2 < 4 ^ (Nat.log 2 n + 1) := by
      rw [← FSBand.two_pow_sq]; exact pow_lt_pow_left₀ hk' hn0 two_ne_zero
    have h2 : (4 : ℝ) ^ (Nat.log 2 n + 2) ≤ 4 ^ i := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (4 : ℝ) ^ (Nat.log 2 n + 2) = 4 * 4 ^ (Nat.log 2 n + 1) := by ring
    have := hS x hx
    nlinarith
  refine (FSLattice.sum_le_sum_shells S _ hnn (fun i x => (4 : ℝ) ^ i ≤ 1 + FSLattice.lsq x ∧
    1 + FSLattice.lsq x ≤ 4 ^ (i + 1)) I hshell).trans ?_
  have hper : ∀ i ∈ Finset.range (I + 1),
      ∑ x ∈ S.filter (fun x => (4 : ℝ) ^ i ≤ 1 + FSLattice.lsq x ∧ 1 + FSLattice.lsq x ≤ 4 ^ (i + 1)),
        (w32 x)⁻¹ ≤ 125 := by
    intro i _
    set Si := S.filter (fun x => (4 : ℝ) ^ i ≤ 1 + FSLattice.lsq x ∧ 1 + FSLattice.lsq x ≤ 4 ^ (i + 1))
    have h1 : ∀ x ∈ Si, (w32 x)⁻¹ ≤ ((8 : ℝ) ^ i)⁻¹ := by
      intro x hx
      have hs := (Finset.mem_filter.mp hx).2.1
      apply inv_anti₀ (by positivity)
      unfold w32
      have hsq : (2 : ℝ) ^ i ≤ Real.sqrt (1 + FSLattice.lsq x) := by
        apply Real.le_sqrt_of_sq_le; rw [FSBand.two_pow_sq]; exact hs
      calc (8 : ℝ) ^ i = 4 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
        _ ≤ (1 + FSLattice.lsq x) * Real.sqrt (1 + FSLattice.lsq x) :=
            mul_le_mul hs hsq (by positivity) (by linarith [FSLattice.lsq_nonneg x])
    have hsub : Si ⊆ FSLattice.box (2 ^ (i + 1)) := by
      intro x hx
      apply FSLattice.mem_box_of_lsq_le
      have := (Finset.mem_filter.mp hx).2.2
      push_cast
      rw [FSBand.two_pow_sq]
      linarith
    have hcard : (Si.card : ℝ) ≤ 125 * 8 ^ i := by
      have h1 : Si.card ≤ (2 * 2 ^ (i + 1) + 1) ^ 3 :=
        (Finset.card_le_card hsub).trans_eq (FSLattice.card_box _)
      have h2 : ((2 * 2 ^ (i + 1) + 1 : ℕ) : ℝ) ≤ 5 * 2 ^ i := by
        push_cast
        have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
        rw [pow_succ]; linarith
      calc (Si.card : ℝ) ≤ (((2 * 2 ^ (i + 1) + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast h1
        _ = ((2 * 2 ^ (i + 1) + 1 : ℕ) : ℝ) ^ 3 := by push_cast; ring
        _ ≤ (5 * 2 ^ i) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
        _ = 125 * 8 ^ i := by rw [mul_pow, ← pow_mul, mul_comm i 3, pow_mul]; norm_num
    calc ∑ x ∈ Si, (w32 x)⁻¹ ≤ ∑ _x ∈ Si, ((8 : ℝ) ^ i)⁻¹ := Finset.sum_le_sum h1
      _ = (Si.card : ℝ) * ((8 : ℝ) ^ i)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 125 * 8 ^ i * ((8 : ℝ) ^ i)⁻¹ := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 125 := by field_simp
  calc ∑ i ∈ Finset.range (I + 1), ∑ x ∈ S.filter (fun x => (4 : ℝ) ^ i ≤ 1 + FSLattice.lsq x ∧
        1 + FSLattice.lsq x ≤ 4 ^ (i + 1)), (w32 x)⁻¹ ≤ ∑ _i ∈ Finset.range (I + 1), (125 : ℝ) :=
        Finset.sum_le_sum hper
    _ = 125 * (Nat.log 2 n + 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; simp only [I]; push_cast; ring

/-- The fibre weight of channel `j`: `(1 + |k_lead|²)^{3/2}`. -/
noncomputable def wl (j : Ch eta) (q : Cfg eta n) : ℝ := w32 (cidx n q (lead j))

omit [Fintype ν] in
open Classical in
/-- The fibre sums of `1/wl` over the cube. -/
lemma fibre_wl_le (hn : 1 ≤ n) (j : Ch eta) (q : Cfg eta n) :
    ∑ p ∈ Finset.univ.filter (fun p : Cfg eta n => OnCh j (cidx n q) (cidx n p)), (wl j p)⁻¹ ≤
      125 * (Nat.log 2 n + 2) := by
  classical
  set F := Finset.univ.filter (fun p : Cfg eta n => OnCh j (cidx n q) (cidx n p))
  have hinj : Set.InjOn (fun p : Cfg eta n => cidx n p (lead j)) F := by
    intro p hp p' hp' h
    have h1 : OnCh j (cidx n p) (cidx n q) := onCh_symm (Finset.mem_filter.mp hp).2
    have h2 : OnCh j (cidx n p') (cidx n q) := onCh_symm (Finset.mem_filter.mp hp').2
    apply chT_injOn j q h1 h2
    show cidx n p (lead j) - cidx n q (lead j) = cidx n p' (lead j) - cidx n q (lead j)
    rw [show cidx n p (lead j) = cidx n p' (lead j) from h]
  have e : ∑ p ∈ F, (wl j p)⁻¹ = ∑ x ∈ F.image (fun p : Cfg eta n => cidx n p (lead j)), (w32 x)⁻¹ := by
    rw [Finset.sum_image hinj]; rfl
  rw [e]
  apply sum_box_inv32_le hn
  intro x hx
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hx
  exact lsq_cidx_le p (lead j)

omit [Fintype ν] in
open Classical in
lemma fibre_wl_le' (hn : 1 ≤ n) (j : Ch eta) (p : Cfg eta n) :
    ∑ q ∈ Finset.univ.filter (fun q : Cfg eta n => OnCh j (cidx n q) (cidx n p)), (wl j q)⁻¹ ≤
      125 * (Nat.log 2 n + 2) := by
  classical
  have e : Finset.univ.filter (fun q : Cfg eta n => OnCh j (cidx n q) (cidx n p)) =
      Finset.univ.filter (fun q : Cfg eta n => OnCh j (cidx n p) (cidx n q)) := by
    ext q; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨onCh_symm, onCh_symm⟩
  rw [e]
  exact fibre_wl_le hn j p

omit [Fintype ν] in
open Classical in
/-- **The fibre trace bound** (`lem:paird`, flat form with a fibre-constant weight `c`). -/
theorem chan_trace_le (hn : 1 ≤ n) (j : Ch eta) (f c : Cfg eta n → ℝ)
    (hc : ∀ q, 0 ≤ c q) (hcc : ∀ q p, OnCh j (cidx n q) (cidx n p) → c q = c p) :
    ∑ q, ∑ p, (if OnCh j (cidx n q) (cidx n p) then f q * f p * c p else 0) ≤
      125 * (Nat.log 2 n + 2) * ∑ q, wl j q * c q * f q ^ 2 := by
  classical
  set g : Cfg eta n → ℝ := fun q => f q * Real.sqrt (c q)
  have hpt : ∀ q p, (if OnCh j (cidx n q) (cidx n p) then f q * f p * c p else 0) =
      (if OnCh j (cidx n q) (cidx n p) then g q * g p else 0) := by
    intro q p
    split_ifs with h
    · simp only [g]
      have hs := Real.mul_self_sqrt (hc p)
      rw [hcc q p h]
      have : f q * Real.sqrt (c p) * (f p * Real.sqrt (c p)) = f q * f p * (Real.sqrt (c p) *
        Real.sqrt (c p)) := by ring
      rw [this, hs]
    · rfl
  simp_rw [hpt]
  have h := FSFlux.fibre_amgm (Finset.univ : Finset (Cfg eta n))
    (fun q p => OnCh j (cidx n q) (cidx n p)) (wl j) (fun q => w32_pos _)
    (N := 125 * (Nat.log 2 n + 2)) (fun q _ => fibre_wl_le hn j q) (fun p _ => fibre_wl_le' hn j p)
    g g
  refine h.trans (le_of_eq ?_)
  have e : ∀ q, wl j q * g q ^ 2 = wl j q * c q * f q ^ 2 := fun q => by
    simp only [g]
    rw [mul_pow, Real.sq_sqrt (hc q)]; ring
  simp only [e]
  ring

end Trace

/-! ## The weight bound and `lem:obs2` -/

section Obs2

variable {sys : CoulombSystem eta ν} {L : ℝ} {n : ℕ} {p₀ : Fin eta}

variable (sys L) in
/-- `κ = 1 + 2 m_top/g²`: `1 + |k_c|² ≤ κ (1 + A)` for every register. -/
noncomputable def kapW : ℝ := 1 + 2 * mtop sys / gF L ^ 2

omit [Fintype ν] in
lemma one_le_kapW (hL : 0 < L) : 1 ≤ kapW sys L := by
  unfold kapW
  have := one_le_mtop sys
  have := gF_pos hL
  have : 0 ≤ 2 * mtop sys / gF L ^ 2 := by positivity
  linarith

omit [Fintype ν] in
lemma one_add_lsq_le (hL : 0 < L) (q : Cfg eta n) (c : Fin eta) :
    1 + FSLattice.lsq (cidx n q c) ≤ kapW sys L * (1 + Asym sys L n q) := by
  have hg := gF_pos hL
  have hm := sys.mass_pos c
  have hmt := mass_le_mtop sys c
  have hA0 := Asym_nonneg (sys := sys) (L := L) q
  have hterm : gF L ^ 2 / (2 * sys.mass c) * nsq (cidx n q c) ≤ Asym sys L n q := by
    rw [Asym_eq_Ek]
    unfold Ek E
    exact Finset.single_le_sum (f := fun c => gF L ^ 2 / (2 * sys.mass c) * nsq (cidx n q c))
      (fun c _ => by have := sys.mass_pos c; have := nsq_nonneg (cidx n q c); positivity)
      (Finset.mem_univ c)
  have hl : FSLattice.lsq (cidx n q c) = nsq (cidx n q c) := rfl
  have h1 : nsq (cidx n q c) ≤ 2 * mtop sys / gF L ^ 2 * Asym sys L n q := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : gF L ^ 2 / (2 * sys.mass c) * nsq (cidx n q c) * (2 * sys.mass c) =
        gF L ^ 2 * nsq (cidx n q c) := by field_simp
    have h2 := mul_le_mul_of_nonneg_right hterm (by positivity : (0 : ℝ) ≤ 2 * sys.mass c)
    rw [this] at h2
    have h3 : Asym sys L n q * (2 * sys.mass c) ≤ Asym sys L n q * (2 * mtop sys) :=
      mul_le_mul_of_nonneg_left (by linarith) hA0
    nlinarith
  unfold kapW
  rw [hl]
  have : 0 ≤ 2 * mtop sys / gF L ^ 2 := by have := one_le_mtop sys; positivity
  nlinarith

omit [Fintype ν] in
/-- **The weight bound**: `(1 + |k_lead|²)^{3/2} (1 + |Π_j|) ≤ 3 κ² (1 + A)²`. -/
lemma wl_pi_le (hL : 0 < L) (j : Ch eta) (q : Cfg eta n) :
    wl j q * (1 + piC j (cidx n q)) ≤ 3 * kapW sys L ^ 2 * (1 + Asym sys L n q) ^ 2 := by
  set X := kapW sys L * (1 + Asym sys L n q) with hX
  have hA0 := Asym_nonneg (sys := sys) (L := L) q
  have hκ := one_le_kapW (sys := sys) hL
  have hX1 : 1 ≤ X := by
    rw [hX]; nlinarith
  have hsX : 1 ≤ Real.sqrt X := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hX1
  have hreg : ∀ c, FSChannel.rho (cidx n q c) ≤ Real.sqrt X := fun c => by
    unfold FSChannel.rho
    apply Real.sqrt_le_sqrt
    have := one_add_lsq_le (sys := sys) hL q c
    linarith
  have hW : wl j q ≤ X * Real.sqrt X := by
    unfold wl w32
    have h1 := one_add_lsq_le (sys := sys) hL q (lead j)
    have h0 : 0 ≤ 1 + FSLattice.lsq (cidx n q (lead j)) := by
      linarith [FSLattice.lsq_nonneg (cidx n q (lead j))]
    exact mul_le_mul h1 (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg _) (by linarith)
  have hP : 1 + piC j (cidx n q) ≤ 3 * Real.sqrt X := by
    cases j with
    | inl a => simp only [piC]; linarith
    | inr pr =>
      simp only [piC]
      have := FSChannel.rho_add_le (cidx n q pr.1.1) (cidx n q pr.1.2)
      linarith [hreg pr.1.1, hreg pr.1.2]
  have hW0 : 0 ≤ wl j q := (w32_pos _).le
  calc wl j q * (1 + piC j (cidx n q)) ≤ X * Real.sqrt X * (3 * Real.sqrt X) :=
        mul_le_mul hW hP (by linarith [piC_nonneg j (cidx n q)]) (by positivity)
    _ = 3 * X * (Real.sqrt X * Real.sqrt X) := by ring
    _ = 3 * X * X := by rw [Real.mul_self_sqrt (by linarith)]
    _ = 3 * kapW sys L ^ 2 * (1 + Asym sys L n q) ^ 2 := by rw [hX]; ring

omit [Fintype ν] in
lemma sum3_comm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (F : α → β → γ → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ a, ∑ b, F a b c := by
  calc ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm

omit [Fintype ν] in
lemma norm_inner_kop_le' (κ : Cfg eta n → Cfg eta n → ℂ) (u : En eta n) :
    ‖⟪u, FSKernel.kop κ u⟫_ℂ‖ ≤ ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * ‖κ q p‖ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, FSKernel.kop_apply, Pi.star_apply, RCLike.star_def]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul, Complex.norm_conj]
  calc ‖∑ p, u.ofLp p * κ q p‖ * ‖u.ofLp q‖ ≤ (∑ p, ‖u.ofLp p‖ * ‖κ q p‖) * ‖u.ofLp q‖ := by
        gcongr
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun p _ => norm_mul _ _
    _ = ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * ‖κ q p‖ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun p _ => by ring

variable (sys L) in
/-- The constant of `lem:obs2`: `C_obs2 = #Ch · chbT n⁻³ · 125 (⌊log₂ n⌋ + 2) · 3 κ²`. -/
noncomputable def Cobs2 (n : ℕ) : ℝ :=
  Fintype.card (Ch eta) * (chbT sys L / (n : ℝ) ^ 3) * (125 * (Nat.log 2 n + 2)) *
    (3 * kapW sys L ^ 2)

/-- **`lem:obs2`** (restated): `|⟨u, [Σ₂^bb, A_{p₀}] u⟩| ≤ C_obs2(n) ‖(1 + A) u‖²` on `E_n`. -/
theorem obs2 (hL : 0 < L) (hn : 2 ≤ n) (u : En eta n) :
    ‖⟪u, (Sig2bb sys L n ∘ₗ FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) -
      FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) ∘ₗ Sig2bb sys L n) u⟫_ℂ‖ ≤
      Cobs2 sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 := by
  classical
  rw [comm_Sig2bb_Aproj]
  refine (norm_inner_kop_le' _ u).trans ?_
  have hn1 : 1 ≤ n := by omega
  have hcb := chbT_nonneg (sys := sys) hL
  have hn3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  set N := (125 * (Nat.log 2 n + 2) : ℝ)
  have hN0 : 0 ≤ N := by positivity
  -- the majorant, channel by channel
  have h1 : ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * ‖obsK sys L n p₀ q p‖ ≤
      ∑ j : Ch eta, ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obsMaj sys L n p₀ j q p := by
    calc ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * ‖obsK sys L n p₀ q p‖
        ≤ ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * ∑ j, obsMaj sys L n p₀ j q p :=
          Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left (norm_obsK_le hL hn q p) (by positivity)
      _ = ∑ j : Ch eta, ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obsMaj sys L n p₀ j q p := by
          simp_rw [Finset.mul_sum]
          exact sum3_comm (fun q p j => ‖u.ofLp q‖ * ‖u.ofLp p‖ * obsMaj sys L n p₀ j q p)
  refine h1.trans ?_
  have h2 : ∀ j : Ch eta, ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obsMaj sys L n p₀ j q p ≤
      chbT sys L / (n : ℝ) ^ 3 * N * (3 * kapW sys L ^ 2) *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 := by
    intro j
    have hc : ∀ q p, OnCh j (cidx n q) (cidx n p) →
        1 + piC j (cidx n q) = 1 + piC j (cidx n p) := fun q p h => by rw [piC_onCh h]
    have hpt : ∀ q p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obsMaj sys L n p₀ j q p ≤
        chbT sys L / (n : ℝ) ^ 3 * (if OnCh j (cidx n q) (cidx n p) then
          ‖u.ofLp q‖ * ‖u.ofLp p‖ * (1 + piC j (cidx n p)) else 0) := by
      intro q p
      unfold obsMaj
      split_ifs with h1 h2 h2
      · exact le_of_eq (by ring)
      · exact absurd h1.2 h2
      · rw [mul_zero]
        have := chbT_nonneg (sys := sys) hL
        have := piC_nonneg j (cidx n p)
        positivity
      · rw [mul_zero, mul_zero]
    calc ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obsMaj sys L n p₀ j q p
        ≤ ∑ q, ∑ p, chbT sys L / (n : ℝ) ^ 3 * (if OnCh j (cidx n q) (cidx n p) then
            ‖u.ofLp q‖ * ‖u.ofLp p‖ * (1 + piC j (cidx n p)) else 0) :=
          Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun p _ => hpt q p
      _ = chbT sys L / (n : ℝ) ^ 3 * ∑ q, ∑ p, (if OnCh j (cidx n q) (cidx n p) then
            ‖u.ofLp q‖ * ‖u.ofLp p‖ * (1 + piC j (cidx n p)) else 0) := by
          rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
      _ ≤ chbT sys L / (n : ℝ) ^ 3 * (N * ∑ q, wl j q * (1 + piC j (cidx n q)) * ‖u.ofLp q‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (chan_trace_le hn1 j (fun q => ‖u.ofLp q‖)
            (fun q => 1 + piC j (cidx n q))
            (fun q => by linarith [piC_nonneg j (cidx n q)]) hc) (by positivity)
      _ ≤ chbT sys L / (n : ℝ) ^ 3 * (N * ∑ q, 3 * kapW sys L ^ 2 * (1 + Asym sys L n q) ^ 2 *
            ‖u.ofLp q‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun q _ => ?_) hN0) (by positivity)
          exact mul_le_mul_of_nonneg_right (wl_pi_le (sys := sys) hL j q) (sq_nonneg _)
      _ = chbT sys L / (n : ℝ) ^ 3 * N * (3 * kapW sys L ^ 2) *
            ∑ q, (1 + Asym sys L n q) ^ 2 * ‖u.ofLp q‖ ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => by ring
      _ = _ := by
          congr 1
          rw [norm_sq_wt]
          refine Finset.sum_congr rfl fun q _ => by rw [Real.rpow_one]
  calc ∑ j : Ch eta, ∑ q, ∑ p, ‖u.ofLp q‖ * ‖u.ofLp p‖ * obsMaj sys L n p₀ j q p
      ≤ ∑ _j : Ch eta, chbT sys L / (n : ℝ) ^ 3 * N * (3 * kapW sys L ^ 2) *
          ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 := Finset.sum_le_sum fun j _ => h2 j
    _ = Cobs2 sys L n * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        unfold Cobs2
        ring

/-- **`lem:obs2` on good states**: `|⟨u, [Σ₂^bb, A_{p₀}] u⟩| ≤ C_obs2(n) M²` for `IsGood 1 M u`. -/
theorem obs2_good (hL : 0 < L) (hn : 2 ≤ n) {M : ℝ} {u : En eta n} (hu : IsGood sys L 1 M u) :
    ‖⟪u, (Sig2bb sys L n ∘ₗ FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) -
      FSKernel.dg (fun q => (Aproj sys L p₀ q : ℂ)) ∘ₗ Sig2bb sys L n) u⟫_ℂ‖ ≤
      Cobs2 sys L n * M ^ 2 := by
  refine (obs2 hL hn u).trans ?_
  have hC : 0 ≤ Cobs2 sys L n := by
    unfold Cobs2
    have := chbT_nonneg (sys := sys) hL
    positivity
  have hw : ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 u‖ ≤ M := by
    have := hu.1
    have := norm_nonneg u
    simp only [one_mul] at *
    linarith
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw 2) hC

end Obs2

end FSNormal

namespace FSAsymp

open FSNormal PL

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ}

theorem pl_Cobs2 : PL (fun n => Cobs2 sys L n) (-3) := by
  have hlog : PL (fun n => (Nat.log 2 n : ℝ)) 0 := by
    have h := natlog_of_le (x := fun n => (n : ℝ)) (c := 1) 1 ⟨1, fun n hn => by
      refine ⟨by exact_mod_cast hn, by rw [pow_one, one_mul]⟩⟩
    exact h.congr ⟨0, fun n _ => by simp⟩
  have h := (((pl_inv3 (chbT sys L)).const_mul (Fintype.card (Ch eta) : ℝ)).mul
    ((hlog.add' (const 2)).const_mul 125)).mul_const (3 * kapW sys L ^ 2)
  refine (h.mono (by norm_num)).congr ⟨0, fun n _ => ?_⟩
  unfold Cobs2
  ring

end FSAsymp
