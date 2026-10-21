import PlaneWave.FluxBox.Round3Commutator

/-!
# Flux route, stage 3, part 32: the `C × C` block, middle-split words

In `T = ⟨W u_C, Ỹ u_C⟩` a word `w` with `Φ_w = Σ_f ω_F² (Σ_b |w(f,b)| x_b)² ≲ n⁻⁵ polylog` (`x = 1_C |u|`)
is bounded by the middle split `Σ_f G ω_F H ≤ ‖1_F G‖ Φ_w^{1/2}`, `G(f) = Σ_{j₃} Σ_c |w₃(f,c)| x_c`
(`‖1_F G‖² ≲ n⁻¹ Σ L²`, `sum_far_G_sq_le`). The bounds `Φ_w ≲ n⁻⁵ (weighted L²)`:

* **M1** flat mixed `Ch1` (`Phi_ch1_mixed`): long first hop by transverse Hardy at the points
  (`hop_lineSum_sq_le`, `κ_f = ω_F c₂ c₁/(c_*² n²)`), short first hop by `shape_L2` and transverse
  Hardy with the weight `1 + |ξ₁|²`;
* **M2** flat mixed `Ch2` (`Phi_ch2fl_mixed`);
* **M3** `Ch3` (`Phi_ch3`): the `Y`-hop carries `π₁(b)/n`;
* **M4** `Ch4`, short first hop (`Phi_ch4_short`): `ω_F |y₂| ≤ 8 c_Y (π₂(d)/n)/max(n², |ζ|²)²`;
* **M5** `Ch4` / `Ch2'`, long first hop, `π₂` constant on the `j₁`-lines (`Phi_ch4_long_ns`,
  `Phi_ch2com_ns`): `ω_F² ≤ C n⁻²(n² + π₂²)⁻¹`, conserved-weight Schur, the input `π₂ x`.

The weighted line squares of a good state (`lineSq_good_psi_le`): any weight `ψ` with
`ψ² ≤ C₀ (1 + E)` costs the critical moment (`π_j`, `lineSq_good_pi_le`).
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Weighted line squares of good states -/

section GoodWeights

variable {sys : CoulombSystem eta ν} {L : ℝ} {N : ℕ}

omit [Fintype ν] in
open Classical in
/-- **A weight of degree one in the energy**: if `ψ² ≤ C₀ (1 + E)`, then
`L²_j(ψ |u|) ≤ 125 (log₂ 2N + 2) 2√2 c_X^{3/2} C₀ (1 + η/2)^{1/2} M² (1 + 2η n_d)`. -/
theorem lineSq_good_psi_le (hL : 0 < L) (hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd)
    {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) (j : Ch eta) (ψ : Cfg eta N → ℝ)
    {C₀ : ℝ} (hψ : ∀ p, ψ p ^ 2 ≤ C₀ * (1 + Asym sys L N p)) :
    lineSq j (fun _ => 1) (fun b => ψ b * ‖u.ofLp b‖) ≤
      125 * (Nat.log 2 (2 * N) + 2) * (2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * C₀ *
        ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd))) := by
  have h := lineSq_le j (fun _ => zero_le_one) (fun b => ψ b * ‖u.ofLp b‖)
    (fun p => w32 (regSum {lead j} (cidx N p))) (fun p => w32_pos _)
    (fun q => lineSum_inv_w32_le hN (coord_lead j) q)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hcm := crit_moment_box (sys := sys) hL hnd hu
  have hC0 : 0 ≤ C₀ := by
    have h1 := hψ (Classical.arbitrary _)
    by_contra hneg
    have := Asym_nonneg sys L N (Classical.arbitrary (Cfg eta N))
    have h2 : C₀ * (1 + Asym sys L N (Classical.arbitrary _)) < 0 :=
      mul_neg_of_neg_of_pos (not_le.mp hneg) (by linarith)
    linarith [sq_nonneg (ψ (Classical.arbitrary _))]
  have hW : 0 ≤ 2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * C₀ := by
    have := cXw_ge_one (sys := sys) hL
    positivity
  calc ∑ p, (1 : ℝ) * w32 (regSum {lead j} (cidx N p)) * (ψ p * ‖u.ofLp p‖) ^ 2 ≤
      ∑ p, 2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * C₀ *
        ((1 + Asym sys L N p) ^ 2 * Real.sqrt (1 + Asym sys L N p) * ‖u.ofLp p‖ ^ 2) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have h2 := weight5_le (sys := sys) hL (coord_lead j).card p (sq_nonneg (ψ p)) (hψ p)
        have e : (1 : ℝ) * w32 (regSum {lead j} (cidx N p)) * (ψ p * ‖u.ofLp p‖) ^ 2 =
            ψ p ^ 2 * w32 (regSum {lead j} (cidx N p)) * ‖u.ofLp p‖ ^ 2 := by ring
        rw [e]
        calc ψ p ^ 2 * w32 (regSum {lead j} (cidx N p)) * ‖u.ofLp p‖ ^ 2 ≤
            2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * C₀ *
              ((1 + Asym sys L N p) ^ 2 * Real.sqrt (1 + Asym sys L N p)) * ‖u.ofLp p‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
          _ = _ := by ring
    _ = 2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) * C₀ *
        ∑ p, (1 + Asym sys L N p) ^ 2 * Real.sqrt (1 + Asym sys L N p) * ‖u.ofLp p‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcm hW

omit [Fintype ν] in
/-- `π_j² ≤ (4 m/g²)(1 + E)`. -/
lemma piC_sq_le (hL : 0 < L) (j : Ch eta) (q : Cfg eta N) :
    piC j (cidx N q) ^ 2 ≤ 4 * mmax sys / gF L ^ 2 * (1 + Asym sys L N q) := by
  have h := Asym_ge_piC (sys := sys) hL j q
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hA := Asym_nonneg sys L N q
  have h1 : piC j (cidx N q) ^ 2 ≤ 4 * mmax sys / gF L ^ 2 * Asym sys L N q := by
    have e : piC j (cidx N q) ^ 2 = 4 * mmax sys / gF L ^ 2 *
        (gF L ^ 2 / (4 * mmax sys) * piC j (cidx N q) ^ 2) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have h2 : 0 ≤ 4 * mmax sys / gF L ^ 2 := by positivity
  nlinarith

omit [Fintype ν] in
open Classical in
/-- **The pair-momentum weight**: `L²_j(π_{j'} |u|) ≲ log N · crit`. -/
theorem lineSq_good_pi_le (hL : 0 < L) (hN : 1 ≤ N) {nd : ℕ} (hnd : gF L * (2 * N) ≤ 2 ^ nd)
    {M : ℝ} {u : En eta N} (hu : IsGood sys L 1 M u) (j j' : Ch eta) :
    lineSq j (fun _ => 1) (fun b => piC j' (cidx N b) * ‖u.ofLp b‖) ≤
      125 * (Nat.log 2 (2 * N) + 2) * (2 * Real.sqrt 2 * (cXw sys L * Real.sqrt (cXw sys L)) *
        (4 * mmax sys / gF L ^ 2) * ((1 + (eta : ℝ) / 2) ^ (1 / 2 : ℝ) * M ^ 2 * (1 + 2 * eta * nd))) :=
  lineSq_good_psi_le hL hN hnd hu j _ (fun p => piC_sq_le hL j' p)

end GoodWeights

/-! ## The potential from cold into the far region -/

section GSide

variable {sys : CoulombSystem eta ν} {L : ℝ} {N n : ℕ}

open Classical in
/-- **The far part of a hop from cold**:
`Σ_{f ∉ Q} (Σ_c |w_j(f,c)| x_c)² ≤ (64 c_j)² (277/n) L²_j(x)` for `x` on the cold ball. -/
theorem sum_far_G_sq_le (hL : 0 < L) (hn : 1 ≤ n) (j : Ch eta) (x : Cfg eta N → ℝ)
    (hx : ∀ b, 0 ≤ x b) (hxC : ∀ b, x b ≠ 0 → InC (n : ℝ) (cst sys) (cidx N b)) :
    ∑ f, (if InQ (n : ℝ) (cidx N f) then 0 else ∑ c, ‖wj sys L N j f c‖ * x c) ^ 2 ≤
      (64 * chC sys L j) ^ 2 * (277 / n) * lineSq j (fun _ => 1) x := by
  classical
  have hc := chC_nonneg sys hL j
  set K : Cfg eta N → Cfg eta N → ℝ := fun f c =>
    if ¬ InQ (n : ℝ) (cidx N f) ∧ InC (n : ℝ) (cst sys) (cidx N c) then ‖wj sys L N j f c‖ else 0
    with hK
  have hK0 : ∀ f c, 0 ≤ K f c := fun f c => by
    simp only [hK]; split_ifs
    · exact norm_nonneg _
    · exact le_rfl
  set κ : Cfg eta N → ℝ := kapM n (64 * chC sys L j) {lead j} with hκ
  have hKb : ∀ f c, K f c ≤ if lab N j f = lab N j c then κ f else 0 := by
    intro f c
    simp only [hK]
    split_ifs with h1 h2 h2
    · have hw := norm_wj_le (sys := sys) hL j f c
      rw [if_pos (lab_eq_iff.mp h2)] at hw
      have hSB : SB sys N n c := fun r => (rho_le_of_inC h1.2 r).trans (by
        have := cst_mul_nonneg (sys := sys) (n := n); linarith)
      have hk := kappa_ball hn (coord_lead j) hSB h1.1 (lab_eq_iff.mp h2)
      simp only [hκ, kapM]
      calc ‖wj sys L N j f c‖ ≤ chC sys L j * (1 / FSLattice.lsq (chT N j f c)) := by
            rw [mul_one_div]; exact hw
        _ ≤ chC sys L j * (64 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum {lead j} (cidx N f)))) :=
            mul_le_mul_of_nonneg_left hk hc
        _ = 64 * chC sys L j / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum {lead j} (cidx N f))) := by ring
    · have hw := norm_wj_le (sys := sys) hL j f c
      rw [if_neg (fun h => h2 (lab_eq_iff.mpr h))] at hw
      exact hw
    · exact kapM_nonneg hn (by positivity) _ f
    · exact le_rfl
  have hll := long_line_le j x hx K hK0 κ hKb (sum_kapM_sq_le hn (coord_lead j) (64 * chC sys L j))
  refine le_trans (le_of_eq ?_) hll
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  simp only [hK]
  by_cases hf : InQ (n : ℝ) (cidx N f)
  · rw [if_pos hf]
    symm
    exact Finset.sum_eq_zero fun c _ => by rw [if_neg (fun h => h.1 hf), zero_mul]
  · rw [if_neg hf]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hcC : InC (n : ℝ) (cst sys) (cidx N c)
    · rw [if_pos ⟨hf, hcC⟩]
    · have : x c = 0 := by by_contra h; exact hcC (hxC c h)
      rw [this, mul_zero, mul_zero]

end GSide

/-! ## The middle-split words -/

section Middle

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N n : ℕ}

open Classical in
/-- The long first hop on the lines: `Σ_b W^L(d,b) x_b ≤ κ^L(d) L_{j}(x)(lab d)`. -/
lemma vL_le (hL : 0 < L) (hn : 1 ≤ n) (j : Ch eta) (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b)
    (d : Cfg eta N) :
    ∑ b, WL sys L N n j d b * x b ≤ kappaL sys L N n {lead j} j d * lineSum j x (lab N j d) := by
  unfold lineSum
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_le_sum fun b _ => ?_
  have h := WL_le_kappa (sys := sys) hL hn (coord_lead j) d b
  split_ifs at h ⊢ with h1 h2 h2
  · exact mul_le_mul_of_nonneg_right h (hx b)
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · have : WL sys L N n j d b = 0 := le_antisymm h (WL_nonneg hL j d b)
    rw [this, zero_mul]

lemma kappaL_le_n (hn : 1 ≤ n) (hL : 0 < L) (j : Ch eta) (d : Cfg eta N) :
    kappaL sys L N n {lead j} j d ≤ chC sys L j * (1 / cst sys ^ 2) / (n : ℝ) ^ 2 := by
  unfold kappaL
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc := chC_nonneg sys hL j
  apply div_le_div_of_nonneg_left (by positivity) (by positivity) (le_max_left _ _)

/-- **M1-L1**: the long first hop then a flat hop of another channel, by transverse Hardy:
`Σ_f ω_F² (Σ_d |w₂| Σ_b W^L₁ x)² ≤ (32 m c₂ c₁/(g² c_*²))² 277 H² n⁻⁵ L²_{j₁}(x; 1 + |ξ₂|²)`. -/
theorem Phi_L1_trans {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {j₁ j₂ : Ch eta} {A₂ : Finset (Fin eta)} {ε₂ : ℤ}
    (hA₂ : IsCoord j₂ A₂ ε₂) (hA₂k : ∀ σ, regSum A₂ (tr j₁ σ) = 0)
    (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ d, ‖wj sys L N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ^ 2 ≤
      (32 * mmax sys * chC sys L j₂ * chC sys L j₁ / (gF L ^ 2 * cst sys ^ 2)) ^ 2 * 277 * Hunit ^ 2 /
        (n : ℝ) ^ 5 * lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum A₂ s)) x := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hc₁ := chC_nonneg sys hL j₁
  have hc₂ := chC_nonneg sys hL j₂
  have hcs := cst_pos sys
  set a : ℝ := chC sys L j₂ * (chC sys L j₁ * (1 / cst sys ^ 2) / (n : ℝ) ^ 2) with ha
  have ha0 : 0 ≤ a := by positivity
  set κ : Cfg eta N → ℝ := fun f => farW sys L N n f * a with hκ
  have hpt : ∀ f, farW sys L N n f ^ 2 * (∑ d, ‖wj sys L N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ^ 2 ≤
      κ f ^ 2 * (∑ d, if OnCh j₂ (cidx N f) (cidx N d) then
        lineSum j₁ x (lab N j₁ d) / FSLattice.lsq (chT N j₂ f d) else 0) ^ 2 := by
    intro f
    have h1 : ∑ d, ‖wj sys L N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b ≤
        a * ∑ d, (if OnCh j₂ (cidx N f) (cidx N d) then
          lineSum j₁ x (lab N j₁ d) / FSLattice.lsq (chT N j₂ f d) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun d _ => ?_
      have hv := vL_le (sys := sys) hL hn j₁ x hx d
      have hk := kappaL_le_n (sys := sys) (L := L) (N := N) hn hL j₁ d
      have hw := norm_wj_le (sys := sys) hL j₂ f d
      have hL0 := lineSum_nonneg j₁ hx (lab N j₁ d)
      have hv' : ∑ b, WL sys L N n j₁ d b * x b ≤
          chC sys L j₁ * (1 / cst sys ^ 2) / (n : ℝ) ^ 2 * lineSum j₁ x (lab N j₁ d) :=
        hv.trans (mul_le_mul_of_nonneg_right hk hL0)
      have hv0 : 0 ≤ ∑ b, WL sys L N n j₁ d b * x b :=
        Finset.sum_nonneg fun b _ => mul_nonneg (WL_nonneg hL j₁ d b) (hx b)
      split_ifs at hw ⊢ with hj
      · calc ‖wj sys L N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b ≤
            chC sys L j₂ / FSLattice.lsq (chT N j₂ f d) *
              (chC sys L j₁ * (1 / cst sys ^ 2) / (n : ℝ) ^ 2 * lineSum j₁ x (lab N j₁ d)) :=
              mul_le_mul hw hv' hv0 (div_nonneg hc₂ (FSLattice.lsq_nonneg _))
          _ = a * (lineSum j₁ x (lab N j₁ d) / FSLattice.lsq (chT N j₂ f d)) := by
              simp only [ha]; ring
      · have : ‖wj sys L N j₂ f d‖ = 0 := le_antisymm hw (norm_nonneg _)
        rw [this, zero_mul, mul_zero]
    have h0 : 0 ≤ ∑ d, ‖wj sys L N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b :=
      Finset.sum_nonneg fun d _ => mul_nonneg (norm_nonneg _)
        (Finset.sum_nonneg fun b _ => mul_nonneg (WL_nonneg hL j₁ d b) (hx b))
    have h2 := pow_le_pow_left₀ h0 h1 2
    have hf := sq_nonneg (farW sys L N n f)
    calc farW sys L N n f ^ 2 * (∑ d, ‖wj sys L N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ^ 2 ≤
        farW sys L N n f ^ 2 * (a * ∑ d, (if OnCh j₂ (cidx N f) (cidx N d) then
          lineSum j₁ x (lab N j₁ d) / FSLattice.lsq (chT N j₂ f d) else 0)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 hf
      _ = _ := by simp only [hκ]; ring
  refine (Finset.sum_le_sum fun f _ => hpt f).trans ?_
  set A : ℝ := (32 * mmax sys * chC sys L j₂ * chC sys L j₁ / (gF L ^ 2 * cst sys ^ 2)) ^ 2 * 277 /
    (n : ℝ) ^ 5 with hAdef
  have hA0 : 0 ≤ A := by positivity
  have hA : ∀ q : Cfg eta N, ∑ f ∈ Finset.univ.filter (fun f => lab N j₁ f = lab N j₁ q), κ f ^ 2 ≤ A := by
    intro q
    have hsum := lineSum_inv_max_sq_le (coord_lead j₁) q hn1 0
    simp only [sub_zero] at hsum
    have hpt2 : ∀ f ∈ Finset.univ.filter (fun f => lab N j₁ f = lab N j₁ q),
        κ f ^ 2 ≤ (32 * mmax sys / gF L ^ 2) ^ 2 * a ^ 2 *
          (1 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum {lead j₁} (cidx N f))) ^ 2) := by
      intro f _
      have h1 := farW_le_max (sys := sys) hL hn (coord_lead j₁).card f
      have h0 := farW_nonneg (sys := sys) (L := L) (n := n) f
      have h2 := pow_le_pow_left₀ h0 h1 2
      simp only [hκ]
      have e : (32 * mmax sys / gF L ^ 2 / max ((n : ℝ) ^ 2)
          (FSLattice.lsq (regSum {lead j₁} (cidx N f)))) ^ 2 =
          (32 * mmax sys / gF L ^ 2) ^ 2 *
            (1 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum {lead j₁} (cidx N f))) ^ 2) := by ring
      rw [e] at h2
      calc (farW sys L N n f * a) ^ 2 = farW sys L N n f ^ 2 * a ^ 2 := by ring
        _ ≤ (32 * mmax sys / gF L ^ 2) ^ 2 *
            (1 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum {lead j₁} (cidx N f))) ^ 2) * a ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = _ := by ring
    refine (Finset.sum_le_sum hpt2).trans ?_
    rw [← Finset.mul_sum]
    calc (32 * mmax sys / gF L ^ 2) ^ 2 * a ^ 2 *
          ∑ f ∈ Finset.univ.filter (fun f => lab N j₁ f = lab N j₁ q),
            1 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum {lead j₁} (cidx N f))) ^ 2 ≤
        (32 * mmax sys / gF L ^ 2) ^ 2 * a ^ 2 * (277 / n) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = A := by
          simp only [hAdef, ha]
          field_simp
  have h := hop_lineSum_sq_le hH hA₂ hA₂k x hx κ hA0 hA
  refine h.trans (le_of_eq ?_)
  simp only [hAdef]
  ring

/-- **M1-L2**: the short first hop then a flat hop of another channel:
`Σ_f ω_F² (Σ_d |w₂| Σ_b W^S₁ x)² ≤ (2048 m c₂/g²)² (277/n⁵) c₁² H² L²_{j₂}(x; 1 + |ξ₁|²)`. -/
theorem Phi_L2_cross {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {j₁ j₂ : Ch eta} {A₁ : Finset (Fin eta)} {ε₁ : ℤ}
    (hA₁ : IsCoord j₁ A₁ ε₁) (hA₁k : ∀ σ, regSum A₁ (tr j₂ σ) = 0)
    (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ d, ‖wj sys L N j₂ f d‖ * ∑ b, WS sys L N n j₁ d b * x b) ^ 2 ≤
      (2048 * mmax sys * chC sys L j₂ / gF L ^ 2) ^ 2 * (277 / (n : ℝ) ^ 5) *
        (chC sys L j₁ ^ 2 * (Hunit ^ 2 * lineSq j₂ (fun s => 1 + FSLattice.lsq (regSum A₁ s)) x)) := by
  classical
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hc₂ := chC_nonneg sys hL j₂
  have hvS0 : ∀ d, 0 ≤ ∑ b, WS sys L N n j₁ d b * x b := fun d =>
    Finset.sum_nonneg fun b _ => mul_nonneg (WS_nonneg hL j₁ d b) (hx b)
  have hL2 := shape_L2 (sys := sys) (L := L) (n := n) j₂ (fun f d => ‖wj sys L N j₂ f d‖)
    (fun f d => norm_nonneg _) (fun d => ∑ b, WS sys L N n j₁ d b * x b) hvS0 (SB sys N n)
    (fun d hd => vS_supp hd)
    (kapM2 n (2048 * mmax sys * chC sys L j₂ / gF L ^ 2) {lead j₂})
    (fun f => kapM2_nonneg hn (by positivity) _ f)
    (fun f d hd => farW_wj_ball_le hL hn (coord_lead j₂) hd)
    (sum_kapM2_sq_le hn (coord_lead j₂) _)
  refine hL2.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact lineSq_WS_cross_le hH hL hA₁ hA₁k x hx

/-- **M1** (flat mixed `Ch1`, `j₁ ≠ j₂`): `Φ ≤ 2 (M1-L1) + 2 (M1-L2)`. -/
theorem Phi_ch1_mixed {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {j₁ j₂ : Ch eta} {A₁ A₂ : Finset (Fin eta)} {ε₁ ε₂ : ℤ}
    (hA₁ : IsCoord j₁ A₁ ε₁) (hA₁k : ∀ σ, regSum A₁ (tr j₂ σ) = 0)
    (hA₂ : IsCoord j₂ A₂ ε₂) (hA₂k : ∀ σ, regSum A₂ (tr j₁ σ) = 0)
    (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ b, ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun d => InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b) ^ 2 ≤
      2 * ((32 * mmax sys * chC sys L j₂ * chC sys L j₁ / (gF L ^ 2 * cst sys ^ 2)) ^ 2 * 277 *
        Hunit ^ 2 / (n : ℝ) ^ 5 * lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum A₂ s)) x) +
      2 * ((2048 * mmax sys * chC sys L j₂ / gF L ^ 2) ^ 2 * (277 / (n : ℝ) ^ 5) *
        (chC sys L j₁ ^ 2 * (Hunit ^ 2 * lineSq j₂ (fun s => 1 + FSLattice.lsq (regSum A₁ s)) x))) := by
  classical
  set vL : Cfg eta N → ℝ := fun d => ∑ b, WL sys L N n j₁ d b * x b with hvL
  set vS : Cfg eta N → ℝ := fun d => ∑ b, WS sys L N n j₁ d b * x b with hvS
  have hpt : ∀ f, ∑ b, ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun d => InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b ≤
      ∑ d, ‖wj sys L N j₂ f d‖ * vL d + ∑ d, ‖wj sys L N j₂ f d‖ * vS d := by
    intro f
    have h := chain_sum_le (fun q => ¬ InP (n : ℝ) (cidx N q))
      (fun d => InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
      (wj sys L N j₂) (wj sys L N j₁) x hx
      (fun f d => ‖wj sys L N j₂ f d‖)
      (fun d b => WL sys L N n j₁ d b + WS sys L N n j₁ d b)
      (fun f d => norm_nonneg _) (fun d b => add_nonneg (WL_nonneg hL j₁ d b) (WS_nonneg hL j₁ d b))
      (fun f d _ _ => le_rfl) (fun d b _ hb _ => norm_wj_le_split hL j₁ hb) f
    refine h.trans (le_of_eq ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hvL, hvS, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hΨ0 : ∀ f, 0 ≤ ∑ b, ‖chainK (fun q => ¬ InP (n : ℝ) (cidx N q))
        (fun d => InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b :=
    fun f => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hx b)
  refine (sum_sq_le_add Finset.univ _ _ _ _ hΨ0 hpt).trans ?_
  have h1 := Phi_L1_trans (sys := sys) hH hL hn hA₂ hA₂k x hx
  have h2 := Phi_L2_cross (sys := sys) hH hL hn hA₁ hA₁k x hx
  linarith

/-- **M2** (flat mixed `Ch2`): the first hop is long; `Φ ≤ M1-L1`. -/
theorem Phi_ch2fl_mixed {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {j₁ j₂ : Ch eta} {A₂ : Finset (Fin eta)} {ε₂ : ℤ}
    (hA₂ : IsCoord j₂ A₂ ε₂) (hA₂k : ∀ σ, regSum A₂ (tr j₁ σ) = 0)
    (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b) ^ 2 ≤
      (32 * mmax sys * chC sys L j₂ * chC sys L j₁ / (gF L ^ 2 * cst sys ^ 2)) ^ 2 * 277 * Hunit ^ 2 /
        (n : ℝ) ^ 5 * lineSq j₁ (fun s => 1 + FSLattice.lsq (regSum A₂ s)) x := by
  classical
  have hpt : ∀ f, ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b ≤
      ∑ d, ‖wj sys L N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b :=
    chain_sum_le _ _ _ (wj sys L N j₂) (wj sys L N j₁) x hx
      (fun f d => ‖wj sys L N j₂ f d‖) (WL sys L N n j₁)
      (fun f d => norm_nonneg _) (WL_nonneg hL j₁)
      (fun f d _ _ => le_rfl) (fun d b hd hb _ => norm_wj_notP_le hL j₁ hb hd)
  have hΨ0 : ∀ f, 0 ≤ ∑ b, ‖chainK (fun q => InP (n : ℝ) (cidx N q) ∧ ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (wj sys L N j₁) f b‖ * x b :=
    fun f => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hx b)
  exact (sum_sq_le_of_le Finset.univ _ _ _ hΨ0 hpt).trans (Phi_L1_trans hH hL hn hA₂ hA₂k x hx)

variable (sys L) in
/-- The constant of the well-gapped `Y`-hop without the pair momentum: `32 m c_j/(M̄_j c_*²)`. -/
noncomputable def cY3' (j : Ch eta) : ℝ := 32 * mmax sys * chC sys L j / Mtot sys j / cst sys ^ 2

lemma cY3'_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ cY3' sys L j := by
  unfold cY3'
  have := chC_nonneg sys hL j
  have := one_le_mmax sys
  apply div_nonneg _ (sq_nonneg _)
  exact div_nonneg (by positivity) (Mtot_pos sys j).le

/-- **M3** (`Ch3`): `Φ ≤ KW1(c₂, cY3'₁) n⁻⁵ L²_{j₁}(π₁ x)`. -/
theorem Phi_ch3 {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) (j₂ j₁ : Ch eta) (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ b, ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (yj sys L p₀ N j₁) f b‖ * x b) ^ 2 ≤
      KW1 sys L Hunit (chC sys L j₂) (cY3' sys L j₁) / (n : ℝ) ^ 5 *
        lineSq j₁ (fun _ => 1) (fun b => piC j₁ (cidx N b) * x b) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc₂ := chC_nonneg sys hL j₂
  have hc₁ := chC_nonneg sys hL j₁
  have hm := one_le_mmax sys
  have hM := Mtot_pos sys j₁
  have hcs := cst_pos sys
  set x' : Cfg eta N → ℝ := fun b => piC j₁ (cidx N b) / n * x b with hx'
  have hx'0 : ∀ b, 0 ≤ x' b := fun b => mul_nonneg (div_nonneg (piC_nonneg _ _) hn0.le) (hx b)
  set K₁ : Cfg eta N → Cfg eta N → ℝ := fun d b =>
    if InC (n : ℝ) (cst sys) (cidx N b) ∧ ¬ InP (n : ℝ) (cidx N d) ∧ OnCh j₁ (cidx N d) (cidx N b) then
      32 * mmax sys * chC sys L j₁ / Mtot sys j₁ / FSLattice.lsq (chT N j₁ d b) else 0 with hK₁
  have hK₁0 : ∀ d b, 0 ≤ K₁ d b := fun d b => by
    simp only [hK₁]; split_ifs
    · exact div_nonneg (div_nonneg (by positivity) hM.le) (FSLattice.lsq_nonneg _)
    · exact le_rfl
  have hK₁b : ∀ d b, K₁ d b ≤ if lab N j₁ d = lab N j₁ b then kapM n (cY3' sys L j₁) {lead j₁} d else 0 := by
    intro d b
    simp only [hK₁]
    split_ifs with h1 h2 h2
    · have hl0 := long_of_cold_notP h1.1 h1.2.1 h1.2.2
      have hl : (cst sys * n) ^ 2 ≤ FSLattice.lsq (chT N j₁ d b) := by
        have hcs32 := cst_le32 sys
        have e1 : cst sys * n ≤ (n : ℝ) / 2 := by nlinarith
        have e2 : 0 ≤ cst sys * n := by positivity
        exact (pow_le_pow_left₀ e2 e1 2).trans hl0
      have hk := kappa_long hn (coord_lead j₁) h1.1 h1.2.2 hl
      unfold kapM cY3'
      calc 32 * mmax sys * chC sys L j₁ / Mtot sys j₁ / FSLattice.lsq (chT N j₁ d b) =
          32 * mmax sys * chC sys L j₁ / Mtot sys j₁ * (1 / FSLattice.lsq (chT N j₁ d b)) := by ring
        _ ≤ 32 * mmax sys * chC sys L j₁ / Mtot sys j₁ *
            ((1 / cst sys ^ 2) / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum {lead j₁} (cidx N d)))) :=
            mul_le_mul_of_nonneg_left hk (div_nonneg (by positivity) hM.le)
        _ = _ := by ring
    · exact absurd (lab_eq_iff.mpr h1.2.2) h2
    · exact kapM_nonneg hn (cY3'_nonneg hL j₁) _ d
    · exact le_rfl
  -- the pointwise chain bound, with the pair momentum moved onto the input
  have hpt : ∀ f, ∑ b, ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (yj sys L p₀ N j₁) f b‖ * x b ≤
      ∑ d, ‖wj sys L N j₂ f d‖ * ∑ b, K₁ d b * x' b := by
    intro f
    have h := chain_sum_le (fun q => ¬ InQ (n : ℝ) (cidx N q))
      (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
      (wj sys L N j₂) (yj sys L p₀ N j₁) x hx
      (fun f d => ‖wj sys L N j₂ f d‖) (fun d b => K₁ d b * (piC j₁ (cidx N b) / n))
      (fun f d => norm_nonneg _)
      (fun d b => mul_nonneg (hK₁0 d b) (div_nonneg (piC_nonneg _ _) hn0.le))
      (fun f d _ _ => le_rfl)
      (fun d b hd hb _ => by
        simp only [hK₁]
        by_cases hj : OnCh j₁ (cidx N d) (cidx N b)
        · rw [if_pos ⟨hb, hd, hj⟩]
          have := norm_yj_cold_notP_le (p₀ := p₀) hL hn hb hd hj
          calc ‖yj sys L p₀ N j₁ d b‖ ≤ 32 * mmax sys * chC sys L j₁ / Mtot sys j₁ *
              (piC j₁ (cidx N b) / n) / FSLattice.lsq (chT N j₁ d b) := this
            _ = _ := by ring
        · rw [if_neg (fun h => hj h.2.2), zero_mul]
          have : yj sys L p₀ N j₁ d b = 0 := by unfold yj ycKc; rw [if_neg hj]
          rw [this, norm_zero]) f
    refine h.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hx']
    ring
  have hΨ0 : ∀ f, 0 ≤ ∑ b, ‖chainK (fun q => ¬ InQ (n : ℝ) (cidx N q))
        (fun d => ¬ InP (n : ℝ) (cidx N d)) (fun p => InC (n : ℝ) (cst sys) (cidx N p))
        (wj sys L N j₂) (yj sys L p₀ N j₁) f b‖ * x b :=
    fun f => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (hx b)
  refine (sum_sq_le_of_le Finset.univ _ _ _ hΨ0 hpt).trans ?_
  have hL1 := shape_L1W (sys := sys) hH hL hn (coord_lead j₂) (fun f d => ‖wj sys L N j₂ f d‖)
    K₁ (fun f d => norm_nonneg _) hK₁0 hc₂
    (fun f d => norm_wj_le hL j₂ f d) (kapM n (cY3' sys L j₁) {lead j₁})
    hK₁b (sum_kapM_sq_le hn (coord_lead j₁) _) x' hx'0
  rw [L1W_form hL hn] at hL1
  refine hL1.trans (le_of_eq ?_)
  have e : x' = fun b => (1 / (n : ℝ)) * (piC j₁ (cidx N b) * x b) := by
    funext b; simp only [hx']; ring
  rw [e, lineSq_smul]
  have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
  field_simp

/-- **The com second hop from the short ball, keeping the pair momentum**:
`ω_F(f) |y_j(f,d)| ≤ 8 c_Y (π_j(d)/n)/max(n², |ζ(f)|²)²` for `f ∉ P`, `d` in the short ball. -/
lemma farW_yj_ball_pi (hL : 0 < L) (hn : 1 ≤ n) {j : Ch eta} {A : Finset (Fin eta)} (hA : A.card ≤ 2)
    {f d : Cfg eta N} (hf : ¬ InP (n : ℝ) (cidx N f)) (hd : SB sys N n d)
    (hj : OnCh j (cidx N f) (cidx N d)) :
    farW sys L N n f * ‖yj sys L p₀ N j f d‖ ≤
      8 * cYb sys L j * (piC j (cidx N d) / n) /
        max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hcC := chC_nonneg sys hL j
  have hM := Mtot_pos sys j
  have hfQ : ¬ InQ (n : ℝ) (cidx N f) := fun h => hf (inP_of_inQ' h)
  have hne : f ≠ d := by
    intro h; rw [h] at hf; exact hf (inP_of_SB hd)
  have h1 := norm_yj_le_gap (sys := sys) (p₀ := p₀) hL hj hne
  have hpi0 := piC_nonneg j (cidx N d)
  have hl := long_of_ball hd hfQ hj
  have hρθ : (n : ℝ) / 8 ≤ FSChannel.rho (chT N j f d) := by
    unfold FSChannel.rho; exact Real.le_sqrt_of_sq_le hl
  have hgap := gap_notP_short (sys := sys) hL hf hd
  have hfar := Asym_ge_far (sys := sys) hL hfQ
  have hApos : 0 < Asym sys L N f := lt_of_lt_of_le (by positivity) hfar
  have hd' : Asym sys L N f / 2 ≤ |Asym sys L N f - Asym sys L N d| :=
    hgap.trans (le_abs_self _)
  have hw : farW sys L N n f = 1 / Asym sys L N f := by unfold farW; rw [if_neg hfQ]
  have hy : ‖yj sys L p₀ N j f d‖ ≤
      16 * chC sys L j * gF L ^ 2 / Mtot sys j * (piC j (cidx N d) / n) * (1 / Asym sys L N f) := by
    refine h1.trans ?_
    have h2 : 1 / (FSChannel.rho (chT N j f d) * |Asym sys L N f - Asym sys L N d|) ≤
        1 / ((n : ℝ) / 8 * (Asym sys L N f / 2)) :=
      one_div_le_one_div_of_le (mul_pos (by positivity) (by linarith)) (mul_le_mul hρθ hd'
        (by linarith) (FSChannel.rho_nonneg _))
    calc chC sys L j * gF L ^ 2 * piC j (cidx N d) / Mtot sys j *
          (1 / (FSChannel.rho (chT N j f d) * |Asym sys L N f - Asym sys L N d|)) ≤
        chC sys L j * gF L ^ 2 * piC j (cidx N d) / Mtot sys j *
          (1 / ((n : ℝ) / 8 * (Asym sys L N f / 2))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by field_simp; ring
  have hmax := farW_le_max (sys := sys) hL hn hA f
  rw [hw] at hmax
  have hM0 : 0 < max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f))) :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  rw [hw]
  calc 1 / Asym sys L N f * ‖yj sys L p₀ N j f d‖ ≤
      1 / Asym sys L N f * (16 * chC sys L j * gF L ^ 2 / Mtot sys j * (piC j (cidx N d) / n) *
        (1 / Asym sys L N f)) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
    _ = 16 * chC sys L j * gF L ^ 2 / Mtot sys j * (piC j (cidx N d) / n) * (1 / Asym sys L N f) ^ 2 := by
        ring
    _ ≤ 16 * chC sys L j * gF L ^ 2 / Mtot sys j * (piC j (cidx N d) / n) *
          (32 * mmax sys / gF L ^ 2 / max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum A (cidx N f)))) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmax 2) (by positivity)
    _ = _ := by unfold cYb; field_simp; ring

open Classical in
/-- **M4** (the short first hop then the com hop, general form):
`Σ_f ω_F² (Σ_d 1_{¬P}(f) |y₂| v_S)² ≤ (8 c_Y)² (277/n⁵) L²_{j₂}((π₂/n) v_S)`. -/
theorem Phi_ch4_short_gen (hL : 0 < L) (hn : 1 ≤ n) (j₂ j₁ : Ch eta) (x : Cfg eta N → ℝ)
    (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ d, (if ¬ InP (n : ℝ) (cidx N f) then ‖yj sys L p₀ N j₂ f d‖ else 0) *
        ∑ b, WS sys L N n j₁ d b * x b) ^ 2 ≤
      (8 * cYb sys L j₂) ^ 2 * (277 / (n : ℝ) ^ 5) *
        lineSq j₂ (fun _ => 1) (fun d => piC j₂ (cidx N d) / n * ∑ b, WS sys L N n j₁ d b * x b) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set vS : Cfg eta N → ℝ := fun d => ∑ b, WS sys L N n j₁ d b * x b with hvS
  have hvS0 : ∀ d, 0 ≤ vS d := fun d =>
    Finset.sum_nonneg fun b _ => mul_nonneg (WS_nonneg hL j₁ d b) (hx b)
  set v' : Cfg eta N → ℝ := fun d => piC j₂ (cidx N d) / n * vS d with hv'
  have hv'0 : ∀ d, 0 ≤ v' d := fun d => mul_nonneg (div_nonneg (piC_nonneg _ _) hn0.le) (hvS0 d)
  set κ : Cfg eta N → ℝ := kapM2 n (8 * cYb sys L j₂) {lead j₂} with hκ
  have hκ0 : ∀ f, 0 ≤ κ f := fun f => kapM2_nonneg hn (by have := cYb_nonneg (sys := sys) hL j₂; positivity) _ f
  set K : Cfg eta N → Cfg eta N → ℝ := fun f d => if lab N j₂ f = lab N j₂ d then κ f else 0 with hK
  have hK0 : ∀ f d, 0 ≤ K f d := fun f d => by simp only [hK]; split_ifs; exact hκ0 f; exact le_rfl
  have hpt : ∀ f, farW sys L N n f ^ 2 * (∑ d, (if ¬ InP (n : ℝ) (cidx N f) then
      ‖yj sys L p₀ N j₂ f d‖ else 0) * vS d) ^ 2 ≤ (∑ d, K f d * v' d) ^ 2 := by
    intro f
    have hfw := farW_nonneg (sys := sys) (L := L) (n := n) f
    have e : farW sys L N n f ^ 2 * (∑ d, (if ¬ InP (n : ℝ) (cidx N f) then
        ‖yj sys L p₀ N j₂ f d‖ else 0) * vS d) ^ 2 =
        (∑ d, farW sys L N n f * (if ¬ InP (n : ℝ) (cidx N f) then
          ‖yj sys L p₀ N j₂ f d‖ else 0) * vS d) ^ 2 := by
      rw [← mul_pow, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    rw [e]
    apply pow_le_pow_left₀ (Finset.sum_nonneg fun d _ => mul_nonneg (mul_nonneg hfw
      (by split_ifs <;> simp)) (hvS0 d))
    refine Finset.sum_le_sum fun d _ => ?_
    by_cases hv : vS d = 0
    · rw [hv, mul_zero]; exact mul_nonneg (hK0 f d) (hv'0 d)
    have hd : SB sys N n d := vS_supp hv
    simp only [hK, hv']
    by_cases hfP : InP (n : ℝ) (cidx N f)
    · rw [if_neg (not_not_intro hfP), mul_zero, zero_mul]
      exact mul_nonneg (hK0 f d) (hv'0 d)
    rw [if_pos hfP]
    by_cases hj : OnCh j₂ (cidx N f) (cidx N d)
    · rw [if_pos (lab_eq_iff.mpr hj)]
      have h1 := farW_yj_ball_pi (sys := sys) (p₀ := p₀) hL hn (coord_lead j₂).card hfP hd hj
      calc farW sys L N n f * ‖yj sys L p₀ N j₂ f d‖ * vS d ≤
          8 * cYb sys L j₂ * (piC j₂ (cidx N d) / n) /
            max ((n : ℝ) ^ 2) (FSLattice.lsq (regSum {lead j₂} (cidx N f))) ^ 2 * vS d :=
            mul_le_mul_of_nonneg_right h1 (hvS0 d)
        _ = κ f * (piC j₂ (cidx N d) / n * vS d) := by simp only [hκ, kapM2]; ring
    · have h0 : yj sys L p₀ N j₂ f d = 0 := by unfold yj ycKc; rw [if_neg hj]
      rw [h0, norm_zero, mul_zero, zero_mul]
      exact mul_nonneg (by split_ifs; exact hκ0 f; exact le_rfl) (hv'0 d)
  refine (Finset.sum_le_sum fun f _ => hpt f).trans ?_
  have hll := long_line_le j₂ v' hv'0 K hK0 κ (fun f d => le_rfl)
    (sum_kapM2_sq_le hn (coord_lead j₂) (8 * cYb sys L j₂))
  exact hll

open Classical in
/-- **M4, same channel**: `Φ ≤ (8 c_Y)² 277 (26 c_* c)² n⁻⁵ L²_j(π_j x)`. -/
theorem Phi_ch4_short_same (hL : 0 < L) (hn : 1 ≤ n) (j : Ch eta) (x : Cfg eta N → ℝ)
    (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ d, (if ¬ InP (n : ℝ) (cidx N f) then ‖yj sys L p₀ N j f d‖ else 0) *
        ∑ b, WS sys L N n j d b * x b) ^ 2 ≤
      (8 * cYb sys L j) ^ 2 * 277 * (26 * cst sys * chC sys L j) ^ 2 / (n : ℝ) ^ 5 *
        lineSq j (fun _ => 1) (fun b => piC j (cidx N b) * x b) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  refine (Phi_ch4_short_gen (p₀ := p₀) hL hn j j x hx).trans ?_
  have e : (fun d => piC j (cidx N d) / n * ∑ b, WS sys L N n j d b * x b) =
      fun d => ∑ b, WS sys L N n j d b * (piC j (cidx N b) / n * x b) := by
    funext d
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : WS sys L N n j d b = 0
    · rw [h]; ring
    · have hj := lab_eq_iff.mp (WS_supp h).2
      rw [piC_onCh hj]; ring
  rw [e]
  have hx' : ∀ b, 0 ≤ piC j (cidx N b) / n * x b := fun b =>
    mul_nonneg (div_nonneg (piC_nonneg _ _) hn0.le) (hx b)
  have h1 := lineSq_WS_same_le (sys := sys) (n := n) hL j (fun _ => zero_le_one)
    (fun b => piC j (cidx N b) / n * x b) hx'
  have e2 : lineSq j (fun _ => 1) (fun b => piC j (cidx N b) / n * x b) =
      (1 / (n : ℝ)) ^ 2 * lineSq j (fun _ => 1) (fun b => piC j (cidx N b) * x b) := by
    have : (fun b => piC j (cidx N b) / n * x b) = fun b => (1 / (n : ℝ)) * (piC j (cidx N b) * x b) := by
      funext b; ring
    rw [this, lineSq_smul]
  rw [e2] at h1
  have hY := cYb_nonneg (sys := sys) hL j
  calc (8 * cYb sys L j) ^ 2 * (277 / (n : ℝ) ^ 5) *
        lineSq j (fun _ => 1) (fun d => ∑ b, WS sys L N n j d b * (piC j (cidx N b) / n * x b)) ≤
      (8 * cYb sys L j) ^ 2 * (277 / (n : ℝ) ^ 5) *
        ((26 * (cst sys * n) * chC sys L j) ^ 2 * ((1 / (n : ℝ)) ^ 2 *
          lineSq j (fun _ => 1) (fun b => piC j (cidx N b) * x b))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp

open Classical in
/-- **M4, across**: `Φ ≤ (8 c_Y)² 277 (4 c_*)² c₁² H² n⁻⁵ L²_{j₂}(x; 1 + |ξ₁|²)`. -/
theorem Phi_ch4_short_cross {Hunit : ℝ} (hH : HasFiniteSupportUnitLatticeCoulombHardyBound Hunit)
    (hL : 0 < L) (hn : 1 ≤ n) {j₁ j₂ : Ch eta} {A₁ : Finset (Fin eta)} {ε₁ : ℤ}
    (hA₁ : IsCoord j₁ A₁ ε₁) (hA₁k : ∀ σ, regSum A₁ (tr j₂ σ) = 0)
    (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ d, (if ¬ InP (n : ℝ) (cidx N f) then ‖yj sys L p₀ N j₂ f d‖ else 0) *
        ∑ b, WS sys L N n j₁ d b * x b) ^ 2 ≤
      (8 * cYb sys L j₂) ^ 2 * 277 * (4 * cst sys) ^ 2 / (n : ℝ) ^ 5 *
        (chC sys L j₁ ^ 2 * (Hunit ^ 2 * lineSq j₂ (fun s => 1 + FSLattice.lsq (regSum A₁ s)) x)) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  refine (Phi_ch4_short_gen (p₀ := p₀) hL hn j₂ j₁ x hx).trans ?_
  have hvS0 : ∀ d, 0 ≤ ∑ b, WS sys L N n j₁ d b * x b := fun d =>
    Finset.sum_nonneg fun b _ => mul_nonneg (WS_nonneg hL j₁ d b) (hx b)
  have hle : ∀ d, piC j₂ (cidx N d) / n * ∑ b, WS sys L N n j₁ d b * x b ≤
      4 * cst sys * ∑ b, WS sys L N n j₁ d b * x b := by
    intro d
    by_cases hv : ∑ b, WS sys L N n j₁ d b * x b = 0
    · rw [hv, mul_zero, mul_zero]
    have hd := vS_supp hv
    have hpi : piC j₂ (cidx N d) ≤ 2 * (2 * (cst sys * n)) :=
      piC_le_of_regs j₂ (by have := cst_mul_nonneg (sys := sys) (n := n); positivity) hd
    have : piC j₂ (cidx N d) / n ≤ 4 * cst sys := by
      rw [div_le_iff₀ hn0]; linarith
    exact mul_le_mul_of_nonneg_right this (hvS0 d)
  have h1 := lineSq_mono j₂ (fun _ => zero_le_one)
    (fun d => mul_nonneg (div_nonneg (piC_nonneg _ _) hn0.le) (hvS0 d)) hle
  rw [lineSq_smul] at h1
  have h2 := lineSq_WS_cross_le (sys := sys) (n := n) hH hL hA₁ hA₁k x hx
  have hY := cYb_nonneg (sys := sys) hL j₂
  calc (8 * cYb sys L j₂) ^ 2 * (277 / (n : ℝ) ^ 5) *
        lineSq j₂ (fun _ => 1) (fun d => piC j₂ (cidx N d) / n * ∑ b, WS sys L N n j₁ d b * x b) ≤
      (8 * cYb sys L j₂) ^ 2 * (277 / (n : ℝ) ^ 5) * ((4 * cst sys) ^ 2 *
        (chC sys L j₁ ^ 2 * (Hunit ^ 2 * lineSq j₂ (fun s => 1 + FSLattice.lsq (regSum A₁ s)) x))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
    _ = _ := by field_simp

/-- **The com dressing, far-weighted, keeping the pair momentum**:
`Σ_f ω_F² (Σ_d |y_j| v)² ≤ (2048 m²/g⁴)(C_j Λ_N)² n⁻⁴ Σ_d π_j(d)² v_d²`. -/
theorem sum_farW_yj_sq_pi_le (hL : 0 < L) (hn : 1 ≤ n)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (j : Ch eta) (v : Cfg eta N → ℝ) :
    ∑ f, farW sys L N n f ^ 2 * (∑ d, ‖yj sys L p₀ N j f d‖ * v d) ^ 2 ≤
      2048 * mmax sys ^ 2 / gF L ^ 4 * (CYc sys L j * LamB sys N) ^ 2 / (n : ℝ) ^ 4 *
        ∑ d, piC j (cidx N d) ^ 2 * v d ^ 2 := by
  classical
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set CE := 2048 * mmax sys ^ 2 / gF L ^ 4 with hCE
  have hCE0 : 0 ≤ CE := by positivity
  set D : Cfg eta N → ℝ := fun q => Real.sqrt ((n : ℝ) ^ 2 + piC j (cidx N q) ^ 2) with hD
  have hD0 : ∀ q, 0 < D q := fun q => Real.sqrt_pos.mpr (by
    have := sq_nonneg (piC j (cidx N q)); positivity)
  have hDsq : ∀ q, D q ^ 2 = (n : ℝ) ^ 2 + piC j (cidx N q) ^ 2 := fun q =>
    Real.sq_sqrt (by have := sq_nonneg (piC j (cidx N q)); positivity)
  set v' : Cfg eta N → ℝ := fun d => v d / D d with hv'
  have hpt : ∀ f, farW sys L N n f ^ 2 * (∑ d, ‖yj sys L p₀ N j f d‖ * v d) ^ 2 ≤
      CE / (n : ℝ) ^ 2 * (∑ d, ‖yj sys L p₀ N j f d‖ * v' d) ^ 2 := by
    intro f
    have h1 := farW_sq_le_pi (sys := sys) hL hn j f
    have h2 : ∑ d, ‖yj sys L p₀ N j f d‖ * v d = D f * ∑ d, ‖yj sys L p₀ N j f d‖ * v' d := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases h0 : yj sys L p₀ N j f d = 0
      · rw [h0, norm_zero, zero_mul, zero_mul, mul_zero]
      · have hj : OnCh j (cidx N f) (cidx N d) := by
          by_contra hj; apply h0; unfold yj ycKc; rw [if_neg hj]
        have hDe : D f = D d := by simp only [hD]; rw [piC_onCh hj]
        simp only [hv']
        rw [hDe]
        have := (hD0 d).ne'
        field_simp
    rw [h2, mul_pow, hDsq]
    have h3 := sq_nonneg (∑ d, ‖yj sys L p₀ N j f d‖ * v' d)
    have h4 := sq_nonneg (piC j (cidx N f))
    calc farW sys L N n f ^ 2 * (((n : ℝ) ^ 2 + piC j (cidx N f) ^ 2) *
          (∑ d, ‖yj sys L p₀ N j f d‖ * v' d) ^ 2) ≤
        CE / ((n : ℝ) ^ 2 * ((n : ℝ) ^ 2 + piC j (cidx N f) ^ 2)) *
          (((n : ℝ) ^ 2 + piC j (cidx N f) ^ 2) * (∑ d, ‖yj sys L p₀ N j f d‖ * v' d) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = CE / (n : ℝ) ^ 2 * (∑ d, ‖yj sys L p₀ N j f d‖ * v' d) ^ 2 := by
          have : 0 < (n : ℝ) ^ 2 + piC j (cidx N f) ^ 2 := by positivity
          field_simp
  refine (Finset.sum_le_sum fun f _ => hpt f).trans ?_
  rw [← Finset.mul_sum]
  have hY := sum_sq_yj_le (p₀ := p₀) hL H hKernel j v'
  have hY2 : ∑ d, rY (sys := sys) (L := L) j d ^ 2 * v' d ^ 2 ≤
      (CYc sys L j * LamB sys N) ^ 2 / (n : ℝ) ^ 2 * ∑ d, piC j (cidx N d) ^ 2 * v d ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    unfold rY
    simp only [hv']
    rw [div_pow, hDsq]
    have hpi := sq_nonneg (piC j (cidx N d))
    have hc := sq_nonneg (CYc sys L j * LamB sys N)
    have hvd := sq_nonneg (v d)
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have h8 : v d ^ 2 / ((n : ℝ) ^ 2 + piC j (cidx N d) ^ 2) ≤ v d ^ 2 / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hvd hn2 (by linarith)
    calc (CYc sys L j * LamB sys N * piC j (cidx N d)) ^ 2 *
          (v d ^ 2 / ((n : ℝ) ^ 2 + piC j (cidx N d) ^ 2)) ≤
        (CYc sys L j * LamB sys N * piC j (cidx N d)) ^ 2 * (v d ^ 2 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h8 (sq_nonneg _)
      _ = _ := by ring
  calc CE / (n : ℝ) ^ 2 * ∑ f, (∑ d, ‖yj sys L p₀ N j f d‖ * v' d) ^ 2 ≤
      CE / (n : ℝ) ^ 2 * ((CYc sys L j * LamB sys N) ^ 2 / (n : ℝ) ^ 2 *
        ∑ d, piC j (cidx N d) ^ 2 * v d ^ 2) :=
        mul_le_mul_of_nonneg_left (hY.trans hY2) (by positivity)
    _ = _ := by field_simp

/-- **M5** (the long first hop then the com hop, `π₂` constant on the `j₁`-lines):
`Φ ≤ KY1(j₂, c₁/c_*²) n⁻⁵ L²_{j₁}(π₂ x)`. -/
theorem Phi_y_long_ns (hL : 0 < L) (hn : 1 ≤ n)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (j₂ j₁ : Ch eta) (hπ : ∀ (k : Cf eta) (τ : Lattice3), piC j₂ (k + tr j₁ τ) = piC j₂ k)
    (x : Cfg eta N → ℝ) (hx : ∀ b, 0 ≤ x b) :
    ∑ f, farW sys L N n f ^ 2 * (∑ d, ‖yj sys L p₀ N j₂ f d‖ * ∑ b, WL sys L N n j₁ d b * x b) ^ 2 ≤
      KY1 sys L N j₂ (chC sys L j₁ * (1 / cst sys ^ 2)) / (n : ℝ) ^ 5 *
        lineSq j₁ (fun _ => 1) (fun b => piC j₂ (cidx N b) * x b) := by
  classical
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := gF_pos hL
  have hm := one_le_mmax sys
  refine (sum_farW_yj_sq_pi_le (p₀ := p₀) hL hn H hKernel j₂ _).trans ?_
  have e : ∀ d, piC j₂ (cidx N d) ^ 2 * (∑ b, WL sys L N n j₁ d b * x b) ^ 2 =
      (∑ b, WL sys L N n j₁ d b * (piC j₂ (cidx N b) * x b)) ^ 2 := by
    intro d
    rw [← mul_pow, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : WL sys L N n j₁ d b = 0
    · rw [h]; ring
    · have hj : OnCh j₁ (cidx N d) (cidx N b) := by
        by_contra hj; apply h; unfold WL; rw [if_neg (fun h' => hj h'.1)]
      have e1 : cidx N d = cidx N b + tr j₁ (cidx N d (lead j₁) - cidx N b (lead j₁)) := hj
      rw [e1, hπ]; ring
  simp only [e]
  have hx' : ∀ b, 0 ≤ piC j₂ (cidx N b) * x b := fun b => mul_nonneg (piC_nonneg _ _) (hx b)
  have hll := long_line_le j₁ (fun b => piC j₂ (cidx N b) * x b) hx' (WL sys L N n j₁)
    (WL_nonneg hL j₁) (kappaL sys L N n {lead j₁} j₁)
    (WL_le_kappa hL hn (coord_lead j₁)) (sum_kappaL_sq_le hn (coord_lead j₁))
  have hY := CYc_nonneg (sys := sys) hL j₂
  have hΛ := LamB_nonneg (sys := sys) N
  calc 2048 * mmax sys ^ 2 / gF L ^ 4 * (CYc sys L j₂ * LamB sys N) ^ 2 / (n : ℝ) ^ 4 *
        ∑ d, (∑ b, WL sys L N n j₁ d b * (piC j₂ (cidx N b) * x b)) ^ 2 ≤
      2048 * mmax sys ^ 2 / gF L ^ 4 * (CYc sys L j₂ * LamB sys N) ^ 2 / (n : ℝ) ^ 4 *
        ((chC sys L j₁ * (1 / cst sys ^ 2)) ^ 2 * (277 / n) *
          lineSq j₁ (fun _ => 1) (fun b => piC j₂ (cidx N b) * x b)) :=
        mul_le_mul_of_nonneg_left hll (by positivity)
    _ = _ := by unfold KY1; field_simp

end Middle

end FSFlux
