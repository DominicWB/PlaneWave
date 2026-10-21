import PlaneWave.KineticCompletion.CompletionClauses

/-!
# Auxiliary claims, part 1: the remaining clauses of `lem:dressed-tails`

`lem:bulk-weighted` at `j = 2`, and the clauses of `lem:dressed-tails` beyond `PlaneWave.Source.DressedState`:

* `col_sig_weighted2_le`: `Σ_q (1+2E(q))² |σ(q,p)|² ≤ M₂ ∝ n⁻¹` for `p ∈ Q`;
* **`form2_sig_Q_state_le`** (eq:bulk-weighted-state, `j = 2`):
  `Σ_q (1+2E(q))² |(Σ_b 1_Q u)(q)|² ≤ #Ch² M₂ Z_{2s} Σ_{p∈Q} (1+|p|²)^{2s} |u_p|²`, i.e.
  `‖E S u‖ ≤ C K^{-1/2} ‖E^s u‖`, and `form2_sig_Q_le` (`‖E S‖ ≤ C K`);
* `fgood_T`: `‖T (1 - P) w‖ ≤ η M K^{-1/2}` for a good `w`;
* **`dressed_kin_tail`**: for the dressed state `w = e^{Σ_G} w₀`,
  `‖T (w - P w)‖ ≤ τ + a₂ M + c₂ (a₀ M + A_σ ρ)`;
* **`dressed_half_tail`** (the interpolation): `Σ_q (1 + E(q)) |(S v)(q)|² ≤ ‖S v‖ (‖S v‖ + ‖T v‖)`;
* **`dressed_r_support`**: `r = P (e^{Σ_b} - 1) x` vanishes off `Q`;
* **`dressed_energy_bounds`** (`lem:dressed-tails` along the trajectory): with `ψ̃_R = S (w - P w)`,
  `‖ψ̃_R‖ + ‖T (w - P w)‖ ≤ (ρ̃ + e_T) Ξ` (so `‖ℰ ψ̃_R‖ ≤ (ρ̃ + e_T) Ξ`),
  `Σ_q (1 + E(q)) |ψ̃_R(q)|² ≤ ρ̃ (ρ̃ + e_T) Ξ²`, `supp r ⊂ Q` and `Θ(r) ≤ (1 + A_max) δ_a Ξ`,
  where the dressed state has an `H²` representative `w`;
* **`FSAsymp.dressed_tails_logfree`**: the orders, with no logarithm (the class `PW`):
  `ρ̃ = O(K^{-5/2})`, `ω̃ = O(K^{-3/2})`, `ρ̃ + e_T = O(K^{-1/2})`, `ρ̃ (ρ̃ + e_T) = O(K⁻³)`,
  `δ_a = O(K^{-7/2})`, `(1 + A_max) δ_a = O(K^{-3/2})`, and the goodness budget of `ψ̃_P` is
  `O(1)`; `FSAsymp.pl_eT`, `pl_half_tail` and `pl_theta_r` are the same orders up to logarithms
  (the class `PL`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics NormedSpace FluxSourceTest FSGalerkin

namespace FSNormal

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The doubly weighted columns of `σ` -/

/-- The doubly weighted column constant `M₂ = #Ch · cSig2 · c₁² · 416/(3n)` (`∝ n⁻¹`). -/
noncomputable def M2 (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Fintype.card (Ch eta) * cSig2 sys L * c1E eta L ^ 2 * (416 / (3 * n))

/-- The form constant `a₂ = (#Ch² M₂ Z₂)^{1/2} c_E` of `‖E Σ_b Q x‖ ≤ a₂ (‖x‖ + ‖T x‖)`
(`∝ n^{-1/2}`). -/
noncomputable def a2c (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (Ch eta) ^ 2 * M2 sys L n * 53) * cE sys L

/-- The operator constant `c₂ = (#Ch² M₂ (2⌈n/4⌉+1)³)^{1/2}` of `‖E Σ_b Q‖ ≤ c₂` (`∝ n`). -/
noncomputable def c2op (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (Ch eta) ^ 2 * M2 sys L n * (2 * ⌈(n : ℝ) / 4⌉₊ + 1 : ℝ) ^ 3)

omit [Fintype ν] in
lemma nsq_sq_mul_tailFn_sq_le {R : ℝ} (hR : 0 < R) (x : L3) :
    nsq x ^ 2 * tailFn R x ^ 2 ≤ tailFn R x := by
  unfold tailFn
  split_ifs with h
  · have hx : 0 < nsq x := lt_trans (by positivity) h
    apply le_of_eq
    rw [show ((nsq x)⁻¹ ^ 2) ^ 2 = (nsq x)⁻¹ ^ 2 * (nsq x)⁻¹ ^ 2 by ring, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hx.ne', one_pow, one_mul]
  · simp

section Main

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)

lemma M2_nonneg : 0 ≤ M2 sys L n := by
  unfold M2; have := cSig2_nonneg sys (L := L); positivity

lemma a2c_nonneg : 0 ≤ a2c sys L n := by
  unfold a2c; have := one_le_cE sys (L := L); positivity

lemma c2op_nonneg : 0 ≤ c2op sys L n := Real.sqrt_nonneg _

include hL hn in
/-- `Σ_q (1 + 2E(q))² |σ(q, p)|² ≤ M₂` (`∝ n⁻¹`) for `p ∈ Q`. -/
theorem col_sig_weighted2_le {p : Cf eta} (hp : InQ (n : ℝ) p) :
    (Summable fun q => (1 + 2 * Ek sys L q) ^ 2 * ‖sigK sys L n q p‖ ^ 2) ∧
      ∑' q, (1 + 2 * Ek sys L q) ^ 2 * ‖sigK sys L n q p‖ ^ 2 ≤ M2 sys L n := by
  classical
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hR : (0 : ℝ) < 3 * n / 4 := by positivity
  set R := (3 * n / 4 : ℝ)
  have hw0 : ∀ q, 0 ≤ 1 + 2 * Ek sys L q := fun q => by
    linarith [one_le_one_add_two_Ek sys L q]
  have hmaj : ∀ j, (Summable fun q => (1 + 2 * Ek sys L q) ^ 2 * sigMaj sys L n j q p ^ 2) ∧
      ∑' q, (1 + 2 * Ek sys L q) ^ 2 * sigMaj sys L n j q p ^ 2 ≤
        (chC sys L j / cgap sys (gF L)) ^ 2 * (c1E eta L ^ 2 * (416 / (3 * n))) := by
    intro j
    have e : (fun q => (1 + 2 * Ek sys L q) ^ 2 * sigMaj sys L n j q p ^ 2) = fun q =>
        if OnCh j q p then (chC sys L j / cgap sys (gF L)) ^ 2 *
          ((1 + 2 * Ek sys L q) ^ 2 * tailFn R (q (lead j) - p (lead j)) ^ 2) else 0 := by
      funext q; unfold sigMaj; split_ifs <;> ring
    have hb : ∀ x, (chC sys L j / cgap sys (gF L)) ^ 2 *
        ((1 + 2 * Ek sys L (p + tr j x)) ^ 2 * tailFn R x ^ 2) ≤
        (chC sys L j / cgap sys (gF L)) ^ 2 * (c1E eta L ^ 2 * tailFn R x) := by
      intro x
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      by_cases hx : R ^ 2 < nsq x
      · have h1 := weight_tr_le sys (L := L) hp j hx
        have h1' : (1 + 2 * Ek sys L (p + tr j x)) ^ 2 ≤ (c1E eta L * nsq x) ^ 2 :=
          pow_le_pow_left₀ (hw0 _) h1 2
        have h2 := nsq_sq_mul_tailFn_sq_le hR x
        calc (1 + 2 * Ek sys L (p + tr j x)) ^ 2 * tailFn R x ^ 2
            ≤ (c1E eta L * nsq x) ^ 2 * tailFn R x ^ 2 :=
              mul_le_mul_of_nonneg_right h1' (sq_nonneg _)
          _ = c1E eta L ^ 2 * (nsq x ^ 2 * tailFn R x ^ 2) := by ring
          _ ≤ c1E eta L ^ 2 * tailFn R x := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      · have : tailFn R x = 0 := by unfold tailFn; rw [if_neg hx]
        rw [this]; simp
    have hs0 : Summable fun x => (chC sys L j / cgap sys (gF L)) ^ 2 *
        (c1E eta L ^ 2 * tailFn R x) :=
      ((tail_bound hn).1.mul_left _).mul_left _
    have hs : Summable fun x => (chC sys L j / cgap sys (gF L)) ^ 2 *
        ((1 + 2 * Ek sys L (p + tr j x)) ^ 2 * tailFn R x ^ 2) :=
      hs0.of_nonneg_of_le (fun x => mul_nonneg (sq_nonneg _)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))) hb
    refine ⟨?_, ?_⟩
    · rw [e, summable_col_iff]; simpa only [lead_add_tr] using hs
    · rw [e, tsum_col]
      simp only [lead_add_tr]
      calc ∑' x, (chC sys L j / cgap sys (gF L)) ^ 2 *
            ((1 + 2 * Ek sys L (p + tr j x)) ^ 2 * tailFn R x ^ 2)
          ≤ ∑' x, (chC sys L j / cgap sys (gF L)) ^ 2 * (c1E eta L ^ 2 * tailFn R x) :=
            hs.tsum_le_tsum hb hs0
        _ = (chC sys L j / cgap sys (gF L)) ^ 2 * (c1E eta L ^ 2 * ∑' x, tailFn R x) := by
            rw [tsum_mul_left, tsum_mul_left]
        _ ≤ _ := by
            gcongr
            exact (tail_bound hn).2
  have hs : Summable fun q => (Fintype.card (Ch eta) : ℝ) *
      ∑ j : Ch eta, (1 + 2 * Ek sys L q) ^ 2 * sigMaj sys L n j q p ^ 2 :=
    (summable_sum fun j _ => (hmaj j).1).mul_left _
  have hle : ∀ q, (1 + 2 * Ek sys L q) ^ 2 * ‖sigK sys L n q p‖ ^ 2 ≤
      (Fintype.card (Ch eta) : ℝ) *
        ∑ j : Ch eta, (1 + 2 * Ek sys L q) ^ 2 * sigMaj sys L n j q p ^ 2 := by
    intro q
    calc (1 + 2 * Ek sys L q) ^ 2 * ‖sigK sys L n q p‖ ^ 2 ≤ (1 + 2 * Ek sys L q) ^ 2 *
          (Fintype.card (Ch eta) * ∑ j : Ch eta, sigMaj sys L n j q p ^ 2) :=
          mul_le_mul_of_nonneg_left (sq_norm_sigK_le sys hL hn0 q p) (sq_nonneg _)
      _ = _ := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨hs.of_nonneg_of_le (fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hle, ?_⟩
  calc ∑' q, (1 + 2 * Ek sys L q) ^ 2 * ‖sigK sys L n q p‖ ^ 2 ≤ ∑' q,
        (Fintype.card (Ch eta) : ℝ) *
          ∑ j : Ch eta, (1 + 2 * Ek sys L q) ^ 2 * sigMaj sys L n j q p ^ 2 :=
        (hs.of_nonneg_of_le (fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hle).tsum_le_tsum
          hle hs
    _ = Fintype.card (Ch eta) * ∑ j : Ch eta,
          ∑' q, (1 + 2 * Ek sys L q) ^ 2 * sigMaj sys L n j q p ^ 2 := by
        rw [tsum_mul_left, Summable.tsum_finsetSum fun j _ => (hmaj j).1]
    _ ≤ Fintype.card (Ch eta) * ∑ j : Ch eta,
          (chC sys L j / cgap sys (gF L)) ^ 2 * (c1E eta L ^ 2 * (416 / (3 * n))) := by
        gcongr with j
        exact (hmaj j).2
    _ = M2 sys L n := by
        unfold M2 cSig2
        rw [← Finset.sum_mul]; ring

open Classical in
include hL in
/-- **eq:bulk-weighted-state, `j = 2`**: the output weight `(1 + 2E)²` with `M₂ ∝ n⁻¹`
(`‖E S u‖ ≤ C K^{-1/2} ‖E^s u‖`). -/
theorem form2_sig_Q_state_le {s : ℝ} (hs : 3 / 4 < s) (u : L2 eta) :
    (Summable fun q => (1 + 2 * Ek sys L q) ^ 2 *
        ‖Sig sys L n hL hn (lpTruncate (Qs eta n) u) q‖ ^ 2) ∧
      ∑' q, (1 + 2 * Ek sys L q) ^ 2 * ‖Sig sys L n hL hn (lpTruncate (Qs eta n) u) q‖ ^ 2 ≤
        Fintype.card (Ch eta) ^ 2 * M2 sys L n * (1 + 26 * (1 + 1 / (2 * (2 * s) - 3))) *
          ∑ p ∈ Qs eta n, Ws s p * ‖u p‖ ^ 2 :=
  gram_sig_Q sys hL hn (fun q => sq_nonneg (1 + 2 * Ek sys L q))
    (fun _ hp => (col_sig_weighted2_le sys hL hn (mem_Qs.mp hp)).1)
    (fun _ hp => (col_sig_weighted2_le sys hL hn (mem_Qs.mp hp)).2)
    (Ws s) (Ws_pos s) (fun j p _ => fibre_weight_le n j p hs) u

open Classical in
include hL in
/-- **`‖E Σ_b Q‖ ≤ c₂`** (`c₂ ∝ n`): `Σ_q (1+2E(q))² |(Σ_b 1_Q x)(q)|² ≤ c₂² ‖x‖²`. -/
theorem form2_sig_Q_le (x : L2 eta) :
    (Summable fun q => (1 + 2 * Ek sys L q) ^ 2 *
        ‖Sig sys L n hL hn (lpTruncate (Qs eta n) x) q‖ ^ 2) ∧
      ∑' q, (1 + 2 * Ek sys L q) ^ 2 * ‖Sig sys L n hL hn (lpTruncate (Qs eta n) x) q‖ ^ 2 ≤
        Fintype.card (Ch eta) ^ 2 * M2 sys L n * (2 * ⌈(n : ℝ) / 4⌉₊ + 1 : ℝ) ^ 3 * ‖x‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := gram_sig_Q sys hL hn (fun q => sq_nonneg (1 + 2 * Ek sys L q))
    (fun p hp => (col_sig_weighted2_le sys hL hn (mem_Qs.mp hp)).1)
    (fun p hp => (col_sig_weighted2_le sys hL hn (mem_Qs.mp hp)).2)
    (fun _ => 1) (fun _ => one_pos)
    (fun j p _ => by
      simp only [inv_one, Finset.sum_const, nsmul_eq_mul, mul_one]
      exact card_fibre_le n j p) x
  refine ⟨h1, h2.trans ?_⟩
  simp only [one_mul]
  have hM := M2_nonneg sys (L := L) (n := n)
  exact mul_le_mul_of_nonneg_left (sum_Qs_sq_le n x) (by positivity)

open Classical in
include hL in
/-- `Σ (1 + 2E)² |Σ_b Q x|² ≤ (a₂ (‖x‖ + ‖T x‖))²` (eq:bulk-weighted-state, `j = 2`, `s = 1`). -/
theorem form2_sigQ_le (w : MolecularFourierH2 eta) :
    (Summable fun q => (1 + 2 * Ek sys L q) ^ 2 *
        ‖Sig sys L n hL hn (lpTruncate (Qs eta n) (Sm eta L w)) q‖ ^ 2) ∧
    ∑' q, (1 + 2 * Ek sys L q) ^ 2 *
        ‖Sig sys L n hL hn (lpTruncate (Qs eta n) (Sm eta L w)) q‖ ^ 2 ≤
      (a2c sys L n * (‖Sm eta L w‖ + ‖coulombFourierKineticH2 sys (gF L) w‖)) ^ 2 := by
  obtain ⟨h1, h⟩ := form2_sig_Q_state_le sys hL hn (s := 1) (by norm_num) (Sm eta L w)
  have hW := sum_Ws_one_le sys hL (n := n) w
  have hc : (1 + 26 * (1 + 1 / (2 * (2 * (1 : ℝ)) - 3))) = 53 := by norm_num
  rw [hc] at h
  have hM2 := M2_nonneg sys (L := L) (n := n)
  refine ⟨h1, ?_⟩
  unfold a2c
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  calc _ ≤ Fintype.card (Ch eta) ^ 2 * M2 sys L n * 53 *
        ∑ p ∈ Qs eta n, Ws 1 p * ‖Sm eta L w p‖ ^ 2 := h
    _ ≤ Fintype.card (Ch eta) ^ 2 * M2 sys L n * 53 *
        (cE sys L ^ 2 * (‖Sm eta L w‖ + ‖coulombFourierKineticH2 sys (gF L) w‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ = _ := by ring

/-! ## The kinetic operator in coordinates -/

omit [Fintype ν] in
lemma kin_apply_eq (v : MolecularFourierH2 eta) (p : Cf eta) :
    coulombFourierKineticH2 sys (gF L) v p = ((Ek sys L p : ℝ) : ℂ) * Sm eta L v p := by
  simp only [coulombFourierKineticH2_apply, Sm, molecularH2StateMap_apply]
  rw [Ek, E_eq_kineticSymbol]

omit [Fintype ν] in
lemma add_kin_apply (v : MolecularFourierH2 eta) (q : Cf eta) :
    (Sm eta L v + coulombFourierKineticH2 sys (gF L) v) q =
      ((1 + Ek sys L q : ℝ) : ℂ) * Sm eta L v q := by
  rw [lp.coeFn_add, Pi.add_apply, kin_apply_eq]
  push_cast; ring

include hL in
/-- `‖T Σ_D y‖² ≤ Σ_q (1 + 2E(q))² |(Σ_b y)(q)|²` (`S Σ_D = Σ_b`). -/
lemma norm_kin_SigD_sq_le (y : L2 eta)
    (hs : Summable fun q => (1 + 2 * Ek sys L q) ^ 2 * ‖Sig sys L n hL hn y q‖ ^ 2) :
    ‖coulombFourierKineticH2 sys (gF L) (SigD sys L n hL (by omega) y)‖ ^ 2 ≤
      ∑' q, (1 + 2 * Ek sys L q) ^ 2 * ‖Sig sys L n hL hn y q‖ ^ 2 := by
  have e : ∀ q, ‖coulombFourierKineticH2 sys (gF L) (SigD sys L n hL (by omega) y) q‖ ^ 2 =
      Ek sys L q ^ 2 * ‖Sig sys L n hL hn y q‖ ^ 2 := by
    intro q
    rw [kin_apply_eq, stateMap_SigD hL hn, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs]
  have hpt : ∀ q, Ek sys L q ^ 2 * ‖Sig sys L n hL hn y q‖ ^ 2 ≤
      (1 + 2 * Ek sys L q) ^ 2 * ‖Sig sys L n hL hn y q‖ ^ 2 := by
    intro q
    have h1 := one_le_one_add_two_Ek sys L q
    have h0 : 0 ≤ Ek sys L q := by linarith
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (by linarith) 2) (sq_nonneg _)
  rw [← tsum_sq_coord (coulombFourierKineticH2 sys (gF L) (SigD sys L n hL (by omega) y)),
    tsum_congr e]
  exact ((summable_sq_coord _).congr e).tsum_le_tsum hpt hs

omit [Fintype ν] in
/-- **The interpolation** `‖ℰ^{1/2} S v‖² ≤ ‖S v‖ ‖ℰ S v‖`:
`Σ_q (1 + E(q)) |(S v)(q)|² ≤ ‖S v‖ (‖S v‖ + ‖T v‖)`. -/
theorem dressed_half_tail (v : MolecularFourierH2 eta) :
    (Summable fun q => (1 + Ek sys L q) * ‖Sm eta L v q‖ ^ 2) ∧
      ∑' q, (1 + Ek sys L q) * ‖Sm eta L v q‖ ^ 2 ≤
        ‖Sm eta L v‖ * (‖Sm eta L v‖ + ‖coulombFourierKineticH2 sys (gF L) v‖) := by
  have hs := summable_norm_mul_of_sq (summable_sq_coord (Sm eta L v))
    (summable_sq_coord (Sm eta L v + coulombFourierKineticH2 sys (gF L) v))
  have hle := tsum_norm_mul_le (Sm eta L v) (Sm eta L v + coulombFourierKineticH2 sys (gF L) v)
  have e : ∀ q, ‖Sm eta L v q‖ * ‖(Sm eta L v + coulombFourierKineticH2 sys (gF L) v) q‖ =
      (1 + Ek sys L q) * ‖Sm eta L v q‖ ^ 2 := by
    intro q
    have hE : 0 ≤ 1 + Ek sys L q := by linarith [one_le_one_add_two_Ek sys L q]
    rw [add_kin_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
    ring
  refine ⟨hs.congr e, ?_⟩
  rw [← tsum_congr e]
  exact hle.trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))

/-! ## The dressed exterior energy -/

open Classical in
/-- **`lem:dressed-tails`, the energy tail**: for `S w₀ = x` with `‖R x‖ ≤ ρ`, `‖T (w₀ - P w₀)‖ ≤ τ`
and `‖x‖ + ‖T w₀‖ ≤ M`, the dressed state `w = e^{Σ_G} w₀` has
`‖T (w - P w)‖ ≤ τ + a₂ M + c₂ (a₀ M + A_σ ρ)`. -/
theorem dressed_kin_tail (w₀ : MolecularFourierH2 eta) {ρ τ M : ℝ}
    (hR : ‖Sm eta L w₀ - molecularH2Truncate n (Sm eta L w₀)‖ ≤ ρ)
    (hT : ‖coulombFourierKineticH2 sys (gF L) (w₀ - molecularH2Truncate n w₀)‖ ≤ τ)
    (hM : ‖Sm eta L w₀‖ + ‖coulombFourierKineticH2 sys (gF L) w₀‖ ≤ M) :
    ‖coulombFourierKineticH2 sys (gF L)
        (exp (SigG sys hL hn) w₀ - molecularH2Truncate n (exp (SigG sys hL hn) w₀))‖ ≤
      τ + a2c sys L n * M + c2op sys L n * (a0c sys L n * M + Asig sys L n * ρ) := by
  have hskew := (Sig_skew_unitary (sys := sys) hL hn).1
  have hA := norm_Sig_le (sys := sys) hL hn
  have hA0 := Asig_nonneg (sys := sys) (n := n) hL
  have ha0 := a0c_nonneg sys (L := L) (n := n)
  have ha2 := a2c_nonneg sys (L := L) (n := n)
  have hM2 := M2_nonneg sys (L := L) (n := n)
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  have hQ : ‖Sig sys L n hL hn (lpTruncate (Qs eta n) (Sm eta L w₀))‖ ≤ a0c sys L n * M :=
    (norm_sigQ_le sys hL hn w₀).trans (mul_le_mul_of_nonneg_left hM ha0)
  have hSx : ‖Sig sys L n hL hn (Sm eta L w₀)‖ ≤ a0c sys L n * M + Asig sys L n * ρ := by
    rw [sig_split sys hL hn (Sm eta L w₀)]
    refine (norm_add_le _ _).trans (add_le_add hQ ?_)
    exact ((Sig sys L n hL hn).le_opNorm _).trans (mul_le_mul hA hR (norm_nonneg _) hA0)
  have hJ : ‖FSConj.Jx (Sig sys L n hL hn) (Sm eta L w₀)‖ ≤
      a0c sys L n * M + Asig sys L n * ρ :=
    (FSConj.norm_Jx_apply_le hskew _).trans hSx
  rw [dressed_lift sys hL hn w₀, map_add, map_add]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hT ?_)) ?_)
  · -- `‖T Σ_D Q x‖ ≤ a₂ M`
    obtain ⟨hs, hb⟩ := form2_sigQ_le sys hL hn w₀
    have h := (norm_kin_SigD_sq_le sys hL hn _ hs).trans hb
    have h2 : ‖coulombFourierKineticH2 sys (gF L)
        (SigD sys L n hL (by omega) (lpTruncate (Qs eta n) (Sm eta L w₀)))‖ ^ 2 ≤
        (a2c sys L n * M) ^ 2 :=
      h.trans (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hM ha2) 2)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  · -- `‖T Σ_D Q J x‖ ≤ c₂ ‖J x‖`
    obtain ⟨hs, hb⟩ := form2_sig_Q_le sys hL hn (FSConj.Jx (Sig sys L n hL hn) (Sm eta L w₀))
    have h := (norm_kin_SigD_sq_le sys hL hn _ hs).trans hb
    have h2 : ‖coulombFourierKineticH2 sys (gF L) (SigD sys L n hL (by omega)
        (lpTruncate (Qs eta n) (FSConj.Jx (Sig sys L n hL hn) (Sm eta L w₀))))‖ ^ 2 ≤
        (c2op sys L n * (a0c sys L n * M + Asig sys L n * ρ)) ^ 2 := by
      refine h.trans ?_
      unfold c2op
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hJ 2) (by positivity)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (c2op_nonneg sys) (le_trans (norm_nonneg _) hJ)) two_ne_zero).mp h2

open Classical in
/-- `(Σ_b R z)(q) = 0` off `Q`: the cube part of `Σ_b` of an exterior vector lies in `Q`. -/
lemma sig_R_apply_eq_zero (z : L2 eta) {q : Cf eta} (hq : ¬ InQ (n : ℝ) q) :
    Sig sys L n hL hn (z - molecularH2Truncate n z) q = 0 := by
  rw [Sig_apply]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  rw [sub_truncate_apply]
  unfold sigK
  split_ifs with hc hp
  · rw [mul_zero]
  · rcases hc with ⟨hq', -⟩ | ⟨-, hp'⟩
    · exact absurd hq' hq
    · exact absurd (hp'.inP (Nat.cast_nonneg n)) hp
  · rw [zero_mul]
  · rw [zero_mul]

open Classical in
/-- **`supp r ⊂ Q`** (`lem:dressed-tails`): `r = P e^{Σ_b} x - P x` vanishes off `Q`. -/
theorem dressed_r_support (x : L2 eta) (q : Cf eta) (hq : q ∉ Qs eta n) :
    (molecularH2Truncate n (exp (Sig sys L n hL hn) x) - molecularH2Truncate n x) q = 0 := by
  rw [dressed_interior sys hL hn x]
  have hq' : ¬ InQ (n : ℝ) q := fun h => hq (mem_Qs.mpr h)
  have h1 := sig_R_apply_eq_zero sys hL hn x hq'
  have h2 := sig_R_apply_eq_zero sys hL hn (FSConj.Jx (Sig sys L n hL hn) x) hq'
  simp only [lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply, h1, h2]
  ring

end Main

section Tail

variable {sys : CoulombSystem eta ν} {L : ℝ}

omit [Fintype ν] in
/-- `‖T (1 - P) w‖ ≤ η M K^{-1/2}` for a good `w` and `K = g n ≥ 1`. -/
lemma fgood_T {M : ℝ} {w : MolecularFourierH2 eta} (h : FGood sys L M w) (hL : 0 < L) {n : ℕ}
    (hK : 1 ≤ gF L * n) :
    ‖coulombFourierKineticH2 sys (gF L) (w - molecularH2Truncate n w)‖ ≤
      eta * M * (gF L * n) ^ (-(1 / 2 : ℝ)) := by
  rw [map_sub, kinetic_truncate]
  refine (PlaneWaveDynamics.norm_sub_truncate_le (gF_pos hL) n _).trans ?_
  calc ∑ a : Fin eta, ‖tailMask (gF L) (gF L * n) a (coulombFourierKineticH2 sys (gF L) w)‖
      ≤ ∑ _a : Fin eta, M * (gF L * n) ^ (-(1 / 2 : ℝ)) :=
        Finset.sum_le_sum fun a _ => (h.2 a _ hK).2
    _ = eta * M * (gF L * n) ^ (-(1 / 2 : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Tail

/-! ## Along the trajectory -/

section Consts

variable (sys : CoulombSystem eta ν) (L Hunit : ℝ) (n : ℕ)

/-- `‖T (1 - P) w(t)‖ ≤ τ Ξ`. -/
noncomputable def tauC : ℝ := eta * cTr sys L Hunit * (gF L * n) ^ (-(1 / 2 : ℝ))

/-- `‖T (w - P w)‖ ≤ e_T Ξ` for the dressed state. -/
noncomputable def eT : ℝ :=
  tauC sys L Hunit n + a2c sys L n * cTr sys L Hunit +
    c2op sys L n * (a0c sys L n * cTr sys L Hunit + Asig sys L n * rhoC sys L Hunit n)

end Consts

section Traj

variable (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) {n : ℕ} (hn : 2 ≤ n)
  (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
  (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
    fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)

include hKernel in
/-- **`lem:dressed-tails` along the trajectory.** At every time `t`, for the dressed state
`ψ̃(t) = e^{Σ_b} ψ(t) = S w`, `ψ̃_R = S (w - P w)` and `r = P ψ̃(t) - P ψ(t)`:

* `ψ̃(t)` has an `H²` representative `w` (`S w = ψ̃(t)`), and for every such `w`:
* `‖ψ̃_R‖ + ‖T (w - P w)‖ ≤ (ρ̃ + e_T) Ξ`, hence `‖ℰ ψ̃_R‖ ≤ (ρ̃ + e_T) Ξ` (`ℰ = 1 + A`);
* `Σ_q (1 + E(q)) |ψ̃_R(q)|² ≤ ρ̃ (ρ̃ + e_T) Ξ²`, i.e. `‖ℰ^{1/2} ψ̃_R‖² ≤ ρ̃ (ρ̃ + e_T) Ξ²`;
* `r` vanishes off `Q`;
* `Θ(r) = ‖(1 + A) r‖ ≤ (1 + A_max) δ_a Ξ`. -/
theorem dressed_energy_bounds (Hunit : ℝ) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    (hKg : 1 ≤ gF L * n) (D : EvoData L H) (t : ℝ) :
    (∃ w : MolecularFourierH2 eta, Sm eta L w = psiT sys hL hn D.U D.u₀ t) ∧
    (∀ w : MolecularFourierH2 eta, Sm eta L w = psiT sys hL hn D.U D.u₀ t →
      ‖Sm eta L (w - molecularH2Truncate n w)‖ +
          ‖coulombFourierKineticH2 sys (gF L) (w - molecularH2Truncate n w)‖ ≤
        (rhoT sys L Hunit n + eT sys L Hunit n) * D.Xi ∧
      (Summable fun q => (1 + Ek sys L q) * ‖Sm eta L (w - molecularH2Truncate n w) q‖ ^ 2) ∧
      ∑' q, (1 + Ek sys L q) * ‖Sm eta L (w - molecularH2Truncate n w) q‖ ^ 2 ≤
        rhoT sys L Hunit n * (rhoT sys L Hunit n + eT sys L Hunit n) * D.Xi ^ 2) ∧
    (∀ q, q ∉ Qs eta n → (molecularH2Truncate n (psiT sys hL hn D.U D.u₀ t) -
        molecularH2Truncate n (D.U t (Sm eta L D.u₀))) q = 0) ∧
    ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1
        (aT sys hL hn D.U D.u₀ t - ext eta n (D.U t (Sm eta L D.u₀)))‖ ≤
      (1 + Amax eta L n) * dA sys L Hunit n * D.Xi := by
  obtain ⟨w, hw1, -, hF⟩ := traj_good sys hL H hKernel Hunit hPeriodic D t
  obtain ⟨hA1, -, hA3, -⟩ := aT_bounds sys hL hn H hKernel Hunit hPeriodic hKg D t
  have hΞ := D.Xi_nonneg
  have hR := fgood_R hF hL hKg
  have hT := fgood_T hF hL hKg
  have hρ : ‖Sm eta L w - molecularH2Truncate n (Sm eta L w)‖ ≤ rhoC sys L Hunit n * D.Xi :=
    hR.trans (le_of_eq (by unfold rhoC; ring))
  have hτ : ‖coulombFourierKineticH2 sys (gF L) (w - molecularH2Truncate n w)‖ ≤
      tauC sys L Hunit n * D.Xi :=
    hT.trans (le_of_eq (by unfold tauC; ring))
  have hpsi : psiT sys hL hn D.U D.u₀ t = exp (Sig sys L n hL hn) (Sm eta L w) := by
    unfold psiT; rw [hw1]
  refine ⟨⟨exp (SigG sys hL hn) w, by rw [exp_SigG_apply, hpsi]⟩, fun w' hw' => ?_,
    fun q hq => ?_, ?_⟩
  · have hw'e : w' = exp (SigG sys hL hn) w :=
      molecularH2StateMap_injective eta (gF L) (by
        change Sm eta L w' = Sm eta L (exp (SigG sys hL hn) w)
        rw [hw', hpsi, exp_SigG_apply])
    have hS : Sm eta L (w' - molecularH2Truncate n w') =
        psiT sys hL hn D.U D.u₀ t - molecularH2Truncate n (psiT sys hL hn D.U D.u₀ t) := by
      rw [map_sub, stateMap_truncate, hw']
    have hK := dressed_kin_tail sys hL hn w hρ hτ hF.1
    rw [← hw'e] at hK
    have hK' : ‖coulombFourierKineticH2 sys (gF L) (w' - molecularH2Truncate n w')‖ ≤
        eT sys L Hunit n * D.Xi := hK.trans (le_of_eq (by unfold eT; ring))
    have h1 : ‖Sm eta L (w' - molecularH2Truncate n w')‖ ≤ rhoT sys L Hunit n * D.Xi := by
      rw [hS]; exact hA1
    obtain ⟨hs, hb⟩ := dressed_half_tail sys (w' - molecularH2Truncate n w')
    refine ⟨?_, hs, ?_⟩
    · calc _ ≤ rhoT sys L Hunit n * D.Xi + eT sys L Hunit n * D.Xi := add_le_add h1 hK'
        _ = _ := by ring
    · refine hb.trans ?_
      have hr0 : 0 ≤ rhoT sys L Hunit n * D.Xi := (norm_nonneg _).trans h1
      calc ‖Sm eta L (w' - molecularH2Truncate n w')‖ *
            (‖Sm eta L (w' - molecularH2Truncate n w')‖ +
              ‖coulombFourierKineticH2 sys (gF L) (w' - molecularH2Truncate n w')‖)
          ≤ (rhoT sys L Hunit n * D.Xi) *
              (rhoT sys L Hunit n * D.Xi + eT sys L Hunit n * D.Xi) :=
            mul_le_mul h1 (add_le_add h1 hK') (by positivity) hr0
        _ = _ := by ring
  · unfold psiT
    exact dressed_r_support sys hL hn _ q hq
  · refine (wt_one_le_Amax sys _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hA3 (by linarith [Amax_nonneg eta L n])

end Traj

end FSNormal

namespace FSAsymp

open FSNormal PL

variable {eta : ℕ} {ν : Type} [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
  (Hunit : ℝ)

theorem pl_M2 : PL (fun n => M2 sys L n) (-1) :=
  (cnpow (Fintype.card (Ch eta) * cSig2 sys L * c1E eta L ^ 2 * (416 / 3)) (-1)).congr
    ⟨1, fun n _ => by rw [Real.rpow_neg_one]; unfold M2; ring⟩

theorem pl_a2c : PL (fun n => a2c sys L n) (-1 / 2) := by
  have h := ((((pl_M2 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul_const
    53).sqrt).mul_const (cE sys L)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

theorem pl_c2op : PL (fun n => c2op sys L n) 1 := by
  have hc : PL (fun n => (2 * (⌈(n : ℝ) / 4⌉₊ : ℝ) + 1)) 1 := by
    refine (lin 4).of_le' ⟨1, fun n hn => ?_⟩
    have h1 : (⌈(n : ℝ) / 4⌉₊ : ℝ) < (n : ℝ) / 4 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg (by positivity)]
    linarith
  have h := (((pl_M2 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul
    (hc.pow 3)).sqrt
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold c2op; ring_nf

include hL in
theorem pl_tauC : PL (fun n => tauC sys L Hunit n) (-1 / 2) := by
  have h := (lin_rpow (gF_pos hL).le (-(1 / 2 : ℝ))).const_mul (eta * cTr sys L Hunit)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold tauC; ring

include hL in
theorem pl_eT : PL (fun n => eT sys L Hunit n) (-1 / 2) := by
  have hA := pl_Asig sys (L := L)
  have ha0 := (pl_a0c sys (L := L)).mul_const (cTr sys L Hunit)
  have ha2 := (pl_a2c sys (L := L)).mul_const (cTr sys L Hunit)
  have hr := pl_rhoC sys hL Hunit
  have hin := ha0.add_le (hA.mul hr) (r := -5 / 2) le_rfl (by norm_num)
  have h3 := (pl_c2op sys (L := L)).mul_le hin (r := -3 / 2) (by norm_num)
  have h := ((pl_tauC sys hL Hunit).add ha2).add_le h3 (r := -1 / 2) le_rfl (by norm_num)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold eT; ring

include hL in
/-- `ρ̃ (ρ̃ + e_T) = O(K⁻³)`: `‖ℰ^{1/2} ψ̃_R‖ ≤ C Ξ K^{-3/2}`. -/
theorem pl_half_tail :
    PL (fun n => rhoT sys L Hunit n * (rhoT sys L Hunit n + eT sys L Hunit n)) (-3) := by
  have h := (pl_rhoT sys hL Hunit).mul_le ((pl_rhoT sys hL Hunit).add_le (pl_eT sys hL Hunit)
    (r := -1 / 2) (by norm_num) le_rfl) (r := -3) (by norm_num)
  exact h

include hL in
/-- `ρ̃ + e_T = O(K^{-1/2})`: `‖ℰ ψ̃_R‖ ≤ C Ξ K^{-1/2}`. -/
theorem pl_energy_tail : PL (fun n => rhoT sys L Hunit n + eT sys L Hunit n) (-1 / 2) :=
  (pl_rhoT sys hL Hunit).add_le (pl_eT sys hL Hunit) (r := -1 / 2) (by norm_num) le_rfl

include hL in
/-- `(1 + A_max) δ_a = O(K^{-3/2})`: `Θ(r) ≤ C Ξ K^{-3/2}`. -/
theorem pl_theta_r : PL (fun n => (1 + Amax eta L n) * dA sys L Hunit n) (-3 / 2) := by
  have h1 : PL (fun n => 1 + Amax eta L n) 2 :=
    (const 1).add_le (pl_Amax (eta := eta) (L := L)) (r := 2) (by norm_num) le_rfl
  exact h1.mul_le (pl_dA sys hL Hunit) (r := -3 / 2) (by norm_num)


/-! ## Log-free orders

`PL` (`PlaneWave.Source.PowerPolylog`) allows a power of `ℓ(n) = 1 + log n`. The coefficients of `lem:dressed-tails` are
explicit powers of `n`, so their orders hold with no logarithm: `PW f p` says `|f(n)| ≤ C n^p` for
all large `n`. -/

/-- **Power bounds without logarithms**: `|f(n)| ≤ C n^p` for all large `n`. -/
def PW (f : ℕ → ℝ) (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n, N ≤ n → |f n| ≤ C * (n : ℝ) ^ p

namespace PW

variable {f g : ℕ → ℝ} {p q r : ℝ}

theorem mono (hf : PW f p) (hpq : p ≤ q) : PW f q := by
  obtain ⟨C, hC, N, h⟩ := hf
  refine ⟨C, hC, max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  exact (h n (le_trans (le_max_left _ _) hn)).trans
    (mul_le_mul_of_nonneg_left (PL.npow_le hn1 hpq) hC)

theorem of_le' (hg : PW g p) (h : ∃ N : ℕ, ∀ n, N ≤ n → |f n| ≤ g n) : PW f p := by
  obtain ⟨C, hC, N, hb⟩ := hg
  obtain ⟨N', h'⟩ := h
  exact ⟨C, hC, max N N', fun n hn => (h' n (le_trans (le_max_right _ _) hn)).trans
    ((le_abs_self _).trans (hb n (le_trans (le_max_left _ _) hn)))⟩

theorem congr (hf : PW f p) (h : ∃ N : ℕ, ∀ n, N ≤ n → g n = f n) : PW g p := by
  obtain ⟨C, hC, N, hb⟩ := hf
  obtain ⟨N', h'⟩ := h
  exact ⟨C, hC, max N N', fun n hn => by
    rw [h' n (le_trans (le_max_right _ _) hn)]; exact hb n (le_trans (le_max_left _ _) hn)⟩

theorem add (hf : PW f p) (hg : PW g p) : PW (fun n => f n + g n) p := by
  obtain ⟨C, hC, N, h⟩ := hf
  obtain ⟨C', hC', N', h'⟩ := hg
  refine ⟨C + C', by positivity, max N N', fun n hn => ?_⟩
  have h1 := h n (le_trans (le_max_left _ _) hn)
  have h2 := h' n (le_trans (le_max_right _ _) hn)
  calc |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ ≤ C * (n : ℝ) ^ p + C' * (n : ℝ) ^ p := add_le_add h1 h2
    _ = (C + C') * (n : ℝ) ^ p := by ring

theorem add' (hf : PW f p) (hg : PW g q) : PW (fun n => f n + g n) (max p q) :=
  (hf.mono (le_max_left p q)).add (hg.mono (le_max_right p q))

theorem add_le (hf : PW f p) (hg : PW g q) (hp : p ≤ r) (hq : q ≤ r) :
    PW (fun n => f n + g n) r := (hf.mono hp).add (hg.mono hq)

theorem mul (hf : PW f p) (hg : PW g q) : PW (fun n => f n * g n) (p + q) := by
  obtain ⟨C, hC, N, h⟩ := hf
  obtain ⟨C', hC', N', h'⟩ := hg
  refine ⟨C * C', by positivity, max (max N N') 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hN' : N' ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [abs_mul, Real.rpow_add hn0]
  have := PL.npow_nonneg n p
  have := PL.npow_nonneg n q
  calc |f n| * |g n| ≤ (C * (n : ℝ) ^ p) * (C' * (n : ℝ) ^ q) :=
        mul_le_mul (h n hN) (h' n hN') (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem mul_le (hf : PW f p) (hg : PW g q) (h : p + q ≤ r) : PW (fun n => f n * g n) r :=
  (hf.mul hg).mono h

theorem const (c : ℝ) : PW (fun _ => c) 0 :=
  ⟨|c|, abs_nonneg c, 1, fun n _ => by rw [Real.rpow_zero, mul_one]⟩

theorem npow (p : ℝ) : PW (fun n => (n : ℝ) ^ p) p :=
  ⟨1, zero_le_one, 0, fun n _ => by rw [abs_of_nonneg (PL.npow_nonneg n p), one_mul]⟩

theorem const_mul (hf : PW f p) (c : ℝ) : PW (fun n => c * f n) p := by
  have := (PW.const c).mul hf
  simpa using this

theorem mul_const (hf : PW f p) (c : ℝ) : PW (fun n => f n * c) p := by
  have := hf.mul (PW.const c)
  simpa using this

theorem cnpow (c p : ℝ) : PW (fun n => c * (n : ℝ) ^ p) p := (PW.npow p).const_mul c

theorem npow_nat (m : ℕ) : PW (fun n => (n : ℝ) ^ m) m :=
  (PW.npow (m : ℝ)).congr ⟨0, fun n _ => by rw [Real.rpow_natCast]⟩

theorem lin (c : ℝ) : PW (fun n => c * (n : ℝ)) 1 :=
  (PW.cnpow c 1).congr ⟨0, fun n _ => by rw [Real.rpow_one]⟩

theorem lin_rpow {c : ℝ} (hc : 0 ≤ c) (r : ℝ) : PW (fun n => (c * (n : ℝ)) ^ r) r :=
  (PW.cnpow (c ^ r) r).congr ⟨0, fun n _ => by rw [Real.mul_rpow hc (Nat.cast_nonneg n)]⟩

theorem sqrt (hf : PW f p) : PW (fun n => Real.sqrt (f n)) (p / 2) := by
  obtain ⟨C, hC, N, h⟩ := hf
  refine ⟨C ^ (1 / 2 : ℝ), Real.rpow_nonneg hC _, N, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := PL.npow_nonneg n p
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : Real.sqrt (f n) ≤ (C * (n : ℝ) ^ p) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans (h n hn))
  refine h1.trans (le_of_eq ?_)
  rw [Real.mul_rpow hC (by positivity), ← Real.rpow_mul hn0,
    show p * (1 / 2 : ℝ) = p / 2 by ring]

theorem pow (hf : PW f p) (m : ℕ) : PW (fun n => f n ^ m) (p * m) := by
  induction m with
  | zero => simpa using PW.const 1
  | succ m ih =>
    have := ih.mul hf
    refine (this.congr ⟨0, fun n _ => by ring⟩).mono (le_of_eq (by push_cast; ring))

theorem rpow (hf : PW f p) (h0 : ∃ N : ℕ, ∀ n, N ≤ n → 0 ≤ f n) {r : ℝ} (hr : 0 ≤ r) :
    PW (fun n => f n ^ r) (p * r) := by
  obtain ⟨C, hC, N, h⟩ := hf
  obtain ⟨N₀, h0'⟩ := h0
  refine ⟨C ^ r, Real.rpow_nonneg hC r, max N N₀, fun n hn => ?_⟩
  have hN : N ≤ n := le_trans (le_max_left _ _) hn
  have hN₀ : N₀ ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hf0 := h0' n hN₀
  rw [abs_of_nonneg (Real.rpow_nonneg hf0 r)]
  have h1 : f n ^ r ≤ (C * (n : ℝ) ^ p) ^ r :=
    Real.rpow_le_rpow hf0 ((le_abs_self _).trans (h n hN)) hr
  refine h1.trans (le_of_eq ?_)
  have := PL.npow_nonneg n p
  rw [Real.mul_rpow hC (by positivity), ← Real.rpow_mul hn0]

/-- A log-free bound is in particular a `PL` bound. -/
theorem toPL (hf : PW f p) : PL f p := by
  obtain ⟨C, hC, N, h⟩ := hf
  exact ⟨C, 0, hC, le_rfl, max N 1, fun n hn => by
    rw [Real.rpow_zero, mul_one]; exact h n (le_trans (le_max_left _ _) hn)⟩

end PW

section LogFree

theorem pw_Asig : PW (fun n => Asig sys L n) (-1) :=
  (PW.cnpow (A0 sys L) (-1)).congr ⟨1, fun n hn => by
    rw [Asig_eq sys (by omega), Real.rpow_neg_one, div_eq_mul_inv]⟩

theorem pw_M0 : PW (fun n => M0 sys L n) (-5) :=
  (PW.cnpow (cM0 sys L) (-5)).congr ⟨1, fun n hn => by
    rw [M0_eq sys (by omega), Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv,
      show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]⟩

theorem pw_M1 : PW (fun n => M1 sys L n) (-3) :=
  (PW.cnpow (cM1 sys L) (-3)).congr ⟨1, fun n hn => by
    rw [M1_eq sys (by omega), Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]⟩

theorem pw_a0c : PW (fun n => a0c sys L n) (-5 / 2) := by
  have h := ((((pw_M0 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul_const
    53).sqrt).mul_const (cE sys L)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

theorem pw_a1c : PW (fun n => a1c sys L n) (-3 / 2) := by
  have h := ((((pw_M1 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul_const
    53).sqrt).mul_const (cE sys L)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

theorem pw_one_add_sq (c : ℝ) : PW (fun n => 1 + c * (n : ℝ) ^ 2) 2 := by
  have h := (PW.const 1).add' ((PW.npow_nat 2).const_mul c)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

theorem pw_ceil : PW (fun n => (2 * (⌈(n : ℝ) / 4⌉₊ : ℝ) + 1)) 1 := by
  refine (PW.lin 4).of_le' ⟨1, fun n hn => ?_⟩
  have h1 : (⌈(n : ℝ) / 4⌉₊ : ℝ) < (n : ℝ) / 4 + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity)]
  linarith

theorem pw_Cop : PW (fun n => Cop sys L n) 0 := by
  have h := ((pw_M1 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul
    (pw_ceil.pow 3)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold Cop; ring

theorem pw_CZ : PW (fun n => CZ sys L Hunit n) 0 := by
  have h1 : PW (fun n => 1 + eta * gF L ^ 2 / 16 * (n : ℝ) ^ 2) 2 := pw_one_add_sq _
  have h2 := (h1.mul ((pw_Asig sys (L := L)).pow 2)).const_mul 2
  have h3 := ((pw_Cop sys (L := L)).const_mul 2).add' h2
  have h := (h3.sqrt).const_mul (finiteCoulombPhysicalMassConstant sys L Hunit)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold CZ; ring_nf

theorem pw_Amax : PW (fun n => Amax eta L n) 2 := by
  have h := (PW.npow_nat 2).const_mul (3 * eta * gF L ^ 2 / 2)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold Amax; ring

include hL in
theorem pw_rhoC : PW (fun n => rhoC sys L Hunit n) (-5 / 2) := by
  have h := (PW.lin_rpow (gF_pos hL).le (-(5 / 2 : ℝ))).const_mul (eta * cTr sys L Hunit)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold rhoC; ring

include hL in
theorem pw_omC : PW (fun n => omC sys L Hunit n) (-3 / 2) := by
  have h := (PW.lin_rpow (gF_pos hL).le (-(3 / 2 : ℝ))).const_mul
    (Real.sqrt 3 * eta * finiteCoulombPhysicalMassConstant sys L Hunit * cTr sys L Hunit)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold omC; ring

include hL in
theorem pw_rhoT : PW (fun n => rhoT sys L Hunit n) (-5 / 2) := by
  have hA := pw_Asig sys (L := L)
  have ha0 := (pw_a0c sys (L := L)).mul_const (cTr sys L Hunit)
  have hr := pw_rhoC sys hL Hunit
  have h := (hr.add ha0).add_le (hA.mul (ha0.add_le (hA.mul hr) (r := -5 / 2) le_rfl
    (by norm_num))) (r := -5 / 2) le_rfl (by norm_num)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold rhoT; ring

include hL in
theorem pw_omT : PW (fun n => omT sys L Hunit n) (-3 / 2) := by
  have hA := pw_Asig sys (L := L)
  have ha0 := (pw_a0c sys (L := L)).mul_const (cTr sys L Hunit)
  have ha1 := ((pw_a1c sys (L := L)).mul_const (cTr sys L Hunit)).const_mul
    (finiteCoulombPhysicalMassConstant sys L Hunit)
  have hr := pw_rhoC sys hL Hunit
  have h := ((pw_omC sys hL Hunit).add ha1).add_le ((pw_CZ sys Hunit (L := L)).mul
    (ha0.add_le (hA.mul hr) (r := -5 / 2) le_rfl (by norm_num))) (r := -3 / 2) le_rfl
    (by norm_num)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold omT; ring

include hL in
theorem pw_dA : PW (fun n => dA sys L Hunit n) (-7 / 2) := by
  have hA := pw_Asig sys (L := L)
  have ha0 := (pw_a0c sys (L := L)).mul_const (cTr sys L Hunit)
  have hr := pw_rhoC sys hL Hunit
  have h := hA.mul_le (hr.add (ha0.add_le (hA.mul hr) (r := -5 / 2) le_rfl (by norm_num)))
    (r := -7 / 2) (by norm_num)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold dA; ring

omit [Fintype ν] in
include hL in
theorem pw_Kqpow {r : ℝ} (hr : 0 ≤ r) : PW (fun n => (1 + Kq L n) ^ r) r := by
  have h := ((PW.const 1).add_le (PW.lin (Real.sqrt 3 * gF L)) (r := 1) (by norm_num)
    le_rfl).rpow ⟨0, fun n _ => by have := gF_pos hL; positivity⟩ hr
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (le_of_eq (by ring))
  unfold Kq; ring_nf

omit [Fintype ν] in
include hL in
theorem pw_pertF {δ : ℕ → ℝ} {q : ℝ} (hδ : PW δ q) :
    PW (fun n => pertF eta L n (δ n)) (q + 5 / 2) := by
  have t1 := hδ.mul (pw_Kqpow hL (r := 5 / 2) (by norm_num))
  have t2 := (((PW.const 1).add_le (pw_Amax (eta := eta) (L := L)) (r := 2) (by norm_num)
    le_rfl).mul hδ).mul_le (pw_Kqpow hL (r := 1 / 2) (by norm_num)) (r := q + 5 / 2)
    (by linarith)
  have h := t1.add t2
  exact h.congr ⟨0, fun n _ => rfl⟩

include hL in
/-- The goodness budget `m_A` of `ψ̃_P` is bounded. -/
theorem pw_mA : PW (fun n => mA sys L Hunit n) 0 := by
  have h := (PW.const (2 * cTr sys L Hunit)).add_le
    (pw_pertF hL (eta := eta) (pw_dA sys hL Hunit)) (r := 0) le_rfl (by norm_num)
  exact h.congr ⟨0, fun n _ => rfl⟩

theorem pw_M2 : PW (fun n => M2 sys L n) (-1) :=
  (PW.cnpow (Fintype.card (Ch eta) * cSig2 sys L * c1E eta L ^ 2 * (416 / 3)) (-1)).congr
    ⟨1, fun n _ => by rw [Real.rpow_neg_one]; unfold M2; ring⟩

theorem pw_a2c : PW (fun n => a2c sys L n) (-1 / 2) := by
  have h := ((((pw_M2 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul_const
    53).sqrt).mul_const (cE sys L)
  refine (h.congr ⟨0, fun n _ => rfl⟩).mono (by norm_num)

theorem pw_c2op : PW (fun n => c2op sys L n) 1 := by
  have h := (((pw_M2 sys (L := L)).const_mul ((Fintype.card (Ch eta) : ℝ) ^ 2)).mul
    (pw_ceil.pow 3)).sqrt
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold c2op; ring_nf

include hL in
theorem pw_tauC : PW (fun n => tauC sys L Hunit n) (-1 / 2) := by
  have h := (PW.lin_rpow (gF_pos hL).le (-(1 / 2 : ℝ))).const_mul (eta * cTr sys L Hunit)
  refine (h.congr ⟨0, fun n _ => ?_⟩).mono (by norm_num)
  unfold tauC; ring

include hL in
theorem pw_eT : PW (fun n => eT sys L Hunit n) (-1 / 2) := by
  have hA := pw_Asig sys (L := L)
  have ha0 := (pw_a0c sys (L := L)).mul_const (cTr sys L Hunit)
  have ha2 := (pw_a2c sys (L := L)).mul_const (cTr sys L Hunit)
  have hr := pw_rhoC sys hL Hunit
  have hin := ha0.add_le (hA.mul hr) (r := -5 / 2) le_rfl (by norm_num)
  have h3 := (pw_c2op sys (L := L)).mul_le hin (r := -3 / 2) (by norm_num)
  have h := ((pw_tauC sys hL Hunit).add ha2).add_le h3 (r := -1 / 2) le_rfl (by norm_num)
  refine h.congr ⟨0, fun n _ => ?_⟩
  unfold eT; ring

include hL in
/-- **`lem:dressed-tails`, the orders with no logarithm** (`n` is the cube index, `K = g n`): the
coefficients of `dressed_energy_bounds` and of the trajectory bounds `aT_bounds` satisfy
`ρ̃ = O(K^{-5/2})` (`‖ψ̃_R‖`), `ω̃ = O(K^{-3/2})` (`‖W ψ̃_R‖`), `ρ̃ + e_T = O(K^{-1/2})`
(`‖ℰ ψ̃_R‖`), `ρ̃ (ρ̃ + e_T) = O(K⁻³)` (`‖ℰ^{1/2} ψ̃_R‖²`), `δ_a = O(K^{-7/2})` (`‖r‖`) and
`(1 + A_max) δ_a = O(K^{-3/2})` (`Θ(r)`), and the goodness budget `m_A` of `ψ̃_P` is `O(1)`. -/
theorem dressed_tails_logfree :
    PW (fun n => rhoT sys L Hunit n) (-5 / 2) ∧ PW (fun n => omT sys L Hunit n) (-3 / 2) ∧
      PW (fun n => rhoT sys L Hunit n + eT sys L Hunit n) (-1 / 2) ∧
      PW (fun n => rhoT sys L Hunit n * (rhoT sys L Hunit n + eT sys L Hunit n)) (-3) ∧
      PW (fun n => dA sys L Hunit n) (-7 / 2) ∧
      PW (fun n => (1 + Amax eta L n) * dA sys L Hunit n) (-3 / 2) ∧
      PW (fun n => mA sys L Hunit n) 0 := by
  have hρ := pw_rhoT sys hL Hunit
  have he := hρ.add_le (pw_eT sys hL Hunit) (r := -1 / 2) (by norm_num) le_rfl
  have h1 : PW (fun n => 1 + Amax eta L n) 2 :=
    (PW.const 1).add_le (pw_Amax (eta := eta) (L := L)) (r := 2) (by norm_num) le_rfl
  exact ⟨hρ, pw_omT sys hL Hunit, he, hρ.mul_le he (r := -3) (by norm_num), pw_dA sys hL Hunit,
    h1.mul_le (pw_dA sys hL Hunit) (r := -3 / 2) (by norm_num), pw_mA sys hL Hunit⟩

end LogFree

end FSAsymp
