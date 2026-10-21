import PlaneWave.Source.QuasiEigenstateTails

/-!
# Flux/source build, block 1b: the time-averaged hot content, eq:tavg-quarter

On the Galerkin space `E_n`, for the retained Hamiltonian `H' = H_N + ΔH` (`ΔH` symmetric,
`‖ΔH‖ ≤ C_Δ`):

* `hotProj L λ`: the Euclidean hot projector `1 - Q`, some register with `|k_a| > λ`;
  `norm_sq_hotProj_le`: `‖(1-Q) u‖² ≤ Σ_a ‖1{|k_a| > λ} u‖²`;
* `hot_sq_le_of_quasi`: for a quasi-eigenstate of energy `-C_low ≤ E ≤ X` and width `γ`,
  `‖(1-Q) q‖² ≤ (α + β (1 + E + C_low)^s) ‖q‖²`, with `α = Σ_a 2 a₁(a)²`, `β = Σ_a 2 b₁(a)²`
  from `regTail_le_of_quasi` (`dev/PlaneWave.Source.QuasiEigenstateTails.lean`), provided `λ > 2 λ₁(a, X)` for every register;
* `retFlow`: the flow `e^{iH'τ}` by the spectral calculus of `H'` (eigenvector basis of the
  symmetric `H'`);
* `graph_le`: `‖(H' + C_low + 1) v‖ ≤ C_G ‖(1 + A) v‖`, `C_G = C_V + C_low + 2`;
* `tavg_hot`: **eq:tavg-quarter, spectral form**: for a datum `u` with kinetic support `A ≤ E₀`,
  `E₀ < X - Δ`,

    `(1/t) ∫₀ᵗ ‖(1-Q) e^{iH'τ} u‖² dτ ≤ 2e [√π (α ‖u‖² + β (1+Δ)^s C_G^s ‖(1+A)^{s/2} u‖²
        + (C_V/(X - Δ - E₀))² ‖(1+A)^{1/2} u‖²) + √(2π) e^{-t²Δ²/2} ‖u‖²]`,

  by `FSSpectral.tavg_hot_abstract` (`dev/PlaneWave.Source.HotContentAbstract.lean`).
-/

set_option autoImplicit false

open scoped InnerProductSpace Real
open PlaneWaveCertificate MeasureTheory

namespace FSGalerkin

open FSLattice FSChannel

variable {eta : ℕ} {ν : Type*}

/-! ## The hot projector -/

section Hot

variable {n : ℕ}

/-- Multiplication by a function of the configuration. -/
noncomputable def cfgMul (φ : Cfg eta n → ℂ) : En eta n →ₗ[ℂ] En eta n where
  toFun u := WithLp.toLp 2 (fun p => φ p * u.ofLp p)
  map_add' u v := by
    ext p
    simp [mul_add]
  map_smul' c u := by
    ext p
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] lemma cfgMul_apply (φ : Cfg eta n → ℂ) (u : En eta n) (p : Cfg eta n) :
    (cfgMul φ u).ofLp p = φ p * u.ofLp p := rfl

/-- The Euclidean hot projector `1 - Q`: some register with `|k_a| > λ`. -/
noncomputable def hotProj (L l : ℝ) : En eta n →ₗ[ℂ] En eta n :=
  cfgMul (fun p => if ∃ a, l < finitePlaneWaveKabs (2 * Real.pi / L) n (p a) then 1 else 0)

lemma norm_sq_hotProj (L l : ℝ) (u : En eta n) :
    ‖hotProj L l u‖ ^ 2 = ∑ p, if (∃ a, l < finitePlaneWaveKabs (2 * Real.pi / L) n (p a))
      then ‖u.ofLp p‖ ^ 2 else 0 := by
  classical
  rw [norm_sq_En]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold hotProj
  rw [cfgMul_apply]
  split_ifs <;> simp

/-- The hot projector is a contraction. -/
lemma norm_hotProj_le (L l : ℝ) (u : En eta n) : ‖hotProj L l u‖ ≤ ‖u‖ := by
  classical
  have h2 : ‖hotProj L l u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [norm_sq_hotProj, norm_sq_En]
    refine Finset.sum_le_sum fun p _ => ?_
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- `‖(1-Q) u‖² ≤ Σ_a ‖1{|k_a| > λ} u‖²`. -/
lemma norm_sq_hotProj_le (L l : ℝ) (u : En eta n) :
    ‖hotProj L l u‖ ^ 2 ≤ ∑ a, ‖regTail L a l u‖ ^ 2 := by
  classical
  rw [norm_sq_hotProj]
  simp_rw [norm_sq_regTail]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun p _ => ?_
  split_ifs with h
  · obtain ⟨a, ha⟩ := h
    calc ‖u.ofLp p‖ ^ 2 = (if l < finitePlaneWaveKabs (2 * Real.pi / L) n (p a)
            then ‖u.ofLp p‖ ^ 2 else 0) := by rw [if_pos ha]
      _ ≤ ∑ b, (if l < finitePlaneWaveKabs (2 * Real.pi / L) n (p b)
            then ‖u.ofLp p‖ ^ 2 else 0) :=
          Finset.single_le_sum (f := fun b => if l < finitePlaneWaveKabs (2 * Real.pi / L) n (p b)
            then ‖u.ofLp p‖ ^ 2 else 0) (fun b _ => by split_ifs <;> positivity)
            (Finset.mem_univ a)
  · exact Finset.sum_nonneg fun b _ => by split_ifs <;> positivity

end Hot

/-! ## The hot content of quasi-eigenstates -/

section HotQuasi

variable [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) {n : ℕ}

/-- `α = Σ_a 2 a₁(a)²`. -/
noncomputable def hotA (sys : CoulombSystem eta ν) (L : ℝ) (s CΔ γ l : ℝ) : ℝ :=
  ∑ a, 2 * regA sys L a s CΔ γ l ^ 2

/-- `β = Σ_a 2 b₁(a)²`. -/
noncomputable def hotB (sys : CoulombSystem eta ν) (L Hunit : ℝ) (s CΔ γ l : ℝ) : ℝ :=
  ∑ a, 2 * regB sys L Hunit a s CΔ γ l ^ 2

lemma qtailL1_mono (a : Fin eta) {E E' : ℝ} (h : E ≤ E') :
    qtailL1 sys L Hunit a E ≤ qtailL1 sys L Hunit a E' := by
  unfold qtailL1
  refine max_le_max le_rfl (Real.sqrt_le_sqrt ?_)
  have := sys.mass_pos a
  nlinarith

/-- **The hot content of a quasi-eigenstate.** -/
theorem hot_sq_le_of_quasi (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} {CΔ : ℝ} (hCΔ : 0 ≤ CΔ) (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {E γ s l X : ℝ} (hγ : 0 ≤ γ) (hs : 3 / 2 < s) (hs2 : s ≤ 2)
    (hE : -Clow sys L Hunit CΔ ≤ E) (hEX : E ≤ X)
    (hl : ∀ a, 2 * qtailL1 sys L Hunit a X < l) (q : En eta n)
    (hq : ‖Hret sys L n ΔH q - (E : ℂ) • q‖ ≤ γ * ‖q‖) :
    ‖hotProj L l q‖ ^ 2 ≤
      (hotA sys L s CΔ γ l + hotB sys L Hunit s CΔ γ l * (1 + E + Clow sys L Hunit CΔ) ^ s) *
        ‖q‖ ^ 2 := by
  refine (norm_sq_hotProj_le L l q).trans ?_
  unfold hotA hotB
  rw [add_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  have hla : 2 * qtailL1 sys L Hunit a E < l :=
    lt_of_le_of_lt (by linarith [qtailL1_mono sys Hunit (L := L) a hEX]) (hl a)
  have h := regTail_le_of_quasi sys Hunit a hL hPeriodic hCΔ hΔb hγ hs hs2 hE q hq hla
  set x := 1 + E + Clow sys L Hunit CΔ with hx
  have hx0 : 0 ≤ x := by rw [hx]; linarith
  set A1 := regA sys L a s CΔ γ l
  set B1 := regB sys L Hunit a s CΔ γ l
  have hxs : (x ^ (s / 2)) ^ 2 = x ^ s := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
    norm_num
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hsq : (A1 + B1 * x ^ (s / 2)) ^ 2 ≤ 2 * A1 ^ 2 + 2 * B1 ^ 2 * x ^ s := by
    rw [← hxs]
    nlinarith [sq_nonneg (A1 - B1 * x ^ (s / 2))]
  calc ‖regTail L a l q‖ ^ 2 ≤ ((A1 + B1 * x ^ (s / 2)) * ‖q‖) ^ 2 := h2
    _ = (A1 + B1 * x ^ (s / 2)) ^ 2 * ‖q‖ ^ 2 := by ring
    _ ≤ (2 * A1 ^ 2 + 2 * B1 ^ 2 * x ^ s) * ‖q‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = _ := by ring

end HotQuasi

/-! ## The retained flow and the graph comparison -/

section Flow

variable [Fintype ν] (sys : CoulombSystem eta ν) (L : ℝ) (n : ℕ)

/-- The eigenvector basis of the symmetric `H' = H_N + ΔH`. -/
noncomputable def retBasis {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) :
    OrthonormalBasis (Fin (Module.finrank ℂ (En eta n))) ℂ (En eta n) :=
  (Hret_isSymmetric sys L n hΔsym).eigenvectorBasis rfl

/-- The eigenvalues of `H'`. -/
noncomputable def retEig {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) :
    Fin (Module.finrank ℂ (En eta n)) → ℝ :=
  (Hret_isSymmetric sys L n hΔsym).eigenvalues rfl

lemma retBasis_eigen {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) (i) :
    Hret sys L n ΔH (retBasis sys L n hΔsym i) =
      (retEig sys L n hΔsym i : ℂ) • retBasis sys L n hΔsym i :=
  (Hret_isSymmetric sys L n hΔsym).apply_eigenvectorBasis rfl i

/-- **The retained flow** `e^{iH'τ} u`. -/
noncomputable def retFlow {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) (τ : ℝ)
    (u : En eta n) : En eta n :=
  FSSpectral.fc (retBasis sys L n hΔsym) (retEig sys L n hΔsym)
    (fun x => Complex.exp (Complex.I * (x : ℂ) * τ)) u

variable {L n}

lemma fc_add_fun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (f g : ℝ → ℂ) (v : E) :
    FSSpectral.fc b lam (fun x => f x + g x) v = FSSpectral.fc b lam f v + FSSpectral.fc b lam g v := by
  unfold FSSpectral.fc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_mul, add_smul]

lemma fc_const {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℂ E) (lam : ι → ℝ) (c : ℂ) (v : E) :
    FSSpectral.fc b lam (fun _ => c) v = c • v := by
  unfold FSSpectral.fc
  have h := FSSpectral.fc_one b lam v
  unfold FSSpectral.fc at h
  conv_rhs => rw [← h]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, one_mul]

omit [Fintype ν] in
/-- `‖A v‖ ≤ ‖(1 + A) v‖`. -/
lemma norm_kin_le_wt (v : En eta n) :
    ‖FSSpectral.kin (sb eta n) (Asym sys L n) v‖ ≤ ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  have h2 : ‖FSSpectral.kin (sb eta n) (Asym sys L n) v‖ ^ 2 ≤
      ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ ^ 2 := by
    rw [norm_sq_wt, norm_sq_En]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [FSSpectral.kin, fc_sb_apply, norm_mul, mul_pow, Real.rpow_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    have h0 := Asym_nonneg sys L n k
    have : Asym sys L n k ^ 2 ≤ (1 + Asym sys L n k) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- **Graph comparison**: `‖(H' + C_low + 1) v‖ ≤ (C_V + C_low + 2) ‖(1 + A) v‖`. -/
theorem graph_le (Hunit : ℝ) (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖) (v : En eta n) :
    ‖FSSpectral.fc (retBasis sys L n hΔsym) (retEig sys L n hΔsym)
        (fun l => ((l + Clow sys L Hunit CΔ + 1 : ℝ) : ℂ)) v‖ ≤
      (CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) *
        ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
  set C₀ := Clow sys L Hunit CΔ with hC₀
  have hC₀0 : 0 ≤ C₀ := (Clow_pos sys Hunit hCΔ).le
  have hfc : FSSpectral.fc (retBasis sys L n hΔsym) (retEig sys L n hΔsym)
      (fun l => ((l + C₀ + 1 : ℝ) : ℂ)) v =
      Hret sys L n ΔH v + ((C₀ + 1 : ℝ) : ℂ) • v := by
    have h1 : (fun l : ℝ => ((l + C₀ + 1 : ℝ) : ℂ)) =
        (fun l : ℝ => (l : ℂ) + ((C₀ + 1 : ℝ) : ℂ)) := by
      funext l; push_cast; ring
    rw [h1, fc_add_fun, fc_const, ← FSSpectral.eigen_fc_id _ _ _ (retBasis_eigen sys L n hΔsym)]
  rw [hfc, Hret_eq_kin_add]
  have hW := norm_le_wt sys L n (s := 1) zero_le_one v
  have hV := (Vret_le_wt sys Hunit n hL hPeriodic hCΔ hΔb v).trans
    (mul_le_mul_of_nonneg_left (wt_mono sys L n (by norm_num : (1 / 2 : ℝ) ≤ 1) v)
      (CVret_nonneg sys Hunit hCΔ))
  have hK := norm_kin_le_wt sys (L := L) v
  have hCV := CVret_nonneg sys Hunit hCΔ (L := L)
  calc ‖FSSpectral.kin (sb eta n) (Asym sys L n) v + Vret sys L n ΔH v + ((C₀ + 1 : ℝ) : ℂ) • v‖
      ≤ ‖FSSpectral.kin (sb eta n) (Asym sys L n) v‖ + ‖Vret sys L n ΔH v‖ +
          ‖((C₀ + 1 : ℝ) : ℂ) • v‖ := norm_add₃_le
    _ ≤ ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ +
          CVret sys L Hunit CΔ * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ +
          (C₀ + 1) * ‖FSSpectral.wt (sb eta n) (Asym sys L n) 1 v‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        have := mul_le_mul_of_nonneg_left hW (by linarith : (0 : ℝ) ≤ C₀ + 1)
        unfold CVret
        linarith
    _ = _ := by ring

end Flow

/-! ## eq:tavg-quarter, spectral form -/

section Tavg

variable [Fintype ν] (sys : CoulombSystem eta ν) {L : ℝ} (Hunit : ℝ) {n : ℕ}

/-- **eq:tavg-quarter, spectral form.** -/
theorem tavg_hot (hL : 0 < L) (hPeriodic : HasCanonicalPeriodicCoulombHardyBound Hunit)
    {ΔH : En eta n →ₗ[ℂ] En eta n} (hΔsym : ΔH.IsSymmetric) {CΔ : ℝ} (hCΔ : 0 ≤ CΔ)
    (hΔb : ∀ v, ‖ΔH v‖ ≤ CΔ * ‖v‖)
    {t Δ X s l E₀ : ℝ} (ht : 0 < t) (hΔ : 0 ≤ Δ) (hs : 3 / 2 < s) (hs2 : s ≤ 2)
    (hX : -Clow sys L Hunit CΔ ≤ X) (hE₀ : E₀ < X - Δ)
    (hl : ∀ a, 2 * qtailL1 sys L Hunit a X < l)
    (u : En eta n) (hu : ∀ k, E₀ < Asym sys L n k → u.ofLp k = 0) :
    (1 / t) * ∫ τ in (0 : ℝ)..t, ‖hotProj L l (retFlow sys L n hΔsym τ u)‖ ^ 2 ≤
      2 * Real.exp 1 * (Real.sqrt π * (hotA sys L s CΔ Δ l * ‖u‖ ^ 2 +
          hotB sys L Hunit s CΔ Δ l * (1 + Δ) ^ s *
            ((CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2) ^ (s / 2)) ^ 2 *
              ‖FSSpectral.wt (sb eta n) (Asym sys L n) (s / 2) u‖ ^ 2 +
          (CVret sys L Hunit CΔ / (X - Δ - E₀)) ^ 2 *
            ‖FSSpectral.wt (sb eta n) (Asym sys L n) (1 / 2) u‖ ^ 2) +
        Real.sqrt (2 * π) * Real.exp (-(t ^ 2 * Δ ^ 2) / 2) * ‖u‖ ^ 2) := by
  classical
  have hH := Hret_isSymmetric sys L n hΔsym
  have hC₀ := (Clow_pos sys Hunit hCΔ (L := L)).le
  have hα : 0 ≤ hotA sys L s CΔ Δ l :=
    Finset.sum_nonneg fun a _ => by positivity
  have hβ : 0 ≤ hotB sys L Hunit s CΔ Δ l :=
    Finset.sum_nonneg fun a _ => by positivity
  have hlow : ∀ i, -Clow sys L Hunit CΔ ≤ retEig sys L n hΔsym i := fun i =>
    eigen_lower (retBasis sys L n hΔsym) (retEig sys L n hΔsym) (Hret sys L n ΔH)
      (retBasis_eigen sys L n hΔsym) (Hret_lower sys Hunit n hL hPeriodic hΔb) i
  have hCG : 0 ≤ CVret sys L Hunit CΔ + Clow sys L Hunit CΔ + 2 := by
    have := CVret_nonneg sys Hunit hCΔ (L := L); linarith
  have hu' : ∀ k, E₀ < Asym sys L n k → ⟪sb eta n k, u⟫_ℂ = 0 := fun k hk => by
    rw [inner_sb]; exact hu k hk
  exact FSSpectral.tavg_hot_abstract (retBasis sys L n hΔsym) (retEig sys L n hΔsym) (sb eta n)
    (Asym sys L n) (Asym_nonneg sys L n) (Hret sys L n ΔH) (Vret sys L n ΔH) hH
    (retBasis_eigen sys L n hΔsym) (Hret_eq_kin_add sys L n ΔH) (CVret_nonneg sys Hunit hCΔ)
    (Vret_le_wt sys Hunit n hL hPeriodic hCΔ hΔb) hlow hCG
    (graph_le sys Hunit hL hPeriodic hΔsym hCΔ hΔb) (hotProj L l) (norm_hotProj_le L l)
    ht hΔ hX (by linarith) hs2 hα hβ hE₀
    (fun E' hE' hE'X q hq => hot_sq_le_of_quasi sys Hunit hL hPeriodic hCΔ hΔb hΔ hs hs2 hE' hE'X hl
      q hq) u hu'

end Tavg

end FSGalerkin
