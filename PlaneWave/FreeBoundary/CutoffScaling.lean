import PlaneWave.FreeBoundary.FreeDynamicsNonBO

/-!
# Mass-weighted cutoffs: scaling

`free_dyn_grid_nbo` holds for any mass-weighted cutoff `χ` whose derivative bound `D` and
cancellation constant `C` are at most `D̄`, `C̄`. Scaling a fixed shape gives such cutoffs for all
large `L` with the same `D̄`, `C̄`: for `X` at `L` and `s ≥ 1`, `χ_s(r) = χ(r/s)` is a cutoff at
`s L` with `D_s = D/s` and `C_s = C/s²`; it is `1` on `s · B^one`, its derivatives vanish off
`s · S`, and it is supported where `|x_i| ≤ s ρ` if `χ` is supported where `|x_i| ≤ ρ`. A fixed
shape exists for all masses `m_i ≥ 1`: `χ = F(Σ_i m_i |x_i|²)` (`exists_quadCutoff`).

* `dirD_scale`: `∂_a (k g(c r)) = k c (∂_a g)(c r)`;
* `DomCutoff.scale`, with `scale_D_le`, `scale_C_le`;
* `DomCutoff.scale_one`, `scale_dS`, `scale_d2S`, `scale_ret`: the support conditions.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

variable {eta : ℕ}

/-! ## Derivatives of scaled functions -/

section Scale

/-- `∂_a (k g(c r)) = k c (∂_a g)(c r)`. -/
lemma dirD_scale {G : Rcfg eta → ℝ} (hG : Differentiable ℝ G) (k c : ℝ) (a : Fin eta × Fin 3) :
    dirD a (fun r => k * G (c • r)) = fun r => k * c * dirD a G (c • r) := by
  funext r
  unfold dirD
  have h1 : HasFDerivAt (fun r : Rcfg eta => c • r)
      (c • ContinuousLinearMap.id ℝ (Rcfg eta)) r := (hasFDerivAt_id r).const_smul c
  have h2 : HasFDerivAt (fun r => G (c • r))
      ((fderiv ℝ G (c • r)).comp (c • ContinuousLinearMap.id ℝ (Rcfg eta))) r :=
    (hG (c • r)).hasFDerivAt.comp r h1
  rw [(h2.const_mul k).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

lemma dirD_scale' {G : Rcfg eta → ℝ} (hG : Differentiable ℝ G) (c : ℝ) (a : Fin eta × Fin 3) :
    dirD a (fun r => G (c • r)) = fun r => c * dirD a G (c • r) := by
  simpa using dirD_scale hG 1 c a

lemma particle_smul (c : ℝ) (r : Rcfg eta) (i : Fin eta) :
    particle (c • r) i = c • particle r i := by
  ext d
  simp [particle]

lemma abs_pow_mul_le {c x D : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hx : |x| ≤ D) (k : ℕ) :
    |c ^ (k + 1) * x| ≤ c * D := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg hc0 _), pow_succ']
  have hD : 0 ≤ D := (abs_nonneg _).trans hx
  have h1 : c ^ k ≤ 1 := pow_le_one₀ hc0 hc1
  calc c * c ^ k * |x| ≤ c * 1 * D := by gcongr
    _ = c * D := by ring

end Scale

namespace DomCutoff

variable {L : ℝ} {m : Fin eta → ℝ} (X : DomCutoff eta L m)

lemma diff0 : Differentiable ℝ X.χ := X.smooth.differentiable (by norm_num)

lemma diff1 (a : Fin eta × Fin 3) : Differentiable ℝ (dirD a X.χ) :=
  (X.c1 a).differentiable (by norm_num)

lemma diff2 (a b : Fin eta × Fin 3) : Differentiable ℝ (dirD b (dirD a X.χ)) :=
  (X.c2 a b).differentiable (by norm_num)

lemma diff3 (a b c : Fin eta × Fin 3) : Differentiable ℝ (dirD c (dirD b (dirD a X.χ))) :=
  (X.c3 a b c).differentiable (by norm_num)

variable (c : ℝ)

lemma scale_d1 (a : Fin eta × Fin 3) :
    dirD a (fun r => X.χ (c • r)) = fun r => c * dirD a X.χ (c • r) :=
  dirD_scale' X.diff0 c a

lemma scale_d2 (a b : Fin eta × Fin 3) :
    dirD b (dirD a (fun r => X.χ (c • r))) = fun r => c ^ 2 * dirD b (dirD a X.χ) (c • r) := by
  rw [X.scale_d1 c a, dirD_scale (X.diff1 a) c c b]
  funext r
  ring

lemma scale_d3 (a b d : Fin eta × Fin 3) :
    dirD d (dirD b (dirD a (fun r => X.χ (c • r)))) =
      fun r => c ^ 3 * dirD d (dirD b (dirD a X.χ)) (c • r) := by
  rw [X.scale_d2 c a b, dirD_scale (X.diff2 a b) (c ^ 2) c d]
  funext r
  ring

lemma scale_d4 (a b d e : Fin eta × Fin 3) :
    dirD e (dirD d (dirD b (dirD a (fun r => X.χ (c • r))))) =
      fun r => c ^ 4 * dirD e (dirD d (dirD b (dirD a X.χ))) (c • r) := by
  rw [X.scale_d3 c a b d, dirD_scale (X.diff3 a b d) (c ^ 3) c e]
  funext r
  ring

lemma massGrad_scale (i : Fin eta) (r : Rcfg eta) :
    massGrad m (fun r => X.χ (c • r)) i r = c • massGrad m X.χ i (c • r) := by
  ext d
  simp only [massGrad, X.scale_d1 c, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **The scaled cutoff** `χ_s(r) = χ(r/s)` at `s L` (`s ≥ 1`): `D_s = D/s`, `C_s = C/s²`. -/
noncomputable def scale {s : ℝ} (hs : 1 ≤ s) : DomCutoff eta (s * L) m where
  χ := fun r => X.χ (s⁻¹ • r)
  smooth := X.smooth.comp (contDiff_const_smul s⁻¹)
  nonneg := fun r => X.nonneg _
  le_one := fun r => X.le_one _
  box := fun r hr a => by
    have hs0 : 0 < s := by linarith
    have h := X.box _ hr a
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hs0, inv_mul_le_iff₀ hs0] at h
    linarith
  D := s⁻¹ * X.D
  D_nonneg := mul_nonneg (inv_nonneg.mpr (by linarith)) X.D_nonneg
  d1 := fun a r => by
    have hs0 : 0 < s := by linarith
    rw [X.scale_d1 s⁻¹ a]
    simpa using abs_pow_mul_le (inv_nonneg.mpr hs0.le) (inv_le_one_of_one_le₀ hs) (X.d1 a _) 0
  d2 := fun a b r => by
    have hs0 : 0 < s := by linarith
    rw [X.scale_d2 s⁻¹ a b]
    exact abs_pow_mul_le (inv_nonneg.mpr hs0.le) (inv_le_one_of_one_le₀ hs) (X.d2 a b _) 1
  d3 := fun a b d r => by
    have hs0 : 0 < s := by linarith
    rw [X.scale_d3 s⁻¹ a b d]
    exact abs_pow_mul_le (inv_nonneg.mpr hs0.le) (inv_le_one_of_one_le₀ hs) (X.d3 a b d _) 2
  d4 := fun a b d e r => by
    have hs0 : 0 < s := by linarith
    rw [X.scale_d4 s⁻¹ a b d e]
    exact abs_pow_mul_le (inv_nonneg.mpr hs0.le) (inv_le_one_of_one_le₀ hs) (X.d4 a b d e _) 3
  C := s⁻¹ * s⁻¹ * X.C
  C_nonneg := by
    have : 0 ≤ s⁻¹ := inv_nonneg.mpr (by linarith)
    have := X.C_nonneg
    positivity
  cancel := fun r i j => by
    have hs0 : 0 < s := by linarith
    have hsi : 0 ≤ s⁻¹ := inv_nonneg.mpr hs0.le
    rw [X.massGrad_scale s⁻¹ i r, X.massGrad_scale s⁻¹ j r, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hsi]
    have h := X.cancel (s⁻¹ • r) i j
    rw [particle_smul, particle_smul, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hsi] at h
    calc s⁻¹ * ‖massGrad m X.χ i (s⁻¹ • r) - massGrad m X.χ j (s⁻¹ • r)‖
        ≤ s⁻¹ * (X.C * (s⁻¹ * ‖particle r i - particle r j‖)) :=
          mul_le_mul_of_nonneg_left h hsi
      _ = s⁻¹ * s⁻¹ * X.C * ‖particle r i - particle r j‖ := by ring

variable {s : ℝ} (hs : 1 ≤ s)

@[simp] lemma scale_χ (r : Rcfg eta) : (X.scale hs).χ r = X.χ (s⁻¹ • r) := rfl

lemma scale_D_le : (X.scale hs).D ≤ X.D := by
  change s⁻¹ * X.D ≤ X.D
  have := X.D_nonneg
  have h1 : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  nlinarith

lemma scale_C_le : (X.scale hs).C ≤ X.C := by
  change s⁻¹ * s⁻¹ * X.C ≤ X.C
  have := X.C_nonneg
  have h1 : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have h0 : 0 ≤ s⁻¹ := inv_nonneg.mpr (by linarith)
  have h2 : s⁻¹ * s⁻¹ ≤ 1 := by nlinarith
  nlinarith

/-- `χ_s = 1` on `s · B^one`. -/
lemma scale_one {Bone : Set (Rcfg eta)} (h : ∀ r ∈ Bone, X.χ r = 1) :
    ∀ r ∈ {r : Rcfg eta | s⁻¹ • r ∈ Bone}, (X.scale hs).χ r = 1 :=
  fun _ hr => h _ hr

/-- The derivatives of `χ_s` vanish off `s · S`. -/
lemma scale_dS {S : Set (Rcfg eta)} (h : ∀ r, r ∉ S → ∀ a, dirD a X.χ r = 0) :
    ∀ r, r ∉ {r : Rcfg eta | s⁻¹ • r ∈ S} → ∀ a, dirD a (X.scale hs).χ r = 0 := by
  intro r hr a
  change dirD a (fun r => X.χ (s⁻¹ • r)) r = 0
  rw [X.scale_d1 s⁻¹ a]
  beta_reduce
  rw [h _ hr a, mul_zero]

lemma scale_d2S {S : Set (Rcfg eta)} (h : ∀ r, r ∉ S → ∀ a, dirD a (dirD a X.χ) r = 0) :
    ∀ r, r ∉ {r : Rcfg eta | s⁻¹ • r ∈ S} → ∀ a, dirD a (dirD a (X.scale hs).χ) r = 0 := by
  intro r hr a
  change dirD a (dirD a (fun r => X.χ (s⁻¹ • r))) r = 0
  rw [X.scale_d2 s⁻¹ a a]
  beta_reduce
  rw [h _ hr a, mul_zero]

/-- If `χ` is supported where every `|x_i| ≤ ρ`, then `χ_s` is supported where `|x_i| ≤ s ρ`. -/
lemma scale_ret {ρ : ℝ} (h : ∀ r, X.χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ ρ) :
    ∀ r, (X.scale hs).χ r ≠ 0 → ∀ i, ‖particle r i‖ ≤ s * ρ := by
  intro r hr i
  have hs0 : 0 < s := by linarith
  have h1 := h _ hr i
  rw [particle_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0),
    inv_mul_le_iff₀ hs0] at h1
  exact h1

lemma measurableSet_scale {T : Set (Rcfg eta)} (hT : MeasurableSet T) :
    MeasurableSet {r : Rcfg eta | s⁻¹ • r ∈ T} :=
  (measurable_const_smul s⁻¹) hT

end DomCutoff

/-! ## A mass-weighted cutoff: `F(Σ_i m_i |x_i|²)` -/

section Quadratic

/-- The mass-weighted square radius `Q(r) = Σ_i m_i |x_i|²` (`= M |X|² + Σ_i m_i |x_i - X|²`, `X`
the centre of mass and `M` the total mass). -/
noncomputable def massQ (m : Fin eta → ℝ) (r : Rcfg eta) : ℝ :=
  ∑ b : Fin eta × Fin 3, m b.1 * r b ^ 2

/-- The profile `F(t) = smoothTransition(2 - t)`: `1` for `t ≤ 1`, `0` for `t ≥ 2`. -/
noncomputable def quadProfile (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

lemma contDiff_quadProfile {n : ℕ∞} : ContDiff ℝ n quadProfile :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

lemma quadProfile_one {t : ℝ} (ht : t ≤ 1) : quadProfile t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma quadProfile_zero {t : ℝ} (ht : 2 ≤ t) : quadProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma deriv_quadProfile_eq_zero {t : ℝ} (ht : t ∉ Icc (1 : ℝ) 2) : deriv quadProfile t = 0 := by
  rcases lt_or_ge t 1 with h | h
  · have e : quadProfile =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds h) fun s hs => quadProfile_one (le_of_lt hs)
    rw [e.deriv_eq, deriv_const]
  · have h2 : 2 < t := by
      by_contra h2
      exact ht ⟨h, not_lt.mp h2⟩
    have e : quadProfile =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds h2) fun s hs => quadProfile_zero (le_of_lt hs)
    rw [e.deriv_eq, deriv_const]

lemma exists_bound_deriv_quadProfile : ∃ M, ∀ t, |deriv quadProfile t| ≤ M := by
  have hc : Continuous (deriv quadProfile) :=
    (contDiff_quadProfile (n := 1)).continuous_deriv (by norm_num)
  have hs : HasCompactSupport (deriv quadProfile) :=
    HasCompactSupport.intro isCompact_Icc fun t ht => deriv_quadProfile_eq_zero ht
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨M, fun t => by simpa [Real.norm_eq_abs] using hM t⟩

lemma contDiff_massQ (m : Fin eta → ℝ) {n : ℕ∞} : ContDiff ℝ n (massQ m) := by
  unfold massQ
  exact ContDiff.sum fun b _ => contDiff_const.mul ((contDiff_apply ℝ ℝ b).pow 2)

lemma dirD_massQ (m : Fin eta → ℝ) (a : Fin eta × Fin 3) (r : Rcfg eta) :
    dirD a (massQ m) r = 2 * m a.1 * r a := by
  let P : Fin eta × Fin 3 → Rcfg eta →L[ℝ] ℝ := fun b => ContinuousLinearMap.proj b
  have hs : HasFDerivAt (fun y : Rcfg eta => ∑ b : Fin eta × Fin 3, m b.1 * P b y ^ 2)
      (∑ b : Fin eta × Fin 3, m b.1 • ((2 • P b r ^ (2 - 1)) • P b)) r :=
    HasFDerivAt.fun_sum fun b _ => (((P b).hasFDerivAt).pow 2).const_mul (m b.1)
  have hQ : HasFDerivAt (massQ m)
      (∑ b : Fin eta × Fin 3, m b.1 • ((2 • P b r ^ (2 - 1)) • P b)) r := hs
  unfold dirD
  rw [hQ.fderiv]
  simp [P, Pi.single_apply]
  ring

lemma dirD_quad (m : Fin eta → ℝ) (a : Fin eta × Fin 3) (r : Rcfg eta) :
    dirD a (fun r => quadProfile (massQ m r)) r =
      deriv quadProfile (massQ m r) * (2 * m a.1 * r a) := by
  have hF : DifferentiableAt ℝ quadProfile (massQ m r) :=
    (contDiff_quadProfile (n := 1)).differentiable (by norm_num) _
  have hG : DifferentiableAt ℝ (massQ m) r :=
    (contDiff_massQ m (n := 1)).differentiable (by norm_num) _
  have h : HasFDerivAt (fun r => quadProfile (massQ m r))
      (deriv quadProfile (massQ m r) • fderiv ℝ (massQ m) r) r :=
    hF.hasDerivAt.comp_hasFDerivAt r hG.hasFDerivAt
  rw [← dirD_massQ m a r]
  unfold dirD
  rw [h.fderiv]
  rfl

/-- **The cancellation**: `∇_iχ/m_i = 2 F'(Q) x_i`. -/
lemma massGrad_quad (m : Fin eta → ℝ) (hm : ∀ i, m i ≠ 0) (i : Fin eta) (r : Rcfg eta) :
    massGrad m (fun r => quadProfile (massQ m r)) i r =
      (2 * deriv quadProfile (massQ m r)) • particle r i := by
  ext d
  simp only [massGrad, dirD_quad, PiLp.smul_apply, smul_eq_mul, particle]
  field_simp [hm i]

lemma sq_le_massQ (m : Fin eta → ℝ) (hm : ∀ i, 1 ≤ m i) (r : Rcfg eta) (b : Fin eta × Fin 3) :
    r b ^ 2 ≤ massQ m r := by
  unfold massQ
  have h1 : r b ^ 2 ≤ m b.1 * r b ^ 2 := by
    have := hm b.1
    nlinarith [sq_nonneg (r b)]
  have h2 := Finset.single_le_sum (f := fun b' => m b'.1 * r b' ^ 2)
    (fun b' _ => mul_nonneg (by linarith [hm b'.1]) (sq_nonneg _)) (Finset.mem_univ b)
  linarith

lemma massQ_lt_of_ne {m : Fin eta → ℝ} {r : Rcfg eta} (h : quadProfile (massQ m r) ≠ 0) :
    massQ m r < 2 := by
  by_contra h'
  exact h (quadProfile_zero (not_lt.mp h'))

/-- `χ = 1` where `Q ≤ 1`. -/
lemma quad_one {m : Fin eta → ℝ} {r : Rcfg eta} (h : massQ m r ≤ 1) :
    quadProfile (massQ m r) = 1 := quadProfile_one h

lemma dirD_eventually_zero {f : Rcfg eta → ℝ} {r : Rcfg eta} {c : ℝ}
    (h : f =ᶠ[𝓝 r] fun _ => c) (a : Fin eta × Fin 3) : dirD a f =ᶠ[𝓝 r] fun _ => 0 :=
  h.eventuallyEq_nhds.mono fun r' hr' => by
    unfold dirD
    rw [hr'.fderiv_eq]
    simp

/-- The derivatives of `χ` vanish where `Q < 1` or `Q > 2`. -/
lemma quad_dS (m : Fin eta → ℝ) {r : Rcfg eta} (h : massQ m r < 1 ∨ 2 < massQ m r)
    (a : Fin eta × Fin 3) :
    dirD a (fun r => quadProfile (massQ m r)) r = 0 ∧
      dirD a (dirD a (fun r => quadProfile (massQ m r))) r = 0 := by
  have hQ : Continuous (massQ m) := (contDiff_massQ m (n := 0)).continuous
  obtain ⟨c, hc⟩ : ∃ c : ℝ, (fun r => quadProfile (massQ m r)) =ᶠ[𝓝 r] fun _ => c := by
    rcases h with h | h
    · exact ⟨1, Filter.eventually_of_mem (hQ.continuousAt.preimage_mem_nhds (Iio_mem_nhds h))
        fun r' hr' => quadProfile_one (le_of_lt hr')⟩
    · exact ⟨0, Filter.eventually_of_mem (hQ.continuousAt.preimage_mem_nhds (Ioi_mem_nhds h))
        fun r' hr' => quadProfile_zero (le_of_lt hr')⟩
  have h1 := dirD_eventually_zero hc a
  exact ⟨h1.self_of_nhds, (dirD_eventually_zero h1 a).self_of_nhds⟩

lemma exists_bound_family {ι : Type*} [Fintype ι] {f : ι → Rcfg eta → ℝ}
    (hc : ∀ i, Continuous (f i)) (hs : ∀ i, HasCompactSupport (f i)) :
    ∃ D, 0 ≤ D ∧ ∀ i r, |f i r| ≤ D := by
  choose C hC using fun i => (hc i).bounded_above_of_compact_support (hs i)
  refine ⟨∑ i, |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun i r => ?_⟩
  have h1 := hC i r
  rw [Real.norm_eq_abs] at h1
  exact h1.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun j => |C j|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)))

lemma hasCompactSupport_chain {f g : Rcfg eta → ℝ} (hf : HasCompactSupport f)
    (hg : tsupport g ⊆ tsupport f) (a : Fin eta × Fin 3) :
    HasCompactSupport (dirD a g) ∧ tsupport (dirD a g) ⊆ tsupport f :=
  ⟨hf.mono' ((subset_tsupport _).trans ((tsupport_dirD_subset a).trans hg)),
    (tsupport_dirD_subset a).trans hg⟩

/-- **A `C⁴` function of compact support has bounded coordinate derivatives of orders `1`
to `4`.** -/
lemma exists_chain_bound {f : Rcfg eta → ℝ} (hf : ContDiff ℝ 4 f) (hc : HasCompactSupport f) :
    ∃ D, 0 ≤ D ∧ (∀ a r, |dirD a f r| ≤ D) ∧ (∀ a b r, |dirD b (dirD a f) r| ≤ D) ∧
      (∀ a b c r, |dirD c (dirD b (dirD a f)) r| ≤ D) ∧
      (∀ a b c d r, |dirD d (dirD c (dirD b (dirD a f))) r| ≤ D) := by
  have c1 : ∀ a, ContDiff ℝ 3 (dirD a f) := fun a => contDiff_dirD_nat (n := 3) hf a
  have c2 : ∀ a b, ContDiff ℝ 2 (dirD b (dirD a f)) := fun a b =>
    contDiff_dirD_nat (n := 2) (c1 a) b
  have c3 : ∀ a b c, ContDiff ℝ 1 (dirD c (dirD b (dirD a f))) := fun a b c =>
    contDiff_dirD_nat (n := 1) (c2 a b) c
  have s1 := fun a => hasCompactSupport_chain hc subset_rfl a
  have s2 := fun a b => hasCompactSupport_chain hc (s1 a).2 b
  have s3 := fun a b c => hasCompactSupport_chain hc (s2 a b).2 c
  have s4 := fun a b c d => hasCompactSupport_chain hc (s3 a b c).2 d
  obtain ⟨D1, h1n, h1⟩ := exists_bound_family (f := fun a => dirD a f)
    (fun a => continuous_dirD hf (by norm_num) a) fun a => (s1 a).1
  obtain ⟨D2, h2n, h2⟩ := exists_bound_family
    (f := fun ab : (Fin eta × Fin 3) × (Fin eta × Fin 3) => dirD ab.2 (dirD ab.1 f))
    (fun ab => continuous_dirD (c1 ab.1) (by norm_num) ab.2) fun ab => (s2 ab.1 ab.2).1
  obtain ⟨D3, h3n, h3⟩ := exists_bound_family
    (f := fun abc : (Fin eta × Fin 3) × (Fin eta × Fin 3) × (Fin eta × Fin 3) =>
      dirD abc.2.2 (dirD abc.2.1 (dirD abc.1 f)))
    (fun abc => continuous_dirD (c2 abc.1 abc.2.1) (by norm_num) abc.2.2)
    fun abc => (s3 abc.1 abc.2.1 abc.2.2).1
  obtain ⟨D4, h4n, h4⟩ := exists_bound_family
    (f := fun abcd : (Fin eta × Fin 3) × (Fin eta × Fin 3) × (Fin eta × Fin 3) ×
        (Fin eta × Fin 3) => dirD abcd.2.2.2 (dirD abcd.2.2.1 (dirD abcd.2.1 (dirD abcd.1 f))))
    (fun abcd => continuous_dirD (c3 abcd.1 abcd.2.1 abcd.2.2.1) (by norm_num) abcd.2.2.2)
    fun abcd => (s4 abcd.1 abcd.2.1 abcd.2.2.1 abcd.2.2.2).1
  refine ⟨D1 + D2 + D3 + D4, by positivity, fun a r => ?_, fun a b r => ?_, fun a b c r => ?_,
    fun a b c d r => ?_⟩
  · have := h1 a r
    linarith
  · have := h2 (a, b) r
    linarith
  · have := h3 (a, b, c) r
    linarith
  · have := h4 (a, b, c, d) r
    linarith

/-- **A mass-weighted cutoff**: `χ(r) = F(Σ_i m_i |x_i|²)` is a `DomCutoff` at `L = 8` for
masses `m_i ≥ 1`, with `∇_iχ/m_i - ∇_jχ/m_j = 2 F'(Q) (x_i - x_j)`. It is `1` where `Q ≤ 1`,
vanishes where `Q ≥ 2` and its derivatives vanish where `Q < 1` or `Q > 2` (`quad_one`,
`massQ_lt_of_ne`, `quad_dS`); scaled by `s ≥ 1` (`DomCutoff.scale`) it gives cutoffs at `8 s` with
the same bounds `D`, `C`. -/
theorem exists_quadCutoff (m : Fin eta → ℝ) (hm : ∀ i, 1 ≤ m i) :
    ∃ X : DomCutoff eta 8 m, ∀ r, X.χ r = quadProfile (massQ m r) := by
  have hsm : ContDiff ℝ 4 (fun r => quadProfile (massQ m r)) :=
    (contDiff_quadProfile (n := 4)).comp (contDiff_massQ m (n := 4))
  have hbox : ∀ r, quadProfile (massQ m r) ≠ 0 → ∀ a, |r a| ≤ 8 / 4 := by
    intro r hr a
    have h1 := massQ_lt_of_ne hr
    have h2 := sq_le_massQ m hm r a
    have h3 : r a ^ 2 < 2 := lt_of_le_of_lt h2 h1
    norm_num
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hcs : HasCompactSupport (fun r => quadProfile (massQ m r)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rcfg eta) 2) fun r hr => ?_
    by_contra hne
    apply hr
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro a
    rw [Real.norm_eq_abs]
    have := hbox r hne a
    norm_num at this
    exact this
  obtain ⟨D, hD0, d1, d2, d3, d4⟩ := exists_chain_bound hsm hcs
  obtain ⟨M, hM⟩ := exists_bound_deriv_quadProfile
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hm0 : ∀ i, m i ≠ 0 := fun i => (lt_of_lt_of_le one_pos (hm i)).ne'
  refine ⟨{ χ := fun r => quadProfile (massQ m r)
            smooth := hsm
            nonneg := fun r => Real.smoothTransition.nonneg _
            le_one := fun r => Real.smoothTransition.le_one _
            box := hbox
            D := D
            D_nonneg := hD0
            d1 := d1
            d2 := d2
            d3 := d3
            d4 := d4
            C := 2 * M
            C_nonneg := by positivity
            cancel := fun r i j => ?_ }, fun r => rfl⟩
  rw [massGrad_quad m hm0 i r, massGrad_quad m hm0 j r, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM _) (by norm_num))
    (norm_nonneg _)

end Quadratic

end FreeBoundary
