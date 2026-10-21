import PlaneWave.FreeBoundary.SingularCommutator

/-!
# The cut initial state in `D(H_L²)`, part 4: the second commutator

The free-space identities behind `H_L² T(χu)`: for `u` with `H_∞ u = h` (weakly, `V u = v`),
weak gradients `∇u = g`, `∇h = g'` and second derivatives `∂_a g_b = g2 b a`, and a smooth test
`Ψ`, the kinetic energy of the commutator `[K, χ] u = Σ_a c_a (∂_a²χ u + 2 ∂_aχ g_a)`
(`c_a = -1/(2 m_a)`) is computed by parts. The only singular term is handled by
`singular_identity`.

* `IP Φ ζ f = ∫ conj(Φ) ζ f`;
* `IP_ibp`, `IP_comm`: integration by parts and the weak commutator identity in this notation;
* `freeId_A`, `freeId_B`: `⟨KΨ, ∂_a²χ u⟩` and `⟨KΨ, ∂_aχ g_a⟩`;
* **`freeId_comm`**: `⟨KΨ, [K, χ] u⟩` as a sum of `IP Ψ ζ f` with bounded weights `ζ` and
  `f ∈ {u, g, g2, g', V g, u/|x_i - x_j|}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate Topology
open Finset Set MeasureTheory Filter
open PlaneWaveGrid PlaneWaveCertificate PlaneWaveDynamics PlaneWaveGridDynamics UnitAddTorus

namespace FreeBoundary

attribute [local instance] unitAddCircleMeasureSpaceFB15 unitAddCircleProbabilityMeasureFB15

variable {eta : ℕ}

/-! ## Notation -/

section IPs

/-- `IP Φ ζ f = ∫ conj(Φ) ζ f`. -/
noncomputable def IP (Φ : Rcfg eta → ℂ) (ζ : Rcfg eta → ℝ) (f : FreeL2 eta) : ℂ :=
  ∫ r, conj (Φ r) * ((ζ r : ℂ) * f r)

/-- The kinetic coefficient `c_a = -1/(2 m_a)`. -/
noncomputable def kc (m : Fin eta → ℝ) (a : Fin eta × Fin 3) : ℂ := (-(1 / 2 : ℂ)) * ((m a.1 : ℂ))⁻¹

lemma two_kc (m : Fin eta → ℝ) (a : Fin eta × Fin 3) :
    2 * kc m a = ((-(m a.1)⁻¹ : ℝ) : ℂ) := by
  unfold kc
  push_cast
  ring

lemma IP_sub_right {Φ : Rcfg eta → ℂ} (hΦ : Continuous Φ) {ζ : Rcfg eta → ℝ} (hζ : Continuous ζ)
    (hζc : HasCompactSupport ζ) (f g : FreeL2 eta) : IP Φ ζ (f - g) = IP Φ ζ f - IP Φ ζ g := by
  unfold IP
  rw [← integral_sub (integrable_conj_mul_weight hΦ hζ hζc f)
    (integrable_conj_mul_weight hΦ hζ hζc g)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub f g] with r hr
  rw [hr, Pi.sub_apply]
  ring

/-- Integration by parts: `IP (∂_aΨ) ζ f = -IP Ψ (∂_aζ) f - IP Ψ ζ G_a`. -/
lemma IP_ibp {f : FreeL2 eta} {G : Fin eta × Fin 3 → FreeL2 eta} (hG : HasWeakGrad f G)
    {ζ : Rcfg eta → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ)
    {Ψ : Rcfg eta → ℂ} (hΨ : ContDiff ℝ 1 Ψ) (a : Fin eta × Fin 3) :
    IP (dirD a Ψ) ζ f = -IP Ψ (dirD a ζ) f - IP Ψ ζ (G a) :=
  ibp_weight hG hζ hζc hΨ a

/-- The weak commutator identity:
`IP (KΨ) χ f = IP Ψ χ k + Σ_b c_b (IP Ψ ∂_b²χ f + 2 IP Ψ ∂_bχ g_b)`. -/
lemma IP_comm (m : Fin eta → ℝ) {χ : Rcfg eta → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) {Ψ : Rcfg eta → ℂ} (hΨ : ContDiff ℝ 2 Ψ)
    {f k : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta}
    (hK : HasFreeWeakKinetic m f k) (hg : HasWeakGrad f g) :
    IP (freeKinetic m Ψ) χ f = IP Ψ χ k + ∑ b : Fin eta × Fin 3, kc m b *
      (IP Ψ (dirD b (dirD b χ)) f + 2 * IP Ψ (dirD b χ) (g b)) :=
  (weak_comm_identity m hχ hχc hΨ hK hg).symm

lemma contDiff_freeKinetic (m : Fin eta → ℝ) {Ψ : Rcfg eta → ℂ} {n : ℕ}
    (hΨ : ContDiff ℝ (n + 2) Ψ) : ContDiff ℝ n (freeKinetic m Ψ) := by
  have hK : freeKinetic m Ψ = fun r => (-(1 / 2 : ℂ)) * ∑ a : Fin eta × Fin 3,
      ((m a.1 : ℂ))⁻¹ * dirD a (dirD a Ψ) r :=
    funext fun r => freeKinetic_eq m (hΨ.of_le (by exact_mod_cast (by omega : 2 ≤ n + 2))) r
  rw [hK]
  exact contDiff_const.mul (ContDiff.sum fun a _ => contDiff_const.mul
    (contDiff_dirD_nat (n := n) (contDiff_dirD_nat (n := n + 1) hΨ a) a))

end IPs

/-! ## The two kinds of commutator terms -/

section Terms

variable {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m)
include hL

/-- **The `∂_a²χ u` term**: `IP (KΨ) ∂_a²χ u = IP Ψ ∂_a²χ h - IP Ψ ∂_a²χ v +
Σ_b c_b (IP Ψ ∂_b²∂_a²χ u + 2 IP Ψ ∂_b∂_a²χ g_b)`. -/
lemma freeId_A {u h v : FreeL2 eta} {g : Fin eta × Fin 3 → FreeL2 eta}
    (hK : HasFreeWeakKinetic m u (h - v)) (hg : HasWeakGrad u g) {Ψ : Rcfg eta → ℂ}
    (hΨ : ContDiff ℝ 2 Ψ) (a : Fin eta × Fin 3) :
    IP (freeKinetic m Ψ) (dirD a (dirD a X.χ)) u =
      IP Ψ (dirD a (dirD a X.χ)) h - IP Ψ (dirD a (dirD a X.χ)) v +
        ∑ b : Fin eta × Fin 3, kc m b * (IP Ψ (dirD b (dirD b (dirD a (dirD a X.χ)))) u +
          2 * IP Ψ (dirD b (dirD a (dirD a X.χ))) (g b)) := by
  rw [IP_comm m (X.c2 a a) (X.hcs_of_sub hL (X.ts2 a a)) hΨ hK hg,
    IP_sub_right hΨ.continuous (X.c2 a a).continuous (X.hcs_of_sub hL (X.ts2 a a))]

/-- **The `∂_aχ g_a` term**: `IP (KΨ) ∂_aχ g_a = IP Ψ ∂_aχ g'_a + (IP Ψ ∂_a²χ v + IP (∂_aΨ) ∂_aχ v)
+ Σ_b c_b (-IP Ψ ∂_b²∂_a²χ u - 2 IP Ψ ∂_b∂_a²χ g_b + IP Ψ ∂_a∂_b²∂_aχ u + IP Ψ ∂_b²∂_aχ g_a
+ 2 IP Ψ ∂_a∂_b∂_aχ g_b + 2 IP Ψ ∂_b∂_aχ ∂_a g_b)`. -/
lemma freeId_B {u h v : FreeL2 eta} {g g' : Fin eta × Fin 3 → FreeL2 eta}
    {g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta}
    (hK : HasFreeWeakKinetic m u (h - v)) (hg : HasWeakGrad u g) (hg' : HasWeakGrad h g')
    (hg2 : ∀ b, HasWeakGrad (g b) (g2 b)) {Ψ : Rcfg eta → ℂ} (hΨ : ContDiff ℝ 3 Ψ)
    (a : Fin eta × Fin 3) :
    IP (freeKinetic m Ψ) (dirD a X.χ) (g a) =
      IP Ψ (dirD a X.χ) (g' a) +
        (IP Ψ (dirD a (dirD a X.χ)) v + IP (dirD a Ψ) (dirD a X.χ) v) +
        ∑ b : Fin eta × Fin 3, kc m b *
          (-IP Ψ (dirD b (dirD b (dirD a (dirD a X.χ)))) u -
            2 * IP Ψ (dirD b (dirD a (dirD a X.χ))) (g b) +
            IP Ψ (dirD a (dirD b (dirD b (dirD a X.χ)))) u +
            IP Ψ (dirD b (dirD b (dirD a X.χ))) (g a) +
            2 * IP Ψ (dirD a (dirD b (dirD a X.χ))) (g b) +
            2 * IP Ψ (dirD b (dirD a X.χ)) (g2 b a)) := by
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by norm_num)
  have hΨ2 : ContDiff ℝ 2 Ψ := hΨ.of_le (by norm_num)
  have hdΨ : ContDiff ℝ 2 (dirD a Ψ) := contDiff_dirD_nat (n := 2) hΨ a
  have hKΨ : ContDiff ℝ 1 (freeKinetic m Ψ) := contDiff_freeKinetic m (n := 1) hΨ
  have hχ1 : ContDiff ℝ 1 (dirD a X.χ) := (X.c1 a).of_le (by norm_num)
  have hcs1 : HasCompactSupport (dirD a X.χ) := X.hcs_of_sub hL (X.ts1 a)
  -- step 1: `IP (∂_a KΨ) ∂_aχ u = -IP (KΨ) ∂_a²χ u - IP (KΨ) ∂_aχ g_a`
  have h1 := IP_ibp hg hχ1 hcs1 hKΨ a
  rw [dirD_freeKinetic m hΨ a] at h1
  -- step 2: the two commutator identities
  have h2 := freeId_A hL X hK hg hΨ2 a
  have h3 := IP_comm m ((X.c1 a).of_le (by norm_num)) hcs1 hdΨ hK hg
  rw [IP_sub_right (continuous_dirD hΨ (by norm_num) a) hχ1.continuous hcs1] at h3
  -- step 3: integration by parts in the remaining `∂_aΨ` terms
  have h4 := IP_ibp hg' hχ1 hcs1 hΨ1 a
  have h5 : ∀ b, IP (dirD a Ψ) (dirD b (dirD b (dirD a X.χ))) u =
      -IP Ψ (dirD a (dirD b (dirD b (dirD a X.χ)))) u - IP Ψ (dirD b (dirD b (dirD a X.χ))) (g a) :=
    fun b => IP_ibp hg (X.c3 a b b) (X.hcs_of_sub hL (X.ts3 a b b)) hΨ1 a
  have h6 : ∀ b, IP (dirD a Ψ) (dirD b (dirD a X.χ)) (g b) =
      -IP Ψ (dirD a (dirD b (dirD a X.χ))) (g b) - IP Ψ (dirD b (dirD a X.χ)) (g2 b a) :=
    fun b => IP_ibp (hg2 b) ((X.c2 a b).of_le (by norm_num)) (X.hcs_of_sub hL (X.ts2 a b)) hΨ1 a
  have hsum : ∑ b : Fin eta × Fin 3, kc m b *
        (-IP Ψ (dirD b (dirD b (dirD a (dirD a X.χ)))) u -
          2 * IP Ψ (dirD b (dirD a (dirD a X.χ))) (g b) +
          IP Ψ (dirD a (dirD b (dirD b (dirD a X.χ)))) u +
          IP Ψ (dirD b (dirD b (dirD a X.χ))) (g a) +
          2 * IP Ψ (dirD a (dirD b (dirD a X.χ))) (g b) +
          2 * IP Ψ (dirD b (dirD a X.χ)) (g2 b a)) =
      -(∑ b : Fin eta × Fin 3, kc m b * (IP Ψ (dirD b (dirD b (dirD a (dirD a X.χ)))) u +
          2 * IP Ψ (dirD b (dirD a (dirD a X.χ))) (g b))) -
        ∑ b : Fin eta × Fin 3, kc m b * (IP (dirD a Ψ) (dirD b (dirD b (dirD a X.χ))) u +
          2 * IP (dirD a Ψ) (dirD b (dirD a X.χ)) (g b)) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [h5 b, h6 b]
    ring
  rw [hsum]
  linear_combination h1 - h2 - h3 - h4

end Terms

/-! ## The commutator -/

section Commutator

variable {L : ℝ} (hL : 0 < L) {m : Fin eta → ℝ} (X : DomCutoff eta L m) (q : Fin eta → ℝ)
include hL

/-- The non-singular part of the `∂_aχ g_a` term. -/
noncomputable def termB (X : DomCutoff eta L m) (Ψ : Rcfg eta → ℂ) (u : FreeL2 eta)
    (g g' : Fin eta × Fin 3 → FreeL2 eta) (g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta)
    (a : Fin eta × Fin 3) : ℂ :=
  IP Ψ (dirD a X.χ) (g' a) +
    ∑ b : Fin eta × Fin 3, kc m b *
      (-IP Ψ (dirD b (dirD b (dirD a (dirD a X.χ)))) u -
        2 * IP Ψ (dirD b (dirD a (dirD a X.χ))) (g b) +
        IP Ψ (dirD a (dirD b (dirD b (dirD a X.χ)))) u +
        IP Ψ (dirD b (dirD b (dirD a X.χ))) (g a) +
        2 * IP Ψ (dirD a (dirD b (dirD a X.χ))) (g b) +
        2 * IP Ψ (dirD b (dirD a X.χ)) (g2 b a))

/-- The `∂_a²χ u` term without its potential part. -/
noncomputable def termA (X : DomCutoff eta L m) (Ψ : Rcfg eta → ℂ) (u h : FreeL2 eta)
    (g : Fin eta × Fin 3 → FreeL2 eta) (a : Fin eta × Fin 3) : ℂ :=
  IP Ψ (dirD a (dirD a X.χ)) h +
    ∑ b : Fin eta × Fin 3, kc m b * (IP Ψ (dirD b (dirD b (dirD a (dirD a X.χ)))) u +
      2 * IP Ψ (dirD b (dirD a (dirD a X.χ))) (g b))

/-- **The kinetic energy of the commutator** `[K, χ] u`, tested with a smooth `Ψ`:
`Σ_a c_a (IP (KΨ) ∂_a²χ u + 2 IP (KΨ) ∂_aχ g_a) = Σ_a c_a (A_a - IP Ψ ∂_a²χ (V u))
  + Σ_a 2c_a (B_a - IP Ψ ∂_aχ (V g_a)) - Σ_{i<j} IP Ψ β_{ij} (u/|x_i - x_j|)`. -/
theorem freeId_comm {u h : FreeL2 eta} {g g' : Fin eta × Fin 3 → FreeL2 eta}
    {g2 : Fin eta × Fin 3 → Fin eta × Fin 3 → FreeL2 eta}
    {Y : FiniteElectronPair eta → FreeL2 eta} {Z : FiniteElectronPair eta → Fin eta × Fin 3 →
      FreeL2 eta}
    (hK : HasFreeWeakKinetic m u (h - pairL2 q Y)) (hg : HasWeakGrad u g)
    (hg' : HasWeakGrad h g') (hg2 : ∀ b, HasWeakGrad (g b) (g2 b))
    (hY : ∀ p, ∀ᵐ r, Y p r = (pinv p r : ℂ) * u r)
    (hZ : ∀ p a, ∀ᵐ r, Z p a r = (pinv p r : ℂ) * g a r) {Ψ : Rcfg eta → ℂ}
    (hΨ : ContDiff ℝ 3 Ψ) :
    ∑ a : Fin eta × Fin 3, kc m a * (IP (freeKinetic m Ψ) (dirD a (dirD a X.χ)) u +
        2 * IP (freeKinetic m Ψ) (dirD a X.χ) (g a)) =
      ∑ a : Fin eta × Fin 3, kc m a * (termA X Ψ u h g a -
          IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y)) +
        ∑ a : Fin eta × Fin 3, 2 * kc m a * (termB X Ψ u g g' g2 a -
          IP Ψ (dirD a X.χ) (pairL2 q fun p => Z p a)) -
        ∑ p : FiniteElectronPair eta, ∫ r, conj (Ψ r) * ((commBeta m q X.χ p r : ℂ) * Y p r) := by
  have hS := singular_identity hL X q hg hY hZ (hΨ.of_le (by norm_num))
  have hA : ∀ a, IP (freeKinetic m Ψ) (dirD a (dirD a X.χ)) u =
      termA X Ψ u h g a - IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) := by
    intro a
    rw [freeId_A hL X hK hg (hΨ.of_le (by norm_num)) a]
    unfold termA
    ring
  have hB : ∀ a, IP (freeKinetic m Ψ) (dirD a X.χ) (g a) =
      termB X Ψ u g g' g2 a +
        (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) + IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y)) := by
    intro a
    rw [freeId_B hL X hK hg hg' hg2 hΨ a]
    unfold termB
    ring
  simp_rw [hA, hB]
  -- the singular identity in `IP` notation
  have hS' : ∑ a : Fin eta × Fin 3, 2 * kc m a *
      (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) + IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y)) =
      -(∑ a : Fin eta × Fin 3, 2 * kc m a * IP Ψ (dirD a X.χ) (pairL2 q fun p => Z p a)) -
        ∑ p : FiniteElectronPair eta,
          ∫ r, conj (Ψ r) * ((commBeta m q X.χ p r : ℂ) * Y p r) := by
    simp_rw [two_kc]
    exact hS
  have e1 : ∑ a : Fin eta × Fin 3, kc m a * (termA X Ψ u h g a -
        IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) + 2 * (termB X Ψ u g g' g2 a +
          (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) + IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y)))) =
      ∑ a : Fin eta × Fin 3, kc m a * (termA X Ψ u h g a -
          IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y)) +
        ∑ a : Fin eta × Fin 3, 2 * kc m a * termB X Ψ u g g' g2 a +
        ∑ a : Fin eta × Fin 3, 2 * kc m a *
          (IP Ψ (dirD a (dirD a X.χ)) (pairL2 q Y) + IP (dirD a Ψ) (dirD a X.χ) (pairL2 q Y)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e2 : ∑ a : Fin eta × Fin 3, 2 * kc m a * (termB X Ψ u g g' g2 a -
        IP Ψ (dirD a X.χ) (pairL2 q fun p => Z p a)) =
      ∑ a : Fin eta × Fin 3, 2 * kc m a * termB X Ψ u g g' g2 a -
        ∑ a : Fin eta × Fin 3, 2 * kc m a * IP Ψ (dirD a X.χ) (pairL2 q fun p => Z p a) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e1, e2, hS']
  ring

end Commutator

end FreeBoundary
