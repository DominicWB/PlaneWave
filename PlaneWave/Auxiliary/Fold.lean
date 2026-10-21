import PlaneWave.Certificate

/-!
# Auxiliary claims, part 4: the fold identity for a general trigonometric polynomial (`lem:fold`)

On a grid of `n'` points per direction (`x_j = j L/n'`), with the plane waves
`φ_p = Ω^{-1/2} e^{-i k_p · r}` (eq:pw) restricted to the grid, the phase of a mode is
`k_ν · x_j = 2π ν · j/n'`, so the cell size drops out and we work on the unit torus with
`x_j = j/n'` and the phase `e(θ) = exp(2πiθ)`. For a trigonometric polynomial
`f(x) = Σ_{ν ∈ S} f̂(ν) e(ν · x)` (any finite Fourier support `S`, the multiplier convention of
eq:fourier-sign) and the orthonormal grid basis `φ_p(x_j) = n'^{-3/2} e(-p · x_j)`:

* `sum_ephase_grid`: `Σ_j e(k · x_j) = n'³ 1[k ∈ n' ℤ³]`;
* **`fold_single`**: `⟨φ_p, Diag[f] φ_q⟩ = Σ_{ν ∈ S, ν ≡ q - p (mod n')} f̂(ν)`, i.e. the sum of
  `f̂(d + n' ℓ)` over the fold indices `ℓ` (`d = q - p`; `exists_fold_index`);
* **`fold_pair`** (eq:fold): `⟨p_a, p_b | Diag[f(x_a - x_b)] | q_a, q_b⟩ =
  Σ_{ν ∈ S, ν ≡ d_a, -ν ≡ d_b} f̂(ν)`, the sum over `d_a + n' ℓ_a = -(d_b + n' ℓ_b)`;
* `fold_pair_eq_zero`: the element vanishes unless `p_a + p_b ≡ q_a + q_b (mod n')`;
* `fold_pair_galerkin`: the element is the Galerkin term `f̂(d_a) 1[d_a = -d_b]`
  (`ℓ_a = ℓ_b = 0`) plus the wrap contribution, the sum over all other fold terms;
* `tpoly_nuc`, `norm_nuc_coeff_le` (clamped nuclei at arbitrary positions `R_ℓ`):
  `-Σ_ℓ ζ_ℓ w(x - R_ℓ)` is the trigonometric polynomial with coefficients
  `-Σ_ℓ ζ_ℓ ŵ(ν) e(-ν · R_ℓ)`, of modulus at most `(Σ_ℓ |ζ_ℓ|) |ŵ(ν)|`.
-/

set_option autoImplicit false

open scoped ComplexConjugate BigOperators
open Finset

namespace GridFold

/-! ## Phases -/

/-- The phase `e(θ) = exp(2πiθ)`. -/
noncomputable def ephase (θ : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * θ)

lemma ephase_add (a b : ℝ) : ephase (a + b) = ephase a * ephase b := by
  unfold ephase; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma conj_ephase (θ : ℝ) : conj (ephase θ) = ephase (-θ) := by
  unfold ephase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast; ring

lemma norm_ephase (θ : ℝ) : ‖ephase θ‖ = 1 := by
  unfold ephase
  rw [show (2 * Real.pi * Complex.I * θ : ℂ) = ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ephase_sum (f : Fin 3 → ℝ) : ephase (∑ c, f c) = ∏ c, ephase (f c) := by
  unfold ephase
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

/-- `Σ_{j < n'} e(k j/n') = n' 1[n' ∣ k]`. -/
lemma sum_ephase_fin {n' : ℕ} (hn : 0 < n') (k : ℤ) :
    ∑ j : Fin n', ephase ((k : ℝ) * ((j : ℕ) : ℝ) / n') = if (n' : ℤ) ∣ k then (n' : ℂ) else 0 := by
  have hn0 : (n' : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpow : ∀ j : ℕ, ephase ((k : ℝ) * (j : ℝ) / n') = ephase ((k : ℝ) / n') ^ j := by
    intro j
    rw [ephase, ephase, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [Fin.sum_univ_eq_sum_range (fun j => ephase ((k : ℝ) * (j : ℝ) / n')) n']
  simp_rw [hpow]
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  split_ifs with hdiv
  · obtain ⟨m, hm⟩ := hdiv
    have h1 : ephase ((k : ℝ) / n') = 1 := by
      rw [ephase, hm]
      have e : (2 * Real.pi * Complex.I * ((((n' * m : ℤ) : ℝ) / n' : ℝ) : ℂ)) =
          (m : ℂ) * (2 * Real.pi * Complex.I) := by
        have : (((n' * m : ℤ) : ℝ) / n' : ℝ) = (m : ℝ) := by push_cast; field_simp
        rw [this]; push_cast; ring
      rw [e]; exact Complex.exp_int_mul_two_pi_mul_I m
    rw [h1]; simp
  · have h1 : ephase ((k : ℝ) / n') ≠ 1 := by
      intro h
      rw [ephase, Complex.exp_eq_one_iff] at h
      obtain ⟨m, hm⟩ := h
      apply hdiv
      have h2 : (((k : ℝ) / n' : ℝ) : ℂ) = (m : ℂ) := by
        apply mul_left_cancel₀ h2pi
        rw [hm]; ring
      have h3 : (k : ℝ) / n' = m := by exact_mod_cast h2
      have h4 : (k : ℝ) = m * n' := by
        rw [div_eq_iff hn0] at h3; exact h3
      refine ⟨m, ?_⟩
      have : (k : ℝ) = ((n' * m : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have h2 : ephase ((k : ℝ) / n') ^ n' = 1 := by
      rw [← hpow n', show (k : ℝ) * (n' : ℝ) / n' = (k : ℝ) by field_simp, ephase]
      have : (2 * Real.pi * Complex.I * (((k : ℝ)) : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [this]; exact Complex.exp_int_mul_two_pi_mul_I k
    rw [geom_sum_eq h1, h2, sub_self, zero_div]

/-! ## The grid -/

/-- `k · x` for an integer vector `k`. -/
def dot3r (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) : ℝ := ∑ c, (k c : ℝ) * x c

lemma dot3r_add (k l : Fin 3 → ℤ) (x : Fin 3 → ℝ) : dot3r (k + l) x = dot3r k x + dot3r l x := by
  unfold dot3r; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_; simp only [Pi.add_apply]; push_cast; ring

lemma dot3r_neg (k : Fin 3 → ℤ) (x : Fin 3 → ℝ) : dot3r (-k) x = -dot3r k x := by
  unfold dot3r; rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_; simp only [Pi.neg_apply]; push_cast; ring

lemma dot3r_sub (k l : Fin 3 → ℤ) (x : Fin 3 → ℝ) : dot3r (k - l) x = dot3r k x - dot3r l x := by
  rw [sub_eq_add_neg, dot3r_add, dot3r_neg, ← sub_eq_add_neg]

lemma dot3r_sub_right (k : Fin 3 → ℤ) (x y : Fin 3 → ℝ) :
    dot3r k (x - y) = dot3r k x - dot3r k y := by
  unfold dot3r; rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_; simp only [Pi.sub_apply]; ring

/-- The grid points `x_j = j/n'` of the unit torus. -/
noncomputable def gpt (n' : ℕ) (j : Fin 3 → Fin n') : Fin 3 → ℝ := fun c => ((j c : ℕ) : ℝ) / n'

/-- **Orthogonality of the grid characters**: `Σ_j e(k · x_j) = n'³ 1[k ∈ n' ℤ³]`. -/
theorem sum_ephase_grid {n' : ℕ} (hn : 0 < n') (k : Fin 3 → ℤ) :
    ∑ j : Fin 3 → Fin n', ephase (dot3r k (gpt n' j)) =
      if ∀ c, (n' : ℤ) ∣ k c then (n' : ℂ) ^ 3 else 0 := by
  classical
  have e : ∀ j : Fin 3 → Fin n', ephase (dot3r k (gpt n' j)) =
      ∏ c, ephase ((k c : ℝ) * ((j c : ℕ) : ℝ) / n') := by
    intro j
    rw [dot3r, ephase_sum]
    refine Finset.prod_congr rfl fun c _ => ?_
    congr 1; unfold gpt; ring
  simp_rw [e]
  rw [← Fintype.prod_sum (fun c (i : Fin n') => ephase ((k c : ℝ) * ((i : ℕ) : ℝ) / n'))]
  simp_rw [sum_ephase_fin hn]
  split_ifs with h
  · rw [Finset.prod_congr rfl fun c _ => if_pos (h c)]
    simp
  · push Not at h
    obtain ⟨c, hc⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ c) (if_neg hc)

/-- The averaged character: `n'⁻³ Σ_j e(k · x_j) = 1[k ∈ n' ℤ³]`. -/
lemma sum_avg_ephase {n' : ℕ} (hn : 0 < n') (k : Fin 3 → ℤ) :
    ∑ j : Fin 3 → Fin n', (1 / (n' : ℂ) ^ 3) * ephase (dot3r k (gpt n' j)) =
      if ∀ c, (n' : ℤ) ∣ k c then 1 else 0 := by
  rw [← Finset.mul_sum, sum_ephase_grid hn]
  have : (n' : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  split_ifs
  · field_simp
  · simp

/-- The orthonormal grid basis `φ_p(x_j) = n'^{-3/2} e(-p · x_j)` (the plane wave of eq:pw on the
grid). -/
noncomputable def gbasis (n' : ℕ) (p : Fin 3 → ℤ) (j : Fin 3 → Fin n') : ℂ :=
  (((Real.sqrt ((n' : ℝ) ^ 3))⁻¹ : ℝ) : ℂ) * ephase (-dot3r p (gpt n' j))

lemma conj_gbasis_mul {n' : ℕ} (p q : Fin 3 → ℤ) (j : Fin 3 → Fin n') :
    conj (gbasis n' p j) * gbasis n' q j =
      (1 / (n' : ℂ) ^ 3) * ephase (dot3r (p - q) (gpt n' j)) := by
  unfold gbasis
  rw [map_mul, Complex.conj_ofReal, conj_ephase, neg_neg]
  have hs : ((Real.sqrt ((n' : ℝ) ^ 3))⁻¹) ^ 2 = 1 / (n' : ℝ) ^ 3 := by
    rw [inv_pow, Real.sq_sqrt (by positivity), one_div]
  have e : (((Real.sqrt ((n' : ℝ) ^ 3))⁻¹ : ℝ) : ℂ) * ephase (dot3r p (gpt n' j)) *
      ((((Real.sqrt ((n' : ℝ) ^ 3))⁻¹ : ℝ) : ℂ) * ephase (-dot3r q (gpt n' j))) =
      ((((Real.sqrt ((n' : ℝ) ^ 3))⁻¹) ^ 2 : ℝ) : ℂ) *
        (ephase (dot3r p (gpt n' j)) * ephase (-dot3r q (gpt n' j))) := by
    push_cast; ring
  rw [e, hs, ← ephase_add, dot3r_sub, ← sub_eq_add_neg]
  push_cast; ring

/-- A trigonometric polynomial `f(x) = Σ_{ν ∈ S} f̂(ν) e(ν · x)` on the unit torus. -/
noncomputable def tpoly (S : Finset (Fin 3 → ℤ)) (fh : (Fin 3 → ℤ) → ℂ) (x : Fin 3 → ℝ) : ℂ :=
  ∑ ν ∈ S, fh ν * ephase (dot3r ν x)

/-- The fold indices: `ν ≡ d (mod n')` componentwise iff `ν = d + n' ℓ` for an integer triple `ℓ`. -/
lemma exists_fold_index (n' : ℕ) (ν d : Fin 3 → ℤ) :
    (∀ c, (n' : ℤ) ∣ ν c - d c) ↔ ∃ ℓ : Fin 3 → ℤ, ν = d + (n' : ℤ) • ℓ := by
  constructor
  · intro h
    choose ℓ hℓ using h
    refine ⟨ℓ, funext fun c => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hℓ c]
  · rintro ⟨ℓ, rfl⟩ c
    exact ⟨ℓ c, by simp⟩

/-! ## The fold identities -/

/-- **`lem:fold`, single-register version**: `⟨φ_p, Diag[f] φ_q⟩ = Σ_{ν ∈ S, ν ≡ q - p} f̂(ν)`. -/
theorem fold_single {n' : ℕ} (hn : 0 < n') (S : Finset (Fin 3 → ℤ)) (fh : (Fin 3 → ℤ) → ℂ)
    (p q : Fin 3 → ℤ) :
    ∑ j : Fin 3 → Fin n', conj (gbasis n' p j) * tpoly S fh (gpt n' j) * gbasis n' q j =
      ∑ ν ∈ S.filter (fun ν => ∀ c, (n' : ℤ) ∣ ν c - (q c - p c)), fh ν := by
  classical
  have e : ∀ j, conj (gbasis n' p j) * tpoly S fh (gpt n' j) * gbasis n' q j =
      ∑ ν ∈ S, fh ν * ((1 / (n' : ℂ) ^ 3) * ephase (dot3r (p - q + ν) (gpt n' j))) := by
    intro j
    rw [mul_right_comm, conj_gbasis_mul, tpoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [dot3r_add, ephase_add]
    ring
  simp_rw [e]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_ephase_grid hn, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hc : ∀ c, (p - q + ν) c = ν c - (q c - p c) := fun c => by
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  simp only [hc]
  have : (n' : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  split_ifs
  · field_simp
  · ring

/-- The summand of the pair element. -/
lemma pair_term (ga gb ga' gb' A B C D fν : ℂ) (h1 : conj ga * ga' = C) (h2 : conj gb * gb' = D) :
    conj (ga * gb) * (fν * (A * B)) * (ga' * gb') = fν * (C * A) * (D * B) := by
  rw [map_mul, ← h1, ← h2]; ring

/-- **`lem:fold`, pair version (eq:fold)**: in the momentum basis, with `d_a = q_a - p_a`,
`d_b = q_b - p_b`, `⟨p_a, p_b | Diag[f(x_a - x_b)] | q_a, q_b⟩ = Σ_{ν ∈ S, ν ≡ d_a, -ν ≡ d_b} f̂(ν)`,
the sum over the fold indices with `d_a + n' ℓ_a = -(d_b + n' ℓ_b) = ν`. -/
theorem fold_pair {n' : ℕ} (hn : 0 < n') (S : Finset (Fin 3 → ℤ)) (fh : (Fin 3 → ℤ) → ℂ)
    (pa pb qa qb : Fin 3 → ℤ) :
    ∑ ja : Fin 3 → Fin n', ∑ jb : Fin 3 → Fin n',
        conj (gbasis n' pa ja * gbasis n' pb jb) * tpoly S fh (gpt n' ja - gpt n' jb) *
          (gbasis n' qa ja * gbasis n' qb jb) =
      ∑ ν ∈ S.filter (fun ν => (∀ c, (n' : ℤ) ∣ ν c - (qa c - pa c)) ∧
        ∀ c, (n' : ℤ) ∣ -ν c - (qb c - pb c)), fh ν := by
  classical
  have e : ∀ ja jb, conj (gbasis n' pa ja * gbasis n' pb jb) *
      tpoly S fh (gpt n' ja - gpt n' jb) * (gbasis n' qa ja * gbasis n' qb jb) =
      ∑ ν ∈ S, fh ν * ((1 / (n' : ℂ) ^ 3) * ephase (dot3r (pa - qa + ν) (gpt n' ja))) *
        ((1 / (n' : ℂ) ^ 3) * ephase (dot3r (pb - qb + -ν) (gpt n' jb))) := by
    intro ja jb
    rw [tpoly, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [dot3r_sub_right, sub_eq_add_neg, ephase_add,
      pair_term _ _ _ _ _ _ _ _ _ (conj_gbasis_mul pa qa ja) (conj_gbasis_mul pb qb jb),
      dot3r_add, dot3r_add, dot3r_neg, ephase_add, ephase_add]
    ring
  simp_rw [e]
  have hswap : ∀ ja : Fin 3 → Fin n', ∑ jb : Fin 3 → Fin n', ∑ ν ∈ S,
      fh ν * ((1 / (n' : ℂ) ^ 3) * ephase (dot3r (pa - qa + ν) (gpt n' ja))) *
        ((1 / (n' : ℂ) ^ 3) * ephase (dot3r (pb - qb + -ν) (gpt n' jb))) =
      ∑ ν ∈ S, fh ν * ((1 / (n' : ℂ) ^ 3) * ephase (dot3r (pa - qa + ν) (gpt n' ja))) *
        ∑ jb : Fin 3 → Fin n', ((1 / (n' : ℂ) ^ 3) * ephase (dot3r (pb - qb + -ν) (gpt n' jb))) := by
    intro ja
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.mul_sum]
  simp_rw [hswap, sum_avg_ephase hn]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, sum_ephase_grid hn, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have hc1 : ∀ c, (pa - qa + ν) c = ν c - (qa c - pa c) := fun c => by
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  have hc2 : ∀ c, (pb - qb + -ν) c = -ν c - (qb c - pb c) := fun c => by
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]; ring
  simp only [hc1, hc2]
  have : (n' : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [ite_and]
  by_cases hA : ∀ c, (n' : ℤ) ∣ ν c - (qa c - pa c) <;>
    by_cases hB : ∀ c, (n' : ℤ) ∣ -ν c - (qb c - pb c)
  · simp only [if_pos hA, if_pos hB]; field_simp
  · simp only [if_pos hA, if_neg hB]; ring
  · simp only [if_neg hA, if_pos hB]; ring
  · simp only [if_neg hA, if_neg hB]; ring

/-- **Total momentum is conserved modulo `n'`**: the pair element vanishes unless
`p_a + p_b ≡ q_a + q_b (mod n')`. -/
theorem fold_pair_eq_zero {n' : ℕ} (hn : 0 < n') (S : Finset (Fin 3 → ℤ))
    (fh : (Fin 3 → ℤ) → ℂ) (pa pb qa qb : Fin 3 → ℤ)
    (h : ¬ ∀ c, (n' : ℤ) ∣ pa c + pb c - (qa c + qb c)) :
    ∑ ja : Fin 3 → Fin n', ∑ jb : Fin 3 → Fin n',
        conj (gbasis n' pa ja * gbasis n' pb jb) * tpoly S fh (gpt n' ja - gpt n' jb) *
          (gbasis n' qa ja * gbasis n' qb jb) = 0 := by
  rw [fold_pair hn]
  refine Finset.sum_eq_zero fun ν hν => absurd ?_ h
  obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hν
  intro c
  have := dvd_add (h1 c) (h2 c)
  have e : ν c - (qa c - pa c) + (-ν c - (qb c - pb c)) = pa c + pb c - (qa c + qb c) := by ring
  rwa [e] at this

/-- **The Galerkin part and the wrap**: the pair element is the Galerkin term
`f̂(d_a) 1[d_a = -d_b]` (the fold indices `ℓ_a = ℓ_b = 0`) plus the wrap contribution, the sum of
`f̂(ν)` over every other fold term (a term with `ℓ_a = 0` but `ℓ_b ≠ 0` belongs to the wrap). -/
theorem fold_pair_galerkin {n' : ℕ} (hn : 0 < n') (S : Finset (Fin 3 → ℤ))
    (fh : (Fin 3 → ℤ) → ℂ) (pa pb qa qb : Fin 3 → ℤ) :
    ∑ ja : Fin 3 → Fin n', ∑ jb : Fin 3 → Fin n',
        conj (gbasis n' pa ja * gbasis n' pb jb) * tpoly S fh (gpt n' ja - gpt n' jb) *
          (gbasis n' qa ja * gbasis n' qb jb) =
      (if qa - pa = -(qb - pb) ∧ qa - pa ∈ S then fh (qa - pa) else 0) +
        ∑ ν ∈ (S.filter (fun ν => (∀ c, (n' : ℤ) ∣ ν c - (qa c - pa c)) ∧
          ∀ c, (n' : ℤ) ∣ -ν c - (qb c - pb c))).filter
            (fun ν => ¬ (ν = qa - pa ∧ -ν = qb - pb)), fh ν := by
  classical
  rw [fold_pair hn, ← Finset.sum_filter_add_sum_filter_not _
    (fun ν => ν = qa - pa ∧ -ν = qb - pb)]
  congr 1
  split_ifs with hg
  · obtain ⟨hd, hS⟩ := hg
    have hset : (S.filter (fun ν => (∀ c, (n' : ℤ) ∣ ν c - (qa c - pa c)) ∧
        ∀ c, (n' : ℤ) ∣ -ν c - (qb c - pb c))).filter (fun ν => ν = qa - pa ∧ -ν = qb - pb) =
        {qa - pa} := by
      ext ν
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h, -⟩; exact h
      · rintro rfl
        have hneg : -(qa - pa) = qb - pb := by rw [hd, neg_neg]
        refine ⟨⟨hS, fun c => by simp, fun c => ?_⟩, rfl, hneg⟩
        have h' := congrFun hneg c
        have : -(qa - pa) c - (qb c - pb c) = 0 := by
          simp only [Pi.neg_apply, Pi.sub_apply] at h' ⊢; linarith
        rw [this]; exact dvd_zero _
    rw [hset, Finset.sum_singleton]
  · refine Finset.sum_eq_zero fun ν hν => absurd ?_ hg
    obtain ⟨⟨hνS, -⟩, h1, h2⟩ := Finset.mem_filter.mp hν |>.imp_left Finset.mem_filter.mp
    refine ⟨?_, h1 ▸ hνS⟩
    rw [← h1, ← h2, neg_neg]

/-! ## Clamped nuclei at arbitrary positions -/

/-- A translate of a trigonometric polynomial: `f(x - R) = Σ_ν (f̂(ν) e(-ν · R)) e(ν · x)`. -/
lemma tpoly_translate (S : Finset (Fin 3 → ℤ)) (fh : (Fin 3 → ℤ) → ℂ) (x R : Fin 3 → ℝ) :
    tpoly S fh (x - R) = tpoly S (fun ν => fh ν * ephase (-dot3r ν R)) x := by
  unfold tpoly
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [dot3r_sub_right, sub_eq_add_neg, ephase_add]
  ring

/-- **The clamped-nucleus term** `-Σ_ℓ ζ_ℓ w(x - R_ℓ)` (nuclei at arbitrary positions `R_ℓ`) is the
trigonometric polynomial with the coefficients `-Σ_ℓ ζ_ℓ ŵ(ν) e(-ν · R_ℓ)` and the support of `w`,
so `fold_single` applies to it. -/
theorem tpoly_nuc (S : Finset (Fin 3 → ℤ)) (wh : (Fin 3 → ℤ) → ℂ) {ι : Type*} (T : Finset ι)
    (ζ : ι → ℝ) (R : ι → Fin 3 → ℝ) (x : Fin 3 → ℝ) :
    -∑ l ∈ T, (ζ l : ℂ) * tpoly S wh (x - R l) =
      tpoly S (fun ν => -∑ l ∈ T, (ζ l : ℂ) * wh ν * ephase (-dot3r ν (R l))) x := by
  have h : ∑ l ∈ T, (ζ l : ℂ) * tpoly S wh (x - R l) =
      tpoly S (fun ν => ∑ l ∈ T, (ζ l : ℂ) * wh ν * ephase (-dot3r ν (R l))) x := by
    simp_rw [tpoly_translate]
    unfold tpoly
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [h]
  unfold tpoly
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- `|-Σ_ℓ ζ_ℓ ŵ(ν) e(-ν · R_ℓ)| ≤ (Σ_ℓ |ζ_ℓ|) |ŵ(ν)|`. -/
theorem norm_nuc_coeff_le (wh : (Fin 3 → ℤ) → ℂ) {ι : Type*} (T : Finset ι) (ζ : ι → ℝ)
    (R : ι → Fin 3 → ℝ) (ν : Fin 3 → ℤ) :
    ‖-∑ l ∈ T, (ζ l : ℂ) * wh ν * ephase (-dot3r ν (R l))‖ ≤ (∑ l ∈ T, |ζ l|) * ‖wh ν‖ := by
  rw [norm_neg, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [norm_mul, norm_mul, norm_ephase, mul_one, Complex.norm_real, Real.norm_eq_abs]

end GridFold
