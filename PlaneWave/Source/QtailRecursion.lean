import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Flux/source build, block 1: the dyadic recursion of `lem:qtail`

The analytic core of `lem:qtail` (eq:qtail-rec, eq:qtail-iter) is a statement about a tail
function `h(λ) = ‖1{‖k_a‖ > λ} q̂‖` that satisfies, above a threshold `λ₁ ≥ 8c`,

  `h(λ) ≤ (c/λ) h(λ/2) + F(λ)`,  `F(λ) = (c₂/λ²)(λ^{-1/2} W + G)`,

and is bounded by `M = ‖q‖` everywhere.  `qtail_recursion` shows `h(λ) ≤ 4 F(λ) + 2c² M/λ²` for
`λ > 2λ₁`.  The manuscript iterates the recursion down to the threshold and sums a geometric series
(every factor `c/(λ/2^ℓ) ≤ 1/8`, ratio `2^{-1/2}`); here the same estimate is proved by induction
on the dyadic level with the invariant `h(λ) ≤ 4F(λ) + 2c²M/λ²`.  The manuscript's two-step margin
appears as the base case `2λ₁ < λ ≤ 4λ₁`, where the recursion is used twice before the trivial
bound `h ≤ M`; with one step the last term would be `(c/λ) M`, one power short.  The term
`2c²M/λ²` is the manuscript's `m_a ‖q‖` term (`c = C_rec m_a`).

Mathlib only.
-/

set_option autoImplicit false

namespace FSQtail

/-- The source term of the recursion, `F(λ) = (c₂/λ²)(λ^{-1/2} W + G)`. -/
noncomputable def F (c₂ W G l : ℝ) : ℝ := c₂ / l ^ 2 * (l ^ (-(1 / 2 : ℝ)) * W + G)

lemma F_nonneg {c₂ W G l : ℝ} (hc₂ : 0 ≤ c₂) (hW : 0 ≤ W) (hG : 0 ≤ G) (hl : 0 < l) :
    0 ≤ F c₂ W G l := by
  unfold F
  have : 0 ≤ l ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hl.le _
  positivity

lemma rpow_neg_half_half_le {l : ℝ} (hl : 0 < l) :
    (l / 2) ^ (-(1 / 2 : ℝ)) ≤ 2 * l ^ (-(1 / 2 : ℝ)) := by
  rw [Real.div_rpow hl.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    div_inv_eq_mul, mul_comm]
  have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
    simpa using this
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hl.le _)

/-- Halving the scale costs at most a factor `8` (in fact `2^{5/2}`). -/
lemma F_half_le {c₂ W G l : ℝ} (hc₂ : 0 ≤ c₂) (hW : 0 ≤ W) (hG : 0 ≤ G) (hl : 0 < l) :
    F c₂ W G (l / 2) ≤ 8 * F c₂ W G l := by
  unfold F
  have h1 := rpow_neg_half_half_le hl
  have hl2 : (l / 2) ^ 2 = l ^ 2 / 4 := by ring
  rw [hl2]
  have hp : 0 ≤ l ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hl.le _
  have hlsq : 0 < l ^ 2 := by positivity
  have key : (l / 2) ^ (-(1 / 2 : ℝ)) * W + G ≤ 2 * (l ^ (-(1 / 2 : ℝ)) * W + G) := by
    nlinarith [mul_le_mul_of_nonneg_right h1 hW]
  calc c₂ / (l ^ 2 / 4) * ((l / 2) ^ (-(1 / 2 : ℝ)) * W + G)
      = 4 * (c₂ / l ^ 2) * ((l / 2) ^ (-(1 / 2 : ℝ)) * W + G) := by field_simp
    _ ≤ 4 * (c₂ / l ^ 2) * (2 * (l ^ (-(1 / 2 : ℝ)) * W + G)) := by
        gcongr
    _ = 8 * (c₂ / l ^ 2 * (l ^ (-(1 / 2 : ℝ)) * W + G)) := by ring

section Recursion

variable {h : ℝ → ℝ} {c c₂ W G M l₁ : ℝ}

/-- The base case `2λ₁ < λ ≤ 4λ₁`: two applications of the recursion and the trivial bound. -/
lemma qtail_base (hc : 0 ≤ c) (hc₂ : 0 ≤ c₂) (hW : 0 ≤ W) (hG : 0 ≤ G) (hl₁ : 0 < l₁)
    (hcl : 8 * c ≤ l₁) (hle : ∀ l, h l ≤ M)
    (hrec : ∀ l, l₁ < l → h l ≤ c / l * h (l / 2) + F c₂ W G l)
    {l : ℝ} (hl : 2 * l₁ < l) :
    h l ≤ 3 / 2 * F c₂ W G l + 2 * c ^ 2 * M / l ^ 2 := by
  have hlpos : 0 < l := by linarith
  have hcl' : c / l ≤ 1 / 16 := by
    rw [div_le_iff₀ hlpos]; linarith
  have hcl0 : 0 ≤ c / l := div_nonneg hc hlpos.le
  have h1 := hrec l (by linarith)
  have h2 := hrec (l / 2) (by linarith)
  have h3 := hle (l / 2 / 2)
  have hc2 : c / (l / 2) = 2 * (c / l) := by field_simp
  have hF := F_half_le hc₂ hW hG hlpos
  have hF0 := F_nonneg hc₂ hW hG hlpos
  have hF20 := F_nonneg hc₂ hW hG (by positivity : 0 < l / 2)
  -- h(λ/2) ≤ (2c/λ) M + F(λ/2)
  have h2' : h (l / 2) ≤ 2 * (c / l) * M + F c₂ W G (l / 2) := by
    rw [hc2] at h2
    have : 2 * (c / l) * h (l / 2 / 2) ≤ 2 * (c / l) * M :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  have h4 : c / l * h (l / 2) ≤ c / l * (2 * (c / l) * M + F c₂ W G (l / 2)) :=
    mul_le_mul_of_nonneg_left h2' hcl0
  have h5 : c / l * F c₂ W G (l / 2) ≤ 1 / 2 * F c₂ W G l := by
    calc c / l * F c₂ W G (l / 2) ≤ 1 / 16 * (8 * F c₂ W G l) :=
          mul_le_mul hcl' hF hF20 (by norm_num)
      _ = 1 / 2 * F c₂ W G l := by ring
  have h6 : c / l * (2 * (c / l) * M) = 2 * c ^ 2 * M / l ^ 2 := by
    field_simp
  nlinarith [h1, h4, h5, h6]

/-- **The `lem:qtail` recursion** (eq:qtail-rec ⟹ eq:qtail-iter ⟹ eq:qtail).  If the tail
function satisfies `h(λ) ≤ (c/λ) h(λ/2) + F(λ)` above `λ₁ ≥ 8c` and `h ≤ M` everywhere, then
`h(λ) ≤ 4 F(λ) + 2c²M/λ²` for every `λ > 2λ₁`. -/
theorem qtail_recursion (hc : 0 ≤ c) (hc₂ : 0 ≤ c₂) (hW : 0 ≤ W) (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hl₁ : 0 < l₁) (hcl : 8 * c ≤ l₁) (hle : ∀ l, h l ≤ M)
    (hrec : ∀ l, l₁ < l → h l ≤ c / l * h (l / 2) + F c₂ W G l) :
    ∀ l, 2 * l₁ < l → h l ≤ 4 * F c₂ W G l + 2 * c ^ 2 * M / l ^ 2 := by
  -- induction on the dyadic level `λ ≤ 2^n · 4λ₁`
  have hstep : ∀ n : ℕ, ∀ l, 2 * l₁ < l → l ≤ 2 ^ n * (4 * l₁) →
      h l ≤ 4 * F c₂ W G l + 2 * c ^ 2 * M / l ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro l hl _
      have := qtail_base hc hc₂ hW hG hl₁ hcl hle hrec hl
      have hF0 := F_nonneg hc₂ hW hG (by linarith : (0 : ℝ) < l)
      linarith
    | succ n ih =>
      intro l hl hln
      by_cases hl4 : l ≤ 4 * l₁
      · have := qtail_base hc hc₂ hW hG hl₁ hcl hle hrec hl
        have hF0 := F_nonneg hc₂ hW hG (by linarith : (0 : ℝ) < l)
        linarith
      · push Not at hl4
        have hlpos : 0 < l := by linarith
        have hcl' : c / l ≤ 1 / 16 := by
          rw [div_le_iff₀ hlpos]; linarith
        have hcl0 : 0 ≤ c / l := div_nonneg hc hlpos.le
        have hIH := ih (l / 2) (by linarith) (by rw [pow_succ] at hln; linarith)
        have h1 := hrec l (by linarith)
        have hF := F_half_le hc₂ hW hG hlpos
        have hF0 := F_nonneg hc₂ hW hG hlpos
        have hF20 := F_nonneg hc₂ hW hG (by positivity : 0 < l / 2)
        have h4 : c / l * h (l / 2) ≤
            c / l * (4 * F c₂ W G (l / 2) + 2 * c ^ 2 * M / (l / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hIH hcl0
        have h5 : c / l * (4 * F c₂ W G (l / 2)) ≤ 2 * F c₂ W G l := by
          calc c / l * (4 * F c₂ W G (l / 2)) ≤ 1 / 16 * (4 * (8 * F c₂ W G l)) :=
                mul_le_mul hcl' (by linarith) (by linarith) (by norm_num)
            _ = 2 * F c₂ W G l := by ring
        have h6 : c / l * (2 * c ^ 2 * M / (l / 2) ^ 2) = 8 * (c / l) * (c ^ 2 * M / l ^ 2) := by
          field_simp; ring
        have h7 : 8 * (c / l) * (c ^ 2 * M / l ^ 2) ≤ 1 / 2 * (c ^ 2 * M / l ^ 2) := by
          have : 0 ≤ c ^ 2 * M / l ^ 2 := by positivity
          nlinarith
        have hX : 0 ≤ c ^ 2 * M / l ^ 2 := by positivity
        have h8 : 2 * c ^ 2 * M / l ^ 2 = 2 * (c ^ 2 * M / l ^ 2) := by ring
        have h9 : c / l * (4 * F c₂ W G (l / 2) + 2 * c ^ 2 * M / (l / 2) ^ 2) =
            c / l * (4 * F c₂ W G (l / 2)) + c / l * (2 * c ^ 2 * M / (l / 2) ^ 2) := by ring
        rw [h8]
        linarith [h1, h4, h5, h6, h7, h9]
  intro l hl
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (l / (4 * l₁)) (by norm_num : (1 : ℝ) < 2)
  have h4l : 0 < 4 * l₁ := by positivity
  exact hstep n l hl (by rw [div_lt_iff₀ h4l] at hn; linarith)

end Recursion

end FSQtail
