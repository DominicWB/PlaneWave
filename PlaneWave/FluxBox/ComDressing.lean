import PlaneWave.FluxBox.FlatRemainderClasses

/-!
# Flux route, stage 2, part 11: the centre-of-mass dressing

* `FSLattice.sum_inv_rho_slab_le`: for transfers with `1 ≤ |θ|² ≤ 4^{I+1}` and
  `2|θ| ≤ |F_c(θ)| < 2^{J+1}·2`, `Σ 1/(|θ| |F_c(θ)|) ≤ 11000 (2J+3)(I+1)` (dyadic shells in `|θ|`
  and the slab-weighted sum of `lem:slab`);
* `gcmK_eq` (the com force on a hop): `G^cm(q, p) = -i w(q, p) c_j(p, θ)`; `gcmK_conj`;
* the split `G^cm = G^{cm,gap} + G^{cm,res}` by the transfer floor `|E(q) - E(p)| ≥ g²|θ|/μ_j`
  (`gapC`), and **the com dressing** `Y = kop y`, `y = G^{cm,gap}/(i ω)` (`ycK`), with
  `i[T_N, Y] = G^{cm,gap}` (`comm_YcN`) and `Y` symmetric (`YcN_symm`);
* **`row_ycK_le`**: for every input `p` and channel `j`,
  `Σ_q |y(q,p)| 1{q on j from p} ≤ (2 μ_j c_j / M̄_j) Λ_N |Π_j(p)|`, `Λ_N = 11000 (2J+3)(I+1)` with
  `J = Jn(2N)`, `I = ⌊log₂ 8N⌋` (`= O(log² N)`);
* **`norm_YN_le`**: `‖Y v‖ ≤ Σ_j (2 μ_j c_j/M̄_j) Λ_N ‖|Π_j| v‖` (Schur with the conserved weight
  `|Π_j|`);
* **`norm_yK_bulk_le`**: on bulk-fed hops (`p ∈ Q`, `q ∉ P`, or the reverse),
  `|y(q, p)| ≤ potMaj(q, p)`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSLattice

open FSChannel Finset

/-- **The gapped slab sum with the transfer weight.** -/
theorem sum_inv_rho_slab_le (c : Fin 3 → ℝ) {I J : ℕ} (T : Finset L3)
    (hT : ∀ θ ∈ T, 1 ≤ lsq θ ∧ lsq θ ≤ 4 ^ (I + 1) ∧ 2 * rho θ ≤ |slabF c θ| ∧
      |slabF c θ| < 2 ^ (J + 1) * 2) :
    ∑ θ ∈ T, 1 / (rho θ * |slabF c θ|) ≤ 11000 * (2 * J + 3) * (I + 1) := by
  classical
  set f : L3 → ℝ := fun θ => 1 / (rho θ * |slabF c θ|)
  have hf0 : ∀ θ, 0 ≤ f θ := fun θ => by
    simp only [f]; have := rho_nonneg θ; positivity
  -- the shell of each transfer
  have hshell : ∀ θ ∈ T, f θ ≤ ∑ i ∈ range (I + 1),
      if (4 : ℝ) ^ i ≤ lsq θ ∧ lsq θ ≤ 4 ^ (i + 1) then f θ else 0 := by
    intro θ hθ
    obtain ⟨h1, h2, -, -⟩ := hT θ hθ
    have hex : ∃ i : ℕ, lsq θ ≤ 4 ^ (i + 1) := ⟨I, h2⟩
    set i := Nat.find hex
    have hiI : i ≤ I := Nat.find_min' hex h2
    have hi2 : lsq θ ≤ 4 ^ (i + 1) := Nat.find_spec hex
    have hi1 : (4 : ℝ) ^ i ≤ lsq θ := by
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h0, pow_zero]; exact h1
      · have hmin := Nat.find_min hex (show i - 1 < i by omega)
        push Not at hmin
        rw [show i - 1 + 1 = i by omega] at hmin
        exact hmin.le
    calc f θ = (if (4 : ℝ) ^ i ≤ lsq θ ∧ lsq θ ≤ 4 ^ (i + 1) then f θ else 0) := by
          rw [if_pos ⟨hi1, hi2⟩]
      _ ≤ _ := by
          apply single_le_sum (f := fun i => if (4 : ℝ) ^ i ≤ lsq θ ∧ lsq θ ≤ 4 ^ (i + 1)
            then f θ else 0)
          · intro i _; split_ifs
            · exact hf0 θ
            · exact le_rfl
          · exact mem_range.mpr (by omega)
  have hsum := sum_le_sum hshell
  rw [sum_comm] at hsum
  -- one shell
  have hpiece : ∀ i ∈ range (I + 1), ∑ θ ∈ T, (if (4 : ℝ) ^ i ≤ lsq θ ∧ lsq θ ≤ 4 ^ (i + 1)
      then f θ else 0) ≤ 11000 * (2 * J + 3) := by
    intro i _
    rw [← sum_filter]
    have hρ : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    have e4 : ((2 : ℝ) ^ i) ^ 2 = 4 ^ i := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    set S := T.filter fun θ => (4 : ℝ) ^ i ≤ lsq θ ∧ lsq θ ≤ 4 ^ (i + 1)
    have hS : ∀ θ ∈ S, (2 : ℝ) ^ i ≤ rho θ := by
      intro θ hθ
      have hs1 := (mem_filter.mp hθ).2.1
      unfold rho
      apply Real.le_sqrt_of_sq_le
      rw [e4]; exact hs1
    have h := slab_inv_sum_le c hρ (by positivity : (0 : ℝ) < 2 ^ (i + 1)) (J := J) S (by
        intro θ hθ
        obtain ⟨hθT, hs1, hs2⟩ := mem_filter.mp hθ
        obtain ⟨-, -, hfl, hcap⟩ := hT θ hθT
        refine ⟨by rw [e4]; exact hs1, by rw [e4, ← pow_succ']; linarith [hs2], ?_, ?_⟩
        · have : (2 : ℝ) ^ (i + 1) = 2 * 2 ^ i := by ring
          rw [this]
          exact le_trans (by linarith [hS θ hθ]) hfl
        · calc |slabF c θ| < 2 ^ (J + 1) * 2 := hcap
            _ ≤ 2 ^ (J + 1) * 2 ^ (i + 1) := by
                gcongr
                calc (2 : ℝ) = 2 ^ 1 := by norm_num
                  _ ≤ 2 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega))
    have e : 11000 * ((2 : ℝ) ^ i) ^ 2 * (2 / 2 ^ (i + 1) + 2 * (J + 1) / 2 ^ i) =
        11000 * (2 * J + 3) * 2 ^ i := by
      field_simp
      ring
    rw [e] at h
    have hfS : ∀ θ ∈ S, f θ ≤ 1 / 2 ^ i * (1 / |slabF c θ|) := by
      intro θ hθ
      simp only [f]
      have hr := hS θ hθ
      have hF : 0 < |slabF c θ| := by
        obtain ⟨-, -, hfl, -⟩ := hT θ (mem_filter.mp hθ).1
        have := rho_nonneg θ
        have h2i : (0 : ℝ) < 2 ^ i := by positivity
        linarith
      rw [div_mul_div_comm, one_mul]
      exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hr hF.le)
    calc ∑ θ ∈ S, f θ ≤ ∑ θ ∈ S, 1 / 2 ^ i * (1 / |slabF c θ|) := sum_le_sum hfS
      _ = 1 / 2 ^ i * ∑ θ ∈ S, 1 / |slabF c θ| := by rw [mul_sum]
      _ ≤ 1 / 2 ^ i * (11000 * (2 * J + 3) * 2 ^ i) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 11000 * (2 * J + 3) := by field_simp
  calc ∑ θ ∈ T, f θ ≤ _ := hsum
    _ ≤ ∑ _i ∈ range (I + 1), (11000 : ℝ) * (2 * J + 3) := sum_le_sum hpiece
    _ = 11000 * (2 * J + 3) * (I + 1) := by
        rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

end FSLattice

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## The com force on a hop -/

section ComKernel

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

omit [Fintype ν] in
lemma cidx_onCh {j : Ch eta} {q p : Cfg eta N} (hj : OnCh j (cidx N q) (cidx N p)) :
    cidx N q = cidx N p + tr j (chT N j q p) := hj

lemma potMaj_eq_chan (_hL : 0 < L) {j : Ch eta} {k k' : Cf eta} (hj : OnCh j k k') (hne : k ≠ k') :
    potMaj sys L k k' = chC sys L j / latticeNormSq (k (lead j) - k' (lead j)) := by
  classical
  unfold potMaj
  rw [Finset.sum_eq_single j]
  · unfold chMaj; rw [if_pos hj]
  · intro j' _ hj'
    unfold chMaj
    rw [if_neg (fun h => hj' (onCh_unique h hj hne))]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- On a channel, `|w(q, p)| ≤ c_j/|θ|²`. -/
lemma norm_wNK_chan_le (hL : 0 < L) {j : Ch eta} {q p : Cfg eta N}
    (hj : OnCh j (cidx N q) (cidx N p)) (hne : q ≠ p) :
    ‖wNK sys L N q p‖ ≤ chC sys L j / FSLattice.lsq (chT N j q p) := by
  have hne' : cidx N q ≠ cidx N p := fun h => hne (finiteConfigLatticeIndex_injective eta N h)
  have h := norm_potKernel_le sys hL (cidx N q) (cidx N p)
  rw [potMaj_eq_chan hL hj hne'] at h
  exact h

omit [Fintype ν] in
/-- `A(q) - A(p) = λ_j (E(q) - E(p)) + c_j(p, θ)` on a channel. -/
lemma Aproj_hop {j : Ch eta} {q p : Cfg eta N} (hj : OnCh j (cidx N q) (cidx N p)) :
    Aproj sys L p₀ q - Aproj sys L p₀ p =
      lamC sys p₀ j * (Asym sys L N q - Asym sys L N p) + comC sys p₀ (gF L) j (cidx N p) (chT N j q p) := by
  rw [Aproj_eq, Aproj_eq, Asym_eq_Ek, Asym_eq_Ek]
  change regL sys (gF L) p₀ (cidx N q) - regL sys (gF L) p₀ (cidx N p) =
    lamC sys p₀ j * (E sys.mass (gF L) (cidx N q) - E sys.mass (gF L) (cidx N p)) +
      comC sys p₀ (gF L) j (cidx N p) (chT N j q p)
  rw [cidx_onCh hj]
  exact regL_hop sys p₀ (gF L) j (cidx N p) (chT N j q p)

/-- **The com force on a hop**: `G^cm(q, p) = -i w(q, p) c_j(p, θ)`. -/
lemma gcmK_eq (hL : 0 < L) {j : Ch eta} {q p : Cfg eta N} (hj : OnCh j (cidx N q) (cidx N p)) :
    gcmK sys L p₀ N q p =
      -Complex.I * wNK sys L N q p * (comC sys p₀ (gF L) j (cidx N p) (chT N j q p) : ℂ) := by
  have h := Aproj_hop (sys := sys) (L := L) (p₀ := p₀) hj
  unfold gcmK gK
  rw [whK_eq_lam hL hj]
  have e : (Aproj sys L p₀ p - Aproj sys L p₀ q : ℝ) =
      -(lamC sys p₀ j * (Asym sys L N q - Asym sys L N p) + comC sys p₀ (gF L) j (cidx N p) (chT N j q p)) := by
    rw [← h]; ring
  rw [e]
  push_cast
  ring

/-- `G^cm` vanishes off the channels. -/
lemma gcmK_eq_zero (h : wNK sys L N q p = 0) : gcmK sys L p₀ N q p = 0 := by
  unfold gcmK gK
  rw [whK_eq_zero_of_wNK h, h]
  ring

omit [Fintype ν] in
lemma symm_I_comm {A B : En eta N →ₗ[ℂ] En eta N} (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (Complex.I • (A ∘ₗ B - B ∘ₗ A)).IsSymmetric := by
  intro x y
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, inner_smul_left,
    inner_smul_right, inner_sub_left, inner_sub_right, Complex.conj_I]
  rw [hA (B x) y, hB x (A y), hB (A x) y, hA x (B y)]
  ring

lemma GcmN_symm (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    (GcmN sys L p₀ N : En eta N →ₗ[ℂ] En eta N).IsSymmetric := by
  have h := GN_split (sys := sys) (p₀ := p₀) (N := N) hL H hKernel
  have e : GcmN sys L p₀ N = GN sys L p₀ N +
      Complex.I • (TN sys L N ∘ₗ WhN sys L p₀ N - WhN sys L p₀ N ∘ₗ TN sys L N) := by
    rw [h]; abel
  rw [e]
  have h1 := GN_symm (sys := sys) (L := L) (p₀ := p₀) (N := N)
  have h2 := symm_I_comm (TN_symm (sys := sys) (L := L) (N := N)) (WhN_symm (sys := sys) (p₀ := p₀) (N := N) hL)
  intro x y
  simp only [LinearMap.add_apply, inner_add_left, inner_add_right]
  rw [h1 x y, h2 x y]

lemma gcmK_conj (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (q p : Cfg eta N) : gcmK sys L p₀ N p q = conj (gcmK sys L p₀ N q p) := by
  have h := FSKernel.matK_conj_of_symm (GcmN_symm (p₀ := p₀) (N := N) hL H hKernel) q p
  rwa [matK_kop, matK_kop] at h

end ComKernel

/-! ## The com dressing -/

section Dressing

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N : ℕ)

open Classical in
/-- The gapped part of the com force (transfer floor). -/
noncomputable def gcmGap (q p : Cfg eta N) : ℂ := if gapC sys L N q p then gcmK sys L p₀ N q p else 0

open Classical in
/-- The resonant part of the com force. -/
noncomputable def gcmRes (q p : Cfg eta N) : ℂ := if gapC sys L N q p then 0 else gcmK sys L p₀ N q p

/-- The kernel of the com dressing, `y = G^{cm,gap}/(i ω)`. -/
noncomputable def ycK (q p : Cfg eta N) : ℂ :=
  FSKernel.divK (Asym sys L N) (fun q p => -Complex.I * gcmGap sys L p₀ N q p) q p

/-- The com dressing `Y` on the box. -/
noncomputable abbrev YcN : En eta N →ₗ[ℂ] En eta N := FSKernel.kop (ycK sys L p₀ N)

variable {sys L p₀ N}

lemma gcmGap_add_gcmRes (q p : Cfg eta N) :
    gcmGap sys L p₀ N q p + gcmRes sys L p₀ N q p = gcmK sys L p₀ N q p := by
  unfold gcmGap gcmRes; split_ifs <;> simp

lemma GcmN_split : GcmN sys L p₀ N = FSKernel.kop (gcmGap sys L p₀ N) + FSKernel.kop (gcmRes sys L p₀ N) := by
  rw [← FSKernel.kop_add]
  show FSKernel.kop (gcmK sys L p₀ N) = _
  congr 1
  funext q p
  exact (gcmGap_add_gcmRes q p).symm

lemma gcmGap_conj (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (q p : Cfg eta N) : gcmGap sys L p₀ N p q = conj (gcmGap sys L p₀ N q p) := by
  unfold gcmGap
  rw [gapC_comm p q]
  split_ifs
  · exact gcmK_conj hL H hKernel q p
  · simp

lemma gcmRes_conj (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (q p : Cfg eta N) : gcmRes sys L p₀ N p q = conj (gcmRes sys L p₀ N q p) := by
  unfold gcmRes
  rw [gapC_comm p q]
  split_ifs
  · simp
  · exact gcmK_conj hL H hKernel q p

/-- **The homological equation** `i[T_N, Y] = G^{cm,gap}`. -/
theorem comm_YcN (hL : 0 < L) :
    Complex.I • (TN sys L N ∘ₗ YcN sys L p₀ N - YcN sys L p₀ N ∘ₗ TN sys L N) =
      FSKernel.kop (gcmGap sys L p₀ N) := by
  have h := FSKernel.comm_divK (Asym sys L N) (fun q p => -Complex.I * gcmGap sys L p₀ N q p) (by
    intro q p hqp
    unfold gcmGap
    split_ifs with hg
    · exact absurd hqp (gapC_ne hL hg)
    · simp)
  have e : YcN sys L p₀ N = FSKernel.kop (FSKernel.divK (Asym sys L N)
      (fun q p => -Complex.I * gcmGap sys L p₀ N q p)) := rfl
  rw [e]
  change Complex.I • (FSKernel.dg (fun q => (Asym sys L N q : ℂ)) ∘ₗ _ - _ ∘ₗ
    FSKernel.dg (fun q => (Asym sys L N q : ℂ))) = _
  rw [h, ← FSKernel.kop_smul]
  congr 1
  funext q p
  simp only [Pi.smul_apply, smul_eq_mul]
  have hI : Complex.I * -Complex.I = 1 := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [← mul_assoc, hI, one_mul]

lemma ycK_conj (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (q p : Cfg eta N) : ycK sys L p₀ N p q = conj (ycK sys L p₀ N q p) := by
  unfold ycK FSKernel.divK
  dsimp only
  by_cases h : Asym sys L N q = Asym sys L N p
  · rw [if_pos h.symm, if_pos h]; simp
  · rw [if_neg (Ne.symm h), if_neg h, gcmGap_conj hL H hKernel q p, map_div₀, map_mul, map_neg,
      Complex.conj_I, Complex.conj_ofReal]
    have hd : ((Asym sys L N q - Asym sys L N p : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr h
    have hd' : ((Asym sys L N p - Asym sys L N q : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (Ne.symm h)
    rw [div_eq_div_iff hd' hd]
    push_cast
    ring

lemma YcN_symm (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q) :
    (YcN sys L p₀ N : En eta N →ₗ[ℂ] En eta N).IsSymmetric :=
  FSKernel.kop_symm _ fun q p => ycK_conj hL H hKernel q p

end Dressing

/-! ## The rows of the dressing -/

section Rows

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

omit [Fintype ν] in
/-- On the box, `A ≤ 3 η g² N²/2`. -/
lemma Asym_le_box (_hL : 0 < L) (q : Cfg eta N) : Asym sys L N q ≤ 3 * eta * gF L ^ 2 * N ^ 2 / 2 := by
  unfold Asym massKineticSymbol
  have hterm : ∀ a, finitePlaneWaveKabs (2 * Real.pi / L) N (q a) ^ 2 / sys.mass a ≤
      3 * gF L ^ 2 * N ^ 2 := by
    intro a
    have hm := sys.one_le_mass a
    have e := kabs_sq_eq (n := N) L (q a)
    have hgl : gL L = gF L := rfl
    rw [hgl] at e
    have hl : FSLattice.lsq (finitePlaneWaveLatticeIndex N (q a)) ≤ 3 * (N : ℝ) ^ 2 :=
      lsq_cidx_le q a
    have h1 : finitePlaneWaveKabs (2 * Real.pi / L) N (q a) ^ 2 ≤ 3 * gF L ^ 2 * N ^ 2 := by
      rw [e]
      have := mul_le_mul_of_nonneg_left hl (sq_nonneg (gF L))
      linarith
    calc finitePlaneWaveKabs (2 * Real.pi / L) N (q a) ^ 2 / sys.mass a
        ≤ finitePlaneWaveKabs (2 * Real.pi / L) N (q a) ^ 2 / 1 :=
          div_le_div_of_nonneg_left (sq_nonneg _) one_pos hm
      _ ≤ _ := by rw [div_one]; exact h1
  calc 1 / 2 * ∑ a, finitePlaneWaveKabs (2 * Real.pi / L) N (q a) ^ 2 / sys.mass a
      ≤ 1 / 2 * ∑ _a : Fin eta, 3 * gF L ^ 2 * N ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hterm a) (by norm_num)
    _ = 3 * eta * gF L ^ 2 * N ^ 2 / 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

omit [Fintype ν] in
/-- **The mismatch cap on the box**: `|F_c(θ)| < 2^{J+1}·2`, `J = Jn(2N)`. -/
lemma slabF_cap_box (hL : 0 < L) {j : Ch eta} {q p : Cfg eta N} (hj : OnCh j (cidx N q) (cidx N p)) :
    |FSLattice.slabF (cCh sys j (cidx N p)) (chT N j q p)| < 2 ^ (Jn sys (2 * N) + 1) * 2 := by
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hE := Asym_hop (sys := sys) (L := L) hj
  have hq' := Asym_le_box (sys := sys) hL q
  have hp' := Asym_le_box (sys := sys) hL p
  have hq0 := Asym_nonneg (sys := sys) (L := L) q
  have hp0 := Asym_nonneg (sys := sys) (L := L) p
  set F := FSLattice.slabF (cCh sys j (cidx N p)) (chT N j q p)
  have habs : |F| = 2 * muCh sys j / gF L ^ 2 * |Asym sys L N q - Asym sys L N p| := by
    rw [hE, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))]
    field_simp
  have hdiff : |Asym sys L N q - Asym sys L N p| ≤ 3 * eta * gF L ^ 2 * N ^ 2 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hF : |F| ≤ 3 * mtop sys * eta * (N : ℝ) ^ 2 := by
    rw [habs]
    have hm := muCh_le_mtop (sys := sys) j
    calc 2 * muCh sys j / gF L ^ 2 * |Asym sys L N q - Asym sys L N p|
        ≤ 2 * muCh sys j / gF L ^ 2 * (3 * eta * gF L ^ 2 * N ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = 3 * muCh sys j * eta * (N : ℝ) ^ 2 := by field_simp
      _ ≤ 3 * mtop sys * eta * (N : ℝ) ^ 2 := by gcongr
  set X := mtop sys * eta * ((2 * N : ℕ) : ℝ) ^ 2 with hXdef
  have hlog : ⌈X⌉₊ < 2 ^ (Jn sys (2 * N) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlog' : X < 2 ^ (Jn sys (2 * N) + 1) := by
    have h1 := Nat.le_ceil X
    have h2 : ((⌈X⌉₊ : ℕ) : ℝ) < ((2 ^ (Jn sys (2 * N) + 1) : ℕ) : ℝ) := by exact_mod_cast hlog
    rw [Nat.cast_pow, Nat.cast_ofNat] at h2
    linarith
  have hX : X = mtop sys * eta * (2 * (N : ℝ)) ^ 2 := by rw [hXdef]; push_cast; ring
  have h2pos : (0 : ℝ) < 2 ^ (Jn sys (2 * N) + 1) := by positivity
  have hm1 := one_le_mtop sys
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h3 : 3 * mtop sys * eta * (N : ℝ) ^ 2 ≤ X := by
    rw [hX]
    have : 0 ≤ mtop sys * eta * (N : ℝ) ^ 2 := by positivity
    nlinarith
  linarith

omit [Fintype ν] in
lemma lsq_chT_box (j : Ch eta) (q p : Cfg eta N) : FSLattice.lsq (chT N j q p) ≤ 4 ^ (Nat.log 2 (8 * N) + 1) := by
  have h1 : FSLattice.lsq (chT N j q p) ≤ 12 * (N : ℝ) ^ 2 := by
    unfold chT
    have hq := inP_cidx q (lead j)
    have hp := inP_cidx p (lead j)
    rw [FSLattice.lsq_eq_sum, Fin.sum_univ_three]
    have b : ∀ i, (((cidx N q (lead j) - cidx N p (lead j)) i : ℤ) : ℝ) ^ 2 ≤ 4 * N ^ 2 := by
      intro i
      have hq' := hq i
      have hp' := hp i
      rw [Pi.sub_apply, Int.cast_sub]
      have : |((cidx N q (lead j) i : ℤ) : ℝ) - ((cidx N p (lead j) i : ℤ) : ℝ)| ≤ 2 * N := by
        have := abs_sub ((cidx N q (lead j) i : ℤ) : ℝ) ((cidx N p (lead j) i : ℤ) : ℝ)
        linarith
      have h0 : (0 : ℝ) ≤ 2 * N := by positivity
      calc (((cidx N q (lead j) i : ℤ) : ℝ) - ((cidx N p (lead j) i : ℤ) : ℝ)) ^ 2
          = |((cidx N q (lead j) i : ℤ) : ℝ) - ((cidx N p (lead j) i : ℤ) : ℝ)| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * N) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = 4 * N ^ 2 := by ring
    have := b 0; have := b 1; have := b 2
    simp only [Pi.sub_apply] at *
    linarith
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    have : FSLattice.lsq (chT 0 j q p) ≤ 0 := by simpa using h1
    have h4 : (0 : ℝ) ≤ 4 ^ (Nat.log 2 (8 * 0) + 1) := by positivity
    linarith
  have h2 : (8 * N : ℕ) < 2 ^ (Nat.log 2 (8 * N) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : ((8 * N : ℕ) : ℝ) < ((2 ^ (Nat.log 2 (8 * N) + 1) : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at h3
  have e : (4 : ℝ) ^ (Nat.log 2 (8 * N) + 1) = ((2 : ℝ) ^ (Nat.log 2 (8 * N) + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm (Nat.log 2 (8 * N) + 1) 2, pow_mul]; norm_num
  rw [e]
  have h5 : (8 * N : ℝ) ^ 2 ≤ ((2 : ℝ) ^ (Nat.log 2 (8 * N) + 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3.le 2
  nlinarith

variable (sys) in
/-- The layer–shell factor of the box, `Λ_N = 11000 (2 Jn(2N) + 3)(⌊log₂ 8N⌋ + 1)`. -/
noncomputable def LamB (N : ℕ) : ℝ := 11000 * (2 * Jn sys (2 * N) + 3) * (Nat.log 2 (8 * N) + 1)

omit [Fintype ν] in
lemma LamB_nonneg (N : ℕ) : 0 ≤ LamB sys N := by unfold LamB; positivity

omit [Fintype ν] in
open FSChannel in
/-- **The gapped row with the transfer weight** on the box. -/
theorem box_row_le (hL : 0 < L) (j : Ch eta) (p : Cfg eta N) (T : Finset (Cfg eta N))
    (hT : ∀ q ∈ T, OnCh j (cidx N q) (cidx N p) ∧ q ≠ p ∧
      gF L ^ 2 * rho (chT N j q p) / muCh sys j ≤ |Asym sys L N q - Asym sys L N p|) :
    ∑ q ∈ T, 1 / (rho (chT N j q p) * |Asym sys L N q - Asym sys L N p|) ≤
      2 * muCh sys j / gF L ^ 2 * LamB sys N := by
  classical
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  set c := cCh sys j (cidx N p)
  set F : Lattice3 → ℝ := fun θ => FSLattice.slabF c θ
  have h1 : ∀ q ∈ T, 1 / (rho (chT N j q p) * |Asym sys L N q - Asym sys L N p|) =
      2 * muCh sys j / gF L ^ 2 * (1 / (rho (chT N j q p) * |F (chT N j q p)|)) := by
    intro q hq
    rw [Asym_hop (hT q hq).1, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))]
    show 1 / (rho (chT N j q p) * (gF L ^ 2 / (2 * muCh sys j) * |F (chT N j q p)|)) =
      2 * muCh sys j / gF L ^ 2 * (1 / (rho (chT N j q p) * |F (chT N j q p)|))
    field_simp
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have hinj : Set.InjOn (fun q => chT N j q p) T := fun q hq q' hq' h =>
    chT_injOn j p (hT q hq).1 (hT q' hq').1 h
  rw [← Finset.sum_image (f := fun θ => 1 / (rho θ * |F θ|)) hinj]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold LamB
  apply FSLattice.sum_inv_rho_slab_le c
  intro θ hθ
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hθ
  obtain ⟨hon, hne, hfl⟩ := hT q hq
  refine ⟨one_le_lsq_chT hon hne, lsq_chT_box j q p, ?_, slabF_cap_box hL hon⟩
  rw [Asym_hop hon, abs_mul, abs_of_pos (by positivity : 0 < gF L ^ 2 / (2 * muCh sys j))] at hfl
  have e : gF L ^ 2 * rho (chT N j q p) / muCh sys j =
      gF L ^ 2 / (2 * muCh sys j) * (2 * rho (chT N j q p)) := by field_simp
  rw [e] at hfl
  exact le_of_mul_le_mul_left hfl (by positivity)

open FSChannel in
/-- The size of the dressing on a gapped hop of channel `j`:
`|y(q, p)| ≤ c_j g² |Π_j(p)| / (M̄_j |θ| |E(q) - E(p)|)`. -/
lemma norm_ycK_chan_le (hL : 0 < L) {j : Ch eta} {q p : Cfg eta N}
    (hj : OnCh j (cidx N q) (cidx N p)) (hne : q ≠ p) :
    ‖ycK sys L p₀ N q p‖ ≤ chC sys L j * gF L ^ 2 * piC j (cidx N p) / Mtot sys j *
      (1 / (rho (chT N j q p) * |Asym sys L N q - Asym sys L N p|)) := by
  have hθ : 1 ≤ FSLattice.lsq (chT N j q p) := one_le_lsq_chT hj hne
  have hρ : 0 < rho (chT N j q p) := by
    unfold rho; exact Real.sqrt_pos.mpr (by linarith)
  have hρsq : rho (chT N j q p) ^ 2 = FSLattice.lsq (chT N j q p) := rho_sq _
  have hcC := chC_nonneg sys hL j
  have hpi := piC_nonneg j (cidx N p)
  have hM := Mtot_pos sys j
  have hg := gF_pos hL
  unfold ycK FSKernel.divK
  split_ifs with hE
  · rw [norm_zero]; positivity
  have hd : 0 < |Asym sys L N q - Asym sys L N p| := abs_pos.mpr (sub_ne_zero.mpr hE)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hg1 : ‖gcmGap sys L p₀ N q p‖ ≤ ‖gcmK sys L p₀ N q p‖ := by
    unfold gcmGap; split_ifs
    · exact le_rfl
    · rw [norm_zero]; exact norm_nonneg _
  have hg2 : ‖gcmK sys L p₀ N q p‖ ≤ chC sys L j / FSLattice.lsq (chT N j q p) *
      (gF L ^ 2 * rho (chT N j q p) * piC j (cidx N p) / Mtot sys j) := by
    rw [gcmK_eq hL hj, norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact mul_le_mul (norm_wNK_chan_le hL hj hne) (abs_comC_le sys p₀ (gF L) j _ _)
      (abs_nonneg _) (by positivity)
  have e : chC sys L j / FSLattice.lsq (chT N j q p) *
      (gF L ^ 2 * rho (chT N j q p) * piC j (cidx N p) / Mtot sys j) =
      chC sys L j * gF L ^ 2 * piC j (cidx N p) / Mtot sys j * (1 / rho (chT N j q p)) := by
    rw [← hρsq]; field_simp
  rw [e] at hg2
  calc ‖gcmGap sys L p₀ N q p‖ / |Asym sys L N q - Asym sys L N p|
      ≤ chC sys L j * gF L ^ 2 * piC j (cidx N p) / Mtot sys j * (1 / rho (chT N j q p)) /
          |Asym sys L N q - Asym sys L N p| := by gcongr; exact hg1.trans hg2
    _ = _ := by field_simp

omit [Fintype ν] in
lemma gapC_onCh {q p : Cfg eta N} (h : gapC sys L N q p) {j : Ch eta}
    (hj : OnCh j (cidx N q) (cidx N p)) :
    gF L ^ 2 * FSChannel.rho (chT N j q p) / muCh sys j ≤ |Asym sys L N q - Asym sys L N p| := by
  obtain ⟨hne, j', hj', hfl⟩ := h
  have hne' : cidx N q ≠ cidx N p := fun h => hne (finiteConfigLatticeIndex_injective eta N h)
  have := onCh_unique hj hj' hne'
  subst this
  exact hfl

variable (sys L) in
/-- The row constant of the dressing on channel `j`: `2 μ_j c_j / M̄_j`. -/
noncomputable def CYc (j : Ch eta) : ℝ := 2 * muCh sys j * chC sys L j / Mtot sys j

lemma CYc_nonneg (hL : 0 < L) (j : Ch eta) : 0 ≤ CYc sys L j := by
  unfold CYc
  have := muCh_pos sys j; have := chC_nonneg sys hL j; have := Mtot_pos sys j
  positivity

open Classical in
/-- **The rows of the dressing**: `Σ_q |y(q, p)| 1{q on j from p} ≤ C_j Λ_N |Π_j(p)|`. -/
theorem row_ycK_le (hL : 0 < L) (j : Ch eta) (p : Cfg eta N) :
    ∑ q, (if OnCh j (cidx N q) (cidx N p) then ‖ycK sys L p₀ N q p‖ else 0) ≤
      CYc sys L j * LamB sys N * piC j (cidx N p) := by
  classical
  have hg := gF_pos hL
  have hμ := muCh_pos sys j
  have hM := Mtot_pos sys j
  have hpi := piC_nonneg j (cidx N p)
  set T := Finset.univ.filter fun q : Cfg eta N =>
    OnCh j (cidx N q) (cidx N p) ∧ gapC sys L N q p
  have hzero : ∀ q, OnCh j (cidx N q) (cidx N p) → ¬ gapC sys L N q p → ycK sys L p₀ N q p = 0 := by
    intro q _ hg'
    unfold ycK FSKernel.divK
    dsimp only
    unfold gcmGap
    rw [if_neg hg']
    split_ifs <;> simp
  have h1 : ∑ q, (if OnCh j (cidx N q) (cidx N p) then ‖ycK sys L p₀ N q p‖ else 0) =
      ∑ q ∈ T, ‖ycK sys L p₀ N q p‖ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hj : OnCh j (cidx N q) (cidx N p)
    · by_cases hgq : gapC sys L N q p
      · simp [hj, hgq]
      · simp [hj, hgq, hzero q hj hgq]
    · simp [hj]
  rw [h1]
  have h2 : ∀ q ∈ T, ‖ycK sys L p₀ N q p‖ ≤ chC sys L j * gF L ^ 2 * piC j (cidx N p) / Mtot sys j *
      (1 / (FSChannel.rho (chT N j q p) * |Asym sys L N q - Asym sys L N p|)) := by
    intro q hq
    obtain ⟨hj, hgq⟩ := (Finset.mem_filter.mp hq).2
    exact norm_ycK_chan_le hL hj hgq.1
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.mul_sum]
  have h3 := box_row_le (sys := sys) hL j p T (by
    intro q hq
    obtain ⟨hj, hgq⟩ := (Finset.mem_filter.mp hq).2
    exact ⟨hj, hgq.1, gapC_onCh hgq hj⟩)
  have hcC := chC_nonneg sys hL j
  calc chC sys L j * gF L ^ 2 * piC j (cidx N p) / Mtot sys j *
        ∑ q ∈ T, 1 / (FSChannel.rho (chT N j q p) * |Asym sys L N q - Asym sys L N p|)
      ≤ chC sys L j * gF L ^ 2 * piC j (cidx N p) / Mtot sys j *
          (2 * muCh sys j / gF L ^ 2 * LamB sys N) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = CYc sys L j * LamB sys N * piC j (cidx N p) := by
        unfold CYc; field_simp

end Rows

/-! ## Schur with a conserved weight -/

section SchurW

variable {X : Type*} [Fintype X]

/-- **Schur's test with a conserved weight**: if `0 ≤ K`, `‖κ‖ ≤ K`, `r` is constant along the
support of `K`, and the rows and columns of `K` are bounded by `r`, then `‖kop κ v‖ ≤ ‖r v‖`. -/
theorem norm_kop_le_weight (κ : X → X → ℂ) (K : X → X → ℝ) (r : X → ℝ) (hK0 : ∀ q p, 0 ≤ K q p)
    (hκ : ∀ q p, ‖κ q p‖ ≤ K q p) (hr0 : ∀ q, 0 ≤ r q)
    (hcons : ∀ q p, K q p ≠ 0 → r q = r p)
    (hrow : ∀ q, ∑ p, K q p ≤ r q) (hcol : ∀ p, ∑ q, K q p ≤ r p) (v : EuclideanSpace ℂ X) :
    ‖FSKernel.kop κ v‖ ^ 2 ≤ ∑ p, r p ^ 2 * ‖v.ofLp p‖ ^ 2 := by
  rw [FSKernel.norm_sq_eq]
  have hq : ∀ q, ‖(FSKernel.kop κ v).ofLp q‖ ^ 2 ≤ r q * ∑ p, K q p * ‖v.ofLp p‖ ^ 2 := by
    intro q
    have h1 : ‖(FSKernel.kop κ v).ofLp q‖ ≤ ∑ p, K q p * ‖v.ofLp p‖ := by
      rw [FSKernel.kop_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hκ q p) (norm_nonneg _)
    have h2 : (∑ p, K q p * ‖v.ofLp p‖) ^ 2 ≤ (∑ p, K q p) * ∑ p, K q p * ‖v.ofLp p‖ ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => hK0 q p)
        (fun p _ => by have := hK0 q p; positivity) (fun p _ => le_of_eq (by ring))
    calc ‖(FSKernel.kop κ v).ofLp q‖ ^ 2 ≤ (∑ p, K q p * ‖v.ofLp p‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ p, K q p) * ∑ p, K q p * ‖v.ofLp p‖ ^ 2 := h2
      _ ≤ r q * ∑ p, K q p * ‖v.ofLp p‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hrow q) (Finset.sum_nonneg fun p _ => by
            have := hK0 q p; positivity)
  calc ∑ q, ‖(FSKernel.kop κ v).ofLp q‖ ^ 2 ≤ ∑ q, r q * ∑ p, K q p * ‖v.ofLp p‖ ^ 2 :=
        Finset.sum_le_sum fun q _ => hq q
    _ = ∑ p, ‖v.ofLp p‖ ^ 2 * ∑ q, K q p * r q := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        ring
    _ = ∑ p, ‖v.ofLp p‖ ^ 2 * (r p * ∑ q, K q p) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        by_cases h : K q p = 0
        · rw [h]; ring
        · rw [hcons q p h]; ring
    _ ≤ ∑ p, ‖v.ofLp p‖ ^ 2 * (r p * r p) := by
        gcongr with p
        · exact hr0 p
        · exact hcol p
    _ = ∑ p, r p ^ 2 * ‖v.ofLp p‖ ^ 2 := by
        refine Finset.sum_congr rfl fun p _ => ?_; ring

end SchurW

/-! ## The operator bound of the dressing -/

section NormY

variable {sys : CoulombSystem eta ν} {L : ℝ} {p₀ : Fin eta} {N : ℕ}

open Classical in
/-- The channel part of the dressing kernel. -/
noncomputable def ycKc (j : Ch eta) (q p : Cfg eta N) : ℂ :=
  if OnCh j (cidx N q) (cidx N p) then ycK sys L p₀ N q p else 0

lemma ycK_eq_sum (_hL : 0 < L) (q p : Cfg eta N) :
    ycK sys L p₀ N q p = ∑ j, ycKc (sys := sys) (L := L) (p₀ := p₀) j q p := by
  classical
  by_cases h0 : ycK sys L p₀ N q p = 0
  · rw [h0]; symm
    exact Finset.sum_eq_zero fun j _ => by unfold ycKc; split_ifs <;> simp [h0]
  have hg : gapC sys L N q p := by
    by_contra hg
    apply h0
    unfold ycK FSKernel.divK
    dsimp only
    unfold gcmGap
    rw [if_neg hg]
    split_ifs <;> simp
  obtain ⟨hne, j, hj, -⟩ := hg
  have hne' : cidx N q ≠ cidx N p := fun h => hne (finiteConfigLatticeIndex_injective eta N h)
  rw [Finset.sum_eq_single j]
  · unfold ycKc; rw [if_pos hj]
  · intro j' _ hj'
    unfold ycKc
    rw [if_neg (fun h => hj' (onCh_unique h hj hne'))]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The pair weight `r_j(p) = C_j Λ_N |Π_j(p)|`. -/
noncomputable def rY (j : Ch eta) (p : Cfg eta N) : ℝ :=
  CYc sys L j * LamB sys N * piC j (cidx N p)

lemma rY_nonneg (hL : 0 < L) (j : Ch eta) (p : Cfg eta N) : 0 ≤ rY (sys := sys) (L := L) j p := by
  unfold rY
  have := CYc_nonneg (sys := sys) hL j
  have := LamB_nonneg (sys := sys) N
  have := piC_nonneg j (cidx N p)
  positivity

/-- **The channel parts of the dressing**: `‖Y_j v‖² ≤ Σ_p r_j(p)² |v_p|²`. -/
theorem norm_sq_kop_ycKc_le (hL : 0 < L)
    (H : MolecularFourierH2 eta →L[ℂ] lp (fun _ : FourierConfig eta Lattice3 => ℂ) 2)
    (hKernel : ∀ N u q, H (molecularH2Truncate N u) q =
      fourierCubeKernelAction (2 * Real.pi / L) (coulombLatticeHamiltonianKernel sys L) N u q)
    (j : Ch eta) (v : En eta N) :
    ‖FSKernel.kop (ycKc (sys := sys) (L := L) (p₀ := p₀) j) v‖ ^ 2 ≤
      ∑ p, rY (sys := sys) (L := L) j p ^ 2 * ‖v.ofLp p‖ ^ 2 := by
  classical
  apply norm_kop_le_weight _ (fun q p => ‖ycKc (sys := sys) (L := L) (p₀ := p₀) j q p‖)
    (rY (sys := sys) (L := L) j) (fun q p => norm_nonneg _) (fun q p => le_rfl)
    (fun q => rY_nonneg hL j q)
  · intro q p h
    have hj : OnCh j (cidx N q) (cidx N p) := by
      by_contra hj; apply h; unfold ycKc; rw [if_neg hj, norm_zero]
    unfold rY
    rw [piC_onCh hj]
  · intro q
    have h := row_ycK_le (sys := sys) (p₀ := p₀) hL j q
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun p _ => ?_
    unfold ycKc
    by_cases hj : OnCh j (cidx N p) (cidx N q)
    · rw [if_pos (onCh_symm hj), if_pos hj, ycK_conj hL H hKernel p q, Complex.norm_conj]
    · rw [if_neg (fun h => hj (onCh_symm h)), if_neg hj, norm_zero]
  · intro p
    have h := row_ycK_le (sys := sys) (p₀ := p₀) hL j p
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold ycKc
    split_ifs <;> simp

end NormY

end FSFlux
