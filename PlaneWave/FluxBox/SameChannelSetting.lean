import PlaneWave.FluxBox.MiddleSplitWords

/-!
# Flux route, stage 3, part 33: the same-channel word in `C × C` — setting

* **Rigidity** (`inQ_of_two_hops`): a configuration one hop of `j` from a cold `b` and one hop of
  `j₃ ≠ j` from a cold `c` lies in the bulk ball (`3 c_* < 1/4`); hence only `j₃ = j` meets the
  same-channel word `ss_j` in `⟨W u_C, Ỹ u_C⟩`.
* **Lines by transfers** (`lineT`, `sum_line_eq`): sums over the `j`-line of `b` in the box are sums
  over the transfers `θ` (`cidx f = cidx b + tr_j θ`).
* **The channel potential along a line** `W_j(θ) = w(tr_j θ)` (`Wl`): Hermitian (`Wl_neg`),
  `|W_j(θ)| ≤ c_j/|θ|²` (`norm_Wl_le`), `w_j(f,b) = W_j(θ)` (`wj_eq_Wl`).
* **The energy along a line** `e_k(θ) = (g²/2μ_j) F_{c(k)}(θ)` (`eL`).
* **The composite kernel** `A(c,b) = Σ_f conj w_j(f,c) ỹ_{ss}(f,b)` (`ssA`), the form identity
  (`inner_W_Yss`) and its transfer form (`ssA_eq`):
  `A(c,b) = -λ Σ_{θ,φ} [b+θ ∈ cube, ∉ P][b+φ ∈ P] W(θ_c - θ) W(θ - φ) W(φ)/e_b(θ)`.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators Topology
open Filter PlaneWaveCertificate PlaneWaveDynamics PlaneWaveKinetic FluxSourceTest FSGalerkin
  NormedSpace FSNormal MeasureTheory

namespace FSFlux

variable {eta : ℕ} {ν : Type} [Fintype ν]

/-! ## Rigidity -/

section Rigidity

variable {sys : CoulombSystem eta ν} {N n : ℕ}

omit [Fintype ν] in
lemma rho_tr_le (j : Ch eta) (θ : Lattice3) (r : Fin eta) :
    FSChannel.rho (tr j θ r) ≤ FSChannel.rho θ := by
  by_cases hr : r ∈ moved j
  · rcases tr_apply_moved j θ hr with h | h
    · rw [h]
    · rw [h]; unfold FSChannel.rho; rw [lsq_neg]
  · rw [tr_apply_not_moved j θ hr]
    unfold FSChannel.rho
    have : FSLattice.lsq (0 : Lattice3) = 0 := by simp [FSLattice.lsq]
    rw [this, Real.sqrt_zero]
    exact Real.sqrt_nonneg _

omit [Fintype ν] in
lemma rho_tr_moved {j : Ch eta} (θ : Lattice3) {r : Fin eta} (hr : r ∈ moved j) :
    FSChannel.rho (tr j θ r) = FSChannel.rho θ := by
  rcases tr_apply_moved j θ hr with h | h
  · rw [h]
  · rw [h]; unfold FSChannel.rho; rw [lsq_neg]

omit [Fintype ν] in
lemma rho_sub_le (a b : Lattice3) : FSChannel.rho (a - b) ≤ FSChannel.rho a + FSChannel.rho b := by
  have h := FSChannel.rho_add_le a (-b)
  have e : FSChannel.rho (-b) = FSChannel.rho b := by unfold FSChannel.rho; rw [lsq_neg]
  rw [sub_eq_add_neg]; linarith

omit [Fintype ν] in
/-- **Rigidity of the same-channel word**: a configuration one hop of `j` from a cold `b` and one hop
of `j₃ ≠ j` from a cold `c` is in the bulk ball. -/
lemma inQ_of_two_hops {j j₃ : Ch eta} (hj : j₃ ≠ j) {f b c : Cfg eta N}
    (hb : InC (n : ℝ) (cst sys) (cidx N b)) (hc : InC (n : ℝ) (cst sys) (cidx N c))
    (h₁ : OnCh j (cidx N f) (cidx N b)) (h₃ : OnCh j₃ (cidx N f) (cidx N c)) :
    InQ (n : ℝ) (cidx N f) := by
  set θ := cidx N f (lead j) - cidx N b (lead j)
  set θ₃ := cidx N f (lead j₃) - cidx N c (lead j₃)
  have e1 : cidx N f = cidx N b + tr j θ := h₁
  have e3 : cidx N f = cidx N c + tr j₃ θ₃ := h₃
  have hcs := cst_le32 sys
  have hc0 := cst_pos sys
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbr : ∀ r, FSChannel.rho (cidx N b r) ≤ cst sys * n := fun r => rho_le_of_inC hb r
  have hcr : ∀ r, FSChannel.rho (cidx N c r) ≤ cst sys * n := fun r => rho_le_of_inC hc r
  -- a register moved by exactly one of the two channels
  have hmv : moved j₃ ≠ moved j := fun h => hj (moved_inj h)
  obtain ⟨s, hs⟩ : ∃ s, ¬ (s ∈ moved j₃ ↔ s ∈ moved j) := by
    by_contra hcon
    exact hmv (Finset.ext fun s => by by_contra h; exact hcon ⟨s, h⟩)
  -- every register of `f` is within `3 c_* n`
  have hall : ∀ r, FSChannel.rho (cidx N f r) ≤ 3 * (cst sys * n) := by
    by_cases hsj : s ∈ moved j
    · have hs3 : s ∉ moved j₃ := fun h => hs ⟨fun _ => hsj, fun _ => h⟩
      have hfs : cidx N f s = cidx N c s := by
        rw [e3, Pi.add_apply, tr_apply_not_moved j₃ θ₃ hs3, add_zero]
      have hθ : FSChannel.rho θ ≤ 2 * (cst sys * n) := by
        have h1 : cidx N f s = cidx N b s + tr j θ s := by rw [e1]; rfl
        have h2 : tr j θ s = cidx N c s - cidx N b s := by rw [← hfs, h1]; abel
        rw [← rho_tr_moved θ hsj, h2]
        have := rho_sub_le (cidx N c s) (cidx N b s)
        linarith [hbr s, hcr s]
      intro r
      have h1 : cidx N f r = cidx N b r + tr j θ r := by rw [e1]; rfl
      rw [h1]
      have := FSChannel.rho_add_le (cidx N b r) (tr j θ r)
      have := rho_tr_le j θ r
      linarith [hbr r]
    · have hs3 : s ∈ moved j₃ := by
        by_contra h; exact hs ⟨fun h' => absurd h' h, fun h' => absurd h' hsj⟩
      have hfs : cidx N f s = cidx N b s := by
        rw [e1, Pi.add_apply, tr_apply_not_moved j θ hsj, add_zero]
      have hθ : FSChannel.rho θ₃ ≤ 2 * (cst sys * n) := by
        have h1 : cidx N f s = cidx N c s + tr j₃ θ₃ s := by rw [e3]; rfl
        have h2 : tr j₃ θ₃ s = cidx N b s - cidx N c s := by rw [← hfs, h1]; abel
        rw [← rho_tr_moved θ₃ hs3, h2]
        have := rho_sub_le (cidx N b s) (cidx N c s)
        linarith [hbr s, hcr s]
      intro r
      have h1 : cidx N f r = cidx N c r + tr j₃ θ₃ r := by rw [e3]; rfl
      rw [h1]
      have := FSChannel.rho_add_le (cidx N c r) (tr j₃ θ₃ r)
      have := rho_tr_le j₃ θ₃ r
      linarith [hcr r]
  intro r
  have h1 := hall r
  have h2 := FSChannel.rho_sq (cidx N f r)
  have h3 := FSChannel.rho_nonneg (cidx N f r)
  have h4 : 3 * (cst sys * n) ≤ (n : ℝ) / 4 := by nlinarith
  have h5 : FSChannel.rho (cidx N f r) ^ 2 ≤ ((n : ℝ) / 4) ^ 2 :=
    pow_le_pow_left₀ h3 (h1.trans h4) 2
  show nsq (cidx N f r) ≤ ((n : ℝ) / 4) ^ 2
  have e : nsq (cidx N f r) = FSChannel.rho (cidx N f r) ^ 2 := by rw [h2]; rfl
  rw [e]; exact h5

end Rigidity

/-! ## Lines by transfers -/

section Lines

variable {N : ℕ}

variable (N) in
/-- The transfers of the `j`-line through `b` inside the box. -/
noncomputable def lineT (j : Ch eta) (b : Cfg eta N) : Finset Lattice3 :=
  (FSLattice.box (2 * N)).filter (fun θ => cidx N b + tr j θ ∈ fourierConfigCube eta N)

omit [Fintype ν] in
lemma chT_mem_box2 (j : Ch eta) (f b : Cfg eta N) : chT N j f b ∈ FSLattice.box (2 * N) := by
  rw [FSLattice.mem_box]
  intro i
  have hf := (mem_fourierConfigCube_iff eta N (cidx N f)).mp (finiteConfigLatticeIndex_mem_cube eta N f)
    (lead j) i
  have hb := (mem_fourierConfigCube_iff eta N (cidx N b)).mp (finiteConfigLatticeIndex_mem_cube eta N b)
    (lead j) i
  unfold chT
  simp only [Pi.sub_apply]
  push_cast
  constructor <;> linarith [hf.1, hf.2, hb.1, hb.2]

omit [Fintype ν] in
open Classical in
/-- **Sums along a line by transfers**:
`Σ_f [f ~_j b] F(θ_f) = Σ_{θ ∈ lineT j b} F(θ)`, `θ_f = chT f b`. -/
lemma sum_line_eq {β : Type*} [AddCommMonoid β] (j : Ch eta) (b : Cfg eta N) (F : Lattice3 → β) :
    ∑ f, (if OnCh j (cidx N f) (cidx N b) then F (chT N j f b) else 0) = ∑ θ ∈ lineT N j b, F θ := by
  classical
  rw [← Finset.sum_filter]
  have hinj : Set.InjOn (fun f => chT N j f b)
      ↑(Finset.univ.filter fun f : Cfg eta N => OnCh j (cidx N f) (cidx N b)) :=
    fun f hf f' hf' h => chT_injOn j b (Finset.mem_filter.mp hf).2 (Finset.mem_filter.mp hf').2 h
  rw [← Finset.sum_image (f := F) hinj]
  congr 1
  ext θ
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, lineT]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨chT_mem_box2 j f b, ?_⟩
    rw [← cidx_onCh hf]
    exact finiteConfigLatticeIndex_mem_cube eta N f
  · rintro ⟨_, hθ⟩
    obtain ⟨f, -, hf⟩ := Finset.mem_image.mp hθ
    have hon : OnCh j (cidx N f) (cidx N b) := by
      have : cidx N f = cidx N b + tr j θ := hf
      exact onCh_of_eq this
    refine ⟨f, hon, ?_⟩
    have e : cidx N f = cidx N b + tr j θ := hf
    unfold chT
    rw [e, Pi.add_apply, tr_lead]
    abel

end Lines

/-! ## The channel potential along a line -/

section Wline

variable (sys : CoulombSystem eta ν) (L : ℝ)

/-- `W_j(θ) = w(tr_j θ)`. -/
noncomputable def Wl (j : Ch eta) (θ : Lattice3) : ℂ := wL sys L (tr j θ)

variable {sys L} {N : ℕ}

lemma wj_eq_Wl {j : Ch eta} {f b : Cfg eta N} (h : OnCh j (cidx N f) (cidx N b)) :
    wj sys L N j f b = Wl sys L j (chT N j f b) := by
  unfold wj chPart Wl
  rw [if_pos h, wNK_eq_convK]
  unfold convK
  rw [cidx_onCh h, add_sub_cancel_left]

/-- `W_j(-θ) = conj W_j(θ)`. -/
lemma Wl_neg (hL : 0 < L) (j : Ch eta) (θ : Lattice3) :
    Wl sys L j (-θ) = conj (Wl sys L j θ) := by
  unfold Wl wL
  have h := potKernel_conj' (sys := sys) hL (tr j θ) 0
  have e : potKernel sys L (tr j (-θ)) 0 = potKernel sys L 0 (tr j θ) := by
    have := potKernel_add_add sys L (tr j (-θ)) 0 (tr j θ)
    rw [← tr_add, neg_add_cancel, zero_add, tr_zero] at this
    exact this.symm
  rw [e, h]

/-- `|W_j(θ)| ≤ c_j/|θ|²` (and `W_j(0) = 0`). -/
lemma norm_Wl_le (hL : 0 < L) (j : Ch eta) (θ : Lattice3) :
    ‖Wl sys L j θ‖ ≤ chC sys L j / FSLattice.lsq θ := by
  by_cases hθ : θ = 0
  · subst hθ
    unfold Wl wL
    rw [tr_zero, potKernel_self_eq_zero (sys := sys) hL, norm_zero]
    exact div_nonneg (chC_nonneg sys hL j) (FSLattice.lsq_nonneg _)
  · have hne : tr j θ ≠ 0 := by
      intro h
      apply hθ
      have := congrFun h (lead j)
      rwa [tr_lead] at this
    have hon : OnCh j (tr j θ) 0 := onCh_of_eq (by rw [zero_add])
    have h1 := norm_potKernel_le sys hL (tr j θ) 0
    rw [potMaj_eq_chan hL hon hne] at h1
    unfold Wl wL
    refine h1.trans (le_of_eq ?_)
    congr 1
    rw [Pi.zero_apply, sub_zero, tr_lead]
    rfl

end Wline

/-! ## The energy along a line -/

section Eline

variable (sys : CoulombSystem eta ν) (L : ℝ)

/-- `e_k(θ) = E(k + tr_j θ) - E(k) = (g²/2μ_j) F_{c_j(k)}(θ)`. -/
noncomputable def eL (j : Ch eta) (k : Cf eta) (θ : Lattice3) : ℝ :=
  gF L ^ 2 / (2 * muCh sys j) * FSLattice.slabF (cCh sys j k) θ

variable {sys L} {N : ℕ}

omit [Fintype ν] in
lemma Asym_sub_eq_eL {j : Ch eta} {f b : Cfg eta N} (h : OnCh j (cidx N f) (cidx N b)) :
    Asym sys L N f - Asym sys L N b = eL sys L j (cidx N b) (chT N j f b) :=
  Asym_hop h

end Eline

/-! ## The composite kernel of the same-channel word -/

section SsKernel

variable (sys : CoulombSystem eta ν) (L : ℝ) (p₀ : Fin eta) (N n : ℕ)

/-- `A(c,b) = Σ_f conj w_j(f,c) ỹ_{ss_j}(f,b)`. -/
noncomputable def ssA (j : Ch eta) (c b : Cfg eta N) : ℂ :=
  ∑ f, conj (wj sys L N j f c) * ytK sys L N n (ssK sys L p₀ N n j) f b

variable {sys L p₀ N n}

/-- **The form of the composite**: `⟨W_j v, Ỹ_{ss} v⟩ = Σ_{c,b} conj(v_c) v_b A(c,b)`. -/
lemma inner_W_Yss (j : Ch eta) (v : En eta N) :
    ⟪FSKernel.kop (wj sys L N j) v, FSKernel.kop (ytK sys L N n (ssK sys L p₀ N n j)) v⟫_ℂ =
      ∑ c, ∑ b, conj (v.ofLp c) * v.ofLp b * ssA sys L p₀ N n j c b := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, FSKernel.kop_apply, map_sum, map_mul]
  unfold ssA
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun f _ => ?_
  ring

omit [Fintype ν] in
lemma chT_sub (j : Ch eta) (f c b : Cfg eta N) : chT N j f c = chT N j f b - chT N j c b := by
  unfold chT; abel

omit [Fintype ν] in
lemma onCh_via {j : Ch eta} {f c b : Cf eta} (h1 : OnCh j f b) (h2 : OnCh j c b) : OnCh j f c :=
  onCh_trans (onCh_symm h2) (onCh_symm h1)

open Classical in
/-- **The composite kernel by transfers**: for a cold `b` and `c` on its `j`-line,
`A(c,b) = -λ_j Σ_{θ,φ ∈ lineT} [b+θ ∉ P, b+φ ∈ P] W(θ_c - θ) W(θ - φ) W(φ)/e_b(θ)`. -/
theorem ssA_eq (hL : 0 < L) {j : Ch eta} {c b : Cfg eta N} (hb : InC (n : ℝ) (cst sys) (cidx N b))
    (hcb : OnCh j (cidx N c) (cidx N b)) :
    ssA sys L p₀ N n j c b = -(lamC sys p₀ j : ℂ) * ∑ θ ∈ lineT N j b, ∑ φ ∈ lineT N j b,
      (if ¬ InP (n : ℝ) (cidx N b + tr j θ) ∧ InP (n : ℝ) (cidx N b + tr j φ) then
        Wl sys L j (chT N j c b - θ) * Wl sys L j (θ - φ) * Wl sys L j φ /
          ((eL sys L j (cidx N b) θ : ℝ) : ℂ) else 0) := by
  classical
  set θc := chT N j c b
  set G : Lattice3 → ℂ := fun θ => -(lamC sys p₀ j : ℂ) * ∑ φ ∈ lineT N j b,
    (if ¬ InP (n : ℝ) (cidx N b + tr j θ) ∧ InP (n : ℝ) (cidx N b + tr j φ) then
      Wl sys L j (θc - θ) * Wl sys L j (θ - φ) * Wl sys L j φ / ((eL sys L j (cidx N b) θ : ℝ) : ℂ)
      else 0) with hG
  have key : ∀ f, conj (wj sys L N j f c) * ytK sys L N n (ssK sys L p₀ N n j) f b =
      if OnCh j (cidx N f) (cidx N b) then G (chT N j f b) else 0 := by
    intro f
    by_cases hf : OnCh j (cidx N f) (cidx N b)
    · rw [if_pos hf]
      set θ := chT N j f b with hθ
      have hfc : OnCh j (cidx N f) (cidx N c) := onCh_via hf hcb
      have hcf : conj (wj sys L N j f c) = Wl sys L j (θc - θ) := by
        rw [wj_eq_Wl hfc, chT_sub j f c b, ← Wl_neg hL]
        congr 1; abel
      have hfθ : cidx N f = cidx N b + tr j θ := cidx_onCh hf
      rw [hcf]
      by_cases hP : InP (n : ℝ) (cidx N f)
      · -- `f ∈ P`: the word vanishes
        have hG0 : G θ = 0 := by
          simp only [hG]
          rw [Finset.sum_eq_zero, mul_zero]
          intro φ _
          rw [if_neg]
          rintro ⟨h1, -⟩
          exact h1 (hfθ ▸ hP)
        have hs : ssK sys L p₀ N n j f b = 0 := by
          unfold ssK chainK; rw [if_neg (fun h => h.1 hP), mul_zero]
        rw [hG0]
        unfold ytK
        rw [hs]
        split_ifs <;> simp
      unfold ytK ssK chainK
      · have hQ : ¬ InQ (n : ℝ) (cidx N f) := fun h => hP (inQ_imp_inP (Nat.cast_nonneg n) h)
        rw [if_pos ⟨hQ, hb⟩, if_pos ⟨hP, hb⟩, Asym_sub_eq_eL hf]
        -- the inner sum along the line
        have hd : ∑ d, wj sys L N j f d * (if InP (n : ℝ) (cidx N d) then wj sys L N j d b else 0) =
            ∑ φ ∈ lineT N j b, (if InP (n : ℝ) (cidx N b + tr j φ) then
              Wl sys L j (θ - φ) * Wl sys L j φ else 0) := by
          rw [← sum_line_eq j b (fun φ => if InP (n : ℝ) (cidx N b + tr j φ) then
              Wl sys L j (θ - φ) * Wl sys L j φ else 0)]
          refine Finset.sum_congr rfl fun d _ => ?_
          by_cases hdb : OnCh j (cidx N d) (cidx N b)
          · rw [if_pos hdb]
            have hfd : OnCh j (cidx N f) (cidx N d) := onCh_via hf hdb
            have hdθ : cidx N d = cidx N b + tr j (chT N j d b) := cidx_onCh hdb
            rw [wj_eq_Wl hfd, wj_eq_Wl hdb, chT_sub j f d b, ← hdθ, ← hθ]
            split_ifs <;> simp
          · rw [if_neg hdb]
            have : wj sys L N j d b = 0 := by unfold wj chPart; rw [if_neg hdb]
            rw [this]; simp
        rw [hd, ← hθ]
        rw [hfθ] at hP
        set e : ℂ := ((eL sys L j (cidx N b) θ : ℝ) : ℂ)
        have hS : ∀ φ ∈ lineT N j b, (if ¬ InP (n : ℝ) (cidx N b + tr j θ) ∧
            InP (n : ℝ) (cidx N b + tr j φ) then
              Wl sys L j (θc - θ) * Wl sys L j (θ - φ) * Wl sys L j φ / e else 0) =
            Wl sys L j (θc - θ) * (if InP (n : ℝ) (cidx N b + tr j φ) then
              Wl sys L j (θ - φ) * Wl sys L j φ else 0) / e := by
          intro φ _
          by_cases h : InP (n : ℝ) (cidx N b + tr j φ)
          · rw [if_pos ⟨hP, h⟩, if_pos h]; ring
          · rw [if_neg (fun h' => h h'.2), if_neg h]; ring
        simp only [hG]
        rw [Finset.sum_congr rfl hS, ← Finset.sum_div, ← Finset.mul_sum]
        ring
    · rw [if_neg hf]
      have hfc : ¬ OnCh j (cidx N f) (cidx N c) := fun h =>
        hf (onCh_trans hcb (onCh_symm h))
      have : wj sys L N j f c = 0 := by unfold wj chPart; rw [if_neg hfc]
      rw [this, map_zero, zero_mul]
  unfold ssA
  rw [Finset.sum_congr rfl fun f _ => key f, sum_line_eq j b G]
  simp only [hG]
  rw [← Finset.mul_sum]

end SsKernel

end FSFlux
