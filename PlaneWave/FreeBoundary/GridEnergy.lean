import PlaneWave.FreeBoundary.GridCoreGeneral
import PlaneWave.FreeBoundary.TorusGroundEnergy

/-!
# `app:free`, part 6: the grid energy theorem for the range-truncated kernel

The first step of the proof of `prop:free`: Theorem `thm:grid-energy` for the `g_L` kernel,
`|E_{N,L} - E_L| ≤ C K^{-3}`.

The Galerkin reference of the generalised grid core (`PlaneWave.FreeBoundary.GridCoreGeneral`) is set to the Fourier
coefficients of `g_L` (`gLNucData`: `γ ρ = ĝ_L` with `γ = (1 + V_θ)/(πL)`, zero mode left out),
and the register Galerkin Hamiltonian is identified with the cube Hamiltonian `gLham` at radius
`2m` (`Hgal_regUnitary_gL`, following the release's bridge). With the torus energy and the cubic
error of `PlaneWave.FreeBoundary.TorusGroundEnergy` this gives:

* **`gLSectorKernelGridError`**: for a Coulomb system, an admissible labelling, `L > 0` and a
  profile `θ`, the torus ground energy `E_L` of the `g_L` Hamiltonian exists, and for every
  `m ≥ gLGridThreshold` and every kernel of the class (`IsGridKernel γ ρ m κ`: real, even,
  `|κ| ≤ γ/|ν|²`, `κ = ĝ_L` for `|ν| ≤ m`, zero beyond `‖ν‖∞ = 2m`) the grid ground energy `E_g`
  of the padded collocation method (`Hpos`, `n' = 4m+1` points per direction, kernel `wKer κ m`,
  `K = (2π/L) m`) satisfies `|E_g - E_L| ≤ C / K³`;
* **`gLSectorGridError`**: the same for the truncated kernel `(g_L)_{≤2K}` (`sharpKernel γ ρ m`).

The zero mode `ĝ_L(0)` is a constant multiplication operator; it shifts `E_g` and `E_L` by the
same constant and is left out of both. The constants depend on the system, `L`, `θ` (through
`V_θ`) and `|E_L|`; they are not claimed to be uniform in `L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace ComplexConjugate BigOperators
open Finset PlaneWaveCertificate FreeBoundary

namespace PlaneWaveGridG

section Bridge

variable {eta : ℕ} {ν : Type} [Fintype ν] {R : ℝ} {θ : ℝ → ℝ}

/-- Positioned nuclei from the release file's nuclear data. -/
def posNucleiOfG (data : FiniteBONuclearData ν) : PosNuclei ν where
  charge := data.charge
  charge_nonneg := data.charge_nonneg
  position := data.position

/-- The quantum particles of a Coulomb system on the register. -/
def regParticlesOfG (sys : CoulombSystem eta ν) : RegParticles eta where
  mass := sys.mass
  one_le_mass := sys.one_le_mass
  charge := sys.charge

@[simp] lemma regParticlesOfG_mass (sys : CoulombSystem eta ν) :
    (regParticlesOfG sys).mass = sys.mass := rfl

@[simp] lemma regParticlesOfG_charge (sys : CoulombSystem eta ν) :
    (regParticlesOfG sys).charge = sys.charge := rfl

lemma nsq_eq_latticeNormSq (x : Lat3) : nsq x = latticeNormSq x := rfl

lemma latticeSub_eq (a b : Lattice3) : latticeSub a b = a - b := by
  funext i; simp [latticeSub]

/-! ### The reference kernel `ĝ_L` -/

/-- `γ = (1 + V)/(πL)`. -/
noncomputable def gLgamma (L V : ℝ) : ℝ := (1 + V) * coulombCellAmplitude L

lemma gLgamma_pos {L V : ℝ} (hL : 0 < L) (hV : 0 ≤ V) : 0 < gLgamma L V :=
  mul_pos (by linarith) (coulombCellAmplitude_pos hL)

/-- The normalised reference kernel `ρ = ĝ_L / γ`. -/
noncomputable def gLref (L : ℝ) (θ : ℝ → ℝ) (V : ℝ) (x : Lat3) : ℝ :=
  (gLlat L θ x).re / gLgamma L V

lemma gLref_neg (L : ℝ) (θ : ℝ → ℝ) (V : ℝ) (x : Lat3) : gLref L θ V (-x) = gLref L θ V x := by
  unfold gLref
  rw [gLlat_neg]

lemma norm_gLlat_le {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (x : Lattice3) :
    ‖gLlat L θ x‖ ≤ (1 + tv R θ) * coulombCellAmplitude L * (1 / latticeNormSq x) := by
  classical
  have hV := hθ.tv_nonneg
  unfold gLlat
  split_ifs with h
  · rw [norm_zero]
    have := latticeNormSq_nonneg x
    have := cellAmp_nonneg L hL
    have : (0 : ℝ) ≤ 1 + tv R θ := by linarith
    positivity
  · have hb := rangecut hL hθ _ h
    have hpos := latticeNormSq_pos h
    rw [what_eq hL] at hb
    refine hb.trans (le_of_eq ?_)
    unfold coulombCellAmplitude
    field_simp

lemma gLref_bound {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (x : Lat3) :
    |gLref L θ (tv R θ) x| ≤ coul x := by
  have hγ := gLgamma_pos hL hθ.tv_nonneg
  unfold gLref
  rw [abs_div, abs_of_pos hγ, div_le_iff₀ hγ]
  calc |(gLlat L θ x).re| ≤ ‖gLlat L θ x‖ := Complex.abs_re_le_norm _
    _ ≤ (1 + tv R θ) * coulombCellAmplitude L * (1 / latticeNormSq x) := norm_gLlat_le hL hθ x
    _ = coul x * gLgamma L (tv R θ) := by
        unfold coul gLgamma
        rw [nsq_eq_latticeNormSq]
        ring

/-- The nuclear data of the register with the `g_L` reference kernel. -/
noncomputable def gLNucData (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) : NucData ν :=
  { (posNucleiOfG sys.nuclei).toNucData with
    ref := gLref L θ (tv R θ)
    ref_neg := fun x => gLref_neg L θ _ x
    ref_bound := fun x => gLref_bound hL hθ x }

lemma kee_gL (sys : CoulombSystem eta ν) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) (x : Lat3) :
    kee (gLNucData sys hL hθ) (gLgamma L (tv R θ)) x = gLlat L θ x := by
  have hγ := (gLgamma_pos hL hθ.tv_nonneg).ne'
  change ((gLgamma L (tv R θ) * ((gLlat L θ x).re / gLgamma L (tv R θ)) : ℝ) : ℂ) = gLlat L θ x
  rw [mul_div_cancel₀ _ hγ]
  exact Complex.conj_eq_iff_re.mp (gLlat_conj hθ L x)

/-! ### Identification with the cube Hamiltonian -/

/-- The release file's finite modes of radius `M` are the register modes. -/
noncomputable def modeEquiv (M : ℕ) : FinitePlaneWaveMode M ≃ GMode (2 * M + 1) := by
  classical
  refine Equiv.ofBijective (fun v => ofLat (finitePlaneWaveLatticeIndex M v)) ?_
  have hbox : ∀ v, InBox M (finitePlaneWaveLatticeIndex M v) := by
    intro v c
    have h := finitePlaneWaveLatticeIndex_coord_bounds M v c
    rw [abs_le]
    exact ⟨by simpa using h.1, by simpa using h.2⟩
  have hinj : Function.Injective (fun v => ofLat (M := M) (finitePlaneWaveLatticeIndex M v)) := by
    intro v w h
    have h2 : gl (ofLat (M := M) (finitePlaneWaveLatticeIndex M v)) =
        gl (ofLat (M := M) (finitePlaneWaveLatticeIndex M w)) := congrArg gl h
    rw [gl_ofLat (hbox v), gl_ofLat (hbox w)] at h2
    exact finitePlaneWaveLatticeIndex_injective M h2
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  rw [finitePlaneWaveMode_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma gl_modeEquiv (M : ℕ) (v : FinitePlaneWaveMode M) :
    gl (modeEquiv M v) = finitePlaneWaveLatticeIndex M v := by
  have hbox : InBox M (finitePlaneWaveLatticeIndex M v) := by
    intro c
    have h := finitePlaneWaveLatticeIndex_coord_bounds M v c
    rw [abs_le]
    exact ⟨by simpa using h.1, by simpa using h.2⟩
  exact gl_ofLat hbox

/-- Configurations: release modes to register modes. -/
noncomputable def cfgEquiv (eta M : ℕ) :
    FourierConfig eta (FinitePlaneWaveMode M) ≃ GConfig eta (2 * M + 1) :=
  Equiv.arrowCongr (Equiv.refl _) (modeEquiv M)

lemma cfgEquiv_apply (eta M : ℕ) (p : FourierConfig eta (FinitePlaneWaveMode M)) (i : Fin eta) :
    cfgEquiv eta M p i = modeEquiv M (p i) := rfl

/-- The lifted lattice configuration of a register configuration. -/
def liftCfg {M : ℕ} (q : GConfig eta (2 * M + 1)) : FourierConfig eta Lattice3 :=
  fun i => gl (q i)

lemma liftCfg_cfgEquiv (eta M : ℕ) (p : FourierConfig eta (FinitePlaneWaveMode M)) :
    liftCfg (cfgEquiv eta M p) = finiteConfigLatticeIndex eta M p := by
  funext i
  simp [liftCfg, cfgEquiv_apply, gl_modeEquiv, finiteConfigLatticeIndex]

lemma liftCfg_injective {M : ℕ} :
    Function.Injective (liftCfg : GConfig eta (2 * M + 1) → FourierConfig eta Lattice3) := by
  intro q p h
  funext i
  exact gl_injective (congrFun h i)

/-- A nuclear Galerkin term is the nuclear lattice kernel of `g_L`. -/
lemma galTerm_nuclear_eq_lattice_gL (sys : CoulombSystem eta ν) (m : ℕ) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (i : Fin eta) (l : ν) (q p : RCfg eta m) :
    galTerm eta m (gLNucData sys hL hθ) (gLgamma L (tv R θ)) (Sum.inr (i, l)) q p =
      latticeReferenceConfigurationKernel i (gLlatNuc sys.nuclei L θ l) (liftCfg q)
        (liftCfg p) := by
  classical
  simp only [galTerm]
  unfold latticeReferenceConfigurationKernel
  by_cases h : Spec1 (M := 2 * m) i q p
  · have h' : ∀ k : Fin eta, k ≠ i → liftCfg q k = liftCfg p k :=
      fun k hk => by simp [liftCfg, h k hk]
    rw [tk_of_rel h, if_pos h', knuc, kee_gL]
    simp only [gLlatNuc, gLNucData, PosNuclei.toNucData, posNucleiOfG, wTau, liftCfg,
      latticeSub_eq]
  · have h' : ¬ ∀ k : Fin eta, k ≠ i → liftCfg q k = liftCfg p k := by
      intro hh
      exact h fun k hk => gl_injective (hh k hk)
    rw [tk_of_not_rel h, if_neg h']

/-- A pair Galerkin term is the pair lattice kernel of `g_L`. -/
lemma galTerm_pair_eq_lattice_gL (sys : CoulombSystem eta ν) (m : ℕ) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (pr : Pairs eta) (q p : RCfg eta m) :
    galTerm eta m (gLNucData sys hL hθ) (gLgamma L (tv R θ)) (Sum.inl pr) q p =
      gLlatPair pr.1.1 pr.1.2 L θ (liftCfg q) (liftCfg p) := by
  classical
  simp only [galTerm]
  unfold gLlatPair
  by_cases h : wRel2 (M := 2 * m) pr.1.1 pr.1.2 q p
  · have h' : (∀ k : Fin eta, k ≠ pr.1.1 → k ≠ pr.1.2 → liftCfg q k = liftCfg p k) ∧
        liftCfg q pr.1.1 + liftCfg q pr.1.2 = liftCfg p pr.1.1 + liftCfg p pr.1.2 :=
      ⟨fun k hk1 hk2 => by simp [liftCfg, h.1 k hk1 hk2], h.2⟩
    rw [tk_of_rel h, if_pos h', kee_gL]
    simp only [wTau, liftCfg, latticeSub_eq]
  · have h' : ¬ ((∀ k : Fin eta, k ≠ pr.1.1 → k ≠ pr.1.2 → liftCfg q k = liftCfg p k) ∧
        liftCfg q pr.1.1 + liftCfg q pr.1.2 = liftCfg p pr.1.1 + liftCfg p pr.1.2) := by
      rintro ⟨hh1, hh2⟩
      exact h ⟨fun k hk1 hk2 => gl_injective (hh1 k hk1 hk2), hh2⟩
    rw [tk_of_not_rel h, if_neg h']

/-- **The register Galerkin Hamiltonian with the `g_L` reference is the lattice kernel of the
`g_L` Hamiltonian.** -/
lemma Hgal_eq_gLLatticeKernel (sys : CoulombSystem eta ν) (m : ℕ) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) :
    Hgal eta m (regParticlesOfG sys) (gLNucData sys hL hθ) (gLgamma L (tv R θ))
        (2 * Real.pi / L) =
      kOp (fun q p => gLlatHam sys L θ (liftCfg q) (liftCfg p)) := by
  classical
  apply LinearMap.ext
  intro u
  ext q
  simp only [Hgal, LinearMap.add_apply, PiLp.add_apply, wMul_apply, kOp_apply,
    gLlatHam, gLlatPot, mul_add, Finset.sum_add_distrib]
  have hk : kinT eta m (regParticlesOfG sys) (2 * Real.pi / L) q =
      1 / 2 * ∑ i : Fin eta, (2 * Real.pi / L) ^ 2 * latticeNormSq (liftCfg q i) /
        sys.mass i := by
    simp only [kinT, wM, liftCfg, add_sub_cancel_left, Finset.mul_sum, nsq_eq_latticeNormSq,
      regParticlesOfG_mass]
    exact sum_congr rfl fun i _ => by ring
  have hkin : (kinT eta m (regParticlesOfG sys) (2 * Real.pi / L) q : ℂ) * u q =
      ∑ p, u p * coulombLatticeKineticKernel sys L (liftCfg q) (liftCfg p) := by
    have hEq : ∀ p, liftCfg p = liftCfg q ↔ p = q := fun p => liftCfg_injective.eq_iff
    simp only [coulombLatticeKineticKernel, hEq, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [hk]
    push_cast
    ring
  rw [hkin]
  congr 1
  unfold vGalK
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Fintype.sum_equiv (Equiv.refl _) _ _ fun p => ?_
  rw [Equiv.refl_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, add_comm]
  congr 1
  · refine sum_congr rfl fun i _ => sum_congr rfl fun l _ => ?_
    rw [galTerm_nuclear_eq_lattice_gL sys m hL hθ i l q p]
    simp only [RegParticles.tcoef, regParticlesOfG_charge]
  · refine Fintype.sum_equiv (Equiv.refl _) _ _ fun pr => ?_
    rw [Equiv.refl_apply, galTerm_pair_eq_lattice_gL sys m hL hθ pr q p]
    simp only [RegParticles.tcoef, regParticlesOfG_charge]

/-- The unitary reindexing between the release file's coefficient space and the register. -/
noncomputable def regUnitary (eta M : ℕ) :
    EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode M)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (GConfig eta (2 * M + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cfgEquiv eta M)

lemma regUnitary_apply (eta M : ℕ)
    (u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode M)))
    (p : FourierConfig eta (FinitePlaneWaveMode M)) :
    regUnitary eta M u (cfgEquiv eta M p) = u p := by
  simp [regUnitary, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

lemma swapCfg_cfgEquiv (eta M : ℕ) (a b : Fin eta)
    (p : FourierConfig eta (FinitePlaneWaveMode M)) :
    swapCfg a b (cfgEquiv eta M p) = cfgEquiv eta M (swapConfig a b p) := by
  funext k
  rfl

lemma regUnitary_swap (eta M : ℕ)
    (u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode M)))
    (a b : Fin eta) (p : FourierConfig eta (FinitePlaneWaveMode M)) :
    regUnitary eta M u (swapCfg a b (cfgEquiv eta M p)) = u (swapConfig a b p) := by
  rw [swapCfg_cfgEquiv, regUnitary_apply]

lemma isSec_regUnitary_iff (eta M : ℕ) (sgn : Fin eta → ℂ) (lab : Fin eta → ℕ)
    (u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode M))) :
    IsSec sgn lab (regUnitary eta M u) ↔ IsSectorVector sgn lab u := by
  constructor
  · intro h a b hab hlab p
    have := h a b hab hlab (cfgEquiv eta M p)
    rw [regUnitary_swap, regUnitary_apply] at this
    exact this
  · intro h a b hab hlab q
    obtain ⟨p, rfl⟩ := (cfgEquiv eta M).surjective q
    rw [regUnitary_swap, regUnitary_apply]
    exact h a b hab hlab p

/-- `Hgal` with the `g_L` reference is the cube Hamiltonian `gLham` at radius `2m`, up to
reindexing. -/
lemma Hgal_regUnitary_gL (sys : CoulombSystem eta ν) (m : ℕ) {L : ℝ} (hL : 0 < L)
    (hθ : Profile R θ) (u : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode (2 * m)))) :
    Hgal eta m (regParticlesOfG sys) (gLNucData sys hL hθ) (gLgamma L (tv R θ))
        (2 * Real.pi / L) (regUnitary eta (2 * m) u) =
      regUnitary eta (2 * m) (gLham sys L θ (2 * m) u) := by
  rw [Hgal_eq_gLLatticeKernel sys m hL hθ, gLham_eq_latticeKernel]
  ext q
  obtain ⟨p, rfl⟩ := (cfgEquiv eta (2 * m)).surjective q
  rw [regUnitary_apply, kOp_apply, finiteCoefficientKernelOperator_apply]
  symm
  refine Fintype.sum_equiv (cfgEquiv eta (2 * m)) _ _ fun p' => ?_
  rw [regUnitary_apply, liftCfg_cfgEquiv, liftCfg_cfgEquiv]

/-- A sector ground state of the cube `2m` gives the register Galerkin Ritz energy. -/
lemma galRitz_of_ground_gL (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ) (m : ℕ) {L : ℝ}
    (hL : 0 < L) (hθ : Profile R θ) (EM : ℝ)
    (uM : EuclideanSpace ℂ (FourierConfig eta (FinitePlaneWaveMode (2 * m))))
    (hS : IsSectorVector sys.sign lab uM) (hn : ‖uM‖ = 1)
    (hEig : gLham sys L θ (2 * m) uM = (EM : ℂ) • uM)
    (hG : IsSectorGroundEnergy sys.sign lab (gLham sys L θ (2 * m)) EM) :
    IsSecRitz sys.sign lab (Hgal eta m (regParticlesOfG sys) (gLNucData sys hL hθ)
      (gLgamma L (tv R θ)) (2 * Real.pi / L)) EM := by
  constructor
  · intro v hv
    obtain ⟨w, rfl⟩ := (regUnitary eta (2 * m)).surjective v
    have hw : IsSectorVector sys.sign lab w :=
      (isSec_regUnitary_iff eta (2 * m) sys.sign lab w).mp hv
    have h := hG w hw
    rw [Hgal_regUnitary_gL sys m hL hθ, LinearIsometryEquiv.inner_map_map,
      LinearIsometryEquiv.norm_map]
    exact h
  · refine ⟨regUnitary eta (2 * m) uM,
      (isSec_regUnitary_iff eta (2 * m) sys.sign lab uM).mpr hS,
      by rw [LinearIsometryEquiv.norm_map, hn], ?_⟩
    rw [Hgal_regUnitary_gL sys m hL hθ, LinearIsometryEquiv.inner_map_map]
    exact form_of_eigen _ uM EM hn hEig

/-- Every exchange sector of an admissible labelling contains a nonzero register state once
`m ≥ η`. -/
lemma exists_nonzero_sec (sys : CoulombSystem eta ν) {lab : Fin eta → ℕ}
    (hlab : sys.IsAdmissible lab) (m : ℕ) (hm : eta ≤ m) :
    ∃ u : EuclideanSpace ℂ (RCfg eta m), IsSec sys.sign lab u ∧ u ≠ 0 := by
  have hcard : eta ≤ (Finset.univ : Finset (GMode (2 * (2 * m) + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    calc eta ≤ m := hm
      _ ≤ 2 * (2 * m) + 1 := by omega
      _ ≤ (2 * (2 * m) + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  obtain ⟨u, hS, hu0, -⟩ := sys.exists_nonzero_sectorVector_supported_of_card hlab
    (μ := GMode (2 * (2 * m) + 1)) Finset.univ hcard
  exact ⟨u, hS, hu0⟩

end Bridge

/-! ## The grid energy theorem -/

section Main

variable {eta : ℕ} {ν : Type} [Fintype ν] {R : ℝ} {θ : ℝ → ℝ}

/-- The grid ground energy of the `g_L` system in the exchange sector `lab` for the kernel with
coefficients `κ`: the Ritz energy of the padded collocation Hamiltonian `Hpos` (`n' = 4m+1`
points per direction, kernel `wKer κ m`, `K = (2π/L) m`) on grid functions in that sector. -/
def IsGLSectorKernelGridGroundEnergy (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ) (L : ℝ)
    (m : ℕ) (κ : Lat3 → ℝ) (Eg : ℝ) : Prop :=
  IsSecRitz sys.sign lab (Hpos (m := m) (regParticlesOfG sys) (posNucleiOfG sys.nuclei) κ
    (2 * Real.pi / L)) Eg

/-- The coupling `m̄ Σ_t |c_t| γ_t` of the register potential. -/
noncomputable def gLGridCoupling (sys : CoulombSystem eta ν) (L V : ℝ) : ℝ :=
  sys.maxMass * Zc (regParticlesOfG sys) (posNucleiOfG sys.nuclei).toNucData (gLgamma L V)

/-- The error constant of the grid theorem: `512 g³ C_grid + C_cub/8`. -/
noncomputable def gLGridErrorConstant (sys : CoulombSystem eta ν) (L V E : ℝ) : ℝ :=
  512 * (2 * Real.pi / L) ^ 3 * Cgrid sys.maxMass (gLGridCoupling sys L V) (2 * Real.pi / L)
      (|E| + 1) +
    gLCubicConst sys L V E / 8

/-- The size threshold of the grid theorem (as in the release's `coulombGridThreshold`). -/
noncomputable def gLGridThreshold (sys : CoulombSystem eta ν) (L V E : ℝ) : ℕ :=
  max (gLCubicThreshold sys L V E)
    (max eta (max (Nat.ceil (gLCubicConst sys L V E ^ ((1 : ℝ) / 3) /
        (2 * (2 * Real.pi / L))))
      (4 * Nat.ceil (2 * Real.sqrt (sys.maxMass * Ebig sys.maxMass (gLGridCoupling sys L V)
        (2 * Real.pi / L) (|E| + 1)) / (2 * Real.pi / L))))) + 8

lemma Ebig_nonneg' {M Z g Eb : ℝ} (hZ : 0 ≤ Z) : 0 ≤ Ebig M Z g Eb := by
  unfold Ebig
  refine le_trans ?_ (le_max_left _ _)
  have := J0g_pos Z g
  positivity

/-- **Grid energy theorem for the range-truncated kernel `g_L`, for every kernel of the
class.** The torus ground energy `E_L` of the `g_L` Hamiltonian exists, and for every `m` above
the threshold and every kernel `κ` of the class (`IsGridKernel γ ρ m κ`, `γ ρ = ĝ_L`) the grid
ground energy `E_g` satisfies `|E_g - E_L| ≤ C / K³`, `K = (2π/L) m`. -/
theorem gLSectorKernelGridError (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E ∧
      ∀ m : ℕ, gLGridThreshold sys L (tv R θ) E ≤ m → ∀ κ : Lat3 → ℝ,
        IsGridKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m κ →
        ∃ Eg : ℝ, IsGLSectorKernelGridGroundEnergy sys lab L m κ Eg ∧
          |Eg - E| ≤ gLGridErrorConstant sys L (tv R θ) E / ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  obtain ⟨E, hE, hCubic⟩ := gL_sector_cubic_error sys lab hlab hL hθ
  refine ⟨E, hE, ?_⟩
  intro m hm κ hκ
  have hthr := hm
  unfold gLGridThreshold at hthr
  have hm8 : 8 ≤ m := by omega
  have hmcub : gLCubicThreshold sys L (tv R θ) E ≤ 2 * m := by omega
  have hmeta : eta ≤ m := by omega
  have hmroot : Nat.ceil (gLCubicConst sys L (tv R θ) E ^ ((1 : ℝ) / 3) /
      (2 * (2 * Real.pi / L))) ≤ m := by omega
  have hmbig : Nat.ceil (2 * Real.sqrt (sys.maxMass * Ebig sys.maxMass
      (gLGridCoupling sys L (tv R θ)) (2 * Real.pi / L) (|E| + 1)) /
      (2 * Real.pi / L)) ≤ m / 4 := by omega
  have hs2 : 2 ≤ m / 4 := by omega
  have hsm : m / 4 ≤ m := Nat.div_le_self m 4
  have hms : m ≤ 8 * (m / 4) := by omega
  obtain ⟨EN, uN, hSN, hnN, hEigN, hGN, hNonneg, hRate⟩ := hCubic (2 * m) hmcub
  have hgal := galRitz_of_ground_gL sys lab m hL hθ EN uN hSN hnN hEigN hGN
  set g : ℝ := 2 * Real.pi / L with hgdef
  have hg : 0 < g := by positivity
  set γ : ℝ := gLgamma L (tv R θ) with hγdef
  have hγ : 0 ≤ γ := (gLgamma_pos hL hθ.tv_nonneg).le
  set P := regParticlesOfG sys with hPdef
  set D := gLNucData sys hL hθ with hDdef
  set M : ℝ := sys.maxMass with hMdef
  have hM0 : 0 < M := sys.maxMass_pos
  set Z : ℝ := gLGridCoupling sys L (tv R θ) with hZdef
  have hZD : Z = M * Zc P D γ := rfl
  have hZ : 0 ≤ Z := by rw [hZD]; exact mul_nonneg hM0.le (Zc_nonneg hγ)
  set Eb : ℝ := |E| + 1 with hEbdef
  set Ccub : ℝ := gLCubicConst sys L (tv R θ) E with hCcubdef
  have hCcub : 0 ≤ Ccub := gLCubicConst_nonneg sys L hθ.tv_nonneg E
  set s : ℕ := m / 4 with hsdef
  have hmr : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsr : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hmsr : (m : ℝ) ≤ 8 * s := by exact_mod_cast hms
  have hEbig0 : 0 ≤ M * Ebig M Z g Eb := mul_nonneg hM0.le (Ebig_nonneg' hZ)
  have hbig : 4 * M * Ebig M Z g Eb ≤ g ^ 2 * (s : ℝ) ^ 2 := by
    have h1 : 2 * Real.sqrt (M * Ebig M Z g Eb) / g ≤ s :=
      (Nat.le_ceil _).trans (by exact_mod_cast hmbig)
    rw [div_le_iff₀ hg] at h1
    have h2 : (2 * Real.sqrt (M * Ebig M Z g Eb)) ^ 2 ≤ (s * g) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, Real.sq_sqrt hEbig0] at h2
    nlinarith
  have hroot : Ccub ^ ((1 : ℝ) / 3) ≤ g * ((2 * m : ℕ) : ℝ) := by
    have h1 : Ccub ^ ((1 : ℝ) / 3) / (2 * g) ≤ m :=
      (Nat.le_ceil _).trans (by exact_mod_cast hmroot)
    rw [div_le_iff₀ (by positivity)] at h1
    push_cast
    linarith
  have hcube : Ccub ≤ (g * ((2 * m : ℕ) : ℝ)) ^ 3 := by
    have h1 : (Ccub ^ ((1 : ℝ) / 3)) ^ 3 = Ccub := by
      rw [show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow hCcub (by norm_num)
    calc Ccub = (Ccub ^ ((1 : ℝ) / 3)) ^ 3 := h1.symm
      _ ≤ (g * ((2 * m : ℕ) : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hCcub _) hroot 3
  have h2m : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * m)
  have hENE : EN - E ≤ 1 :=
    hRate.trans ((div_le_one (by positivity)).mpr hcube)
  have hEb : |EN| ≤ Eb := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le E]
    · linarith [le_abs_self E]
  have hNZ := exists_nonzero_sec sys hlab m hmeta
  have hP : ∀ a b, lab a = lab b → P.mass a = P.mass b ∧ P.charge a = P.charge b :=
    fun a b h => ⟨sys.mass_eq a b (hlab a b h), sys.charge_eq a b (hlab a b h)⟩
  obtain ⟨Eg, hRitz, hdiff⟩ := grid_galerkin_energy (P := P) (D := D) (m := m) sys.sign lab hP
    hγ hg hs2 hsm hms hκ.gridKernel hNZ EN Eb hEb hgal hbig
  have hRitz' : IsSecRitz sys.sign lab
      (Hgrid eta m P (posNucleiOfG sys.nuclei).toNucData κ g) Eg := hRitz
  have hpos : IsGLSectorKernelGridGroundEnergy sys lab L m κ Eg :=
    (isSecRitz_Hpos_iff sys.sign lab P (posNucleiOfG sys.nuclei) κ hκ.even g Eg).mpr hRitz'
  have hCg0 : 0 ≤ Cgrid M Z g Eb := by
    unfold Cgrid
    exact mul_nonneg (Cform_nonneg hZ) (sq_nonneg _)
  have hdiff' : |Eg - EN| ≤ 512 * Cgrid M Z g Eb / (m : ℝ) ^ 3 := by
    have hdiff2 : |Eg - EN| ≤ Cgrid M Z g Eb / (s : ℝ) ^ 3 := hdiff
    refine hdiff2.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm3 : (m : ℝ) ^ 3 ≤ 512 * (s : ℝ) ^ 3 := by
      calc (m : ℝ) ^ 3 ≤ (8 * (s : ℝ)) ^ 3 := pow_le_pow_left₀ hmr.le hmsr 3
        _ = 512 * (s : ℝ) ^ 3 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hm3 hCg0]
  have hrate' : EN - E ≤ Ccub / (8 * (g * m) ^ 3) := by
    refine hRate.trans (le_of_eq ?_)
    push_cast
    ring
  have htri : |Eg - E| ≤ |Eg - EN| + |EN - E| := by
    have := abs_sub_le Eg EN E
    linarith
  rw [abs_of_nonneg hNonneg] at htri
  have hGE : gLGridErrorConstant sys L (tv R θ) E = 512 * g ^ 3 * Cgrid M Z g Eb + Ccub / 8 :=
    rfl
  have hfinal : 512 * Cgrid M Z g Eb / (m : ℝ) ^ 3 + Ccub / (8 * (g * m) ^ 3) =
      gLGridErrorConstant sys L (tv R θ) E / (g * (m : ℝ)) ^ 3 := by
    rw [hGE, div_add_div _ _ (by positivity) (by positivity),
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  refine ⟨Eg, hpos, ?_⟩
  calc |Eg - E| ≤ |Eg - EN| + (EN - E) := htri
    _ ≤ 512 * Cgrid M Z g Eb / (m : ℝ) ^ 3 + Ccub / (8 * (g * m) ^ 3) :=
      add_le_add hdiff' hrate'
    _ = gLGridErrorConstant sys L (tv R θ) E / (g * (m : ℝ)) ^ 3 := hfinal

/-- **Grid energy theorem for the range-truncated kernel** (the truncated kernel
`(g_L)_{≤2K}`, coefficients `ĝ_L` on `‖ν‖∞ ≤ 2m`, zero mode left out): the torus ground energy
`E_L` of the `g_L` Hamiltonian exists, and for every `m` above the threshold the grid ground
energy `E_g` satisfies `|E_g - E_L| ≤ C / K³`, `K = (2π/L) m`. -/
theorem gLSectorGridError (sys : CoulombSystem eta ν) (lab : Fin eta → ℕ)
    (hlab : sys.IsAdmissible lab) {L : ℝ} (hL : 0 < L) (hθ : Profile R θ) :
    ∃ E : ℝ, IsGLTorusGroundEnergy sys lab L θ E ∧
      ∀ m : ℕ, gLGridThreshold sys L (tv R θ) E ≤ m →
        ∃ Eg : ℝ, IsGLSectorKernelGridGroundEnergy sys lab L m
            (sharpKernel (gLgamma L (tv R θ)) (gLref L θ (tv R θ)) m) Eg ∧
          |Eg - E| ≤ gLGridErrorConstant sys L (tv R θ) E / ((2 * Real.pi / L) * (m : ℝ)) ^ 3 := by
  obtain ⟨E, hE, hGrid⟩ := gLSectorKernelGridError sys lab hlab hL hθ
  exact ⟨E, hE, fun m hm => hGrid m hm _ (sharpKernel_isGridKernel
    (gLgamma_pos hL hθ.tv_nonneg).le (gLref_neg L θ _) (gLref_bound hL hθ) m)⟩

end Main

end PlaneWaveGridG
