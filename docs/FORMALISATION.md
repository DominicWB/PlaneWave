# PlaneWave: formalisation and manuscript correspondence

See the [repository README](../README.md) for the quick start. Run all build commands below from the repository root; backticked file paths are relative to that root.

A Lean 4 formalisation of plane-wave and grid discretisation error bounds for periodic Coulomb
systems, and of the auxiliary results of the manuscript (projection flux, kinetic-energy source,
free-boundary systems, logarithmic kinetic-energy bounds). Lean 4.32.1, Mathlib v4.32.1.

One Lake library, `PlaneWave`: 262 modules, about 213k lines. No module
contains `sorry`, and every main statement depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound` (`AxiomCheck.lean`, 1179 reports).

Contents:

- [Manuscript version and conventions](#manuscript-version-and-conventions)
- [Build](#build)
- [Layout](#layout)
- [Map from the manuscript to the Lean statements](#map-from-the-manuscript-to-the-lean-statements)
- [Scope and retained hypotheses](#scope-retained-hypotheses-and-statements-not-constructed)
- [Module index](#module-index)

## Manuscript version and conventions

This correspondence follows the corrected version 13 manuscript, with all standalone displayed
equations numbered (`plane_wave_error_bounds_v13_numbered.zip`, 23 October 2026). The tables use
LaTeX source labels, such as `eq:kinetic-grid-pairing`, rather than printed equation numbers.
Those labels are unchanged by the numbering update, so the existing correspondence remains
valid. The internal keys `cor:reslayer` and `prop:z3` label Lemmas; their prefixes are retained
for reference compatibility. Earlier-draft labels and labels from the separate completion note
are identified below.

The manuscript uses kets for abstract states and momentum-basis amplitudes
`u_k = ⟨k|u⟩`. Lean represents these states as functions or Hilbert-space elements, and some
formulas below retain that coordinate notation when describing declarations. A hat on a scalar
interaction kernel still denotes its Fourier coefficient.

The following conventions matter when matching the statements:

- In the periodic sections, `H` uses the zero-mean periodic Coulomb kernel `w` of `eq:w`.
  The isolated-system reference Hamiltonian `H_∞` uses the free-space interaction `1/|x|`.
  The range-truncated cell and grid Hamiltonians are distinguished below by whether they retain
  their common zero-mode scalar.
- The main manuscript uses an odd side length `n`, with `K = π(n − 1)/L`. In the finite-box
  subsection of Appendix G, including `thm:flux3`, `n` is instead the cube radius:
  `K = (2π/L)n` and the side length is `2n + 1`.
- Radial momentum tails use the Euclidean norm; cubical tails use the maximum norm.
  Since `{|k|_∞ > λ} ⊆ {|k|₂ > λ}`, a radial tail bound also controls the corresponding
  cubical tail, including after applying the diagonal kinetic weights.
- Lean's field `D.Xi` is the manuscript's unscaled data norm `𝒟`. The manuscript's
  `Ξ = C₀ m_max 𝒟` in Appendices C and G includes a common fixed-system regularity constant.
  This `C₀` is unrelated to the zero-mode shift denoted by `C₀` in the free-boundary modules.
- The asymptotic tables simplify additive constants in logarithms. The Lean endpoint bounds
  retain expressions such as `[1 + t + log(2 + K)]/K³` and their stated cutoff thresholds.

## Build

Requirements: the Lean toolchain manager `elan` (it installs Lean 4.32.1 from `lean-toolchain`)
and about 7 GB of memory. From the project root:

```powershell
lake exe cache get      # optional: download Mathlib's compiled files instead of building Mathlib
lake build              # compiles the 262 modules
.\scripts\check_axioms.ps1
```

or `scripts\build.ps1`, which runs `lake build`, saves its output in `build_log.txt` and then runs
the axiom check. Under bash: `bash scripts/build.sh` (or `lake build` and
`bash scripts/check_axioms.sh`). If Mathlib v4.32.1 is already built in another Lake project, its
`.lake/packages` folder can be copied (or linked) into this project instead of `lake exe cache get`.
The first `lake build` fetches Mathlib from GitHub if `.lake/packages` is missing.

`scripts/check_axioms.ps1` (and `.sh`) elaborates `AxiomCheck.lean`, writes the output to
`axiom_report.txt`, prints the number of reports and lists every report with an axiom other than
`propext`, `Classical.choice` and `Quot.sound` (for example `sorryAx`); it exits with code 1 if
there is one, or if elaboration fails.

The records below describe the reported Lean development builds. The version 13 documentation
update changes no Lean source and does not constitute a new build.

<details>
<summary>Recorded build history, 15–23 October 2026</summary>

Build record (2026-10-15, a 2-core machine with 7 GB of memory, Mathlib v4.32.1 prebuilt, Lean
4.32.1): `bash scripts/build.sh` with an empty `.lake/build` compiled the 208 modules of that
release in 44 minutes with no errors and no warnings (four `info` messages: `ring` suggesting
`ring_nf`), and the axiom check found 827 reports, all listing only `propext`, `Classical.choice`
and `Quot.sound`. On 2026-10-16 the eleven clamped-nuclei modules
(`PlaneWave.FreeBoundary.NuclearPotential` to `.FreeDynamicsBOUniform`) were added, and
`bash scripts/build.sh` compiled them on top of that build in about a minute with no errors and
no warnings (855 reports); then the three spin modules (`PlaneWave.FreeBoundary.SpinFreeStep` to
`.SpinFreeDynamicsEndpoint`) in the same way, in under a minute, with no errors and no warnings;
the axiom check found 869 reports, all listing only `propext`, `Classical.choice` and
`Quot.sound`. The four `ring` calls behind the `info` messages were then replaced by `ring_nf`
(`.Source.CutoffErrorConstant`, `.KineticCompletion.FirstRotationWords`, `.Auxiliary.DressedTails`),
and `bash scripts/build.sh` recompiled the 157 affected modules in 29 minutes with no errors, no
warnings and no `info` messages; the axiom check again found 869 reports, all standard.

On 2026-10-22 the 33 modules `PlaneWave.KineticLog.*` (the logarithmic kinetic-energy bounds)
were added. With an empty `.lake/build`, `bash scripts/build.sh` compiled all 255 modules in 63
minutes on the machine above, with no errors, no warnings and no `info` messages, and the axiom
check found 1005 reports (136 of them for `KineticLog`), all listing only `propext`,
`Classical.choice` and `Quot.sound`.

On 2026-10-23 seven modules were added in answer to an external review. Four are in
`PlaneWave.KineticLog`: `.PeriodicN`, `.PeriodicMasses`, `.OpenVbar` and `.OpenZeroMode`. They cover
the periodic endpoints in terms of `N` and for arbitrary positive masses, and the isolated-system
kinetic endpoints for profiles with `V_θ ≤ V̄` and for the physical cell and grid Hamiltonians with
their zero modes. Three are in `PlaneWave.FreeBoundary`: `.EnergyVbar`, `.DynamicsVbar` and
`.DynamicsZeroMode`. They extend `prop:free` (with the complexity statement) and `prop:free-dyn` to
profiles with `V_θ ≤ V̄`, and state `prop:free-dyn` for the physical Hamiltonians. No other source
file changed apart from `PlaneWave.lean` and `AxiomCheck.lean`. With the build outputs of the seven
modules removed, `bash scripts/build.sh` compiled them and the root on top of the 2026-10-22 build
in about 3 minutes, with no errors, no warnings and no `info` messages. The axiom check found 1179
reports (252 of them for `KineticLog`, 58 for the three new `FreeBoundary` modules), all listing
only `propext`, `Classical.choice` and `Quot.sound`. Every Lean name in the tables below
resolves (`#check`).
`PlaneWave.FreeBoundary.ObservableMomentsUniform` imports Mathlib's Fourier transform of Schwartz
functions; when Mathlib is built from source rather than downloaded, this adds about 46 Mathlib
modules (4 minutes on the machine above).

</details>

## Layout

| Module or folder | Modules | Lines | Contents |
|---|---|---|---|
| `PlaneWave.Certificate` | 1 | 56,203 | the ground-energy theorems (`thm:main`, `thm:nbo`) with polynomial constants; the propagators; `thm:dyn`, `cor:norm`; the kinetic-energy appendix (Galerkin); spin |
| `PlaneWave.GridCore` | 1 | 5,072 | the finite-dimensional grid core (`grid_galerkin_energy`); imports only Mathlib |
| `PlaneWave.Grid` | 1 | 17,075 | `thm:grid-energy`; `prop:fullkernel`; `prop:grid-dyn`, `thm:grid-dyn-sharp`; the kinetic energy on the grid; spin |
| `PlaneWave.Source` | 60 | 26,929 | the kinetic-energy source appendix: `thm:src1`, and the earlier normal-form route to `thm:src3`, `cor:stopping3` (spectral layer, normal form) |
| `PlaneWave.SourceBand` | 7 | 6,022 | the band bounds of the source side (`lem:band`, `prop:src-res`) |
| `PlaneWave.SamePair` | 8 | 2,986 | same-pair third order of the normal form (earlier-draft `lem:h3`, `lem:res3`; the generator) |
| `PlaneWave.Observable` | 2 | 1,063 | the second- and third-order observable corrections (earlier-draft `lem:obs2`, `lem:obs3`) |
| `PlaneWave.Flux` | 6 | 4,048 | the projection flux: `thm:flux`, `prop:elim`, `prop:phase`, `thm:flux2` |
| `PlaneWave.FluxBox` | 53 | 23,206 | the flux route in the box: `thm:flux3` |
| `PlaneWave.FluxSourceSpin` | 1 | 341 | the flux and source theorems on the spin-inclusive space |
| `PlaneWave.KineticCompletion` | 6 | 5,275 | the kinetic completion (`thm:completion` of the completion note): `thm:src3`, `cor:stopping3` unconditionally |
| `PlaneWave.Auxiliary` | 9 | 4,118 | auxiliary clauses and claims of the manuscript |
| `PlaneWave.FreeBoundary` | 70 | 40,487 | `app:free`: `lem:scaling`, eq:rangecut, `prop:free`, eq:free-energy, the complexity `N = O(ε⁻¹ log³(1/ε))`, `prop:free-dyn` (free-space step, with the propagator of `H_L`; grid step: `thm:grid-dyn-sharp` for `g_L`, also with `L`-uniform constants for `L ≥ 2π`; the two composed; for a fixed Schwartz observable, constants depending on `f` only; for the non-Born–Oppenheimer system, the domain condition `T(χψ_∞(0)) ∈ D(H_L²)` proved with `L`-free bounds, and the free-space regularity of `ψ_∞(0)` derived from `H_∞ψ_∞(0)`, `H_∞²ψ_∞(0) ∈ L²`; the torus version of the observable constructed; the endpoints in the form of the manuscript: `prop:free-dyn` with one constant for all `L ≥ L₀`, and `prop:free` from a free-space eigenfunction with Agmon decay and, for the lower bound, a torus ground state with (A); with clamped nuclei, the domain condition for cutoffs flat near the nuclei, derived from `H_∞ψ_∞(0)`, `H_∞²ψ_∞(0) ∈ L²`, and, for equal masses, `prop:free-dyn` with the product cutoff and one constant for all `L ≥ L₀`; with internal spin, `prop:free-dyn` for the spin-inclusive state, with the leakage summed over the spin components, the Hilbert norms and constants independent of the number of spin components); `prop:free`, the complexity and `prop:free-dyn` for profiles with `V_θ ≤ V̄`, and `prop:free-dyn` for the physical cell and grid Hamiltonians (zero modes kept) |
| `PlaneWave.KineticLog` | 37 | 20,197 | the logarithmic kinetic-energy bounds: `thm:kinetic-log` (Galerkin and grid, full kernel class), eq:kinetic-retained-galerkin, `cor:stopping-log`, with spin, for arbitrary positive masses and in terms of `N`; `prop:free-kinetic-log` (general cutoff with (H_dom), compatible and explicit cutoffs, spin), `cor:free-stopping-log`, eq:free-kinetic-N, for profiles with `V_θ ≤ V̄` and for the physical cell and grid Hamiltonians (zero mode kept, eq:free-zero-mode) |

`PlaneWave.lean` imports every module. The namespaces (`PlaneWaveCertificate`, `PlaneWaveGrid`,
`PlaneWaveDynamics`, `FSNormal`, `FreeBoundary`, ...) are those of the statements below.

## Map from the manuscript to the Lean statements

### Ground energy, grid energy, dynamics and the kinetic energy

| Manuscript | Lean | Module |
|---|---|---|
| `thm:main` (Born–Oppenheimer, electronic space with spin; in every exchange sector) | `PlaneWaveCertificate.periodicMolecularCubicError`, `periodicMolecularCubicConvergence`, `periodicMolecularCubicAccuracyOfBasisBudget`, `periodicMolecularCubicAccuracy`; the same with `Sector` | `PlaneWave.Certificate` |
| `thm:nbo` (quantum particles with masses `≥ 1`, any charges, fermions and bosons, static nuclei; spin-inclusive space and every exchange sector) | `PlaneWaveCertificate.periodicCoulombCubicError`, `periodicCoulombCubicConvergence`, `periodicCoulombCubicAccuracyOfBasisBudget`, `periodicCoulombCubicAccuracy`; the same with `Sector` | `PlaneWave.Certificate` |
| the constants and thresholds, polynomial in the data | `PlaneWaveCertificate.coulombDataCubicErrorConstant_le_coarse`, `coulombDataCubicThreshold_le_poly`, `molecularDataCubicErrorConstant_le_coarse`, `molecularDataCubicThreshold_le_poly` | `PlaneWave.Certificate` |
| `thm:grid-energy`, finite part | `PlaneWaveGrid.grid_galerkin_energy`, `isSecRitz_Hpos_iff` | `PlaneWave.GridCore` |
| `thm:grid-energy` (every kernel of `𝒦_K`; spin-inclusive space and every sector; Born–Oppenheimer case) | `PlaneWaveGrid.periodicCoulombGridError`, `periodicCoulombSectorGridError`, `periodicCoulombKernelGridError`, `periodicCoulombSectorKernelGridError`, `periodicMolecularGridError`, ... | `PlaneWave.Grid` |
| the grid constant and threshold, polynomial in the data | `PlaneWaveGrid.coulombGridErrorConstant_le_poly`, `coulombGridThreshold_le_poly` | `PlaneWave.Grid` |
| the propagators | `PlaneWaveDynamics.exists_coulombPropagator`, `exists_finitePropagator` | `PlaneWave.Certificate` |
| `thm:dyn` (eq:dyn-main, eq:dyn-simple) | `PlaneWaveDynamics.thm_dyn`, `thm_dyn_rates`, `thm_dyn_hchi`, `thm_dyn_simple`; with spin `thm_dyn_spin`, ... | `PlaneWave.Certificate` |
| `cor:norm` | `PlaneWaveDynamics.coulomb_observable_normalised`, `coulomb_normalisation_threshold` (and `_spin`) | `PlaneWave.Certificate` |
| `thm:mult-gal`, `thm:mult-cap` (for a fixed cap, eq:F-fixed-cap-gal), `cor:stopping`, `cor:stopping2` (Galerkin) | `PlaneWaveKinetic.thm_mult_gal`, `thm_mult_cap` (`kinetic_capped_error`), `stopping_galerkin`, `stopping_window`; with spin `PlaneWaveSpin.thm_mult_gal_spin`, ... | `PlaneWave.Certificate` |
| `prop:grid-dyn`, `thm:grid-dyn-sharp`, `cor:norm` on the grid | `PlaneWaveGridDynamics.thm_grid_dyn`, `thm_grid_dyn_min`, `thm_grid_dyn_sharp`, `thm_grid_dyn_sharp_min`, `grid_observable_normalised`, `grid_normalisation_threshold`; with spin `PlaneWaveSpin.thm_grid_dyn_spin`, ... | `PlaneWave.Grid` |
| `lem:grid-obs`, eq:obs-theta: the weighted observable bound and finiteness of its second Fourier moment under (Hχ) | `PlaneWaveGridDynamics.norm_wM_gridObs_le`, `PlaneWaveGridDynamics.summable_nsq_of_HChi` (see the constant comparison below) | `PlaneWave.Grid` |
| `prop:mult-grid`, `thm:mult-cap` (for a fixed cap, eq:F-fixed-cap-grid), `cor:stopping`, `cor:stopping2` (grid) | `PlaneWaveKinetic.thm_mult_grid`, `thm_mult_cap_grid` (`grid_capped_fixed_rate`), `stopping_grid`, `stopping_window_grid`; with spin | `PlaneWave.Grid` |
| `prop:fullkernel` | `PlaneWaveFullKernel.periodicCoulombSectorFullKernelError`, `periodicCoulombFullKernelError`, `periodicMolecularSectorFullKernelError`, `periodicMolecularFullKernelError`; the polynomial bounds `fullKernelErrorConstant_le_poly`, ... | `PlaneWave.Grid` |

The docstrings of `PlaneWave.Certificate` and `PlaneWave.Grid` state the hypotheses and the
conventions of these theorems in full; the sections named after former development files in those
two modules (for example `DevU15`) are the parts merged into them. In the docstrings of all modules,
"the release file" means `PlaneWave.Certificate` (and "the grid release file" `PlaneWave.Grid`).

For `prop:grid-dyn`, the corrected manuscript lists both `C_{χ,3}` and `C_{χ,5}` in the error
constant. The latter controls the high-frequency observable remainder in the `K^{-5}` term and
appears explicitly as `CM 5` in `PlaneWaveGridDynamics.thm_grid_dyn`. The cutoff threshold is
system/kernel dependent; no ground-state eigenvalue is an input to this dynamical proof.
The separate normalisation corollary retains its own initial-data-dependent threshold.

For `lem:grid-obs`, the manuscript uses a product-and-wrap estimate. The direct cyclic-shift
argument in `norm_wM_gridObs_le` instead uses the second Fourier moment `D'_χ`. The corrected
manuscript absorbs that moment using the `M = 3` tail in (Hχ):

`D'_χ ≤ 3(L/(2π))² (C_χ + 2C_{χ,3})`.

Thus `D'_χ` is no longer listed as an independent constant in `eq:obs-theta`, the backward-flow
budget `Ξ'_χ`, or `prop:grid-dyn`. Its definition `eq:Dchi-prime` is retained. Lean proves its
finiteness from (Hχ) in `summable_nsq_of_HChi`; the displayed quantitative absorption is a
manuscript calculation, not a separately exported Lean declaration.

### Flux, source and free boundary

| Manuscript | Lean | Module |
|---|---|---|
| `thm:flux` | `FSFlux.thm_flux` | `PlaneWave.Flux.ForceForm` |
| `prop:elim` | `FSFlux.thm_elim_bdry`, `FSFlux.thm_elim` | `PlaneWave.Flux.FluxDressing` |
| `prop:phase`, `thm:flux2` | `FSFlux.thm_phase`, `FSFlux.thm_flux2` | `PlaneWave.Flux.Flux2` |
| `thm:flux3` | `FSFlux.thm_flux3` | `PlaneWave.FluxBox.Flux3` |
| `thm:src1` | `FSSrc1.thm_src1` | `PlaneWave.Source.FirstSourceRound` |
| `thm:src3` (unconditional) | `FSAsymp.thm_src3_uncond` | `PlaneWave.KineticCompletion.Completion` |
| `cor:stopping3` (unconditional) | `FSAsymp.cor_stopping3_uncond` | `PlaneWave.KineticCompletion.Completion` |
| `thm:src3`, `cor:stopping3` from the completion conditions (the interface) | `FSAsymp.thm_src3`, `FSAsymp.cor_stopping3` | `PlaneWave.Source.Src3Conditional`, `PlaneWave.Source.Stopping3Conditional` |
| the completion: `Σ₃ = Σ₃^sp`, `R₃ = H₃^{res,sp} + H₃^mp` satisfy the conditions | `FSAsymp.completion` | `PlaneWave.KineticCompletion.Completion` |
| same-channel third order of the normal form (earlier-draft `lem:h3`, `lem:res3`; the generator) | `FSNormal.same_pair_package` | `PlaneWave.SamePair.Package` |
| the second- and third-order observable corrections (earlier-draft `lem:obs2`, `lem:obs3`; same-pair class) | `FSNormal.obs2`, `FSNormal.lem_obs3_sp` | `PlaneWave.Observable.SecondOrder`, `PlaneWave.Observable.ThirdOrderSamePair` |
| the six results above with spin | `FSSpin.thm_flux_spin`, `thm_flux2_spin`, `thm_flux3_spin`, `thm_src1_spin`, `thm_src3_spin`, `cor_stopping3_spin` | `PlaneWave.FluxSourceSpin` |
| `thm:src3`, `cor:stopping3` with spin (unconditional) | `FSSpin.thm_src3_spin_uncond`, `FSSpin.cor_stopping3_spin_uncond` | `PlaneWave.KineticCompletion.Completion` |
| `lem:scaling` (`app:free`; for any kernel satisfying eq:rangecut) | `FreeBoundary.scaling_low`, `scaling_tail`, `scaling_tail_tsum`, `scaling_moment2`, `scaling_moment4`, `slice_sobolev` | `PlaneWave.FreeBoundary.Scaling` |
| eq:rangecut for `g_L = θ(\|x\|)/\|x\|`: `\|ĝ_L(ν)\| ≤ (1 + V_θ) ŵ(ν)`, `\|ĝ_L(0)\| ≤ π/(2L)`, the radial Fourier integral; `lem:scaling` for `g_L` | `FreeBoundary.rangecut`, `ghat_zero_le_half`, `gFT_eq_sin`, `scaling_low_gL` … `scaling_moment4_gL` | `PlaneWave.FreeBoundary.RangeCut` |
| The `g_L` Hamiltonian on the cube (`app:free`, stage FB3): symmetric; `H¹`, mass-weighted and tail bounds by Fourier domination; the Galerkin energy bound `0 ≤ E_N - E`, `K³(E_N - E) ≤ C` | `FreeBoundary.gLham`, `gLpot_isSymmetric`, `gLpot_h1Bound`, `gLpot_massBound`, `gLpot_tail_bound`, `gL_eigen_fullH2Sq_le`, `gL_cubic_energy_bound` | `PlaneWave.FreeBoundary.CubeHamiltonian` |
| The grid core (`grid_galerkin_energy`) with a general real, even Galerkin reference kernel `γρ`, `\|ρ\| ≤ 1/\|ν\|²` (a copy of `PlaneWave.GridCore`) | `PlaneWaveGridG.grid_galerkin_energy`, `isSecRitz_Hpos_iff` | `PlaneWave.FreeBoundary.GridCoreGeneral` |
| The `g_L` torus ground energy `E_L` (infimum of the form over trigonometric polynomials of the sector) and the cubic Galerkin error `0 ≤ E_M - E_L ≤ C/K³` | `FreeBoundary.exists_gLTorusGroundEnergy`, `gL_cubic_error`, `gL_sector_cubic_error`, `gLham_eq_latticeKernel`, `transport_form` | `PlaneWave.FreeBoundary.TorusGroundEnergy` |
| `thm:grid-energy` for the range-truncated kernel (first step of `prop:free`): `\|E_{N,L} - E_L\| ≤ C/K³` for the grid method with kernel `(g_L)_{≤2K}` or any kernel of the class (zero mode left out on both sides) | `PlaneWaveGridG.gLSectorGridError`, `gLSectorKernelGridError` | `PlaneWave.FreeBoundary.GridEnergy` |
| The retained region (`g_L = 1/r` on `B_L`, so the `g_L` interaction is the free-space one there) and the torus Fourier coefficients of the position-space `g_L` (nearest-image definition) are `ĝ_L`, zero mode included | `FreeBoundary.retained_potential`, `gLni_eq_inv`, `niDist_eq_norm`, `mFourierCoeff_gLtorus`, `mFourierCoeff_gLtorus_zero` | `PlaneWave.FreeBoundary.RetainedRegion` |
| The `g_L` multiplication function on the configuration torus (zero mode removed) has exactly the potential lattice kernel of the Fourier-space `g_L` Hamiltonian; `g_L ∈ L²(T³)` | `FreeBoundary.gLFourierPotential_fourierCoeff`, `memLp_gLtorus`, `mFourierCoeff_gLtorus0` | `PlaneWave.FreeBoundary.PositionPotential` |
| The completed `g_L` Hamiltonian on `H²`; `E_L ‖ψ‖² ≤ Re⟨ψ, Hψ⟩` on the `H²` sector; its potential part is multiplication by the `g_L` function; for every `C²` periodic sector state `φ`, `E_L ‖φ‖² ≤ Re⟨φ, Kφ⟩ + Re⟨φ, Vφ⟩` | `FreeBoundary.exists_gLFourierH2Operator`, `gL_variational_H2`, `gLPositionPotentialH2_pointwise`, `gL_variational_C2` | `PlaneWave.FreeBoundary.CompletedHamiltonian` |
| `prop:free`, the transplant inequality: a `C²` free-space sector state `φ` supported in the retained region `B_{R_L}(0)^η` is carried to the torus (`φ(L·rep(x))`) with norm, kinetic and potential forms scaled by `L^{-3η}`; in the retained region the `g_L` function is the free-space Coulomb interaction minus the zero-mode shift `C₀`; hence `(E_L + C₀)‖φ‖² ≤ Re⟨φ, Kφ⟩ + ∫ V_∞\|φ\|²`, and `E_L + C₀ ≤ E_∞ + δ` when retained trial states reach `E_∞ + δ` | `FreeBoundary.integral_transplant`, `contDiffKinetic_transplant`, `gLFourierPotential_eq_freePot`, `free_transplant_bound`, `free_upper_of_trial` | `PlaneWave.FreeBoundary.Transplant` |
| With the grid theorem: `E_{N,L} + C₀ ≤ E_∞ + δ + C K^{-3}` | `FreeBoundary.free_grid_upper` | `PlaneWave.FreeBoundary.UpperComposite` |
| IMS localisation on `ℝ^{3η}` (Mathlib's integration by parts): `∫(Ku)ū = (1/2)Σ m⁻¹∫\|∂u\|²` for `u ∈ C²_c`; for `χ² + η² = 1`, `E(χφ) + E(ηφ) = E(φ) + (1/2)Σ m⁻¹∫((∂χ)² + (∂η)²)\|φ\|²`; a normalised state with energy `≤ E_∞ + ε` and outer mass `≤ τ` gives a retained trial state; hence `E_L + C₀ ≤ E_∞ + Mτ/(2(1-τ))` | `FreeBoundary.integral_freeKinetic_mul_conj`, `freeEnergy_ims`, `retained_trial`, `free_upper_ims` | `PlaneWave.FreeBoundary.IMS` |
| `prop:free`, upper bound: the localisation pair `cos/sin(π/2·T((\|r\|² - R₁²)/(R_L² - R₁²)))`, `M ≤ π²B²/w²`; if `E_∞` bounds the form on `C²_c` sector states and is approached by states with mass `≤ τ` outside `\|r\| < R_L - w` (Agmon: `τ = Ce^{-2α(R_L-w)}`), then `E_L + C₀ ≤ E_∞ + π²B²τ/(2w²(1-τ))` and `E_{N,L} + C₀ ≤ E_∞ + π²B²τ/(2w²(1-τ)) + CK^{-3}` | `FreeBoundary.stdLocPair`, `free_upper_agmon`, `free_grid_upper_agmon` | `PlaneWave.FreeBoundary.LocalisationPair` |
| IMS localisation on the configuration torus (the certificate's periodic integration of coordinate derivatives); the torus energy `torusEnergy`; `E_L ∫\|w\|² ≤ torusEnergy(w)` for `C²` sector states | `FreeBoundary.torus_kinetic_by_parts`, `torusEnergy_ims`, `torus_variational` | `PlaneWave.FreeBoundary.TorusIMS` |
| `prop:free`, lower bound under (A), and eq:free-energy: the reverse transplant (bump times periodic lift) and `torusEnergy(Tφ) = L^{-3η}(E(φ) - C₀‖φ‖²)`; if `E_L` is approached by normalised `C²` torus sector states with mass `≤ τ_A` outside `\|r\| < R_L - w`, then `E_∞ ≤ E_L + C₀ + Mτ_A/(2(1-τ_A))`; with the upper bound, `\|E_L + C₀ - E_∞\| ≤ δ` and `\|E_{N,L} + C₀ - E_∞\| ≤ δ + CK^{-3}`, `δ = π²B²/w²·max(τ/(2(1-τ)), τ_A/(2(1-τ_A)))` | `FreeBoundary.transplant_torusEnergy`, `free_lower_torus`, `free_grid_two_sided`, `free_grid_exponential` | `PlaneWave.FreeBoundary.LowerBound` |
| `L`-uniform constants, the grid core: the comparison `\|E_grid - E_gal\| ≤ C/K³` (`K = g s`) with the physical weight `1 + g²Σ\|ν_a\|²`, the Sobolev sum `Σ_ν (1 + g²\|ν\|²)⁻² ≤ 1 + 78/g³` and a coupling `m̄ Z_c ≤ z g`; the constants depend on `z`, `σ ≥ g³ + 78` and the energy budget, not on `g` | `PlaneWaveGridG.sum_sobolevP_le`, `grid_galerkin_energyP` | `PlaneWave.FreeBoundary.UniformGridCore` |
| `L`-uniform constants, the cubic error: the certificate's high-pass and tail bounds with `1 + 78/g³ ≤ C_s²` (the certificate: `1 + 108/g⁴`), so `C_s B_ker` is bounded in `L`; the `g_L` tail bound, Galerkin energy bound and cubic error with this constant | `PlaneWaveCertificate.finitePlaneWave_hasOneParticleInverseH2WeightBoundP`, `FreeBoundary.gL_sector_cubic_errorP` | `PlaneWave.FreeBoundary.UniformCubic` |
| `thm:grid-energy` for `g_L` with `L`-uniform constants: for `L ≥ 2π`, an energy budget `E_b ≥ \|E_L\| + 1`, `m ≥ η + 8` and `K = (2π/L) m ≥ K₀(E_b)`: `\|E_{N,L} - E_L\| ≤ C(E_b)/K³`, with `K₀` and `C` independent of `L` | `PlaneWaveGridG.gLSectorKernelGridErrorU`, `gLSectorGridErrorU` | `PlaneWave.FreeBoundary.UniformGridEnergy` |
| eq:free-energy with the `L`-uniform grid constant: `\|E_{N,L} + C₀ - E_∞\| ≤ δ + C(E_b)K^{-3}` and `≤ C′e^{-γL} + C(E_b)K^{-3}` for `L ≥ 2π` | `FreeBoundary.free_grid_two_sidedU`, `free_grid_exponentialU` | `PlaneWave.FreeBoundary.UniformFreeEnergy` |
| `prop:free` and eq:free-energy in the manuscript's product geometry: the localisation pair `cos/sin(π/2·(1 - ∏_i(1 - T((\|r_i\|² - R₁²)/(R_L² - R₁²)))))`, equal to `1` when every particle lies in `B_{R₁}(0)` and to `0` as soon as one leaves `B_{R_L}(0)`, gradient constant `ηπ²B²/w²`; all the bounds above with the mass hypotheses (Agmon decay, and (A)) on the complement of the product region `{every particle in B_{R_L - w}(0)}` and `π²B²/w²` replaced by `ηπ²B²/w²` | `FreeBoundary.prodLocPair`, `prodTorusLocPair`, `free_upper_agmon_prod`, `free_grid_two_sided_prod`, `free_grid_exponential_prod`, `free_grid_exponentialU_prod` | `PlaneWave.FreeBoundary.ProductLocalisation` |
| `prop:free`, the complexity: for the molecule in cells of size `L ≥ L₀ ≥ 2π` under the hypotheses of eq:free-energy for every such `L` (profiles of fixed total variation, Agmon decay at every radius, (A) in the product geometry), there is `D` such that for every `0 < ε ≤ 1/2` a cell size `L` and register radius `2m` with `N = (4m+1)³ ≤ Dε⁻¹log³(1/ε)` grid points per particle give `\|E_{N,L} + C₀ - E_∞\| ≤ ε`; the arithmetic for any approximation family with the rate `C′e^{-γL} + CK^{-3}`; `\|C₀\| ≤ Qπ/(2L)` | `FreeBoundary.free_grid_complexity_prod`, `complexity_of_rate`, `abs_zeroModeShift_re_le` | `PlaneWave.FreeBoundary.Complexity` |
| `prop:free-dyn`, free-space step: for any propagator `U` of `H_L`, under (H_leak) `‖φ(t) − e^{−iC₀t}U(t)φ(0)‖ ≤ Cεt`, `φ = T(χψ_∞)`, and the multiplier-observable comparison `≤ ε² + (‖ψ_∞(t)‖ + ‖ψ_∞(0)‖)Cεt` | `FreeBoundary.free_dyn_torus`, `transplant_hasGLHamiltonian`, `duhamel_phase` | `PlaneWave.FreeBoundary.Dynamics` |
| `prop:free-dyn`, the propagator of `H_L`: the strongly continuous unitary group generated by the completed `g_L` operator; the free-space step for it | `FreeBoundary.exists_gLPropagator`, `free_dyn_gL` | `PlaneWave.FreeBoundary.Propagator` |
| `prop:free-dyn`, grid step: `thm:grid-dyn-sharp` for the `g_L` kernel, `\|⟪ψ(t), χ(x_a)ψ(t)⟫ − ⟪ψ_g(t), O_gψ_g(t)⟫\| ≤ (A₁ + (A₃3^{5/2} + ‖ψ₀‖²)C_{χ,5})K⁻⁵ + A₂tK⁻³` for `ψ₀ ∈ D(H_L²)` and kernels of the class with reference `ĝ_L`; the continuum interface of the release's proof for `H_L` | `FreeBoundary.thm_grid_dyn_sharp_gL`, `grid_observable_position_sharp_gL`, `grid_observable_rate_sharp_gL`, `regCoeff_H_eq_grid_gL`, `tails_at_time_gL` | `PlaneWave.FreeBoundary.GridDynamicsTheorem`, `GridDynamicsSharp`, `GridDynamicsInterface` |
| `prop:free-dyn`, the two steps composed: `\|∫ f(r_a)\|ψ_∞(t)\|² - ⟨ψ_g(t), O_gψ_g(t)⟩\| ≤ ε² + (‖ψ_∞(t)‖ + ‖ψ_∞(0)‖)Cεt + (A₁ + (A₃3^{5/2} + ‖φ(0)‖²)C_{χ,5})K⁻⁵ + A₂tK⁻³`, with the domain condition `φ(0) = T(χ_𝓑ψ_∞(0)) ∈ D(H_L²)` as a hypothesis and a one-particle observable | `FreeBoundary.free_dyn_grid_gL`, `grid_dyn_sharp_gL_of_propagator` | `PlaneWave.FreeBoundary.FreeDynamicsGrid` |
| `prop:free-dyn`, grid step, `L`-uniform first-order estimates: the `g_L` grid Hamiltonian in physical units (weight `w_g = 1 + Σ_b \|gν_b\|²/m_b`): `26 Z J₀ ≤ A = gLAU` `L`-free, `‖H_grid v‖ ≤ (5/8)‖w_g v‖ + A‖v‖`, `‖w_g v‖ ≤ (8/3)‖H_grid v‖ + (4/3)(1 + 2A)‖v‖`, `‖w_g U(t)v‖ ≤ (5/3)‖w_g v‖ + (4/3)(1 + 4A)‖v‖`, the collocated observable in `w_g`; `A₁`, `A₃` of the polynomial-`L` theorem bounded uniformly | `FreeBoundary.gLGridA_le_U`, `gridGraphNorm_gL`, `norm_wPhys_gridFlow_le_gL`, `norm_wPhys_gridObs_le`, `gridConstsSharp_gL_one_le_U` | `PlaneWave.FreeBoundary.GridDynamicsUniform` |
| `prop:free-dyn`, grid step with `L`-uniform constants: for `L ≥ 2π`, `m ≥ 8`, `K ≥ 8`, `\|⟪ψ(t), χ(x_a)ψ(t)⟫ − ⟪ψ_g(t), O_gψ_g(t)⟫\| ≤ (A₁ + (A₃3^{5/2} + ‖ψ₀‖²)C_{χ,5})K⁻⁵ + A₂tK⁻³` with `(A₁, A₂, A₃) = gridConstsPosU` independent of `L`; the two steps composed with these constants; the second-order estimates, second moments, duality and rates in the physical weight | `FreeBoundary.thm_grid_dyn_sharp_gLU`, `free_dyn_grid_gLU`, `grid_observable_rate_sharp_gLU`, `second_ellipticP`, `second_moment_regCoeff_le_gLU`, `grid_duality_shell_gLU` | `PlaneWave.FreeBoundary.GridDynamicsUniformTheorem`, `GridObservablePhysical`, `GridSecondMomentPhysical`, `GridSecondOrderPhysical` |
| `prop:free-dyn` for a fixed Schwartz observable `f`, `0 ≤ f ≤ 1`, vanishing outside the ball of radius `R_f`, `L ≥ 2π`, `L > 2R_f`: the composed bound with `(A₁, A₂, A₃)` and `C_{χ,5}` functions of the system, `V_θ`, the data and `f` only; `χ̂(ν) = L⁻³ f̂(ν/L)`; `Σ\|χ̂\| ≤ 27B₆`, `g²Σ\|ν\|²\|χ̂\| ≤ 27(2π)²B₈`, `g⁴Σ\|ν\|⁴\|χ̂\| ≤ 27(2π)⁴B₁₀`, `C_{χ,M} = 27(2π)^M B_{M+6}` with `B_N = sup_ξ(1+\|ξ\|)^N\|f̂(ξ)\|` | `FreeBoundary.free_dyn_grid_gLU_schwartz`, `free_dyn_grid_gLU_decay`, `gridConstsPosU_le_of_decay`, `CellDecay.hChi`, `mFourierCoeff_cell`, `tsum_latWeight_le` | `PlaneWave.FreeBoundary.ObservableMomentsUniform` |
| `prop:free-dyn`, the domain condition, non-Born–Oppenheimer (no clamped nuclei; masses `m_i ≥ 1`, charges `q_i`): for a cutoff `χ` in the retained region with derivatives of orders 1 to 4 bounded by `D` and the mass-weighted cancellation `\|∇_iχ/m_i - ∇_jχ/m_j\| ≤ C\|x_i - x_j\|`, and `\|C₀\| ≤ c₀`: `φ = T(χu)` satisfies `H_Lφ = h₀`, `H_Lh₀ = h₁` with `‖φ‖ ≤ N`, `‖h₀‖ ≤ ΛN`, `‖h₁‖ ≤ Λ²N`; `N` is the free-space data norm of `u = ψ_∞(0)` (`u`, `H_∞u`, `H_∞²u`, `∇u`, `∇H_∞u`, `∇²u`, `u/\|x_i - x_j\|`) and `Λ = 1 + c₀ + 6(1 + 3η)²D + CΣ_{i<j}\|q_iq_j\|`; the singular part of `[V, [K, χ]]` is `Σ_{i<j} β_{ij}/\|x_i - x_j\|` with `\|β_{ij}\| ≤ \|q_iq_j\|C` | `FreeBoundary.cut_state_domain`, `commT_hasGLHamiltonian`, `freeId_comm`, `singular_identity`, `DomCutoff.abs_commBeta_le` | `PlaneWave.FreeBoundary.CutStateDomain`, `CommutatorTransplant`, `SecondCommutator`, `SingularCommutator`, `MassWeightedCutoff`, `DomainWeakCalculus` |
| `prop:free-dyn` without the domain hypothesis, non-Born–Oppenheimer: the bound of `free_dyn_grid_gLU_schwartz` with `(A₁, A₂, A₃) = gridConstsSharp_gLU` at the data `(N, ΛN, ΛN, Λ²N)`, `c₀ = Q/4` and cutoff bounds `D ≤ D̄`, `C ≤ C̄`, and the commutator constant `3η·(3/2)D̄`: all `L`-free; mass-weighted cutoffs at `L = 8s`, `s ≥ 1`, with `D_s = D/s`, `C_s = C/s²`: `χ_s(r) = F(Σ_i m_i\|x_i\|²/s²)`, `F = 1` on `[0, 1]`, `F = 0` on `[2, ∞)` | `FreeBoundary.free_dyn_grid_nbo`, `gridConstsSharp_gLU_mono_data`, `norm_zeroModeShift_le`, `DomCutoff.scale`, `exists_quadCutoff` | `PlaneWave.FreeBoundary.FreeDynamicsNonBO`, `CutoffScaling` |
| `prop:free-dyn`, the torus version of the observable: for `f` continuous and vanishing outside the ball of radius `R_f < L/2`, `χ(t) = f(L·rep t)` (`rep t ∈ (-1/2, 1/2]³`) is continuous on the torus, `χ(x_a) = f((L·rep x)_a)`; the statements above with this `χ` constructed rather than assumed | `FreeBoundary.cellObs`, `continuous_cellRep_comp`, `cellObs_particle`, `free_dyn_grid_gLU_schwartz_cell`, `free_dyn_grid_gLU_decay_cell`, `free_dyn_grid_nbo_cell` | `PlaneWave.FreeBoundary.CellObservable` |
| `prop:free-dyn`, the free-space regularity of `ψ_∞(0)` (non-Born–Oppenheimer): from `H_∞u = h`, `H_∞h = k`, weak first and second derivatives with `Σ_a m_a⁻¹‖∂_au‖² ≤ 2‖u‖‖z‖` and `Σ_{a,b} m_a⁻¹m_b⁻¹‖∂_a∂_bu‖² = 4‖z‖²` (`z = h − Vu`); Hardy's inequality `‖f/\|x_i − x_j\|‖² ≤ 4Σ_c‖∂_{(i,c)}f‖²` for `f ∈ L²` with a weak gradient; `dataNorm ≤ C_sys(‖u‖ + ‖h‖ + ‖k‖)`; the domain theorem and `prop:free-dyn` from the Hamiltonian relations alone, with constants in `‖ψ₀‖ + ‖H_∞ψ₀‖ + ‖H_∞²ψ₀‖` | `FreeBoundary.weak_kinetic_regularity`, `hardy_weak`, `HasWeakGrad.unique`, `free_hamiltonian_regularity`, `free_data_regularity`, `cut_state_domain_reg`, `free_dyn_grid_nbo_reg` | `PlaneWave.FreeBoundary.Mollification`, `KineticRegularity`, `HardyInequality`, `RegularityBridge` |
| `prop:free-dyn` in the form of the manuscript: the norm is conserved along a solution curve of `H_∞` (`⟨f, H_∞f⟩` is real); the bound `C[K⁻⁵ + tK⁻³] + C(1 + t)ε` for `0 ≤ ε ≤ 1` with `C` independent of `L` (any system with the domain condition as a hypothesis; without clamped nuclei from `‖ψ(0)‖ + ‖H_∞ψ(0)‖ + ‖H_∞²ψ(0)‖ ≤ D`); for every `L ≥ L₀ = max(8, 2π, 2R_f + 1, 16(R₀ + ρ))`, with the cutoff `F(Σ_i m_i\|x_i\|²/(L/8)²)`, its leakage regions, the cell observable and every kernel of the class, one constant, for the molecule in every cell (`sysAt sys P L`); the constants read only the masses and charges | `FreeBoundary.norm_conserved`, `free_dyn_endpoint`, `free_dyn_nbo_endpoint`, `free_dyn_uniform`, `free_dyn_nbo_uniform`, `freeDynConst_sysAt` | `PlaneWave.FreeBoundary.FreeDynamicsEndpoint` |
| `prop:free-dyn`, the domain condition with clamped nuclei (nuclei at `P_ℓ` with charges `Z_ℓ`, `V = Σ_{i<j} q_iq_j/\|x_i - x_j\| + Σ_{i,ℓ} q_iZ_ℓ/\|x_i - P_ℓ\|`): `Vu`, `V∂_au` are sums of pair and nuclear Hardy functions; for a mass-weighted cutoff flat near the nuclei (`∂_{(i,c)}χ(r) = 0` whenever `\|x_i - P_ℓ\| < δ`), the nuclear part of `-Σ_a m_a⁻¹∂_aχ∂_aV` is bounded by `Σ_{i,ℓ}\|q_iZ_ℓ\|\|∂_aχ\|/δ²` and its weak identity holds (regularised interaction, dominated convergence); `φ = T(χu)` satisfies `H_Lφ = h₀`, `H_Lh₀ = h₁` with `‖φ‖ ≤ N`, `‖h₀‖ ≤ Λ′N`, `‖h₁‖ ≤ Λ′²N`, `Λ′ = Λ + 3ηDΣ_{i,ℓ}\|q_iZ_ℓ\|/δ²`; from `H_∞u = h`, `H_∞h = k` alone, `N ≤ c′(‖u‖ + ‖h‖ + ‖k‖)` with `c′` depending only on the masses, the charges and `η` | `FreeBoundary.cut_state_domain_nuc`, `cut_state_domain_reg_nuc`, `commT_hasGLHamiltonian_nuc`, `nuc_singular_identity`, `free_hamiltonian_regularity_nuc`, `free_data_regularity_nuc`, `hasL2PointwisePotential_pair_nucL2` | `PlaneWave.FreeBoundary.NuclearPotential`, `NuclearRegularity`, `NuclearSingularIdentity`, `NuclearCommutator`, `CutStateDomainNuclear`, `RegularityBridgeNuclear` |
| `prop:free-dyn` with clamped nuclei in the form of the manuscript: for a cutoff flat near the nuclei, the bound `C[K⁻⁵ + tK⁻³] + C(1 + t)ε` from `‖ψ(0)‖ + ‖H_∞ψ(0)‖ + ‖H_∞²ψ(0)‖ ≤ D`, `C` depending on the system, `V_θ`, `f`, `D`, the cutoff bounds and `δ`; for equal masses `m_i = m₀ ≥ 1` the product cutoff `Π_i q(x_i)` (`q = 1` on `B_1(0)`, `0` outside `B_2(0)`) is mass-weighted (exchange symmetry) and flat in `x_i` where `\|x_i\| < 1`; scaled to `Π_i q(16x_i/L)`, with leakage measured where some `\|x_i\| ≥ L/16` and gradient leakage on `{some \|x_i\| ≥ L/16, every \|x_i\| ≤ L/8}`, one constant for every `L ≥ L₀ = max(16, 2R_f + 1, 16(R₀ + ρ + δ))`, nuclei in `B_{R₀}(0)` | `FreeBoundary.free_dyn_grid_bo`, `free_dyn_bo_uniform`, `exists_prodCutoff`, `prodChi_isFlatNear`, `DomCutoff.scale_isFlatNear`, `prodCutoffL_derivs` | `PlaneWave.FreeBoundary.FreeDynamicsBO`, `FreeDynamicsBOUniform`, `ProductCutoff`, `ProductCutoffCancellation`, `ProductCutoffRegions` |
| `prop:free-dyn` with internal spin (`L²(ℝ^{3η}) ⊗ ℂ^ς`, one component for each spin configuration, the Hamiltonian acting on each component): with the leakage summed over the spin components, `Σ_σ‖1_{(B^one)ᶜ}Ψ_σ‖² ≤ ε²` and `Σ_σ‖1_S∇Ψ_σ‖² ≤ ε²`, the free-space step gives `ε² + (‖Ψ(t)‖ + ‖Ψ(0)‖)Cεt` with the Hilbert norms and `C = 3η(D₁ + D₂/2)`; the grid step acts on each component with one grid flow, and its error, quadratic in the component, is at most `N_σ²` times its value at the unit data `(1, Λ, Λ²)`; the bound `C[K⁻⁵ + tK⁻³] + C(1 + t)ε` from `‖Ψ₀‖ + ‖H_∞Ψ₀‖ + ‖H_∞²Ψ₀‖ ≤ D`, without and with clamped nuclei, with one constant for all `L ≥ L₀`; no constant depends on the number of spin components | `FreeBoundary.free_dyn_torus_spin`, `free_dyn_grid_spin`, `norm_le_sq_mul_of_unit`, `norm_conserved_spin`, `free_dyn_nbo_spin_endpoint`, `free_dyn_bo_spin_endpoint`, `free_dyn_nbo_spin_uniform`, `free_dyn_bo_spin_uniform` | `PlaneWave.FreeBoundary.SpinFreeStep`, `SpinFreeDynamicsGrid`, `SpinFreeDynamicsEndpoint` |
| `prop:free`, approximation in the form norm: Hardy's inequality `‖f/\|Y\|‖² ≤ 4Σ_c‖∂_{(i,c)}f‖²` for `Y = x_i - x_j` and for `Y = x_i - R` (`R` a nucleus); the Coulomb form `∫V_∞\|f\|²` is continuous in the form norm; an `L²` function of an exchange sector with a weak gradient is the form-norm limit of smooth functions of compact support of the same sector, `χ_n·(σ_n ⋆ ψ)` with `σ_n` a product of one-particle mollifiers | `FreeBoundary.hardy_weak_aff`, `hardy_nuc`, `coulomb_sub_le`, `tendsto_integral_freePot`, `moll_freeSwap`, `apprN_tendsto` | `PlaneWave.FreeBoundary.HardyNuclear`, `CoulombForm`, `FormApproximation` |
| `prop:free`, near-minimisers from the ground states: if `H_∞ψ = E_∞ψ`, `‖ψ‖ = 1`, `ψ` is in the sector and `Σ_i ∫e^{2α\|x_i\|}\|ψ\|² ≤ A`, then for every `ε > 0` some normalised `C²` sector state of compact support has energy `≤ E_∞ + ε` and mass `≤ 2max(A, 1)e^{-2αR}` outside `{every \|x_i\| < R}`; on the torus, an `H²` state `u_L` of the sector with `‖u_L‖ = 1` and `Re⟨u_L, Hu_L⟩ ≤ E` (`H` the completed `g_L` operator) and `Σ_i ∫e^{2β(\|x_i\| - R′)}\|u_L\|² ≤ A′` gives, through its Fourier truncations, normalised `C²` sector states with torus energy `≤ E + ε` and mass `≤ 2max(A′, 1)e^{-2β(d - R′)}` outside `{every \|x_i\| < d}` | `FreeBoundary.eigen_energy`, `approx_ground`, `approx_ground_agmon`, `torusEnergy_eq_form`, `approx_torus_ground`, `approx_torus_agmon` | `PlaneWave.FreeBoundary.AgmonApproximation`, `TorusApproximation` |
| `prop:free` in the form of the manuscript (nuclei at `P_ℓ ∈ B_{R₀}(0)`, cells of size `L ≥ L₀`, `L₀` explicit): under the free-space ground-state and localisation hypotheses, without assumption (A), `E_L + C₀ ≤ E_∞ + C′e^{-αL/2}` and `E_{N,L} + C₀ ≤ E_∞ + C′e^{-αL/2} + CK^{-3}` for `K ≥ K₀` (with `E_L ≥ -(B² + 1/4)`, `B` independent of `L ≥ 2π`); under (A) for the torus ground state, `Σ_i ∫e^{2β(\|x_i\| - R_{L/2})}\|u_L\|² ≤ A′` (implied by `‖e^{β dist(·, 𝓑_{L/2})}u_L‖ ≤ C` with `A′ = ηC²`), eq:free-energy `\|E_L + C₀ - E_∞\| ≤ C′e^{-γL}` and `\|E_{N,L} + C₀ - E_∞\| ≤ C′e^{-γL} + CK^{-3}` for `K ≥ K₀`, `γ = min(α, β/2)/2`, and the complexity `N = O(ε⁻¹log³(1/ε))`; `L₀`, `C′`, `γ`, `K₀`, `C` independent of `L` | `FreeBoundary.free_energy_upper`, `gLTorusGroundEnergy_ge`, `free_energy_endpoint`, `free_energy_complexity`, `approx_torus_prod` | `PlaneWave.FreeBoundary.FreeEnergyEndpoint` |
| `prop:free`, eq:free-energy and the complexity `N = O(ε⁻¹log³(1/ε))` for profiles with `V_θ ≤ V̄`: the thresholds and constants at `V̄` (they are increasing in `V` and in the energy budget); the kernel class keeps the majorant of the actual profile | `FreeBoundary.gLKThresholdU_mono`, `gLErrorConstU_mono`, `freeUpperBudget_mono`, `gLSectorKernelGridErrorU_vbar`, `gLSectorGridErrorU_vbar`, `gLTorusGroundEnergy_ge_vbar`, `free_grid_two_sidedU_vbar`, `free_grid_exponentialU_vbar`, `free_grid_two_sidedU_prod_vbar`, `free_grid_exponentialU_prod_vbar`, `free_energy_upper_vbar`, `free_energy_endpoint_vbar`, `free_energy_complexity_vbar`, `free_grid_complexity_prod_vbar` | `PlaneWave.FreeBoundary.EnergyVbar` |
| `prop:free-dyn` for profiles with `V_θ ≤ V̄`: the constants at `V̄` (the grid constants `(A₁, A₂, A₃)` are increasing in `V`), for every endpoint in the form of the manuscript (general cutoff with (H_dom), compatible cutoffs, explicit cutoffs uniform in `L`, spin) | `FreeBoundary.gridConstsSharp_gLU_mono_V`, `freeDynConst_mono`, `freeDynConstNBO_mono`, `freeDynConstBO_mono`, `freeDynConstSpinNBO_mono`, `freeDynConstSpinBO_mono`, `free_dyn_endpoint_vbar`, `free_dyn_nbo_endpoint_vbar`, `free_dyn_grid_bo_vbar`, `free_dyn_uniform_vbar`, `free_dyn_nbo_uniform_vbar`, `free_dyn_bo_uniform_vbar`, `free_dyn_nbo_spin_endpoint_vbar`, `free_dyn_bo_spin_endpoint_vbar`, `free_dyn_nbo_spin_uniform_vbar`, `free_dyn_bo_spin_uniform_vbar` | `PlaneWave.FreeBoundary.DynamicsVbar` |
| `prop:free-dyn` for the physical Hamiltonians (eq:free-zero-mode, eq:free-kinetic-kernel: the zero modes kept in the cell and on the grid), with `V_θ ≤ V̄`: `G[κ] = G[κ⁰] + κ(0)z_g`; every propagator of the physical grid Hamiltonian is `e^{-itC₀}` times every propagator of the zero-mode-free one; the free-space step `‖φ(t) - e^{-itH_L}φ(0)‖ ≤ Cεt` for the physical `H_L`; (H_dom) for the physical `H_L` with budget `𝒟` gives the budget `(1 + Q/4)²𝒟`; the endpoints for every propagator of the physical grid Hamiltonian | `FreeBoundary.Hpos_update`, `Hpos_isSymmetric`, `posProp_phase`, `posProp_phase_zeroMode`, `exists_posPropagatorZ`, `cell_unphase`, `free_dyn_torus_phys`, `free_dyn_torus_spin_phys`, `budget_zero_mode_each`, `free_dyn_endpoint_phys`, `free_dyn_nbo_endpoint_phys`, `free_dyn_grid_bo_phys`, `free_dyn_uniform_phys`, `free_dyn_nbo_uniform_phys`, `free_dyn_bo_uniform_phys`, `free_dyn_nbo_spin_endpoint_phys`, `free_dyn_bo_spin_endpoint_phys`, `free_dyn_nbo_spin_uniform_phys`, `free_dyn_bo_spin_uniform_phys` | `PlaneWave.FreeBoundary.DynamicsZeroMode` |

The spin versions hold for any finite set of spin configurations, with the spin-inclusive data norm
`‖Ψ₀‖ + ‖HΨ₀‖ + ‖H²Ψ₀‖` and the constants of the spinless theorems. In `thm_src3_spin` and
`cor_stopping3_spin` the completion hypotheses are on the spatial `Σ₃`, `R₃`, so the spin-inclusive
generator and residual are `Σ₃ ⊗ 1` and `R₃ ⊗ 1`.

The completion discharges the additional normal-form conditions in the earlier source theorems;
the system and initial-data hypotheses still apply. These endpoint declarations state: for every
`ε > 0` there are `C_ε` and `N₀` such that for every cutoff
`n ≥ N₀`, every datum and every `t ≥ 1` (every window `T ≥ 1` for the stopping power),
`|⟨ψ(t), A_{p₀} ψ(t)⟩ - ⟨ψ_N(t), A_{p₀} ψ_N(t)⟩| ≤ C_ε Ξ² (1 + t) K^{-3+ε}` and
`|ΔŜ| ≤ C_ε Ξ²/v_p (K^{-3+ε} + K^{-3+ε}/T)`.

The manuscript derives `thm:src3` and `cor:stopping3` from `thm:kinetic-log` and
`cor:stopping-log` by absorbing `log(2 + K)` into `K^ε`. The Lean proofs above take an earlier
route, through the normal form of the source appendix and the completion; the stronger logarithmic
forms are proved separately (`PlaneWave.KineticLog`, below). Labels marked "earlier-draft" here, in
the auxiliary tables and in the module index are those of the earlier version of the source
appendix. They do not occur in the current manuscript; the module docstrings keep them.

The manuscript retains the earlier displayed ranges `t ≥ 1` and `τ ≥ 1` to match these endpoint
declarations, but now explicitly notes the stronger consequences for every `t ≥ 0` and every
`τ > 0`. They follow from the logarithmic results using
`1 + t + log(2 + K) ≤ (1 + t)[1 + log(2 + K)]` and
`1 + log(2 + K) ≤ C_ε K^ε`. No extension of the older declarations is being asserted here;
the wider ranges are consequences of the separately proved logarithmic theorems.

### The kinetic completion (`PlaneWave.KineticCompletion`)

| Completion note (`kinetic_energy_completion.tex`) | Lean | File |
|---|---|---|
| `lem:relativeD` (eq:Drelative), as the two Schur sums with the weight `Λ⁻¹`, uniform in the centre | `FSLattice.inv_mismatch_row`, `inv_mismatch_col` | `PlaneWave.KineticCompletion.InverseMismatch` |
| `lem:transverse` | `FSNormal.exists_dir`, `lam_mul_le` | `PlaneWave.KineticCompletion.CrossCommutators` |
| eq:Zdirection, `‖Z_j Λ_d⁻¹‖ ≤ C K⁻³ log² K` | `FSNormal.norm_Zj_le` | `PlaneWave.KineticCompletion.CrossCommutators` |
| eq:directionHardy | `FSNormal.dir_hardy` | `PlaneWave.KineticCompletion.CrossCommutators` |
| `lem:crosscomm` | `FSNormal.norm_crossX_le` | `PlaneWave.KineticCompletion.CrossCommutators` |
| `lem:separation` | `FSNormal.sep_inP`, `fA_eq_zero`, `fB_eq_zero`, `fC_eq_zero` | `PlaneWave.KineticCompletion.FirstRotationWords` |
| eq:Sdirection (as Schur sums), eq:H3fexact (the word expansion) | `FSNormal.row_sig_lam`, `h3fW_eq` | `PlaneWave.KineticCompletion.FirstRotationWords` |
| `prop:mp`, `‖H₃^mp u‖ ≤ C K⁻³ log² K ‖(1+A)u‖` | `FSNormal.norm_H3mp_le` | `PlaneWave.KineticCompletion.FirstRotationWords` |
| `lem:weighted`, for `\|α\| ≤ 1/2` | `FSNormal.norm_wt_Sig3sp_le` | `PlaneWave.KineticCompletion.QuarterPowerWeights` |
| eq:completionweighted on good states (budget `M`) | `FSNormal.weighted_Sig3sp_good` | `PlaneWave.KineticCompletion.QuarterPowerWeights` |
| `thm:completion` | `FSAsymp.completion` | `PlaneWave.KineticCompletion.Completion` |
| the corollary (both endpoints, with and without spin) | `FSAsymp.thm_src3_uncond`, `cor_stopping3_uncond`, `FSSpin.thm_src3_spin_uncond`, `cor_stopping3_spin_uncond` | `PlaneWave.KineticCompletion.Completion` |
| `comp:lem:relativeD` in its general form (any finite set in a ball, complex dominated matrices) | `FSLattice.relativeD`, `relativeD_log` | `PlaneWave.KineticCompletion.CompletionClauses` |
| eq:formW, `‖E^{-1/4} W_N E^{-1/4}‖ ≤ C` (by a lattice Kato bound, not by interpolation) | `FSNormal.form_VN_le`, `norm_formW_le` | `PlaneWave.KineticCompletion.CompletionClauses` |
| eq:completionweighted for every `u` (the `E^{±1/4}` form) | `FSNormal.weighted_Sig3sp_E14` | `PlaneWave.KineticCompletion.CompletionClauses` |
| `R₃* = R₃` | `FSNormal.inner_R3` | `PlaneWave.KineticCompletion.CompletionClauses` |
| eq:Sdirection as operator norms | `FSNormal.norm_Sj_le`, `norm_Sj_lam_le`, `FSAsymp.Sdirection_orders` | `PlaneWave.KineticCompletion.CompletionClauses` |
| `comp:thm:completion` with every clause | `FSAsymp.completion_full` | `PlaneWave.KineticCompletion.CompletionClauses` |

Differences from the note: the powers of `log K` are not tracked (some fixed `q`, absorbed into
`K^ε`); `comp:lem:weighted` is proved for `|α| ≤ 1/2`. The interface (`FSAsymp.completion`) uses
the weighted estimate on good states; `FSAsymp.completion_full` adds eq:formW, the weighted
estimate for every `u` and `R₃* = R₃`.

### Auxiliary clauses (`PlaneWave.Auxiliary.GalerkinDynamics`, `PlaneWave.Auxiliary.FluxSourceClauses`)

| Manuscript | Lean |
|---|---|
| `prop:F2`, `prop:nbo-KR`: self-adjointness of `H` (domain `S(H²)`) | `PlaneWaveDynamics.coulombPMap_isSelfAdjoint` |
| `prop:duhamel`, eq:normlevel for the full error | `PlaneWaveDynamics.coulomb_normlevel_full` |
| `lem:disc-tails` for every threshold `λ ≥ max(1, 4π/L)` (constants uniform in the register, with `m̄` in place of `m_a`; a factor 6 above `K`), its vanishing for `λ ≥ √3K`, and the ∞-norm variant | `PlaneWaveKinetic.cube_tails_all`, `cube_supTails_all` |
| `ψ_N(t) ∈ ran P ∩ S` | `PlaneWaveDynamics.galerkin_flow_isSector`, `galerkin_trajectory_isSector` |
| `lem:gap`, sharpness of `3/32` | `FluxSourceTest.gap_sharp` |
| `lem:pin`, sharpness | `FSLattice.pin_sharp` |
| earlier-draft `lem:acorr`, eq:acorr-id (second identity) and the third bound | `FSNormal.acorr_PR`, `norm_acorr_PR_le` |
| earlier-draft `lem:tavg`, second identity | `FSSpectral.tavg_mass` |
| `lem:phi` with `A_p^E`, `0 ≤ α ≤ 1/2` | `FSNormal.flow_datum_interp` |

### Auxiliary claims (`PlaneWave.Auxiliary`)

| Manuscript | Lean | Module |
|---|---|---|
| earlier-draft `lem:bulk-weighted`, `j = 2` | `FSNormal.form2_sig_Q_state_le`, `form2_sig_Q_le` | `PlaneWave.Auxiliary.DressedTails` |
| earlier-draft `lem:dressed-tails`: `‖ℰψ̃_R‖ ≤ CΞK^{-1/2}`, `‖ℰ^{1/2}ψ̃_R‖ ≤ CΞK^{-3/2}`, `supp r ⊂ Q`, `Θ(r) ≤ CΞK^{-3/2}` | `FSNormal.dressed_energy_bounds`, with the log-free orders `FSAsymp.dressed_tails_logfree` | `PlaneWave.Auxiliary.DressedTails` |
| `lem:phi` with `A_p^E`, log-free: `CBK^α` (`0 ≤ α ≤ 1/2`), `CBK^{2σ-1/2}` (`1/4 < σ ≤ 1`) | `FSNormal.phi_logfree_low`, `phi_logfree_high` | `PlaneWave.Auxiliary.LogFreePhi` |
| eq:duhamel | `PlaneWaveDynamics.coulomb_duhamel_eq` | `PlaneWave.Auxiliary.Duhamel` |
| `lem:fold` for a general trigonometric polynomial (pair and single register, clamped nuclei) | `GridFold.fold_pair`, `fold_single`, `fold_pair_eq_zero`, `fold_pair_galerkin`, `tpoly_nuc` | `PlaneWave.Auxiliary.Fold` |
| `lem:fourier-domination` on a finite Fourier cube (eq:fourier-domination, eq:dominated-Hardy, single register, `ĝ(0)`); the manuscript's statement for general states is not a separate declaration | `FSNormal.fourier_domination`, `dominated_pair_hardy`, `dominated_single_hardy`, `fcko_const` | `PlaneWave.Auxiliary.FourierDomination` |
| `lem:grid-KR` (i), eq:grid-KRpair | `FSNormal.grid_KR` | `PlaneWave.Auxiliary.FourierDomination` |
| `lem:grid-KR` (ii), eq:alias-mult, eq:alias-restricted (`C_alias = √728 ≤ 27`) | `FSNormal.alias_bound`, `alias_bound_restricted`, `norm_gridDiag_le`, `tail_gridDiag_le` | `PlaneWave.Auxiliary.AliasGrid` |
| `lem:grid-KR` (iii), eq:grid-tail, eq:grid-potential-tail (factor `m̄`) | `FSNormal.grid_tail`, `grid_potential_tail`, `grid_potential_tail_explicit` | `PlaneWave.Auxiliary.PotentialTails` |
| `lem:grid-KR` (iv), eq:grid-graph-equivalence, the lower bound, eq:grid-form-lower | `FSNormal.grid_graph_equivalence`, `grid_lower_bound`, `grid_form_lower` | `PlaneWave.Auxiliary.AliasGrid` |

In `PlaneWave.Auxiliary.FourierDomination` ... `PlaneWave.Auxiliary.PotentialTails` the grid potential is `V_grid = Σ_t c_t Diag[g_t]` on the cube, with
`Diag[g] = P'(g ·) + R(g ·)` in momentum coordinates (`gridDiag`; `gridDiag_apply` is the fold form
`(Diag[g] u)(p) = Σ_{t ≡ p} (g u)(t)`). The kernels are those dominated by `C_g` times the Coulomb
pair kernel or the Coulomb kernel of one register (`CoulombDominated`); the alias bounds take as a
hypothesis that the outputs lie in the alias region (transfers at most the zone half-width,
`outReg_of_kernel`). `eq:grid-tail` holds for every `K ≥ 1` with the mass factor `m̄` (the coarser
bound mentioned in the text), not `√(m_a m̄)`.

### Hypotheses of the flux and source theorems

The flux and source theorems take the Hamiltonian `H` (with `hKernel`, its kernel on the cube) and
a Hardy constant (with `hPeriodic`) as parameters. Both are discharged in `PlaneWave.Certificate`:
`exists_coulombFourierH2Operator` and `canonicalPeriodicCoulombHardyBound_explicit`. The data
`D : EvoData L H` (propagator and datum in `D(H²)`) exist for every datum in `D(H²)`:
`FSNormal.exists_evoData` (`PlaneWave.KineticCompletion.Completion`) builds them from `exists_coulombFourierPropagator`.

### The free-boundary dynamics (`PlaneWave.FreeBoundary.Dynamics`, `.Propagator`)

`FreeBoundary.free_dyn_torus` is the free-space step of `prop:free-dyn`. The free-space evolution
is any curve `ψ` in `L²(ℝ^{3η})` with `iψ' = H_∞ψ`, where `H_∞ f = h` means that the Coulomb term
`V_∞ f` lies in `L²` and `h - V_∞ f` is the weak kinetic image of `f` against `C²` tests of compact
support (`HasFreeHamiltonian`), together with weak gradients (`HasWeakGrad`). The torus evolution is
any strongly continuous unitary group `U` whose generator relation is the `g_L` Hamiltonian
(`HasGLHamiltonian`, the form of `PlaneWaveCertificate.HasCoulombHamiltonian`). The cutoff
`χ` (`FreeBoundary.Cutoff`) is `C²`, `0 ≤ χ ≤ 1`, equal to `1` on `B^one`, supported in the retained
region, and its first and second derivatives (bounded by `D₁`, `D₂`) vanish off a shell `S` disjoint
from `B^one`. Under (H_leak), `∫_{(B^one)ᶜ} |ψ(s)|² ≤ ε²` and `∫_S |∇ψ(s)|² ≤ ε²` for `0 ≤ s ≤ t`:

* `‖φ(t) - e^{-iC₀t} U(t) φ(0)‖ ≤ C ε t` for the transplanted cutoff state `φ(s) = T(χψ(s))`, with
  `C = 3η (D₁ + D₂/2)` (masses `≥ 1`) and the zero-mode shift `C₀` (`e^{-iC₀t} U(t)` is the torus
  evolution with the zero mode included);
* `|⟨ψ(t), χ_o ψ(t)⟩ - ⟨U(t)φ(0), G U(t)φ(0)⟩| ≤ ε² + (‖ψ(t)‖ + ‖ψ(0)‖) C ε t` for every measurable
  multiplier `0 ≤ χ_o ≤ 1` whose torus version `G = χ_o ∘ cell` is continuous.

Here `T` includes the volume factor needed to preserve the norm of the cutoff state; the state
is not divided by its norm. The free-space step is stated through the weak Hamiltonian and
gradient relations above and requires no pointwise `C²` regularity of `ψ`. Ordinary Sobolev
regularity `H²` is distinct from the squared-Hamiltonian domain `D(H_L²)` used for the subsequent
cell-to-grid comparison. `D₁` and `D₂` bound every coordinate derivative `∂_aχ`, `∂_a²χ` separately.

The propagator of the torus Hamiltonian is constructed in `PlaneWave.FreeBoundary.Propagator`:
`FreeBoundary.exists_gLPropagator` gives the strongly continuous unitary group `e^{-iH_L t}`
(graph-preserving, solving the Schrödinger equation, unique among solutions in the graph), by the
certificate's resolvent construction applied to the completed `g_L` operator
(`exists_fourierPropagator_of_relBound`, with `gLH2_symm` and the relative bound
`gL_potential_sq_le_quarter`). `FreeBoundary.free_dyn_gL` states the two bounds above for this
propagator, for `R ≤ L/2`, with no propagator hypothesis.

The grid step of `prop:free-dyn` is `thm:grid-dyn-sharp` for the `g_L` kernel
(`FreeBoundary.thm_grid_dyn_sharp_gL`, `PlaneWave.FreeBoundary.GridDynamicsTheorem`). The release's
proof uses the Coulomb Hamiltonian only through the Galerkin compression, the symmetry, the relative
bound and the tails of the potential, and the Galerkin reference of the register;
`PlaneWave.FreeBoundary.GridDynamicsInterface` proves these for the completed `g_L` operator (tail
constant `gLtailM = Q (1 + V_θ) c_tail M₂` in physical units, from `gLpot_tail_boundP`), with the
reference `ĝ_L` of
the general grid core, and `PlaneWave.FreeBoundary.GridDynamicsSharp` runs the release's proof
(`DevGS2`–`DevGS5`) with them. The bound is `(A₁ + (A₃ 3^{5/2} + ‖ψ₀‖²) C_{χ,5}) K⁻⁵ + A₂ t K⁻³`
for `ψ₀ ∈ D(H_L²)`, `m ≥ 8`, `K ≥ 8`, every kernel of the class with reference `ĝ_L`
(`PlaneWaveGridG.IsGridKernel`), with `(A₁, A₂, A₃) = gridConstsSharp_gL` independent of `K` and
`t`. The grid values of the release are in the frame of `physMap` (Fourier synthesis followed by
`x ↦ -x`) while `HasGLHamiltonian` is in the frame of the synthesis, so the collocated observable of
`χ(x_a)` is `χ(-x_{j_a})` (`chiRefl χ`, `synth_mulCLM`).

`FreeBoundary.free_dyn_grid_gL` (`PlaneWave.FreeBoundary.FreeDynamicsGrid`) composes the two steps
with one propagator `U`: for the free-space evolution `ψ_∞` under (H_leak), the text's domain
condition for the transplanted cut initial state `φ(0) = T(χ_𝓑 ψ_∞(0))` (`H_L φ(0) = h₀`,
`H_L h₀ = h₁`, a hypothesis), and a one-particle observable `f(r_a)`, `0 ≤ f ≤ 1`, whose torus
version on the cell is a continuous `χ` with `(Hχ)`:
`|∫ f(r_a)|ψ_∞(t, r)|² dr - ⟨ψ_g(t), χ(-x_{j_a}) ψ_g(t)⟩| ≤ ε² + (‖ψ_∞(t)‖ + ‖ψ_∞(0)‖)Cεt +
(A₁ + (A₃ 3^{5/2} + ‖φ(0)‖²)C_{χ,5})K⁻⁵ + A₂tK⁻³`.

The constants of the grid step are polynomial in `L` in the release's proof, which works in lattice
units (weight `wM = 1 + Σ_b |ν_b|²/m_b`, lattice Sobolev constants). For `L ≥ 2π` the grid step
also holds with constants that do not depend on `L` (`FreeBoundary.thm_grid_dyn_sharp_gLU`,
`free_dyn_grid_gLU`, `PlaneWave.FreeBoundary.GridDynamicsUniformTheorem`); the proof runs in the
physical weight `w_g = 1 + g² Σ_b |ν_b|²/m_b` with the physical Sobolev constant `1 + 78/g³`:

* `PlaneWave.FreeBoundary.GridDynamicsUniform`: the relative-bound and tail constants are `L`-free
  in physical units, the relative bound of the grid potential has the `L`-free constant
  `A = gLAU = 43264·79 z³ + 52 z` (`gLGridA_le_U`), and the generic register Hamiltonian with
  kinetic scale `c` (`RegHamP`) gives the first-order graph-norm equivalence and the trajectory
  bound with `L`-free constants (`gridGraphNorm_gL`, `norm_wPhys_gridFlow_le_gL`);
* `PlaneWave.FreeBoundary.GridSecondOrderPhysical`: the weighted relative bound and the second-order
  elliptic estimate in `w_g`, with growth `C₂ ≤ σ_U (g(4m+1))^{3/2}`, `σ_U = 2A + 4√79 z`
  (`second_ellipticP`, `secondConstP_le_gL`), the second moments of grid trajectories and the shells
  of the backward flows (`norm_wPhys_sq_gridFlow_le_gL`, `shell_gridFlow_gridObs_le_gLU`);
* `PlaneWave.FreeBoundary.GridSecondMomentPhysical`: the layer cake in physical momenta, the second
  moment of the projected trajectory and duality on the grid with the physical form constant
  (`second_moment_regCoeff_le_gLU`, `grid_duality_shell_gLU`);
* `PlaneWave.FreeBoundary.GridObservablePhysical`: the observable error and the arithmetic of the
  rates in physical units (`grid_observable_error_sharp_gLU`, `grid_rate_arith_sharpP`).

The constants `(A₁, A₂, A₃) = gridConstsSharp_gLU` (`gridConstsPosU` in position space) are
functions of the system, of the total variation `V_θ` of the range cut, of
`(‖ψ₀‖, ‖H ψ₀‖, ‖H² ψ₀‖)` and of the physical moments of the observable
(`Σ |χ̂(ν)|`, the norm of the convolution with `χ̂`, `Σ |gν|² |χ̂(ν)|`, `Σ |gν|⁴ |χ̂(ν)|`) only.

For a fixed observable these moments are bounded uniformly in `L`
(`PlaneWave.FreeBoundary.ObservableMomentsUniform`). If `f` is a Schwartz function vanishing outside
the ball of radius `R_f` and `L > 2R_f`, the torus version `χ(t) = f(L·rep t)` has the coefficients
`χ̂(ν) = L⁻³ f̂(ν/L)`, `f̂(ξ) = ∫ f(x) e^{-2πi x·ξ} dx` (`mFourierCoeff_cell`). With
`B_N = sup_ξ (1 + |ξ|)^N |f̂(ξ)|` (`ftDecay`) and the lattice sum
`Σ_ν L⁻³ (1 + |ν/L|)⁻⁶ ≤ 27` for `L ≥ 1` (`tsum_latWeight_le`), the moments satisfy
`Σ |χ̂| ≤ 27 B₆`, `g² Σ |ν|² |χ̂| ≤ 27 (2π)² B₈`, `g⁴ Σ |ν|⁴ |χ̂| ≤ 27 (2π)⁴ B₁₀`, and `(Hχ)` holds
with `C_{χ,M} = 27 (2π)^M B_{M+6}` (`CellDecay.hChi`). The constants are monotone in the moments
(`gridConstsSharp_gLU_mono`), so `prop:free-dyn` holds with `(A₁, A₂, A₃)` and `C_{χ,5}` that
depend only on the system, `V_θ`, the data and `f` (`free_dyn_grid_gLU_schwartz`).

For the non-Born–Oppenheimer system (every particle quantum, no clamped nuclei) the domain
condition of `prop:free-dyn` is proved (`PlaneWave.FreeBoundary.CutStateDomain`). The cutoff is
mass-weighted (`DomCutoff`): besides `C⁴` bounds `D`, it satisfies
`|∇_iχ/m_i - ∇_jχ/m_j| ≤ C |x_i - x_j|`, so that the singular part
`-Σ_a m_a⁻¹ ∂_aχ ∂_aV` of the double commutator `[V, [K, χ]]` is `Σ_{i<j} β_{ij}/|x_i - x_j|` with
`|β_{ij}| ≤ |q_i q_j| C`; this identity is proved in weak form through the regularised interaction
`V_ε` and dominated convergence (`singular_identity`). The free-space hypotheses on `u = ψ_∞(0)`
are `H_∞ u = h`, `H_∞ h = k`, weak gradients of `u`, `h` and `∇u`, and the Hardy functions
`u/|x_i - x_j|`, `∂_a u/|x_i - x_j|` in `L²`. Then `H_L T([K, χ] u)` is computed on trigonometric
test functions (`commT_hasGLHamiltonian`), and `T(χu) ∈ D(H_L²)` with `‖H_L^k T(χu)‖ ≤ Λ^k N`
(`cut_state_domain`). The constants of the grid step are monotone in the data
(`gridConstsSharp_gLU_mono_data`) and `|C₀| ≤ Q/4` for `L ≥ 2π`, so `prop:free-dyn` holds without
the domain hypothesis, with constants that depend only on the system, `V_θ`, `f`, the free-space
data and bounds `D̄`, `C̄` for the cutoff (`free_dyn_grid_nbo`). Scaling a fixed cutoff,
`χ_s(r) = χ(r/s)` (`DomCutoff.scale`), keeps these bounds; `χ = F(Σ_i m_i |x_i|²)` is such a cutoff
for any masses `m_i ≥ 1` (`exists_quadCutoff`), equal to `1` where `Σ_i m_i |x_i|² ≤ 1`, so the
leakage hypotheses for `χ_s` control both the internal separations and the centre of mass.

The torus version `χ` of the observable is constructed (`PlaneWave.FreeBoundary.CellObservable`):
for `f` continuous and vanishing outside the ball of radius `R_f < L/2`, `χ(t) = f(L·rep t)` is
continuous on the torus (`cellObs`), since the representative `rep` is continuous wherever no
coordinate is `1/2 mod 1`, and `χ` vanishes on the open set where some coordinate has
`L‖t_c‖ > R_f`; the two sets cover the torus. The `_cell` versions of the theorems use it
(`free_dyn_grid_gLU_schwartz_cell`, `free_dyn_grid_nbo_cell`).

The free-space regularity of `u = ψ_∞(0)` is derived from the two Hamiltonian relations
(`PlaneWave.FreeBoundary.Mollification` to `.RegularityBridge`). `H_∞ u = h` says that `Vu ∈ L²`
and that `z = h - Vu` is the weak kinetic image of `u`. The mollification `F_n = ρ_n ⋆ u` is smooth
with `K F_n = ρ_n ⋆ z`, and integration by parts gives `Σ_a m_a⁻¹ ‖∂_a F‖² = 2⟨F, KF⟩` and
`Σ_{a,b} m_a⁻¹ m_b⁻¹ ‖∂_a ∂_b F‖² = 4 ‖KF‖²`; so the derivatives of `F_n` are Cauchy in `L²` and
their limits are the weak derivatives of `u` (`weak_kinetic_regularity`). Hardy's inequality
`‖f/|x_i - x_j|‖² ≤ 4 Σ_c ‖∂_{(i,c)} f‖²` is proved with the vector field
`(x_i - x_j)/(|x_i - x_j|² + δ²)` for smooth `f`, extended to `f` with a weak gradient by
mollification, and `δ → 0` by monotone convergence (`hardy_weak`); applied to `u` and to `∂_a u` it
gives the quotients. With `M` the largest mass and `Q = Σ_{i<j} |q_i q_j|`,
`‖Vu‖² ≤ 8 M Q² ‖u‖ ‖z‖`, hence `‖z‖ ≤ 2 ‖h‖ + 8 M Q² ‖u‖`, and the data norm is at most
`C_sys (‖u‖ + ‖h‖ + ‖k‖)`, with `C_sys` depending only on the masses, the charges and `η`
(`free_data_regularity`). `cut_state_domain_reg` and `free_dyn_grid_nbo_reg` take only the
Hamiltonian relations (and, for the leakage, the weak gradients along the trajectory).

The endpoints in the form of the manuscript (`PlaneWave.FreeBoundary.FreeDynamicsEndpoint` to
`.FreeEnergyEndpoint`). Along a solution curve of `H_∞` the norm is conserved, since `⟨f, H_∞ f⟩`
is real (`norm_conserved`); so the factor `‖ψ(t)‖ + ‖ψ(0)‖` of the dynamics bounds is `2‖ψ(0)‖`,
and `prop:free-dyn` takes the form `C[K⁻⁵ + tK⁻³] + C(1 + t)ε` (`free_dyn_endpoint`,
`free_dyn_nbo_endpoint`). `free_dyn_uniform` and `free_dyn_nbo_uniform` fix the cutoff
`F(Σ_i m_i |x_i|²/(L/8)²)`, the cell observable and the kernel class, and give one constant for
every `L ≥ L₀`; the constants read only the masses and charges (`freeDynConst_sysAt`). For
`prop:free`, the near-minimisers taken by the product-geometry theorems
(normalised `C²` sector states with small mass outside the retained region) are derived from the
ground states. In free space: the eigenfunction `ψ_∞` has a weak gradient (`H_∞ψ_∞ ∈ L²`), its
energy is `(1/2) Σ_a m_a⁻¹ ‖∂_a ψ_∞‖² + ∫ V_∞ |ψ_∞|²` (`eigen_energy`), the approximants
`χ_n · (σ_n ⋆ ψ_∞)` lie in the sector and converge in the form norm, and Hardy's inequality for
`|x_i - x_j|` and `|x_i - R_ℓ|` makes the Coulomb form continuous in that norm
(`tendsto_integral_freePot`). On the torus: the ground state is an `H²` state `u_L` with
`H u_L = E_L u_L` for the completed `g_L` operator `H`; its cubic Fourier truncations are
trigonometric polynomials of the sector and converge in `H²`, and the torus energy of a `C²` state
is the form of `H` at its `H²` coordinates (`torusEnergy_eq_form`). The masses outside the retained
region are bounded by the exponential moments, with a factor 2 of slack. The rates are those of
the manuscript: `e^{-αL/2}` for the upper bound (eq:free-energy-upper) and `γ = min(α, β/2)/2` for
eq:free-energy. The grid constants `K₀`, `C` are those of `thm:grid-energy`
at an energy budget bounding `|E_L| + 1` for all `L`: from the two-sided bound, or, for the
upper bound without assumption (A), from `E_L ≥ -(B² + 1/4)` with `B` the `L`-free mass-weighted relative
bound of the `g_L` potential (`gLTorusGroundEnergy_ge`). As in the manuscript the nuclei are
clamped: without clamped nuclei `H_∞` is translation invariant and has no normalisable
eigenfunction.

With clamped nuclei (`PlaneWave.FreeBoundary.NuclearPotential` to `.FreeDynamicsBOUniform`) the
potential is `V = Σ_{i<j} q_i q_j/|x_i - x_j| + Σ_{i,ℓ} q_i Z_ℓ/|x_i - P_ℓ|`, and `Vu`, `V∂_a u` are
sums of pair and nuclear Hardy functions (`hasL2PointwisePotential_pair_nucL2`, with Hardy's
inequality for `|x_i - R|`). The nuclear part of `-Σ_a m_a⁻¹ ∂_aχ ∂_aV` is singular like
`|x_i - P_ℓ|⁻²` unless `∇_iχ` vanishes near `P_ℓ`. For a cutoff flat near the nuclei
(`IsFlatNear`: `∂_{(i,c)}χ(r) = 0` whenever `|x_i - P_ℓ| < δ`) it is bounded by
`Σ_{i,ℓ} |q_i Z_ℓ| |∂_aχ|/δ²`, and its weak identity passes to the limit from the regularised
`(|x_i - P_ℓ|² + ε²)^{-1/2}` by dominated convergence (`nuc_singular_identity`). The domain theorem
holds with `Λ′ = Λ + 3η D Σ_{i,ℓ} |q_i Z_ℓ|/δ²` (`cut_state_domain_nuc`), and the regularity
bridge with `Q′ = Σ_{i<j} |q_i q_j| + Σ_{i,ℓ} |q_i Z_ℓ|` in place of `Q`
(`free_data_regularity_nuc`, `cut_state_domain_reg_nuc`); `free_dyn_grid_bo` is `prop:free-dyn`
without the domain hypothesis.
The cutoff `F(Σ_i m_i |x_i|²)` is not flat near the nuclei. For equal masses (the moving particles
are electrons) the product `χ(r) = Π_i q(x_i)` of one bump (`q = 1` on `B_1(0)`, `0` outside
`B_2(0)`) is: it is flat in `x_i` where `|x_i| < 1`, and it is symmetric under exchanges, so
`∂_{(i,c)}χ - ∂_{(j,c)}χ` vanishes where `x_i = x_j` and, being Lipschitz, is at most
`K |x_i - x_j|` (`exists_prodCutoff`). Scaled by `L/16` it is flat near nuclei in `B_{R₀}(0)` at
distance `δ` once `L ≥ 16(R₀ + δ)`, and `free_dyn_bo_uniform` gives one constant for all `L ≥ L₀`.

With internal spin (`PlaneWave.FreeBoundary.SpinFreeStep` to `.SpinFreeDynamicsEndpoint`) the state
is in `L²(ℝ^{3η}) ⊗ ℂ^ς` (`FreeSpinL2`), one component for each spin configuration, with the
Hilbert norm `‖Ψ‖² = Σ_σ ‖Ψ_σ‖²`; the Hamiltonian acts on each component. Duhamel's estimate is
applied in the spin-inclusive space, and the commutator bound with separate leakages
(`Cutoff.norm_commT_le₂`) gives `Σ_σ ‖T([K, χ]Ψ_σ)‖² ≤ (Cε)²` when the leakages summed over the spin
components are at most `ε²` (`Cutoff.sum_norm_commT_sq_le`), so the free-space step holds with the
constant `C = 3η(D₁ + D₂/2)` of the spinless case (`free_dyn_torus_spin`). The grid step acts on
each component with one grid flow. Its observable error is quadratic in the component
(`gridErr_smul`), so the bound at the unit data `(1, Λ, Λ²)` gives `N_σ²` times that bound for a
component with data `(N_σ, ΛN_σ, Λ²N_σ)` (`norm_le_sq_mul_of_unit`), and the components add to
`(Σ_σ N_σ²)` times it (`free_dyn_grid_spin`); with `N_σ = c′(‖Ψ₀,σ‖ + ‖H_∞Ψ₀,σ‖ + ‖H_∞²Ψ₀,σ‖)`,
`Σ_σ N_σ² ≤ (c′D)²` by the triangle inequality in `ℓ²` (`sum_sq_add3_le`). The endpoints
(`free_dyn_nbo_spin_uniform`, `free_dyn_bo_spin_uniform`) have one constant for all `L ≥ L₀`
(`freeDynConstSpinNBO`, `freeDynConstSpinBO`: the grid constants at the unit data scaled by
`(c′D)²`), independent of the number of spin components.

`prop:free`, eq:free-energy and `prop:free-dyn` assume only a uniform bound `V_θ ≤ V̄` on the
total variation of the profiles (`PlaneWave.FreeBoundary.EnergyVbar`, `.DynamicsVbar`). The
thresholds and constants above are increasing in the variation: for the ground energy the threshold
`gLKThresholdU` and the constant `gLErrorConstU`, in `V` and in the energy budget, and the budget
`freeUpperBudget`; for the dynamics the grid constants `gridConstsSharp_gLU`, hence `freeDynConst`,
`freeDynConstNBO`, `freeDynConstBO`, `freeDynConstSpinNBO` and `freeDynConstSpinBO`. Each is built
from the `L`-free constants `gLzU`, `gLAU`, `gLmassConstU`, `relBU`, `gLtailMU`, `gridFlowConstU`
and `sigmaU` (and the factor `1 + V`) by sums, products, powers, roots and maxima with
nonnegative coefficients. The `_vbar` forms state, for the profiles with `tv R θ ≤ V̄` and with
thresholds and constants at `V̄`, every ground-energy statement that fixed `V_θ = V` or evaluated its
`L`-uniform constants at `tv R θ` (including the single-profile bounds from near-minimisers and
`gLTorusGroundEnergy_ge`), and every `prop:free-dyn` endpoint in the form of the manuscript; the
kernel class keeps the majorant `(1 + V_θ)ŵ` of the actual profile, as eq:rangecut gives it. The
intermediate dynamics statements (`free_dyn_grid_gLU_schwartz_cell`, `free_dyn_grid_nbo`,
`free_dyn_grid_spin`, ...) keep constants written with `V_θ`, bounded at `V̄` by
`gridConstsSharp_gLU_mono_V`.

The physical cell Hamiltonian keeps the zero mode of `g_L`, `H_L = H_L^{(0)} + C₀`
(eq:free-zero-mode), and so does the grid kernel, `κ(0) = ĝ_L(0)` (eq:free-kinetic-kernel;
`KineticLog.HasGLHamiltonianZ`, `KineticLog.IsGridKernelZ`, in `PlaneWave.KineticLog.OpenZeroMode`).
`PlaneWave.FreeBoundary.DynamicsZeroMode` states `prop:free-dyn` for these Hamiltonians. In position
space the grid zero mode is the scalar `κ(0)z_g` (`Hpos_update`); every propagator of the physical
grid Hamiltonian is `e^{-itC₀}` times every propagator of `G[κ⁰]` (`posProp_phase`, by uniqueness
for the symmetric generator; `κ(0)z_g = C₀`, `posProp_phase_zeroMode`), and the grid observable
`⟨ψ_g, O_gψ_g⟩` does not see the phase. The free-space step holds for every strongly continuous
unitary group of the physical `H_L` in the form `‖φ(t) - e^{-itH_L}φ(0)‖ ≤ Cεt`
(`free_dyn_torus_phys`, with spin `free_dyn_torus_spin_phys`, through `U(t) = e^{itC₀}U_Z(t)`,
`cell_unphase`). (H_dom) for the physical
`H_L` with `‖φ₀‖, ‖h₀‖, ‖h₁‖ ≤ 𝒟` gives (H_dom) for `H_L^{(0)}` with the budget `(1 + Q/4)²𝒟`
(`budget_zero_mode_each`, `|C₀| ≤ Q/4`). The `_phys` endpoints hold for every propagator of the
physical grid Hamiltonian (they exist: `exists_posPropagatorZ`) and every kernel of the class
eq:free-kinetic-kernel, with the constants of the `_vbar` forms, at the budget `(1 + Q/4)²𝒟` where
(H_dom) is assumed. The ground energy needs no change: eq:free-energy already compares `E_L + C₀`
with `E_∞`.

### The logarithmic kinetic-energy bounds (`PlaneWave.KineticLog`)

`app:source` (`thm:kinetic-log`, eq:kinetic-retained-galerkin, `cor:stopping-log`) and the
isolated-grid results of `app:free` (`prop:free-kinetic-log`, `cor:free-stopping-log`,
eq:free-kinetic-N), with the spectral proofs of the manuscript: comparison on low-energy spectral
subspaces of the full Hamiltonians, the dyadic Duhamel estimate, ordered-spectrum Sylvester
absorption and graph pairing. The names are in the namespace `KineticLog`; the modules are
`PlaneWave.KineticLog.*`.

| Manuscript | Lean | Module |
|---|---|---|
| `sec:kinetic-inputs`: eq:kinetic-generic-tails; eq:kinetic-forms (the form bound and its norm form); eq:kinetic-grid-bandwidth (the lattice weight on the register, `‖wTot v‖ ≤ (1 + 12ηm²)‖v‖`); eq:kinetic-exact-flow-tails, on the register | `W_tail_le`, `W_tail_le_h2`; `PlaneWaveGrid.Delta_form`, `PlaneWaveKinetic.norm_Delta_le`; `PlaneWaveKinetic.norm_wTot_le_reg`; `exact_traj_shells` | `.SpectralTails`, `.GridSpectral`, `PlaneWave.GridCore`, `PlaneWave.Grid`, `.GridTraj` |
| eq:kinetic-spectral-filters: the low-energy spectral projector `S = 1_{𝖧≤Λ}` of the periodic Hamiltonian, the action of every propagator on its eigenvectors; the grid eigenbasis for `S_g = 1_{𝖧_g≤2Λ}`, uniformly over the kernel class | `exists_exactEigen`, `ExactEigen.evo_b`, `ExactEigen.inner_b_evo`, `ExactEigen.norm_sub_proj_le`; `grB`, `grE`, `grE_lower`, `grid_flow_eigen`, `inner_grB_flow` | `.ExactSpectral`, `.GridSpectral` |
| `lem:kinetic-strong`: eq:kinetic-consistency; eq:kinetic-residual-tail, with the shells of `P′u` beyond `⌊m/4⌋` (`θ = 1/4`) and the tail of `u` beyond the cube `2m`; eq:kinetic-grid-flow-tails | `regCoeff_H_eq_gRes`, `grid_cons`; `norm_gRes_le`, `norm_gSrc_le`; `grid_traj_shells` | `.GridConsistency`, `.GridTraj` |
| `lem:kinetic-low`: eq:kinetic-spectral-momentum-tail (by the absorption eq:kinetic-absorption), eq:kinetic-low-consistency, eq:kinetic-strong-consistency (the bound `F_raw` of eq:kinetic-residual-tail on inverse-weighted low-energy states, `F_raw ≤ C K^{-1/2}`) | `norm_tail_zv_le`, `norm_tail_zv_shift_le`, `grid_low_tail`; `grid_delta_raw` with `dRawG_le`; `exact_low_reg` with `fRawG_le` | `.SpectralTails`, `.GridSpectral`, `.GridConsistency`, `.GridRates` |
| `lem:kinetic-dyadic` (eq:kinetic-dyadic), in eigenbasis coordinates, `C = 48` | `dyadic_duhamel`; Sylvester absorption `norm_sylvester_le`, `norm_sylvester_le'`; time integration `norm_mop_phiT_le` | `.DyadicDuhamel`, `.Sylvester` |
| `lem:kinetic-leakage` (eq:kinetic-transfer): the separated block `‖Y‖ ≤ F_raw/(Λ − d)` | `grid_transfer_raw` with `fRawG_le` | `.GridConsistency`, `.GridRates` |
| `lem:kinetic-high` (eq:kinetic-high-moment, from the shells eq:kinetic-one-shell) | `norm_wM_regKin_shells`, with `exact_traj_shells`, `grid_traj_shells` (see below) | `.GridShells`, `.GridTraj` |
| eq:kinetic-grid-pairing (containing eq:kinetic-low-flow-error and eq:kinetic-leakage-state) | `grid_core_pair` (the eigen-coordinates `grid_coord`) | `.GridDuhamel` |
| eq:kinetic-pairing, eq:kinetic-high-kinetic-error, eq:kinetic-initial-high, eq:kinetic-projection-error: the grid case assembled | `regExpect_pair_le`, `grid_proj_term`, `grid_kinetic_explicit` | `.GridEndpoint` |
| `sec:kinetic-galerkin`: eq:kinetic-galerkin-graph, eq:kinetic-galerkin-strong, eq:kinetic-galerkin-low, eq:kinetic-galerkin-low-flow, eq:kinetic-galerkin-transfer, eq:kinetic-galerkin-filtered | `galerkin_graph`; `gcons_combo`; `norm_tail_zv_le`, `galerkin_delta`; `galerkin_transfer`; `galerkin_retained_core` | `.GalerkinConsistency`, `.SpectralTails`, `.Galerkin` |
| eq:kinetic-retained-galerkin | `kinetic_retained_galerkin` | `.GalerkinEndpoint` |
| `thm:kinetic-log`, Galerkin case | `thm_kinetic_log_galerkin_all`; `thm_kinetic_log_galerkin` | `.PeriodicUniform`, `.GalerkinEndpoint` |
| `thm:kinetic-log`, grid case, every kernel of eq:kernelclass and every grid propagator | `thm_kinetic_log_grid_all`; `thm_kinetic_log_grid`, `grid_kinetic_explicit` | `.PeriodicUniform`, `.GridEndpoint` |
| `cor:stopping-log` (both methods) | `cor_stopping_log_galerkin_all`, `cor_stopping_log_grid_all`; `cor_stopping_log_galerkin`, `cor_stopping_log_grid` | `.PeriodicUniform`, `.GalerkinEndpoint`, `.GridEndpoint` |
| the same with finite internal spin | `kinetic_retained_galerkin_spin_all`, `thm_kinetic_log_galerkin_spin_all`, `cor_stopping_log_galerkin_spin_all`, `thm_kinetic_log_grid_spin_all`, `cor_stopping_log_grid_spin_all`; for one spin set: `kinetic_retained_galerkin_spin`, `thm_kinetic_log_galerkin_spin`, `cor_stopping_log_galerkin_spin`, `thm_kinetic_log_grid_spin`, `cor_stopping_log_grid_spin` | `.PeriodicUniform`, `.GalerkinSpin`, `.GridSpin` |
| `prop:free-kinetic-log`: the uniform cell inputs (`L ≥ 2π`) | `exists_exactEigen_gL`, `norm_tail_zv_gL`, `norm_tail_zv_shift_gL`, `grE_lower_U`, `grid_low_tail_U`, `norm_gRes_gL`, `grid_delta_raw_gL`, `grid_transfer_raw_gL`, `dRawU_le`, `fRawU_le`, `traj_tails_gL`, `exact_traj_shells_gL`, `grid_traj_shells_gL` | `.OpenExact` to `.OpenRates` |
| `prop:free-kinetic-log`: the cell-to-grid step, uniform in `L ≥ 2π` | `cell_kinetic_explicit`, `thm_cell_kinetic_log_gL` | `.OpenCell` |
| `prop:free-kinetic-log`: localisation (eq:free-kinetic-pairing) | `free_torus_kin` (free space to the transplant at time `t`), `torus_pair_step`, `torus_pair_core` (transplant to the cell trajectory), `cell_step` | `.OpenLocal`, `.OpenEndpoint`, `.OpenSpin` |
| the free-space kinetic energy | `freeKinQ` (the quadratic form), `exists_kinP`, `inner_kinP_eq`; `norm_H_conserved` | `.OpenFree`, `.OpenCompat` |
| `prop:free-kinetic-log`, general cutoff with (H_dom) | `free_kinetic_log_endpoint` (`C = freeKinC`, `K₀ = cellK0`), `free_kinetic_log` (`∃ C, K₀` first) | `.OpenEndpoint`, `.OpenCompat` |
| `prop:free-kinetic-log` and `cor:free-stopping-log` for a fixed molecule (`∃ C, K₀` before `L` and the nuclear positions) | `free_kinetic_log_at`, `free_kinetic_log_spin_at`, `free_stopping_log_at`, `free_stopping_log_spin_at` | `.OpenFixed` |
| `prop:free-kinetic-log`, compatible cutoffs (`D_* ≤ C𝒟_∞`) | `free_kinetic_log_nbo`, `free_kinetic_log_bo`; the explicit cutoffs with one constant for all `L ≥ L₀`: `free_kinetic_log_nbo_uniform`, `free_kinetic_log_bo_uniform` | `.OpenCompat`, `.OpenUniform` |
| `prop:free-kinetic-log` with finite internal spin | `free_kinetic_log_spin`; `free_kinetic_log_nbo_spin`, `free_kinetic_log_bo_spin`, `free_kinetic_log_nbo_spin_uniform`, `free_kinetic_log_bo_spin_uniform` | `.OpenSpin`, `.OpenSpinCompat` |
| `cor:free-stopping-log` (with spin) | `free_stopping_log`, `free_stopping_log_spin` | `.OpenStop`, `.OpenSpin` |
| eq:free-kinetic-N | `free_kinetic_log_N`, `basis_count_arith` | `.OpenStop` |
| `thm:kinetic-log`, eq:kinetic-retained-galerkin, `cor:stopping-log` in terms of `N` (`O([1 + t + log(2 + N)]/N)`, `N = (2n + 1)³`) | `thm_kinetic_log_galerkin_N`, `kinetic_retained_galerkin_N`, `cor_stopping_log_galerkin_N`, `thm_kinetic_log_grid_N`, `cor_stopping_log_grid_N`; with spin `kinetic_retained_galerkin_spin_N`, `thm_kinetic_log_galerkin_spin_N`, `cor_stopping_log_galerkin_spin_N`, `thm_kinetic_log_grid_spin_N`, `cor_stopping_log_grid_spin_N`; the basis count `basis_N_arith`, `basis_N_arith_stop` | `.PeriodicN` |
| `thm:kinetic-log`, eq:kinetic-retained-galerkin, `cor:stopping-log` for arbitrary positive masses `μ_i > 0` (`PosSystem`) | `thm_kinetic_log_galerkin_pos`, `kinetic_retained_galerkin_pos`, `cor_stopping_log_galerkin_pos`, `thm_kinetic_log_grid_pos`, `cor_stopping_log_grid_pos`; with spin `kinetic_retained_galerkin_spin_pos`, `thm_kinetic_log_galerkin_spin_pos`, `cor_stopping_log_galerkin_spin_pos`, `thm_kinetic_log_grid_spin_pos`, `cor_stopping_log_grid_spin_pos`; in terms of `N` the `_pos_N` and `_spin_pos_N` forms; the rescaling `PosSystem.latticeKernel_eq`, `PosSystem.kinExpect_eq`, `PosSystem.gridExpect_eq`, `PosSystem.galerkinH_eq`, `PosSystem.gridH_eq`, `evoRescale`, `PosSystem.galerkin_solution_eq`; existence `PosSystem.exists_H`, `exists_evoData_pos`, `PosSystem.exists_galerkin_solution`, `PosSystem.exists_gridPropagator`; agreement with the release for masses `≥ 1`: `PosSystem.ofCoulomb_latticeKernel`, `PosSystem.ofCoulomb_kinExpect`, `PosSystem.ofCoulomb_gridExpect`, `PosSystem.ofCoulomb_galerkinH`, `PosSystem.ofCoulomb_gridH` | `.PeriodicMasses` |
| `prop:free-kinetic-log`, `cor:free-stopping-log`, eq:free-kinetic-N for every profile with `V_θ ≤ V̄` (constants and thresholds at `V̄`) | `freeKinC_mono`, `cellK0_mono`, `freeKinConstNBO_mono`, `freeKinConstBO_mono`; `free_kinetic_log_vbar`, `free_kinetic_log_at_vbar`, `free_kinetic_log_spin_at_vbar`, `free_stopping_log_at_vbar`, `free_stopping_log_spin_at_vbar`; `free_kinetic_log_endpoint_vbar`, `free_stopping_log_vbar`, `free_kinetic_log_N_vbar`, `free_kinetic_log_spin_vbar`, `free_stopping_log_spin_vbar`; `free_kinetic_log_nbo_vbar`, `free_kinetic_log_bo_vbar`, `free_kinetic_log_nbo_uniform_vbar`, `free_kinetic_log_bo_uniform_vbar` and their spin forms | `.OpenVbar` |
| eq:free-zero-mode: `H_L = H_L^{(0)} + C_zm`, `e^{-itH_L} = e^{-itC_zm} e^{-itH_L^{(0)}}`; the physical budget `D_*` | `gLFourierPotentialZ`, `HasGLHamiltonianZ`, `gLFourierPotentialZ_eq`, `hasGLHamiltonianZ_iff`, `cell_phase`, `cell_phase_eq`, `exists_gLPropagatorZ`, `budget_zero_mode`, `budget_zero_mode_spin` | `.OpenZeroMode` |
| eq:free-kinetic-kernel (the grid kernel keeps `ĝ_L(0)`); the grid zero mode | `IsGridKernelZ`, `IsGridKernelZ.zeroed`, `IsGridKernelZ.ofIsGridKernel`, `isGridKernelZ_sharp`; `Hgrid_update`, `gridZero_eq_zeroModeShift` (`κ(0)z_g = C_zm`), `grid_phase`, `regExpect_phase` | `.OpenZeroMode` |
| `prop:free-kinetic-log`, `cor:free-stopping-log` for the physical cell and grid Hamiltonians (zero modes kept, `V_θ ≤ V̄`) | `free_kinetic_log_phys`, `free_kinetic_log_phys_at`, `free_kinetic_log_spin_phys_at`, `free_stopping_log_phys_at`, `free_stopping_log_spin_phys_at` (`C = freeKinCZ sys V̄ D̄ = (1 + Q/4)⁴ freeKinC sys V̄ D̄`); `free_kinetic_log_phys_endpoint`, `free_stopping_log_phys_endpoint`, `free_kinetic_log_N_phys_endpoint`, `free_kinetic_log_spin_phys_endpoint`, `free_stopping_log_spin_phys_endpoint`; the compatible and explicit cutoffs `free_kinetic_log_nbo_phys`, `free_kinetic_log_bo_phys`, `free_kinetic_log_nbo_uniform_phys`, `free_kinetic_log_bo_uniform_phys` and their spin forms | `.OpenZeroMode` |

Conventions and proof correspondence:

* **Masses.** The systems (`CoulombSystem`) have masses `≥ 1`, the convention of the whole
  package. The periodic theorems also hold for any positive masses (`.PeriodicMasses`), by a charge
  rescaling: for a `PosSystem` with masses `μ_i > 0`, charges `q_i`, nuclear charges `Z_ℓ` and
  `λ = 1 + Σ_i 1/μ_i`, the system `S.scaled` (masses `λμ_i ≥ 1`, charges `q_i/√λ`, `Z_ℓ/√λ`) has
  every operator equal to `λ⁻¹` times that of `S` — the Hamiltonian kernel, the kinetic energies,
  the Galerkin and grid Hamiltonians — so `e^{-iHt} = e^{-iH′λt}`, with the same `K`, data norm
  bound and kernel class; the constants are `λ²C′` (`λC′` for eq:kinetic-retained-galerkin). The
  Galerkin trajectory is any solution of `iψ_N′ = H_Nψ_N`, `ψ_N(0) = Pψ₀` (unique by
  `ode_unique`; one exists, `PosSystem.exists_galerkin_solution`). The isolated-system results keep
  `m_i ≥ 1`, as `app:free` does.
* **In terms of `N`** (`.PeriodicN`). Galerkin: `N = (2n + 1)³` modes per register; grid: the
  unpadded admissible size `n = 2m + 1`, `N = (2m + 1)³` (register `(4m + 1)³`). The conversion is
  `[1 + t + log(2 + K)]/K³ ≤ c_L [1 + t + log(2 + N)]/N`, `c_L = 27L³(1 + log(1 + 2π/L))/(8π³)`
  (`cNL`, `basis_N_arith`), so `C_N = c_L C`.
* **Periodic data.** `H` is any operator with the cube-kernel identity `hKernel`, and `Hunit` a
  constant with `hPeriodic` (both discharged as for the flux theorems:
  `exists_coulombFourierH2Operator`, `canonicalPeriodicCoulombHardyBound_explicit`). A datum is
  `D : EvoData L H`: a propagator `U(t)` with its Schrödinger equation and `ψ₀ ∈ D(H²)`
  (`FSNormal.exists_evoData` builds one for every datum); the theorems hold for every such
  propagator (`ExactEigen.evo_b`). The field `D.Xi` equals
  `𝒟 = ‖ψ₀‖ + ‖Hψ₀‖ + ‖H²ψ₀‖`; the manuscript's regularity budget is
  `Ξ = C₀ m_max 𝒟`, as explained above. The Galerkin trajectory
  is `e^{-iH_N t}Pψ₀` (`retFlow` with `ΔH = 0`), `K = 2πn/L`; the grid trajectory is `U_g(t)P'ψ₀`
  for every unitary group `U_g` with `U_g(0) = 1`, commuting with `G` and with derivative `-iGU_g`
  (`PlaneWaveGridDynamics.exists_gridPropagator`: there is exactly one), on the register of radius
  `2m` with `n' = 4m + 1` points per axis, `K = 2πm/L` and cutoff `2K`. In the parametrisation
  `n' = 2n - 1`, `K = π(n - 1)/L` of `app:source`, with `n` odd, this is `n = 2m + 1`: every
  admissible size. The projected data are not renormalised, and there is no normalisation, gap
  or sector assumption.
* **Order of the constants.** In the `_all` statements (`.PeriodicUniform`) the constant and the
  threshold come first, before the cutoff, the kernel, the propagators, the measured particle, the
  datum, the time and, with spin, the finite spin set. The statements in `.GalerkinEndpoint`,
  `.GridEndpoint`, `.GalerkinSpin` and `.GridSpin` take the measured particle (and the spin set)
  before the constants; their constants do not depend on them, and the `_all` versions follow
  from them.
*  **Lemmas.** The Lean proof follows the argument of `app:source`. The differences are in form.
  `lem:kinetic-dyadic` is proved for finite matrices in eigenbasis coordinates and applied through
  eigen-decompositions constructed from the compact resolvent (`exists_exactEigen`,
  `exists_exactEigen_gL`). The separated blocks of `lem:kinetic-dyadic`, `lem:kinetic-leakage` and
  eq:kinetic-galerkin-transfer are bounded by absorbing `‖X‖` in the Sylvester equation
  (`norm_sylvester_le`), not through the integral eq:kinetic-transfer-integral; the bound
  `‖X‖ ≤ ‖F‖/(separation)` is the same. In the periodic endpoints the spectral cutoff `Λ = aK²` has
  `a = 1/(1024 m̄)` for the grid and `a = 1/(8 m̄)` for Galerkin. The grid-trajectory tails
  eq:kinetic-grid-flow-tails come from the grid tails of the release (`lem:grid-traj`,
  `lem:grid-tails`; `grid_traj_shells`), so eq:kinetic-data-consistency is not used.
  eq:kinetic-low-flow-error and eq:kinetic-leakage-state are not exported separately:
  `grid_core_pair` is eq:kinetic-grid-pairing, with the low grid rows bounded by the dyadic estimate
  and the high rows by the Sylvester block. `lem:kinetic-high` is the shell bound
  `‖W T_p φ‖ ≤ 3g²m√m (2T₀²B₀ + 4B)` in the kinetic weight `W`, that is `O(𝒟K^{3/2})`
  (`norm_wM_regKin_shells`). The separated transfer contributes the additional factor
  `‖Y‖ ≤ F_raw/(Λ − d) = O(K^{-5/2})`, since `F_raw = O(K^{-1/2})` and `Λ = aK²`.
  With the spectral factor `(2Λ)^{-1}` and the two data norms, the high-energy pairing is
  `O(𝒟² K^{-5/2} K^{-2} K^{3/2}) = O(𝒟² K^{-3})` (`grid_core_pair`, `grid_kinetic_explicit`).
* **Stopping corollaries.** As in the manuscript, the error at time `0` is bounded by the endpoint
  theorem at `t = 0`; the bounds have the form of eq:stopping-log and eq:free-stopping-log with
  the constant `2C`.
*  **Isolated grid.** In the isolated-system parts (17–31, 33 and 36), `H_L` is the `g_L`
  Hamiltonian without its zero mode, and the kernel class
  `PlaneWaveGridG.IsGridKernel (gLgamma L V_θ) (gLref L θ V_θ) m κ` (real and even,
  `|κ(ν)| ≤ (1 + V_θ)/(πL|ν|²)`, equal to `ĝ_L` for `|k_ν| ≤ K`, zero outside the cube `2K`, in
  unit-torus coefficients) has `κ(0) = 0`: the common zero-mode scalar `C₀` is left out of both
  Hamiltonians, which multiplies both trajectories by the same phase `e^{-iC₀t}` and leaves the
  kinetic energies unchanged. The free-space step carries this phase (`free_dyn_torus`). The nuclear
  phases are included (`posNucleiOf`). Accordingly `D_*` is measured with the zero-mode-free `H_L`
  there. `.OpenZeroMode` completes the correspondence with the physical Hamiltonians of `app:free`:
  `HasGLHamiltonianZ` keeps the zero mode (`H_L f = h ⟺ H_L^{(0)} f = h - C₀f`,
  `hasGLHamiltonianZ_iff`; propagators `cell_phase`), the kernel class `IsGridKernelZ` keeps
  `κ(0) = ĝ_L(0)` (eq:free-kinetic-kernel), the grid zero mode is the scalar `κ(0)z_g`
  (`Hgrid_update`) and every physical grid propagator is a phase times one of `G[κ⁰]` with the same
  kinetic expectations (`grid_phase`). The physical budget `D_* ≥ ‖φ₀‖ + ‖H_Lφ₀‖ + ‖H_L²φ₀‖` gives
  the shifted one up to `(1 + Q/4)²` (`budget_zero_mode`, `|C₀| ≤ Q/4`), so the `_phys` endpoints
  have the constant `freeKinCZ = (1 + Q/4)⁴ freeKinC`.
* **Free-space solution.** `ψ` is a supplied curve, defined for all `s ∈ ℝ` (as `e^{-isH_∞}ψ₀` is),
  with `ψ' = -iH_∞ψ` in `L²` and weak gradients at every time (`HasFreeHamiltonian`,
  `HasWeakGrad`), as in `prop:free-dyn`. The free kinetic energy is the form
  `freeKinQ sys p ∇ψ = (2m_p)^{-1} Σ_c ‖∂_{p,c}ψ‖²`, which is `⟨ψ, T_pψ⟩` whenever `T_pψ ∈ L²`
  (`exists_kinP`). The graph budget at time `t` is proved from the equation
  (`norm_conserved`, `norm_H_conserved`): no all-time graph budget is assumed. The general endpoint
  needs only `‖ψ₀‖ + ‖H_∞ψ₀‖ ≤ 𝒟_∞`; the compatible-cutoff versions use
  `‖ψ₀‖ + ‖H_∞ψ₀‖ + ‖H_∞²ψ₀‖ ≤ 𝒟` (with spin, the norms of the spin-inclusive space).
* **Hypotheses of `prop:free-kinetic-log`.** The leakage bounds hold on `[0, t]` (with spin: the
  squared norms summed over the components at each time); `ε_leak ≤ 1` is not needed. (H_dom) is the
  pair `HasGLHamiltonian … φ₀ h₀`, `HasGLHamiltonian … h₀ h₁` with
  `‖φ₀‖ + ‖h₀‖ + ‖h₁‖ ≤ D_*` (with spin: `√Σ‖φ_σ‖² + √Σ‖h₀σ‖² + √Σ‖h₁σ‖² ≤ D_*`); it is proved for
  the compatible cutoffs. Thresholds: `L ≥ 2π`, `m ≥ 8`, `K ≥ K₀ = cellK0 sys V_θ`, and for the
  explicit cutoffs `L ≥ freeKinL0 R₀ ρ` (`freeKinBOL0 R₀ ρ δ` with clamped nuclei, equal moving
  masses). The constant `freeKinC sys V_θ D̄` depends only on the masses and charges, the profile
  variation `V_θ` and the cutoff bound `D̄` — not on the nuclear positions.
* **Uniformity in `L`.** `sys` stores the clamped nuclei in unit-torus coordinates, and `hpos` places
  them at `-P_ℓ/L`; for a fixed molecule the system in the cell of size `L` is `sysAt sys P L`. The
  `_at` statements (`.OpenFixed`, and `_at_vbar`, `_phys_at` in `.OpenVbar`, `.OpenZeroMode`) and
  `free_kinetic_log_bo_uniform` have one constant for every `L` and every configuration `P` in
  `B_{R₀}(0)`; in `free_kinetic_log`, whose `sys` is fixed before
  `L`, clamped nuclei scale with `L` (without clamped nuclei the two forms agree).
* **Profile variation.** The statements of parts 26–31 and 33 take the exact total variation
  `V = tv R θ` (in the `∃` forms and the explicit-cutoff versions, the same `V` for every `L`).
  `.OpenVbar` proves that the constants `freeKinC`, `freeKinConstNBO`, `freeKinConstBO` and the
  threshold `cellK0` are increasing in `V` (every constant of the chain is built from the `L`-free
  constants `PlaneWaveGridG.gLzU`, `PlaneWaveGridG.gLAU`, `PlaneWaveGridG.gLmassConstU`,
  `FreeBoundary.gLtailMU`, `FreeBoundary.relBU`, `FreeBoundary.gridFlowConstU` by sums, products,
  powers and square roots), and states every endpoint for the profiles with `tv R θ ≤ V̄`, with the
  constant and the threshold at `V̄` (`_vbar`, and the `_phys` forms). The kernel majorant stays
  `(1 + tv R θ)ŵ` of the actual profile, as in eq:free-kinetic-kernel. `prop:free` and
  `prop:free-dyn` have the same forms (`PlaneWave.FreeBoundary.EnergyVbar`, `.DynamicsVbar`, and
  `.DynamicsZeroMode` for the physical zero modes).
* **eq:free-kinetic-N** is the explicit bound
  `(125/(4π³)) C D_*² (L³/N)[1 + t + log(2 + N^{1/3}/L)] + C(𝒟_∞ + D_*)(1 + t)ε` with
  `N = (4m + 1)³`; the factor `L³` is kept.

## Scope, retained hypotheses and statements not constructed

* The domain condition of `prop:free-dyn` (the transplanted cut initial state in `D(H_L²)`, with
  `H_L φ(0) = h₀`, `H_L h₀ = h₁`) is a hypothesis of `free_dyn_grid_gL` and
  `free_dyn_grid_gLU_schwartz` (any system, including clamped nuclei); it is proved for the
  non-Born–Oppenheimer system (`free_dyn_grid_nbo`) and, for cutoffs flat near the nuclei, with
  clamped nuclei (`free_dyn_grid_bo`), and there the regularity of `ψ_∞(0)` (second weak
  derivatives, the quotients by `|x_i - x_j|` and `|x_i - P_ℓ|` in `L²`) is derived from
  `H_∞ ψ_∞(0)`, `H_∞² ψ_∞(0) ∈ L²` (`free_dyn_grid_nbo_reg`, `cut_state_domain_reg_nuc`). That
  `ψ_∞(0) ∈ D(H_∞²)`, and the leakage bounds, remain hypotheses.
* Assumption (A) of `prop:free` (decay of the torus ground states) is a hypothesis of the lower
  bound; the Agmon decay of the free-space ground state, and `E_∞` bounding the energy form below
  on the sector, are hypotheses of both bounds. In `PlaneWave.FreeBoundary.FreeEnergyEndpoint` they
  are stated for the ground states: `Σ_i ∫ e^{2α|x_i|} |ψ_∞|² ≤ A` for the eigenfunction `ψ_∞`, and
  `Σ_i ∫ e^{2β(|x_i| - R_{L/2})} |u_L|² ≤ A′` for an `H²` torus ground state `u_L`, whose existence
  is part of the hypothesis. In the earlier modules they enter as mass bounds, for `C²`
  approximants, outside the retained region: the product region `{every particle in B_{R_L - w}(0)}`
  of the manuscript in `PlaneWave.FreeBoundary.ProductLocalisation`, the configuration-space ball
  `Σ_i |r_i|² < (R_L - w)²` before it.
* The free-space evolution `e^{-itH_∞}` is not constructed: the statements of `prop:free-dyn` take a
  solution curve `ψ` with `ψ′(t) = -i H_∞ ψ(t)` in `L²`.
* `prop:free` is formalised in each exchange sector; the identification of the spin-inclusive
  free-space ground energy with the minimum over the sectors is not formalised (`prop:free-dyn` has
  spin-inclusive versions). With clamped nuclei the cutoff family of `free_dyn_bo_uniform` needs
  equal masses of the moving particles: for the product cutoff the mass-weighted cancellation fails
  at `x_i = x_j` when `m_i ≠ m_j`.
* In `free_dyn_grid_gL` and `free_dyn_grid_gLU_schwartz` the continuous torus version `χ` of `f`
  is a hypothesis; it is constructed in the `_cell` versions (`cellObs`), for `f` continuous and
  vanishing outside a ball of radius `R_f < L/2`.
* The logarithmic kinetic-energy proof does not export every displayed intermediate equation of
  `app:source` as a separate theorem (eq:kinetic-data-consistency is not used;
  eq:kinetic-low-flow-error and eq:kinetic-leakage-state are inside `grid_core_pair`). For
  `prop:free-kinetic-log`, the
  free-space evolution remains a supplied solution, (H_dom) remains a hypothesis
  for a general cutoff, and the explicit clamped-nucleus cutoff requires equal
  moving masses.
* The constants are explicit but crude: the exponents of the polynomial bounds are far from optimal.

## Module index

The development names are those of the earlier packages (`dev/DevXX.lean`). The topics follow
the module docstrings. Their source-appendix labels that are not in the current manuscript
(`lem:qtail`, eq:tavg-quarter, `lem:retflow`, `lem:quarter-flow`, `prop:src-nc1`,
`lem:dressed-tails`, `lem:bulkobs`, `lem:bulkobsE`, `lem:h2`, `lem:a2`, `prop:tavgU`, `lem:h3`, `lem:res3`,
`lem:obs2`, `lem:obs3`) are earlier-draft labels; `comp:thm:completion` is the completion note's.

| Module | Former name | Topic |
|---|---|---|
| `PlaneWave.Certificate` | `PlaneWaveCertificate_release_4_32_1` | the ground energy (`thm:main`, `thm:nbo`), the propagators, the Galerkin dynamics and kinetic energy, spin |
| `PlaneWave.GridCore` | `PlaneWaveGrid_core_4_32_1` | the finite-dimensional grid core of `thm:grid-energy` |
| `PlaneWave.Grid` | `PlaneWaveGrid_release_4_32_1` | `thm:grid-energy`, full-kernel collocation, the grid dynamics and kinetic energy, spin |
| `PlaneWave.Source.BulkGeneratorPrototype` | `DevFS1` | Flux/source scoping prototype: the bulk generator of the block normal form |
| `PlaneWave.Source.SpectralLayer` | `DevFS3` | Flux/source build, block 1a: the abstract spectral layer |
| `PlaneWave.Source.LoewnerHeinz` | `DevFS4` | Löwner–Heinz comparison of fractional powers |
| `PlaneWave.Source.HotContentAbstract` | `DevFS5` | Flux/source build, block 1a: the abstract time-averaged hot-content bound |
| `PlaneWave.Source.LatticeSums` | `DevFS6` | Lattice sums on `ℤ³` |
| `PlaneWave.Source.QtailRecursion` | `DevFS7` | Flux/source build, block 1: the dyadic recursion of `lem:qtail` |
| `PlaneWave.Source.GalerkinSpectralLayer` | `DevFS9` | Flux/source build, block 1b: the spectral layer on the release's Galerkin space |
| `PlaneWave.Source.RetainedHamiltonian` | `DevFS10` | Flux/source build, block 1b: the retained Hamiltonian and its regularity |
| `PlaneWave.Source.ChannelKernels` | `DevFS11` | Flux/source build, block 1b: output-weighted Coulomb channel kernels |
| `PlaneWave.Source.RegisterStructure` | `DevFS12` | Flux/source build, block 1b: the register structure of the Galerkin Hamiltonian |
| `PlaneWave.Source.QuasiEigenstateTails` | `DevFS13` | Flux/source build, block 1b: tails of quasi-eigenstates, `lem:qtail` |
| `PlaneWave.Source.TimeAveragedHotContent` | `DevFS14` | Flux/source build, block 1b: the time-averaged hot content, eq:tavg-quarter |
| `PlaneWave.Source.WeightedMoments` | `DevFS15` | Flux/source build, block 1b: weighted moments of states with register tails |
| `PlaneWave.Source.GoodStates` | `DevFS16` | Flux/source build, block 1b: good states and the truncated datum |
| `PlaneWave.Source.TavgQuarterExplicit` | `DevFS17` | Flux/source build, block 1b: eq:tavg-quarter with explicit `K`-dependence |
| `PlaneWave.Source.RetainedFlow` | `DevFS18` | Flux/source build, block 1b: the retained flow, `lem:retflow`, `lem:quarter-flow`, `prop:src-nc1` |
| `PlaneWave.Source.ChannelPotentials` | `DevFS19` | Flux/source build, block 2a: channels and the potential on `ℓ²(ℤ^{3η})` |
| `PlaneWave.Source.BulkGenerator` | `DevFS20` | Flux/source build, block 2b: the bulk generator `Σ_b` for all channels |
| `PlaneWave.Source.Conjugation` | `DevFS21` | Flux/source build, block 2c: conjugation by `e^{Σ}` (Mathlib only) |
| `PlaneWave.Source.TransformedHamiltonian` | `DevFS22` | Flux/source build, block 2d: the transformed Hamiltonian on `D(T)` |
| `PlaneWave.Source.AssemblyIdentity` | `DevFS23` | Flux/source build, block 2e: the retained block, Duhamel, the assembly identity |
| `PlaneWave.Source.HardyBound` | `DevFS24` | Flux/source build, block 3a: Hardy on `ℓ²` and the bound `‖V_b‖ ≤ C K` |
| `PlaneWave.Source.FibreBounds` | `DevFS25` | Flux/source build, block 3b: the fibre bounds of the bulk generator |
| `PlaneWave.Source.RetainedCorrection` | `DevFS26` | Flux/source build, block 3c: `‖W Σ_b‖ ≤ C` and the retained correction |
| `PlaneWave.Source.ExponentialBounds` | `DevFS27` | Flux/source build, block 3d: vector bounds for `e^{Z}` (Mathlib only) |
| `PlaneWave.Source.DressedState` | `DevFS28` | Flux/source build, block 3e: the dressed state (`lem:dressed-tails`) |
| `PlaneWave.Source.GoodStatesBothSpaces` | `DevFS29` | Flux/source build, block 4a: good states on both spaces |
| `PlaneWave.Source.ObservableNonsecular` | `DevFS30` | Flux/source build, block 3f: the observable and the nonsecular terms |
| `PlaneWave.Source.FirstRetainedCorrection` | `DevFS31` | Flux/source build, block 3g: the first retained correction on good states, and the coupling |
| `PlaneWave.Source.SourceTerm` | `DevFS32` | Flux/source build, block 3h: the source term |
| `PlaneWave.Source.TruncatedObservable` | `DevFS33` | Flux/source build, block 4b: reduction to the truncated observable (`lem:bulkobs`, `lem:bulkobsE`) |
| `PlaneWave.Source.BulkLatticeCounts` | `DevFS34` | Flux/source build, block 5: lattice counts for the bulk hierarchy |
| `PlaneWave.Source.KernelOperators` | `DevFS35` | Flux/source build, block 5: kernel operators on a finite configuration set |
| `PlaneWave.Source.BulkBlock` | `DevFS36` | Flux/source build, block 5: the bulk block `H₂^bb` (`lem:h2`) |
| `PlaneWave.Source.BulkRotation` | `DevFS37` | Flux/source build, block 5: the bulk rotation `Σ₂^bb` |
| `PlaneWave.Source.BulkRotationSchur` | `DevFS38` | Flux/source build, block 5: Schur bounds for the bulk rotation |
| `PlaneWave.Source.BulkGoodStates` | `DevFS39` | Flux/source build, block 5: good-state bounds for the bulk class |
| `PlaneWave.Source.MixedClass` | `DevFS40` | Flux/source build, block 5: the mixed class |
| `PlaneWave.Source.PotentialTails` | `DevFS41` | Flux/source build, block 5: potential tails and the Coulomb form bound |
| `PlaneWave.Source.TaylorRemainder` | `DevFS42` | Flux/source build, block 5: vector Taylor expansions and the first-rotation remainder |
| `PlaneWave.Source.RetainedLedger` | `DevFS43` | Flux/source build, block 5: the exact ledger of the retained rotations |
| `PlaneWave.Source.RetainedRotations` | `DevFS44` | Flux/source build, block 5: the retained rotations on `E_n` |
| `PlaneWave.Source.RefinedBudgets` | `DevFS45` | Flux/source build, block 5: goodness with refined budgets |
| `PlaneWave.Source.LedgerGoodStates` | `DevFS46` | Flux/source build, block 5: the ledger on good states |
| `PlaneWave.Source.RetainedComparison` | `DevFS47` | Flux/source build, block 5: the retained comparison (`thm:src3`, first term) |
| `PlaneWave.Source.TrajectoryBudgets` | `DevFS48` | Flux/source build, block 5: the budgets of the trajectories |
| `PlaneWave.Source.RetainedComparisonExplicit` | `DevFS49` | Flux/source build, block 5: the retained comparison with explicit constants |
| `PlaneWave.Source.SourceNonsecularTerms` | `DevFS50` | Flux/source build, block 5: the source and the nonsecular terms with explicit constants |
| `PlaneWave.Source.SourceNonsecularExplicit` | `DevFS51` | Flux/source build, block 5: the source and the nonsecular terms, explicit |
| `PlaneWave.Source.Src3Terms` | `DevFS52` | Flux/source build, block 5: `thm:src3` with explicit constants |
| `PlaneWave.Source.Src3Explicit` | `DevFS53` | Flux/source build, block 5: `thm:src3` with explicit constants |
| `PlaneWave.Source.PowerPolylog` | `DevFS54` | Flux/source build, block 5: power-polylog bounds in the cutoff (Mathlib only) |
| `PlaneWave.Source.CutoffBasicConstants` | `DevFS55` | Flux/source build, block 5: the cutoff dependence of the basic constants |
| `PlaneWave.Source.CutoffScales` | `DevFS56` | Flux/source build, block 5: the cutoff dependence of the scales and the derived constants |
| `PlaneWave.Source.CutoffLedger` | `DevFS57` | Flux/source build, block 5: the cutoff dependence of the ledger and of the budgets |
| `PlaneWave.Source.CutoffErrorConstant` | `DevFS58` | Flux/source build, block 5: the cutoff dependence of the budgets and of the error constant |
| `PlaneWave.Source.Src3Conditional` | `DevFS59` | Flux/source build, block 5: `thm:src3` and `cor:stopping3` (conditional) |
| `PlaneWave.Source.Stopping3Conditional` | `DevFS60` | Flux/source build, block 5: `cor:stopping3` (conditional) |
| `PlaneWave.Source.FirstSourceRound` | `DevFS61` | The first source round: `lem:phi`, `prop:src-decomp`, `prop:src1`, `thm:src1` |
| `PlaneWave.Source.SourceLeftovers` | `DevFS62` | Source side, leftovers: the rest of `lem:phi` and `lem:a2` |
| `PlaneWave.Flux.ForceForm` | `DevFX1` | Flux route, part 1: the force form, eq:flux-id, eq:hardy-a and `thm:flux` |
| `PlaneWave.Flux.FluxDressing` | `DevFX2` | Flux route, part 2: `prop:elim`, the flux dressing `Y = [Σ_b, A_{p₀}]` |
| `PlaneWave.Flux.Flux2Split` | `DevFX3` | Flux route, part 3: the exact split of `thm:flux2` and its assembly |
| `PlaneWave.Flux.PhaseTools` | `DevFX4` | Flux route, part 4: tools for `prop:phase` |
| `PlaneWave.Flux.PhaseBulkBlock` | `DevFX5` | Flux route, part 5: the bulk block of `prop:phase` |
| `PlaneWave.Flux.Flux2` | `DevFX6` | Flux route, part 6: `prop:phase` and `thm:flux2` |
| `PlaneWave.SourceBand.ThinShellCounts` | `DevSB1` | Source band block, part 1: thin-shell lattice counts and `lem:thinschur` |
| `PlaneWave.SourceBand.Band` | `DevSB2` | Source band block, part 2: `lem:band` |
| `PlaneWave.SourceBand.BandGalerkin` | `DevSB3` | Source band block, part 3: `lem:band` for the Galerkin states; `lem:good-stab` (band) |
| `PlaneWave.SourceBand.SpectatorBound` | `DevSB4` | Source band block, part 4: the channel potentials and the spectator bound |
| `PlaneWave.SourceBand.MovingRegister` | `DevSB5` | Source band block, part 5: K2 for a channel that moves the register |
| `PlaneWave.SourceBand.SrcRes` | `DevSB6` | Source band block, part 6: `prop:src-res` |
| `PlaneWave.SourceBand.BandTails` | `DevSB7` | Source band block, part 7: the band bounds of `lem:qtail` and `prop:tavgU` |
| `PlaneWave.SamePair.LatticeCounts` | `DevH1` | Same-pair third order, part 1: lattice counts |
| `PlaneWave.SamePair.SameChannelKernel` | `DevH2` | Same-pair third order, part 2: the same-channel kernel of `[Σ₂^bb, W_N]` |
| `PlaneWave.SamePair.LatticeSums` | `DevH3` | Same-pair third order, part 3: two more lattice sums |
| `PlaneWave.SamePair.ThirdOrderKernel` | `DevH4` | Same-pair third order, part 4: the kernel of `P H^{(3)} P` and its channel words |
| `PlaneWave.SamePair.RetainedThirdOrder` | `DevH5` | Same-pair third order, part 5: the same-pair component of `H₃^ret` and `lem:h3` |
| `PlaneWave.SamePair.Res3` | `DevH6` | Same-pair third order, part 6: `lem:res3` for the same-pair component |
| `PlaneWave.SamePair.ThirdGenerator` | `DevH7` | Same-pair third order, part 7: the same-pair third generator `Σ₃^sp` |
| `PlaneWave.SamePair.Package` | `DevH8` | Same-pair third order, part 8: orders of the constants and the package |
| `PlaneWave.Observable.SecondOrder` | `DevO1` | `lem:obs2` (restated): the second-order observable correction |
| `PlaneWave.FluxBox.BigBox` | `DevFY1` | Flux route, stage 2, part 1: the big box |
| `PlaneWave.FluxBox.CentreOfMassSplit` | `DevFY2` | Flux route, stage 2, part 2: the exact centre-of-mass split of the force |
| `PlaneWave.FluxBox.BoxLatticeTools` | `DevFY3` | Flux route, stage 2, part 3: lattice tools for the box |
| `PlaneWave.FluxBox.BoxHardy` | `DevFY4` | Flux route, stage 2, part 4: Hardy bounds for channel-dominated box kernels |
| `PlaneWave.FluxBox.BoxCommutator` | `DevFY5` | Flux route, stage 2, part 5: the box commutator on good states |
| `PlaneWave.FluxBox.FlatElimination` | `DevFY6` | Flux route, stage 2, part 6: tails on the box and the flat elimination |
| `PlaneWave.FluxBox.FlatLedger` | `DevFY7` | Flux route, stage 2, part 7: the flat ledger along the trajectory |
| `PlaneWave.FluxBox.LongHops` | `DevFY8` | Flux route, stage 2, part 8: long hops and the flat endpoint |
| `PlaneWave.FluxBox.FlatEndpoint` | `DevFY9` | Flux route, stage 2, part 9: the endpoint of the flat elimination |
| `PlaneWave.FluxBox.FlatRemainderClasses` | `DevFY10` | Flux route, stage 2, part 10: the classes of the flat remainder |
| `PlaneWave.FluxBox.ComDressing` | `DevFY11` | Flux route, stage 2, part 11: the centre-of-mass dressing |
| `PlaneWave.FluxBox.ResonantComFlux` | `DevFY12` | Flux route, stage 2, part 12: the resonant com flux at the target rate |
| `PlaneWave.FluxBox.ComElimination` | `DevFY13` | Flux route, stage 2, part 13: the com elimination and its endpoint |
| `PlaneWave.FluxBox.ComRemainderClasses` | `DevFY14` | Flux route, stage 2, part 14: the classes of the com remainder |
| `PlaneWave.FluxBox.SymbolCurrentKernel` | `DevFY15` | Flux route, stage 2, part 15: the kernel of the symbol current |
| `PlaneWave.FluxBox.KineticFloor` | `DevFY16` | Flux route, stage 2, part 16: the kinetic floor and the pinned symbol current |
| `PlaneWave.FluxBox.SecondDressing` | `DevFY17` | Flux route, stage 2, part 17: the second dressing `Y₂` |
| `PlaneWave.FluxBox.CommutatorSamePair` | `DevFY18` | Flux route, stage 2, part 18: the commutator `[W, Y₂]`, the same-pair part |
| `PlaneWave.FluxBox.CommutatorCrossChannel` | `DevFY19` | Flux route, stage 2, part 19: the commutator `[W, Y₂]`, the cross-channel part |
| `PlaneWave.FluxBox.CommutatorTargetRate` | `DevFY20` | Flux route, stage 2, part 20: the commutator `[W, Y₂]` at the target rate |
| `PlaneWave.FluxBox.ThirdDressing` | `DevFY21` | Flux route, stage 3, part 21: the third dressing `Y₃` |
| `PlaneWave.FluxBox.FarColdWords` | `DevFY22` | Flux route, stage 3, part 22: the words of the far–cold kernel |
| `PlaneWave.FluxBox.ClassHardy` | `DevFY23` | Flux route, stage 3, part 23: Hardy on classes and the line tools |
| `PlaneWave.FluxBox.ConservedWeightSchur` | `DevFY24` | Flux route, stage 3, part 24: conserved-weight Schur, radial and ball sums, moments |
| `PlaneWave.FluxBox.FarColdGeometry` | `DevFY25` | Flux route, stage 3, part 25: geometry and energies of the far–cold paths |
| `PlaneWave.FluxBox.FarColdDressing` | `DevFY26` | Flux route, stage 3, part 26: the far–cold dressing and its three shapes |
| `PlaneWave.FluxBox.FarColdHops` | `DevFY27` | Flux route, stage 3, part 27: the hop bounds of the far–cold words |
| `PlaneWave.FluxBox.FirstHops` | `DevFY28` | Flux route, stage 3, part 28: the first hops from cold, and line squares of hops |
| `PlaneWave.FluxBox.FarColdColdInputs` | `DevFY29` | Flux route, stage 3, part 29: the far–cold words against cold inputs |
| `PlaneWave.FluxBox.FarColdDressingCold` | `DevFY30` | Flux route, stage 3, part 30: the far–cold dressing against cold inputs (P2) |
| `PlaneWave.FluxBox.Round3Commutator` | `DevFY31` | Flux route, stage 3, part 31: the round-3 commutator outside `C × C` |
| `PlaneWave.FluxBox.MiddleSplitWords` | `DevFY32` | Flux route, stage 3, part 32: the `C × C` block, middle-split words |
| `PlaneWave.FluxBox.SameChannelSetting` | `DevFY33` | Flux route, stage 3, part 33: the same-channel word in `C × C` — setting |
| `PlaneWave.FluxBox.ReflectionLatticeSums` | `DevFY34` | Flux route, stage 3, part 34: lattice sums for the reflection pairing |
| `PlaneWave.FluxBox.PairingGeometry` | `DevFY35` | Flux route, stage 3, part 35: the same-channel word — geometry of the pairing |
| `PlaneWave.FluxBox.PairingLatticeSums` | `DevFY36` | Flux route, stage 3, part 36: the same-channel word — lattice sums of the pairing |
| `PlaneWave.FluxBox.PairingDefect` | `DevFY37` | Flux route, stage 3, part 37: the same-channel word — the pairing defect |
| `PlaneWave.FluxBox.PairingTrace` | `DevFY38` | Flux route, stage 3, part 38: the same-channel word — the trace |
| `PlaneWave.FluxBox.SharedComAlignment` | `DevFY39` | Flux route, stage 3, part 39: the shared com words — alignment and Hardy twice |
| `PlaneWave.FluxBox.SharedComCoordinate` | `DevFY40` | Flux route, stage 3, part 40: the shared com words with a common coordinate |
| `PlaneWave.FluxBox.SharedComDegenerate` | `DevFY41` | Flux route, stage 3, part 41: the shared com words, degenerate triples |
| `PlaneWave.FluxBox.SharedComCases` | `DevFY42` | Flux route, stage 3, part 42: the shared com words — the case analysis |
| `PlaneWave.FluxBox.TrilinearReduction` | `DevFY43` | Flux route, stage 3, part 43: the `C × C` block — reduction to trilinear forms |
| `PlaneWave.FluxBox.WordsGoodStates` | `DevFY44` | Flux route, stage 3, part 44: the `C × C` block — good-state bounds of the words |
| `PlaneWave.FluxBox.MiddleSplitCold` | `DevFY45` | Flux route, stage 3, part 45: the `C × C` block — the middle-split words on cold inputs |
| `PlaneWave.FluxBox.BlockBound` | `DevFY46` | Flux route, stage 3, part 46: the `C × C` block — the shared words, the rest and the block bound |
| `PlaneWave.FluxBox.Round3GoodStates` | `DevFY47` | Flux route, stage 3, part 47: round 3 on good box states |
| `PlaneWave.FluxBox.OutOfBoxErrors` | `DevFY48` | Flux route, stage 3, part 48: the dressings on good box states and the out-of-box errors |
| `PlaneWave.FluxBox.BoxLedger` | `DevFY49` | Flux route, stage 3, part 49: the box ledger |
| `PlaneWave.FluxBox.DataScaling` | `DevFY50` | Flux route, stage 3, part 50: scaling of the data |
| `PlaneWave.FluxBox.RoundConstants` | `DevFY51` | Flux route, stage 3, part 51: the cutoff dependence of the round constants |
| `PlaneWave.FluxBox.CompositeConstants` | `DevFY52` | Flux route, stage 3, part 52: the cutoff dependence of the composite constants |
| `PlaneWave.FluxBox.Flux3` | `DevFY53` | Flux route, stage 3, part 53: `thm:flux3` |
| `PlaneWave.Observable.ThirdOrderSamePair` | `DevO2` | `lem:obs3`, restated for the same-pair class |
| `PlaneWave.FluxSourceSpin` | `DevSF1` | The flux and source theorems on the spin-inclusive space |
| `PlaneWave.KineticCompletion.InverseMismatch` | `DevKC1` | Kinetic completion, part 1: the inverse mismatch relative to one direction |
| `PlaneWave.KineticCompletion.CrossCommutators` | `DevKC2` | Kinetic completion, part 2: directional derivatives and the cross commutators |
| `PlaneWave.KineticCompletion.FirstRotationWords` | `DevKC3` | Kinetic completion, part 3: the multi-channel first-rotation words |
| `PlaneWave.KineticCompletion.QuarterPowerWeights` | `DevKC4` | Kinetic completion, part 4: quarter-power weights for the same-channel generator |
| `PlaneWave.KineticCompletion.Completion` | `DevKC5` | Kinetic completion, part 5: the completion and the unconditional theorems |
| `PlaneWave.KineticCompletion.CompletionClauses` | `DevKC6` | Kinetic completion, part 6: the remaining clauses of `comp:thm:completion` |
| `PlaneWave.Auxiliary.FluxSourceClauses` | `DevAX2` | Auxiliary clauses of the manuscript, part 2: `app:flux` and `app:source` |
| `PlaneWave.Auxiliary.DressedTails` | `DevAU1` | Auxiliary claims, part 1: the remaining clauses of `lem:dressed-tails` |
| `PlaneWave.Auxiliary.LogFreePhi` | `DevAU2` | Auxiliary claims, part 2: the log-free bounds of `lem:phi` |
| `PlaneWave.Auxiliary.FourierDomination` | `DevAU5` | Auxiliary claims, part 5: Fourier domination and the uniform Kato–Rellich bound for truncated kernels (`lem:fourier-domination`, `lem:grid-KR` (i)) |
| `PlaneWave.Auxiliary.AliasGrid` | `DevAU6` | Auxiliary claims, part 6: the alias bound and the grid operator (`lem:grid-KR` (ii), (iv)) |
| `PlaneWave.Auxiliary.PotentialTails` | `DevAU7` | Auxiliary claims, part 7: the potential tails of the truncated kernels |
| `PlaneWave.Auxiliary.GalerkinDynamics` | `DevAX1` | Auxiliary clauses of the manuscript, part 1: Galerkin dynamics |
| `PlaneWave.FreeBoundary.Scaling` | `DevFB1` | `lem:scaling` (Appendix `app:free`): the lattice estimates of the range-truncated kernel |
| `PlaneWave.FreeBoundary.RangeCut` | `DevFB2` | `app:free`, part 2: the Fourier coefficients of the range-truncated kernel (eq:rangecut) |
| `PlaneWave.FreeBoundary.CubeHamiltonian` | `DevFB3` | `app:free`, part 3: the `g_L` Hamiltonian on the cube and its Galerkin energy bound |
| `PlaneWave.FreeBoundary.GridCoreGeneral` | `DevFB4` | `app:free`, part 4: the grid core with a general Galerkin reference kernel |
| `PlaneWave.FreeBoundary.TorusGroundEnergy` | `DevFB5` | `app:free`, part 5: the `g_L` Hamiltonian on all cubes and the torus ground energy |
| `PlaneWave.FreeBoundary.GridEnergy` | `DevFB6` | `app:free`, part 6: the grid energy theorem for the range-truncated kernel |
| `PlaneWave.FreeBoundary.RetainedRegion` | `DevFB7` | `app:free`, part 7: the position-space kernel, the retained region and the torus Fourier coefficients |
| `PlaneWave.FreeBoundary.PositionPotential` | `DevFB8` | `app:free`, part 8: the position-space `g_L` potential on the configuration torus |
| `PlaneWave.FreeBoundary.CompletedHamiltonian` | `DevFB9` | `app:free`, part 9: the completed `g_L` Hamiltonian on `H²` and the variational bound for `C²` torus states |
| `PlaneWave.FreeBoundary.Transplant` | `DevFB10` | `app:free`, part 10: transplanting free-space trial states to the torus |
| `PlaneWave.FreeBoundary.UpperComposite` | `DevFB11` | `app:free`, part 11: the upper half of the composite bound |
| `PlaneWave.FreeBoundary.IMS` | `DevFB12` | `app:free`, part 12: IMS localisation |
| `PlaneWave.FreeBoundary.LocalisationPair` | `DevFB13` | `app:free`, part 13: the explicit localisation pair and the upper bound |
| `PlaneWave.FreeBoundary.TorusIMS` | `DevFB14` | `app:free`, part 14: IMS localisation on the configuration torus |
| `PlaneWave.FreeBoundary.LowerBound` | `DevFB15` | `app:free`, part 15: the lower bound of `prop:free` under assumption (A) |
| `PlaneWave.FreeBoundary.UniformGridCore` | `DevFL1` | `app:free`, `L`-uniform constants, part 1: the grid core in physical units |
| `PlaneWave.FreeBoundary.UniformCubic` | `DevFL2` | `app:free`, `L`-uniform constants, part 2: the cubic Galerkin error with the sharper Sobolev constant |
| `PlaneWave.FreeBoundary.UniformGridEnergy` | `DevFL3` | `app:free`, `L`-uniform constants, part 3: `thm:grid-energy` for `g_L` with constants uniform in `L` |
| `PlaneWave.FreeBoundary.UniformFreeEnergy` | `DevFL4` | `app:free`, `L`-uniform constants, part 4: eq:free-energy with an `L`-uniform grid constant |
| `PlaneWave.FreeBoundary.Dynamics` | `DevFB16` | `prop:free-dyn`: the free-space step of the free-boundary dynamics |
| `PlaneWave.FreeBoundary.Propagator` | `DevFB17` | `prop:free-dyn`: the propagator of the `g_L` Hamiltonian |
| `PlaneWave.FreeBoundary.GridDynamicsInterface` | `DevFB18` | `thm:grid-dyn-sharp` for `g_L`: the continuum interface (compression, symmetry, relative bound, tails) |
| `PlaneWave.FreeBoundary.GridDynamicsSharp` | `DevFB19` | `thm:grid-dyn-sharp` for `g_L`: the sharp observable bound on the Fourier side |
| `PlaneWave.FreeBoundary.GridDynamicsTheorem` | `DevFB20` | `thm:grid-dyn-sharp` for `g_L` in position space |
| `PlaneWave.FreeBoundary.ProductLocalisation` | `DevFB21` | `prop:free` in the product geometry: the product localisation pair |
| `PlaneWave.FreeBoundary.Complexity` | `DevFB22` | `prop:free`: the basis-size complexity `N = O(ε⁻¹ log³(1/ε))` |
| `PlaneWave.FreeBoundary.FreeDynamicsGrid` | `DevFB23` | `prop:free-dyn`: the free-space evolution against the grid |
| `PlaneWave.FreeBoundary.GridDynamicsUniform` | `DevFB24` | `prop:free-dyn`: `L`-uniform first-order estimates of the grid step (physical units) |
| `PlaneWave.FreeBoundary.GridSecondOrderPhysical` | `DevFB25` | the second-order estimates of the grid step in the physical weight |
| `PlaneWave.FreeBoundary.GridSecondMomentPhysical` | `DevFB26` | second moments and duality on the grid in the physical weight |
| `PlaneWave.FreeBoundary.GridObservablePhysical` | `DevFB27` | the observable error and its rates in physical units |
| `PlaneWave.FreeBoundary.GridDynamicsUniformTheorem` | `DevFB28` | `thm:grid-dyn-sharp` and `prop:free-dyn` for `g_L` with `L`-uniform constants |
| `PlaneWave.FreeBoundary.ObservableMomentsUniform` | `DevFB29` | `prop:free-dyn`: the moments of a fixed Schwartz observable, uniformly in `L` |
| `PlaneWave.FreeBoundary.DomainWeakCalculus` | `DevFB30` | the cut initial state in `D(H_L²)`, part 1: weak calculus and trigonometric tests |
| `PlaneWave.FreeBoundary.MassWeightedCutoff` | `DevFB31` | part 2: mass-weighted cutoffs |
| `PlaneWave.FreeBoundary.SingularCommutator` | `DevFB32` | part 3: the singular part of the double commutator (non-Born–Oppenheimer) |
| `PlaneWave.FreeBoundary.SecondCommutator` | `DevFB33` | part 4: the free-space identities of the second commutator |
| `PlaneWave.FreeBoundary.CommutatorTransplant` | `DevFB34` | part 5: the transplanted commutator in `D(H_L)` |
| `PlaneWave.FreeBoundary.CutStateDomain` | `DevFB35` | part 6: the domain theorem with `L`-free bounds |
| `PlaneWave.FreeBoundary.FreeDynamicsNonBO` | `DevFB36` | `prop:free-dyn` without the domain hypotheses (non-Born–Oppenheimer) |
| `PlaneWave.FreeBoundary.CutoffScaling` | `DevFB37` | mass-weighted cutoffs: scaling, and `F(Σ_i m_i \|x_i\|²)` |
| `PlaneWave.FreeBoundary.CellObservable` | `DevFB38` | `prop:free-dyn`: the torus version of the observable, constructed |
| `PlaneWave.FreeBoundary.Mollification` | `DevFB39` | free-space regularity, part 1: mollification |
| `PlaneWave.FreeBoundary.KineticRegularity` | `DevFB40` | part 2: the weak kinetic relation gives `H²` |
| `PlaneWave.FreeBoundary.HardyInequality` | `DevFB41` | part 3: Hardy's inequality |
| `PlaneWave.FreeBoundary.RegularityBridge` | `DevFB42` | part 4: the data of the domain theorem from the Hamiltonian relations |
| `PlaneWave.FreeBoundary.FreeDynamicsEndpoint` | `DevFB43` | `prop:free-dyn` in the form of the manuscript |
| `PlaneWave.FreeBoundary.HardyNuclear` | `DevFB44` | free-space regularity, part 5: Hardy's inequality for one particle and a point |
| `PlaneWave.FreeBoundary.CoulombForm` | `DevFB45` | part 6: the Coulomb form |
| `PlaneWave.FreeBoundary.FormApproximation` | `DevFB46` | part 7: smooth approximation in the form norm |
| `PlaneWave.FreeBoundary.AgmonApproximation` | `DevFB47` | part 8: approximate ground states from an eigenfunction |
| `PlaneWave.FreeBoundary.TorusApproximation` | `DevFB48` | part 9: approximate torus ground states |
| `PlaneWave.FreeBoundary.FreeEnergyEndpoint` | `DevFB49` | `prop:free` in the form of the manuscript |
| `PlaneWave.FreeBoundary.NuclearPotential` | `DevFB50` | clamped nuclei, part 1: `Vu` as pair and nuclear Hardy functions, flatness near the nuclei, the nuclear weight |
| `PlaneWave.FreeBoundary.NuclearRegularity` | `DevFB51` | part 2: the regularity bridge with nuclei |
| `PlaneWave.FreeBoundary.NuclearSingularIdentity` | `DevFB52` | part 3: the nuclear singular identity |
| `PlaneWave.FreeBoundary.NuclearCommutator` | `DevFB53` | part 4: `T([K, χ]u)` in `D(H_L)` with clamped nuclei |
| `PlaneWave.FreeBoundary.CutStateDomainNuclear` | `DevFB54` | part 5: the domain theorem with clamped nuclei |
| `PlaneWave.FreeBoundary.RegularityBridgeNuclear` | `DevFB55` | part 6: the domain theorem from the Hamiltonian relations |
| `PlaneWave.FreeBoundary.ProductCutoff` | `DevFB56` | part 7: the product cutoff, exchange symmetry and flatness |
| `PlaneWave.FreeBoundary.ProductCutoffCancellation` | `DevFB57` | part 8: the product cutoff as a mass-weighted cutoff (equal masses) |
| `PlaneWave.FreeBoundary.ProductCutoffRegions` | `DevFB58` | part 9: the regions of the product cutoff, flatness after scaling |
| `PlaneWave.FreeBoundary.FreeDynamicsBO` | `DevFB59` | part 10: `prop:free-dyn` with clamped nuclei without the domain hypothesis |
| `PlaneWave.FreeBoundary.FreeDynamicsBOUniform` | `DevFB60` | part 11: `prop:free-dyn` with clamped nuclei, one constant for all `L ≥ L₀` |
| `PlaneWave.FreeBoundary.SpinFreeStep` | `DevFB61` | spin, part 1: the free-space step with internal spin |
| `PlaneWave.FreeBoundary.SpinFreeDynamicsGrid` | `DevFB62` | part 2: the two steps composed, homogeneity of the grid step |
| `PlaneWave.FreeBoundary.SpinFreeDynamicsEndpoint` | `DevFB63` | part 3: `prop:free-dyn` with internal spin in the form of the manuscript |
| `PlaneWave.FreeBoundary.EnergyVbar` | — | `prop:free`, eq:free-energy and the complexity for profiles with `V_θ ≤ V̄` |
| `PlaneWave.FreeBoundary.DynamicsVbar` | — | `prop:free-dyn` for profiles with `V_θ ≤ V̄` |
| `PlaneWave.FreeBoundary.DynamicsZeroMode` | — | `prop:free-dyn` for the physical cell and grid Hamiltonians (zero modes kept) |
| `PlaneWave.Auxiliary.Duhamel` | `DevAU3` | Auxiliary claims, part 3: the Duhamel identity (eq:duhamel) |
| `PlaneWave.Auxiliary.Fold` | `DevAU4` | Auxiliary claims, part 4: the fold identity for a general trigonometric polynomial (`lem:fold`) |
| `PlaneWave.KineticLog.Sylvester` | — | `thm:kinetic-log`, part 1: matrix operators, Sylvester absorption, time integration |
| `PlaneWave.KineticLog.DyadicDuhamel` | — | part 2: the dyadic spectral Duhamel estimate (`lem:kinetic-dyadic`) |
| `PlaneWave.KineticLog.ExactSpectral` | — | part 3: the spectral decomposition of the periodic Hamiltonian |
| `PlaneWave.KineticLog.SpectralTails` | — | part 4: Fourier tails of inverse-weighted low-energy states (`lem:kinetic-low`, exact side) |
| `PlaneWave.KineticLog.GalerkinConsistency` | — | part 5: the Galerkin consistency estimates |
| `PlaneWave.KineticLog.Galerkin` | — | part 6: the Galerkin retained-state comparison |
| `PlaneWave.KineticLog.GalerkinEndpoint` | — | part 7: eq:kinetic-retained-galerkin, `thm:kinetic-log` and `cor:stopping-log` (Galerkin) |
| `PlaneWave.KineticLog.GalerkinSpin` | — | part 8: the Galerkin endpoints with finite internal spin |
| `PlaneWave.KineticLog.GridSpectral` | — | part 9: spectral data of the grid comparison (common shift, grid eigenbasis) |
| `PlaneWave.KineticLog.GridConsistency` | — | part 10: the grid consistency error (`lem:kinetic-strong`, `lem:kinetic-low`, `lem:kinetic-leakage`, grid forms) |
| `PlaneWave.KineticLog.GridDuhamel` | — | part 11: the filtered grid comparison |
| `PlaneWave.KineticLog.GridShells` | — | part 12: momentum shells of the trajectories; the full-power high-kinetic estimate (`lem:kinetic-high`) |
| `PlaneWave.KineticLog.GridTraj` | — | part 13: the shells of the exact and grid trajectories |
| `PlaneWave.KineticLog.GridRates` | — | part 14: the rates of the raw grid constants |
| `PlaneWave.KineticLog.GridEndpoint` | — | part 15: `thm:kinetic-log` and `cor:stopping-log` (grid, full kernel class) |
| `PlaneWave.KineticLog.GridSpin` | — | part 16: the periodic grid endpoints with finite internal spin |
| `PlaneWave.KineticLog.OpenExact` | — | part 17: `prop:free-kinetic-log`, the exact side of the isolated (range-cut) cell |
| `PlaneWave.KineticLog.OpenGridSpectral` | — | part 18: grid spectral data of the isolated cell, uniform in `L` |
| `PlaneWave.KineticLog.OpenConsistency` | — | part 19: the grid consistency error of the isolated cell |
| `PlaneWave.KineticLog.OpenDuhamel` | — | part 20: the filtered grid comparison on the isolated cell |
| `PlaneWave.KineticLog.OpenTraj` | — | part 21: trajectory shells in the physical weight |
| `PlaneWave.KineticLog.OpenRates` | — | part 22: the rates of the cell constants, uniform in `L` |
| `PlaneWave.KineticLog.OpenCell` | — | part 23: the cell-to-grid kinetic estimate, uniform in `L` |
| `PlaneWave.KineticLog.OpenFree` | — | part 24: free-space calculus for the kinetic localisation |
| `PlaneWave.KineticLog.OpenLocal` | — | part 25: the spatial localisation of the kinetic energy |
| `PlaneWave.KineticLog.OpenEndpoint` | — | part 26: `prop:free-kinetic-log` (general cutoff, (H_dom)) |
| `PlaneWave.KineticLog.OpenCompat` | — | part 27: `prop:free-kinetic-log`, its forms and compatible cutoffs |
| `PlaneWave.KineticLog.OpenUniform` | — | part 28: `prop:free-kinetic-log` with the explicit cutoffs, uniform in `L` |
| `PlaneWave.KineticLog.OpenStop` | — | part 29: `cor:free-stopping-log` and eq:free-kinetic-N |
| `PlaneWave.KineticLog.OpenSpin` | — | part 30: `prop:free-kinetic-log` and `cor:free-stopping-log` with spin |
| `PlaneWave.KineticLog.OpenSpinCompat` | — | part 31: compatible cutoffs with spin |
| `PlaneWave.KineticLog.PeriodicUniform` | — | part 32: the periodic endpoints with the constants first |
| `PlaneWave.KineticLog.OpenFixed` | — | part 33: a fixed molecule in growing cells (one constant for every `L` and nuclear configuration) |
| `PlaneWave.KineticLog.PeriodicN` | — | part 34: the periodic endpoints in terms of `N` |
| `PlaneWave.KineticLog.PeriodicMasses` | — | part 35: the periodic endpoints for arbitrary positive masses (charge rescaling) |
| `PlaneWave.KineticLog.OpenVbar` | — | part 36: the isolated-system endpoints for profiles with `V_θ ≤ V̄` |
| `PlaneWave.KineticLog.OpenZeroMode` | — | part 37: the zero mode of the cell interaction; the endpoints for the physical cell and grid Hamiltonians |
