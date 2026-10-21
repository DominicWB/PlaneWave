# PlaneWave

Lean 4 proofs of spatial discretisation error bounds for Coulomb quantum
simulation. The accompanying research paper is released separately and is not
part of this repository.

The project covers periodic plane-wave and spatial-grid estimates,
unconditional Galerkin kinetic-energy and stopping-power bounds, projection
flux, and free-boundary energy and dynamical comparisons under their stated
hypotheses. The free-boundary dynamical theorems include moving nuclei,
clamped nuclei, and internal spin.

## Requirements and build

Install [Elan](https://lean-lang.org/install/manual/) and Git. The repository
pins **Lean 4.32.1**, **Mathlib v4.32.1**, and all dependency revisions in
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`. Run from the
repository root:

```sh
lake exe cache get
lake build
```

`lake exe cache get` is recommended for downloading precompiled Mathlib; it
is not necessary if Mathlib is already built. The build may need several GB
of memory. Do not run `lake update` when reproducing the locked version.

## Proof and axiom checks

The umbrella module `PlaneWave.lean` imports all **222** library modules.
`AxiomCheck.lean` contains **869** `#print axioms` commands for key results:

```sh
lake env lean AxiomCheck.lean
```

The expected foundational axioms are `propext`, `Classical.choice` and
`Quot.sound`. The GitHub Actions workflow builds the library and checks the
complete axiom-report sequence against these allowed axioms.

## Main declarations

| Result | Lean declaration |
|---|---|
| Periodic ground-energy error | `PlaneWaveCertificate.periodicMolecularCubicError` |
| Projection flux | `FSFlux.thm_flux3` |
| Unconditional kinetic-energy bound | `FSAsymp.thm_src3_uncond` |
| Stopping-power bound | `FSAsymp.cor_stopping3_uncond` |
| Free-boundary energy and mode-count bound | `FreeBoundary.free_energy_endpoint`, `FreeBoundary.free_energy_complexity` |
| Non-Born–Oppenheimer dynamics | `FreeBoundary.free_dyn_nbo_spin_uniform` |
| Clamped-nuclei dynamics | `FreeBoundary.free_dyn_bo_spin_uniform` |

For example, in a Lean file:

```lean
import PlaneWave
#check FSAsymp.thm_src3_uncond
#check FreeBoundary.free_dyn_bo_spin_uniform
```

## Scope

“Unconditional” for the Galerkin kinetic-energy bound refers to the proved
third-order completion, not to removal of the theorem's regularity assumptions.
The free-boundary energy comparison assumes the specified ground-state
localisation, and its ground-energy statement is in a scalar exchange sector.
The free-boundary dynamical estimates assume an exact free-space solution
and local leakage. A canonical free-space propagator and a spin-sector
minimisation theorem for the free-boundary ground energy are not part of this
formalisation.

The separate research paper gives the full mathematical statements and proofs.
When citing the code, identify the repository's release tag or commit hash.
