# PlaneWave

Lean 4 proofs accompanying **Basis-set error bounds for first-quantised quantum simulation of
chemistry**. The project formalises plane-wave and specified spatial-grid discretisation bounds
for Coulomb Hamiltonians, including ground energies, smooth position observables, logarithmic
kinetic-energy bounds and stopping-power estimates.

This package contains **262 library modules** and an axiom-check file with **1,179 reports**.
Lean and Mathlib are pinned to **v4.32.1**; `lake-manifest.json` records the exact dependency
commits. The report count is a count of checks, not distinct theorems.

## Build and check

Install Git and the Lean toolchain manager `elan`, then run these commands from the directory
containing `lakefile.toml`. The toolchain is selected by `lean-toolchain`.

Linux or macOS:

```bash
lake exe cache get
bash scripts/build.sh
```

Windows PowerShell:

```powershell
lake exe cache get
.\scripts\build.ps1
```

The cache command downloads compiled Mathlib dependencies; it does not verify this project's
proofs. The build script runs `lake build` and then elaborates `AxiomCheck.lean`. The local axiom
scripts reject failed elaboration and axioms other than `propext`, `Classical.choice` and
`Quot.sound`, including `sorryAx`. To rerun only that check after a successful build, use
`bash scripts/check_axioms.sh` or `.\scripts\check_axioms.ps1`.

Generated build and axiom logs are written in the project root and excluded from version
control, together with `.lake/`. Keep `lean-toolchain` and the dependency lockfile unchanged
when reproducing this release. The
[GitHub workflow](.github/workflows/ci.yml) runs the build and additionally requires the complete
axiom-report sequence to match `AxiomCheck.lean`, in order, with no unexpected output.

## Results and scope

- **Periodic systems:** ground-energy bounds cover fixed and quantum nuclei, including electronic
  spin and the stated exchange sectors. Smooth-observable and kinetic-energy estimates concern
  the specified Galerkin and truncated-kernel grid Hamiltonians.
- **Dynamical data:** the manuscript's bounds use initial states in the domain of the squared
  Hamiltonian, with the stated norm budgets. Smooth-observable estimates require the observable
  regularity specified in the statements. Projected initial states are not renormalised unless
  a normalisation result is explicitly invoked.
- **Isolated-system energies:** the two-sided result uses clamped nuclei in a specified scalar
  exchange sector, an exponentially localised free-space ground state, and the separate
  finite-volume ground-state localisation assumption. The corresponding sufficient basis-size
  bound is conditional on these inputs; the package does not identify this sector energy with
  the full spin-inclusive free-space ground energy.
- **Isolated-system dynamics:** the free-space solution is supplied, rather than constructed by
  the formalisation. Wavefunction and shell-gradient leakage remain hypotheses. The cut initial
  state must satisfy the squared-Hamiltonian-domain condition with uniform bounds; the package
  proves this condition for the stated compatible cutoffs. Explicit clamped-nucleus product
  cutoffs require equal moving-particle masses. Spin-inclusive dynamical versions are included.

The latest modules include periodic kinetic endpoints for arbitrary positive masses and in
terms of the one-particle basis size, as well as isolated-system endpoints for bounded profile
variation and physical cell and grid Hamiltonians with their zero modes retained.

## Principal declarations

The following are entry points, not a replacement for the hypotheses in their Lean statements.
The [full correspondence](docs/FORMALISATION.md) lists supporting results and conventions.

| Result | Selected declarations |
|---|---|
| Periodic ground energy | `PlaneWaveCertificate.periodicMolecularCubicError`, `PlaneWaveCertificate.periodicCoulombCubicError` |
| Periodic truncated-kernel grid energy | `PlaneWaveGrid.periodicCoulombSectorKernelGridError` |
| Smooth observables with spin | `PlaneWaveDynamics.thm_dyn_spin`, `PlaneWaveSpin.thm_grid_dyn_sharp_spin` |
| Periodic kinetic energy, positive masses, spin and basis-size conversion | `KineticLog.thm_kinetic_log_galerkin_spin_pos_N`, `KineticLog.thm_kinetic_log_grid_spin_pos_N` |
| Isolated-system energy and sufficient basis size | `FreeBoundary.free_energy_endpoint_vbar`, `FreeBoundary.free_energy_complexity_vbar` |
| Isolated-system smooth observables, physical Hamiltonians | `FreeBoundary.free_dyn_nbo_spin_uniform_phys`, `FreeBoundary.free_dyn_bo_spin_uniform_phys` |
| Isolated-system kinetic energy and stopping power, physical Hamiltonians | `KineticLog.free_kinetic_log_spin_phys_at`, `KineticLog.free_stopping_log_spin_phys_at` |

`PlaneWave.lean` imports all library modules. The main source directories are
`PlaneWave/KineticLog/` for the logarithmic kinetic bounds and
`PlaneWave/FreeBoundary/` for isolated systems; the older flux and source estimates remain part
of the library. See [docs/FORMALISATION.md](docs/FORMALISATION.md) for the complete module index,
manuscript-label map and proof correspondence.

## Verification

Compiling the library checks every proof. `AxiomCheck.lean`, run by the build scripts and by the
GitHub workflow, confirms that each of the 1,179 checked statements depends only on `propext`,
`Classical.choice` and `Quot.sound`; no module contains `sorry`. A clean build of the project
takes about an hour on two CPU cores with 7 GB of memory, with the Mathlib dependencies
downloaded by `lake exe cache get`.
