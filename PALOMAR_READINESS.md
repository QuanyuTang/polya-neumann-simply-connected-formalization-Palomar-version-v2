# Palomar readiness report

Date of the record: 2026-10-07. The Linux command transcript in
`verification/local-build.txt` is inherited from the Aristotle Palomar export and was
not rerun from a commit of this V2 repository. It is retained as a historical
portability record, not as evidence for a particular V2 commit. The source, metadata,
checksum, and compatibility audits below were performed while preparing this snapshot.
Before public submission, rerun the full build and sandboxed Comparator from the exact
public commit and append its full SHA and results.

## 1. Versions

| | Original | Ported (this repository) |
| --- | --- | --- |
| Lean | `leanprover/lean4:v4.28.0` | `leanprover/lean4:v4.35.0-rc2` |
| Mathlib | `v4.28.0` (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`) | `v4.35.0-rc2` (`065356127b1dc0016f66b7283ce0ce2c4055aa55`) |

Palomar's current minimum toolchain was checked on 2026-10-07 at
`PalomarRegistry/PalomarSubmission/toolchains.json`: `"minimum": "v4.35.0-rc2"`
(also the `toolchain_floor` in its `verification-profile.json`). The official
`PalomarRegistry/PalomarTemplate` (commit `2891de4c48955af824969a263d31b25e7a9a1406`) uses
Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2`, the versions used here. The project
`lean-toolchain` and the `lean-toolchain` of the pinned Mathlib commit are both exactly
`leanprover/lean4:v4.35.0-rc2`.

All entries of `lake-manifest.json` are public GitHub repositories pinned to full
40-character commit SHAs: mathlib4, plausible, LeanSearchClient, import-graph,
ProofWidgets4, aesop, quote4, batteries (all `leanprover-community`) and
`leanprover/lean4-cli`, that is, exactly Mathlib's own pinned dependency closure.

## 2. Main files changed or added

* `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: new toolchain and Mathlib pin;
  `Challenge` and `Solution` `lean_lib`s added as in the PalomarTemplate; default targets
  `RequestProject.Main`, `Challenge`, `Solution`.
* `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`,
  `PALOMAR_READINESS.md` (new); `scripts/` (unmodified copies of the current
  PalomarTemplate scripts).
* `RequestProject/AxiomCheck.lean`, `verification/Audit.lean`: `module` headers added;
  the audit now also checks the Palomar wrapper theorems and the definitional equality
  of the Palomar definitions with those of `RequestProject/Defs.lean`.
* `README.md`, `FORMALIZATION.md`, `.github/workflows/lean.yml`, `.gitignore`,
  `verification/SHA256SUMS`, `verification/local-build.txt`: updated.
* Proof development: 133 of the 312 `RequestProject/*.lean` modules (besides
  `AxiomCheck.lean`) received compatibility edits for the Lean/Mathlib upgrade, for
  example: `MemLp` is now defined as `eLpNorm f p μ < ∞` (so `h.1` became
  `h.aestronglyMeasurable` and anonymous constructors were dropped); new explicit
  arguments (`eLpNorm_norm`, `Lp.eLpNorm_le_of_ae_tendsto`); `simpa` proofs that relied on
  unfolding `Function.comp`, `Pi` operations, `IntegrableOn` or unapplied definitions
  during the final definitional check, which now fails under the module system, were
  given the corresponding simp lemmas or an explicit `unfold`; renamed lemmas.
  `RequestProject/Shift.lean` registers a few high-priority instances that are the
  standard Mathlib instances, to fix elaboration under the stricter unifier.
  `RequestProject/Defs.lean` is byte-for-byte unchanged, and no theorem statement on
  the path to the main results was changed. The edited modules are: ArcLength, Area,
  AreaTrace, BasePoint, BiLipschitz, BoundaryChart, BoundaryConnected, BoundaryFourier,
  BoundaryLoop, BoundaryRegularity, BoundaryWalk, BZField, BZFlow, BZLevel, BZMono, Cayley,
  CayleyFactorization, ChainRule, Coercivity, ConormalNormalization,
  CorrectedKernelEnergy, CorrectedKernelSmooth, CurveContinuity, CutTrace,
  DiskHardyDerivative, DiskHardyExtension, DiskHarmonicModes, Driven,
  FactorialGaugeInverse, Finite, FiniteRankCompletion, FixedSpace,
  FourierFiniteRankRegularity, FourierLipschitz, FractionalInterp, FractionalRows,
  FractionalSobolev, GreenWinding, Herglotz, HerglotzDensity, HerglotzForm, HerglotzModes,
  HerglotzPoincare, HerglotzReduction, HilbertSchmidt, LipschitzChange,
  LocalConformalBoundaryLipschitz, LocalConformalBoundaryLoad, LocalConformalFourierCollar,
  LocalConformalHardyExtension, LocalConformalHardyPrimitive,
  LocalConformalHerglotzBoundaryTransfer, LocalConformalPeriodicBoundaryNull,
  LocalConformalRadialVekua, LocalConformalReducedBoundaryBound,
  LocalConformalRegularObservation, LocalConformalRotation,
  LocalConformalRoughGaugeRegularity, LocalConformalRoughHardySupport,
  LocalConformalVekuaConormalBridge, LocalConformalVekuaForward, LocalConformalVekuaSeries,
  LocalConformalVekuaTransport, LocalDirichletBoundaryJets,
  LocalDirichletBoundaryRegularity, LocalDirichletFlattenedEquation,
  LocalDirichletNormalBootstrap, LocalDirichletNormalRecovery,
  LocalDirichletRectangularSobolev, LocalDirichletTangentialBootstrap,
  LpBoundedMultiplier, Main, MatrixHS, MollifierEstimate, MollifierL2, NegativeIndex,
  NeumannBoundaryPole, NeumannBoundaryResolvent, NeumannH1FirstOrderGreen,
  NeumannMultiplicity, NeumannNormalizedBoundary, NeumannOperator,
  NeumannRegularSelfAdjoint, NeumannResonanceDimension, NeumannSobolev, NeumannSpectral,
  NormalizedPeriodicBoundary, ObservationDual, ObservationHSEnergy,
  PeriodicFourierDerivative, PeriodicRegularContinuity, PeriodicRegularSelfAdjoint,
  PhysicalCauchyBoundaryExtension, PhysicalDrivenHardyRegularity,
  PhysicalDrivenIntegrable, PhysicalDrivenKernelConormal, PhysicalDrivenL2Reconstruction,
  PhysicalDrivenMoments, PhysicalDrivenReconstruction, PhysicalMomentHardyCriterion,
  PhysicalMomentPrimitive, Poincare, PolynomialTransmutation, PositiveFourierBasis,
  ReconBasic, ReconBessel, ReconChordArc, ReconDensity, ReconFourierBasic, ReconModes,
  ReconOuter, Reconstruction, ReconVanish, RellichCompact, Reparam,
  RiemannMappingBoundaryCrosscut, RiemannMappingBoundaryDerivative,
  RiemannMappingBoundaryOscillation, RiemannMappingBoundaryParamRegularity,
  RiemannMappingCapWinding, RiemannMappingCaratheodory, RiemannMappingInterior,
  RiemannMappingSmoothBoundary, RoughVekuaTransport, SawtoothKernel, SchurKernel, Shift,
  SobolevCircle, SobolevMultiplier, Spectrum, TraceH1, VolterraUniqueness, WeightedMass.
  (This list was obtained by comparing with the checksums of the original v4.28.0
  release recorded in the previous `verification/SHA256SUMS`.)

No module was deleted.

## 3. Theorem names

| | Declaration | Module |
| --- | --- | --- |
| Main theorem | `PolyaNeumann.strict_neumann_polya` (alias `main`) | `RequestProject.Main` |
| Counting form | `PolyaNeumann.strict_neumann_polya_count` (alias `main_counting`) | `RequestProject.Main` |
| Challenge theorem | `PalomarPolyaNeumann.strict_neumann_polya` | `Challenge` (stated), `Solution` (proved) |
| Challenge theorem | `PalomarPolyaNeumann.strict_neumann_polya_count` | `Challenge` (stated), `Solution` (proved) |

The statements of the four `PolyaNeumann`/top-level theorems are the original ones
(printed by `verification/Audit.lean`):

```text
PolyaNeumann.strict_neumann_polya (Ω : Set ℂ) (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
  (hsc : SimplyConnectedSpace ↑Ω) (j : ℕ) (hj : 1 ≤ j) :
  volume Ω * neumannEigenvalue Ω j < ENNReal.ofReal (4 * Real.pi * ↑j)
PolyaNeumann.strict_neumann_polya_count (Ω : Set ℂ) (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
  (hsc : SimplyConnectedSpace ↑Ω) (E : ℝ) (hE : 0 < E) :
  volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * Real.pi) < ↑(neumannCount Ω (ENNReal.ofReal E))
```

The Challenge statements are the same with `PalomarPolyaNeumann` definitions.

## 4. `lake build`

The table in this section is the historical Linux record imported from the Aristotle
export; it is not a clean-checkout claim about a committed V2 revision. Current Windows
preparation checks additionally compiled `RequestProject.Main`, `Challenge`, and
`Solution` successfully (see `verification/local-build.txt`). A fresh Linux build from
the eventual public commit remains required before Palomar submission.

| Command | Result |
| --- | --- |
| `lake env lean --version` | `Lean (version 4.35.0-rc2, x86_64-unknown-linux-gnu, commit 11acb17ec6b07a8f9e9173e6845197929540936b, Release)` |
| `lake exe cache get` | success (Mathlib cache present) |
| `lake build RequestProject.Main` | success, 4214 jobs |
| `lake build Challenge` | success, 8932 jobs (one expected "declaration uses `sorry`" warning per Challenge theorem) |
| `lake build Solution` | success, 9230 jobs |

The build prints non-fatal linter and deprecation warnings only.

Not built: the seven experimental modules `ConformalConormalGeometry`,
`ConformalH1Pullback`, `FourierCoefficientGain`, `HerglotzKernelForm`,
`LocalConformalObservationKernel`, `NeumannFractionalResolvent`, `PhysicalCauchyJump`.
They are imported by no other module (in particular not by `RequestProject.Main` or
`Solution`), are byte-for-byte identical to the original release, were never built by
its CI (which built only `+RequestProject.Main`), and they fail to compile with
v4.35.0-rc2. At least one of them (`LocalConformalObservationKernel`) uses section
variables in proofs without including them, which Lean rejected well before v4.28, so
they were most likely already broken before the port. They are not part of any claim,
are not default targets, and do not enter the Comparator check. `lake build
RequestProject` (the whole glob) therefore fails on exactly these seven modules.

## 5. `lake comparator`

The Comparator results below are also inherited from the historical export and were
run unsandboxed. They have not yet been reproduced from a V2 commit in Palomar's Linux
sandbox.

`bwrap` could be installed but cannot create namespaces in this environment
(`bwrap: Creating new namespace failed: Operation not permitted`), so the toolchain's
`lake comparator` was run with `--inadvisably-no-sandbox`, which only disables the
sandbox (the run is not hardened against a malicious project, but the checks are the
same):

* `lake comparator --inadvisably-no-sandbox` (with `comparator.json`): **accepted**
  ("Lean default kernel accepts the solution", "Your solution is okay!", exit code 0).
* Same, with the configuration `scripts/verify-comparator.sh` generates (Palomar-style
  `external_kernels`: the toolchain's `nanoda_bin` and `con-ron`): **accepted** by
  con-ron, nanoda and the Lean kernel, exit code 0.

Palomar itself runs Comparator in its sandbox; `./scripts/verify-comparator.sh` reproduces
that locally on a machine where `bwrap` works.

To obtain identical statement terms, `Solution.lean` locally removes (`attribute
[-instance]`) the project's high-priority instance
`PolyaNeumann.instIsTopologicalAddGroupComplex` before restating the definitions; with
it, `neumannEigenvalue` elaborated with a different (definitionally equal) auxiliary
proof term than in `Challenge.lean`, which Comparator rejects.

## 6. Axiom audit

The exit-code-0 audit result below is the historical Linux result. The current Windows
run of `RequestProject/AxiomCheck.lean` succeeds and reports only the three permitted
standard axioms; the full guarded `verification/Audit.lean` process can terminate
without diagnostics on this machine while expanding all checks. Re-run the guarded
audit from the exact public commit on Linux before registration.

`lake env lean RequestProject/AxiomCheck.lean` and the guarded
`lake env lean verification/Audit.lean` (exit code 0) give, for `main`, `main_counting`,
`PolyaNeumann.strict_neumann_polya`, `PolyaNeumann.strict_neumann_polya_count`,
`PalomarPolyaNeumann.strict_neumann_polya`, `PalomarPolyaNeumann.strict_neumann_polya_count`
and nine principal intermediate theorems:

```text
depends on axioms: [propext, Classical.choice, Quot.sound]
```

The audit also checks `PalomarPolyaNeumann.X = PolyaNeumann.X := rfl` for all eleven
statement-side definitions.

## 7. `sorry` counts

* Substantive proof development (`RequestProject/`, including the seven unbuilt
  experimental modules) and `Solution.lean`: **0** `sorry`, **0** `admit`, **0**
  `native_decide`, **0** `axiom` declarations; `sorry_in_definitions = 0`.
* `Challenge.lean`: **2** deliberate statement `sorry`s (one per Challenge theorem), as
  required by the Palomar format.

(Full-text search with `rg -w 'sorry|admit|native_decide'` over all `.lean` files; the
only other hits are the English word "admit" in two docstrings and the word `sorry` in a
comment of `Solution.lean`.)

## 8. Challenge dependency audit

* `Challenge.lean` has a `module` header, a single import `public import Mathlib`, and no
  `RequestProject` import; its transitive import closure is Lean core plus Mathlib and
  Mathlib's own pinned dependencies (Batteries, Aesop, Qq, ProofWidgets, Plausible,
  LeanSearchClient, ImportGraph).
* 128 lines, 6688 bytes (limits: 1000 lines / 100 KiB; target 300 lines / 32 KiB).
* Defines, with docstrings, `IsDomain`, `IsLipschitzDomain`, `L2`, `coordDir`,
  `TestFunction`, `IsWeakGradient`, `H1`, `neumannEnergy`, `rayleigh`,
  `neumannEigenvalue`, `neumannCount` (no definition holes; `definition_names` is empty)
  and states the two theorems.
* `Solution.lean` does not import `Challenge`.

## 9. Mechanical requirements

| Requirement | Status |
| --- | --- |
| Every `.lean` file starts with a `module` header | yes (`python3 scripts/check-lean-sources.py`, the PalomarTemplate copy of Palomar's source check: no issues) |
| Every `.lean` file ≤ 10,000 lines | yes (largest: `LocalDirichletFlattenedEquation.lean`, 2270 lines) |
| Challenge < 1000 lines and < 100 KiB | yes (128 lines, 6.5 KiB) |
| Checkout < 500 MiB | yes (about 6 MB) |
| No compiled artifacts (`.olean`, `.ilean`, `.so`, `.o`, `.a`, `.trace`, …) | none |
| No Git LFS pointers, symlinks or submodules | none |
| Exactly one licence file at the root | `LICENSE`, the standard Apache License 2.0 text (identical to the PalomarTemplate `LICENSE`); `formalization.yaml` has `license: "Apache-2.0"` |
| `formalization.yaml` | `version: "v0.4"`; passes `ruby scripts/validate-formalization.rb` and Palomar's `load_formalization_metadata` (from `PalomarSubmission/scripts/submission_contract.py`); arXiv `math.SP`, `math.AP` and MSC2020 `35P15`, `35P20`, `35J05` checked against Palomar's taxonomy files |
| Mathlib pin and toolchain agree exactly | yes |
| Git dependencies public GitHub, full SHAs | yes |

The licence covers this repository's own files only, not Mathlib, other dependencies,
or the cited mathematical literature.

## 10. Metadata and authorship

The metadata names Quanyu Tang and Zuoqin Wang as the authors and responsible
maintainers, records the AI-assisted Aristotle/Codex workflow, and identifies the
immutable manuscript source commit. The repository is licensed under Apache-2.0.
The review status is deliberately `self-assessed`: the local checks below are not
an independent mathematical peer review and this snapshot has not been
submitted to or registered by Palomar.

## 11. Verdict for this snapshot

The repository has the Palomar project layout, pinned Lean/Mathlib revisions,
module headers, a short Mathlib-only Challenge, a proved Solution, a Comparator
configuration, filled metadata, and a checked Lean-source checksum list. The
default theorem path and the Palomar interface are the audited scope. The seven
documented experimental modules remain outside that path and are not claimed as
part of the submitted result.

The historical local Comparator run recorded here was unsandboxed because this Windows
environment cannot provide Linux `bwrap` namespaces. It is not a substitute for checking
the current V2 commit. Before a public submission, run the same commit in Palomar's
sandbox or on Linux and record the resulting registry status. Until then, describe this
repository as Palomar-compatible and prepared for submission, not as registered or
endorsed by Palomar.
