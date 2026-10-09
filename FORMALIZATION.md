# Formalization status

The project is a Lean 4 formalization of the strict Neumann Pólya inequality in the accompanying paper. The plane is represented by `ℂ`, and the Neumann spectrum is defined by the variational min–max construction in `RequestProject/Defs.lean`.

## Main results

`RequestProject/Main.lean` proves:

- `PolyaNeumann.strict_neumann_polya`: for every bounded simply connected Lipschitz domain and every `j ≥ 1`,
  `volume Ω * neumannEigenvalue Ω j < ENNReal.ofReal (4 * π * j)`;
- `PolyaNeumann.strict_neumann_polya_count`: the equivalent strict counting inequality for every positive energy;
- the smooth-domain quantitative estimate and the approximation and boundary-parametrization results used to pass to bounded Lipschitz domains.

The main proof chain includes the Neumann variational spectrum, boundary transport, Cayley and phase estimates, the Herglotz reduction, the small-energy argument, the smooth approximation of Lipschitz domains, and the limiting argument.

## Verification

Run:

```text
lake exe cache get
lake build RequestProject.Main
lake build Challenge
lake build Solution
lake env lean verification/Audit.lean
```

`verification/Audit.lean` checks the final inequalities, the spectral,
reconstruction, approximation, and Cayley bridge theorems, and the two Palomar
wrapper theorems of `Solution.lean`. Every guarded
declaration is required to use exactly:

```text
propext, Classical.choice, Quot.sound
```

There is no `SorryAx` in the dependency closure of these theorems. No code-level
`sorry`, `admit`, or `native_decide` is used in the proof development or in
`Solution.lean`; the only `sorry`s in the repository are the two deliberate
statement placeholders of the Palomar `Challenge.lean`. The compiler may still emit linter
suggestions such as unused simp arguments; these are non-fatal cleanup messages.

The GitHub Actions workflow repeats this build and audit on the pinned Lean and
Mathlib revisions. `verification/SHA256SUMS` records the hashes of every Lean
source file and the audit, while `verification/local-build.txt` records the
successful local run. The final theorem path is modular: a small number of
experimental modules outside the `RequestProject.Main` import closure are not
part of the audited result.

## Source organization

The `RequestProject` directory contains the complete Lean source tree. Files are organized by the mathematical stages of the proof: definitions and spectrum, Sobolev and compactness results, boundary geometry, transport and Cayley operators, Herglotz waves, phase counting, smooth approximation, and the final theorem in `Main.lean`.

The source uses Lean `leanprover/lean4:v4.35.0-rc2` and Mathlib `v4.35.0-rc2`
(commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`); it was ported from the
original Lean/Mathlib `v4.28.0` version (see `PALOMAR_READINESS.md`). The
accompanying paper is currently in preparation and will be posted on arXiv
shortly. The Palomar v1.0.0 snapshot is recorded at
[PALOMAR-2026-10-09-000007, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-09-000007&version=1).
