# Strict Neumann Pólya inequality: Lean formalization

**Authors:** Quanyu Tang and Zuoqin Wang

This repository contains a modular Lean 4 formalization of the strict Neumann
Pólya inequality for bounded simply connected planar Lipschitz domains, together
with a Challenge/Solution interface prepared for the
[Palomar Registry](https://palomar-registry.org/). This repository is a
pre-submission snapshot; it has not yet been registered by Palomar.
The accompanying paper is currently in preparation; the authors plan to post a
public version on arXiv. No arXiv identifier is available yet.

[Lean source](RequestProject/Main.lean) ·
[Palomar Challenge](Challenge.lean) ·
[Palomar Solution](Solution.lean) ·
[Verification audit](verification/Audit.lean) ·
[Paper PDF](paper/N_simply_connected_strict_v3.pdf) ·
[Paper source](paper/N_simply_connected_strict_v3.tex) ·
[Palomar readiness report](PALOMAR_READINESS.md)

## 1. The substantive Lean theorem

For every bounded simply connected Lipschitz domain \(\Omega\subset\mathbb R^2\cong\mathbb C\)
and every integer \(j\ge 1\),

\[
  |\Omega|\,\mu_j(\Omega) < 4\pi j .
\]

In Lean (`RequestProject/Main.lean`):

```lean
theorem PolyaNeumann.strict_neumann_polya (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (j : ℕ) (hj : 1 ≤ j) :
    volume Ω * neumannEigenvalue Ω j < ENNReal.ofReal (4 * π * j)
```

`main` is a stable top-level alias of this theorem.

* `IsLipschitzDomain Ω` (`RequestProject/Defs.lean`): `Ω` is open and connected
  and near every boundary point it is, after a rigid motion, the region strictly
  above the graph of a Lipschitz function.
* `neumannEigenvalue Ω j` is the Courant–Fischer min–max value of the Rayleigh
  quotient `∫_Ω |∇u|² / ‖u‖²` over `(j+1)`-dimensional subspaces (`H¹(Ω)` is
  defined through weak gradients in `L²(Ω)`). Eigenvalues are indexed from
  `μ₀ = 0` and repeated according to multiplicity. The development proves that
  these values coincide with the spectrum of the constructed self-adjoint
  Neumann operator (`PolyaNeumann.neumannEigenvalue_eq_spectral`).

## 2. Counting-function version

With `N_N(E) = #{j ≥ 0 : μ_j(Ω) < E}` (including `μ₀ = 0`), for every `E > 0`

\[
  N_N(E) > \frac{|\Omega|\,E}{4\pi}.
\]

```lean
theorem PolyaNeumann.strict_neumann_polya_count (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (E : ℝ) (hE : 0 < E) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) <
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal)
```

`main_counting` is its top-level alias.

## 3. Palomar Challenge/Solution interface

* [`Challenge.lean`](Challenge.lean) imports **only Mathlib**. It restates, in
  the namespace `PalomarPolyaNeumann`, every definition needed to read the result
  (`IsDomain`, `IsLipschitzDomain`, `L2`, `coordDir`, `TestFunction`,
  `IsWeakGradient`, `H1`, `neumannEnergy`, `rayleigh`, `neumannEigenvalue`,
  `neumannCount`, copied verbatim from `RequestProject/Defs.lean`, with
  docstrings) and states the two theorems
  `PalomarPolyaNeumann.strict_neumann_polya` and
  `PalomarPolyaNeumann.strict_neumann_polya_count`. Their proofs are the
  deliberate `sorry`s that the Palomar format requires of a challenge statement;
  these are the only `sorry`s in the repository.
* [`Solution.lean`](Solution.lean) imports `RequestProject.Main`, repeats the
  same definitions and statements, and proves the two theorems by applying
  `PolyaNeumann.strict_neumann_polya` and `PolyaNeumann.strict_neumann_polya_count`.
  It contains no `sorry`, no custom axiom and no `native_decide`. Its proved
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
* [`comparator.json`](comparator.json) lists the two theorems, no definition
  holes, and the permitted axioms `propext`, `Quot.sound`, `Classical.choice`.

`verification/Audit.lean` additionally checks by `rfl` that each
`PalomarPolyaNeumann` definition is definitionally equal to its
`PolyaNeumann` counterpart.

## 4. Versions

| Component | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc2` (`lean-toolchain`) |
| Mathlib | tag `v4.35.0-rc2`, commit `065356127b1dc0016f66b7283ce0ce2c4055aa55` (`lake-manifest.json`) |

The Mathlib revision's own `lean-toolchain` is also `leanprover/lean4:v4.35.0-rc2`.
The development was originally written for Lean/Mathlib `v4.28.0` and was ported
to the Palomar minimum toolchain `v4.35.0-rc2`; see
[`PALOMAR_READINESS.md`](PALOMAR_READINESS.md).

## 5. Reproduction

```text
lake env lean --version
lake exe cache get
lake build RequestProject.Main
lake build Challenge
lake build Solution
lake env lean RequestProject/AxiomCheck.lean
lake env lean verification/Audit.lean
python3 scripts/check-lean-sources.py
./scripts/verify-comparator.sh        # lake comparator, needs bubblewrap
```

The bare `lake build` builds the default targets `RequestProject.Main`,
`Challenge` and `Solution`. The first build of the ≈100,000-line development
takes a while; `verification/local-build.txt` records a complete local run.

## 6. Axiom audit

`verification/Audit.lean` uses `#guard_msgs` to require that `main`,
`main_counting`, `PolyaNeumann.strict_neumann_polya`,
`PolyaNeumann.strict_neumann_polya_count`, the principal intermediate results,
and the two Palomar wrapper theorems depend on exactly

```text
propext, Classical.choice, Quot.sound
```

In particular `sorryAx` does not occur. The proof development and `Solution.lean`
contain no `sorry`, `admit` or `native_decide`, and the project declares no
custom axioms.

## 7. Relationship with the paper

`paper/N_simply_connected_strict_v3.tex` (Theorem 1 and the counting form stated
right after it) is the mathematical source.

| Paper | Palomar Challenge | Proof development |
| --- | --- | --- |
| Theorem 1: \(|\Omega|\mu_j(\Omega)<4\pi j\), \(j\ge1\) | `PalomarPolyaNeumann.strict_neumann_polya` | `PolyaNeumann.strict_neumann_polya` (`main`) |
| \(N_N(E)>E|\Omega|/(4\pi)\), \(E>0\) | `PalomarPolyaNeumann.strict_neumann_polya_count` | `PolyaNeumann.strict_neumann_polya_count` (`main_counting`) |

The paper's formal-verification paragraph records the original Lean 4.28.0
formalization and the Lean 4.35.0-rc2 compatibility port; the statements are
unchanged in the port.

## 8. Scope and the meaning of a Palomar record

A Palomar registration records that a fixed public repository commit passed the
registry's machine checks and automated review. It is not a journal publication,
expert peer review, novelty certificate, or importance certificate. Readers
should inspect the definitions in `Challenge.lean` and the exact registered
commit themselves.

Seven experimental modules in `RequestProject/` (`ConformalConormalGeometry`,
`ConformalH1Pullback`, `FourierCoefficientGain`, `HerglotzKernelForm`,
`LocalConformalObservationKernel`, `NeumannFractionalResolvent`,
`PhysicalCauchyJump`) are not imported by `RequestProject.Main`, by
`Solution.lean` or by any other module. They are unchanged from the original
repository, were not built by its CI, do not build with `v4.35.0-rc2`, and are
not part of any claim.

## Files

| File or directory | Purpose |
| --- | --- |
| `RequestProject/Main.lean` | Final theorems and the entry point of the proof development |
| `RequestProject/*.lean` | Definitions and proof stages |
| `Challenge.lean`, `Solution.lean`, `comparator.json` | Palomar interface |
| `formalization.yaml` | Palomar / mathlib-initiative metadata (v0.4) |
| `verification/Audit.lean` | Guarded statement and axiom audit |
| `RequestProject/AxiomCheck.lean` | Plain `#print axioms` report |
| `verification/SHA256SUMS` | Checksums of all Lean sources |
| `verification/local-build.txt` | Recorded local build, audit and Comparator run |
| `scripts/` | Palomar template checks (source requirements, metadata, Comparator) |
| `paper/` | Paper source and PDF |
| `LICENSE` | Apache License 2.0 (covers this repository's own files only) |
