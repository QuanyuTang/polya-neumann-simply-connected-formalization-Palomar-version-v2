module

import RequestProject.Main
import Solution

/-!
This file is the machine-checked release audit for the Neumann formalization.
The guards below fail if any audited theorem acquires an unexpected axiom,
including `sorryAx`.  The source remains modular; `RequestProject.Main` is the
canonical entry point for the complete dependency closure.

The second part audits the Palomar interface: the two wrapper theorems proved in
`Solution.lean` (whose statements are identical to those of `Challenge.lean`), and
the fact that every statement-side definition of the Palomar namespace is
definitionally equal to the corresponding definition of `RequestProject/Defs.lean`.
-/

#check main
#check main_counting
#check PolyaNeumann.strict_neumann_polya
#check PolyaNeumann.strict_neumann_polya_count
#check PolyaNeumann.neumannEigenvalue_eq_spectral
#check PolyaNeumann.neumannEigenvalue_has_operator_eigenvector
#check PolyaNeumann.neumann_reconstruction
#check PolyaNeumann.lipschitz_quantitative
#check PolyaNeumann.smooth_eigen
#check PolyaNeumann.exists_smoothApproximation
#check PolyaNeumann.uniform_cayley_rank_bound
#check PolyaNeumann.neumannEigenvalue_pos
#check PolyaNeumann.neumannEigenvalue_zero

/-- info: 'main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms main

/-- info: 'main_counting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms main_counting

/-- info: 'PolyaNeumann.strict_neumann_polya' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyaNeumann.strict_neumann_polya

/-- info: 'PolyaNeumann.strict_neumann_polya_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyaNeumann.strict_neumann_polya_count

/-- info: 'PolyaNeumann.neumannEigenvalue_eq_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyaNeumann.neumannEigenvalue_eq_spectral

/-- info: 'PolyaNeumann.neumannEigenvalue_has_operator_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyaNeumann.neumannEigenvalue_has_operator_eigenvector

/-- info: 'PolyaNeumann.neumann_reconstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyaNeumann.neumann_reconstruction

/-- info: 'PolyaNeumann.lipschitz_quantitative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyaNeumann.lipschitz_quantitative

/-- info: 'PolyaNeumann.smooth_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyaNeumann.smooth_eigen

/-- info: 'PolyaNeumann.exists_smoothApproximation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyaNeumann.exists_smoothApproximation

/-- info: 'PolyaNeumann.uniform_cayley_rank_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyaNeumann.uniform_cayley_rank_bound

/-- info: 'PolyaNeumann.neumannEigenvalue_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyaNeumann.neumannEigenvalue_pos

/-- info: 'PolyaNeumann.neumannEigenvalue_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolyaNeumann.neumannEigenvalue_zero

/-! ## Palomar interface (`Challenge.lean` / `Solution.lean`) -/

#check PalomarPolyaNeumann.strict_neumann_polya
#check PalomarPolyaNeumann.strict_neumann_polya_count

/-- info: 'PalomarPolyaNeumann.strict_neumann_polya' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalomarPolyaNeumann.strict_neumann_polya

/-- info: 'PalomarPolyaNeumann.strict_neumann_polya_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PalomarPolyaNeumann.strict_neumann_polya_count

/-! The Palomar statement-side definitions coincide definitionally with the definitions
used by the proof development. -/

example : PalomarPolyaNeumann.IsDomain = PolyaNeumann.IsDomain := rfl
example : PalomarPolyaNeumann.IsLipschitzDomain = PolyaNeumann.IsLipschitzDomain := rfl
example : PalomarPolyaNeumann.L2 = PolyaNeumann.L2 := rfl
example : PalomarPolyaNeumann.coordDir = PolyaNeumann.coordDir := rfl
example : PalomarPolyaNeumann.TestFunction = PolyaNeumann.TestFunction := rfl
example : PalomarPolyaNeumann.IsWeakGradient = PolyaNeumann.IsWeakGradient := rfl
example : PalomarPolyaNeumann.H1 = PolyaNeumann.H1 := rfl
example : PalomarPolyaNeumann.neumannEnergy = PolyaNeumann.neumannEnergy := rfl
example : PalomarPolyaNeumann.rayleigh = PolyaNeumann.rayleigh := rfl
example : PalomarPolyaNeumann.neumannEigenvalue = PolyaNeumann.neumannEigenvalue := rfl
example : PalomarPolyaNeumann.neumannCount = PolyaNeumann.neumannCount := rfl
