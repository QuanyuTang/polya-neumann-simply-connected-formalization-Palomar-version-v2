module

import RequestProject.Main

/-!
# Axiom check for the main theorems

Prints the axioms used by the principal theorems of the proof development.
The expected output for each declaration is `[propext, Classical.choice, Quot.sound]`.
The guarded version of this check (which fails on any deviation) is `verification/Audit.lean`.
-/

#print axioms PolyaNeumann.strict_neumann_polya
#print axioms PolyaNeumann.strict_neumann_polya_count
#print axioms main
#print axioms main_counting
#print axioms PolyaNeumann.uniform_cayley_rank_bound
