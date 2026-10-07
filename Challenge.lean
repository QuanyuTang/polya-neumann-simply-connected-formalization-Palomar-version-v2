module

public import Mathlib

/-!
# The strict Neumann Pólya inequality on bounded simply connected planar Lipschitz domains

This file is the statement surface of the formalization.  It imports only Mathlib and
contains every definition needed to read the two advertised theorems.  The proofs are
supplied in `Solution.lean`, which imports the full proof development in
`RequestProject/`; Comparator checks that the declarations of the two files agree.

## Conventions

* The plane `ℝ²` is identified with `ℂ`; `volume` is two-dimensional Lebesgue measure, so
  `volume Ω` is the area `|Ω|` (an extended nonnegative real).
* `L²(Ω)` is the complex Hilbert space `Lp ℂ 2 (volume.restrict Ω)`.
* `H¹(Ω)` is the set of `u ∈ L²(Ω)` having a weak gradient in `L²(Ω)²`, the weak gradient
  being tested against smooth compactly supported functions in `Ω`.
* The Neumann eigenvalues are defined variationally by the Courant–Fischer min–max formula
  for the Neumann form `q[u] = ∫_Ω |∇u|²` on `H¹(Ω)`.  They are indexed from `0` and repeated
  according to multiplicity: `0 = μ₀(Ω) ≤ μ₁(Ω) ≤ μ₂(Ω) ≤ ⋯` (for a bounded Lipschitz domain,
  `μ₀ = 0 < μ₁`).  No boundary condition is imposed on the test spaces: this is the natural
  (Neumann) boundary condition.
* `N_N(E) = #{j ≥ 0 : μ_j(Ω) < E}` is the strict counting function, including `μ₀ = 0`.

## Main statements

* `PalomarPolyaNeumann.strict_neumann_polya`: for every bounded simply connected Lipschitz
  domain `Ω ⊂ ℝ²` and every integer `j ≥ 1`, `|Ω| μ_j(Ω) < 4πj`.
* `PalomarPolyaNeumann.strict_neumann_polya_count`: for every such `Ω` and every real
  `E > 0`, `N_N(E) > |Ω| E / (4π)`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace PalomarPolyaNeumann

/-- A domain: a nonempty connected open subset of `ℝ² = ℂ`
(`IsConnected` includes nonemptiness). -/
def IsDomain (Ω : Set ℂ) : Prop := IsOpen Ω ∧ IsConnected Ω

/-- A Lipschitz domain: a domain whose boundary is locally, after a rigid change of
coordinates `w ↦ c * (w - p)` (`‖c‖ = 1`, i.e. a translation followed by a rotation), the
graph of a Lipschitz function `f`, with the domain lying on one side (above the graph).
Precisely, for every boundary point `p` there are a rotation `c`, a box half-width `r > 0`, a
box half-height `h > 0` and a Lipschitz function `f : ℝ → ℝ` with `f 0 = 0` and `|f| < h` on
`(-r, r)`, such that a point `w` whose rotated coordinates `c * (w - p)` lie in the box
`(-r, r) × (-h, h)` belongs to `Ω` exactly when it lies strictly above the graph of `f`. -/
def IsLipschitzDomain (Ω : Set ℂ) : Prop :=
  IsDomain Ω ∧
  ∀ p ∈ frontier Ω, ∃ (c : ℂ) (r h : ℝ) (K : NNReal) (f : ℝ → ℝ),
    ‖c‖ = 1 ∧ 0 < r ∧ 0 < h ∧ LipschitzWith K f ∧ f 0 = 0 ∧
    (∀ x : ℝ, |x| < r → |f x| < h) ∧
    ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im)

/-- `L²(Ω)`: complex-valued square-integrable functions on `Ω` (modulo null functions), with
respect to two-dimensional Lebesgue measure restricted to `Ω`. -/
abbrev L2 (Ω : Set ℂ) := Lp ℂ 2 (volume.restrict Ω)

/-- The coordinate directions `e_x = 1` and `e_y = i` of `ℝ² = ℂ`. -/
def coordDir : Fin 2 → ℂ := ![1, Complex.I]

/-- `φ` is a test function on `Ω`, i.e. `φ ∈ C_c^∞(Ω)`: `φ : ℂ → ℂ` is infinitely
differentiable (as a function of two real variables), has compact support, and its support
is contained in `Ω`. -/
def TestFunction (Ω : Set ℂ) (φ : ℂ → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- `g = (g_x, g_y) ∈ L²(Ω)²` is a weak gradient of `u ∈ L²(Ω)`: for every test function `φ`
and each coordinate direction `i`, `∫_Ω u ∂_i φ = - ∫_Ω g_i φ`. -/
def IsWeakGradient (Ω : Set ℂ) (u : L2 Ω) (g : Fin 2 → L2 Ω) : Prop :=
  ∀ φ : ℂ → ℂ, TestFunction Ω φ → ∀ i : Fin 2,
    ∫ w in Ω, u w * fderiv ℝ φ w (coordDir i) = - ∫ w in Ω, g i w * φ w

/-- The Sobolev space `H¹(Ω)`, as the subset of `L²(Ω)` of functions having a weak gradient
in `L²(Ω)²`. -/
def H1 (Ω : Set ℂ) : Set (L2 Ω) := {u | ∃ g, IsWeakGradient Ω u g}

/-- The Neumann form `q_Ω[u] = ∫_Ω |∇u|² = ‖g_x‖² + ‖g_y‖²` for `u ∈ H¹(Ω)` with weak gradient
`g`, taking the value `⊤` when `u ∉ H¹(Ω)` (the infimum over an empty set). -/
def neumannEnergy (Ω : Set ℂ) (u : L2 Ω) : ENNReal :=
  ⨅ (g : Fin 2 → L2 Ω) (_ : IsWeakGradient Ω u g), ∑ i, (‖g i‖₊ : ENNReal) ^ 2

/-- The Rayleigh quotient `q_Ω[u] / ‖u‖²_{L²(Ω)}`. -/
def rayleigh (Ω : Set ℂ) (u : L2 Ω) : ENNReal :=
  neumannEnergy Ω u / (‖u‖₊ : ENNReal) ^ 2

/-- The Neumann eigenvalues `μ_j(Ω)`, `j = 0, 1, 2, …`, counted with multiplicity, given by
the Courant–Fischer min–max formula
`μ_j(Ω) = inf_{S ⊆ L²(Ω), dim S = j + 1} sup_{0 ≠ u ∈ S} q_Ω[u] / ‖u‖²`.
Subspaces not contained in `H¹(Ω)` have supremum `⊤` and so do not contribute; thus this is
the usual min–max over `(j+1)`-dimensional subspaces of `H¹(Ω)`, and `μ₀(Ω) = 0` for a
bounded domain. -/
def neumannEigenvalue (Ω : Set ℂ) (j : ℕ) : ENNReal :=
  ⨅ (S : Submodule ℂ (L2 Ω)) (_ : Module.finrank ℂ S = j + 1),
    ⨆ (u : L2 Ω) (_ : u ∈ S) (_ : u ≠ 0), rayleigh Ω u

/-- The strict Neumann counting function `N_N(E) = #{j ∈ ℕ : μ_j(Ω) < E}` (including the
index `j = 0`), as an extended natural number. -/
def neumannCount (Ω : Set ℂ) (E : ENNReal) : ℕ∞ :=
  {j : ℕ | neumannEigenvalue Ω j < E}.encard

open scoped Real

/-- **Strict Neumann Pólya inequality.** For every bounded simply connected Lipschitz domain
`Ω ⊂ ℝ² = ℂ` and every integer `j ≥ 1`, `|Ω| μ_j(Ω) < 4πj`. -/
theorem strict_neumann_polya (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (j : ℕ) (hj : 1 ≤ j) :
    volume Ω * neumannEigenvalue Ω j < ENNReal.ofReal (4 * π * j) := by
  sorry

/-- **Strict Neumann Pólya inequality, counting form.** For every bounded simply connected
Lipschitz domain `Ω ⊂ ℝ² = ℂ` and every real `E > 0`, `N_N(E) > |Ω| E / (4π)`. -/
theorem strict_neumann_polya_count (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (E : ℝ) (hE : 0 < E) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) <
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  sorry

end PalomarPolyaNeumann

end
