module

public import RequestProject.NeumannBoundaryPole
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-!
# Energy comparison for the genuine Neumann boundary maps

The inverse difference identity is applied to the actual weak Helmholtz
form `B_E = I - (E + 1) J†J`. Compactness of `J†J` then proves compactness
of the differences of the actual H¹ solution maps and L² NtD maps.
At energy `-1` the form is the identity, so this reference energy requires
no nonnegative-energy or nonresonance assumption.

These are identities for the genuine ordinary-`dθ` boundary maps. They do
not assert a fractional trace estimate or a conformal principal symbol.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

private theorem inverse_sub_of_units {R : Type*} [Ring R]
    (A B : R) (hA : IsUnit A) (hB : IsUnit B) :
    Ring.inverse A - Ring.inverse B =
      Ring.inverse A * (B - A) * Ring.inverse B := by
  symm
  calc
    Ring.inverse A * (B - A) * Ring.inverse B =
        (Ring.inverse A * B) * Ring.inverse B -
          (Ring.inverse A * A) * Ring.inverse B := by
      rw [mul_sub, sub_mul]
    _ = Ring.inverse A - Ring.inverse B := by
      rw [mul_assoc (Ring.inverse A) B (Ring.inverse B),
        Ring.mul_inverse_cancel B hB, Ring.inverse_mul_cancel A hA,
        mul_one, one_mul]

/-- The difference of the actual form operators, in the order needed for
the inverse difference identity. -/
private theorem shifted_form_sub
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (M : X →L[ℂ] X) (E F : ℝ) :
    (1 - ((F + 1 : ℝ) : ℂ) • M) - (1 - ((E + 1 : ℝ) : ℂ) • M) =
      ((E - F : ℝ) : ℂ) • M := by
  have hc : ((E + 1 : ℝ) : ℂ) - ((F + 1 : ℝ) : ℂ) =
      ((E - F : ℝ) : ℂ) := by
    push_cast
    ring
  calc
    _ = ((E + 1 : ℝ) : ℂ) • M - ((F + 1 : ℝ) : ℂ) • M := by abel
    _ = (((E + 1 : ℝ) : ℂ) - ((F + 1 : ℝ) : ℂ)) •
        M := (sub_smul _ _ _).symm
    _ = _ := by rw [hc]

theorem h1HelmholtzForm_sub (Ω : Set ℂ) (E F : ℝ) :
    h1HelmholtzForm Ω F - h1HelmholtzForm Ω E =
      ((E - F : ℝ) : ℂ) • h1MassOperator Ω :=
  shifted_form_sub (h1MassOperator Ω) E F

/-- The exact two-energy identity for the genuine weak Helmholtz inverse.
The order is `B_E⁻¹ J†J B_F⁻¹`; no commutativity is used. -/
theorem h1HelmholtzResolvent_sub (Ω : Set ℂ) {E F : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E))
    (hF : IsUnit (h1HelmholtzForm Ω F)) :
    h1HelmholtzResolvent Ω E - h1HelmholtzResolvent Ω F =
      ((E - F : ℝ) : ℂ) •
        ((h1HelmholtzResolvent Ω E).comp
          ((h1MassOperator Ω).comp (h1HelmholtzResolvent Ω F))) := by
  have h := inverse_sub_of_units (h1HelmholtzForm Ω E)
    (h1HelmholtzForm Ω F) hE hF
  rw [h1HelmholtzForm_sub Ω E F] at h
  simpa only [h1HelmholtzResolvent, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_assoc] using h

/-- Rellich compactness makes the difference of the actual H¹ inverses
compact whenever both form operators are invertible. -/
theorem h1HelmholtzResolvent_sub_isCompactOperator {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E F : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E))
    (hF : IsUnit (h1HelmholtzForm Ω F)) :
    IsCompactOperator (h1HelmholtzResolvent Ω E - h1HelmholtzResolvent Ω F) := by
  rw [h1HelmholtzResolvent_sub Ω hE hF]
  exact (((h1MassOperator_isCompactOperator hb hL).comp_clm
    (h1HelmholtzResolvent Ω F)).clm_comp (h1HelmholtzResolvent Ω E)).smul
      (((E - F : ℝ) : ℂ))

/-- Invertibility alone proves the actual boundary Poisson solution
equation, including at negative reference energies. -/
theorem neumannBoundaryPoisson_isSolution_of_isUnit {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) (g : BoundaryL2) :
    IsBoundaryNeumannSolution hb hL hγ E g
      (neumannBoundaryPoisson hb hL hγ E g) := by
  apply (isBoundaryNeumannSolution_iff_form_eq hb hL hγ E g _).2
  change h1HelmholtzForm Ω E
    (Ring.inverse (h1HelmholtzForm Ω E) (h1BoundaryLoad hb hL hγ g)) =
      h1BoundaryLoad hb hL hγ g
  rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hE,
    ContinuousLinearMap.one_apply]

/-- The actual boundary solution maps obey the same inverse difference
identity, with the conormal load on the right. -/
theorem neumannBoundaryPoisson_sub {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E F : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E))
    (hF : IsUnit (h1HelmholtzForm Ω F)) :
    neumannBoundaryPoisson hb hL hγ E - neumannBoundaryPoisson hb hL hγ F =
      ((E - F : ℝ) : ℂ) •
        ((h1HelmholtzResolvent Ω E).comp
          ((h1MassOperator Ω).comp (neumannBoundaryPoisson hb hL hγ F))) := by
  have h := congrArg
    (fun R : NeumannH1 Ω →L[ℂ] NeumannH1 Ω => R.comp (h1BoundaryLoad hb hL hγ))
    (h1HelmholtzResolvent_sub Ω hE hF)
  simpa only [neumannBoundaryPoisson, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc] using h

/-- Compare the genuine Poisson solution to an arbitrary invertible
reference energy. -/
theorem neumannBoundaryPoisson_reference {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E F : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E))
    (hF : IsUnit (h1HelmholtzForm Ω F)) :
    neumannBoundaryPoisson hb hL hγ E = neumannBoundaryPoisson hb hL hγ F +
      ((E - F : ℝ) : ℂ) •
        ((h1HelmholtzResolvent Ω E).comp
          ((h1MassOperator Ω).comp (neumannBoundaryPoisson hb hL hγ F))) := by
  exact (sub_eq_iff_eq_add.mp (neumannBoundaryPoisson_sub hb hL hγ hE hF)).trans
    (add_comm _ _)

theorem neumannBoundaryPoisson_reference_apply {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E F : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E))
    (hF : IsUnit (h1HelmholtzForm Ω F)) (g : BoundaryL2) :
    neumannBoundaryPoisson hb hL hγ E g = neumannBoundaryPoisson hb hL hγ F g +
      ((E - F : ℝ) : ℂ) • h1HelmholtzResolvent Ω E
        (h1MassOperator Ω (neumannBoundaryPoisson hb hL hγ F g)) := by
  exact congrArg (fun P : BoundaryL2 →L[ℂ] NeumannH1 Ω => P g)
    (neumannBoundaryPoisson_reference hb hL hγ hE hF)

theorem neumannBoundaryPoisson_sub_isCompactOperator {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E F : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E))
    (hF : IsUnit (h1HelmholtzForm Ω F)) :
    IsCompactOperator
      (neumannBoundaryPoisson hb hL hγ E - neumannBoundaryPoisson hb hL hγ F) := by
  change IsCompactOperator ((h1HelmholtzResolvent Ω E).comp (h1BoundaryLoad hb hL hγ) -
    (h1HelmholtzResolvent Ω F).comp (h1BoundaryLoad hb hL hγ))
  rw [← ContinuousLinearMap.sub_comp]
  exact (h1HelmholtzResolvent_sub_isCompactOperator hb hL hE hF).comp_clm
    (h1BoundaryLoad hb hL hγ)

/-- The two-energy identity for the actual L² NtD map is obtained by
taking the actual trace of the solution identity. -/
theorem neumannToDirichletL2_sub {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E F : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E))
    (hF : IsUnit (h1HelmholtzForm Ω F)) :
    neumannToDirichletL2 hb hL hγ E - neumannToDirichletL2 hb hL hγ F =
      ((E - F : ℝ) : ℂ) •
        ((h1BoundaryTrace hb hL hγ).comp
          ((h1HelmholtzResolvent Ω E).comp
            ((h1MassOperator Ω).comp (neumannBoundaryPoisson hb hL hγ F)))) := by
  have h := congrArg
    (fun P : BoundaryL2 →L[ℂ] NeumannH1 Ω => (h1BoundaryTrace hb hL hγ).comp P)
    (neumannBoundaryPoisson_sub hb hL hγ hE hF)
  simpa only [neumannToDirichletL2, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.comp_smul] using h

/-- Compactness comes from the actual interior mass operator, without
any compact-trace hypothesis. -/
theorem neumannToDirichletL2_sub_isCompactOperator {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E F : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E))
    (hF : IsUnit (h1HelmholtzForm Ω F)) :
    IsCompactOperator
      (neumannToDirichletL2 hb hL hγ E - neumannToDirichletL2 hb hL hγ F) := by
  change IsCompactOperator
    ((h1BoundaryTrace hb hL hγ).comp (neumannBoundaryPoisson hb hL hγ E) -
      (h1BoundaryTrace hb hL hγ).comp (neumannBoundaryPoisson hb hL hγ F))
  rw [← ContinuousLinearMap.comp_sub]
  exact (neumannBoundaryPoisson_sub_isCompactOperator hb hL hγ hE hF).clm_comp
    (h1BoundaryTrace hb hL hγ)

/-- At the coercive reference energy `-1`, the genuine weak form is exactly
the shifted H¹ inner product. -/
private theorem shifted_form_neg_one
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (M : X →L[ℂ] X) :
    1 - (((-1 : ℝ) + 1 : ℝ) : ℂ) • M = 1 := by
  simp

@[simp] theorem h1HelmholtzForm_neg_one (Ω : Set ℂ) :
    h1HelmholtzForm Ω (-1) = 1 :=
  shifted_form_neg_one (h1MassOperator Ω)

theorem h1HelmholtzForm_neg_one_isUnit (Ω : Set ℂ) :
    IsUnit (h1HelmholtzForm Ω (-1)) := by
  rw [h1HelmholtzForm_neg_one]
  exact isUnit_one

@[simp] theorem h1HelmholtzResolvent_neg_one (Ω : Set ℂ) :
    h1HelmholtzResolvent Ω (-1) = 1 := by
  rw [h1HelmholtzResolvent, h1HelmholtzForm_neg_one, Ring.inverse_one]

@[simp] theorem neumannBoundaryPoisson_neg_one {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    neumannBoundaryPoisson hb hL hγ (-1) = h1BoundaryLoad hb hL hγ := by
  apply ContinuousLinearMap.ext
  intro g
  simp only [neumannBoundaryPoisson, h1HelmholtzResolvent_neg_one,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]

/-- The reference load itself is the unique actual weak solution at `-1`. -/
theorem existsUnique_boundaryNeumannSolution_neg_one {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (g : BoundaryL2) :
    ∃! u : NeumannH1 Ω, IsBoundaryNeumannSolution hb hL hγ (-1) g u := by
  have hsol : IsBoundaryNeumannSolution hb hL hγ (-1) g
      (h1BoundaryLoad hb hL hγ g) := by
    apply (isBoundaryNeumannSolution_iff_form_eq hb hL hγ (-1) g _).2
    rw [h1HelmholtzForm_neg_one, ContinuousLinearMap.one_apply]
  refine ⟨h1BoundaryLoad hb hL hγ g, hsol, ?_⟩
  intro u hu
  have h := (isBoundaryNeumannSolution_iff_form_eq hb hL hγ (-1) g u).1 hu
  simpa only [h1HelmholtzForm_neg_one, ContinuousLinearMap.one_apply] using h

@[simp] theorem neumannToDirichletL2_neg_one {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    neumannToDirichletL2 hb hL hγ (-1) =
      (h1BoundaryTrace hb hL hγ).comp (h1BoundaryLoad hb hL hγ) := by
  rw [neumannToDirichletL2, neumannBoundaryPoisson_neg_one]

theorem neumannToDirichletL2_neg_one_isPositive {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ContinuousLinearMap.IsPositive (neumannToDirichletL2 hb hL hγ (-1)) := by
  rw [neumannToDirichletL2_neg_one]
  exact ContinuousLinearMap.isPositive_self_comp_adjoint (h1BoundaryTrace hb hL hγ)

/-- The reference comparison requires only invertibility at the target
energy; invertibility at `-1` is a theorem. -/
theorem neumannBoundaryPoisson_reference_neg_one {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) :
    neumannBoundaryPoisson hb hL hγ E = h1BoundaryLoad hb hL hγ +
      ((E + 1 : ℝ) : ℂ) •
        ((h1HelmholtzResolvent Ω E).comp
          ((h1MassOperator Ω).comp (h1BoundaryLoad hb hL hγ))) := by
  simpa only [neumannBoundaryPoisson_neg_one, sub_neg_eq_add] using
    neumannBoundaryPoisson_reference hb hL hγ hE (h1HelmholtzForm_neg_one_isUnit Ω)

/-- The genuine L² NtD map differs compactly from its coercive reference
trace Gram operator. -/
theorem neumannToDirichletL2_sub_reference_isCompactOperator {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) :
    IsCompactOperator (neumannToDirichletL2 hb hL hγ E -
      (h1BoundaryTrace hb hL hγ).comp (h1BoundaryLoad hb hL hγ)) := by
  simpa only [neumannToDirichletL2_neg_one] using
    neumannToDirichletL2_sub_isCompactOperator hb hL hγ hE
      (h1HelmholtzForm_neg_one_isUnit Ω)

end PolyaNeumann

end
