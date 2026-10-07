module

public import RequestProject.NeumannNormalizedBoundary

/-!
# The actual weak equation for the projected Neumann resolvent

The fixed complement is invariant under the genuine mass and Helmholtz
operators. Consequently the regular resolvent solves the actual form
equation with exactly the resonant component of the load removed. The
removed component has its genuine physical mass pairing, with the factor
`E₀ + 1` from the shifted-energy H¹ inner product.

These identities use the actual variational resonance space and do not
assume any boundary principal-part or smoothing formula.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped Real InnerProductSpace ComplexConjugate

/- These computations are checked before specialization to the concrete
H¹ space. The public conclusions below retain the actual operators. -/
private theorem projected_mass_from_kernel
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (M : H →L[ℂ] H) (c : ℂ) (hc : c ≠ 0) (u : H)
    (hu : ((1 : H →L[ℂ] H) - c • M) u = 0) : M u = c⁻¹ • u := by
  have heq : u = c • M u := sub_eq_zero.mp (by
    simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply] using hu)
  calc
    M u = c⁻¹ • (c • M u) := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • u := congrArg (fun v : H => c⁻¹ • v) heq.symm

private theorem projected_mass_preserves_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) (M : H →L[ℂ] H) (hM : IsSelfAdjoint M) (c : ℂ)
    (hS : ∀ v ∈ S, M v = c • v) {u : H} (hu : u ∈ Sᗮ) : M u ∈ Sᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  have hzero : ⟪v, u⟫_ℂ = 0 := (S.mem_orthogonal u).1 hu v hv
  calc
    ⟪v, M u⟫_ℂ = ⟪M v, u⟫_ℂ := (hM.isSymmetric v u).symm
    _ = ⟪c • v, u⟫_ℂ := congrArg (fun w : H => ⟪w, u⟫_ℂ) (hS v hv)
    _ = 0 := by simp only [inner_smul_left, hzero, mul_zero]

private theorem projected_compression_apply
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] (M : H →L[ℂ] H)
    (hS : ∀ v ∈ S, M v ∈ S) (u : S) :
    ((S.orthogonalProjection ∘L M ∘L S.subtypeL) u : H) = M u := by
  have hproj := Submodule.orthogonalProjection_mem_subspace_eq_self (K := S)
    (⟨M u, hS u u.property⟩ : S)
  simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using
    congrArg Subtype.val hproj

private theorem projected_form_coe
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (S : Submodule ℂ H) (M : H →L[ℂ] H) (C : S →L[ℂ] S)
    (hC : ∀ u : S, (C u : H) = M u) (c : ℂ) (u : S) :
    (((1 : S →L[ℂ] S) - c • C) u : H) =
      ((1 : H →L[ℂ] H) - c • M) u := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, Submodule.coe_sub, Submodule.coe_smul, hC]

private theorem projected_inverse_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (hA : IsUnit A) (x : H) : A (Ring.inverse A x) = x := by
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using
    congrArg (fun B : H →L[ℂ] H => B x) (Ring.mul_inverse_cancel A hA)

private theorem projected_regular_solve
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] (A : H →L[ℂ] H) (B : S →L[ℂ] S)
    (hAB : ∀ u : S, A (u : H) = (B u : H)) (hB : IsUnit B) (x : H) :
    A ((S.subtypeL ∘L Ring.inverse B ∘L S.orthogonalProjection) x) =
      S.starProjection x := by
  calc
    _ = (B (Ring.inverse B (S.orthogonalProjection x)) : H) := by
      simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using
        hAB (Ring.inverse B (S.orthogonalProjection x))
    _ = (S.orthogonalProjection x : H) :=
      congrArg (fun v : S => (v : H))
        (projected_inverse_apply B hB (S.orthogonalProjection x))
    _ = S.starProjection x := rfl

private theorem projected_shifted_mass_scalar
    (a b : ℂ) (E : ℝ) (h : a = (E : ℂ) * b) :
    b + a = ((E + 1 : ℝ) : ℂ) * b := by
  rw [h]
  push_cast
  ring

private theorem projected_form_pairing_of_solve
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] (A : H →L[ℂ] H)
    (W M : H → H → ℂ) (c : ℂ)
    (hA : ∀ v u, ⟪v, A u⟫_ℂ = W v u)
    (hM : ∀ w ∈ S, ∀ v, ⟪v, w⟫_ℂ = c * M v w)
    {u x : H} (hsolve : A u = Sᗮ.starProjection x) (v : H) :
    W v u = ⟪v, x⟫_ℂ - c * M v (S.starProjection x) := by
  calc
    W v u = ⟪v, A u⟫_ℂ := (hA v u).symm
    _ = ⟪v, Sᗮ.starProjection x⟫_ℂ := congrArg (fun w : H => ⟪v, w⟫_ℂ) hsolve
    _ = ⟪v, x⟫_ℂ - ⟪v, S.starProjection x⟫_ℂ := by
      rw [Submodule.starProjection_orthogonal_val, inner_sub_right]
    _ = _ := congrArg (fun z : ℂ => ⟪v, x⟫_ℂ - z)
      (hM _ (S.starProjection_apply_mem x) v)

private theorem projected_adjoint_pairing_sub
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (Q : H →L[ℂ] G) (v : H) (b : G) (z : ℂ) :
    ⟪v, ContinuousLinearMap.adjoint Q b⟫_ℂ - z = ⟪Q v, b⟫_ℂ - z :=
  congrArg (fun t : ℂ => t - z) (ContinuousLinearMap.adjoint_inner_right Q v b)

/-- The genuine mass operator acts by the shifted inverse eigenvalue on
the actual kernel of the Helmholtz form. -/
theorem h1ResonantMass_eq_inverse_smul {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {u : NeumannH1 Ω} (hu : u ∈ h1ResonantSpace Ω E₀) :
    h1MassOperator Ω u = (((E₀ + 1 : ℝ) : ℂ)⁻¹) • u := by
  have hc : ((E₀ + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show E₀ + 1 ≠ 0 by linarith)
  exact projected_mass_from_kernel (h1MassOperator Ω) ((E₀ + 1 : ℝ) : ℂ) hc u hu

/-- Self-adjointness and the actual resonant mass identity show that the
fixed orthogonal complement is invariant under the mass operator. -/
theorem h1MassOperator_preserves_resonantComplement {Ω : Set ℂ} {E₀ : ℝ}
    (hE₀ : 0 ≤ E₀) {u : NeumannH1 Ω} (hu : u ∈ (h1ResonantSpace Ω E₀)ᗮ) :
    h1MassOperator Ω u ∈ (h1ResonantSpace Ω E₀)ᗮ := by
  exact projected_mass_preserves_orthogonal (h1ResonantSpace Ω E₀)
    (h1MassOperator Ω) (h1MassOperator_isSelfAdjoint Ω)
    (((E₀ + 1 : ℝ) : ℂ)⁻¹)
    (fun _ hv => h1ResonantMass_eq_inverse_smul hE₀ hv) hu

/-- The compressed mass operator is the actual mass operator on its
invariant complement, including after embedding into the full H¹ space. -/
theorem h1ComplementMass_coe_eq {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (u : (h1ResonantSpace Ω E₀)ᗮ) :
    (h1ComplementMass Ω E₀ u : NeumannH1 Ω) = h1MassOperator Ω u := by
  exact projected_compression_apply (h1ResonantSpace Ω E₀)ᗮ (h1MassOperator Ω)
    (fun _ hv => h1MassOperator_preserves_resonantComplement hE₀ hv) u

/-- The genuine complement form embeds as the actual full Helmholtz
form, at every energy. -/
theorem h1ComplementForm_coe_eq {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (E : ℝ) (u : (h1ResonantSpace Ω E₀)ᗮ) :
    (h1ComplementForm Ω E₀ E u : NeumannH1 Ω) = h1HelmholtzForm Ω E u := by
  exact projected_form_coe (h1ResonantSpace Ω E₀)ᗮ (h1MassOperator Ω)
    (h1ComplementMass Ω E₀) (h1ComplementMass_coe_eq hE₀)
    ((E + 1 : ℝ) : ℂ) u

/-- Applying the genuine Helmholtz form to the genuine regular resolvent
gives exactly the orthogonal-complement projection of the original load. -/
theorem h1RegularResolvent_projected_solve {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {E : ℝ} (hunit : IsUnit (h1ComplementForm Ω E₀ E)) (u : NeumannH1 Ω) :
    h1HelmholtzForm Ω E (h1RegularResolvent Ω E₀ E u) =
      (h1ResonantSpace Ω E₀)ᗮ.starProjection u := by
  exact projected_regular_solve (h1ResonantSpace Ω E₀)ᗮ (h1HelmholtzForm Ω E)
    (h1ComplementForm Ω E₀ E) (fun v => (h1ComplementForm_coe_eq hE₀ E v).symm)
    hunit u

/-- Actual resonant vectors satisfy the zero-load weak Neumann equation
against every genuine H¹ test vector. -/
theorem h1Resonant_weak_pairing {Ω : Set ℂ} {E₀ : ℝ}
    {w : NeumannH1 Ω} (hw : w ∈ h1ResonantSpace Ω E₀) (v : NeumannH1 Ω) :
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i w⟫_ℂ) =
      (E₀ : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ := by
  have hzero : h1HelmholtzForm Ω E₀ w = 0 := hw
  have h := h1HelmholtzForm_inner Ω E₀ v w
  rw [hzero, inner_zero_right] at h
  exact sub_eq_zero.mp h.symm

/-- The shifted H¹ pairing of an actual resonant vector is its physical
mass pairing multiplied by `E₀ + 1`. -/
theorem h1Resonant_inner_eq_mass {Ω : Set ℂ} {E₀ : ℝ}
    {w : NeumannH1 Ω} (hw : w ∈ h1ResonantSpace Ω E₀) (v : NeumannH1 Ω) :
    ⟪v, w⟫_ℂ = ((E₀ + 1 : ℝ) : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ := by
  exact (h1_inner Ω v w).trans
    (projected_shifted_mass_scalar _ _ E₀ (h1Resonant_weak_pairing hw v))

/-- The all-test-vector weak equation for the genuine regular resolvent.
The removed resonant load contributes with a minus sign and the actual
shifted-energy factor `E₀ + 1`. -/
theorem h1RegularResolvent_weak_pairing {Ω : Set ℂ} {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {E : ℝ} (hunit : IsUnit (h1ComplementForm Ω E₀ E)) (x : NeumannH1 Ω) :
    ∀ v : NeumannH1 Ω,
      (∑ i, ⟪h1Gradient Ω i v,
        h1Gradient Ω i (h1RegularResolvent Ω E₀ E x)⟫_ℂ) -
          (E : ℂ) * ⟪h1Value Ω v,
            h1Value Ω (h1RegularResolvent Ω E₀ E x)⟫_ℂ =
        ⟪v, x⟫_ℂ - ((E₀ + 1 : ℝ) : ℂ) *
          ⟪h1Value Ω v, h1Value Ω ((h1ResonantSpace Ω E₀).starProjection x)⟫_ℂ := by
  intro v
  exact projected_form_pairing_of_solve (h1ResonantSpace Ω E₀)
    (h1HelmholtzForm Ω E)
    (fun v u => (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      (E : ℂ) * ⟪h1Value Ω v, h1Value Ω u⟫_ℂ)
    (fun v u => ⟪h1Value Ω v, h1Value Ω u⟫_ℂ) ((E₀ + 1 : ℝ) : ℂ)
    (h1HelmholtzForm_inner Ω E) (fun _ hw v => h1Resonant_inner_eq_mass hw v)
    (h1RegularResolvent_projected_solve hE₀ hunit x) v

/-- The actual regular solution with normalized boundary load `Q† b`
satisfies the projected weak Neumann equation against every H¹ vector. -/
theorem h1RegularResolvent_adjoint_weak_pairing {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {E : ℝ} (hunit : IsUnit (h1ComplementForm Ω E₀ E)) (b : L2Z) :
    ∀ v : NeumannH1 Ω,
      (∑ i, ⟪h1Gradient Ω i v,
        h1Gradient Ω i (h1RegularResolvent Ω E₀ E (ContinuousLinearMap.adjoint Q b))⟫_ℂ) -
          (E : ℂ) * ⟪h1Value Ω v,
            h1Value Ω (h1RegularResolvent Ω E₀ E (ContinuousLinearMap.adjoint Q b))⟫_ℂ =
        ⟪Q v, b⟫_ℂ - ((E₀ + 1 : ℝ) : ℂ) *
          ⟪h1Value Ω v, h1Value Ω ((h1ResonantSpace Ω E₀).starProjection
            (ContinuousLinearMap.adjoint Q b))⟫_ℂ := by
  intro v
  exact (h1RegularResolvent_weak_pairing hE₀ hunit
    (ContinuousLinearMap.adjoint Q b) v).trans (projected_adjoint_pairing_sub Q v b _)

end PolyaNeumann

end
