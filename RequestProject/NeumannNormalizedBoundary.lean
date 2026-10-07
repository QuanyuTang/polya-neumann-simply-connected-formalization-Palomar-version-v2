module

public import RequestProject.NeumannBoundaryDifference
public import RequestProject.NeumannResidueRank
public import RequestProject.SobolevCircle

/-!
# The actual Neumann form with bounded boundary coordinates

These constructions accept a bounded coordinate trace Q. The interior
operator and its spectral sequence remain the actual variational Neumann
ones. In conformal coordinates Q is the constructed conformal half trace;
it need not come from a constant-speed circle parameter. Compatibility
with physical boundary data is a separate identity for that actual Q.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Filter Topology
open scoped InnerProductSpace

/- The identities below are proved while the Hilbert spaces are abstract.
Specializing their opaque proofs avoids recomputing the concrete H¹ and
Fourier-space structures in operator coercions and adjoint identities. -/

section HilbertBarriers

variable {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

private theorem normalized_trace_weak_iff
    (Q : H →L[ℂ] G) (A : H →L[ℂ] H) (W : H → H → ℂ)
    (hA : ∀ v u, ⟪v, A u⟫_ℂ = W v u) (b : G) (u : H) :
    (∀ v, W v u = ⟪Q v, b⟫_ℂ) ↔ A u = ContinuousLinearMap.adjoint Q b := by
  constructor
  · intro hu
    exact ext_inner_left ℂ fun v =>
      (hA v u).trans ((hu v).trans
        (ContinuousLinearMap.adjoint_inner_right Q v b).symm)
  · intro hu v
    exact (hA v u).symm.trans
      ((congrArg (fun x : H => ⟪v, x⟫_ℂ) hu).trans
        (ContinuousLinearMap.adjoint_inner_right Q v b))

omit [CompleteSpace H] in
private theorem normalized_form_inverse_apply
    (A : H →L[ℂ] H) (hA : IsUnit A) (x : H) :
    A (Ring.inverse A x) = x := by
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using
    congrArg (fun B : H →L[ℂ] H => B x) (Ring.mul_inverse_cancel A hA)

private theorem normalized_trace_inverse_solution
    (Q : H →L[ℂ] G) (A : H →L[ℂ] H) (W : H → H → ℂ)
    (hA : ∀ v u, ⟪v, A u⟫_ℂ = W v u) (hunit : IsUnit A) (b : G) :
    ∀ v, W v (((Ring.inverse A).comp (ContinuousLinearMap.adjoint Q)) b) =
      ⟪Q v, b⟫_ℂ := by
  apply (normalized_trace_weak_iff Q A W hA b _).2
  simpa only [ContinuousLinearMap.comp_apply] using
    normalized_form_inverse_apply A hunit (ContinuousLinearMap.adjoint Q b)

private theorem normalized_form_solution_eq
    (A : H →L[ℂ] H) (hA : IsUnit A) {u v y : H}
    (hu : A u = y) (hv : A v = y) : u = v :=
  (ContinuousLinearMap.isUnit_iff_bijective.mp hA).1 (hu.trans hv.symm)

private theorem normalized_trace_sandwich_isSelfAdjoint
    (Q : H →L[ℂ] G) (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (Q.comp (A.comp (ContinuousLinearMap.adjoint Q))) :=
  hA.conj_adjoint Q

private theorem normalized_trace_sandwich_sub_isCompactOperator
    (Q : H →L[ℂ] G) (A B : H →L[ℂ] H)
    (hAB : IsCompactOperator (A - B)) :
    IsCompactOperator
      (Q.comp (A.comp (ContinuousLinearMap.adjoint Q)) -
        Q.comp (B.comp (ContinuousLinearMap.adjoint Q))) := by
  rw [← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp]
  exact (hAB.comp_clm (ContinuousLinearMap.adjoint Q)).clm_comp Q

private theorem normalized_trace_projected_range
    (S : Submodule ℂ H) [CompleteSpace S] [FiniteDimensional ℂ S]
    (Q : H →L[ℂ] G) (hinj : Function.Injective (Q.comp S.subtypeL))
    (c : ℂ) (hc : c ≠ 0) :
    (c • (Q ∘L S.starProjection ∘L ContinuousLinearMap.adjoint Q)).range =
      (Q.comp S.subtypeL).range :=
  range_scaled_projected_trace_gram (H := H) (G := G) (c := c) S Q hinj hc

omit [CompleteSpace H] [CompleteSpace G] in
private theorem normalized_trace_finrank_range
    (T : H →L[ℂ] G) (hinj : Function.Injective T) :
    Module.finrank ℂ T.range = Module.finrank ℂ H :=
  LinearMap.finrank_range_of_inj (f := T.toLinearMap) hinj

private theorem normalized_trace_projected_finrank
    (S : Submodule ℂ H) [CompleteSpace S] [FiniteDimensional ℂ S]
    (Q : H →L[ℂ] G) (hinj : Function.Injective (Q.comp S.subtypeL))
    (c : ℂ) (hc : c ≠ 0) :
    Module.finrank ℂ
        (c • (Q ∘L S.starProjection ∘L ContinuousLinearMap.adjoint Q)).range =
      Module.finrank ℂ S := by
  exact (congrArg (fun T : Submodule ℂ G => Module.finrank ℂ T)
    (normalized_trace_projected_range S Q hinj c hc)).trans
      (normalized_trace_finrank_range (Q.comp S.subtypeL) hinj)

private theorem continuousOn_normalized_trace_sandwich
    (Q : H →L[ℂ] G) (A : ℝ → H →L[ℂ] H) {U : Set ℝ}
    (hA : ContinuousOn A U) :
    ContinuousOn (fun E => Q.comp ((A E).comp (ContinuousLinearMap.adjoint Q))) U :=
  continuousOn_const.clm_comp (hA.clm_comp continuousOn_const)

private theorem normalized_trace_sandwich_pole
    (Q : H →L[ℂ] G) {A P R : H →L[ℂ] H} {a c d : ℂ}
    (ha : a = c * d) (hA : A = a • P + R) :
    Q.comp (A.comp (ContinuousLinearMap.adjoint Q)) =
      c • (d • (Q.comp (P.comp (ContinuousLinearMap.adjoint Q)))) +
        Q.comp (R.comp (ContinuousLinearMap.adjoint Q)) := by
  rw [hA, ha]
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]

end HilbertBarriers

section

variable {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z)

def normalizedNeumannPoisson (E : ℝ) : L2Z →L[ℂ] NeumannH1 Ω :=
  (h1HelmholtzResolvent Ω E).comp (ContinuousLinearMap.adjoint Q)

def normalizedNeumannBoundary (E : ℝ) : L2Z →L[ℂ] L2Z :=
  Q.comp (normalizedNeumannPoisson Q E)

def IsNormalizedNeumannSolution (E : ℝ) (b : L2Z) (u : NeumannH1 Ω) : Prop :=
  ∀ v : NeumannH1 Ω,
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      (E : ℂ) * ⟪h1Value Ω v, h1Value Ω u⟫_ℂ = ⟪Q v, b⟫_ℂ

theorem isNormalizedNeumannSolution_iff (E : ℝ) (b : L2Z) (u : NeumannH1 Ω) :
    IsNormalizedNeumannSolution Q E b u ↔
      h1HelmholtzForm Ω E u = ContinuousLinearMap.adjoint Q b := by
  exact normalized_trace_weak_iff (H := NeumannH1 Ω) (G := L2Z) Q
    (h1HelmholtzForm Ω E)
    (fun v w => (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i w⟫_ℂ) -
      (E : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ)
    (h1HelmholtzForm_inner Ω E) b u

theorem normalizedNeumannPoisson_isSolution {E : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) (b : L2Z) :
    IsNormalizedNeumannSolution Q E b (normalizedNeumannPoisson Q E b) := by
  exact normalized_trace_inverse_solution (H := NeumannH1 Ω) (G := L2Z) Q
    (h1HelmholtzForm Ω E)
    (fun v w => (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i w⟫_ℂ) -
      (E : ℂ) * ⟪h1Value Ω v, h1Value Ω w⟫_ℂ)
    (h1HelmholtzForm_inner Ω E) hE b

theorem existsUnique_normalizedNeumannSolution {E : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) (b : L2Z) :
    ∃! u : NeumannH1 Ω, IsNormalizedNeumannSolution Q E b u := by
  have hs := normalizedNeumannPoisson_isSolution Q hE b
  refine ⟨normalizedNeumannPoisson Q E b, hs, ?_⟩
  intro u hu
  exact normalized_form_solution_eq (H := NeumannH1 Ω) (h1HelmholtzForm Ω E) hE
    ((isNormalizedNeumannSolution_iff Q E b u).1 hu)
    ((isNormalizedNeumannSolution_iff Q E b _).1 hs)

theorem normalizedNeumannBoundary_isSelfAdjoint (E : ℝ) :
    IsSelfAdjoint (normalizedNeumannBoundary Q E) := by
  simpa only [normalizedNeumannBoundary, normalizedNeumannPoisson] using
    normalized_trace_sandwich_isSelfAdjoint (H := NeumannH1 Ω) (G := L2Z) Q
      (h1HelmholtzResolvent Ω E) (h1HelmholtzResolvent_isSelfAdjoint Ω E)

theorem normalizedNeumannBoundary_sub_isCompactOperator
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E F : ℝ}
    (hE : IsUnit (h1HelmholtzForm Ω E)) (hF : IsUnit (h1HelmholtzForm Ω F)) :
    IsCompactOperator (normalizedNeumannBoundary Q E - normalizedNeumannBoundary Q F) := by
  simpa only [normalizedNeumannBoundary, normalizedNeumannPoisson] using
    normalized_trace_sandwich_sub_isCompactOperator (H := NeumannH1 Ω) (G := L2Z)
      Q (h1HelmholtzResolvent Ω E) (h1HelmholtzResolvent Ω F)
      (h1HelmholtzResolvent_sub_isCompactOperator hb hL hE hF)

def normalizedNeumannResidue (E₀ : ℝ) : L2Z →L[ℂ] L2Z :=
  ((E₀ + 1 : ℝ) : ℂ) •
    (Q ∘L (h1ResonantSpace Ω E₀).starProjection ∘L ContinuousLinearMap.adjoint Q)

def normalizedNeumannRegular (E₀ E : ℝ) : L2Z →L[ℂ] L2Z :=
  Q ∘L h1RegularResolvent Ω E₀ E ∘L ContinuousLinearMap.adjoint Q

theorem normalizedNeumannResidue_range_eq
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (hinj : Function.Injective (Q.comp (h1ResonantSpace Ω E).subtypeL)) :
    (normalizedNeumannResidue Q E).range = (Q.comp (h1ResonantSpace Ω E).subtypeL).range := by
  letI : FiniteDimensional ℂ (h1ResonantSpace Ω E) :=
    finiteDimensional_h1ResonantSpace hb hL E
  have hc : ((E + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show E + 1 ≠ 0 by linarith)
  simpa only [normalizedNeumannResidue] using
    normalized_trace_projected_range (H := NeumannH1 Ω) (G := L2Z)
      (h1ResonantSpace Ω E) Q hinj ((E + 1 : ℝ) : ℂ) hc

theorem normalizedNeumannResidue_finrank_eq
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (hinj : Function.Injective (Q.comp (h1ResonantSpace Ω E).subtypeL)) :
    Module.finrank ℂ (normalizedNeumannResidue Q E).range =
      Module.finrank ℂ (h1ResonantSpace Ω E) := by
  letI : FiniteDimensional ℂ (h1ResonantSpace Ω E) :=
    finiteDimensional_h1ResonantSpace hb hL E
  have hc : ((E + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (show E + 1 ≠ 0 by linarith)
  exact normalized_trace_projected_finrank (H := NeumannH1 Ω) (G := L2Z)
    (h1ResonantSpace Ω E) Q hinj ((E + 1 : ℝ) : ℂ) hc

theorem normalizedNeumannResidue_multiplicity_eq
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (hinj : Function.Injective (Q.comp (h1ResonantSpace Ω E).subtypeL)) :
    (Module.finrank ℂ (normalizedNeumannResidue Q E).range : ℕ∞) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  exact (congrArg (fun n : ℕ => (n : ℕ∞))
    (normalizedNeumannResidue_finrank_eq Q hb hL hE hinj)).trans
      (h1ResonantSpace_multiplicity_eq hb hL hE)

theorem continuousOn_normalizedNeumannRegular {E₀ : ℝ} {U : Set ℝ}
    (hi : ContinuousOn (fun E => Ring.inverse (h1ComplementForm Ω E₀ E)) U) :
    ContinuousOn (normalizedNeumannRegular Q E₀) U := by
  exact continuousOn_normalized_trace_sandwich (H := NeumannH1 Ω) (G := L2Z)
      Q (h1RegularResolvent Ω E₀) (continuousOn_h1RegularResolvent hi)

theorem normalizedNeumannBoundary_eq_pole_add_regular
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E₀ E : ℝ}
    (hE₀ : 0 ≤ E₀) (hne : E ≠ E₀) (hunit : IsUnit (h1ComplementForm Ω E₀ E)) :
    normalizedNeumannBoundary Q E =
      (-((E - E₀ : ℝ) : ℂ)⁻¹) • normalizedNeumannResidue Q E₀ +
        normalizedNeumannRegular Q E₀ E := by
  have hs : -(((E₀ + 1 : ℝ) : ℂ) / ((E - E₀ : ℝ) : ℂ)) =
      (-((E - E₀ : ℝ) : ℂ)⁻¹) * ((E₀ + 1 : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    ring
  exact normalized_trace_sandwich_pole (H := NeumannH1 Ω) (G := L2Z) Q hs
    (h1HelmholtzResolvent_eq_pole_add_regular hb hL hE₀ hne hunit)

theorem exists_normalizedNeumannRegular_near
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    ∃ U ∈ 𝓝 E₀, ContinuousOn (normalizedNeumannRegular Q E₀) U ∧
      ∀ E ∈ U, E ≠ E₀ → normalizedNeumannBoundary Q E =
        (-((E - E₀ : ℝ) : ℂ)⁻¹) • normalizedNeumannResidue Q E₀ +
          normalizedNeumannRegular Q E₀ E := by
  obtain ⟨U, hU, hunit, hi⟩ := h1ComplementForm_isUnit_near hb hL hE₀
  exact ⟨U, hU, continuousOn_normalizedNeumannRegular Q hi,
    fun E hEU hne => normalizedNeumannBoundary_eq_pole_add_regular Q hb hL hE₀ hne
      (hunit E hEU)⟩

end

end PolyaNeumann

end
