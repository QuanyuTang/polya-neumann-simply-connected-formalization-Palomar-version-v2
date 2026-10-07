module

public import RequestProject.NeumannResidueBasis
public import RequestProject.NeumannHerglotzBoundary
public import Mathlib.Tactic.Ring

/-!
# The physical Neumann regular part at resonance

At the reference energy, the actual complement inverse removes exactly
the kernel component of any genuine weak Helmholtz solution. Taking the
actual boundary trace identifies the pole-subtracted NtD map on compatible
data. In an L²-normalized Neumann basis the correction is the sum of the
eigenfunction boundary traces times their actual interior L² coefficients.

The identities apply to actual Herglotz waves, including at resonance.
All boundary pairings use ordinary coordinate measure `dθ`. No transport
cut term or fractional boundary extension is asserted here.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace ComplexConjugate

private theorem compressed_form_projected
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] (A : H →L[ℂ] H)
    (hker : ∀ v ∈ S, A v = 0) (u : H) :
    (Sᗮ.orthogonalProjection ∘L A ∘L Sᗮ.subtypeL) (Sᗮ.orthogonalProjection u) =
      Sᗮ.orthogonalProjection (A u) := by
  have hzero : A (S.starProjection u) = 0 :=
    hker _ (S.orthogonalProjection u).property
  have hsplit := congrArg A (S.starProjection_add_starProjection_orthogonal u)
  rw [map_add, hzero, zero_add] at hsplit
  exact congrArg Sᗮ.orthogonalProjection hsplit

private theorem regular_inverse_comp_form
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Submodule ℂ H) [CompleteSpace S] (A : H →L[ℂ] H)
    (B : Sᗮ →L[ℂ] Sᗮ)
    (hB : B = Sᗮ.orthogonalProjection ∘L A ∘L Sᗮ.subtypeL)
    (hker : ∀ v ∈ S, A v = 0) (hunit : IsUnit B) :
    (Sᗮ.subtypeL ∘L Ring.inverse B ∘L Sᗮ.orthogonalProjection).comp A =
      Sᗮ.starProjection := by
  apply ContinuousLinearMap.ext
  intro u
  have hBu : B (Sᗮ.orthogonalProjection u) = Sᗮ.orthogonalProjection (A u) :=
    (congrArg (fun T : Sᗮ →L[ℂ] Sᗮ => T (Sᗮ.orthogonalProjection u)) hB).trans
      (compressed_form_projected S A hker u)
  change (Ring.inverse B (Sᗮ.orthogonalProjection (A u)) : H) =
    (Sᗮ.orthogonalProjection u : H)
  apply congrArg (fun v : Sᗮ => (v : H))
  rw [← hBu, ← ContinuousLinearMap.mul_apply,
    Ring.inverse_mul_cancel _ hunit, ContinuousLinearMap.one_apply]

private theorem selfAdjoint_kernel_inner_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (v u : H) (hv : A v = 0) :
    ⟪v, A u⟫_ℂ = 0 := by
  exact (hA.isSymmetric v u).symm.trans
    ((congrArg (fun w : H => ⟪w, u⟫_ℂ) hv).trans (inner_zero_left u))

/-- The complement form really is the orthogonal compression of the
actual weak Helmholtz form, at every energy. -/
theorem h1ComplementForm_eq_compression (Ω : Set ℂ) (E₀ E : ℝ) :
    h1ComplementForm Ω E₀ E =
      (h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection.comp
        ((h1HelmholtzForm Ω E).comp (h1ResonantSpace Ω E₀)ᗮ.subtypeL) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [h1ComplementForm, h1ComplementMass, h1HelmholtzForm,
    h1MassOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, Submodule.subtypeL_apply,
    map_sub, map_smul, Submodule.orthogonalProjection_mem_subspace_eq_self]

/-- The actual reference form kills the actual kernel projection. -/
theorem h1HelmholtzForm_kernelProjection (Ω : Set ℂ) (E₀ : ℝ)
    (u : NeumannH1 Ω) :
    h1HelmholtzForm Ω E₀ ((h1ResonantSpace Ω E₀).starProjection u) = 0 := by
  change h1HelmholtzForm Ω E₀
    ((h1ResonantSpace Ω E₀).orthogonalProjection u : NeumannH1 Ω) = 0
  exact ((h1ResonantSpace Ω E₀).orthogonalProjection u).property

/-- At the reference energy the compressed form on the complement
projection agrees with the complement projection of the full form. -/
theorem h1ComplementForm_projected (Ω : Set ℂ) (E₀ : ℝ) (u : NeumannH1 Ω) :
    h1ComplementForm Ω E₀ E₀ ((h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection u) =
      (h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection (h1HelmholtzForm Ω E₀ u) := by
  exact (congrArg
    (fun T : (h1ResonantSpace Ω E₀)ᗮ →L[ℂ] (h1ResonantSpace Ω E₀)ᗮ =>
      T ((h1ResonantSpace Ω E₀)ᗮ.orthogonalProjection u))
    (h1ComplementForm_eq_compression Ω E₀ E₀)).trans
      (compressed_form_projected (h1ResonantSpace Ω E₀) (h1HelmholtzForm Ω E₀)
        (fun _ hv => hv) u)

/-- The actual regular resolvent composed with the actual reference form
is precisely the projection onto the orthogonal complement of its kernel.
Invertibility of the center compression is proved, rather than assumed. -/
theorem h1RegularResolvent_comp_form_center {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    (h1RegularResolvent Ω E₀ E₀).comp (h1HelmholtzForm Ω E₀) =
      (h1ResonantSpace Ω E₀)ᗮ.starProjection := by
  exact regular_inverse_comp_form (h1ResonantSpace Ω E₀)
    (h1HelmholtzForm Ω E₀) (h1ComplementForm Ω E₀ E₀)
    (h1ComplementForm_eq_compression Ω E₀ E₀) (fun _ hv => hv)
    (h1ComplementForm_isUnit hb hL hE₀)

/-- At resonance the regular NtD map is the trace of the genuine weak
solution with its actual kernel component removed. -/
theorem neumannBoundaryRegular_trace_of_solution {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {g : BoundaryL2} {u : NeumannH1 Ω}
    (hu : IsBoundaryNeumannSolution hb hL hγ E₀ g u) :
    neumannBoundaryRegular hb hL hγ E₀ E₀ g = h1BoundaryTrace hb hL hγ u -
      h1BoundaryTrace hb hL hγ ((h1ResonantSpace Ω E₀).starProjection u) := by
  have hform := (isBoundaryNeumannSolution_iff_form_eq hb hL hγ E₀ g u).1 hu
  have hreg : h1RegularResolvent Ω E₀ E₀ (h1BoundaryLoad hb hL hγ g) =
      (h1ResonantSpace Ω E₀)ᗮ.starProjection u := by
    rw [← hform]
    exact congrArg (fun A : NeumannH1 Ω →L[ℂ] NeumannH1 Ω => A u)
      (h1RegularResolvent_comp_form_center hb hL hE₀)
  change h1BoundaryTrace hb hL hγ
    (h1RegularResolvent Ω E₀ E₀ (h1BoundaryLoad hb hL hγ g)) = _
  rw [hreg, Submodule.starProjection_orthogonal_val, map_sub]

/-- Every actual kernel boundary trace annihilates the conormal density of
any actual weak solution at the same energy. -/
theorem boundaryNeumannSolution_compatible {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E₀ : ℝ}
    {g : BoundaryL2} {u : NeumannH1 Ω}
    (hu : IsBoundaryNeumannSolution hb hL hγ E₀ g u)
    (v : h1ResonantSpace Ω E₀) :
    ⟪neumannResonantTrace hb hL hγ E₀ v, g⟫_ℂ = 0 := by
  have hform := (isBoundaryNeumannSolution_iff_form_eq hb hL hγ E₀ g u).1 hu
  change ⟪h1BoundaryTrace hb hL hγ (v : NeumannH1 Ω), g⟫_ℂ = 0
  rw [← h1BoundaryLoad_inner, ← hform]
  exact selfAdjoint_kernel_inner_zero (h1HelmholtzForm Ω E₀)
    (h1HelmholtzForm_isSelfAdjoint Ω E₀) (v : NeumannH1 Ω) u v.property

/-- Compatibility also holds for the boundary traces of the genuinely
L²-normalized Neumann modes. -/
theorem boundaryNeumannSolution_compatible_L2Mode {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E₀ : ℝ}
    {g : BoundaryL2} {u : NeumannH1 Ω}
    (hu : IsBoundaryNeumannSolution hb hL hγ E₀ g u)
    (v : h1ResonantSpace Ω E₀) :
    ⟪neumannResonantBoundaryMode hb hL hγ E₀ v, g⟫_ℂ = 0 := by
  rw [neumannResonantBoundaryMode, inner_smul_left,
    boundaryNeumannSolution_compatible hb hL hγ hu v, mul_zero]

/-- The eigenvector identity fixes the mixed H¹/L² inner product even
when the second vector is an arbitrary H¹ solution. -/
theorem h1ResonantSpace_inner_left (Ω : Set ℂ) (E₀ : ℝ)
    (v : h1ResonantSpace Ω E₀) (u : NeumannH1 Ω) :
    ⟪(v : NeumannH1 Ω), u⟫_ℂ =
      ((E₀ + 1 : ℝ) : ℂ) * ⟪h1Value Ω v, h1Value Ω u⟫_ℂ := by
  have hzero : ⟪(v : NeumannH1 Ω), h1HelmholtzForm Ω E₀ u⟫_ℂ = 0 := by
    exact selfAdjoint_kernel_inner_zero (h1HelmholtzForm Ω E₀)
      (h1HelmholtzForm_isSelfAdjoint Ω E₀) (v : NeumannH1 Ω) u v.property
  have h := h1HelmholtzForm_inner Ω E₀ v u
  rw [hzero] at h
  have hgrad := sub_eq_zero.mp h.symm
  rw [h1_inner, hgrad]
  push_cast
  ring

/-- The forced L² normalization converts the boundary correction
coefficient to the actual interior L² pairing. -/
theorem neumannResonantBoundaryMode_inner_smul {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (v : h1ResonantSpace Ω E₀) (u : NeumannH1 Ω) :
    ⟪neumannResonantL2Mode Ω E₀ v, h1Value Ω u⟫_ℂ •
        neumannResonantBoundaryMode hb hL hγ E₀ v =
      ⟪(v : NeumannH1 Ω), u⟫_ℂ • neumannResonantTrace hb hL hγ E₀ v := by
  have hs : (Real.sqrt (E₀ + 1) : ℂ) * (Real.sqrt (E₀ + 1) : ℂ) =
      ((E₀ + 1 : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (show 0 ≤ E₀ + 1 by linarith)
  simp only [neumannResonantL2Mode, neumannResonantBoundaryMode,
    inner_smul_left, Complex.conj_ofReal, smul_smul]
  rw [h1ResonantSpace_inner_left]
  apply congrArg (fun c : ℂ => c • neumannResonantTrace hb hL hγ E₀ v)
  calc
    _ = ((Real.sqrt (E₀ + 1) : ℂ) * (Real.sqrt (E₀ + 1) : ℂ)) *
        ⟪h1Value Ω v, h1Value Ω u⟫_ℂ := by ring
    _ = _ := by rw [hs]

/-- The trace of the actual kernel projection is the finite correction
sum in any actual L²-normalized Neumann basis. -/
theorem h1BoundaryTrace_kernelProjection_eq_sum {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (h1ResonantSpace Ω E₀))
    (u : NeumannH1 Ω) :
    h1BoundaryTrace hb hL hγ ((h1ResonantSpace Ω E₀).starProjection u) =
      ∑ i, ⟪neumannResonantL2Mode Ω E₀ (b i), h1Value Ω u⟫_ℂ •
        neumannResonantBoundaryMode hb hL hγ E₀ (b i) := by
  classical
  change neumannResonantTrace hb hL hγ E₀
    ((h1ResonantSpace Ω E₀).orthogonalProjection u) = _
  rw [b.orthogonalProjection_apply_eq_sum u, map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact (neumannResonantBoundaryMode_inner_smul hb hL hγ hE₀ (b i) u).symm

/-- The actual regular NtD map on an actual weak solution has the precise
eigenfunction correction stated in the physical resonance identity. -/
theorem neumannBoundaryRegular_eq_trace_sub_sum {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (h1ResonantSpace Ω E₀))
    {g : BoundaryL2} {u : NeumannH1 Ω}
    (hu : IsBoundaryNeumannSolution hb hL hγ E₀ g u) :
    neumannBoundaryRegular hb hL hγ E₀ E₀ g = h1BoundaryTrace hb hL hγ u -
      ∑ i, ⟪neumannResonantL2Mode Ω E₀ (b i), h1Value Ω u⟫_ℂ •
        neumannResonantBoundaryMode hb hL hγ E₀ (b i) := by
  rw [neumannBoundaryRegular_trace_of_solution hb hL hγ hE₀ hu,
    h1BoundaryTrace_kernelProjection_eq_sum hb hL hγ hE₀ b u]

/-- In particular the genuine Herglotz wave gives compatible conormal
data at every nonnegative energy, including actual resonances. -/
theorem herglotzConormal_compatible_L2Mode {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {a : ℝ → ℂ} (ha : IsDirDensity a) (v : h1ResonantSpace Ω E₀) :
    ⟪neumannResonantBoundaryMode hb hL hγ E₀ v,
      herglotzConormalL2 hγ ha (Real.sqrt E₀)⟫_ℂ = 0 :=
  boundaryNeumannSolution_compatible_L2Mode hb hL hγ
    (herglotzWaveH1_sqrt_isBoundaryNeumannSolution hb hL hγ ha hE₀) v

/-- The genuine pole-subtracted NtD map takes the conormal of the actual
Herglotz wave to its boundary value minus its actual resonant contribution. -/
theorem neumannBoundaryRegular_herglotzConormal {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    neumannBoundaryRegular hb hL hγ E₀ E₀
        (herglotzConormalL2 hγ ha (Real.sqrt E₀)) =
      herglotzDirichletL2 hγ ha (Real.sqrt E₀) - h1BoundaryTrace hb hL hγ
        ((h1ResonantSpace Ω E₀).starProjection (herglotzWaveH1 hb ha (Real.sqrt E₀))) := by
  rw [neumannBoundaryRegular_trace_of_solution hb hL hγ hE₀
    (herglotzWaveH1_sqrt_isBoundaryNeumannSolution hb hL hγ ha hE₀),
    h1BoundaryTrace_herglotzWaveH1 hb hL hγ ha (Real.sqrt E₀)]

/-- The complete physical NtD part of the Herglotz resonance identity,
with the finite sum written in actual L²-normalized Neumann modes. -/
theorem neumannBoundaryRegular_herglotzConormal_eq_sub_sum {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ (h1ResonantSpace Ω E₀))
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    neumannBoundaryRegular hb hL hγ E₀ E₀
        (herglotzConormalL2 hγ ha (Real.sqrt E₀)) =
      herglotzDirichletL2 hγ ha (Real.sqrt E₀) -
        ∑ i, ⟪neumannResonantL2Mode Ω E₀ (b i),
          h1Value Ω (herglotzWaveH1 hb ha (Real.sqrt E₀))⟫_ℂ •
            neumannResonantBoundaryMode hb hL hγ E₀ (b i) := by
  rw [neumannBoundaryRegular_herglotzConormal hb hL hγ hE₀ ha,
    h1BoundaryTrace_kernelProjection_eq_sum hb hL hγ hE₀ b]

end PolyaNeumann

end
