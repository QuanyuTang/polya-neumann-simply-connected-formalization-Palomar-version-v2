module

public import RequestProject.NeumannBoundaryPole
public import RequestProject.NeumannSpectral

/-!
# Dimension of the genuine form resonance space

The H¹ kernel used in the boundary pole is linearly equivalent to the
original weak Neumann eigenspace. Its complex dimension therefore agrees
with the multiplicity in the original variational sequence.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Topology
open scoped InnerProductSpace

private lemma continuous_one_sub_real_smul
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (M : X →L[ℂ] X) :
    Continuous (fun E : ℝ => (1 : X →L[ℂ] X) - ((E + 1 : ℝ) : ℂ) • M) := by
  fun_prop

/-- Inclusion sends the actual form kernel to the weak eigenspace. -/
def h1ResonantInclusion (Ω : Set ℂ) (E : ℝ) :
    h1ResonantSpace Ω E →ₗ[ℂ] neumannEigenspace Ω E where
  toFun u := ⟨h1Value Ω u,
    h1HelmholtzForm_kernel_mem Ω E u u.property⟩
  map_add' u v := Subtype.ext ((h1Value Ω).map_add u v)
  map_smul' c u := Subtype.ext ((h1Value Ω).map_smul c u)

theorem h1ResonantInclusion_injective {Ω : Set ℂ} (hΩ : IsOpen Ω) (E : ℝ) :
    Function.Injective (h1ResonantInclusion Ω E) := by
  intro u v huv
  apply Subtype.ext
  apply h1Value_injective hΩ
  exact congrArg Subtype.val huv

/-- Every genuine weak eigenfunction has an H¹ lift in the form kernel. -/
theorem h1ResonantInclusion_surjective (Ω : Set ℂ) (E : ℝ) :
    Function.Surjective (h1ResonantInclusion Ω E) := by
  intro u
  obtain ⟨g, hg, hw⟩ := u.property
  have hzero : h1HelmholtzForm Ω E (h1Vector hg) = 0 := by
    apply ext_inner_left ℂ
    intro v
    rw [h1HelmholtzForm_inner, inner_zero_right]
    simp only [h1Value_h1Vector, h1Gradient_h1Vector]
    exact sub_eq_zero.mpr (hw (h1Value Ω v) (fun i => h1Gradient Ω i v)
      (h1Value_weakGradient Ω v))
  exact ⟨⟨h1Vector hg, hzero⟩, Subtype.ext rfl⟩

def h1ResonantEquiv {Ω : Set ℂ} (hΩ : IsOpen Ω) (E : ℝ) :
    h1ResonantSpace Ω E ≃ₗ[ℂ] neumannEigenspace Ω E :=
  LinearEquiv.ofBijective (h1ResonantInclusion Ω E)
    ⟨h1ResonantInclusion_injective hΩ E, h1ResonantInclusion_surjective Ω E⟩

/-- On resonance vectors the shifted H¹ inner product is exactly the
L² inner product multiplied by `E + 1`. This fixes the normalization of
the boundary pole when an L²-orthonormal eigenfunction basis is used. -/
theorem h1ResonantSpace_inner (Ω : Set ℂ) (E : ℝ)
    (u v : h1ResonantSpace Ω E) :
    ⟪(u : NeumannH1 Ω), (v : NeumannH1 Ω)⟫_ℂ =
      ((E + 1 : ℝ) : ℂ) * ⟪h1Value Ω u, h1Value Ω v⟫_ℂ := by
  have h := h1HelmholtzForm_inner Ω E (u : NeumannH1 Ω) v
  rw [show h1HelmholtzForm Ω E (v : NeumannH1 Ω) = 0 from v.property,
    inner_zero_right] at h
  have hgrad := sub_eq_zero.mp h.symm
  rw [h1_inner, hgrad]
  push_cast
  ring

theorem h1ResonantSpace_multiplicity_eq {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (h1ResonantSpace Ω E) : ℕ∞) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  rw [(h1ResonantEquiv hL.1.1 E).finrank_eq]
  exact neumannEigenvalue_multiplicity_eq hb hL hE

/-- At a nonresonant reference energy the genuine full inverse is
continuous, including at the reference point itself. -/
theorem continuousAt_h1HelmholtzResolvent {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E₀) :
    ContinuousAt (h1HelmholtzResolvent Ω) E₀ := by
  have hB : Continuous (h1HelmholtzForm Ω) := by
    exact continuous_one_sub_real_smul
      ((ContinuousLinearMap.adjoint (h1Value Ω)).comp (h1Value Ω))
  obtain ⟨u, hu⟩ := h1HelmholtzForm_isUnit hb hL hE₀ hnr
  have hi := @NormedRing.inverse_continuousAt (NeumannH1 Ω →L[ℂ] NeumannH1 Ω) _ _ u
  rw [hu] at hi
  exact hi.comp hB.continuousAt

/-- The actual boundary NtD map is continuous at every nonresonant
reference energy. This includes the centre in the zero-multiplicity case. -/
theorem continuousAt_neumannToDirichletL2 {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E₀) :
    ContinuousAt (neumannToDirichletL2 hb hL hγ) E₀ := by
  exact continuousAt_const.clm_comp
    ((continuousAt_h1HelmholtzResolvent hb hL hE₀ hnr).clm_comp continuousAt_const)

end PolyaNeumann

end
