module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import RequestProject.HerglotzForm
public import RequestProject.Reparam

/-!
# Reparametrization of the actual Herglotz boundary bound

A monotone Lipschitz change of parameter fixing `0` and `2π` preserves the
initial Herglotz jet and the monodromy. Consequently it preserves both the
actual observation of the conormal density and the Herglotz quadratic form.
The finite number of linear conditions on the direction density is unchanged.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open scoped Real InnerProductSpace

/-- The observation of a genuine Herglotz conormal density is unchanged by an
orientation-preserving Lipschitz reparametrization fixing the endpoints. -/
theorem observationAdj_herglotz_comp {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ (2 * π) = 2 * π)
    {E : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport (γ ∘ τ) E W')
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    observationAdj W' (herglotzConormal (Real.sqrt E) a (γ ∘ τ)) =
      observationAdj W (herglotzConormal (Real.sqrt E) a γ) := by
  have hclosed' : (γ ∘ τ) (2 * π) = (γ ∘ τ) 0 := by
    change γ (τ (2 * π)) = γ (τ 0)
    rw [hL, h0, hclosed]
  have hU := monodromy_comp hK hm hτ h0 hL hW hW'
  rw [(herglotzForm_eq (hK.comp hτ) hclosed' hW' ha).1,
    (herglotzForm_eq hK hclosed hW ha).1]
  change ((Real.sqrt 2 : ℂ) * Complex.I) • (monodromy W' - 1)
      (herglotzVec ha (Real.sqrt E) ((γ ∘ τ) 0)) =
    ((Real.sqrt 2 : ℂ) * Complex.I) • (monodromy W - 1)
      (herglotzVec ha (Real.sqrt E) (γ 0))
  simp only [Function.comp_apply, h0, hU]

/-- The genuine Herglotz form is unchanged by the same reparametrization. -/
theorem herglotzForm_comp {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ (2 * π) = 2 * π)
    {E : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport (γ ∘ τ) E W')
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    herglotzForm W' (γ ∘ τ) E a = herglotzForm W γ E a := by
  have hclosed' : (γ ∘ τ) (2 * π) = (γ ∘ τ) 0 := by
    change γ (τ (2 * π)) = γ (τ 0)
    rw [hL, h0, hclosed]
  have hU := monodromy_comp hK hm hτ h0 hL hW hW'
  rw [herglotzForm_eq_im (hK.comp hτ) hclosed' hW' ha,
    herglotzForm_eq_im hK hclosed hW ha]
  simp only [Function.comp_apply, h0, hU]

/-- A lower bound with finitely many conditions on the direction density transfers
with the same constant and the same linear map to the reparametrized curve. -/
theorem herglotz_density_lower_bound_comp {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ (2 * π) = 2 * π)
    {E A : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport (γ ∘ τ) E W')
    {m : ℕ} (L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hbound : ∀ a, IsDirDensity a → L a = 0 →
      -(A * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
        herglotzForm W γ E a) :
    ∀ a, IsDirDensity a → L a = 0 →
      -(A * ‖observationAdj W' (herglotzConormal (Real.sqrt E) a (γ ∘ τ))‖ ^ 2) ≤
        herglotzForm W' (γ ∘ τ) E a := by
  intro a ha hLa
  rw [observationAdj_herglotz_comp hK hclosed hm hτ h0 hL hW hW' ha,
    herglotzForm_comp hK hclosed hm hτ h0 hL hW hW' ha]
  exact hbound a ha hLa

/-- The same equality also transfers a density bound back to the original
curve. No Lipschitz estimate for the inverse change of parameter is needed. -/
theorem herglotz_density_lower_bound_of_comp {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ (2 * π) = 2 * π)
    {E A : ℝ} {W W' : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (hW' : IsTransport (γ ∘ τ) E W')
    {m : ℕ} (L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hbound : ∀ a, IsDirDensity a → L a = 0 →
      -(A * ‖observationAdj W' (herglotzConormal (Real.sqrt E) a (γ ∘ τ))‖ ^ 2) ≤
        herglotzForm W' (γ ∘ τ) E a) :
    ∀ a, IsDirDensity a → L a = 0 →
      -(A * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
        herglotzForm W γ E a := by
  intro a ha hLa
  have hb := hbound a ha hLa
  rw [observationAdj_herglotz_comp hK hclosed hm hτ h0 hL hW hW' ha,
    herglotzForm_comp hK hclosed hm hτ h0 hL hW hW' ha] at hb
  exact hb

/-- The local finite-rank boundary estimate, with exactly the energy and spectral
conditions used by the main theorem, transfers to any explicitly reparametrized
curve. The source estimate is used only on the source curve; the two physical
boundary forms and observations are identified by the preceding theorems. -/
theorem herglotz_boundary_bound_reparam {Ω : Set ℂ} {γ γ' : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ (2 * π) = 2 * π) (hcomp : γ ∘ τ = γ')
    (E₀ : ℝ) (m : ℕ)
    (hbound : ∃ A δ : ℝ, 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) →
      ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
        ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → L a = 0 →
          -(A * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
            herglotzForm W γ E a) :
    ∃ A δ : ℝ, 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) →
      ∀ W' : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ' E W' →
        ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → L a = 0 →
          -(A * ‖observationAdj W' (herglotzConormal (Real.sqrt E) a γ')‖ ^ 2) ≤
            herglotzForm W' γ' E a := by
  subst γ'
  obtain ⟨A, δ, hδ, hA⟩ := hbound
  refine ⟨A, δ, hδ, ?_⟩
  intro E hE hEδ hnr W' hW'
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  obtain ⟨L, hLbound⟩ := hA E hE hEδ hnr W hW
  exact ⟨L, herglotz_density_lower_bound_comp hK hclosed hm hτ h0 hL hW hW' L hLbound⟩

/-- The reverse local estimate is useful for the arclength construction, whose
output satisfies `γ_const ∘ τ = γ_original`. The source transport can be
composed with `τ`, so an inverse Lipschitz reparametrization is unnecessary. -/
theorem herglotz_boundary_bound_of_reparam {Ω : Set ℂ} {γ γ' : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0)
    {τ : ℝ → ℝ} (hm : Monotone τ) {Kτ : NNReal} (hτ : LipschitzWith Kτ τ)
    (h0 : τ 0 = 0) (hL : τ (2 * π) = 2 * π) (hcomp : γ ∘ τ = γ')
    (E₀ : ℝ) (m : ℕ)
    (hbound : ∃ A δ : ℝ, 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) →
      ∀ W' : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ' E W' →
        ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → L a = 0 →
          -(A * ‖observationAdj W' (herglotzConormal (Real.sqrt E) a γ')‖ ^ 2) ≤
            herglotzForm W' γ' E a) :
    ∃ A δ : ℝ, 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) →
      ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
        ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → L a = 0 →
          -(A * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
            herglotzForm W γ E a := by
  subst γ'
  obtain ⟨A, δ, hδ, hA⟩ := hbound
  refine ⟨A, δ, hδ, ?_⟩
  intro E hE hEδ hnr W hW
  have hW' := isTransport_comp hK hm hτ h0 hL hW
  obtain ⟨L, hLbound⟩ := hA E hE hEδ hnr (W ∘ τ) hW'
  exact ⟨L, herglotz_density_lower_bound_of_comp hK hclosed hm hτ h0 hL hW hW' L hLbound⟩

end PolyaNeumann

end
