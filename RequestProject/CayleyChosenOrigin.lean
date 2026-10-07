module

public import RequestProject.CayleyRankRebase
public import RequestProject.HerglotzForm

/-!
# Universal Cayley bounds from a chosen boundary origin

A Herglotz lower bound may be established at one cyclic starting point
chosen near a fixed energy. The Cayley rank estimate transfers back to
the supplied periodic curve, with the same threshold and multiplicity.
The energy restriction is arbitrary, so the original nonresonance
predicate can be used without changing its spectral meaning.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped Real

/-- A local Herglotz estimate at one chosen cyclic origin yields the same
uniform Cayley rank bound for the original boundary parameter. -/
theorem uniform_cayley_rank_bound_of_chosen_origin
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ (2 * π)) (E₀ : ℝ) (m : ℕ) (P : ℝ → Prop)
    (hbound : ∃ t ∈ Icc 0 (2 * π), ∃ A δ : ℝ, 0 < δ ∧
      ∀ E, 0 < E → |E - E₀| < δ → P E →
        ∀ W' : ℝ → Ell2 →L[ℂ] Ell2,
          IsTransport (fun θ => γ (θ + t)) E W' →
            ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ),
              ∀ a, IsDirDensity a → L a = 0 →
                -(A * ‖observationAdj W'
                  (herglotzConormal (Real.sqrt E) a (fun θ => γ (θ + t)))‖ ^ 2) ≤
                  herglotzForm W' (fun θ => γ (θ + t)) E a) :
    ∃ A δ : ℝ, 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ → P E →
      CayleyRankBound (monodromyAt γ E) A m := by
  obtain ⟨t, ht, A, δ, hδ, hA⟩ := hbound
  have hKt : LipschitzWith K (fun θ => γ (θ + t)) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [dist_add_right] using hK.dist_le_mul (x + t) (y + t)
  have hclosedt : (fun θ => γ (θ + t)) (2 * π) =
      (fun θ => γ (θ + t)) 0 := by
    change γ (2 * π + t) = γ (0 + t)
    rw [zero_add, add_comm (2 * π) t]
    exact hper t
  refine ⟨A, δ, hδ, ?_⟩
  intro E hE hEδ hPE
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  obtain ⟨W', hW'⟩ := transport_exists_of_lipschitz (fun θ => γ (θ + t)) hKt E
  obtain ⟨L, hL⟩ := hA E hE hEδ hPE W' hW'
  have hshift : CayleyRankBound (monodromy W') A m :=
    cayleyRankBound_of_herglotzForm_bound hKt hclosedt hW' A A le_rfl L hL
  rw [monodromyAt_eq hK hW]
  exact cayleyRankBound_of_rebased_transport hK hper hW ht hW' hshift

end PolyaNeumann

end
