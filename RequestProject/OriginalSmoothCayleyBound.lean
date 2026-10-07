module

public import RequestProject.RiemannMappingSmoothCollar
public import RequestProject.LocalConformalBoundaryParamSync
public import RequestProject.LocalConformalSuppliedHerglotzBound
public import RequestProject.BoundaryOrigin
public import RequestProject.CayleyChosenOrigin
public import RequestProject.Reparam

/-!
# The original smooth-domain Cayley bound at a chosen physical origin

The origin is chosen on the supplied physical boundary parameter.  The genuine
smooth conformal coordinates are then synchronized with this shifted physical
curve.  Their endpoint-preserving arclength lift transfers the nonzero cut to
the conformal transport, so the actual supplied-coordinate Herglotz estimate
has exactly the chosen-origin form required by the Cayley rank transfer.

The intermediate monodromy nontriviality input is the genuine fixed-space
consequence proved before the smooth-domain argument in `Main`.  This module
does not import `Main`, and its spectral restriction and multiplicity are the
original ones.  This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped Real

/-- The unchanged uniform Cayley rank estimate under the original bounded
smooth simply-connected domain assumptions, using the independently proved
nontriviality of the original boundary monodromy at the center energy. -/
theorem uniform_cayley_rank_bound_of_original_smooth_domain
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ)
    (E₀ : ℝ) (hE₀ : 0 < E₀) (m : ℕ)
    (hm : {i | neumannEigenvalue Ω i = ENNReal.ofReal E₀}.encard = m)
    (hU₀ : monodromyAt γ E₀ ≠ 1) :
    ∃ A δ : ℝ, 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) →
      CayleyRankBound (monodromyAt γ E) A m := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  let Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2 := fun E =>
    Classical.choose (transport_exists_of_lipschitz γ hKγ E)
  have hWs : ∀ E, IsTransport γ E (Ws E) := fun E =>
    Classical.choose_spec (transport_exists_of_lipschitz γ hKγ E)
  have hU : monodromy (Ws E₀) ≠ 1 := by
    simpa only [monodromyAt_eq hKγ (hWs E₀)] using hU₀
  obtain ⟨t, ht, ε, hε, _hεE, hcut⟩ :=
    exists_boundary_origin_of_boundaryParam hγ hWs hE₀ hU
  let γt : ℝ → ℂ := fun θ => γ (θ + t)
  have hγt : IsBoundaryParam Ω γt := hγ.shift t

  obtain ⟨R, C, K, F, e, hR, _hCpos, _hKpos, hFs, hhol, _hinj, himage,
    _hnz, hC, hK, he, hsource, hes, _hclosed, _hsphere⟩ :=
    exists_smoothConformal_coordinates Ω hb hS hsc
  have hbF : Bornology.IsBounded (F '' ball (0 : ℂ) 1) := by
    rw [himage]
    exact hb
  have hLF : IsLipschitzDomain (F '' ball (0 : ℂ) 1) := by
    rw [himage]
    exact hS.isLipschitzDomain
  have hγtF : IsBoundaryParam (F '' ball (0 : ℂ) 1) γt := by
    rw [himage]
    exact hγt
  obtain ⟨φ, _hφ, c, L, himageφ, _hclosedφ, hFsφ, hbφ, hLφ, hholφ,
    hinjφ, hCφ, hKφ, heφ, hsourceφ, hesφ, hγtφ, hτ, _hτper, hcoord,
    hΓLip, _horigin⟩ :=
    exists_localConformal_original_boundary_coordinates hR F hFs hbF hLF hhol
      hC hK e he hsource hes hγtF
  let τ : ℝ → ℝ :=
    localConformalRotateTraceReparam (normalizedArcReparam (physicalCircleTrace F)) φ
  let Γ : ℝ → ℂ := physicalCircleTrace (localConformalRotate F φ)
  have hτ' : IsC1TraceReparam τ c := hτ
  have hcomp : Γ = γt ∘ τ := by
    funext θ
    exact hcoord θ
  let WΓ : ℝ → ℝ → Ell2 →L[ℂ] Ell2 := fun E =>
    Classical.choose (transport_exists_of_lipschitz Γ hΓLip E)
  have hWΓ : ∀ E, IsTransport Γ E (WΓ E) := fun E =>
    Classical.choose_spec (transport_exists_of_lipschitz Γ hΓLip E)
  obtain ⟨Kγt, hKγt⟩ := hγt.lipschitz
  obtain ⟨Wt, hWt⟩ := transport_exists_of_lipschitz γt hKγt E₀
  have hcut_t : cutC (Wt (2 * π)) (basisVec 0) ≠ 0 :=
    hcut E₀ ⟨by linarith, by linarith⟩ Wt hWt
  obtain ⟨Kτ, hKτ⟩ := hτ'.lipschitz
  have hWΓcomp : IsTransport (γt ∘ τ) E₀ (WΓ E₀) := by
    rw [← hcomp]
    exact hWΓ E₀
  have hmono : monodromy (WΓ E₀) = monodromy Wt :=
    monodromy_comp hKγt hτ'.monotone hKτ hτ'.zero hτ'.endpoint hWt hWΓcomp
  have hcutΓ : cutC (WΓ E₀ (2 * π)) (basisVec 0) ≠ 0 := by
    have hcut_eq : cutC (WΓ E₀ (2 * π)) (basisVec 0) =
        cutC (Wt (2 * π)) (basisVec 0) := by
      change monodromy (WΓ E₀) (basisVec 0) - basisVec 0 =
        monodromy Wt (basisVec 0) - basisVec 0
      rw [hmono]
    rw [hcut_eq]
    exact hcut_t

  have himageφΩ : localConformalRotate F φ '' ball (0 : ℂ) 1 = Ω :=
    himageφ.trans himage
  have hmφ : {i | neumannEigenvalue (localConformalRotate F φ '' ball (0 : ℂ) 1) i =
      ENNReal.ofReal E₀}.encard = m := by
    simpa only [himageφΩ] using hm
  obtain ⟨A, δ, _hA, hδ, hbound⟩ :=
    exists_localConformal_original_herglotz_boundary_bound_of_multiplicity
      hR (localConformalRotate F φ) hFsφ hbφ hLφ hholφ
      (hinjφ.mono ball_subset_closedBall) hCφ hKφ
      (localConformalRotatePartialHomeomorph e φ) heφ hsourceφ hesφ
      hγtφ hτ hcoord hΓLip WΓ hWΓ hE₀ hcutΓ m hmφ
  refine uniform_cayley_rank_bound_of_chosen_origin hKγ hγ.periodic E₀ m
    (fun E => ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) ?_
  refine ⟨t, ht, A, δ, hδ, ?_⟩
  intro E hE hnear hnr W hW
  have hnrφ : ∀ j,
      neumannEigenvalue (localConformalRotate F φ '' ball (0 : ℂ) 1) j ≠
        ENNReal.ofReal E := by
    simpa only [himageφΩ] using hnr
  exact hbound E hE hnear hnrφ W hW

end PolyaNeumann

end
