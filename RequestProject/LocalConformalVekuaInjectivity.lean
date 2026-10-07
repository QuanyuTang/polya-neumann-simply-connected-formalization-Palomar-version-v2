module

public import RequestProject.LocalConformalVekuaConormalBridge
public import RequestProject.NeumannResonanceDimension
public import RequestProject.LocalConformalHardySubspace

/-!
# Genuine Neumann kernels of the physical Vekua map

The normalized conormal kernel maps injectively into the actual H¹
Neumann resonance space. Its complex dimension is therefore bounded by
the original variational multiplicity. Away from that spectrum the
normalized conormal map is injective on the nonpositive Fourier inputs.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric
open scoped InnerProductSpace

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "VF" => localConformalVekuaH1AtBoundaryOrigin
  hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF

include hγ hτ hcoord in
/-- The true normalized conormal weak equation, written as equality of
the actual H¹ form pairing. -/
theorem localConformalVekuaHelmholtz_inner (E : ℝ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (w : NeumannH1 ΩF) :
    ⟪w, h1HelmholtzForm ΩF E (VF (E : ℂ) b)⟫_ℂ =
      ⟪QF w, NF (E : ℂ) b⟫_ℂ := by
  rw [h1HelmholtzForm_inner]
  exact localConformalVekuaH1_normalizedConormal_weak_form
    hR F hFs hb hL hhol hinj hC hK e he hsource hes hγ hτ hcoord (E : ℂ) b hbn w

include hγ hτ hcoord in
/-- Vanishing of the actual conormal is equivalent to membership of the
physical Vekua vector in the genuine Neumann form kernel. -/
theorem localConformalVekuaConormal_kernel_iff (E : ℝ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) :
    NF (E : ℂ) b = 0 ↔ h1HelmholtzForm ΩF E (VF (E : ℂ) b) = 0 := by
  constructor
  · intro hb0
    apply ext_inner_left ℂ
    intro w
    rw [localConformalVekuaHelmholtz_inner hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord E b hbn w, hb0, inner_zero_right, inner_zero_right]
  · intro hu0
    apply localConformalDiskHalfTrace_separates hR F hFs hb hL hhol hinj hC hK
      e he hsource hes
    intro w
    rw [← localConformalVekuaHelmholtz_inner hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord E b hbn w, hu0, inner_zero_right, inner_zero_right]

include hb hL hhol hinj hC hK e he hsource hes hγ hτ hcoord in
/-- The physical normalized conormal has no kernel on the full Hardy
input space at a nonresonant nonnegative real energy. -/
theorem localConformalVekuaConormal_injective_on_nonpositive
    {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) :
    InjOn (NF (E : ℂ)) {b : L2Z | IsNonpositiveFourierSupport b} := by
  intro b hb' d hd' hbd
  have hsupport : IsNonpositiveFourierSupport (b - d) := by
    intro n hn
    simp [hb' n hn, hd' n hn]
  have hconormal : NF (E : ℂ) (b - d) = 0 := by
    rw [map_sub, hbd, sub_self]
  have hform := (localConformalVekuaConormal_kernel_iff hR F hFs hb hL hhol hinj
    hC hK e he hsource hes hγ hτ hcoord E (b - d) hsupport).mp hconormal
  have hphysical : VF (E : ℂ) (b - d) = 0 := by
    apply h1HelmholtzForm_injective (Ω := ΩF) hb hL hE hnr
    simpa only [map_zero] using hform
  have hinput : b - d = 0 :=
    localConformalVekuaH1AtBoundaryOrigin_injective_on_nonpositive
      hR F hFs hb hL hhol hinj hC hK e he hsource hes (E : ℂ)
      hsupport (by intro n hn; simp) (by simpa only [map_zero] using hphysical)
  exact sub_eq_zero.mp hinput

/-- The actual normalized conormal kernel with nonpositive support. -/
def localConformalVekuaConormalKernel (E : ℝ) : Submodule ℂ L2Z :=
  nonpositiveFourierSubspace ⊓ (NF (E : ℂ)).ker

local notation "KF" => localConformalVekuaConormalKernel hR F hFs

/-- The genuine physical Vekua map embeds its conormal kernel in the
original H¹ resonance space. -/
def localConformalVekuaConormalKernelToResonance (E : ℝ) :
    KF E →ₗ[ℂ] h1ResonantSpace ΩF E where
  toFun b := ⟨VF (E : ℂ) b,
    (localConformalVekuaConormal_kernel_iff hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord E b b.property.1).mp b.property.2⟩
  map_add' b d := Subtype.ext ((VF (E : ℂ)).map_add b d)
  map_smul' c b := Subtype.ext ((VF (E : ℂ)).map_smul c b)

theorem localConformalVekuaConormalKernelToResonance_injective (E : ℝ) :
    Function.Injective (localConformalVekuaConormalKernelToResonance hR F hFs hb hL
      hhol hinj hC hK e he hsource hes hγ hτ hcoord E) := by
  intro b d hbd
  apply Subtype.ext
  exact localConformalVekuaH1AtBoundaryOrigin_injective_on_nonpositive
    hR F hFs hb hL hhol hinj hC hK e he hsource hes (E : ℂ)
    b.property.1 d.property.1 (congrArg Subtype.val hbd)

include hb hL hhol hinj hC hK e he hsource hes hγ hτ hcoord in
theorem finiteDimensional_localConformalVekuaConormalKernel (E : ℝ) :
    FiniteDimensional ℂ (KF E) := by
  haveI := finiteDimensional_h1ResonantSpace (Ω := ΩF) hb hL E
  exact Module.Finite.of_injective
    (localConformalVekuaConormalKernelToResonance hR F hFs hb hL hhol hinj hC hK
      e he hsource hes hγ hτ hcoord E)
    (localConformalVekuaConormalKernelToResonance_injective hR F hFs hb hL hhol hinj
      hC hK e he hsource hes hγ hτ hcoord E)

include hb hL hhol hinj hC hK e he hsource hes hγ hτ hcoord in
/-- The original complex Neumann multiplicity bounds the true conormal
kernel; no real-dimension doubling enters this estimate. -/
theorem localConformalVekuaConormalKernel_finrank_le_multiplicity
    {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (KF E) : ℕ∞) ≤
      {j : ℕ | neumannEigenvalue ΩF j = ENNReal.ofReal E}.encard := by
  haveI := finiteDimensional_h1ResonantSpace (Ω := ΩF) hb hL E
  have hdim := LinearMap.finrank_le_finrank_of_injective
    (localConformalVekuaConormalKernelToResonance_injective hR F hFs hb hL hhol hinj
      hC hK e he hsource hes hγ hτ hcoord E)
  calc
    (Module.finrank ℂ (KF E) : ℕ∞) ≤
        (Module.finrank ℂ (h1ResonantSpace ΩF E) : ℕ∞) := by exact_mod_cast hdim
    _ = _ := h1ResonantSpace_multiplicity_eq (Ω := ΩF) hb hL hE

end PhysicalCoordinates

end PolyaNeumann

end
