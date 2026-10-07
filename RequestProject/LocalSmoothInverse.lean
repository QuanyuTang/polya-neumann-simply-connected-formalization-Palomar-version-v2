module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.Separation.Hausdorff
public import RequestProject.SmoothCompactExtension

/-!
# Smooth inverse coordinates near a compact injective set

Compact injectivity and local invertibility give an inverse on an open
neighborhood, rather than a homeomorphism of the whole plane. Smooth
functions in these inverse coordinates then have genuine compactly
supported physical representatives near the image of the compact set.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Filter
open scoped Topology

theorem exists_localSmoothInverse {K U : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F U) (hinj : InjOn F K)
    (hD : ∀ x ∈ U, ∃ D : ℂ ≃L[ℝ] ℂ, HasFDerivAt F (D : ℂ →L[ℝ] ℂ) x) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : ℂ → ℂ) = F ∧ K ⊆ e.source ∧
      e.source ⊆ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  have hcont (x : ℂ) (hx : x ∈ K) : ContinuousAt F x :=
    (hFs.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt
  have hloc (x : ℂ) (hx : x ∈ K) : ∃ V ∈ 𝓝 x, InjOn F V := by
    obtain ⟨D, hDx⟩ := hD x (hKU hx)
    have hs := hFs.contDiffAt (hU.mem_nhds (hKU hx))
    let e := hs.toOpenPartialHomeomorph F hDx (by simp)
    refine ⟨e.source, e.open_source.mem_nhds ?_, e.injOn⟩
    exact hs.mem_toOpenPartialHomeomorph_source hDx (by simp)
  obtain ⟨W, hW, hKW, hinjW⟩ := hinj.exists_isOpen_superset hK hcont hloc
  let V := W ∩ U
  have hV : IsOpen V := hW.inter hU
  have hKV : K ⊆ V := fun x hx => ⟨hKW hx, hKU hx⟩
  have hVU : V ⊆ U := inter_subset_right
  have hinjV : InjOn F V := hinjW.mono inter_subset_left
  have hopen : IsOpenMap (V.restrict F) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    obtain ⟨D, hDx⟩ := hD x (hVU x.prop)
    have hs := (hFs.contDiffAt (hU.mem_nhds (hVU x.prop))).hasStrictFDerivAt'
      hDx (by simp)
    change 𝓝 (F x) ≤ Filter.map (F ∘ Subtype.val) (𝓝 x)
    rw [← Filter.map_map, map_nhds_subtype_val, hV.nhdsWithin_eq x.prop]
    exact hs.map_nhds_eq_of_equiv.ge
  let e : OpenPartialHomeomorph ℂ ℂ :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hinjV.toPartialEquiv F V)
      (hFs.continuousOn.mono hVU) hopen hV
  refine ⟨e, rfl, hKV, hVU, ?_⟩
  intro y hy
  obtain ⟨D, hDy⟩ := hD (e.symm y) (hVU (e.symm.mapsTo hy))
  exact (e.contDiffAt_symm hy hDy
    (hFs.contDiffAt (hU.mem_nhds (hVU (e.symm.mapsTo hy))))).contDiffWithinAt

/-- Invertibility is required only on the compact set. Continuity of the
differential extends it to a neighborhood before the local inverses are glued. -/
theorem exists_localSmoothInverse_of_compact_differential {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F U) (hinj : InjOn F K)
    (hD : ∀ x ∈ K, ∃ D : ℂ ≃L[ℝ] ℂ, HasFDerivAt F (D : ℂ →L[ℝ] ℂ) x) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : ℂ → ℂ) = F ∧ K ⊆ e.source ∧
      e.source ⊆ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target := by
  let V := U ∩ {x | fderiv ℝ F x ∈
    range ((↑) : (ℂ ≃L[ℝ] ℂ) → (ℂ →L[ℝ] ℂ))}
  have hVU : V ⊆ U := inter_subset_left
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    refine Filter.inter_mem (hU.mem_nhds hx.1) ?_
    exact ((hFs.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt
      (hU.mem_nhds hx.1)).preimage_mem_nhds
        (ContinuousLinearEquiv.isOpen.mem_nhds hx.2)
  have hKV : K ⊆ V := by
    intro x hx
    obtain ⟨D, hDx⟩ := hD x hx
    exact ⟨hKU hx, ⟨D, hDx.fderiv.symm⟩⟩
  have hDV : ∀ x ∈ V, ∃ D : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt F (D : ℂ →L[ℝ] ℂ) x := by
    intro x hx
    obtain ⟨D, hDeq⟩ := hx.2
    refine ⟨D, ?_⟩
    rw [hDeq]
    exact ((hFs.contDiffAt (hU.mem_nhds hx.1)).differentiableAt (by simp)).hasFDerivAt
  obtain ⟨e, he, hKe, heV, hes⟩ :=
    exists_localSmoothInverse hK hV hKV F (hFs.mono hVU) hinj hDV
  exact ⟨e, he, hKe, heV.trans hVU, hes⟩

theorem localSmoothInverse_testFunction (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {K : Set ℂ} (hK : IsCompact K) (hKs : K ⊆ e.source)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ f : ℂ → ℂ, TestFunction univ f ∧
      ∀ x ∈ e '' K, f =ᶠ[𝓝 x] (φ ∘ e.symm) := by
  apply exists_smooth_compact_extension
    (hK.image_of_continuousOn (e.continuousOn.mono hKs)) e.open_target
    (image_subset_iff.mpr (fun x hx => e.mapsTo (hKs hx)))
  exact hφ.comp_contDiffOn hes

end PolyaNeumann

end
