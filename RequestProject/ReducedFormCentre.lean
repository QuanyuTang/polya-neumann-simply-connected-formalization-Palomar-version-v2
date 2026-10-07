module

public import RequestProject.ReducedForm

/-!
# Chart reduction on the actual set of admissible energies

The reduction is stated on an energy set `U`, without removing its centre.
In the physical application `U` consists of nonresonant energies. If the
centre has zero multiplicity, it belongs to `U` and the residue is zero;
if the multiplicity is positive, it does not belong to `U`.

All form, nullspace and pole identities must hold on `U`. This file proves
only their functional-analytic consequence; it does not assert these
identities for physical boundary operators without their separate proofs.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open InnerProductSpace ContinuousLinearMap Filter Topology Module
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (H₀ : Submodule ℂ H) [H₀.HasOrthogonalProjection]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

theorem chart_reduced_boundary_bound_on_energy_set {m : ℕ} (J : ℝ → H₀ →L[ℂ] H) (R : H₀ᗮ →L[ℂ] H)
    (E₀ : ℝ) (U : Set ℝ)
    (hunit : ∀ E ∈ U, IsUnit (J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection))
    (P Preg : ℝ → H →L[ℂ] H) (S : ℝ → H →L[ℂ] Y) (w : Fin m → H)
    (hsa : ∀ E ∈ U, IsSelfAdjoint (P E))
    (hnullP : ∀ E ∈ U, P E ∘L J E = 0) (hnullS : ∀ E ∈ U, S E ∘L J E = 0)
    (hpole : ∀ E ∈ U,
      P E = ((-2 / (E - E₀) : ℝ) : ℂ) • ∑ j, rankOne ℂ (w j) (w j) + Preg E)
    (hPreg : ContinuousAt Preg E₀) (hS : ContinuousAt S E₀)
    (α : ℝ) (hα : 0 < α) (C : H₀ᗮ →L[ℂ] H₀ᗮ) (hC : IsCompactOperator C)
    (hreg : adjoint R ∘L Preg E₀ ∘L R = (α : ℂ) • ContinuousLinearMap.id ℂ H₀ᗮ + C)
    (hinj : ∀ z : H₀ᗮ, (∀ j, ⟪adjoint R (w j), z⟫_ℂ = 0) → S E₀ (R z) = 0 → z = 0) :
    ∃ A₀ > 0, ∃ V ∈ 𝓝 E₀, ∀ E ∈ V, E ∈ U →
      ∃ ℓ : H →ₗ[ℂ] (Fin m → ℂ), ∀ y, ℓ y = 0 →
        -(A₀ * ‖S E y‖ ^ 2) ≤ (⟪y, P E y⟫_ℂ).re := by
  set η : Fin m → H₀ᗮ := fun j => adjoint R (w j) with hη
  set Z : Submodule ℂ H₀ᗮ := (Submodule.span ℂ (Set.range η))ᗮ with hZ
  have hmemZ : ∀ z, z ∈ Z ↔ ∀ j, ⟪η j, z⟫_ℂ = 0 := by
    intro z
    constructor
    · intro hz j
      exact (Submodule.mem_orthogonal _ _).1 hz _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro h
      rw [Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  obtain ⟨A₀, hA₀, hev⟩ := reduced_lower_bound_subspace Z α hα C hC
    (fun E => adjoint R ∘L Preg E ∘L R) (fun E => S E ∘L R) E₀
    (continuousAt_const.clm_comp (hPreg.clm_comp continuousAt_const))
    (hS.clm_comp continuousAt_const) hreg (fun z hz h0 => hinj z ((hmemZ z).1 hz) h0)
  refine ⟨A₀, hA₀, _, hev, ?_⟩
  intro E hE hEU
  obtain ⟨u, hu⟩ := hunit E hEU
  set zc : H →L[ℂ] H₀ᗮ := H₀ᗮ.orthogonalProjection ∘L (↑u⁻¹ : H →L[ℂ] H) with hzc
  refine ⟨LinearMap.pi fun j => (((innerSL ℂ (η j)) ∘L zc : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ), ?_⟩
  intro y hy
  set x := (↑u⁻¹ : H →L[ℂ] H) y with hx
  set a := H₀.orthogonalProjection x with ha
  set z := H₀ᗮ.orthogonalProjection x with hz
  have hzj : ∀ j, ⟪η j, z⟫_ℂ = 0 := by
    intro j
    exact congrFun hy j
  have hyx : y = J E a + R z := by
    have h1 : (u : H →L[ℂ] H) x = y := by
      rw [hx, ← ContinuousLinearMap.mul_apply, Units.mul_inv, ContinuousLinearMap.one_apply]
    rw [← h1, hu]
    rfl
  have hSy : S E y = S E (R z) := by
    have := congrArg (fun T => T a) (hnullS E hEU)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
    rw [hyx, map_add, this, zero_add]
  have hPJa : P E (J E a) = 0 := by
    have := congrArg (fun T => T a) (hnullP E hEU)
    simpa using this
  have hPy : ⟪y, P E y⟫_ℂ = ⟪R z, P E (R z)⟫_ℂ := by
    rw [hyx, map_add, hPJa, zero_add, inner_add_left]
    have : ⟪J E a, P E (R z)⟫_ℂ = 0 := by
      rw [← (hsa E hEU).adjoint_eq, adjoint_inner_right, hPJa, inner_zero_left]
    rw [this, zero_add]
  have hwR : ∀ j, ⟪w j, R z⟫_ℂ = 0 := by
    intro j
    rw [← adjoint_inner_left]
    exact hzj j
  have hpz : ⟪R z, P E (R z)⟫_ℂ = ⟪z, (adjoint R ∘L Preg E ∘L R) z⟫_ℂ := by
    rw [hpole E hEU, inner_pole_add_eq_of_orthogonal w _ _ _ hwR,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, adjoint_inner_right]
  have hb := hE z ((hmemZ z).2 hzj)
  rw [hPy, hpz, hSy]
  exact hb


theorem chart_boundary_lower_bound_on_energy_set {m : ℕ} {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (J : ℝ → H₀ →L[ℂ] H) (R : H₀ᗮ →L[ℂ] H)
    (E₀ : ℝ) (U : Set ℝ)
    (hunit : ∀ E ∈ U, IsUnit (J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection))
    (P Preg : ℝ → H →L[ℂ] H) (S : ℝ → H →L[ℂ] Y) (w : Fin m → H)
    (hsa : ∀ E ∈ U, IsSelfAdjoint (P E))
    (hnullP : ∀ E ∈ U, P E ∘L J E = 0) (hnullS : ∀ E ∈ U, S E ∘L J E = 0)
    (hpole : ∀ E ∈ U,
      P E = ((-2 / (E - E₀) : ℝ) : ℂ) • ∑ j, rankOne ℂ (w j) (w j) + Preg E)
    (hPreg : ContinuousAt Preg E₀) (hS : ContinuousAt S E₀)
    (α : ℝ) (hα : 0 < α) (C : H₀ᗮ →L[ℂ] H₀ᗮ) (hC : IsCompactOperator C)
    (hreg : adjoint R ∘L Preg E₀ ∘L R = (α : ℂ) • ContinuousLinearMap.id ℂ H₀ᗮ + C)
    (hinj : ∀ z : H₀ᗮ, (∀ j, ⟪adjoint R (w j), z⟫_ℂ = 0) → S E₀ (R z) = 0 → z = 0)
    (Aop : ℝ → H →L[ℂ] H) (Oadj : ℝ → H →L[ℂ] X) (B : ℝ → X →L[ℂ] X)
    (Pi : ℝ → X →L[ℂ] Y) (b : ℝ)
    (hA : ∀ E ∈ U, ∀ y, (⟪y, Aop E y⟫_ℂ).re =
      (⟪y, P E y⟫_ℂ).re - (⟪Oadj E y, B E (Oadj E y)⟫_ℂ).re)
    (hB : ∀ E ∈ U, ‖B E‖ ≤ b) (hPi : ∀ E ∈ U, ‖Pi E‖ ≤ 1)
    (hSO : ∀ E ∈ U, S E = Pi E ∘L Oadj E) :
    ∃ A₁, ∃ V ∈ 𝓝 E₀, ∀ E ∈ V, E ∈ U →
      ∃ ℓ : H →ₗ[ℂ] (Fin m → ℂ), ∀ y, ℓ y = 0 →
        -(A₁ * ‖Oadj E y‖ ^ 2) ≤ (⟪y, Aop E y⟫_ℂ).re := by
  obtain ⟨A₀, hA₀, V, hV, h⟩ := chart_reduced_boundary_bound_on_energy_set H₀ J R E₀ U hunit P Preg S w hsa
    hnullP hnullS hpole hPreg hS α hα C hC hreg hinj
  refine ⟨A₀ + b, V, hV, fun E hE hEU => ?_⟩
  obtain ⟨ℓ, hℓ⟩ := h E hE hEU
  refine ⟨ℓ, fun y hy => ?_⟩
  have h1 := hℓ y hy
  have h2 : ‖S E y‖ ≤ ‖Oadj E y‖ := by
    rw [hSO E hEU, ContinuousLinearMap.comp_apply]
    calc ‖Pi E (Oadj E y)‖ ≤ ‖Pi E‖ * ‖Oadj E y‖ := (Pi E).le_opNorm _
      _ ≤ 1 * ‖Oadj E y‖ := by gcongr; exact hPi E hEU
      _ = ‖Oadj E y‖ := one_mul _
  have h3 : ‖S E y‖ ^ 2 ≤ ‖Oadj E y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 : (⟪Oadj E y, B E (Oadj E y)⟫_ℂ).re ≤ b * ‖Oadj E y‖ ^ 2 := by
    calc (⟪Oadj E y, B E (Oadj E y)⟫_ℂ).re ≤ ‖⟪Oadj E y, B E (Oadj E y)⟫_ℂ‖ :=
          Complex.re_le_norm _
      _ ≤ ‖Oadj E y‖ * ‖B E (Oadj E y)‖ := norm_inner_le_norm _ _
      _ ≤ ‖Oadj E y‖ * (‖B E‖ * ‖Oadj E y‖) := by gcongr; exact (B E).le_opNorm _
      _ ≤ ‖Oadj E y‖ * (b * ‖Oadj E y‖) := by gcongr; exact hB E hEU
      _ = b * ‖Oadj E y‖ ^ 2 := by ring
  rw [hA E hEU]
  nlinarith [mul_le_mul_of_nonneg_left h3 hA₀.le]

end PolyaNeumann

end
