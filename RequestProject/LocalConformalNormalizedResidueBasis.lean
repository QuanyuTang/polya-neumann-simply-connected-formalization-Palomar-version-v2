module

public import RequestProject.NormalizedPeriodicBoundary
public import RequestProject.LocalConformalHerglotzDensity
public import RequestProject.TraceReparamReverse

/-!
The true normalized Neumann pole in a basis indexed by the multiplicity
of the original physical Neumann sequence.  The physical L2 normalization
absorbs the shifted H1 factor E+1.  Actual arclength reparametrization
identifies its compatibility conditions with the original physical loads.
This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Metric
open scoped InnerProductSpace ComplexConjugate

/-- The multiplicity is taken from the original physical Neumann
sequence; its finiteness and its equality to the true kernel dimension
are proved below. -/
def originalNeumannMultiplicity (Ω : Set ℂ) (E : ℝ) : ℕ :=
  {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard.toNat

theorem originalNeumannMultiplicity_eq_finrank {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    originalNeumannMultiplicity Ω E = Module.finrank ℂ (h1ResonantSpace Ω E) := by
  unfold originalNeumannMultiplicity
  rw [← h1ResonantSpace_multiplicity_eq hb hL hE]
  exact ENat.toNat_coe _

theorem originalNeumannMultiplicity_encard {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    (originalNeumannMultiplicity Ω E : ℕ∞) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  rw [originalNeumannMultiplicity_eq_finrank hb hL hE]
  exact h1ResonantSpace_multiplicity_eq hb hL hE

theorem originalNeumannMultiplicity_finite {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard ≠ ⊤ := by
  rw [← originalNeumannMultiplicity_encard hb hL hE]
  simp

/-- A genuine orthonormal H1 basis, with exactly the multiplicity
specified by the original variational Neumann spectrum. -/
def originalNeumannResonanceH1Basis {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    OrthonormalBasis (Fin (originalNeumannMultiplicity Ω E)) ℂ (h1ResonantSpace Ω E) := by
  letI : FiniteDimensional ℂ (h1ResonantSpace Ω E) := finiteDimensional_h1ResonantSpace hb hL E
  exact (stdOrthonormalBasis ℂ (h1ResonantSpace Ω E)).reindex
    (finCongr (originalNeumannMultiplicity_eq_finrank hb hL hE).symm)

/-- The physical eigenfunction lifted to the actual H1 graph space,
normalized in the original L2 space. -/
def originalNeumannResonanceH1Mode {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) : NeumannH1 Ω :=
  (Real.sqrt (E + 1) : ℂ) • (originalNeumannResonanceH1Basis hb hL hE j : NeumannH1 Ω)

def originalNeumannResonanceL2Mode {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) : L2 Ω :=
  neumannResonantL2Mode Ω E (originalNeumannResonanceH1Basis hb hL hE j)

theorem originalNeumannResonanceH1Mode_mem {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) :
    originalNeumannResonanceH1Mode hb hL hE j ∈ h1ResonantSpace Ω E := by
  exact (h1ResonantSpace Ω E).smul_mem _
    (originalNeumannResonanceH1Basis hb hL hE j).property

theorem originalNeumannResonanceL2Mode_eq_value {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) :
    originalNeumannResonanceL2Mode hb hL hE j =
      h1Value Ω (originalNeumannResonanceH1Mode hb hL hE j) := by
  simp only [originalNeumannResonanceL2Mode, originalNeumannResonanceH1Mode,
    neumannResonantL2Mode, map_smul]

theorem originalNeumannResonanceL2Mode_mem {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) :
    originalNeumannResonanceL2Mode hb hL hE j ∈ neumannEigenspace Ω E := by
  exact neumannResonantL2Mode_mem Ω E _

theorem originalNeumannResonanceL2Mode_orthonormal {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    Orthonormal ℂ (originalNeumannResonanceL2Mode hb hL hE) := by
  exact orthonormal_neumannResonantL2Mode Ω hE (originalNeumannResonanceH1Basis hb hL hE)

private theorem original_resonance_scale_ne_zero {E : ℝ} (hE : 0 ≤ E) :
    (Real.sqrt (E + 1) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (by linarith : 0 < E + 1)).ne'

private theorem original_scaled_basis_value_sum
    {ι X Y : Type*} [Fintype ι] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (b : OrthonormalBasis ι ℂ X)
    (V : X →ₗ[ℂ] Y) (s : ℂ) (hs : s ≠ 0) (m : ι → Y)
    (hm : ∀ j, m j = s • V (b j)) (v : X) :
    V v = ∑ j, (s⁻¹ * ⟪b j, v⟫_ℂ) • m j := by
  classical
  calc
    V v = V (∑ j, ⟪b j, v⟫_ℂ • b j) := congrArg V (b.sum_repr' v).symm
    _ = ∑ j, ⟪b j, v⟫_ℂ • V (b j) := by simp only [map_sum, map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hm j, smul_smul, mul_right_comm, inv_mul_cancel₀ hs, one_mul]

/-- These are a complete physical L2 eigenfunction basis, not only an
orthonormal family selected from a larger eigenspace. -/
theorem originalNeumannResonanceL2Mode_complete {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) (u : neumannEigenspace Ω E) :
    ∃ c : Fin (originalNeumannMultiplicity Ω E) → ℂ,
       (u : L2 Ω) = ∑ j, c j • originalNeumannResonanceL2Mode hb hL hE j := by
  classical
  let b : OrthonormalBasis (Fin (originalNeumannMultiplicity Ω E)) ℂ
      (h1ResonantSpace Ω E) := originalNeumannResonanceH1Basis hb hL hE
  let v : h1ResonantSpace Ω E := (h1ResonantEquiv hL.1.1 E).symm u
  let V : h1ResonantSpace Ω E →ₗ[ℂ] L2 Ω :=
    (h1Value Ω).toLinearMap.comp (h1ResonantSpace Ω E).subtype
  let s : ℂ := Real.sqrt (E + 1)
  have hv : V v = (u : L2 Ω) := by
    change h1Value Ω (v : NeumannH1 Ω) = (u : L2 Ω)
    exact congrArg Subtype.val ((h1ResonantEquiv hL.1.1 E).apply_symm_apply u)
  have hm (j : Fin (originalNeumannMultiplicity Ω E)) :
      originalNeumannResonanceL2Mode hb hL hE j = s • V (b j) := by
    rw [originalNeumannResonanceL2Mode_eq_value]
    change h1Value Ω (s • (b j : NeumannH1 Ω)) =
      s • h1Value Ω (b j : NeumannH1 Ω)
    exact (h1Value Ω).map_smul s (b j : NeumannH1 Ω)
  refine ⟨fun j => s⁻¹ * ⟪b j, v⟫_ℂ, hv.symm.trans ?_⟩
  exact original_scaled_basis_value_sum b V s (original_resonance_scale_ne_zero hE)
    (originalNeumannResonanceL2Mode hb hL hE) hm v

/-- The normalized boundary vector is the true half trace of the
original L2-normalized physical eigenfunction. -/
def normalizedNeumannResonanceMode {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z)
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) : L2Z :=
  Q (originalNeumannResonanceH1Mode hb hL hE j)

theorem normalizedNeumannResonanceMode_eq_scaled {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z)
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity Ω E)) :
    normalizedNeumannResonanceMode Q hb hL hE j =
      (Real.sqrt (E + 1) : ℂ) • Q (originalNeumannResonanceH1Basis hb hL hE j) := by
  simp only [normalizedNeumannResonanceMode, originalNeumannResonanceH1Mode, map_smul]

theorem normalizedNeumannResidue_eq_original_basis {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    normalizedNeumannResidue Q E = ∑ j : Fin (originalNeumannMultiplicity Ω E),
      InnerProductSpace.rankOne ℂ (normalizedNeumannResonanceMode Q hb hL hE j)
        (normalizedNeumannResonanceMode Q hb hL hE j) := by
  simpa only [normalizedNeumannResonanceMode_eq_scaled] using
    normalizedNeumannResidue_eq_sum_rankOne Q hE (originalNeumannResonanceH1Basis hb hL hE)

theorem normalizedNeumannCompatibility_iff_original_basis {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) (y : L2Z) :
    y ∈ normalizedNeumannCompatibility Q E ↔
      ∀ j : Fin (originalNeumannMultiplicity Ω E),
        ⟪normalizedNeumannResonanceMode Q hb hL hE j, y⟫_ℂ = 0 := by
  classical
  rw [mem_normalizedNeumannCompatibility_iff]
  constructor
  · intro hy j
    rw [normalizedNeumannResonanceMode_eq_scaled, inner_smul_left, hy, mul_zero]
  · intro hy v
    let b := originalNeumannResonanceH1Basis hb hL hE
    have hj (j : Fin (originalNeumannMultiplicity Ω E)) : ⟪Q (b j), y⟫_ℂ = 0 := by
      have h := hy j
      rw [normalizedNeumannResonanceMode_eq_scaled, inner_smul_left, Complex.conj_ofReal] at h
      exact (mul_eq_zero.mp h).resolve_left (original_resonance_scale_ne_zero hE)
    rw [← b.sum_repr' v]
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
      sum_inner, inner_smul_left, hj, mul_zero, Finset.sum_const_zero]

/-- Compression transports the actual original resonance modes by the
adjoint of the chart. It introduces no assumption that their compressed
images remain independent. -/
theorem normalizedNeumannResidue_chart_eq_original_basis
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) (T : X →L[ℂ] L2Z) :
    ContinuousLinearMap.adjoint T ∘L normalizedNeumannResidue Q E ∘L T =
      ∑ j : Fin (originalNeumannMultiplicity Ω E),
        InnerProductSpace.rankOne ℂ
          (ContinuousLinearMap.adjoint T (normalizedNeumannResonanceMode Q hb hL hE j))
          (ContinuousLinearMap.adjoint T (normalizedNeumannResonanceMode Q hb hL hE j)) := by
  classical
  rw [normalizedNeumannResidue_eq_original_basis Q hb hL hE]
  simp only [ContinuousLinearMap.comp_finset_sum, ContinuousLinearMap.finset_sum_comp,
    InnerProductSpace.comp_rankOne, InnerProductSpace.rankOne_comp]

/-- The chart compatibility conditions are the genuine compressed
original physical resonance traces. -/
theorem normalizedNeumannCompatibility_chart_iff_original_basis
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    {Ω : Set ℂ} (Q : NeumannH1 Ω →L[ℂ] L2Z) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) (T : X →L[ℂ] L2Z) (z : X) :
    T z ∈ normalizedNeumannCompatibility Q E ↔
      ∀ j : Fin (originalNeumannMultiplicity Ω E),
        ⟪ContinuousLinearMap.adjoint T (normalizedNeumannResonanceMode Q hb hL hE j), z⟫_ℂ = 0 := by
  rw [normalizedNeumannCompatibility_iff_original_basis Q hb hL hE]
  simp only [ContinuousLinearMap.adjoint_inner_left]

section ActualCoordinates

variable {R C : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1))
    (hC : ∀ z ∈ ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL

include hb hhol hinj hC hγ hτ hcoord in
theorem localConformalDiskHalfTrace_eq_zero_iff_boundaryTrace (u : NeumannH1 ΩF) :
    QF u = 0 ↔ h1BoundaryTrace hb hL hγ u = 0 := by
  have htrace := localConformalDiskH1Trace_eq_reparam hR F hFs hb hL hhol hinj hC hγ hτ hcoord
  constructor
  · intro hu
    have ht : localConformalDiskH1Trace hR F hFs hL u = 0 := by
      apply boundaryFourier.injective
      apply lp.ext
      funext n
      have hn : QF u n = 0 := by
        simpa only [lp.coeFn_zero, Pi.zero_apply] using congrArg (fun b : L2Z => b n) hu
      rw [localConformalDiskHalfTrace_apply] at hn
      have hs : (Real.sqrt (1 + |(n : ℝ)|) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 1 + |(n : ℝ)|)).ne'
      simpa only [map_zero, lp.coeFn_zero, Pi.zero_apply] using
        (mul_eq_zero.mp hn).resolve_left hs
    rw [← htrace] at ht
    exact (h1ReparamBoundaryTrace_eq_zero_iff hb hL hγ hτ u).mp ht
  · intro hu
    have ht := (h1ReparamBoundaryTrace_eq_zero_iff hb hL hγ hτ u).mpr hu
    rw [htrace] at ht
    apply lp.ext
    funext n
    simp only [localConformalDiskHalfTrace_apply, ht, map_zero,
      lp.coeFn_zero, Pi.zero_apply, mul_zero]

include hb hhol hinj hC hγ hτ hcoord in
/-- True normalized traces are injective on the original physical
resonance space, including its genuine constant mode at E=0. -/
theorem localConformalResonantHalfTrace_injective {E : ℝ} (hE : 0 ≤ E) :
    Function.Injective ((localConformalDiskHalfTrace hR F hFs hL).comp
      (h1ResonantSpace ΩF E).subtypeL) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have ht : h1BoundaryTrace hb hL hγ (u : NeumannH1 ΩF) = 0 :=
    (localConformalDiskHalfTrace_eq_zero_iff_boundaryTrace
      hR F hFs hb hL hhol hinj hC hγ hτ hcoord u).mp hu
  apply neumannResonantTrace_injective_nonneg hb hL hγ hE
  simpa only [neumannResonantTrace, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, map_zero] using ht

include hb hhol hinj hC hγ hτ hcoord in
theorem localConformal_normalizedResidue_original_rank {E : ℝ} (hE : 0 ≤ E) :
    Module.finrank ℂ (normalizedNeumannResidue QF E).range = originalNeumannMultiplicity ΩF E := by
  rw [normalizedNeumannResidue_finrank_eq QF hb hL hE
    (localConformalResonantHalfTrace_injective hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE)]
  exact (originalNeumannMultiplicity_eq_finrank hb hL hE).symm

include hb hhol hinj hC hγ hτ hcoord in
theorem localConformal_normalizedResidue_original_multiplicity {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (normalizedNeumannResidue QF E).range : ℕ∞) =
      {j : ℕ | neumannEigenvalue ΩF j = ENNReal.ofReal E}.encard := by
  rw [localConformal_normalizedResidue_original_rank hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE]
  exact originalNeumannMultiplicity_encard hb hL hE

include hb hhol hinj hC hγ hτ hcoord in
/-- The full compatibility space has exactly the original physical
complex codimension. The finite range is derived from the actual kernel. -/
theorem localConformal_normalizedCompatibility_original_codimension {E : ℝ} (hE : 0 ≤ E) :
    Module.finrank ℂ (normalizedNeumannCompatibility QF E)ᗮ = originalNeumannMultiplicity ΩF E := by
  letI : FiniteDimensional ℂ (h1ResonantSpace ΩF E) := finiteDimensional_h1ResonantSpace hb hL E
  letI : FiniteDimensional ℂ ((localConformalDiskHalfTrace hR F hFs hL).comp
    (h1ResonantSpace ΩF E).subtypeL).range := inferInstance
  rw [normalizedNeumannCompatibility, Submodule.orthogonal_orthogonal]
  rw [← normalizedNeumannResidue_range_eq QF hb hL hE
    (localConformalResonantHalfTrace_injective hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE)]
  exact localConformal_normalizedResidue_original_rank hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE

include hb hhol hinj hC hγ hτ hcoord in
theorem localConformal_normalizedResidue_mode_physical_pairing {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity ΩF E)) (g : BoundaryL2) :
    ⟪normalizedNeumannResonanceMode QF hb hL hE j, localConformalBoundaryLoad hτ g⟫_ℂ =
      ⟪h1BoundaryTrace hb hL hγ (originalNeumannResonanceH1Mode hb hL hE j), g⟫_ℂ := by
  exact localConformalBoundaryLoad_inner hR F hFs hb hL hhol hinj hC hγ hτ hcoord _ g

include hb hhol hinj hC hγ hτ hcoord in
/-- Compatibility with the entire normalized pole is exactly physical
orthogonality to all original L2-normalized Neumann resonance traces. -/
theorem localConformal_normalizedCompatibility_physical_basis {E : ℝ} (hE : 0 ≤ E)
    (g : BoundaryL2) :
    localConformalBoundaryLoad hτ g ∈ normalizedNeumannCompatibility QF E ↔
      ∀ j : Fin (originalNeumannMultiplicity ΩF E),
        ⟪h1BoundaryTrace hb hL hγ (originalNeumannResonanceH1Mode hb hL hE j), g⟫_ℂ = 0 := by
  rw [normalizedNeumannCompatibility_iff_original_basis QF hb hL hE]
  simp only [localConformal_normalizedResidue_mode_physical_pairing
    hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE]

include hb hhol hinj hC hγ hτ hcoord in
theorem localConformal_normalizedResidue_mode_coordinate_trace {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity ΩF E)) (n : ℤ) :
    normalizedNeumannResonanceMode QF hb hL hE j n =
      (Real.sqrt (1 + |(n : ℝ)|) : ℂ) *
        boundaryFourier (h1ReparamBoundaryTrace hL hγ hτ
          (originalNeumannResonanceH1Mode hb hL hE j)) n := by
  rw [localConformalDiskH1Trace_eq_reparam hR F hFs hb hL hhol hinj hC hγ hτ hcoord]
  exact localConformalDiskHalfTrace_apply hR F hFs hL _ n

include hb hhol hinj hC hγ hτ hcoord in
/-- The same actual mode with averaged Fourier coefficients, displaying
the full sqrt(2π) normalization at every frequency, including n=0. -/
theorem localConformal_normalizedResidue_mode_averaged_coeff {E : ℝ} (hE : 0 ≤ E)
    (j : Fin (originalNeumannMultiplicity ΩF E)) (n : ℤ) :
    normalizedNeumannResonanceMode QF hb hL hE j n =
      (Real.sqrt (1 + |(n : ℝ)|) : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) *
        fourierCoeffOn Real.two_pi_pos
          (h1ReparamBoundaryTrace hL hγ hτ (originalNeumannResonanceH1Mode hb hL hE j)) n := by
  rw [localConformal_normalizedResidue_mode_coordinate_trace
    hR F hFs hb hL hhol hinj hC hγ hτ hcoord hE j n, boundaryFourier_apply]
  ring

end ActualCoordinates

end PolyaNeumann

end
