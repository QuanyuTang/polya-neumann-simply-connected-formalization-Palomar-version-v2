module

public import RequestProject.TraceH1
public import RequestProject.SobolevCircle
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier coordinates for the actual boundary L² space

The source uses ordinary coordinate measure `dθ` on `(0, 2π]`. Its unitary
Fourier coefficients are therefore `sqrt (2π)` times the averaged Fourier
coefficients. The map is constructed through actual Lp functions on the
circle, and its surjectivity follows by pulling those functions back to the
parameter interval. No norm or completeness identity is assumed.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Real
open scoped InnerProductSpace ComplexConjugate

local instance boundaryFourierTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- Circle L² with Haar measure of total mass one. -/
abbrev BoundaryCircleHaarL2 := Lp ℂ 2
  (@AddCircle.haarAddCircle (2 * π) boundaryFourierTwoPiPos)

private theorem boundaryCircle_ae_volume_iff {p : AddCircle (2 * π) → Prop} :
    (∀ᵐ q ∂(volume : Measure (AddCircle (2 * π))), p q) ↔
      ∀ᵐ q ∂AddCircle.haarAddCircle, p q := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  have hs : ENNReal.ofReal (2 * π) ≠ 0 := by positivity
  simp only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hs, false_or]

/-- Transport an a.e. equality on the interval through its actual representative map. -/
theorem boundary_liftIoc_congr_ae {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioc 0 (2 * π))] g) :
    AddCircle.liftIoc (2 * π) 0 f =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIoc (2 * π) 0 g := by
  have hmp : MeasurePreserving
      (fun q : AddCircle (2 * π) => (AddCircle.equivIoc (2 * π) 0 q : ℝ))
      volume (volume.restrict (Ioc 0 (2 * π))) := by
    simpa only [zero_add, Function.comp_def] using
      (measurePreserving_subtype_coe measurableSet_Ioc).comp
        (AddCircle.measurePreserving_equivIoc (2 * π) (a := 0))
  apply boundaryCircle_ae_volume_iff.mp
  simpa only [AddCircle.liftIoc, Set.restrict_def, Function.comp_def] using
    hmp.quasiMeasurePreserving.ae h

/-- Every actual boundary L² function has an L² circle lift, without a boundedness assumption. -/
theorem boundaryCircleLift_memLp (g : BoundaryL2) :
    MemLp (AddCircle.liftIoc (2 * π) 0 (g : ℝ → ℂ)) 2
      AddCircle.haarAddCircle := by
  have hg : MemLp (g : ℝ → ℂ) 2 (volume.restrict (Ioc 0 (0 + 2 * π))) := by
    simpa only [zero_add] using Lp.memLp g
  exact hg.memLp_liftIoc.haarAddCircle

/-- The unscaled circle lift; its squared norm is divided by `2π`. -/
def boundaryCircleLift (g : BoundaryL2) : BoundaryCircleHaarL2 :=
  (boundaryCircleLift_memLp g).toLp (AddCircle.liftIoc (2 * π) 0 (g : ℝ → ℂ))

theorem boundaryCircleLift_coe (g : BoundaryL2) :
    (boundaryCircleLift g : AddCircle (2 * π) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIoc (2 * π) 0 (g : ℝ → ℂ) :=
  (boundaryCircleLift_memLp g).coeFn_toLp

def boundaryCircleLiftLin : BoundaryL2 →ₗ[ℂ] BoundaryCircleHaarL2 where
  toFun := boundaryCircleLift
  map_add' g h := by
    apply Lp.ext
    filter_upwards [boundaryCircleLift_coe (g + h),
      boundaryCircleLift_coe g, boundaryCircleLift_coe h,
      Lp.coeFn_add (boundaryCircleLift g) (boundaryCircleLift h),
      boundary_liftIoc_congr_ae (Lp.coeFn_add g h)] with q hgh hg hh hadd hlift
    change boundaryCircleLift (g + h) q = (boundaryCircleLift g + boundaryCircleLift h) q
    rw [hgh, hadd]
    change AddCircle.liftIoc (2 * π) 0 ((g + h : BoundaryL2) : ℝ → ℂ) q =
      boundaryCircleLift g q + boundaryCircleLift h q
    rw [hg, hh, hlift]
    rfl
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [boundaryCircleLift_coe (c • g), boundaryCircleLift_coe g,
      Lp.coeFn_smul c (boundaryCircleLift g),
      boundary_liftIoc_congr_ae (Lp.coeFn_smul c g)] with q hcg hg hsmul hlift
    change boundaryCircleLift (c • g) q = (c • boundaryCircleLift g) q
    rw [hcg, hsmul]
    change AddCircle.liftIoc (2 * π) 0 ((c • g : BoundaryL2) : ℝ → ℂ) q =
      c • boundaryCircleLift g q
    rw [hg, hlift]
    rfl

private theorem boundary_integral_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : Lp ℂ 2 μ) : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖f‖ ^ 2 := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) f f)
  rw [inner_self_eq_norm_sq, ← integral_re (L2.integrable_inner f f)] at h
  simp_rw [inner_self_eq_norm_sq] at h
  exact h.symm

theorem boundaryCircleLift_norm_sq (g : BoundaryL2) :
    ‖boundaryCircleLift g‖ ^ 2 = (2 * π)⁻¹ * ‖g‖ ^ 2 := by
  calc
    ‖boundaryCircleLift g‖ ^ 2 =
        ∫ q : AddCircle (2 * π), ‖boundaryCircleLift g q‖ ^ 2
          ∂AddCircle.haarAddCircle := (boundary_integral_norm_sq _).symm
    _ = ∫ q : AddCircle (2 * π),
        ‖AddCircle.liftIoc (2 * π) 0 (g : ℝ → ℂ) q‖ ^ 2
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [boundaryCircleLift_coe g] with q hq
      rw [hq]
    _ = (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), ‖g θ‖ ^ 2 := by
      rw [AddCircle.integral_haarAddCircle]
      change (2 * π)⁻¹ • (∫ q : AddCircle (2 * π),
        AddCircle.liftIoc (2 * π) 0 (fun θ => ‖g θ‖ ^ 2) q) = _
      rw [AddCircle.integral_liftIoc_eq_intervalIntegral, zero_add,
        intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul]
    _ = (2 * π)⁻¹ * ‖g‖ ^ 2 := by rw [boundary_integral_norm_sq]

private theorem boundary_liftIoc_pullback (f : AddCircle (2 * π) → ℂ) :
    AddCircle.liftIoc (2 * π) 0 (fun θ : ℝ => f (θ : AddCircle (2 * π))) = f := by
  funext q
  have hrep : ((AddCircle.equivIoc (2 * π) 0 q : ℝ) : AddCircle (2 * π)) = q :=
    (AddCircle.equivIoc (2 * π) 0).symm_apply_apply q
  exact congrArg f hrep

/-- Circle functions can all be recovered from actual L² functions on the parameter interval. -/
theorem boundaryCircleLift_surjective : Function.Surjective boundaryCircleLift := by
  intro f
  have hf : MemLp (f : AddCircle (2 * π) → ℂ) 2
      (volume : Measure (AddCircle (2 * π))) := (Lp.memLp f).of_haarAddCircle
  have hgp : MemLp (fun θ : ℝ => f (θ : AddCircle (2 * π))) 2
      (volume.restrict (Ioc 0 (2 * π))) := by
    simpa only [zero_add, Function.comp_def] using
      hf.comp_measurePreserving (AddCircle.measurePreserving_mk (2 * π) 0)
  let g : BoundaryL2 := hgp.toLp (fun θ : ℝ => f (θ : AddCircle (2 * π)))
  refine ⟨g, Lp.ext ?_⟩
  exact (boundaryCircleLift_coe g).trans
    ((boundary_liftIoc_congr_ae hgp.coeFn_toLp).trans
      (Eventually.of_forall fun q => congrFun (boundary_liftIoc_pullback f) q))

/-- Scaling the circle lift converts ordinary boundary measure to normalized Haar measure. -/
def boundaryCircleUnitaryLin : BoundaryL2 →ₗ[ℂ] BoundaryCircleHaarL2 :=
  (√(2 * π) : ℂ) • boundaryCircleLiftLin

theorem boundaryCircleUnitaryLin_norm (g : BoundaryL2) :
    ‖boundaryCircleUnitaryLin g‖ = ‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(√(2 * π) : ℂ) • boundaryCircleLift g‖ ^ 2 = ‖g‖ ^ 2
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt two_pi_pos.le, boundaryCircleLift_norm_sq,
    ← mul_assoc, mul_inv_cancel₀ two_pi_pos.ne', one_mul]

def boundaryCircleUnitaryIsometry : BoundaryL2 →ₗᵢ[ℂ] BoundaryCircleHaarL2 where
  toLinearMap := boundaryCircleUnitaryLin
  norm_map' := boundaryCircleUnitaryLin_norm

theorem boundaryCircleUnitary_surjective :
    Function.Surjective boundaryCircleUnitaryIsometry := by
  intro f
  obtain ⟨g, hg⟩ := boundaryCircleLift_surjective ((√(2 * π) : ℂ)⁻¹ • f)
  refine ⟨g, ?_⟩
  change (√(2 * π) : ℂ) • boundaryCircleLift g = f
  rw [hg, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast (Real.sqrt_pos.mpr two_pi_pos).ne'

def boundaryCircleUnitary : BoundaryL2 ≃ₗᵢ[ℂ] BoundaryCircleHaarL2 :=
  LinearIsometryEquiv.ofSurjective boundaryCircleUnitaryIsometry
    boundaryCircleUnitary_surjective

/-- The genuine unitary Fourier map from boundary L² with ordinary `dθ` to `ℓ²(ℤ)`. -/
def boundaryFourier : BoundaryL2 ≃ₗᵢ[ℂ] L2Z :=
  boundaryCircleUnitary.trans (fourierBasis (T := 2 * π)).repr

/-- Its coordinates are the orthonormal Fourier coefficients for ordinary parameter measure. -/
theorem boundaryFourier_apply (g : BoundaryL2) (n : ℤ) :
    boundaryFourier g n = (√(2 * π) : ℂ) *
      fourierCoeffOn two_pi_pos (g : ℝ → ℂ) n := by
  change (fourierBasis (T := 2 * π)).repr
    ((√(2 * π) : ℂ) • boundaryCircleLift g) n = _
  rw [fourierBasis_repr,
    fourierCoeff_congr_ae (Lp.coeFn_smul (√(2 * π) : ℂ) (boundaryCircleLift g)),
    fourierCoeff.const_smul,
    fourierCoeff_congr_ae (boundaryCircleLift_coe g), fourierCoeff_liftIoc_eq]
  simp only [zero_add, smul_eq_mul]

/-- The actual orthonormal boundary Fourier basis. -/
def boundaryFourierBasis : HilbertBasis ℤ ℂ BoundaryL2 :=
  HilbertBasis.ofRepr boundaryFourier

theorem boundaryFourier_parseval (g : BoundaryL2) :
    (∑' n : ℤ, ‖(√(2 * π) : ℂ) * fourierCoeffOn two_pi_pos (g : ℝ → ℂ) n‖ ^ 2) =
      ∫ θ in Ioc 0 (2 * π), ‖g θ‖ ^ 2 := by
  simp_rw [← boundaryFourier_apply]
  rw [← norm_sq_L2Z, boundaryFourier.norm_map, boundary_integral_norm_sq]

/-- The half-open representatives differ only at the identified endpoint, a Haar-null point. -/
theorem boundary_liftIoc_eq_liftIco_ae (f : ℝ → ℂ) :
    AddCircle.liftIoc (2 * π) 0 f =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIco (2 * π) 0 f := by
  have hv : (volume : Measure (AddCircle (2 * π))) {0} = 0 := by
    have h := AddCircle.volume_closedBall (T := 2 * π) (x := 0) 0
    simpa only [Metric.closedBall_zero, mul_zero, min_eq_right two_pi_pos.le,
      ENNReal.ofReal_zero] using h
  have hh : (@AddCircle.haarAddCircle (2 * π) _) {0} = 0 := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, Measure.smul_apply, smul_eq_mul] at hv
    exact (mul_eq_zero.mp hv).resolve_left (by positivity)
  have hne : ∀ᵐ q : AddCircle (2 * π) ∂AddCircle.haarAddCircle, q ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_eq_eq_singleton] using hh
  filter_upwards [hne] with q hq
  obtain ⟨θ, hθ, rfl⟩ := AddCircle.eq_coe_Ico q
  have hθ0 : θ ≠ 0 := fun h => hq (by rw [h]; rfl)
  have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 hθ0.symm
  rw [AddCircle.liftIoc_zero_coe_apply ⟨hθpos, hθ.2.le⟩,
    AddCircle.liftIco_zero_coe_apply hθ]

/-- The `[0, 2π)` lift used in kernel rows defines the same actual Lp element. -/
theorem boundaryCircleLift_eq_liftIco (g : BoundaryL2) :
    boundaryCircleLift g =
      ((boundaryCircleLift_memLp g).ae_eq (boundary_liftIoc_eq_liftIco_ae
        (g : ℝ → ℂ))).toLp (AddCircle.liftIco (2 * π) 0 (g : ℝ → ℂ)) := by
  apply Lp.ext
  have hIco := (boundaryCircleLift_memLp g).ae_eq
    (boundary_liftIoc_eq_liftIco_ae (g : ℝ → ℂ))
  exact ((boundaryCircleLift_coe g).trans
    (boundary_liftIoc_eq_liftIco_ae (g : ℝ → ℂ))).trans
      hIco.coeFn_toLp.symm

/-- Conjugate an actual bounded boundary operator through the genuine Fourier equivalence. -/
def boundaryFourierConjugate (N : BoundaryL2 →L[ℂ] BoundaryL2) : L2Z →L[ℂ] L2Z :=
  (boundaryFourier : BoundaryL2 →L[ℂ] L2Z) ∘L N ∘L
    (boundaryFourier.symm : L2Z →L[ℂ] BoundaryL2)

theorem boundaryFourierConjugate_apply (N : BoundaryL2 →L[ℂ] BoundaryL2)
    (g : BoundaryL2) :
    boundaryFourierConjugate N (boundaryFourier g) = boundaryFourier (N g) := by
  change boundaryFourier (N (boundaryFourier.symm (boundaryFourier g))) =
    boundaryFourier (N g)
  rw [boundaryFourier.symm_apply_apply]

theorem boundaryFourierConjugate_isSelfAdjoint (N : BoundaryL2 →L[ℂ] BoundaryL2)
    (hN : IsSelfAdjoint N) : IsSelfAdjoint (boundaryFourierConjugate N) := by
  unfold boundaryFourierConjugate
  rw [← boundaryFourier.adjoint_eq_symm]
  exact hN.conj_adjoint (boundaryFourier : BoundaryL2 →L[ℂ] L2Z)

/-- The full sesquilinear form, including its quadratic specialization, is preserved. -/
theorem boundaryFourierConjugate_inner (N : BoundaryL2 →L[ℂ] BoundaryL2)
    (f g : BoundaryL2) :
    ⟪boundaryFourier f, boundaryFourierConjugate N (boundaryFourier g)⟫_ℂ =
      ⟪f, N g⟫_ℂ := by
  rw [boundaryFourierConjugate_apply]
  exact boundaryFourier.inner_map_map f (N g)

theorem boundaryFourierConjugate_isCompactOperator (N : BoundaryL2 →L[ℂ] BoundaryL2)
    (hN : IsCompactOperator N) : IsCompactOperator (boundaryFourierConjugate N) :=
  (hN.comp_clm (boundaryFourier.symm : L2Z →L[ℂ] BoundaryL2)).clm_comp
    (boundaryFourier : BoundaryL2 →L[ℂ] L2Z)

end PolyaNeumann

end
