module

public import RequestProject.BoundaryFourier
public import RequestProject.FiniteFourierChartRemainder
public import RequestProject.LocalConformalPrincipalFactorization

/-!
# The genuine periodic primitive of a normalized negative-half-order load

The input is an arbitrary normalized Fourier vector. Its load coefficients
are `Lambda^(1/2) y`, not necessarily the Fourier coefficients of an L2
function. Removing the constant load produces an actual BoundaryL2
primitive with half a Sobolev derivative. Its derivative identity is proved
coefficientwise, including frequency zero, and in weak Fourier pairing.

No endpoint value is assigned to this critical half-order primitive.
For a finite Fourier chart, regularity of its positive primitive implies
half-order regularity of the actual chart output and input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace ComplexConjugate

/-- The phase of the inverse tangential derivative, with a harmless value
at zero; the inverse-absolute-frequency operator removes that mode. -/
def roughPrimitivePhase (n : ℤ) : ℂ :=
  if 0 < n then -Complex.I else Complex.I

theorem norm_roughPrimitivePhase (n : ℤ) : ‖roughPrimitivePhase n‖ = 1 := by
  unfold roughPrimitivePhase
  split_ifs <;> simp

def roughPrimitivePhaseOperator : L2Z →L[ℂ] L2Z :=
  diagOp roughPrimitivePhase 1 (fun n => (norm_roughPrimitivePhase n).le)

def roughNormalizedPrimitiveCore : L2Z →L[ℂ] L2Z :=
  roughPrimitivePhaseOperator.comp normalizedInverseAbsOperator

@[simp] theorem roughNormalizedPrimitiveCore_apply (y : L2Z) (n : ℤ) :
    roughNormalizedPrimitiveCore y n =
      roughPrimitivePhase n * normalizedInverseAbsSymbol n * y n := by
  simp only [roughNormalizedPrimitiveCore, ContinuousLinearMap.comp_apply,
    roughPrimitivePhaseOperator, diagOp_apply, normalizedInverseAbsOperator_apply]
  ring

/-- Actual Fourier synthesis of the mean-zero periodic primitive. -/
def roughNormalizedPrimitiveFourier : L2Z →L[ℂ] L2Z :=
  (sobolevSmoothing (1 / 2 : ℝ) (by norm_num)).comp roughNormalizedPrimitiveCore

/-- An actual ordinary-measure boundary L2 element, even for a rough load. -/
def roughNormalizedPrimitive : L2Z →L[ℂ] BoundaryL2 :=
  boundaryFourier.symm.toLinearIsometry.toContinuousLinearMap.comp
    roughNormalizedPrimitiveFourier

@[simp] theorem boundaryFourier_roughNormalizedPrimitive (y : L2Z) :
    boundaryFourier (roughNormalizedPrimitive y) = roughNormalizedPrimitiveFourier y := by
  exact boundaryFourier.apply_symm_apply _

theorem roughNormalizedPrimitiveFourier_apply (y : L2Z) (n : ℤ) :
    roughNormalizedPrimitiveFourier y n =
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (roughPrimitivePhase n * normalizedInverseAbsSymbol n * y n) := by
  change fromL2 (1 / 2 : ℝ) (roughNormalizedPrimitiveCore y) n = _
  rw [fromL2, roughNormalizedPrimitiveCore_apply]

theorem roughNormalizedPrimitive_half_sobolev (y : L2Z) :
    IsSobolevSeq (1 / 2 : ℝ)
      (boundaryFourier (roughNormalizedPrimitive y) : ℤ → ℂ) := by
  rw [boundaryFourier_roughNormalizedPrimitive]
  exact isSobolevSeq_fromL2 (1 / 2 : ℝ) (roughNormalizedPrimitiveCore y)

@[simp] theorem roughNormalizedPrimitive_zero_mode (y : L2Z) :
    boundaryFourier (roughNormalizedPrimitive y) 0 = 0 := by
  rw [boundaryFourier_roughNormalizedPrimitive, roughNormalizedPrimitiveFourier_apply]
  simp [normalizedInverseAbsSymbol]

/-- Genuine negative-half-order load coefficients, in unitary Fourier
normalization. This definition makes no ordinary L2 load assertion. -/
def roughNormalizedLoadCoeff (y : L2Z) : ℤ → ℂ := fromL2 (-(1 / 2 : ℝ)) y

theorem roughNormalizedLoadCoeff_sobolev (y : L2Z) :
    IsSobolevSeq (-(1 / 2 : ℝ)) (roughNormalizedLoadCoeff y) :=
  isSobolevSeq_fromL2 (-(1 / 2 : ℝ)) y

theorem roughNormalizedLoadCoeff_apply (y : L2Z) (n : ℤ) :
    roughNormalizedLoadCoeff y n = (Real.sqrt (sobWeight n) : ℂ) * y n := by
  unfold roughNormalizedLoadCoeff fromL2
  rw [neg_neg, ← Real.sqrt_eq_rpow]

@[simp] theorem roughNormalizedLoadCoeff_zero (y : L2Z) :
    roughNormalizedLoadCoeff y 0 = y 0 := by
  simp [roughNormalizedLoadCoeff, fromL2, sobWeight]

private theorem rough_frequency_phase (n : ℤ) :
    (Complex.I * (n : ℂ)) * roughPrimitivePhase n = ((|(n : ℝ)| : ℝ) : ℂ) := by
  by_cases hn : 0 < n
  · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    rw [roughPrimitivePhase, if_pos hn, abs_of_pos hnr, Complex.ofReal_intCast]
    calc
      (Complex.I * (n : ℂ)) * -Complex.I =
          -(Complex.I * Complex.I) * (n : ℂ) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  · have hnr : (n : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hn)
    rw [roughPrimitivePhase, if_neg hn, abs_of_nonpos hnr, Complex.ofReal_neg,
      Complex.ofReal_intCast]
    calc
      (Complex.I * (n : ℂ)) * Complex.I =
          (Complex.I * Complex.I) * (n : ℂ) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring

private theorem rough_primitive_core_derivative (n : ℤ) (hn : n ≠ 0) :
    (Complex.I * (n : ℂ)) *
      (roughPrimitivePhase n * normalizedInverseAbsSymbol n) = (sobWeight n : ℂ) := by
  have habs : ((|(n : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, abs_ne_zero]
    exact_mod_cast hn
  rw [← mul_assoc, rough_frequency_phase, normalizedInverseAbsSymbol, if_neg hn,
    Complex.ofReal_div]
  exact mul_div_cancel₀ _ habs

private theorem rough_weight_half (n : ℤ) :
    sobWeight n ^ (-(1 / 2 : ℝ)) * sobWeight n = sobWeight n ^ (1 / 2 : ℝ) := by
  conv_lhs => rhs; rw [← Real.rpow_one (sobWeight n)]
  rw [← Real.rpow_add (sobWeight_pos n)]
  congr 1
  norm_num

/-- The true derivative coefficients at every nonzero frequency. -/
theorem roughNormalizedPrimitive_derivative_ne_zero (y : L2Z) (n : ℤ) (hn : n ≠ 0) :
    (Complex.I * (n : ℂ)) * boundaryFourier (roughNormalizedPrimitive y) n =
      roughNormalizedLoadCoeff y n := by
  rw [boundaryFourier_roughNormalizedPrimitive, roughNormalizedPrimitiveFourier_apply]
  calc
    _ = ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ((Complex.I * (n : ℂ)) *
          (roughPrimitivePhase n * normalizedInverseAbsSymbol n)) * y n := by ring
    _ = ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (sobWeight n : ℂ) * y n := by
      rw [rough_primitive_core_derivative n hn]
    _ = roughNormalizedLoadCoeff y n := by
      rw [← Complex.ofReal_mul, rough_weight_half]
      simp only [roughNormalizedLoadCoeff, fromL2, neg_neg]

/-- The constant load is separate: a periodic primitive differentiates to
the load minus its actual constant Fourier coefficient. -/
theorem roughNormalizedPrimitive_derivative (y : L2Z) (n : ℤ) :
    (Complex.I * (n : ℂ)) * boundaryFourier (roughNormalizedPrimitive y) n =
      roughNormalizedLoadCoeff (y - zeroModeProjection y) n := by
  by_cases hn : n = 0
  · subst n
    simp [roughNormalizedLoadCoeff, fromL2, zeroModeProjection_apply]
  · rw [roughNormalizedPrimitive_derivative_ne_zero y n hn]
    simp only [roughNormalizedLoadCoeff, fromL2, lp.coeFn_sub, Pi.sub_apply,
      zeroModeProjection_apply, if_neg hn, zero_mul, sub_zero]

/-- Removing the constant has not silently set the original mean to zero. -/
theorem roughNormalizedLoadCoeff_split_constant (y : L2Z) (n : ℤ) :
    roughNormalizedLoadCoeff y n =
      (Complex.I * (n : ℂ)) * boundaryFourier (roughNormalizedPrimitive y) n +
        (if n = 0 then y 0 else 0) := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [roughNormalizedPrimitive_derivative_ne_zero y n hn, if_neg hn, add_zero]

theorem rough_test_derivative_memℓp (t : L2Z)
    (ht : IsSobolevSeq 1 (t : ℤ → ℂ)) :
    Memℓp (fun n : ℤ => (Complex.I * (n : ℂ)) * t n) 2 := by
  refine memℓp_two_iff_summable.mpr ?_
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) ht
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast, Real.rpow_one]
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right (by unfold sobWeight; linarith [abs_nonneg (n : ℝ)])
      (norm_nonneg _)) 2

/-- The actual L2 Fourier derivative of a genuinely H1 test sequence. -/
def roughFourierTestDerivative (t : L2Z) (ht : IsSobolevSeq 1 (t : ℤ → ℂ)) : L2Z :=
  ⟨fun n => (Complex.I * (n : ℂ)) * t n, rough_test_derivative_memℓp t ht⟩

@[simp] theorem roughFourierTestDerivative_apply (t : L2Z)
    (ht : IsSobolevSeq 1 (t : ℤ → ℂ)) (n : ℤ) :
    roughFourierTestDerivative t ht n = (Complex.I * (n : ℂ)) * t n := rfl

/-- A true weak derivative identity, tested against every H1 Fourier
vector. Both pairings are actual L2 inner products, and the mean load
remains separate. No regularity of the rough input is assumed. -/
theorem roughNormalizedPrimitive_weak_pairing (y t : L2Z)
    (ht : IsSobolevSeq 1 (t : ℤ → ℂ)) :
    ⟪roughFourierTestDerivative t ht,
      boundaryFourier (roughNormalizedPrimitive y)⟫_ℂ =
      -⟪sobVec (1 / 2 : ℝ) (t : ℤ → ℂ)
        ((sobNormSq_mono (by norm_num : (1 / 2 : ℝ) ≤ 1) ht).1),
          y - zeroModeProjection y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_neg]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply', roughFourierTestDerivative_apply, sobVec_apply]
  change conj ((Complex.I * (n : ℂ)) * t n) *
      boundaryFourier (roughNormalizedPrimitive y) n =
    -(conj (((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * t n) *
      (y - zeroModeProjection y) n)
  have hd := roughNormalizedPrimitive_derivative y n
  have he : roughNormalizedLoadCoeff (y - zeroModeProjection y) n =
      ((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (y - zeroModeProjection y) n := by
    simp only [roughNormalizedLoadCoeff, fromL2, neg_neg]
  simp only [map_mul, Complex.conj_I, map_intCast, Complex.conj_ofReal]
  calc
    _ = -(conj (t n) * ((Complex.I * (n : ℂ)) *
        boundaryFourier (roughNormalizedPrimitive y) n)) := by ring
    _ = -(conj (t n) *
        (((sobWeight n ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (y - zeroModeProjection y) n)) := by
      rw [hd, he]
    _ = _ := by ring

/-- A regular positive primitive controls the positive normalized load.
No regularity of its unknown negative sector is assumed. -/
theorem roughNormalizedLoad_pos_half_of_primitive_pos_one (y : L2Z)
    (hp : IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ)) :
    IsSobolevSeq (1 / 2 : ℝ) (posProj y : ℤ → ℂ) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hp
  by_cases hn : 0 < n
  · have he := congrArg norm (roughNormalizedPrimitive_derivative_ne_zero y n hn.ne')
    rw [roughNormalizedLoadCoeff_apply, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_intCast, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] at he
    simp only [posProj, diagOp_apply, if_pos hn, one_mul, Real.rpow_one]
    rw [← Real.sqrt_eq_rpow, ← he]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right (by unfold sobWeight; linarith [abs_nonneg (n : ℝ)])
        (norm_nonneg _)) 2
  · simp only [posProj, diagOp_apply, if_neg hn, zero_mul, norm_zero, mul_zero]
    exact le_rfl

/-- When the other Fourier sector has finite support, positive primitive
regularity proves half-order regularity of the full normalized input. -/
theorem roughNormalizedLoad_half_of_primitive_pos_one (y : L2Z)
    (hfin : (Function.support (((1 - posProj) y : L2Z) : ℤ → ℂ)).Finite)
    (hp : IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ)) :
    IsSobolevSeq (1 / 2 : ℝ) (y : ℤ → ℂ) := by
  have hypos := roughNormalizedLoad_pos_half_of_primitive_pos_one y hp
  have hyneg := isSobolevSeq_of_finite_fourier_support (1 / 2 : ℝ) hfin
  have heq : posProj y + (1 - posProj) y = y := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    abel
  change y ∈ fourierSobolevSubmodule (1 / 2 : ℝ)
  rw [← heq]
  exact (fourierSobolevSubmodule (1 / 2 : ℝ)).add_mem hypos hyneg

private theorem rough_nonpositive_part_support {b : L2Z}
    (hb : (Function.support (b : ℤ → ℂ)).Finite) :
    (Function.support (((1 - posProj) b : L2Z) : ℤ → ℂ)).Finite := by
  refine hb.subset ?_
  intro n hn
  by_contra hb0
  have hbz : b n = 0 := not_not.mp hb0
  exact hn (by simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    posProj, diagOp_apply, hbz])

/-- The genuine finite Fourier chart has only finitely many nonpositive
output coefficients, regardless of the regularity of its input. -/
theorem finiteFourierChart_nonpositive_part_finite {d : ℕ}
    (u : Fin d → nonpositiveFourierSubspaceᗮ) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (z : nonpositiveFourierSubspaceᗮ) :
    (Function.support
      (((1 - posProj) (finiteFourierChart u v z) : L2Z) : ℤ → ℂ)).Finite := by
  have hfin : finiteFourierChart u v z - (z : L2Z) ∈ finiteFourierSubmodule := by
    simp only [finiteFourierChart, ContinuousLinearMap.add_apply, Submodule.subtypeL_apply,
      add_sub_cancel_left]
    rw [ContinuousLinearMap.sum_apply]
    apply Submodule.sum_mem
    intro r _
    rw [InnerProductSpace.rankOne_apply]
    exact finiteFourierSubmodule.smul_mem _ (hv r)
  have hzpos : posProj (z : L2Z) = (z : L2Z) := by
    rw [← nonpositive_orthogonal_starProjection]
    exact Submodule.starProjection_mem_subspace_eq_self z
  have hzero : (1 - posProj) (z : L2Z) = 0 := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hzpos, sub_self]
  have heq : (1 - posProj) (finiteFourierChart u v z) =
      (1 - posProj) (finiteFourierChart u v z - (z : L2Z)) := by
    rw [map_sub, hzero, sub_zero]
  rw [heq]
  exact rough_nonpositive_part_support hfin

/-- The rough chart bootstrap has a genuine, checkable primitive premise.
It does not assume that the normalized load is already half regular. -/
theorem finiteFourierChart_half_of_rough_primitive_pos_one {d : ℕ}
    (u : Fin d → nonpositiveFourierSubspaceᗮ) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (z : nonpositiveFourierSubspaceᗮ)
    (hp : IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive (finiteFourierChart u v z))) :
        ℤ → ℂ)) :
    IsSobolevSeq (1 / 2 : ℝ) (finiteFourierChart u v z : ℤ → ℂ) ∧
      IsSobolevSeq (1 / 2 : ℝ) ((z : L2Z) : ℤ → ℂ) := by
  have hy := roughNormalizedLoad_half_of_primitive_pos_one (finiteFourierChart u v z)
    (finiteFourierChart_nonpositive_part_finite u v hv z) hp
  refine ⟨hy, ?_⟩
  have hc := finiteFourierChart_correction_sobolev u v hv (1 / 2 : ℝ) z
  have heq : (z : L2Z) = finiteFourierChart u v z -
      (finiteFourierChart u v z - (z : L2Z)) := by abel
  change (z : L2Z) ∈ fourierSobolevSubmodule (1 / 2 : ℝ)
  rw [heq]
  exact (fourierSobolevSubmodule (1 / 2 : ℝ)).sub_mem hy hc

end PolyaNeumann

end
