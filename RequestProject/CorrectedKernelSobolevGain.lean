module

public import RequestProject.CorrectedKernelSymm
public import RequestProject.ConormalNormalization
public import RequestProject.ReducedFormTwoStep

/-!
# Sobolev gains of the actual normalized corrected-kernel operator

The base operator is always the existing `hsMatrixOp` with matrix
`correctedRemainderMatrix W 0 0`. The weighted matrices are identified with
its Sobolev conjugates on the standard Fourier basis, and equality on every
input follows from density of that basis and continuity. Consequently their
square summability proves gains of the base operator itself.

The physical hypotheses are a Lipschitz curve, a Lipschitz bound for its
derivative, actual transport, and a nonzero cut vector. Constant speed and
an `IsBoundaryParam` witness are not needed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Real

private theorem corrected_gain_matrix_factor
    (W : ℝ → Ell2 →L[ℂ] Ell2) (δ s : ℝ) (m n : ℤ) :
    correctedRemainderMatrix W δ s (m, n) =
      ((sobWeight m ^ ((1 + 2 * s + 2 * δ) / 2) : ℝ) : ℂ) *
        ((sobWeight n ^ ((1 - 2 * s) / 2) : ℝ) : ℂ) *
        (2 * π : ℂ) *
        fourierCoeffOn two_pi_pos
          (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) (-n)) m := by
  simp only [correctedRemainderMatrix, sobWeight, Complex.ofReal_mul]
  push_cast
  ring

/-- The weights of the actual base matrix and the weighted matrix cancel
exactly. This includes the constant frequency, whose Sobolev weight is one. -/
theorem correctedRemainderMatrix_sobolev_weights
    (W : ℝ → Ell2 →L[ℂ] Ell2) (δ s : ℝ) (m n : ℤ) :
    ((sobWeight m ^ (-(s + δ)) : ℝ) : ℂ) *
        correctedRemainderMatrix W δ s (m, n) =
      correctedRemainderMatrix W 0 0 (m, n) *
        ((sobWeight n ^ (-s) : ℝ) : ℂ) := by
  have hm : sobWeight m ^ (-(s + δ)) *
      sobWeight m ^ ((1 + 2 * s + 2 * δ) / 2) =
        sobWeight m ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add (sobWeight_pos m)]
    congr 1
    ring
  have hn : sobWeight n ^ ((1 - 2 * s) / 2) =
      sobWeight n ^ (1 / 2 : ℝ) * sobWeight n ^ (-s) := by
    rw [← Real.rpow_add (sobWeight_pos n)]
    congr 1
    ring
  rw [corrected_gain_matrix_factor, corrected_gain_matrix_factor]
  simp only [mul_zero, add_zero, sub_zero]
  calc
    _ = (((sobWeight m ^ (-(s + δ)) : ℝ) : ℂ) *
          ((sobWeight m ^ ((1 + 2 * s + 2 * δ) / 2) : ℝ) : ℂ)) *
        ((sobWeight n ^ ((1 - 2 * s) / 2) : ℝ) : ℂ) *
        (2 * π : ℂ) *
        fourierCoeffOn two_pi_pos
          (fun θ => fourierCoeffOn two_pi_pos (correctedKernel W θ) (-n)) m := by ring
    _ = _ := by
      rw [← Complex.ofReal_mul, hm, hn, Complex.ofReal_mul]
      ring

private theorem corrected_gain_smoothing_stdBasis
    (s : ℝ) (hs : 0 ≤ s) (n : ℤ) :
    sobolevSmoothing s hs (stdBasisZ n) =
      ((sobWeight n ^ (-s) : ℝ) : ℂ) • stdBasisZ n := by
  ext m
  simp only [sobolevSmoothing, diagOp_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, stdBasisZ_apply, lp.single_apply]
  by_cases h : m = n
  · subst m
    simp
  · simp [h]

/-- The bounded Sobolev conjugation identity for the actual base operator.
The proof checks each Fourier basis vector and then extends by density. -/
theorem correctedRemainderOp_sobolev_conjugation
    (W : ℝ → Ell2 →L[ℂ] Ell2) {δ s : ℝ} (hs : 0 ≤ s)
    (hst : 0 ≤ s + δ)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    (hweighted : Summable fun p => ‖correctedRemainderMatrix W δ s p‖ ^ 2) :
    (hsMatrixOp (correctedRemainderMatrix W 0 0) hbase).comp
        (sobolevSmoothing s hs) =
      (sobolevSmoothing (s + δ) hst).comp
        (hsMatrixOp (correctedRemainderMatrix W δ s) hweighted) := by
  apply ContinuousLinearMap.ext_on
    ((Submodule.dense_iff_topologicalClosure_eq_top).2 stdBasisZ.dense_span)
  rintro _ ⟨n, rfl⟩
  apply lp.ext
  funext m
  simp only [ContinuousLinearMap.comp_apply]
  rw [corrected_gain_smoothing_stdBasis s hs n, map_smul]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    sobolevSmoothing, diagOp_apply, hsMatrixOp_stdBasisZ]
  simpa only [mul_comm] using
    (correctedRemainderMatrix_sobolev_weights W δ s m n).symm

private theorem corrected_gain_smoothing_sobVec
    (s : ℝ) (hs : 0 ≤ s) (f : L2Z)
    (hf : IsSobolevSeq s (f : ℤ → ℂ)) :
    sobolevSmoothing s hs (sobVec s (f : ℤ → ℂ) hf) = f := by
  ext n
  change fromL2 s (sobVec s (f : ℤ → ℂ) hf) n = f n
  exact congrFun (fromL2_sobVec s (f : ℤ → ℂ) hf) n

/-- Every `H^s` input to the actual base operator has `H^{s+δ}` output.
Square summability of the weighted matrix is used only to construct its
bounded conjugate; the output belongs to the original base operator. -/
theorem isSobolevSeq_correctedRemainderOp
    (W : ℝ → Ell2 →L[ℂ] Ell2) {δ s : ℝ} (hs : 0 ≤ s)
    (hst : 0 ≤ s + δ)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    (hweighted : Summable fun p => ‖correctedRemainderMatrix W δ s p‖ ^ 2)
    (f : L2Z) (hf : IsSobolevSeq s (f : ℤ → ℂ)) :
    IsSobolevSeq (s + δ)
      (hsMatrixOp (correctedRemainderMatrix W 0 0) hbase f : ℤ → ℂ) := by
  let F := sobVec s (f : ℤ → ℂ) hf
  let G := hsMatrixOp (correctedRemainderMatrix W δ s) hweighted F
  have heq : hsMatrixOp (correctedRemainderMatrix W 0 0) hbase f =
      sobolevSmoothing (s + δ) hst G := by
    rw [← corrected_gain_smoothing_sobVec s hs f hf]
    exact congrArg (fun T : L2Z →L[ℂ] L2Z => T F)
      (correctedRemainderOp_sobolev_conjugation W hs hst hbase hweighted)
  have hcoef :
      (hsMatrixOp (correctedRemainderMatrix W 0 0) hbase f : ℤ → ℂ) =
        fromL2 (s + δ) G := by
    rw [heq]
    rfl
  rw [hcoef]
  exact isSobolevSeq_fromL2 (s + δ) G

section PhysicalKernel

variable {γ : ℝ → ℂ} {K K' : NNReal} {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ)
    (hγ' : ∀ x ∈ Icc 0 (2 * π), ∀ y ∈ Icc 0 (2 * π),
      ‖deriv γ x - deriv γ y‖ ≤ K' * |x - y|)
    (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)

include hK hγ' hW hc

/-- The genuine Lipschitz-derivative estimates instantiate the full-input
gain of the actual corrected-kernel operator, without a constant-speed
boundary parametrization hypothesis. -/
theorem correctedRemainderOp_sobolev_gain
    {δ s : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2)
    (hs : 0 ≤ s) (hs' : s ≤ 1 / 2)
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    (f : L2Z) (hf : IsSobolevSeq s (f : ℤ → ℂ)) :
    IsSobolevSeq (s + δ)
      (hsMatrixOp (correctedRemainderMatrix W 0 0) hbase f : ℤ → ℂ) := by
  exact isSobolevSeq_correctedRemainderOp W hs (add_nonneg hs hδ) hbase
    (summable_correctedRemainderMatrix hK hγ' hW hc hδ hδ' hs hs') f hf

/-- First bootstrap step: the actual base operator maps every `L²` input
to `H^{1/4}`. -/
theorem correctedRemainderOp_gain_zero_quarter
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    (f : L2Z) :
    IsSobolevSeq (1 / 4 : ℝ)
      (hsMatrixOp (correctedRemainderMatrix W 0 0) hbase f : ℤ → ℂ) := by
  have hf : IsSobolevSeq 0 (f : ℤ → ℂ) := by
    simpa only [IsSobolevSeq, Real.rpow_zero, one_mul] using summable_norm_sq_L2Z f
  simpa only [zero_add] using
    correctedRemainderOp_sobolev_gain hK hγ' hW hc
      (δ := (1 / 4 : ℝ)) (s := 0) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hbase f hf

/-- Second bootstrap step: the same actual base operator sends `H^{1/4}`
inputs to `H^{1/2}`. -/
theorem correctedRemainderOp_gain_quarter_half
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    (f : L2Z) (hf : IsSobolevSeq (1 / 4 : ℝ) (f : ℤ → ℂ)) :
    IsSobolevSeq (1 / 2 : ℝ)
      (hsMatrixOp (correctedRemainderMatrix W 0 0) hbase f : ℤ → ℂ) := by
  simpa only [show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num] using
    correctedRemainderOp_sobolev_gain hK hγ' hW hc
      (δ := (1 / 4 : ℝ)) (s := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hbase f hf

/-- The two actual gains give the regularity conclusion used by the
two-step reduced-form bootstrap for a fixed point of this operator. -/
theorem correctedRemainderOp_fixed_point_half
    (hbase : Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2)
    (z : L2Z)
    (hfix : hsMatrixOp (correctedRemainderMatrix W 0 0) hbase z = z) :
    IsSobolevSeq (1 / 2 : ℝ) (z : ℤ → ℂ) := by
  have hz := correctedRemainderOp_gain_zero_quarter hK hγ' hW hc hbase z
  rw [hfix] at hz
  have hhalf := correctedRemainderOp_gain_quarter_half hK hγ' hW hc hbase z hz
  rwa [hfix] at hhalf

end PhysicalKernel

end PolyaNeumann

end
