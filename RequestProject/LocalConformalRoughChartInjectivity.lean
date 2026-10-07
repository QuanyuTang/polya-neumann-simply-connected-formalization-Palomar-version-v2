module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import RequestProject.RoughVekuaTransport
public import RequestProject.LocalConformalRoughHardySupport
public import RequestProject.LocalConformalReducedCoercivity
public import RequestProject.LocalConformalFourierComplement
public import RequestProject.LocalConformalRoughGaugeRegularity

/-!
# Actual rough observation kernels in finite Fourier conormal charts

A genuine Hardy gauge differs from the negative imaginary multiple of
the rough periodic primitive by an actual H1 correction. The positive
primitive therefore has H1 Fourier coefficients. Finite Fourier chart
corrections then give half-order regularity of the full normalized load,
which permits the true L2 conormal realization and chart injectivity.

The final supplied-coordinate wrappers use the constructed rough driven
gauge; they do not assume regularity or Hardy support of the unknown
normalized load.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ComplexConjugate

local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
local notation "H₀" => nonpositiveFourierSubspace

private theorem rough_chart_posProj_eq_zero_of_nonpositive (b : L2Z)
    (hb : IsNonpositiveFourierSupport (b : ℤ → ℂ)) : posProj b = 0 := by
  apply lp.ext
  funext n
  by_cases hn : 0 < n
  · simp only [posProj, diagOp_apply, if_pos hn, hb n hn, mul_zero,
      lp.coeFn_zero, Pi.zero_apply]
  · simp only [posProj, diagOp_apply, if_neg hn, zero_mul,
      lp.coeFn_zero, Pi.zero_apply]

/-- A true L2 Hardy split controls the positive rough primitive. This
This lemma concerns actual boundary vectors and uses no endpoint value. -/
theorem roughNormalizedPrimitive_pos_one_of_hardy_split
    (y : L2Z) (H K : BoundaryL2)
    (hH : IsNonpositiveFourierSupport (boundaryFourier H : ℤ → ℂ))
    (hK : IsSobolevSeq 1 (boundaryFourier K : ℤ → ℂ))
    (hsplit : H = -Complex.I • roughNormalizedPrimitive y + K) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  let p : L2Z := posProj (boundaryFourier (roughNormalizedPrimitive y))
  let k : L2Z := posProj (boundaryFourier K)
  have hzero := rough_chart_posProj_eq_zero_of_nonpositive (boundaryFourier H) hH
  have hs := congrArg (fun B : BoundaryL2 => posProj (boundaryFourier B)) hsplit
  change posProj (boundaryFourier H) =
    posProj (boundaryFourier (-Complex.I • roughNormalizedPrimitive y + K)) at hs
  rw [hzero, map_add, map_smul, map_add, map_smul] at hs
  change (0 : L2Z) = -Complex.I • p + k at hs
  have hi := congrArg (fun B : L2Z => Complex.I • B) hs
  simp only [smul_zero, smul_add, smul_smul, mul_neg,
    Complex.I_mul_I, neg_neg, one_smul] at hi
  have hp : p = -Complex.I • k := by
    have h := eq_neg_of_add_eq_zero_left hi.symm
    simpa only [neg_smul] using h
  change p ∈ fourierSobolevSubmodule 1
  rw [hp]
  exact (fourierSobolevSubmodule 1).smul_mem _ (isSobolevSeq_posProj hK)

theorem roughNormalizedPrimitive_pos_one_of_hardy_split_ae
    (y : L2Z) (H K : BoundaryL2)
    (hH : IsNonpositiveFourierSupport (boundaryFourier H : ℤ → ℂ))
    (hK : IsSobolevSeq 1 (boundaryFourier K : ℤ → ℂ))
    (hsplit : (H : ℝ → ℂ) =ᵐ[μB]
      (fun θ => -Complex.I * roughNormalizedPrimitive y θ + K θ)) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  apply roughNormalizedPrimitive_pos_one_of_hardy_split y H K hH hK
  apply Lp.ext
  filter_upwards [hsplit, Lp.coeFn_add (-Complex.I • roughNormalizedPrimitive y) K,
    Lp.coeFn_smul (-Complex.I) (roughNormalizedPrimitive y)] with θ hs ha hm
  simpa only [ha, hm, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hs

/-- Raw H1 correction coefficients give the actual unitary Fourier H1
vector; the ordinary-measure sqrt(2pi) normalization is retained. -/
theorem boundaryFourier_toLp_sobolev_one_of_coefficients
    {K : ℝ → ℂ} (hK : MemLp K 2 μB)
    (hK1 : IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos K)) :
    IsSobolevSeq 1 (boundaryFourier (hK.toLp K) : ℤ → ℂ) := by
  have heq : (boundaryFourier (hK.toLp K) : ℤ → ℂ) =
      (Real.sqrt (2 * Real.pi) : ℂ) • fourierCoeffOn Real.two_pi_pos K := by
    funext n
    rw [boundaryFourier_apply,
      fourierCoeffOn_congr_ae Real.two_pi_pos hK.coeFn_toLp]
    rfl
  rw [heq]
  exact isSobolevSeq_smul _ hK1

/-- Actual raw L2 gauges and corrections can be passed to the boundary
vector split without introducing pointwise periodicity of the gauge. -/
theorem roughNormalizedPrimitive_pos_one_of_raw_hardy_split
    (y : L2Z) (H K : ℝ → ℂ) (hH2 : MemLp H 2 μB) (hK2 : MemLp K 2 μB)
    (hH : IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos H))
    (hK1 : IsSobolevSeq 1 (fourierCoeffOn Real.two_pi_pos K))
    (hsplit : H =ᵐ[μB] fun θ => -Complex.I * roughNormalizedPrimitive y θ + K θ) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  have hHB : IsNonpositiveFourierSupport (boundaryFourier (hH2.toLp H) : ℤ → ℂ) := by
    intro n hn
    rw [boundaryFourier_apply, fourierCoeffOn_congr_ae Real.two_pi_pos hH2.coeFn_toLp,
      hH n hn, mul_zero]
  apply roughNormalizedPrimitive_pos_one_of_hardy_split_ae y (hH2.toLp H) (hK2.toLp K)
    hHB (boundaryFourier_toLp_sobolev_one_of_coefficients hK2 hK1)
  filter_upwards [hH2.coeFn_toLp, hK2.coeFn_toLp, hsplit] with θ hh hk hs
  rw [hh, hk]
  exact hs

section PhysicalCoordinates

variable {R C K : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (Metric.ball (0 : ℂ) R))
    (hb : Bornology.IsBounded (F '' Metric.ball (0 : ℂ) 1))
    (hL : IsLipschitzDomain (F '' Metric.ball (0 : ℂ) 1))
    (hhol : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1))
    (hinj : InjOn F (Metric.ball (0 : ℂ) 1))
    (hC : ∀ z ∈ Metric.ball (0 : ℂ) 1, 1 ≤ C * ‖deriv F z‖ ^ 2)
    (hK : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖fderiv ℝ F z 1‖ ≤ K)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = F)
    (hsource : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hes : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)

local notation "ΓF" => physicalCircleTrace F
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs
local notation "NF" => normalizedConormal hβF haF hgF

include hR hFs hb hL hhol e he hsource hes in
/-- The genuine rough driven gauge is Hardy for every normalized
observation-kernel input. The moments come from the actual positive-row
ODE and factorial tails, and the Hardy conclusion uses the true L2
physical moment criterion. -/
theorem localConformal_roughGauge_exists_nonpositive_of_projObsDual_eq_zero
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (y : L2Z) (hy : projObsDual W y = 0) :
    ∃ α : ℂ,
      roughVekuaRegularCorrection ΓF E W (roughNormalizedPrimitive y) (roughNormalizedMean y)
        α (2 * Real.pi) = α • basisVec 0 ∧
      MemLp (physicalDrivenGauge ΓF E
        (roughVekuaDrivenVector ΓF E W (roughNormalizedPrimitive y) (roughNormalizedMean y) α) 0)
        2 μB ∧
      IsNonpositiveFourierSupport (fourierCoeffOn Real.two_pi_pos
        (physicalDrivenGauge ΓF E
          (roughVekuaDrivenVector ΓF E W (roughNormalizedPrimitive y) (roughNormalizedMean y) α) 0)) := by
  have hΓ : ContDiff ℝ 1 ΓF :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  obtain ⟨α, hα0, hαT⟩ :=
    roughVekuaRegularCorrection_exists_periodic_of_projObsDual_eq_zero hΓLip hΓ hW y hy
  have hH2 := roughVekuaGauge_zero_memLp hΓLip hΓ hW
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α
  refine ⟨α, hαT, hH2, ?_⟩
  apply localConformal_physicalMoments_nonpositive_of_memLp_of_smoothInverse
    hR F hFs hb hL hhol e he hsource hes _ hH2
  intro k
  have hm := roughVekuaGauge_physicalMoment_eq_zero hΓLip hΓ hW hE
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α hαT 0 k
  simpa only [physicalDrivenMoment, physicalDrivenCentered, map_sub, mul_assoc] using hm

include hR hFs hb hL hhol e he hsource hes in
/-- Original normalized observation nullity gives the positive primitive
H1 regularity. Every gauge and Sobolev fact used here is constructed from
the true rough driven equation. -/
theorem localConformal_roughProjectedObservation_primitive_pos_one
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (y : L2Z) (hy : projObsDual W y = 0) :
    IsSobolevSeq 1
      (posProj (boundaryFourier (roughNormalizedPrimitive y)) : ℤ → ℂ) := by
  have hΓ : ContDiff ℝ 1 ΓF :=
    contDiff_physicalCircleTrace_of_neighborhood hR F (hFs.of_le (by simp))
  obtain ⟨α, hαT, hH2, hHn⟩ :=
    localConformal_roughGauge_exists_nonpositive_of_projObsDual_eq_zero
      hR F hFs hb hL hhol e he hsource hes hΓLip hE hW y hy
  have hK2 := roughVekuaGauge_regular_memLp hΓLip hΓ hW
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α 0
  have hK1 := roughVekuaGauge_regular_isSobolevSeq_one hΓLip hΓ hW
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α hαT
  apply roughNormalizedPrimitive_pos_one_of_raw_hardy_split y _ _ hH2 hK2 hHn hK1
  exact Eventually.of_forall (roughVekuaGauge_zero_split
    (roughNormalizedPrimitive y) (roughNormalizedMean y) α)

include hR hFs hb hL hhol e he hsource hes in
/-- Finite Fourier chart outputs acquire genuine half-order regularity
from their original normalized observation-null equation. No Sobolev or
gauge premise is imposed on the unknown chart vector. -/
theorem localConformal_finiteFourierChart_projectedObservation_kernel_half_regular
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    {d : ℕ} (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (z : H₀ᗮ) (hobs : projObsDual W (finiteFourierChart u v z) = 0) :
    IsSobolevSeq (1 / 2 : ℝ) (finiteFourierChart u v z : ℤ → ℂ) ∧
      IsSobolevSeq (1 / 2 : ℝ) ((z : L2Z) : ℤ → ℂ) := by
  exact finiteFourierChart_half_of_rough_primitive_pos_one u v hv z
    (localConformal_roughProjectedObservation_primitive_pos_one
      hR F hFs hb hL hhol e he hsource hes hΓLip hE hW _ hobs)

include hR hFs hb hL hhol hinj hC hK e he hsource hes in
/-- The full normalized projected-observation kernel of an actual
invertible finite Fourier conormal chart is zero. The half-order step is
proved above, so the true L2 conormal realization applies. -/
theorem localConformal_finiteFourierChart_projectedObservation_kernel_eq_zero
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    {d : ℕ} (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (hunit : IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
      (finiteFourierChart u v) ∘L H₀ᗮ.orthogonalProjection))
    (z : H₀ᗮ) (hobs : projObsDual W (finiteFourierChart u v z) = 0) : z = 0 := by
  have hy := (localConformal_finiteFourierChart_projectedObservation_kernel_half_regular
    hR F hFs hb hL hhol e he hsource hes hΓLip hE hW u v hv z hobs).1
  exact localConformal_fixed_complement_half_regular_kernel_eq_zero
    hR F hFs hb hL hhol hinj hC hK e he hsource hes hΓLip hE hW
    (finiteFourierChart u v) hunit z hy hobs

include hR hFs hb hL hhol hinj hC hK e he hsource hes in
theorem localConformal_finiteFourierChart_projectedObservation_injective
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    {d : ℕ} (u : Fin d → H₀ᗮ) (v : Fin d → L2Z)
    (hv : ∀ r, (Function.support (v r : ℤ → ℂ)).Finite)
    (hunit : IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
      (finiteFourierChart u v) ∘L H₀ᗮ.orthogonalProjection)) :
    Function.Injective ((projObsDual W).comp (finiteFourierChart u v)) := by
  intro z z' heq
  have hz : projObsDual W (finiteFourierChart u v (z - z')) = 0 := by
    rw [map_sub, map_sub]
    change (projObsDual W).comp (finiteFourierChart u v) z -
      (projObsDual W).comp (finiteFourierChart u v) z' = 0
    rw [heq, sub_self]
  exact sub_eq_zero.mp
    (localConformal_finiteFourierChart_projectedObservation_kernel_eq_zero
      hR F hFs hb hL hhol hinj hC hK e he hsource hes hΓLip hE hW u v hv hunit (z - z') hz)

include hR hFs hb hL hhol hinj hC hK e he hsource hes in
/-- A genuine nonzero reference cut supplies an actual finite Fourier
complement with full normalized projected-observation injectivity. No
half-order hypothesis is added to its chart inputs. -/
theorem exists_localConformal_fixed_fourier_complement_projectedObservation_injective
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E₀ : ℝ} (hE₀ : 0 < E₀)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E₀ W)
    (hcut : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ (d : ℕ) (u : Fin d → H₀ᗮ) (v : Fin d → L2Z),
      (∀ r, (Function.support ((u r : L2Z) : ℤ → ℂ)).Finite) ∧
      (∀ r, (Function.support (v r : ℤ → ℂ)).Finite) ∧
      Function.Injective ((projObsDual W).comp (finiteFourierChart u v)) ∧
      ∃ U ∈ 𝓝 E₀,
        (∀ E ∈ U, IsUnit ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
          (finiteFourierChart u v) ∘L H₀ᗮ.orthogonalProjection)) ∧
        ContinuousOn (fun E : ℝ => Ring.inverse
          ((NF (E : ℂ)).comp (H₀).subtypeL ∘L (H₀).orthogonalProjection +
            (finiteFourierChart u v) ∘L H₀ᗮ.orthogonalProjection)) U := by
  obtain ⟨d, u, v, hu, hv, U, hU, hunit, hcont⟩ :=
    exists_localConformal_fixed_fourier_complement_of_cutC_ne_zero
      hR F hFs hb hL hhol hinj hC hK e he hsource hes hE₀.le hW hcut
  refine ⟨d, u, v, hu, hv, ?_, U, hU, hunit, hcont⟩
  exact localConformal_finiteFourierChart_projectedObservation_injective
    hR F hFs hb hL hhol hinj hC hK e he hsource hes hΓLip hE₀ hW u v hv
    (hunit E₀ (mem_of_mem_nhds hU))

end PhysicalCoordinates

end PolyaNeumann

end
