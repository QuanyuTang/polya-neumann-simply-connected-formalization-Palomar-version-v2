module

public import RequestProject.LocalConformalNormalizedResidueBasis
public import RequestProject.HerglotzReparam
public import RequestProject.ObservationLp
public import RequestProject.PhysicalHardyWeights
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
The genuine transfer from the normalized periodic boundary estimate to
the original Herglotz direction densities. The weak load is
`b = sqrt(2π) Λ⁻¹ᐟ² ĝ`. Its form is the ordinary, unaveraged boundary
pairing, and `sqrt(2π) • projObsDual b` is the projected ordinary
observation. The paper vector is `sqrt(2π) • b`; only that vector has
the form factor `1 / (2π)`. The unprojected observation is used only on
the actual ordinary L2 conormal trace. The resulting statements are part of
the verified dependency chain.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann

open Set MeasureTheory Filter Metric Real
open scoped InnerProductSpace ComplexConjugate Topology

local notation "μB" => volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))

/-- The actual physical conormal L2 class is linear on direction densities. -/
def herglotzConormalBoundaryLin {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (k : ℝ) : dirDensities →ₗ[ℂ] BoundaryL2 where
  toFun a := herglotzConormalL2 hγ a.property k
  map_add' a b := by
    apply Lp.ext
    filter_upwards [herglotzConormalL2_ae hγ (a + b).property k,
      herglotzConormalL2_ae hγ a.property k, herglotzConormalL2_ae hγ b.property k,
      Lp.coeFn_add (herglotzConormalL2 hγ a.property k)
        (herglotzConormalL2 hγ b.property k)] with θ hab ha hb hs
    rw [hab, hs]
    simp only [Pi.add_apply, ha, hb]
    exact congrFun (herglotzConormal_add_density a.property b.property k γ) θ
  map_smul' c a := by
    apply Lp.ext
    filter_upwards [herglotzConormalL2_ae hγ (c • a).property k,
      herglotzConormalL2_ae hγ a.property k,
      Lp.coeFn_smul c (herglotzConormalL2 hγ a.property k)] with θ hca ha hs
    simp only [RingHom.id_apply]
    rw [hca, hs]
    simp only [Pi.smul_apply, ha, smul_eq_mul]
    exact congrFun (herglotzConormal_smul_density a.property c k γ) θ

/-- Genuine Jacobian transport of ordinary L2 loads as a linear map. -/
def traceReparamConormalLinearMap {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) : BoundaryL2 →ₗ[ℂ] BoundaryL2 where
  toFun := traceReparamConormalL2 hτ
  map_add' g h := by
    apply Lp.ext
    have hadd := isC1TraceReparam_ae_comp hτ (Lp.coeFn_add g h)
    filter_upwards [traceReparamConormalL2_ae hτ (g + h),
      traceReparamConormalL2_ae hτ g, traceReparamConormalL2_ae hτ h,
      Lp.coeFn_add (traceReparamConormalL2 hτ g) (traceReparamConormalL2 hτ h),
      hadd] with θ hab hg hh hs hc
    rw [hab, hs]
    simp only [Pi.add_apply, hg, hh, hc, smul_add]
  map_smul' a g := by
    apply Lp.ext
    have hsmul := isC1TraceReparam_ae_comp hτ (Lp.coeFn_smul a g)
    filter_upwards [traceReparamConormalL2_ae hτ (a • g),
      traceReparamConormalL2_ae hτ g,
      Lp.coeFn_smul a (traceReparamConormalL2 hτ g), hsmul] with θ hag hg hs hc
    simp only [RingHom.id_apply]
    rw [hag, hs]
    simp only [Pi.smul_apply, hg, hc]
    exact smul_comm (deriv τ θ) a (g (τ θ))

/-- The actual normalized weak-load map, with the physical Jacobian. -/
def localConformalBoundaryLoadLinearMap {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) : BoundaryL2 →ₗ[ℂ] L2Z :=
  (sobolevSmoothing (1 / 2 : ℝ) (by norm_num)).toLinearMap.comp
    (boundaryFourier.toLinearMap.comp (traceReparamConormalLinearMap hτ))

theorem localConformalBoundaryLoadLinearMap_apply {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (g : BoundaryL2) :
    localConformalBoundaryLoadLinearMap hτ g = localConformalBoundaryLoad hτ g := rfl

/-- Direction densities give the actual physical conormal followed by its
true Jacobian transport and its unitary Fourier normalization. -/
def localConformalHerglotzBoundaryLin {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (k : ℝ) : dirDensities →ₗ[ℂ] L2Z :=
  (localConformalBoundaryLoadLinearMap hτ).comp (herglotzConormalBoundaryLin hγ k)

theorem localConformalHerglotzBoundaryLin_apply {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (k : ℝ) (a : dirDensities) :
    localConformalHerglotzBoundaryLin hγ hτ k a =
      localConformalBoundaryLoad hτ (herglotzConormalL2 hγ a.property k) := rfl

/-- Extension to arbitrary direction functions does not change any
condition on the genuine density subspace. -/
theorem exists_localConformalHerglotz_density_conditions {Ω : Set ℂ}
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {τ : ℝ → ℝ} {c : ℝ}
    (hτ : IsC1TraceReparam τ c) (k : ℝ) {m : ℕ}
    (ℓ : L2Z →ₗ[ℂ] (Fin m → ℂ)) :
    ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a (ha : IsDirDensity a),
      L a = ℓ (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha k)) := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend
    (ℓ.comp (localConformalHerglotzBoundaryLin hγ hτ k))
  refine ⟨L, fun a ha => ?_⟩
  exact congrArg (fun T => T ⟨a, ha⟩) hL

/-- The actual bounded cut correction has one uniform norm bound near
a nonzero cut, derived from the genuine energy-dependent transport. -/
theorem exists_herglotzCut_uniform_bound {δ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K δ) (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2)
    (hWs : ∀ E, IsTransport δ E (Ws E)) (E₀ : ℝ)
    (hc : cutC (Ws E₀ (2 * Real.pi)) (basisVec 0) ≠ 0) :
    ∃ B ρ : ℝ, 0 < B ∧ 0 < ρ ∧ ∀ E, |E - E₀| < ρ →
      cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0 ∧ ‖cutBE (Ws E)‖ ≤ B := by
  have hB : ∀ᶠ E in 𝓝 E₀, ‖cutBE (Ws E)‖ ≤ ‖cutBE (Ws E₀)‖ + 1 :=
    ((tendsto_cutBE_energy hK hWs E₀ hc).norm.eventually
      (gt_mem_nhds (by linarith : ‖cutBE (Ws E₀)‖ < ‖cutBE (Ws E₀)‖ + 1))).mono
        fun _ h => h.le
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp
    ((eventually_cutC_ne hK hWs E₀ hc).and hB)
  refine ⟨‖cutBE (Ws E₀)‖ + 1, ρ, by positivity, hρ, fun E hE => ?_⟩
  exact hsub (mem_ball.mpr (by simpa only [Real.dist_eq] using hE))

section Coordinates

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
local notation "ΓF" => physicalCircleTrace F
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL

include hγ hτ hcoord in
/-- A genuine Lipschitz bound for the actual coordinate curve follows
from the supplied physical boundary and its actual reparametrization. -/
theorem localConformalHerglotzCoordinate_exists_lipschitz :
    ∃ L : NNReal, LipschitzWith L ΓF := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨Kτ, hKτ⟩ := hτ.lipschitz
  refine ⟨Kγ * Kτ, ?_⟩
  have hΓ : ΓF = γ ∘ τ := by funext θ; exact hcoord θ
  rw [hΓ]
  exact hKγ.comp hKτ

private theorem herglotz_transfer_observationAdj_congr_ae
    (W : ℝ → Ell2 →L[ℂ] Ell2) {g h : ℝ → ℂ} (he : g =ᵐ[μB] h) :
    observationAdj W g = observationAdj W h := by
  rw [observationAdj, observationAdj,
    intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  apply integral_congr_ae
  filter_upwards [he] with θ hθ
  rw [hθ]

include hcoord in
/-- The unitary weak-load scale of the projected observation. The
unprojected integral is evaluated only on the true conormal density. -/
theorem localConformalHerglotzBoundary_projObsDual
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    (Real.sqrt (2 * Real.pi) : ℂ) • projObsDual W
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
      cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
        (observationAdj W (herglotzConormal (Real.sqrt E) a ΓF)) := by
  rw [localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord hΓLip ha]
  rw [← map_smul]
  have h := projObsDual_boundary_normalized hΓLip hW
    (localConformalHerglotzCoordinateLoad F hΓLip ha (Real.sqrt E))
  rw [herglotz_transfer_observationAdj_congr_ae W
    (localConformalHerglotzCoordinateLoad_ae F hΓLip ha (Real.sqrt E))] at h
  exact h

include hcoord in
theorem localConformalHerglotzBoundary_projObsDual_norm_sq
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    (2 * Real.pi) * ‖projObsDual W
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))‖ ^ 2 =
      ‖cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
        (observationAdj W (herglotzConormal (Real.sqrt E) a ΓF))‖ ^ 2 := by
  have hn := congrArg (fun v : Ell2 => ‖v‖ ^ 2)
    (localConformalHerglotzBoundary_projObsDual F hγ hτ hcoord hΓLip hW ha)
  simpa only [norm_smul, Complex.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt Real.two_pi_pos.le] using hn

include hcoord in
/-- The paper vector has the unscaled projected ordinary observation. -/
theorem localConformalHerglotzBoundary_paper_projObsDual
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    projObsDual W ((Real.sqrt (2 * Real.pi) : ℂ) •
        localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
      cutProj (cutC (W (2 * Real.pi)) (basisVec 0))
        (observationAdj W (herglotzConormal (Real.sqrt E) a ΓF)) := by
  rw [map_smul]
  exact localConformalHerglotzBoundary_projObsDual F hγ hτ hcoord hΓLip hW ha

include hcoord in
/-- Exact equality to the physical Fourier construction with coefficients
2π Λ⁻¹ᐟ² ĝ, including frequency zero. -/
theorem physicalHerglotzConormalVec_eq_scaled_weakLoad
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (k : ℝ) (a : dirDensities) :
    physicalHerglotzConormalVec hΓLip k a = (Real.sqrt (2 * Real.pi) : ℂ) •
      localConformalBoundaryLoad hτ (herglotzConormalL2 hγ a.property k) := by
  apply lp.ext
  funext n
  rw [physicalHerglotzConormalVec_apply,
    localConformalHerglotzBoundaryLoad_eq_coordinateLoad F hγ hτ hcoord hΓLip a.property]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, sobolevSmoothing, diagOp_apply]
  rw [boundaryFourier_apply, sobWeight_rpow_neg_half, Complex.ofReal_inv,
    congrFun (fourierCoeffOn_congr_ae Real.two_pi_pos
      (localConformalHerglotzCoordinateLoad_ae F hΓLip a.property k)) n]
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) := by exact_mod_cast Real.mul_self_sqrt Real.two_pi_pos.le
  simp only [div_eq_mul_inv]
  calc
    _ = (((2 * Real.pi : ℝ) : ℂ) * (Real.sqrt (1 + |(n : ℝ)|) : ℂ)⁻¹) *
        fourierCoeffOn Real.two_pi_pos (herglotzConormal k a.1 ΓF) n := by
      push_cast
      ring
    _ = _ := by rw [← hs]; ring

include hR hFs in
private theorem herglotz_transfer_kernel_summable
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport ΓF E W)
    (hc : cutC (W (2 * Real.pi)) (basisVec 0) ≠ 0) :
    Summable fun p => ‖correctedRemainderMatrix W 0 0 p‖ ^ 2 := by
  have hΓ4 := contDiff_physicalCircleTrace_four_of_neighborhood hR F
    (hFs.of_le (WithTop.coe_le_coe.mpr le_top))
  have hΓ2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) ΓF := hΓ4.of_le (by norm_num)
  obtain ⟨B, hB⟩ := hΓ2.deriv'.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_Icc 0 (2 * Real.pi)) isCompact_Icc
  have hdiff : ∀ x ∈ Icc 0 (2 * Real.pi), ∀ y ∈ Icc 0 (2 * Real.pi),
      ‖deriv ΓF x - deriv ΓF y‖ ≤ B * |x - y| := by
    intro x hx y hy
    have h := hB.dist_le_mul x hx y hy
    rwa [dist_eq_norm, Real.dist_eq] at h
  exact summable_correctedRemainderMatrix hΓLip hdiff hW hc
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

include hb hhol hinj hC hcoord in
/-- The actual full family on a Herglotz load is its true corrected
observation adjoint. Nonresonance removes precisely the genuine form
kernel, rather than suppressing the constant Fourier mode. -/
theorem normalizedPeriodicBoundaryFamily_herglotz_eq
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    normalizedPeriodicBoundaryFamily QF Ws E
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))) =
      (Real.sqrt (2 * Real.pi) : ℂ) • ContinuousLinearMap.adjoint (projObsDual (Ws E))
        (regularHerglotzObservationVector (γ := ΓF) E (Ws E) ha) := by
  have hunit := h1HelmholtzForm_isUnit hb hL hE hnr
  have hbase := herglotz_transfer_kernel_summable hR F hFs hΓLip hW hc
  rw [normalizedPeriodicBoundaryFamily_eq_regular_at_nonresonant_reference QF hb hL Ws hE hunit,
    normalizedPeriodicRegularFamily_eq QF E E Ws hbase]
  rw [normalizedPeriodicRegularOperator_herglotz_eq hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord hΓLip hE hW hc ha hbase,
    h1Resonant_starProjection_eq_zero_of_form_isUnit hunit, map_zero, smul_zero, sub_zero]

private theorem herglotz_transfer_periodic_inner
    {δ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K δ)
    (hclosed : δ (2 * Real.pi) = δ 0) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport δ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    l2Inner (herglotzConormal (Real.sqrt E) a δ)
      (periodicP W (fun θ => herglotzWave (Real.sqrt E) a (δ θ))
        (herglotzConormal (Real.sqrt E) a δ)) =
      ⟪observationAdj W (herglotzConormal (Real.sqrt E) a δ),
        regularHerglotzObservationVector (γ := δ) E W ha⟫_ℂ := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  rw [inner_observationAdj hW.1 hgm hgB]
  unfold l2Inner
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le Real.two_pi_pos.le] at hθ
  change conj (herglotzConormal (Real.sqrt E) a δ θ) *
      periodicP W (fun s => herglotzWave (Real.sqrt E) a (δ s))
        (herglotzConormal (Real.sqrt E) a δ) θ =
    conj (herglotzConormal (Real.sqrt E) a δ θ) *
      observation W (regularHerglotzObservationVector (γ := δ) E W ha) θ
  rw [periodicP_herglotz_eq_regularObservation hK hclosed hW ha hθ]

include hb hhol hinj hC hcoord in
/-- The exact complex ordinary-boundary pairing equals the full
normalized pairing for the unitary weak load, with no factor 2π. -/
theorem normalizedPeriodicBoundaryFamily_herglotz_inner
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))
    ⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ =
      l2Inner (herglotzConormal (Real.sqrt E) a ΓF)
        (periodicP (Ws E) (fun θ => herglotzWave (Real.sqrt E) a (ΓF θ))
          (herglotzConormal (Real.sqrt E) a ΓF)) := by
  dsimp only
  rw [normalizedPeriodicBoundaryFamily_herglotz_eq hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord Ws hE hnr hΓLip hW hc ha,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right]
  have hclosed : ΓF (2 * Real.pi) = ΓF 0 := by
    simpa only [zero_add] using physicalCircleTrace_periodic F 0
  have hz := regularHerglotzObservationVector_cutProj hΓLip hclosed hW hc ha
  have hobs := localConformalHerglotzBoundary_projObsDual F hγ hτ hcoord hΓLip hW ha
  calc
    _ = ⟪(Real.sqrt (2 * Real.pi) : ℂ) • projObsDual (Ws E)
        (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))),
          regularHerglotzObservationVector (γ := ΓF) E (Ws E) ha⟫_ℂ := by
      rw [inner_smul_left, Complex.conj_ofReal]
    _ = ⟪observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF),
        regularHerglotzObservationVector (γ := ΓF) E (Ws E) ha⟫_ℂ := by
      rw [hobs, inner_cutProj_left, hz]
    _ = _ := (herglotz_transfer_periodic_inner hΓLip hclosed hW ha).symm

include hb hhol hinj hC hcoord in
/-- The true unitary normalization of the original Herglotz form. -/
theorem localConformalHerglotzForm_eq_normalizedBoundary
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))
    let O := observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)
    herglotzForm (Ws E) ΓF E a =
      (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re -
        (⟪O, cutBE (Ws E) O⟫_ℂ).re := by
  dsimp only
  rw [herglotzForm_eq_periodicP_sub_cutBE hΓLip
    (by simpa only [zero_add] using physicalCircleTrace_periodic F 0) hW ha,
    normalizedPeriodicBoundaryFamily_herglotz_inner hR F hFs hb hL hhol hinj hC
      hγ hτ hcoord Ws hE hnr hΓLip hW hc ha]

private theorem herglotz_transfer_pair_sqrt_scale (P : L2Z →L[ℂ] L2Z) (b : L2Z) :
    (⟪(Real.sqrt (2 * Real.pi) : ℂ) • b,
      P ((Real.sqrt (2 * Real.pi) : ℂ) • b)⟫_ℂ).re =
        (2 * Real.pi) * (⟪b, P b⟫_ℂ).re := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) := by exact_mod_cast Real.mul_self_sqrt Real.two_pi_pos.le
  rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    ← mul_assoc, hs]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

include hb hhol hinj hC hcoord in
/-- For the paper vector v = 2π Λ⁻¹ᐟ² ĝ the factor 1/(2π) is actual. -/
theorem localConformalHerglotzForm_eq_paperNormalizedBoundary
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    let v := (Real.sqrt (2 * Real.pi) : ℂ) •
      localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E))
    let O := observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)
    herglotzForm (Ws E) ΓF E a =
      (1 / (2 * Real.pi)) * (⟪v, normalizedPeriodicBoundaryFamily QF Ws E v⟫_ℂ).re -
        (⟪O, cutBE (Ws E) O⟫_ℂ).re := by
  dsimp only
  rw [localConformalHerglotzForm_eq_normalizedBoundary hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord Ws hE hnr hΓLip hW hc ha, herglotz_transfer_pair_sqrt_scale]
  congr 1
  field_simp [Real.two_pi_pos.ne']

include hb hhol hinj hC hcoord in
/-- The sharp normalization in the fixed-energy transfer is A0/(2π).
The remaining correction is the norm of the actual bounded cut operator. -/
theorem localConformalHerglotzForm_lower_of_normalizedBoundary
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hbound : let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E));
      -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
        (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    -((A₀ / (2 * Real.pi) + ‖cutBE (Ws E)‖) *
      ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)‖ ^ 2) ≤
        herglotzForm (Ws E) ΓF E a := by
  dsimp only at hbound
  have hn := localConformalHerglotzBoundary_projObsDual_norm_sq F hγ hτ hcoord hΓLip hW ha
  have hn' : ‖projObsDual (Ws E)
      (localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E)))‖ ^ 2 =
      ‖cutProj (cutC (Ws E (2 * Real.pi)) (basisVec 0))
        (observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF))‖ ^ 2 /
          (2 * Real.pi) := by
    apply (eq_div_iff Real.two_pi_pos.ne').mpr
    simpa only [mul_comm] using hn
  rw [hn', normalizedPeriodicBoundaryFamily_herglotz_inner hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord Ws hE hnr hΓLip hW hc ha] at hbound
  apply herglotzForm_lower_of_periodicP_lower hΓLip
    (by simpa only [zero_add] using physicalCircleTrace_periodic F 0) hW ha
    (div_nonneg hA₀ Real.two_pi_pos.le)
  convert hbound using 1; ring

include hb hhol hinj hC hcoord in
theorem localConformalHerglotzForm_lower_of_normalizedBoundary_boundedCut
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) {A₀ B : ℝ} (hA₀ : 0 ≤ A₀)
    (hB : ‖cutBE (Ws E)‖ ≤ B)
    (hbound : let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E));
      -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
        (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    -((A₀ / (2 * Real.pi) + B) *
      ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)‖ ^ 2) ≤
        herglotzForm (Ws E) ΓF E a := by
  have h := localConformalHerglotzForm_lower_of_normalizedBoundary hR F hFs hb hL hhol
    hinj hC hγ hτ hcoord Ws hE hnr hΓLip hW hc ha hA₀ hbound
  have hm := mul_le_mul_of_nonneg_right hB (sq_nonneg
    ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)‖)
  nlinarith

include hb hhol hinj hC hcoord in
theorem localConformalHerglotzForm_lower_conservative
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {L : NNReal} (hΓLip : LipschitzWith L ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {a : ℝ → ℂ} (ha : IsDirDensity a) {A₀ B : ℝ} (hA₀ : 0 ≤ A₀)
    (hB : ‖cutBE (Ws E)‖ ≤ B)
    (hbound : let b := localConformalBoundaryLoad hτ (herglotzConormalL2 hγ ha (Real.sqrt E));
      -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
        (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    -((A₀ + B) * ‖observationAdj (Ws E)
      (herglotzConormal (Real.sqrt E) a ΓF)‖ ^ 2) ≤ herglotzForm (Ws E) ΓF E a := by
  have h := localConformalHerglotzForm_lower_of_normalizedBoundary_boundedCut hR F hFs hb hL
    hhol hinj hC hγ hτ hcoord Ws hE hnr hΓLip hW hc ha hA₀ hB hbound
  have hT : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hdiv : A₀ / (2 * Real.pi) ≤ A₀ := by
    apply (div_le_iff₀ Real.two_pi_pos).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hT hA₀
  have hm := mul_le_mul_of_nonneg_right hdiv (sq_nonneg
    ‖observationAdj (Ws E) (herglotzConormal (Real.sqrt E) a ΓF)‖)
  nlinarith

include hb hhol hinj hC hγ hτ hcoord in
/-- The number of direction conditions is exactly the given number of
normalized conditions. Instantiating it with originalNeumannMultiplicity
therefore retains the original complex spectral multiplicity. -/
theorem exists_localConformalHerglotz_boundary_conditions
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {KΓ : NNReal} (hΓLip : LipschitzWith KΓ ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {A₀ B : ℝ} (hA₀ : 0 ≤ A₀) (hB : ‖cutBE (Ws E)‖ ≤ B) {m : ℕ}
    (ℓ : L2Z →ₗ[ℂ] (Fin m → ℂ))
    (hbound : ∀ b : L2Z, ℓ b = 0 → -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
      (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → L a = 0 →
      -((A₀ / (2 * Real.pi) + B) * ‖observationAdj (Ws E)
        (herglotzConormal (Real.sqrt E) a ΓF)‖ ^ 2) ≤ herglotzForm (Ws E) ΓF E a := by
  obtain ⟨L, hconditions⟩ := exists_localConformalHerglotz_density_conditions hγ hτ (Real.sqrt E) ℓ
  refine ⟨L, fun a ha hLa => ?_⟩
  apply localConformalHerglotzForm_lower_of_normalizedBoundary_boundedCut hR F hFs hb hL
    hhol hinj hC hγ hτ hcoord Ws hE hnr hΓLip hW hc ha hA₀ hB
  apply hbound
  exact (hconditions a ha).symm.trans hLa

include hb hhol hinj hC hγ hτ hcoord in
/-- The same actual conditions give the original arclength-boundary
estimate when the proved reparametrization fixes the integration endpoints. -/
theorem exists_originalHerglotz_boundary_conditions_of_normalized
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) {E : ℝ} (hE : 0 ≤ E)
    (hnr : ∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E)
    {KΓ : NNReal} (hΓLip : LipschitzWith KΓ ΓF) (hW : IsTransport ΓF E (Ws E))
    (hc : cutC (Ws E (2 * Real.pi)) (basisVec 0) ≠ 0)
    {Wγ : ℝ → Ell2 →L[ℂ] Ell2} (hWγ : IsTransport γ E Wγ)
    {A₀ B : ℝ} (hA₀ : 0 ≤ A₀) (hB : ‖cutBE (Ws E)‖ ≤ B) {m : ℕ}
    (ℓ : L2Z →ₗ[ℂ] (Fin m → ℂ))
    (hbound : ∀ b : L2Z, ℓ b = 0 → -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
      (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ a, IsDirDensity a → L a = 0 →
      -((A₀ / (2 * Real.pi) + B) * ‖observationAdj Wγ
        (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤ herglotzForm Wγ γ E a := by
  obtain ⟨L, hconditions⟩ := exists_localConformalHerglotz_boundary_conditions hR F hFs hb hL
    hhol hinj hC hγ hτ hcoord Ws hE hnr hΓLip hW hc hA₀ hB ℓ hbound
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨Kτ, hKτ⟩ := hτ.lipschitz
  have hΓ : ΓF = γ ∘ τ := by funext θ; exact hcoord θ
  have hWcomp : IsTransport (γ ∘ τ) E (Ws E) := by rw [← hΓ]; exact hW
  refine ⟨L, ?_⟩
  apply herglotz_density_lower_bound_of_comp hKγ
    (by simpa only [zero_add] using hγ.periodic 0) hτ.monotone hKτ
    hτ.zero hτ.endpoint hWγ hWcomp L
  rw [← hΓ]
  exact hconditions

include hb hhol hinj hC hγ hτ hcoord in
/-- The genuine normalized estimate transfers uniformly to the original
boundary with exactly the original complex multiplicity. Its constant
is A0/(2π) plus a derived uniform cut norm. No form identification or
unprojected observation on rough normalized data is a premise. -/
theorem exists_uniform_originalHerglotz_bound_of_normalized
    {KΓ : NNReal} (hΓLip : LipschitzWith KΓ ΓF)
    (Ws : ℝ → ℝ → Ell2 →L[ℂ] Ell2) (hWs : ∀ E, IsTransport ΓF E (Ws E))
    (E₀ : ℝ) (hc : cutC (Ws E₀ (2 * Real.pi)) (basisVec 0) ≠ 0)
    (hbound : ∃ A₀ δ₀ : ℝ, 0 < A₀ ∧ 0 < δ₀ ∧ ∀ E, 0 < E → |E - E₀| < δ₀ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∃ ℓ : L2Z →ₗ[ℂ] (Fin (originalNeumannMultiplicity ΩF E₀) → ℂ),
        ∀ b : L2Z, ℓ b = 0 → -(A₀ * ‖projObsDual (Ws E) b‖ ^ 2) ≤
          (⟪b, normalizedPeriodicBoundaryFamily QF Ws E b⟫_ℂ).re) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∀ E, 0 < E → |E - E₀| < δ →
      (∀ j, neumannEigenvalue ΩF j ≠ ENNReal.ofReal E) →
      ∀ Wγ : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E Wγ →
        ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin (originalNeumannMultiplicity ΩF E₀) → ℂ),
          ∀ a, IsDirDensity a → L a = 0 →
            -(A * ‖observationAdj Wγ (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
              herglotzForm Wγ γ E a := by
  obtain ⟨A₀, δ₀, hA₀, hδ₀, hnormalized⟩ := hbound
  obtain ⟨B, ρ, hB, hρ, hcutBound⟩ := exists_herglotzCut_uniform_bound hΓLip Ws hWs E₀ hc
  refine ⟨A₀ / (2 * Real.pi) + B, min δ₀ ρ,
    add_pos (div_pos hA₀ Real.two_pi_pos) hB, lt_min hδ₀ hρ, ?_⟩
  intro E hE hnear hnr Wγ hWγ
  have hnear₀ := lt_of_lt_of_le hnear (min_le_left δ₀ ρ)
  have hnearρ := lt_of_lt_of_le hnear (min_le_right δ₀ ρ)
  obtain ⟨hcE, hBE⟩ := hcutBound E hnearρ
  obtain ⟨ℓ, hℓ⟩ := hnormalized E hE hnear₀ hnr
  exact exists_originalHerglotz_boundary_conditions_of_normalized hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord Ws hE.le hnr hΓLip (hWs E) hcE hWγ hA₀.le hBE ℓ hℓ

end Coordinates
end PolyaNeumann
end
