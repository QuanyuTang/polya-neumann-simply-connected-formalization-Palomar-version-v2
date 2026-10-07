module

public import RequestProject.LocalConformalVekuaConormal
public import RequestProject.LocalConformalVekuaTrace
public import RequestProject.DiskWeakModes

/-!
# Identification of the actual Vekua flux and the Fourier conormal remainder

The physical velocity multipliers are transported by the genuine arclength
Jacobian on dense smooth H¹ restrictions. Both sides are continuous trace
pairings, so the identity extends to actual H¹ vectors. The supplied H¹
inverse and actual harmonic disk tests separate the half-trace pairings.
Consequently the normalized physical flux is the half-smoothed unitary
Fourier transform of the actual coordinate flux. Its convergent trace
series is then exactly the existing conormal remainder operator.

The center is F(1); the averaged multiplier coefficients and ordinary
dθ Fourier normalization are retained. Existence of the supplied coordinates
is separate.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology InnerProductSpace ComplexConjugate

local instance conormalBridgeTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private theorem bridge_summable_coeff {s : ℝ} (hs : 0 ≤ s) {a : ℤ → ℂ}
    (ha : IsWL1 s a) : Summable a := by
  apply Summable.of_norm
  exact ha.of_nonneg_of_le (fun n => norm_nonneg _) (fun n =>
    le_mul_of_one_le_left (norm_nonneg _)
      (Real.one_le_rpow (one_le_sobWeight n) hs))

private theorem bridge_isWL1_mono {s t : ℝ} (hst : s ≤ t) {a : ℤ → ℂ}
    (ha : IsWL1 t a) : IsWL1 s a := by
  refine ha.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (Real.rpow_nonneg (sobWeight_pos n).le _) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) hst) (norm_nonneg _)

private theorem bridge_circle_coeff (A : C(AddCircle (2 * Real.pi), ℂ)) :
    fourierCoeff A = fourierCoeffOn Real.two_pi_pos
      (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) := by
  funext n
  have he : AddCircle.liftIoc (2 * Real.pi) 0
      (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) =
      (A : AddCircle (2 * Real.pi) → ℂ) := by
    funext q
    change A ((AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) :
      AddCircle (2 * Real.pi)) = A q
    have hrep : ((AddCircle.equivIoc (2 * Real.pi) 0 q : ℝ) :
        AddCircle (2 * Real.pi)) = q :=
      (AddCircle.equivIoc (2 * Real.pi) 0).symm_apply_apply q
    rw [hrep]
  have h := fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := 0)
    (fun θ : ℝ => A (θ : AddCircle (2 * Real.pi))) n
  simpa only [he, zero_add] using h

/-- The actual continuous nonconjugate angular velocity of F on the circle. -/
def localConformalVelocityCircle (F : ℂ → ℂ) : C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨fun q => conj (localConformalPrimitiveCircle F q),
    Complex.continuous_conj.comp (localConformalPrimitiveCircle F).continuous⟩

theorem localConformalVelocityCircle_apply {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) (θ : ℝ) :
    localConformalVelocityCircle F (θ : AddCircle (2 * Real.pi)) =
      deriv (physicalCircleTrace F) θ := by
  change conj (localConformalPrimitiveCircle F (θ : AddCircle (2 * Real.pi))) = _
  rw [localConformalPrimitiveCircle_apply hR F hFs, Complex.conj_conj]

theorem localConformalVelocityCircle_coeff {R : ℝ} (hR : 1 < R) (F : ℂ → ℂ)
    (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    fourierCoeff (localConformalVelocityCircle F) =
      fourierCoeffOn Real.two_pi_pos (deriv (physicalCircleTrace F)) := by
  rw [bridge_circle_coeff]
  congr 1
  exact funext (localConformalVelocityCircle_apply hR F hFs)

theorem localConformalVelocityCircle_isWL1_half {R : ℝ} (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ (⊤ : ℕ∞) F (ball (0 : ℂ) R)) :
    IsWL1 (1 / 2 : ℝ) (fourierCoeff (localConformalVelocityCircle F)) := by
  rw [localConformalVelocityCircle_coeff hR F hFs]
  exact bridge_isWL1_mono (by norm_num)
    (periodic_contDiff_four_fourier_weights
      (contDiff_physicalCircleTrace_four_of_neighborhood hR F
        (hFs.of_le (WithTop.coe_le_coe.mpr le_top)))
      (physicalCircleTrace_periodic F)).1

private def bridge_physicalVelocity {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (conjugated : Bool) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  let B : NNReal := Classical.choose hγ.lipschitz
  let hB : LipschitzWith B γ := Classical.choose_spec hγ.lipschitz
  lpBoundedMultiplier
    (fun θ => if conjugated then conj (deriv γ θ) else deriv γ θ)
    (by cases conjugated
        · simpa using (measurable_deriv γ).aestronglyMeasurable.restrict
        · simpa using (Complex.continuous_conj.comp_aestronglyMeasurable
            (measurable_deriv γ).aestronglyMeasurable).restrict)
    (Eventually.of_forall fun θ => by
      cases conjugated <;> simpa using
        (norm_deriv_le_of_lipschitz hB : ‖deriv γ θ‖ ≤ B))

private theorem bridge_physicalVelocity_ae {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (conjugated : Bool) (g : BoundaryL2) :
    (bridge_physicalVelocity hγ conjugated g : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))]
      fun θ => (if conjugated then conj (deriv γ θ) else deriv γ θ) * g θ :=
  lpBoundedMultiplier_ae _ _ _ g

private theorem bridge_half_pairing (q t b : L2Z)
    (hq : ∀ n, q n = (Real.sqrt (sobWeight n) : ℂ) * t n) :
    ⟪q, sobolevSmoothing (1 / 2 : ℝ) (by norm_num) b⟫_ℂ = ⟪t, b⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply', hq, sobolevSmoothing, diagOp_apply,
    map_mul, Complex.conj_ofReal]
  have hw : (Real.sqrt (sobWeight n) : ℂ) *
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Complex.ofReal_mul, sobWeight_rpow_mul_neg,
      Complex.ofReal_one]
  calc
    _ = ((Real.sqrt (sobWeight n) : ℂ) *
        ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) *
        (conj (t n) * b n) := by ring
    _ = _ := by rw [hw, one_mul]

section CoordinatePairing

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
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "TP" => h1BoundaryTrace hb hL hγ

include hR hFs hγ hτ hcoord in
private theorem bridge_velocity_jacobian (conjugated : Bool) :
    (fun θ : ℝ => if conjugated then
        localConformalPrimitiveCircle F (θ : AddCircle (2 * Real.pi)) else
        localConformalVelocityCircle F (θ : AddCircle (2 * Real.pi))) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))]
      fun θ => deriv τ θ •
        (if conjugated then conj (deriv γ (τ θ)) else deriv γ (τ θ)) := by
  obtain ⟨B, hB⟩ := hγ.lipschitz
  obtain ⟨D, hD⟩ := hτ.lipschitz
  have hchain := (ae_deriv_comp hB hτ.monotone hD).filter_mono
    (ae_restrict_le : ae (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) ≤ ae volume)
  have he : γ ∘ τ = physicalCircleTrace F := funext fun θ => (hcoord θ).symm
  rw [he] at hchain
  filter_upwards [hchain] with θ hθ
  cases conjugated <;> simp only [Bool.false_eq_true, ↓reduceIte,
    localConformalPrimitiveCircle_apply hR F hFs,
    localConformalVelocityCircle_apply hR F hFs, hθ,
    Complex.real_smul, map_mul, Complex.conj_ofReal]

include hhol hinj hC hτ hcoord in
/-- Actual velocity multiplication transforms with the real Jacobian. The
two trace inputs are extended separately from smooth H¹ restrictions. -/
private theorem bridge_velocity_pairing (conjugated : Bool)
    (w u : NeumannH1 ΩF) :
    ⟪TP w, bridge_physicalVelocity hγ conjugated (TP u)⟫_ℂ =
      ⟪TF w, boundaryContinuousMultiplier
        (if conjugated then localConformalPrimitiveCircle F else
          localConformalVelocityCircle F) (TF u)⟫_ℂ := by
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on
    (p := fun v => ⟪TP v, bridge_physicalVelocity hγ conjugated (TP u)⟫_ℂ =
      ⟪TF v, boundaryContinuousMultiplier
        (if conjugated then localConformalPrimitiveCircle F else
          localConformalVelocityCircle F) (TF u)⟫_ℂ) w ?_ ?_
  · exact isClosed_eq ((TP).continuous.inner continuous_const)
      ((TF).continuous.inner continuous_const)
  · intro f
    refine (denseRange_smoothTraceH1Lin hb hL).induction_on
      (p := fun v => ⟪TP (smoothTraceH1 ΩF f),
        bridge_physicalVelocity hγ conjugated (TP v)⟫_ℂ =
        ⟪TF (smoothTraceH1 ΩF f), boundaryContinuousMultiplier
          (if conjugated then localConformalPrimitiveCircle F else
            localConformalVelocityCircle F) (TF v)⟫_ℂ) u ?_ ?_
    · exact isClosed_eq
        (continuous_const.inner ((bridge_physicalVelocity hγ conjugated).continuous.comp
          (TP).continuous))
        (continuous_const.inner ((boundaryContinuousMultiplier
          (if conjugated then localConformalPrimitiveCircle F else
            localConformalVelocityCircle F)).continuous.comp (TF).continuous))
    · intro g
      simp only [smoothTraceH1Lin_apply]
      rw [L2.inner_def, L2.inner_def]
      calc
        _ = ∫ s in Ioc (0 : ℝ) (2 * Real.pi), conj (f (γ s)) *
            ((if conjugated then conj (deriv γ s) else deriv γ s) * g (γ s)) := by
          apply integral_congr_ae
          filter_upwards [h1BoundaryTrace_smooth_ae hb hL hγ f,
            h1BoundaryTrace_smooth_ae hb hL hγ g,
            bridge_physicalVelocity_ae hγ conjugated (TP (smoothTraceH1 ΩF g))]
            with s hf hg hp
          simp only [RCLike.inner_apply', hf, hp, hg]
        _ = ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), deriv τ θ •
            (conj (f (γ (τ θ))) *
              ((if conjugated then conj (deriv γ (τ θ)) else deriv γ (τ θ)) *
                g (γ (τ θ)))) :=
          (integral_traceReparam_conormal hτ _).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC f,
            localConformalDiskH1Trace_smooth_ae hR F hFs hb hL hhol hinj hC g,
            boundaryContinuousMultiplier_ae
              (if conjugated then localConformalPrimitiveCircle F else
                localConformalVelocityCircle F) (TF (smoothTraceH1 ΩF g)),
            bridge_velocity_jacobian hR F hFs hγ hτ hcoord conjugated]
            with θ hf hg hm hj
          cases conjugated <;>
            simp only [Bool.false_eq_true, ↓reduceIte] at * <;>
            simp only [RCLike.inner_apply', hf, hm, hg, hcoord] <;>
            rw [hj] <;> simp only [Complex.real_smul] <;> ring

end CoordinatePairing

section VekuaCoordinates

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

local notation "ΩF" => F '' ball (0 : ℂ) 1
local notation "UF" => localConformalHardyH1Extension hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "JF" => localConformalHardyPrimitive hR F hFs
local notation "MF" => neumannH1AffineMultiplier hb (F 1)
local notation "TF" => localConformalDiskH1Trace hR F hFs hL
local notation "QF" => localConformalDiskHalfTrace hR F hFs hL
local notation "AF" => localConformalVekuaGradientA hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "BF" => localConformalVekuaGradientB hR F hFs hb hL hhol hinj hC hK e he hsource hes
local notation "βF" => fourierCoeff (localConformalVelocityCircle F)
local notation "aF" => localConformalHardyPrimitiveMultiplier F
local notation "gF" => fourierCoeff (localConformalCenteredCircle hR F hFs)
local notation "hβF" => localConformalVelocityCircle_isWL1_half hR F hFs
local notation "haF" => localConformalHardyPrimitiveMultiplier_isWL1 hR F hFs
local notation "hgF" => localConformalCenteredCircle_isWL1_half hR F hFs

/-- The genuine coordinate flux; its two inputs are the actual H¹ gradient
representatives. The variable circle speed is included in its velocities. -/
def localConformalVekuaCoordinateConormalRemainder (E : ℂ) : L2Z →L[ℂ] BoundaryL2 :=
  (-Complex.I) • ((boundaryContinuousMultiplier (localConformalVelocityCircle F)).comp
      ((TF).comp (AF (F 1) E))) +
    Complex.I • ((boundaryContinuousMultiplier (localConformalPrimitiveCircle F)).comp
      ((TF).comp (BF (F 1) E)))

local notation "CCF" => localConformalVekuaCoordinateConormalRemainder
  hR F hFs hb hL hhol hinj hC hK e he hsource hes

private theorem bridge_inner_basis (n : ℤ) (b : L2Z) :
    ⟪stdBasisZ n, b⟫_ℂ = b n := by
  rw [stdBasisZ_apply, lp.inner_single_left]
  simp

include hb hhol hinj hC hK e he hsource hes in
/-- The actual conformal half trace separates L² coefficient vectors.
This uses genuine harmonic tests and the constructed H¹ inverse. -/
theorem localConformalDiskHalfTrace_separates (x y : L2Z)
    (hxy : ∀ w : NeumannH1 ΩF, ⟪QF w, x⟫_ℂ = ⟪QF w, y⟫_ℂ) : x = y := by
  apply lp.ext
  funext n
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · have h := hxy (localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK
      e he hsource hes (diskHolomorphicH1Test m))
    change ⟪diskHalfTrace (localConformalH1Pullback hR F hFs hL _), x⟫_ℂ =
      ⟪diskHalfTrace (localConformalH1Pullback hR F hFs hL _), y⟫_ℂ at h
    rw [localConformalH1Pullback_pushforward, diskHalfTrace_holomorphicTest,
      inner_smul_left, inner_smul_left, bridge_inner_basis, bridge_inner_basis] at h
    exact mul_left_cancel₀ (by
      simp only [map_mul, Complex.conj_ofReal]
      exact mul_ne_zero
        (by exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos (m : ℤ))).ne')
        (by exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne')) h
  · have h := hxy (localConformalH1Pushforward hR F hFs hb hL hhol hinj hC hK
      e he hsource hes (diskAntiholomorphicH1Test m))
    change ⟪diskHalfTrace (localConformalH1Pullback hR F hFs hL _), x⟫_ℂ =
      ⟪diskHalfTrace (localConformalH1Pullback hR F hFs hL _), y⟫_ℂ at h
    rw [localConformalH1Pullback_pushforward, diskHalfTrace_antiholomorphicTest,
      inner_smul_left, inner_smul_left, bridge_inner_basis, bridge_inner_basis] at h
    exact mul_left_cancel₀ (by
      simp only [map_mul, Complex.conj_ofReal]
      exact mul_ne_zero
        (by exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos (-(m : ℤ)))).ne')
        (by exact_mod_cast (Real.sqrt_pos.mpr Real.two_pi_pos).ne')) h

variable {γ : ℝ → ℂ} (hγ : IsBoundaryParam (F '' ball (0 : ℂ) 1) γ)
    {τ : ℝ → ℝ} {c : ℝ} (hτ : IsC1TraceReparam τ c)
    (hcoord : ∀ θ, F (circleMap 0 1 θ) = γ (τ θ))

private theorem bridge_physicalFlux_split (E : ℂ) (b : L2Z) :
    localConformalVekuaConormalRemainder hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hγ (F 1) E b =
      (-Complex.I) • bridge_physicalVelocity hγ false
        (h1BoundaryTrace hb hL hγ (AF (F 1) E b)) +
        Complex.I • bridge_physicalVelocity hγ true
          (h1BoundaryTrace hb hL hγ (BF (F 1) E b)) := by
  apply Lp.ext
  filter_upwards [localConformalVekuaConormalRemainder_ae hR F hFs hb hL hhol hinj
      hC hK e he hsource hes hγ (F 1) E b,
    Lp.coeFn_add
      ((-Complex.I) • bridge_physicalVelocity hγ false
        (h1BoundaryTrace hb hL hγ (AF (F 1) E b)))
      (Complex.I • bridge_physicalVelocity hγ true
        (h1BoundaryTrace hb hL hγ (BF (F 1) E b))),
    Lp.coeFn_smul (-Complex.I) (bridge_physicalVelocity hγ false
      (h1BoundaryTrace hb hL hγ (AF (F 1) E b))),
    Lp.coeFn_smul Complex.I (bridge_physicalVelocity hγ true
      (h1BoundaryTrace hb hL hγ (BF (F 1) E b))),
    bridge_physicalVelocity_ae hγ false (h1BoundaryTrace hb hL hγ (AF (F 1) E b)),
    bridge_physicalVelocity_ae hγ true (h1BoundaryTrace hb hL hγ (BF (F 1) E b))]
    with θ hc ha hA hB hv hvc
  rw [hc, ha]
  simp only [Pi.add_apply, hA, hB, Pi.smul_apply, smul_eq_mul, hv, hvc,
    Bool.false_eq_true, ↓reduceIte]
  ring

include hcoord in
/-- The actual normalized physical remainder is the half-smoothed Fourier
transform of the actual coordinate flux. The Jacobian is proved, not assumed. -/
theorem localConformalVekuaNormalizedConormalRemainder_eq_coordinate (E : ℂ) (b : L2Z) :
    localConformalVekuaNormalizedConormalRemainder hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hγ hτ (F 1) E b =
      sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier (CCF E b)) := by
  apply localConformalDiskHalfTrace_separates hR F hFs hb hL hhol hinj hC hK
    e he hsource hes
  intro w
  rw [localConformalVekuaNormalizedConormalRemainder,
    localConformalBoundaryLoad_inner hR F hFs hb hL hhol hinj hC hγ hτ hcoord,
    bridge_physicalFlux_split hR F hFs hb hL hhol hinj hC hK e he hsource hes hγ,
    inner_add_right, inner_smul_right, inner_smul_right]
  have hh := bridge_half_pairing (QF w) (boundaryFourier (TF w))
    (boundaryFourier (CCF E b)) (fun n => by
      simpa only [sobWeight] using localConformalDiskHalfTrace_apply hR F hFs hL w n)
  rw [hh, boundaryFourier.inner_map_map]
  change _ = ⟪TF w, (-Complex.I) • boundaryContinuousMultiplier
      (localConformalVelocityCircle F) (TF (AF (F 1) E b)) +
    Complex.I • boundaryContinuousMultiplier (localConformalPrimitiveCircle F)
      (TF (BF (F 1) E b))⟫_ℂ
  let uA : NeumannH1 ΩF := AF (F 1) E b
  let uB : NeumannH1 ΩF := BF (F 1) E b
  have hA := bridge_velocity_pairing hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord false w uA
  have hB := bridge_velocity_pairing hR F hFs hb hL hhol hinj hC
    hγ hτ hcoord true w uB
  simp only [Bool.false_eq_true, ↓reduceIte] at hA hB
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  exact congrArg₂ (fun x y : ℂ => (-Complex.I) * x + Complex.I * y) hA hB

private theorem bridge_fromL2_multiplier (a : ℤ → ℂ)
    (ha : IsWL1 (1 / 2 : ℝ) a) (b : L2Z) :
    fromL2 (1 / 2 : ℝ) (normalizedHardyMultiplier a ha b) =
      seqConv a (fromL2 (1 / 2 : ℝ) b) := by
  funext n
  rw [fromL2, normalizedHardyMultiplier_apply, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm (sobWeight n ^ (-(1 / 2 : ℝ))), sobWeight_rpow_mul_neg,
    Complex.ofReal_one, one_mul]

/-- Independent affine and primitive powers have their actual coefficient
convolution. The primitive constant and the frequency-zero term are included. -/
theorem localConformalVekuaConormal_trace_term (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j k : ℕ) :
    (boundaryFourier (TF ((MF ^ j) (UF ((JF ^ k) b)))) : ℤ → ℂ) =
      seqConv (seqConvPow gF j) (antiPrimIter aF k (fromL2 (1 / 2 : ℝ) b)) := by
  rw [← fromL2_half_localConformalDiskHalfTrace,
    localConformalDiskHalfTrace_affineMultiplier_pow hR F hFs hb hL hhol hinj hC,
    bridge_fromL2_multiplier,
    localConformalDiskHalfTrace_hardyExtension_eq_of_nonpositive hR F hFs hb hL hhol
      hinj hC hK e he hsource hes _
      (localConformalHardyPrimitive_pow_nonpositive hR F hFs hhol b hbn k),
    fromL2_localConformalHardyPrimitive_pow]

def bridge_coordinateNormalizer : BoundaryL2 →L[ℂ] L2Z :=
  (sobolevSmoothing (1 / 2 : ℝ) (by norm_num)).comp
    boundaryFourier.toLinearIsometry.toContinuousLinearMap

private theorem bridge_coordinateNormalizer_apply (g : BoundaryL2) (n : ℤ) :
    bridge_coordinateNormalizer g n =
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * boundaryFourier g n := rfl

private theorem bridge_coordinateNormalizer_multiplier (A : C(AddCircle (2 * Real.pi), ℂ))
    (hA : Summable (fourierCoeff A)) (u : NeumannH1 ΩF) (n : ℤ) :
    bridge_coordinateNormalizer (boundaryContinuousMultiplier A (TF u)) n =
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        seqConv (fourierCoeff A) (boundaryFourier (TF u)) n := by
  rw [bridge_coordinateNormalizer_apply, boundaryFourier_continuousMultiplier A hA]

private theorem bridge_toCLM_apply {s t D : ℝ}
    {Φ : (ℤ → ℂ) → (ℤ → ℂ)} (H : SeqOpBound s t D Φ) (b : L2Z) (n : ℤ) :
    H.toCLM b n = ((sobWeight n ^ t : ℝ) : ℂ) * Φ (fromL2 s b) n := rfl

private theorem bridge_smoothed_conormalTerm_apply (j : ℕ) (b : L2Z) (n : ℤ) :
    sobolevSmoothing 1 zero_le_one
        (conormalTermOp (by norm_num) hβF haF hgF j b) n =
      ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        conormalTermMap βF aF gF j (fromL2 (1 / 2 : ℝ) b) n := by
  change ((sobWeight n ^ (-(1 : ℝ)) : ℝ) : ℂ) *
      conormalTermOp (by norm_num) hβF haF hgF j b n = _
  rw [conormalTermOp, bridge_toCLM_apply, ← mul_assoc, ← Complex.ofReal_mul,
    ← Real.rpow_add (sobWeight_pos n)]
  have he : -(1 : ℝ) + 1 / 2 = -(1 / 2 : ℝ) := by ring
  rw [he]

/-- Each actual coordinate flux term equals the existing normalized conormal
term after smoothing. Its velocities use averaged Fourier coefficients. -/
theorem localConformalVekuaConormal_coordinate_term (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (j : ℕ) :
    bridge_coordinateNormalizer
      ((-Complex.I) • boundaryContinuousMultiplier (localConformalVelocityCircle F)
          (TF ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
            (MF ^ j) (UF ((JF ^ (j + 1)) b)))) +
        Complex.I • boundaryContinuousMultiplier (localConformalPrimitiveCircle F)
          (TF (physicalVekuaCoeff E (j + 1) •
            (MF ^ (j + 1)) (UF ((JF ^ j) b))))) =
      conormalCoeff E j • sobolevSmoothing 1 zero_le_one
        (conormalTermOp (by norm_num) hβF haF hgF j b) := by
  have hβ : Summable βF := bridge_summable_coeff (by norm_num) hβF
  have ha : Summable (fourierCoeff (localConformalPrimitiveCircle F)) := by
    rw [localConformalPrimitiveCircle_coeff hR F hFs]
    exact bridge_summable_coeff (by norm_num) haF
  apply lp.ext
  funext n
  simp only [map_add, map_smul, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [bridge_coordinateNormalizer_multiplier hR F hFs hL _ hβ,
    bridge_coordinateNormalizer_multiplier hR F hFs hL _ ha,
    localConformalPrimitiveCircle_coeff hR F hFs,
    localConformalVekuaConormal_trace_term hR F hFs hb hL hhol hinj hC hK
      e he hsource hes b hbn,
    localConformalVekuaConormal_trace_term hR F hFs hb hL hhol hinj hC hK
      e he hsource hes b hbn,
    bridge_smoothed_conormalTerm_apply hR F hFs j b n]
  simp only [conormalTermMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    conormalCoeff, physicalVekuaCoeff]
  ring

/-- Exact identification with the old operator series. This is obtained
from genuine H¹ trace HasSums, without a premise identifying the conormal. -/
theorem localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier (CCF E b)) =
      sobolevSmoothing 1 zero_le_one
        (conormalRemOp (by norm_num) hβF haF hgF E b) := by
  let P := (boundaryContinuousMultiplier (localConformalVelocityCircle F)).comp TF
  let Q := (boundaryContinuousMultiplier (localConformalPrimitiveCircle F)).comp TF
  have hA := (P.hasSum (localConformalVekuaGradientA_hasSum hR F hFs hb hL hhol hinj
    hC hK e he hsource hes (F 1) E b)).const_smul (-Complex.I)
  have hB := (Q.hasSum (localConformalVekuaGradientB_hasSum hR F hFs hb hL hhol hinj
    hC hK e he hsource hes (F 1) E b)).const_smul Complex.I
  have hl := bridge_coordinateNormalizer.hasSum (hA.add hB)
  have heq (j : ℕ) : bridge_coordinateNormalizer
      ((-Complex.I) • P ((physicalVekuaCoeff E (j + 1) * ((j + 1 : ℕ) : ℂ)) •
          (MF ^ j) (UF ((JF ^ (j + 1)) b))) +
        Complex.I • Q (physicalVekuaCoeff E (j + 1) •
          (MF ^ (j + 1)) (UF ((JF ^ j) b)))) =
      conormalCoeff E j • sobolevSmoothing 1 zero_le_one
        (conormalTermOp (by norm_num) hβF haF hgF j b) :=
    localConformalVekuaConormal_coordinate_term hR F hFs hb hL hhol hinj hC hK
      e he hsource hes E b hbn j
  have hl' : HasSum (fun j : ℕ => conormalCoeff E j • sobolevSmoothing 1 zero_le_one
      (conormalTermOp (by norm_num) hβF haF hgF j b))
      (sobolevSmoothing (1 / 2 : ℝ) (by norm_num) (boundaryFourier (CCF E b))) := by
    have hl0 := hl.congr_fun (fun j => (heq j).symm)
    have h_simpa := hl0
    simp only [P, Q, bridge_coordinateNormalizer, localConformalVekuaCoordinateConormalRemainder, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, LinearIsometry.coe_toContinuousLinearMap] at h_simpa ⊢
    exact h_simpa
  have hr := (sobolevSmoothing 1 zero_le_one).hasSum
    ((ContinuousLinearMap.apply ℂ L2Z b).hasSum
      (summable_conormalSeries (by norm_num) hβF haF hgF E).hasSum)
  have hr' : HasSum (fun j : ℕ => conormalCoeff E j • sobolevSmoothing 1 zero_le_one
      (conormalTermOp (by norm_num) hβF haF hgF j b))
      (sobolevSmoothing 1 zero_le_one
        (conormalRemOp (by norm_num) hβF haF hgF E b)) := by
    simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply,
      map_smul, conormalRemOp] using hr
  exact hl'.unique hr'

include hcoord in
/-- The actual physical normalized flux is precisely the Fourier conormal
remainder used by formal transmutation, including the zero Fourier mode. -/
theorem localConformalVekuaNormalizedConormalRemainder_eq_conormalRemOp
    (E : ℂ) (b : L2Z) (hbn : IsNonpositiveFourierSupport b) :
    localConformalVekuaNormalizedConormalRemainder hR F hFs hb hL hhol hinj hC hK
        e he hsource hes hγ hτ (F 1) E b =
      sobolevSmoothing 1 zero_le_one
        (conormalRemOp (by norm_num) hβF haF hgF E b) := by
  rw [localConformalVekuaNormalizedConormalRemainder_eq_coordinate hR F hFs hb hL
    hhol hinj hC hK e he hsource hes hγ hτ hcoord]
  exact localConformalVekuaCoordinateConormalRemainder_eq_conormalRemOp hR F hFs hb hL
    hhol hinj hC hK e he hsource hes E b hbn

include hγ hτ hcoord in
/-- The actual Vekua solution has the existing normalized conormal weak
form, proved through its genuine physical gradient and boundary flux. -/
theorem localConformalVekuaH1_normalizedConormal_weak_form (E : ℂ) (b : L2Z)
    (hbn : IsNonpositiveFourierSupport b) (w : NeumannH1 ΩF) :
    (∑ i : Fin 2, ⟪h1Gradient ΩF i w, h1Gradient ΩF i
      (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes
        (F 1) E b)⟫_ℂ) - E * ⟪h1Value ΩF w, h1Value ΩF
      (localConformalVekuaH1 hR F hFs hb hL hhol hinj hC hK e he hsource hes
        (F 1) E b)⟫_ℂ =
      ⟪QF w, normalizedConormal hβF haF hgF E b⟫_ℂ := by
  have h := localConformalVekuaH1_normalized_weak_form hR F hFs hb hL hhol hinj hC hK
    e he hsource hes hγ hτ hcoord (F 1) E b hbn w
  rw [localConformalVekuaNormalizedConormalRemainder_eq_conormalRemOp hR F hFs hb hL
    hhol hinj hC hK e he hsource hes hγ hτ hcoord E b hbn] at h
  have hbproj : (1 - posProj) b = b := by
    ext n
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      lp.coeFn_sub, Pi.sub_apply, posProj, diagOp_apply]
    by_cases hn : 0 < n
    · simp [hn, hbn n hn]
    · simp [hn]
  simpa only [hbproj, normalizedConormal, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply] using h

end VekuaCoordinates

end PolyaNeumann

end
