module

public import RequestProject.ArcLength
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Calculus.Monotone
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Algebra.Group.Int.Units

/-!
# Actual lifts between physical boundary parametrizations

The six physical `IsBoundaryParam` fields give an actual homeomorphism from
the additive circle onto the physical frontier.  Lifting the resulting circle
homeomorphism and its inverse gives a genuine real homeomorphism, rather than
an assumed reparametrization.  A regular C¹ reference curve then gives actual
local Lipschitz bounds and an almost-everywhere chain rule for this lift.

Absolute continuity and the two actual constant speeds make the lift affine.
Single traversal forces its slope to be `1` or `-1`; the signed-area fields
select `1` whenever the physical area is nonzero.  In particular this gives
exact shift synchronization for an actual bounded domain, without a new
hypothesis in the original bounded-domain theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter
open scoped Real ComplexConjugate Topology

local instance boundaryParamPeriod_pos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The actual periodic curve descended to the additive circle. -/
def boundaryParamCircleMap (γ : ℝ → ℂ) : AddCircle (2 * Real.pi) → ℂ :=
  AddCircle.liftIco (2 * Real.pi) 0 γ

/-- The circle map agrees with the original curve at every real parameter. -/
theorem boundaryParamCircleMap_coe {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (θ : ℝ) :
    boundaryParamCircleMap γ (θ : AddCircle (2 * Real.pi)) = γ θ := by
  change γ (toIcoMod Real.two_pi_pos 0 θ) = γ θ
  rw [toIcoMod, hγ.periodic.sub_zsmul_eq]

theorem boundaryParamCircleMap_continuous {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : Continuous (boundaryParamCircleMap γ) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  exact AddCircle.liftIco_zero_continuous
    (by simpa only [zero_add] using (hγ.periodic 0).symm) hK.continuous.continuousOn

theorem boundaryParamCircleMap_mem_frontier {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (q : AddCircle (2 * Real.pi)) :
    boundaryParamCircleMap γ q ∈ frontier Ω := by
  rw [← hγ.image]
  refine ⟨(AddCircle.equivIco (2 * Real.pi) 0 q : ℝ), ?_, rfl⟩
  exact Ico_subset_Icc_self (by
    simpa only [zero_add] using (AddCircle.equivIco (2 * Real.pi) 0 q).property)

theorem boundaryParamCircleMap_injective {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : Function.Injective (boundaryParamCircleMap γ) := by
  intro q r hqr
  apply (AddCircle.equivIco (2 * Real.pi) 0).injective
  apply Subtype.ext
  exact hγ.injOn
    (by simpa only [zero_add] using (AddCircle.equivIco (2 * Real.pi) 0 q).property)
    (by simpa only [zero_add] using (AddCircle.equivIco (2 * Real.pi) 0 r).property) hqr

theorem boundaryParam_eq_iff_circle_coe_eq {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (x y : ℝ) :
    γ x = γ y ↔ (x : AddCircle (2 * Real.pi)) = (y : AddCircle (2 * Real.pi)) := by
  constructor
  · intro hxy
    apply boundaryParamCircleMap_injective hγ
    rwa [boundaryParamCircleMap_coe hγ x, boundaryParamCircleMap_coe hγ y]
  · intro hxy
    rw [← boundaryParamCircleMap_coe hγ x, ← boundaryParamCircleMap_coe hγ y, hxy]

/-- The actual map with codomain the physical frontier.  Its membership proof
is public because it is part of this computational definition. -/
def boundaryParamFrontierMap {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : AddCircle (2 * Real.pi) → frontier Ω :=
  fun q => ⟨boundaryParamCircleMap γ q, boundaryParamCircleMap_mem_frontier hγ q⟩

theorem boundaryParamFrontierMap_continuous {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : Continuous (boundaryParamFrontierMap hγ) :=
  (boundaryParamCircleMap_continuous hγ).subtype_mk _

theorem boundaryParamFrontierMap_bijective {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : Function.Bijective (boundaryParamFrontierMap hγ) := by
  constructor
  · intro q r hqr
    exact boundaryParamCircleMap_injective hγ (congrArg Subtype.val hqr)
  · intro z
    have hz : (z : ℂ) ∈ γ '' Icc 0 (2 * Real.pi) := by
      rw [hγ.image]
      exact z.property
    obtain ⟨θ, hθ, hθz⟩ := hz
    refine ⟨(θ : AddCircle (2 * Real.pi)), Subtype.ext ?_⟩
    exact (boundaryParamCircleMap_coe hγ θ).trans hθz

/-- The genuine compact-to-Hausdorff boundary homeomorphism. -/
def boundaryParamCircleHomeomorph {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : AddCircle (2 * Real.pi) ≃ₜ frontier Ω :=
  (Equiv.ofBijective (boundaryParamFrontierMap hγ)
    (boundaryParamFrontierMap_bijective hγ)).toHomeomorphOfContinuousClosed
      (boundaryParamFrontierMap_continuous hγ)
      (boundaryParamFrontierMap_continuous hγ).isClosedMap

theorem boundaryParamCircleHomeomorph_coe {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (θ : ℝ) :
    (boundaryParamCircleHomeomorph hγ (θ : AddCircle (2 * Real.pi)) : ℂ) = γ θ :=
  boundaryParamCircleMap_coe hγ θ

/-- Two actual parametrizations induce an actual homeomorphism of the circle. -/
def boundaryParamCircleChange {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : IsBoundaryParam Ω β) (hγ : IsBoundaryParam Ω γ) :
    AddCircle (2 * Real.pi) ≃ₜ AddCircle (2 * Real.pi) :=
  (boundaryParamCircleHomeomorph hγ).trans (boundaryParamCircleHomeomorph hβ).symm

theorem boundaryParamCircleChange_apply {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : IsBoundaryParam Ω β) (hγ : IsBoundaryParam Ω γ)
    (q : AddCircle (2 * Real.pi)) :
    boundaryParamCircleMap β (boundaryParamCircleChange hβ hγ q) =
      boundaryParamCircleMap γ q := by
  exact congrArg Subtype.val
    ((boundaryParamCircleHomeomorph hβ).apply_symm_apply
      (boundaryParamCircleHomeomorph hγ q))

/-- A homeomorphism of the genuine additive circle has a genuine real
homeomorphic lift.  The inverse lift is constructed independently and proved
to be an inverse by uniqueness of covering lifts. -/
theorem exists_realHomeomorph_lift_of_addCircleHomeomorph
    (e : AddCircle (2 * Real.pi) ≃ₜ AddCircle (2 * Real.pi)) :
    ∃ t ∈ Ico 0 (2 * Real.pi), ∃ T : ℝ ≃ₜ ℝ,
      T 0 = t ∧ ∀ θ : ℝ,
        (T θ : AddCircle (2 * Real.pi)) = e (θ : AddCircle (2 * Real.pi)) := by
  letI : LocPathConnectedSpace ℝ := LocPathConnectedSpace.of_bases
    (fun x : ℝ => nhds_basis_Ioo x)
    (fun x b hx => (convex_Ioo (𝕜 := ℝ) b.1 b.2).isPathConnected ⟨x, hx⟩)
  let t : ℝ := AddCircle.equivIco (2 * Real.pi) 0 (e 0)
  have ht : t ∈ Ico 0 (2 * Real.pi) := by
    simpa only [zero_add] using (AddCircle.equivIco (2 * Real.pi) 0 (e 0)).property
  have htcoe : (t : AddCircle (2 * Real.pi)) = e 0 :=
    (AddCircle.equivIco (2 * Real.pi) 0).symm_apply_apply (e 0)
  let f : C(ℝ, AddCircle (2 * Real.pi)) :=
    ⟨fun θ => e (θ : AddCircle (2 * Real.pi)),
      e.continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))⟩
  have hf0 : (t : AddCircle (2 * Real.pi)) = f 0 := by
    simpa only [f, ContinuousMap.coe_mk, QuotientAddGroup.mk_zero] using htcoe
  obtain ⟨T, hT, _⟩ :=
    (AddCircle.isCoveringMap_coe (2 * Real.pi)).existsUnique_continuousMap_lifts f 0 t hf0
  have hTcoe (θ : ℝ) :
      (T θ : AddCircle (2 * Real.pi)) = e (θ : AddCircle (2 * Real.pi)) :=
    congrFun hT.2 θ
  let f' : C(ℝ, AddCircle (2 * Real.pi)) :=
    ⟨fun θ => e.symm (θ : AddCircle (2 * Real.pi)),
      e.symm.continuous.comp (AddCircle.continuous_mk' (2 * Real.pi))⟩
  have hf't : ((0 : ℝ) : AddCircle (2 * Real.pi)) = f' t := by
    change (0 : AddCircle (2 * Real.pi)) = e.symm (t : AddCircle (2 * Real.pi))
    rw [htcoe, e.symm_apply_apply]
  obtain ⟨S, hS, _⟩ :=
    (AddCircle.isCoveringMap_coe (2 * Real.pi)).existsUnique_continuousMap_lifts f' t 0 hf't
  have hScoe (θ : ℝ) :
      (S θ : AddCircle (2 * Real.pi)) = e.symm (θ : AddCircle (2 * Real.pi)) :=
    congrFun hS.2 θ
  have hST : (fun θ : ℝ => S (T θ)) = fun θ : ℝ => θ := by
    refine (AddCircle.isCoveringMap_coe (2 * Real.pi)).eq_of_comp_eq
      (S.continuous.comp T.continuous) continuous_id ?_ 0 ?_
    · funext θ
      change (S (T θ) : AddCircle (2 * Real.pi)) = (θ : AddCircle (2 * Real.pi))
      rw [hScoe, hTcoe, e.symm_apply_apply]
    · change S (T 0) = 0
      rw [hT.1, hS.1]
  have hTS : (fun θ : ℝ => T (S θ)) = fun θ : ℝ => θ := by
    refine (AddCircle.isCoveringMap_coe (2 * Real.pi)).eq_of_comp_eq
      (T.continuous.comp S.continuous) continuous_id ?_ t ?_
    · funext θ
      change (T (S θ) : AddCircle (2 * Real.pi)) = (θ : AddCircle (2 * Real.pi))
      rw [hTcoe, hScoe, e.apply_symm_apply]
    · change T (S t) = t
      rw [hS.1, hT.1]
  let H : ℝ ≃ₜ ℝ :=
    { toFun := T
      invFun := S
      left_inv := fun θ => congrFun hST θ
      right_inv := fun θ => congrFun hTS θ
      continuous_toFun := T.continuous
      continuous_invFun := S.continuous }
  exact ⟨t, ht, H, hT.1, hTcoe⟩

/-- Actual real synchronization up to a homeomorphic lift, with no assumed
reparametrization, orientation, or equality of speeds. -/
theorem exists_boundaryParam_realHomeomorph {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : IsBoundaryParam Ω β) (hγ : IsBoundaryParam Ω γ) :
    ∃ t ∈ Ico 0 (2 * Real.pi), ∃ T : ℝ ≃ₜ ℝ,
      T 0 = t ∧ (∀ θ : ℝ, γ θ = β (T θ)) ∧ (StrictMono T ∨ StrictAnti T) := by
  obtain ⟨t, ht, T, hT0, hTcoe⟩ :=
    exists_realHomeomorph_lift_of_addCircleHomeomorph (boundaryParamCircleChange hβ hγ)
  refine ⟨t, ht, T, hT0, ?_, T.continuous.strictMono_of_inj T.injective⟩
  intro θ
  calc
    γ θ = boundaryParamCircleMap γ (θ : AddCircle (2 * Real.pi)) :=
      (boundaryParamCircleMap_coe hγ θ).symm
    _ = boundaryParamCircleMap β (boundaryParamCircleChange hβ hγ
        (θ : AddCircle (2 * Real.pi))) := (boundaryParamCircleChange_apply hβ hγ _).symm
    _ = boundaryParamCircleMap β (T θ : AddCircle (2 * Real.pi)) := by rw [hTcoe]
    _ = β (T θ) := boundaryParamCircleMap_coe hβ (T θ)

/-- Nonzero C¹ velocity gives a genuine local inverse chord bound between
any two parameters, by the real tangent projection and the mean value theorem. -/
theorem exists_regularCurve_local_inverse_bound (β : ℝ → ℂ)
    (hβ : ContDiff ℝ 1 β) (t : ℝ) (ht : deriv β t ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ Ioo (t - r) (t + r), ∀ y ∈ Ioo (t - r) (t + r),
        |x - y| ≤ C * ‖β x - β y‖ := by
  let c : ℂ := conj (deriv β t)
  let D : ℝ := Complex.normSq (deriv β t)
  let f : ℝ → ℝ := fun x => (c * β x).re
  have hD : 0 < D := Complex.normSq_pos.mpr ht
  have hc : 0 < ‖c‖ := by
    simpa only [c, Complex.norm_conj] using norm_pos_iff.mpr ht
  have hdt : (c * deriv β t).re = D := by
    dsimp only [c, D]
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have hdf (x : ℝ) : HasDerivAt f (c * deriv β x).re x := by
    have hd := ((hβ.differentiable_one x).hasDerivAt).const_mul c
    simpa only [f, Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  have hfc : Continuous f :=
    Complex.continuous_re.comp (continuous_const.mul hβ.continuous)
  have hfd : Differentiable ℝ f := fun x => (hdf x).differentiableAt
  have hdc : Continuous (fun x : ℝ => (c * deriv β x).re) :=
    Complex.continuous_re.comp (continuous_const.mul hβ.continuous_deriv_one)
  have hopen : IsOpen {x : ℝ | D / 2 < (c * deriv β x).re} :=
    isOpen_lt continuous_const hdc
  have htmem : t ∈ {x : ℝ | D / 2 < (c * deriv β x).re} := by
    change D / 2 < (c * deriv β t).re
    rw [hdt]
    linarith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds htmem)
  have hlower (x : ℝ) (hx : x ∈ Ioo (t - r) (t + r)) : D / 2 ≤ deriv f x := by
    rw [(hdf x).deriv]
    have hxball : x ∈ Metric.ball t r := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    exact le_of_lt (hball hxball)
  have hgrowth := (convex_Ioo (𝕜 := ℝ) (t - r) (t + r)).mul_sub_le_image_sub_of_le_deriv
    hfc.continuousOn hfd.differentiableOn
    (fun x hx => hlower x (interior_subset hx))
  refine ⟨r, hr, ‖c‖ / (D / 2), div_pos hc (half_pos hD), ?_⟩
  intro x hx y hy
  have hp : D / 2 * |x - y| ≤ |f x - f y| := by
    by_cases hxy : x ≤ y
    · calc
        _ = D / 2 * (y - x) := by rw [abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
        _ ≤ f y - f x := hgrowth x hx y hy hxy
        _ ≤ |f y - f x| := le_abs_self _
        _ = |f x - f y| := abs_sub_comm _ _
    · have hyx : y ≤ x := (not_le.mp hxy).le
      calc
        _ = D / 2 * (x - y) := by rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        _ ≤ f x - f y := hgrowth y hy x hx hyx
        _ ≤ |f x - f y| := le_abs_self _
  have hproj : f x - f y = (c * (β x - β y)).re := by
    simp only [f, mul_sub, Complex.sub_re]
  have hpn : D / 2 * |x - y| ≤ ‖c‖ * ‖β x - β y‖ := by
    calc
      _ ≤ |f x - f y| := hp
      _ = |(c * (β x - β y)).re| := by rw [hproj]
      _ ≤ ‖c * (β x - β y)‖ := Complex.abs_re_le_norm _
      _ = _ := norm_mul _ _
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (half_pos hD)).mpr (by simpa only [mul_comm] using hpn)

/-- The actual lift is locally Lipschitz because its reference curve has a
genuine local inverse bound and the arbitrary physical curve is Lipschitz. -/
theorem boundaryParamLift_locallyLipschitz {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : ContDiff ℝ 1 β) (hnz : ∀ t, deriv β t ≠ 0)
    (hγ : IsBoundaryParam Ω γ) (T : ℝ ≃ₜ ℝ)
    (hcomp : ∀ θ : ℝ, γ θ = β (T θ)) : LocallyLipschitz (T : ℝ → ℝ) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  intro θ
  obtain ⟨r, hr, C, hC, hbound⟩ :=
    exists_regularCurve_local_inverse_bound β hβ (T θ) (hnz (T θ))
  let U : Set ℝ := T ⁻¹' Ioo (T θ - r) (T θ + r)
  have hU : U ∈ 𝓝 θ :=
    T.continuous.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  refine ⟨Real.toNNReal (C * (K : ℝ)), U, hU, ?_⟩
  apply LipschitzOnWith.of_dist_le'
  intro x hx y hy
  calc
    dist (T x) (T y) = |T x - T y| := Real.dist_eq _ _
    _ ≤ C * ‖β (T x) - β (T y)‖ := hbound (T x) hx (T y) hy
    _ = C * dist (γ x) (γ y) := by rw [← hcomp x, ← hcomp y, dist_eq_norm]
    _ ≤ C * ((K : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hK.dist_le_mul x y) hC.le
    _ = (C * (K : ℝ)) * dist x y := by ring

/-- In particular, the genuine lift is Lipschitz on every compact parameter interval. -/
theorem boundaryParamLift_lipschitzOn_Icc {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : ContDiff ℝ 1 β) (hnz : ∀ t, deriv β t ≠ 0)
    (hγ : IsBoundaryParam Ω γ) (T : ℝ ≃ₜ ℝ)
    (hcomp : ∀ θ : ℝ, γ θ = β (T θ)) (a b : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (T : ℝ → ℝ) (Icc a b) :=
  LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
    (boundaryParamLift_locallyLipschitz hβ hnz hγ T hcomp).locallyLipschitzOn

/-- A genuine real homeomorphism is differentiable almost everywhere; no
differentiability or absolute-continuity premise is imposed on its lift. -/
theorem realHomeomorph_ae_differentiable (T : ℝ ≃ₜ ℝ) :
    ∀ᵐ θ : ℝ ∂volume, DifferentiableAt ℝ (T : ℝ → ℝ) θ := by
  obtain hT | hT := T.continuous.strictMono_of_inj T.injective
  · exact hT.monotone.ae_differentiableAt
  · have hn : Monotone (fun θ : ℝ => -T θ) :=
      fun x y hxy => neg_le_neg (hT.antitone hxy)
    filter_upwards [hn.ae_differentiableAt] with θ hθ
    have hθ' := hθ.neg
    change DifferentiableAt ℝ (fun x : ℝ => -(-T x)) θ at hθ'
    simpa only [neg_neg] using hθ'

/-- The actual almost-everywhere derivative chain for the homeomorphic lift. -/
theorem boundaryParamLift_ae_deriv_chain {β γ : ℝ → ℂ}
    (hβ : ContDiff ℝ 1 β) (T : ℝ ≃ₜ ℝ)
    (hcomp : ∀ θ : ℝ, γ θ = β (T θ)) :
    ∀ᵐ θ : ℝ ∂volume, deriv γ θ = deriv (T : ℝ → ℝ) θ • deriv β (T θ) := by
  have hfun : γ = β ∘ T := funext hcomp
  filter_upwards [realHomeomorph_ae_differentiable T] with θ hθ
  rw [hfun]
  exact ((hβ.differentiable_one (T θ)).hasDerivAt.scomp θ hθ.hasDerivAt).deriv

/-- The real speed of a C¹ physical boundary parametrization is constant
everywhere, because its genuine almost-everywhere speed is continuous. -/
theorem boundaryParam_contDiff_constant_speed {Ω : Set ℂ} {β : ℝ → ℂ}
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ : ℝ, ‖deriv β θ‖ = c := by
  obtain ⟨c, hc, hspeed⟩ := hβ.const_speed
  have heq : (fun θ : ℝ => ‖deriv β θ‖) = fun _ : ℝ => c :=
    Measure.eq_of_ae_eq hspeed hβC1.continuous_deriv_one.norm continuous_const
  exact ⟨c, hc, fun θ => congrFun heq θ⟩

/-- The actual constant-speed fields determine the absolute derivative of
the constructed lift.  Neither equality of the two speeds nor its orientation
is assumed. -/
theorem boundaryParamLift_ae_abs_deriv {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β)
    (hγ : IsBoundaryParam Ω γ) (T : ℝ ≃ₜ ℝ)
    (hcomp : ∀ θ : ℝ, γ θ = β (T θ)) :
    ∃ cβ : ℝ, 0 < cβ ∧ ∃ cγ : ℝ, 0 < cγ ∧
      (∀ θ : ℝ, ‖deriv β θ‖ = cβ) ∧
      (∀ᵐ θ : ℝ ∂volume, |deriv (T : ℝ → ℝ) θ| = cγ / cβ) := by
  obtain ⟨cβ, hcβ, hβspeed⟩ := boundaryParam_contDiff_constant_speed hβ hβC1
  obtain ⟨cγ, hcγ, hγspeed⟩ := hγ.const_speed
  refine ⟨cβ, hcβ, cγ, hcγ, hβspeed, ?_⟩
  filter_upwards [hγspeed, boundaryParamLift_ae_deriv_chain hβC1 T hcomp] with θ hθ hchain
  have heq : |deriv (T : ℝ → ℝ) θ| * cβ = cγ := by
    calc
      _ = ‖deriv (T : ℝ → ℝ) θ • deriv β (T θ)‖ := by
        rw [norm_smul, Real.norm_eq_abs, hβspeed]
      _ = ‖deriv γ θ‖ := congrArg norm hchain.symm
      _ = cγ := hθ
  exact (eq_div_iff hcβ.ne').mpr heq

/-- The proved synchronization package for a smooth regular reference and
an arbitrary actual physical boundary parametrization. -/
theorem exists_boundaryParam_locallyLipschitz_realHomeomorph
    {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β)
    (hnz : ∀ θ, deriv β θ ≠ 0) (hγ : IsBoundaryParam Ω γ) :
    ∃ t ∈ Ico 0 (2 * Real.pi), ∃ T : ℝ ≃ₜ ℝ,
      T 0 = t ∧ (∀ θ : ℝ, γ θ = β (T θ)) ∧
      (StrictMono T ∨ StrictAnti T) ∧ LocallyLipschitz (T : ℝ → ℝ) ∧
      (∀ᵐ θ : ℝ ∂volume,
        deriv γ θ = deriv (T : ℝ → ℝ) θ • deriv β (T θ)) := by
  obtain ⟨t, ht, T, hT0, hcomp, hmono⟩ := exists_boundaryParam_realHomeomorph hβ hγ
  exact ⟨t, ht, T, hT0, hcomp, hmono,
    boundaryParamLift_locallyLipschitz hβC1 hnz hγ T hcomp,
    boundaryParamLift_ae_deriv_chain hβC1 T hcomp⟩

/-- Genuine real absolute continuity makes a locally Lipschitz function with
constant a.e. derivative affine.  This uses the actual AC fundamental theorem. -/
theorem locallyLipschitz_eq_affine_of_ae_deriv {f : ℝ → ℝ} {a : ℝ}
    (hf : LocallyLipschitz f) (hd : ∀ᵐ θ : ℝ ∂volume, deriv f θ = a) :
    ∀ θ : ℝ, f θ = a * θ + f 0 := by
  intro θ
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (s := uIcc 0 θ) isCompact_uIcc hf.locallyLipschitzOn
  have hi : ∫ s in (0 : ℝ)..θ, deriv f s = ∫ s in (0 : ℝ)..θ, a := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with s hs _ using hs
  have hFTC := hK.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  rw [hi, intervalIntegral.integral_const] at hFTC
  simp only [sub_zero, smul_eq_mul] at hFTC
  linarith

/-- Constant-speed physical curves force the actual real lift to be affine;
the slope is derived from their two genuine speeds. -/
theorem boundaryParamLift_affine {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β)
    (hnz : ∀ θ, deriv β θ ≠ 0) (hγ : IsBoundaryParam Ω γ)
    (T : ℝ ≃ₜ ℝ) (hcomp : ∀ θ : ℝ, γ θ = β (T θ)) :
    ∃ a : ℝ, a ≠ 0 ∧ ∀ θ : ℝ, T θ = a * θ + T 0 := by
  obtain ⟨cβ, hcβ, cγ, hcγ, _, habs⟩ :=
    boundaryParamLift_ae_abs_deriv hβ hβC1 hγ T hcomp
  have hc : 0 < cγ / cβ := div_pos hcγ hcβ
  have hLip := boundaryParamLift_locallyLipschitz hβC1 hnz hγ T hcomp
  obtain hmono | hanti := T.continuous.strictMono_of_inj T.injective
  · refine ⟨cγ / cβ, hc.ne', locallyLipschitz_eq_affine_of_ae_deriv hLip ?_⟩
    filter_upwards [habs] with θ hθ
    rwa [abs_of_nonneg hmono.monotone.deriv_nonneg] at hθ
  · refine ⟨-(cγ / cβ), neg_ne_zero.mpr hc.ne',
      locallyLipschitz_eq_affine_of_ae_deriv hLip ?_⟩
    filter_upwards [habs] with θ hθ
    rw [abs_of_nonpos hanti.antitone.deriv_nonpos] at hθ
    linarith

/-- The same boundary image and single traversal force an affine lift's
slope to be an integer unit.  Thus its slope is exactly `1` or `-1`. -/
theorem boundaryParamLift_affine_unit {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : IsBoundaryParam Ω β) (hγ : IsBoundaryParam Ω γ)
    (T : ℝ ≃ₜ ℝ) (hcomp : ∀ θ : ℝ, γ θ = β (T θ))
    (a : ℝ) (ha : ∀ θ : ℝ, T θ = a * θ + T 0) : a = 1 ∨ a = -1 := by
  have hperne : 2 * Real.pi ≠ 0 := Real.two_pi_pos.ne'
  have hβsame : β (T (2 * Real.pi)) = β (T 0) := by
    calc
      β (T (2 * Real.pi)) = γ (2 * Real.pi) := (hcomp (2 * Real.pi)).symm
      _ = γ 0 := by simpa only [zero_add] using hγ.periodic 0
      _ = β (T 0) := hcomp 0
  have hco := (boundaryParam_eq_iff_circle_coe_eq hβ _ _).mp hβsame
  have hzero : ((a * (2 * Real.pi) : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
    have hsub : ((T (2 * Real.pi) - T 0 : ℝ) : AddCircle (2 * Real.pi)) = 0 := by
      rw [AddCircle.coe_sub, hco, sub_self]
    simpa only [ha (2 * Real.pi), add_sub_cancel_right] using hsub
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (2 * Real.pi)).mp hzero
  have hmR : (m : ℝ) = a := by
    rw [zsmul_eq_mul] at hm
    exact mul_right_cancel₀ hperne hm
  let x : ℝ := T.symm (T 0 + 2 * Real.pi)
  have hTx : T x = T 0 + 2 * Real.pi := T.apply_symm_apply _
  have hγsame : γ x = γ 0 := by
    rw [hcomp x, hTx, hβ.periodic (T 0), ← hcomp 0]
  have hxzero : (x : AddCircle (2 * Real.pi)) = 0 := by
    simpa only [AddCircle.coe_zero] using
      (boundaryParam_eq_iff_circle_coe_eq hγ x 0).mp hγsame
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (2 * Real.pi)).mp hxzero
  have hx : a * x = 2 * Real.pi := by
    rw [ha x] at hTx
    linarith
  have hmnR : (m : ℝ) * (n : ℝ) = 1 := by
    apply mul_right_cancel₀ hperne
    calc
      ((m : ℝ) * (n : ℝ)) * (2 * Real.pi) = a * x := by
        rw [hmR, ← hn, zsmul_eq_mul]
        ring
      _ = 2 * Real.pi := hx
      _ = 1 * (2 * Real.pi) := by ring
  have hmn : m * n = 1 := by exact_mod_cast hmnR
  obtain hmone | hmneg := Int.eq_one_or_neg_one_of_mul_eq_one hmn
  · left
    rw [← hmR, hmone, Int.cast_one]
  · right
    rw [← hmR, hmneg, Int.cast_neg, Int.cast_one]

/-- Actual synchronization has only the two possible unit-speed orientations.
No speed equality, lift, or orientation is supplied as a premise. -/
theorem exists_boundaryParam_shift_or_reverse {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β)
    (hnz : ∀ θ, deriv β θ ≠ 0) (hγ : IsBoundaryParam Ω γ) :
    ∃ t ∈ Ico 0 (2 * Real.pi),
      (∀ θ : ℝ, γ θ = β (θ + t)) ∨ (∀ θ : ℝ, γ θ = β (-θ + t)) := by
  obtain ⟨t, ht, T, hT0, hcomp, _⟩ := exists_boundaryParam_realHomeomorph hβ hγ
  obtain ⟨a, _, ha⟩ := boundaryParamLift_affine hβ hβC1 hnz hγ T hcomp
  refine ⟨t, ht, ?_⟩
  obtain haone | haneg := boundaryParamLift_affine_unit hβ hγ T hcomp a ha
  · left
    intro θ
    rw [hcomp θ, ha θ, haone, one_mul, hT0]
  · right
    intro θ
    rw [hcomp θ, ha θ, haneg, neg_one_mul, hT0]

theorem integral_signedAreaDensity_add_shift {β : ℝ → ℂ}
    (hper : Function.Periodic β (2 * Real.pi)) (t : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity (fun θ => β (θ + t)) θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity β θ := by
  calc
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity β (θ + t) := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [signedAreaDensity, deriv_comp_add_const]
    _ = ∫ θ in t..t + 2 * Real.pi, signedAreaDensity β θ := by
      rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm (2 * Real.pi) t]
    _ = _ := integral_signedAreaDensity_shift hper t

/-- The reverse lift reverses the actual signed area, even with a shifted
origin.  This is the orientation test, not an assumed orientation. -/
theorem integral_signedAreaDensity_reverse_shift {β : ℝ → ℂ}
    (hper : Function.Periodic β (2 * Real.pi)) (t : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity (fun θ => β (-θ + t)) θ) =
      -(∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity β θ) := by
  let δ : ℝ → ℂ := fun θ => β (θ + t)
  have hδper : Function.Periodic δ (2 * Real.pi) := by
    intro θ
    change β ((θ + 2 * Real.pi) + t) = β (θ + t)
    rw [show (θ + 2 * Real.pi) + t = (θ + t) + 2 * Real.pi by ring, hper]
  have hd (θ : ℝ) :
      signedAreaDensity (fun θ => β (-θ + t)) θ = -signedAreaDensity δ (-θ) := by
    change signedAreaDensity (fun θ => δ (-θ)) θ = -signedAreaDensity δ (-θ)
    simp only [signedAreaDensity, deriv_comp_neg, mul_neg, Complex.neg_im]
  simp_rw [hd]
  rw [intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_neg (fun θ => signedAreaDensity δ θ), neg_zero]
  have hshift := integral_signedAreaDensity_shift hδper (-(2 * Real.pi))
  rw [neg_add_cancel] at hshift
  rw [hshift]
  exact congrArg Neg.neg (integral_signedAreaDensity_add_shift hper t)

/-- The physical signed-area fields exclude the reverse lift at nonzero
physical area, and give the exact shift requested by boundary synchronization. -/
theorem exists_boundaryParam_shift_of_area_ne_zero {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β)
    (hnz : ∀ θ, deriv β θ ≠ 0) (hγ : IsBoundaryParam Ω γ)
    (harea : (volume Ω).toReal ≠ 0) :
    ∃ t ∈ Icc 0 (2 * Real.pi), ∀ θ : ℝ, γ θ = β (θ + t) := by
  obtain ⟨t, ht, hshift | hreverse⟩ := exists_boundaryParam_shift_or_reverse hβ hβC1 hnz hγ
  · exact ⟨t, Ico_subset_Icc_self ht, hshift⟩
  · have hfun : γ = fun θ : ℝ => β (-θ + t) := funext hreverse
    have hγarea : (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity γ θ) =
        2 * (volume Ω).toReal := hγ.area
    have hβarea : (∫ θ in (0 : ℝ)..(2 * Real.pi), signedAreaDensity β θ) =
        2 * (volume Ω).toReal := hβ.area
    rw [hfun, integral_signedAreaDensity_reverse_shift hβ.periodic t, hβarea] at hγarea
    exact (harea (by linarith)).elim

/-- The original bounded-domain geometry itself supplies positive finite
area.  Thus a smooth regular physical boundary parameter synchronizes with
every original physical boundary parameter by an actual cyclic shift. -/
theorem exists_boundaryParam_shift_of_bounded_domain {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsDomain Ω)
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β)
    (hnz : ∀ θ, deriv β θ ≠ 0) (hγ : IsBoundaryParam Ω γ) :
    ∃ t ∈ Icc 0 (2 * Real.pi), ∀ θ : ℝ, γ θ = β (θ + t) := by
  have hvolpos : 0 < (volume Ω).toReal :=
    ENNReal.toReal_pos (hΩ.1.measure_pos volume hΩ.2.nonempty).ne' hb.measure_lt_top.ne
  exact exists_boundaryParam_shift_of_area_ne_zero hβ hβC1 hnz hγ hvolpos.ne'

/-- Consequently the original arbitrary physical boundary parameter is C¹,
with a nonzero velocity, once the genuine smooth regular reference exists. -/
theorem boundaryParam_contDiff_of_regular_reference {Ω : Set ℂ} {β γ : ℝ → ℂ}
    (hb : Bornology.IsBounded Ω) (hΩ : IsDomain Ω)
    (hβ : IsBoundaryParam Ω β) (hβC1 : ContDiff ℝ 1 β)
    (hnz : ∀ θ, deriv β θ ≠ 0) (hγ : IsBoundaryParam Ω γ) :
    ContDiff ℝ 1 γ ∧ ∀ θ : ℝ, deriv γ θ ≠ 0 := by
  obtain ⟨t, _, hshift⟩ := exists_boundaryParam_shift_of_bounded_domain hb hΩ hβ hβC1 hnz hγ
  have hfun : γ = fun θ : ℝ => β (θ + t) := funext hshift
  constructor
  · rw [hfun]
    exact hβC1.comp (contDiff_id.add contDiff_const)
  · intro θ
    rw [hfun, deriv_comp_add_const]
    exact hnz (θ + t)

end PolyaNeumann

end
