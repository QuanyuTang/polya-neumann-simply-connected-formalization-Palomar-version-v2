module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import RequestProject.CurveContinuity

/-!
# The Cayley transform of the endpoint (Lemma 4.16)

Let `V` be a unitary operator on a complex Hilbert space with `ker (I - V) = 0` (for the
transport endpoint `V = V_E` this holds at a Neumann-nonresonant energy by Lemma 4.13).
The paper's Cayley transform is the unbounded operator
`K = i (I + V) (I - V)⁻¹` with domain `ran (I - V)`, i.e. `K ((I - V) a) = i (I + V) a`.

We prove (Lemma 4.16):
* `K` is densely defined and self-adjoint (`cayleyOp_dense`, `cayleyOp_isSelfAdjoint`);
* the resolvent identities `(K + i)⁻¹ = (I - V)/(2i)` and `(K - i)⁻¹ = (I - V) V^*/(2i)`
  (`cayleyOp_add_I_resolvent`, `cayleyOp_sub_I_resolvent` and their left-inverse versions);
* if `U v = e^{iθ} v` with `U = V^*` and `0 < θ < 2π`, then `K v = cot(θ/2) v`
  (`cayleyOp_eigen`).

Compactness of the resolvents (which uses that `I - V_E` is trace class) is not formalized.
-/

@[expose] public section

open scoped ComplexConjugate

noncomputable section

namespace PolyaNeumann

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain `ran (I - V)` of the Cayley transform. -/
abbrev cayleyDomain (V : H →L[ℂ] H) : Submodule ℂ H :=
  LinearMap.range ((1 - V : H →L[ℂ] H) : H →ₗ[ℂ] H)

/-- The Cayley transform `K = i (I + V) (I - V)⁻¹` on `ran (I - V)`, for `I - V` injective. -/
def cayleyOp (V : H →L[ℂ] H) (hV : Function.Injective (1 - V : H →L[ℂ] H)) : H →ₗ.[ℂ] H where
  domain := cayleyDomain V
  toFun := ((Complex.I • (1 + V) : H →L[ℂ] H) : H →ₗ[ℂ] H).comp
    (LinearEquiv.ofInjective ((1 - V : H →L[ℂ] H) : H →ₗ[ℂ] H) hV).symm.toLinearMap

variable {V : H →L[ℂ] H} (hV : Function.Injective (1 - V : H →L[ℂ] H))

lemma mem_cayleyDomain (a : H) : (1 - V : H →L[ℂ] H) a ∈ cayleyDomain V := ⟨a, rfl⟩

/-- `K` evaluated on a domain element given as `(I - V) a` is `i (a + V a)`. -/
lemma cayleyOp_apply' (x : cayleyDomain V) (a : H) (hx : (x : H) = (1 - V : H →L[ℂ] H) a) :
    cayleyOp V hV x = Complex.I • (a + V a) := by
  have h : (LinearEquiv.ofInjective ((1 - V : H →L[ℂ] H) : H →ₗ[ℂ] H) hV).symm x = a := by
    rw [LinearEquiv.symm_apply_eq]
    ext
    rw [LinearEquiv.ofInjective_apply]
    simp [hx]
  change (Complex.I • (1 + V) : H →L[ℂ] H)
    ((LinearEquiv.ofInjective ((1 - V : H →L[ℂ] H) : H →ₗ[ℂ] H) hV).symm x) = _
  rw [h]
  simp

/-- `K ((I - V) a) = i (a + V a)`. -/
lemma cayleyOp_apply (a : H) :
    cayleyOp V hV ⟨(1 - V : H →L[ℂ] H) a, mem_cayleyDomain a⟩ = Complex.I • (a + V a) :=
  cayleyOp_apply' hV _ a rfl

/-- Every vector of the domain has the form `(I - V) a`. -/
lemma exists_eq_of_mem_cayleyDomain (x : cayleyDomain V) :
    ∃ a : H, (x : H) = (1 - V : H →L[ℂ] H) a := by
  obtain ⟨a, ha⟩ := x.2
  exact ⟨a, ha.symm⟩

variable [CompleteSpace H] (hU : V ∈ unitary (H →L[ℂ] H))
include hU

omit hV in
lemma unitary_adjoint_apply_apply (a : H) : ContinuousLinearMap.adjoint V (V a) = a := by
  have := (Unitary.mem_iff.mp hU).1
  rw [ContinuousLinearMap.star_eq_adjoint] at this
  rw [← ContinuousLinearMap.mul_apply, this, ContinuousLinearMap.one_apply]

omit hV in
lemma unitary_apply_adjoint_apply (a : H) : V (ContinuousLinearMap.adjoint V a) = a := by
  have := (Unitary.mem_iff.mp hU).2
  rw [ContinuousLinearMap.star_eq_adjoint] at this
  rw [← ContinuousLinearMap.mul_apply, this, ContinuousLinearMap.one_apply]

omit hV in
lemma unitary_inner_map_map (a b : H) : inner ℂ (V a) (V b) = inner ℂ a b := by
  rw [← ContinuousLinearMap.adjoint_inner_right, unitary_adjoint_apply_apply hU]

/-- `K` is symmetric: `⟨K x, y⟩ = ⟨x, K y⟩` on `ran (I - V)`. -/
theorem cayleyOp_symmetric : (cayleyOp V hV).IsFormalAdjoint (cayleyOp V hV) := by
  intro x y
  obtain ⟨a, ha⟩ := exists_eq_of_mem_cayleyDomain x
  obtain ⟨b, hb⟩ := exists_eq_of_mem_cayleyDomain y
  rw [cayleyOp_apply' hV x a ha, cayleyOp_apply' hV y b hb, ha, hb]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_smul_left,
    inner_smul_right, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    unitary_inner_map_map hU, Complex.conj_I]
  ring

omit [CompleteSpace H] hU in
/-- **Resolvent identity** `(K + i)⁻¹ = (I - V)/(2i)`: the vector `(I - V) b / (2i)` lies in the
domain and `(K + i)` maps it to `b`. -/
theorem cayleyOp_add_I_resolvent (b : H) :
    ∃ hx : (2 * Complex.I)⁻¹ • (1 - V : H →L[ℂ] H) b ∈ cayleyDomain V,
      cayleyOp V hV ⟨_, hx⟩ + Complex.I • ((2 * Complex.I)⁻¹ • (1 - V : H →L[ℂ] H) b) = b := by
  have he : (2 * Complex.I)⁻¹ • (1 - V : H →L[ℂ] H) b =
      (1 - V : H →L[ℂ] H) ((2 * Complex.I)⁻¹ • b) := (map_smul _ _ _).symm
  refine ⟨he ▸ mem_cayleyDomain _, ?_⟩
  erw [cayleyOp_apply' hV _ _ he]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_smul]
  match_scalars <;> field_simp <;> ring

omit [CompleteSpace H] hU in
/-- `(I - V)/(2i)` is also a left inverse of `K + i` on the domain. -/
theorem cayleyOp_add_I_resolvent_left (x : cayleyDomain V) :
    (2 * Complex.I)⁻¹ • (1 - V : H →L[ℂ] H) (cayleyOp V hV x + Complex.I • (x : H)) = x := by
  obtain ⟨a, ha⟩ := exists_eq_of_mem_cayleyDomain x
  rw [cayleyOp_apply' hV x a ha, ha]
  have : Complex.I • (a + V a) + Complex.I • (1 - V : H →L[ℂ] H) a = (2 * Complex.I) • a := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    module
  rw [this, map_smul, smul_smul, inv_mul_cancel₀ (by simp), one_smul]

/-- **Resolvent identity** `(K - i)⁻¹ = (I - V) V^*/(2i)`. -/
theorem cayleyOp_sub_I_resolvent (b : H) :
    ∃ hx : (2 * Complex.I)⁻¹ • (1 - V : H →L[ℂ] H) (ContinuousLinearMap.adjoint V b) ∈
        cayleyDomain V,
      cayleyOp V hV ⟨_, hx⟩ -
        Complex.I • ((2 * Complex.I)⁻¹ • (1 - V : H →L[ℂ] H) (ContinuousLinearMap.adjoint V b)) =
        b := by
  have he : (2 * Complex.I)⁻¹ • (1 - V : H →L[ℂ] H) (ContinuousLinearMap.adjoint V b) =
      (1 - V : H →L[ℂ] H) ((2 * Complex.I)⁻¹ • ContinuousLinearMap.adjoint V b) :=
    (map_smul _ _ _).symm
  refine ⟨he ▸ mem_cayleyDomain _, ?_⟩
  erw [cayleyOp_apply' hV _ _ he]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_smul,
    unitary_apply_adjoint_apply hU]
  match_scalars <;> field_simp <;> ring

/-- `(I - V) V^*/(2i)` is also a left inverse of `K - i` on the domain. -/
theorem cayleyOp_sub_I_resolvent_left (x : cayleyDomain V) :
    (2 * Complex.I)⁻¹ • (1 - V : H →L[ℂ] H)
      (ContinuousLinearMap.adjoint V (cayleyOp V hV x - Complex.I • (x : H))) = x := by
  obtain ⟨a, ha⟩ := exists_eq_of_mem_cayleyDomain x
  rw [cayleyOp_apply' hV x a ha, ha]
  have : Complex.I • (a + V a) - Complex.I • (1 - V : H →L[ℂ] H) a = (2 * Complex.I) • V a := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    module
  rw [this, map_smul, unitary_adjoint_apply_apply hU, map_smul, smul_smul,
    inv_mul_cancel₀ (by simp), one_smul]

/-- **Eigenvalues.**  If `U v = e^{iθ} v` for `U = V^*` and `0 < θ < 2π`, then `v` lies in
the domain of `K` and `K v = cot(θ/2) v`. -/
theorem cayleyOp_eigen {v : H} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 2 * Real.pi)
    (hv : ContinuousLinearMap.adjoint V v = Complex.exp (θ * Complex.I) • v) :
    ∃ hx : v ∈ cayleyDomain V, cayleyOp V hV ⟨v, hx⟩ = (Real.cot (θ / 2) : ℂ) • v := by
  set w : ℂ := Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) with hwdef
  set e : ℂ := Complex.exp (θ * Complex.I) with hedef
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hew : e = w * w := by
    rw [hedef, hwdef, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he0 : e ≠ 0 := Complex.exp_ne_zero _
  have he1 : e ≠ 1 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    have hθn : θ = n * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      simpa [Complex.mul_im] using this
    have h1 : (0 : ℝ) < n := by
      by_contra hcon
      push_neg at hcon
      nlinarith [Real.pi_pos]
    have h2 : (n : ℝ) < 1 := by
      by_contra hcon
      push_neg at hcon
      nlinarith [Real.pi_pos]
    have h1' : (0 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  -- `V v = e⁻¹ v`
  have hVv : V v = e⁻¹ • v := by
    have h1 := congrArg V hv
    rw [unitary_apply_adjoint_apply hU, map_smul] at h1
    calc V v = e⁻¹ • (e • V v) := by rw [smul_smul, inv_mul_cancel₀ he0, one_smul]
      _ = e⁻¹ • v := by rw [← h1]
  have hc : (1 - e⁻¹) ≠ 0 := by
    intro h
    apply he1
    have : e⁻¹ = 1 := (sub_eq_zero.mp h).symm
    simpa using congrArg (·⁻¹) this
  have hrep : v = (1 - V : H →L[ℂ] H) ((1 - e⁻¹)⁻¹ • v) := by
    rw [map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hVv,
      show v - e⁻¹ • v = (1 - e⁻¹) • v by module, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hww : w * w ≠ 1 := hew ▸ he1
  have hd1 : w⁻¹ - w ≠ 0 := by
    intro h
    apply hww
    have : w⁻¹ = w := sub_eq_zero.mp h
    rw [show w * w = w⁻¹ * w by rw [this]]
    exact inv_mul_cancel₀ hw0
  have hd2 : w * w - 1 ≠ 0 := sub_ne_zero.mpr hww
  have hcot : ((Real.cot (θ / 2) : ℝ) : ℂ) = Complex.I * ((1 - e⁻¹)⁻¹ * (1 + e⁻¹)) := by
    rw [Complex.ofReal_cot, Complex.cot_eq_cos_div_sin, Complex.cos, Complex.sin, ← hwdef,
      neg_mul, Complex.exp_neg, ← hwdef, hew]
    field_simp
    rw [Complex.I_sq, mul_neg_one, neg_div, ← div_neg, neg_sub]
  refine ⟨hrep ▸ mem_cayleyDomain _, ?_⟩
  erw [cayleyOp_apply' hV _ _ hrep, map_smul, hVv, hcot]
  module


/-- `K` is densely defined. -/
theorem cayleyOp_dense : Dense ((cayleyOp V hV).domain : Set H) := by
  change Dense ((LinearMap.range ((1 - V : H →L[ℂ] H) : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  have h := ContinuousLinearMap.orthogonal_range (1 - V : H →L[ℂ] H)
  rw [h, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hx2 : ContinuousLinearMap.adjoint V x = x := by
    refine ext_inner_right ℂ fun a => ?_
    have := ContinuousLinearMap.adjoint_inner_left (1 - V : H →L[ℂ] H) a x
    rw [show (ContinuousLinearMap.adjoint (1 - V)) x = 0 from hx, inner_zero_left] at this
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      inner_sub_right] at this
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact (sub_eq_zero.mp this.symm).symm
  rw [Submodule.mem_bot]
  apply hV
  have hx' : V x = x := by
    conv_lhs => rw [← hx2]
    exact unitary_apply_adjoint_apply hU x
  simp [hx']

/-- **Lemma 4.16.**  The Cayley transform `K = i (I + V)(I - V)⁻¹` of a unitary `V` with
`ker (I - V) = 0` is self-adjoint. -/
theorem cayleyOp_isSelfAdjoint : IsSelfAdjoint (cayleyOp V hV) := by
  have hD := cayleyOp_dense hV hU
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm ?_ ((cayleyOp_symmetric hV hU).le_adjoint hD)
  -- every vector of the adjoint domain lies in `ran (I - V)`, with matching values
  have key : ∀ y : (cayleyOp V hV).adjoint.domain, ∃ b : H, (y : H) = (1 - V : H →L[ℂ] H) b ∧
      (cayleyOp V hV).adjoint y = Complex.I • (b + V b) := by
    intro y
    set z := (cayleyOp V hV).adjoint y
    have hz : ∀ a : H, inner ℂ z ((1 - V : H →L[ℂ] H) a) =
        inner ℂ (y : H) (Complex.I • (a + V a)) := fun a => by
      have := LinearPMap.adjoint_isFormalAdjoint hD y ⟨_, mem_cayleyDomain a⟩
      rw [cayleyOp_apply] at this
      exact this
    have hop : z - ContinuousLinearMap.adjoint V z =
        (-Complex.I) • ((y : H) + ContinuousLinearMap.adjoint V y) := by
      refine ext_inner_right ℂ fun a => ?_
      have := hz a
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_right,
        inner_smul_right, inner_add_right] at this
      simp only [inner_sub_left, inner_smul_left, inner_add_left,
        ContinuousLinearMap.adjoint_inner_left, Complex.conj_neg_I, this]
    have hVz : V z = z - Complex.I • (V y + (y : H)) := by
      have := congrArg V hop
      simp only [map_sub, map_smul, map_add, unitary_apply_adjoint_apply hU] at this
      rw [sub_eq_iff_eq_add] at this
      rw [this]
      module
    refine ⟨(2 : ℂ)⁻¹ • ((y : H) - Complex.I • z), ?_, ?_⟩
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_smul, map_sub,
        hVz]
      match_scalars <;> field_simp <;> ring_nf <;> simp [Complex.I_sq]; ring
    · simp only [map_smul, map_sub, hVz]
      match_scalars <;> field_simp <;> ring_nf <;> simp [Complex.I_sq]
  refine ⟨fun y hy => ?_, fun y x hxy => ?_⟩
  · obtain ⟨b, hb, -⟩ := key ⟨y, hy⟩
    exact ⟨b, hb.symm⟩
  · obtain ⟨b, hb, hval⟩ := key y
    rw [hval, cayleyOp_apply' hV x b (hxy ▸ hb)]

omit hV in
/-- `ran (V^* - I) = ran (I - V)` for unitary `V` (used in Lemma 4.17). -/
theorem range_adjoint_sub_one :
    LinearMap.range ((ContinuousLinearMap.adjoint V - 1 : H →L[ℂ] H) : H →ₗ[ℂ] H) =
      cayleyDomain V := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨ContinuousLinearMap.adjoint V a, ?_⟩
    simp [unitary_apply_adjoint_apply hU]
  · rintro ⟨a, rfl⟩
    refine ⟨V a, ?_⟩
    simp [unitary_adjoint_apply_apply hU]

omit hV hU in
/-- **Lemma 4.16 for the transport endpoint.**  For a Lipschitz curve and any energy, if
`ker (I - V_E) = 0` then the Cayley transform `K_E = i (I + V_E)(I - V_E)⁻¹` of the transport
endpoint `V_E = W_E(L)` is densely defined and self-adjoint. -/
theorem transport_cayleyOp_isSelfAdjoint {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (hinj : Function.Injective (1 - W (2 * Real.pi) : Ell2 →L[ℂ] Ell2)) :
    Dense ((cayleyOp (W (2 * Real.pi)) hinj).domain : Set Ell2) ∧
      IsSelfAdjoint (cayleyOp (W (2 * Real.pi)) hinj) := by
  have hU := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  exact ⟨cayleyOp_dense hinj hU, cayleyOp_isSelfAdjoint hinj hU⟩

end PolyaNeumann

end
